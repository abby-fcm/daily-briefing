#!/usr/bin/env python3
"""
briefing.py -- one tool for the daily briefings: feeds, research (PubMed), trends.

Merged from daily_briefing_feeds.py, daily_briefing_research.py and trends.py.
One config (config.yaml), one state folder (state/), outputs in reports/ and docs/.

Commands
  plan    [--job feeds|research|trends|all]   JSON list of sources to gather today
  collect [--job ...]                         gather over direct HTTP (needs open network)
  ingest  FILE|-                              add items gathered by any other means
  leads                                       trend leads awaiting a relevance score (JSON)
  scores  FILE|-                              store relevance scores for those leads
  report  [--job ...] [--no-dig]              write reports, update state
  run     [--job ...]                         collect + report + extra searches in one go (GitHub Actions)
  status                                      state and inbox summary

Ingest format (one object or a list of objects):
  {"source": "feed:STAT News", "ok": true, "msg": "", "items": [{"title": "...", "url": "...", "date": "..."}]}
Source prefixes: feed:<outlet>  pubmed:<topic>  news:<query>  trends  reddit  youtube
  feed    items: title, url, date
  pubmed  items: title, url (or pmid), journal, date
  news    items: title, url, where (outlet), date
  trends  items: title, traffic, news: [{title, url, source}]
  Use "ok": false for a source that could not be reached.

Scores format: [{"id": 0, "score": 8, "angle": "headline idea if score >= 6"}]

Exit codes: 0 done, 2 error, 3 trends report needs extra searches (see its JSON), run them,
ingest as news:dig:<query>, score, then run report again.

Environment: BRIEFING_HOME (default: folder of this file), BRIEFING_DATE (YYYY-MM-DD, testing),
CONTACT_EMAIL, REDDIT_CLIENT_ID, REDDIT_CLIENT_SECRET, YOUTUBE_API_KEY (live collection only).
"""

import argparse
import html
import json
import math
import os
import random
import re
import sys
import time
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import quote, quote_plus, urlparse, urlsplit

try:
    import requests
except ImportError:  # only needed for `collect`
    requests = None
try:
    import yaml
except ImportError:
    sys.exit("PyYAML is required: pip install pyyaml")

ROOT = Path(os.environ.get("BRIEFING_HOME") or Path(__file__).parent).resolve()
STATE = ROOT / "state"
REPORTS = ROOT / "reports"
DOCS_DIR = ROOT / "docs"
SEEN_FILE = STATE / "seen.json"
HISTORY_FILE = STATE / "history.json"
CURSOR_FILE = STATE / "cursors.json"
INBOX_FILE = STATE / "inbox.json"
PLAN_FILE = STATE / "plan.json"
LEADS_FILE = STATE / "leads.json"

HISTORY_DAYS = 30
BASELINE_DAYS = 7
MIN_DAYS_FOR_RISING = 3
ARCHIVE_DAYS = 90
TREND_KEEP_DAYS = 21     # trend-item repeat memory
BRIEFING_KEEP_DAYS = 365  # feeds/research repeat memory
MAX_SEEN = 40000

_env_date = os.environ.get("BRIEFING_DATE")
NOW = (datetime.strptime(_env_date, "%Y-%m-%d").replace(hour=12, tzinfo=timezone.utc)
       if _env_date else datetime.now(timezone.utc))
TODAY = NOW.strftime("%Y-%m-%d")

USER_AGENT = "content-briefing/3.0 (daily research tool)"

EMPTY = "- (nothing new since your last briefing)"
BLOCKED = "- (source unreachable right now — will try again next run)"


# ================================================================ reused analysis and rendering

GENERIC_HEALTH = [
    "health", "healthy", "doctor", "doctors", "disease", "outbreak", "recall",
    "fda", "cdc", "cancer", "hospital", "study", "symptoms", "virus", "vitamin",
    "diet", "nutrition", "wellness", "medication", "drug", "treatment", "infection",
    "surgery", "dermatologist", "dietitian", "nurse", "mental health",
]

STOPWORDS = set("""
a about above after again against all almost also am an and any are aren't as at be because been
before being below between both but by can can't cannot could couldn't did didn't do does doesn't
doing don't down during each even ever every few for from further get gets getting got had hadn't
has hasn't have haven't having he her here hers herself him himself his how i i'd i'll i'm i've if
in into is isn't it it's its itself just know like make many me might more most much must my myself
need new no nor not now of off on once one only or other our ours ourselves out over own really same
say says she should shouldn't since so some still such than that that's the their theirs them
themselves then there there's these they they're this those though through to too two under until
up upon us very via was wasn't way we we're were weren't what what's when where which while who
whom why will with won't would wouldn't yet you you're your yours yourself yourselves want wants
anyone someone something anything everything thing things people feel feeling felt think thought
going go goes went take taking took use using used start started getting try tried trying good bad
best better worse worst first last back time times today yesterday tomorrow ago around much lot lots
little big long made keep keeps kept since though without within another every also however
reddit post posts comment comments thread edit update help question advice please thanks thank
anyone else normal weird experience experiences share sharing looking look looks find found
tips tip vs amp say said says tell told ask asked asking news report reports new study studies
could might may year years month months week weeks day days hour hours minute minutes
actually worth fixed finally literally honestly trend trends trending viral tiktok doctors experts
weigh women woman men man girl girls guys
instagram reddit youtube reels reel influencer influencers social media users redditors tiktoker tiktokers everyone everybody nobody someone tried working works
""".split())

def local_name(tag):
    return tag.split("}")[-1] if "}" in tag else tag


def child_text(el, name):
    for c in el:
        if local_name(c.tag) == name:
            return (c.text or "").strip()
    return ""


def children(el, name):
    return [c for c in el if local_name(c.tag) == name]


def kw_pattern(kw):
    """Whole-word match that also catches simple plurals (supplement -> supplements)."""
    kw = kw.lower()
    suffix = r"(?:s|es)?" if kw[-1].isalpha() else ""
    return re.compile(r"(?<![a-z0-9])" + re.escape(kw) + suffix + r"(?![a-z0-9])")


class Tagger:
    def __init__(self, categories):
        self.patterns = []  # (keyword, category, regex)
        for cat, kws in categories.items():
            for kw in kws or []:
                kw = str(kw).strip()
                if kw:
                    self.patterns.append((kw.lower(), cat, kw_pattern(kw)))
        self.generic = [kw_pattern(k) for k in GENERIC_HEALTH]

    def match(self, text):
        """Return (set of keywords, sorted list of categories) found in text."""
        t = (text or "").lower()
        kws, cats = set(), set()
        for kw, cat, rx in self.patterns:
            if rx.search(t):
                kws.add(kw)
                cats.add(cat)
        return kws, sorted(cats)

    def is_health(self, text):
        t = (text or "").lower()
        if any(rx.search(t) for _, _, rx in self.patterns):
            return True
        return any(rx.search(t) for rx in self.generic)


def news_key(title):
    return "n:" + re.sub(r"[^a-z0-9]", "", title.lower())[:80]


def item_key(it):
    if it["kind"] == "news":
        return news_key(it["title"])
    if it["kind"] == "trend":
        return "t:" + it["title"].lower().strip()
    return it["url"]


def dig_queries(cfg, rising, n):
    """Extra searches: first go deeper on what's rising, then rotate through
    the topic keywords so a different slice gets searched each day."""
    qs = []
    for r in rising:
        qs += [f'"{r["kw"]}" TikTok', f'"{r["kw"]}" trend']
    all_kws = sorted({str(k) for kws in cfg["categories"].values() for k in (kws or [])})
    if all_kws:
        start = (NOW.toordinal() * n) % len(all_kws)
        rotation = (all_kws[start:] + all_kws[:start])[:n]
        suffixes = ["trend", "TikTok", "viral", "experts say"]
        qs += [f'"{kw}" {suffixes[i % len(suffixes)]}' for i, kw in enumerate(rotation)]
    out = []
    for q in qs:
        if q not in out:
            out.append(q)
    return out[:n]


def tokenize(text):
    words = re.findall(r"[a-z][a-z0-9'+-]*[a-z0-9+]|[a-z]", text.lower())
    words = [w.strip("'-") for w in words]
    return [w for w in words if w]


def extract_terms(text):
    words = tokenize(text)
    terms = set()
    for w in words:
        if len(w) >= 4 and w not in STOPWORDS and not w.isdigit():
            terms.add(w)
    for a, b in zip(words, words[1:]):
        if a in STOPWORDS or b in STOPWORDS or len(a) < 3 or len(b) < 3:
            continue
        terms.add(f"{a} {b}")
    return terms


def analyze(all_items, tagger, hist, kw_category):
    kw_counts, term_counts = Counter(), Counter()
    kw_examples, term_examples = defaultdict(list), defaultdict(list)

    for it in all_items:
        kws, cats = tagger.match(it["text"])
        it["cats"] = cats
        it["kws"] = sorted(kws)
        if it.get("dug"):
            continue  # extra searches would skew day-to-day counts
        for kw in kws:
            kw_counts[kw] += 1
            if len(kw_examples[kw]) < 3:
                kw_examples[kw].append(it)
        if it["kind"] in ("reddit", "news", "youtube"):
            for t in extract_terms(it["title"]):
                term_counts[t] += 1
                if len(term_examples[t]) < 3:
                    term_examples[t].append(it)

    prev_days = sorted(d for d in hist["days"] if d < TODAY)
    baseline = prev_days[-BASELINE_DAYS:]
    n_base = len(baseline)

    # Rising keywords
    rising = []
    if n_base >= MIN_DAYS_FOR_RISING:
        for kw, c in kw_counts.items():
            avg = sum(hist["days"][d]["kw"].get(kw, 0) for d in baseline) / n_base
            if c >= 3 and ((avg == 0) or (c / avg >= 1.8 and c - avg >= 2)):
                spark_days = prev_days[-13:]
                series = [hist["days"][d]["kw"].get(kw, 0) for d in spark_days] + [c]
                rising.append({
                    "kw": kw, "cat": kw_category.get(kw, ""), "count": c, "avg": avg,
                    "ratio": (c / avg) if avg else None, "series": series,
                    "examples": kw_examples[kw],
                })
        rising.sort(key=lambda r: ((r["ratio"] or 99), r["count"]), reverse=True)

    # Brand-new terms
    new_terms = []
    if n_base >= MIN_DAYS_FOR_RISING:
        lookback = prev_days[-14:]
        seen = Counter()
        for d in lookback:
            seen.update(hist["days"][d].get("terms", {}))
        for t, c in term_counts.items():
            if c >= 3 and seen[t] == 0 and t not in kw_category:
                sources = {e["kind"] + e["where"] for e in term_examples[t]}
                if len(sources) >= 2:
                    new_terms.append({"term": t, "count": c, "examples": term_examples[t]})
        new_terms.sort(key=lambda x: x["count"], reverse=True)
        # Drop single words that are part of a listed bigram
        bigrams = [n["term"] for n in new_terms if " " in n["term"]]
        new_terms = [n for n in new_terms
                     if " " in n["term"] or not any(n["term"] in b.split() for b in bigrams)]

    # Save today to history
    for r in rising:
        streak = 1
        for d in reversed(prev_days):
            if r["kw"] in hist["days"][d].get("rising", []):
                streak += 1
            else:
                break
        r["streak"] = streak

    hist["days"][TODAY] = {
        "kw": dict(kw_counts),
        "terms": dict(term_counts.most_common(4000)),
        "rising": [r["kw"] for r in rising[:15]],
    }
    return rising[:15], new_terms[:20], n_base


def esc(s):
    return html.escape(str(s or ""), quote=True)


def fmt_age(h):
    if h < 1:
        return "under 1h"
    if h < 48:
        return f"{int(h)}h"
    return f"{int(h // 24)}d"


def fmt_num(n):
    n = float(n)
    if n >= 1_000_000:
        return f"{n / 1_000_000:.1f}M"
    if n >= 1000:
        return f"{n / 1000:.1f}k"
    return f"{int(n)}"


def sparkline(series):
    if not series:
        return ""
    w, h, pad = 96, 26, 2
    mx = max(series) or 1
    n = len(series)
    step = (w - pad * 2) / max(n - 1, 1)
    pts = [(pad + i * step, h - pad - (v / mx) * (h - pad * 2)) for i, v in enumerate(series)]
    poly = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
    lx, ly = pts[-1]
    return (f'<svg class="spark" viewBox="0 0 {w} {h}" width="{w}" height="{h}" aria-hidden="true">'
            f'<polyline points="{poly}" fill="none" stroke="currentColor" stroke-width="1.5" '
            f'stroke-linejoin="round" stroke-linecap="round"/>'
            f'<circle cx="{lx:.1f}" cy="{ly:.1f}" r="2.6" class="spark-dot"/></svg>')


def cats_attr(cats):
    return esc("|".join(cats) if cats else "Other")


def tag_list(cats):
    return "".join(f'<span class="tag">{esc(c)}</span>' for c in cats)


PLATFORM_NAMES = [
    ("TikTok", r"tiktok|tik tok"), ("Reddit", r"reddit"), ("Instagram", r"instagram|reels?"),
    ("YouTube", r"youtube"), ("Threads", r"threads app|on threads"), ("X", r"on x|twitter"),
    ("Pinterest", r"pinterest"), ("Facebook", r"facebook"),
]


def platforms_in(text):
    t = (text or "").lower()
    return [name for name, rx in PLATFORM_NAMES if re.search(r"(?<![a-z])(?:" + rx + r")(?![a-z])", t)]


def platform_links(term):
    q = quote(term)
    links = [
        ("TikTok", f"https://www.tiktok.com/search?q={q}"),
        ("Instagram", f"https://www.instagram.com/explore/search/keyword/?q={q}"),
        ("YouTube Shorts", f"https://www.youtube.com/results?search_query={quote_plus(term + ' #shorts')}"),
        ("Pinterest", f"https://www.pinterest.com/search/pins/?q={q}"),
        ("Google Trends", f"https://trends.google.com/trends/explore?date=today%203-m&geo=US&q={q}"),
    ]
    return ('<div class="go" aria-label="Search this on other platforms">'
            + "".join(f'<a href="{esc(u)}" target="_blank" rel="noopener">{n}</a>' for n, u in links)
            + '</div>')


def example_links(examples):
    out = []
    for e in examples:
        out.append(f'<li><a href="{esc(e["url"])}" target="_blank" rel="noopener">{esc(e["title"])}</a>'
                   f'<span class="src">{esc(e["where"])}</span></li>')
    return f'<ul class="examples">{"".join(out)}</ul>'


def fit_html(it):
    if it.get("fit") is None:
        return ""
    return f'<span class="fit">Fit {it["fit"]}/10</span>'


def angle_html(it):
    return f'<p class="angle">{esc(it["angle"])}</p>' if it.get("angle") else ""


def render(cfg, results, rising, new_terms, n_base, ai_status=None, repeat_status=None,
           extra_html="", have_trends=True, extra_cats=()):
    reddit, news, trends, yt = (results[k][0] for k in ("reddit", "news", "trends", "youtube"))
    status = {k: v[1] for k, v in results.items()}
    labels = {"reddit": "Reddit", "news": "Google News", "trends": "Google Trends", "youtube": "YouTube"}

    used_cats = set(extra_cats)
    for group in (reddit, news, trends, yt):
        for it in group:
            used_cats.update(it.get("cats") or ["Other"])
    ordered = [c for c in cfg["categories"] if c in used_cats]
    if "Other" in used_cats:
        ordered.append("Other")
    chips = ['<button class="chip is-on" data-cat="all" aria-pressed="true">All</button>']
    chips += [f'<button class="chip" data-cat="{esc(c)}" aria-pressed="false">{esc(c)}</button>' for c in ordered]

    # Rising block
    if n_base < MIN_DAYS_FOR_RISING:
        rising_html = (f'<p class="note">Rising topics need a few days of history to compare against. '
                       f'Day {n_base + 1} of {MIN_DAYS_FOR_RISING + 1} collected. Check back after '
                       f'{MIN_DAYS_FOR_RISING - n_base} more daily run(s).</p>')
    elif not rising:
        rising_html = '<p class="note">No keyword jumped above its usual level today.</p>'
    else:
        rows = []
        for r in rising:
            mult = f'×{r["ratio"]:.1f}' if r["ratio"] else "new"
            usual = f'usually {r["avg"]:.1f}' if r["avg"] else "none last week"
            rows.append(
                f'<article class="rise" data-cats="{esc(r["cat"] or "Other")}">'
                f'<div class="rise-head"><h3>{esc(r["kw"])}</h3>'
                f'<span class="mult">{mult}</span></div>'
                + (f'<p class="streak">Rising {r["streak"]} days in a row</p>' if r.get("streak", 1) > 1 else "")
                + f'<div class="rise-meta">{sparkline(r["series"])}'
                f'<span>{r["count"]} today, {usual}</span>'
                f'<span class="tag">{esc(r["cat"])}</span></div>'
                f'<details><summary>See posts</summary>{example_links(r["examples"])}</details>'
                f'{platform_links(r["kw"])}'
                f'</article>')
        rising_html = "".join(rows)

    if n_base < MIN_DAYS_FOR_RISING:
        new_html = '<p class="note">New terms appear once there are a few days of history.</p>'
    elif not new_terms:
        new_html = '<p class="note">No brand-new terms showed up in multiple places today.</p>'
    else:
        new_html = "".join(
            f'<article class="term" data-cats="all-only"><h3>{esc(t["term"])}</h3>'
            f'<span class="count">{t["count"]} mentions</span>'
            f'<details><summary>See posts</summary>{example_links(t["examples"])}</details>'
            f'{platform_links(t["term"])}</article>'
            for t in new_terms)

    def item_rows(items, meta_fn):
        if not items:
            return ""
        return "".join(
            f'<li class="item" data-cats="{cats_attr(it.get("cats"))}">'
            f'<a href="{esc(it["url"])}" target="_blank" rel="noopener">{esc(it["title"])}</a>'
            f'<div class="meta">{fit_html(it)}{meta_fn(it)}{tag_list(it.get("cats") or [])}</div>'
            f'{angle_html(it)}</li>'
            for it in items)

    reddit_rows = item_rows(reddit, lambda p: (
        f'<span>{esc(p["where"])}</span><span>{fmt_num(p["score"])} upvotes</span>'
        f'<span>{fmt_num(p["comments"])} comments</span><span>{fmt_age(p["age_h"])} old</span>'))
    news_rows = item_rows(news, lambda n: (
        "".join(f'<span class="plat">{p}</span>' for p in platforms_in(n["title"]))
        + f'<span>{esc(n["where"])}</span><span>{fmt_age(n["age_h"])} ago</span>'))
    yt_long = [v for v in yt if not v.get("short")]
    yt_short = [v for v in yt if v.get("short")]
    yt_meta = lambda v: (
        f'<span>{esc(v["where"])}</span><span>{fmt_num(v["views"])} views</span>'
        f'<span>{fmt_num(v["velocity"])}/hour</span>')
    yt_rows = item_rows(yt_long, yt_meta)
    shorts_rows = item_rows(yt_short, yt_meta)
    trend_rows = "".join(
        f'<li class="item" data-cats="{cats_attr(t.get("cats"))}">'
        f'<a href="{esc(t["url"])}" target="_blank" rel="noopener">{esc(t["title"])}</a>'
        f'<div class="meta">{fit_html(t)}<span>{esc(t["where"])}</span>{tag_list(t.get("cats") or [])}</div>'
        f'{angle_html(t)}'
        + (f'<ul class="examples">' + "".join(
            f'<li><a href="{esc(n["url"])}" target="_blank" rel="noopener">{esc(n["title"])}</a>'
            f'<span class="src">{esc(n["source"])}</span></li>' for n in t["news"]) + '</ul>' if t["news"] else "")
        + '</li>' for t in trends)

    def section(sid, title, desc, key, rows):
        st = status[key]
        body = f'<ol class="list">{rows}</ol>' if rows else f'<p class="note">{esc(st["msg"])}</p>'
        return (f'<section id="{sid}" class="feed"><header><h2>{title}</h2><p>{desc}</p></header>'
                f'{body}<p class="note empty" hidden>Nothing in this category here today.</p></section>')

    all_status = dict(status)
    labels["ai"] = "Relevance AI"
    if ai_status:
        all_status["ai"] = ai_status
    labels["repeats"] = "Repeats"
    if repeat_status:
        all_status["repeats"] = repeat_status
    status_html = "".join(
        f'<li class="{"ok" if s["ok"] else "off"}"><strong>{labels[k]}</strong> {esc(s["msg"])}</li>'
        for k, s in all_status.items())

    manual = [
        ("TikTok Creative Center", "Set industry to Health, 7 days, tick “New to top 100”.",
         "https://ads.tiktok.com/business/creativecenter/inspiration/popular/hashtag/pc/en"),
        ("Google Trends: rising health searches", "Scroll to Related queries and choose Rising.",
         "https://trends.google.com/trends/explore?cat=45&date=now%207-d&geo=US"),
        ("Pinterest Trends", "Filter to Health or Wellness, sort by Growing.",
         "https://trends.pinterest.com/?region=US"),
        ("Instagram Reels", "Search a rising keyword from above and sort by recent.",
         "https://www.instagram.com/reels/"),
    ]
    manual_html = "".join(
        f'<li><a href="{esc(u)}" target="_blank" rel="noopener">{esc(t)}</a><span>{esc(d)}</span></li>'
        for t, d, u in manual)

    sections = []
    if reddit or status["reddit"]["ok"]:
        sections.append(section("reddit", "Gaining fast on Reddit",
                                "Rising posts in health communities, ranked by upvotes and comments per hour.",
                                "reddit", reddit_rows))
    sections += [
        section("news", "Trends people are posting about",
                "News coverage from the last three days of what’s spreading on TikTok, Instagram, Reddit and "
                "other platforms. Tags show which platform a story mentions.",
                "news", news_rows),
        section("trends", "Health searches trending today",
                "From Google Trends, filtered to health topics.", "trends", trend_rows),
    ]
    if yt or status["youtube"]["ok"]:
        sections.append(section("shorts", "Fast-growing short videos",
                                "YouTube Shorts from the last three days, ranked by views per hour. "
                                "Many are reposted TikToks, so this is the closest automatic view of TikTok.",
                                "youtube", shorts_rows))
        sections.append(section("youtube", "Fast-growing YouTube videos",
                                "Longer videos from the last three days, ranked by views per hour.", "youtube", yt_rows))

    page = TEMPLATE
    replacements = {
        "{{UPDATED}}": NOW.isoformat(),
        "{{CHIPS}}": "".join(chips),
        "{{RISING}}": rising_html if have_trends else '<p class="note">Trend job has not run today.</p>',
        "{{NEWTERMS}}": new_html if have_trends else '<p class="note">Trend job has not run today.</p>',
        "{{EXTRA}}": extra_html,
        "{{SECTIONS}}": "".join(sections),
        "{{MANUAL}}": manual_html,
        "{{STATUS}}": status_html,
    }
    for k, v in replacements.items():
        page = page.replace(k, v)
    return page


TEMPLATE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Daily briefing</title>
<link rel="icon" href="data:image/svg+xml,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'><text y='.9em' font-size='90'>📈</text></svg>">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Newsreader:opsz,wght@6..72,500;6..72,650&family=Public+Sans:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{
  --bg:#EEF3F0; --surface:#FFFFFF; --ink:#16302B; --muted:#57706A; --line:#D3DED9;
  --signal:#A8325F; --signal-soft:#F6E3EB; --tag:#E2ECE7; --focus:#2458C6;
  --serif:"Newsreader",Georgia,"Times New Roman",serif;
  --sans:"Public Sans",system-ui,-apple-system,"Segoe UI",Roboto,Arial,sans-serif;
  box-sizing:border-box;
  padding-top:env(safe-area-inset-top,0px);
  padding-bottom:env(safe-area-inset-bottom,0px);
}
@media (prefers-color-scheme:dark){
  :root{--bg:#0F1916; --surface:#16231F; --ink:#E3EDE9; --muted:#95AAA3; --line:#27372F;
        --signal:#F07AA6; --signal-soft:#3A1F2B; --tag:#22332D; --focus:#8FB0FF;}
}
*,*::before,*::after{box-sizing:inherit}
html{scroll-padding-top:calc(env(safe-area-inset-top,0px) + 64px)}
body{margin:0;background:var(--bg);color:var(--ink);font:400 16px/1.5 var(--sans);-webkit-text-size-adjust:100%}
a{color:inherit}
a:focus-visible,button:focus-visible,summary:focus-visible{outline:2px solid var(--focus);outline-offset:2px;border-radius:4px}
.wrap{max-width:760px;margin:0 auto;padding:0 18px 48px}
.top{padding:28px 0 8px}
.top h1{font:650 clamp(2rem,7vw,2.8rem)/1.05 var(--serif);margin:0;letter-spacing:-.01em}
.top p{margin:.4rem 0 0;color:var(--muted);font-size:.9rem}
.chips{position:sticky;top:env(safe-area-inset-top,0px);z-index:5;background:var(--bg);
  display:flex;gap:8px;overflow-x:auto;padding:12px 18px;margin:0 -18px;scrollbar-width:none;
  border-bottom:1px solid var(--line)}
.chips::-webkit-scrollbar{display:none}
.chip{flex:none;font:500 .85rem/1 var(--sans);color:var(--ink);background:var(--surface);
  border:1px solid var(--line);border-radius:999px;padding:9px 14px;cursor:pointer}
.chip.is-on{background:var(--ink);color:var(--bg);border-color:var(--ink)}
h2{font:650 1.45rem/1.2 var(--serif);margin:0}
.feed header p,.block>p.lede{margin:.25rem 0 0;color:var(--muted);font-size:.9rem}
.block,.feed{margin-top:36px}
.rising-list{margin-top:14px;display:grid;gap:0}
.rise{padding:12px 0;border-top:1px solid var(--line)}
.rise:last-child{border-bottom:1px solid var(--line)}
.rise-head{display:flex;align-items:baseline;justify-content:space-between;gap:12px}
.rise h3{font:500 clamp(1.5rem,5.5vw,2rem)/1.1 var(--serif);margin:0}
.mult{font:650 1.25rem/1 var(--serif);color:var(--signal);white-space:nowrap}
.rise-meta{display:flex;flex-wrap:wrap;align-items:center;gap:6px 12px;margin-top:6px;color:var(--muted);font-size:.85rem}
.spark{color:var(--signal)}
.sub{font:600 1rem/1.2 var(--sans);margin:22px 0 0}
.static-block details .list{margin-top:8px}
.spark-dot{fill:var(--signal)}
.terms{display:flex;flex-wrap:wrap;gap:10px;margin-top:14px}
.term{background:var(--signal-soft);border-radius:14px;padding:12px 14px;flex:1 1 220px}
.term h3{font:500 1.2rem/1.2 var(--serif);margin:0}
.term .count{font-size:.8rem;color:var(--muted)}
.go{display:flex;flex-wrap:wrap;gap:6px;margin-top:10px}
.go a{font-size:.78rem;font-weight:500;text-decoration:none;border:1px solid var(--line);background:var(--surface);border-radius:999px;padding:5px 10px}
.go a:hover{border-color:var(--ink)}
details{margin-top:8px}
summary{cursor:pointer;font-size:.85rem;font-weight:600;color:var(--signal);list-style:none}
summary::-webkit-details-marker{display:none}
summary::before{content:"+ "}
details[open] summary::before{content:"− "}
.examples{list-style:none;margin:8px 0 0;padding:0;display:grid;gap:8px}
.examples li{font-size:.9rem;line-height:1.35}
.examples a{text-decoration:none}
.examples a:hover{text-decoration:underline}
.src{display:block;font-size:.78rem;color:var(--muted)}
.list{list-style:none;margin:14px 0 0;padding:0;background:var(--surface);border:1px solid var(--line);border-radius:12px}
.item{padding:14px 16px;border-top:1px solid var(--line)}
.item:first-child{border-top:0}
.item>a{font-weight:500;text-decoration:none;line-height:1.35;display:block}
.item>a:hover{text-decoration:underline}
.item .examples{margin-top:8px;padding-left:12px;border-left:2px solid var(--line)}
.meta{display:flex;flex-wrap:wrap;gap:4px 10px;margin-top:6px;font-size:.8rem;color:var(--muted);align-items:center}
.plat{background:var(--ink);color:var(--bg);border-radius:6px;padding:2px 7px;font-size:.72rem;font-weight:600}
.fit{background:var(--signal-soft);color:var(--signal);border-radius:6px;padding:2px 7px;font-size:.72rem;font-weight:600}
.angle{margin:6px 0 0;font:500 .95rem/1.35 var(--serif);font-style:italic;color:var(--ink)}
.angle::before{content:"Pitch idea: ";font:600 .72rem/1 var(--sans);font-style:normal;color:var(--muted);text-transform:uppercase;letter-spacing:.04em}
.streak{margin:2px 0 0;font-size:.78rem;font-weight:600;color:var(--signal)}
.tag{background:var(--tag);color:var(--ink);border-radius:6px;padding:2px 7px;font-size:.74rem;font-weight:500}
.note{color:var(--muted);font-size:.9rem;background:var(--surface);border:1px dashed var(--line);border-radius:12px;padding:14px 16px;margin:14px 0 0}
.manual{list-style:none;padding:0;margin:14px 0 0;display:grid;gap:10px}
.manual li{background:var(--surface);border:1px solid var(--line);border-radius:12px;padding:12px 16px}
.manual a{font-weight:600}
.manual span{display:block;font-size:.85rem;color:var(--muted)}
.status{list-style:none;padding:0;margin:12px 0 0;font-size:.82rem;color:var(--muted);display:grid;gap:4px}
.status li::before{content:"";display:inline-block;width:8px;height:8px;border-radius:50%;margin-right:8px;background:#3E9B6E}
.status li.off::before{background:#C9A227}
.status strong{color:var(--ink);font-weight:600;margin-right:4px}
[hidden]{display:none!important}
@media (prefers-reduced-motion:no-preference){.chip{transition:background .15s,color .15s}}
</style>
</head>
<body>
<div class="wrap">
  <div class="top">
    <h1>Daily briefing</h1>
    <p id="updated" data-iso="{{UPDATED}}">Updated {{UPDATED}}</p>
  </div>

  <nav class="chips" aria-label="Filter by topic">{{CHIPS}}</nav>

  <section class="block" id="rising">
    <h2>Rising topics</h2>
    <p class="lede">Keywords mentioned far more today than their usual daily level.</p>
    <div class="rising-list">{{RISING}}</div>
    <p class="note empty" hidden>No rising topics in this category today.</p>
  </section>

  <section class="block" id="new-terms">
    <h2>Brand-new terms</h2>
    <p class="lede">Words and phrases showing up in several places that haven’t appeared in the past two weeks. Add good ones to config.yaml to track them.</p>
    <div class="terms">{{NEWTERMS}}</div>
  </section>

  {{SECTIONS}}

  {{EXTRA}}

  <section class="block" id="manual">
    <h2>Check by hand</h2>
    <p class="lede">These sites don’t allow automatic collection. Use the buttons under each rising topic to search it directly, or browse here.</p>
    <ul class="manual">{{MANUAL}}</ul>
  </section>

  <section class="block" id="sources">
    <h2>Sources</h2>
    <ul class="status">{{STATUS}}</ul>
  </section>
</div>
<script>
(function(){
  var u=document.getElementById('updated');
  try{var d=new Date(u.dataset.iso);u.textContent='Updated '+d.toLocaleString([], {weekday:'long',month:'short',day:'numeric',hour:'numeric',minute:'2-digit'});}catch(e){}
  var chips=[].slice.call(document.querySelectorAll('.chip'));
  var newTerms=document.getElementById('new-terms');
  function apply(cat){
    chips.forEach(function(c){var on=c.dataset.cat===cat;c.classList.toggle('is-on',on);c.setAttribute('aria-pressed',on)});
    newTerms.hidden = cat!=='all';
    [].forEach.call(document.querySelectorAll('.static-block'),function(s){s.hidden=cat!=='all'});
    document.querySelectorAll('#rising, .feed').forEach(function(sec){
      var items=sec.querySelectorAll('[data-cats]'), shown=0;
      items.forEach(function(el){
        var ok=cat==='all'||el.dataset.cats.split('|').indexOf(cat)>-1;
        el.hidden=!ok; if(ok) shown++;
      });
      var empty=sec.querySelector('.empty');
      if(empty) empty.hidden = !(items.length && !shown);
      var list=sec.querySelector('.list');
      if(list) list.hidden = items.length>0 && !shown;
    });
  }
  chips.forEach(function(c){c.addEventListener('click',function(){apply(c.dataset.cat)})});
})();
</script>
</body>
</html>
"""



# ================================================================ config, state

def log(msg):
    print(msg, file=sys.stderr, flush=True)


def die(msg, code=2):
    print(msg, file=sys.stderr)
    sys.exit(code)


def load_config():
    p = ROOT / "config.yaml"
    if not p.exists():
        die(f"config.yaml not found in {ROOT}")
    cfg = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    for k in ("subreddits", "news_searches", "youtube_searches"):
        cfg.setdefault(k, [])
    cfg.setdefault("categories", {})
    cfg.setdefault("reddit_allow_without_login", False)
    sc = cfg.get("scoring") or {}
    sc.setdefault("min_score", 6)
    sc.setdefault("publications", "Verywell Health, Verywell Mind, Verywell Fit, Health.com, and Prevention")
    cfg["scoring"] = sc
    rep = cfg.get("repeats") or {}
    rep.setdefault("hide_repeats", True)
    rep.setdefault("min_new_items", 12)
    rep.setdefault("max_extra_searches", 12)
    cfg["repeats"] = rep
    b = cfg.get("briefing") or {}
    b.setdefault("news_days", 2)
    b.setdefault("results_each", 5)
    b.setdefault("feed_fetch_size", 40)
    b.setdefault("research_days", 5)
    b.setdefault("research_topics_per_run", 20)
    b.setdefault("news_topics", [])
    b.setdefault("research_topics", [])
    b.setdefault("publication_feeds", {})
    b.setdefault("excluded_outlets", [])
    cfg["briefing"] = b
    out = cfg.get("outputs") or {}
    out.setdefault("markdown", False)  # also write reports/briefing-*.md
    cfg["outputs"] = out
    global USER_AGENT
    name = re.sub(r"^/?u/", "", str(cfg.get("reddit_username") or "").strip())
    contact = os.environ.get("CONTACT_EMAIL", "")
    USER_AGENT = (f"python:content-briefing:v3 (by /u/{name})" if name else
                  f"content-briefing/3.0 (daily research tool; contact: {contact or 'none set'})")
    for w in cfg.get("extra_stopwords") or []:
        STOPWORDS.add(str(w).lower())
    return cfg


def jload(path, default):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except Exception:
        return default


def jsave(path, obj):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(obj, separators=(",", ":"), ensure_ascii=False), encoding="utf-8")


def parse_date(s):
    s = str(s or "").strip()
    if not s:
        return None
    try:
        d = parsedate_to_datetime(s)
    except Exception:
        try:
            d = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except Exception:
            return None
    if d is None:
        return None
    if d.tzinfo is None:
        d = d.replace(tzinfo=timezone.utc)
    return d


def _is_trendy_key(k):
    return k.startswith(("n:", "t:")) or "reddit.com/" in k or "youtube.com/" in k


class Seen:
    """Repeat memory shared by all three jobs. key -> first date shown.
    A key first shown today still counts as new, so re-running a report is safe."""

    def __init__(self):
        self.d = jload(SEEN_FILE, {})
        self.run = set()

    def fresh(self, key):
        key = (key or "").strip()
        return bool(key) and key not in self.run and (key not in self.d or self.d[key] >= TODAY)

    def claim(self, key):
        key = (key or "").strip()
        if key:
            self.run.add(key)
            self.d.setdefault(key, TODAY)

    def is_repeat(self, key):
        first = self.d.get(key)
        return first is not None and first < TODAY

    def save(self):
        short = (NOW - timedelta(days=TREND_KEEP_DAYS)).strftime("%Y-%m-%d")
        long_ = (NOW - timedelta(days=BRIEFING_KEEP_DAYS)).strftime("%Y-%m-%d")
        keep = {k: v for k, v in self.d.items() if v >= (short if _is_trendy_key(k) else long_)}
        if len(keep) > MAX_SEEN:
            keep = dict(sorted(keep.items(), key=lambda kv: kv[1])[-MAX_SEEN:])
        self.d = keep
        jsave(SEEN_FILE, keep)


def load_history():
    h = jload(HISTORY_FILE, None)
    return h if isinstance(h, dict) and "days" in h else {"days": {}}


def save_history(hist):
    days = hist["days"]
    for d in sorted(days)[:-HISTORY_DAYS]:
        del days[d]
    jsave(HISTORY_FILE, hist)


def load_inbox():
    ib = jload(INBOX_FILE, {})
    if ib.get("date") != TODAY:
        ib = {"date": TODAY, "sources": {}, "items": [], "scores": {}}
    ib.setdefault("scores", {})
    return ib


def save_inbox(ib):
    jsave(INBOX_FILE, ib)


# ================================================================ items

KIND_OF = {"feed": "feed", "pubmed": "pubmed", "news": "news",
           "trends": "trend", "reddit": "reddit", "youtube": "youtube"}


def norm_item(source, it):
    prefix = source.split(":", 1)[0]
    kind = KIND_OF.get(prefix)
    if not kind:
        raise ValueError(f"unknown source prefix in '{source}' (use feed:, pubmed:, news:, trends, reddit, youtube)")
    title = re.sub(r"\s+", " ", html.unescape(str(it.get("title") or ""))).strip()
    url = str(it.get("url") or it.get("link") or "").strip()
    if kind == "pubmed" and not url and it.get("pmid"):
        url = f"https://pubmed.ncbi.nlm.nih.gov/{it['pmid']}/"
    if kind == "trend" and not url and title:
        url = "https://www.google.com/search?q=" + quote_plus(title)
    if not title or not url:
        return None
    d = dict(it)
    d.update(kind=kind, title=title, url=url, source=source)
    raw_date = str(it.get("date") or it.get("pubDate") or it.get("published") or "").strip()
    dt = parse_date(raw_date)
    d["date"] = raw_date[:16].strip()
    if dt:
        d["published"] = dt.isoformat()
    age = max((NOW - dt).total_seconds() / 3600, 0) if dt else 0.0
    d["age_h"] = float(it["age_h"]) if it.get("age_h") is not None else age
    d["text"] = str(it.get("text") or title)
    rest = source.split(":", 1)[1] if ":" in source else ""
    if kind == "feed":
        d["outlet"] = rest
    elif kind == "pubmed":
        d["topic"] = rest
        d["journal"] = str(it.get("journal") or "")
    elif kind == "news":
        where = str(it.get("where") or it.get("outlet") or "").strip()
        if where and title.endswith(" - " + where):
            d["title"] = title[: -(len(where) + 3)].strip()
            d["text"] = d["title"]
        d["where"] = where or "News"
        d["dug"] = rest.startswith("dig:")
    elif kind == "trend":
        traffic = str(it.get("traffic") or "").strip()
        d["where"] = d.get("where") or (traffic + " searches" if traffic else "Google Trends")
        d["news"] = [n for n in (it.get("news") or []) if isinstance(n, dict) and n.get("title") and n.get("url")][:3]
        for n in d["news"]:
            n.setdefault("source", "")
        d["text"] = title + " " + " ".join(n["title"] for n in d["news"])
    elif kind == "reddit":
        d["where"] = d.get("where") or "Reddit"
        d["score"] = int(it.get("score") or 0)
        d["comments"] = int(it.get("comments") or 0)
        d["velocity"] = float(it.get("velocity") or 0)
        d["rank"] = float(it.get("rank") or d["velocity"])
    elif kind == "youtube":
        d["where"] = d.get("where") or "YouTube"
        d["views"] = int(it.get("views") or 0)
        d["velocity"] = float(it.get("velocity") or 0)
        d["short"] = bool(it.get("short"))
    return d


def add_batch(ib, batch):
    src = str(batch.get("source") or "").strip()
    if not src:
        raise ValueError("batch is missing 'source'")
    items = []
    for raw in batch.get("items") or []:
        n = norm_item(src, raw)
        if n:
            items.append(n)
    ib["items"] = [i for i in ib["items"] if i["source"] != src] + items
    ib["sources"][src] = {"ok": bool(batch.get("ok", True)), "msg": str(batch.get("msg") or ""), "n": len(items)}
    return len(items)


# ================================================================ plan

def base_domain(host):
    parts = host.lower().split(":")[0].split(".")
    if len(parts) >= 3 and len(parts[-1]) == 2 and parts[-2] in ("co", "com", "org", "gov", "ac"):
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def rotating_slice(items, start, count):
    n = len(items)
    if n == 0 or count >= n:
        return list(items), 0
    start %= n
    end = start + count
    chunk = items[start:end] if end <= n else items[start:] + items[: end - n]
    return chunk, end % n


def gnews_url(q, window="3d"):
    return ("https://news.google.com/rss/search?q=" + quote_plus(f"{q} when:{window}")
            + "&hl=en-US&gl=US&ceid=US:en")


def esearch_params(topic, days, email=""):
    p = {"db": "pubmed", "term": topic, "reldate": days, "datetype": "pdat",
         "retmax": 15, "retmode": "json", "sort": "date", "tool": "daily_content_briefing"}
    if email:
        p["email"] = email
    return p


def make_plan(cfg, job):
    b = cfg["briefing"]
    tasks, plan_state = [], {"date": TODAY}
    if job in ("feeds", "all"):
        for outlet, url in b["publication_feeds"].items():
            tasks.append({"source": f"feed:{outlet}", "job": "feeds", "url": url,
                          "search": {"query": f"{outlet} health news",
                                     "allowed_domains": [base_domain(urlparse(url).netloc)]}})
    if job in ("research", "all"):
        cur = jload(CURSOR_FILE, {}).get("research", 0)
        topics, nxt = rotating_slice(b["research_topics"], cur, b["research_topics_per_run"])
        plan_state["research"] = {"topics": topics, "cursor": cur, "next": nxt}
        for t in topics:
            tasks.append({"source": f"pubmed:{t}", "job": "research",
                          "url": "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?"
                                 + "&".join(f"{k}={quote_plus(str(v))}" for k, v in
                                            esearch_params(t, b["research_days"]).items()),
                          "search": {"query": t, "allowed_domains": ["pubmed.ncbi.nlm.nih.gov"],
                                     "recency": f"published in the last {b['research_days']} days"}})
    if job in ("trends", "all"):
        for q in cfg["news_searches"]:
            tasks.append({"source": f"news:{q}", "job": "trends", "url": gnews_url(q),
                          "search": {"query": q, "recency": "last 3 days"}})
        tasks.append({"source": "trends", "job": "trends",
                      "url": "https://trends.google.com/trending/rss?geo=US", "search": None})
    old = jload(PLAN_FILE, {})
    if old.get("date") == TODAY:
        for k, v in old.items():
            plan_state.setdefault(k, v)
    jsave(PLAN_FILE, plan_state)
    return tasks


# ================================================================ live collection (needs open network)

MIN_DELAY = {"www.reddit.com": 7.0, "oauth.reddit.com": 1.2, "news.google.com": 3.0,
             "trends.google.com": 3.0, "www.googleapis.com": 0.5, "eutils.ncbi.nlm.nih.gov": 0.4}
MAX_RETRY_WAIT = 120
_last_request = {}
_robots_cache = {}


class RateLimited(Exception):
    pass


def _wait_turn(host):
    gap = MIN_DELAY.get(host, 1.0)
    elapsed = time.monotonic() - _last_request.get(host, 0)
    if elapsed < gap:
        time.sleep(gap - elapsed + random.uniform(0, gap * 0.25))
    _last_request[host] = time.monotonic()


def http_get(url, retries=2, **kwargs):
    if requests is None:
        die("`collect` needs the requests package (pip install requests)")
    headers = kwargs.pop("headers", {})
    headers.setdefault("User-Agent", USER_AGENT)
    host = urlparse(url).netloc
    for attempt in range(retries + 1):
        _wait_turn(host)
        r = requests.get(url, headers=headers, timeout=25, **kwargs)
        if r.status_code not in (429, 503):
            return r
        ra = r.headers.get("Retry-After", "")
        wait = int(ra) if ra.isdigit() else 15 * (2 ** attempt)
        if attempt == retries or wait > MAX_RETRY_WAIT:
            raise RateLimited(f"{host} asked us to slow down (HTTP {r.status_code})")
        log(f"{host} returned {r.status_code}; waiting {wait}s")
        time.sleep(wait)
    raise RateLimited(host)


def _fetch_robots_text(origin):
    if origin in _robots_cache:
        return _robots_cache[origin]
    text = None
    try:
        r = requests.get(f"{origin}/robots.txt", timeout=10, headers={"User-Agent": USER_AGENT})
        if r.status_code == 200:
            text = r.text
        elif r.status_code == 404:
            text = ""
    except Exception:
        text = None
    _robots_cache[origin] = text
    return text


def _parse_robots(text):
    groups, agents, rules, started = [], [], [], False
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line or ":" not in line:
            continue
        field, _, value = line.partition(":")
        field, value = field.strip().lower(), value.strip()
        if field == "user-agent":
            if started:
                if agents:
                    groups.append((agents, rules))
                agents, rules, started = [], [], False
            agents.append(value.lower())
        elif field in ("allow", "disallow"):
            started = True
            if value:
                rules.append((field == "allow", value))
    if agents:
        groups.append((agents, rules))
    return groups


def _pattern_to_regex(pattern):
    escaped = re.escape(pattern).replace(r"\*", ".*")
    if escaped.endswith(r"\$"):
        escaped = escaped[:-2] + "$"
    return "^" + escaped


def _select_group(groups, user_agent):
    ua = user_agent.lower()
    named, wildcard = None, None
    for agents, rules in groups:
        for a in agents:
            if a == "*":
                wildcard = rules
            elif a in ua and (named is None or len(a) > named[0]):
                named = (len(a), rules)
    return named[1] if named else (wildcard or [])


def robots_allowed(url, user_agent):
    parts = urlsplit(url)
    text = _fetch_robots_text(f"{parts.scheme}://{parts.netloc}")
    if not text:
        return True
    path = (parts.path or "/") + (("?" + parts.query) if parts.query else "")
    best = None
    for is_allow, pattern in _select_group(_parse_robots(text), user_agent):
        if re.match(_pattern_to_regex(pattern), path) and (best is None or len(pattern) > best[0]):
            best = (len(pattern), is_allow)
    return True if best is None else best[1]


def rss_items(content, how_many):
    out = []
    for it in ET.fromstring(content).iter("item"):
        out.append({"title": child_text(it, "title"), "url": child_text(it, "link"),
                    "date": child_text(it, "pubDate"), "where": child_text(it, "source")})
        if len(out) >= how_many:
            break
    return out


def live_feed(outlet, url, n):
    src = f"feed:{outlet}"
    if not robots_allowed(url, USER_AGENT):
        return {"source": src, "ok": False, "msg": "robots.txt disallows", "items": []}
    try:
        r = http_get(url)
        r.raise_for_status()
        return {"source": src, "ok": True, "items": rss_items(r.content, n)}
    except Exception as e:
        return {"source": src, "ok": False, "msg": str(e), "items": []}


def live_pubmed(topic, days):
    email = os.environ.get("CONTACT_EMAIL", "")
    base = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    src = f"pubmed:{topic}"
    try:
        r = http_get(base + "esearch.fcgi", params=esearch_params(topic, days, email))
        r.raise_for_status()
        ids = r.json().get("esearchresult", {}).get("idlist", [])
        items = []
        if ids:
            sp = {"db": "pubmed", "id": ",".join(ids), "retmode": "json", "tool": "daily_content_briefing"}
            if email:
                sp["email"] = email
            s = http_get(base + "esummary.fcgi", params=sp)
            s.raise_for_status()
            res = s.json().get("result", {})
            for pmid in ids:
                info = res.get(pmid, {})
                items.append({"pmid": pmid, "title": info.get("title", ""),
                              "journal": info.get("fulljournalname", ""), "date": info.get("pubdate", "")})
        return {"source": src, "ok": True, "items": items}
    except Exception as e:
        return {"source": src, "ok": False, "msg": str(e), "items": []}


def live_news(q, window="3d"):
    src = f"news:{q}"
    try:
        r = http_get(gnews_url(q, window))
        r.raise_for_status()
        return {"source": src, "ok": True, "items": rss_items(r.content, 100)}
    except Exception as e:
        return {"source": src, "ok": False, "msg": str(e), "items": []}


def live_trends():
    try:
        r = http_get("https://trends.google.com/trending/rss?geo=US")
        r.raise_for_status()
        items = []
        for it in ET.fromstring(r.content).iter("item"):
            items.append({
                "title": child_text(it, "title"), "traffic": child_text(it, "approx_traffic"),
                "news": [{"title": html.unescape(child_text(n, "news_item_title")),
                          "url": child_text(n, "news_item_url"), "source": child_text(n, "news_item_source")}
                         for n in children(it, "news_item")]})
        return {"source": "trends", "ok": True, "items": items}
    except Exception as e:
        return {"source": "trends", "ok": False, "msg": str(e), "items": []}


def live_reddit(cfg):
    cid, secret = os.environ.get("REDDIT_CLIENT_ID"), os.environ.get("REDDIT_CLIENT_SECRET")
    subs = cfg["subreddits"]
    token = None
    if cid and secret:
        try:
            r = requests.post("https://www.reddit.com/api/v1/access_token", auth=(cid, secret),
                              data={"grant_type": "client_credentials"},
                              headers={"User-Agent": USER_AGENT}, timeout=25)
            r.raise_for_status()
            token = r.json().get("access_token")
        except Exception as e:
            log(f"Reddit login failed: {e}")
    if token:
        base, headers = "https://oauth.reddit.com", {"Authorization": f"bearer {token}"}
    elif cfg["reddit_allow_without_login"]:
        base, headers = "https://www.reddit.com", {}
    else:
        return {"source": "reddit", "ok": False, "msg": "Off. Add Reddit API keys to turn on.", "items": []}
    posts, stopped = [], None
    for sub in subs:
        try:
            r = http_get(f"{base}/r/{sub}/rising.json?limit=25&raw_json=1", headers=dict(headers))
            rem, reset = r.headers.get("X-Ratelimit-Remaining"), r.headers.get("X-Ratelimit-Reset")
            if rem and reset:
                try:
                    if float(rem) < 5:
                        time.sleep(min(float(reset) + 1, MAX_RETRY_WAIT))
                except ValueError:
                    pass
            if r.status_code in (401, 403):
                stopped = "Reddit refused access. Check your Reddit API keys."
                break
            if r.status_code == 404:
                continue
            r.raise_for_status()
            for ch in r.json().get("data", {}).get("children", []):
                d = ch.get("data", {})
                if d.get("over_18") or d.get("stickied"):
                    continue
                age_h = max((NOW.timestamp() - (d.get("created_utc") or 0)) / 3600, 0.5)
                score, comments = int(d.get("score") or 0), int(d.get("num_comments") or 0)
                if score < 5 and comments < 5:
                    continue
                subs_count = int(d.get("subreddit_subscribers") or 10000)
                vel = (score + 2 * comments) / age_h
                posts.append({"title": d.get("title", ""),
                              "text": d.get("title", "") + " " + (d.get("selftext") or "")[:500],
                              "url": "https://www.reddit.com" + d.get("permalink", ""),
                              "where": "r/" + d.get("subreddit", sub), "score": score, "comments": comments,
                              "age_h": age_h, "velocity": vel,
                              "rank": vel / math.sqrt(max(subs_count, 10000) / 10000)})
        except RateLimited as e:
            stopped = "Reddit asked us to slow down, so collection stopped early."
            log(str(e))
            break
        except Exception as e:
            log(f"Reddit r/{sub}: {e}")
    if not posts:
        return {"source": "reddit", "ok": False, "msg": stopped or "No Reddit posts came back.", "items": []}
    return {"source": "reddit", "ok": True, "items": posts, "msg": stopped or ""}


def live_youtube(cfg):
    key = os.environ.get("YOUTUBE_API_KEY")
    if not key:
        return {"source": "youtube", "ok": False, "msg": "Off. Set YOUTUBE_API_KEY to turn on.", "items": []}
    after = (NOW - timedelta(days=3)).strftime("%Y-%m-%dT%H:%M:%SZ")
    ids, short_ids = [], set()
    for duration in ("any", "short"):
        for q in cfg["youtube_searches"]:
            try:
                r = http_get("https://www.googleapis.com/youtube/v3/search", params={
                    "part": "snippet", "q": q, "type": "video", "order": "viewCount", "publishedAfter": after,
                    "maxResults": 10, "regionCode": "US", "relevanceLanguage": "en",
                    "videoDuration": duration, "key": key})
                r.raise_for_status()
                for it in r.json().get("items", []):
                    vid = it.get("id", {}).get("videoId")
                    if vid:
                        if duration == "short":
                            short_ids.add(vid)
                        if vid not in ids:
                            ids.append(vid)
            except RateLimited:
                break
            except Exception as e:
                log(f"YouTube '{q}': {e}")
    videos = []
    for i in range(0, len(ids), 50):
        try:
            r = http_get("https://www.googleapis.com/youtube/v3/videos",
                         params={"part": "snippet,statistics", "id": ",".join(ids[i:i + 50]), "key": key})
            r.raise_for_status()
            for v in r.json().get("items", []):
                sn, st = v.get("snippet", {}), v.get("statistics", {})
                pub = datetime.fromisoformat(sn.get("publishedAt", NOW.isoformat()).replace("Z", "+00:00"))
                age_h = max((NOW - pub).total_seconds() / 3600, 1)
                views = int(st.get("viewCount") or 0)
                videos.append({"title": html.unescape(sn.get("title", "")),
                               "text": html.unescape(sn.get("title", "") + " " + (sn.get("description") or "")[:300]),
                               "url": f"https://www.youtube.com/watch?v={v['id']}", "where": sn.get("channelTitle", "YouTube"),
                               "views": views, "age_h": age_h, "velocity": views / age_h, "short": v["id"] in short_ids})
        except Exception as e:
            log(f"YouTube stats: {e}")
    if not videos:
        return {"source": "youtube", "ok": False, "msg": "YouTube returned nothing. Check the API key.", "items": []}
    return {"source": "youtube", "ok": True, "items": videos}


def collect_live(cfg, job):
    b = cfg["briefing"]
    batches = []
    if job in ("feeds", "all"):
        log("Fetching publication feeds...")
        for outlet, url in b["publication_feeds"].items():
            batches.append(live_feed(outlet, url, b["feed_fetch_size"]))
            time.sleep(0.5)
    if job in ("research", "all"):
        log("Checking PubMed...")
        make_plan(cfg, "research")
        for t in jload(PLAN_FILE, {}).get("research", {}).get("topics", []):
            batches.append(live_pubmed(t, b["research_days"]))
    if job in ("trends", "all"):
        log("Collecting Reddit, Google News, Google Trends, YouTube...")
        batches.append(live_reddit(cfg))
        for q in cfg["news_searches"]:
            batches.append(live_news(q))
        batches.append(live_trends())
        batches.append(live_youtube(cfg))
    return batches


# ================================================================ reports: feeds + research

def _topic_match_term(topic):
    lower = topic.lower()
    for suffix in (" trend", " study", " warning", " research", " misinformation"):
        if lower.endswith(suffix):
            return lower[: -len(suffix)].strip()
    return lower


def news_block(lines, articles, ok, limit, seen, excluded, sink=None):
    shown = 0
    for title, link, date in articles:
        if any(bad.lower() in (title + " " + link).lower() for bad in excluded):
            continue
        if seen.fresh(link):
            seen.claim(link)
            lines.append(f"- [{title}]({link})" + (f" — {date}" if date else ""))
            if sink is not None:
                sink.append([title, link, date])
            shown += 1
        if shown >= limit:
            break
    if shown == 0:
        lines.append(EMPTY if ok else BLOCKED)
    lines.append("")
    return shown > 0


def report_feeds(cfg, ib, seen):
    b = cfg["briefing"]
    feeds = b["publication_feeds"]
    ex, lim, days = b["excluded_outlets"], b["results_each"], b["news_days"]
    pool = [(i["title"], i["url"], i["date"], i.get("outlet", "")) for i in ib["items"] if i["kind"] == "feed"]
    status = {o: ib["sources"].get(f"feed:{o}", {}).get("ok", False) for o in feeds}
    part = {"days": days, "signals": [], "outlets": [], "topics": [], "topics_total": len(b["news_topics"])}
    lines = [f"# Daily Content Briefing — {TODAY}", "", "_Everything below is new since your last briefing._", "",
             "## Rising Signals", "",
             "For live TikTok hashtag data (no scraping, official free tool): "
             "https://ads.tiktok.com/business/creativecenter/inspiration/popular/hashtag "
             "— industry filter *Health*, period *Last 7 days*.", "",
             "For live Google search-spike data: https://trends.google.com/trending "
             "— select category *Health*, compare 24-hour and 7-day growth.", "",
             f"New coverage using viral/trend language (last {days * 24} hours):"]
    words = ("tiktok", "viral", "trend", "hack", "challenge", "doctors warn", "dietitians warn",
             "everyone is", "why is everyone")
    news_block(lines, [(t, l, d) for t, l, d, o in pool if any(w in t.lower() for w in words)],
               True, lim * 2, seen, ex, part["signals"])
    lines += [f"## New From Health Publications (last {days * 24} hours)", ""]
    for outlet in feeds:
        lines.append(f"**{outlet}**")
        sink = []
        news_block(lines, [(t, l, d) for t, l, d, o in pool if o == outlet], status.get(outlet, False),
                   lim, seen, ex, sink)
        part["outlets"].append({"name": outlet, "ok": bool(status.get(outlet, False)), "items": sink})
    lines += [f"## Trending News, Outbreaks & Recalls (last {days * 24} hours)", ""]
    hits = 0
    for topic in b["news_topics"]:
        term = _topic_match_term(topic)
        matched = [(t, l, d) for t, l, d, o in pool if term in t.lower() and seen.fresh(l)]
        if not matched:
            continue
        lines.append(f"**{topic.title()}**")
        sink = []
        if news_block(lines, matched, True, lim, seen, ex, sink):
            hits += 1
            part["topics"].append({"topic": topic, "items": sink})
    lines += [f"_{hits} of {len(b['news_topics'])} topics had new matches today "
              f"(the rest are omitted rather than listed as empty)._", ""]
    summary = {"job": "feeds", "feeds_ok": sum(status.values()), "feeds_total": len(feeds), "topics_with_hits": hits}
    if cfg["outputs"]["markdown"]:
        REPORTS.mkdir(parents=True, exist_ok=True)
        out = REPORTS / f"briefing-feeds-{TODAY}.md"
        out.write_text("\n".join(lines), encoding="utf-8")
        summary["file"] = str(out.relative_to(ROOT))
    return summary, part


def report_research(cfg, ib, seen):
    b = cfg["briefing"]
    topics_all = b["research_topics"]
    plan = jload(PLAN_FILE, {})
    rs = plan.get("research") if plan.get("date") == TODAY else None
    if not rs:
        cur = jload(CURSOR_FILE, {}).get("research", 0)
        topics, nxt = rotating_slice(topics_all, cur, b["research_topics_per_run"])
        rs = {"topics": topics, "cursor": cur, "next": nxt}
    topics, cur, nxt = rs["topics"], rs["cursor"], rs["next"]
    lim, days = b["results_each"], b["research_days"]
    lines = [f"# Daily Content Briefing — {TODAY}", "", "_Everything below is new since your last briefing._", "",
             f"## Medical Research Published in the Last {days} Days", ""]
    part = {"days": days, "topics": []}
    with_hits = 0
    for topic in topics:
        src = ib["sources"].get(f"pubmed:{topic}")
        if src is None:
            continue  # never gathered; leave it out rather than claim a failure
        out, rows = [], []
        for it in ib["items"]:
            if it["source"] != f"pubmed:{topic}" or not seen.fresh(it["url"]):
                continue
            seen.claim(it["url"])
            out.append(f"- [{it['title']}]({it['url']}) — {it.get('journal', '')}, {it.get('date', '')}")
            rows.append([it["title"], it["url"], it.get("journal", ""), it.get("date", "")])
            if len(out) >= lim:
                break
        if out:
            lines += [f"**{topic.title()}**"] + out + [""]
            part["topics"].append({"topic": topic, "failed": False, "items": rows})
            with_hits += 1
        elif not src["ok"]:
            lines += [f"**{topic.title()}**", BLOCKED, ""]
            part["topics"].append({"topic": topic, "failed": True, "items": []})
    gathered = sum(1 for t in topics if f"pubmed:{t}" in ib["sources"])
    total_t = len(topics_all)
    span = (f"{cur + 1}-{cur + len(topics)}" if cur + len(topics) <= total_t
            else f"{cur + 1}-{total_t} and 1-{cur + len(topics) - total_t}")
    cycle = -(-total_t // b["research_topics_per_run"]) if b["research_topics_per_run"] else 1
    footer = (f"{with_hits} of {len(topics)} queried research topics had new results today "
              f"(the rest are omitted rather than listed as empty). This run covered topics {span} of {total_t} "
              f"(rotates each run, full cycle takes about {cycle} runs); next run starts at topic {nxt + 1}.")
    lines += [f"_{footer}_", ""]
    part["footer"] = footer
    summary = {"job": "research", "topics_gathered": gathered, "topics_planned": len(topics),
               "topics_with_hits": with_hits, "cursor_advanced": bool(gathered)}
    if cfg["outputs"]["markdown"]:
        REPORTS.mkdir(parents=True, exist_ok=True)
        out_path = REPORTS / f"briefing-research-{TODAY}.md"
        out_path.write_text("\n".join(lines), encoding="utf-8")
        summary["file"] = str(out_path.relative_to(ROOT))
    cursors = jload(CURSOR_FILE, {})
    if gathered:  # only advance the rotation if something was actually gathered
        cursors["research"] = nxt
        jsave(CURSOR_FILE, cursors)
    return summary, part


# ================================================================ reports: trends

DIG = {}  # set by report_trends when extra searches are needed


def tag_kind(items, tagger):
    for it in items:
        it["cats"] = tagger.match(it["text"])[1]


def build_trend_results(cfg, tagger, ib):
    """Raw inbox items -> the same four result groups the dashboard always used."""
    srcs = ib["sources"]
    by = defaultdict(list)
    for it in ib["items"]:
        by[it["kind"]].append(it)

    def src_msgs(prefix):
        return [(k, v) for k, v in srcs.items() if k == prefix or k.startswith(prefix + ":")]

    # news
    seen_keys, news, dropped = set(), [], 0
    for it in sorted(by["news"], key=lambda x: (bool(x.get("dug")), x["age_h"])):
        k = news_key(it["title"])
        if k == "n:" or k in seen_keys:
            continue
        seen_keys.add(k)
        if not tagger.match(it["title"])[0] and not tagger.is_health(it["title"]):
            dropped += 1
            continue
        news.append(it)
    base_news = [n for n in news if not n.get("dug")][:60]
    dug_news = [n for n in news if n.get("dug")][:40]
    nsrc = [(k, v) for k, v in src_msgs("news") if not k.startswith("news:dig:")]
    errors = sum(1 for _, v in nsrc if not v["ok"])
    if base_news:
        msg = f"{len(base_news)} health headlines ({dropped} off-topic skipped)"
        msg += f" ({errors} searches failed)" if errors else ""
        news_status = {"ok": True, "msg": msg}
    else:
        news_status = {"ok": False, "msg": "Google News returned nothing." if nsrc else
                       "No news searches were gathered."}

    # trends
    trends, total = [], 0
    for it in by["trend"]:
        total += 1
        if tagger.is_health(it["text"]):
            trends.append(it)
    if "trends" in srcs and srcs["trends"]["ok"]:
        trend_status = {"ok": True, "msg": f"{len(trends)} health-related of {total} trending searches"}
    else:
        trend_status = {"ok": False, "msg": srcs.get("trends", {}).get("msg") or
                        "Google Trends was not gathered (needs direct network access)."}

    # reddit
    posts = sorted(by["reddit"], key=lambda p: p["rank"], reverse=True)
    per_sub, kept = Counter(), []
    for p in posts:
        if per_sub[p["where"]] < 3:
            kept.append(p)
            per_sub[p["where"]] += 1
    kept = kept[:45]
    rs = srcs.get("reddit")
    if kept:
        reddit_status = {"ok": True, "msg": f"{len(posts)} rising posts from {len({p['where'] for p in posts})} "
                                            f"subreddits" + (". " + rs["msg"] if rs and rs.get("msg") else "")}
    else:
        reddit_status = {"ok": False, "msg": (rs or {}).get("msg") or "Off. Needs Reddit API keys and direct network access."}

    # youtube
    vids = sorted(by["youtube"], key=lambda v: v["velocity"], reverse=True)
    longs = [v for v in vids if not v["short"]][:30]
    shorts = [v for v in vids if v["short"]][:30]
    ys = srcs.get("youtube")
    if vids:
        yt_status = {"ok": True, "msg": f"{len(longs)} videos and {len(shorts)} short videos"}
    else:
        yt_status = {"ok": False, "msg": (ys or {}).get("msg") or "Off. Needs YOUTUBE_API_KEY and direct network access."}

    results = {"reddit": (kept, reddit_status), "news": (base_news, news_status),
               "trends": (trends, trend_status), "youtube": (longs + shorts, yt_status)}
    return results, dug_news


def apply_scores(items, ib):
    n = 0
    for it in items:
        s = ib["scores"].get(item_key(it))
        if s:
            it["fit"] = max(0, min(10, int(s.get("score", 0))))
            it["angle"] = str(s.get("angle") or "").strip()[:140]
            n += 1
    return n


def keep_relevant(items, min_score):
    return [it for it in items if it.get("fit") is None or it["fit"] >= min_score]


def report_trends(cfg, ib, seen, no_dig=False):
    tagger = Tagger(cfg["categories"])
    kw_category = {}
    for cat, kws in cfg["categories"].items():
        for kw in kws or []:
            kw_category.setdefault(str(kw).lower(), cat)
    ms, rep = cfg["scoring"]["min_score"], cfg["repeats"]

    results, dug_news = build_trend_results(cfg, tagger, ib)
    total_items = sum(len(v[0]) for v in results.values()) + len(dug_news)
    scored = sum(apply_scores(v[0], ib) for v in results.values()) + apply_scores(dug_news, ib)
    ai_status = ({"ok": True, "msg": f"Claude scored {scored} of {total_items} items; "
                                     f"showing those rated {ms}+ out of 10"} if scored else
                 {"ok": False, "msg": "Not scored, so nothing was filtered for relevance."})
    results = {k: (keep_relevant(v[0], ms), v[1]) for k, v in results.items()}
    dug_news = keep_relevant(dug_news, ms)
    results["news"][0].sort(key=lambda n: (-(n.get("fit") or 0), n["age_h"]))

    all_items = [it for k in ("reddit", "news", "trends", "youtube") for it in results[k][0]]
    hist = load_history()
    rising, new_terms, n_base = analyze(all_items, tagger, hist, kw_category)

    repeat_status = None
    if rep["hide_repeats"]:
        hidden = 0
        for k in ("reddit", "news", "trends", "youtube"):
            items, st = results[k]
            fresh = [it for it in items if not seen.is_repeat(item_key(it))]
            hidden += len(items) - len(fresh)
            results[k] = (fresh, st)
        exclude = set(seen.d) | {item_key(it) for k in results for it in results[k][0]}
        dug_done = any(k.startswith("news:dig:") for k in ib["sources"])
        need = rep["min_new_items"] - len(results["news"][0])
        if need > 0 and rep["max_extra_searches"] > 0 and not dug_done and not no_dig:
            queries = dig_queries(cfg, rising, rep["max_extra_searches"])
            if queries:
                DIG.clear()
                DIG.update({
                    "status": "need_dig", "reason": f"only {len(results['news'][0])} new headlines "
                                                    f"(want {rep['min_new_items']})",
                    "next": "gather these like any news source, ingest with source news:dig:<query>, "
                            "run leads/scores, then run report again (or pass --no-dig to skip)",
                    "tasks": [{"source": f"news:dig:{q}", "job": "trends", "url": gnews_url(q, "2d"),
                               "search": {"query": q, "recency": "last 2 days"}} for q in queries]})
                return None
        extra, seen_in_extra = [], set()
        for it in dug_news:
            k = item_key(it)
            if k in exclude or k in seen_in_extra or seen.is_repeat(k):
                continue
            seen_in_extra.add(k)
            extra.append(it)
        tag_kind(extra, tagger)
        if extra:
            merged = results["news"][0] + extra
            merged.sort(key=lambda n: (-(n.get("fit") or 0), n["age_h"]))
            results["news"] = (merged, results["news"][1])
        msg = f"{hidden} items already shown on earlier days were hidden"
        if dug_done:
            msg += f"; extra searches found {len(extra)} new items"
        repeat_status = {"ok": True, "msg": msg}

    if all_items:
        save_history(hist)
    for k in results:
        for it in results[k][0]:
            seen.claim(item_key(it))
    shown = sum(len(results[k][0]) for k in results)

    if not all_items and not shown:
        return {"job": "trends", "error": "No trend data collected from any source.", "shown": 0}, None
    part = {"results": {k: [v[0], v[1]] for k, v in results.items()}, "rising": rising, "new_terms": new_terms,
            "n_base": n_base, "ai_status": ai_status, "repeat_status": repeat_status}
    return ({"job": "trends", "shown": shown, "rising": len(rising), "new_terms": len(new_terms),
             "baseline_days": n_base, "sources": {k: v[1]["msg"] for k, v in results.items()}}, part)


# ================================================================ combined dashboard

PARTS_FILE = STATE / "parts.json"


def feed_section(sid, title, desc, rows, empty_msg, extra_note=""):
    body = f'<ol class="list">{rows}</ol>' if rows else f'<p class="note">{esc(empty_msg)}</p>'
    return (f'<section id="{sid}" class="feed"><header><h2>{title}</h2><p>{desc}</p></header>{body}{extra_note}'
            '<p class="note empty" hidden>Nothing in this category here today.</p></section>')


def item_row(tagger, title, url, bits, plats=(), cats_text=None):
    cats = tagger.match(cats_text or title)[1]
    meta = ("".join(f'<span class="plat">{p}</span>' for p in plats)
            + "".join(f"<span>{esc(x)}</span>" for x in bits if x) + tag_list(cats))
    return (f'<li class="item" data-cats="{cats_attr(cats)}"><a href="{esc(url)}" target="_blank" rel="noopener">'
            f'{esc(title)}</a><div class="meta">{meta}</div></li>'), cats


def feeds_html(part, tagger):
    rows, cats, seen_urls, down = [], set(), set(), []

    def add(t, u, bits, plats=()):
        if u in seen_urls:
            return
        seen_urls.add(u)
        r, c = item_row(tagger, t, u, bits, plats)
        rows.append(r)
        cats.update(c or ["Other"])

    for t, u, d in part["signals"]:
        add(t, u, [d], platforms_in(t))
    for o in part["outlets"]:
        for t, u, d in o["items"]:
            add(t, u, [o["name"], d], platforms_in(t))
        if not o["items"] and not o["ok"]:
            down.append(o["name"])
    for tp in part["topics"]:
        for t, u, d in tp["items"]:
            add(t, u, [d], platforms_in(t))
    note = f'<p class="note">Not reachable this run: {esc(", ".join(down))}.</p>' if down else ""
    html_ = feed_section("publications", "New from health publications",
                         f'Articles from the last {part["days"] * 24} hours that you have not seen before.',
                         "".join(rows), "Nothing new from the publication feeds today.", note)
    return html_, cats


def research_html(part, tagger):
    rows, cats, down = [], set(), []
    for tp in part["topics"]:
        if tp["failed"]:
            down.append(tp["topic"].title())
        for t, u, j, d in tp["items"]:
            r, c = item_row(tagger, t, u, [tp["topic"].title(), j, d], cats_text=t + " " + tp["topic"])
            rows.append(r)
            cats.update(c or ["Other"])
    note = f'<p class="note">{esc(part.get("footer", ""))}</p>'
    if down:
        note += f'<p class="note">Not reachable this run: {esc(", ".join(down))}.</p>'
    html_ = feed_section("research", "New medical research",
                         f'PubMed studies published in the last {part["days"]} days, rotating through the topic list.',
                         "".join(rows), "No new research in today's topics.", note)
    return html_, cats


def build_dashboard(cfg, parts):
    t = parts.get("trends")
    if t:
        results = {k: (v[0], v[1]) for k, v in t["results"].items()}
        rising, new_terms, n_base = t["rising"], t["new_terms"], t["n_base"]
        ai_status, repeat_status = t["ai_status"], t["repeat_status"]
    else:
        off = {"ok": False, "msg": "Trend job has not run today."}
        results = {k: ([], off) for k in ("reddit", "news", "trends", "youtube")}
        rising, new_terms, n_base, ai_status, repeat_status = [], [], 0, None, None
    tagger = Tagger(cfg["categories"])
    extra, extra_cats = "", set()
    if parts.get("feeds"):
        h_, c_ = feeds_html(parts["feeds"], tagger)
        extra += h_
        extra_cats |= c_
    if parts.get("research"):
        h_, c_ = research_html(parts["research"], tagger)
        extra += h_
        extra_cats |= c_
    page = render(cfg, results, rising, new_terms, n_base, ai_status, repeat_status,
                  extra_html=extra, have_trends=bool(t), extra_cats=extra_cats)
    DOCS_DIR.mkdir(exist_ok=True)
    (DOCS_DIR / "index.html").write_text(page, encoding="utf-8")
    daily = DOCS_DIR / "daily"
    daily.mkdir(exist_ok=True)
    name = f"daily-{TODAY}.html"
    (daily / name).write_text(page, encoding="utf-8")
    for old in sorted(daily.glob("*.html"))[:-ARCHIVE_DAYS]:
        old.unlink()
    return "docs/index.html"


# ================================================================ commands

def read_json_arg(arg):
    try:
        return json.load(sys.stdin if arg == "-" else open(arg, encoding="utf-8"))
    except Exception as e:
        die(f"could not read JSON from {arg}: {e}")


def cmd_plan(cfg, a):
    tasks = make_plan(cfg, a.job)
    print(json.dumps({"date": TODAY, "job": a.job, "count": len(tasks), "tasks": tasks}, indent=1))


def cmd_collect(cfg, a):
    ib = load_inbox()
    batches = collect_live(cfg, a.job)
    for b in batches:
        add_batch(ib, b)
    save_inbox(ib)
    ok = sum(1 for b in batches if b["ok"])
    print(json.dumps({"collected": len(batches), "ok": ok, "failed": len(batches) - ok,
                      "failed_sources": [b["source"] for b in batches if not b["ok"]][:20]}))
    if batches and not ok:
        die("every source failed; network is probably restricted. Use `plan` and `ingest` instead.")


def cmd_ingest(cfg, a):
    payload = read_json_arg(a.file)
    batches = payload if isinstance(payload, list) else [payload]
    ib = load_inbox()
    total = 0
    for b in batches:
        try:
            total += add_batch(ib, b)
        except ValueError as e:
            die(str(e))
    save_inbox(ib)
    print(json.dumps({"batches": len(batches), "items": total, "inbox_sources": len(ib["sources"])}))


def lead_pool(cfg, ib):
    tagger = Tagger(cfg["categories"])
    results, dug = build_trend_results(cfg, tagger, ib)
    items = [it for k in ("reddit", "news", "trends", "youtube") for it in results[k][0]] + dug
    return items


RUBRIC = """Score each lead 0-10 for how likely it could become a timely article for {pubs}.
These publications cover evidence-based consumer health for a general audience: health conditions, symptoms and
treatments, medications and supplements, nutrition, fitness, sleep, mental health, skin and hair through a health
lens, women's and men's health, pregnancy and children's health, aging, and viral wellness trends or health claims
that readers want explained or fact-checked.
9-10: a new or fast-spreading health or wellness trend, claim, or reader question with a clear expert-explainer
      angle (for example, a viral TikTok remedy doctors are weighing in on).
7-8:  clearly relevant and timely consumer health news or discussion.
4-6:  health-adjacent but weak, too niche, too clinical, or already old news.
0-3:  not a fit: politics or policy without direct reader health impact, business, stocks, lawsuits, platform bans,
      celebrity gossip without a health angle, sports results, tech, fashion, product deals, crime, or local news.
"angle": one short article headline idea (under 14 words) if score >= 6, else "". Judge only the text given.
Return every id as [{"id": 0, "score": 8, "angle": "..."}]."""


def cmd_leads(cfg, a):
    ib = load_inbox()
    seen = Seen()
    pool = [it for it in lead_pool(cfg, ib) if item_key(it) not in ib["scores"]]
    if a.new_only:
        pool = [it for it in pool if not seen.is_repeat(item_key(it))]
    mapping, leads = {}, []
    for i, it in enumerate(pool):
        mapping[str(i)] = item_key(it)
        text = it["title"]
        if it["kind"] == "trend" and it.get("news"):
            text += " | related headlines: " + "; ".join(n["title"] for n in it["news"][:2])
        elif it["kind"] == "reddit":
            text = f'{it["where"]}: {text}'
        leads.append({"id": i, "kind": it["kind"], "text": re.sub(r"\s+", " ", text)[:320]})
    jsave(LEADS_FILE, {"date": TODAY, "map": mapping})
    print(json.dumps({"rubric": RUBRIC.replace("{pubs}", cfg["scoring"]["publications"]),
                      "count": len(leads), "leads": leads}, ensure_ascii=False, indent=1))


def cmd_scores(cfg, a):
    payload = read_json_arg(a.file)
    rows = payload.get("scores", payload) if isinstance(payload, dict) else payload
    if isinstance(rows, dict):
        rows = [{"id": k, **(v if isinstance(v, dict) else {"score": v})} for k, v in rows.items()]
    lm = jload(LEADS_FILE, {})
    if lm.get("date") != TODAY:
        die("no leads for today; run `leads` first")
    ib = load_inbox()
    n = bad = 0
    for r in rows:
        key = lm["map"].get(str(r.get("id")))
        if key is None or "score" not in r:
            bad += 1
            continue
        ib["scores"][key] = {"score": int(r["score"]), "angle": str(r.get("angle") or "")}
        n += 1
    save_inbox(ib)
    print(json.dumps({"stored": n, "skipped": bad}))


def do_report(cfg, ib, job, no_dig=False):
    seen = Seen()
    parts = jload(PARTS_FILE, {})
    if parts.get("date") != TODAY:
        parts = {"date": TODAY}
    outs, code = [], 0
    jobs = ["feeds", "research", "trends"] if job == "all" else [job]
    for j in jobs:
        if j == "feeds":
            if any(k.startswith("feed:") for k in ib["sources"]):
                s, part = report_feeds(cfg, ib, seen)
                outs.append(s)
                parts["feeds"] = part
        elif j == "research":
            if any(k.startswith("pubmed:") for k in ib["sources"]):
                s, part = report_research(cfg, ib, seen)
                outs.append(s)
                parts["research"] = part
        elif j == "trends":
            if any(k.startswith(("news:", "trends", "reddit", "youtube")) for k in ib["sources"]):
                r = report_trends(cfg, ib, seen, no_dig=no_dig)
                if r is None:
                    code = 3
                else:
                    s, part = r
                    outs.append(s)
                    if part:
                        parts["trends"] = part
    if len(parts) > 1:
        jsave(PARTS_FILE, parts)
        dash = build_dashboard(cfg, parts)
        for s in outs:
            s.setdefault("dashboard", dash)
    seen.save()
    return outs, code


def cmd_report(cfg, a):
    ib = load_inbox()
    if not ib["items"] and not ib["sources"]:
        die("inbox is empty today; gather with `collect` or `ingest` first")
    outs, code = do_report(cfg, ib, a.job, a.no_dig)
    if outs:
        print(json.dumps(outs, indent=1))
    if code == 3:
        print(json.dumps(DIG, indent=1))
    if not outs and not code:
        die(f"nothing to report for job '{a.job}': no matching sources in today's inbox")
    sys.exit(code)


def cmd_run(cfg, a):
    """Unattended daily run for GitHub Actions: collect over HTTP, report, run extra searches if short."""
    ib = load_inbox()
    batches = collect_live(cfg, a.job)
    for bt in batches:
        add_batch(ib, bt)
    save_inbox(ib)
    ok = sum(1 for bt in batches if bt["ok"])
    log(f"collected {ok} of {len(batches)} sources")
    if batches and not ok:
        die("every source failed to load; nothing to report")
    outs, code = do_report(cfg, ib, a.job)
    if code == 3:
        log(f"only a few new headlines; running {len(DIG['tasks'])} extra searches")
        for t in DIG["tasks"]:
            q = t["source"][len("news:dig:"):]
            add_batch(ib, live_news(q, "2d") | {"source": t["source"]})
        save_inbox(ib)
        outs, code = do_report(cfg, ib, a.job)
    print(json.dumps(outs, indent=1))
    bad = [o for o in outs if o.get("error")]
    if bad or not outs:
        die("; ".join(o["error"] for o in bad) or "nothing was reported")


def cmd_status(cfg, a):
    ib = load_inbox()
    seen = jload(SEEN_FILE, {})
    hist = load_history()
    kinds = Counter(i["kind"] for i in ib["items"])
    print(json.dumps({
        "home": str(ROOT), "date": TODAY, "seen_keys": len(seen),
        "history_days": len(hist["days"]), "cursors": jload(CURSOR_FILE, {}),
        "inbox": {"sources": len(ib["sources"]), "failed": [k for k, v in ib["sources"].items() if not v["ok"]],
                  "items": dict(kinds), "scored": len(ib["scores"])},
        "latest_reports": sorted(p.name for p in REPORTS.glob("briefing-*.md"))[-3:],
        "dashboard": sorted(p.name for p in (DOCS_DIR / "daily").glob("*.html"))[-1:]}, indent=1))


def main():
    ap = argparse.ArgumentParser(prog="briefing.py", description=__doc__.split("\n")[1])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, fn in (("plan", cmd_plan), ("collect", cmd_collect), ("report", cmd_report), ("run", cmd_run)):
        p = sub.add_parser(name)
        p.add_argument("--job", choices=["feeds", "research", "trends", "all"], default="all")
        if name == "report":
            p.add_argument("--no-dig", action="store_true")
        p.set_defaults(fn=fn)
    for name, fn in (("ingest", cmd_ingest), ("scores", cmd_scores)):
        p = sub.add_parser(name)
        p.add_argument("file")
        p.set_defaults(fn=fn)
    p = sub.add_parser("leads")
    p.add_argument("--new-only", action="store_true", help="skip leads already shown on earlier days")
    p.set_defaults(fn=cmd_leads)
    sub.add_parser("status").set_defaults(fn=cmd_status)
    a = ap.parse_args()
    a.fn(load_config(), a)


if __name__ == "__main__":
    main()
