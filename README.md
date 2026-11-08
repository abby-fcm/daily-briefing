# Daily Briefing

One GitHub tool that replaces the two old repos. Every day GitHub runs `briefing.py` and updates one page, `docs/index.html`. Everything is on that page, styled alike and filterable by topic:

- **Rising topics and brand-new terms** from Reddit (optional), Google News, Google Trends and YouTube (optional)
- **Trend headlines** and one-tap searches on TikTok, Instagram, YouTube Shorts, Pinterest and Google Trends
- **New from health publications** (CDC, WHO, NIH, STAT, NPR, KFF, Mayo, BBC, Guardian and others)
- **New medical research** from PubMed, rotating through the topic list

Nothing repeats. Anything shown on an earlier day is hidden. Past days are in `docs/daily/`, including the earlier briefings from the old repos.

## Setup (about 10 minutes, in your browser)

1. **Create a repository.** Click **+** (top right), then **New repository**. Name it `daily-briefing`. Choose **Public** if you want the web page (free GitHub Pages needs public), otherwise Private.
2. **Upload everything in this folder**, including the `state` and `docs` folders. Click **uploading an existing file**, drag the contents in, then **Commit changes**.
3. **Check the workflow file.** `.github/workflows/daily.yml` must exist. If the upload skipped it, click **Add file**, **Create new file**, type exactly `.github/workflows/daily.yml`, paste the file's contents, and commit.
4. **Allow saving.** **Settings**, **Actions**, **General**, **Workflow permissions**, choose **Read and write permissions**, **Save**.
5. **Run it once.** **Actions** tab, **Daily briefing**, **Run workflow**. Wait about 5 minutes for the green check.
6. **Turn on the page** (public repos). **Settings**, **Pages**, Branch `main` and folder `/docs`, **Save**. Your page is at `https://YOUR-USERNAME.github.io/daily-briefing/`.
7. **Retire the old repos.** In each old repo, **Actions**, pick each workflow, three dots, **Disable workflow**.

It then runs every day at 10:00 UTC (6am Eastern). Change the `cron` line in `daily.yml` to move it.

## Optional keys

Add under **Settings**, **Secrets and variables**, **Actions**, **New repository secret**:

| Secret | Turns on |
|---|---|
| `REDDIT_CLIENT_ID`, `REDDIT_CLIENT_SECRET` | Reddit rising posts (create an app at reddit.com/prefs/apps, type *script*) |
| `YOUTUBE_API_KEY` | YouTube and Shorts sections |
| `CONTACT_EMAIL` | Identifies the tool to NCBI and publishers, as they request |

Put your Reddit username in `config.yaml` after `reddit_username:`.

## Changing what it tracks

Edit `config.yaml` (pencil icon). `briefing:` holds the publication feeds, research topics and news topics; `subreddits`, `news_searches`, `youtube_searches` and `categories` drive the trend sections and the topic filters. Keep the indentation and the `- ` at the start of each item.

## Files

| Path | Purpose |
|---|---|
| `briefing.py` | The whole tool |
| `config.yaml` | All settings |
| `state/` | Memory: what was already shown, trend history, research rotation. Do not delete |
| `docs/` | The page (`index.html`) and past days |

## If something looks broken

- **Red X in Actions:** open the run and read the failed step. A spacing mistake in `config.yaml` is the usual cause.
- **A section says it was not reached:** that site was down or asked the tool to slow down. It retries tomorrow.
- **Page stopped updating:** GitHub pauses scheduled runs after 60 days without activity. In **Actions**, re-enable the workflow.
