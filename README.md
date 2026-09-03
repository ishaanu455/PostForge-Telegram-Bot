# Postimoji

A Telegram bot for creating styled Facebook post images/videos (with Sinhala
text support) and publishing them directly to Facebook Pages — with
scheduling, templates, and TikTok/Pinterest video downloading built in.

## Features

### Post creation
- Turn typed text into a styled image post, with full Sinhala (and emoji)
  rendering via a custom HTML/CSS template rendered through Playwright.
- Adjustable font size, weight, and italics for body text.
- **Header (quoted) text** — wrap part of your text in `"..."` to render it
  as a separate styled header (own size/color/bold, configurable spacing).
- **Highlight text** — wrap part of your text in `^^...^^` to make it larger
  (adjustable scale, bold, italic).
- Custom emoji rendering (Apple-style, fetched and cached).
- Background options: solid color, uploaded photo, or a TikTok/Pinterest
  video link.
- Background photo/video adjustments: overlay opacity, text vertical
  offset, blur (Gaussian or Motion), chromatic aberration (subtle RGB
  split), VHS/retro effect, and a fade-in-from-black video intro.
- Background music — upload an audio file or pull the audio straight from
  a TikTok link, with automatic duration/beat fitting against the
  background video.

### Video downloader
- Download TikTok or Pinterest videos directly by sending a link
  (`📹 Video Download` flow) — no watermark, best available quality.
- TikTok downloads use the [tikwm.com](https://www.tikwm.com) API first
  (fast, no-watermark, HD) and automatically fall back to `yt-dlp` if that
  ever fails. Pinterest downloads always use `yt-dlp`.

### Self-blur video tool (`/selfblur`)
- Take a foreground video/photo (upload or TikTok/Pinterest link) and
  composite it over a blurred, fitted background — the common
  "TikTok/FB Reels fill-screen" look — with adjustable blur strength,
  foreground size, and vertical position.
- Optional watermark image/text, logo image/text, and background music
  (upload or TikTok link) can be layered in.
- Save your settings as a reusable template.

### Facebook publishing
- `/pages` — connect and manage multiple Facebook Pages (label, Page ID,
  access token) directly from the bot.
- Post the generated image/video straight to a selected Page via the
  Facebook Graph API.
- `/schedule` — view, edit, delete, or immediately post scheduled posts.
  A background job checks for due posts and auto-publishes them.
- `/templates` — save and reuse post styling (fonts, colors, effects,
  backgrounds) as named templates.
- Group chat support — trigger a new post directly from a group chat.

### Reliability
- Persistent state (`PicklePersistence`) — in-progress settings and pages
  survive a bot restart.
- Automatic retry with backoff for transient download/network failures.
- Emoji-safe grapheme-cluster text splitting for correct rendering of
  multi-codepoint emoji.

## Requirements

- Python 3.11+
- [ffmpeg](https://ffmpeg.org/) and `ffprobe` installed and on `PATH`
  (used for video/audio processing)
- A Telegram bot token from [@BotFather](https://t.me/BotFather)
- A Sinhala-capable OpenType/TrueType font file
- Facebook Page(s) with a Graph API access token, if you want to use the
  publishing features

## Setup

1. **Clone the repo**
   ```bash
   git clone <this-repo-url>
   cd postimoji
   ```

2. **Create a virtual environment and install dependencies**
   ```bash
   python3 -m venv venv
   source venv/bin/activate
   pip install -r requirements.txt
   playwright install --with-deps chromium
   ```

3. **Install ffmpeg** (if not already installed)
   ```bash
   sudo apt install ffmpeg
   ```

4. **Add your Sinhala font**
   Place a font file at `fonts/YourSinhalaFont.ttf` (or update `FONT_PATH`
   in `bot.py` to point at your font).

5. **Set your bot token**
   ```bash
   cp .env.example .env
   ```
   Then edit `.env` and set:
   ```
   BOT_TOKEN=your_telegram_bot_token_here
   ```
   The token is loaded from the environment at startup — it is never
   hardcoded in the source.

6. **Run the bot**
   ```bash
   python3 bot.py
   ```

## Commands

| Command      | Description                                    |
|--------------|-------------------------------------------------|
| `/start`     | Start the bot / show the main menu             |
| `/newpost`   | Start creating a new post                      |
| `/templates` | List and manage saved templates                |
| `/pages`     | Manage connected Facebook Pages                |
| `/schedule`  | View and manage scheduled posts                |
| `/selfblur`  | Start the self-blur video tool                 |
| `/cancel`    | Cancel the current operation                   |

## Running as a background service

For a VPS, running under `systemd` is recommended so the bot restarts
automatically on crash or reboot. Example unit file:

```ini
[Unit]
Description=Postimoji Telegram Bot
After=network.target

[Service]
WorkingDirectory=/path/to/postimoji
ExecStart=/path/to/postimoji/venv/bin/python3 bot.py
Restart=always
RestartSec=5

[Install]
WantedBy=multi-user.target
```

## Notes

- `bot.py` must always be saved as UTF-8 (no BOM) — it contains emoji and
  Sinhala characters that require multi-byte encoding. Editing it with a
  tool that defaults to ANSI/Windows-1252 will silently corrupt those
  characters.
- `bot_persistence.pickle` (created automatically) holds live bot state
  and is git-ignored — don't commit it.
