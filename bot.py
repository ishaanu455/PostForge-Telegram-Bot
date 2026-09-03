# -*- coding: utf-8 -*-
# IMPORTANT: this file MUST always be saved as UTF-8 (no BOM). It contains
# emoji and Sinhala characters that need multi-byte UTF-8 encoding to exist
# at all. If you edit this file on the server with an editor that defaults
# to "ANSI"/Windows-1252 (e.g. some SFTP-client built-in editors), saving
# will silently replace every emoji/Sinhala character with a literal '?'
# and there is no way to recover them from code afterwards - the file has
# to be re-uploaded as a fresh UTF-8 copy. Prefer editing locally (VS Code /
# Notepad++ with UTF-8 selected) and re-uploading the whole file, or use
# `nano`/`vim` directly over SSH with a UTF-8 locale.
import asyncio
import base64
import bisect
import html as html_module
import json
import logging
import os
import re
import shutil
import subprocess
import tempfile
import uuid
from datetime import datetime, timedelta, timezone
from io import BytesIO
from pathlib import Path
from zoneinfo import ZoneInfo   # Sri Lankan time (Asia/Colombo) walata - schedule feature eka

import httpx
import regex   # used for emoji-safe text splitting (grapheme clusters), pip install regex
import yt_dlp  # used to download Pinterest / TikTok videos, pip install yt-dlp
from dotenv import load_dotenv   # .env file eken BOT_TOKEN load karaganna, pip install python-dotenv
from PIL import Image, ImageOps
from playwright.async_api import async_playwright

load_dotenv()   # server eke .env file ekak thibboth, e values tika os.environ walata load wenawa

from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputMediaPhoto,
)
from telegram.error import BadRequest, NetworkError
from telegram.request import HTTPXRequest
from telegram.ext import (
    ApplicationBuilder,
    ContextTypes,
    ConversationHandler,
    MessageHandler,
    CommandHandler,
    CallbackQueryHandler,
    PersistenceInput,
    PicklePersistence,
    filters,
)

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# group chat walata "aluth post ekak patan ganna" trigger eka - bot ekage
# id/username eka post_init eken methanata fill wenawa (application build
# unata passe witharai me values tika available wenne)
_BOT_INFO = {"id": None, "username": None}

# ---------------- CONFIG ----------------
# BOT_TOKEN eka code eke hardcode karanne na - .env file eken (hari server
# eke environment variable ekak vidihata) load wenawa, e nisa GitHub ekata
# push kalath token eka leak wenne na. Server eke bot.py eka thiyena
# folder ekema ".env" file ekak hadala "BOT_TOKEN=your_token_here" danna.
BOT_TOKEN = os.environ.get("BOT_TOKEN")
if not BOT_TOKEN:
    raise RuntimeError(
        "BOT_TOKEN environment variable eka set karala nehe. Bot eka thiyena "
        "folder ekema '.env' file ekak hadala 'BOT_TOKEN=your_token_here' widiyata danna."
    )

FONT_PATH = Path("fonts/YourSinhalaFont.ttf")   # Sinhala OpenType font ekak methanata
IMG_SIZE = 1080

MAX_TEXT_WIDTH = 760
MAX_TEXT_HEIGHT = 460
SIDE_PADDING = 70   # left/right align karaddi canvas edge ekedin methara idak thiyenawa

FONT_SIZE_DEFAULT = 56
FONT_SIZE_MIN, FONT_SIZE_MAX, FONT_SIZE_STEP = 20, 110, 6

EMOJI_SIZE_DEFAULT = 60
EMOJI_SIZE_MIN, EMOJI_SIZE_MAX, EMOJI_SIZE_STEP = 20, 140, 8

FONT_WEIGHT_DEFAULT = 400
FONT_WEIGHT_MIN, FONT_WEIGHT_MAX, FONT_WEIGHT_STEP = 300, 800, 100
ITALIC_DEFAULT = False   # body text (header nemei) ekata global "Italic" toggle eka

# ---- header (quoted text) settings ----
# user type kala text eke "..." widiyata quote kara kotasak thiyenawa nam, e
# kotasa "header" ekak vidihata (wenama size/color/bold + top-bottom space
# ekak ekka) render karanawa. Header ekak nathi text ekakata methanin ekakuth
# effect ekak nehe - "Header" adjust button eka pennanne header ekak
# thiyena poddo witharai (ADJUSTING screen eke).
HEADER_FONT_SIZE_DEFAULT = 72
HEADER_FONT_SIZE_MIN, HEADER_FONT_SIZE_MAX, HEADER_FONT_SIZE_STEP = 30, 140, 6

HEADER_BOLD_DEFAULT = True

HEADER_COLOR_DEFAULT = "#ffd400"   # yellow - normal text eken wenas karanna default eken penenna

# header eka saha e passe ena normal text eka athara space eka (header eke
# pahalin thiyena gap eka), saha header ekata udin thiyena gap eka (top)
HEADER_GAP_TOP_DEFAULT = 0
HEADER_GAP_TOP_MIN, HEADER_GAP_TOP_MAX, HEADER_GAP_TOP_STEP = 0, 200, 10

HEADER_GAP_BOTTOM_DEFAULT = 34
HEADER_GAP_BOTTOM_MIN, HEADER_GAP_BOTTOM_MAX, HEADER_GAP_BOTTOM_STEP = 0, 200, 10

# user text eke ^^ dala mark karapu kotasa (loku/highlight) - normal body
# text size ekata relative widiyata (1.0x = wenasak na, 2.0x = double)
# multiply karanawa. User ^^ dala witharama (buttons ekak thakila nathuwa)
# default eken thoda loku widiyata (1.3x) penei - ithuru loku/podi/bold/
# italic control tika "🔆 Highlight" submenu eke buttons walin.
HIGHLIGHT_FONT_SCALE_DEFAULT = 1.3
HIGHLIGHT_FONT_SCALE_MIN, HIGHLIGHT_FONT_SCALE_MAX, HIGHLIGHT_FONT_SCALE_STEP = 1.0, 2.0, 0.1

HIGHLIGHT_BOLD_DEFAULT = False
HIGHLIGHT_ITALIC_DEFAULT = False

# background photo upload karoth, e udin danna black overlay eke default opacity eka
OVERLAY_OPACITY_DEFAULT = 0.35
OVERLAY_OPACITY_MIN, OVERLAY_OPACITY_MAX, OVERLAY_OPACITY_STEP = 0.0, 0.9, 0.1

# text eka image eke center ekedin udata/pahalata gena yanna px offset eka
TEXT_OFFSET_DEFAULT = 0
TEXT_OFFSET_STEP = 40
TEXT_OFFSET_MIN, TEXT_OFFSET_MAX = -1000, 1000

# background photo/video ekata blur ekak (px/sigma eken) - text eka clear ekata
# penenna background eka distract wenna una unoth methanin adjust karagannawa
BLUR_DEFAULT = 0
BLUR_MIN, BLUR_MAX, BLUR_STEP = 0, 20, 2

# "gaussian" = hama disawakatama sama widiyata blur wenawa (kalinma tibbe meka)
# "motion" = tirayen ekaha (horizontal) witharak "streak" ekak wage blur wenawa,
# video ekak panning/moving unoth wage look ekak. Dekamatama BLUR_DEFAULT/MIN/MAX
# strength eka share karagannawa - "type" eka witharai wenas wenne.
BLUR_TYPE_DEFAULT = "gaussian"
BLUR_TYPE_LABELS = {"gaussian": "🌫 Blur: Gaussian", "motion": "🌀 Blur: Motion"}
# motion blur ekedi vertical (Y) direction eka methanin fix karala thiyenne wisala
# unoth wenas wenne strength eken witharai (X/horizontal side eka) - "streak" look eka
# nathi wela pure gaussian blur ekak wage penena eka methanin awoid karanawa
MOTION_BLUR_SIGMA_V = 1.0

# ---- chromatic aberration (subtle RGB split) settings ----
# gaussian/motion blur wagema methanath video background ekatama apply wenawa
# (text/logo overlay ekata passe nemei, e issellama - text eka clean widiyata
# penei). "shift" eka = red channel eka wamata, blue channel eka dakunata
# px ganak shift karanawa (subtle cinematic look ekakata thani single px
# ganak witharai methanin, RGB "glitch" wage strong ekak nemei).
CHROMATIC_ABERRATION_DEFAULT = False
CHROMATIC_SHIFT_DEFAULT = 3
CHROMATIC_SHIFT_MIN, CHROMATIC_SHIFT_MAX, CHROMATIC_SHIFT_STEP = 1, 12, 1

# ---- VHS / retro look settings ----
# noise (grain) + saturation/contrast bump + vignette ekak combine karala
# "old cassette tape" look ekak denawa. "strength" eka (%) grain amount eka
# witharak drive karanawa - color-bleed/vignette eka fix widiyata thiyenawa.
VHS_EFFECT_DEFAULT = False
VHS_STRENGTH_DEFAULT = 40
VHS_STRENGTH_MIN, VHS_STRENGTH_MAX, VHS_STRENGTH_STEP = 10, 100, 10

# ---- video intro (fade in from black) settings ----
# video editor apps wala "black enter"/fade-in transition eka wagema - video
# background eke issellamama black ekata gradually fade wela content ekata
# enawa. Length eka user ta +/- buttons walin 0.5s step ekakin control
# karanna puluwan. Video eke existing duration eka methen wenas wenne na -
# eka fade transition ekak witharai, wenama black clip ekak ithuru wenne na.
INTRO_BLACK_SECONDS_DEFAULT = 0.0
INTRO_BLACK_SECONDS_MIN, INTRO_BLACK_SECONDS_MAX, INTRO_BLACK_SECONDS_STEP = 0.0, 10.0, 0.5

# ---- video background settings ----
# TikTok/Pinterest video ekak background ekak vidihata upload kaloth, e video eka
# methanin kiyana thanata vada digu unoth ithuru kotasa kapala damanawa (30s witharak
# process karanawa - server load/time ithuru karaganna)
BG_VIDEO_MAX_SECONDS = 30

# encode quality: crf adui unoth quality vaddi wenawa (file size ithuru wenawa).
# 23/veryfast walin 20/medium walata maru kalath, TikTok/Pinterest wage
# dhanatamath compressed video walata udin text/logo overlay eka clear widiyata
# penenna meka wadagath wenawa (veryfast walata wada process wela ganna
# tikak time wadi wenawa, eth quality ekedi wenasa loku widiyata penenawa)
BG_VIDEO_CRF = "20"
BG_VIDEO_PRESET = "medium"

# ffmpeg -progress output eken % ekak vidihata caller ekata (chat message eke
# "⏳ 40% rendering..." wage update ekakata) yawana frequency eka - Telegram
# edit_message_text ekata rate-limit ekak thiyena nisa, hama line ekakatama
# edit karanne nathuwa, methanin kiyana % change ekak una gaman witharak
# update karanawa
BG_VIDEO_PROGRESS_MIN_STEP = 5   # percent

# ---- "self-blur" video settings ----
# "/selfblur" - user danna video ekma dedena widiyata use karana feature eka
# (compose_self_blur_video() balanna): full-canvas blur background + center
# eke podi clear copy ekak. Mee tikama +/- buttons walin adjust karanna puluwan.
SELFBLUR_MAX_SECONDS = 30   # BG_VIDEO_MAX_SECONDS ekma cap eka - process load/time ithuru karaganna

# Meme Layout mode eke fixed canvas sizes - output eka 1080x1080 square wenawa.
# Uda thiyena sudu text box eka MEME_BOX_H (300px), pahala video area eka
# MEME_VIDEO_H (780px), total = MEME_CANVAS_W x (MEME_BOX_H + MEME_VIDEO_H) = 1080x1080.
MEME_CANVAS_W  = 1080
MEME_VIDEO_H   = 780   # video area (bg+fg) height - pad before danawa
MEME_BOX_H     = 300   # white text box height at top

# Meme mode sudu box eke text eka user adjust karaganna (up/down) - px
# MEME_BOX_H (300px) athule witharai, edge walata over-wenna dena naha
MEME_TEXT_YOFF_DEFAULT = 0
MEME_TEXT_YOFF_STEP    = 10
MEME_TEXT_YOFF_MIN     = -100   # uda direction (300px box eke uda side)
MEME_TEXT_YOFF_MAX     = 100    # pahala direction

# Meme mode fg left/right/bottom divider line settings
MEME_DIVIDER_WIDTH  = 8        # px wide white line (left, right, bottom)
MEME_DIVIDER_ALPHA  = 1.0      # opacity (0 = invisible, 1 = solid)

# Meme mode default logo offset: center fg video eke pahala kotaseta (~180px
# above canvas bottom = red-circle position the user marked in the screenshot)
MEME_LOGO_OFFSET_DEFAULT = 180

SELFBLUR_BLUR_DEFAULT = 36
# 30 nam podi welak - main background video flow eke BLUR_MAX ekatama match
# karanna methana 60 dakwa dala thiyenne (gblur sigma, so 60 = godak wisala blur)
SELFBLUR_BLUR_MIN, SELFBLUR_BLUR_MAX, SELFBLUR_BLUR_STEP = 0, 60, 2

# main background video flow eke wagema "gaussian" (hama disawakatama sama)
# vs "motion" (horizontal streak) blur type eka methanatath - constants tika
# (BLUR_TYPE_DEFAULT/LABELS/MOTION_BLUR_SIGMA_V) share karanawa, "selfblur_blur_type"
# key eken witharai state eka wenama track karanne
SELFBLUR_BLUR_TYPE_DEFAULT = BLUR_TYPE_DEFAULT

SELFBLUR_FG_PCT_DEFAULT = 65   # canvas width eke % ekak vidihata, center eke thiyena clear video eke width eka
SELFBLUR_FG_PCT_MIN, SELFBLUR_FG_PCT_MAX, SELFBLUR_FG_PCT_STEP = 30, 95, 5

# vertical position - canvas height eke % ekak vidihata, center ekedin
# okkoma (+ = pahalata, - = udata) - user "udata/pahalata" adjust karana eka
SELFBLUR_YOFF_DEFAULT = 0
SELFBLUR_YOFF_MIN, SELFBLUR_YOFF_MAX, SELFBLUR_YOFF_STEP = -35, 35, 5

# center video eke udin danna caption/emoji text eka (ekak dammoth witharai
# effect ekak) - font size eka witharai methanin adjust karanna one, esengath
# okkoma (color/bold/italic/header/highlight) main post-creator eke widiyatama
# text eke ##bold## //italic// ""header"" ^^highlight^^ syntax eken danna
# puluwan (generate_image() eka reuse karana nisa).
SELFBLUR_FONT_SIZE_DEFAULT = FONT_SIZE_DEFAULT
SELFBLUR_FONT_SIZE_MIN, SELFBLUR_FONT_SIZE_MAX, SELFBLUR_FONT_SIZE_STEP = FONT_SIZE_MIN, FONT_SIZE_MAX, FONT_SIZE_STEP

# "/selfblur" ekedi default eken userta text ekak type karanna one nathuwama,
# menu eka patan gaththatama top eke penena placeholder text eka - user ta
# "✏️ Edit Text" eken witharai wenas karagannna one, /skip ekak thawa danna
# one nehe (danata thibba widiyata caption eka ahana step eka mulinma skip
# karala, direct menu ekatama yanawa).
SELFBLUR_TEXT_DEFAULT = "Your text here"
# text color/stroke eka - main post-creator flow ekema COLORS/STROKE_WIDTH_*
# constants tikama share karanawa (aluth "SELFBLUR_" prefixed ewa one nehe,
# value ekama danata thiyena text_keyboard() eke pattern ekatama match wenawa)
SELFBLUR_TEXT_COLOR_DEFAULT = "#ffffff"

# text eke vertical position eka (build_html() eke "translateY" px ekama,
# text_offset_y global TEXT_OFFSET_* constants share karanawa) - "⬆️ Top" /
# "⬇️ Bottom" preset buttons dekaka target value tika methanin, + fine-tune
# ekata TEXT_OFFSET_STEP ekama use karanawa. Default eka "Top" ekata dala
# thiyenne - user default preview eka video eke uda penenna one kiyala kiwwa nisa.
#
# ± value eka canvas center ekedin translateY karana px ganana nisa, values
# godak loku unoth (kalin ±700 thibba), podi-height source video (e.g.
# 720x1280 wage Pinterest/TikTok clips - canvas center ~640px) ekakadi
# text-box eka (content-block eke udinma thiyena, emoji row ekata kalin)
# canvas eken pිටටම (negative y) push wela cropped/invisible wela, emoji
# row eka witharai (block eke pahalin thiyena eka) podi ptharyak penei -
# "text penne na, emoji witharai loku widiyata penei" kiyana bug eka una eka.
# ±420 = ithurath "clearly top/bottom" widiyata penei, eth 720px height
# canvas ekakadi wath multi-line Sinhala text ekak (~4 lines) safe widiyata
# canvas athule ithuru wenawa.
SELFBLUR_TEXT_TOP_OFFSET = -420
SELFBLUR_TEXT_BOTTOM_OFFSET = 420
# default eken (video eka ready una gaman) text eka methana thiyenne - "Top"
# preset ekama value eka (SELFBLUR_TEXT_TOP_OFFSET) - kalin methana 380
# (bottom-ish) widiyata thibba eka comment eka ekka contradict una bug ekak,
# ithin "Top" ekatama fix kara (user preview eka default widiyatama video
# eke uda penenna one kiyala kiwwa nisa).
SELFBLUR_TEXT_YOFF_DEFAULT = SELFBLUR_TEXT_TOP_OFFSET

# background (blur karapu) layer eka udin danna black overlay eka - center
# eke clear video ekatai userge text/emoji ekatai meka apply wenne nehe
# (blur bg layer ekatama witharai), text/emoji tika udata pennana widiyata
# opacity eka user ta +/- karaganna puluwan.
SELFBLUR_OVERLAY_OPACITY_DEFAULT = 20
SELFBLUR_OVERLAY_OPACITY_MIN, SELFBLUR_OVERLAY_OPACITY_MAX, SELFBLUR_OVERLAY_OPACITY_STEP = 0, 90, 10

# background eka - default eka "blur" (danata pattern eka: source video ekemma
# blur karapu copy ekak background widiyata) - eth methanin "🖼 Background"
# menu eken user ta wenas karaganna puluwan: "color" (solid fill - COLORS
# dict eke thiyena stock colors), "image" (custom static image, upload
# karapu eka) hari "video" (custom video, loop wela full duration eka fill
# karanawa). "image"/"video" walata blur+chromatic/vhs effect eka thawath
# apply karannath (selfblur_bg_blur_enabled) puluwan - kalinma bg eka danata
# thiyena video ekema witharak nisa methanin "wenama background ekak danna
# puluwan" kiyana request eka implement karanne.
SELFBLUR_BG_KIND_DEFAULT = "blur"
SELFBLUR_BG_KINDS = ["blur", "color", "image", "video"]
SELFBLUR_BG_COLOR_DEFAULT = "#000000"

# ---- "photo -> video" settings ----
# user ekage plain background photo eka, music ekak ekka video ekak vidihata
# convert karana feature eka. Music dammoth video length eka e music eke
# length ekatama (BG_VIDEO_MAX_SECONDS cap ekatama) set wenawa - music skip
# kaloth witharai methanin length eka preset buttons walin ahanne.
PHOTO_VIDEO_DURATION_PRESETS = [5, 10, 15, 30]   # seconds - "skip music" flow ekedi pennana buttons

# ---- logo / watermark settings ----
# Logo is anchored bottom-center by default; "offset_bottom" is how many px
# its baseline sits above the canvas bottom edge (user moves it up/down with
# buttons). "scale" is a single 100%-based percentage that drives both the
# image width and the text font-size, so one +/- control resizes either kind.
LOGO_SCALE_DEFAULT = 100
LOGO_SCALE_MIN, LOGO_SCALE_MAX, LOGO_SCALE_STEP = 25, 400, 15
LOGO_IMG_BASE_WIDTH = 260    # px, at scale=100
LOGO_TEXT_BASE_SIZE = 42     # px font-size, at scale=100
LOGO_OFFSET_DEFAULT = 50     # px gap between logo and the canvas bottom edge
# MIN eka kalin -300 tibba - "logo down" click karala offset eka 0ta pahalata
# (negative) giyoth, CSS "bottom: Npx" eka canvas/viewport eke pahala edge eka
# pahaddila logo eka rendered PNG eke pita bhagayata (screenshot viewport eken
# pitin) yanawa - screenshot eken e kotasa capture wenne ma na, ithin logo eka
# final video eke "invisible" widiyata penei (layer ekak pahalata giya wage
# penila thibunath, ඇත්තටම canvas boundary eken pita giya nisai). MIN eka 0ta
# dala thiyenne, "down" click kochchara welak kalath logo eka canvas bottom
# edge ekatama witharai enna puluwan widiyata - eeken over-clip/invisible
# wena eka sampurnayenma vahagannawa.
LOGO_OFFSET_MIN, LOGO_OFFSET_MAX, LOGO_OFFSET_STEP = 0, 900, 30

# logo layer eke opacity eka (%) - watermark/logo eka background eka udin
# godak "loud" widiyata penenawa nam methanin adui karaganna puluwan
LOGO_OPACITY_DEFAULT = 100
LOGO_OPACITY_MIN, LOGO_OPACITY_MAX, LOGO_OPACITY_STEP = 10, 100, 10

# emoji row eka text ekedin (udata/pahalata) independently move karanna px
# offset eka - text_offset_y eken text+emoji dekama ekathuwa move wenawa,
# meken emoji row eka witharak text ekata relative widiyata nudge karanna puluwan
EMOJI_OFFSET_DEFAULT = 0
EMOJI_OFFSET_MIN, EMOJI_OFFSET_MAX, EMOJI_OFFSET_STEP = -200, 200, 20

# ---- scrolling watermark settings (video backgrounds only) ----
# Static logo eken wenas - meka video background ekak udin continuously
# scroll/loop wena watermark ekak (pirated-video-style "moving watermark"
# effect ekak). opacity (%) + direction (4k) + speed (px/sec) + scale (%,
# canvas width ekata relative) - okkoma user ta adjust karanna puluwan.
WATERMARK_OPACITY_DEFAULT = 70
WATERMARK_OPACITY_MIN, WATERMARK_OPACITY_MAX, WATERMARK_OPACITY_STEP = 10, 100, 10

WATERMARK_SPEED_DEFAULT = 120     # px/sec vidihata scale karapu "speed" value ekak
WATERMARK_SPEED_MIN, WATERMARK_SPEED_MAX, WATERMARK_SPEED_STEP = 30, 400, 30

WATERMARK_SCALE_DEFAULT = 20      # %, canvas width ekata relative (logo_scale eke pattern ekama)
WATERMARK_SCALE_MIN, WATERMARK_SCALE_MAX, WATERMARK_SCALE_STEP = 5, 60, 5

WATERMARK_DIRECTION_DEFAULT = "up_down"
WATERMARK_DIRECTIONS = ["up_down", "down_up"]
WATERMARK_DIRECTION_LABELS = {
    "up_down": "⬇️ Top → Bottom",
    "down_up": "⬆️ Bottom → Top",
}

# scroll wenne vertically witharai (uda-pahala) - eth watermark eka canvas eke
# ohoma horizontal widiyakin "left" hari "right" hari side ekaka thiyenna
# puluwan (center ekedi nemei) - user ta cycle karagannna puluwan.
WATERMARK_SIDE_DEFAULT = "left"
WATERMARK_SIDES = ["left", "right"]
WATERMARK_SIDE_LABELS = {
    "left": "⬅️ Left side",
    "right": "➡️ Right side",
}

# ---- watermark preview settings ----
# Preview eka 3-tier fallback widiyata hadanawa (godak slow/busy server ekaka
# hang wela "fail" widiyata penena eka nawattanna):
#   tier 1 (normal)  -> short low-res MP4, single-pass, progress % ekak ekka
#   tier 2 (light)   -> ithuru ithuru podi/ikmanata MP4 (tier 1 timeout unoth)
#   tier 3 (frame)   -> watermark eka overlay kara static PNG frame ekak
#                       witharai (tier 2 ekath timeout unoth) - meken
#                       speed eka penenne nehe, eth opacity/scale/side ewa
#                       instant widiyata check karaganna puluwan
WATERMARK_PREVIEW_SECONDS = 2
WATERMARK_PREVIEW_WIDTH = 480          # kalinma 280 tibbe - logo eka pixelated widiyata penuna nisa wadi kala
WATERMARK_PREVIEW_TIMEOUT = 15        # seconds, tier 1

WATERMARK_PREVIEW_LIGHT_SECONDS = 1.5
WATERMARK_PREVIEW_LIGHT_WIDTH = 320    # kalinma 200 tibbe - eket wagema wadi kala (tier 2 - tier 1 fail unoth witharai)
WATERMARK_PREVIEW_LIGHT_TIMEOUT = 12  # seconds, tier 2

WATERMARK_PREVIEW_FRAME_TIMEOUT = 8   # seconds, tier 3 (static frame - super fast)

WATERMARK_PREVIEW_PROGRESS_MIN_STEP = 10   # percent, edit_message_text rate-limit ekata


# "left" | "center" | "right" - text ekath emoji tikath ekama side ekatama align wenawa
ALIGN_DEFAULT = "center"
ALIGN_LABELS = {"left": "⬅️ Left", "center": "↔️ Center", "right": "➡️ Right"}
ALIGN_ITEMS = {"left": "flex-start", "center": "center", "right": "flex-end"}   # CSS align-items/justify-content

COLORS = {
    "yellow": "#ffd400",
    "red": "#ff3b30",
    "blue": "#3b82f6",
    "white": "#ffffff",
    "black": "#000000",
}

COLOR_LABELS = {
    "yellow": "🟡 Yellow",
    "red": "🔴 Red",
    "blue": "🔵 Blue",
    "white": "⚪ White",
    "black": "⚫ Black",
}

# body text stroke ("stock") - akuru wala outline eka. 0.5px step ekakin
# +/- karagannna puluwan (bold weight step ekata wada podi steps - font-weight
# eka wagema ekpaharatama ganakama loku wenne nathuwa, gradual widiyata akuru
# mahatha karaganna puluwan). width 0 nam stroke eka completely off (CSS
# property eka methanin add wenne nehe).
STROKE_WIDTH_DEFAULT = 0.0
STROKE_WIDTH_MIN = 0.0
STROKE_WIDTH_MAX = 3.0
STROKE_WIDTH_STEP = 0.5
STROKE_COLOR_DEFAULT = "#000000"

# ---- Facebook Page direct-post settings ----
# post iwara una gaman, user ta ownge Facebook Page ekata (Graph API eken)
# direct widiyata upload karanna puluwan option ekak methanin denawa. Page
# Access Token eka + Page ID eka user_data (persistence) ekata save wenawa,
# ithin ekvarak dunnama passe post gananakatama ekamai reuse karanna puluwan.
FACEBOOK_GRAPH_VERSION = "v20.0"
FACEBOOK_GRAPH_BASE = f"https://graph.facebook.com/{FACEBOOK_GRAPH_VERSION}"
FACEBOOK_UPLOAD_TIMEOUT = 120.0   # seconds - photo/video upload ekata generous timeout ekak

# "/pages" flow eke "Add Page" step ekedi saha "ℹ️ Token guide" button eken
# user ta pennana step-by-step guide eka - Page ID + Page Access Token eka
# hariyata hදගන්නේ කොහොමද කියලා.
PAGE_GUIDE_TEXT = (
    "🧭 *Page Access Token එකක් හදාගන්නා විදිය:*\n\n"
    "1️⃣ https://developers.facebook.com/tools/explorer/ යන්න\n"
    "2️⃣ Top right - ඔයාගේ App එක select කරන්න\n"
    "3️⃣ \"Get Token\" → \"Get User Access Token\" click කරලා, permissions වලින් මේවා check කරන්න:\n"
    "   • `pages_show_list`\n"
    "   • `pages_read_engagement`\n"
    "   • `pages_manage_posts`\n"
    "   • video upload කරනවා නම් `pages_manage_engagement` එකත් dagන්න\n"
    "4️⃣ \"Generate Access Token\" → login/authorize කරන්න\n"
    "5️⃣ දැන් ඒ *User token* එකෙන්ම `GET /me/accounts` කියලා query field එකට ටයිප් කරලා Submit කරන්න "
    "(Explorer එකේම query field එකට `me/accounts` ටයිප් කරන්න)\n"
    "6️⃣ Response එකේ ඔයාගේ Page list එක එයි - ඔයාට ඕන Page එකට ඇතුළේ තියෙන `access_token` "
    "field එකම copy කරගන්න — මේකයි real *Page Access Token* එක (User token එකක් නෙමෙයි)\n\n"
    "⚠️ App එක \"Development mode\" එකේ තියෙනවා නම්, ඔයා (App admin/developer role එකේ) විතරයි "
    "post කරන්න පුළුවන් - වෙන කෙනෙක් use කරනවා නම් App Review එකක් ඕන `pages_manage_posts` permission එකට.\n"
    "⏳ Short-lived token (1hr) එකක් නම් ඉක්මනට expire වෙනවා - testing එකට ok, production එකට "
    "long-lived token (60 days) එකක් exchange කරගන්න ඕන.\n\n"
    "Page ID + Token දෙකම හදාගත්තට පස්සේ, පහළින් \"➕ Add Page\" click කරලා දෙකම දාන්න."
)

PERSISTENCE_FILE = "bot_persistence.pickle"   # user settings mekedi save wenne (restart unath thiyenawa)

# ---- Facebook post scheduling settings ----
# "🕒 Schedule කරන්න" ekedi user ta ahanne me timezone eken (Sri Lanka), display
# karanawath methanma - UTC ekata convert karala witharai file eke save karanne.
SRI_LANKA_TZ = ZoneInfo("Asia/Colombo")
SCHEDULE_TIME_INPUT_FORMATS = ("%d-%m-%Y %H:%M", "%Y-%m-%d %H:%M")
SCHEDULE_TIME_EXAMPLE = "05-08-2026 21:30"
# scheduled/draft posts wala media files (image/video) tika, post/delete wena
# thuru save karagena inna dedicated folder eka (fb_pending_file wage temp
# folder ekak nemei - meka permanent widiyata thiyenawa)
SCHEDULED_POSTS_DIR = Path("scheduled_posts")
# job_queue eken kochchara welakට ekakට scheduled posts tika "due" da kiyala
# check karanawada kiyana interval eka (seconds)
SCHEDULE_CHECK_INTERVAL_SECONDS = 30

START_MESSAGE = (
    "🙏 *ආයුබෝවන්! Bot එකට Welcome.*\n\n"
    "මම ඔයාගේ post images වලට *Sinhala text + emoji* add කරලා, professional විදිහට "
    "*design* කරලා දෙන්න help කරන bot එකක්.\n\n"
    "*✨ මට කරන්න පුළුවන් දේවල්:*\n"
    "🖼 *Background* – plain color, image upload කරලා, TikTok/Pinterest video link එකක් දාලා, "
    "හෝ video upload කරලා set කරන්න පුළුවන්.\n"
    "🔤 *Text + Emoji* – font size, color, align (left/center/right) customize කරන්න පුළුවන්. "
    "Bold/Italic මුළු text එකටම toggle කරන්න පුළුවන්, ඒ වගේම text එකේ *ම* specific කොටසක් "
    "`##bold##` / `//italic//` / `^loku karanna one kotasa^` විදිහට type කරලා වෙන වෙනම "
    "bold/italic/loku (highlight) කරගන්නත්, ඕන ordar එකකින් mix කරගන්නත් (`##^text^##` වගේ) පුළුවන්. "
    "Telegram එකේම bold/italic button එකෙන් type කළත් (native formatting) ඒක automatic ම හඳුනාගන්නවා.\n"
    "🎨 *Styling* – bold text, blur effects (gaussian/motion), overlay opacity, position adjust කරන්න පුළුවන්.\n"
    "🏷 *Logo/Watermark* – image logo එකක් හෝ text logo එකක්, size & position එක්ක add කරන්න පුළුවන්.\n"
    "🎵 *Background Audio* – video background එකට music add කරන්න පුළුවන් (upload කරලා හෝ TikTok එකෙන්).\n"
    "📹 *Video Download* – TikTok/Pinterest video link එකක් විතරක් දීලා, direct download කරගන්න පුළුවන්.\n"
    "💾 *Templates* – ඔයාගේ favourite style එකක් save කරගෙන, පස්සේ post ගානකටම එකේම reuse කරගන්න පුළුවන් (/templates).\n\n"
    "*🚀 පටන් ගමු:*\n"
    "ඔයාගේ post එකට දාන්න ඕන text එක type කරලා send කරන්න. මම step-by-step ඔයාව guide කරන්නම්!\n\n"
    "❓ වෙනස් වෙලාවක අලුතෙන් පටන් ගන්න ඕන නම්, හැමදාම /cancel type කරන්න."
)
# -----------------------------------------

# ---------------- NETWORK RESILIENCE ----------------
# python-telegram-bot's default httpx timeouts (5s connect/read/write/pool)
# are too tight for uploading full-size background photos / final PNGs /
# videos from a small VPS - a slow or briefly congested upload then raises
# httpx.ReadError / WriteError / ConnectTimeout mid-transfer even though
# nothing is actually broken. Two changes handle this:
#   1) REQUEST_* timeouts below are passed into HTTPXRequest and used for
#      every bot API call (see main()).
#   2) send_with_retry() wraps the calls most likely to carry large payloads
#      (final image, video document) so a single transient network blip
#      doesn't lose the user's output.
REQUEST_CONNECT_TIMEOUT = 15.0
REQUEST_READ_TIMEOUT = 60.0
REQUEST_WRITE_TIMEOUT = 60.0
REQUEST_POOL_TIMEOUT = 15.0

NETWORK_RETRY_ATTEMPTS = 3
NETWORK_RETRY_BASE_DELAY = 2.0   # seconds; doubles each retry (2s, 4s, ...)


async def send_with_retry(coro_fn, *args, what: str = "request", **kwargs):
    """Calls an async bot method (e.g. context.bot.send_document) and retries
    on transient NetworkError failures (httpx ReadError/WriteError/ConnectError/
    TimeoutException, all wrapped by PTB as telegram.error.NetworkError or its
    TimedOut subclass). BadRequest (e.g. "message is not modified") is NOT
    retried - it's re-raised immediately instead, even though PTB's BadRequest
    class technically inherits from NetworkError (so it needs its own except
    clause, checked before the NetworkError one, or it'd get swept into the
    retry loop too). `what` is just a short label used in the log line if
    retries happen."""
    last_exc = None
    for attempt in range(1, NETWORK_RETRY_ATTEMPTS + 1):
        # A failed upload may have already consumed part of a file-like body
        # (BytesIO / open file handle). Rewind anything seekable before each
        # attempt, or the retry would send a truncated/empty file.
        for val in list(args) + list(kwargs.values()):
            if hasattr(val, "seek"):
                try:
                    val.seek(0)
                except Exception:
                    pass
            media = getattr(val, "media", None)   # InputMediaPhoto/Document wrap the file in .media
            if media is not None and hasattr(media, "seek"):
                try:
                    media.seek(0)
                except Exception:
                    pass
        try:
            return await coro_fn(*args, **kwargs)
        except BadRequest:
            # BadRequest (e.g. "message is not modified", "message to edit not
            # found") PTB library ekedi NetworkError ekenma inherit wenawa, ithin
            # meka check karanna kalin danna widiyata "except NetworkError"
            # block ekatama hikma yanawa - e kiyanne "not modified" wage
            # transient-nemei error ekakuth 3 parak retry karala (2s+4s delay
            # ekak), user ta bot eka "lag/stuck" wela wage penuna (real
            # cause eka methanin fix karanawa). BadRequest yanne request eka
            # kohomath waradi/invalid unu welavata (retry kaloth response eka
            # wenas wenne nehe), ithin methanin immediate ma re-raise karala
            # caller ekatama athdanawa - retry karanna deyak nehe.
            raise
        except NetworkError as e:
            last_exc = e
            if attempt < NETWORK_RETRY_ATTEMPTS:
                delay = NETWORK_RETRY_BASE_DELAY * (2 ** (attempt - 1))
                logger.warning(
                    f"{what}: transient network error on attempt {attempt}/{NETWORK_RETRY_ATTEMPTS} "
                    f"({e!r}), retrying in {delay:.0f}s"
                )
                await asyncio.sleep(delay)
            else:
                logger.error(f"{what}: giving up after {NETWORK_RETRY_ATTEMPTS} attempts ({e!r})")
    raise last_exc
# ------------------------------------------------------

(
    WAITING_EMOJI, WAITING_COLOR, ADJUSTING, ASK_VIDEO_PLATFORM, WAITING_VIDEO_LINK,
    ASK_BACKGROUND, WAITING_BG_IMAGE, CHOOSE_LOGO_TYPE, WAITING_LOGO_IMAGE, WAITING_LOGO_TEXT,
    ASK_BG_VIDEO_PLATFORM, WAITING_BG_VIDEO_LINK, WAITING_BG_VIDEO_UPLOAD,
    ASK_BG_VIDEO_AUDIO, ASK_BG_AUDIO_SOURCE, WAITING_BG_AUDIO_UPLOAD,
    WAITING_BG_AUDIO_TIKTOK_LINK, ASK_AUDIO_FIT, WAITING_TEMPLATE_NAME, CHOOSE_TEMPLATE,
    ASK_FB_POST, WAITING_FB_CAPTION, WAITING_EDIT_TEXT, ASK_FB_RETRY,
    # video/image eka export karala Telegram ekata evapu passe, Facebook ask
    # step ekata yanna kalin "ayeth edit karanna ona da" kiyala ahana step eka
    ASK_REEDIT,
    # meva "/pages" command eken enna, wenama Facebook-page-manager conversation
    # ekata witharak use wena states - "fb_pages" dict eka (page_id -> {label, token})
    # ekata multiple pages save karaganna/edit karanna methanin puluwan
    WAITING_PAGE_LABEL, WAITING_PAGE_ADD_ID, WAITING_PAGE_ADD_TOKEN, WAITING_PAGE_EDIT_TOKEN,
    # scrolling watermark - dedicated sub-menu (video background posts walata
    # witharai) + ekata aluth watermark image ekak upload karana state eka +
    # text watermark ekak type karana state eka
    WATERMARK_MENU, WAITING_WATERMARK_IMAGE, WAITING_WATERMARK_TEXT,
    # caption/hashtags type kara ivara welata "දැන්ම Post/Schedule/Draft" kiyala
    # ahana state eka, + "Schedule" eka thoraganoth date/time eka ahana state eka.
    # WAITING_EDIT_SCHEDULE_TIME eka "/schedule" eken enna wenama mini-conversation
    # ekata witharai use wenne (scheduled post ekaka time eka passe edit karanna).
    ASK_FB_SCHEDULE, WAITING_SCHEDULE_TIME, WAITING_EDIT_SCHEDULE_TIME,
    # "🎬 Photo eka Video ekak karanna" flow eka - music skip kaloth witharak
    # methanata enawa (video length eka preset buttons walin ahanawa). Music
    # dammoth ASK_BG_AUDIO_SOURCE/WAITING_BG_AUDIO_UPLOAD/WAITING_BG_AUDIO_TIKTOK_LINK
    # states tikama reuse karanawa (photo_video_flow flag eken branch karanawa).
    ASK_PHOTO_VIDEO_DURATION,
    # "/selfblur" - wenama, sampurna independent conversation eka. Video eka
    # (link/upload) ahagena, blur/size/position/audio/watermark adjust karana
    # main menu ekata (SELFBLUR_ADJUSTING - self-loop, +/- buttons walata)
    # yanawa, ithin render karanawa.
    SELFBLUR_ASK_VIDEO_PLATFORM, WAITING_SELFBLUR_VIDEO_LINK, WAITING_SELFBLUR_VIDEO_UPLOAD,
    SELFBLUR_ADJUSTING, WAITING_SELFBLUR_AUDIO_UPLOAD, WAITING_SELFBLUR_AUDIO_TIKTOK_LINK,
    WAITING_SELFBLUR_WATERMARK_IMAGE,
    # video eka ready una passe, render karanna kalin caption/emoji text eka
    # ahana state eka (skip karanna puluwan). Render iwara unu passe "Post to
    # Page" ahana states dekath methanma (fb_pages walin ekak thoraganna, ho
    # skip karanna).
    WAITING_SELFBLUR_TEXT, ASK_SELFBLUR_FB_POST, WAITING_SELFBLUR_FB_CAPTION,
    # video eka download unu-unuma (onboarding), text ekata passe "usergen"
    # flow eken kiyapu order ekatama (link -> text -> emoji -> preview)
    # emoji ekak witharak ahana wenama step eka - text step eka wagema
    # /skip karanna puluwan, ithin preview/adjust menu ekata yanawa.
    WAITING_SELFBLUR_EMOJI,
    # "🏷 Watermark Settings" / "🖼 Logo Settings" sub-menus walata - image logo
    # ekak upload karana state eka, saha "✏️ Type value" button eken px/%
    # value ekak manually type karana wenama generic state eka (which field
    # ekada edit karanne kiyala "selfblur_manual_target" eken track karanawa)
    WAITING_SELFBLUR_LOGO_IMAGE, WAITING_SELFBLUR_MANUAL_VALUE,
    # "🖼 Background" sub-menu - custom image/video background upload states
    WAITING_SELFBLUR_BG_IMAGE, WAITING_SELFBLUR_BG_VIDEO,
    # "📁 Templates" - "💾 Save as Template" click unu passe, template
    # nama ahagana state eka
    WAITING_SELFBLUR_TEMPLATE_NAME,
    WAITING_SELFBLUR_LOGO_TEXT, WAITING_SELFBLUR_WATERMARK_TEXT,
) = range(54)

# ekakata save karanna puluwan max templates gana - pickle file eka loku wena eka
# and template list eka scroll karanna one wena eka awoid karanna methanin limit karanawa
MAX_TEMPLATES_PER_USER = 15

_FONT_B64_CACHE = None
_EMOJI_CACHE: dict[str, str] = {}   # emoji char -> base64, process eka running wenakan reuse wenawa

# User kenek keyboard eken ":)" ":D" "<3" wage "text emoticons" type kaloth,
# ewa plain ASCII/symbol characters vitharai (real Unicode emoji na) - eka nisa
# emojicdn.elk.sh ekata query kaloth fail wela, e symbol tika image ekata
# ennema nathuwa silent wela yanawa. Ithin e commonly-use vena text emoticons tika,
# ewata samana real Unicode emoji ekakata methanin convert karanawa - real
# emoji ekak nam meke wenas wenne na, hariyatama e widiyatama pass wenawa.
TEXT_EMOTICON_MAP = {
    ":-)": "🙂", ":)": "🙂", "=)": "🙂",
    ":-(": "🙁", ":(": "🙁", "=(": "🙁",
    ":-D": "😄", ":D": "😄", "=D": "😄",
    ":-P": "😛", ":P": "😛", ":-p": "😛", ":p": "😛",
    ";-)": "😉", ";)": "😉",
    ":'-(": "😢", ":'(": "😢",
    ":'-D": "😂", ":'D": "😂",
    "xD": "😆", "XD": "😆", "xd": "😆",
    "<3": "❤️", "</3": "💔",
    ":-o": "😮", ":-O": "😮", ":o": "😮", ":O": "😮",
    ":-|": "😐", ":|": "😐",
    ":-/": "😕", ":/": "😕", ":-\\": "😕", ":\\": "😕",
    "8-)": "😎", "8)": "😎", "B-)": "😎", "B)": "😎",
    ":-*": "😘", ":*": "😘",
    "^_^": "😊", "^^": "😊",
    "o_O": "😲", "O_o": "😲",
}


def convert_text_emoticons(text: str) -> str:
    """':)' vage keyboard-symbol emoticons tika, ewata samana real Unicode
    emoji ekakata convert karanawa - meka call karanne emoji CDN ekata
    yawanna kalin. Longer patterns (e.g. ':-)') tika, shorter patterns
    (e.g. ':)') walata kalin match karanawa - naththam ':-)' eke '-' eka
    ain wela ':)' witharak match wela adha result eka wenas wenna puluwan."""
    if not text:
        return text
    for pattern in sorted(TEXT_EMOTICON_MAP, key=len, reverse=True):
        text = text.replace(pattern, TEXT_EMOTICON_MAP[pattern])
    return text


def get_font_b64() -> str:
    global _FONT_B64_CACHE
    if _FONT_B64_CACHE is None:
        if not FONT_PATH.exists():
            raise FileNotFoundError(f"Font file hamba welle nehe: {FONT_PATH}")
        _FONT_B64_CACHE = base64.b64encode(FONT_PATH.read_bytes()).decode("utf-8")
    return _FONT_B64_CACHE


def split_graphemes(text: str) -> list[str]:
    """Splits text into grapheme clusters instead of raw Unicode code points.
    Plain str iteration (`for ch in text`) breaks apart multi-codepoint emoji
    - flags, family/couple ZWJ sequences, skin-tone modifiers - into broken
    fragments. \\X groups each of those back into a single visual unit, so
    any number of simple OR compound emoji are handled correctly."""
    return regex.findall(r"\X", text)


# real Unicode emoji symbols (pictures) detect karanna - "\p{Extended_Pictographic}"
# eken plain digits/#/* wage (Emoji=Yes unath pictograph nemei) characters
# godak wela reject wenawa, ithuru wenne "😥" wage niyama pictograph symbols
# witharai. Flag emoji (regional indicator pairs, e.g. 🇱🇰) methanin catch
# wenne na - ewa podi edge case ekak vidihata plain text vidihatama ridee.
_PICTOGRAPHIC_EMOJI_RE = regex.compile(r"\p{Extended_Pictographic}")


def extract_pictographic_emoji(text: str) -> tuple[str, str]:
    """User type kala text ekedi (selfblur caption wage thanaka) inline
    embedded unu real Unicode emoji tika text eken separate karala, wenama
    "emojis" string ekak vidihata denawa - main post-creator flow ekema
    widiyata e ewa passe generate_image() ekata "emojis" param eken danna
    puluwan widiyata (fetch_apple_emoji_b64 -> apple-style CDN image, text
    eken embedded widiyata rendered unoth wenne browser/OS eke default
    (non-apple) emoji font eken - eyai methanin wenas karanne).
    Returns (clean_text_without_emoji, emoji_chars_in_order)."""
    if not text:
        return text, ""
    kept: list[str] = []
    emoji_chars: list[str] = []
    for ch in split_graphemes(text):
        if _PICTOGRAPHIC_EMOJI_RE.match(ch):
            emoji_chars.append(ch)
        else:
            kept.append(ch)
    return "".join(kept), "".join(emoji_chars)


async def fetch_apple_emoji_b64(emoji_char: str) -> str | None:
    """emojicdn.elk.sh eken apple-style emoji image ekak fetch karala base64 vidihata denawa.
    Dan fetch karapu emoji ekak nam cache eken denawa, aye download karanne nehe."""
    if emoji_char in _EMOJI_CACHE:
        return _EMOJI_CACHE[emoji_char]

    url = f"https://emojicdn.elk.sh/{emoji_char}?style=apple"
    try:
        async with httpx.AsyncClient(timeout=15) as client:
            resp = await client.get(url, follow_redirects=True)
            resp.raise_for_status()
            b64 = base64.b64encode(resp.content).decode("utf-8")
            _EMOJI_CACHE[emoji_char] = b64
            return b64
    except Exception:
        logger.warning(f"emoji fetch failed for: {emoji_char}")
        return None


async def get_video_direct_url(url: str) -> str:
    """yt-dlp eken video eka download NEHE - direct CDN URL eka witharak
    extract karagannawa. Meka pass unoth VPS eke bandwidth/disk kisima
    ekak use wenne nehe (Telegram server ekenma fetch karanawa). Pinterest
    ekath TikTok ekath dekamatama use wenne mekama function eka - yt-dlp
    eken site eka auto-detect wenawa URL eken. Fail unoth exception ekak
    throw karanawa (caller eken slow-path ekata fallback karanawa)."""
    ydl_opts = {
        # "best" kiyanne single (progressive) file ekak - video+audio
        # dekama URL ekakama thiyena eka. bestvideo+bestaudio danne nehe,
        # e dekama welada URL dekakin nam merge karanna VPS ekatama
        # download karanna wenawa, e "fast path" eka nathi wenawa.
        "format": "best",
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "skip_download": True,
    }

    def _run() -> str:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
        direct_url = info.get("url")
        if not direct_url:
            raise RuntimeError("No direct video URL found for that link.")
        return direct_url

    return await asyncio.to_thread(_run)


# tikwm.com ekage free public API eka - TikTok video/audio download ekata
# yt-dlp ekata wada methanin priority ekak denawa (methanin TikTok ekatama
# specific, watermark-free video + audio direct URL denawa). yt-dlp ge
# TikTok extractor eka TikTok side eken site structure eka wenas kaloth
# frequently break wenawa - tikwm ekage service eka e wenas kama tikak
# wegayen update karanawa, e nisa TikTok download ekata methanin methanin
# kalinma try karala, fail unoth witharai yt-dlp ekata fallback wenawa.
# Pinterest link walata meka use karanne na (tikwm TikTok ekatama specific).
TIKWM_API_URL = "https://www.tikwm.com/api/"


def _is_tiktok_url(url: str) -> bool:
    """URL eka TikTok link ekakda kiyala domain eken check karanawa."""
    return "tiktok.com" in url.lower()


async def _tikwm_fetch(url: str) -> dict:
    """tikwm API eka call karala, e link ekee (watermark නැති HD) video
    play URL eka saha audio (music) URL eka thiyena data dict eka denawa.
    Fail unoth (rate-limit/link invalid/service down) exception ekak
    throw karanawa - caller eken yt-dlp fallback ekata switch karanawa."""
    async with httpx.AsyncClient(timeout=20) as client:
        resp = await client.get(TIKWM_API_URL, params={"url": url, "hd": 1})
        resp.raise_for_status()
        payload = resp.json()
    if payload.get("code") != 0 or not payload.get("data"):
        raise RuntimeError(f"tikwm API error: {payload.get('msg', 'unknown error')}")
    return payload["data"]


def _tikwm_full_url(path: str) -> str:
    """tikwm eken ena URL eka relative ("/..." wage) nam domain eka
    prepend karanawa - already full URL ekak nam ehemama return karanawa."""
    return path if path.startswith("http") else f"https://www.tikwm.com{path}"


async def _download_tikwm_file(file_url: str, tmp_dir: str, filename: str) -> str:
    """tikwm eken dena direct file URL ekakin (video hari audio hari)
    content eka fetch karala local file ekakata write karala path eka denawa."""
    dest = Path(tmp_dir) / filename
    async with httpx.AsyncClient(timeout=60, follow_redirects=True) as client:
        resp = await client.get(file_url)
        resp.raise_for_status()
        dest.write_bytes(resp.content)
    return str(dest)


async def download_video_via_tikwm(url: str) -> str:
    """TikTok video ekak tikwm API eken (watermark නැති HD play URL eken)
    download karala, local temp file path eka return karanawa."""
    tmp_dir = tempfile.mkdtemp(prefix="vid_tikwm_")
    data = await _tikwm_fetch(url)
    play_url = data.get("hdplay") or data.get("play")
    if not play_url:
        raise RuntimeError("tikwm didn't return a playable video URL.")
    filename = f"{data.get('id') or uuid.uuid4().hex}.mp4"
    return await _download_tikwm_file(_tikwm_full_url(play_url), tmp_dir, filename)


async def extract_audio_via_tikwm(url: str) -> str:
    """TikTok video ekage audio track eka (music) tikwm API eken witharak
    download karanawa - video eka gena ffmpeg eken extract karanna one na
    nisa, methana yt-dlp+ffmpeg fallback ekatath wada wegayen wade karanawa."""
    tmp_dir = tempfile.mkdtemp(prefix="aud_tikwm_")
    data = await _tikwm_fetch(url)
    music_url = data.get("music")
    if not music_url:
        raise RuntimeError("tikwm didn't return an audio URL.")
    filename = f"{data.get('id') or uuid.uuid4().hex}.mp3"
    return await _download_tikwm_file(_tikwm_full_url(music_url), tmp_dir, filename)


async def download_video(url: str) -> str:
    """TikTok link ekak nam palamuwa tikwm API eken (wegayi, reliable)
    download karanna try karanawa - eka fail unoth witharai, pahalin
    thiyena yt-dlp path ekatama fallback wenawa (Pinterest link okkoma
    methanin kelinma yt-dlp ekatama yanawa, tikwm eka call karanne na).

    yt-dlp eken video eka (Pinterest hari TikTok hari) best available
    quality ekenma download karala, local temp file path eka return karanawa.
    Fail unoth exception ekak throw karanawa (caller eken catch karanawa)."""
    if _is_tiktok_url(url):
        try:
            return await download_video_via_tikwm(url)
        except Exception as e:
            logger.warning("tikwm video download failed for %s (%s), falling back to yt-dlp", url, e)

    tmp_dir = tempfile.mkdtemp(prefix="vid_")

    def _run(fmt: str) -> str:
        ydl_opts = {
            "format": fmt,
            "outtmpl": str(Path(tmp_dir) / "%(id)s.%(ext)s"),
            "merge_output_format": "mp4",
            "quiet": True,
            "no_warnings": True,
            "noplaylist": True,
        }
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            ydl.download([url])
        files = [f for f in Path(tmp_dir).iterdir() if f.is_file()]
        if not files:
            raise RuntimeError("No video file was produced from that link.")
        return str(files[0])

    try:
        # video eke separate video/audio streams thibboth, highest quality
        # ekatama merge karagannawa - meka ffmpeg one wenawa
        return await asyncio.to_thread(_run, "bestvideo+bestaudio/best")
    except Exception as e:
        if "ffmpeg" not in str(e).lower():
            raise
        # server eke ffmpeg install karala nehe - merge karanna barinam,
        # single-file (progressive) format ekakata fallback wenawa, e ekata
        # merge one na
        logger.warning("ffmpeg not available on this server, falling back to a progressive format")
        return await asyncio.to_thread(_run, "best")

    # yt-dlp eka blocking (sync) library ekak nisa, event loop eka block
    # karanne naththam thread ekaka welada denawa
    return await asyncio.to_thread(_run)


# slow-path download eka fail unoth (network blip ekak wage transient
# issue ekak nisa wenna puluwan), user ta error eka penna aye link eka
# ahanna one wenne nehe widiyata - methanin auto-retry karanawa. Site eke
# extractor eka break unoth wage permanent failure ekakata retry ekakin
# vaasi ekak nehe, eth ehema unath ithuru wela wenne "attempts" gana
# tikak wada balala thamai user ta pennanne, ehema nisa loss ekak nehe.
DOWNLOAD_RETRY_ATTEMPTS = 3
DOWNLOAD_RETRY_DELAY = 3.0   # seconds, retry ekakata kalin


async def download_video_with_retry(
    url: str,
    attempts: int = DOWNLOAD_RETRY_ATTEMPTS,
    delay: float = DOWNLOAD_RETRY_DELAY,
) -> str:
    """download_video eka call karanawa - fail unoth, user ta ekkenma error eka
    pennanne nathuwa 'attempts' gananakata (delay tikak dala) aye try karanawa.
    Okkoma try unath fail unoth witharai, aatharada exception eka raise karanawa
    (caller eken e welawata witharak user ta error message eka pennanawa)."""
    last_exc: Exception | None = None
    for attempt in range(1, attempts + 1):
        try:
            return await download_video(url)
        except Exception as e:
            last_exc = e
            logger.warning(
                "download_video attempt %d/%d failed for %s: %s",
                attempt, attempts, url, e,
            )
            if attempt < attempts:
                await asyncio.sleep(delay)
    assert last_exc is not None
    raise last_exc


async def extract_audio_from_url(url: str) -> str:
    """TikTok link ekakin, video eke thiyena audio track eka witharak (video
    eka nathuwa) extract karala local mp3 file ekak vidihata download karanawa
    - "mute + add new audio" flow ekedi TikTok link option ekata use wenawa.

    Palamuwa yt-dlp ekema "bestaudio" extractor eka try karanawa (fast, video
    eka download karanne na). Eka fail unoth (TikTok/Pinterest ekedi audio-
    only format ekak nathi welawaka wenna puluwan), full video eka (already
    reliable widiyata wade karana download_video eken) download karala,
    ffmpeg eken local widiyata audio track eka extract karana fallback
    ekatama switch wenawa. Dekama fail unoth witharai exception ekak throw
    karanawa (caller eken catch karanawa).

    TikTok link ekak nam methanata wada issellama tikwm API eken (wegayi,
    video eka gena one na) audio eka try karanawa - eka fail unoth witharai
    pahalin thiyena yt-dlp path ekatama fallback wenawa."""
    if _is_tiktok_url(url):
        try:
            return await extract_audio_via_tikwm(url)
        except Exception as e:
            logger.warning("tikwm audio extraction failed for %s (%s), falling back to yt-dlp", url, e)

    tmp_dir = tempfile.mkdtemp(prefix="aud_")

    def _run() -> str:
        ydl_opts = {
            "format": "bestaudio/best",
            "outtmpl": str(Path(tmp_dir) / "%(id)s.%(ext)s"),
            "postprocessors": [{
                "key": "FFmpegExtractAudio",
                "preferredcodec": "mp3",
            }],
            "quiet": True,
            "no_warnings": True,
            "noplaylist": True,
        }
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            ydl.download([url])
        files = [f for f in Path(tmp_dir).iterdir() if f.is_file()]
        if not files:
            raise RuntimeError("No audio track was found in that link.")
        return str(files[0])

    try:
        return await asyncio.to_thread(_run)
    except Exception as e:
        logger.warning(
            "Direct bestaudio extraction failed for %s (%s), falling back to "
            "full video download + local ffmpeg audio extraction", url, e,
        )
        shutil.rmtree(tmp_dir, ignore_errors=True)
        return await _extract_audio_via_video_fallback(url)


async def _extract_audio_via_video_fallback(url: str) -> str:
    """extract_audio_from_url ekage "bestaudio" path eka fail unoth use wena
    fallback eka - video eka MUKALINMA (video+audio dekama) download karala
    (download_video eken - background video flow ekedi already reliable
    widiyata wade karana ekama function eka), passe ffmpeg eken audio track
    eka witharak local widiyata extract karanawa. Meka video eka full
    widiyata download wena nisa tikak slow - eth yt-dlp ekema "bestaudio"
    extractor eka break unath, thawa chance ekak denawa."""
    video_path = await download_video(url)
    tmp_dir = Path(video_path).parent
    audio_path = str(tmp_dir / "audio.mp3")

    def _run() -> str:
        subprocess.run(
            ["ffmpeg", "-y", "-i", video_path, "-vn", "-acodec", "libmp3lame", audio_path],
            capture_output=True, check=True,
        )
        if not Path(audio_path).exists():
            raise RuntimeError("Couldn't extract an audio track from that video.")
        return audio_path

    try:
        return await asyncio.to_thread(_run)
    finally:
        # video file eka thawath one na - audio eka witharai one wenne
        try:
            Path(video_path).unlink(missing_ok=True)
        except Exception:
            pass


async def extract_audio_from_url_with_retry(
    url: str,
    attempts: int = DOWNLOAD_RETRY_ATTEMPTS,
    delay: float = DOWNLOAD_RETRY_DELAY,
) -> str:
    """extract_audio_from_url ekage retry-version eka - download_video_with_retry
    ekama pattern eka (transient failure ekakata user ta ekkenma error eka
    pennanne nathuwa, attempts gananakata try karanawa)."""
    last_exc: Exception | None = None
    for attempt in range(1, attempts + 1):
        try:
            return await extract_audio_from_url(url)
        except Exception as e:
            last_exc = e
            logger.warning(
                "extract_audio_from_url attempt %d/%d failed for %s: %s",
                attempt, attempts, url, e,
            )
            if attempt < attempts:
                await asyncio.sleep(delay)
    assert last_exc is not None
    raise last_exc


async def probe_audio_duration(path: str) -> float:
    """ffprobe eken audio file ekee duration_seconds eka denawa - upload karapu
    audio ekak/TikTok eken extract kara audio ekak, background video eke
    duration ekata fit wenawada balaganna use wenawa."""

    def _run() -> float:
        result = subprocess.run(
            [
                "ffprobe", "-v", "error",
                "-show_entries", "format=duration",
                "-of", "json",
                path,
            ],
            capture_output=True, text=True, check=True,
        )
        info = json.loads(result.stdout)
        return float(info["format"]["duration"])

    return await asyncio.to_thread(_run)


async def probe_video(path: str) -> tuple[int, int, float, int]:
    """ffprobe eken video ekee (width, height, duration_seconds, bitrate_kbps)
    tuple ekak denawa. Meka background video ekak download unu passema,
    canvas size eka + max 30s trim eka calculate karaganna one wenawa.

    bitrate_kbps ekath ain kale - TikTok/Pinterest re-share/re-compress unu
    video wala, resolution eka (720p/1080p) ekama widiyata thibbath, bitrate
    eka godak podi welawaka (heavy re-compression nisa) thiyenawa - eka
    nisama visual quality eka blurry/pixelated wenawa, eth width/height
    check ekakin witharak eka allagaanna baha."""

    def _run() -> tuple[int, int, float, int]:
        result = subprocess.run(
            [
                "ffprobe", "-v", "error",
                "-select_streams", "v:0",
                "-show_entries", "stream=width,height,bit_rate",
                "-show_entries", "format=duration,bit_rate",
                "-of", "json",
                path,
            ],
            capture_output=True, text=True, check=True,
        )
        info = json.loads(result.stdout)
        stream = info["streams"][0]
        width, height = int(stream["width"]), int(stream["height"])
        duration = float(info["format"]["duration"])
        # Stream-level bit_rate eka nathi welawaka (containers gananakin
        # ain karala thiyenne format-level ekama) - format-level eka
        # fallback widiyata use karanawa.
        bit_rate_raw = stream.get("bit_rate") or info["format"].get("bit_rate")
        bitrate_kbps = int(int(bit_rate_raw) / 1000) if bit_rate_raw else 0
        return width, height, duration, bitrate_kbps

    return await asyncio.to_thread(_run)


# Source video eke quality eka podi nam (highly-compressed re-share ekak
# wage), bot eka monaha kaleth output ekath e-pissu quality ekmama pennei -
# eka bot eke bug ekak nemei. E confusion eka ain karaganna, video eka add
# karana welavema quality eka check karala podi nam user ta Sinhala
# bhashaven, professional widiyata kiyanawa - saha "Replace Video" button
# eken (Adjust screen eke) meka aye maru karaganna puluwan bawa mathaka
# karanawa.
#
# Width/height (resolution) ekama check kirima madi - TikTok/Pinterest walin
# aana re-share unu video, dan resolution eka (720p/1080p) normal widiyatama
# thibbath, heavy re-compression nisa bitrate eka godak podi welawaka
# thiyenawa - eka nisama pennena eka blurry/pixelated wenawa. Ee nisa
# resolution eka + bitrate eka dekama ekatuwa balala tier eka decide karanawa.
LOW_RES_WARNING_THRESHOLD = 720   # width/height dekema methanata wada adui nam "Low" tier eka

# bitrate (kbps) methanata wada adui nam, e resolution tier eka ekak
# adui karanawa (e.g. 1080p ekak thibbath, bitrate eka podi nam "Good" ekata
# adui karanawa)
_BITRATE_THRESHOLDS_BY_MIN_DIM = (
    (1080, 2500),
    (720, 1200),
    (480, 600),
)


def _video_quality_tier(width: int, height: int, bitrate_kbps: int = 0) -> tuple[str, int]:
    min_dim = min(width, height)
    if min_dim >= 1080:
        tier_idx = 3
    elif min_dim >= 720:
        tier_idx = 2
    elif min_dim >= 480:
        tier_idx = 1
    else:
        tier_idx = 0

    # bitrate eka danna nathi welawaka (0), resolution eka witharak balanawa
    if bitrate_kbps:
        for min_dim_threshold, bitrate_threshold in _BITRATE_THRESHOLDS_BY_MIN_DIM:
            if min_dim >= min_dim_threshold and bitrate_kbps < bitrate_threshold:
                tier_idx = max(0, tier_idx - 1)
                break

    labels = {3: "ඉහළම (Max)", 2: "හොඳයි (Good)", 1: "මධ්‍යම (Medium)", 0: "පහළ (Low)"}
    return labels[tier_idx], tier_idx


def _low_res_warning(width: int, height: int, bitrate_kbps: int = 0) -> str | None:
    tier_label, tier_idx = _video_quality_tier(width, height, bitrate_kbps)
    if tier_idx >= 2:   # Good/Max nam warning ekak one na
        return None
    bitrate_line = f" · ~{bitrate_kbps} kbps" if bitrate_kbps else ""
    return (
        f"⚠️ *මෙම වීඩියෝවේ තත්ත්වය (quality) අඩුයි* ({width}x{height}{bitrate_line}).\n\n"
        f"මෙම video එකේ output quality මට්ටම: *{tier_label}*\n\n"
        f"Source video එකේම quality එක අඩු නිසා (resolution/bitrate), final "
        f"output එකත් එම මට්ටමින්ම (අඩු quality එකින්) පැමිණේ — මෙය bot "
        f"එකේ දෝෂයක් නොවේ, මුල් video එකේම තත්ත්වයයි.\n\n"
        f"වඩා හොඳ quality video එකක් යොදන්න ඕන නම්, ඉදිරියේදී Adjust screen "
        f"එකේ 🎥 *Replace Video* button එකෙන් මෙය ඕනෑම වේලාවක වෙනස් කරගත "
        f"හැක."
    )


async def extract_preview_frame_b64(path: str) -> str:
    """Video eke first frame eka PNG (base64) widiyata denawa - "Done" click karanna
    kalin, text/emoji/logo + blur eka mema (still) frame eka udinma preview
    karanna methanin use wenawa (photo background ekakadi kalinma widiyatama)."""

    def _run() -> bytes:
        result = subprocess.run(
            [
                "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
                "-i", path, "-frames:v", "1", "-f", "image2", "-c:v", "png", "pipe:1",
            ],
            capture_output=True, check=True,
        )
        return result.stdout

    png_bytes = await asyncio.to_thread(_run)
    return base64.b64encode(png_bytes).decode("utf-8")


def _watermark_overlay_expr(direction: str, speed: int, side: str = WATERMARK_SIDE_DEFAULT) -> tuple[str, str]:
    """Direction eka anuwa scrolling watermark ekata ffmpeg `overlay` filter
    ekata one wena x/y expression pair eka return karanawa. Scroll wenne
    vertically witharai (uda->pahala / pahala->uda) - `side` eken watermark
    eka horizontal widiyata canvas eke "left" hari "right" hari edge ekaka
    (SIDE_PADDING gap ekak ekka) fix karanawa, scroll unath e x position eka
    wenas wenne nehe.

    Pattern eka: `mod(t*speed, H+h)-h` - meken watermark eka thani side
    ekakin (e.g. top) canvas eken pita idan enna patan gena, anith side
    ekata (e.g. bottom) sampurnayenma pita yanakan gaman karala, aye mul
    positio nekatama loop wela (wrap) enawa - eka nisa "seam" ekak nathuwa
    infinite scroll ekak wage penenawa. `W`/`H` = background video eke
    width/height, `w`/`h` = watermark image eke width/height - dekama
    ffmpeg overlay filter eke built-in variables (runtime ekedi automatic
    widiyata resolve wenawa, methanin manual widiyata calculate karanna
    one na).
    """
    speed = max(1, int(speed))
    x_expr = f"W-w-{SIDE_PADDING}" if side == "right" else f"{SIDE_PADDING}"
    if direction == "down_up":
        y_expr = f"H-mod(t*{speed}\\,(H+h))"
    else:
        # default: up_down
        y_expr = f"mod(t*{speed}\\,(H+h))-h"
    return x_expr, y_expr


def _prepare_watermark_png(watermark_png_bytes: bytes, canvas_width: int, opacity_pct: int, scale_pct: int) -> bytes:
    """Watermark PNG eka canvas_width ekata relative widiyata (scale_pct%)
    resize karala, opacity_pct% ekata alpha channel eka multiply karala,
    aye PNG bytes vidihata return karanawa - `overlay=` filter ekata directly
    danna puluwan widiyata (ffmpeg colorchannelmixer eken venuwata methanin
    PIL eken karanawa, dim.png hadana widiyatama)."""
    img = Image.open(BytesIO(watermark_png_bytes)).convert("RGBA")
    target_w = max(10, round(canvas_width * scale_pct / 100))
    ratio = target_w / img.width
    target_h = max(10, round(img.height * ratio))
    img = img.resize((target_w, target_h), Image.LANCZOS)
    if opacity_pct < 100:
        alpha = img.split()[3].point(lambda a, o=opacity_pct: round(a * o / 100))
        img.putalpha(alpha)
    buf = BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()


async def render_watermark_text_png(browser, text: str) -> bytes:
    """User type kala text eka (image watermark ekakata wage) transparent
    PNG ekakata render karanawa - Sinhala font eka + existing Playwright
    pipeline ekama use karanawa (emoji render karanne nehe, watermark ekata
    plain text witharai one nisa). Screenshot eka ain karapu passe, PIL
    `getbbox()` eken transparent padding eka trim karala (auto-crop) return
    karanawa - font-size eka methanin loku widiyata (150px) fix kara
    thibbath, watermark eka danna gaman `_prepare_watermark_png()` eken
    canvas_width ekata relative scale_pct% ekatama resize wena nisa,
    prathama font-size eka aarthikayak wenne nehe."""
    font_b64 = get_font_b64()
    html = f"""
    <html>
    <head>
    <style>
        @font-face {{
            font-family: 'CustomSinhala';
            src: url(data:font/ttf;base64,{font_b64}) format('truetype');
        }}
        html, body {{ margin: 0; padding: 60px; background: transparent; }}
        .t {{
            font-family: 'CustomSinhala', sans-serif;
            color: #ffffff;
            font-size: 150px;
            font-weight: 700;
            text-shadow: 0 3px 10px rgba(0,0,0,0.6);
            white-space: nowrap;
            display: inline-block;
        }}
    </style>
    </head>
    <body><div class="t">{html_module.escape(text)}</div></body>
    </html>
    """
    page = await browser.new_page(viewport={"width": 2200, "height": 500}, device_scale_factor=2)
    try:
        await page.set_content(html)
        screenshot = await page.screenshot(type="png", omit_background=True)
    finally:
        await page.close()

    img = Image.open(BytesIO(screenshot)).convert("RGBA")
    bbox = img.getbbox()
    if bbox:
        img = img.crop(bbox)
    buf = BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()


async def compose_video_background(
    video_path: str,
    overlay_png_bytes: bytes,
    blur_type: str,
    blur_px: int,
    overlay_opacity: float,
    duration_seconds: float,
    progress_cb=None,
    audio_path: str | None = None,
    audio_mode: str = "keep",
    audio_fit: str = "trim_audio",
    watermark_png_bytes: bytes | None = None,
    watermark_opacity: int = WATERMARK_OPACITY_DEFAULT,
    watermark_scale: int = WATERMARK_SCALE_DEFAULT,
    watermark_direction: str = WATERMARK_DIRECTION_DEFAULT,
    watermark_speed: int = WATERMARK_SPEED_DEFAULT,
    watermark_side: str = WATERMARK_SIDE_DEFAULT,
    chromatic_aberration: bool = CHROMATIC_ABERRATION_DEFAULT,
    chromatic_shift: int = CHROMATIC_SHIFT_DEFAULT,
    vhs_effect: bool = VHS_EFFECT_DEFAULT,
    vhs_strength: int = VHS_STRENGTH_DEFAULT,
    intro_black_seconds: float = INTRO_BLACK_SECONDS_DEFAULT,
    background_is_static_image: bool = False,
) -> str:
    """Background video ekata (gaussian/motion) blur ekak + dark overlay ekak apply
    karala, e udin text/emoji/logo PNG eka ("overlay_png_bytes" - generate_image()
    eken transparent=True kara hadapu eka) burn-in karala, duration_seconds valata
    trim karala, final .mp4 file eke path eka return karanawa. Caller eken e file eke
    parent temp dir eka pasuwa delete karanna one (_cleanup_bg_video()/shutil.rmtree).

    progress_cb: optional async callable, `await progress_cb(percent)` widiyata
    call karanawa ffmpeg render eka wenakota (0-100 int). Meka fail unath render
    eka continue wenawa - UI update ekak fail unama render eka නවත්තන්න one නෑ.

    audio_mode: "keep" (original video audio ekma) | "mute" (audio ekakma na) |
    "replace" (original eka mute karala, audio_path eke thiyena file eka danawa).
    audio_fit: "replace" mode ekedi audio eka video ekata wada podi unoth witharai
    wadagath - "loop" nam audio eka -stream_loop karala full video duration ekatama
    pirenawa, "trim_audio" (default) nam audio/video dekama global -t eken trim wenawa.

    background_is_static_image: "🎬 Photo eka Video ekak karanna" feature eka
    witharak use karanawa - `video_path` eka real video ekak nemei, thani photo
    ekak (PNG/JPEG) unoth True danna. Ffmpeg walata e photo eka "-loop 1" eken
    infinite-duration frame ekak vidihata dennawa (thawත් pipeline eka - blur/
    overlay/watermark/effects/audio okkoma - real video ekakata wagema wade
    karanawa, "-t total_duration" eken witharai output eke length eka decide wenne)."""
    tmp_dir = tempfile.mkdtemp(prefix="vidbg_")
    overlay_path = Path(tmp_dir) / "overlay.png"
    overlay_path.write_bytes(overlay_png_bytes)

    # overlay_opacity > 0 nam, text/logo PNG eka danna kalin video eka udin
    # solid-black-with-alpha PNG ekak (dim.png) ekak overlay karala "darken" karanawa
    # - photo background ekedi CSS rgba() overlay ekak dapu widiyatama, video ekakata
    # eka ffmpeg filter ekakin karanna one nisa methanin PNG ekak vidihata hadanawa
    dim_path = None
    if overlay_opacity > 0:
        w, h = Image.open(BytesIO(overlay_png_bytes)).size
        dim_img = Image.new("RGBA", (w, h), (0, 0, 0, round(overlay_opacity * 255)))
        dim_buf = BytesIO()
        dim_img.save(dim_buf, format="PNG")
        dim_path = Path(tmp_dir) / "dim.png"
        dim_path.write_bytes(dim_buf.getvalue())

    out_path = Path(tmp_dir) / "final.mp4"

    sigma = float(blur_px)
    # motion blur ekedi vertical sigma eka witharak podi ekaka fix karala thiyenawa -
    # eken horizontal "streak" ekak witharak ithuru wenawa (gaussian ekedi dekama sama)
    sigma_v = sigma if blur_type == "gaussian" else min(sigma, MOTION_BLUR_SIGMA_V)
    blur_stage = f"gblur=sigma={sigma}:sigmaV={sigma_v}" if sigma > 0 else "null"

    # chromatic aberration + VHS/retro - text/logo eka overlay karanna kalinma
    # raw background video ekatama apply karanawa (blur ekama pattern eka),
    # ithin text eka mese distort/noisy wenne na - background eka witharai.
    raw_stage_parts = [blur_stage]
    if chromatic_aberration:
        shift = max(CHROMATIC_SHIFT_MIN, min(CHROMATIC_SHIFT_MAX, int(chromatic_shift)))
        # red channel eka wamata, blue channel eka dakunata "shift" px ganak -
        # green channel eka move karanne na (edges walata subtle color-fringe
        # ekak ithuru wenawa, RGB "glitch" wage strong ekak nemei)
        raw_stage_parts.append(f"rgbashift=rh=-{shift}:bh={shift}:edge=smear")
    if vhs_effect:
        strength = max(VHS_STRENGTH_MIN, min(VHS_STRENGTH_MAX, int(vhs_strength)))
        # grain amount eka strength eken drive wenawa (10-100% -> ~6-60 noise units),
        # color-bleed/contrast bump + corner vignette eka fix widiyata thiyenawa
        noise_amt = max(1, round(strength * 0.6))
        raw_stage_parts.append(f"noise=alls={noise_amt}:allf=t+u")
        raw_stage_parts.append("eq=saturation=1.15:contrast=1.05:brightness=0.01")
        raw_stage_parts.append("vignette=PI/5")
    raw_stage = ",".join(raw_stage_parts)

    # thani photo ekak (static image) nam, "-loop 1" eken ffmpeg ekata e frame
    # eka infinite-duration video ekak widiyata dennawa - pipeline eke ithuru
    # kotasa (blur/overlay/watermark/effects/-t trim) real video ekakata wagema
    inputs: list[str] = (["-loop", "1", "-i", video_path] if background_is_static_image else ["-i", video_path])
    filter_parts = [f"[0:v]{raw_stage}[blurred]"]
    last_label = "blurred"
    input_idx = 1

    if dim_path:
        inputs += ["-loop", "1", "-i", str(dim_path)]
        filter_parts.append(f"[{last_label}][{input_idx}:v]overlay=0:0:format=auto[dimmed]")
        last_label = "dimmed"
        input_idx += 1

    inputs += ["-loop", "1", "-i", str(overlay_path)]
    filter_parts.append(f"[{last_label}][{input_idx}:v]overlay=0:0:format=auto[textlogo]")
    last_label = "textlogo"
    input_idx += 1

    # scrolling watermark - text/logo overlay eka udin, canvas eke edge ekakin
    # anith ekata continuously loop wena watermark ekak (thibba nam witharai)
    wm_path = None
    if watermark_png_bytes:
        w, h = Image.open(BytesIO(overlay_png_bytes)).size   # canvas dimensions (text/logo PNG eke size eka)
        prepared = _prepare_watermark_png(watermark_png_bytes, w, watermark_opacity, watermark_scale)
        wm_path = Path(tmp_dir) / "watermark.png"
        wm_path.write_bytes(prepared)

    if wm_path:
        inputs += ["-loop", "1", "-i", str(wm_path)]
        x_expr, y_expr = _watermark_overlay_expr(watermark_direction, watermark_speed, watermark_side)
        filter_parts.append(
            f"[{last_label}][{input_idx}:v]overlay=x='{x_expr}':y='{y_expr}':eval=frame:format=auto,"
            f"scale=trunc(iw/2)*2:trunc(ih/2)*2,format=yuv420p[content]"
        )
        input_idx += 1
    else:
        # libx264 (yuv420p) walata width/height dekama 2 walin divisible wenna
        # one - photo eka odd height/width ekak (ex: 736x981) nam encoder eka
        # "height not divisible by 2" kiyala crash wenawa. scale filter eken
        # 1px witharak visually invisible ekak crop karala even dimensions
        # ekata force karanawa.
        filter_parts.append(f"[{last_label}]scale=trunc(iw/2)*2:trunc(ih/2)*2,format=yuv420p[content]")
    last_label = "content"

    # video intro - "fade in from black" transition ekak (video editor apps
    # walata thiyena "black enter" effect ekamai) - content eke duration eka
    # methen wenas wenne na, thiyena video eke issellamama black ekata gradually
    # fade wela content ekata enawa (wenama black clip ekak ithuru karanne na).
    intro_seconds = max(0.0, float(intro_black_seconds))
    if intro_seconds > 0:
        filter_parts.append(f"[{last_label}]fade=t=in:st=0:d={intro_seconds}:color=black[out]")
    else:
        filter_parts.append(f"[{last_label}]null[out]")

    filter_complex = ";".join(filter_parts)
    total_duration = duration_seconds

    # audio: "keep" nam original video eke audio track eka (thibboth) map
    # karanawa, "mute" nam kisima audio input ekak danne na (silent output),
    # "replace" nam original eka mute karala aluth audio_path eka map karanawa -
    # eka video ekata wada podi nam "loop" fit eken -stream_loop karanawa,
    # ehema natthang okkoma global -t eken automatically trim wenawa
    audio_map_args: list[str] = []
    if audio_mode == "replace" and audio_path:
        if audio_fit == "loop":
            inputs += ["-stream_loop", "-1", "-i", audio_path]
        else:
            inputs += ["-i", audio_path]
        audio_map_args = ["-map", f"{input_idx}:a"]
    elif audio_mode == "keep":
        audio_map_args = ["-map", "0:a?"]
    # audio_mode == "mute" (or "replace" without an audio_path) -> no -map for audio

    # intro eka thibba nam, audio ekath (thibba nam witharai) e welawatama
    # "fade in" karanawa - video eke black fade ekata sync wena audio fade-in
    # ekak. "-map 0:a?" optional nisa audio track ekak nathnam methanin -af
    # ekata apply karanna deyak nehe (error ekak wenne na).
    audio_filter_args: list[str] = []
    if intro_seconds > 0 and audio_map_args:
        audio_filter_args = ["-af", f"afade=t=in:st=0:d={intro_seconds}"]


    cmd = [
        "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
        *inputs,
        "-filter_complex", filter_complex,
        "-map", "[out]", *audio_map_args, *audio_filter_args,
        "-t", str(total_duration),
        "-c:v", "libx264", "-preset", BG_VIDEO_PRESET, "-crf", BG_VIDEO_CRF,
        "-c:a", "aac", "-movflags", "+faststart",
        # -progress pipe:1 dunoth ffmpeg eken stdout ekata "key=value" progress
        # lines (out_time_ms=..., progress=continue/end) machine-readable widiyata
        # yawanawa - eken live % ekak calculate karala progress_cb ekata denawa
        "-progress", "pipe:1", "-nostats",
        str(out_path),
    ]

    process = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )

    last_reported = -1
    stderr_chunks: list[bytes] = []

    async def _report(pct: int):
        nonlocal last_reported
        last_reported = pct
        if progress_cb is None:
            return
        try:
            await progress_cb(pct)
        except Exception:
            logger.exception("compose_video_background progress_cb failed, ignoring")

    async def _read_stdout():
        assert process.stdout is not None
        async for raw_line in process.stdout:
            line = raw_line.decode("utf-8", errors="ignore").strip()
            if line.startswith("out_time_ms="):
                try:
                    out_time_us = int(line.split("=", 1)[1])
                except ValueError:
                    continue
                if total_duration > 0:
                    # ffmpeg output eka thawath "us" ekak nemei, "microseconds"
                    # ekakma (key eke name eka "ms" unath) - 1_000_000 walin
                    # bahinawa seconds walata convert karanna
                    pct = max(0, min(99, int((out_time_us / 1_000_000) / total_duration * 100)))
                    if pct - last_reported >= BG_VIDEO_PROGRESS_MIN_STEP:
                        await _report(pct)
            elif line == "progress=end" and last_reported < 100:
                await _report(100)

    async def _read_stderr():
        assert process.stderr is not None
        async for chunk in process.stderr:
            stderr_chunks.append(chunk)

    await asyncio.gather(_read_stdout(), _read_stderr())
    returncode = await process.wait()
    if returncode != 0:
        raise subprocess.CalledProcessError(
            returncode, cmd, output=b"", stderr=b"".join(stderr_chunks)
        )

    return str(out_path)


def _selfblur_bg_fg_filter(canvas_w: int, canvas_h: int, blur_px: int, fg_scale_pct: int,
                            fg_y_offset_pct: int, blur_type: str = SELFBLUR_BLUR_TYPE_DEFAULT,
                            chromatic_aberration: bool = CHROMATIC_ABERRATION_DEFAULT,
                            chromatic_shift: int = CHROMATIC_SHIFT_DEFAULT,
                            vhs_effect: bool = VHS_EFFECT_DEFAULT,
                            vhs_strength: int = VHS_STRENGTH_DEFAULT,
                            overlay_opacity_pct: int = SELFBLUR_OVERLAY_OPACITY_DEFAULT,
                            bg_kind: str = SELFBLUR_BG_KIND_DEFAULT,
                            bg_color: str = SELFBLUR_BG_COLOR_DEFAULT,
                            bg_input_label: str | None = None,
                            bg_blur_enabled: bool = True,
                            layout_mode: str = "standard") -> tuple[list[str], str]:
    """compose_self_blur_video() saha render_selfblur_preview_frame() dekamatama
    share karana core filter eka - "background layer + center clear fg ->
    overlay" chain eka. (filter_parts list eka, last output label eka) return
    karanawa - caller eka [input_idx:v] ewa ithuru karanna (watermark/text
    overlay) hari, output map karanna hari use karanawa.

    bg_kind:
      "blur" (default)  - danata pattern eka: "[0:v]" eka dedena kotasakata
                           split karala, ekak full-canvas fill+gblur karala
                           background widiyata, anith eka clear/sharp fg.
      "color"            - solid fill ekak (bg_color hex) - "0:v" split
                            karanne na, fg eka "[0:v]" ekenma direct.
      "image" / "video"  - bg_input_label eken danapu wenama ffmpeg input
                            ekak (custom bg upload eka) background widiyata -
                            fg eka methedi thawath "[0:v]" ekenma direct.
                            bg_blur_enabled=True nam methanatath gblur/
                            chromatic/vhs chain eka apply wenawa.

    blur_type/chromatic/vhs - compose_video_background() eke widiyatama, mee
    okkoma bg layer ekatama witharak apply wenawa (blur ekama pattern eka) -
    center eke clear/sharp fg video eka methen touch wenne na."""
    sigma = float(blur_px)
    # "motion" nam vertical sigma eka podi ekaka fix karala (streak look eka),
    # "gaussian" nam dekama sama - compose_video_background() ekema logic eka
    sigma_v = sigma if blur_type == "gaussian" else min(sigma, MOTION_BLUR_SIGMA_V)
    blur_stage = f"gblur=sigma={sigma}:sigmaV={sigma_v}" if sigma > 0 else "null"

    bg_stage_parts = [blur_stage]
    if chromatic_aberration:
        shift = max(CHROMATIC_SHIFT_MIN, min(CHROMATIC_SHIFT_MAX, int(chromatic_shift)))
        bg_stage_parts.append(f"rgbashift=rh=-{shift}:bh={shift}:edge=smear")
    if vhs_effect:
        strength = max(VHS_STRENGTH_MIN, min(VHS_STRENGTH_MAX, int(vhs_strength)))
        noise_amt = max(1, round(strength * 0.6))
        bg_stage_parts.append(f"noise=alls={noise_amt}:allf=t+u")
        bg_stage_parts.append("eq=saturation=1.15:contrast=1.05:brightness=0.01")
        bg_stage_parts.append("vignette=PI/5")
    bg_stage = ",".join(bg_stage_parts)

    fg_pct = max(10, min(100, int(fg_scale_pct)))
    fg_w_expr = f"trunc({canvas_w}*{fg_pct}/100/2)*2"

    # y-offset eka canvas height eken % ekak widiyata - foreground eka
    # canvas ekenma sampurnayenma pita yanna denne nathuwa clamp karanawa
    yoff_pct = max(-45, min(45, int(fg_y_offset_pct)))
    yoff_px = round(canvas_h * yoff_pct / 100)
    overlay_y_expr = f"(H-h)/2+{yoff_px}" if yoff_px >= 0 else f"(H-h)/2-{abs(yoff_px)}"

    bg_label = "bgblur"
    filter_parts: list[str] = []

    if bg_kind == "color":
        safe_color = (bg_color or SELFBLUR_BG_COLOR_DEFAULT).lstrip("#") or "000000"
        filter_parts.append(f"color=c=0x{safe_color}:s={canvas_w}x{canvas_h}[{bg_label}]")
        fg_source = "[0:v]"
    elif bg_kind in ("image", "video") and bg_input_label:
        stage = f",{bg_stage}" if (bg_blur_enabled and bg_stage != "null") else ""
        filter_parts.append(
            f"[{bg_input_label}]scale={canvas_w}:{canvas_h}:force_original_aspect_ratio=increase,"
            f"crop={canvas_w}:{canvas_h}{stage}[{bg_label}]"
        )
        fg_source = "[0:v]"
    else:   # "blur" (default) - source video ekemma blur karapu copy eka
        filter_parts.append("[0:v]split=2[bgsrc][fgsrc]")
        filter_parts.append(
            f"[bgsrc]scale={canvas_w}:{canvas_h}:force_original_aspect_ratio=increase,"
            f"crop={canvas_w}:{canvas_h},{bg_stage}[{bg_label}]"
        )
        fg_source = "[fgsrc]"

    # black overlay eka - blur karapu background layer ekatama witharai apply
    # wenawa (center clear video ekatai userge text/emoji ekatai methanata
    # kalinma, fg eka ekathu karanna kalinma insert karana nisa touch wenne
    # na) - text/emoji tika udata pennana widiyata opacity eka user ta
    # buttons walin adu/wadi karaganna puluwan.
    alpha = max(0, min(SELFBLUR_OVERLAY_OPACITY_MAX, int(overlay_opacity_pct))) / 100
    if alpha > 0:
        filter_parts.append(f"color=c=black@{alpha:.2f}:s={canvas_w}x{canvas_h}[blkov]")
        filter_parts.append(f"[{bg_label}][blkov]overlay=0:0[bgdark]")
        bg_label = "bgdark"

    filter_parts.append(f"{fg_source}scale={fg_w_expr}:-2[fg]")
    filter_parts.append(f"[{bg_label}][fg]overlay=(W-w)/2:{overlay_y_expr}[merged]")

    _last_label_fg = "merged"
    if layout_mode == "meme":
        # White divider lines: left vertical, right vertical, bottom horizontal
        # Bottom line is drawn before pad, so after pad it becomes the true canvas bottom
        _dw = MEME_DIVIDER_WIDTH
        _da = f"{MEME_DIVIDER_ALPHA:.2f}"
        filter_parts.append(
            f"[{_last_label_fg}]"
            f"drawbox=x=0:y=0:w={_dw}:h={canvas_h}:color=white@{_da}:t=fill,"
            f"drawbox=x={canvas_w - _dw}:y=0:w={_dw}:h={canvas_h}:color=white@{_da}:t=fill,"
            f"drawbox=x=0:y={canvas_h - _dw}:w={canvas_w}:h={_dw}:color=white@{_da}:t=fill"
            f"[merged_lines]"
        )
        _last_label_fg = "merged_lines"
        # MEME_BOX_H px sudu box eka udata add karala 1080x1080 square wenawa
        filter_parts.append(
            f"[{_last_label_fg}]pad=width={MEME_CANVAS_W}:height={MEME_VIDEO_H + MEME_BOX_H}"
            f":x=0:y={MEME_BOX_H}:color=white[padded]"
        )
        _last_label_fg = "padded"

    return filter_parts, _last_label_fg


async def render_selfblur_preview_frame(
    video_path: str,
    blur_px: int,
    fg_scale_pct: int,
    fg_y_offset_pct: int = 0,
    watermark_png_bytes: bytes | None = None,
    watermark_opacity: int = WATERMARK_OPACITY_DEFAULT,
    watermark_scale: int = WATERMARK_SCALE_DEFAULT,
    watermark_side: str = WATERMARK_SIDE_DEFAULT,
    text_overlay_png_bytes: bytes | None = None,
    blur_type: str = SELFBLUR_BLUR_TYPE_DEFAULT,
    chromatic_aberration: bool = CHROMATIC_ABERRATION_DEFAULT,
    chromatic_shift: int = CHROMATIC_SHIFT_DEFAULT,
    vhs_effect: bool = VHS_EFFECT_DEFAULT,
    vhs_strength: int = VHS_STRENGTH_DEFAULT,
    overlay_opacity_pct: int = SELFBLUR_OVERLAY_OPACITY_DEFAULT,
    bg_kind: str = SELFBLUR_BG_KIND_DEFAULT,
    bg_color: str = SELFBLUR_BG_COLOR_DEFAULT,
    bg_image_path: str | None = None,
    bg_video_path: str | None = None,
    bg_blur_enabled: bool = True,
    layout_mode: str = "standard",
) -> tuple[bytes, int, int]:
    """/selfblur ADJUSTING screen eke "live preview" ekata - full video render
    ekak karanna nathuwa, ekma blur/size/position filter chain ekama use
    karala frame ekak witharak (PNG) hariyata generate karanawa - video encode
    ekak nathi nisa fast (sub-second). (png bytes, canvas_w, canvas_h) return
    karanawa. watermark eka thibba nam e udinuth static frame ekaka penena
    widiyata danawa (scroll animation eka witharai skip wenne, position/opacity
    eka dan penei). text_overlay_png_bytes - user ge caption/emoji text eka
    (generate_image eken hදpu transparent PNG ekak, canvas size ekama) - danawa
    nam final render ekaka wagema text eka udin penei.

    bg_kind="image"/"video" nam, bg_image_path/bg_video_path (danata thiyena
    "🖼 Background" menu eken thoragapu custom background file eka) background
    widiyata use wenawa - "blur"/"color" walata mee dekama ignore wenawa."""
    src_w, src_h, _dur, _br = await probe_video(video_path)
    if layout_mode == "meme":
        canvas_w = MEME_CANVAS_W
        canvas_h = MEME_VIDEO_H
    else:
        canvas_w = max(2, (src_w // 2) * 2)
        canvas_h = max(2, (src_h // 2) * 2)

    tmp_dir = tempfile.mkdtemp(prefix="selfblur_prev_")
    inputs: list[str] = ["-i", video_path]
    input_idx = 1

    bg_input_label = None
    if bg_kind == "image" and bg_image_path and Path(bg_image_path).exists():
        inputs += ["-loop", "1", "-i", bg_image_path]
        bg_input_label = f"{input_idx}:v"
        input_idx += 1
    elif bg_kind == "video" and bg_video_path and Path(bg_video_path).exists():
        inputs += ["-i", bg_video_path]
        bg_input_label = f"{input_idx}:v"
        input_idx += 1

    filter_parts, last_label = _selfblur_bg_fg_filter(
        canvas_w, canvas_h, blur_px, fg_scale_pct, fg_y_offset_pct,
        blur_type=blur_type, chromatic_aberration=chromatic_aberration, chromatic_shift=chromatic_shift,
        vhs_effect=vhs_effect, vhs_strength=vhs_strength, overlay_opacity_pct=overlay_opacity_pct,
        bg_kind=bg_kind, bg_color=bg_color, bg_input_label=bg_input_label, bg_blur_enabled=bg_blur_enabled,
        layout_mode=layout_mode,
    )

    if text_overlay_png_bytes:
        txt_path = Path(tmp_dir) / "text_overlay.png"
        txt_path.write_bytes(text_overlay_png_bytes)
        inputs += ["-loop", "1", "-i", str(txt_path)]
        filter_parts.append(f"[{last_label}][{input_idx}:v]overlay=0:0[textmerged]")
        last_label = "textmerged"
        input_idx += 1

    if watermark_png_bytes:
        prepared = _prepare_watermark_png(watermark_png_bytes, canvas_w, watermark_opacity, watermark_scale)
        wm_path = Path(tmp_dir) / "watermark_preview.png"
        wm_path.write_bytes(prepared)
        inputs += ["-loop", "1", "-i", str(wm_path)]
        # static preview ekaka scroll animation eka pennanna bari nisa, side
        # ekata thani frame ekak vidiyata rest karanawa (danata thiyena side
        # ekedin witharai, "speed" eka meke relevant nehe)
        if layout_mode == "meme":
            # meme mode: center fg video bounds athulema witharai (blur/white box skip)
            _pv_fg_w = int(MEME_CANVAS_W * fg_scale_pct / 100 / 2) * 2
            _pv_left_x = (MEME_CANVAS_W - _pv_fg_w) // 2
            _pv_right_x = _pv_left_x + _pv_fg_w
            if watermark_side == "right":
                x_expr = f"{_pv_right_x}-w-{SIDE_PADDING}"
            else:
                x_expr = f"{_pv_left_x}+{SIDE_PADDING}"
            # y: video section bottom (not white box or blur zone)
            y_expr = f"{MEME_BOX_H}+{MEME_VIDEO_H}-h-40"
        else:
            x_expr = f"{SIDE_PADDING}" if watermark_side != "right" else f"W-w-{SIDE_PADDING}"
            y_expr = "H-h-40"
        filter_parts.append(f"[{last_label}][{input_idx}:v]overlay=x={x_expr}:y={y_expr}[wmmerged]")
        last_label = "wmmerged"
        input_idx += 1

    out_path = Path(tmp_dir) / "preview.png"
    filter_complex = ";".join(filter_parts) + f";[{last_label}]format=rgba[out]"
    cmd = [
        "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
        *inputs,
        "-filter_complex", filter_complex,
        "-map", "[out]",
        "-frames:v", "1",
        str(out_path),
    ]
    try:
        process = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
        )
        _out, err = await process.communicate()
        if process.returncode != 0:
            raise subprocess.CalledProcessError(process.returncode, cmd, output=b"", stderr=err)
        png_bytes = out_path.read_bytes()
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)

    return png_bytes, canvas_w, canvas_h


async def compose_self_blur_video(
    video_path: str,
    blur_px: int,
    fg_scale_pct: int,
    duration_seconds: float,
    progress_cb=None,
    audio_path: str | None = None,
    audio_mode: str = "keep",
    audio_fit: str = "trim_audio",
    fg_y_offset_pct: int = 0,
    watermark_png_bytes: bytes | None = None,
    watermark_opacity: int = WATERMARK_OPACITY_DEFAULT,
    watermark_scale: int = WATERMARK_SCALE_DEFAULT,
    watermark_direction: str = WATERMARK_DIRECTION_DEFAULT,
    watermark_speed: int = WATERMARK_SPEED_DEFAULT,
    watermark_side: str = WATERMARK_SIDE_DEFAULT,
    text_overlay_png_bytes: bytes | None = None,
    blur_type: str = SELFBLUR_BLUR_TYPE_DEFAULT,
    chromatic_aberration: bool = CHROMATIC_ABERRATION_DEFAULT,
    chromatic_shift: int = CHROMATIC_SHIFT_DEFAULT,
    vhs_effect: bool = VHS_EFFECT_DEFAULT,
    vhs_strength: int = VHS_STRENGTH_DEFAULT,
    intro_black_seconds: float = INTRO_BLACK_SECONDS_DEFAULT,
    overlay_opacity_pct: int = SELFBLUR_OVERLAY_OPACITY_DEFAULT,
    bg_kind: str = SELFBLUR_BG_KIND_DEFAULT,
    bg_color: str = SELFBLUR_BG_COLOR_DEFAULT,
    bg_image_path: str | None = None,
    bg_video_path: str | None = None,
    bg_blur_enabled: bool = True,
    layout_mode: str = "standard",
) -> str:
    """"Self-blur" background - ekma video eka dedena widiyata use karanawa:
    (1) full-canvas eka fill karana widiyata scale+crop karala gblur dapu
        "background" copy ekak, (2) e udinma podi (fg_scale_pct% width)
        clear/sharp copy ekak center karala danawa (TikTok/FB Reels walata
        thibba vertical video ekak "fill screen" karanna use karana trick eka).

    compose_video_background() ekaga wagema, wenama background video/image
    ekak danna one nehe - user danna video ekmai dekma layers walata source
    eka. Canvas size eka = original video eke dimensions (upscale karanne na).

    fg_scale_pct: center eke thiyena clear video eke width eka, canvas
    width eken % ekak widiyata (ex: 65 = canvas width eke 65%).
    fg_y_offset_pct: clear video eke vertical position eka, canvas height eke
    % ekak widiyata, vertical-center ekedin (+ = pahalata, - = udata). User ta
    "⬆️ Up / ⬇️ Down" buttons walin adjust karanna puluwan.
    blur_px: background layer ekata gblur sigma eka (0 = blur ekak nehe).

    audio_mode/audio_fit: compose_video_background() ekema semantics -
    "keep" (original audio), "mute", "replace" (audio_path eka danawa).
    """
    tmp_dir = tempfile.mkdtemp(prefix="selfblur_")
    out_path = Path(tmp_dir) / "final.mp4"

    src_w, src_h, _src_dur, _ = await probe_video(video_path)
    # Meme layout: fixed 1080x1080 square output (video area 1080x780 + 300px text box)
    # Standard: even dimensions force (libx264 walata width/height 2 walin divisible one)
    if layout_mode == "meme":
        canvas_w = MEME_CANVAS_W
        canvas_h = MEME_VIDEO_H
    else:
        canvas_w = max(2, (src_w // 2) * 2)
        canvas_h = max(2, (src_h // 2) * 2)

    input_idx = 1
    inputs: list[str] = ["-i", video_path]

    # danata thiyena "🖼 Background" setting eka "image"/"video" nam, custom
    # bg file eka thawath ffmpeg input ekak widiyata methanin ekathu
    # karanawa - filter eka call karanna kalinma (bg_input_label eka danna
    # one nisa). video bg eka -stream_loop -1 karala danawa - fg video eke
    # duration eken bagawathnam podda hutuwath, "-t total_duration" (pahalin)
    # eken loop wela full duration ekatama thiyenna.
    bg_input_label = None
    if bg_kind == "image" and bg_image_path and Path(bg_image_path).exists():
        inputs += ["-loop", "1", "-i", bg_image_path]
        bg_input_label = f"{input_idx}:v"
        input_idx += 1
    elif bg_kind == "video" and bg_video_path and Path(bg_video_path).exists():
        inputs += ["-stream_loop", "-1", "-i", bg_video_path]
        bg_input_label = f"{input_idx}:v"
        input_idx += 1

    filter_parts, last_label = _selfblur_bg_fg_filter(
        canvas_w, canvas_h, blur_px, fg_scale_pct, fg_y_offset_pct,
        blur_type=blur_type, chromatic_aberration=chromatic_aberration, chromatic_shift=chromatic_shift,
        vhs_effect=vhs_effect, vhs_strength=vhs_strength, overlay_opacity_pct=overlay_opacity_pct,
        bg_kind=bg_kind, bg_color=bg_color, bg_input_label=bg_input_label, bg_blur_enabled=bg_blur_enabled,
        layout_mode=layout_mode,
    )

    # user caption/emoji text ekak type karala thibba nam (WAITING_SELFBLUR_TEXT
    # step eke), e text eka generate_image() eken hadapu transparent PNG ekak
    # (canvas size ekama) - watermark ekatath kalinma methanin overlay karanawa,
    # ithin watermark eka hamadaman text eke udinma penei (main flow eke
    # logo/text order ekama).
    if text_overlay_png_bytes:
        txt_path = Path(tmp_dir) / "text_overlay.png"
        txt_path.write_bytes(text_overlay_png_bytes)
        inputs += ["-loop", "1", "-i", str(txt_path)]
        filter_parts.append(f"[{last_label}][{input_idx}:v]overlay=0:0[textmerged]")
        last_label = "textmerged"
        input_idx += 1

    wm_path = None
    if watermark_png_bytes:
        prepared = _prepare_watermark_png(watermark_png_bytes, canvas_w, watermark_opacity, watermark_scale)
        wm_path = Path(tmp_dir) / "watermark.png"
        wm_path.write_bytes(prepared)

    if wm_path:
        inputs += ["-loop", "1", "-i", str(wm_path)]
        if layout_mode == "meme":
            # Meme mode: watermark eka center fg video area athulema witharai scroll wenawa
            # (blur area walata / sudu box ekata yanna bh)
            _wm_fg_w = int(MEME_CANVAS_W * fg_scale_pct / 100 / 2) * 2
            _wm_left_x = (MEME_CANVAS_W - _wm_fg_w) // 2
            _wm_right_x = _wm_left_x + _wm_fg_w
            _wm_spd = max(1, int(watermark_speed))
            # Y: MEME_BOX_H ekedin pahalata witharai (sudu box eke uda area skip)
            if watermark_direction == "down_up":
                y_expr = f"{MEME_BOX_H}+{MEME_VIDEO_H}-mod(t*{_wm_spd}\\,({MEME_VIDEO_H}+h))"
            else:
                y_expr = f"{MEME_BOX_H}+mod(t*{_wm_spd}\\,({MEME_VIDEO_H}+h))-h"
            # X: fg video horizontal bounds athulema (blur area skip)
            if watermark_side == "right":
                x_expr = f"{_wm_right_x}-w-{SIDE_PADDING}"
            else:
                x_expr = f"{_wm_left_x}+{SIDE_PADDING}"
        else:
            x_expr, y_expr = _watermark_overlay_expr(watermark_direction, watermark_speed, watermark_side)
        filter_parts.append(
            f"[{last_label}][{input_idx}:v]overlay=x='{x_expr}':y='{y_expr}':eval=frame:format=auto,"
            f"scale=trunc(iw/2)*2:trunc(ih/2)*2,format=yuv420p[content]"
        )
        input_idx += 1
    else:
        filter_parts.append(f"[{last_label}]scale=trunc(iw/2)*2:trunc(ih/2)*2,format=yuv420p[content]")
    last_label = "content"

    # video intro fade (compose_video_background() ekema "black enter" effect eka)
    intro_seconds = max(0.0, float(intro_black_seconds))
    if intro_seconds > 0:
        filter_parts.append(f"[{last_label}]fade=t=in:st=0:d={intro_seconds}:color=black[out]")
    else:
        filter_parts.append(f"[{last_label}]null[out]")

    filter_complex = ";".join(filter_parts)
    total_duration = duration_seconds

    audio_map_args: list[str] = []
    if audio_mode == "replace" and audio_path:
        if audio_fit == "loop":
            inputs += ["-stream_loop", "-1", "-i", audio_path]
        else:
            inputs += ["-i", audio_path]
        audio_map_args = ["-map", f"{input_idx}:a"]
    elif audio_mode == "keep":
        audio_map_args = ["-map", "0:a?"]
    # audio_mode == "mute" -> no -map for audio

    audio_filter_args: list[str] = []
    if intro_seconds > 0 and audio_map_args:
        audio_filter_args = ["-af", f"afade=t=in:st=0:d={intro_seconds}"]

    cmd = [
        "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
        *inputs,
        "-filter_complex", filter_complex,
        "-map", "[out]", *audio_map_args, *audio_filter_args,
        "-t", str(total_duration),
        "-c:v", "libx264", "-preset", BG_VIDEO_PRESET, "-crf", BG_VIDEO_CRF,
        "-c:a", "aac", "-movflags", "+faststart",
        "-progress", "pipe:1", "-nostats",
        str(out_path),
    ]

    process = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )

    last_reported = -1
    stderr_chunks: list[bytes] = []

    async def _report(pct: int):
        nonlocal last_reported
        last_reported = pct
        if progress_cb is None:
            return
        try:
            await progress_cb(pct)
        except Exception:
            logger.exception("compose_self_blur_video progress_cb failed, ignoring")

    async def _read_stdout():
        assert process.stdout is not None
        async for raw_line in process.stdout:
            line = raw_line.decode("utf-8", errors="ignore").strip()
            if line.startswith("out_time_ms="):
                try:
                    out_time_us = int(line.split("=", 1)[1])
                except ValueError:
                    continue
                if total_duration > 0:
                    pct = max(0, min(99, int((out_time_us / 1_000_000) / total_duration * 100)))
                    if pct - last_reported >= BG_VIDEO_PROGRESS_MIN_STEP:
                        await _report(pct)
            elif line == "progress=end" and last_reported < 100:
                await _report(100)

    async def _read_stderr():
        assert process.stderr is not None
        async for chunk in process.stderr:
            stderr_chunks.append(chunk)

    await asyncio.gather(_read_stdout(), _read_stderr())
    returncode = await process.wait()
    if returncode != 0:
        raise subprocess.CalledProcessError(
            returncode, cmd, output=b"", stderr=b"".join(stderr_chunks)
        )

    return str(out_path)


async def _run_ffmpeg_with_timeout(cmd: list[str], duration_seconds: float, timeout: float, progress_cb=None):
    """ffmpeg command ekak `-progress pipe:1` output eken 0-100% progress
    track karagena run karanawa, HARD TIMEOUT ekak ekka. Meka thamai
    watermark preview eka "godak welavak balan innna" wenna hodhi - kalinma
    code eke methanin timeout ekak thibbenne nehe, ffmpeg eka busy/slow
    server ekaka hang unoth ada indefinite widiyata block wenawa. Dæn,
    `timeout` seconds ganan athule ivara vunne nathnam process eka
    `.kill()` karala, `asyncio.TimeoutError` raise karanawa - caller ekata
    ithuru fallback tier ekakata (hari static frame ekakata) yanna puluwan.
    """
    process = await asyncio.create_subprocess_exec(
        *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
    )
    stderr_chunks: list[bytes] = []
    last_reported = -1

    async def _report(pct: int):
        nonlocal last_reported
        if progress_cb is None or (pct != 100 and pct - last_reported < WATERMARK_PREVIEW_PROGRESS_MIN_STEP):
            return
        last_reported = pct
        try:
            await progress_cb(pct)
        except Exception:
            logger.exception("watermark preview progress_cb failed, ignoring")

    async def _read_stdout():
        assert process.stdout is not None
        async for raw_line in process.stdout:
            line = raw_line.decode("utf-8", errors="ignore").strip()
            if line.startswith("out_time_ms=") and duration_seconds > 0:
                try:
                    out_time_us = int(line.split("=", 1)[1])
                except ValueError:
                    continue
                pct = max(0, min(99, int((out_time_us / 1_000_000) / duration_seconds * 100)))
                await _report(pct)
            elif line == "progress=end":
                await _report(100)

    async def _read_stderr():
        assert process.stderr is not None
        async for chunk in process.stderr:
            stderr_chunks.append(chunk)

    try:
        await asyncio.wait_for(asyncio.gather(_read_stdout(), _read_stderr()), timeout=timeout)
        returncode = await asyncio.wait_for(process.wait(), timeout=5)
    except asyncio.TimeoutError:
        try:
            process.kill()
            await process.wait()
        except Exception:
            pass
        raise

    if returncode != 0:
        raise subprocess.CalledProcessError(returncode, cmd, output=b"", stderr=b"".join(stderr_chunks))


async def generate_watermark_preview(
    video_path: str,
    watermark_png_bytes: bytes,
    watermark_opacity: int,
    watermark_scale: int,
    watermark_direction: str,
    watermark_speed: int,
    watermark_side: str = WATERMARK_SIDE_DEFAULT,
    progress_cb=None,
    background_is_static_image: bool = False,
) -> tuple[str, bytes]:
    """Scrolling watermark eka preview karanna 3-tier fallback:
      tier 1 (normal) -> short low-res MP4, single-pass (no palette needed
                          for mp4 - GIF ekata wage 2 pass yanna one nehe)
      tier 2 (light)  -> tier 1 timeout/fail unoth, thawa podi/ikman MP4 ekak
      tier 3 (frame)  -> tier 2ath fail unoth, watermark eka overlay kara
                          static PNG frame ekak (opacity/scale/side check
                          karaganna, speed/scroll eka penenne nehe)
    Server busy/slow unath user ta *yamkisi* preview ekak (video nattham
    photo ekak) 100% ekakma guarantee wenna methanin try karanawa - "godak
    welavak balan innna" hari "kisima reply ekak nathuwa hang wenawa" kියන
    dekama methanin nawattanawa.

    Return: (media_kind, bytes) - media_kind eka "video" | "photo".
    progress_cb: optional async callable, `await progress_cb(pct:int)`
    widiyata tier 1/2 walata witharai call wenawa (tier 3 instant nisa
    ondak nehe).
    """

    async def _tier_video(width: int, seconds: float, timeout: float) -> bytes:
        tmp_dir = tempfile.mkdtemp(prefix="wmprev_")
        try:
            prepared = _prepare_watermark_png(watermark_png_bytes, width, watermark_opacity, watermark_scale)
            wm_path = Path(tmp_dir) / "wm.png"
            wm_path.write_bytes(prepared)
            out_path = Path(tmp_dir) / "preview.mp4"

            x_expr, y_expr = _watermark_overlay_expr(watermark_direction, watermark_speed, watermark_side)
            filter_complex = (
                f"[0:v]scale={width}:-2,fps=12[bg];"
                f"[bg][1:v]overlay=x='{x_expr}':y='{y_expr}':eval=frame:format=auto,format=yuv420p[out]"
            )
            # -threads 1 - podi VPS ekaka decode/filter/encode dekama parallel
            # threads ganan wadi wunoth, per-thread frame buffers ekath
            # ekathu wela peak memory eka wadi wenawa - preview ekakata eka
            # awoid karanna thread eka 1kata limit karanawa.
            # thani photo ekak (static image) background ekak nam - "-loop 1"
            # nathuwa ffmpeg eken 1 frame ekak witharai dena nisa, scroll
            # animation eka penne na (video wagema loop karanna one)
            bg_input_args = (["-loop", "1", "-t", str(seconds), "-i", video_path]
                              if background_is_static_image else ["-t", str(seconds), "-i", video_path])
            cmd = [
                "ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-threads", "1",
                *bg_input_args,
                "-loop", "1", "-i", str(wm_path),
                "-filter_complex", filter_complex,
                "-map", "[out]", "-an",
                "-t", str(seconds),
                "-c:v", "libx264", "-preset", "ultrafast", "-crf", "24",
                "-movflags", "+faststart",
                "-progress", "pipe:1", "-nostats",
                str(out_path),
            ]
            await _run_ffmpeg_with_timeout(cmd, seconds, timeout, progress_cb)
            if not out_path.exists():
                raise RuntimeError("preview mp4 file eka hadenna baye")
            return out_path.read_bytes()
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)

    async def _tier_frame() -> bytes:
        tmp_dir = tempfile.mkdtemp(prefix="wmframe_")
        try:
            prepared = _prepare_watermark_png(
                watermark_png_bytes, WATERMARK_PREVIEW_WIDTH, watermark_opacity, watermark_scale
            )
            wm_path = Path(tmp_dir) / "wm.png"
            wm_path.write_bytes(prepared)
            out_path = Path(tmp_dir) / "frame.png"

            # meka static frame ekak witharai nisa scroll (y) eka use karanne
            # nehe (t=0 ekedi watermark eka canvas eken pita idan tibbenna
            # puluwan) - vertically center karala, x (side) eka witharak
            # real setting ekatama danawa, ithin opacity/scale/side ewa
            # check karaganna puluwan (speed/direction eka penenne nehe)
            x_expr, _ = _watermark_overlay_expr(watermark_direction, watermark_speed, watermark_side)
            filter_complex = (
                f"[0:v]scale={WATERMARK_PREVIEW_WIDTH}:-2[bg];"
                f"[bg][1:v]overlay=x='{x_expr}':y='(H-h)/2':format=auto[out]"
            )
            bg_input_args = (["-loop", "1", "-i", video_path]
                              if background_is_static_image else ["-i", video_path])
            cmd = [
                "ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-threads", "1",
                *bg_input_args, "-loop", "1", "-i", str(wm_path),
                "-filter_complex", filter_complex,
                "-map", "[out]", "-frames:v", "1",
                str(out_path),
            ]
            await _run_ffmpeg_with_timeout(cmd, 0, WATERMARK_PREVIEW_FRAME_TIMEOUT, None)
            if not out_path.exists():
                raise RuntimeError("preview frame eka hadenna baye")
            return out_path.read_bytes()
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)

    try:
        data = await _tier_video(WATERMARK_PREVIEW_WIDTH, WATERMARK_PREVIEW_SECONDS, WATERMARK_PREVIEW_TIMEOUT)
        return "video", data
    except Exception:
        logger.warning("Watermark preview tier 1 (normal) failed, trying lighter tier", exc_info=True)

    try:
        data = await _tier_video(
            WATERMARK_PREVIEW_LIGHT_WIDTH, WATERMARK_PREVIEW_LIGHT_SECONDS, WATERMARK_PREVIEW_LIGHT_TIMEOUT
        )
        return "video", data
    except Exception:
        logger.warning("Watermark preview tier 2 (light) failed, falling back to a static frame", exc_info=True)

    data = await _tier_frame()
    return "photo", data


PREVIEW_BG = "#808080"   # black text button ekath penennata (pure black bg ekaka black text penne nehe)


# "..." walin wahapu pramukhathama kotasa header ekak vidihata gannawa - ithuru
# text eka (quote eken pita/asala) body ekak vidihata gannawa. Quote ekak
# nathnam, ho quote athule blank nam, header ekak vidihata gannne na (raw
# text eka ekamawa body vidihata pennanawa - kalinma behavior eka).
HEADER_QUOTE_PATTERN = re.compile(r'"(.+?)"', re.DOTALL)


def split_header_text(raw_text: str) -> tuple[str | None, str]:
    match = HEADER_QUOTE_PATTERN.search(raw_text or "")
    if not match:
        return None, raw_text
    header_text = match.group(1).strip()
    if not header_text:
        return None, raw_text
    body_text = (raw_text[:match.start()] + raw_text[match.end():]).strip("\n")
    return header_text, body_text


# user ta text eke specific kotasak witharak ##bold## widiyatath, //italic//
# widiyatath, ^loku/highlight^ widiyatath (mekath ekathu karala ##^text^##
# wage ordar ekakin combine karanth) type karagannna puluwan.
#
# Meka dan (pahala) old alternation-regex ekak nemei, "toggle tokenizer"
# ekak - ##, //, ^ tunama ekineka wenas independent flags (bold/italic/
# highlight) widiyata therum ganna, delimiter ekak hambunu særy ee flag eka
# ON/OFF karanawa. Ithin ##//text//## widiyatath, //##text##// widiyatath,
# ^##text##^ widiyatath - close karana order eka monawa una vunath (##//..##//
# wage waradi close order ekak unath) hariyata parse wenawa, danna ##/// wage
# dedena delimiters ekaka combo walata witharak wada karana kalin
# "stack-based" approach ekaka thibba edge-case bugs valin nathiwa.
_MARKUP_TOKEN_PATTERN = re.compile(r'##|//|\^')


# http:// ho https:// wage link ekak text eke thiyenawa nam, ee link eke
# "//" dekama italic delimiter widiyata therum ganna epa - ehema unoth link
# eka mැදින් kadala/wenas karala danawa. Ithin markup tokenizer eka run
# karanna kalin, link tika methanin welak karala "protect" karala thiyenawa.
_URL_PATTERN = re.compile(r'(?:https?://|www\.)\S+', re.IGNORECASE)


def _render_markup_segment(
    segment: str,
    highlight_scale: float = HIGHLIGHT_FONT_SCALE_DEFAULT,
    highlight_bold: bool = HIGHLIGHT_BOLD_DEFAULT,
    highlight_italic: bool = HIGHLIGHT_ITALIC_DEFAULT,
) -> str:
    """Link ekak nathi (ho link ekakin welak kala) plain text kotasak witharak
    methanata ennne - meke witharai ##/// / ^ markup ekata check karanawa.
    bold/italic/highlight tuna ekineka independent toggle widiyata therum
    ganna nisa, ##^text^## wage ordar ekaka danapu combo ekakuth,
    ^##text##^ wage venath ordar ekakuth dekama hariyata support wenawa.
    highlight_scale/bold/italic - "🔆 Highlight" submenu eke user danapu
    settings, ^^ athule kotasata witharak apply wenawa (body text ekata
    effect ekak nehe)."""
    bold = italic = highlight = False
    out_parts = []
    buf = []

    def flush():
        chunk = "".join(buf)
        buf.clear()
        if not chunk:
            return
        chunk = html_module.escape(chunk)
        if highlight:
            style_bits = [f"font-size:{highlight_scale}em"]
            if highlight_bold:
                style_bits.append("font-weight:700")
            if highlight_italic:
                style_bits.append("font-style:italic")
            chunk = f"<span style=\"{';'.join(style_bits)}\">{chunk}</span>"
        if italic:
            chunk = f"<i>{chunk}</i>"
        if bold:
            chunk = f"<b>{chunk}</b>"
        out_parts.append(chunk)

    pos = 0
    for m in _MARKUP_TOKEN_PATTERN.finditer(segment):
        buf.append(segment[pos:m.start()])
        flush()
        token = m.group(0)
        if token == "##":
            bold = not bold
        elif token == "//":
            italic = not italic
        else:  # "^"
            highlight = not highlight
        pos = m.end()
    buf.append(segment[pos:])
    flush()
    return "".join(out_parts)


def render_inline_markup(
    line: str,
    highlight_scale: float = HIGHLIGHT_FONT_SCALE_DEFAULT,
    highlight_bold: bool = HIGHLIGHT_BOLD_DEFAULT,
    highlight_italic: bool = HIGHLIGHT_ITALIC_DEFAULT,
) -> str:
    # line eke link (http://, https://, www.) thiyena kotas welak karala,
    # ithuru non-link kotas witharak markup ekata (## / //) check karanawa -
    # link eke "//" ekata italic widiyata therum genna epa nisa.
    parts = []
    last_end = 0
    for m in _URL_PATTERN.finditer(line):
        parts.append(_render_markup_segment(line[last_end:m.start()], highlight_scale, highlight_bold, highlight_italic))
        parts.append(html_module.escape(m.group(0)))   # link eka markup ekata check karanne na
        last_end = m.end()
    parts.append(_render_markup_segment(line[last_end:], highlight_scale, highlight_bold, highlight_italic))
    return "".join(parts)


# user ##/// wrong widiyata (close karanna amathaka una, symbol dekak mix
# una wage) type kaloth, e post eka silently wenas widiyaka render wenawa
# (## / // characters ekama literal widiyata penila). Ithin post eka
# generate karanna kalinma, methanin hoyala user ta "ehema thiyenawa" kiyala
# kalin danawa - line ekaka ## count eka ho // count eka odd nam (close
# karala nathi widiyata), ee gana warning ekak dennawa. Link (http/https/
# www) walata udin thiyena "//" tika count karanne na.
def find_markup_issues(text: str) -> list[str]:
    issues = []
    for i, line in enumerate((text or "").split("\n"), start=1):
        stripped = _URL_PATTERN.sub("", line)
        if stripped.count("##") % 2 != 0:
            issues.append(f"Line {i}: `##` sign eka close karala නෑ")
        if stripped.count("//") % 2 != 0:
            issues.append(f"Line {i}: `//` sign eka close karala නෑ")
        if stripped.count("^") % 2 != 0:
            issues.append(f"Line {i}: `^` sign eka close karala නෑ")
    return issues


def _build_utf16_index_map(text: str) -> list[int]:
    """text eke character ekak ithuru utf-16 code unit "cumulative end offset"
    tika methanin denawa - Telegram entity offset/length (elawenne utf-16
    units walin) Python string index ekakata convert karanna methana use
    karanawa (emoji wage BMP eken pita characters walata utf-16 eken 2ක්
    one wenawa, Python string ekaka ekak witharak nisa)."""
    offsets = [0]
    total = 0
    for ch in text:
        total += 2 if ord(ch) > 0xFFFF else 1
        offsets.append(total)
    return offsets


def apply_native_formatting_as_markup(text: str, entities) -> str:
    """User Telegram app eke bold/italic button ekenma (**text** type kaloth
    ho selection eka select karala bold/italic dunnoth) format kala kotas -
    ee widiyata format kaloth, bot ekata plain text ekama enne (** ehema
    symbols message eke thiyenne na), ee wenuwata "entities" kiyana
    metadata (type, offset, length - utf-16 units walin) witharak enawa.
    Ithin bot eke ##/// tokenizer ekata e range eka "hambenne" naha, e
    kotasa render wenne plain widiyatama.

    Meka e entities tika kiyawala, e range walata ##.../ //.../ (bold+
    italic dekama thibba nam ##//.../ ) markers dala, user type kala
    ##/// markup ekama pipeline ekatama merge karanawa - dෙකම (Telegram-
    native formatting ekath, ##/// ekath) ekapaarata support wenna."""
    if not entities or not text:
        return text

    n = len(text)
    bold_mask = [False] * n
    italic_mask = [False] * n
    offsets = _build_utf16_index_map(text)
    has_any = False

    for ent in entities:
        etype = getattr(ent, "type", None)
        if etype not in ("bold", "italic"):
            continue
        start_py = bisect.bisect_left(offsets, ent.offset)
        end_py = bisect.bisect_left(offsets, ent.offset + ent.length)
        start_py = max(0, min(start_py, n))
        end_py = max(start_py, min(end_py, n))
        if end_py <= start_py:
            continue
        has_any = True
        for i in range(start_py, end_py):
            if etype == "bold":
                bold_mask[i] = True
            else:
                italic_mask[i] = True

    if not has_any:
        return text

    parts = []
    i = 0
    while i < n:
        b, it = bold_mask[i], italic_mask[i]
        j = i
        while j < n and bold_mask[j] == b and italic_mask[j] == it:
            j += 1
        chunk = text[i:j]
        if b and it:
            parts.append(f"##//{chunk}//##")
        elif b:
            parts.append(f"##{chunk}##")
        elif it:
            parts.append(f"//{chunk}//")
        else:
            parts.append(chunk)
        i = j
    return "".join(parts)


def build_html(text, emoji_items, font_b64, font_size, emoji_size, text_color, transparent: bool, font_weight: int = FONT_WEIGHT_DEFAULT, italic: bool = False, align: str = ALIGN_DEFAULT, bg_color: str = "#000000", canvas_width: int = IMG_SIZE, canvas_height: int = IMG_SIZE, bg_image_b64: str | None = None, overlay_opacity: float = 0.0, text_offset_y: int = 0, blur_px: int = 0, blur_type: str = BLUR_TYPE_DEFAULT, logo_kind: str | None = None, logo_value: str | None = None, logo_width_px: int = 0, logo_font_size_px: int = 0, logo_offset_bottom: int = LOGO_OFFSET_DEFAULT, logo_opacity: int = LOGO_OPACITY_DEFAULT, header_text: str | None = None, header_font_size: int = HEADER_FONT_SIZE_DEFAULT, header_color: str = HEADER_COLOR_DEFAULT, header_bold: bool = HEADER_BOLD_DEFAULT, header_gap_top: int = HEADER_GAP_TOP_DEFAULT, header_gap_bottom: int = HEADER_GAP_BOTTOM_DEFAULT, highlight_font_scale: float = HIGHLIGHT_FONT_SCALE_DEFAULT, highlight_bold: bool = HIGHLIGHT_BOLD_DEFAULT, highlight_italic: bool = HIGHLIGHT_ITALIC_DEFAULT, stroke_width: float = STROKE_WIDTH_DEFAULT, stroke_color: str = STROKE_COLOR_DEFAULT, emoji_offset_y: int = EMOJI_OFFSET_DEFAULT, text_area_height: int | None = None) -> str:
    # user enter kala widiyatama, e widiyatama line break wenna html-escape
    # karala (**bold** / _italic_ widiyata user danapu kotasval witharak
    # <b>/<i> tags walata render_inline_markup() eken convert karanawa)
    lines_html = "".join(
        f"<div class='line'>{render_inline_markup(line, highlight_font_scale, highlight_bold, highlight_italic) if line.strip() else '&nbsp;'}</div>"
        for line in text.split("\n")
    )
    # emoji_items eke tiyenne (kind, value) tuples - "img" nam CDN eken fetch
    # unu real emoji ekak (base64 png), "text" nam CDN eken image ekak hamba
    # unne na character ekak (" quote marks, ), : ithara punctuation ehema) -
    # e widiyata unath eka drop karanne nathuwa, user type kala e akurema
    # image ekata pennanna text vidihata methanin render karanawa. Order eka
    # user type kala order ekatama methanin ithuru wenawa (heart + quote nam
    # heart eka pahalin, quote eka passe pennanawa).
    parts = []
    for kind, value in emoji_items:
        if kind == "img":
            parts.append(f"<img class='emoji' src='data:image/png;base64,{value}'>")
        else:
            parts.append(f"<span class='emoji-text'>{html_module.escape(value)}</span>")
    emoji_html = "".join(parts)
    bg = "transparent" if transparent else bg_color
    font_weight_css = str(font_weight)
    font_style = "italic" if italic else "normal"
    # text-box eka + emoji row eka dekama meka side ekatama align wenawa
    align_items = ALIGN_ITEMS.get(align, ALIGN_ITEMS[ALIGN_DEFAULT])

    # logo eka text align eka anuwa side ekatama danna (left align nam logo
    # eka wamata, right align nam dakunata, center nam kalinma widiyatama
    # center ekata) - kalin logo eka hamotama center ekata fix wela thibba,
    # text align eka monaha unath logo position eka wenas wune na.
    LOGO_POSITION_CSS = {
        "left": f"left: {SIDE_PADDING}px;",
        "center": "left: 50%; transform: translateX(-50%);",
        "right": f"right: {SIDE_PADDING}px;",
    }
    logo_position_css = LOGO_POSITION_CSS.get(align, LOGO_POSITION_CSS[ALIGN_DEFAULT])

    # background photo ekak thiyenawanam, e eka canvas eka full ekatama danawa
    # (canvas eka photo ekema dimensions walata match wena nisa, crop/stretch
    # karanna one wenne nehe - "object-fit: cover" methanin danne safety
    # widiyata witharai). e udin, opacity adjustable black overlay ekak.
    # blur_px > 0 nam, image eka canvas eke sidin ithuru "overscan" ekakin
    # (110%, center karala) danawa - naththam blur eken edge walata thin
    # (blur wela nathi wage) rekha penenna puluwan, overscan eken eka clip
    # wenawa canvas eke pita bhaagayen.
    bg_image_html = (
        f"<div class='bg-blur-wrap'><img class='bg-image' src='data:image/png;base64,{bg_image_b64}'></div>"
        if bg_image_b64 else ""
    )
    # motion blur ekedi, plain CSS blur(Npx) ekata direction ekak dennna beri nisa
    # SVG feGaussianBlur ekak (horizontal strong, vertical podi) inline widiyata
    # danawa - meka preview ekedi witharai, final video ekedi ffmpeg gblur eken
    # ekamawagema (sigma/sigmaV) apply karanawa
    motion_svg_html = ""
    if bg_image_b64 and blur_type == "motion" and blur_px > 0:
        motion_svg_html = (
            "<svg width='0' height='0' style='position:absolute'>"
            "<filter id='motionBlurFilter'>"
            f"<feGaussianBlur stdDeviation='{blur_px} {max(0.5, blur_px * 0.15)}' />"
            "</filter></svg>"
        )
        bg_blur_css = "url(#motionBlurFilter)"
    else:
        bg_blur_css = f"blur({blur_px}px)"
    overlay_html = (
        f"<div class='overlay' style='background: rgba(0,0,0,{overlay_opacity});'></div>"
        if bg_image_b64 else ""
    )

    # user-uploaded PNG logo or plain-text logo/watermark, anchored bottom-
    # center and always drawn above the background/overlay/caption - user
    # controls its size (logo_width_px / logo_font_size_px) and vertical
    # position (logo_offset_bottom, px above the canvas bottom edge) via
    # the Adjust buttons.
    logo_inner_html = ""
    if logo_kind == "image" and logo_value:
        logo_inner_html = f"<img class='logo-image' src='data:image/png;base64,{logo_value}'>"
    elif logo_kind == "text" and logo_value:
        logo_inner_html = f"<div class='logo-text-el'>{html_module.escape(logo_value)}</div>"
    logo_html = f"<div class='logo-layer'>{logo_inner_html}</div>" if logo_inner_html else ""

    # user "" walin danapu header eka thiyenawa nam witharai methanin render
    # wenne - nathnam header-box eka ekkenma DOM eken ain wenawa (space ekakuth
    # ithuru wenne nehe, kalinma widiyatama body text eka witharai penenne)
    header_html = ""
    if header_text:
        header_weight = "700" if header_bold else "400"
        header_lines_html = "".join(
            f"<div class='line'>{render_inline_markup(line) if line.strip() else '&nbsp;'}</div>"
            for line in header_text.split("\n")
        )
        header_html = (
            f"<div class='header-box' style='color:{header_color}; font-size:{header_font_size}px; "
            f"font-weight:{header_weight}; margin-top:{header_gap_top}px; margin-bottom:{header_gap_bottom}px;'>"
            f"{header_lines_html}</div>"
        )

    # body text "stock" (stroke/outline) eka - width 0 nam property eka
    # ekkenma CSS ekata add karanne nathuwa (off state ekata clean). -webkit-
    # text-stroke eka Chromium ekedi (Playwright use karana browser eka)
    # hodatama support karanawa, paint-order eken stroke eka fill ekata
    # pahalin aandinawa (letter shape eka clean widiyata penna gannna).
    stroke_css = (
        f"-webkit-text-stroke: {stroke_width:g}px {stroke_color}; paint-order: stroke fill;"
        if stroke_width > 0 else ""
    )

    return f"""
    <html>
    <head>
    <style>
        @font-face {{
            font-family: 'CustomSinhala';
            src: url(data:font/ttf;base64,{font_b64}) format('truetype');
        }}
        html, body {{
            margin: 0; padding: 0;
            width: {canvas_width}px; height: {canvas_height}px;
            background: {bg};
            position: relative;
            overflow: hidden;
        }}
        .bg-blur-wrap {{
            position: absolute; top: 0; left: 0;
            width: 100%; height: 100%;
            overflow: hidden;
        }}
        .bg-image {{
            position: absolute; top: -6%; left: -6%;
            width: 112%; height: 112%;
            object-fit: cover;
            filter: {bg_blur_css};
        }}
        .overlay {{
            position: absolute; top: 0; left: 0;
            width: 100%; height: 100%;
        }}
        .wrap {{
            position: relative; z-index: 2;
            width: 100%; height: {text_area_height if text_area_height is not None else canvas_height}px;
            display: flex; flex-direction: column;
            align-items: {align_items}; justify-content: center;
            background: transparent;
            padding: 0 {SIDE_PADDING}px;
            box-sizing: border-box;
            transform: translateY({text_offset_y}px);
        }}
        .content-block {{
            display: flex;
            flex-direction: column;
            align-items: {align_items};
            width: 100%;
        }}
        .text-box {{
            font-family: 'CustomSinhala', sans-serif;
            color: {text_color};
            font-size: {font_size}px;
            font-weight: {font_weight_css};
            font-style: {font_style};
            line-height: 1.35;
            text-align: {align};
            max-width: {MAX_TEXT_WIDTH}px;
            {stroke_css}
        }}
        .line {{
            white-space: pre-wrap;
        }}
        .header-box {{
            font-family: 'CustomSinhala', sans-serif;
            line-height: 1.25;
            text-align: {align};
            max-width: {MAX_TEXT_WIDTH}px;
        }}
        .emojis {{
            margin-top: 26px;
            display: flex;
            align-items: center;
            justify-content: {align_items};
            gap: 0px;
            width: 100%;
            transform: translateY({emoji_offset_y}px);
        }}
        .emoji {{
            width: {emoji_size}px; height: {emoji_size}px;
            flex-shrink: 0;
        }}
        .emoji-text {{
            font-family: 'CustomSinhala', sans-serif;
            color: {text_color};
            font-size: {emoji_size}px;
            line-height: 1;
            flex-shrink: 0;
        }}
        .logo-layer {{
            position: absolute;
            {logo_position_css}
            bottom: {logo_offset_bottom}px;
            z-index: 5;
            display: flex;
            justify-content: center;
            align-items: center;
            pointer-events: none;
            opacity: {max(0, min(100, int(logo_opacity))) / 100};
        }}
        .logo-image {{
            width: {logo_width_px}px;
            height: auto;
            display: block;
        }}
        .logo-text-el {{
            font-family: 'CustomSinhala', sans-serif;
            color: #ffffff;
            font-size: {logo_font_size_px}px;
            font-weight: 700;
            white-space: nowrap;
        }}
    </style>
    </head>
    <body>
        {motion_svg_html}
        {bg_image_html}
        {overlay_html}
        <div class="wrap">
            <div class="content-block">
                {header_html}
                <div class="text-box">{lines_html}</div>
                <div class="emojis">{emoji_html}</div>
            </div>
        </div>
        {logo_html}
    </body>
    </html>
    """


def build_autofit_js(font_size: int, header_font_size: int | None = None, max_height: int | None = None, max_width: int | None = None) -> str:
    # kalinma .text-box eke height/width witharak check kalේ - e nisa header
    # ekak/emoji tikak thibboth, e tika ekathu karama block eka canvas eken
    # ithuruwela giyath, .text-box eka thanියම thani widiyata "maxHeight"
    # ekata adui unoth loop eka nawathinawa (thawath e uda header/emoji
    # thiyena eka gana ganne nathuwa) - eth nisama "kochchara podi kalath
    # wenasak na" widiyata penuna. Dan .content-block eka (header + text-box
    # + emojis okkoma ekatama) scrollHeight/scrollWidth eka check karanawa.
    #
    # Templates walin loku header size ekak save wela nam (body text eka
    # monaha unath), header eka witharama box eka overflow karanna puluwan -
    # e nisa body text eka kochchara podi kalath wenasak penne na, mokada
    # overflow eke ainma cause eka header eka una nisa. Dan body text eka
    # wagema header eka thiyenawa nam eeka ekath (headerFontSizeMin walata
    # adui wena vidiyata) ekathuwama shrink karanawa.
    header_size_js = "null" if header_font_size is None else str(header_font_size)
    return f"""
    () => {{
        const block = document.querySelector('.content-block');
        const box = document.querySelector('.text-box');
        const header = document.querySelector('.header-box');
        let size = {font_size};
        let headerSize = {header_size_js};
        const maxWidth = {max_width if max_width is not None else MAX_TEXT_WIDTH};
        const maxHeight = {max_height if max_height is not None else MAX_TEXT_HEIGHT};
        const minSize = {FONT_SIZE_MIN};
        const headerMinSize = {HEADER_FONT_SIZE_MIN};
        while (
            (block.scrollHeight > maxHeight || box.scrollWidth > maxWidth) &&
            (size > minSize || (header && headerSize !== null && headerSize > headerMinSize))
        ) {{
            if (size > minSize) {{
                size -= 2;
                box.style.fontSize = size + 'px';
            }}
            if (header && headerSize !== null && headerSize > headerMinSize) {{
                headerSize -= 2;
                header.style.fontSize = headerSize + 'px';
            }}
        }}
    }}
    """


async def generate_image(browser, text, emojis, font_size, emoji_size, text_color, transparent: bool = False, font_weight: int = FONT_WEIGHT_DEFAULT, italic: bool = False, align: str = ALIGN_DEFAULT, bg_color: str = "#000000", canvas_width: int = IMG_SIZE, canvas_height: int = IMG_SIZE, bg_image_b64: str | None = None, overlay_opacity: float = 0.0, text_offset_y: int = 0, blur_px: int = 0, blur_type: str = BLUR_TYPE_DEFAULT, logo_kind: str | None = None, logo_value: str | None = None, logo_scale: int = LOGO_SCALE_DEFAULT, logo_offset_bottom: int = LOGO_OFFSET_DEFAULT, logo_opacity: int = LOGO_OPACITY_DEFAULT, header_text: str | None = None, header_font_size: int = HEADER_FONT_SIZE_DEFAULT, header_color: str = HEADER_COLOR_DEFAULT, header_bold: bool = HEADER_BOLD_DEFAULT, header_gap_top: int = HEADER_GAP_TOP_DEFAULT, header_gap_bottom: int = HEADER_GAP_BOTTOM_DEFAULT, highlight_font_scale: float = HIGHLIGHT_FONT_SCALE_DEFAULT, highlight_bold: bool = HIGHLIGHT_BOLD_DEFAULT, highlight_italic: bool = HIGHLIGHT_ITALIC_DEFAULT, stroke_width: float = STROKE_WIDTH_DEFAULT, stroke_color: str = STROKE_COLOR_DEFAULT, emoji_offset_y: int = EMOJI_OFFSET_DEFAULT, autofit: bool = True, autofit_max_height: int | None = None, autofit_max_width: int | None = None, text_area_height: int | None = None) -> BytesIO:
    """browser eka welada denna ona - hama warak-ma aluthen launch karanne nehe, ehema kalot lag wenawa.
    canvas_width/canvas_height: background photo ekak upload kara nam, e photo eke
    ORIGINAL size ekama methanin use wenawa (crop/stretch karanne nehe).

    text_area_height: text/emoji block eka confine karanna one height eka canvas_height
    ekatama wada podi welak (ex: meme layout eke 300px sudu box eka, canvas eka 1080px
    unath) - danne nathnam canvas_height ekama use wenawa (kalinma widiyatama). Logo eka
    (.logo-layer) methanin affect wenne na - eka hamotama FULL canvas_height ekata
    relative widiyata (bottom: Npx) position wenawa, box eka athule "trapped" wenne na."""
    font_b64 = get_font_b64()

    emoji_items = []   # (kind, value) tuples, user type kala order ekatama
    for ch in split_graphemes(emojis):
        if ch.isspace():
            continue
        b64 = await fetch_apple_emoji_b64(ch)
        if b64:
            emoji_items.append(("img", b64))
        else:
            # CDN eke image ekak nathi character ekak (" quote, ), : ithara
            # punctuation) - drop karanne nathuwa, plain text vidihata pennanawa
            emoji_items.append(("text", ch))

    # single scale % drives either the image width or the text font-size,
    # whichever kind of logo is actually set
    logo_width_px = int(LOGO_IMG_BASE_WIDTH * logo_scale / 100) if logo_kind == "image" else 0
    logo_font_size_px = int(LOGO_TEXT_BASE_SIZE * logo_scale / 100) if logo_kind == "text" else 0

    html = build_html(
        text, emoji_items, font_b64, font_size, emoji_size, text_color, transparent, font_weight, italic, align,
        bg_color, canvas_width, canvas_height, bg_image_b64, overlay_opacity, text_offset_y, blur_px, blur_type,
        logo_kind, logo_value, logo_width_px, logo_font_size_px, logo_offset_bottom, logo_opacity=logo_opacity,
        emoji_offset_y=emoji_offset_y,
        header_text=header_text, header_font_size=header_font_size, header_color=header_color,
        header_bold=header_bold, header_gap_top=header_gap_top, header_gap_bottom=header_gap_bottom,
        highlight_font_scale=highlight_font_scale, highlight_bold=highlight_bold, highlight_italic=highlight_italic,
        stroke_width=stroke_width, stroke_color=stroke_color,
        text_area_height=text_area_height,
    )


    page = await browser.new_page(
        viewport={"width": canvas_width, "height": canvas_height},
        device_scale_factor=2,
    )
    try:
        await page.set_content(html)
        if autofit:
            await page.evaluate(build_autofit_js(font_size, header_font_size if header_text else None, max_height=autofit_max_height, max_width=autofit_max_width))
        screenshot = await page.screenshot(type="png", omit_background=transparent)
    finally:
        await page.close()

    hi_res = Image.open(BytesIO(screenshot)).convert("RGBA" if transparent else "RGB")
    final_img = hi_res.resize((canvas_width, canvas_height), Image.LANCZOS)

    buf = BytesIO()
    final_img.save(buf, format="PNG")
    buf.name = "post.png"
    buf.seek(0)
    return buf


# ---------------- KEYBOARDS ----------------

def color_keyboard(show_last_settings: bool) -> InlineKeyboardMarkup:
    rows = [
        [
            InlineKeyboardButton("🟡 Yellow", callback_data="color_yellow"),
            InlineKeyboardButton("🔴 Red", callback_data="color_red"),
        ],
        [
            InlineKeyboardButton("🔵 Blue", callback_data="color_blue"),
            InlineKeyboardButton("⚪ White", callback_data="color_white"),
        ],
        [
            InlineKeyboardButton("⚫ Black", callback_data="color_black"),
        ],
    ]
    if show_last_settings:
        rows.append(
            [InlineKeyboardButton("✨ Use last settings", callback_data="use_last_settings")]
        )
    return InlineKeyboardMarkup(rows)


def size_keyboard(has_bg_image: bool = False, logo_kind: str | None = None, active_template: str | None = None, has_header: bool = False, has_highlight: bool = False, has_bg_video: bool = False, watermark_enabled: bool = False, is_reedit: bool = False, bg_kind: str | None = None) -> InlineKeyboardMarkup:
    # Main menu eka dan "hub" ekak vidihata clean karala thiyenne - text/emoji/
    # effects/logo related okkoma buttons ("Header"/"Highlight" wagema pattern
    # ekak) wenama sub-menu ekakata damala, methanin witharak e sub-menu ekata
    # yanna button ekak pennanawa. Ithuru details text_keyboard/emoji_keyboard/
    # effects_keyboard/logo_keyboard functions walin.
    rows = [
        [
            InlineKeyboardButton("✏️ Text වෙනස් කරන්න", callback_data="adj_edit_text"),
        ],
        [
            InlineKeyboardButton("🔤 Text Settings", callback_data="adj_text_menu"),
            InlineKeyboardButton("😀 Emoji Settings", callback_data="adj_emoji_menu"),
        ],
    ]

    # user text eke "" header ekak dala nam witharai methanin "Header" button
    # eka pennanne - header ekak nathi post ekakata meka kisima thanaka penne nehe
    if has_header:
        rows.append([InlineKeyboardButton("🏷 Header", callback_data="adj_header_menu")])

    # text eke ^...^ (loku/highlight) block ekak thiyenawa nam witharai
    # methanin "Highlight" button eka pennanne - header button eka wagema
    if has_highlight:
        rows.append([InlineKeyboardButton("🔆 Highlight", callback_data="adj_highlight_menu")])

    # background photo ekak upload kara nam witharai "Background Effects"
    # (blur/overlay) sub-menu eka penenne - plain background ekata meka relevant na nisa
    if has_bg_image:
        rows.append([InlineKeyboardButton("🎛 Background Effects", callback_data="adj_effects_menu")])

    # thani photo background ekak witharai (dawasak downloaded video ekak
    # nemei) - photo eka + music ekak (ho silent) ekka video ekak vidihata
    # convert karana option eka. Convert karapu passe bg_kind "video" wena
    # nisa, methanin passe methe button eka penenne na (Scrolling Watermark
    # eka wagema has_bg_video check ekakma dan pennanawa)
    if bg_kind == "photo":
        rows.append([InlineKeyboardButton("🎬 Photo eka Video ekak karanna", callback_data="adj_convert_photo_video")])

    # Logo settings tika dan ekama button ekak - Header/Highlight wagema click
    # kalama sub-menu ekata yanawa (logo ekak set wela nathnam e sub-menu eke
    # "Add logo" button eka witharak penei).
    logo_label = "🏷 Logo Settings ✅" if logo_kind else "🏷 Logo Settings"
    rows.append([InlineKeyboardButton(logo_label, callback_data="adj_logo_menu")])

    # scrolling watermark eka - video background ekakata witharai relevant
    # (photo/plain background ekakata scroll animation ekak penne nehe nisa)
    if has_bg_video:
        wm_label = "🌀 Scrolling Watermark ✅" if watermark_enabled else "🌀 Scrolling Watermark"
        rows.append([InlineKeyboardButton(wm_label, callback_data="adj_watermark_menu")])

    # "Replace Video" / "Replace Audio" - Re-edit karapu passe witharai penenawa
    # (mulinma design karana welavata methanata one na, "Re-edit" click kalapu
    # passe witharak wadagath wenne background video eka dan set wela thiyena
    # nisa) - video background ekakata witharai relevant
    if is_reedit and has_bg_video:
        rows.append([
            InlineKeyboardButton("🎥 Replace Video", callback_data="adj_replace_video"),
            InlineKeyboardButton("🎵 Replace Audio", callback_data="adj_replace_audio"),
        ])

    if active_template:
        # dan pau (loaded) tibba template ekaka nama ahanne nathuwa, methanma
        # ekata directly overwrite karaganna "Update" button eka pennanawa -
        # aluthen "Save as Template" ekak witharak nam, edit karapu style eka
        # save karagatta kiyala "penuna nam eth ekata effect ekak una nehe"
        # wage confusion ekak thibba eka methanin fix karanawa
        label = f"🔄 Update '{active_template}' Template"
        if len(label.encode("utf-8")) > 60:   # button label digu unoth Telegram eken trim karanawa
            label = "🔄 Update Template"
        rows.append([InlineKeyboardButton(label, callback_data="adj_update_template")])
        rows.append([InlineKeyboardButton("💾 Save as New Template", callback_data="adj_save_template")])
    else:
        rows.append([InlineKeyboardButton("💾 Save as Template", callback_data="adj_save_template")])
    rows.append([InlineKeyboardButton("✅ Done", callback_data="adj_done")])
    return InlineKeyboardMarkup(rows)


def _align_button(key: str, align: str) -> InlineKeyboardButton:
    # dan select karala thiyena align eka, "✅" ekakin methanin
    # visible karanawa - user kenekta harida kiyala ekpalathama penna gannawa
    label = ALIGN_LABELS[key]
    if align == key:
        label = f"✅ {label}"
    return InlineKeyboardButton(label, callback_data=f"adj_align_{key}")


def text_keyboard(font_size: int = FONT_SIZE_DEFAULT, font_weight: int = FONT_WEIGHT_DEFAULT, italic: bool = ITALIC_DEFAULT, align: str = ALIGN_DEFAULT, has_bg_image: bool = False, text_offset_y: int = TEXT_OFFSET_DEFAULT, stroke_width: float = STROKE_WIDTH_DEFAULT, stroke_color: str = STROKE_COLOR_DEFAULT) -> InlineKeyboardMarkup:
    """"🔤 Text Settings" sub-menu eka - body text ekatama specific tika okkoma
    methanin (size, position, align, weight/italic, colour, stroke). Background photo
    ekak thibba nam witharai "text position" (up/down/recenter) row eka penenne
    - eka plain background ekakata relevant na nisa."""
    stroke_color_key = next((k for k, v in COLORS.items() if v == stroke_color), None)
    rows = [
        [
            InlineKeyboardButton("🔡 Text -", callback_data="adj_font_dec"),
            InlineKeyboardButton(f"🔠 {font_size}px", callback_data="adj_noop"),
            InlineKeyboardButton("🔠 Text +", callback_data="adj_font_inc"),
        ],
        [InlineKeyboardButton("♻️ Reset Size", callback_data="adj_font_reset")],
        # align ekata thani button 3k - kalin thibba "toggle/cycle" button ekedi
        # center ekata yanna left/right dekama passe kramayen click karanna one una,
        # eka nisa center eka "select wenne nathi wage" penuna. Dan hama option
        # ekakatama thani button ekak, ithin user ta ekpalatama center eka
        # direct click karagannna puluwan.
        [
            _align_button("left", align),
            _align_button("center", align),
            _align_button("right", align),
        ],
        [
            # Bold ON/OFF toggle ekata badulu, weight eka +/- karagannna puluwan
            # numeric control ekak - font file ekema single weight ekak witharai
            # thiyenne nisa, browser eka synthetic/faux-bold widiyata thickness
            # eka approximate karanawa (thin -> thick continuum ekak vidihata)
            InlineKeyboardButton("➖ Weight", callback_data="adj_weight_dec"),
            InlineKeyboardButton(f"🅱️ {font_weight}", callback_data="adj_noop"),
            InlineKeyboardButton("➕ Weight", callback_data="adj_weight_inc"),
        ],
        [InlineKeyboardButton("♻️ Reset Weight", callback_data="adj_weight_reset")],
        [
            InlineKeyboardButton(
                "🇮 Italic: ON" if italic else "🇮 Italic: OFF",
                callback_data="adj_italic_toggle",
            ),
        ],
        [
            InlineKeyboardButton("🎨 Colour", callback_data="adj_pick_color"),
        ],
        # akuru wala "stock" (stroke/outline) eka - font-weight wagema
        # ekpaharatama loku wenne nathuwa, 0.5px step ekakin gradual widiyata
        # akuru tika mahatha karaganna puluwan. width 0 nam stroke eka off,
        # ithin color buttons pennanne width > 0 unath witharai (chromatic
        # shift buttons wagema pattern ekama).
        [
            InlineKeyboardButton("➖ Stroke", callback_data="adj_stroke_dec"),
            InlineKeyboardButton(f"🖊 {stroke_width:g}px", callback_data="adj_noop"),
            InlineKeyboardButton("➕ Stroke", callback_data="adj_stroke_inc"),
        ],
    ]
    if stroke_width > 0:
        stroke_color_buttons = [
            InlineKeyboardButton(
                ("✅ " if stroke_color_key == key else "") + label,
                callback_data=f"adj_strokecolor_{key}",
            )
            for key, label in COLOR_LABELS.items()
        ]
        rows.append(stroke_color_buttons[:3])
        rows.append(stroke_color_buttons[3:])
    if has_bg_image:
        rows.append([
            InlineKeyboardButton("⬆️ Text up", callback_data="adj_text_up"),
            InlineKeyboardButton(f"↕️ {text_offset_y}px", callback_data="adj_noop"),
            InlineKeyboardButton("⬇️ Text down", callback_data="adj_text_down"),
        ])
        rows.append([InlineKeyboardButton("🎯 Recenter", callback_data="adj_text_recenter")])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="adj_text_back")])
    return InlineKeyboardMarkup(rows)


def emoji_keyboard(emoji_size: int = EMOJI_SIZE_DEFAULT) -> InlineKeyboardMarkup:
    """"😀 Emoji Settings" sub-menu eka - emoji size + reset witharak."""
    rows = [
        [
            InlineKeyboardButton("😀 Emoji +", callback_data="adj_emoji_inc"),
            InlineKeyboardButton("🙂 Emoji -", callback_data="adj_emoji_dec"),
            InlineKeyboardButton("♻️ Reset", callback_data="adj_emoji_reset"),
        ],
        [InlineKeyboardButton("🔙 Back", callback_data="adj_emoji_back")],
    ]
    return InlineKeyboardMarkup(rows)


def effects_keyboard(
    overlay_opacity: float = OVERLAY_OPACITY_DEFAULT,
    blur_px: int = BLUR_DEFAULT,
    blur_type: str = BLUR_TYPE_DEFAULT,
    chromatic_aberration: bool = CHROMATIC_ABERRATION_DEFAULT,
    chromatic_shift: int = CHROMATIC_SHIFT_DEFAULT,
    vhs_effect: bool = VHS_EFFECT_DEFAULT,
    vhs_strength: int = VHS_STRENGTH_DEFAULT,
    intro_black_seconds: float = INTRO_BLACK_SECONDS_DEFAULT,
) -> InlineKeyboardMarkup:
    """"🎛 Background Effects" sub-menu eka - background photo/video eka udin
    dana blur, chromatic aberration, VHS look, black overlay saha video intro
    (black screen) effects tika methanin (text position ekata methanin effect
    ekak nehe - eka "Text Settings" sub-menu ekedi)."""
    rows = [
        [
            InlineKeyboardButton(BLUR_TYPE_LABELS.get(blur_type, BLUR_TYPE_LABELS[BLUR_TYPE_DEFAULT]), callback_data="adj_blur_type_toggle"),
        ],
        [
            InlineKeyboardButton("🌫 Blur -", callback_data="adj_blur_dec"),
            InlineKeyboardButton(f"🌫 {blur_px}px", callback_data="adj_noop"),
            InlineKeyboardButton("🌫 Blur +", callback_data="adj_blur_inc"),
        ],
        [InlineKeyboardButton("♻️ Reset Blur", callback_data="adj_blur_reset")],
        [
            InlineKeyboardButton("🌑 Overlay -", callback_data="adj_overlay_dec"),
            InlineKeyboardButton(f"⬛ {round(overlay_opacity * 100)}%", callback_data="adj_noop"),
            InlineKeyboardButton("🌑 Overlay +", callback_data="adj_overlay_inc"),
        ],
        [InlineKeyboardButton("♻️ Reset Overlay", callback_data="adj_overlay_reset")],
        [
            InlineKeyboardButton(
                "🌈 Chromatic: ON" if chromatic_aberration else "🌈 Chromatic: OFF",
                callback_data="adj_chromatic_toggle",
            ),
        ],
    ]
    if chromatic_aberration:
        rows.append([
            InlineKeyboardButton("➖ Shift", callback_data="adj_chromatic_dec"),
            InlineKeyboardButton(f"🌈 {chromatic_shift}px", callback_data="adj_noop"),
            InlineKeyboardButton("➕ Shift", callback_data="adj_chromatic_inc"),
        ])
    rows.append([
        InlineKeyboardButton(
            "📺 VHS: ON" if vhs_effect else "📺 VHS: OFF",
            callback_data="adj_vhs_toggle",
        ),
    ])
    if vhs_effect:
        rows.append([
            InlineKeyboardButton("➖ Grain", callback_data="adj_vhs_dec"),
            InlineKeyboardButton(f"📺 {vhs_strength}%", callback_data="adj_noop"),
            InlineKeyboardButton("➕ Grain", callback_data="adj_vhs_inc"),
        ])
    rows.append([
        InlineKeyboardButton("➖ Fade 0.5s", callback_data="adj_intro_dec"),
        InlineKeyboardButton(f"⬛️ Fade in {intro_black_seconds:g}s", callback_data="adj_noop"),
        InlineKeyboardButton("➕ Fade 0.5s", callback_data="adj_intro_inc"),
    ])
    if intro_black_seconds > 0:
        rows.append([InlineKeyboardButton("♻️ Reset Fade", callback_data="adj_intro_reset")])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="adj_effects_back")])
    return InlineKeyboardMarkup(rows)


def logo_keyboard(logo_kind: str | None = None, logo_scale: int = LOGO_SCALE_DEFAULT, logo_offset_bottom: int = LOGO_OFFSET_DEFAULT) -> InlineKeyboardMarkup:
    """"🏷 Logo Settings" sub-menu eka - logo ekak set wela nam resize/reposition/
    change/remove buttons tika, naththam thani "Add logo" button ekak witharai."""
    rows = []
    if logo_kind:
        rows.append([
            InlineKeyboardButton("➖ Logo size", callback_data="adj_logo_dec"),
            InlineKeyboardButton(f"🏷 {logo_scale}%", callback_data="adj_noop"),
            InlineKeyboardButton("➕ Logo size", callback_data="adj_logo_inc"),
        ])
        rows.append([
            InlineKeyboardButton("⬆️ Logo up", callback_data="adj_logo_up"),
            InlineKeyboardButton(f"↕️ {logo_offset_bottom}px", callback_data="adj_noop"),
            InlineKeyboardButton("⬇️ Logo down", callback_data="adj_logo_down"),
        ])
        rows.append([
            InlineKeyboardButton("🔁 Change logo", callback_data="adj_logo_change"),
            InlineKeyboardButton("🗑 Remove logo", callback_data="adj_logo_remove"),
        ])
    else:
        rows.append([InlineKeyboardButton("🏷 Add logo", callback_data="adj_logo_change")])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="adj_logo_back")])
    return InlineKeyboardMarkup(rows)


def header_keyboard(header_bold: bool, header_gap_top: int = HEADER_GAP_TOP_DEFAULT, header_gap_bottom: int = HEADER_GAP_BOTTOM_DEFAULT) -> InlineKeyboardMarkup:
    """"Header" button eken enna sub-menu eka - methanin manage wenne header
    ekata witharai (size/color/bold/top-space/bottom-space), normal text ekata
    kisima effect ekak nehe."""
    color_buttons = [
        InlineKeyboardButton(label.split(" ", 1)[0], callback_data=f"adj_hdrcolor_{key}")
        for key, label in COLOR_LABELS.items()
    ]
    rows = [
        [
            InlineKeyboardButton("🔠 Header Text +", callback_data="adj_header_font_inc"),
            InlineKeyboardButton("🔡 Header Text -", callback_data="adj_header_font_dec"),
        ],
        [
            InlineKeyboardButton(
                "🅱️ Header Bold: ON" if header_bold else "🅱️ Header Bold: OFF",
                callback_data="adj_header_bold_toggle",
            ),
        ],
        color_buttons,
        [
            InlineKeyboardButton("⬆️ Top space -", callback_data="adj_header_gap_top_dec"),
            InlineKeyboardButton("⬆️ Top space +", callback_data="adj_header_gap_top_inc"),
        ],
        [
            InlineKeyboardButton("⬇️ Bottom space -", callback_data="adj_header_gap_bottom_dec"),
            InlineKeyboardButton("⬇️ Bottom space +", callback_data="adj_header_gap_bottom_inc"),
        ],
        [InlineKeyboardButton("🔙 Back", callback_data="adj_header_back")],
    ]
    return InlineKeyboardMarkup(rows)


def highlight_keyboard(highlight_font_scale: float = HIGHLIGHT_FONT_SCALE_DEFAULT, highlight_bold: bool = HIGHLIGHT_BOLD_DEFAULT, highlight_italic: bool = HIGHLIGHT_ITALIC_DEFAULT) -> InlineKeyboardMarkup:
    """"🔆 Highlight" button eken enna sub-menu eka - text eke ^...^ dala
    mark kala kotasata witharak apply wenawa (loku/podi karana size,
    bold/italic toggle), normal body text ekata effect ekak nehe."""
    rows = [
        [
            InlineKeyboardButton("🔎 Loku -", callback_data="adj_highlight_size_dec"),
            InlineKeyboardButton(f"🔆 {highlight_font_scale:.1f}x", callback_data="adj_noop"),
            InlineKeyboardButton("🔍 Loku +", callback_data="adj_highlight_size_inc"),
        ],
        [
            InlineKeyboardButton(
                "🅱️ Highlight Bold: ON" if highlight_bold else "🅱️ Highlight Bold: OFF",
                callback_data="adj_highlight_bold_toggle",
            ),
            InlineKeyboardButton(
                "🇮 Highlight Italic: ON" if highlight_italic else "🇮 Highlight Italic: OFF",
                callback_data="adj_highlight_italic_toggle",
            ),
        ],
        [InlineKeyboardButton("🔙 Back", callback_data="adj_highlight_back")],
    ]
    return InlineKeyboardMarkup(rows)


# ---------------- SHARED PREVIEW RENDERER ----------------

async def render_preview(query, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Preview photo eka generate karala, dan message ekak thiyenawa nam edit karanawa,
    naththam aluthen evanawa. Success unoth True, error welath False return karanawa.

    Debounce eka methanma (centralized) manage karanawa - kalin widiyata hama
    caller ekakma (color pick / logo change / template use / adjust buttons)
    "generating" flag eka thaniyama set/reset karanna one wela thibba, eeka
    consistent karanna amathaka unoth (e.g. color_callback, logo_choice_callback,
    template use flow) render_preview() 2k ekpaharatama (Playwright screenshot 2k)
    run wenna puluwan una - low RAM server ekakata danger ekak. Dan methanata
    call karana hama tenakama (12+ call sites) methanin automatically protect
    wenawa, wenama flag management ekak nathuwa."""
    data = context.user_data

    if data.get("generating"):
        # dan render ekak process wemin - meka duplicate/overlapping call ekak
        # (double-click ekak, ho dekma-welavata text/photo 2k ewapu ekak) nisa
        # meka skip karala, kalin thibba state/preview ekama widiyata thiyenawa
        # (eka error ekak newei nisa False newei True return karanne)
        if hasattr(query, "answer"):
            try:
                await query.answer("⏳ Please wait, still generating the previous one...", show_alert=False)
            except Exception:
                pass
        else:
            try:
                await query.message.reply_text("⏳ Please wait, still generating the previous one...")
            except Exception:
                pass
        return True

    data["generating"] = True
    try:
        return await _render_preview_impl(query, context)
    finally:
        data["generating"] = False


async def _render_preview_impl(query, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """render_preview() eke ඇත්ත logic eka - debounce lock eka gaathi wela
    thiyenakota witharak methanata ennawa."""
    data = context.user_data
    browser = context.application.bot_data["browser"]

    bg_image_b64 = data.get("bg_image_b64")
    canvas_width = data.get("bg_width") or IMG_SIZE
    canvas_height = data.get("bg_height") or IMG_SIZE

    # user "" walin dapu header ekak thiyenawa nam, e kotasa text eken vekkarala
    # wenama style ekakin (header_*) render karanawa - nathnam kalinma widiyatama
    # raw text eka ekamawa body vidihata pennanawa
    header_text, body_text = split_header_text(data["text"])
    has_header = header_text is not None
    # header ekak nathi giya nisa, header sub-menu ekaka "stuck" wela hitiyoth
    # (e.g. user text eka edit kara header eka ain kara) main menu ekatama fallback
    if not has_header and data.get("adjust_menu") == "header":
        data["adjust_menu"] = "main"

    # text eke ^...^ balanced pair ekak thiyenawada check karanawa - "Highlight"
    # button/submenu eka pennanne meka thibba welavata witharai (header eka wagema)
    has_highlight = data["text"].count("^") >= 2 and data["text"].count("^") % 2 == 0
    if not has_highlight and data.get("adjust_menu") == "highlight":
        data["adjust_menu"] = "main"

    # background photo eka ain una nam, "Background Effects" sub-menu eka
    # eken "stuck" wela hitiyoth main menu ekatama fallback wenawa (header/
    # highlight walata wagema)
    if not bg_image_b64 and data.get("adjust_menu") == "effects":
        data["adjust_menu"] = "main"

    try:
        image_buf = await generate_image(
            browser,
            body_text,
            data["emojis"],
            data["font_size"],
            data["emoji_size"],
            data["color"],
            transparent=False,   # preview eka pennanne grey background ekakin (black text ekath penenna) - background photo ekak nam eka methanin loadwenawa
            font_weight=data.get("font_weight", FONT_WEIGHT_DEFAULT),
            italic=data.get("italic", ITALIC_DEFAULT),
            align=data.get("align", ALIGN_DEFAULT),
            bg_color=PREVIEW_BG,
            canvas_width=canvas_width,
            canvas_height=canvas_height,
            bg_image_b64=bg_image_b64,
            overlay_opacity=data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT),
            text_offset_y=data.get("text_offset_y", TEXT_OFFSET_DEFAULT),
            blur_px=data.get("bg_blur", BLUR_DEFAULT),
            blur_type=data.get("blur_type", BLUR_TYPE_DEFAULT),
            logo_kind=data.get("logo_kind"),
            logo_value=data.get("logo_value"),
            logo_scale=data.get("logo_scale", LOGO_SCALE_DEFAULT),
            logo_offset_bottom=data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT),
            header_text=header_text,
            header_font_size=data.get("header_font_size", HEADER_FONT_SIZE_DEFAULT),
            header_color=data.get("header_color", HEADER_COLOR_DEFAULT),
            header_bold=data.get("header_bold", HEADER_BOLD_DEFAULT),
            header_gap_top=data.get("header_gap_top", HEADER_GAP_TOP_DEFAULT),
            header_gap_bottom=data.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT),
            highlight_font_scale=data.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT),
            highlight_bold=data.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT),
            highlight_italic=data.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT),
            stroke_width=data.get("stroke_width", STROKE_WIDTH_DEFAULT),
            stroke_color=data.get("stroke_color", STROKE_COLOR_DEFAULT),
        )
    except Exception as e:
        logger.exception("Image generation failed")
        await query.message.reply_text(f"⚠️ Something went wrong while generating the image: {e}")
        return False

    preview_msg_id = data.get("preview_msg_id")
    if data.get("adjust_menu") == "header":
        keyboard = header_keyboard(
            data.get("header_bold", HEADER_BOLD_DEFAULT),
            header_gap_top=data.get("header_gap_top", HEADER_GAP_TOP_DEFAULT),
            header_gap_bottom=data.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT),
        )
    elif data.get("adjust_menu") == "highlight":
        keyboard = highlight_keyboard(
            highlight_font_scale=data.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT),
            highlight_bold=data.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT),
            highlight_italic=data.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT),
        )
    elif data.get("adjust_menu") == "text":
        keyboard = text_keyboard(
            data.get("font_size", FONT_SIZE_DEFAULT),
            data.get("font_weight", FONT_WEIGHT_DEFAULT),
            italic=data.get("italic", ITALIC_DEFAULT),
            align=data.get("align", ALIGN_DEFAULT),
            has_bg_image=bool(bg_image_b64),
            text_offset_y=data.get("text_offset_y", TEXT_OFFSET_DEFAULT),
            stroke_width=data.get("stroke_width", STROKE_WIDTH_DEFAULT),
            stroke_color=data.get("stroke_color", STROKE_COLOR_DEFAULT),
        )
    elif data.get("adjust_menu") == "emoji":
        keyboard = emoji_keyboard(emoji_size=data.get("emoji_size", EMOJI_SIZE_DEFAULT))
    elif data.get("adjust_menu") == "effects":
        keyboard = effects_keyboard(
            overlay_opacity=data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT),
            blur_px=data.get("bg_blur", BLUR_DEFAULT),
            blur_type=data.get("blur_type", BLUR_TYPE_DEFAULT),
            chromatic_aberration=data.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT),
            chromatic_shift=data.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT),
            vhs_effect=data.get("vhs_effect", VHS_EFFECT_DEFAULT),
            vhs_strength=data.get("vhs_strength", VHS_STRENGTH_DEFAULT),
            intro_black_seconds=data.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT),
        )
    elif data.get("adjust_menu") == "logo":
        keyboard = logo_keyboard(
            logo_kind=data.get("logo_kind"),
            logo_scale=data.get("logo_scale", LOGO_SCALE_DEFAULT),
            logo_offset_bottom=data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT),
        )
    else:
        keyboard = size_keyboard(
            has_bg_image=bool(bg_image_b64),
            logo_kind=data.get("logo_kind"),
            active_template=data.get("active_template_name"),
            has_header=has_header,
            has_highlight=has_highlight,
            has_bg_video=data.get("bg_kind") == "video" and bool(data.get("bg_video_path")),
            watermark_enabled=bool(data.get("watermark_enabled") and data.get("watermark_image_b64")),
            is_reedit=bool(data.get("is_reedit")),
            bg_kind=data.get("bg_kind"),
        )
    if preview_msg_id:
        try:
            await send_with_retry(
                context.bot.edit_message_media,
                chat_id=query.message.chat_id,
                message_id=preview_msg_id,
                media=InputMediaPhoto(media=image_buf),
                reply_markup=keyboard,
                what="preview edit_message_media",
            )
        except BadRequest as e:
            # user +/- button ekak (e.g. size max/min ekedi ithuru click kaloth)
            # click kaloth, data eke wenasak wenne nathi welavata - image eka +
            # keyboard eka dekama kalin thibba widiyatama exact widiyata ithuru
            # wenawa, Telegram eka ee request eka "not modified" kiyala reject
            # karanawa. Meka harmless (preview eka dan pennana eka hariyatama
            # thiyenne one widiyatama) nisa, silently ignore karanawa - naththam
            # ee error eka bubble unoth handler eka crash wela user ta kisima
            # response ekak enne na (log eke pennuna widiyata).
            if "not modified" not in str(e).lower():
                raise
    else:
        sent = await send_with_retry(
            query.message.reply_photo,
            photo=image_buf,
            reply_markup=keyboard,
            what="preview reply_photo",
        )
        data["preview_msg_id"] = sent.message_id

    return True


async def _notify_generating(context: ContextTypes.DEFAULT_TYPE, chat_id: int, text: str = "⏳ Generating your preview...") -> int | None:
    """render_preview() eka call karanna kalin (screenshot eka generate wenna
    tikak welavak yanna puluwan - Playwright render ekak nisa) user ta
    "loading" pennana temporary message ekak evanawa, render eka iwara welata
    methema delete karanawa. Button click ekak nam Telegram eken auto
    spinner ekak penei, eth text/photo message ekak evala trigger wena
    render ekakata ehema built-in indicator ekak nehe - ithin methanin
    dala danawa (screenshot eka late unoth user confuse wenna denne nathuwa).
    Late-arriving preview ekak thiyena wena hama thanakama (emoji/edit-text/
    logo/color step) methema use karanna."""
    try:
        sent = await context.bot.send_message(chat_id=chat_id, text=text)
        return sent.message_id
    except Exception:
        return None


async def _clear_generating_notice(context: ContextTypes.DEFAULT_TYPE, chat_id: int, msg_id: int | None):
    if not msg_id:
        return
    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=msg_id)
    except Exception:
        pass


# ---------------- HANDLERS ----------------

def _cleanup_bg_video(data: dict):
    """Background video ekata download unu (raw) temp file eka disk eken ain
    karanawa - `bg_video_path` set unu hama welawakama (cancel, aluth post ekak
    patan gaddi, "Done" click karpu passe) call karanna one, ehema nathnam VPS eke
    disk eka temp video files walin purawenawa. Audio track eka (add kara nam)
    weradi temp dir ekaka thiyena nisa eyath methanin ain karanawa."""
    path = data.get("bg_video_path")
    if path:
        try:
            shutil.rmtree(Path(path).parent, ignore_errors=True)
        except Exception:
            pass
        data["bg_video_path"] = None
        data["bg_video_is_photo"] = False

    audio_path = data.get("bg_audio_path")
    if audio_path:
        try:
            shutil.rmtree(Path(audio_path).parent, ignore_errors=True)
        except Exception:
            pass
        data["bg_audio_path"] = None


async def _ask_emoji(chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    """Emoji ekak prompt karana step eka - plain background eken ekath, photo
    upload karapu passeth, video background flow eken (audio settings dila
    passeth) - okkoma path ekenma methanata ekama vidiyata enawa."""
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text="Nice! 🎉\n\nNow send the emoji you'd like to add to this post - "
        "one or more, e.g. 🔥❤️👍",
    )
    context.user_data["emoji_prompt_msg_id"] = sent.message_id
    return WAITING_EMOJI


async def _ask_video_audio(chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    """Background video ekak set unu passe (link ekakin hari, upload ekakin hari)
    methanata enawa - Pinterest video godayakma audio eka broken/mute nisa, e
    original audio eka thiyaganna one da nathnam mute karala aluth audio ekak
    (local file ekak/TikTok link ekakin extract kara ekak) danna one da kiyala ahanawa."""
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text="🔊 What should I do with this video's original audio?",
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🔈 Keep original audio", callback_data="audio_keep"),
            InlineKeyboardButton("🔇 Mute it", callback_data="audio_mute"),
        ]]),
    )
    context.user_data["bg_audio_prompt_msg_id"] = sent.message_id
    return ASK_BG_VIDEO_AUDIO


async def _ask_new_audio_source(chat_id: int, context: ContextTypes.DEFAULT_TYPE, allow_skip: bool = False) -> int:
    """"Aluth audio ekak danna" prompt eka (local upload / TikTok link) -
    initial "mute -> aluth audio ekak" flow ekenuth, "Replace Video"/"Replace
    Audio" (Re-edit passe) flow ekenuth, "🎬 Photo eka Video ekak karanna"
    flow ekenuth okkoma methanatama enawa.

    allow_skip: "Photo eka Video ekak karanna" flow ekata witharak True -
    music ekak nathuwama (silent) video ekak hadaganna one nam, "skip" button
    ekak ithuru karanawa (video ekata pre-existing length ekak nathi nisa,
    e welavata length eka preset buttons walin wenama ahanawa)."""
    rows = [[
        InlineKeyboardButton("📱 Local audio upload", callback_data="audiosrc_upload"),
        InlineKeyboardButton("🎵 Paste TikTok link", callback_data="audiosrc_tiktok"),
    ]]
    if allow_skip:
        rows.append([InlineKeyboardButton("⏭ No music, skip", callback_data="audiosrc_skip")])
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text="🎵 Send me the new audio - upload a local audio file, or paste a "
        "TikTok video link and I'll pull the audio out of it.",
        reply_markup=InlineKeyboardMarkup(rows),
    )
    context.user_data["bg_audio_source_prompt_msg_id"] = sent.message_id
    return ASK_BG_AUDIO_SOURCE


async def bg_audio_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    chat_id = query.message.chat_id

    try:
        await query.message.delete()
    except Exception:
        pass

    if query.data == "audio_keep":
        context.user_data["bg_audio_mode"] = "keep"
        return await _ask_emoji(chat_id, context)

    # audio_mute - mute karala, aluth audio ekak danna one da kiyala ahanawa
    context.user_data["bg_audio_mode"] = "mute"
    return await _ask_new_audio_source(chat_id, context)


async def bg_audio_source_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    chat_id = query.message.chat_id

    try:
        await query.message.delete()
    except Exception:
        pass

    if query.data == "audiosrc_skip":
        # "🎬 Photo eka Video ekak karanna" flow ekata witharak penena button
        # eka - music ekak nathuwama (silent) video ekak hadaganna one nam,
        # e welavata length eka preset buttons walin wenama ahanawa
        return await _ask_photo_video_duration(chat_id, context)

    if query.data == "audiosrc_upload":
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text="📱 Send me the audio file (mp3, m4a, voice note, etc).",
        )
        context.user_data["bg_audio_prompt_msg_id"] = sent.message_id
        return WAITING_BG_AUDIO_UPLOAD

    # audiosrc_tiktok
    sent = await context.bot.send_message(chat_id=chat_id, text="📎 Send me the TikTok link.")
    context.user_data["bg_audio_prompt_msg_id"] = sent.message_id
    return WAITING_BG_AUDIO_TIKTOK_LINK


async def _finish_replace_flow(chat_id: int, query_like, context: ContextTypes.DEFAULT_TYPE) -> int:
    """"Replace Video"/"Replace Audio" (Re-edit passe) flow eka iwara unu
    passe methanatama enawa - "replace_flow" flag eka clear karala, preview
    eka aye render karala ADJUSTING (main menu ekatama) ayeth yanawa. `query_like`
    ekata one wenne `.message.chat_id` / `.message.reply_photo` witharai
    (real CallbackQuery ekak unath, _FakeQuery ekak unath dekamatama methanin
    reuse karanna puluwan)."""
    context.user_data.pop("replace_flow", None)
    notice_id = await _notify_generating(context, chat_id)
    ok = await render_preview(query_like, context)
    await _clear_generating_notice(context, chat_id, notice_id)
    return ADJUSTING if ok else ConversationHandler.END


async def _ask_photo_video_duration(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> int:
    """"🎬 Photo eka Video ekak karanna" flow eka - music skip kaloth witharak
    methanata enawa (music dammoth video length eka e music eke length ekatama
    set wenawa, ithin methanin ahanna one na - _finalize_bg_audio() balanna)."""
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text="⏱ Video eka kopamana welavak (seconds) thiyanna one?",
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton(f"{s}s", callback_data=f"pvdur_{s}")
            for s in PHOTO_VIDEO_DURATION_PRESETS
        ]]),
    )
    context.user_data["photo_video_duration_prompt_msg_id"] = sent.message_id
    return ASK_PHOTO_VIDEO_DURATION


async def _finish_photo_video_flow(chat_id: int, query_like, context: ContextTypes.DEFAULT_TYPE) -> int:
    """"🎬 Photo eka Video ekak karanna" flow eka (music/duration decide unu
    passe) iwara karanawa - dan tibba background photo eka (bg_image_b64)
    temp PNG file ekakata dala `bg_video_path` ekata set karanawa, `bg_kind`
    eka "video" bawata maru karanawa (methanin passe "🌀 Scrolling Watermark" /
    "🎛 Background Effects" / (Re-edit ekaka) "Replace Video/Audio" buttons
    dan auto-widiyata penena eka - e okkoma `bg_kind == "video"` check
    karanne), preview eka aye render karala ADJUSTING ekatama yanawa.

    `bg_video_is_photo` flag eka witharai aluthin ithuru wenne - `adj_done`
    handler eke `compose_video_background()` call karana welawe methanin
    "background_is_static_image=True" danna one kiyala danaganna."""
    data = context.user_data
    data.pop("photo_video_flow", None)

    prompt_msg_id = data.pop("photo_video_duration_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    bg_image_b64 = data.get("bg_image_b64")
    tmp_dir = tempfile.mkdtemp(prefix="phvid_")
    photo_path = str(Path(tmp_dir) / "photo.png")
    Path(photo_path).write_bytes(base64.b64decode(bg_image_b64))

    # methana "convert to video" ekata kalin bg_video_path ekaka enam
    # nathuwa one na (normally thiyenne na, defensive widiyata witharai)
    old_video_path = data.get("bg_video_path")
    if old_video_path and old_video_path != photo_path:
        try:
            shutil.rmtree(Path(old_video_path).parent, ignore_errors=True)
        except Exception:
            pass

    data["bg_video_path"] = photo_path
    data["bg_video_is_photo"] = True
    data["bg_kind"] = "video"

    notice_id = await _notify_generating(context, chat_id)
    ok = await render_preview(query_like, context)
    await _clear_generating_notice(context, chat_id, notice_id)
    return ADJUSTING if ok else ConversationHandler.END


async def photo_video_duration_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """"🎬 Photo eka Video ekak karanna" flow eka - music skip karapu passe,
    video length eka preset buttons walin (pvdur_5/10/15/30) methanin thoragannawa."""
    query = update.callback_query
    await query.answer()
    chat_id = query.message.chat_id
    try:
        await query.message.delete()
    except Exception:
        pass

    try:
        seconds = float(query.data.split("_", 1)[1])
    except (IndexError, ValueError):
        seconds = PHOTO_VIDEO_DURATION_PRESETS[0]

    data = context.user_data
    data["bg_video_duration"] = seconds
    data["bg_audio_mode"] = "mute"
    data["bg_audio_path"] = None
    data["bg_audio_fit"] = "trim_audio"
    return await _finish_photo_video_flow(chat_id, query, context)


async def _finalize_bg_audio(chat_id: int, context: ContextTypes.DEFAULT_TYPE, audio_path: str, message=None) -> int:
    """Aluth audio file eka (upload/tiktok-extract dekedinma) probe karala,
    video duration ekata wada podi nam "how to fit" ahanawa, ehema natthang
    dirakma emoji step ekata (nathnam "Replace Audio" flow ekaka nam ADJUSTING
    ekatama) yanawa. Return karanne next conversation state eka."""
    try:
        audio_duration = await probe_audio_duration(audio_path)
    except Exception as e:
        logger.exception("Audio probe failed")
        shutil.rmtree(Path(audio_path).parent, ignore_errors=True)
        await context.bot.send_message(
            chat_id=chat_id,
            text=f"⚠️ Couldn't read that audio file: {e}\n\nSend it again, or /cancel to stop.",
        )
        return WAITING_BG_AUDIO_UPLOAD

    # "Replace Audio" flow ekaka nam, kalin tibba audio track eka (thiyenawa
    # nam) disk eken methanin ain karanawa - passe overwrite wenna kalin
    old_audio_path = context.user_data.get("bg_audio_path")
    if old_audio_path and old_audio_path != audio_path:
        try:
            shutil.rmtree(Path(old_audio_path).parent, ignore_errors=True)
        except Exception:
            pass

    context.user_data["bg_audio_path"] = audio_path
    context.user_data["bg_audio_duration"] = audio_duration
    context.user_data["bg_audio_mode"] = "replace"

    if context.user_data.get("photo_video_flow"):
        # "🎬 Photo eka Video ekak karanna" flow ekaka nam, "Replace Audio"/
        # normal video-bg flow eke wagema pre-existing video duration ekak
        # naha - ithin "video eka audio ekata wada podida loku da" kiyala
        # ahanna one na, video length ekama methanin music eke length
        # ekatama (cap ekakata trim karala) directly set karanawa
        context.user_data["bg_video_duration"] = min(audio_duration, BG_VIDEO_MAX_SECONDS)
        context.user_data["bg_audio_fit"] = "trim_audio"
        return await _finish_photo_video_flow(chat_id, _FakeQuery(message), context)

    video_duration = context.user_data.get("bg_video_duration") or BG_VIDEO_MAX_SECONDS

    if audio_duration + 0.25 >= video_duration:
        # audio eka video ekata wada digu/ekasama - trim karagannawa video
        # duration ekatama, ehema unoth wenama ahanna one na
        context.user_data["bg_audio_fit"] = "trim_audio"
        if context.user_data.get("replace_flow"):
            return await _finish_replace_flow(chat_id, _FakeQuery(message), context)
        return await _ask_emoji(chat_id, context)

    # audio eka video ekata wada podi (e.g. video 30s ekakata audio 15sk) -
    # reject karanne nathuwa, user gen ahanawa fit karanne kohomada kiyala
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text=(
            f"🎵 Your audio is {audio_duration:.0f}s but the video is "
            f"{video_duration:.0f}s. How should I fit them together?"
        ),
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("✂️ Trim video to audio length", callback_data="audiofit_trim_video"),
            InlineKeyboardButton("🔁 Loop audio to fill video", callback_data="audiofit_loop_audio"),
        ]]),
    )
    context.user_data["bg_audio_fit_prompt_msg_id"] = sent.message_id
    return ASK_AUDIO_FIT


async def receive_bg_audio_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id

    tg_audio = (
        update.message.audio
        or update.message.voice
        or (
            update.message.document
            if update.message.document and (update.message.document.mime_type or "").startswith("audio/")
            else None
        )
    )
    if tg_audio is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like an audio file. Send an audio file, or /cancel to stop."
        )
        return WAITING_BG_AUDIO_UPLOAD

    status_msg = await update.message.reply_text("⏳ Downloading your audio...")

    tmp_dir = tempfile.mkdtemp(prefix="audup_")
    ext = Path(getattr(tg_audio, "file_name", None) or "audio.mp3").suffix or ".mp3"
    audio_path = str(Path(tmp_dir) / f"audio{ext}")

    try:
        tg_file = await context.bot.get_file(tg_audio.file_id)
        await tg_file.download_to_drive(audio_path)
    except Exception as e:
        logger.exception("Background audio upload download failed")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't download that audio: {e}\n\n"
            "(Bots can only download files up to 20MB from Telegram.)\n\n"
            "Send it again, or /cancel to stop."
        )
        return WAITING_BG_AUDIO_UPLOAD

    audio_prompt_msg_id = context.user_data.pop("bg_audio_prompt_msg_id", None)
    if audio_prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=audio_prompt_msg_id)
        except Exception:
            pass

    try:
        await status_msg.delete()
    except Exception:
        pass

    return await _finalize_bg_audio(chat_id, context, audio_path, message=update.message)


async def receive_bg_audio_tiktok_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    url = update.message.text.strip()
    chat_id = update.message.chat_id

    status_msg = await update.message.reply_text("⏳ Pulling the audio out of that TikTok link...")

    try:
        audio_path = await extract_audio_from_url_with_retry(url)
    except Exception as e:
        logger.exception("TikTok audio extraction failed after retries")
        await status_msg.edit_text(
            f"⚠️ Couldn't get audio from that link: {e}\n\n"
            "Send the TikTok link again, or /cancel to stop."
        )
        return WAITING_BG_AUDIO_TIKTOK_LINK

    audio_prompt_msg_id = context.user_data.pop("bg_audio_prompt_msg_id", None)
    if audio_prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=audio_prompt_msg_id)
        except Exception:
            pass

    try:
        await status_msg.delete()
    except Exception:
        pass

    return await _finalize_bg_audio(chat_id, context, audio_path, message=update.message)


async def bg_audio_fit_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    chat_id = query.message.chat_id

    try:
        await query.message.delete()
    except Exception:
        pass

    if query.data == "audiofit_trim_video":
        # audio eka witharak dirakma - video eka eyata gasagannawa (render duration
        # eka podi karala)
        context.user_data["bg_video_duration"] = context.user_data.get("bg_audio_duration")
        context.user_data["bg_audio_fit"] = "trim_audio"
    else:
        # audiofit_loop_audio - audio eka loop karala video full length ekatama pirenawa
        context.user_data["bg_audio_fit"] = "loop"

    if context.user_data.get("replace_flow"):
        # "Replace Video"/"Replace Audio" flow ekaka nam, emoji step ekata
        # yanne nathuwa direct ADJUSTING (main menu) ekatama return karanawa
        return await _finish_replace_flow(chat_id, query, context)

    return await _ask_emoji(chat_id, context)


async def receive_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """User kelinma text ekak evapuwoth (command ekak newei) methanin patan gannawa.

    Private chat ekaka - okkoma bare text ekatama methanin patan gannawa.
    Group/supergroup ekaka - normal chat eka interrupt wenna denne nathuwa,
    bot ekatama directly address karapu message ekakata witharak methanin
    patan gannawa (bot ekage message ekakata "reply" kaloth, hari
    "@botusername" widiyata mention kaloth - _GroupBotTriggerFilter eka
    balanna). "/newpost <text>" (_newpost_command) eken group ekakath
    directly patan ganna puluwan - dekamama logic ekama (_start_new_post)
    share karanawa."""
    raw_text = apply_native_formatting_as_markup(
        update.message.text or "", update.message.entities or ()
    )
    if update.effective_chat and update.effective_chat.type != "private":
        # group ekaka nam, trigger karanna use kala "@botusername" mention eka
        # post eke text ekedi penenna one na - eka methanin ain karanawa
        bot_username = _BOT_INFO.get("username")
        if bot_username:
            raw_text = re.sub(
                rf"(?i)@{re.escape(bot_username)}\b", "", raw_text
            ).strip()
        if not raw_text:
            await update.message.reply_text(
                "✏️ Post එකට ඕන text එක මාව reply/mention කරද්දිම එක්ක දාන්න, "
                "නැත්නම් `/newpost ඔයාගේ text එක මෙතන` විදිහට එවන්න.",
                parse_mode="Markdown",
            )
            return ConversationHandler.END
    return await _start_new_post(update, context, raw_text)


async def _newpost_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Group chats walata "/newpost <text>" - group ekaka type wena okkoma
    text ekatama bot eka react wela normal chat eka interrupt wenna denne
    nathuwa, explicit command ekak witharak trigger karanawa. (Meka thawat
    hondai - Telegram bot privacy mode eka ON unath (default eka), commands
    okkoma bot ekata pennei, eth plain text pennenne nehe - ithin bare-text
    trigger ekak group ekaka reliable widiyata wada karanne na wagේම, "/newpost"
    ekak use karoth me issue ekath ain wenawa.) Private chat ekaka methema
    one na - plain text ekama dan patan gannawa."""
    full_text = apply_native_formatting_as_markup(
        update.message.text or "", update.message.entities or ()
    )
    raw_text = full_text.partition(" ")[2].strip()
    if not raw_text:
        await update.message.reply_text(
            "✏️ Post එකට ඕන text එක මෙහෙම දාන්න:\n`/newpost ඔයාගේ text එක මෙතන`",
            parse_mode="Markdown",
        )
        return ConversationHandler.END
    return await _start_new_post(update, context, raw_text)


async def _start_new_post(update: Update, context: ContextTypes.DEFAULT_TYPE, raw_text: str):
    """receive_text (private, bare text) saha _newpost_command (group, "/newpost")
    dekamama share karana core logic eka."""
    # ##/// markup eka close karanna amathaka una wage waradi typing ekak
    # thiyenawa nam, post ekak generate karanna kalinma user ta danawa - ehema
    # nathnam ## / // characters ekama post eke literal widiyata output wela,
    # user ta wenna one bold/italic effect eka nathuwa yanawa.
    markup_issues = find_markup_issues(raw_text)
    if markup_issues:
        await update.message.reply_text(
            "⚠️ Text එකේ ##/// sign වැරදිලා තියෙනවා වගේ පේනවා (close කරලා නෑ):\n"
            + "\n".join(markup_issues)
            + "\n\nඑවා හරි කරලා ආයෙත් text එක type කරලා send කරන්න."
        )
        return

    last_settings = context.user_data.get("last_settings", {})
    templates = context.user_data.get("templates", {})
    fb_pages = context.user_data.get("fb_pages", {})
    scheduled_posts = context.user_data.get("scheduled_posts")
    context.user_data.clear()
    context.user_data["last_settings"] = last_settings   # save unu setting tika restore karanawa
    context.user_data["templates"] = templates           # save karapu templates tika restore karanawa
    if fb_pages:
        context.user_data["fb_pages"] = fb_pages          # "/pages" eken save karapu Facebook Pages tika restore karanawa
    if scheduled_posts:
        context.user_data["scheduled_posts"] = scheduled_posts   # schedule/draft වෙලා තියෙන posts tika restore karanawa

    context.user_data["text"] = raw_text
    context.user_data["font_size"] = last_settings.get("font_size", FONT_SIZE_DEFAULT)
    context.user_data["emoji_size"] = last_settings.get("emoji_size", EMOJI_SIZE_DEFAULT)
    context.user_data["color"] = last_settings.get("color", COLORS["white"])
    context.user_data["font_weight"] = last_settings.get("font_weight", FONT_WEIGHT_DEFAULT)
    context.user_data["italic"] = last_settings.get("italic", ITALIC_DEFAULT)
    context.user_data["align"] = last_settings.get("align", ALIGN_DEFAULT)

    # header ("" quote eken danapu titile eka) styling - post ekakata ekakma,
    # last_settings eken restore wenawa (thibba nam), header ekak thiyenawada
    # kiyala render_preview eke text eka parse karala witharai therenne
    context.user_data["adjust_menu"] = "main"
    context.user_data["is_reedit"] = False
    context.user_data["replace_flow"] = None
    context.user_data["header_font_size"] = last_settings.get("header_font_size", HEADER_FONT_SIZE_DEFAULT)
    context.user_data["header_color"] = last_settings.get("header_color", HEADER_COLOR_DEFAULT)
    context.user_data["header_bold"] = last_settings.get("header_bold", HEADER_BOLD_DEFAULT)
    context.user_data["header_gap_top"] = last_settings.get("header_gap_top", HEADER_GAP_TOP_DEFAULT)
    context.user_data["header_gap_bottom"] = last_settings.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT)
    context.user_data["highlight_font_scale"] = last_settings.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT)
    context.user_data["highlight_bold"] = last_settings.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT)
    context.user_data["highlight_italic"] = last_settings.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT)
    context.user_data["stroke_width"] = last_settings.get("stroke_width", STROKE_WIDTH_DEFAULT)
    context.user_data["stroke_color"] = last_settings.get("stroke_color", STROKE_COLOR_DEFAULT)

    # post ekakata specific ewa - hama post ekakatama aluthen ahanawa (last_settings
    # ekata save karanne nehe), photo/video ekak upload kalath ekak nathiwath post
    # ekak ekak ithurak witharai. Kalin post ekaka bg video temp file ekak ho
    # Facebook-pending file ekak ithuru unoth (edge case - e.g. "Facebook post
    # karanna da" ahapu welavata Yes/No click karanne nathuwa, aye aluth text
    # ekak type kara aluth post ekak patan gattoth), methanin disk eken clean karanawa
    _cleanup_bg_video(context.user_data)
    _cleanup_fb_pending(context.user_data)
    context.user_data["bg_kind"] = None
    context.user_data["bg_image_b64"] = None
    context.user_data["bg_width"] = None
    context.user_data["bg_height"] = None
    context.user_data["bg_video_path"] = None
    context.user_data["bg_video_is_photo"] = None
    context.user_data["bg_video_duration"] = None
    context.user_data["bg_audio_path"] = None
    context.user_data["bg_audio_mode"] = None
    context.user_data["bg_audio_fit"] = None
    context.user_data["overlay_opacity"] = last_settings.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT)
    context.user_data["text_offset_y"] = last_settings.get("text_offset_y", TEXT_OFFSET_DEFAULT)
    context.user_data["bg_blur"] = last_settings.get("bg_blur", BLUR_DEFAULT)
    context.user_data["blur_type"] = last_settings.get("blur_type", BLUR_TYPE_DEFAULT)
    context.user_data["chromatic_aberration"] = last_settings.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT)
    context.user_data["chromatic_shift"] = last_settings.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT)
    context.user_data["vhs_effect"] = last_settings.get("vhs_effect", VHS_EFFECT_DEFAULT)
    context.user_data["vhs_strength"] = last_settings.get("vhs_strength", VHS_STRENGTH_DEFAULT)
    context.user_data["intro_black_seconds"] = last_settings.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT)

    # logo/watermark eka - last time use kala eka nam methanin default vidihata
    # ithuru wenawa (user ta Adjust screen eken change/remove karanna puluwan)
    last_logo = last_settings.get("logo") or {}
    context.user_data["logo_kind"] = last_logo.get("kind")
    context.user_data["logo_value"] = last_logo.get("value")
    context.user_data["logo_scale"] = last_logo.get("scale", LOGO_SCALE_DEFAULT)
    context.user_data["logo_offset_bottom"] = last_logo.get("offset_bottom", LOGO_OFFSET_DEFAULT)

    # scrolling watermark eka - logo eka wagema last time use kala eka
    # default vidihata ithuru wenawa (video background ekak upload kaloth
    # witharai button eka penenne, eth settings tika methanin ready wela thiyenawa)
    last_watermark = last_settings.get("watermark") or {}
    context.user_data["watermark_enabled"] = bool(last_watermark.get("image_b64"))
    context.user_data["watermark_kind"] = last_watermark.get("kind")
    context.user_data["watermark_image_b64"] = last_watermark.get("image_b64")
    context.user_data["watermark_opacity"] = last_watermark.get("opacity", WATERMARK_OPACITY_DEFAULT)
    # e-kalinma save karapu "left_right"/"right_left" values (aluth code ekedi
    # ain karapu) hambunoth, default (up_down) ekatama sanitize karanawa
    _saved_dir = last_watermark.get("direction", WATERMARK_DIRECTION_DEFAULT)
    context.user_data["watermark_direction"] = _saved_dir if _saved_dir in WATERMARK_DIRECTIONS else WATERMARK_DIRECTION_DEFAULT
    context.user_data["watermark_speed"] = last_watermark.get("speed", WATERMARK_SPEED_DEFAULT)
    context.user_data["watermark_scale"] = last_watermark.get("scale", WATERMARK_SCALE_DEFAULT)
    context.user_data["watermark_side"] = last_watermark.get("side", WATERMARK_SIDE_DEFAULT)

    keyboard_rows = [
        [
            InlineKeyboardButton("🖼 Upload a photo", callback_data="bg_choice_photo"),
            InlineKeyboardButton("🎥 Use a video", callback_data="bg_choice_video"),
        ],
        [InlineKeyboardButton("⬛ Plain background", callback_data="bg_choice_plain")],
    ]
    if templates:
        keyboard_rows.append([InlineKeyboardButton("📁 Use Template", callback_data="bg_choice_template")])
    keyboard = InlineKeyboardMarkup(keyboard_rows)
    await update.message.reply_text(
        "Got it ✅\n\nDo you want to use your own photo, a TikTok/Pinterest video, "
        "or a plain background?",
        reply_markup=keyboard,
    )
    return ASK_BACKGROUND


async def bg_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()

    # e "photo/plain" prompt eka sampurnayenma chat eken ain karanawa
    try:
        await query.message.delete()
    except Exception:
        pass

    if query.data == "bg_choice_template":
        templates = context.user_data.get("templates", {})
        if not templates:
            # button eka penenne templates thibba nam witharai, ithin methanata
            # ena eka normally wenne na - eth defensive check ekak vidihata
            await context.bot.send_message(
                chat_id=query.message.chat_id,
                text="📁 Oyata thama saved templates naha. /cancel karala aye text eka "
                "type karala send karanna.",
            )
            return ConversationHandler.END

        rows = [
            [InlineKeyboardButton(f"📁 {name}", callback_data=f"tpl_use_{name}")]
            for name in templates
        ]
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="📁 *Monoma template ekakda use karanne?*",
            parse_mode="Markdown",
            reply_markup=InlineKeyboardMarkup(rows),
        )
        return CHOOSE_TEMPLATE

    if query.data == "bg_choice_photo":
        context.user_data["bg_kind"] = "photo"
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="📸 Send me the photo you want to use as the background.\n\n"
            "(Original size eka ekama - crop/resize karanne nehe.)",
        )
        context.user_data["bg_prompt_msg_id"] = sent.message_id
        return WAITING_BG_IMAGE

    if query.data == "bg_choice_video":
        context.user_data["bg_kind"] = "video"
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🎥 Which platform is the background video from?",
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("📌 Pinterest", callback_data="bgvid_pinterest"),
                    InlineKeyboardButton("🎵 TikTok", callback_data="bgvid_tiktok"),
                ],
                [
                    InlineKeyboardButton("📱 Upload from phone", callback_data="bgvid_upload"),
                ],
            ]),
        )
        context.user_data["bg_video_prompt_msg_id"] = sent.message_id
        return ASK_BG_VIDEO_PLATFORM

    # bg_choice_plain
    return await _ask_emoji(query.message.chat_id, context)


async def template_use_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """CHOOSE_TEMPLATE state - user save karapu template ekak select kaloth,
    e style settings tika load karala, background type ekak ahanawa (photo/video/plain) -
    template eke background eka save wenne nehe, style witharai."""
    query = update.callback_query
    await query.answer()

    try:
        await query.message.delete()
    except Exception:
        pass

    name = query.data[len("tpl_use_"):]
    snapshot = context.user_data.get("templates", {}).get(name)

    if not snapshot:
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=f"⚠️ '{name}' template eka thama naha (delete wela wenna puluwan).",
        )
        return ConversationHandler.END

    _apply_style_snapshot(context.user_data, snapshot)
    # dan use karapu template eke nama methanin track karanawa - passe Adjust
    # screen ekedi "Save as Template" click kaloth, aye nama ahanne nathuwa
    # methanma template ekata update karaganna methanin puluwan wenawa
    context.user_data["active_template_name"] = name
    # methanin passe (emoji ahapu passe) color eka aye ahanne nathuwa - template
    # eke color eka dan set wela, "Use Last Settings" button ekakuth kohewath
    # pennanne nathuwa methanin control karanawa
    context.user_data["from_template"] = True

    keyboard = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🖼 Upload a photo", callback_data="bg_choice_photo"),
            InlineKeyboardButton("🎥 Use a video", callback_data="bg_choice_video"),
        ],
    ])
    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text=f"✅ *'{name}'* template eka load kara!\n\nDan background eka mokakda?",
        parse_mode="Markdown",
        reply_markup=keyboard,
    )
    return ASK_BACKGROUND


async def receive_bg_image(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id

    photo = None
    if update.message.photo:
        photo = update.message.photo[-1]   # Telegram eken hama photo ekakatama size 5k denawa - eken hondama (highest res) eka
    elif update.message.document and (update.message.document.mime_type or "").startswith("image/"):
        photo = update.message.document   # "compressed nathuwa" (file vidiyata) evapu image ekak

    if photo is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like a photo. Please send an image, or /cancel to stop."
        )
        return WAITING_BG_IMAGE

    bg_prompt_msg_id = context.user_data.pop("bg_prompt_msg_id", None)
    if bg_prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=bg_prompt_msg_id)
        except Exception:
            pass

    status_msg = await update.message.reply_text("⏳ Processing your photo...")

    try:
        tg_file = await context.bot.get_file(photo.file_id)
        raw_bytes = bytes(await tg_file.download_as_bytearray())

        img = Image.open(BytesIO(raw_bytes))
        # phone camera photo godayak EXIF orientation ekakin (rotated) enawa -
        # eka apply karala hariyata "upright" karanawa, naththam background eka
        # side ekata/පෙරළිලා yanna puluwan
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGB")

        buf = BytesIO()
        img.save(buf, format="PNG")
        context.user_data["bg_image_b64"] = base64.b64encode(buf.getvalue()).decode("utf-8")
        # ORIGINAL size ekama methanin save wenawa - passe canvas eka hadanne
        # methanin ithuru unu dimensions walatama (crop/stretch karanne nehe)
        context.user_data["bg_width"], context.user_data["bg_height"] = img.size
    except Exception as e:
        logger.exception("Background photo processing failed")
        await status_msg.edit_text(
            f"⚠️ Couldn't process that photo: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_BG_IMAGE

    try:
        await status_msg.delete()
    except Exception:
        pass

    return await _ask_emoji(chat_id, context)


async def bg_video_platform_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    chat_id = query.message.chat_id

    try:
        await query.message.delete()
    except Exception:
        pass

    if query.data == "bgvid_upload":
        # link ekakin nemei, user gema phone ekedin video eka methanata direct
        # yawanawa - yt-dlp/download_video eka mehedi use wenne na, telegram
        # eken diretma file eka download karagannawa (receive_bg_video_upload)
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text="📱 Send me the video file directly (send it as a 'file/document', "
            "not a normal video message - Telegram re-compresses normal video "
            "messages and quality drops).\n\n"
            "⚠️ Bots can only download files up to 20MB from Telegram.",
        )
        context.user_data["bg_video_link_prompt_msg_id"] = sent.message_id
        return WAITING_BG_VIDEO_UPLOAD

    platform = query.data.replace("bgvid_", "")
    label = VIDEO_PLATFORM_LABELS.get(platform, "video")
    context.user_data["bg_video_platform"] = platform

    sent = await context.bot.send_message(chat_id=chat_id, text=f"📎 Send me the {label} link.")
    context.user_data["bg_video_link_prompt_msg_id"] = sent.message_id
    return WAITING_BG_VIDEO_LINK


async def receive_bg_video_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    url = update.message.text.strip()
    chat_id = update.message.chat_id
    platform = context.user_data.get("bg_video_platform", "video")
    label = VIDEO_PLATFORM_LABELS.get(platform, "video")

    status_msg = await update.message.reply_text(f"⏳ Downloading video from {label}...")

    try:
        video_path = await download_video_with_retry(url)
    except Exception as e:
        logger.exception("Background video download failed after retries")
        await status_msg.edit_text(
            f"⚠️ Couldn't download that video: {e}\n\n"
            f"Send the {label} link again, or /cancel to stop."
        )
        return WAITING_BG_VIDEO_LINK

    try:
        await status_msg.edit_text("⏳ Preparing your video background...")
    except Exception:
        pass

    try:
        width, height, duration, bitrate_kbps = await probe_video(video_path)
        frame_b64 = await extract_preview_frame_b64(video_path)
    except Exception as e:
        logger.exception("Background video processing failed")
        shutil.rmtree(Path(video_path).parent, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't process that video: {e}\n\n"
            f"Send the {label} link again, or /cancel to stop."
        )
        return WAITING_BG_VIDEO_LINK

    bg_video_link_prompt_msg_id = context.user_data.pop("bg_video_link_prompt_msg_id", None)
    if bg_video_link_prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=bg_video_link_prompt_msg_id)
        except Exception:
            pass

    # "Replace Video" flow eka (Re-edit passe) nam, kalin tibba video/audio
    # temp files (thiyenawa nam) disk eken methanin ain karanawa - passe
    # bg_video_path/bg_audio_path aluth values walin overwrite wenna kalin
    _cleanup_bg_video(context.user_data)

    # Final render ekedi meken vada digu witharak process karanne nehe (max
    # BG_VIDEO_MAX_SECONDS) - eth preview ekata full frame ekma OK
    context.user_data["bg_video_path"] = video_path
    context.user_data["bg_width"] = width
    context.user_data["bg_height"] = height
    context.user_data["bg_video_duration"] = min(duration, BG_VIDEO_MAX_SECONDS)
    context.user_data["bg_image_b64"] = frame_b64   # preview ekata witharai - final render eka ffmpeg eken

    low_res_warning = _low_res_warning(width, height, bitrate_kbps)
    if low_res_warning:
        await context.bot.send_message(chat_id=chat_id, text=low_res_warning, parse_mode="Markdown")

    try:
        await status_msg.delete()
    except Exception:
        pass

    if context.user_data.get("replace_flow") == "video":
        # video eka replace unu nisa kalin audio eka invalid - "keep/mute"
        # ahanne nathuwa direct aluth audio ekak ahanawa
        return await _ask_new_audio_source(chat_id, context)

    return await _ask_video_audio(chat_id, context)


async def receive_bg_video_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """receive_bg_video_link ekේ upload-version eka - link ekakin nemei, user
    gema phone ekedin video file eka (video message ekak vidihata hari,
    document/file ekak vidihata hari) direct evapuwoth methanin handle wenawa."""
    chat_id = update.message.chat_id

    tg_video = update.message.video or (
        update.message.document
        if update.message.document and (update.message.document.mime_type or "").startswith("video/")
        else None
    )
    if tg_video is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like a video file. Send a video, or /cancel to stop."
        )
        return WAITING_BG_VIDEO_UPLOAD

    status_msg = await update.message.reply_text("⏳ Downloading your video...")

    tmp_dir = tempfile.mkdtemp(prefix="vidup_")
    # original filename eke extension eka thiyenawa nam eka use karanawa, nathnam
    # .mp4 default ekak - ffprobe/ffmpeg walata extension eka wadagath na, methana
    # thiyenne consistency ekatai
    ext = Path(getattr(tg_video, "file_name", None) or "video.mp4").suffix or ".mp4"
    video_path = str(Path(tmp_dir) / f"upload{ext}")

    try:
        # 20MB ekata vada loku file ekak nam Telegram Bot API eken get_file eka
        # denne na (BadRequest "File is too big") - e error eka methanin
        # message ekakata pennenawa
        tg_file = await context.bot.get_file(tg_video.file_id)
        await tg_file.download_to_drive(video_path)
    except Exception as e:
        logger.exception("Background video upload download failed")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't download that video: {e}\n\n"
            "(Bots can only download files up to 20MB from Telegram.)\n\n"
            "Send it again, or /cancel to stop."
        )
        return WAITING_BG_VIDEO_UPLOAD

    try:
        await status_msg.edit_text("⏳ Preparing your video background...")
    except Exception:
        pass

    try:
        width, height, duration, bitrate_kbps = await probe_video(video_path)
        frame_b64 = await extract_preview_frame_b64(video_path)
    except Exception as e:
        logger.exception("Background video processing failed")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't process that video: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_BG_VIDEO_UPLOAD

    bg_video_link_prompt_msg_id = context.user_data.pop("bg_video_link_prompt_msg_id", None)
    if bg_video_link_prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=bg_video_link_prompt_msg_id)
        except Exception:
            pass

    # "Replace Video" flow eka (Re-edit passe) nam, kalin tibba video/audio
    # temp files (thiyenawa nam) disk eken methanin ain karanawa - passe
    # bg_video_path/bg_audio_path aluth values walin overwrite wenna kalin
    _cleanup_bg_video(context.user_data)

    # Final render ekedi meken vada digu witharak process karanne nehe (max
    # BG_VIDEO_MAX_SECONDS) - eth preview ekata full frame ekma OK
    context.user_data["bg_video_path"] = video_path
    context.user_data["bg_width"] = width
    context.user_data["bg_height"] = height
    context.user_data["bg_video_duration"] = min(duration, BG_VIDEO_MAX_SECONDS)
    context.user_data["bg_image_b64"] = frame_b64   # preview ekata witharai - final render eka ffmpeg eken

    low_res_warning = _low_res_warning(width, height, bitrate_kbps)
    if low_res_warning:
        await context.bot.send_message(chat_id=chat_id, text=low_res_warning, parse_mode="Markdown")

    try:
        await status_msg.delete()
    except Exception:
        pass

    if context.user_data.get("replace_flow") == "video":
        # video eka replace unu nisa kalin audio eka invalid - "keep/mute"
        # ahanne nathuwa direct aluth audio ekak ahanawa
        return await _ask_new_audio_source(chat_id, context)

    return await _ask_video_audio(chat_id, context)


class _FakeQuery:
    """render_preview() only ever touches `query.message` (for chat_id and
    reply_photo). The logo image/text handlers below fire from a plain text/
    photo message, not a CallbackQuery, so this thin shim lets them reuse
    render_preview() unchanged instead of duplicating its logic."""
    def __init__(self, message):
        self.message = message


def _watermark_menu_keyboard(data: dict) -> InlineKeyboardMarkup:
    """Scrolling watermark ekata dedicated sub-menu eka - watermark ekak dan
    nathnam "add" options witharai, thibba nam okkoma settings (opacity/
    direction/speed/size) + preview/remove buttons."""
    has_wm = bool(data.get("watermark_enabled") and data.get("watermark_image_b64"))

    if not has_wm:
        rows = []
        can_reuse = data.get("logo_kind") == "image" and bool(data.get("logo_value"))
        if can_reuse:
            rows.append([InlineKeyboardButton("🔁 Use existing logo", callback_data="wm_add_reuse")])
        rows.append([InlineKeyboardButton("📤 Upload image", callback_data="wm_add_upload")])
        rows.append([InlineKeyboardButton("✏️ Type text", callback_data="wm_add_text")])
        rows.append([InlineKeyboardButton("🔙 Back", callback_data="wm_back")])
        return InlineKeyboardMarkup(rows)

    direction_label = WATERMARK_DIRECTION_LABELS.get(
        data.get("watermark_direction", WATERMARK_DIRECTION_DEFAULT),
        WATERMARK_DIRECTION_LABELS[WATERMARK_DIRECTION_DEFAULT],
    )
    side_label = WATERMARK_SIDE_LABELS.get(
        data.get("watermark_side", WATERMARK_SIDE_DEFAULT),
        WATERMARK_SIDE_LABELS[WATERMARK_SIDE_DEFAULT],
    )
    opacity = data.get("watermark_opacity", WATERMARK_OPACITY_DEFAULT)
    speed = data.get("watermark_speed", WATERMARK_SPEED_DEFAULT)
    scale = data.get("watermark_scale", WATERMARK_SCALE_DEFAULT)
    rows = [
        [
            InlineKeyboardButton("🌑 Opacity -", callback_data="wm_opacity_dec"),
            InlineKeyboardButton(f"👻 {opacity}%", callback_data="wm_noop"),
            InlineKeyboardButton("🌑 Opacity +", callback_data="wm_opacity_inc"),
        ],
        [InlineKeyboardButton(f"🔀 Scroll: {direction_label}", callback_data="wm_dir_cycle")],
        [InlineKeyboardButton(f"↔️ Position: {side_label}", callback_data="wm_side_cycle")],
        [
            InlineKeyboardButton("🐢 Speed -", callback_data="wm_speed_dec"),
            InlineKeyboardButton(f"⚡ {speed}px/s", callback_data="wm_noop"),
            InlineKeyboardButton("🐇 Speed +", callback_data="wm_speed_inc"),
        ],
        [
            InlineKeyboardButton("➖ Size", callback_data="wm_scale_dec"),
            InlineKeyboardButton(f"📏 {scale}%", callback_data="wm_noop"),
            InlineKeyboardButton("➕ Size", callback_data="wm_scale_inc"),
        ],
        [InlineKeyboardButton("🎬 Preview", callback_data="wm_preview")],
        [
            InlineKeyboardButton("📤 Change image", callback_data="wm_add_upload"),
            InlineKeyboardButton("✏️ Change text", callback_data="wm_add_text"),
        ],
        [InlineKeyboardButton("🗑 Remove watermark", callback_data="wm_remove")],
        [InlineKeyboardButton("🔙 Back", callback_data="wm_back")],
    ]
    return InlineKeyboardMarkup(rows)


def _watermark_menu_text(data: dict) -> str:
    has_wm = bool(data.get("watermark_enabled") and data.get("watermark_image_b64"))
    if has_wm:
        return "🌀 *Scrolling Watermark*\n\nAdjust the settings below, or preview it."
    return (
        "🌀 *Scrolling Watermark*\n\nAdd an image logo or type text that continuously "
        "scrolls up/down across your video background (like a moving watermark)."
    )


async def _wm_clear_media(context: ContextTypes.DEFAULT_TYPE, chat_id: int, data: dict):
    """Scrolling watermark preview ekedin (wm_preview click ekedin) hadapu
    video/photo message tika delete karanawa - preview ganna gaman aye click
    kaloth, kalin preview eka chat eke ithuru wenne nathuwa methanin clear
    karagannawa. wm_back click kaloth wath methema call karanawa."""
    ids = data.pop("wm_media_msg_ids", None) or []
    for mid in ids:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=mid)
        except Exception:
            pass


async def _wm_clear_user_messages(context: ContextTypes.DEFAULT_TYPE, chat_id: int, data: dict):
    """Watermark image/text type karanna kiyala user eva message tika (prompt
    eka nemei, e passe user eyaama evapu photo/text message eka) wm_back
    click kaloth clear karanawa - chat eka flow eka clean wenna."""
    ids = data.pop("wm_user_msg_ids", None) or []
    for mid in ids:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=mid)
        except Exception:
            pass


async def logo_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """CHOOSE_LOGO_TYPE state ekedi user photo/text/last-logo/remove/cancel
    monawa select kalath methanin handle wenawa."""
    query = update.callback_query
    await query.answer()
    data = context.user_data
    action = query.data
    chat_id = query.message.chat_id

    if action == "logo_choice_cancel":
        # ehema logo ekakwත් wenas kale nathuwa - preview eka dan tibba widiyatama thiyenawa
        try:
            await query.message.delete()
        except Exception:
            pass
        return ADJUSTING

    if action == "logo_choice_photo":
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text="📤 Send me the logo image (a transparent PNG sent as a *file*, "
            "not a compressed photo, works best).",
            parse_mode="Markdown",
        )
        data["logo_prompt_msg_id"] = sent.message_id
        return WAITING_LOGO_IMAGE

    if action == "logo_choice_text":
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text="✏️ Send me the text you want to use as your logo/watermark.",
        )
        data["logo_prompt_msg_id"] = sent.message_id
        return WAITING_LOGO_TEXT

    if action == "logo_choice_last":
        last_logo = data.get("last_settings", {}).get("logo")
        if not last_logo:
            await query.answer("No previous logo found", show_alert=True)
            return CHOOSE_LOGO_TYPE
        data["logo_kind"] = last_logo["kind"]
        data["logo_value"] = last_logo["value"]
        data["logo_scale"] = last_logo.get("scale", LOGO_SCALE_DEFAULT)
        data["logo_offset_bottom"] = last_logo.get("offset_bottom", LOGO_OFFSET_DEFAULT)
        try:
            await query.message.delete()
        except Exception:
            pass
        ok = await render_preview(query, context)
        return ADJUSTING if ok else ConversationHandler.END

    if action == "logo_choice_remove":
        data["logo_kind"] = None
        data["logo_value"] = None
        try:
            await query.message.delete()
        except Exception:
            pass
        ok = await render_preview(query, context)
        return ADJUSTING if ok else ConversationHandler.END

    return CHOOSE_LOGO_TYPE


async def receive_logo_image(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id

    photo = None
    if update.message.document and (update.message.document.mime_type or "").startswith("image/"):
        photo = update.message.document   # file vidiyata evapu eka - transparency preserve wenawa
    elif update.message.photo:
        photo = update.message.photo[-1]   # compressed photo - Telegram eken JPEG ekata convert wela transparency nathi wenawa

    if photo is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like an image. Please send a PNG, or /cancel to stop."
        )
        return WAITING_LOGO_IMAGE

    logo_prompt_msg_id = context.user_data.pop("logo_prompt_msg_id", None)
    if logo_prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=logo_prompt_msg_id)
        except Exception:
            pass

    status_msg = await update.message.reply_text("⏳ Processing your logo...")

    try:
        tg_file = await context.bot.get_file(photo.file_id)
        raw_bytes = bytes(await tg_file.download_as_bytearray())

        img = Image.open(BytesIO(raw_bytes))
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGBA")   # background photo eken wenas - methanin alpha channel eka ithuru karagannawa (transparent logo)

        buf = BytesIO()
        img.save(buf, format="PNG")
        context.user_data["logo_kind"] = "image"
        context.user_data["logo_value"] = base64.b64encode(buf.getvalue()).decode("utf-8")
        context.user_data.setdefault("logo_scale", LOGO_SCALE_DEFAULT)
        context.user_data.setdefault("logo_offset_bottom", LOGO_OFFSET_DEFAULT)
    except Exception as e:
        logger.exception("Logo image processing failed")
        await status_msg.edit_text(
            f"⚠️ Couldn't process that logo: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_LOGO_IMAGE

    try:
        await status_msg.delete()
    except Exception:
        pass

    notice_id = await _notify_generating(context, update.message.chat_id)
    ok = await render_preview(_FakeQuery(update.message), context)
    await _clear_generating_notice(context, update.message.chat_id, notice_id)
    return ADJUSTING if ok else ConversationHandler.END


async def receive_logo_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = update.message.text.strip()
    if not text:
        await update.message.reply_text("⚠️ Please send some text to use as the logo, or /cancel to stop.")
        return WAITING_LOGO_TEXT

    logo_prompt_msg_id = context.user_data.pop("logo_prompt_msg_id", None)
    if logo_prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=update.message.chat_id, message_id=logo_prompt_msg_id)
        except Exception:
            pass

    context.user_data["logo_kind"] = "text"
    context.user_data["logo_value"] = text
    context.user_data.setdefault("logo_scale", LOGO_SCALE_DEFAULT)
    context.user_data.setdefault("logo_offset_bottom", LOGO_OFFSET_DEFAULT)

    notice_id = await _notify_generating(context, update.message.chat_id)
    ok = await render_preview(_FakeQuery(update.message), context)
    await _clear_generating_notice(context, update.message.chat_id, notice_id)
    return ADJUSTING if ok else ConversationHandler.END


async def watermark_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """WATERMARK_MENU state ekedi wm_* buttons okkoma methanin handle wenawa -
    add(reuse/upload)/remove eka + opacity/direction/speed/size adjust +
    GIF preview + back (main Adjust menu ekata)."""
    query = update.callback_query
    data = context.user_data
    action = query.data

    if data.get("generating"):
        await query.answer("⏳ Please wait...", show_alert=False)
        return WATERMARK_MENU

    # "wm_preview" ekata methanin ma (await query.answer() ekatawath kalin)
    # lock eka set karanne - naththam podi race ekak thiyenawa: user ikmanata
    # button eka 2k click kaloth, 2ni callback eka methanata ena welawata,
    # mulinma ekata "generating" flag eka thawama False widiyata thiyennata
    # puluwan (await query.answer() eken event loop eka yield unoth), ithin
    # ffmpeg process 2k ekawara patan gannawa - 1GB RAM server ekaka eka
    # danger ekak.
    if action == "wm_preview":
        data["generating"] = True

    await query.answer()

    if action == "wm_noop":
        return WATERMARK_MENU

    if action == "wm_back":
        chat_id = query.message.chat_id
        # preview eken hadapu video/photo tika + user type/upload kala
        # message tika + dan penena menu (button set) eka - okkoma ain
        # karala ADJUSTING screen ekata (main preview + Done button eka
        # witharai) clean widiyata return karanawa
        await _wm_clear_media(context, chat_id, data)
        await _wm_clear_user_messages(context, chat_id, data)
        data.pop("watermark_menu_msg_id", None)
        try:
            await query.message.delete()
        except Exception:
            pass
        return ADJUSTING

    if action == "wm_add_reuse":
        if data.get("logo_kind") != "image" or not data.get("logo_value"):
            await query.answer("⚠️ No existing image logo to reuse", show_alert=True)
            return WATERMARK_MENU
        data["watermark_kind"] = "image"
        data["watermark_image_b64"] = data["logo_value"]
        data["watermark_enabled"] = True
        data.setdefault("watermark_opacity", WATERMARK_OPACITY_DEFAULT)
        data.setdefault("watermark_direction", WATERMARK_DIRECTION_DEFAULT)
        data.setdefault("watermark_speed", WATERMARK_SPEED_DEFAULT)
        data.setdefault("watermark_scale", WATERMARK_SCALE_DEFAULT)
        data.setdefault("watermark_side", WATERMARK_SIDE_DEFAULT)
        await query.edit_message_text(
            _watermark_menu_text(data), parse_mode="Markdown", reply_markup=_watermark_menu_keyboard(data),
        )
        return WATERMARK_MENU

    if action == "wm_add_upload":
        # "Upload image" click karapu welavata udin thibba menu (button set)
        # eka chat eken ain karanawa - ehema karoth prompt eka witharai penei,
        # kalin button set eka "ithiri" wela chat eke thiyenne nehe
        try:
            await query.message.delete()
        except Exception:
            pass
        data.pop("watermark_menu_msg_id", None)
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="📤 Send me the watermark image (a transparent PNG sent as a *file*, "
            "not a compressed photo, works best).",
            parse_mode="Markdown",
        )
        data["watermark_prompt_msg_id"] = sent.message_id
        return WAITING_WATERMARK_IMAGE

    if action == "wm_add_text":
        # methanath ekamai - "Type text" click kaloth kalin thibba menu eka
        # ain karala prompt eka witharak thiyenna denawa
        try:
            await query.message.delete()
        except Exception:
            pass
        data.pop("watermark_menu_msg_id", None)
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="✏️ Send me the text you want to use as your watermark.",
        )
        data["watermark_prompt_msg_id"] = sent.message_id
        return WAITING_WATERMARK_TEXT

    if action == "wm_remove":
        data["watermark_enabled"] = False
        data["watermark_kind"] = None
        data["watermark_image_b64"] = None
        await query.edit_message_text(
            _watermark_menu_text(data), parse_mode="Markdown", reply_markup=_watermark_menu_keyboard(data),
        )
        return WATERMARK_MENU

    if action == "wm_opacity_inc":
        data["watermark_opacity"] = min(WATERMARK_OPACITY_MAX, data.get("watermark_opacity", WATERMARK_OPACITY_DEFAULT) + WATERMARK_OPACITY_STEP)
    elif action == "wm_opacity_dec":
        data["watermark_opacity"] = max(WATERMARK_OPACITY_MIN, data.get("watermark_opacity", WATERMARK_OPACITY_DEFAULT) - WATERMARK_OPACITY_STEP)
    elif action == "wm_speed_inc":
        data["watermark_speed"] = min(WATERMARK_SPEED_MAX, data.get("watermark_speed", WATERMARK_SPEED_DEFAULT) + WATERMARK_SPEED_STEP)
    elif action == "wm_speed_dec":
        data["watermark_speed"] = max(WATERMARK_SPEED_MIN, data.get("watermark_speed", WATERMARK_SPEED_DEFAULT) - WATERMARK_SPEED_STEP)
    elif action == "wm_scale_inc":
        data["watermark_scale"] = min(WATERMARK_SCALE_MAX, data.get("watermark_scale", WATERMARK_SCALE_DEFAULT) + WATERMARK_SCALE_STEP)
    elif action == "wm_scale_dec":
        data["watermark_scale"] = max(WATERMARK_SCALE_MIN, data.get("watermark_scale", WATERMARK_SCALE_DEFAULT) - WATERMARK_SCALE_STEP)
    elif action == "wm_dir_cycle":
        cur = data.get("watermark_direction", WATERMARK_DIRECTION_DEFAULT)
        idx = WATERMARK_DIRECTIONS.index(cur) if cur in WATERMARK_DIRECTIONS else 0
        data["watermark_direction"] = WATERMARK_DIRECTIONS[(idx + 1) % len(WATERMARK_DIRECTIONS)]
    elif action == "wm_side_cycle":
        cur = data.get("watermark_side", WATERMARK_SIDE_DEFAULT)
        idx = WATERMARK_SIDES.index(cur) if cur in WATERMARK_SIDES else 0
        data["watermark_side"] = WATERMARK_SIDES[(idx + 1) % len(WATERMARK_SIDES)]
    elif action == "wm_preview":
        if not (data.get("bg_kind") == "video" and data.get("bg_video_path")):
            data["generating"] = False
            await query.answer("⚠️ Video background ekak thiyanna one - meka preview karanna", show_alert=True)
            return WATERMARK_MENU
        if not data.get("watermark_image_b64"):
            data["generating"] = False
            await query.answer("⚠️ Watermark image ekak dama nehe", show_alert=True)
            return WATERMARK_MENU

        # "generating" text eka methanma (menu message ekema, button set eka
        # udin) edit karanawa - wenama status message ekak button set ekata
        # PAHALA send karanne nehe (kalinma code ekedi widiyata). Progress %
        # eka 0->100 methanma update wenawa, button ticak thiyenawa - user ta
        # ekamawa panel ekema real-time progress eka penenawa.
        async def _progress(pct: int):
            try:
                await query.edit_message_text(
                    f"⏳ Generating preview... {pct}%",
                    reply_markup=_watermark_menu_keyboard(data),
                )
            except Exception:
                pass  # "message is not modified" wage harmless errors ignore karanawa

        try:
            await _progress(0)
        except Exception:
            pass

        media_kind, media_bytes, note = "video", b"", None
        try:
            media_kind, media_bytes = await generate_watermark_preview(
                data["bg_video_path"],
                base64.b64decode(data["watermark_image_b64"]),
                watermark_opacity=data.get("watermark_opacity", WATERMARK_OPACITY_DEFAULT),
                watermark_scale=data.get("watermark_scale", WATERMARK_SCALE_DEFAULT),
                watermark_direction=data.get("watermark_direction", WATERMARK_DIRECTION_DEFAULT),
                watermark_speed=data.get("watermark_speed", WATERMARK_SPEED_DEFAULT),
                watermark_side=data.get("watermark_side", WATERMARK_SIDE_DEFAULT),
                progress_cb=_progress,
                background_is_static_image=bool(data.get("bg_video_is_photo")),
            )
            if media_kind == "photo":
                note = (
                    "⚠️ Server eka busy nisa video preview eka fast eken hadenna baruna - "
                    "meka opacity/scale/position check karaganna static frame ekak (speed eka "
                    "methanin penenne nehe, final video ekedi හරියටම scroll වෙනවා)."
                )
        except Exception:
            logger.exception("Watermark preview failed (all fallback tiers)")
            media_bytes = b""

        chat_id = query.message.chat_id

        # kalin preview click ekaka hadapu video/photo eka thibba nam, aluth
        # eka evanna kalin eka delete karanawa - chat eka video ganan
        # ithuru wela flow eka dirty wenna denne nehe
        await _wm_clear_media(context, chat_id, data)

        if media_bytes:
            try:
                if media_kind == "photo":
                    sent_media = await context.bot.send_photo(
                        chat_id=chat_id, photo=BytesIO(media_bytes), caption=note
                    )
                else:
                    sent_media = await context.bot.send_video(chat_id=chat_id, video=BytesIO(media_bytes))
                data["wm_media_msg_ids"] = [sent_media.message_id]
            except Exception:
                logger.exception("Sending watermark preview media failed")
                await context.bot.send_message(chat_id=chat_id, text="⚠️ Preview eka send karanna baruna.")
        else:
            await context.bot.send_message(
                chat_id=chat_id,
                text="⚠️ Preview eka hadenna baye (server busy). Final video ekedi watermark eka හරියටම එනවා.",
            )

        # button set (menu) eka - kalinma tibba widiyata methanma edit
        # karanne nathuwa, dan evapu preview ekata PAHALA aluth message
        # ekak vidihata evanawa (kalin tibba menu message eka delete
        # karala) - ehema karoth buttons tik hama welawakama chat eke
        # ATHIN ma thiyenawa, video/photo tika udin scroll karanna one na
        try:
            await query.message.delete()
        except Exception:
            pass
        new_menu = await context.bot.send_message(
            chat_id=chat_id,
            text=_watermark_menu_text(data), parse_mode="Markdown", reply_markup=_watermark_menu_keyboard(data),
        )
        data["watermark_menu_msg_id"] = new_menu.message_id

        data["generating"] = False
        return WATERMARK_MENU
    else:
        return WATERMARK_MENU

    try:
        await query.edit_message_reply_markup(reply_markup=_watermark_menu_keyboard(data))
    except Exception:
        pass
    return WATERMARK_MENU


async def receive_watermark_image(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id

    photo = None
    if update.message.document and (update.message.document.mime_type or "").startswith("image/"):
        photo = update.message.document
    elif update.message.photo:
        photo = update.message.photo[-1]

    if photo is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like an image. Please send a PNG, or /cancel to stop."
        )
        return WAITING_WATERMARK_IMAGE

    # user unmath (image eka) tama send kala message eka - "wm_back" click
    # karoth methanin ain karanna one nisa, watermark flow eke aluth track
    # ekata methanma add karagannawa
    context.user_data.setdefault("wm_user_msg_ids", []).append(update.message.message_id)

    prompt_msg_id = context.user_data.pop("watermark_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    status_msg = await update.message.reply_text("⏳ Processing your watermark image...")

    try:
        tg_file = await context.bot.get_file(photo.file_id)
        raw_bytes = bytes(await tg_file.download_as_bytearray())

        img = Image.open(BytesIO(raw_bytes))
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGBA")

        buf = BytesIO()
        img.save(buf, format="PNG")
        data = context.user_data
        data["watermark_kind"] = "image"
        data["watermark_image_b64"] = base64.b64encode(buf.getvalue()).decode("utf-8")
        data["watermark_enabled"] = True
        data.setdefault("watermark_opacity", WATERMARK_OPACITY_DEFAULT)
        data.setdefault("watermark_direction", WATERMARK_DIRECTION_DEFAULT)
        data.setdefault("watermark_speed", WATERMARK_SPEED_DEFAULT)
        data.setdefault("watermark_scale", WATERMARK_SCALE_DEFAULT)
        data.setdefault("watermark_side", WATERMARK_SIDE_DEFAULT)
    except Exception as e:
        logger.exception("Watermark image processing failed")
        await status_msg.edit_text(
            f"⚠️ Couldn't process that image: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_WATERMARK_IMAGE

    try:
        await status_msg.delete()
    except Exception:
        pass

    sent_menu = await update.message.reply_text(
        _watermark_menu_text(context.user_data),
        parse_mode="Markdown",
        reply_markup=_watermark_menu_keyboard(context.user_data),
    )
    context.user_data["watermark_menu_msg_id"] = sent_menu.message_id
    return WATERMARK_MENU


async def receive_watermark_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """WAITING_WATERMARK_TEXT state ekedi user type kala text eka, transparent
    PNG ekakata render karala (`render_watermark_text_png()`), image watermark
    ekak wage ma save karanawa - ithuru okkoma code eka (scale/opacity/
    scroll/preview) PNG bytes ekak vidihata handle karana nisa wenasak ona
    wenne nehe."""
    text = update.message.text.strip()
    if not text:
        await update.message.reply_text("⚠️ Please send some text to use as the watermark, or /cancel to stop.")
        return WAITING_WATERMARK_TEXT

    chat_id = update.message.chat_id

    # user unmath (text eka) tama send kala message eka - "wm_back" click
    # karoth methanin ain karanna one nisa, watermark flow eke track ekata
    # methanma add karagannawa
    context.user_data.setdefault("wm_user_msg_ids", []).append(update.message.message_id)

    prompt_msg_id = context.user_data.pop("watermark_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    status_msg = await update.message.reply_text("⏳ Processing your watermark text...")

    try:
        browser = context.application.bot_data["browser"]
        png_bytes = await render_watermark_text_png(browser, text)
        data = context.user_data
        data["watermark_kind"] = "text"
        data["watermark_image_b64"] = base64.b64encode(png_bytes).decode("utf-8")
        data["watermark_enabled"] = True
        data.setdefault("watermark_opacity", WATERMARK_OPACITY_DEFAULT)
        data.setdefault("watermark_direction", WATERMARK_DIRECTION_DEFAULT)
        data.setdefault("watermark_speed", WATERMARK_SPEED_DEFAULT)
        data.setdefault("watermark_scale", WATERMARK_SCALE_DEFAULT)
        data.setdefault("watermark_side", WATERMARK_SIDE_DEFAULT)
    except Exception as e:
        logger.exception("Watermark text processing failed")
        await status_msg.edit_text(
            f"⚠️ Couldn't process that text: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_WATERMARK_TEXT

    try:
        await status_msg.delete()
    except Exception:
        pass

    sent_menu = await update.message.reply_text(
        _watermark_menu_text(context.user_data),
        parse_mode="Markdown",
        reply_markup=_watermark_menu_keyboard(context.user_data),
    )
    context.user_data["watermark_menu_msg_id"] = sent_menu.message_id
    return WATERMARK_MENU


async def receive_emoji(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # user ':)' ':D' '<3' wage text emoticons dammoth, ewa real Unicode
    # emoji walata methanin convert karanawa - naththam pahalin emoji CDN
    # eken fetch karaddi fail wela, image ekata ennema nathuwa yanawa
    context.user_data["emojis"] = convert_text_emoticons(update.message.text.strip())

    # e step eka iwara una nisa e prompt eka chat eken sampurnayenma ain karanawa
    # (edit karala ehema thiyaganne nehe) - hama step ekatama e step ekatama
    # thani message ekak witharai thiyenne
    emoji_prompt_msg_id = context.user_data.pop("emoji_prompt_msg_id", None)
    if emoji_prompt_msg_id:
        try:
            await context.bot.delete_message(
                chat_id=update.message.chat_id, message_id=emoji_prompt_msg_id
            )
        except Exception:
            pass   # message eka kalinma delete unath ptoblem nehe

    if context.user_data.get("from_template"):
        # Template eken style eka (color eka ekthara) dan set wela, ithin
        # aye ahanna one nathuwa kelinma preview eka pennanawa - color eka
        # wenas karanna one unoth, Adjust screen eke "🎨 Pick Color" button
        # eken passe wenas karaganna puluwan
        notice_id = await _notify_generating(context, update.message.chat_id)
        ok = await render_preview(_FakeQuery(update.message), context)
        await _clear_generating_notice(context, update.message.chat_id, notice_id)
        return ADJUSTING if ok else ConversationHandler.END

    last_settings = context.user_data.get("last_settings")
    if last_settings:
        text = (
            "Nice! 🎉\n\n"
            "Now choose a color for the text, "
            "or apply your last used settings (size + color) with a single tap 👇"
        )
    else:
        text = "Nice! 🎉\n\nNow choose a color for the text 👇"

    keyboard = color_keyboard(show_last_settings=bool(last_settings))
    sent = await update.message.reply_text(text, reply_markup=keyboard)
    context.user_data["color_prompt_msg_id"] = sent.message_id

    return WAITING_COLOR


async def receive_edit_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Adjust screen eke '✏️ Text වෙනස් කරන්න' button eken enna - user aluth
    text ekak type kaloth methanin patan gannawa, e text ekama "" quote eken
    header ekakuth thiyenne nam ekath methanin re-parse wenawa (render_preview
    eken)."""
    data = context.user_data
    new_text = update.message.text
    if not new_text or not new_text.strip():
        await update.message.reply_text("⚠️ Text එක හිස්. ආයෙත් type කරලා send කරන්න:")
        return WAITING_EDIT_TEXT

    new_text = apply_native_formatting_as_markup(new_text, update.message.entities or ())

    markup_issues = find_markup_issues(new_text)
    if markup_issues:
        await update.message.reply_text(
            "⚠️ Text එකේ ##/// sign වැරදිලා තියෙනවා වගේ පේනවා (close කරලා නෑ):\n"
            + "\n".join(markup_issues)
            + "\n\nඑවා හරි කරලා ආයෙත් text එක type කරලා send කරන්න."
        )
        return WAITING_EDIT_TEXT

    edit_text_prompt_msg_id = data.pop("edit_text_prompt_msg_id", None)
    if edit_text_prompt_msg_id:
        try:
            await context.bot.delete_message(
                chat_id=update.message.chat_id, message_id=edit_text_prompt_msg_id
            )
        except Exception:
            pass

    data["text"] = new_text
    notice_id = await _notify_generating(context, update.message.chat_id)
    try:
        ok = await render_preview(_FakeQuery(update.message), context)
    finally:
        await _clear_generating_notice(context, update.message.chat_id, notice_id)
    return ADJUSTING if ok else ConversationHandler.END


async def _finish_color_step(query, context: ContextTypes.DEFAULT_TYPE):
    """Color eka confirm unu passe, e prompt message eka chat eken sampurnayenma
    ain karala (buttons witharak ain karanne na) preview eka pennanawa."""
    color_prompt_msg_id = context.user_data.pop("color_prompt_msg_id", None)
    if color_prompt_msg_id:
        try:
            await context.bot.delete_message(
                chat_id=query.message.chat_id, message_id=color_prompt_msg_id
            )
        except Exception:
            pass   # message eka kalinma delete unath ptoblem nehe

    notice_id = await _notify_generating(context, query.message.chat_id)
    ok = await render_preview(query, context)
    await _clear_generating_notice(context, query.message.chat_id, notice_id)
    return ADJUSTING if ok else ConversationHandler.END


async def color_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()

    color_key = query.data.replace("color_", "")
    context.user_data["color"] = COLORS.get(color_key, COLORS["white"])

    return await _finish_color_step(query, context)


async def use_last_settings_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = context.user_data
    last_settings = data.get("last_settings")

    if not last_settings:
        await query.answer("No previous settings found", show_alert=True)
        return WAITING_COLOR

    await query.answer("Applying last settings...")

    data["font_size"] = last_settings.get("font_size", FONT_SIZE_DEFAULT)
    data["emoji_size"] = last_settings.get("emoji_size", EMOJI_SIZE_DEFAULT)
    data["color"] = last_settings.get("color", COLORS["white"])
    data["font_weight"] = last_settings.get("font_weight", FONT_WEIGHT_DEFAULT)
    data["italic"] = last_settings.get("italic", ITALIC_DEFAULT)
    data["align"] = last_settings.get("align", ALIGN_DEFAULT)
    # background photo ekak thibba nam witharai methanin real effect ekak
    # thiyenne (photo ekak nathi post ekakata overlay/blur/position relevant nehe)
    data["overlay_opacity"] = last_settings.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT)
    data["text_offset_y"] = last_settings.get("text_offset_y", TEXT_OFFSET_DEFAULT)
    data["bg_blur"] = last_settings.get("bg_blur", BLUR_DEFAULT)
    data["chromatic_aberration"] = last_settings.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT)
    data["chromatic_shift"] = last_settings.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT)
    data["vhs_effect"] = last_settings.get("vhs_effect", VHS_EFFECT_DEFAULT)
    data["vhs_strength"] = last_settings.get("vhs_strength", VHS_STRENGTH_DEFAULT)
    data["intro_black_seconds"] = last_settings.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT)
    data["header_font_size"] = last_settings.get("header_font_size", HEADER_FONT_SIZE_DEFAULT)
    data["header_color"] = last_settings.get("header_color", HEADER_COLOR_DEFAULT)
    data["header_bold"] = last_settings.get("header_bold", HEADER_BOLD_DEFAULT)
    data["header_gap_top"] = last_settings.get("header_gap_top", HEADER_GAP_TOP_DEFAULT)
    data["header_gap_bottom"] = last_settings.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT)

    return await _finish_color_step(query, context)


async def receive_template_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    data = context.user_data
    name = update.message.text.strip()

    if not name:
        await update.message.reply_text("⚠️ Nomak ekak type karanna (empty widiyata yawanna bari).")
        return WAITING_TEMPLATE_NAME

    if len(name.encode("utf-8")) > 45:
        # callback_data ekata Telegram eken 64-byte limit ekak thiyenawa
        # ("tpl_delete_" prefix ekath ekka), Sinhala characters multi-byte
        # (UTF-8 ekedi 3 bytes vitharak) nisa character count ekata wada
        # byte length ekma check karanawa
        await update.message.reply_text(
            "⚠️ Nama tikak digui. Podi nomak ekak (Sinhala nam character 10-15ක් "
            "witharak, English nam 30-40ක් witharak) try karanna."
        )
        return WAITING_TEMPLATE_NAME

    templates = data.setdefault("templates", {})
    if len(templates) >= MAX_TEMPLATES_PER_USER and name not in templates:
        await update.message.reply_text(
            f"⚠️ Max {MAX_TEMPLATES_PER_USER} templates witharai save karanna puluwan. "
            f"/templates ekedin ekak delete karala try karanna."
        )
        return ADJUSTING

    is_overwrite = name in templates
    templates[name] = _style_snapshot(data)
    data["active_template_name"] = name   # methanin passe "Update Template" button ekata switch wenawa

    await update.message.reply_text(
        f"✅ *'{name}'* {'update' if is_overwrite else 'save'} kara!\n\n"
        f"අලුත් post ekak patan gannakota *📁 Use Template* button eken methanin "
        f"kelinma load karagannna puluwan.",
        parse_mode="Markdown",
    )
    return ADJUSTING


async def list_templates(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/templates command - save karapu templates tika balanna saha delete karanna."""
    templates = context.user_data.get("templates", {})
    if not templates:
        await update.message.reply_text(
            "📁 Oyata thama saved templates naha.\n\n"
            "Post ekak hadaddi, Adjust screen ekedi *💾 Save as Template* button eken "
            "ekak save karanna puluwan.",
            parse_mode="Markdown",
        )
        return

    rows = [
        [
            InlineKeyboardButton(f"👁 {name}", callback_data=f"tpl_preview_{name}"),
            InlineKeyboardButton("🗑", callback_data=f"tpl_delete_{name}"),
        ]
        for name in templates
    ]
    await update.message.reply_text(
        f"📁 *Oyage saved templates ({len(templates)}/{MAX_TEMPLATES_PER_USER}):*\n\n"
        f"👁 - sample text ekakin ekeka ehema penei kiyala balanna, 🗑 - delete karanna "
        f"(post hadaddi *Use Template* eken methanin templates use karanna puluwan).",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup(rows),
    )


async def template_preview_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/templates list eke 👁 button eken enna - "Use Template" click karanna
    kalinma, e template eke style eka (color/size/bold/logo/watermark/header
    okkoma) dummy sample text ekakin, plain background ekaka render karala
    photo ekak vidihata pennanawa - user ta thoraganna kalinma ඇත්තටම කොහොමද
    පේන්නෙ කියලා දකින්න පුළුවන්."""
    query = update.callback_query
    name = query.data[len("tpl_preview_"):]
    templates = context.user_data.get("templates", {})
    snapshot = templates.get(name)
    if not snapshot:
        await query.answer("⚠️ Me template eka thama naha (delete wela wenna puluwan).", show_alert=True)
        return
    await query.answer("⏳ Preview ekak hadanawa...")

    browser = context.application.bot_data["browser"]
    sample_raw = (
        f'"{name}"\n\n'
        "Me tamai me template eke sample preview eka - text size, color, "
        "bold/italic saha logo/watermark okkoma me widiyata penei."
    )
    header_text, body_text = split_header_text(sample_raw)
    logo = snapshot.get("logo") or {}

    try:
        image_buf = await generate_image(
            browser,
            body_text,
            "",   # sample ekata emoji ona na
            snapshot.get("font_size", FONT_SIZE_DEFAULT),
            EMOJI_SIZE_DEFAULT,
            snapshot.get("color", COLORS["white"]),
            transparent=False,
            font_weight=snapshot.get("font_weight", FONT_WEIGHT_DEFAULT),
            italic=snapshot.get("italic", ITALIC_DEFAULT),
            align=snapshot.get("align", ALIGN_DEFAULT),
            bg_color=PREVIEW_BG,
            canvas_width=IMG_SIZE,
            canvas_height=IMG_SIZE,
            bg_image_b64=None,
            overlay_opacity=snapshot.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT),
            text_offset_y=snapshot.get("text_offset_y", TEXT_OFFSET_DEFAULT),
            blur_px=0,
            blur_type=snapshot.get("blur_type", BLUR_TYPE_DEFAULT),
            logo_kind=logo.get("kind"),
            logo_value=logo.get("value"),
            logo_scale=logo.get("scale", LOGO_SCALE_DEFAULT),
            logo_offset_bottom=logo.get("offset_bottom", LOGO_OFFSET_DEFAULT),
            header_text=header_text,
            header_font_size=snapshot.get("header_font_size", HEADER_FONT_SIZE_DEFAULT),
            header_color=snapshot.get("header_color", HEADER_COLOR_DEFAULT),
            header_bold=snapshot.get("header_bold", HEADER_BOLD_DEFAULT),
            header_gap_top=snapshot.get("header_gap_top", HEADER_GAP_TOP_DEFAULT),
            header_gap_bottom=snapshot.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT),
            highlight_font_scale=snapshot.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT),
            highlight_bold=snapshot.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT),
            highlight_italic=snapshot.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT),
            stroke_width=snapshot.get("stroke_width", STROKE_WIDTH_DEFAULT),
            stroke_color=snapshot.get("stroke_color", STROKE_COLOR_DEFAULT),
        )
    except Exception as e:
        logger.exception("Template preview generation failed")
        await context.bot.send_message(
            chat_id=query.message.chat_id, text=f"⚠️ Preview ekak hadanna baruna: {e}"
        )
        return

    await send_with_retry(
        context.bot.send_photo,
        chat_id=query.message.chat_id,
        photo=image_buf,
        caption=f"👁 *'{name}'* template eke preview eka (sample text ekakin)",
        parse_mode="Markdown",
        what="template preview send_photo",
    )


async def template_delete_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    name = query.data[len("tpl_delete_"):]
    templates = context.user_data.get("templates", {})
    templates.pop(name, None)
    try:
        await query.edit_message_text(f"🗑 *'{name}'* delete kara.", parse_mode="Markdown")
    except Exception:
        pass


def _style_snapshot(data: dict) -> dict:
    """Dan tibba style settings tika (text color/size/align/bold, overlay/blur/text-position,
    logo) ekama dict ekakata gannawa - Templates walata mekama use karanawa (save/use dekamatama)."""
    return {
        "font_size": data.get("font_size", FONT_SIZE_DEFAULT),
        "emoji_size": data.get("emoji_size", EMOJI_SIZE_DEFAULT),
        "color": data.get("color", COLORS["white"]),
        "font_weight": data.get("font_weight", FONT_WEIGHT_DEFAULT),
        "italic": data.get("italic", ITALIC_DEFAULT),
        "align": data.get("align", ALIGN_DEFAULT),
        "overlay_opacity": data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT),
        "bg_blur": data.get("bg_blur", BLUR_DEFAULT),
        "blur_type": data.get("blur_type", BLUR_TYPE_DEFAULT),
        "chromatic_aberration": data.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT),
        "chromatic_shift": data.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT),
        "vhs_effect": data.get("vhs_effect", VHS_EFFECT_DEFAULT),
        "vhs_strength": data.get("vhs_strength", VHS_STRENGTH_DEFAULT),
        "intro_black_seconds": data.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT),
        "text_offset_y": data.get("text_offset_y", TEXT_OFFSET_DEFAULT),
        "header_font_size": data.get("header_font_size", HEADER_FONT_SIZE_DEFAULT),
        "header_color": data.get("header_color", HEADER_COLOR_DEFAULT),
        "header_bold": data.get("header_bold", HEADER_BOLD_DEFAULT),
        "header_gap_top": data.get("header_gap_top", HEADER_GAP_TOP_DEFAULT),
        "header_gap_bottom": data.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT),
        "highlight_font_scale": data.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT),
        "highlight_bold": data.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT),
        "highlight_italic": data.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT),
        "stroke_width": data.get("stroke_width", STROKE_WIDTH_DEFAULT),
        "stroke_color": data.get("stroke_color", STROKE_COLOR_DEFAULT),
        "logo": (
            {
                "kind": data["logo_kind"],
                "value": data["logo_value"],
                "scale": data.get("logo_scale", LOGO_SCALE_DEFAULT),
                "offset_bottom": data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT),
            }
            if data.get("logo_kind") else None
        ),
        # scrolling watermark eka - image ekak dama tibba nam witharai save
        # wenne (settings 4mama - opacity/direction/speed/scale - image ekath ekka)
        "watermark": (
            {
                "kind": data.get("watermark_kind"),
                "image_b64": data.get("watermark_image_b64"),
                "opacity": data.get("watermark_opacity", WATERMARK_OPACITY_DEFAULT),
                "direction": data.get("watermark_direction", WATERMARK_DIRECTION_DEFAULT),
                "speed": data.get("watermark_speed", WATERMARK_SPEED_DEFAULT),
                "scale": data.get("watermark_scale", WATERMARK_SCALE_DEFAULT),
                "side": data.get("watermark_side", WATERMARK_SIDE_DEFAULT),
            }
            if data.get("watermark_enabled") and data.get("watermark_image_b64") else None
        ),
    }


def _apply_style_snapshot(data: dict, snapshot: dict):
    """_style_snapshot() eken save kala dict ekak aye data ekata apply karanawa
    (Use Template eka click kaloth, saha "use last settings" ekedith methanma
    logic eka - eeka wenama duplicate karanne nathuwa methanin share karanawa)."""
    data["font_size"] = snapshot.get("font_size", FONT_SIZE_DEFAULT)
    data["emoji_size"] = snapshot.get("emoji_size", EMOJI_SIZE_DEFAULT)
    data["color"] = snapshot.get("color", COLORS["white"])
    data["font_weight"] = snapshot.get("font_weight", FONT_WEIGHT_DEFAULT)
    data["italic"] = snapshot.get("italic", ITALIC_DEFAULT)
    data["align"] = snapshot.get("align", ALIGN_DEFAULT)
    data["overlay_opacity"] = snapshot.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT)
    data["bg_blur"] = snapshot.get("bg_blur", BLUR_DEFAULT)
    data["blur_type"] = snapshot.get("blur_type", BLUR_TYPE_DEFAULT)
    data["chromatic_aberration"] = snapshot.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT)
    data["chromatic_shift"] = snapshot.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT)
    data["vhs_effect"] = snapshot.get("vhs_effect", VHS_EFFECT_DEFAULT)
    data["vhs_strength"] = snapshot.get("vhs_strength", VHS_STRENGTH_DEFAULT)
    data["intro_black_seconds"] = snapshot.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT)
    data["text_offset_y"] = snapshot.get("text_offset_y", TEXT_OFFSET_DEFAULT)
    data["header_font_size"] = snapshot.get("header_font_size", HEADER_FONT_SIZE_DEFAULT)
    data["header_color"] = snapshot.get("header_color", HEADER_COLOR_DEFAULT)
    data["header_bold"] = snapshot.get("header_bold", HEADER_BOLD_DEFAULT)
    data["header_gap_top"] = snapshot.get("header_gap_top", HEADER_GAP_TOP_DEFAULT)
    data["header_gap_bottom"] = snapshot.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT)
    data["highlight_font_scale"] = snapshot.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT)
    data["highlight_bold"] = snapshot.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT)
    data["highlight_italic"] = snapshot.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT)
    data["stroke_width"] = snapshot.get("stroke_width", STROKE_WIDTH_DEFAULT)
    data["stroke_color"] = snapshot.get("stroke_color", STROKE_COLOR_DEFAULT)
    logo = snapshot.get("logo") or {}
    data["logo_kind"] = logo.get("kind")
    data["logo_value"] = logo.get("value")
    data["logo_scale"] = logo.get("scale", LOGO_SCALE_DEFAULT)
    data["logo_offset_bottom"] = logo.get("offset_bottom", LOGO_OFFSET_DEFAULT)

    watermark = snapshot.get("watermark") or {}
    data["watermark_enabled"] = bool(watermark.get("image_b64"))
    data["watermark_kind"] = watermark.get("kind")
    data["watermark_image_b64"] = watermark.get("image_b64")
    data["watermark_opacity"] = watermark.get("opacity", WATERMARK_OPACITY_DEFAULT)
    _saved_dir = watermark.get("direction", WATERMARK_DIRECTION_DEFAULT)
    data["watermark_direction"] = _saved_dir if _saved_dir in WATERMARK_DIRECTIONS else WATERMARK_DIRECTION_DEFAULT
    data["watermark_speed"] = watermark.get("speed", WATERMARK_SPEED_DEFAULT)
    data["watermark_scale"] = watermark.get("scale", WATERMARK_SCALE_DEFAULT)
    data["watermark_side"] = watermark.get("side", WATERMARK_SIDE_DEFAULT)


async def adjust_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = context.user_data
    action = query.data

    # dan ekak generate wemin thiyenna athara ithuru click ignore karanawa (debounce)
    if data.get("generating"):
        await query.answer("⏳ Please wait...", show_alert=False)
        return ADJUSTING

    await query.answer()

    if action == "adj_noop":
        # meka info-only button ekak (e.g. "40%" / "+0px" label eka) - click
        # karoth kisima wenasak wenne nehe
        return ADJUSTING

    if action == "adj_update_template":
        name = data.get("active_template_name")
        templates = data.setdefault("templates", {})
        if not name or name not in templates:
            # template eka delete wela wenna puluwan (methanata ena athara /templates
            # ekedin) - ehema unoth normal "save as new" flow ekatama fallback wenawa
            await query.answer(
                "⚠️ Me template eka thama naha (delete wela wenna puluwan). "
                "'Save as New Template' widiyata save karanna.",
                show_alert=True,
            )
            return ADJUSTING
        templates[name] = _style_snapshot(data)
        await query.answer(f"✅ '{name}' template eka update kara!", show_alert=True)
        return ADJUSTING

    if action == "adj_save_template":
        templates = data.get("templates", {})
        if len(templates) >= MAX_TEMPLATES_PER_USER:
            await query.answer(
                f"⚠️ Max {MAX_TEMPLATES_PER_USER} templates witharai save karanna puluwan. "
                f"/templates ekedin ekak delete karala try karanna.",
                show_alert=True,
            )
            return ADJUSTING
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="💾 *Template ekata monoma nomak dennada?*\n\n"
            "(e.g. \"Quote Style\", \"Motivation Post\" - passe menna nama eken "
            "aye load karagannawa)",
            parse_mode="Markdown",
        )
        data["template_prompt_msg_id"] = sent.message_id
        return WAITING_TEMPLATE_NAME

    if action == "adj_pick_color":
        show_last = bool(data.get("last_settings")) and not data.get("from_template")
        await query.edit_message_reply_markup(
            reply_markup=color_keyboard(show_last_settings=show_last)
        )
        return ADJUSTING

    if action == "adj_edit_text":
        # kalin type kala text eka replace karanna one welawakadi - style/color/logo
        # settings tika touch karanne nathuwa, "text" field eka witharak wenas
        # karala preview eka aye render karanawa
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="✏️ අලුත් text එක type කරලා send කරන්න (කලින් type කරපු එක replace වෙනවා):",
        )
        data["edit_text_prompt_msg_id"] = sent.message_id
        return WAITING_EDIT_TEXT

    if action == "adj_replace_video":
        # "Re-edit" karapu passe witharak penena button eka - dan tibba video
        # background eka wenasakota, ithin video download unu passe aluth
        # audio ekakuth ahanawa (kalin audio eka aluth video ekata match wenne
        # nathi nisa "keep/mute" ahanne nathuwa direct aluth audio ekak ahanawa)
        data["replace_flow"] = "video"
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🎥 Which platform is the new background video from?",
            reply_markup=InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("📌 Pinterest", callback_data="bgvid_pinterest"),
                    InlineKeyboardButton("🎵 TikTok", callback_data="bgvid_tiktok"),
                ],
                [
                    InlineKeyboardButton("📱 Upload from phone", callback_data="bgvid_upload"),
                ],
            ]),
        )
        data["bg_video_prompt_msg_id"] = sent.message_id
        return ASK_BG_VIDEO_PLATFORM

    if action == "adj_replace_audio":
        # "Re-edit" karapu passe witharak penena button eka - video eka
        # ehemama thiyaganna, audio eka witharak wenas karanawa
        data["replace_flow"] = "audio"
        return await _ask_new_audio_source(query.message.chat_id, context)

    if action == "adj_convert_photo_video":
        # background photo eka (dan tibba) video ekak vidihata convert
        # karanawa - music ekak (upload/TikTok link) ho "skip" (silent,
        # preset duration ekak) ahagena _finish_photo_video_flow() ekata yanawa.
        # e passe bg_kind="video" wena nisa Scrolling Watermark/Background
        # Effects buttons dan auto-widiyata penei (has_bg_video check eka balanna).
        data["photo_video_flow"] = True
        return await _ask_new_audio_source(query.message.chat_id, context, allow_skip=True)

    if action == "adj_watermark_menu":
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=_watermark_menu_text(data),
            parse_mode="Markdown",
            reply_markup=_watermark_menu_keyboard(data),
        )
        data["watermark_menu_msg_id"] = sent.message_id
        return WATERMARK_MENU

    if action == "adj_logo_change":
        # "Add logo" (naththam) unath "Change logo" (dan logo ekak tibba nam)
        # unath - dekamatama methanatama enawa, sub-menu ekak evala state eka
        # wenas karanawa (photo/text/last-logo/remove/cancel options)
        has_last_logo = bool(data.get("last_settings", {}).get("logo"))
        has_current_logo = bool(data.get("logo_kind"))
        rows = [[
            InlineKeyboardButton("📤 Upload PNG", callback_data="logo_choice_photo"),
            InlineKeyboardButton("✏️ Text logo", callback_data="logo_choice_text"),
        ]]
        if has_last_logo:
            rows.append([InlineKeyboardButton("✨ Use last logo", callback_data="logo_choice_last")])
        if has_current_logo:
            rows.append([InlineKeyboardButton("🗑 Remove logo", callback_data="logo_choice_remove")])
        rows.append([InlineKeyboardButton("❌ Cancel", callback_data="logo_choice_cancel")])
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🏷 How do you want to add your logo/watermark?",
            reply_markup=InlineKeyboardMarkup(rows),
        )
        data["logo_prompt_msg_id"] = sent.message_id
        return CHOOSE_LOGO_TYPE

    if action == "adj_logo_remove":
        data["logo_kind"] = None
        data["logo_value"] = None
        await render_preview(query, context)
        return ADJUSTING

    browser = context.application.bot_data["browser"]
    bg_image_b64 = data.get("bg_image_b64")
    canvas_width = data.get("bg_width") or IMG_SIZE
    canvas_height = data.get("bg_height") or IMG_SIZE

    if action == "adj_done":
        # last used settings tika persist karanna save karanawa (bot restart unath thiyenna).
        # background photo eka ekama save karanne nehe (post ekakata specific), eth
        # overlay/blur/text-position values tika save karanawa - passe photo ekak
        # upload kaloth "use last settings" eken methanin restore wenna
        prev_last = data.get("last_settings", {})
        data["last_settings"] = {
            "font_size": data["font_size"],
            "emoji_size": data["emoji_size"],
            "color": data["color"],
            "font_weight": data.get("font_weight", FONT_WEIGHT_DEFAULT),
            "italic": data.get("italic", ITALIC_DEFAULT),
            "align": data.get("align", ALIGN_DEFAULT),
            "overlay_opacity": (
                data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT) if bg_image_b64
                else prev_last.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT)
            ),
            "bg_blur": (
                data.get("bg_blur", BLUR_DEFAULT) if bg_image_b64
                else prev_last.get("bg_blur", BLUR_DEFAULT)
            ),
            "blur_type": (
                data.get("blur_type", BLUR_TYPE_DEFAULT) if bg_image_b64
                else prev_last.get("blur_type", BLUR_TYPE_DEFAULT)
            ),
            "chromatic_aberration": (
                data.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT) if (bg_image_b64 or data.get("bg_video_path"))
                else prev_last.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT)
            ),
            "chromatic_shift": (
                data.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT) if (bg_image_b64 or data.get("bg_video_path"))
                else prev_last.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT)
            ),
            "vhs_effect": (
                data.get("vhs_effect", VHS_EFFECT_DEFAULT) if (bg_image_b64 or data.get("bg_video_path"))
                else prev_last.get("vhs_effect", VHS_EFFECT_DEFAULT)
            ),
            "vhs_strength": (
                data.get("vhs_strength", VHS_STRENGTH_DEFAULT) if (bg_image_b64 or data.get("bg_video_path"))
                else prev_last.get("vhs_strength", VHS_STRENGTH_DEFAULT)
            ),
            "intro_black_seconds": (
                data.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT) if data.get("bg_video_path")
                else prev_last.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT)
            ),
            "text_offset_y": (
                data.get("text_offset_y", TEXT_OFFSET_DEFAULT) if bg_image_b64
                else prev_last.get("text_offset_y", TEXT_OFFSET_DEFAULT)
            ),
            "header_font_size": data.get("header_font_size", HEADER_FONT_SIZE_DEFAULT),
            "header_color": data.get("header_color", HEADER_COLOR_DEFAULT),
            "header_bold": data.get("header_bold", HEADER_BOLD_DEFAULT),
            "header_gap_top": data.get("header_gap_top", HEADER_GAP_TOP_DEFAULT),
            "header_gap_bottom": data.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT),
            "highlight_font_scale": data.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT),
            "highlight_bold": data.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT),
            "highlight_italic": data.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT),
            "stroke_width": data.get("stroke_width", STROKE_WIDTH_DEFAULT),
            "stroke_color": data.get("stroke_color", STROKE_COLOR_DEFAULT),
            # logo eka - overlay/blur wagema nemei, meka bg photo ekata depend
            # wenne na, ithin literally "last time use kala eka" methanin save
            # wenawa (logo ekak use karala nathnam, "no logo" ekamai save wenne)
            "logo": (
                {
                    "kind": data["logo_kind"],
                    "value": data["logo_value"],
                    "scale": data.get("logo_scale", LOGO_SCALE_DEFAULT),
                    "offset_bottom": data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT),
                }
                if data.get("logo_kind") else None
            ),
            # scrolling watermark eka - logo eka wagema, "last time use kala eka"
            # methanin save wenawa (aluth post ekaka default vidihata ithuru wenna)
            "watermark": (
                {
                    "kind": data.get("watermark_kind"),
                    "image_b64": data.get("watermark_image_b64"),
                    "opacity": data.get("watermark_opacity", WATERMARK_OPACITY_DEFAULT),
                    "direction": data.get("watermark_direction", WATERMARK_DIRECTION_DEFAULT),
                    "speed": data.get("watermark_speed", WATERMARK_SPEED_DEFAULT),
                    "scale": data.get("watermark_scale", WATERMARK_SCALE_DEFAULT),
                    "side": data.get("watermark_side", WATERMARK_SIDE_DEFAULT),
                }
                if data.get("watermark_enabled") and data.get("watermark_image_b64") else None
            ),
        }
        header_text, body_text = split_header_text(data["text"])
        header_kwargs = dict(
            header_text=header_text,
            header_font_size=data.get("header_font_size", HEADER_FONT_SIZE_DEFAULT),
            header_color=data.get("header_color", HEADER_COLOR_DEFAULT),
            header_bold=data.get("header_bold", HEADER_BOLD_DEFAULT),
            header_gap_top=data.get("header_gap_top", HEADER_GAP_TOP_DEFAULT),
            header_gap_bottom=data.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT),
            highlight_font_scale=data.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT),
            highlight_bold=data.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT),
            highlight_italic=data.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT),
            stroke_width=data.get("stroke_width", STROKE_WIDTH_DEFAULT),
            stroke_color=data.get("stroke_color", STROKE_COLOR_DEFAULT),
        )
        is_video_bg = data.get("bg_kind") == "video" and bool(data.get("bg_video_path"))
        status_msg = None
        if is_video_bg:
            status_msg = await context.bot.send_message(
                chat_id=query.message.chat_id,
                text="⏳ Rendering your video, this can take a little while... (0%)",
            )

        # ffmpeg render eka wenakota status_msg eka live % ekak dakinna edit
        # karanawa - edit_text ekak fail unath (rate limit / "not modified" etc)
        # render eka continue wenna one, ehema nisa methanin swallow karanawa
        async def _report_render_progress(pct: int):
            if status_msg is None:
                return
            try:
                await status_msg.edit_text(f"⏳ Rendering your video... {pct}%")
            except Exception:
                pass

        fb_pending_path = None   # design eka save unoth, Facebook post step ekata pass karana temp file path eka
        try:
            if is_video_bg:
                # background video ekata compose karanna one - text/emoji/logo eka
                # thani transparent PNG ekak vidihata (background/blur ekak nathuwa,
                # eeka pahalin ffmpeg eken venama apply karanawa) generate karagannawa
                overlay_buf = await generate_image(
                    browser, body_text, data["emojis"], data["font_size"], data["emoji_size"], data["color"],
                    transparent=True,
                    font_weight=data.get("font_weight", FONT_WEIGHT_DEFAULT),
                    italic=data.get("italic", ITALIC_DEFAULT),
                    align=data.get("align", ALIGN_DEFAULT),
                    canvas_width=canvas_width,
                    canvas_height=canvas_height,
                    bg_image_b64=None,
                    overlay_opacity=0.0,
                    text_offset_y=data.get("text_offset_y", TEXT_OFFSET_DEFAULT),
                    blur_px=0,
                    logo_kind=data.get("logo_kind"),
                    logo_value=data.get("logo_value"),
                    logo_scale=data.get("logo_scale", LOGO_SCALE_DEFAULT),
                    logo_offset_bottom=data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT),
                    **header_kwargs,
                )
                watermark_enabled = bool(data.get("watermark_enabled") and data.get("watermark_image_b64"))
                final_video_path = await compose_video_background(
                    data["bg_video_path"],
                    overlay_buf.getvalue(),
                    blur_type=data.get("blur_type", BLUR_TYPE_DEFAULT),
                    blur_px=data.get("bg_blur", BLUR_DEFAULT),
                    overlay_opacity=data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT),
                    duration_seconds=data.get("bg_video_duration", BG_VIDEO_MAX_SECONDS),
                    progress_cb=_report_render_progress,
                    audio_path=data.get("bg_audio_path"),
                    audio_mode=data.get("bg_audio_mode") or "keep",
                    audio_fit=data.get("bg_audio_fit") or "trim_audio",
                    watermark_png_bytes=(
                        base64.b64decode(data["watermark_image_b64"]) if watermark_enabled else None
                    ),
                    watermark_opacity=data.get("watermark_opacity", WATERMARK_OPACITY_DEFAULT),
                    watermark_scale=data.get("watermark_scale", WATERMARK_SCALE_DEFAULT),
                    watermark_direction=data.get("watermark_direction", WATERMARK_DIRECTION_DEFAULT),
                    watermark_speed=data.get("watermark_speed", WATERMARK_SPEED_DEFAULT),
                    watermark_side=data.get("watermark_side", WATERMARK_SIDE_DEFAULT),
                    chromatic_aberration=data.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT),
                    chromatic_shift=data.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT),
                    vhs_effect=data.get("vhs_effect", VHS_EFFECT_DEFAULT),
                    vhs_strength=data.get("vhs_strength", VHS_STRENGTH_DEFAULT),
                    intro_black_seconds=data.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT),
                    background_is_static_image=bool(data.get("bg_video_is_photo")),
                )
                try:
                    with open(final_video_path, "rb") as f:
                        sent_output_msg = await send_with_retry(
                            context.bot.send_document,
                            chat_id=query.message.chat_id,
                            document=f,
                            filename="post.mp4",
                            # video widget ekak vidihata nemei, plain file ekak vidihata
                            # penna gannawa - Telegram eken .mp4 documents automatic
                            # widiyata video-player UI ekak dapan try karanawa (quality
                            # loss ekak nathuwath), eka methanin off karanawa
                            disable_content_type_detection=True,
                            what="final video-bg send_document",
                        )
                    # "Re-edit" click kaloth mekath delete karanna one nisa
                    # (reedit_choice_callback eka balanna) message id eka save karagannawa
                    data["last_output_msg_id"] = sent_output_msg.message_id
                    # Facebook post step ekata pahalin one wenna puluwan nisa, delete
                    # karanna kalin wenama stable temp folder ekakata copy ekak gannawa
                    fb_pending_path = _save_fb_pending_file(True, final_video_path=final_video_path)
                finally:
                    shutil.rmtree(Path(final_video_path).parent, ignore_errors=True)
            else:
                final_buf = await generate_image(
                    browser, body_text, data["emojis"], data["font_size"], data["emoji_size"], data["color"],
                    # background photo ekak nathnam kalinma widiyatama transparent PNG ekak
                    # (user ta pahasuwen wenat background ekaka use karanna). photo ekak
                    # tibbanam eka + overlay eka ekkama "baked in" karala opaque image ekak denawa.
                    transparent=not bool(bg_image_b64),
                    font_weight=data.get("font_weight", FONT_WEIGHT_DEFAULT),
                    italic=data.get("italic", ITALIC_DEFAULT),
                    align=data.get("align", ALIGN_DEFAULT),
                    canvas_width=canvas_width,
                    canvas_height=canvas_height,
                    bg_image_b64=bg_image_b64,
                    overlay_opacity=data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT),
                    text_offset_y=data.get("text_offset_y", TEXT_OFFSET_DEFAULT),
                    blur_px=data.get("bg_blur", BLUR_DEFAULT),
                    blur_type=data.get("blur_type", BLUR_TYPE_DEFAULT),
                    logo_kind=data.get("logo_kind"),
                    logo_value=data.get("logo_value"),
                    logo_scale=data.get("logo_scale", LOGO_SCALE_DEFAULT),
                    logo_offset_bottom=data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT),
                    **header_kwargs,
                )
                sent_output_msg = await send_with_retry(
                    context.bot.send_document,
                    chat_id=query.message.chat_id,
                    document=final_buf,
                    filename="post.png",
                    what="final image send_document",
                )
                # "Re-edit" click kaloth mekath delete karanna one nisa
                # (reedit_choice_callback eka balanna) message id eka save karagannawa
                data["last_output_msg_id"] = sent_output_msg.message_id
                fb_pending_path = _save_fb_pending_file(False, final_buf=final_buf)
        except Exception as e:
            logger.exception("Final generation failed")
            if isinstance(e, subprocess.CalledProcessError) and e.stderr:
                logger.error(
                    "ffmpeg stderr (exit %s):\n%s",
                    e.returncode,
                    e.stderr.decode("utf-8", errors="ignore"),
                )
            await query.message.reply_text(f"⚠️ Something went wrong while generating the {'video' if is_video_bg else 'image'}: {e}")
        finally:
            # bg_video_path/bg_audio_path methanin ain karanne na - "Re-edit"
            # click kaloth ayeth methama video eka use karanna one nisa, e
            # cleanup eka "Continue" (reedit_no) click karapu welavatama
            # dala thiyenawa (reedit_choice_callback eka balanna).
            if status_msg:
                try:
                    await status_msg.delete()
                except Exception:
                    pass

        await query.edit_message_reply_markup(reply_markup=None)

        # user_data eka methanin clear karanne na (kalinma widiyata) - "Re-edit"
        # option eka daanna one nisa, adjustment settings tika (font/color/blur/
        # effects/bg_video_path...) ehemama thiyaganna one, user "Re-edit"
        # click kaloth eka data eken ma ADJUSTING ekata ayeth yanna puluwan
        # widiyata. Facebook post ekata one wena "fb_pending_*" data witharak
        # methanata ithuru karagannawa - "Continue" click kaloth witharai (passe
        # reedit_choice_callback eke "no" branch eke) real cleanup + clear eka wenne.
        if fb_pending_path:
            data["fb_pending_file"] = fb_pending_path
            data["fb_pending_is_video"] = is_video_bg

        # background eka dan wenmama video ekak/photo ekak vidihata iwara una nam,
        # "video ekakuth ona da" kiyala aye ahanna one na (plain background ekakadi
        # witharai e option eka wadagath wenne) - e widiyata Facebook post step eka
        # iwara unu passe ekpalatama iwara karanna one da, nathnam video download eka
        # ahanna one da kiyana eka methanin flag ekakin save karagannawa
        data["fb_after_video_offer"] = not (is_video_bg or bg_image_b64)

        reedit_prompt_msg = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🎬 *Export ekak iwara!* Ayeth text/effects wenas karanna one da, nathnam ihalata yanna da?",
            parse_mode="Markdown",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔁 Re-edit", callback_data="reedit_yes")],
                [InlineKeyboardButton("➡️ Continue", callback_data="reedit_no")],
            ]),
        )
        # "Re-edit" click kaloth me prompt eka mekama delete karanna one nisa
        # (reedit_choice_callback eka balanna) message id eka save karagannawa
        data["reedit_prompt_msg_id"] = reedit_prompt_msg.message_id
        return ASK_REEDIT

    if action == "adj_font_inc":
        data["font_size"] = min(FONT_SIZE_MAX, data["font_size"] + FONT_SIZE_STEP)
    elif action == "adj_font_dec":
        data["font_size"] = max(FONT_SIZE_MIN, data["font_size"] - FONT_SIZE_STEP)
    elif action == "adj_font_reset":
        data["font_size"] = FONT_SIZE_DEFAULT
    elif action == "adj_emoji_inc":
        data["emoji_size"] = min(EMOJI_SIZE_MAX, data["emoji_size"] + EMOJI_SIZE_STEP)
    elif action == "adj_emoji_dec":
        data["emoji_size"] = max(EMOJI_SIZE_MIN, data["emoji_size"] - EMOJI_SIZE_STEP)
    elif action == "adj_emoji_reset":
        data["emoji_size"] = EMOJI_SIZE_DEFAULT
    elif action == "adj_weight_inc":
        data["font_weight"] = min(FONT_WEIGHT_MAX, data.get("font_weight", FONT_WEIGHT_DEFAULT) + FONT_WEIGHT_STEP)
    elif action == "adj_weight_dec":
        data["font_weight"] = max(FONT_WEIGHT_MIN, data.get("font_weight", FONT_WEIGHT_DEFAULT) - FONT_WEIGHT_STEP)
    elif action == "adj_weight_reset":
        data["font_weight"] = FONT_WEIGHT_DEFAULT
    elif action == "adj_italic_toggle":
        data["italic"] = not data.get("italic", ITALIC_DEFAULT)
    elif action in ("adj_align_left", "adj_align_center", "adj_align_right"):
        data["align"] = action.replace("adj_align_", "")
    elif action == "adj_overlay_inc":
        data["overlay_opacity"] = round(
            min(OVERLAY_OPACITY_MAX, data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT) + OVERLAY_OPACITY_STEP), 2
        )
    elif action == "adj_overlay_dec":
        data["overlay_opacity"] = round(
            max(OVERLAY_OPACITY_MIN, data.get("overlay_opacity", OVERLAY_OPACITY_DEFAULT) - OVERLAY_OPACITY_STEP), 2
        )
    elif action == "adj_overlay_reset":
        data["overlay_opacity"] = OVERLAY_OPACITY_DEFAULT
    elif action == "adj_blur_inc":
        data["bg_blur"] = min(BLUR_MAX, data.get("bg_blur", BLUR_DEFAULT) + BLUR_STEP)
    elif action == "adj_blur_dec":
        data["bg_blur"] = max(BLUR_MIN, data.get("bg_blur", BLUR_DEFAULT) - BLUR_STEP)
    elif action == "adj_blur_reset":
        data["bg_blur"] = BLUR_DEFAULT
    elif action == "adj_blur_type_toggle":
        data["blur_type"] = "motion" if data.get("blur_type", BLUR_TYPE_DEFAULT) == "gaussian" else "gaussian"
    elif action == "adj_chromatic_toggle":
        data["chromatic_aberration"] = not data.get("chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT)
    elif action == "adj_chromatic_inc":
        data["chromatic_shift"] = min(
            CHROMATIC_SHIFT_MAX, data.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT) + CHROMATIC_SHIFT_STEP
        )
    elif action == "adj_chromatic_dec":
        data["chromatic_shift"] = max(
            CHROMATIC_SHIFT_MIN, data.get("chromatic_shift", CHROMATIC_SHIFT_DEFAULT) - CHROMATIC_SHIFT_STEP
        )
    elif action == "adj_vhs_toggle":
        data["vhs_effect"] = not data.get("vhs_effect", VHS_EFFECT_DEFAULT)
    elif action == "adj_vhs_inc":
        data["vhs_strength"] = min(
            VHS_STRENGTH_MAX, data.get("vhs_strength", VHS_STRENGTH_DEFAULT) + VHS_STRENGTH_STEP
        )
    elif action == "adj_vhs_dec":
        data["vhs_strength"] = max(
            VHS_STRENGTH_MIN, data.get("vhs_strength", VHS_STRENGTH_DEFAULT) - VHS_STRENGTH_STEP
        )
    elif action == "adj_intro_inc":
        data["intro_black_seconds"] = round(min(
            INTRO_BLACK_SECONDS_MAX, data.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT) + INTRO_BLACK_SECONDS_STEP
        ), 1)
    elif action == "adj_intro_dec":
        data["intro_black_seconds"] = round(max(
            INTRO_BLACK_SECONDS_MIN, data.get("intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT) - INTRO_BLACK_SECONDS_STEP
        ), 1)
    elif action == "adj_intro_reset":
        data["intro_black_seconds"] = INTRO_BLACK_SECONDS_DEFAULT
    elif action == "adj_text_up":
        data["text_offset_y"] = max(
            TEXT_OFFSET_MIN, data.get("text_offset_y", TEXT_OFFSET_DEFAULT) - TEXT_OFFSET_STEP
        )
    elif action == "adj_text_down":
        data["text_offset_y"] = min(
            TEXT_OFFSET_MAX, data.get("text_offset_y", TEXT_OFFSET_DEFAULT) + TEXT_OFFSET_STEP
        )
    elif action == "adj_text_recenter":
        data["text_offset_y"] = TEXT_OFFSET_DEFAULT
    elif action == "adj_logo_inc":
        data["logo_scale"] = min(LOGO_SCALE_MAX, data.get("logo_scale", LOGO_SCALE_DEFAULT) + LOGO_SCALE_STEP)
    elif action == "adj_logo_dec":
        data["logo_scale"] = max(LOGO_SCALE_MIN, data.get("logo_scale", LOGO_SCALE_DEFAULT) - LOGO_SCALE_STEP)
    elif action == "adj_logo_up":
        data["logo_offset_bottom"] = min(
            LOGO_OFFSET_MAX, data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT) + LOGO_OFFSET_STEP
        )
    elif action == "adj_logo_down":
        data["logo_offset_bottom"] = max(
            LOGO_OFFSET_MIN, data.get("logo_offset_bottom", LOGO_OFFSET_DEFAULT) - LOGO_OFFSET_STEP
        )
    elif action == "adj_text_menu":
        data["adjust_menu"] = "text"
    elif action == "adj_text_back":
        data["adjust_menu"] = "main"
    elif action == "adj_emoji_menu":
        data["adjust_menu"] = "emoji"
    elif action == "adj_emoji_back":
        data["adjust_menu"] = "main"
    elif action == "adj_effects_menu":
        data["adjust_menu"] = "effects"
    elif action == "adj_effects_back":
        data["adjust_menu"] = "main"
    elif action == "adj_logo_menu":
        data["adjust_menu"] = "logo"
    elif action == "adj_logo_back":
        data["adjust_menu"] = "main"
    elif action == "adj_header_menu":
        # header ekak thiyena post ekakata witharai me button eka penenne, ithin
        # methanata ena eka thamai "Header" sub-menu ekata switch wenna ona kiyana signal eka
        data["adjust_menu"] = "header"
    elif action == "adj_header_back":
        data["adjust_menu"] = "main"
    elif action == "adj_header_font_inc":
        data["header_font_size"] = min(
            HEADER_FONT_SIZE_MAX, data.get("header_font_size", HEADER_FONT_SIZE_DEFAULT) + HEADER_FONT_SIZE_STEP
        )
    elif action == "adj_header_font_dec":
        data["header_font_size"] = max(
            HEADER_FONT_SIZE_MIN, data.get("header_font_size", HEADER_FONT_SIZE_DEFAULT) - HEADER_FONT_SIZE_STEP
        )
    elif action == "adj_header_bold_toggle":
        data["header_bold"] = not data.get("header_bold", HEADER_BOLD_DEFAULT)
    elif action == "adj_header_gap_top_inc":
        data["header_gap_top"] = min(
            HEADER_GAP_TOP_MAX, data.get("header_gap_top", HEADER_GAP_TOP_DEFAULT) + HEADER_GAP_TOP_STEP
        )
    elif action == "adj_header_gap_top_dec":
        data["header_gap_top"] = max(
            HEADER_GAP_TOP_MIN, data.get("header_gap_top", HEADER_GAP_TOP_DEFAULT) - HEADER_GAP_TOP_STEP
        )
    elif action == "adj_header_gap_bottom_inc":
        data["header_gap_bottom"] = min(
            HEADER_GAP_BOTTOM_MAX, data.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT) + HEADER_GAP_BOTTOM_STEP
        )
    elif action == "adj_header_gap_bottom_dec":
        data["header_gap_bottom"] = max(
            HEADER_GAP_BOTTOM_MIN, data.get("header_gap_bottom", HEADER_GAP_BOTTOM_DEFAULT) - HEADER_GAP_BOTTOM_STEP
        )
    elif action.startswith("adj_hdrcolor_"):
        color_key = action[len("adj_hdrcolor_"):]
        data["header_color"] = COLORS.get(color_key, COLORS["white"])
    elif action == "adj_stroke_inc":
        data["stroke_width"] = round(
            min(STROKE_WIDTH_MAX, data.get("stroke_width", STROKE_WIDTH_DEFAULT) + STROKE_WIDTH_STEP), 1
        )
    elif action == "adj_stroke_dec":
        data["stroke_width"] = round(
            max(STROKE_WIDTH_MIN, data.get("stroke_width", STROKE_WIDTH_DEFAULT) - STROKE_WIDTH_STEP), 1
        )
    elif action.startswith("adj_strokecolor_"):
        color_key = action[len("adj_strokecolor_"):]
        data["stroke_color"] = COLORS.get(color_key, COLORS["black"])
    elif action == "adj_highlight_menu":
        # text eke ^...^ block ekak thibba nam witharai me button eka penenne,
        # ithin methanata ena eka "Highlight" sub-menu ekata switch wenna ona kiyana signal eka
        data["adjust_menu"] = "highlight"
    elif action == "adj_highlight_back":
        data["adjust_menu"] = "main"
    elif action == "adj_highlight_size_inc":
        data["highlight_font_scale"] = round(min(
            HIGHLIGHT_FONT_SCALE_MAX, data.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT) + HIGHLIGHT_FONT_SCALE_STEP
        ), 1)
    elif action == "adj_highlight_size_dec":
        data["highlight_font_scale"] = round(max(
            HIGHLIGHT_FONT_SCALE_MIN, data.get("highlight_font_scale", HIGHLIGHT_FONT_SCALE_DEFAULT) - HIGHLIGHT_FONT_SCALE_STEP
        ), 1)
    elif action == "adj_highlight_bold_toggle":
        data["highlight_bold"] = not data.get("highlight_bold", HIGHLIGHT_BOLD_DEFAULT)
    elif action == "adj_highlight_italic_toggle":
        data["highlight_italic"] = not data.get("highlight_italic", HIGHLIGHT_ITALIC_DEFAULT)

    await render_preview(query, context)

    return ADJUSTING


async def _finish_up(chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    """Hama path ekakama (video ekak download unath, na unath) end wenne
    methanin - success message eka evala, user_data clear karanawa. Aluth
    post ekak patan gannna one nam, thani "▶️ Start" button ekak witharai
    danawa (START_MESSAGE full instructions ekama hama welawakama spam
    karanne nathuwa - button click kaloth witharai eka pennanne)."""
    await context.bot.send_message(chat_id=chat_id, text="✅ All done! Your post is ready.")
    await context.bot.send_message(
        chat_id=chat_id,
        text="Aluth post ekak hadanna one nam 👇",
        reply_markup=InlineKeyboardMarkup(
            [[InlineKeyboardButton("▶️ Start", callback_data="start_new_post")]]
        ),
    )

    last_settings = context.user_data.get("last_settings")
    templates = context.user_data.get("templates")
    fb_pages = context.user_data.get("fb_pages")
    scheduled_posts = context.user_data.get("scheduled_posts")
    context.user_data.clear()
    if last_settings:
        context.user_data["last_settings"] = last_settings
    if templates:
        context.user_data["templates"] = templates
    if fb_pages:
        context.user_data["fb_pages"] = fb_pages
    if scheduled_posts:
        context.user_data["scheduled_posts"] = scheduled_posts


async def reedit_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Export ekata passe ahana "Re-edit / Continue" prompt ekata response eka
    methanin handle karanawa.

    - "Re-edit" (reedit_yes) unoth: user_data eka clear karanne na (data
      dan hitiyema thiyenawa - font/color/effects/bg_video_path okkoma
      thiyennema), witharai me post ekata specific-wela thibba "pending fb
      copy" eka (use karanna yanne nathi nisa) delete karala, preview eka
      ayeth render karala ADJUSTING ekatama yanawa.
    - "Continue" (reedit_no) unoth: dan witharai kalinma widiyata
      bg_video_path/bg_audio_path source temp files tika cleanup karala,
      post-specific data clear karala (last_settings/templates/fb_pages/
      fb_pending_* witharak ithuru karagena) Facebook ask step ekata yanawa.
    """
    query = update.callback_query
    await query.answer()
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

    data = context.user_data
    action = query.data

    if action == "reedit_yes":
        # me export eka venuwen witharak hadapu "pending fb copy" eka use
        # karanne nathnam waedi wenne na, disk eka ithuru karanna delete karanawa
        _cleanup_fb_pending(data)
        data.pop("fb_after_video_offer", None)

        # output file eka ("post.mp4"/"post.png") ha "🎬 Export ekak iwara!"
        # prompt eka - deka ma chat eken delete karanawa, preview eka (adjustment
        # buttons ekkama) witharak ithuru wenna
        chat_id = query.message.chat_id
        output_msg_id = data.pop("last_output_msg_id", None)
        if output_msg_id:
            try:
                await context.bot.delete_message(chat_id=chat_id, message_id=output_msg_id)
            except Exception:
                pass
        prompt_msg_id = data.pop("reedit_prompt_msg_id", None)
        if prompt_msg_id:
            try:
                await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
            except Exception:
                pass

        # dan idan "Re-edit" flow eka - methanin witharak "Replace Video"/
        # "Replace Audio" buttons main menu ekedi penenawa (size_keyboard eka balanna)
        data["is_reedit"] = True

        ok = await render_preview(query, context)
        return ADJUSTING if ok else ConversationHandler.END

    # "Continue" - dan witharai bg video/audio source cleanup + post-specific
    # data clear karala, kalinma widiyata Facebook ask step ekata yanawa
    _cleanup_bg_video(data)
    last_settings = data.get("last_settings")
    templates = data.get("templates")
    fb_pages = data.get("fb_pages")
    scheduled_posts = data.get("scheduled_posts")
    fb_pending_file = data.get("fb_pending_file")
    fb_pending_is_video = data.get("fb_pending_is_video")
    fb_after_video_offer = data.get("fb_after_video_offer", False)
    context.user_data.clear()
    if last_settings:
        context.user_data["last_settings"] = last_settings
    if templates:
        context.user_data["templates"] = templates
    if fb_pages:
        context.user_data["fb_pages"] = fb_pages
    if scheduled_posts:
        context.user_data["scheduled_posts"] = scheduled_posts
    if fb_pending_file:
        context.user_data["fb_pending_file"] = fb_pending_file
        context.user_data["fb_pending_is_video"] = fb_pending_is_video
    context.user_data["fb_after_video_offer"] = fb_after_video_offer

    return await _ask_facebook_post(query.message.chat_id, context)


# ---------------- FACEBOOK PAGE DIRECT POST ----------------
# post eka (image/video) generate karala Telegram ekata evapu passe, user ta
# "/pages" command eken kalinma save kara thibba Page(s) walata (Graph API
# eken) direct widiyata upload karanna puluwan option ekak methanin denawa.
# context.user_data["fb_pages"] dict eka (persistence file eka ekka) save
# wenawa, ithin ekvarak add kara gattama passe post gananakatama reuse
# karanna puluwan.

def _cleanup_fb_pending(data: dict):
    """fb_pending_file eka point karana temp folder eka (thiyenawa nam) disk
    eken ain karanawa - post kara ivara unath, "No" kiyoth udath methanin
    call karanawa, ithuru temp files server eke ithiri wenna denne nathuwa."""
    path = data.pop("fb_pending_file", None)
    data.pop("fb_pending_is_video", None)
    if path:
        try:
            shutil.rmtree(Path(path).parent, ignore_errors=True)
        except Exception:
            pass


def _save_fb_pending_file(is_video: bool, final_buf: BytesIO | None = None, final_video_path: str | None = None) -> str:
    """Design eka telegram ekata evapu passe, Facebook post ekata thawath
    method message pahakata pahalin use karanna one nisa, stable temp folder
    ekakata save karagannawa (image eke nam memory buffer eka witharak
    thibbe, video eke nam original file eka methanata pahalin delete
    wenawa ithin copy ekak gannawa)."""
    tmp_dir = Path(tempfile.mkdtemp(prefix="fbpost_"))
    if is_video:
        dest = tmp_dir / "post.mp4"
        shutil.copy(final_video_path, dest)
    else:
        dest = tmp_dir / "post.png"
        with open(dest, "wb") as f:
            f.write(final_buf.getvalue())
    return str(dest)


async def _continue_after_fb(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Facebook post step eka (post kalath, skip kalath) iwara una passe,
    kalinma thibba flow ekatama continue karanawa - background eka
    video/photo ekak nam ekpalatama iwara karanawa, nathnam "video ekakuth
    ona da" kiyala ahanawa (background eka plain color ekak unoth witharai)."""
    data = context.user_data
    ask_video = data.pop("fb_after_video_offer", False)
    if not ask_video:
        await _finish_up(chat_id, context)
        return ConversationHandler.END

    await context.bot.send_message(
        chat_id=chat_id,
        text="🎥 Want to grab a video too? Choose where from:",
        reply_markup=InlineKeyboardMarkup([
            [
                InlineKeyboardButton("📌 Pinterest", callback_data="vid_pinterest"),
                InlineKeyboardButton("🎵 TikTok", callback_data="vid_tiktok"),
            ],
            [InlineKeyboardButton("❌ No", callback_data="vid_no")],
        ]),
    )
    return ASK_VIDEO_PLATFORM


async def _ask_facebook_post(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Design eka generate karala Telegram ekata evapu passe, "Facebook Page
    ekatama post karanna da" kiyala ahanawa. "/pages" command eken save
    karapu pages tika thiyenawa nam, ekeka ekakama button ekak vidihata
    pennanawa (thoraganna witharai), naththam okkoma pages walata ekpaharatama
    post karanna "සියලුම Pages" button ekakuth."""
    data = context.user_data
    if not data.get("fb_pending_file"):
        # kohomahari generate eka fail unoth (file ekak nathi nisa) me step eka witharak skip karanawa
        return await _continue_after_fb(chat_id, context)

    pages = data.get("fb_pages") or {}
    rows = []
    for pid, info in pages.items():
        label = info.get("label") or pid
        short = label if len(label) <= 28 else label[:28] + "…"
        rows.append([InlineKeyboardButton(f"📄 {short}", callback_data=f"fb_page_{pid}")])
    if len(pages) > 1:
        rows.append([InlineKeyboardButton("📢 සියලුම Pages වලටම Post කරන්න", callback_data="fb_page_all")])
    if not pages:
        rows.append([InlineKeyboardButton("➕ Page එකක් Add කරන්න", callback_data="fb_goto_pages")])
    rows.append([InlineKeyboardButton("❌ No, Skip", callback_data="fb_post_no")])

    text = "📤 *මේ post එක Facebook Page එකකට direct upload කරන්නද?*"
    text += (
        "\n\nකැමති Page එකක් (හෝ කීපයක්) තෝරන්න 👇"
        if pages else
        "\n\nඔයාට තවම Page එකක්වත් add කරලා නෑ - පහළින් එකක් add කරගන්න."
    )

    await context.bot.send_message(
        chat_id=chat_id,
        text=text,
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup(rows),
    )
    return ASK_FB_POST


async def fb_post_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = context.user_data
    action = query.data
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

    if action == "fb_post_no":
        _cleanup_fb_pending(data)
        return await _continue_after_fb(query.message.chat_id, context)

    if action == "fb_goto_pages":
        # methanata pahalin file eka pending wela thiyenna ona nisa, "/pages"
        # ekedin add kara ivara welata post ekama methanin continue karanna
        # bari nisa (aluth post ekakadi "Facebook post karanna da" kiyala aye
        # ahanawa), skip karala pages menu eka witharak pennanawa
        await send_pages_menu(query.message.chat_id, context)
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="ℹ️ Page එක add කරගත්තට පස්සේ, මේ design එකටම Facebook post option එක "
            "ආයෙත් ගන්න ඕන නම් Adjust screen එකේ \"✅ Done\" click කරන්න.",
        )
        _cleanup_fb_pending(data)
        return await _continue_after_fb(query.message.chat_id, context)

    pages = data.get("fb_pages") or {}

    if action == "fb_page_all":
        targets = [{"page_id": pid, **info} for pid, info in pages.items()]
    elif action.startswith("fb_page_"):
        pid = action[len("fb_page_"):]
        info = pages.get(pid)
        if not info:
            await context.bot.send_message(
                chat_id=query.message.chat_id,
                text="⚠️ Me Page එක තව නෑ (delete වෙලා වෙන්න පුළුවන්), /pages ඇතුළේ check කරන්න.",
            )
            _cleanup_fb_pending(data)
            return await _continue_after_fb(query.message.chat_id, context)
        targets = [{"page_id": pid, **info}]
    else:
        targets = []

    if not targets:
        _cleanup_fb_pending(data)
        return await _continue_after_fb(query.message.chat_id, context)

    data["fb_pending_targets"] = targets
    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text="📝 *Caption + Hashtags* එක type කරලා send කරන්න "
        "(caption එකේම ඕන තැනක hashtags දාන්න පුළුවන්):",
        parse_mode="Markdown",
    )
    return WAITING_FB_CAPTION


async def post_photo_to_facebook_page(page_id: str, token: str, file_path: str, caption: str) -> tuple[bool, str]:
    """Graph API /{page-id}/photos ekata multipart POST ekak - image eka +
    caption eka + access_token eka ekathuwa yawanawa. Success unoth new
    post/photo id eka, nathnam Facebook eken awa error message eka return karanawa."""
    url = f"{FACEBOOK_GRAPH_BASE}/{page_id}/photos"
    try:
        async with httpx.AsyncClient(timeout=FACEBOOK_UPLOAD_TIMEOUT) as client:
            with open(file_path, "rb") as f:
                resp = await client.post(
                    url,
                    data={"caption": caption, "access_token": token},
                    files={"source": ("post.png", f, "image/png")},
                )
        payload = resp.json()
        if resp.status_code == 200 and "id" in payload:
            return True, payload["id"]
        err = (payload.get("error") or {}).get("message", str(payload))
        return False, err
    except Exception as e:
        return False, str(e)


async def post_video_to_facebook_page(page_id: str, token: str, file_path: str, caption: str) -> tuple[bool, str]:
    """Graph API /{page-id}/videos ekata multipart POST ekak - meka simple
    (non-chunked) upload ekak, ithin loku files walata (500MB+) Facebook eken
    "resumable upload" one karanna puluwan, eth me bot eke bg-video length
    eka thanikama BG_VIDEO_MAX_SECONDS ekata seemaa wela thiyena nisa
    danata thiyena size ekata methanin danna requesst eka hodatama sufficient."""
    url = f"{FACEBOOK_GRAPH_BASE}/{page_id}/videos"
    try:
        async with httpx.AsyncClient(timeout=FACEBOOK_UPLOAD_TIMEOUT) as client:
            with open(file_path, "rb") as f:
                resp = await client.post(
                    url,
                    data={"description": caption, "access_token": token},
                    files={"source": ("post.mp4", f, "video/mp4")},
                )
        payload = resp.json()
        if resp.status_code == 200 and ("id" in payload or "video_id" in payload):
            return True, payload.get("id") or payload.get("video_id")
        err = (payload.get("error") or {}).get("message", str(payload))
        return False, err
    except Exception as e:
        return False, str(e)


async def receive_fb_caption(update: Update, context: ContextTypes.DEFAULT_TYPE):
    data = context.user_data
    caption = update.message.text or ""
    file_path = data.get("fb_pending_file")
    targets = data.get("fb_pending_targets") or []

    if not file_path or not Path(file_path).exists():
        await update.message.reply_text("⚠️ Post file එක තව තියෙන්නේ නෑ, Facebook post එක skip කරනවා.")
        _cleanup_fb_pending(data)
        return await _continue_after_fb(update.message.chat_id, context)

    if not targets:
        await update.message.reply_text("⚠️ Post කරන්න Page එකක් තෝරලා තිබුණේ නෑ, Facebook post එක skip කරනවා.")
        _cleanup_fb_pending(data)
        return await _continue_after_fb(update.message.chat_id, context)

    data["fb_pending_caption"] = caption
    await update.message.reply_text(
        "🚀 *දැන් මොකද කරන්නේ?*",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("📤 දැන්ම Post කරන්න", callback_data="fb_when_now")],
            [InlineKeyboardButton("🕒 Schedule කරන්න", callback_data="fb_when_schedule")],
            [InlineKeyboardButton("📝 Draft විදිහට Save කරන්න", callback_data="fb_when_draft")],
        ]),
    )
    return ASK_FB_SCHEDULE


async def fb_schedule_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """ASK_FB_SCHEDULE state - caption/hashtags type kara ivara welata
    "දැන්ම Post කරන්න" / "Schedule කරන්න" / "Draft විදිහට Save කරන්න" button
    thunෙන් එකක් click kaloth methanin handle wenawa."""
    query = update.callback_query
    await query.answer()
    data = context.user_data
    action = query.data
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

    if action == "fb_when_now":
        targets = data.pop("fb_pending_targets", None) or []
        file_path = data.get("fb_pending_file")
        if not targets or not file_path or not Path(file_path).exists():
            await context.bot.send_message(
                chat_id=query.message.chat_id,
                text="⚠️ Post file/Page එක තව නෑ, Facebook post එක skip කරනවා.",
            )
            _cleanup_fb_pending(data)
            data.pop("fb_pending_caption", None)
            return await _continue_after_fb(query.message.chat_id, context)

        status_msg = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=f"⏳ Page {len(targets)}ක්{'' if len(targets) == 1 else ' (okkomatama)'} එකට upload කරමින්..."
            if len(targets) > 1 else "⏳ Facebook Page එකට upload කරමින්...",
        )
        return await _post_to_facebook_targets(query.message.chat_id, context, targets, status_msg)

    if action == "fb_when_draft":
        _save_pending_as_scheduled(context, query.message.chat_id, when_utc=None)
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="📝 Draft විදිහට save කළා! /schedule command එකෙන් ඕන වෙලාවක post කරන්න පුළුවන්.",
        )
        _cleanup_fb_pending(data)
        data.pop("fb_pending_caption", None)
        data.pop("fb_pending_targets", None)
        return await _continue_after_fb(query.message.chat_id, context)

    if action == "fb_when_schedule":
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=(
                "🕒 *Post එක auto-post වෙන්න ඕන දිනය සහ වේලාව* type කරලා send කරන්න "
                "(*Sri Lankan time*, 24-hour format එකෙන්):\n\n"
                f"`DD-MM-YYYY HH:MM`\n\n"
                f"උදාහරණයක්: රාත්‍රී 9.30ට කියනවා නම් — `{SCHEDULE_TIME_EXAMPLE}`\n"
                "(උදේ 7ට = 07:00, දවල් 1ට = 13:00, රෑ 11.45ට = 23:45)"
            ),
            parse_mode="Markdown",
        )
        return WAITING_SCHEDULE_TIME

    # anith monawa unath (recognize karanna bari action ekak), skip karala continue karanawa
    _cleanup_fb_pending(data)
    data.pop("fb_pending_caption", None)
    data.pop("fb_pending_targets", None)
    return await _continue_after_fb(query.message.chat_id, context)


async def receive_schedule_time(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """WAITING_SCHEDULE_TIME state - user type kala date/time text eka parse
    karala, valid + future welavak nam post eka scheduled_posts list ekata
    save karanawa."""
    when_utc = _parse_sl_time_input(update.message.text or "")
    now_utc = datetime.now(timezone.utc)

    if when_utc is None:
        await update.message.reply_text(
            f"⚠️ Format එක වැරදියි. `DD-MM-YYYY HH:MM` විදිහට (24-hour, Sri Lankan time) "
            f"type කරන්න, උදා: `{SCHEDULE_TIME_EXAMPLE}` විදිහට, හෝ /cancel කරන්න.",
            parse_mode="Markdown",
        )
        return WAITING_SCHEDULE_TIME

    if when_utc <= now_utc + timedelta(minutes=1):
        await update.message.reply_text(
            "⚠️ Time එක අනිවාර්යයෙන්ම මින් පස්සේ (future) එකක් වෙන්න ඕන. ආයෙත් type කරලා යවන්න, "
            "හෝ /cancel කරන්න."
        )
        return WAITING_SCHEDULE_TIME

    _save_pending_as_scheduled(context, update.message.chat_id, when_utc)
    data = context.user_data
    _cleanup_fb_pending(data)
    data.pop("fb_pending_caption", None)
    data.pop("fb_pending_targets", None)

    await update.message.reply_text(
        f"✅ Post එක schedule කළා!\n🕒 *{_format_sl_time(when_utc)}* (Sri Lankan time)ට automatic ම "
        "Facebook එකට post වෙනවා.\n\n"
        "ℹ️ Time එක change කරන්න/delete කරන්න/දැන්ම post කරන්න ඕන නම් /schedule command එක use කරන්න.",
        parse_mode="Markdown",
    )
    return await _continue_after_fb(update.message.chat_id, context)


async def _post_to_facebook_targets(chat_id: int, context: ContextTypes.DEFAULT_TYPE, targets: list, status_msg=None) -> int:
    """targets tikata (Page ekak ho ekakata wadi ganak) post karala, results
    eka report karanawa. Kalin widiyata post fail una welavata (network error/
    token expired wage), user ta mulu flow ekama ayet repeat karanna one wela
    thibba - dan ekekma fail una Page tika witharak "🔁 Retry" button ekakin
    ayeth try karanna puluwan, ithin fail una file eka methanata pahalin
    (retry karana thuru) delete karanne nehe."""
    data = context.user_data
    file_path = data.get("fb_pending_file")
    is_video = data.get("fb_pending_is_video", False)
    caption = data.get("fb_pending_caption", "")

    results = []
    for target in targets:
        page_id = target.get("page_id")
        token = target.get("token")
        label = target.get("label") or page_id
        if is_video:
            ok, result = await post_video_to_facebook_page(page_id, token, file_path, caption)
        else:
            ok, result = await post_photo_to_facebook_page(page_id, token, file_path, caption)
        results.append((label, ok, result, target))

    if status_msg is not None:
        try:
            await status_msg.delete()
        except Exception:
            pass

    lines = []
    failed_targets = []
    for label, ok, result, target in results:
        if ok:
            lines.append(f"✅ {label}: post කරලා ඉවරයි (id: {result})")
        else:
            lines.append(f"⚠️ {label}: fail උනා - {result}")
            failed_targets.append(target)

    if not failed_targets:
        # okkoma success - methanata pahalin retry karanna monawat naha, ithin
        # pending file eka methanmama clean karala continue karanawa
        await context.bot.send_message(chat_id=chat_id, text="\n".join(lines))
        _cleanup_fb_pending(data)
        data.pop("fb_pending_caption", None)
        return await _continue_after_fb(chat_id, context)

    data["fb_failed_targets"] = failed_targets
    lines.append("")
    lines.append(f"⚠️ Page {len(failed_targets)}ක upload eka fail una - retry karanna da?")
    await context.bot.send_message(
        chat_id=chat_id,
        text="\n".join(lines),
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔁 Retry failed", callback_data="fb_retry_go")],
            [InlineKeyboardButton("⏭ Continue without retrying", callback_data="fb_retry_skip")],
        ]),
    )
    return ASK_FB_RETRY


async def fb_retry_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """ASK_FB_RETRY state - "🔁 Retry failed" / "⏭ Continue without retrying"
    button eka click kaloth methanin handle wenawa."""
    query = update.callback_query
    await query.answer()
    data = context.user_data
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

    if query.data == "fb_retry_skip":
        _cleanup_fb_pending(data)
        data.pop("fb_pending_caption", None)
        data.pop("fb_failed_targets", None)
        return await _continue_after_fb(query.message.chat_id, context)

    targets = data.pop("fb_failed_targets", None) or []
    file_path = data.get("fb_pending_file")
    if not targets or not file_path or not Path(file_path).exists():
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="⚠️ Retry කරන්න file එක තව නෑ, Facebook post එක skip කරනවා.",
        )
        _cleanup_fb_pending(data)
        data.pop("fb_pending_caption", None)
        return await _continue_after_fb(query.message.chat_id, context)

    status_msg = await context.bot.send_message(
        chat_id=query.message.chat_id,
        text=f"⏳ Page {len(targets)}ක් retry කරමින්..." if len(targets) > 1 else "⏳ Retry කරමින්...",
    )
    return await _post_to_facebook_targets(query.message.chat_id, context, targets, status_msg)


# ---------------- FACEBOOK POST SCHEDULING (/schedule) ----------------
# "Schedule කරන්න" / "Draft විදිහට Save කරන්න" ekak thoraganoth, post eka
# (image/video + caption + target pages) context.user_data["scheduled_posts"]
# list ekata (persistence file eka ekka save wenawa, restart unath thiyenawa)
# add karagannawa. Media file eka fb_pending_file wage temp folder ekaka
# nemei, SCHEDULED_POSTS_DIR yata dedicated permanent folder ekaka save
# karagannawa - eka post/delete wena thuru witharai ain karanne.
#
# job_queue eken (SCHEDULE_CHECK_INTERVAL_SECONDS ekakata parak) hama users
# ge scheduled_posts okkoma check karala, "when_utc" welawa pahu unu ewa
# auto-post karanawa. "when_utc" eka None nam eka "Draft" ekak - job eken
# ekakuth wenas karanne na, user ma /schedule eken "දැන්ම Post කරන්න" click
# karapu welavata witharai post wenne.

def _save_scheduled_post_file(post_id: str, is_video: bool, src_path: str) -> str:
    dest_dir = SCHEDULED_POSTS_DIR / post_id
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest = dest_dir / ("post.mp4" if is_video else "post.png")
    shutil.copy(src_path, dest)
    return str(dest)


def _delete_scheduled_post_file(entry: dict):
    path = entry.get("file_path")
    if path:
        try:
            shutil.rmtree(Path(path).parent, ignore_errors=True)
        except Exception:
            pass


def _format_sl_time(dt_utc: datetime) -> str:
    """UTC datetime ekak, Sri Lankan (Asia/Colombo) time ekata convert karala
    user ta pennana format ekata daanawa."""
    return dt_utc.astimezone(SRI_LANKA_TZ).strftime("%Y-%m-%d %H:%M")


def _parse_sl_time_input(text: str) -> datetime | None:
    """User type kala 'DD-MM-YYYY HH:MM' (24-hour, Sri Lankan time) text eka
    parse karala, UTC datetime ekak return karanawa. Invalid text ekakata None."""
    text = (text or "").strip()
    for fmt in SCHEDULE_TIME_INPUT_FORMATS:
        try:
            naive = datetime.strptime(text, fmt)
        except ValueError:
            continue
        local = naive.replace(tzinfo=SRI_LANKA_TZ)
        return local.astimezone(timezone.utc)
    return None


def _scheduled_list(context: ContextTypes.DEFAULT_TYPE) -> list:
    return context.user_data.setdefault("scheduled_posts", [])


def _find_scheduled(context: ContextTypes.DEFAULT_TYPE, post_id: str) -> dict | None:
    for entry in _scheduled_list(context):
        if entry.get("id") == post_id:
            return entry
    return None


def _save_pending_as_scheduled(context: ContextTypes.DEFAULT_TYPE, chat_id: int, when_utc: datetime | None) -> dict:
    """fb_pending_* data (design eka + caption + target pages) scheduled_posts
    list ekata permanent entry ekak vidihata move karanawa. when_utc=None
    unoth "Draft" ekak vidihata save wenawa (time ekak nathuwa)."""
    data = context.user_data
    file_path = data.get("fb_pending_file")
    is_video = data.get("fb_pending_is_video", False)
    caption = data.get("fb_pending_caption", "")
    targets = data.get("fb_pending_targets") or []

    post_id = uuid.uuid4().hex[:8]
    stored_path = _save_scheduled_post_file(post_id, is_video, file_path)
    entry = {
        "id": post_id,
        "file_path": stored_path,
        "is_video": is_video,
        "caption": caption,
        "targets": targets,
        "when_utc": when_utc.isoformat() if when_utc else None,
        "chat_id": chat_id,
    }
    _scheduled_list(context).append(entry)
    return entry


async def _publish_scheduled_entry(context: ContextTypes.DEFAULT_TYPE, chat_id: int, entry: dict) -> bool:
    """Scheduled/draft entry ekak Facebook ekata post karala, result eka user
    ta report karanawa. Return eka True unoth entry eka (+ file eka) delete
    karanna puluwan (fully success unoth, ho file/page missing unoth), False
    unoth (partial/full fail) entry eka Draft ekak widiyata thiyaganna one
    (/schedule eken user ta manual widiyata "දැන්ම Post කරන්න" ekෙන් retry
    karanna puluwan)."""
    file_path = entry.get("file_path")
    is_video = entry.get("is_video", False)
    caption = entry.get("caption", "")
    targets = entry.get("targets") or []

    if not file_path or not Path(file_path).exists() or not targets:
        try:
            await context.bot.send_message(
                chat_id=chat_id,
                text="⚠️ Scheduled post එකක් post කරන්න බැරි උනා (file එක හෝ page එක missing), delete කරනවා.",
            )
        except Exception:
            pass
        _delete_scheduled_post_file(entry)
        return True

    results = []
    for target in targets:
        page_id = target.get("page_id")
        token = target.get("token")
        label = target.get("label") or page_id
        if is_video:
            ok, result = await post_video_to_facebook_page(page_id, token, file_path, caption)
        else:
            ok, result = await post_photo_to_facebook_page(page_id, token, file_path, caption)
        results.append((label, ok, result))

    all_ok = all(ok for _, ok, _ in results)
    lines = ["🕒 *Scheduled post එක auto-post වුණා!*" if all_ok else "🕒 *Scheduled post එකේ upload එකේදී ප්‍රශ්නයක්!*", ""]
    for label, ok, result in results:
        lines.append(f"✅ {label}: post කරලා ඉවරයි (id: {result})" if ok else f"⚠️ {label}: fail උනා - {result}")
    if not all_ok:
        lines.append("")
        lines.append("ℹ️ Fail උනු ඒවා /schedule command එකේ \"📤 දැන්ම Post කරන්න\" button එකෙන් ආයෙත් try කරන්න.")

    try:
        await context.bot.send_message(chat_id=chat_id, text="\n".join(lines), parse_mode="Markdown")
    except Exception:
        pass

    if all_ok:
        _delete_scheduled_post_file(entry)
        return True
    return False


async def _check_scheduled_posts(context: ContextTypes.DEFAULT_TYPE):
    """job_queue eken SCHEDULE_CHECK_INTERVAL_SECONDS ekakata parak repeating
    widiyata call wenawa - okkoma users ge scheduled_posts okkoma scan karala,
    time eka pැහැලවෙච්ච (due) ewa auto-post karanawa. Drafts (when_utc None)
    methanin skip karanawa - user ma manual widiyata post karanna one."""
    app = context.application
    now_utc = datetime.now(timezone.utc)
    for user_id, user_data in list(app.user_data.items()):
        entries = user_data.get("scheduled_posts") or []
        for entry in list(entries):
            when_iso = entry.get("when_utc")
            if not when_iso:
                continue
            try:
                when_utc = datetime.fromisoformat(when_iso)
            except Exception:
                continue
            if when_utc > now_utc:
                continue
            chat_id = entry.get("chat_id") or user_id
            removable = await _publish_scheduled_entry(context, chat_id, entry)
            if removable:
                if entry in entries:
                    entries.remove(entry)
            else:
                # fail unu eka Draft ekak widiyata pahatha wenawa - auto-retry
                # loop ekak wenna denne nathuwa, /schedule eken manual widiyata
                # user ma retry karana thuru enna one
                entry["when_utc"] = None


def _scheduled_menu_content(context: ContextTypes.DEFAULT_TYPE) -> tuple[str, InlineKeyboardMarkup]:
    entries = _scheduled_list(context)
    if not entries:
        text = (
            "🗓 *ඔයාට දැනට Schedule කරපු / Draft posts නෑ.*\n\n"
            "Post එකක් හදද්දි Facebook step එකේදී \"🕒 Schedule කරන්න\" හෝ "
            "\"📝 Draft විදිහට Save කරන්න\" click කරලා එකක් add කරගන්න."
        )
        return text, InlineKeyboardMarkup([])

    ordered = sorted(entries, key=lambda e: e.get("when_utc") or "9999")
    text = "🗓 *Schedule / Draft Posts:*\n\n(පහළින් එකක් තෝරලා, view/edit-time/delete/post-now කරන්න)"
    rows = []
    for entry in ordered:
        preview = (entry.get("caption") or "").strip().replace("\n", " ")
        if len(preview) > 22:
            preview = preview[:22] + "…"
        if entry.get("when_utc"):
            when_local = _format_sl_time(datetime.fromisoformat(entry["when_utc"]))
            label = f"🕒 {when_local} — {preview or '(caption නෑ)'}"
        else:
            label = f"📝 Draft — {preview or '(caption නෑ)'}"
        rows.append([InlineKeyboardButton(label, callback_data=f"sch_view_{entry['id']}")])
    return text, InlineKeyboardMarkup(rows)


async def schedule_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Top-level '/schedule' command eka - scheduled/draft posts okkoma
    list karala pennanawa. Post ekak hadanna kalinma, passe, monawahari call
    karanna puluwan, main post-creator conversation eka ekka conflict wenne na.

    Group/private dekakama use karanna puluwan - eth group ekaka meka call
    karoth, scheduled/draft posts eke captions tika group eke ඉන්න
    හැමෝටම penei (private chat ekakata witharak thani unoth witharai
    hidden widiyata thiyenne), e nisa group ekaka nam warning ekak
    piliwelata ekathu karanawa."""
    text, keyboard = _scheduled_menu_content(context)
    if update.effective_chat and update.effective_chat.type != "private":
        text = (
            "⚠️ Group ekaka use karana nisa, me list eke captions group eke "
            "ඉන්න හැමෝටම penei. Private ekakata one nam bot ekata DM ekak "
            "evala try කරන්න.\n\n"
        ) + text
    await update.message.reply_text(text, parse_mode="Markdown", reply_markup=keyboard)


async def schedule_back_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    text, keyboard = _scheduled_menu_content(context)
    await context.bot.send_message(chat_id=query.message.chat_id, text=text, parse_mode="Markdown", reply_markup=keyboard)


async def schedule_view_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Ekeka save karapu scheduled/draft post ekaka thumbnail eka (photo/video
    widiyatama) + caption + status + edit/delete/post-now options pennanawa."""
    query = update.callback_query
    post_id = query.data[len("sch_view_"):]
    entry = _find_scheduled(context, post_id)
    if not entry:
        await query.answer("⚠️ මේ post එක තව නෑ (delete වෙලා වෙන්න පුළුවන්).", show_alert=True)
        return await schedule_back_callback(update, context)
    await query.answer()

    when_iso = entry.get("when_utc")
    status_line = (
        f"🕒 Scheduled: *{_format_sl_time(datetime.fromisoformat(when_iso))}* (Sri Lankan time)"
        if when_iso else "📝 *Draft* (time set කරලා නෑ තවම)"
    )
    target_labels = ", ".join((t.get("label") or t.get("page_id") or "") for t in (entry.get("targets") or []))
    caption_text = entry.get("caption") or "(caption නෑ)"
    preview_text = f"{status_line}\n📄 Pages: {target_labels or '—'}\n\n📝 *Caption:*\n{caption_text}"
    if len(preview_text) > 950:
        preview_text = preview_text[:950] + "…"

    rows = [
        [InlineKeyboardButton("✏️ Time එක Edit කරන්න", callback_data=f"sch_edittime_{post_id}")],
        [InlineKeyboardButton("📤 දැන්ම Post කරන්න", callback_data=f"sch_postnow_{post_id}")],
        [InlineKeyboardButton("🗑 Delete කරන්න", callback_data=f"sch_delete_{post_id}")],
        [InlineKeyboardButton("🔙 Back", callback_data="sch_back")],
    ]
    file_path = entry.get("file_path")
    try:
        if entry.get("is_video"):
            with open(file_path, "rb") as f:
                await context.bot.send_video(
                    chat_id=query.message.chat_id, video=f, caption=preview_text,
                    parse_mode="Markdown", reply_markup=InlineKeyboardMarkup(rows),
                )
        else:
            with open(file_path, "rb") as f:
                await context.bot.send_photo(
                    chat_id=query.message.chat_id, photo=f, caption=preview_text,
                    parse_mode="Markdown", reply_markup=InlineKeyboardMarkup(rows),
                )
    except Exception:
        await context.bot.send_message(
            chat_id=query.message.chat_id, text=preview_text, parse_mode="Markdown",
            reply_markup=InlineKeyboardMarkup(rows),
        )


async def schedule_delete_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    post_id = query.data[len("sch_delete_"):]
    entries = _scheduled_list(context)
    entry = _find_scheduled(context, post_id)
    if entry:
        entries.remove(entry)
        _delete_scheduled_post_file(entry)
    await query.answer("🗑 Delete කළා!" if entry else "⚠️ මේ post එක තව නෑ.", show_alert=True)
    text, keyboard = _scheduled_menu_content(context)
    await context.bot.send_message(chat_id=query.message.chat_id, text=text, parse_mode="Markdown", reply_markup=keyboard)


async def schedule_postnow_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    post_id = query.data[len("sch_postnow_"):]
    entry = _find_scheduled(context, post_id)
    if not entry:
        await query.answer("⚠️ මේ post එක තව නෑ.", show_alert=True)
        return
    await query.answer()
    status_msg = await context.bot.send_message(chat_id=query.message.chat_id, text="⏳ Post කරමින්...")
    removable = await _publish_scheduled_entry(context, query.message.chat_id, entry)
    try:
        await status_msg.delete()
    except Exception:
        pass
    if removable:
        entries = _scheduled_list(context)
        if entry in entries:
            entries.remove(entry)


async def schedule_edittime_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """'✏️ Time එක Edit කරන්න' button eken patan gannawa - aluth date/time
    ekak ahanawa (schedule_edit_conv - dedicated mini-conversation ekaka)."""
    query = update.callback_query
    post_id = query.data[len("sch_edittime_"):]
    entry = _find_scheduled(context, post_id)
    if not entry:
        await query.answer("⚠️ මේ post එක තව නෑ.", show_alert=True)
        return ConversationHandler.END
    await query.answer()
    context.user_data["sch_editing_id"] = post_id
    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text=(
            "🕒 *අලුත් දිනය සහ වේලාව* type කරලා send කරන්න (Sri Lankan time, 24-hour format):\n\n"
            f"`DD-MM-YYYY HH:MM`\nඋදාහරණයක්: `{SCHEDULE_TIME_EXAMPLE}`"
        ),
        parse_mode="Markdown",
    )
    return WAITING_EDIT_SCHEDULE_TIME


async def receive_edit_schedule_time(update: Update, context: ContextTypes.DEFAULT_TYPE):
    post_id = context.user_data.get("sch_editing_id")
    entry = _find_scheduled(context, post_id) if post_id else None
    if not entry:
        await update.message.reply_text("⚠️ මේ post එක තව නෑ.")
        context.user_data.pop("sch_editing_id", None)
        return ConversationHandler.END

    when_utc = _parse_sl_time_input(update.message.text or "")
    now_utc = datetime.now(timezone.utc)

    if when_utc is None:
        await update.message.reply_text(
            f"⚠️ Format එක වැරදියි. `DD-MM-YYYY HH:MM` විදිහට type කරන්න, උදා: `{SCHEDULE_TIME_EXAMPLE}`, "
            "හෝ /cancel කරන්න.",
            parse_mode="Markdown",
        )
        return WAITING_EDIT_SCHEDULE_TIME

    if when_utc <= now_utc + timedelta(minutes=1):
        await update.message.reply_text(
            "⚠️ Time එක අනිවාර්යයෙන්ම future එකේ එකක් වෙන්න ඕන. ආයෙත් type කරන්න, හෝ /cancel කරන්න."
        )
        return WAITING_EDIT_SCHEDULE_TIME

    entry["when_utc"] = when_utc.isoformat()
    context.user_data.pop("sch_editing_id", None)
    await update.message.reply_text(
        f"✅ Time එක update කළා! 🕒 *{_format_sl_time(when_utc)}*ට auto-post වෙනවා.",
        parse_mode="Markdown",
    )
    return ConversationHandler.END


async def schedule_edittime_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.pop("sch_editing_id", None)
    await update.message.reply_text("❌ Cancel කළා - time එක වෙනස් වුණේ නෑ.")
    return ConversationHandler.END


# ---------------- FACEBOOK PAGES MANAGER (/pages) ----------------
# "/pages" command eken, post ekak hadanna kalinma (ONIMA welavaka) user ta
# ownge Facebook Pages tika add/edit/delete karaganna puluwan. Save wena
# data eka context.user_data["fb_pages"] dict eka - { page_id: {"label", "token"} }
# - persistence file eka ekka save wenawa (bot restart unath thiyenawa).

def _pages_menu_content(pages: dict) -> tuple[str, InlineKeyboardMarkup]:
    """/pages menu eke text + keyboard eka - "pages_view_" callback eken enna
    submenu ekatath, add/delete/guide passe aye methanatama return wenna
    one nisa wenama function ekakata vekkarala thiyenawa."""
    if pages:
        text = (
            "📑 *ඔයාගේ Saved Facebook Pages:*\n\n"
            "(පහළින් Page එකක් තෝරලා, token එක edit කරන්න/page එක delete කරන්න පුළුවන්)"
        )
    else:
        text = (
            "📑 *ඔයාට තවම Facebook Page එකක්වත් add කරලා නෑ.*\n\n"
            "පහළින් \"➕ Add Page\" click කරලා එකක් add කරගන්න. "
            "Post එකක් හදද්දි, methanin add කරපු ඕන Page එකකට (හෝ කීපයකටම) "
            "එකපාරටම direct post කරන්න පුළුවන් වෙනවා."
        )
    rows = []
    for pid, info in pages.items():
        label = info.get("label") or pid
        short = label if len(label) <= 24 else label[:24] + "…"
        rows.append([InlineKeyboardButton(f"📄 {short}", callback_data=f"pages_view_{pid}")])
    rows.append([InlineKeyboardButton("➕ අලුත් Page එකක් Add කරන්න", callback_data="pages_add")])
    rows.append([InlineKeyboardButton("ℹ️ Token එක ගන්නා විදිය", callback_data="pages_guide")])
    return text, InlineKeyboardMarkup(rows)


async def send_pages_menu(chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    pages = context.user_data.get("fb_pages", {})
    text, keyboard = _pages_menu_content(pages)
    await context.bot.send_message(chat_id=chat_id, text=text, parse_mode="Markdown", reply_markup=keyboard)


async def pages_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Top-level '/pages' command eka - ONIMA welavaka (post ekak hadanna
    kalinma, passe, monawahari) call karanna puluwan, main post-creator
    conversation eka ekka conflict wenne na.

    Group/private dekakama use karanna puluwan (user ekage explicit request
    ekak eka - security risk eka therigena). Meke flow eke (Page ID + access
    token) plain text vidihata type karanna one wenawa - group ekaka type
    karoth e token eka group eke ඉන්න හැමෝටම penei, e nisa group ekaka nam
    hema welema warning ekak issellama pennanawa."""
    if update.effective_chat and update.effective_chat.type != "private":
        await update.message.reply_text(
            "⚠️ Security nisa danna one - passe eka Facebook Page ID/access "
            "token type karanna one welawa, e text eka type karana group "
            "eke ඉන්න හැමෝටම penei. Private ekakata one nam bot ekata DM "
            "ekak evala try karanna."
        )
    await send_pages_menu(update.message.chat_id, context)


async def pages_back_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    text, keyboard = _pages_menu_content(context.user_data.get("fb_pages", {}))
    try:
        await query.edit_message_text(text, parse_mode="Markdown", reply_markup=keyboard)
    except Exception:
        await send_pages_menu(query.message.chat_id, context)


async def pages_view_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Ekeka save karapu Page ekaka details tika + edit/delete options
    pennanawa (token eka full ekම penne nathuwa, ithuru wenne anthima
    characters 6 witharai - security ekata)."""
    query = update.callback_query
    pid = query.data[len("pages_view_"):]
    pages = context.user_data.get("fb_pages", {})
    info = pages.get(pid)
    if not info:
        await query.answer("⚠️ Me Page එක තව නෑ (delete වෙලා වෙන්න පුළුවන්).", show_alert=True)
        text, keyboard = _pages_menu_content(pages)
        try:
            await query.edit_message_text(text, parse_mode="Markdown", reply_markup=keyboard)
        except Exception:
            await send_pages_menu(query.message.chat_id, context)
        return
    await query.answer()

    label = info.get("label") or pid
    token = info.get("token", "")
    masked = ("•" * 6 + token[-6:]) if len(token) > 6 else (token or "—")
    text = f"📄 *{label}*\n🆔 Page ID: `{pid}`\n🔑 Token: `{masked}`"
    rows = [
        [InlineKeyboardButton("✏️ Token එක Edit කරන්න", callback_data=f"pages_edittoken_{pid}")],
        [InlineKeyboardButton("🗑 Page එක Delete කරන්න", callback_data=f"pages_delete_{pid}")],
        [InlineKeyboardButton("🔙 Back", callback_data="pages_back")],
    ]
    try:
        await query.edit_message_text(text, parse_mode="Markdown", reply_markup=InlineKeyboardMarkup(rows))
    except Exception:
        await context.bot.send_message(
            chat_id=query.message.chat_id, text=text, parse_mode="Markdown",
            reply_markup=InlineKeyboardMarkup(rows),
        )


async def pages_delete_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    pid = query.data[len("pages_delete_"):]
    pages = context.user_data.get("fb_pages", {})
    removed = pages.pop(pid, None)
    await query.answer(
        f"🗑 '{removed.get('label', pid)}' Delete කළා!" if removed else "⚠️ Me Page එක තව නෑ.",
        show_alert=True,
    )
    await pages_back_callback(update, context)


async def pages_guide_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    await context.bot.send_message(chat_id=query.message.chat_id, text=PAGE_GUIDE_TEXT, parse_mode="Markdown")


async def pages_add_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """'➕ Add Page' button eken patan gannawa - mulinma guide eka pennala,
    passe label -> page id -> token kiyala thunak ahanawa."""
    query = update.callback_query
    await query.answer()
    await context.bot.send_message(chat_id=query.message.chat_id, text=PAGE_GUIDE_TEXT, parse_mode="Markdown")
    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text="🏷 මුලින්ම, මේ Page එක ලේසියෙන් identify කරගන්න පුළුවන් නමක් (label) type කරලා "
        "send කරන්න (e.g. \"AegisX Main Page\"):",
    )
    return WAITING_PAGE_LABEL


async def receive_page_label(update: Update, context: ContextTypes.DEFAULT_TYPE):
    label = (update.message.text or "").strip()
    if not label:
        await update.message.reply_text("⚠️ නමක් type කරලා send කරන්න:")
        return WAITING_PAGE_LABEL
    context.user_data["pages_pending_label"] = label
    await update.message.reply_text(
        "🆔 දැන් ඔයාගේ Facebook *Page ID* එක type කරලා send කරන්න:",
        parse_mode="Markdown",
    )
    return WAITING_PAGE_ADD_ID


async def receive_page_add_id(update: Update, context: ContextTypes.DEFAULT_TYPE):
    page_id = (update.message.text or "").strip()
    if not page_id or " " in page_id:
        await update.message.reply_text("⚠️ Page ID එක වැරදියි (space තියෙන්න බෑ), ආයෙත් හරියට type කරන්න:")
        return WAITING_PAGE_ADD_ID
    context.user_data["pages_pending_id"] = page_id
    await update.message.reply_text(
        "🔑 දැන් ඔයාගේ Facebook *Page Access Token* එක type කරලා send කරන්න "
        "(උඩ guide එකේ කියපු විදිහට `me/accounts` response එකෙන් ගත්ත Page token එකම, "
        "User token එකක් නෙමෙයි):",
        parse_mode="Markdown",
    )
    return WAITING_PAGE_ADD_TOKEN


async def receive_page_add_token(update: Update, context: ContextTypes.DEFAULT_TYPE):
    token = (update.message.text or "").strip()
    if not token or " " in token:
        await update.message.reply_text("⚠️ Token එක වැරදියි (space තියෙන්න බෑ), ආයෙත් හරියට type කරන්න:")
        return WAITING_PAGE_ADD_TOKEN

    data = context.user_data
    page_id = data.pop("pages_pending_id", None)
    label = data.pop("pages_pending_label", None) or page_id
    pages = data.setdefault("fb_pages", {})
    pages[page_id] = {"label": label, "token": token}

    await update.message.reply_text(f"✅ '{label}' Page එක add කරලා ඉවරයි! දැන් post කරන කොට මේකත් list එකේ පේනවා.")
    await send_pages_menu(update.message.chat_id, context)
    return ConversationHandler.END


async def pages_edittoken_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Ekeka save karapu Page ekaka token eka witharak, ONIMA welavaka change
    karanna puluwan (e.g. token eka expire unoth) - Page ID eka aye type
    karanna one na."""
    query = update.callback_query
    pid = query.data[len("pages_edittoken_"):]
    pages = context.user_data.get("fb_pages", {})
    if pid not in pages:
        await query.answer("⚠️ Me Page එක තව නෑ (delete වෙලා වෙන්න පුළුවන්).", show_alert=True)
        return ConversationHandler.END
    await query.answer()
    context.user_data["pages_edit_target"] = pid
    label = pages[pid].get("label", pid)
    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text=f"🔑 '{label}' Page එකට අලුත් *Page Access Token* එක type කරලා send කරන්න:",
        parse_mode="Markdown",
    )
    return WAITING_PAGE_EDIT_TOKEN


async def receive_page_edit_token(update: Update, context: ContextTypes.DEFAULT_TYPE):
    token = (update.message.text or "").strip()
    if not token or " " in token:
        await update.message.reply_text("⚠️ Token එක වැරදියි (space තියෙන්න බෑ), ආයෙත් හරියට type කරන්න:")
        return WAITING_PAGE_EDIT_TOKEN

    data = context.user_data
    pid = data.pop("pages_edit_target", None)
    pages = data.get("fb_pages", {})
    if not pid or pid not in pages:
        await update.message.reply_text("⚠️ Me Page එක තව නෑ (delete වෙලා වෙන්න පුළුවන්).")
        return ConversationHandler.END

    pages[pid]["token"] = token
    await update.message.reply_text(f"✅ '{pages[pid].get('label', pid)}' Page එකේ token එක update කළා!")
    await send_pages_menu(update.message.chat_id, context)
    return ConversationHandler.END


async def pages_manager_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.pop("pages_pending_label", None)
    context.user_data.pop("pages_pending_id", None)
    context.user_data.pop("pages_edit_target", None)
    await update.message.reply_text("❌ Cancelled.")
    return ConversationHandler.END


VIDEO_PLATFORM_LABELS = {"pinterest": "Pinterest", "tiktok": "TikTok"}


async def video_platform_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()

    # e "monawa hari video ekak ona da" prompt eka sampurnayenma chat eken ain karanawa
    try:
        await query.message.delete()
    except Exception:
        pass

    if query.data == "vid_no":
        await _finish_up(query.message.chat_id, context)
        return ConversationHandler.END

    # vid_pinterest or vid_tiktok
    platform = query.data.replace("vid_", "")
    context.user_data["video_platform"] = platform
    label = VIDEO_PLATFORM_LABELS.get(platform, "video")

    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text=f"📎 Send me the {label} link.",
    )
    return WAITING_VIDEO_LINK


async def receive_video_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    url = update.message.text.strip()
    chat_id = update.message.chat_id
    platform = context.user_data.get("video_platform", "video")
    label = VIDEO_PLATFORM_LABELS.get(platform, "video")

    status_msg = await update.message.reply_text(f"⏳ Fetching video from {label}...")

    # --- FAST PATH: direct URL eka Telegram ekatama fetch karanna denawa,
    # VPS eke bandwidth/disk kisima ekak use wenne nehe. Pinterest ekath
    # TikTok ekath dekamatama methanata kelinma yanawa - function eka
    # site-agnostic (yt-dlp eken URL eken site eka auto-detect wenawa). ---
    try:
        direct_url = await get_video_direct_url(url)
        await send_with_retry(
            context.bot.send_document,
            chat_id=chat_id,
            document=direct_url,
            filename=f"{platform}_video.mp4",
            disable_content_type_detection=True,
            what="fast-path video send_document",
        )
        try:
            await status_msg.delete()
        except Exception:
            pass
        await _finish_up(chat_id, context)
        return ConversationHandler.END
    except Exception:
        # source CDN eken Telegram server ekata fetch eka block wela
        # (referer/user-agent check ekak thiyenna puluwan - TikTok/Pinterest
        # dekamatama meka wenna puluwan) - meka expected welawaka wenna
        # puluwan, ehema nisa slow path ekata fallback wenawa
        logger.info("Fast direct-URL send failed, falling back to local download")

    # --- SLOW PATH (fallback): VPS ekatama download karala, ithin re-upload
    # karanawa - hamawelama wada karanawa, ethakota witharak time/bandwidth
    # ithuru ganne ---
    try:
        await status_msg.edit_text(f"⏳ Downloading video from {label}...")
    except Exception:
        pass

    try:
        video_path = await download_video_with_retry(url)
    except Exception as e:
        logger.exception("Video download failed after retries")
        await status_msg.edit_text(
            f"⚠️ Couldn't download that video: {e}\n\n"
            f"Send the {label} link again, or /cancel to stop."
        )
        return WAITING_VIDEO_LINK

    try:
        with open(video_path, "rb") as f:
            # send_document ekenma yawanne - send_video kalot Telegram eken
            # video eka re-compress karanna puluwan, ehema unoth original
            # quality eka nathi wenawa
            await send_with_retry(
                context.bot.send_document,
                chat_id=chat_id,
                document=f,
                filename=f"{platform}_video.mp4",
                disable_content_type_detection=True,
                what="slow-path video send_document",
            )
    finally:
        shutil.rmtree(Path(video_path).parent, ignore_errors=True)

    try:
        await status_msg.delete()
    except Exception:
        pass

    await _finish_up(chat_id, context)
    return ConversationHandler.END


def _cleanup_selfblur(data: dict):
    """selfblur_* temp files (video/audio) disk eken clean karanawa - render
    ivara unu passe, ho user /cancel kaloth, ho aluth /selfblur ekak patan
    ganna kalin call karanawa."""
    video_path = data.pop("selfblur_video_path", None)
    if video_path:
        try:
            shutil.rmtree(Path(video_path).parent, ignore_errors=True)
        except Exception:
            pass
    audio_path = data.pop("selfblur_audio_path", None)
    if audio_path:
        try:
            shutil.rmtree(Path(audio_path).parent, ignore_errors=True)
        except Exception:
            pass
    rendered_path = data.pop("selfblur_rendered_path", None)
    if rendered_path:
        try:
            shutil.rmtree(Path(rendered_path).parent, ignore_errors=True)
        except Exception:
            pass
    bg_image_path = data.pop("selfblur_bg_image_path", None)
    if bg_image_path:
        try:
            shutil.rmtree(Path(bg_image_path).parent, ignore_errors=True)
        except Exception:
            pass
    bg_video_path = data.pop("selfblur_bg_video_path", None)
    if bg_video_path:
        try:
            shutil.rmtree(Path(bg_video_path).parent, ignore_errors=True)
        except Exception:
            pass
    for key in (
        "selfblur_blur_px", "selfblur_fg_pct", "selfblur_fg_yoff", "selfblur_duration",
        "selfblur_audio_mode", "selfblur_audio_fit", "selfblur_watermark_bytes",
        "selfblur_menu_msg_id", "selfblur_prompt_msg_id", "selfblur_view",
        "selfblur_text", "selfblur_font_size", "selfblur_preview_msg_id",
        "selfblur_generating", "selfblur_fb_target_page_id",
        "selfblur_text_color", "selfblur_stroke_width", "selfblur_stroke_color",
        "selfblur_text_yoff", "selfblur_overlay_opacity", "selfblur_emoji_size",
        "selfblur_settings_msg_id", "selfblur_caption_msg_id", "selfblur_onboarding",
        "selfblur_emoji_yoff",
        "selfblur_watermark_opacity", "selfblur_watermark_scale", "selfblur_watermark_speed",
        "selfblur_watermark_direction", "selfblur_watermark_side",
        "selfblur_logo_kind", "selfblur_logo_value", "selfblur_logo_scale",
        "selfblur_logo_offset_bottom", "selfblur_logo_opacity", "selfblur_manual_target",
        "selfblur_bg_kind", "selfblur_bg_color", "selfblur_bg_blur_enabled",
        "selfblur_active_template_name", "selfblur_layout", "selfblur_meme_text_yoff",
    ):
        data.pop(key, None)


async def selfblur_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/selfblur - ekma video ekma dedena widiyata use karana ("blur behind
    itself") feature eka patan gannawa. Video eka (TikTok/Pinterest link,
    hari phone eken direct upload) ahagannawa."""
    _cleanup_selfblur(context.user_data)
    await update.message.reply_text(
        "🌫 *Self-Blur Video*\n\n"
        "Video eka danna - eka video ekma center eke clear widiyata + "
        "full-screen blur background ekක් widiyata dekamatama use karanawa "
        "(TikTok/FB Reels 'fill screen' effect eka wagේ).\n\n"
        "Video eka koහෙන්ද ගන්නෙ?",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup([
            [
                InlineKeyboardButton("📌 Pinterest", callback_data="sbvid_pinterest"),
                InlineKeyboardButton("🎵 TikTok", callback_data="sbvid_tiktok"),
            ],
            [InlineKeyboardButton("📱 Upload from phone", callback_data="sbvid_upload")],
        ]),
    )
    return SELFBLUR_ASK_VIDEO_PLATFORM


async def selfblur_platform_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    chat_id = query.message.chat_id

    try:
        await query.message.delete()
    except Exception:
        pass

    if query.data == "sbvid_upload":
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text="📱 Send me the video file directly (send it as a 'file/document', "
            "not a normal video message - Telegram re-compresses normal video "
            "messages and quality drops).\n\n"
            "⚠️ Bots can only download files up to 20MB from Telegram.",
        )
        context.user_data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_VIDEO_UPLOAD

    platform = query.data.replace("sbvid_", "")
    label = VIDEO_PLATFORM_LABELS.get(platform, "video")
    context.user_data["selfblur_platform"] = platform
    sent = await context.bot.send_message(chat_id=chat_id, text=f"📎 Send me the {label} link.")
    context.user_data["selfblur_prompt_msg_id"] = sent.message_id
    return WAITING_SELFBLUR_VIDEO_LINK


async def _selfblur_video_ready(chat_id: int, context: ContextTypes.DEFAULT_TYPE, video_path: str,
                                 duration: float, status_msg) -> int:
    """Video eka (link/upload dekedinma) download unu passe common step eka -
    defaults set karala, adjust menu eka pennanawa."""
    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    context.user_data["selfblur_video_path"] = video_path
    context.user_data["selfblur_duration"] = min(duration, SELFBLUR_MAX_SECONDS)
    context.user_data["selfblur_blur_px"] = SELFBLUR_BLUR_DEFAULT
    context.user_data["selfblur_fg_pct"] = SELFBLUR_FG_PCT_DEFAULT
    context.user_data["selfblur_fg_yoff"] = SELFBLUR_YOFF_DEFAULT
    context.user_data["selfblur_audio_mode"] = "keep"
    context.user_data["selfblur_audio_path"] = None
    context.user_data["selfblur_audio_fit"] = "loop"
    context.user_data["selfblur_watermark_bytes"] = None
    context.user_data["selfblur_watermark_opacity"] = WATERMARK_OPACITY_DEFAULT
    context.user_data["selfblur_watermark_scale"] = WATERMARK_SCALE_DEFAULT
    context.user_data["selfblur_watermark_speed"] = WATERMARK_SPEED_DEFAULT
    context.user_data["selfblur_watermark_direction"] = WATERMARK_DIRECTION_DEFAULT
    context.user_data["selfblur_watermark_side"] = WATERMARK_SIDE_DEFAULT
    context.user_data["selfblur_logo_kind"] = None
    context.user_data["selfblur_logo_value"] = None
    context.user_data["selfblur_logo_scale"] = LOGO_SCALE_DEFAULT
    context.user_data["selfblur_logo_offset_bottom"] = LOGO_OFFSET_DEFAULT
    context.user_data["selfblur_logo_opacity"] = LOGO_OPACITY_DEFAULT
    context.user_data["selfblur_emoji_yoff"] = EMOJI_OFFSET_DEFAULT
    context.user_data["selfblur_view"] = "main"
    # "usergen" flow eka anuwa - video link ekata passe direct adjust menu
    # ekata yanne nathuwa, mulinma text eka ahala, ithin (Emoji step ekakin)
    # emoji ahala, dekama ivara una passe witharai preview/adjust menu eka
    # penenne (SELFBLUR_TEXT_DEFAULT placeholder eka danne na methanata).
    context.user_data["selfblur_text"] = None
    context.user_data["selfblur_font_size"] = SELFBLUR_FONT_SIZE_DEFAULT
    context.user_data["selfblur_emoji_size"] = EMOJI_SIZE_DEFAULT
    context.user_data["selfblur_text_color"] = SELFBLUR_TEXT_COLOR_DEFAULT
    context.user_data["selfblur_stroke_width"] = STROKE_WIDTH_DEFAULT
    context.user_data["selfblur_stroke_color"] = STROKE_COLOR_DEFAULT
    context.user_data["selfblur_text_yoff"] = SELFBLUR_TEXT_YOFF_DEFAULT
    context.user_data["selfblur_overlay_opacity"] = SELFBLUR_OVERLAY_OPACITY_DEFAULT
    context.user_data["selfblur_blur_type"] = SELFBLUR_BLUR_TYPE_DEFAULT
    context.user_data["selfblur_chromatic_aberration"] = CHROMATIC_ABERRATION_DEFAULT
    context.user_data["selfblur_chromatic_shift"] = CHROMATIC_SHIFT_DEFAULT
    context.user_data["selfblur_vhs_effect"] = VHS_EFFECT_DEFAULT
    context.user_data["selfblur_vhs_strength"] = VHS_STRENGTH_DEFAULT
    context.user_data["selfblur_intro_black_seconds"] = INTRO_BLACK_SECONDS_DEFAULT
    context.user_data["selfblur_bg_kind"] = SELFBLUR_BG_KIND_DEFAULT
    context.user_data["selfblur_bg_color"] = SELFBLUR_BG_COLOR_DEFAULT
    context.user_data["selfblur_bg_image_path"] = None
    context.user_data["selfblur_bg_video_path"] = None
    context.user_data["selfblur_bg_blur_enabled"] = True

    try:
        await status_msg.delete()
    except Exception:
        pass

    # onboarding flag eka - "usergen" order eka (link->text->emoji->preview)
    # drive karanne methanin, receive_selfblur_text/receive_selfblur_emoji
    # dekama methana check karanawa.
    context.user_data["selfblur_onboarding"] = True
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text="✏️ Video eke danna text eka type karanna (##bold## //italic// "
        "\"header\" ^^highlight^^ syntax + emoji characters support wenawa), "
        "nathnam /skip karala text ekak nathuwama ahaganna.",
        parse_mode="Markdown",
    )
    context.user_data["selfblur_prompt_msg_id"] = sent.message_id
    return WAITING_SELFBLUR_TEXT


async def receive_selfblur_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Video eka ready una passe ahana caption/emoji text eka - main
    post-creator eke text syntax ekama (##bold## //italic// ""header""
    ^^highlight^^) support karanawa, ithin generate_image() eka reuse karala
    text_overlay PNG ekak (blur_px eka methanata relevant na, transparent
    background ekaka) hadala video eke udin overlay karanawa.

    "usergen" onboarding flow eka anuwa (link -> text -> emoji -> preview)
    methanin ithuru pahatha "sb_text_edit" button eken (menu eka pennapu
    passe, text eka wenas karanna) enna puluwan - eth danata selfblur_onboarding
    flag eka thiyenawa nam witharai, ita passe emoji step ekata yanawa; ehema
    nathnam kalinma widiyatama, methanin ekamma menu ekata return wenawa."""
    chat_id = update.message.chat_id
    raw_text = apply_native_formatting_as_markup(
        update.message.text or "", update.message.entities or ()
    )
    raw_text = convert_text_emoticons(raw_text)
    markup_issues = find_markup_issues(raw_text)
    if markup_issues:
        await update.message.reply_text(
            "⚠️ Text එකේ ##/// sign වැරදිලා තියෙනවා වගේ පේනවා (close කරලා නෑ):\n"
            + "\n".join(markup_issues)
            + "\n\nඑවා හරි කරලා ආයෙත් text එක type කරලා send කරන්න, නැත්නම් /skip කරන්න."
        )
        return WAITING_SELFBLUR_TEXT
    context.user_data["selfblur_text"] = raw_text
    if context.user_data.pop("selfblur_onboarding", False):
        return await _ask_selfblur_emoji(chat_id, context)
    return await _selfblur_show_menu(chat_id, context)


async def selfblur_skip_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/skip - caption/emoji text ekak danna one nathi welata."""
    chat_id = update.message.chat_id
    context.user_data["selfblur_text"] = None
    if context.user_data.pop("selfblur_onboarding", False):
        return await _ask_selfblur_emoji(chat_id, context)
    return await _selfblur_show_menu(chat_id, context)


async def _ask_selfblur_emoji(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> int:
    """"usergen" flow eke 3-va step eka - text ekata yatin danna emoji 2-3k
    (real Unicode emoji, apple-style CDN eken render wenawa) ahaganawa.
    /skip karoth emoji ekak nathuwama preview/adjust menu ekata yanawa."""
    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass
    # emoji step ekedith onboarding flag eka thiyaganna one - user text step
    # eka skip kara nam methanata dan ena nisa, emoji ivara welata therenna
    # one methanma flow ekema koටsak kiyala (menu ekata witharai passe yanawa)
    context.user_data["selfblur_onboarding"] = True
    sent = await context.bot.send_message(
        chat_id=chat_id,
        text="😀 Text ekata yatin danna emoji 2-3k danna (e.g. 🔥❤️👍), "
        "nathnam /skip karala emoji ekak nathuwama continue karanna.",
    )
    context.user_data["selfblur_prompt_msg_id"] = sent.message_id
    return WAITING_SELFBLUR_EMOJI


async def receive_selfblur_emoji(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id
    emoji_text = (update.message.text or "").strip()
    existing_text = context.user_data.get("selfblur_text")
    if emoji_text:
        # extract_pictographic_emoji eka text eke koheth hari thiyena pictographic
        # emoji tika ekathu karagena, text eka pahalin apple-style row ekakata
        # render karanawa nisa, methanin plain widiyata append karoth witharai ida ganawa
        context.user_data["selfblur_text"] = (
            f"{existing_text}\n{emoji_text}" if existing_text else emoji_text
        )
    context.user_data.pop("selfblur_onboarding", None)
    return await _selfblur_show_menu(chat_id, context)


async def selfblur_skip_emoji(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.pop("selfblur_onboarding", None)
    return await _selfblur_show_menu(update.message.chat_id, context)


async def _selfblur_show_menu(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> int:
    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass
    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_video_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    url = update.message.text.strip()
    chat_id = update.message.chat_id
    platform = context.user_data.get("selfblur_platform", "video")
    label = VIDEO_PLATFORM_LABELS.get(platform, "video")

    status_msg = await update.message.reply_text(f"⏳ Downloading video from {label}...")

    try:
        video_path = await download_video_with_retry(url)
    except Exception as e:
        logger.exception("Self-blur video download failed after retries")
        await status_msg.edit_text(
            f"⚠️ Couldn't download that video: {e}\n\n"
            f"Send the {label} link again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_VIDEO_LINK

    try:
        _w, _h, duration, _br = await probe_video(video_path)
    except Exception as e:
        logger.exception("Self-blur video probe failed")
        shutil.rmtree(Path(video_path).parent, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't process that video: {e}\n\n"
            f"Send the {label} link again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_VIDEO_LINK

    return await _selfblur_video_ready(chat_id, context, video_path, duration, status_msg)


async def receive_selfblur_video_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id
    tg_video = update.message.video or (
        update.message.document
        if update.message.document and (update.message.document.mime_type or "").startswith("video/")
        else None
    )
    if tg_video is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like a video file. Send a video, or /cancel to stop."
        )
        return WAITING_SELFBLUR_VIDEO_UPLOAD

    status_msg = await update.message.reply_text("⏳ Downloading your video...")

    tmp_dir = tempfile.mkdtemp(prefix="sbvidup_")
    ext = Path(getattr(tg_video, "file_name", None) or "video.mp4").suffix or ".mp4"
    video_path = str(Path(tmp_dir) / f"upload{ext}")

    try:
        tg_file = await context.bot.get_file(tg_video.file_id)
        await tg_file.download_to_drive(video_path)
    except Exception as e:
        logger.exception("Self-blur video upload download failed")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't download that video: {e}\n\n"
            "(Bots can only download files up to 20MB from Telegram.)\n\n"
            "Send it again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_VIDEO_UPLOAD

    try:
        _w, _h, duration, _br = await probe_video(video_path)
    except Exception as e:
        logger.exception("Self-blur video probe failed")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't process that video: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_VIDEO_UPLOAD

    return await _selfblur_video_ready(chat_id, context, video_path, duration, status_msg)


def _selfblur_bg_label(data: dict) -> str:
    kind = data.get("selfblur_bg_kind", SELFBLUR_BG_KIND_DEFAULT)
    if kind == "color":
        color = data.get("selfblur_bg_color", SELFBLUR_BG_COLOR_DEFAULT)
        name = next((k for k, v in COLORS.items() if v == color), None)
        return f"🎨 Solid {name or color}"
    if kind == "image":
        return "🖼 Custom image" + (" (+blur)" if data.get("selfblur_bg_blur_enabled", True) else "")
    if kind == "video":
        return "🎥 Custom video" + (" (+blur)" if data.get("selfblur_bg_blur_enabled", True) else "")
    return "🌫 Blurred video (auto, from source)"


def _selfblur_menu_text(data: dict) -> str:
    audio_mode = data.get("selfblur_audio_mode", "keep")
    audio_label = {"keep": "🎵 Original audio", "mute": "🔇 Muted", "replace": "🎶 Replaced"}.get(audio_mode, "keep")
    wm_on = bool(data.get("selfblur_watermark_bytes"))
    logo_on = bool(data.get("selfblur_logo_kind") and data.get("selfblur_logo_value"))
    has_text = bool(data.get("selfblur_text"))
    overlay_pct = data.get("selfblur_overlay_opacity", SELFBLUR_OVERLAY_OPACITY_DEFAULT)
    return (
        "🌫 *Self-Blur Video Settings*\n\n"
        f"🖼 Background: {_selfblur_bg_label(data)}\n"
        f"🌫 Blur strength: `{data.get('selfblur_blur_px', SELFBLUR_BLUR_DEFAULT)}`\n"
        f"🔍 Center video size: `{data.get('selfblur_fg_pct', SELFBLUR_FG_PCT_DEFAULT)}%`\n"
        f"↕️ Position: `{data.get('selfblur_fg_yoff', SELFBLUR_YOFF_DEFAULT):+d}%`\n"
        f"⬛ Background overlay: `{overlay_pct}%`\n"
        f"🔳 Layout: {'Meme (Top Box)' if data.get('selfblur_layout', 'standard') == 'meme' else 'Standard (Overlay)'}\n"
        f"🔤 Text: {'(no text added)' if not has_text else 'set - tap 🔤 Text Settings to edit'}\n"
        f"🎧 Audio: {audio_label}\n"
        f"🏷 Scrolling watermark: {'✅ On' if wm_on else '❌ Off'}\n"
        f"🖼 Center logo: {'✅ On' if logo_on else '❌ Off'}\n"
        f"{BLUR_TYPE_LABELS.get(data.get('selfblur_blur_type', SELFBLUR_BLUR_TYPE_DEFAULT), '')}\n"
        f"🌈 Chromatic: {'ON ' + str(data.get('selfblur_chromatic_shift', CHROMATIC_SHIFT_DEFAULT)) + 'px' if data.get('selfblur_chromatic_aberration', CHROMATIC_ABERRATION_DEFAULT) else 'OFF'}\n"
        f"📺 VHS: {'ON ' + str(data.get('selfblur_vhs_strength', VHS_STRENGTH_DEFAULT)) + '%' if data.get('selfblur_vhs_effect', VHS_EFFECT_DEFAULT) else 'OFF'}\n"
        f"⬛ Intro fade: `{data.get('selfblur_intro_black_seconds', INTRO_BLACK_SECONDS_DEFAULT)}s`\n\n"
        "👆 Preview eka udinma penei - adjust karala, 'Render' click karanna 👇"
    )


def _selfblur_text_menu_text(data: dict) -> str:
    font_size = data.get("selfblur_font_size", SELFBLUR_FONT_SIZE_DEFAULT)
    text_color_key = next(
        (k for k, v in COLORS.items() if v == data.get("selfblur_text_color", SELFBLUR_TEXT_COLOR_DEFAULT)), None
    )
    stroke_width = data.get("selfblur_stroke_width", STROKE_WIDTH_DEFAULT)
    yoff = data.get("selfblur_text_yoff", SELFBLUR_TEXT_YOFF_DEFAULT)
    return (
        "🔤 *Text Settings*\n\n"
        f"🔠 Size: `{font_size}px`\n"
        f"🎨 Colour: {COLOR_LABELS.get(text_color_key, '—')}\n"
        f"🖊 Stroke: `{stroke_width:g}px`\n"
        f"↕️ Position: `{yoff:+d}px`\n\n"
        "👆 Preview eka udinma penei - adjust karala, 🔙 Back karanna 👇"
    )


def _selfblur_video_menu_text(data: dict) -> str:
    blur_type = data.get("selfblur_blur_type", SELFBLUR_BLUR_TYPE_DEFAULT)
    return (
        "🎬 *Video Settings*\n\n"
        f"🌫 Blur strength: `{data.get('selfblur_blur_px', SELFBLUR_BLUR_DEFAULT)}`\n"
        f"🌫 Blur type: {BLUR_TYPE_LABELS.get(blur_type, blur_type)}\n"
        f"🔍 Size: `{data.get('selfblur_fg_pct', SELFBLUR_FG_PCT_DEFAULT)}%`\n"
        f"↕️ Position: `{data.get('selfblur_fg_yoff', SELFBLUR_YOFF_DEFAULT):+d}%`\n"
        f"⬛ Overlay: `{data.get('selfblur_overlay_opacity', SELFBLUR_OVERLAY_OPACITY_DEFAULT)}%`\n\n"
        "👆 Preview eka udinma penei - adjust karala, 🔙 Back karanna 👇"
    )


def _selfblur_video_keyboard(data: dict) -> InlineKeyboardMarkup:
    blur_type = data.get("selfblur_blur_type", SELFBLUR_BLUR_TYPE_DEFAULT)
    rows = [
        [
            InlineKeyboardButton("➖", callback_data="sb_blur_dec"),
            InlineKeyboardButton(f"🌫 Blur: {data.get('selfblur_blur_px', SELFBLUR_BLUR_DEFAULT)}", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_blur_inc"),
        ],
        [InlineKeyboardButton(BLUR_TYPE_LABELS.get(blur_type, "🌫 Blur type"), callback_data="sb_blur_type_toggle")],
        [
            InlineKeyboardButton("➖", callback_data="sb_size_dec"),
            InlineKeyboardButton(f"🔍 Size: {data.get('selfblur_fg_pct', SELFBLUR_FG_PCT_DEFAULT)}%", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_size_inc"),
        ],
        [
            InlineKeyboardButton("⬆️ Up", callback_data="sb_pos_up"),
            InlineKeyboardButton(f"↕️ {data.get('selfblur_fg_yoff', SELFBLUR_YOFF_DEFAULT):+d}%", callback_data="sb_noop"),
            InlineKeyboardButton("⬇️ Down", callback_data="sb_pos_down"),
        ],
        [
            InlineKeyboardButton("➖", callback_data="sb_overlay_dec"),
            InlineKeyboardButton(
                f"⬛ Overlay: {data.get('selfblur_overlay_opacity', SELFBLUR_OVERLAY_OPACITY_DEFAULT)}%",
                callback_data="sb_noop",
            ),
            InlineKeyboardButton("➕", callback_data="sb_overlay_inc"),
        ],
        [InlineKeyboardButton("🔙 Back", callback_data="sb_video_back")],
    ]
    return InlineKeyboardMarkup(rows)


def _selfblur_effects_menu_text(data: dict) -> str:
    chromatic_on = bool(data.get("selfblur_chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT))
    vhs_on = bool(data.get("selfblur_vhs_effect", VHS_EFFECT_DEFAULT))
    return (
        "✨ *Effects Settings*\n\n"
        f"🌈 Chromatic aberration: {'ON (' + str(data.get('selfblur_chromatic_shift', CHROMATIC_SHIFT_DEFAULT)) + 'px)' if chromatic_on else 'OFF'}\n"
        f"📺 VHS effect: {'ON (' + str(data.get('selfblur_vhs_strength', VHS_STRENGTH_DEFAULT)) + '%)' if vhs_on else 'OFF'}\n"
        f"⬛ Intro fade: `{data.get('selfblur_intro_black_seconds', INTRO_BLACK_SECONDS_DEFAULT)}s`\n\n"
        "👆 Preview eka udinma penei - adjust karala, 🔙 Back karanna 👇"
    )


def _selfblur_effects_keyboard(data: dict) -> InlineKeyboardMarkup:
    chromatic_on = bool(data.get("selfblur_chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT))
    vhs_on = bool(data.get("selfblur_vhs_effect", VHS_EFFECT_DEFAULT))
    rows = [
        [InlineKeyboardButton("🌈 Chromatic: ON" if chromatic_on else "🌈 Chromatic: OFF", callback_data="sb_chromatic_toggle")],
    ]
    if chromatic_on:
        rows.append([
            InlineKeyboardButton("➖ Shift", callback_data="sb_chromatic_dec"),
            InlineKeyboardButton(f"🌈 {data.get('selfblur_chromatic_shift', CHROMATIC_SHIFT_DEFAULT)}px", callback_data="sb_noop"),
            InlineKeyboardButton("➕ Shift", callback_data="sb_chromatic_inc"),
        ])
    rows.append([InlineKeyboardButton("📺 VHS: ON" if vhs_on else "📺 VHS: OFF", callback_data="sb_vhs_toggle")])
    if vhs_on:
        rows.append([
            InlineKeyboardButton("➖ Grain", callback_data="sb_vhs_dec"),
            InlineKeyboardButton(f"📺 {data.get('selfblur_vhs_strength', VHS_STRENGTH_DEFAULT)}%", callback_data="sb_noop"),
            InlineKeyboardButton("➕ Grain", callback_data="sb_vhs_inc"),
        ])
    rows.append([
        InlineKeyboardButton("➖", callback_data="sb_intro_dec"),
        InlineKeyboardButton(f"⬛ Intro: {data.get('selfblur_intro_black_seconds', INTRO_BLACK_SECONDS_DEFAULT)}s", callback_data="sb_noop"),
        InlineKeyboardButton("➕", callback_data="sb_intro_inc"),
    ])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="sb_effects_back")])
    return InlineKeyboardMarkup(rows)


def _selfblur_keyboard(data: dict) -> InlineKeyboardMarkup:
    wm_on = bool(data.get("selfblur_watermark_bytes"))
    logo_on = bool(data.get("selfblur_logo_kind") and data.get("selfblur_logo_value"))
    
    rows = [
        [InlineKeyboardButton(f"🖼 Background: {_selfblur_bg_label(data)}", callback_data="sb_bg_menu")],
        [
            InlineKeyboardButton("🔳 Layout: Meme" if data.get("selfblur_layout", "standard") == "meme" else "🔳 Layout: Standard", callback_data="sb_layout_toggle")
        ],
        [InlineKeyboardButton("🎬 Video Settings", callback_data="sb_video_menu")],
        [
            InlineKeyboardButton("🔤 Text Settings", callback_data="sb_text_menu"),
            InlineKeyboardButton("😀 Emoji Settings", callback_data="sb_emoji_menu")
        ],
        [InlineKeyboardButton("🎧 Audio", callback_data="sb_audio_menu")],
        [
            InlineKeyboardButton(
                "🏷 Watermark Settings ✅" if wm_on else "🏷 Watermark Settings",
                callback_data="sb_wm_menu",
            ),
            InlineKeyboardButton(
                "🖼 Logo Settings ✅" if logo_on else "🖼 Logo Settings",
                callback_data="sb_logo_menu",
            )
        ],
        [InlineKeyboardButton("✨ Effects", callback_data="sb_effects_menu")],
        [InlineKeyboardButton("📁 Templates", callback_data="sb_tpl_menu")],
        [InlineKeyboardButton("✅ Render Video", callback_data="sb_render")],
        [InlineKeyboardButton("❌ Cancel", callback_data="sb_cancel")],
    ]
    return InlineKeyboardMarkup(rows)


def _selfblur_text_keyboard(data: dict) -> InlineKeyboardMarkup:
    """"🔤 Text Settings" sub-menu eka (main /newpost text_keyboard() eke
    pattern ekama) - size, colour, stroke (+ stroke colour), position (top/
    bottom preset + pixel-level fine-tune) okkoma methanma."""
    text_color_key = next(
        (k for k, v in COLORS.items() if v == data.get("selfblur_text_color", SELFBLUR_TEXT_COLOR_DEFAULT)), None
    )
    stroke_width = data.get("selfblur_stroke_width", STROKE_WIDTH_DEFAULT)
    stroke_color_key = next(
        (k for k, v in COLORS.items() if v == data.get("selfblur_stroke_color", STROKE_COLOR_DEFAULT)), None
    )
    rows = [
        [InlineKeyboardButton("✏️ Edit Text", callback_data="sb_text_edit")],
        [
            InlineKeyboardButton("➖", callback_data="sb_font_dec"),
            InlineKeyboardButton(f"🔤 Size: {data.get('selfblur_font_size', SELFBLUR_FONT_SIZE_DEFAULT)}px", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_font_inc"),
        ],
    ]
    color_buttons = [
        InlineKeyboardButton(
            ("✅ " if text_color_key == key else "") + label,
            callback_data=f"sb_textcolor_{key}",
        )
        for key, label in COLOR_LABELS.items()
    ]
    rows.append(color_buttons[:3])
    rows.append(color_buttons[3:])
    rows.append([
        InlineKeyboardButton("➖ Stroke", callback_data="sb_stroke_dec"),
        InlineKeyboardButton(f"🖊 {stroke_width:g}px", callback_data="sb_noop"),
        InlineKeyboardButton("➕ Stroke", callback_data="sb_stroke_inc"),
    ])
    if stroke_width > 0:
        stroke_buttons = [
            InlineKeyboardButton(
                ("✅ " if stroke_color_key == key else "") + label,
                callback_data=f"sb_strokecolor_{key}",
            )
            for key, label in COLOR_LABELS.items()
        ]
        rows.append(stroke_buttons[:3])
        rows.append(stroke_buttons[3:])
    # Meme mode: sudu box athule text eka px walin up/down adjust karanna
    # Standard mode: Top/Bottom presets + pixel nudge
    _layout_mode = data.get("selfblur_layout", "standard")
    if _layout_mode == "meme":
        _myoff = data.get("selfblur_meme_text_yoff", MEME_TEXT_YOFF_DEFAULT)
        rows.append([
            InlineKeyboardButton("⬆️ Text Up", callback_data="sb_meme_text_up"),
            InlineKeyboardButton(f"📍 {_myoff:+d}px", callback_data="sb_noop"),
            InlineKeyboardButton("⬇️ Text Down", callback_data="sb_meme_text_down"),
        ])
    else:
        rows.append([
            InlineKeyboardButton("⬆️ Top", callback_data="sb_text_top"),
            InlineKeyboardButton("⬇️ Bottom", callback_data="sb_text_bottom"),
        ])
        rows.append([
            InlineKeyboardButton("⬆️ Nudge up", callback_data="sb_text_up"),
            InlineKeyboardButton(f"↕️ {data.get('selfblur_text_yoff', SELFBLUR_TEXT_YOFF_DEFAULT)}px", callback_data="sb_noop"),
            InlineKeyboardButton("⬇️ Nudge down", callback_data="sb_text_down"),
        ])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="sb_text_back")])
    return InlineKeyboardMarkup(rows)


def _selfblur_emoji_menu_text(data: dict) -> str:
    yoff = data.get("selfblur_emoji_yoff", EMOJI_OFFSET_DEFAULT)
    return (
        "😀 *Emoji Settings*\n\n"
        f"😀 Size: `{data.get('selfblur_emoji_size', EMOJI_SIZE_DEFAULT)}px`\n"
        f"↕️ Position: `{yoff:+d}px`\n\n"
        "Text eke type kala real emoji (apple-style, text ekata yatin, gap ekak "
        "nathuwa) tikaka size eka + udata/pahalata (px) position eka methanin "
        "control karanna. 🔙 Back karaddi, preview eka aluthen render wenawa."
    )


def _selfblur_emoji_keyboard(data: dict) -> InlineKeyboardMarkup:
    """"😀 Emoji Settings" sub-menu eka - size +/- eka, udata/pahalata px nudge
    eka (⬆️/⬇️ + manual "✏️ Type px" button ekakin exact value ekak type
    karanna puluwan), reset + back."""
    yoff = data.get("selfblur_emoji_yoff", EMOJI_OFFSET_DEFAULT)
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("➖", callback_data="sb_emoji_dec"),
            InlineKeyboardButton(f"😀 Size: {data.get('selfblur_emoji_size', EMOJI_SIZE_DEFAULT)}px", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_emoji_inc"),
        ],
        [
            InlineKeyboardButton("⬆️ Up", callback_data="sb_emoji_up"),
            InlineKeyboardButton(f"↕️ {yoff:+d}px", callback_data="sb_noop"),
            InlineKeyboardButton("⬇️ Down", callback_data="sb_emoji_down"),
        ],
        [InlineKeyboardButton("✏️ Type exact px value", callback_data="sb_manual_emoji_yoff")],
        [InlineKeyboardButton("♻️ Reset", callback_data="sb_emoji_reset")],
        [InlineKeyboardButton("🔙 Back", callback_data="sb_emoji_back")],
    ])


def _selfblur_watermark_menu_text(data: dict) -> str:
    """"🏷 Watermark Settings" sub-menu eka - scrolling watermark eka (edge
    ekakin anith ekata continuously loop wena eka) e udinma control karana
    text eka. Watermark ekak set karala nathnam, upload karanna witharai
    button ekak penei."""
    wm_on = bool(data.get("selfblur_watermark_bytes"))
    if not wm_on:
        return (
            "🏷 *Scrolling Watermark*\n\n"
            "Danata watermark ekak nehe. Video eke pættak indan anith pættata "
            "continuously scroll wena (pirated-video-style) watermark ekak "
            "danna, image eka upload karanna 👇"
        )
    direction_label = WATERMARK_DIRECTION_LABELS.get(
        data.get("selfblur_watermark_direction", WATERMARK_DIRECTION_DEFAULT), "↕️ Direction"
    )
    side_label = WATERMARK_SIDE_LABELS.get(
        data.get("selfblur_watermark_side", WATERMARK_SIDE_DEFAULT), "↔️ Side"
    )
    return (
        "🏷 *Scrolling Watermark*\n\n"
        f"🎚 Opacity: `{data.get('selfblur_watermark_opacity', WATERMARK_OPACITY_DEFAULT)}%`\n"
        f"📐 Size: `{data.get('selfblur_watermark_scale', WATERMARK_SCALE_DEFAULT)}%`\n"
        f"🏃 Speed: `{data.get('selfblur_watermark_speed', WATERMARK_SPEED_DEFAULT)} px/s`\n"
        f"↕️ Direction: {direction_label}\n"
        f"↔️ Side: {side_label}\n\n"
        "👆 Preview eke position/size/opacity eka penei - scroll animation eka "
        "+ speed eka nam 'Render Video' karapu passe witharai penenne "
        "(static photo ekaka animation ekak pennanna bari nisa).\n\n"
        "🔙 Back karaddi preview eka aluthen render wenawa."
    )


def _selfblur_watermark_keyboard(data: dict) -> InlineKeyboardMarkup:
    wm_on = bool(data.get("selfblur_watermark_bytes"))
    if not wm_on:
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("🖼 Add Watermark Image", callback_data="sb_wm_add")],
            [InlineKeyboardButton("📝 Add Watermark Text", callback_data="sb_wm_text")],
            [InlineKeyboardButton("🔙 Back", callback_data="sb_wm_back")],
        ])
    direction = data.get("selfblur_watermark_direction", WATERMARK_DIRECTION_DEFAULT)
    side = data.get("selfblur_watermark_side", WATERMARK_SIDE_DEFAULT)
    direction_label = WATERMARK_DIRECTION_LABELS.get(direction, "↕️ Direction")
    rows = [
        [
            InlineKeyboardButton("➖", callback_data="sb_wm_opacity_dec"),
            InlineKeyboardButton(f"🎚 Opacity: {data.get('selfblur_watermark_opacity', WATERMARK_OPACITY_DEFAULT)}%", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_wm_opacity_inc"),
        ],
        [InlineKeyboardButton("✏️ Type opacity %", callback_data="sb_manual_wm_opacity")],
        [
            InlineKeyboardButton("➖", callback_data="sb_wm_scale_dec"),
            InlineKeyboardButton(f"📐 Size: {data.get('selfblur_watermark_scale', WATERMARK_SCALE_DEFAULT)}%", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_wm_scale_inc"),
        ],
        [InlineKeyboardButton("✏️ Type size %", callback_data="sb_manual_wm_scale")],
        [
            InlineKeyboardButton("➖", callback_data="sb_wm_speed_dec"),
            InlineKeyboardButton(f"🏃 Speed: {data.get('selfblur_watermark_speed', WATERMARK_SPEED_DEFAULT)}", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_wm_speed_inc"),
        ],
        [InlineKeyboardButton("✏️ Type speed", callback_data="sb_manual_wm_speed")],
        [InlineKeyboardButton(direction_label, callback_data="sb_wm_direction_toggle")],
        [InlineKeyboardButton(WATERMARK_SIDE_LABELS.get(side, "↔️ Side"), callback_data="sb_wm_side_toggle")],
        [InlineKeyboardButton("🖼 Change Image", callback_data="sb_wm_add")],
        [InlineKeyboardButton("🗑 Remove Watermark", callback_data="sb_wm_remove")],
        [InlineKeyboardButton("🔙 Back", callback_data="sb_wm_back")],
    ]
    return InlineKeyboardMarkup(rows)


def _selfblur_logo_menu_text(data: dict) -> str:
    """"🖼 Logo Settings" sub-menu eka - scrolling watermark eken sampurnayenma
    wenama, video eke CENTER ekata static widiyata danna logo ekak (opacity +
    udata/pahalata position dekama control karanna puluwan)."""
    logo_on = bool(data.get("selfblur_logo_kind") and data.get("selfblur_logo_value"))
    if not logo_on:
        return (
            "🖼 *Center Logo*\n\n"
            "Danata logo ekak nehe - scrolling watermark eken wenama, video eke "
            "center ekata STATIC widiyata danna logo/brand image ekak upload "
            "karanna, nathnam text logo ekak type karanna 👇"
        )
    logo_kind = data.get("selfblur_logo_kind")
    kind_label = "🖼 Image logo" if logo_kind == "image" else "📝 Text logo"
    return (
        "🖼 *Center Logo*\n\n"
        f"Type: {kind_label}\n"
        f"📐 Size: `{data.get('selfblur_logo_scale', LOGO_SCALE_DEFAULT)}%`\n"
        f"🎚 Opacity: `{data.get('selfblur_logo_opacity', LOGO_OPACITY_DEFAULT)}%`\n"
        f"↕️ Position: `{data.get('selfblur_logo_offset_bottom', LOGO_OFFSET_DEFAULT)}px` (canvas bottom ekedin)\n\n"
        "👆 Preview eka udinma penei - adjust karala, 🔙 Back karanna 👇"
    )


def _selfblur_logo_keyboard(data: dict) -> InlineKeyboardMarkup:
    logo_on = bool(data.get("selfblur_logo_kind") and data.get("selfblur_logo_value"))
    if not logo_on:
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("🖼 Add Logo Image", callback_data="sb_logo_add")],
            [InlineKeyboardButton("📝 Add Logo Text", callback_data="sb_logo_text")],
            [InlineKeyboardButton("🔙 Back", callback_data="sb_logo_back")],
        ])
    logo_kind = data.get("selfblur_logo_kind")
    rows = [
        [
            InlineKeyboardButton("➖", callback_data="sb_logo_scale_dec"),
            InlineKeyboardButton(f"📐 Size: {data.get('selfblur_logo_scale', LOGO_SCALE_DEFAULT)}%", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_logo_scale_inc"),
        ],
        [InlineKeyboardButton("✏️ Type size %", callback_data="sb_manual_logo_scale")],
        [
            InlineKeyboardButton("➖", callback_data="sb_logo_opacity_dec"),
            InlineKeyboardButton(f"🎚 Opacity: {data.get('selfblur_logo_opacity', LOGO_OPACITY_DEFAULT)}%", callback_data="sb_noop"),
            InlineKeyboardButton("➕", callback_data="sb_logo_opacity_inc"),
        ],
        [InlineKeyboardButton("✏️ Type opacity %", callback_data="sb_manual_logo_opacity")],
        [
            InlineKeyboardButton("⬆️ Up", callback_data="sb_logo_pos_up"),
            InlineKeyboardButton(f"↕️ {data.get('selfblur_logo_offset_bottom', LOGO_OFFSET_DEFAULT)}px", callback_data="sb_noop"),
            InlineKeyboardButton("⬇️ Down", callback_data="sb_logo_pos_down"),
        ],
        [InlineKeyboardButton("✏️ Type position px", callback_data="sb_manual_logo_offset")],
    ]
    if logo_kind == "image":
        rows.append([InlineKeyboardButton("🖼 Change Image", callback_data="sb_logo_add")])
        rows.append([InlineKeyboardButton("📝 Switch to Text Logo", callback_data="sb_logo_text")])
    else:
        rows.append([InlineKeyboardButton("📝 Edit Text Logo", callback_data="sb_logo_text")])
        rows.append([InlineKeyboardButton("🖼 Switch to Image Logo", callback_data="sb_logo_add")])
    rows.append([InlineKeyboardButton("🗑 Remove Logo", callback_data="sb_logo_remove")])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="sb_logo_back")])
    return InlineKeyboardMarkup(rows)


def _selfblur_bg_menu_text(data: dict) -> str:
    """"🖼 Background" sub-menu eka - danata "blur" (source video eken auto
    generate karana blur eka) witharak thibba background eka, methanin
    solid color ekakට, custom image ekakට, hari custom video ekakට wenas
    karaganna puluwan. Center eke penena "fg" (user ge clear video eka)
    kohomath touch wenne na - background layer eka witharai wenas wenne."""
    return (
        "🖼 *Background*\n\n"
        f"Danata: {_selfblur_bg_label(data)}\n\n"
        "🌫 Blurred video - default eka, video ekemma blur karapu copy ekak\n"
        "🎨 Solid Color - black/white/yellow/red/blue (stock colors)\n"
        "🖼 Custom Image - danata upload karapu image ekak\n"
        "🎥 Custom Video - danata upload karapu wenama video ekak (loop wela)\n\n"
        "Image/Video walata 🌫 Blur eka thawath ON karaganna puluwan."
    )


def _selfblur_bg_keyboard(data: dict) -> InlineKeyboardMarkup:
    kind = data.get("selfblur_bg_kind", SELFBLUR_BG_KIND_DEFAULT)
    rows = [
        [InlineKeyboardButton(
            ("✅ " if kind == "blur" else "") + "🌫 Blurred Video (auto)", callback_data="sb_bg_blur",
        )],
        [InlineKeyboardButton(
            ("✅ " if kind == "color" else "") + "🎨 Solid Color", callback_data="sb_bg_color_menu",
        )],
        [InlineKeyboardButton(
            ("✅ " if kind == "image" else "") + "🖼 Custom Image", callback_data="sb_bg_image_add",
        )],
        [InlineKeyboardButton(
            ("✅ " if kind == "video" else "") + "🎥 Custom Video", callback_data="sb_bg_video_add",
        )],
    ]
    if kind in ("image", "video"):
        blur_on = data.get("selfblur_bg_blur_enabled", True)
        rows.append([InlineKeyboardButton(
            "🌫 Blur effect: ON" if blur_on else "🌫 Blur effect: OFF", callback_data="sb_bg_blur_toggle",
        )])
        rows.append([InlineKeyboardButton(
            "🖼 Change Image" if kind == "image" else "🎥 Change Video",
            callback_data="sb_bg_image_add" if kind == "image" else "sb_bg_video_add",
        )])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="sb_bg_back")])
    return InlineKeyboardMarkup(rows)


def _selfblur_bg_color_keyboard(data: dict) -> InlineKeyboardMarkup:
    """🎨 Solid Color eke stock color swatches - text color picker ekema
    COLORS dict eka (yellow/red/blue/white/black) reuse karanawa."""
    cur = data.get("selfblur_bg_color", SELFBLUR_BG_COLOR_DEFAULT)
    rows = []
    row = []
    for key, hexval in COLORS.items():
        mark = "✅ " if hexval.lower() == (cur or "").lower() else ""
        row.append(InlineKeyboardButton(f"{mark}{key.title()}", callback_data=f"sb_bgcolor_{key}"))
        if len(row) == 3:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="sb_bg_menu")])
    return InlineKeyboardMarkup(rows)


def _selfblur_tpl_menu_text(data: dict) -> str:
    store_key = _tpl_store_key(data)
    templates = data.get(store_key, {}) or {}
    active = data.get("selfblur_active_template_name")
    layout_mode = data.get("selfblur_layout", "standard")
    mode_label = "🎭 Meme" if layout_mode == "meme" else "🌫 Self-Blur"
    lines = [f"📁 *{mode_label} Templates*\n"]
    if active:
        lines.append(f"✅ Active template: `{active}`\n")
    if templates:
        lines.append(f"Save karapu templates ({len(templates)}/{MAX_TEMPLATES_PER_USER}):")
        for name in templates:
            lines.append(f"• `{name}`")
    else:
        lines.append("Danata save kala templates nehe.")
    lines.append(
        "\n🖼 logo, ↕️ text position, 🏷 scrolling watermark + position, "
        "🔤 text size/colors, 🔍 center video size - okkoma methanin "
        "template ekaka save karagena, ayet video ekakata load karaganna "
        "puluwan.\n\n💡 Meme + Standard layouts separate templates walata save wenawa."
    )
    return "\n".join(lines)


def _selfblur_tpl_keyboard(data: dict) -> InlineKeyboardMarkup:
    store_key = _tpl_store_key(data)
    templates = data.get(store_key, {}) or {}
    active = data.get("selfblur_active_template_name")
    rows = [[InlineKeyboardButton("💾 Save as new template", callback_data="sb_tpl_save")]]
    # Active template thibba nam 'Update' button eka pennanna
    if active and active in templates:
        rows.append([InlineKeyboardButton(
            f"🔄 Update '{active}'", callback_data="sb_tpl_update"
        )])
    for name in templates:
        rows.append([
            InlineKeyboardButton(f"📥 {name}", callback_data=f"sb_tpl_load_{name}"),
            InlineKeyboardButton("🗑", callback_data=f"sb_tpl_delete_{name}"),
        ])
    rows.append([InlineKeyboardButton("🔙 Back", callback_data="sb_tpl_back")])
    return InlineKeyboardMarkup(rows)


# ---- 📁 Templates: hama "adjust-able" setting ekakma bundle karana list eka
# - "💾 Save as Template" click kalama methanin listed field tikama danata
# user data eken copy karala save karanawa, "📥 Load" kalama ayet methanin
# listed field tikama apply karanawa. Aluth setting ekak add kaloth,
# methanatath ekathu karanna one (nathnam eka template eke save wenne na).
SELFBLUR_TEMPLATE_FIELDS = [
    "selfblur_blur_px", "selfblur_blur_type", "selfblur_fg_pct", "selfblur_fg_yoff",
    "selfblur_overlay_opacity", "selfblur_font_size", "selfblur_text_color",
    "selfblur_stroke_width", "selfblur_stroke_color", "selfblur_text_yoff",
    "selfblur_emoji_size", "selfblur_emoji_yoff",
    "selfblur_watermark_opacity", "selfblur_watermark_scale", "selfblur_watermark_speed",
    "selfblur_watermark_direction", "selfblur_watermark_side", "selfblur_watermark_bytes",
    "selfblur_logo_kind", "selfblur_logo_value", "selfblur_logo_scale",
    "selfblur_logo_offset_bottom", "selfblur_logo_opacity",
    "selfblur_chromatic_aberration", "selfblur_chromatic_shift",
    "selfblur_vhs_effect", "selfblur_vhs_strength", "selfblur_intro_black_seconds",
    "selfblur_bg_kind", "selfblur_bg_color", "selfblur_bg_blur_enabled",
    # layout_mode eka okkoma save wenawa - load kalama correct type eka restore wenawa
    "selfblur_layout", "selfblur_meme_text_yoff",
]


def _tpl_store_key(data: dict) -> str:
    """Current layout_mode eka anuwa correct template store key eka return.
    Meme templates + Standard templates separate dict walata save wenawa."""
    return "selfblur_templates_meme" if data.get("selfblur_layout") == "meme" else "selfblur_templates_standard"


async def _flush_persistence(context: ContextTypes.DEFAULT_TYPE):
    """PicklePersistence eka default eken disk ekata write wenne background
    job ekakin, 60 seconds ekakata parak witharai (BasePersistence's
    update_interval=60 default eka). E kiyanne template ekak save/update/
    delete karapu WELAWEMA bot eka crash una or force-restart (kill -9,
    VPS panel restart, OOM) una nam, e last 60s athule change eka disk
    ekata write wela nathuwama nethiwela yanawa - PTB application.shutdown()
    eken witharai graceful ekak welawata final flush ekak karanne (SIGTERM/
    Ctrl+C wage 'clean' stop ekaka). Ithin critical write ekak (template
    save/update/delete) welavata methanin explicit widiyata immediately
    disk ekata force-write karanawa - ee window eka sampurnayenma vahagannawa."""
    try:
        await context.application.update_persistence()
    except Exception:
        logger.exception("selfblur template persistence flush eka fail una")


# "✏️ Type value" buttons (emoji/watermark/logo sub-menus) walata - target
# field eka anuwa (data_key, min/max, default, unit label, prompt text, e
# field eka thiyena sub-menu eka monakda) define karana table eka. Methanin
# witharai referring karala, ekma generic handler ekakinma (receive_
# selfblur_manual_value) field godak (emoji/watermark/logo) support
# karanawa - hama field ekatama wenama handler ekak liyanna one na.
SELFBLUR_MANUAL_TARGETS = {
    "emoji_yoff": {
        "data_key": "selfblur_emoji_yoff", "min": EMOJI_OFFSET_MIN, "max": EMOJI_OFFSET_MAX,
        "default": EMOJI_OFFSET_DEFAULT, "unit": "px",
        "prompt": "😀 Emoji position eka type karanna (px - negative = udata, positive = pahalata)",
        "menu": "emoji",
    },
    "wm_opacity": {
        "data_key": "selfblur_watermark_opacity", "min": WATERMARK_OPACITY_MIN, "max": WATERMARK_OPACITY_MAX,
        "default": WATERMARK_OPACITY_DEFAULT, "unit": "%",
        "prompt": "🏷 Watermark opacity eka type karanna (%)",
        "menu": "wm",
    },
    "wm_scale": {
        "data_key": "selfblur_watermark_scale", "min": WATERMARK_SCALE_MIN, "max": WATERMARK_SCALE_MAX,
        "default": WATERMARK_SCALE_DEFAULT, "unit": "%",
        "prompt": "🏷 Watermark size eka type karanna (%, canvas width ekata relative)",
        "menu": "wm",
    },
    "wm_speed": {
        "data_key": "selfblur_watermark_speed", "min": WATERMARK_SPEED_MIN, "max": WATERMARK_SPEED_MAX,
        "default": WATERMARK_SPEED_DEFAULT, "unit": "px/s",
        "prompt": "🏷 Watermark scroll speed eka type karanna (px/sec)",
        "menu": "wm",
    },
    "logo_scale": {
        "data_key": "selfblur_logo_scale", "min": LOGO_SCALE_MIN, "max": LOGO_SCALE_MAX,
        "default": LOGO_SCALE_DEFAULT, "unit": "%",
        "prompt": "🖼 Logo size eka type karanna (%)",
        "menu": "logo",
    },
    "logo_opacity": {
        "data_key": "selfblur_logo_opacity", "min": LOGO_OPACITY_MIN, "max": LOGO_OPACITY_MAX,
        "default": LOGO_OPACITY_DEFAULT, "unit": "%",
        "prompt": "🖼 Logo opacity eka type karanna (%)",
        "menu": "logo",
    },
    "logo_offset": {
        "data_key": "selfblur_logo_offset_bottom", "min": LOGO_OFFSET_MIN, "max": LOGO_OFFSET_MAX,
        "default": LOGO_OFFSET_DEFAULT, "unit": "px",
        "prompt": "🖼 Logo position eka type karanna (px - canvas bottom ekedin gap eka)",
        "menu": "logo",
    },
}


def _selfblur_manual_target_menu(menu: str, data: dict) -> tuple[str, InlineKeyboardMarkup]:
    """SELFBLUR_MANUAL_TARGETS eke "menu" key eka anuwa, e field eka thiyena
    sub-menu ekema (text, keyboard) pair eka return karanawa - manual value
    ekak type kara ivara welata, e sub-menu ekatama aye yanna."""
    if menu == "emoji":
        return _selfblur_emoji_menu_text(data), _selfblur_emoji_keyboard(data)
    if menu == "wm":
        return _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data)
    if menu == "logo":
        return _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data)
    return _selfblur_menu_text(data), _selfblur_keyboard(data)


async def _selfblur_build_text_overlay_png(context: ContextTypes.DEFAULT_TYPE, canvas_w: int, canvas_h: int) -> bytes | None:
    """User type kala caption/emoji text eka (thibba nam) - main post-creator
    ekema generate_image() function eka reuse karala, transparent PNG ekak
    (canvas size ekama) widiyata render karanawa. ##bold## //italic//
    ""header"" ^^highlight^^ syntax eka okkoma methanin support wenawa,
    danata thiyena text ekema settings walata.

    IMPORTANT: canvas_h methanata denna one FULL final canvas height eka
    (meme layout ekedi MEME_BOX_H+MEME_VIDEO_H, box witharak nemei) - ffmpeg
    eke final composited canvas ekama size eka. Text eka witharak (meme mode
    ekedi) 300px box ekatama "text_area_height" param eken confine karanawa,
    logo eka FULL canvas_h ekatama relative widiyata position wenawa - ehema
    nathnam logo eka box eke pita giya welawakadi (overlay png eka box
    height ekatama witharak generate una nam) invisible/clipped wenawa.

    User type kala real Unicode emoji (thibba nam) text eken methanin
    extract karala, main post-creator flow ekema widiyata wenama "emojis"
    param ekakin generate_image() ekata danawa - eken e emoji tika apple-style
    (emojicdn.elk.sh) images widiyata render wenawa, text eke embedded widiyata
    browser eke default emoji font eken render unoth wage nemei."""
    data = context.user_data
    raw_text = data.get("selfblur_text")
    has_logo = bool(data.get("selfblur_logo_kind") and data.get("selfblur_logo_value"))
    if not raw_text and not has_logo:
        return None
    browser = context.application.bot_data["browser"]
    header_text, body_text = split_header_text(raw_text or "")
    body_text, emoji_chars = extract_pictographic_emoji(body_text)
    layout_mode = data.get("selfblur_layout", "standard")
    # BUG FIX: meke transparent_bg eka kalinma "standard" layout ekatama witharak
    # True karala tibba (meme mode ekedi False, bg_color=#ffffff opaque widiyata).
    # Meka kalinma awlak wunne na, mokada e welawata meme mode ekedi mee text PNG
    # eka generate karala tibbe box height ekatama witharai (300px) - opaque white
    # unath eka ffmpeg overlay ekedi box area ekatama witharai crop wela thibba.
    # Ithin dan (logo clip bug eka fix karapu passe) mee PNG eka FULL 1080px
    # canvas ekatama generate wenawa - eth eka thawamath opaque white nam,
    # box height eken pahalata (780px video area ekatama) full opaque white
    # ekak overlay wela, yatin thiyena selfblur video eka sampurnayenma vaseema
    # yanawa (screenshot eke penuna widiyatama - video ekma penne na). Sudu
    # box eka danatamath ffmpeg pad filter eken (_selfblur_bg_fg_filter, color=white)
    # danawa nisa, mee text layer eka layout mode ekka related nathuwama
    # HAMADAMA transparent widiyata thiyenna one - text/logo pixels witharai
    # opaque wenna one, ithiri canvas eka (box athule th, video area eth) okkoma
    # transparent widiyata thibba one.
    transparent_bg = True
    _bg_color = "#ffffff" if layout_mode == "meme" else "#000000"
    _text_color = data.get("selfblur_text_color", SELFBLUR_TEXT_COLOR_DEFAULT) if layout_mode == "standard" else "#000000"

    _yoff = data.get("selfblur_text_yoff", SELFBLUR_TEXT_YOFF_DEFAULT)
    if layout_mode == "meme":
        # sudu box athule witharai (MEME_TEXT_YOFF_MIN..MAX clamp)
        _yoff = max(MEME_TEXT_YOFF_MIN, min(MEME_TEXT_YOFF_MAX,
                    data.get("selfblur_meme_text_yoff", MEME_TEXT_YOFF_DEFAULT)))

    image_buf = await generate_image(
        browser,
        body_text,
        emoji_chars,   # apple-style CDN emoji row - main flow ekema pattern eka
        data.get("selfblur_font_size", SELFBLUR_FONT_SIZE_DEFAULT),
        data.get("selfblur_emoji_size", EMOJI_SIZE_DEFAULT),
        _text_color,
        transparent=transparent_bg,
        bg_color=_bg_color,
        canvas_width=canvas_w,
        canvas_height=canvas_h,
        header_text=header_text,
        text_offset_y=_yoff,
        stroke_width=data.get("selfblur_stroke_width", STROKE_WIDTH_DEFAULT),
        stroke_color=data.get("selfblur_stroke_color", STROKE_COLOR_DEFAULT),
        emoji_offset_y=data.get("selfblur_emoji_yoff", EMOJI_OFFSET_DEFAULT),
        logo_kind=data.get("selfblur_logo_kind"),
        logo_value=data.get("selfblur_logo_value"),
        logo_scale=data.get("selfblur_logo_scale", LOGO_SCALE_DEFAULT),
        # max(LOGO_OFFSET_MIN, ...) - kalin -300 dakwa negative values allow
        # una nisa save wela tibbe pura data (session eke or old template
        # ekaka) ekka thawamath negative value ekak thiyenna puluwan; e
        # eka clamp nokarama use kaloth logo eka canvas boundary eken pita
        # gihin invisible wenawa (LOGO_OFFSET_MIN eke comment eka balanna).
        # Methanin clamp karama, dan LOGO_OFFSET_MIN eka 0 unath, parana
        # negative-value data ekath render welata safe widiyata self-heal wenawa.
        logo_offset_bottom=max(LOGO_OFFSET_MIN, data.get("selfblur_logo_offset_bottom", LOGO_OFFSET_DEFAULT)),
        logo_opacity=data.get("selfblur_logo_opacity", LOGO_OPACITY_DEFAULT),
        # Meme mode: autofit=True ekak dala 300px box eke inside fit wena
        # widiyata text eka shrink karanawa (260px usable height, 1000px width).
        # Standard mode: autofit=False - canvas eka loku (video height ekama)
        # nisa text eka ekenma fit wenawa.
        autofit=(layout_mode == "meme"),
        autofit_max_height=(260 if layout_mode == "meme" else None),
        autofit_max_width=(1000 if layout_mode == "meme" else None),
        # BUG FIX: kalinma meme mode ekedi canvas_h eka methanata MEME_BOX_H
        # (300px) witharak danapu nisa, e 300px-tala PNG eka thamai (logo eka
        # ekathuwama) ffmpeg eken final canvas eke (1080px) top ekata overlay
        # karanne - eken logo eka 300px box eken pita monaha unath (offset
        # eken "down" karoth wath) capture wenne ma na (screenshot viewport
        # eka ma 300px witharai), invisible/clipped widiyata penuna. Dan
        # caller eken FULL canvas height eka (canvas_h) methanata denawa, e
        # widiyata logo eka canvas boundary eka ma athule witharai clip
        # wenne - text eka witharak "text_area_height" eken 300px box ekatama
        # confine karala (logo eka methen affect wenne na, full canvas
        # height ekatama relative widiyata thamai position wenne).
        text_area_height=(MEME_BOX_H if layout_mode == "meme" else None),
    )
    return image_buf.getvalue()


async def _selfblur_generate_preview_png(context: ContextTypes.DEFAULT_TYPE) -> bytes | None:
    """Danata thiyena blur/size/position/watermark/text settings okkoma ekka,
    real video eken hadapu single-frame preview eka (PNG) generate karanawa -
    "Render Video" click karanna kalinma, ethi widiyatama penena eka."""
    data = context.user_data
    video_path = data.get("selfblur_video_path")
    if not video_path or not Path(video_path).exists():
        return None
    try:
        src_w, src_h, _dur, _br = await probe_video(video_path)
    except Exception:
        logger.exception("Self-blur preview: probe_video failed")
        return None
    _layout_mode_prev = data.get("selfblur_layout", "standard")
    if _layout_mode_prev == "meme":
        canvas_w = MEME_CANVAS_W
        canvas_h = MEME_VIDEO_H
    else:
        canvas_w = max(2, (src_w // 2) * 2)
        canvas_h = max(2, (src_h // 2) * 2)
    try:
        # BUG FIX: text overlay PNG eka (logo eka ekathuwama) FULL final canvas
        # height ekatama (box+video) generate karanna one - "canvas_h" methanin
        # (uda thiyena) meme layout ekata MEME_VIDEO_H (780) witharai, box eka
        # ekathu karanne na (eka _selfblur_bg_fg_filter ekatama use wenne).
        # Full height eka wenama methanin calculate karala danawa - text eka
        # "text_area_height" eken 300px box ekatama confine wenawa (methanin
        # wenas wenne na), logo eka witharai dan full canvas ekatama relative
        # widiyata correct widiyata position wenne (box eken pita clip wenne na).
        _text_full_h = (MEME_BOX_H + MEME_VIDEO_H) if _layout_mode_prev == "meme" else canvas_h
        text_png = await _selfblur_build_text_overlay_png(context, canvas_w, _text_full_h)
    except Exception:
        logger.exception("Self-blur preview: text overlay generation failed")
        text_png = None
    try:
        png_bytes, _w, _h = await render_selfblur_preview_frame(
            video_path,
            blur_px=data.get("selfblur_blur_px", SELFBLUR_BLUR_DEFAULT),
            fg_scale_pct=data.get("selfblur_fg_pct", SELFBLUR_FG_PCT_DEFAULT),
            fg_y_offset_pct=data.get("selfblur_fg_yoff", SELFBLUR_YOFF_DEFAULT),
            watermark_png_bytes=data.get("selfblur_watermark_bytes"),
            watermark_opacity=data.get("selfblur_watermark_opacity", WATERMARK_OPACITY_DEFAULT),
            watermark_scale=data.get("selfblur_watermark_scale", WATERMARK_SCALE_DEFAULT),
            watermark_side=data.get("selfblur_watermark_side", WATERMARK_SIDE_DEFAULT),
            text_overlay_png_bytes=text_png,
            blur_type=data.get("selfblur_blur_type", SELFBLUR_BLUR_TYPE_DEFAULT),
            chromatic_aberration=data.get("selfblur_chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT),
            chromatic_shift=data.get("selfblur_chromatic_shift", CHROMATIC_SHIFT_DEFAULT),
            vhs_effect=data.get("selfblur_vhs_effect", VHS_EFFECT_DEFAULT),
            vhs_strength=data.get("selfblur_vhs_strength", VHS_STRENGTH_DEFAULT),
            overlay_opacity_pct=data.get("selfblur_overlay_opacity", SELFBLUR_OVERLAY_OPACITY_DEFAULT),
            bg_kind=data.get("selfblur_bg_kind", SELFBLUR_BG_KIND_DEFAULT),
            bg_color=data.get("selfblur_bg_color", SELFBLUR_BG_COLOR_DEFAULT),
            bg_image_path=data.get("selfblur_bg_image_path"),
            bg_video_path=data.get("selfblur_bg_video_path"),
            bg_blur_enabled=data.get("selfblur_bg_blur_enabled", True),
            layout_mode=data.get("selfblur_layout", "standard"),
        )
    except Exception:
        logger.exception("Self-blur preview frame generation failed")
        return None
    return png_bytes


async def _selfblur_update_caption_message(context: ContextTypes.DEFAULT_TYPE, chat_id: int, caption: str, keyboard: InlineKeyboardMarkup | None = None):
    """Main preview photo eka anit wenama thiyena settings-caption text
    message eka (selfblur_caption_msg_id) update karanawa - thiyenawa nam
    edit_message_text, nathnam (delete unath, ho patanmama nathnam) aluthen
    send karanawa. Photo eke caption eka methanata gahanne na - eka nisama
    tamai photo eka "cropped" widiyata penuna bug eka una. Button set eka
    (keyboard) methama - photo eka + button set eka madata caption message
    eka penena widiyata (image -> settings text -> buttons piliwelata)."""
    data = context.user_data
    msg_id = data.get("selfblur_caption_msg_id")
    if msg_id:
        try:
            await context.bot.edit_message_text(
                chat_id=chat_id, message_id=msg_id, text=caption, parse_mode="Markdown", reply_markup=keyboard,
            )
            return
        except Exception:
            pass
    try:
        sent = await context.bot.send_message(chat_id=chat_id, text=caption, parse_mode="Markdown", reply_markup=keyboard)
        data["selfblur_caption_msg_id"] = sent.message_id
    except Exception:
        pass


async def _send_selfblur_menu(chat_id: int, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Adjust menu eka + live preview photo eka (blur/size/position/text
    okkoma udinma penena) patan gannawa. Photo eka (caption/buttons ekakuth
    nathuwa) ekath, settings text eka (button set ekath ekka) wenama plain
    text message ekakata - meken photo eka udinma caption eka danne nathi
    nisa, Telegram client ekedi bubble height eka podi wela image eka
    "cropped" widiyata penena bug eka fix wenawa (full size eka ekapaharatama
    penei, tap karanna one na). Photo eka -> settings text eka -> button set
    eka piliwelata (button set eka settings text eke reply_markup ekata,
    photo ekata nemei) chat eke penei."""
    data = context.user_data
    data["selfblur_view"] = "main"
    png_bytes = await _selfblur_generate_preview_png(context)
    caption = _selfblur_menu_text(data)
    keyboard = _selfblur_keyboard(data)
    if png_bytes:
        sent = await send_with_retry(
            context.bot.send_photo,
            chat_id=chat_id,
            photo=BytesIO(png_bytes),
            what="self-blur preview send_photo",
        )
        caption_sent = await context.bot.send_message(
            chat_id=chat_id, text=caption, parse_mode="Markdown", reply_markup=keyboard,
        )
        data["selfblur_caption_msg_id"] = caption_sent.message_id
    else:
        # preview eka generate karanna baruna nam (ffmpeg issue ekak), preview
        # ekak nathuwath adjust flow eka block wenna denne na - text message
        # ekak widiyata fallback karanawa (methanata witharai caption eka +
        # keyboard eka ekama message ekakata, danna photo ekak nathi nisa)
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text=caption + "\n\n⚠️ Preview eka load karanna barunath, settings walata effect wenawa.",
            parse_mode="Markdown",
            reply_markup=keyboard,
        )
        data.pop("selfblur_caption_msg_id", None)
    data["selfblur_menu_msg_id"] = sent.message_id
    return SELFBLUR_ADJUSTING


async def _selfblur_open_settings_menu(query, context: ContextTypes.DEFAULT_TYPE, caption: str, keyboard: InlineKeyboardMarkup):
    """"🔤 Text Settings" / "😀 Emoji Settings" wage sub-menu ekakata yana
    gaman call wenawa - main preview photo eka (eketama caption/media eka)
    THIYENA VIDIYATAMA ain karanne nathuwa, wenama plain text message ekak
    (photo ekak nathuwa) ahala danawa. Meken danata thibba widiyata sub-menu
    ekedi photo eka repeatedly edit_message_media karaddi Telegram client
    ekedi preview eka podi/cropped widiyata penuna eka fix wenawa - photo eka
    "ekapaharatama fully" balanna one nam, methanin ain karapu wenama message
    eka nathuwa, main preview photo eka ekamama thiyenawa.

    Main settings caption eka (selfblur_caption_msg_id - photo eka anit
    wenama message ekak) - sub-menu eka open wela thiyena welawata METHANIN
    delete karanawa, ehema nathnam "Self-Blur Video Settings" card eka +
    "Text Settings" card eka dekama ekapahara chat eke penī, godak "dirty"/
    cluttered widiyata penei. Back click kaloth (_selfblur_close_settings_and_refresh_main)
    methanma aye send karanawa."""
    data = context.user_data
    chat_id = query.message.chat_id
    old_id = data.pop("selfblur_settings_msg_id", None)
    if old_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=old_id)
        except Exception:
            pass
    caption_id = data.pop("selfblur_caption_msg_id", None)
    if caption_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=caption_id)
        except Exception:
            pass
    # Main photo eke button set eka (Blur/Size/Text Settings/... okkoma)
    # methanin ain karanawa - ehema nathnam sub-menu ekath + main button set
    # ekath dekama ekapahara chat eke thiyela, user ta uda-pahala scroll
    # karaddi karaddi tamai edit karanna one wenne (godak "awl" widiyata
    # penena UX issue eka). Sub-menu ekedi tියෙන welawata button set එකක්
    # witharai (sub-menu ekema eka) penei; "Back" click kaloth
    # (_selfblur_close_settings_and_refresh_main) methanma aye restore wenawa.
    # (Main button set eka photo ekata nemei, settings text message ekata -
    # eka uda caption_id ekenma delete wela ivarai, wenama clear karanna one na.)
    sent = await context.bot.send_message(
        chat_id=chat_id, text=caption, parse_mode="Markdown", reply_markup=keyboard,
    )
    data["selfblur_settings_msg_id"] = sent.message_id


async def _selfblur_edit_settings_menu(context: ContextTypes.DEFAULT_TYPE, chat_id: int, caption: str, keyboard: InlineKeyboardMarkup):
    """Sub-menu eka thulama +/- adjust button ekak click kaloth methanin -
    wenama settings message eka (photo ekak nemei, plain text ekak nisa)
    edit_message_text ekenma fast widiyata update karanawa. Text/emoji
    settings tika VISUAL ekatama effect wena nisa (kalinma "Back" click
    karanna kalinma preview eka update wuna na - user ta "live edit wenne
    na" widiyata penuna eka), main preview photo ekath METHANINMA
    regenerate karanawa - main adjust menu eke Blur/Size widiyatama, hama
    +/-/colour/position click ekakatama preview eka udinma refresh wenawa."""
    data = context.user_data
    msg_id = data.get("selfblur_settings_msg_id")
    if msg_id:
        try:
            await context.bot.edit_message_text(
                chat_id=chat_id, message_id=msg_id, text=caption, parse_mode="Markdown", reply_markup=keyboard,
            )
        except Exception:
            pass

    main_msg_id = data.get("selfblur_menu_msg_id")
    if not main_msg_id:
        return
    if data.get("selfblur_generating"):
        data["selfblur_generation_queued"] = True
        return
    data["selfblur_generating"] = True
    while True:
        data["selfblur_generation_queued"] = False
        try:
            png_bytes = await _selfblur_generate_preview_png(context)
        except Exception:
            png_bytes = None
        if png_bytes:
            try:
                await context.bot.edit_message_media(
                    chat_id=chat_id, message_id=main_msg_id,
                    media=InputMediaPhoto(BytesIO(png_bytes)),
                )
            except Exception:
                pass
        if not data.get("selfblur_generation_queued"):
            break
    data["selfblur_generating"] = False


async def _selfblur_close_settings_and_refresh_main(context: ContextTypes.DEFAULT_TYPE, chat_id: int, regenerate_preview: bool):
    """Sub-menu ekedi "🔙 Back" click kaloth - wenama settings message eka
    delete karala, main preview photo eka (menna methanma - selfblur_menu_msg_id)
    update karanawa. regenerate_preview=True nam (text/emoji settings passe,
    video eke udin penena widiya wenas unu nisa) ffmpeg eken preview PNG eka
    aluthen render karala photo eka replace karanawa; False nam (audio wage,
    visual ekata effect karanne nathi settings) caption/keyboard eka witharak
    (cheap, ffmpeg ekak nathuwa) update karanawa."""
    data = context.user_data
    settings_msg_id = data.pop("selfblur_settings_msg_id", None)
    if settings_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=settings_msg_id)
        except Exception:
            pass

    main_msg_id = data.get("selfblur_menu_msg_id")
    if not main_msg_id:
        return

    caption = _selfblur_menu_text(data)
    keyboard = _selfblur_keyboard(data)

    if regenerate_preview:
        if data.get("selfblur_generating"):
            return
        data["selfblur_generating"] = True
        try:
            png_bytes = await _selfblur_generate_preview_png(context)
        finally:
            data["selfblur_generating"] = False
        if png_bytes:
            try:
                await context.bot.edit_message_media(
                    chat_id=chat_id, message_id=main_msg_id,
                    media=InputMediaPhoto(BytesIO(png_bytes)),
                )
                await _selfblur_update_caption_message(context, chat_id, caption, keyboard)
                return
            except Exception:
                pass
    # regenerate_preview=False, or media edit failed above -> photo eka thiyena
    # widiyatama thiyaganna, caption + keyboard eka witharak update karanawa
    # (photo ekata reply_markup ekak danne na - button set eka danata
    # settings text eke reply_markup eka widiyata)
    await _selfblur_update_caption_message(context, chat_id, caption, keyboard)


async def _selfblur_send_settings_submenu(context: ContextTypes.DEFAULT_TYPE, chat_id: int, caption: str, keyboard: InlineKeyboardMarkup):
    """_selfblur_open_settings_menu() ekema logic eka - eth CallbackQuery ekak
    nathuwa, chat_id ekakinma call karanna puluwan widiyata (manual value
    ekak type kara ivara welata, message handler ekaka indan sub-menu eka
    aye pennanna one welawata use karanawa)."""
    data = context.user_data
    old_id = data.pop("selfblur_settings_msg_id", None)
    if old_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=old_id)
        except Exception:
            pass
    caption_id = data.pop("selfblur_caption_msg_id", None)
    if caption_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=caption_id)
        except Exception:
            pass
    # Main button set eka photo ekata nemei, settings text message ekata -
    # eka uda caption_id ekenma delete wela ivarai, wenama clear karanna one na.
    sent = await context.bot.send_message(chat_id=chat_id, text=caption, parse_mode="Markdown", reply_markup=keyboard)
    data["selfblur_settings_msg_id"] = sent.message_id


async def _selfblur_regenerate_main_preview(context: ContextTypes.DEFAULT_TYPE, chat_id: int):
    """Main live-preview photo eka (selfblur_menu_msg_id) witharak aluthen
    render karala replace karanawa - keyboard/caption eka touch karanne na
    (ewa dan wenama sub-menu ekaka penena nisa). Manual value input eka
    passe use karanawa."""
    data = context.user_data
    main_msg_id = data.get("selfblur_menu_msg_id")
    if not main_msg_id:
        return
    if data.get("selfblur_generating"):
        return
    data["selfblur_generating"] = True
    try:
        png_bytes = await _selfblur_generate_preview_png(context)
    finally:
        data["selfblur_generating"] = False
    if png_bytes:
        try:
            await context.bot.edit_message_media(
                chat_id=chat_id, message_id=main_msg_id, media=InputMediaPhoto(BytesIO(png_bytes)),
            )
        except Exception:
            pass


async def _refresh_selfblur_menu(query, context: ContextTypes.DEFAULT_TYPE):
    """Main menu eke buttons click kaloth methanin - caption/keyboard update
    karala, preview photo eka queue-based debounce ekakin live update karanawa."""
    data = context.user_data
    caption = _selfblur_menu_text(data)
    keyboard = _selfblur_keyboard(data)
    chat_id = query.message.chat_id

    try:
        await query.edit_message_text(caption, parse_mode="Markdown", reply_markup=keyboard)
    except Exception:
        await _selfblur_update_caption_message(context, chat_id, caption, keyboard)

    # Queue-based live preview - button ekak ekapaharata click karaddi
    # selfblur_generation_queued = True karagena, generate wena eka ivara
    # welata eka detect karala catch-up karaganawa.
    main_msg_id = data.get("selfblur_menu_msg_id")
    if not main_msg_id:
        return
    if data.get("selfblur_generating"):
        data["selfblur_generation_queued"] = True
        return
    data["selfblur_generating"] = True
    while True:
        data["selfblur_generation_queued"] = False
        try:
            png_bytes = await _selfblur_generate_preview_png(context)
        except Exception:
            png_bytes = None
        if png_bytes:
            try:
                await context.bot.edit_message_media(
                    chat_id=chat_id, message_id=main_msg_id,
                    media=InputMediaPhoto(BytesIO(png_bytes)),
                )
            except Exception:
                pass
        if not data.get("selfblur_generation_queued"):
            break
    data["selfblur_generating"] = False


def _selfblur_audio_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🎵 Keep original audio", callback_data="sb_audio_keep")],
        [InlineKeyboardButton("🔇 Mute", callback_data="sb_audio_mute")],
        [
            InlineKeyboardButton("📱 Upload new audio", callback_data="sb_audio_upload"),
            InlineKeyboardButton("🎵 TikTok audio", callback_data="sb_audio_tiktok"),
        ],
        [InlineKeyboardButton("🔙 Back", callback_data="sb_audio_back")],
    ])


async def selfblur_adjust_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """SELFBLUR_ADJUSTING state eke okkoma "sb_*" button clicks methanin
    handle wenawa - blur/size/position +/- , audio submenu, watermark toggle,
    render, cancel. Adjust buttons walata state eka self-loop wenawa (methanma
    keyboard eka refresh karanawa)."""
    query = update.callback_query
    data = context.user_data
    action = query.data

    if action == "sb_noop":
        await query.answer()
        return SELFBLUR_ADJUSTING

    if action == "sb_blur_dec":
        data["selfblur_blur_px"] = max(SELFBLUR_BLUR_MIN, data.get("selfblur_blur_px", SELFBLUR_BLUR_DEFAULT) - SELFBLUR_BLUR_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_blur_inc":
        data["selfblur_blur_px"] = min(SELFBLUR_BLUR_MAX, data.get("selfblur_blur_px", SELFBLUR_BLUR_DEFAULT) + SELFBLUR_BLUR_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_size_dec":
        data["selfblur_fg_pct"] = max(SELFBLUR_FG_PCT_MIN, data.get("selfblur_fg_pct", SELFBLUR_FG_PCT_DEFAULT) - SELFBLUR_FG_PCT_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_size_inc":
        data["selfblur_fg_pct"] = min(SELFBLUR_FG_PCT_MAX, data.get("selfblur_fg_pct", SELFBLUR_FG_PCT_DEFAULT) + SELFBLUR_FG_PCT_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_pos_up":
        # "Up" click kaloth, screen ekedi video eka udata move wenna one -
        # ithin yoff value eka adui karanawa (negative = udata, overlay
        # eke y-expr eke "-" widiyata)
        data["selfblur_fg_yoff"] = max(SELFBLUR_YOFF_MIN, data.get("selfblur_fg_yoff", SELFBLUR_YOFF_DEFAULT) - SELFBLUR_YOFF_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_pos_down":
        data["selfblur_fg_yoff"] = min(SELFBLUR_YOFF_MAX, data.get("selfblur_fg_yoff", SELFBLUR_YOFF_DEFAULT) + SELFBLUR_YOFF_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_font_dec":
        data["selfblur_font_size"] = max(SELFBLUR_FONT_SIZE_MIN, data.get("selfblur_font_size", SELFBLUR_FONT_SIZE_DEFAULT) - SELFBLUR_FONT_SIZE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_font_inc":
        data["selfblur_font_size"] = min(SELFBLUR_FONT_SIZE_MAX, data.get("selfblur_font_size", SELFBLUR_FONT_SIZE_DEFAULT) + SELFBLUR_FONT_SIZE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_text_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_text_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action.startswith("sb_textcolor_"):
        color_key = action[len("sb_textcolor_"):]
        data["selfblur_text_color"] = COLORS.get(color_key, COLORS["white"])
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_stroke_dec":
        data["selfblur_stroke_width"] = round(
            max(STROKE_WIDTH_MIN, data.get("selfblur_stroke_width", STROKE_WIDTH_DEFAULT) - STROKE_WIDTH_STEP), 1
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_stroke_inc":
        data["selfblur_stroke_width"] = round(
            min(STROKE_WIDTH_MAX, data.get("selfblur_stroke_width", STROKE_WIDTH_DEFAULT) + STROKE_WIDTH_STEP), 1
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action.startswith("sb_strokecolor_"):
        color_key = action[len("sb_strokecolor_"):]
        data["selfblur_stroke_color"] = COLORS.get(color_key, COLORS["black"])
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_text_top":
        data["selfblur_text_yoff"] = max(TEXT_OFFSET_MIN, min(TEXT_OFFSET_MAX, SELFBLUR_TEXT_TOP_OFFSET))
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_text_bottom":
        data["selfblur_text_yoff"] = max(TEXT_OFFSET_MIN, min(TEXT_OFFSET_MAX, SELFBLUR_TEXT_BOTTOM_OFFSET))
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_text_up":
        data["selfblur_text_yoff"] = max(
            TEXT_OFFSET_MIN, data.get("selfblur_text_yoff", SELFBLUR_TEXT_YOFF_DEFAULT) - TEXT_OFFSET_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_text_down":
        data["selfblur_text_yoff"] = min(
            TEXT_OFFSET_MAX, data.get("selfblur_text_yoff", SELFBLUR_TEXT_YOFF_DEFAULT) + TEXT_OFFSET_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_meme_text_up":
        data["selfblur_meme_text_yoff"] = max(
            MEME_TEXT_YOFF_MIN, data.get("selfblur_meme_text_yoff", MEME_TEXT_YOFF_DEFAULT) - MEME_TEXT_YOFF_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_meme_text_down":
        data["selfblur_meme_text_yoff"] = min(
            MEME_TEXT_YOFF_MAX, data.get("selfblur_meme_text_yoff", MEME_TEXT_YOFF_DEFAULT) + MEME_TEXT_YOFF_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_text_menu_text(data), _selfblur_text_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_emoji_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_emoji_menu_text(data), _selfblur_emoji_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_emoji_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action == "sb_emoji_dec":
        data["selfblur_emoji_size"] = max(EMOJI_SIZE_MIN, data.get("selfblur_emoji_size", EMOJI_SIZE_DEFAULT) - EMOJI_SIZE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_emoji_menu_text(data), _selfblur_emoji_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_emoji_inc":
        data["selfblur_emoji_size"] = min(EMOJI_SIZE_MAX, data.get("selfblur_emoji_size", EMOJI_SIZE_DEFAULT) + EMOJI_SIZE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_emoji_menu_text(data), _selfblur_emoji_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_emoji_reset":
        data["selfblur_emoji_size"] = EMOJI_SIZE_DEFAULT
        data["selfblur_emoji_yoff"] = EMOJI_OFFSET_DEFAULT
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_emoji_menu_text(data), _selfblur_emoji_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_emoji_up":
        data["selfblur_emoji_yoff"] = max(
            EMOJI_OFFSET_MIN, data.get("selfblur_emoji_yoff", EMOJI_OFFSET_DEFAULT) - EMOJI_OFFSET_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_emoji_menu_text(data), _selfblur_emoji_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_emoji_down":
        data["selfblur_emoji_yoff"] = min(
            EMOJI_OFFSET_MAX, data.get("selfblur_emoji_yoff", EMOJI_OFFSET_DEFAULT) + EMOJI_OFFSET_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_emoji_menu_text(data), _selfblur_emoji_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_overlay_dec":
        data["selfblur_overlay_opacity"] = max(
            SELFBLUR_OVERLAY_OPACITY_MIN, data.get("selfblur_overlay_opacity", SELFBLUR_OVERLAY_OPACITY_DEFAULT) - SELFBLUR_OVERLAY_OPACITY_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_overlay_inc":
        data["selfblur_overlay_opacity"] = min(
            SELFBLUR_OVERLAY_OPACITY_MAX, data.get("selfblur_overlay_opacity", SELFBLUR_OVERLAY_OPACITY_DEFAULT) + SELFBLUR_OVERLAY_OPACITY_STEP
        )
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_blur_type_toggle":
        current = data.get("selfblur_blur_type", SELFBLUR_BLUR_TYPE_DEFAULT)
        data["selfblur_blur_type"] = "motion" if current == "gaussian" else "gaussian"
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_chromatic_toggle":
        data["selfblur_chromatic_aberration"] = not bool(data.get("selfblur_chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT))
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_chromatic_dec":
        data["selfblur_chromatic_shift"] = max(CHROMATIC_SHIFT_MIN, data.get("selfblur_chromatic_shift", CHROMATIC_SHIFT_DEFAULT) - CHROMATIC_SHIFT_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_chromatic_inc":
        data["selfblur_chromatic_shift"] = min(CHROMATIC_SHIFT_MAX, data.get("selfblur_chromatic_shift", CHROMATIC_SHIFT_DEFAULT) + CHROMATIC_SHIFT_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_vhs_toggle":
        data["selfblur_vhs_effect"] = not bool(data.get("selfblur_vhs_effect", VHS_EFFECT_DEFAULT))
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_vhs_dec":
        data["selfblur_vhs_strength"] = max(VHS_STRENGTH_MIN, data.get("selfblur_vhs_strength", VHS_STRENGTH_DEFAULT) - VHS_STRENGTH_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_vhs_inc":
        data["selfblur_vhs_strength"] = min(VHS_STRENGTH_MAX, data.get("selfblur_vhs_strength", VHS_STRENGTH_DEFAULT) + VHS_STRENGTH_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_intro_dec":
        data["selfblur_intro_black_seconds"] = round(max(
            INTRO_BLACK_SECONDS_MIN, data.get("selfblur_intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT) - INTRO_BLACK_SECONDS_STEP
        ), 1)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_intro_inc":
        data["selfblur_intro_black_seconds"] = round(min(
            INTRO_BLACK_SECONDS_MAX, data.get("selfblur_intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT) + INTRO_BLACK_SECONDS_STEP
        ), 1)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_text_edit":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        # "sb_text_edit" dan click wenne wenama "🔤 Text Settings" message
        # eken (main preview photo eken nemei) - ithin main preview photo
        # eka (selfblur_menu_msg_id) methanin nathuwama delete karanawa,
        # naththam aluth text ekak type kala passe _send_selfblur_menu()
        # eken aluth photo ekak yawaddi, kalinma photo ekath ekathu widiyata
        # deka wela chat eke thiyennwa.
        old_main_id = data.pop("selfblur_menu_msg_id", None)
        if old_main_id:
            try:
                await context.bot.delete_message(chat_id=query.message.chat_id, message_id=old_main_id)
            except Exception:
                pass
        old_caption_id = data.pop("selfblur_caption_msg_id", None)
        if old_caption_id:
            try:
                await context.bot.delete_message(chat_id=query.message.chat_id, message_id=old_caption_id)
            except Exception:
                pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="✏️ Aluth caption/emoji text eka type karanna (##bold## //italic// "
            "\"header\" ^^highlight^^ syntax + emoji characters support wenawa), "
            "nathnam /skip karala text eka ain karanna.",
            parse_mode="Markdown",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_TEXT

    if action == "sb_audio_menu":
        await query.answer()
        await _selfblur_open_settings_menu(
            query, context,
            "🎧 *Audio*\n\nMokakda one? Original audio ekma thiyaganna, mute karanna, "
            "nathnam aluth music ekak (upload/TikTok) danna.",
            _selfblur_audio_keyboard(),
        )
        return SELFBLUR_ADJUSTING

    if action == "sb_audio_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=False)
        return SELFBLUR_ADJUSTING

    if action == "sb_audio_keep":
        data["selfblur_audio_mode"] = "keep"
        if data.get("selfblur_audio_path"):
            shutil.rmtree(Path(data["selfblur_audio_path"]).parent, ignore_errors=True)
        data["selfblur_audio_path"] = None
        await query.answer("🎵 Original audio eka thiyaganna!")
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=False)
        return SELFBLUR_ADJUSTING

    if action == "sb_audio_mute":
        data["selfblur_audio_mode"] = "mute"
        if data.get("selfblur_audio_path"):
            shutil.rmtree(Path(data["selfblur_audio_path"]).parent, ignore_errors=True)
        data["selfblur_audio_path"] = None
        await query.answer("🔇 Mute karala!")
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=False)
        return SELFBLUR_ADJUSTING

    if action == "sb_audio_upload":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="📱 Send me the audio file (mp3, m4a, voice note, etc).",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_AUDIO_UPLOAD

    if action == "sb_audio_tiktok":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(chat_id=query.message.chat_id, text="📎 Send me the TikTok link.")
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_AUDIO_TIKTOK_LINK

    # ---- 🏷 Watermark Settings sub-menu ----
    if action == "sb_wm_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_add":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🖼 Send me the scrolling watermark image (PNG with transparent background works best).",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_WATERMARK_IMAGE

    if action == "sb_wm_text":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="📝 Send me the text for your scrolling watermark.",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_WATERMARK_TEXT

    if action == "sb_wm_remove":
        data["selfblur_watermark_bytes"] = None
        await query.answer("🏷 Watermark removed!")
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_opacity_dec":
        data["selfblur_watermark_opacity"] = max(WATERMARK_OPACITY_MIN, data.get("selfblur_watermark_opacity", WATERMARK_OPACITY_DEFAULT) - WATERMARK_OPACITY_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_opacity_inc":
        data["selfblur_watermark_opacity"] = min(WATERMARK_OPACITY_MAX, data.get("selfblur_watermark_opacity", WATERMARK_OPACITY_DEFAULT) + WATERMARK_OPACITY_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_scale_dec":
        data["selfblur_watermark_scale"] = max(WATERMARK_SCALE_MIN, data.get("selfblur_watermark_scale", WATERMARK_SCALE_DEFAULT) - WATERMARK_SCALE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_scale_inc":
        data["selfblur_watermark_scale"] = min(WATERMARK_SCALE_MAX, data.get("selfblur_watermark_scale", WATERMARK_SCALE_DEFAULT) + WATERMARK_SCALE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_speed_dec":
        data["selfblur_watermark_speed"] = max(WATERMARK_SPEED_MIN, data.get("selfblur_watermark_speed", WATERMARK_SPEED_DEFAULT) - WATERMARK_SPEED_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_speed_inc":
        data["selfblur_watermark_speed"] = min(WATERMARK_SPEED_MAX, data.get("selfblur_watermark_speed", WATERMARK_SPEED_DEFAULT) + WATERMARK_SPEED_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_direction_toggle":
        cur = data.get("selfblur_watermark_direction", WATERMARK_DIRECTION_DEFAULT)
        idx = WATERMARK_DIRECTIONS.index(cur) if cur in WATERMARK_DIRECTIONS else 0
        data["selfblur_watermark_direction"] = WATERMARK_DIRECTIONS[(idx + 1) % len(WATERMARK_DIRECTIONS)]
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_wm_side_toggle":
        cur = data.get("selfblur_watermark_side", WATERMARK_SIDE_DEFAULT)
        idx = WATERMARK_SIDES.index(cur) if cur in WATERMARK_SIDES else 0
        data["selfblur_watermark_side"] = WATERMARK_SIDES[(idx + 1) % len(WATERMARK_SIDES)]
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_watermark_menu_text(data), _selfblur_watermark_keyboard(data))
        return SELFBLUR_ADJUSTING

    # ---- 🖼 Logo Settings sub-menu (static, video center, wenama scrolling
    # watermark eken independent) ----
    if action == "sb_logo_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_add":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🖼 Send me the logo image (PNG with transparent background works best) - "
            "it'll be placed in the center of the video.",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_LOGO_IMAGE

    if action == "sb_video_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_video_menu_text(data), _selfblur_video_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_video_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action == "sb_effects_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_effects_menu_text(data), _selfblur_effects_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_effects_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_text":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="📝 Send me the text for your logo (e.g., your brand name).",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_LOGO_TEXT

    if action == "sb_logo_remove":
        data["selfblur_logo_kind"] = None
        data["selfblur_logo_value"] = None
        await query.answer("🖼 Logo removed!")
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_scale_dec":
        data["selfblur_logo_scale"] = max(LOGO_SCALE_MIN, data.get("selfblur_logo_scale", LOGO_SCALE_DEFAULT) - LOGO_SCALE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_scale_inc":
        data["selfblur_logo_scale"] = min(LOGO_SCALE_MAX, data.get("selfblur_logo_scale", LOGO_SCALE_DEFAULT) + LOGO_SCALE_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_opacity_dec":
        data["selfblur_logo_opacity"] = max(LOGO_OPACITY_MIN, data.get("selfblur_logo_opacity", LOGO_OPACITY_DEFAULT) - LOGO_OPACITY_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_opacity_inc":
        data["selfblur_logo_opacity"] = min(LOGO_OPACITY_MAX, data.get("selfblur_logo_opacity", LOGO_OPACITY_DEFAULT) + LOGO_OPACITY_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_pos_up":
        data["selfblur_logo_offset_bottom"] = min(LOGO_OFFSET_MAX, data.get("selfblur_logo_offset_bottom", LOGO_OFFSET_DEFAULT) + LOGO_OFFSET_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_logo_pos_down":
        data["selfblur_logo_offset_bottom"] = max(LOGO_OFFSET_MIN, data.get("selfblur_logo_offset_bottom", LOGO_OFFSET_DEFAULT) - LOGO_OFFSET_STEP)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_logo_menu_text(data), _selfblur_logo_keyboard(data))
        return SELFBLUR_ADJUSTING

    # ---- "✏️ Type value" buttons (emoji/watermark/logo sub-menus tikama
    # share karana generic manual-input trigger eka) ----
    if action.startswith("sb_manual_"):
        target = action[len("sb_manual_"):]
        cfg = SELFBLUR_MANUAL_TARGETS.get(target)
        if not cfg:
            await query.answer()
            return SELFBLUR_ADJUSTING
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        data["selfblur_manual_target"] = target
        current = data.get(cfg["data_key"], cfg["default"])
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=f"✏️ {cfg['prompt']}.\n\n"
            f"Danata value eka: `{current}{cfg['unit']}`. Aluth value ekak "
            f"({cfg['min']} - {cfg['max']}) type karanna, nathnam /cancel karanna.",
            parse_mode="Markdown",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_MANUAL_VALUE

    # ---- 🖼 Background sub-menu ----
    if action == "sb_layout_toggle":
        current = data.get("selfblur_layout", "standard")
        data["selfblur_layout"] = "meme" if current == "standard" else "standard"
        await query.answer()
        await _refresh_selfblur_menu(query, context)
        return SELFBLUR_ADJUSTING

    if action == "sb_bg_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_bg_menu_text(data), _selfblur_bg_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_bg_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action == "sb_bg_blur":
        data["selfblur_bg_kind"] = "blur"
        await query.answer("🌫 Background = blurred video")
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_bg_menu_text(data), _selfblur_bg_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_bg_color_menu":
        await query.answer()
        data["selfblur_bg_kind"] = "color"
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_bg_menu_text(data), _selfblur_bg_color_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action.startswith("sb_bgcolor_"):
        color_key = action[len("sb_bgcolor_"):]
        data["selfblur_bg_kind"] = "color"
        data["selfblur_bg_color"] = COLORS.get(color_key, COLORS["black"])
        await query.answer(f"🎨 Background = {color_key.title()}")
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_bg_menu_text(data), _selfblur_bg_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_bg_image_add":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🖼 Send me the background image (PNG/JPG) - it'll fill the whole canvas behind your video.",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_BG_IMAGE

    if action == "sb_bg_video_add":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="🎥 Send me the background video - it'll loop behind your video for the full duration.",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_BG_VIDEO

    if action == "sb_bg_blur_toggle":
        data["selfblur_bg_blur_enabled"] = not data.get("selfblur_bg_blur_enabled", True)
        await query.answer()
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_bg_menu_text(data), _selfblur_bg_keyboard(data))
        return SELFBLUR_ADJUSTING

    # ---- 📁 Templates sub-menu ----
    if action == "sb_tpl_menu":
        await query.answer()
        await _selfblur_open_settings_menu(query, context, _selfblur_tpl_menu_text(data), _selfblur_tpl_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_tpl_back":
        await query.answer()
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=False)
        return SELFBLUR_ADJUSTING

    if action == "sb_tpl_save":
        store_key = _tpl_store_key(data)
        templates = data.get(store_key, {}) or {}
        if len(templates) >= MAX_TEMPLATES_PER_USER:
            await query.answer(f"⚠️ Max {MAX_TEMPLATES_PER_USER} templates witharai save karanna puluwan.", show_alert=True)
            return SELFBLUR_ADJUSTING
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        sent = await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="✏️ Mee template ekata name ekak type karanna (e.g. `My Style`), nathnam /cancel karanna.",
            parse_mode="Markdown",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_TEMPLATE_NAME

    if action == "sb_tpl_update":
        # Active template eka same name ekatama overwrite (name prompt ekak naha)
        active = data.get("selfblur_active_template_name")
        store_key = _tpl_store_key(data)
        templates = data.setdefault(store_key, {})
        if not active or active not in templates:
            await query.answer("⚠️ Active template ekak naha - 'Save as new' use karanna.", show_alert=True)
            return SELFBLUR_ADJUSTING
        templates[active] = {field: data.get(field) for field in SELFBLUR_TEMPLATE_FIELDS}
        await _flush_persistence(context)   # update unu welavama disk ekata force-write
        await query.answer(f"✅ '{active}' update una!")
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_tpl_menu_text(data), _selfblur_tpl_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action.startswith("sb_tpl_load_"):
        name = action[len("sb_tpl_load_"):]
        # Meme templates OR standard templates - name eka thiyena store eka check karanawa
        tpl = None
        for sk in ("selfblur_templates_meme", "selfblur_templates_standard"):
            tpl = (data.get(sk) or {}).get(name)
            if tpl:
                break
        if not tpl:
            await query.answer("⚠️ Template eka hoyaganna bari una.", show_alert=True)
            return SELFBLUR_ADJUSTING
        for field in SELFBLUR_TEMPLATE_FIELDS:
            if field in tpl:
                data[field] = tpl[field]
        data["selfblur_active_template_name"] = name
        await query.answer(f"📥 '{name}' template eka load una!")
        await _selfblur_close_settings_and_refresh_main(context, query.message.chat_id, regenerate_preview=True)
        return SELFBLUR_ADJUSTING

    if action.startswith("sb_tpl_delete_"):
        name = action[len("sb_tpl_delete_"):]
        store_key = _tpl_store_key(data)
        templates = data.get(store_key, {}) or {}
        templates.pop(name, None)
        data[store_key] = templates
        if data.get("selfblur_active_template_name") == name:
            data["selfblur_active_template_name"] = None
        await _flush_persistence(context)   # delete unu welavama disk ekata force-write
        await query.answer(f"🗑 '{name}' delete una!")
        await _selfblur_edit_settings_menu(context, query.message.chat_id, _selfblur_tpl_menu_text(data), _selfblur_tpl_keyboard(data))
        return SELFBLUR_ADJUSTING

    if action == "sb_cancel":
        await query.answer()
        try:
            await query.message.delete()
        except Exception:
            pass
        # query.message eka danata settings text eka (button set eka
        # thiyena eka) - main preview photo eka (selfblur_menu_msg_id)
        # wenama methanin delete karanawa
        main_id = data.get("selfblur_menu_msg_id")
        if main_id:
            try:
                await context.bot.delete_message(chat_id=query.message.chat_id, message_id=main_id)
            except Exception:
                pass
        _cleanup_selfblur(data)
        await context.bot.send_message(chat_id=query.message.chat_id, text="❌ Cancelled.")
        return ConversationHandler.END

    if action == "sb_render":
        await query.answer()
        return await _selfblur_render(query, context)

    await query.answer()
    return SELFBLUR_ADJUSTING


async def receive_selfblur_audio_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id
    tg_audio = (
        update.message.audio
        or update.message.voice
        or (
            update.message.document
            if update.message.document and (update.message.document.mime_type or "").startswith("audio/")
            else None
        )
    )
    if tg_audio is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like an audio file. Send an audio file, or /cancel to stop."
        )
        return WAITING_SELFBLUR_AUDIO_UPLOAD

    status_msg = await update.message.reply_text("⏳ Downloading your audio...")
    tmp_dir = tempfile.mkdtemp(prefix="sbaudup_")
    ext = Path(getattr(tg_audio, "file_name", None) or "audio.mp3").suffix or ".mp3"
    audio_path = str(Path(tmp_dir) / f"audio{ext}")

    try:
        tg_file = await context.bot.get_file(tg_audio.file_id)
        await tg_file.download_to_drive(audio_path)
    except Exception as e:
        logger.exception("Self-blur audio upload download failed")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't download that audio: {e}\n\n"
            "(Bots can only download files up to 20MB from Telegram.)\n\nSend it again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_AUDIO_UPLOAD

    return await _finalize_selfblur_audio(chat_id, context, audio_path, status_msg)


async def receive_selfblur_audio_tiktok_link(update: Update, context: ContextTypes.DEFAULT_TYPE):
    url = update.message.text.strip()
    chat_id = update.message.chat_id
    status_msg = await update.message.reply_text("⏳ Extracting audio from TikTok...")

    try:
        audio_path = await extract_audio_from_url_with_retry(url)
    except Exception as e:
        logger.exception("Self-blur TikTok audio extract failed after retries")
        await status_msg.edit_text(
            f"⚠️ Couldn't get audio from that link: {e}\n\nSend the TikTok link again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_AUDIO_TIKTOK_LINK

    return await _finalize_selfblur_audio(chat_id, context, audio_path, status_msg)


async def _finalize_selfblur_audio(chat_id: int, context: ContextTypes.DEFAULT_TYPE, audio_path: str, status_msg) -> int:
    data = context.user_data
    try:
        await probe_audio_duration(audio_path)   # validate karanawa witharai - fit eka "loop" fixed widiyata use karanawa
    except Exception as e:
        logger.exception("Self-blur audio probe failed")
        shutil.rmtree(Path(audio_path).parent, ignore_errors=True)
        await status_msg.edit_text(f"⚠️ Couldn't read that audio file: {e}\n\nSend it again, or /cancel to stop.")
        return WAITING_SELFBLUR_AUDIO_UPLOAD

    old_audio_path = data.get("selfblur_audio_path")
    if old_audio_path and old_audio_path != audio_path:
        shutil.rmtree(Path(old_audio_path).parent, ignore_errors=True)

    data["selfblur_audio_path"] = audio_path
    data["selfblur_audio_mode"] = "replace"
    # audio eka video ekata wada podi nam loop karanawa, digu nam global -t
    # eken auto-trim wenawa - ithin "loop" fixed widiyata use kaloth dekama
    # welavata weda karanawa, wenama "how to fit" ahanna one na
    data["selfblur_audio_fit"] = "loop"

    prompt_msg_id = data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass
    try:
        await status_msg.delete()
    except Exception:
        pass

    # audio submenu eka dan wenama message ekak (main preview photo eken
    # nemei) nisa, "Upload/TikTok" click kaloth delete unne e wenama message
    # eka witharai - main preview photo eka (selfblur_menu_msg_id) thaamath
    # chat eke ithuru wela thiyenawa, ithin _send_selfblur_menu() aluth photo
    # ekak yawanna kalin eka methanin explicitly delete karanawa (naththam
    # dekama chat eke thiyenawa).
    old_main_id = data.pop("selfblur_menu_msg_id", None)
    if old_main_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=old_main_id)
        except Exception:
            pass
    old_caption_id = data.pop("selfblur_caption_msg_id", None)
    if old_caption_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=old_caption_id)
        except Exception:
            pass
    data.pop("selfblur_settings_msg_id", None)

    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_watermark_image(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id
    tg_photo = update.message.photo[-1] if update.message.photo else (
        update.message.document
        if update.message.document and (update.message.document.mime_type or "").startswith("image/")
        else None
    )
    if tg_photo is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like an image. Send a PNG/JPG watermark image, or /cancel to stop."
        )
        return WAITING_SELFBLUR_WATERMARK_IMAGE

    tg_file = await context.bot.get_file(tg_photo.file_id)
    img_bytes = await tg_file.download_as_bytearray()
    context.user_data["selfblur_watermark_bytes"] = bytes(img_bytes)

    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_logo_image(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """"🖼 Add Logo Image" (Logo Settings sub-menu eken) - scrolling watermark
    eken sampurnayenma wenama, video eke CENTER ekata static widiyata danna
    logo image eka methanin ahaganawa. main-flow receive_logo_image() ekema
    pattern eka (RGBA convert karala base64 PNG widiyata "selfblur_logo_value"
    ekata save karanawa)."""
    chat_id = update.message.chat_id
    photo = None
    if update.message.document and (update.message.document.mime_type or "").startswith("image/"):
        photo = update.message.document
    elif update.message.photo:
        photo = update.message.photo[-1]

    if photo is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like an image. Please send a PNG/JPG logo, or /cancel to stop."
        )
        return WAITING_SELFBLUR_LOGO_IMAGE

    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    status_msg = await update.message.reply_text("⏳ Processing your logo...")
    try:
        tg_file = await context.bot.get_file(photo.file_id)
        raw_bytes = bytes(await tg_file.download_as_bytearray())
        img = Image.open(BytesIO(raw_bytes))
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGBA")
        buf = BytesIO()
        img.save(buf, format="PNG")
        context.user_data["selfblur_logo_kind"] = "image"
        context.user_data["selfblur_logo_value"] = base64.b64encode(buf.getvalue()).decode("utf-8")
        context.user_data.setdefault("selfblur_logo_scale", LOGO_SCALE_DEFAULT)
        _logo_off_default = MEME_LOGO_OFFSET_DEFAULT if context.user_data.get("selfblur_layout") == "meme" else LOGO_OFFSET_DEFAULT
        context.user_data.setdefault("selfblur_logo_offset_bottom", _logo_off_default)
        context.user_data.setdefault("selfblur_logo_opacity", LOGO_OPACITY_DEFAULT)
    except Exception as e:
        logger.exception("Self-blur logo image processing failed")
        await status_msg.edit_text(
            f"⚠️ Couldn't process that logo: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_LOGO_IMAGE

    try:
        await status_msg.delete()
    except Exception:
        pass

    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_watermark_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id
    wm_text = (update.message.text or "").strip()
    if not wm_text:
        await update.message.reply_text("⚠️ Please send some text for the watermark, or /cancel to stop.")
        return WAITING_SELFBLUR_WATERMARK_TEXT
    status_msg = await update.message.reply_text("⏳ Processing watermark text...")
    try:
        browser = context.application.bot_data["browser"]
        png_bytes = await render_watermark_text_png(browser, wm_text)
    except Exception as e:
        await status_msg.edit_text(f"⚠️ Failed to process: {e}")
        return WAITING_SELFBLUR_WATERMARK_TEXT
    try:
        await status_msg.delete()
    except Exception:
        pass
    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass
    try:
        await update.message.delete()
    except Exception:
        pass
    context.user_data["selfblur_watermark_bytes"] = bytes(png_bytes)
    context.user_data.setdefault("selfblur_watermark_opacity", WATERMARK_OPACITY_DEFAULT)
    context.user_data.setdefault("selfblur_watermark_scale", WATERMARK_SCALE_DEFAULT)
    context.user_data.setdefault("selfblur_watermark_speed", WATERMARK_SPEED_DEFAULT)
    context.user_data.setdefault("selfblur_watermark_direction", WATERMARK_DIRECTION_DEFAULT)
    context.user_data.setdefault("selfblur_watermark_side", WATERMARK_SIDE_DEFAULT)
    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_logo_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id
    logo_text = (update.message.text or "").strip()
    
    if not logo_text:
        await update.message.reply_text("⚠️ Please send some text for the logo, or /cancel to stop.")
        return WAITING_SELFBLUR_LOGO_TEXT

    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    try:
        await update.message.delete()
    except Exception:
        pass

    context.user_data["selfblur_logo_kind"] = "text"
    context.user_data["selfblur_logo_value"] = logo_text
    context.user_data.setdefault("selfblur_logo_scale", LOGO_SCALE_DEFAULT)
    _logo_off_default2 = MEME_LOGO_OFFSET_DEFAULT if context.user_data.get("selfblur_layout") == "meme" else LOGO_OFFSET_DEFAULT
    context.user_data.setdefault("selfblur_logo_offset_bottom", _logo_off_default2)
    context.user_data.setdefault("selfblur_logo_opacity", LOGO_OPACITY_DEFAULT)
    
    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_manual_value(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """"✏️ Type exact value" buttons (emoji/watermark/logo sub-menus tikama
    share karana) walin ena, WAITING_SELFBLUR_MANUAL_VALUE state eke text
    input eka methanin handle wenawa - number ekak parse karala, allowed
    range ekata clamp karala, "sb_manual_*" button eken thoragapu field eka
    update karala, e sub-menu ekatama aye yanawa (live preview eka + main
    photo eka dekama methanin regenerate wenawa)."""
    chat_id = update.message.chat_id
    data = context.user_data
    target = data.pop("selfblur_manual_target", None)
    cfg = SELFBLUR_MANUAL_TARGETS.get(target)

    prompt_msg_id = data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    if not cfg:
        # target eka manageka nomawki nam (state eka corrupt unoth / bot
        # restart ekakin passe), main menu ekatama fallback karanawa
        return await _send_selfblur_menu(chat_id, context)

    raw = (update.message.text or "").strip().replace("px/s", "").replace("px", "").replace("%", "")
    try:
        value = int(round(float(raw)))
    except ValueError:
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text=f"⚠️ Number ekak type karanna (e.g. `{cfg['default']}`). Ayeth try karanna, "
            "nathnam /cancel karanna.",
            parse_mode="Markdown",
        )
        data["selfblur_manual_target"] = target
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_MANUAL_VALUE

    value = max(cfg["min"], min(cfg["max"], value))
    data[cfg["data_key"]] = value

    try:
        await update.message.delete()
    except Exception:
        pass

    menu_text, keyboard = _selfblur_manual_target_menu(cfg["menu"], data)
    await _selfblur_send_settings_submenu(context, chat_id, menu_text, keyboard)
    await _selfblur_regenerate_main_preview(context, chat_id)
    return SELFBLUR_ADJUSTING


async def receive_selfblur_bg_image(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """"🖼 Custom Image" (Background sub-menu) - full-canvas custom background
    image ekak methanin ahaganawa, disk ekata save karala "selfblur_bg_image_path"
    ekata danawa (watermark/logo walata wenas - meka video compose eke direct
    ffmpeg input ekak widiyata use wena nisa, disk ekaka persist wenna one)."""
    chat_id = update.message.chat_id
    tg_photo = update.message.photo[-1] if update.message.photo else (
        update.message.document
        if update.message.document and (update.message.document.mime_type or "").startswith("image/")
        else None
    )
    if tg_photo is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like an image. Send a PNG/JPG, or /cancel to stop."
        )
        return WAITING_SELFBLUR_BG_IMAGE

    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    status_msg = await update.message.reply_text("⏳ Processing background image...")
    try:
        tg_file = await context.bot.get_file(tg_photo.file_id)
        raw_bytes = bytes(await tg_file.download_as_bytearray())
        img = Image.open(BytesIO(raw_bytes))
        img = ImageOps.exif_transpose(img)
        img = img.convert("RGB")

        # danata thiyena bg image path ekak (wenama upload ekak) thibba nam,
        # ekee temp dir eka methanin clean karanawa - disk eka leak wenna
        # denne na, hamada aluth image ekakma save wenne aluth folder ekaka.
        old_path = context.user_data.get("selfblur_bg_image_path")
        if old_path:
            try:
                shutil.rmtree(Path(old_path).parent, ignore_errors=True)
            except Exception:
                pass

        tmp_dir = tempfile.mkdtemp(prefix="sbbgimg_")
        img_path = str(Path(tmp_dir) / "bg.png")
        img.save(img_path, format="PNG")

        context.user_data["selfblur_bg_kind"] = "image"
        context.user_data["selfblur_bg_image_path"] = img_path
        context.user_data.setdefault("selfblur_bg_blur_enabled", True)
    except Exception as e:
        logger.exception("Self-blur bg image processing failed")
        await status_msg.edit_text(
            f"⚠️ Couldn't process that image: {e}\n\nSend it again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_BG_IMAGE

    try:
        await status_msg.delete()
    except Exception:
        pass

    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_bg_video(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """"🎥 Custom Video" (Background sub-menu) - main /selfblur upload ekema
    pattern eka (disk ekata download karala path eka save karanawa) - meka
    "selfblur_video_path" (center clear video) ekata wenama, background
    layer ekata witharak use wena wenama file ekak."""
    chat_id = update.message.chat_id
    tg_video = update.message.video or (
        update.message.document
        if update.message.document and (update.message.document.mime_type or "").startswith("video/")
        else None
    )
    if tg_video is None:
        await update.message.reply_text(
            "⚠️ That doesn't look like a video file. Send a video, or /cancel to stop."
        )
        return WAITING_SELFBLUR_BG_VIDEO

    prompt_msg_id = context.user_data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    status_msg = await update.message.reply_text("⏳ Downloading background video...")

    old_path = context.user_data.get("selfblur_bg_video_path")
    if old_path:
        try:
            shutil.rmtree(Path(old_path).parent, ignore_errors=True)
        except Exception:
            pass

    tmp_dir = tempfile.mkdtemp(prefix="sbbgvid_")
    ext = Path(getattr(tg_video, "file_name", None) or "bg.mp4").suffix or ".mp4"
    video_path = str(Path(tmp_dir) / f"bg{ext}")

    try:
        tg_file = await context.bot.get_file(tg_video.file_id)
        await tg_file.download_to_drive(video_path)
        await probe_video(video_path)   # eka corrupt file ekak nam methedima catch wenawa
    except Exception as e:
        logger.exception("Self-blur bg video download failed")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        await status_msg.edit_text(
            f"⚠️ Couldn't process that video: {e}\n\n"
            "(Bots can only download files up to 20MB from Telegram.)\n\n"
            "Send it again, or /cancel to stop."
        )
        return WAITING_SELFBLUR_BG_VIDEO

    context.user_data["selfblur_bg_kind"] = "video"
    context.user_data["selfblur_bg_video_path"] = video_path
    context.user_data.setdefault("selfblur_bg_blur_enabled", True)

    try:
        await status_msg.delete()
    except Exception:
        pass

    return await _send_selfblur_menu(chat_id, context)


async def receive_selfblur_template_name(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """"💾 Save current settings as template" click unu passe, WAITING_
    SELFBLUR_TEMPLATE_NAME state eke text input eka methanin handle
    wenawa - SELFBLUR_TEMPLATE_FIELDS eke listed hama field ekakma
    "selfblur_templates" dict ekata copy karanawa (video eka/link eka
    NEVER save wenne na - settings witharai, ithin ANY video ekakata
    passe ma load karaganna puluwan)."""
    chat_id = update.message.chat_id
    data = context.user_data

    prompt_msg_id = data.pop("selfblur_prompt_msg_id", None)
    if prompt_msg_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_msg_id)
        except Exception:
            pass

    name = (update.message.text or "").strip()[:40]
    if not name:
        sent = await context.bot.send_message(
            chat_id=chat_id, text="⚠️ Name ekak type karanna, nathnam /cancel karanna."
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_TEMPLATE_NAME

    templates = data.setdefault(_tpl_store_key(data), {})
    if len(templates) >= MAX_TEMPLATES_PER_USER and name not in templates:
        sent = await context.bot.send_message(
            chat_id=chat_id,
            text=f"⚠️ Max {MAX_TEMPLATES_PER_USER} templates witharai save karanna puluwan. "
            "Danata thiyena ekak delete karala try karanna.",
        )
        data["selfblur_prompt_msg_id"] = sent.message_id
        return WAITING_SELFBLUR_TEMPLATE_NAME

    templates[name] = {field: data.get(field) for field in SELFBLUR_TEMPLATE_FIELDS}
    data["selfblur_active_template_name"] = name
    await _flush_persistence(context)   # save unu welavama disk ekata force-write

    try:
        await update.message.delete()
    except Exception:
        pass

    return await _send_selfblur_menu(chat_id, context)


async def _selfblur_render(query, context: ContextTypes.DEFAULT_TYPE) -> int:
    """"✅ Render Video" click unu passe - compose_self_blur_video() call
    karala, live % progress eka edit karagena, final .mp4 eka send karanawa."""
    chat_id = query.message.chat_id
    data = context.user_data
    video_path = data.get("selfblur_video_path")
    if not video_path or not Path(video_path).exists():
        await context.bot.send_message(chat_id=chat_id, text="⚠️ Video eka nathi wela - /selfblur ayeth patan ganna.")
        _cleanup_selfblur(data)
        return ConversationHandler.END

    try:
        await query.message.delete()
    except Exception:
        pass
    # query.message eka danata settings text eka (button set eka thiyena eka)
    # - main preview photo eka (selfblur_menu_msg_id) wenama methanin
    # delete karanawa
    main_id = data.pop("selfblur_menu_msg_id", None)
    if main_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=main_id)
        except Exception:
            pass
    data.pop("selfblur_caption_msg_id", None)

    status_msg = await context.bot.send_message(chat_id=chat_id, text="⏳ Rendering... 0%")
    last_pct_shown = -1

    async def _progress(pct: int):
        nonlocal last_pct_shown
        if pct == last_pct_shown:
            return
        last_pct_shown = pct
        try:
            await status_msg.edit_text(f"⏳ Rendering... {pct}%")
        except Exception:
            pass

    # caption/emoji text ekak thibba nam, final render eke resolution ekatama
    # match wena transparent PNG ekak methanin kalinma hadagannawa (canvas
    # dimensions - compose_self_blur_video() ekma logic ekama)
    text_png = None
    has_logo = bool(data.get("selfblur_logo_kind") and data.get("selfblur_logo_value"))
    if data.get("selfblur_text") or has_logo:
        try:
            src_w, src_h, _dur, _br = await probe_video(video_path)
            _lm = data.get("selfblur_layout", "standard")
            if _lm == "meme":
                canvas_w = MEME_CANVAS_W
                canvas_h = MEME_VIDEO_H
                # BUG FIX: methanata kalinma MEME_BOX_H (300px) witharak dila
                # tibba - eken text/logo PNG eka box height ekatama witharak
                # generate una, ffmpeg eken FULL 1080px canvas ekata overlay
                # karana welavata logo eka box eken pita giya welawakadi
                # (offset eken "down" karoth wath) capture wenne ma nathuwa
                # invisible/clipped una. Dan FULL canvas height eka (box+video)
                # methanata denawa - text eka witharak "text_area_height" eken
                # 300px box ekatama confine wenawa (_selfblur_build_text_
                # overlay_png() athule), logo eka full canvas ekatama relative
                # widiyata correct widiyata position wenne.
                _th = MEME_BOX_H + MEME_VIDEO_H
            else:
                canvas_w = max(2, (src_w // 2) * 2)
                canvas_h = max(2, (src_h // 2) * 2)
                _th = canvas_h
            text_png = await _selfblur_build_text_overlay_png(context, canvas_w, _th)
        except Exception:
            logger.exception("Self-blur render: text/logo overlay generation failed, continuing without it")
            text_png = None

    try:
        final_path = await compose_self_blur_video(
            video_path,
            blur_px=data.get("selfblur_blur_px", SELFBLUR_BLUR_DEFAULT),
            fg_scale_pct=data.get("selfblur_fg_pct", SELFBLUR_FG_PCT_DEFAULT),
            duration_seconds=data.get("selfblur_duration", SELFBLUR_MAX_SECONDS),
            progress_cb=_progress,
            audio_path=data.get("selfblur_audio_path"),
            audio_mode=data.get("selfblur_audio_mode", "keep"),
            audio_fit=data.get("selfblur_audio_fit", "loop"),
            fg_y_offset_pct=data.get("selfblur_fg_yoff", SELFBLUR_YOFF_DEFAULT),
            watermark_png_bytes=data.get("selfblur_watermark_bytes"),
            watermark_opacity=data.get("selfblur_watermark_opacity", WATERMARK_OPACITY_DEFAULT),
            watermark_scale=data.get("selfblur_watermark_scale", WATERMARK_SCALE_DEFAULT),
            watermark_direction=data.get("selfblur_watermark_direction", WATERMARK_DIRECTION_DEFAULT),
            watermark_speed=data.get("selfblur_watermark_speed", WATERMARK_SPEED_DEFAULT),
            watermark_side=data.get("selfblur_watermark_side", WATERMARK_SIDE_DEFAULT),
            text_overlay_png_bytes=text_png,
            blur_type=data.get("selfblur_blur_type", SELFBLUR_BLUR_TYPE_DEFAULT),
            chromatic_aberration=data.get("selfblur_chromatic_aberration", CHROMATIC_ABERRATION_DEFAULT),
            chromatic_shift=data.get("selfblur_chromatic_shift", CHROMATIC_SHIFT_DEFAULT),
            vhs_effect=data.get("selfblur_vhs_effect", VHS_EFFECT_DEFAULT),
            vhs_strength=data.get("selfblur_vhs_strength", VHS_STRENGTH_DEFAULT),
            intro_black_seconds=data.get("selfblur_intro_black_seconds", INTRO_BLACK_SECONDS_DEFAULT),
            overlay_opacity_pct=data.get("selfblur_overlay_opacity", SELFBLUR_OVERLAY_OPACITY_DEFAULT),
            bg_kind=data.get("selfblur_bg_kind", SELFBLUR_BG_KIND_DEFAULT),
            bg_color=data.get("selfblur_bg_color", SELFBLUR_BG_COLOR_DEFAULT),
            bg_image_path=data.get("selfblur_bg_image_path"),
            bg_video_path=data.get("selfblur_bg_video_path"),
            bg_blur_enabled=data.get("selfblur_bg_blur_enabled", True),
            layout_mode=data.get("selfblur_layout", "standard"),
        )
    except Exception as e:
        logger.exception("Self-blur render failed")
        if isinstance(e, subprocess.CalledProcessError) and e.stderr:
            logger.error("self-blur ffmpeg stderr (exit %s):\n%s", e.returncode, e.stderr.decode("utf-8", errors="ignore"))
        try:
            await status_msg.edit_text(f"⚠️ Something went wrong while rendering: {e}")
        except Exception:
            pass
        _cleanup_selfblur(data)
        return ConversationHandler.END

    try:
        with open(final_path, "rb") as f:
            # send_document ekenma yawanne - send_video kalot Telegram eken
            # video eka re-compress karanna puluwan, ehema unoth original
            # quality eka nathi wenawa (main /newpost flow ekema pattern eka)
            await send_with_retry(
                context.bot.send_document,
                chat_id=chat_id,
                document=f,
                filename="selfblur.mp4",
                disable_content_type_detection=True,
                what="self-blur final video send_document",
            )
    finally:
        try:
            await status_msg.delete()
        except Exception:
            pass

    # render ivara una passe, saved fb_pages walin ekakata (hari kipeka)
    # direct post karanna one da kiyala ahanawa - final_path eka danata
    # delete karanne na (Yes/No dekama tenaka witharai clean karanne),
    # ithin state eka methanin ASK_SELFBLUR_FB_POST ekata mahara wenawa
    pages = context.user_data.get("fb_pages") or {}
    if not pages:
        shutil.rmtree(Path(final_path).parent, ignore_errors=True)
        _cleanup_selfblur(data)
        return ConversationHandler.END

    data["selfblur_rendered_path"] = final_path
    rows = []
    for pid, info in pages.items():
        label = info.get("label") or pid
        short = label if len(label) <= 28 else label[:28] + "…"
        rows.append([InlineKeyboardButton(f"📄 {short}", callback_data=f"sbfb_page_{pid}")])
    rows.append([InlineKeyboardButton("❌ No, Skip", callback_data="sbfb_no")])
    await context.bot.send_message(
        chat_id=chat_id,
        text="📤 *Me video eka Facebook Page ekakata direct upload karanna da?*\n\n"
        "Kæmathi Page ekak thoraganna 👇",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup(rows),
    )
    return ASK_SELFBLUR_FB_POST


async def selfblur_fb_post_choice_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = context.user_data
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

    final_path = data.get("selfblur_rendered_path")

    if query.data == "sbfb_no":
        if final_path:
            shutil.rmtree(Path(final_path).parent, ignore_errors=True)
        _cleanup_selfblur(data)
        return ConversationHandler.END

    pid = query.data[len("sbfb_page_"):]
    pages = data.get("fb_pages") or {}
    info = pages.get(pid)
    if not info or not final_path or not Path(final_path).exists():
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="⚠️ Page eka hari video file eka thava naha, post karanna baruna.",
        )
        if final_path:
            shutil.rmtree(Path(final_path).parent, ignore_errors=True)
        _cleanup_selfblur(data)
        return ConversationHandler.END

    data["selfblur_fb_target_page_id"] = pid
    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text="📝 *Caption + Hashtags* eka type karala send karanna:",
        parse_mode="Markdown",
    )
    return WAITING_SELFBLUR_FB_CAPTION


async def receive_selfblur_fb_caption(update: Update, context: ContextTypes.DEFAULT_TYPE):
    data = context.user_data
    caption = update.message.text or ""
    final_path = data.get("selfblur_rendered_path")
    pid = data.get("selfblur_fb_target_page_id")
    pages = data.get("fb_pages") or {}
    info = pages.get(pid) if pid else None

    if not final_path or not Path(final_path).exists() or not info:
        await update.message.reply_text("⚠️ Video file eka/Page eka thava naha, post eka skip karanawa.")
        if final_path:
            shutil.rmtree(Path(final_path).parent, ignore_errors=True)
        _cleanup_selfblur(data)
        return ConversationHandler.END

    status_msg = await update.message.reply_text("⏳ Facebook Page ekata upload karanawa...")
    ok, result = await post_video_to_facebook_page(pid, info.get("token", ""), final_path, caption)
    try:
        if ok:
            await status_msg.edit_text(f"✅ Post kara! (id: `{result}`)", parse_mode="Markdown")
        else:
            await status_msg.edit_text(f"⚠️ Facebook post eka fail una: {result}")
    except Exception:
        pass

    shutil.rmtree(Path(final_path).parent, ignore_errors=True)
    _cleanup_selfblur(data)
    return ConversationHandler.END


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(START_MESSAGE, parse_mode="Markdown")


async def start_button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Post ekak iwara unu passe pennana thani '▶️ Start' button eka click
    kaloth, /start ekedi pennana instructions eka methanin pennanawa."""
    query = update.callback_query
    await query.answer()
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass
    await context.bot.send_message(
        chat_id=query.message.chat_id, text=START_MESSAGE, parse_mode="Markdown"
    )


async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    _cleanup_bg_video(context.user_data)
    _cleanup_fb_pending(context.user_data)
    _cleanup_selfblur(context.user_data)
    last_settings = context.user_data.get("last_settings")
    templates = context.user_data.get("templates")
    fb_pages = context.user_data.get("fb_pages")
    scheduled_posts = context.user_data.get("scheduled_posts")
    context.user_data.clear()
    if last_settings:
        context.user_data["last_settings"] = last_settings
    if templates:
        context.user_data["templates"] = templates
    if fb_pages:
        context.user_data["fb_pages"] = fb_pages
    if scheduled_posts:
        context.user_data["scheduled_posts"] = scheduled_posts
    await update.message.reply_text(
        "❌ Cancelled.\n\nTo start over, just type a new text and send it."
    )
    return ConversationHandler.END


async def _handle_conversation_timeout(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """conversation_timeout eka (900s / 15min) trigger unoth methanin call
    wenawa. Kalinma (methe fix karanna kalin) states dict eke methanata
    ConversationHandler.TIMEOUT ekata kisima handler ekak thibbe na - eka
    nisa 15 minutes silent unoth, state eka danata "silent" widiyata clear
    wela (user ta kisima notification ekak nathuwa, aye /start karanna one
    kiyala therenne nathuwa), e tharamatama ithuru unu bg-video temp file
    ekath (download kara tibba TikTok/Pinterest video ekak) disk eken clean
    wenne na (disk space leak). Dan methanin dekama fix karanawa: (1) user ta
    chat eke "session eka expire una" kiyala danawa, (2) bg-video/fb-pending
    temp files tika methanma clean karanawa."""
    _cleanup_bg_video(context.user_data)
    _cleanup_fb_pending(context.user_data)
    last_settings = context.user_data.get("last_settings")
    templates = context.user_data.get("templates")
    fb_pages = context.user_data.get("fb_pages")
    scheduled_posts = context.user_data.get("scheduled_posts")
    context.user_data.clear()
    if last_settings:
        context.user_data["last_settings"] = last_settings
    if templates:
        context.user_data["templates"] = templates
    if fb_pages:
        context.user_data["fb_pages"] = fb_pages
    if scheduled_posts:
        context.user_data["scheduled_posts"] = scheduled_posts

    chat_id = update.effective_chat.id if update.effective_chat else None
    if chat_id is not None:
        try:
            await context.bot.send_message(
                chat_id=chat_id,
                text="⏳ 15 විනාඩියක් කිසිම reply එකක් නැති නිසා, මේ post එකේ session එක "
                "expire වුනා.\n\nඅලුතෙන් patan gaanna one nam, text එකක් type කරලා evanna.",
            )
        except Exception:
            pass
    return ConversationHandler.END


async def _handle_pages_conv_timeout(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """"/pages" manager eke conversation_timeout eka (600s) trigger unoth
    methanin - meke temp file ekak naha, ithin user ta notify karanawa
    witharai."""
    chat_id = update.effective_chat.id if update.effective_chat else None
    if chat_id is not None:
        try:
            await context.bot.send_message(
                chat_id=chat_id,
                text="⏳ Page setup eke session eka time-out una. /pages ආයෙත් run කරන්න.",
            )
        except Exception:
            pass
    return ConversationHandler.END


# state ekak (button click ekak, ho specific file type ekak) monawahari
# expect karana thanaka, user ta ese unath wenama widiyaka input ekak (e.g.
# button eka press karanne nathuwa text ekak/link ekak, ho photo ekak asha
# karaddi video ekak) evapuwoth - e message eka danata state eke registered
# handler ekatath match wenne na, ithin ese kalin thibba widiyata mulu conv
# eke fallback ekata (receive_text) wetila, mulu post ekama silently reset
# wela aluthenma patan gannawa (user ta e vidiyaka danneth nathuwa progress
# eka nashi wela yanawa), nathnam (media type waradi nam) kisima response
# ekakuth nathuwa bot eka mulinma silent wenawa.
#
# Methanin hadana handler eka state ekakatama "catch-all" widiyata (e state
# eke thiyena specific handlers walata passe, aluth atma widiyata) danna
# ekak - match wena widiyaka input ekak nathnam methanin hint ekak dila,
# danata state ekemama user ta hitaganna denawa (reset karanne na).
def _unexpected_input_handler(state: int, hint: str):
    async def _handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
        await update.effective_message.reply_text(hint)
        return state
    return _handler


class _GroupBotTriggerFilter(filters.MessageFilter):
    """Group/supergroup chat ekaka witharai apply wena filter ekak - private
    chat ekata effect ekak nehe (eka wenama entry_point ekakin handle wenne).

    Group ekaka type wena OKKOMA text ekatama bot eka react unoth (kalin
    kaloth wage), e group eke normal chat eka completely interrupt wenawa -
    e nisa methanin match wenne METHANA witharai:
      1) user kenek bot ekage message ekakata "reply" kaloth, hari
      2) user kenek message eke "@botusername" kiyala mention kaloth
    e widihata bot ekatama directly address karapu message ekakata witharak
    "aluth post ekak patan ganna" flow eka fire wenawa - anith okkoma group
    chat eka wagema issue ekak nathuwa yanawa."""

    def filter(self, message):
        if not message.text:
            return False
        bot_id = _BOT_INFO.get("id")
        bot_username = _BOT_INFO.get("username")
        if (
            bot_id is not None
            and message.reply_to_message
            and message.reply_to_message.from_user
            and message.reply_to_message.from_user.id == bot_id
        ):
            return True
        if bot_username and f"@{bot_username.lower()}" in message.text.lower():
            return True
        return False


_group_bot_trigger_filter = _GroupBotTriggerFilter()


# ---------------- LIFECYCLE (persistent browser) ----------------

async def post_init(application):
    application.bot_data["playwright"] = await async_playwright().start()
    application.bot_data["browser"] = await application.bot_data["playwright"].chromium.launch()
    logger.info("Playwright browser launched and ready.")

    # group ekaka "aluth post ekak patan ganna" bare-text trigger eka - bot ta
    # reply karapu / bot ta @mention karapu message witharak fire karanna
    # _BOT_INFO["id"]/["username"] eka methanin fill karanawa (application.bot
    # eken hama welema id/username ganna puluwan - initialize wela ithin)
    _BOT_INFO["id"] = application.bot.id
    _BOT_INFO["username"] = application.bot.username
    logger.info("Bot username resolved as @%s (id=%s) for group mention/reply trigger.",
                _BOT_INFO["username"], _BOT_INFO["id"])


async def post_shutdown(application):
    browser = application.bot_data.get("browser")
    playwright = application.bot_data.get("playwright")
    if browser:
        await browser.close()
    if playwright:
        await playwright.stop()
    logger.info("Playwright browser closed.")


def main():
    SCHEDULED_POSTS_DIR.mkdir(parents=True, exist_ok=True)

    # bot_data withara exclude karanawa - eyata thiyenne Playwright browser/playwright
    # objects (pickle karanna bari ewa), eyata try karoth WHOLE save eka (user_data
    # ekath ekka) silently fail wela last_settings vage data ehema restart ekakin
    # passe ain wela yanawa. user_data witharak persist karoth mekath fix wenawa.
    persistence = PicklePersistence(
        filepath=PERSISTENCE_FILE,
        store_data=PersistenceInput(bot_data=False, chat_data=True, user_data=True, callback_data=True),
    )

    # Generous timeouts for the bot API HTTP client - default 5s connect/read/
    # write/pool timeouts are too tight for uploading full-size photos/videos
    # from a modest VPS and were causing the httpx.ReadError seen in the logs.
    request = HTTPXRequest(
        connect_timeout=REQUEST_CONNECT_TIMEOUT,
        read_timeout=REQUEST_READ_TIMEOUT,
        write_timeout=REQUEST_WRITE_TIMEOUT,
        pool_timeout=REQUEST_POOL_TIMEOUT,
    )

    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .request(request)
        .persistence(persistence)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    conv = ConversationHandler(
        # Bare text (no command) patan gannawa: private chat ekaka okkoma
        # text ekatama, group/supergroup ekaka nam bot ekatama address
        # karapu (reply/@mention) message ekatama witharak - anith siyalu
        # group chat eka wagema normal ekatama react wenna denne nathuwa.
        # Group ekaka "/newpost <text>" (CommandHandler eka pahalin) eken
        # directlama patanna puluwan.
        entry_points=[
            MessageHandler(filters.ChatType.PRIVATE & filters.TEXT & ~filters.COMMAND, receive_text),
            MessageHandler(
                filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND & _group_bot_trigger_filter,
                receive_text,
            ),
            CommandHandler("newpost", _newpost_command),
        ],
        states={
            ASK_BACKGROUND: [
                CallbackQueryHandler(bg_choice_callback, pattern="^bg_choice_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_BACKGROUND,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් background type එක තෝරන්න "
                    "(Upload a photo / Use a video / Plain background), හෝ /cancel කරන්න."
                )),
            ],
            WAITING_BG_IMAGE: [
                MessageHandler(filters.PHOTO | filters.Document.IMAGE, receive_bg_image),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_BG_IMAGE,
                    "⚠️ Photo එකක් (image file එකක් විදිහටත් පුළුවන්) එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_BG_VIDEO_PLATFORM: [
                CallbackQueryHandler(bg_video_platform_callback, pattern="^bgvid_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_BG_VIDEO_PLATFORM,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න (TikTok link / Pinterest link / "
                    "Upload from phone), හෝ /cancel කරන්න."
                )),
            ],
            WAITING_BG_VIDEO_LINK: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_bg_video_link),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_BG_VIDEO_LINK,
                    "⚠️ TikTok/Pinterest video link එක text විදිහට type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_BG_VIDEO_UPLOAD: [
                MessageHandler(filters.VIDEO | filters.Document.VIDEO, receive_bg_video_upload),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_BG_VIDEO_UPLOAD,
                    "⚠️ Video file එකක් upload කරන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_BG_VIDEO_AUDIO: [
                CallbackQueryHandler(bg_audio_choice_callback, pattern="^audio_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_BG_VIDEO_AUDIO,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_BG_AUDIO_SOURCE: [
                CallbackQueryHandler(bg_audio_source_callback, pattern="^audiosrc_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_BG_AUDIO_SOURCE,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_BG_AUDIO_UPLOAD: [
                MessageHandler(
                    filters.AUDIO | filters.VOICE | filters.Document.AUDIO, receive_bg_audio_upload
                ),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_BG_AUDIO_UPLOAD,
                    "⚠️ Audio/voice file එකක් upload කරන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_BG_AUDIO_TIKTOK_LINK: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_bg_audio_tiktok_link),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_BG_AUDIO_TIKTOK_LINK,
                    "⚠️ TikTok link එක text විදිහට type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_AUDIO_FIT: [
                CallbackQueryHandler(bg_audio_fit_callback, pattern="^audiofit_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_AUDIO_FIT,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            # "🎬 Photo eka Video ekak karanna" - music skip kaloth witharak
            # methanata enawa (video length eka preset buttons walin ahanawa)
            ASK_PHOTO_VIDEO_DURATION: [
                CallbackQueryHandler(photo_video_duration_callback, pattern="^pvdur_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_PHOTO_VIDEO_DURATION,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් වීඩියෝ length එක තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_EMOJI: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_emoji),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_EMOJI,
                    "⚠️ Emoji ටික text විදිහට type කරලා එවන්න (e.g. 🔥❤️👍), හෝ /cancel කරන්න."
                )),
            ],
            WAITING_COLOR: [
                CallbackQueryHandler(color_callback, pattern="^color_"),
                CallbackQueryHandler(use_last_settings_callback, pattern="^use_last_settings$"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_COLOR,
                    "⚠️ කරුණාකර උඩින් තියෙන color button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            ADJUSTING: [
                CallbackQueryHandler(color_callback, pattern="^color_"),
                CallbackQueryHandler(use_last_settings_callback, pattern="^use_last_settings$"),
                CallbackQueryHandler(adjust_callback, pattern="^adj_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ADJUSTING,
                    "⚠️ කරුණාකර උඩින් තියෙන adjust button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_EDIT_TEXT: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_edit_text),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_EDIT_TEXT,
                    "⚠️ අලුත් text එක type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            CHOOSE_LOGO_TYPE: [
                CallbackQueryHandler(logo_choice_callback, pattern="^logo_choice_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    CHOOSE_LOGO_TYPE,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_LOGO_IMAGE: [
                MessageHandler(filters.PHOTO | filters.Document.IMAGE, receive_logo_image),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_LOGO_IMAGE,
                    "⚠️ Photo එකක් (image file එකක් විදිහටත් පුළුවන්) එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_LOGO_TEXT: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_logo_text),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_LOGO_TEXT,
                    "⚠️ Logo text එක type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            WATERMARK_MENU: [
                CallbackQueryHandler(watermark_callback, pattern="^wm_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WATERMARK_MENU,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_WATERMARK_IMAGE: [
                MessageHandler(filters.PHOTO | filters.Document.IMAGE, receive_watermark_image),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_WATERMARK_IMAGE,
                    "⚠️ Photo එකක් (image file එකක් විදිහටත් පුළුවන්) එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_WATERMARK_TEXT: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_watermark_text),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_WATERMARK_TEXT,
                    "⚠️ Watermark text එක type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_VIDEO_PLATFORM: [
                CallbackQueryHandler(video_platform_callback, pattern="^vid_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_VIDEO_PLATFORM,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න (TikTok / Pinterest), හෝ /cancel කරන්න."
                )),
            ],
            WAITING_VIDEO_LINK: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_video_link),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_VIDEO_LINK,
                    "⚠️ Video link එක text විදිහට type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_TEMPLATE_NAME: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_template_name),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_TEMPLATE_NAME,
                    "⚠️ Template එකේ නම text විදිහට type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            CHOOSE_TEMPLATE: [
                CallbackQueryHandler(template_use_callback, pattern="^tpl_use_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    CHOOSE_TEMPLATE,
                    "⚠️ කරුණාකර උඩින් තියෙන template එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_REEDIT: [
                CallbackQueryHandler(reedit_choice_callback, pattern="^reedit_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_REEDIT,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_FB_POST: [
                CallbackQueryHandler(fb_post_choice_callback, pattern="^fb_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_FB_POST,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            WAITING_FB_CAPTION: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_fb_caption),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_FB_CAPTION,
                    "⚠️ Facebook caption එක text විදිහට type කරලා එවන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_FB_RETRY: [
                CallbackQueryHandler(fb_retry_choice_callback, pattern="^fb_retry"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_FB_RETRY,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න, හෝ /cancel කරන්න."
                )),
            ],
            ASK_FB_SCHEDULE: [
                CallbackQueryHandler(fb_schedule_choice_callback, pattern="^fb_when_"),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    ASK_FB_SCHEDULE,
                    "⚠️ කරුණාකර උඩින් තියෙන button එකකින් තෝරන්න (Post Now / Schedule / Draft), හෝ /cancel කරන්න."
                )),
            ],
            WAITING_SCHEDULE_TIME: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_schedule_time),
                MessageHandler(filters.ALL & ~filters.COMMAND, _unexpected_input_handler(
                    WAITING_SCHEDULE_TIME,
                    "⚠️ Date/Time එක `DD-MM-YYYY HH:MM` විදිහට (24-hour, Sri Lankan time) type කරලා එවන්න, "
                    "හෝ /cancel කරන්න."
                )),
            ],
            # 15 min silent unoth methanin trigger wenawa - user ta notify karala,
            # bg-video/fb-pending temp files tika clean karanawa (issue: kalin
            # methanata handler ekak thibbe na, ithin silent widiyata END unoth
            # e cleanup ekath sidu wune na).
            ConversationHandler.TIMEOUT: [
                MessageHandler(filters.ALL, _handle_conversation_timeout),
                CallbackQueryHandler(_handle_conversation_timeout),
            ],
        },
        # oyage state eka monaha unath (emoji/color/adjust ekaka waiting unath),
        # user aluth text ekak evapuwoth eeka fallback ekak vidihata catch karala
        # aluthen patan gannawa - ehema nathnam bot restart ekakin passe user
        # kalin state ekaka "stuck" unoth aluth text ekata silent wenawa.
        # (private chat ekaka okkoma text ekatama, group ekaka nam "/newpost"
        # eken hari bot ekatama reply/@mention karapu text ekakin hari.)
        fallbacks=[
            CommandHandler("cancel", cancel),
            CommandHandler("newpost", _newpost_command),
            MessageHandler(filters.ChatType.PRIVATE & filters.TEXT & ~filters.COMMAND, receive_text),
            MessageHandler(
                filters.ChatType.GROUPS & filters.TEXT & ~filters.COMMAND & _group_bot_trigger_filter,
                receive_text,
            ),
        ],
        # 15 minutes kisima response ekak nathuwa hitiyoth, state eka auto-clear
        # karala aye stuck wena eka wenna denne nehe.
        conversation_timeout=900,
        name="post_creator_conv",
        persistent=True,
    )

    # "/pages" - Facebook pages manage karana wenama conversation eka. Meka
    # main "conv" ekata kalinma add karanawa - user "pages_add"/"pages_edittoken_"
    # flow ekaka (text ahana state ekaka) hitiyoth, e text eka methanin witharak
    # catch wenna one, main conv eke generic text-entry-point eken "aluth post
    # ekak" widiyata misinterpret wenna denne nathuwa (handler registration
    # order ekama, ConversationHandler dekakma matching state ekakadi priority
    # eka decide karanne).
    pages_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(pages_add_start, pattern="^pages_add$"),
            CallbackQueryHandler(pages_edittoken_start, pattern="^pages_edittoken_"),
        ],
        states={
            WAITING_PAGE_LABEL: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_page_label),
            ],
            WAITING_PAGE_ADD_ID: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_page_add_id),
            ],
            WAITING_PAGE_ADD_TOKEN: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_page_add_token),
            ],
            WAITING_PAGE_EDIT_TOKEN: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_page_edit_token),
            ],
            ConversationHandler.TIMEOUT: [
                MessageHandler(filters.ALL, _handle_pages_conv_timeout),
                CallbackQueryHandler(_handle_pages_conv_timeout),
            ],
        },
        fallbacks=[CommandHandler("cancel", pages_manager_cancel)],
        conversation_timeout=600,
        name="pages_manager_conv",
        persistent=True,
    )

    # "/schedule" - scheduled/draft Facebook posts manage karana wenama
    # conversation eka (pages_conv wagema). Meka main "conv" ekata kalinma
    # add karanawa - user "sch_edittime_" flow eke (time ahana state ekaka)
    # hitiyoth, e text eka methanin witharak catch wenna one, main conv eke
    # generic text-entry-point eken "aluth post ekak" widiyata misinterpret
    # wenna denne nathuwa.
    schedule_edit_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(schedule_edittime_start, pattern="^sch_edittime_")],
        states={
            WAITING_EDIT_SCHEDULE_TIME: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_edit_schedule_time),
            ],
        },
        fallbacks=[CommandHandler("cancel", schedule_edittime_cancel)],
        conversation_timeout=600,
        name="schedule_edit_conv",
        persistent=True,
    )

    # "/selfblur" - "self-blur video" feature eka, main "conv" ekata
    # sampurnayenma independent wenama conversation ekak (pages_conv/
    # schedule_edit_conv wagema) - meka main conv ekata KALINMA add karanawa,
    # user link/video/audio type/upload karana welavata, main conv eke
    # generic text-entry-point eken "aluth post ekak" widiyata misinterpret
    # wenna denne nathuwa.
    selfblur_conv = ConversationHandler(
        entry_points=[CommandHandler("selfblur", selfblur_command)],
        states={
            SELFBLUR_ASK_VIDEO_PLATFORM: [
                CallbackQueryHandler(selfblur_platform_callback, pattern="^sbvid_"),
            ],
            WAITING_SELFBLUR_VIDEO_LINK: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_video_link),
            ],
            WAITING_SELFBLUR_VIDEO_UPLOAD: [
                MessageHandler(filters.VIDEO | filters.Document.VIDEO, receive_selfblur_video_upload),
            ],
            SELFBLUR_ADJUSTING: [
                CallbackQueryHandler(selfblur_adjust_callback, pattern="^sb_"),
            ],
            WAITING_SELFBLUR_AUDIO_UPLOAD: [
                MessageHandler(filters.AUDIO | filters.VOICE | filters.Document.AUDIO, receive_selfblur_audio_upload),
            ],
            WAITING_SELFBLUR_AUDIO_TIKTOK_LINK: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_audio_tiktok_link),
            ],
            WAITING_SELFBLUR_WATERMARK_IMAGE: [
                MessageHandler(filters.PHOTO | filters.Document.IMAGE, receive_selfblur_watermark_image),
            ],
            WAITING_SELFBLUR_LOGO_IMAGE: [
                MessageHandler(filters.PHOTO | filters.Document.IMAGE, receive_selfblur_logo_image),
            ],
            WAITING_SELFBLUR_LOGO_TEXT: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_logo_text),
            ],
            WAITING_SELFBLUR_WATERMARK_TEXT: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_watermark_text),
            ],
            WAITING_SELFBLUR_MANUAL_VALUE: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_manual_value),
            ],
            WAITING_SELFBLUR_BG_IMAGE: [
                MessageHandler(filters.PHOTO | filters.Document.IMAGE, receive_selfblur_bg_image),
            ],
            WAITING_SELFBLUR_BG_VIDEO: [
                MessageHandler(filters.VIDEO | filters.Document.VIDEO, receive_selfblur_bg_video),
            ],
            WAITING_SELFBLUR_TEMPLATE_NAME: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_template_name),
            ],
            WAITING_SELFBLUR_TEXT: [
                CommandHandler("skip", selfblur_skip_text),
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_text),
            ],
            WAITING_SELFBLUR_EMOJI: [
                CommandHandler("skip", selfblur_skip_emoji),
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_emoji),
            ],
            ASK_SELFBLUR_FB_POST: [
                CallbackQueryHandler(selfblur_fb_post_choice_callback, pattern="^sbfb_"),
            ],
            WAITING_SELFBLUR_FB_CAPTION: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_selfblur_fb_caption),
            ],
        },
        fallbacks=[CommandHandler("cancel", cancel), CommandHandler("selfblur", selfblur_command)],
        conversation_timeout=600,
        name="selfblur_conv",
        persistent=True,
    )

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("templates", list_templates))
    app.add_handler(CommandHandler("pages", pages_command))
    app.add_handler(CommandHandler("schedule", schedule_command))
    app.add_handler(CallbackQueryHandler(template_delete_callback, pattern="^tpl_delete_"))
    app.add_handler(CallbackQueryHandler(template_preview_callback, pattern="^tpl_preview_"))
    app.add_handler(CallbackQueryHandler(start_button_callback, pattern="^start_new_post$"))
    app.add_handler(CallbackQueryHandler(pages_view_callback, pattern="^pages_view_"))
    app.add_handler(CallbackQueryHandler(pages_delete_callback, pattern="^pages_delete_"))
    app.add_handler(CallbackQueryHandler(pages_back_callback, pattern="^pages_back$"))
    app.add_handler(CallbackQueryHandler(pages_guide_callback, pattern="^pages_guide$"))
    app.add_handler(CallbackQueryHandler(schedule_view_callback, pattern="^sch_view_"))
    app.add_handler(CallbackQueryHandler(schedule_delete_callback, pattern="^sch_delete_"))
    app.add_handler(CallbackQueryHandler(schedule_postnow_callback, pattern="^sch_postnow_"))
    app.add_handler(CallbackQueryHandler(schedule_back_callback, pattern="^sch_back$"))
    app.add_handler(pages_conv)
    app.add_handler(schedule_edit_conv)
    app.add_handler(selfblur_conv)
    app.add_handler(conv)

    # scheduled posts okkoma periodic widiyata check karala, due unu ewa
    # auto-post karana background job eka. job_queue eka load wenne
    # "python-telegram-bot[job-queue]" extra eka install karala thibunoth
    # witharai - eka nathnam scheduled posts manually witharai post karanna
    # puluwan ("/schedule" -> "📤 දැන්ම Post කරන්න").
    if app.job_queue is not None:
        app.job_queue.run_repeating(_check_scheduled_posts, interval=SCHEDULE_CHECK_INTERVAL_SECONDS, first=10)
    else:
        logger.warning(
            "JobQueue eka load unne na - scheduled posts auto-post wenne na. Fix karanna: "
            "'pip install \"python-telegram-bot[job-queue]\"' karala bot eka restart karanna."
        )

    app.run_polling()


if __name__ == "__main__":
    main()