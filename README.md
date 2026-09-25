# Telegram Channel Reaction Bot

**Python 3.10+ · python-telegram-bot 22.8 · SQLite**

A Telegram bot with force-sub membership checks, admin-verified channel linking, and one primary-bot reaction on each **new** post. Optional **Multi-Bot Premium** unlocks up to **five additional, owner-controlled bots**, each configurable with its own allowed emoji/custom emoji ID, per linked channel for **100 Stars / 30 days (one-time)** or via owner manual grant. Inline-keyboard controls, SQLite persistence, and a verification animation are included.

**One Python bot file:** All Telegram logic, SQLite storage, read-only connectivity check, flying-emoji GIF, and health server live in **`bot.py`**. A tiny **`run.sh`** starts just one Python poller and restarts it after exit 137 (possible OOM) on Render. Other files are documentation, dependencies, the placeholder `config.js`, `.gitignore`, and `render.yaml`. No Node.js process or separate Python web-server file is needed.

> **Important limit:** Telegram limits each bot to **up to one reaction per message** [1](https://core.telegram.org/bots/api). Five authorized child bots can each *try* one reaction of their own when they are channel admins; these are **bot reactions, not real members or guaranteed engagement**. Do not claim otherwise to buyers. One "Join All" button also **cannot automatically join** users to channels: users join manually and press **Check Membership**.

> **SECURITY:** A bot token was pasted into this chat. Treat it as compromised: revoke it using @BotFather (`/revoke`) and generate a **new** one. Never paste primary/child-bot tokens into chat or this shared workspace. Put real credentials **only in a private copy of `config.js` on your own machine/server or Render's secret environment variables**. The bundled `config.js` contains placeholders only; this project does not use or include the previously shared token. Never commit a token-filled `config.js` to Git.

## Quick start

1. Create a bot using Telegram **@BotFather** and obtain its token. Find your **numeric** Telegram user ID (for example using @userinfobot). **Never paste the token into public chats/repositories.**
2. In the project directory:

   ```bash
   python -m venv .venv
   source .venv/bin/activate          # Windows: .venv\Scripts\activate
   pip install -r requirements.txt
   ```

3. Open the bundled **`config.js`** *only on your private computer/server*, not in this shared workspace. It contains this safe placeholder example:

   ```js
   module.exports = {
     "BOT_TOKEN": "REPLACE_WITH_NEW_PRIVATE_TOKEN",
     "OWNER_ID": 123456789,
     "CHILD_BOT_TOKENS": [],
     "DB_PATH": "bot.sqlite3",
     "DEFAULT_EMOJI": "👍",
     "CELEBRATION_EFFECT_ID": "5046509860389126442"
   };
   ```

   Replace `BOT_TOKEN` with the **newly rotated** main bot token and `OWNER_ID` with **your own numeric Telegram user ID** (use `/whoami` or @userinfobot to find it). For the optional paid Premium service, create **five separate bots you own** via @BotFather, and privately fill the array like `"CHILD_BOT_TOKENS": ["CHILD_1_TOKEN", "CHILD_2_TOKEN", "CHILD_3_TOKEN", "CHILD_4_TOKEN", "CHILD_5_TOKEN"]` using **real private credentials only on your own machine**. Leave `[]` until all five are ready; the free bot still works but Stars checkout/Multi React stay disabled. `config.js` must use **quoted keys, JSON-compatible values, no inline comments or trailing commas**. Python reads it as data; **Node.js is not needed**. `.env` is also supported for existing setups. Env vars take precedence over `config.js` (on Render use env vars; see below). `.gitignore` excludes real `config.js`, `.env`, and SQLite files from Git. **Never upload token-filled files to this workspace or public repositories.**
4. **After rotating the leaked token**, run `python bot.py --selfcheck` locally: it makes read-only Telegram `getMe`/admin checks using your new private config, reports only public bot usernames/admin readiness, and **never sends a reaction or charges Stars**. This agent has **not run** that live check because the shared token must be revoked first. Then run `python bot.py` for continuous reactions. SQLite uses `DB_PATH` (default `bot.sqlite3` beside `bot.py`); back it up. Run **one polling instance per primary token** and stop any existing webhook. Child bots are **API clients only**; do not run pollers for them with this project.
5. Before sharing the bot, set owner-required channels: add the bot as **admin** to each required channel, then DM the bot `/addforce @publicchannel`. For a private required channel, use `/addforce -1001234567890 https://t.me/+your_invite_code`. Use `/forces` to inspect/remove requirements. With no required channels configured, `/start` immediately shows the dashboard.
6. A user sends `/start`, opens every required channel's join button, **joins manually**, then taps **Join All — Check Membership**. When verified, the dashboard is shown and the bot sends one flying-emoji GIF with a native Telegram message effect if accepted. The bot must **remain admin** in every required channel for reliable `getChatMember` checks [1](https://core.telegram.org/bots/api).
7. User taps **Set Channel** (or `/setchannel`), makes the **main** bot an **admin** of their target channel, enables reactions, and **forwards an existing channel post into the main bot's private chat**. The main bot verifies origin and admin access, links the channel and tries a test reaction. Future new posts receive the main bot's one reaction.
8. Premium users use `/childbots` to see the owner-controlled bots' **public usernames** (not tokens). They manually add **all five** as admins to **each** linked channel. In **My Channels → Channel Settings → 5 Extra Emojis**, they choose one reaction for **each child bot** using inline buttons (or `/setmulti`); the main bot's emoji is configured separately with **Change Reaction**. Then use `/multireact CHANNEL_ID` or the inline **Enable Multi React** button. The main bot verifies its own, the registered user's, and all five child bots' admin status before enabling. Free reaction remains available when Premium expires; extra reactions stop until Premium is renewed.

A channel with **protected content / forwarding disabled** cannot use this forward-based setup as written; forwarding must be possible for the setup post. Standard reaction emojis must be allowed in the channel. Edited posts are not processed. Already-published historical posts are not bulk-processed; only the forwarded setup post is tried once as a test.

## Render deployment / alive server

- `render.yaml` configures **one paid Render Python Web Service** (`0.5c-512mb`), one **persistent 1 GB disk**, `DB_PATH=/var/data/bot.sqlite3`, and `/healthz`. Review the **compute and disk charges** before deploying. Render's Free Web Services **sleep after 15 minutes without incoming traffic** and lose local SQLite files on spin-down/redeploy; **Free cannot attach a persistent disk** [1](https://render.com/docs/free) [2](https://render.com/docs/disks). A health endpoint or self-ping **does not guarantee 24×7 on Free**. Paid plans do not idle-spin-down, but restarts, deploys, internet/Telegram outages, and maintenance can still cause interruption; don't advertise 100% uptime [1](https://render.com/docs/faq).
- Put the contents of the ZIP's `telegram_reaction_bot/` folder **at the root of a private Git repo**: `bot.py`, `run.sh`, `requirements.txt`, `README.md`, `.gitignore`, `render.yaml`. **Do not commit `config.js` after filling it with secrets** (`.gitignore` already excludes it). On Render, use **New → Blueprint**, choose your Git repo, and review the paid plan/disk. The `sync: false` entries prompt for secret values on initial creation; on an existing service, edit the environment variables in Render's dashboard [1](https://render.com/docs/blueprint-spec).
- **Simplest Render secret setup:** In Render's secret env settings set `BOT_TOKEN` to the **new** private primary token, `OWNER_ID` to **your numeric ID** (example `123456789`), and `CHILD_BOT_TOKENS` to **five distinct owner-managed tokens separated by commas** (no quote marks/spaces around tokens). `DB_PATH` is preconfigured to the persistent disk path. Environment variables override `config.js`. If you don't have all five child bots yet, leave `CHILD_BOT_TOKENS` blank; free features run, Stars checkout disabled. Never paste tokens in chat, Git, logs or `render.yaml`.
- **If you specifically want `config.js` on Render:** Render Dashboard → your service → **Environment → Secret Files → Add Secret File** named `config.js`; privately paste your completed JSON-compatible `module.exports = {...};` there. Render supplies it at `/etc/secrets/config.js` and in the Python service root [1](https://render.com/docs/configure-environment-variables). **Remove/unset** `BOT_TOKEN`, `OWNER_ID`, and `CHILD_BOT_TOKENS` environment variables on that service, otherwise they override the file (a blank env value also overrides it). Keep `DB_PATH=/var/data/bot.sqlite3` as configured in `render.yaml`. A Blueprint prompts for the secret env vars initially; switching to a Secret File afterward requires clearing those env vars and redeploying. Do **not** commit the credential-filled file.
- On Render, `render.yaml` starts **`bash run.sh`**, which runs a *single* `python -u bot.py` child. The Python process runs Telegram polling and a tiny HTTP readiness server on `0.0.0.0:$PORT` (Render's default is port 10000 [1](https://render.com/docs/web-services)). `https://YOUR-SERVICE.onrender.com/healthz` returns HTTP **200** with `{"status":"ready"}` only after polling starts, **503** while starting; `/` is also a status endpoint. It **never serves** `config.js`, bot source, `.env`, or the database. A ready response confirms process readiness, **not that Telegram accepts every reaction/payment**. Render uses `/healthz` for service health [1](https://render.com/docs/health-checks). Locally, the HTTP server stays off unless `HEALTH_SERVER=1` or `PORT` is set; `--selfcheck` never launches it.
- Run only **one** poller for this main token (stop other Render/local copies and any webhook). Back up `/var/data/bot.sqlite3` to secure external storage; this SQLite database includes Premium payments/refunds and channel settings. First test with owner `/grantpremium USER_ID 1`, child bots as admins and a new channel post **without charging Stars**; then test Stars carefully. This agent has not deployed to your Render account or used any real token.

### OOM restart, 30–40 channels, and UptimeRobot

- **OOM/SIGKILL recovery on Render:** `run.sh` keeps one Python child at a time. If that child exits with code **137** (SIGKILL, *possibly* OOM), it waits 2, 4, 8, 16, then up to 32 seconds between attempts and starts a new child. Exit 137 alone does **not** prove OOM; inspect Render's logs/memory graph. During Render shutdown, the launcher forwards SIGTERM to the child, waits for it to exit, and does **not** relaunch it. Other exits are surfaced to Render instead of concealing broken credentials in an aggressive restart loop. Locally on Linux/macOS you may run `bash run.sh`; normal `python bot.py` does not include the launcher.
- **If the entire instance/launcher is killed:** no in-process code can recover from SIGKILL. Render's `/healthz` check provides platform-side recovery: its docs say a running instance is automatically restarted after **60 seconds of consecutive failed health checks** [1](https://render.com/docs/health-checks). Instance replacement can take longer and is not zero-downtime for this single poller. If OOM repeats, reduce workload/investigate leaks or move to a larger paid plan; a restart is not extra RAM. Keep the persistent disk and secure backups. **A hard kill can interrupt reactions already in flight; missed posts are not guaranteed to be replayed.** The launcher itself starts no extra bot or duplicate poller.
- **For a first 30–40 moderately active channel rollout on 512 MB:** only the channel-post handler runs in limited parallelism (**four jobs maximum**); private bot menus, verification and payments keep their normal sequential handling. For a Premium post, the main-bot reaction and the channel-owner admin check overlap, followed by five child-bot reaction requests in parallel. One Premium post can make **up to seven** Telegram API requests; bursts, Telegram restrictions/rate limits, or slow network can delay/fail reactions. An offline mocked **40-channel burst** passed, but this is **not a live capacity/uptime guarantee**. Start with roughly 1–5 posts per channel per day, observe reaction latency/Render memory/logs, then increase gradually. Avoid promising instant reactions if all channels post at once.
- **UptimeRobot external alert setup (requires your own account):** deploy the **paid** Render service first; open `https://YOUR-SERVICE.onrender.com/healthz` and confirm HTTP 200 `{"status":"ready"}`. In UptimeRobot choose **Add New Monitor → HTTP(s)**, paste that full URL, choose an available check interval, add an **email/push alert contact**, and save [1](https://help.uptimerobot.com/en/articles/11358364-how-to-create-your-first-monitor-on-uptimerobot-quick-setup-guide). The endpoint supports both **HEAD and GET** (UptimeRobot often sends HEAD by default [1](https://uptimerobot.com/help/monitor-status-is-wrong/)). HTTP 503 means not ready; monitor alerts can lag the probe interval. **UptimeRobot reports downtime; it does not restart the bot, test Telegram reactions, or make Render Free + SQLite into 24×7 hosting.** Render's own health checks and the launcher perform recovery. Never paste tokens or a private Secret File into a monitor URL.

## 🎨 Five different Premium bot reactions

- Each Premium channel has **five child-bot slots**. Tap **5 Extra Emojis**, then slot 1–5 and an inline supported emoji; alternatively send `/setmulti 😍 ❤️ 🥰 🤩 💘` if you have one linked channel, or `/setmulti CHANNEL_ID 😍 ❤️ 🥰 🤩 💘` for several. `❤️` is normalized to Telegram's `❤`. Slots are saved in SQLite. The main bot keeps its separately chosen emoji. For existing channels, every child bot continues using the main emoji until a slot is customized; `main` in the command or **Use main emoji** in the picker follows that setting. Users can reset all five to main.
- **💫 and 💓 are not Telegram standard reaction emojis** [1](https://core.telegram.org/bots/api). Plainly typing `/setmulti 😍 ❤️ 💫 🥰 💓` is rejected rather than silently substituting or falsely promising reactions. For **💫 + ❤️**, set the main bot with `/setreaction CHANNEL_ID ❤️`, then choose a permitted 💫 custom emoji ID for one child bot, for example `/setmulti CHANNEL_ID custom:YOUR_NUMERIC_ID ❤️ 🥰 😍 💘` (five child slots; replace the example with a real ID). For the same appearance, tap the slot's **Send custom emoji / ID** button and send a **Telegram custom emoji entity** as its own message, or set `custom:NUMERIC_ID` in the five-emoji command. The bot extracts the `custom_emoji_id` from real Telegram custom emoji entities (even when pasted inside `/setmulti`); merely pasting ordinary Unicode 💫/💓 is not a custom emoji entity. A given custom ID can react **only if the channel explicitly allows it or it is already present on the post** [1](https://core.telegram.org/bots/api). For reliable reactions to new posts, configure channel reactions to permit the chosen custom IDs. Telegram can still reject them; the other bots continue trying their own reactions.
- Changing child-bot slots requires active Premium plus the registered user and main bot still being channel admins. **Enable Multi React** additionally requires all five child bots to be channel admins. Every bot can add at most one reaction per post; the five reactions are **from bot accounts**, not real channel members. Owner should test in a controlled channel before offering paid access: use `/grantpremium USER_ID 1` for a one-day manual test without Stars, configure five slots, enable Multi React and publish a **new** test post. Reordering `CHILD_BOT_TOKENS` later reassigns which public child bot controls each numbered slot.

## ⭐ Paid Multi-Bot Premium: terms and payments

- **100 Telegram Stars buys 30 days, one-time, not recurring.** `/premium` → **Buy** → read `/terms` → press **I agree** → Telegram's own Stars invoice. Each additional successful payment extends the paid time by 30 days. This is a **bot-service tier**, not Telegram Premium for the user's Telegram account and not a guarantee of custom emoji privileges. Telegram requires Stars (`XTR`) for digital services sold inside Telegram [1](https://core.telegram.org/bots/payments-stars).
- Paid checkout is **disabled until exactly five distinct owner-managed child bots initialize successfully**. Payment `pre_checkout_query` verifies the user, terms acceptance, invoice payload, price, freshness and that **all five child tokens still respond** (short timeout); **only a matching `successful_payment` activates access**. Duplicate charge IDs cannot double-grant. Paid access/refund information persists in SQLite. If an approved invoice is charged twice concurrently, each distinct successful charge gives 30 days instead of silently discarding a purchase.
- Owner may activate without payment with `/grantpremium USER_ID [days]` (30 days default); `/revokepremium USER_ID` cancels only manual access, **not paid time**. `/refundstars TELEGRAM_CHARGE_ID` uses Telegram's Stars refund API; for an **untracked** charge, owner first checks the buyer's Telegram receipt then uses `/refundstars USER_ID TELEGRAM_CHARGE_ID`. A refunded payment stops contributing to paid time. Customers can reach the owner via `/support message` or `/paysupport message`; the owner replies with `/reply USER_ID message`. Owner must `/start` the bot and monitor support in a timely fashion. Buyers should never send bot tokens, card details, or passwords in support messages.
- A user must still be an **admin of their own linked channel**; the main and **all five** child bots must also be admins. A Premium user may configure **different emojis for each child bot**, including custom IDs subject to Telegram/channel restrictions; **💫/💓 plain Unicode are not supported standard reactions**. Even when enabled, Telegram/network/channel restrictions may prevent one or more reactions, especially custom IDs not explicitly allowed for new posts. The bot **does not react to historical posts in bulk**, and extra bot reactions are **not organic members**. If the child-bot service becomes unavailable, owner should restore it or handle support/refunds promptly. Display the terms accurately to buyers. This is a starter implementation: review taxes, platform terms and your jurisdiction before launching a paid service.

## ✨ Premium emoji and flying celebration

- Once a non-owner passes **all** force-sub membership checks, the bot sends **one flying-emoji GIF embedded inside `bot.py`** (no separate asset file) **inside the chat message**, and tries to add Telegram's native `message_effect_id` to the **same message**. That native effect may animate confetti over the private chat [1](https://core.telegram.org/bots/api). The example 🎉 ID in `config.js` is community-reported [1](https://stackoverflow.com/questions/78600012/message-effect-id-in-telegram-bot-api), **not guaranteed** to remain valid. If Telegram rejects it, the GIF still sends. Telegram clients/settings may not show native effects; the bot cannot force an animation across the user's whole phone screen.
- A first-time verified user sees this once; repeatedly clicking Verify does not flood them. Losing membership and verifying again, or adding a new required channel, makes them eligible for a fresh celebration. The GIF is bundled in the Python file; Pillow is **not** a runtime dependency.
- In the celebration's text/caption the bot **tries your `tg-emoji` IDs** (`🤩` and `✈️`) with `parse_mode="HTML"`. If Telegram rejects custom emoji for this bot, it automatically retries with ordinary emoji. Custom emoji entities require an eligible bot (for example, a qualifying Premium bot owner for direct private messages, or additional purchased bot usernames) [1](https://core.telegram.org/bots/api).
- Owner can test immediately with `/effecttest`. To select another Telegram-native effect, send a message **with that effect** to your bot, then reply **to that message** with `/seteffect` (or use `/seteffect EFFECT_ID`). `/seteffect off` selects GIF-only. Alternatively set `"CELEBRATION_EFFECT_ID": ""` in your private `config.js` (or blank Render env value) for GIF-only, then restart. `/seteffect` changes persist in SQLite and override `.env`. To reset an effect that fails, choose another ID and run `/effecttest` again.

**GIF attribution:** The fallback is a new animated composition made from modified [1](https://github.com/jdecked/twemoji) emoji graphics (party popper, confetti, sparkles, heart, star, and party face). Twemoji graphics copyright Twitter, Inc. and contributors; graphics licensed under CC BY 4.0. Modifications: resized, layered and animated. Attribution is also printed inside the GIF.

## Commands

| Who | Command | What it does |
| --- | --- | --- |
| Anyone | `/start` | Check required channels; open dashboard or join buttons |
| Anyone | `/help` | Explain commands and limits |
| Anyone | `/whoami` | Show your numeric user ID |
| Verified user | `/setchannel` | Start admin-verified channel linking; forward a channel post next |
| Verified user | `/mychannels` | Show linked channels and inline controls |
| Verified user | `/setreaction 🔥` | Set the **main bot's** emoji (prompts for a channel if you own several) |
| Verified user | `/setreaction -1001234567890 ❤️` | Change the main emoji of a specific linked channel |
| Premium user | `/setmulti` | Inline picker for the five child bots' individual emojis/custom IDs |
| Premium user | `/setmulti [CHANNEL_ID] 😍 ❤️ 🥰 🤩 💘` | Set five separate child-bot reactions in one command |
| Premium user | `/setmulti [CHANNEL_ID] 😍 ❤️ custom:ID 🥰 💘` | Use a channel-permitted custom emoji ID for one child bot |
| Verified user | `/pause [channel_id]` | Stop reacting to new posts in a channel |
| Verified user | `/resume [channel_id]` | Resume, after admin check |
| Verified user | `/removechannel [channel_id]` | Unlink with confirmation |
| Verified user | `/premium` | Premium status and 100-Star invoice path |
| Verified user | `/childbots` | Five child-bot usernames and setup instructions |
| Verified user | `/multireact [channel_id]` | Turn on 5 child bots after Premium/admin checks |
| Verified user | `/multireact off [channel_id]` | Turn off extras without affecting the free reaction |
| Anyone | `/terms`, `/support your question` | Purchase terms and support/refund request |
| Bot owner only | `/addforce @publicchannel` | Require membership of a public channel (bot must be admin) |
| Bot owner only | `/addforce -1001234567890 https://t.me/+invite` | Require membership of a private channel |
| Bot owner only | `/forces` | See required channels and inline removal controls |
| Bot owner only | `/delforce @publicchannel` | Remove a required channel (or pass its numeric ID) |
| Bot owner only | `/seteffect EFFECT_ID` or reply `/seteffect` | Change the private-chat celebration effect |
| Bot owner only | `/seteffect off` | Use animated GIF only |
| Bot owner only | `/effecttest` | Preview the effect/custom emojis or GIF in the owner's chat |
| Bot owner only | `/grantpremium USER_ID [days]` | Grant free manual access (default 30 days) |
| Bot owner only | `/revokepremium USER_ID` | Remove manual access; paid access is unchanged |
| Bot owner only | `/refundstars CHARGE_ID` (or `/refundstars USER_ID CHARGE_ID`) | Refund a tracked payment (or verified untracked charge) |
| Bot owner only | `/reply USER_ID message` | Reply to a support request |
| Bot owner only | `/stats` | Counts, child-bot readiness and owner panel |

If there's only one linked channel, `/pause`, `/resume`, `/removechannel`, and `/setreaction 🔥` work without a channel ID. For several channels, use their inline buttons or specify the numeric ID. Someone who is no longer a channel admin cannot change its reaction or resume it. A previously linked channel cannot be claimed by a different admin while its linked admin still has admin access (except by the bot owner).

## What are `tg-emoji` tags?

The example in your message:

```html
<tg-emoji emoji-id="5332656211034652890">📞</tg-emoji>
```

is **Telegram HTML message formatting** for a **custom emoji**. `emoji-id` identifies the custom artwork; `📞` is the ordinary fallback. A Python dict with keys `whatsapp`, `telegram`, `facebook`, `instagram`, `tiktok`, `google`, `twitter` is just a **named icon map**: it does not connect those social networks to your bot. `twitter: "🐦"` is simply a regular emoji.

- With eligible bots, this tag can be sent in **message text** with `parse_mode="HTML"`. Telegram places eligibility conditions on custom emoji entities (for example, a bot with an additional purchased username or qualifying Premium owner, depending on where the bot sends the message) [1](https://core.telegram.org/bots/api).
- **Inline keyboard button text is plain text**, not HTML; putting `<tg-emoji ...>` directly into button `text` will show the literal markup. This bot therefore uses normal emoji (`🔗`, `✅`, etc.) in inline buttons.
- A custom emoji **display ID** is not itself a request to add lots of reaction counts. `/setreaction` sets the **main bot's standard reaction** only. `/setmulti` can assign a **custom emoji ID** to an individual child bot using `custom:NUMERIC_ID`, not the literal HTML `<tg-emoji>` tag. Telegram accepts that bot's reaction only if the ID is already on the post or explicitly allowed in the channel [1](https://core.telegram.org/bots/api).

API references: Telegram Bot API [1](https://core.telegram.org/bots/api) (setMessageReaction, getChatMember, formatting) and python-telegram-bot documentation [2](https://docs.python-telegram-bot.org/en/stable/).

## Troubleshooting

- **Verification unavailable:** bot must be admin in *each* force-sub channel, and the saved private invite link must actually let users join. Re-run `/addforce` to update a link.
- **Channel link fails:** check both admins, forward a real channel post (not a copied post, message from a group, or a post with protected forwarding), and make sure Telegram lets the bot access the channel.
- **Reaction fails:** enable reactions in the target channel and allow the chosen standard emoji; check the process logs for the failure type (raw API errors are not logged to protect tokens). The bot changes its own **single** reaction; it cannot add a second independent reaction as itself.
- **No reaction on posts:** keep `bash run.sh` running on Render (or `python bot.py` locally); grant the main bot admin access; check `/mychannels` status; ensure no other poller/webhook consumes main-bot updates. The project requests `channel_post` updates.
- **Repeated OOM / exit 137:** inspect Render memory metrics and logs to confirm why the process was SIGKILLed; the launcher retries one child with capped delay, but cannot solve memory exhaustion. Reduce burst rate or upgrade above 512 MB if needed. Check that only one Render instance/poller is running; don't add a second UptimeRobot-triggered bot process.
- **UptimeRobot says DOWN:** test `/healthz` (not `/bot.py`, which intentionally returns 404), check Render health/deploy logs, and ensure the paid service is up. HTTP 200 means the process and poller report running, **not** guaranteed Telegram delivery. UptimeRobot notifications alone do not restart anything.
- **Multi React OFF / fewer than 5 bots:** privately set five distinct owner-controlled `CHILD_BOT_TOKENS` in your local `config.js` or Render env and restart; read startup logs for slot numbers **without logging tokens**. Add **every** child bot as admin to the user's channel; then try `/multireact CHANNEL_ID`. Premium payment is disabled unless all five are online.
- **💫/💓 or another chosen emoji fails:** plain 💫/💓 are not standard reactions. Use the slot's **Send custom emoji / ID** control with an actual Telegram custom emoji, then permit its ID in channel reactions (or it must already be present on each post). A saved custom ID is **not a guarantee** of successful auto-reactions; check a new test post and try supported alternatives if Telegram rejects it.
- **No Stars invoice:** owner must configure all five bots; user must join required channels and agree to purchase terms. The bot requests `pre_checkout_query` updates. Payments are live: Telegram charges after its checkout flow and buyer confirmation; the bot grants access only after `successful_payment` arrives.
- **Security:** rotate any exposed primary token via @BotFather before running. `config.js`, `.env`, and SQLite are git-ignored; protect them and back up the database. Never ask users to send bot tokens, never bundle **real** secrets in the ZIP, and do not present the extra bots as genuine human engagement.

## Local tests (optional source workspace)

The **compact ZIP omits test files** to keep the release to the minimum number of files. The source workspace retains one combined offline test script, `tests/test_bot.py`. To run it from the source workspace:

```bash
python -m unittest discover -s tests -v
```

All 53 offline tests passed before packaging, including five distinct child-bot reactions, custom IDs, migrations, inline controls, config.js/env precedence, Render Secret File fallback, local HTTP health checks, a mocked 40-channel burst, and launcher SIGKILL/SIGTERM behavior. Telegram calls are mocked; live load, Render deployment, UptimeRobot alerts and bot permissions still require your own account and a new private token.
