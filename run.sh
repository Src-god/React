#!/usr/bin/env bash
# Render launcher: restart the single Python poller after SIGKILL (often OOM).
# If this launcher/the instance is killed too, Render's /healthz check is the fallback.
set -u
cd "$(dirname "$0")" || exit 1

child_pid=""
delay_pid=""
stopping=0

stop() {
    stopping=1
    if [[ -n "$child_pid" ]]; then
        kill -TERM "$child_pid" 2>/dev/null || true
    fi
    if [[ -n "$delay_pid" ]]; then
        kill -TERM "$delay_pid" 2>/dev/null || true
    fi
}
trap stop TERM INT

retries=0
while (( !stopping )); do
    python -u bot.py &
    child_pid=$!
    wait "$child_pid"
    code=$?
    if (( stopping )); then
        # A signal can interrupt wait before the child has exited; reap it.
        wait "$child_pid" 2>/dev/null || true
        exit 0
    fi
    child_pid=""

    if (( code != 137 )); then
        # Do not conceal bad config or other application errors in a hot loop.
        printf 'Bot exited with status %s; leaving recovery to Render.\n' "$code" >&2
        exit "$code"
    fi

    retries=$(( retries < 5 ? retries + 1 : 5 ))
    delay=$(( 1 << retries ))  # 2, 4, 8, 16, then at most 32 seconds.
    printf 'Bot received SIGKILL (exit 137; possible OOM); retrying in %ss.\n' "$delay" >&2
    sleep "$delay" &
    delay_pid=$!
    wait "$delay_pid" || true
    delay_pid=""
done
