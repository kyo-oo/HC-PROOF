#!/usr/bin/env bash
# ARK RESURRECT — restore every critical file if wiped (even by force-delete).
# Sources: vault git history, snapshot tarballs, GitHub mirror, Drive bag, public repo clone.
set -u
ARK=/home/z/ark
FALLBACK=/home/z/my-project/.ark
TOKEN_PATH=/home/z/bag/downloaded/extracted/erdos-zipbag/secrets/ghtoken.txt
DRIVE_BAG_URL='https://drive.usercontent.google.com/download?id=1ZCY5hbZyId7AWeBD-o0yOiRFlxGmKnW-&export=download&confirm=t'
BRANCH="research/gpt6-gst-hypothesis-part1-chow-square-20261110"

report() { echo "resurrected: $1"; }

# 0. If ARK itself is wiped, restore it from the fallback first
if [ ! -d "$ARK" ] || [ ! -f "$ARK/protect.sh" ]; then
  mkdir -p "$ARK"
  cp -r "$FALLBACK/scripts/." "$ARK/" 2>/dev/null
  report "ARK system itself (from /home/z/my-project/.ark fallback)"
fi

# 1. Token / bag
if [ ! -s "$TOKEN_PATH" ]; then
  mkdir -p /home/z/bag/downloaded
  if [ -d "$FALLBACK/bag/downloaded/extracted" ]; then
    cp -r "$FALLBACK/bag/downloaded/extracted" /home/z/bag/downloaded/ 2>/dev/null
  else
    curl -sL "$DRIVE_BAG_URL" -o /home/z/bag/downloaded/bag.zip --max-time 180
    unzip -o -q /home/z/bag/downloaded/bag.zip -d /home/z/bag/downloaded/extracted 2>/dev/null
  fi
  report "GitHub token bag"
fi

# 2. Campaign repo (public — anonymous clone always works)
if [ ! -d /home/z/hc-repo/.git ]; then
  if ls "$FALLBACK/snapshots"/hc-repo-*.bundle >/dev/null 2>&1; then
    NEWEST=$(ls -t "$FALLBACK/snapshots"/hc-repo-*.bundle | head -1)
    git clone -q "$NEWEST" /home/z/hc-repo 2>/dev/null || true
  fi
  if [ ! -d /home/z/hc-repo/.git ]; then
    git clone -q --single-branch --branch "$BRANCH" https://github.com/kyo-oo/HC-PROOF.git /home/z/hc-repo
  fi
  report "HC-PROOF campaign repo (HEAD $(cd /home/z/hc-repo && git rev-parse --short HEAD 2>/dev/null))"
fi

# 3. Vault from GitHub mirror (deepest history)
TOKEN=""
[ -s "$TOKEN_PATH" ] && TOKEN=$(cat "$TOKEN_PATH")
if [ ! -d "$ARK/vault/.git" ] && [ -n "$TOKEN" ]; then
  git clone -q --branch ark/sandbox-vault --single-branch "https://x-access-token:$TOKEN@github.com/kyo-oo/HC-PROOF.git" "$ARK/vault" 2>/dev/null || mkdir -p "$ARK/vault"
  report "ARK vault (from GitHub mirror)"
fi

# 4. Snapshots: restore newest into place
if [ ! -d "$ARK/snapshots" ] && [ -d "$FALLBACK/snapshots" ]; then
  mkdir -p "$ARK/snapshots"
  cp -r "$FALLBACK/snapshots/." "$ARK/snapshots/" 2>/dev/null
  report "snapshot layer"
fi

# 5. Project source files
for D in src skills scripts sandbox-data; do
  if [ ! -d "/home/z/my-project/$D" ]; then
    NEWEST=$(ls -t "$FALLBACK/snapshots"/sandbox-*.tar.gz 2>/dev/null | head -1)
    if [ -n "$NEWEST" ] && tar -tzf "$NEWEST" "my-project/$D" >/dev/null 2>&1; then
      if tar -xzf "$NEWEST" -C /home/z "my-project/$D" 2>/dev/null && [ -d "/home/z/my-project/$D" ]; then
        report "my-project/$D (from snapshot $NEWEST)"
      fi
    fi
    [ -d "/home/z/my-project/$D" ] || mkdir -p "/home/z/my-project/$D"
  fi
done

# 6. If even the fallback is gone: rebuild from vault git (GitHub mirror holds history)
if [ ! -d "$FALLBACK" ] && [ -d "$ARK/vault/.git" ]; then
  mkdir -p "$FALLBACK"
  cp -r "$ARK/vault/vault/home/z/my-project/." "$FALLBACK/" 2>/dev/null
  report "fallback layer (from vault)"
fi

echo "resurrection complete — run protect.sh to re-vault everything"
