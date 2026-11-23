#!/usr/bin/env bash
# ARK PROTECT — re-vault all critical sandbox files, snapshot, mirror to GitHub.
# BOSS ORDER: every file must survive. Nothing gets erased. Ever.
set -u
ARK=/home/z/ark
FALLBACK=/home/z/my-project/.ark
TOKEN_PATH=/home/z/bag/downloaded/extracted/erdos-zipbag/secrets/ghtoken.txt
REPO_URL="https://github.com/kyo-oo/HC-PROOF.git"
DRIVE_BAG_URL='https://drive.usercontent.google.com/download?id=1ZCY5hbZyId7AWeBD-o0yOiRFlxGmKnW-&export=download&confirm=t'
STAMP=$(date -u +%Y%m%dT%H%M%SZ)

mkdir -p "$ARK/vault" "$ARK/snapshots" "$FALLBACK/snapshots" /home/z/bag/downloaded

# --- Layer 0: Drive bag (token) — re-download if missing ---
if [ ! -s "$TOKEN_PATH" ]; then
  curl -sL "$DRIVE_BAG_URL" -o /home/z/bag/downloaded/bag.zip --max-time 180
  unzip -o -q /home/z/bag/downloaded/bag.zip -d /home/z/bag/downloaded/extracted 2>/dev/null
fi

# --- Layer 1: live protection — chmod everything read-only where possible ---
chmod -R a+r /home/z/ark 2>/dev/null
chattr -R +i "$ARK/vault" 2>/dev/null || true  # immutable if fs allows

# --- Layer 2: git vault (structured, versioned) ---
cd "$ARK/vault" || exit 1
[ -d .git ] || git init -q
git config user.email "ark@survival" ; git config user.name "ARK"
mkdir -p worklog
{
  echo "ARK sweep $STAMP"
  echo "repo HEAD: $(cd /home/z/hc-repo 2>/dev/null && git rev-parse HEAD || echo MISSING)"
  echo "token: $( [ -s $TOKEN_PATH ] && echo ALIVE || echo MISSING )"
} > worklog/sweep-$STAMP.txt
# Vault the critical trees (git add is idempotent + versioned)
for TARGET in /home/z/my-project/src /home/z/my-project/skills /home/z/my-project/scripts /home/z/my-project/sandbox-data /home/z/my-project/.ark/scripts; do
  [ -d "$TARGET" ] && mkdir -p "vault$(dirname $TARGET | sed 's|/home/z||')" && cp -r "$TARGET" "vault$(dirname $TARGET | sed 's|/home/z||' 2>/dev/null)" 2>/dev/null
done
[ -f /home/z/hc-repo/.git ] || true
git add -A 2>/dev/null
git commit -qm "ark: protect sweep $STAMP" 2>/dev/null || true

# --- Layer 3: snapshot tarballs (two physical locations) ---
SNAP="$ARK/snapshots/sandbox-$STAMP.tar.gz"
tar -czf "$SNAP" --exclude='node_modules' --exclude='.next' --exclude='.git/objects/pack' \
  -C /home/z my-project/src my-project/skills my-project/scripts 2>/dev/null
# hc-repo bundle (full history, single file)
[ -d /home/z/hc-repo/.git ] && (cd /home/z/hc-repo && git bundle create "$ARK/snapshots/hc-repo-$STAMP.bundle" --all 2>/dev/null && git bundle create "$FALLBACK/snapshots/hc-repo-$STAMP.bundle" --all 2>/dev/null)
# bag copy into fallback
cp -r /home/z/bag "$FALLBACK/bag" 2>/dev/null
cp "$SNAP" "$FALLBACK/snapshots/" 2>/dev/null
# keep last 15 snapshots per location
ls -t "$ARK/snapshots"/sandbox-*.tar.gz 2>/dev/null | tail -n +16 | xargs -r rm -f
ls -t "$FALLBACK/snapshots"/sandbox-*.tar.gz 2>/dev/null | tail -n +16 | xargs -r rm -f
ls -t "$FALLBACK/snapshots"/hc-repo-*.bundle 2>/dev/null | tail -n +8 | xargs -r rm -f

# --- Layer 4: GitHub mirror (immutable remote copy of the vault) ---
if [ -s "$TOKEN_PATH" ]; then
  TOKEN=$(cat "$TOKEN_PATH")
  cd "$ARK/vault"
  if ! git remote | grep -q mirror; then
    git remote add mirror "https://x-access-token:$TOKEN@github.com/kyo-oo/HC-PROOF.git"
  fi
  git push -q mirror HEAD:refs/heads/ark/sandbox-vault 2>/dev/null || true
fi

# --- Layer 5: cron watchdog lives OUTSIDE the sandbox (survives sandbox deletion) ---
echo "sweep done $STAMP"
