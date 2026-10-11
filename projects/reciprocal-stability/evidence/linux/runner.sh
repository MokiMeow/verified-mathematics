#!/usr/bin/env bash
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq
apt-get install -y -qq curl ca-certificates git zstd python3 >/work/packages.log
cd /work
if [ ! -x lean-4.34.0-linux/bin/lean ]; then
  curl -L --fail --retry 3 -o lean.tar.zst https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux.tar.zst
  echo 'caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b  lean.tar.zst' | sha256sum -c -
  tar --zstd -xf lean.tar.zst
fi
export PATH=/work/lean-4.34.0-linux/bin:$PATH
mkdir -p project
cd project
tar -xf /input/reciprocal-stability-v1.0.0.tar
lean --version
lake --version
while read -r name url rev; do
  case "$name" in *[!a-zA-Z0-9_-]*) echo 'Invalid package name'; exit 1;; esac
  path="/work/project/.lake/packages/$name"
  if [ -d "$path" ] && ! git -C "$path" rev-parse --verify HEAD >/dev/null 2>&1; then
    mv "$path" "/work/interrupted-$name-$(date +%s)"
  fi
  if [ ! -d "$path/.git" ]; then
    mkdir -p "$path"
    git -C "$path" init -q
    git -C "$path" remote add origin "$url"
    git -C "$path" fetch --depth 1 origin "$rev"
    git -C "$path" checkout -q --detach FETCH_HEAD
  fi
done < <(python3 -c 'import json; j=json.load(open("lake-manifest.json")); [print(p["name"],p["url"],p["rev"]) for p in j["packages"]]')
lake exe cache get Kantorovich.lean Kantorovich/Stability.lean Kantorovich/ThreeCertificates.lean Kantorovich/ThreeStability.lean Kantorovich/Examples.lean
lake build
for file in Kantorovich.lean Kantorovich/Stability.lean Kantorovich/ThreeCertificates.lean Kantorovich/ThreeStability.lean Kantorovich/Examples.lean Audit.lean StabilityAudit.lean; do
  echo "FRESH SOURCE: $file"
  lake env lean -DwarningAsError=true "$file"
done
lake env lean -DwarningAsError=true /input/SequentialReplay.lean
python3 sanity_checks.py
python3 stability_sanity.py
echo 'ALL LINUX CHECKS PASSED'
