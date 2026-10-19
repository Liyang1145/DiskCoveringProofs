#!/bin/bash
. "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/_paths.sh"  # portable roots, see hark-archive/_paths.sh
# fetch path from repo via API to src/
# needs Hark's `apicall` CLI (or replace with: gh api repos/Liyang1145/DiskCoveringProofs/contents/$p)
TMPF=$(mktemp "${TMPDIR:-/tmp}/dcp-fetch.XXXXXX")
p="$1"; out="src/$p"; mkdir -p "$(dirname "$out")"
apicall github contents_get owner=Liyang1145 repo=DiskCoveringProofs path="$p" > "$TMPF"
python3 - "$out" "$TMPF" <<'P'
import json,base64,sys
d=json.load(open(sys.argv[2]))
if isinstance(d,list):
    for e in d: print(e['type'],e['path'],e.get('size'))
else:
    open(sys.argv[1],'wb').write(base64.b64decode(d['content'])); print('saved',sys.argv[1],d['size'])
P
rm -f "$TMPF"
