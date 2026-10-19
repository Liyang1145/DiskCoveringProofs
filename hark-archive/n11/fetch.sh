#!/bin/bash
# fetch path from repo via API to src/
p="$1"; out="src/$p"; mkdir -p "$(dirname "$out")"
apicall github contents_get owner=Liyang1145 repo=DiskCoveringProofs path="$p" > /tmp/f.json
python3 - "$out" <<'P'
import json,base64,sys
d=json.load(open('/tmp/f.json'))
if isinstance(d,list):
    for e in d: print(e['type'],e['path'],e.get('size'))
else:
    open(sys.argv[1],'wb').write(base64.b64decode(d['content'])); print('saved',sys.argv[1],d['size'])
P
