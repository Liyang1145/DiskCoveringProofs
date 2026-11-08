"""Restore an immutable public compressed report, checking Git and original SHA256."""
from pathlib import Path
from datetime import datetime,timezone,timedelta
import gzip,hashlib,json,urllib.request

HERE=Path(__file__).resolve().parent
DEST=(HERE/'native-recovered').resolve()
DEST.mkdir(exist_ok=True)
COMMIT='11bf26e8b9ca601ab7220a93c1ef39451513aed0'
NAME='n26-mixed-after-six-midarc-supplemental-current-v1.json'
SIZE=12645909
GIT_SHA='7334217a39b2f93b32c4a8f95be91f9b79b4f565'
ORIGINAL_SHA='ba52dbb56f9d273c30e1b356c55bdb0d3ff8fdaa36061248e5c8ec1e490a81a1'
URL=f'https://raw.githubusercontent.com/Liyang1145/DiskCoveringProofs/{COMMIT}/cover26/proof_bundle/outputs/{NAME}.gz.part0001'
compressed=DEST/(NAME+'.gz.part0001');decoded=DEST/NAME
for p in [compressed,decoded]:
    if not p.resolve().is_relative_to(DEST):raise ValueError('Unsafe destination')

def hash_file(path,kind='sha256',prefix=b''):
    h=hashlib.new(kind);h.update(prefix)
    with path.open('rb') as stream:
        while chunk:=stream.read(1024*1024):h.update(chunk)
    return h.hexdigest()

if not compressed.exists():
    temporary=compressed.with_suffix(compressed.suffix+'.partial')
    total=0
    with urllib.request.urlopen(URL,timeout=30) as source,temporary.open('wb') as output:
        while chunk:=source.read(1024*1024):
            total+=len(chunk)
            if total>SIZE:raise ValueError('Oversized download')
            output.write(chunk)
    if total!=SIZE:raise ValueError('Incomplete public chunk')
    digest=hash_file(temporary,'sha1',b'blob '+str(SIZE).encode()+b'\0')
    if digest!=GIT_SHA:raise ValueError('Public Git blob mismatch')
    temporary.replace(compressed)
if compressed.stat().st_size!=SIZE or hash_file(compressed,'sha1',b'blob '+str(SIZE).encode()+b'\0')!=GIT_SHA:
    raise ValueError('Existing compressed byte mismatch')
print('verified compressed Git blob',GIT_SHA,flush=True)
if not decoded.exists():
    temporary=decoded.with_suffix('.json.partial');total=0
    with gzip.open(compressed,'rb') as source,temporary.open('wb') as output:
        while chunk:=source.read(1024*1024):
            total+=len(chunk)
            if total>2*1024**3:raise ValueError('Unexpected expanded size')
            output.write(chunk)
    digest=hash_file(temporary)
    if digest!=ORIGINAL_SHA:raise ValueError('Original current SHA256 mismatch: '+digest)
    temporary.replace(decoded)
if hash_file(decoded)!=ORIGINAL_SHA:raise ValueError('Existing current bytes changed')
receipt={'date':datetime.now(timezone(timedelta(hours=8))).isoformat(),
    'source_commit':COMMIT,'url':URL,'compressed_bytes':SIZE,'compressed_git_sha1':GIT_SHA,
    'decoded_bytes':decoded.stat().st_size,'decoded_sha256':ORIGINAL_SHA,
    'restored_original_bytes':True,'semantic_replay_performed':False,
    'native_frontier_paid':0,'path':str(decoded)}
(DEST/'RECOVERY-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
