"""Losslessly restore the latest historical root25 arithmetic snapshot."""
from pathlib import Path
from datetime import datetime,timezone,timedelta
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib,json,gzip,io,urllib.request

HERE=Path(__file__).resolve().parent
DEST=(HERE/'native-recovered').resolve();DEST.mkdir(exist_ok=True)
TREE=HERE.parent/'round-20261107d/native-source/PUBLIC-OUTPUT-TREE.json'
PREFIX='n26-root25-current346-refit2-origin-append-composition-v1.json'
COMMIT='11bf26e8b9ca601ab7220a93c1ef39451513aed0'
SHA='c1675552b56d762de0bca83ca3adbb28e06c71e95c94b387d7f216eee41187c9'
EXPECTED_BYTES=480441790
base=f'https://raw.githubusercontent.com/Liyang1145/DiskCoveringProofs/{COMMIT}/cover26/proof_bundle/outputs/'
entries=sorted((r for r in json.loads(TREE.read_text())['tree']
               if r['type']=='blob' and r['path'].startswith(PREFIX+'.gz.part')),key=lambda r:r['path'])
if len(entries)!=6:raise ValueError('Incomplete public part inventory')
for i,row in enumerate(entries,1):
    if row['path']!=PREFIX+'.gz.part'+str(i).zfill(4):raise ValueError('Noncanonical part order')
    if not (DEST/row['path']).resolve().is_relative_to(DEST):raise ValueError('Unsafe part path')

def digest(path,kind='sha256',prefix=b''):
    value=hashlib.new(kind);value.update(prefix)
    with path.open('rb') as source:
        for chunk in iter(lambda:source.read(1024*1024),b''):value.update(chunk)
    return value.hexdigest()

def acquire(row):
    path=DEST/row['path'];header=b'blob '+str(row['size']).encode()+b'\0'
    if not path.exists():
        temp=path.with_suffix(path.suffix+'.partial');size=0;sha=hashlib.sha1(header)
        with urllib.request.urlopen(base+row['path'],timeout=45) as source,temp.open('wb') as target:
            for chunk in iter(lambda:source.read(1024*1024),b''):
                size+=len(chunk)
                if size>row['size']:raise ValueError('Oversized part')
                sha.update(chunk);target.write(chunk)
        if size!=row['size'] or sha.hexdigest()!=row['sha']:raise ValueError('Downloaded part identity mismatch')
        temp.replace(path)
    if path.stat().st_size!=row['size'] or digest(path,'sha1',header)!=row['sha']:
        raise ValueError('Existing part identity mismatch')
    return {'file':row['path'],'bytes':row['size'],'git_sha1':row['sha']}

receipts=[]
with ThreadPoolExecutor(max_workers=3) as pool:
    for future in as_completed([pool.submit(acquire,row) for row in entries]):
        receipt=future.result();receipts.append(receipt)
        print('verified compressed part',receipt['file'],receipt['bytes'],flush=True)

class Parts(io.RawIOBase):
    def __init__(self,paths):self.paths=iter(paths);self.stream=None;self.advance()
    def advance(self):
        if self.stream:self.stream.close()
        path=next(self.paths,None);self.stream=None if path is None else path.open('rb')
    def readable(self):return True
    def readinto(self,target):
        while self.stream:
            n=self.stream.readinto(target)
            if n:return n
            self.advance()
        return 0
    def close(self):
        if self.stream:self.stream.close()
        super().close()

decoded=DEST/PREFIX
if not decoded.exists():
    temp=decoded.with_suffix('.json.partial');count=0;value=hashlib.sha256()
    with Parts([DEST/r['path'] for r in entries]) as parts,io.BufferedReader(parts) as buffer:
        with gzip.GzipFile(fileobj=buffer) as source,temp.open('wb') as target:
            for chunk in iter(lambda:source.read(1024*1024),b''):
                count+=len(chunk)
                if count>EXPECTED_BYTES:raise ValueError('Unexpected decoded size')
                value.update(chunk);target.write(chunk)
    if count!=EXPECTED_BYTES or value.hexdigest()!=SHA:raise ValueError('Original arithmetic SHA256 mismatch')
    temp.replace(decoded)
if decoded.stat().st_size!=EXPECTED_BYTES or digest(decoded)!=SHA:raise ValueError('Existing arithmetic bytes changed')
result={'date':datetime.now(timezone(timedelta(hours=8))).isoformat(),'source_commit':COMMIT,
    'decoded_file':str(decoded),'decoded_bytes':EXPECTED_BYTES,'decoded_sha256':SHA,
    'compressed_parts':sorted(receipts,key=lambda row:row['file']),'restored_original_bytes':True,
    'semantic_replay_performed':False,'new_geometric_payments':0,'global_optimality_proved':False}
(DEST/'ARITHMETIC-RECOVERY.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS exact historical arithmetic current bytes',SHA,EXPECTED_BYTES,flush=True)
