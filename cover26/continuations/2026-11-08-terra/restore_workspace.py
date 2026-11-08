"""Restore only this continuation's compressed inputs, without network access."""
from pathlib import Path
import gzip,hashlib,io,json,os,tempfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PREFIX=HERE.relative_to(ROOT).as_posix()+"/workspace/"
def digest(path):
    h=hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda:f.read(1048576),b""):h.update(b)
    return h.hexdigest()
def safe(name):
    p=(ROOT/name).resolve()
    if not p.is_relative_to(ROOT.resolve()):raise ValueError("Unsafe manifest path")
    return p
for line in (ROOT/"manifests/FILES.jsonl").read_text(encoding="utf-8").splitlines():
    row=json.loads(line)
    if not row["path"].startswith(PREFIX) or row["encoding"]!="gzip-parts-v1":continue
    target=safe(row["path"])
    if target.exists():
        if target.stat().st_size!=row["bytes"] or digest(target)!=row["sha256"]:raise ValueError("Different target exists: "+str(target))
        continue
    packed=tempfile.SpooledTemporaryFile(max_size=8000000)
    for part in row["parts"]:
        p=safe(part["path"])
        if p.stat().st_size!=part["bytes"] or digest(p)!=part["sha256"]:raise ValueError("Part mismatch")
        with p.open("rb") as f:
            for b in iter(lambda:f.read(1048576),b""):packed.write(b)
    packed.seek(0);target.parent.mkdir(parents=True,exist_ok=True)
    fd,name=tempfile.mkstemp(prefix="restore-",dir=target.parent)
    tmp=Path(name)
    try:
        h=hashlib.sha256();size=0
        with os.fdopen(fd,"wb") as out,gzip.GzipFile(fileobj=packed,mode="rb") as stream:
            for b in iter(lambda:stream.read(1048576),b""):out.write(b);h.update(b);size+=len(b)
        if size!=row["bytes"] or h.hexdigest()!=row["sha256"]:raise ValueError("Restored digest mismatch")
        if target.exists():raise ValueError("Concurrent target creation")
        tmp.replace(target)
    finally:
        packed.close()
        if tmp.exists():tmp.unlink()
    print("Restored",row["path"],flush=True)
print("Continuation inputs restored by byte identity; this is not a mathematical proof.")
