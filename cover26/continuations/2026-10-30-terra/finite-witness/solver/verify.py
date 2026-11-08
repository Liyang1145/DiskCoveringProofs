"""Independent exact verifier for finite-set-cover-tree-v1; standard library only."""
from pathlib import Path
import argparse,gzip,hashlib,json
if not __debug__:raise RuntimeError('Assertions must be enabled')
def load(p):
 raw=Path(p).read_bytes();return raw,json.loads(gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw)
def indices(x):
 while x:
  q=x&-x;yield q.bit_length()-1;x-=q
def main():
 ap=argparse.ArgumentParser();ap.add_argument('input');ap.add_argument('certificate');args=ap.parse_args()
 raw,d=load(args.input);_,c=load(args.certificate)
 assert c['input_sha256']==hashlib.sha256(raw).hexdigest()
 n=len(d['points']);assert n==c['n'] and n>0
 full=(1<<n)-1;masks=sorted(set(int(x,16) for x in d['masks'] if int(x,16)),reverse=True)
 assert masks and all(m&~full==0 for m in masks)
 if c['schema']=='finite-set-cover-cover-v1':
  chosen=[int(x,16) for x in c['masks']];assert all(x in masks for x in chosen)
  union=0
  for x in chosen:union|=x
  assert union==full
  print('VERIFIED finite mask cover uses',len(chosen),'masks')
  print('Geometry is not verified here; mask realizability must be separately checked.')
  return
 assert c['schema']=='finite-set-cover-tree-v1'
 w=c['integer_weights'];assert len(w)==n and all(type(x) is int and x>=0 for x in w)
 target=c['target'];assert type(target) is int and target>=0
 nodes=0
 def check(node,U,k):
  nonlocal nodes
  nodes+=1
  assert U and k>=0 and isinstance(node,dict)
  if node['kind']=='weight':
   total=sum(w[i] for i in indices(U))
   peak=max(sum(w[i] for i in indices(m&U)) for m in masks)
   assert total>k*peak
  elif node['kind']=='packing':
   pts=node['points'];assert len(pts)>k and len(pts)==len(set(pts))
   assert all(type(i) is int and 0<=i<n and U>>i&1 for i in pts)
   chosen=sum(1<<i for i in pts)
   assert all((m&chosen).bit_count()<=1 for m in masks)
  elif node['kind']=='branch':
   assert k>0
   p=node['point'];assert type(p) is int and 0<=p<n and U>>p&1
   options=sorted({m&U for m in masks if m>>p&1},reverse=True)
   children=node['children'];assert len(options)==len(children)
   for opt,child in zip(options,children):check(child,U&~opt,k-1)
  else:raise AssertionError('unknown proof node')
 check(c['tree'],full,target)
 print('VERIFIED finite set cover requires more than',target,'masks; tree nodes',nodes)
 print('Geometry is not verified here; independently verify coverage of all possible disk centers.')
if __name__=='__main__':main()
