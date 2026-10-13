"""Complete q11 locally chorded disk enumeration via exact piece gluing.
Conditional on owner-count geometry; no metric optimality assertion.
"""
import importlib.util,json,time
from pathlib import Path
from itertools import combinations,permutations,product
P=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('gen',P/'gen_k10_fixed_copy.py');g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
cache={};stats={}
def expand(fs,N,m):
 result=set()
 for perm in permutations(range(m)):
  for sign in(-1,1):
   for sh in range(N):
    result.add(tuple(sorted(tuple(sorted((sh+sign*v)%N if v<N else N+perm[v-N]for v in f))for f in fs)))
 return result
def pieces(N,m):
 if (N,m)not in cache:
  if m==0:
   assert N==3;cache[N,m]=[((0,1,2),)]
  else:
   _,_,_,results,dt=g.run(N,m,10000)
   fs=set()
   for key in results:fs.update(expand(key,N,m))
   cache[N,m]=sorted(fs)
   stats[f'{N}/{m}']={'unmarked_classes':len(results),'fully_labelled':len(fs)}
 return cache[N,m]
def canon(fs):return g.full_canon(11,3,fs)
def mapped(fs,outer,inner):
 labels=outer+inner
 return [tuple(sorted(labels[v]for v in f))for f in fs]
# All independent S up to D11, using unrestricted dihedral set action.
sets={}
for mask in range(1<<11):
 S=tuple(i for i in range(11)if mask>>i&1)
 if any((i+1)%11 in S for i in S):continue
 key=min(tuple(sorted((sign*i+sh)%11 for i in S))for sign in(-1,1)for sh in range(11))
 sets[key]=None
catalogue={};perS={};start=time.time()
for S in sorted(sets,key=lambda S:(len(S),S)):
 outer=[i for i in range(11)if i not in S];t=len(S);count=0
 # Hub labels fixed per piece; final global S3 quotient means no lost allocation.
 for ms in g.compositions(3,t+1):
  if not ms[0]:continue
  blocks=[];nextid=11
  for k,m in enumerate(ms):
   interior=list(range(nextid,nextid+m));nextid+=m
   boundary=outer if k==0 else [(S[k-1]-1)%11,S[k-1],(S[k-1]+1)%11]
   blocks.append([mapped(fs,boundary,interior)for fs in pieces(len(boundary),m)])
  for bs in product(*blocks):
   faces=[f for block in bs for f in block];assert len(faces)==15
   key=canon(faces);catalogue.setdefault(key,{'m':3,'chord_middle_representative':list(S),'piece_hub_counts':list(ms),'faces':[list(f)for f in key]});count+=1
 perS[str(S)]=count
 print('S',S,'assembled',count,'cumulative',len(catalogue),'seconds',round(time.time()-start,1),flush=True)
output={'schema':'q11-locally-chorded-disk/v1','N':11,'m':3,'scope':'conditional triangulated disk topology, no metric realizability assertion','piece_counts':stats,'S_orbits':len(sets),'assembled_per_S':perS,'class_count':len(catalogue),'entries':list(catalogue.values())}
(P/'q11-pocket-catalogue.json').write_text(json.dumps(output,indent=1))
print('DONE',len(catalogue),round(time.time()-start,1),flush=True)
