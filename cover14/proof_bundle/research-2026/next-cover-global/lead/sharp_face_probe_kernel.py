"""Bounded numeric 3D boxsupport test: oneinteriorface radiusdeficit; notcertificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,heapq,time
from itertools import combinations
from fractions import Fraction as Q
from pathlib import Path
P=Path(__file__).resolve().parent;r=.33173203427623414;a=r*r

def support(lo,hi,p):
 t=0 if p>=a else(math.pi if p<=-a else math.acos(p/a));t=max(lo,min(hi,t));return a*math.sin(t)-p*t

def boxbound(box,p):
 lo=[x[0]for x in box];hi=[x[1]for x in box];dist=max(0,sum(lo)-math.pi,math.pi-sum(hi));g=lambda h:1 if h>=math.pi else (math.pi-h)/2*math.tan(h/2); pen=a/2*min(2*(1-math.cos(l))/(1+g(h)) for l,h in box)*dist
 return sum(support(x,y,z)for(x,y),z in zip(box,p))-pen

def solve(p,budget=4000):
 box=[(0,math.pi)]*3;heap=[(-boxbound(box,p),0,box)];uid=0
 for k in range(budget):
  neg,_,box=heapq.heappop(heap);j=max(range(3),key=lambda j:box[j][1]-box[j][0]);lo,hi=box[j];mid=(lo+hi)/2
  for seg in [(lo,mid),(mid,hi)]:
   b=box.copy();b[j]=seg;uid+=1;heapq.heappush(heap,(-boxbound(b,p),uid,b))
 return -heap[0][0]

