"""Pure combinatorial graph input for closed witness networks."""
def triangle(blocks):
 assert len(blocks)==3 and sum(blocks)==9 and min(blocks)>=0
 labels=sum(([9+k]*n for k,n in enumerate(blocks)),[])
 faces=[(i,(i+1)%9,labels[i]) for i in range(9)]
 start=0
 for k,n in enumerate(blocks):
  start+=n;faces.append((start%9,9+k,9+(k+1)%3))
 faces.append((9,10,11))
 return faces

def network_edges(faces,nsites=None):
 if nsites is None:nsites=1+max(max(f) for f in faces)
 assert nsites>=10
 for f in faces:assert len(f)==3 and len(set(f))==3 and min(f)>=0 and max(f)<nsites
 nf=nsites+len(faces);edges=[]
 for i in range(9):edges.extend([(nf+i,i),(nf+i,(i+1)%9)])
 for i,f in enumerate(faces):edges.extend([(nsites+i,k) for k in f])
 return nf,edges
