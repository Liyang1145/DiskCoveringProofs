import numpy as np, json, itertools
from scipy.linalg import null_space, orth
S=np.load('struct1669.npz'); AX=S['AX']; BT=S['BT']; lam0=S['lam0']; H0=np.load('H0.npy')
D=json.load(open('kkt2_122.json')); A=D['A']
Z=[k for k in range(len(A)) if lam0[k]<1e-12]
Na=null_space(AX); NZ=Na[Z]
Kz=null_space(NZ)            # c-directions free in sign (incl lam0)
G2=BT@Na@Kz; print('two-sided gradient rank',np.linalg.matrix_rank(G2,1e-9))
# one-sided: triples weights t = per-triple sum of NZ rows
trip=[Z[i:i+3] for i in range(0,30,3)]
Comp=orth(NZ.T)              # 5-dim complement directions in c space (row space of NZ)
T=NZ@Comp                    # 30 x 5
tt=np.array([T[3*i:3*i+3].sum(0) for i in range(10)])  # 10 x 5 triple weights (linear in c')
print('triple weight matrix rank',np.linalg.matrix_rank(tt,1e-9))
# check within-triple proportionality
for i in range(10):
    blk=T[3*i:3*i+3]; print(i,'rank of triple block',np.linalg.matrix_rank(blk,1e-9), end='; ')
print()
# cone {c': T c' >=0}; find its extreme rays numerically via LP vertices: assume rows pair up
# gradients of one-sided part
G1=BT@Na@Comp   # 15x5, gradient = G1 c' for c' in cone
# subspace Tsub = orth complement of range(G2)
P2=orth(G2); Tb=null_space(P2.T)   # 15 x 10 basis of T
print('dim T',Tb.shape[1])
# cone C = {u in T: (G1 c').u <=0 for all c' with T c'>=0}; get rays of {c': T c'>=0}
from scipy.optimize import linprog
rays=[]
for i in range(10):
    # maximize t_i subject to T c'>=0, t_j=0 for j's in same... brute: rays = c' with 4 independent zero triples
    pass
best=None
# brute force rays: choose 4 triples that are zero -> 1-dim solution
for comb in itertools.combinations(range(10),4):
    M=tt[list(comb)]
    if np.linalg.matrix_rank(M,1e-9)<4: continue
    r=null_space(M)
    if r.shape[1]!=1: continue
    r=r[:,0]
    for s in (1,-1):
        v=s*r
        if (T@v>=-1e-9).all() and np.abs(T@v).max()>1e-9:
            if not any(np.allclose(v/np.linalg.norm(v),x) for x in rays): rays.append(v/np.linalg.norm(v))
print('extreme rays of one-sided cone',len(rays))
g=[G1@r for r in rays]; g=[Tb.T@x for x in g]   # in T coords
gm=np.array(g)
HT=Tb.T@H0@Tb; print('eig H0 on T',np.linalg.eigvalsh(HT)[:4])
mins=[]
for k in range(len(rays)+1):
    for J in itertools.combinations(range(len(rays)),k):
        if J: sub=null_space(gm[list(J)])
        else: sub=np.eye(Tb.shape[1])
        if sub.shape[1]==0: continue
        Hs=sub.T@HT@sub; ev,V=np.linalg.eigh(Hs)
        for e,v in zip(ev,V.T):
            for s in (1,-1):
                u=s*sub@v
                if (gm@u<=1e-10).all(): mins.append((e,J))
mins.sort(key=lambda x:x[0]); print('min u^T H0 u over critical cone C (|u|=1):',mins[0])
np.savez('crit.npz',Tb=Tb,gm=gm,rays=np.array(rays),Comp=Comp,Kz=Kz,Na=Na)
