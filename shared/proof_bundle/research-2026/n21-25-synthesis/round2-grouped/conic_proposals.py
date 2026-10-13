"""Fast numerical SOCP proposals via isolated Clarabel 0.11.1.

The solver is NOT in the proof trust base. Every proposed certificate must pass
the inspected exact integer/Fraction checker on the whole angle box.
"""
from pathlib import Path
import os
os.environ["OPENBLAS_NUM_THREADS"]="1"
os.environ["OMP_NUM_THREADS"]="1"
import sys
import math
import numpy as np
from scipy.sparse import csc_matrix

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/"deps/clarabel0111"))
import clarabel


def make_solver_class(G,C):
    class Solver:
        def __init__(self,B,faces):
            self.B=B
            self.centers=G.N
            self.ed=G.edges(B,faces)
            self.E=np.array(self.ed,dtype=int)
            self.V=max(v for edge in self.ed for v in edge)+1
            assert self.V==G.V==C.V
            self.ne=len(self.ed)
            self.nvar=2*(self.V-1)+1
            # Static edge and unit-cone sparse entries.
            self.static_rows=[];self.static_cols=[];self.static_vals=[]
            self.base_b=np.zeros(3*self.ne+4*(B-1))
            for k,(u,v) in enumerate(self.ed):
                self.static_rows.append(3*k);self.static_cols.append(self.nvar-1);self.static_vals.append(-1.)
                for axis in (0,1):
                    row=3*k+1+axis
                    for node,sign in ((u,1),(v,-1)):
                        if node:
                            self.static_rows.append(row);self.static_cols.append(2*(node-1)+axis)
                            self.static_vals.append(-float(sign))
                        elif axis==0:
                            self.base_b[row]+=sign
            self.unit_offset=3*self.ne+B-1
            for i in range(B-1):
                self.base_b[self.unit_offset+3*i]=1.
                for axis in (0,1):
                    self.static_rows.append(self.unit_offset+3*i+1+axis)
                    self.static_cols.append(2*i+axis);self.static_vals.append(-1.)
            self.P=csc_matrix((self.nvar,self.nvar))
            self.objective=np.zeros(self.nvar);self.objective[-1]=1.
            self.cones=[clarabel.SecondOrderConeT(3) for _ in range(self.ne)]
            self.cones += [clarabel.NonnegativeConeT(B-1)]
            self.cones += [clarabel.SecondOrderConeT(3) for _ in range(B-1)]
            self.settings=clarabel.DefaultSettings()
            self.settings.verbose=False
            self.settings.max_iter=180
            self.settings.tol_gap_abs=1e-9
            self.settings.tol_gap_rel=1e-9
            self.settings.tol_feas=1e-9

        def solve_slsqp(self,lo,hi,maxiter=100):
            # Compatibility name only: no SLSQP is called.
            aa=[];bb=[]
            for l,h in zip(lo,hi):
                a,b=G.arc_halfplane(l,h)
                aa.append(a);bb.append(b)
            aa=np.array(aa,dtype=float)/G.QA
            bb=np.array(bb,dtype=float)/G.QB
            rows=list(self.static_rows);cols=list(self.static_cols);values=list(self.static_vals)
            rhs=self.base_b.copy()
            for i in range(self.B-1):
                row=3*self.ne+i
                rhs[row]=-bb[i]
                for axis in (0,1):
                    rows.append(row);cols.append(2*i+axis);values.append(-aa[i,axis])
            A=csc_matrix((values,(rows,cols)),shape=(len(rhs),self.nvar))
            solver=clarabel.DefaultSolver(self.P,self.objective,A,rhs,self.cones,self.settings)
            solution=solver.solve()
            x=np.asarray(solution.x,dtype=float)
            dual=np.asarray(solution.z,dtype=float)
            status={"success":str(solution.status) in ("Solved","AlmostSolved"),
                    "solver_status":str(solution.status),"radius":float(x[-1]),
                    "iterations":int(solution.iterations),"algorithm":"Clarabel0.11.1 numerical proposal only"}
            if not np.all(np.isfinite(x)) or not np.all(np.isfinite(dual)):
                return None,x,status
            flow=-dual[:3*self.ne].reshape(self.ne,3)[:,1:]
            lam=dual[3*self.ne:3*self.ne+self.B-1]
            support=-dual[self.unit_offset:].reshape(self.B-1,3)[:,1:]
            certificate,margin=C.rationalize(self.B,self.ed,lo,hi,lam,support,flow)
            status["exact_margin"]=None if margin is None else float(margin)
            return certificate,x,status

        def fixed_unit_anchor_proposal(self,x):
            """Untrusted diagnostic realization after normalizing all anchors.

            It may guide refinement routing, but cannot prove a cover or exclude
            a graph. No numerical feasibility status is an accepting premise.
            """
            q=np.vstack(([1.,0.],np.asarray(x[:2*(self.B-1)]).reshape(-1,2)))
            norms=np.linalg.norm(q,axis=1)
            if np.min(norms)<1e-9:
                return None
            q=q/norms[:,None]
            free=self.V-self.B
            nv=2*free+1
            rows=[];cols=[];vals=[];rhs=np.zeros(3*self.ne)
            for k,(u,v) in enumerate(self.ed):
                rows.append(3*k);cols.append(nv-1);vals.append(-1.)
                for axis in (0,1):
                    for node,sign in ((u,1),(v,-1)):
                        if node<self.B:
                            rhs[3*k+1+axis]+=sign*q[node,axis]
                        else:
                            rows.append(3*k+1+axis);cols.append(2*(node-self.B)+axis);vals.append(-float(sign))
            A=csc_matrix((vals,(rows,cols)),shape=(len(rhs),nv))
            objective=np.zeros(nv);objective[-1]=1.
            solver=clarabel.DefaultSolver(csc_matrix((nv,nv)),objective,A,rhs,
                      [clarabel.SecondOrderConeT(3) for _ in range(self.ne)],self.settings)
            solution=solver.solve()
            radius=float(solution.x[-1])
            if not math.isfinite(radius):
                return None
            result={"radius_float":radius,"solver_status":str(solution.status),
                    "anchor_angles_turns":(np.mod(np.arctan2(q[:,1],q[:,0]),2*np.pi)/(2*np.pi)).tolist(),
                    "untrusted_numeric_diagnostic":True}
            if self.centers==21 and self.ne==120-self.B:
                free_points=np.asarray(solution.x[:-1]).reshape(-1,2)
                result["potential_complete_graph_centers"]=free_points[:21].tolist()
                result["not_a_certified_cover"]=True
            return result
    return Solver
