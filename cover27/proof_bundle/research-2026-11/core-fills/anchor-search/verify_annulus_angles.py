"""Test annulus incidence and core/boundary coverage in lifted polar angles."""
import argparse
from itertools import permutations
import json
from pathlib import Path

from polar_tables import CORE_CAPS, DEAD, END, PI_HI, R, SCALE, TRIG_SCALE, TURN, beta, cosine_ticks, machins_formula
from verify_b14_core_marks import K
from verify_boundary_walk import B, NORM_CEILING


LEVELS=(901_500_000,905_600_000,908_500_000,911_500_000)
CORE_NORM_CAP=CORE_CAPS[12]
SHORT_CAPS=tuple(CORE_CAPS[j] for j in (3,4,5))


def cross_edges(degrees):
    output=[]
    j=-1
    for i,d in enumerate(degrees):
        output.extend((i,k) for k in range(j,j+d-2))
        j+=d-3
    if j!=K-1:
        raise ValueError("strip does not run once around the inner cycle")
    return output


def difference_feasible(graph):
    """Test every directed difference constraint by integer Bellman-Ford."""
    d=[0]*len(graph)
    for _ in graph:
        changed=False
        for u,neighbors in enumerate(graph):
            for v,w in neighbors:
                candidate=d[u]+w
                if d[v]>candidate:
                    d[v]=candidate
                    changed=True
        if not changed:
            return True
    return False


def add(graph,u,v,w):
    graph[u].append((v,w))


def arcs(graph,start,length,width):
    for i in range(length):
        j=(i+1)%length
        wrap=TURN if j==0 else 0
        add(graph,start+i,start+j,width[i]+width[j]-wrap)
        add(graph,start+j,start+i,width[i]+width[j]+wrap)


def compatible(record,cap,config):
    outer_width,core_width,cross_width,witness_width=config
    graph=[[] for _ in range(B+K)]
    arcs(graph,0,B,[outer_width]*B)
    arcs(graph,B,K,[core_width[c] for c in cap])
    for i,k in record["cross_edges"]:
        j=k%K
        wrap=(k//K)*TURN
        limit=cross_width[cap[j]]
        if limit<0:
            return False
        add(graph,i,B+j,limit-wrap)
        add(graph,B+j,i,limit+wrap)
    for i,k in enumerate(record["apex_cycle_positions"]):
        upper=witness_width[cap[k]]
        if upper is None:
            continue
        j=(i+1)%B
        wrap=TURN if j==0 else 0
        add(graph,i,j,upper-wrap)
        add(graph,j,i,upper+wrap)
    return difference_feasible(graph)


def small_cap(least,second,third):
    cap=[CORE_NORM_CAP]*K
    for j,k in enumerate((least,second,third)):
        cap[k]=SHORT_CAPS[j]
    return cap


def candidates(record,config):
    for chosen in permutations(range(K),3):
        if chosen[0] in record["shared_apices"]:
            continue
        cap=small_cap(*chosen)
        if compatible(record,cap,config):
            yield cap


def make_config(floor):
    core=floor-R-1000
    low=floor-2*R
    if not 2*R<floor or not R<core or low<=core-R:
        raise ValueError("core and cross-edge radial domains")
    caps=(*SHORT_CAPS,CORE_NORM_CAP)
    widths={p:beta(core,low,min(p,core+R)) for p in caps}
    if any(v<0 for v in widths.values()):
        raise ValueError("an attained core norm is outside the core shell")
    # The cross-edge witness lies at distance at most 2R from an outer
    # site. The owner's norm can be reduced to floor if t<=floor.
    outer=beta(SCALE,floor,END)
    if not max(SHORT_CAPS)<=CORE_NORM_CAP<=floor:
        raise ValueError("core endpoint may be above the outer norm floor")
    # The shortest-norm representative cannot be the apex of two
    # consecutive boundary faces. Certify the two-edge lens comparison.
    v=SHORT_CAPS[0]
    gap=TURN//2-12*beta(SCALE,SCALE-R,END)
    numerator=2*PI_HI.numerator*gap
    denominator=PI_HI.denominator*TURN
    cos_lower=2*denominator*denominator-numerator*numerator
    if gap<=0 or 2*v*denominator*denominator>=floor*cos_lower:
        raise ValueError("bad domain for the shared-apex radial bound")
    if (floor*floor+v*v-4*R*R)*TRIG_SCALE<=2*floor*v*cosine_ticks(gap):
        raise ValueError("the least-norm core site could be a shared apex")
    cross={p:beta(floor,low,p,2*R) for p in caps}
    largest=max(cross.values())
    max_width=max(max(widths.values()),outer)
    if 2*(largest+max_width)>=TURN or 8*max(widths.values())>=TURN or 4*outer>=TURN:
        raise ValueError("ambiguity in the common angular lift")
    witness={}
    for p in caps:
        w=p+R
        # In this domain the largest angular deviation of an outer
        # site from the witness occurs at outer norm floor and witness
        # norm w, or at the interior radial maximum of beta.
        witness[p]=None
        if w<=floor:
            theta=beta(floor,floor-R,w)
            if theta==DEAD:
                raise ValueError("unmodelled empty outer-face wedge")
            witness[p]=2*theta
    if any(x is not None and 2*x>=TURN for x in witness.values()):
        raise ValueError("outer-face wedge is longer than a half turn")
    return outer,widths,cross,witness


def annulus_records(source):
    machins_formula()
    ring=json.loads(source.read_text(encoding="utf-8"))
    reps=[]
    for index in ring["orbit_representative_indices"]:
        a=ring["strips"][index]
        a["cross_edges"]=cross_edges(a["outer_degrees"])
        actual=set()
        for f in a["triangles"]:
            for i in f:
                for j in f:
                    if i<B<=j:
                        actual.add((i,a["inner_cycle"].index(j)))
        shift=next(k for k in range(K) if {(i,(j+k)%K) for i,j in a["cross_edges"]}==actual)
        positions={}
        for j,block in enumerate(a["apex_pattern"],B):
            k=a["inner_cycle"].index(j)
            for i in block:
                positions[i]=(k-shift)%K
        a["apex_cycle_positions"]=[positions[i] for i in range(B)]
        a["shared_apices"]={k for k in a["apex_cycle_positions"] if a["apex_cycle_positions"].count(k)==2}
        reps.append(a)
    return reps


def verify(source):
    reps=annulus_records(source)
    report=[]
    for floor in LEVELS:
        if not floor<=NORM_CEILING:
            raise ValueError("floor exceeds the available owner norm range")
        config=make_config(floor)
        kept=[]
        for record in reps:
            feasible=sum(1 for _ in candidates(record,config))
            kept.append(feasible)
        print(f"PASS B=14: at D1 >= {floor}/1e9, {sum(n>0 for n in kept)} annuli and {sum(kept)} placements of the three short-norm core sites survive angular bounds.",flush=True)
        report.append({"owner_norm_floor":floor,"placements_per_annulus":kept})
    return report


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("annuli",type=Path)
    parser.add_argument("--output",type=Path)
    a=parser.parse_args()
    records=verify(a.annuli)
    if a.output:
        a.output.write_text(json.dumps(records,separators=(",",":"))+"\n",encoding="utf-8")
