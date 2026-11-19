"""Exact weighted-ring lower bound for the thirteen-disk core."""
from polar_tables import R, TURN, beta, machins_formula
from weighted_rings import verify_weighted_rings

CORE=688_083_000
WEIGHTS=(
    (250,147163),(255,270227),(260,235568),(265,209123),(270,188388),
    (275,171263),(280,157708),(285,145675),(290,135537),(295,126164),
    (300,118560),(305,111357),(310,104924),(315,98803),(320,93467),
    (325,88455),(330,83702),(335,79142),(340,74874),(345,70931),
    (350,66997),(355,63182),(360,59414),(365,55873),(370,52305),
    (375,48555),(380,45058),(385,40964),(390,37804),(395,32266),
    (400,30098),(405,20681),(410,20782),(415,373),(435,2170),(440,23233),
)
RINGS=tuple((s*10**6,w) for s,w in WEIGHTS)+((CORE,6689217),)


def verify():
    machins_formula()
    if 18*beta(CORE,CORE-R,CORE)>=TURN or CORE+R!=918_879_000:
        raise ValueError("core radius assumptions failed")
    counts=verify_weighted_rings(R,RINGS,[(10,CORE-R,CORE,".22956"),(3,0,CORE,".28188")])
    for start,boxes in zip((CORE-R,0),counts):
        print(f"Verified weighted capacity on [{start},{CORE}] in {boxes} closed boxes.")
    print("PASS: r_D(13) >= 230796000/688083000, so the B=14 minimum owner norm is below 0.918879.")


if __name__=="__main__":
    verify()
