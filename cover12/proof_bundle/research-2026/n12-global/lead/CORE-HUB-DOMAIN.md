# Inner-core constraints independent of boundary topology

Object: any radius-r cover, 1/3<r≤U<1/2, k boundary-active disks, m=12-k∈{1,2,3} other disks. Let a=1-2r>0. Every active center has norm≥1-r. Thus all points ||x||<a are strictly farther than r from every active center. By closedness and finite union, the m nonactive disks cover the whole core B(0,a). This holds with singleton boundary arcs and redundant boundary disks.

## One hub (m=1)
B(0,a)⊆B(h,r) iff ||h||+a≤r. Hence ||h||≤3r-1. This gives a compact eccentricity interval for dual-circle capacity. No Voronoi classification is required: if the other disks cover D together with B(h,r), then for every q∈(r,1-||h||), S(h,q) must be covered by those other disks; letting q↓r gives boundary capacity inequalities with continuous weights. At our radius bound 1-||h||>r is strict.

## Two hubs (m=2): at least one central hub
If either h=0, the conclusion below is immediate. Otherwise the portion of S(0,a) covered by B(h,r) is a closed arc (possibly full or empty). If ||h||²+a²>r², its halfwidth is strictly below π/2, by
cos β=(a²+||h||²-r²)/(2a||h||)>0.
If both hubs had squared norm>r²-a², their two covered arcs would have total length strictly less than 2πa, contradicting core coverage. Consequently
min(||h1||,||h2||)≤sqrt(r²-a²)=sqrt((1-r)(3r-1)).
After relabelling, this bounds a designated central hub. No bound of this strength for BOTH hubs follows; the other may be redundant for the core. This is a necessary condition, not a sufficiency criterion for full disk coverage.

## Three hubs (m=3): central alternative
The same arc argument shows at least one core arc has halfwidth≥π/3. If a single hub covers all S(0,a) this also applies. Its norm t therefore satisfies
a²+t²-r²≤a t,
so t≤a/2+sqrt(r²-3a²/4).
This is a weaker radius-domain reduction but valid without assumptions on pairwise hub adjacency. Center0 is already within this bound. An empty or point arc cannot be the selected arc.

## Why this is not yet a classification
Core coverage is necessary only. m2 and m3 may have hubs redundant for the core but essential in outer annuli. Nor do these inequalities show the hub Voronoi cells are adjacent or that their induced graph is connected. Such conclusions require additional geometry; they are not assumed here.

Current next use: m1 biased two-circle capacity; m2 union-boundary capacity with one designated central hub; m3 candidate structure is a separate investigation, not a WLOG.
