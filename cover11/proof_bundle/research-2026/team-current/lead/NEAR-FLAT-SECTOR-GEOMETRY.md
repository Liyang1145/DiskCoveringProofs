# Quantitative near-flat sector geometry (not a feasible patch projection)

Let r∈[3/8,19/50], 0<g≤w≤2asin r, h=sin(w/2), k=cos(w/2), s=sqrt(1-r²). Let P±=(k,±h), c=(k-a,y) satisfy |c|≤s and |P±-c|≤r. Then k≥s and c_x≤s imply a≥0. Suppose the ordinary angle at c between P+-c and P--c is alpha=pi-eps, 0≤eps≤pi/2 (with nonzero endpoint distances). Set h0=sin(g/2)>0.

## Exact identities and bounds
The cross-product magnitude is 2ha, so
  2ha=|P+-c| |P--c| sin(eps) ≤r² sin(eps),
and 0≤a≤A := r² sin(eps)/(2h0).
The norm constraint expands as
  r²-h²+y²+a²≤2ka≤2a.
In particular 0≤r²-h²≤2a. The two endpoint constraints give
  a²+(h+|y|)²≤r²,
so |y|≤r-h≤2a/(r+h)≤2A/r.
Also 0≤k-s=(r²-h²)/(k+s)≤a/s, hence
  |c_x-s|≤a+(k-s)≤A(1+1/s).
Thus relative to the unique flat sector c0=(s,0), P0±=(s,±r),
  |c-c0|≤A sqrt((1+1/s)²+(2/r)²),
  |P±-P0±|≤A sqrt(s^(-2)+(2/r)²).
All these are uniform O(sin eps), hence O(eps), with explicit finite constants when g>0. Moreover 2asin r-w≤2(r-h)/s≤4A/(rs), by the derivative of asin on [h,r].
At eps=0 these inequalities recover the exact flat-sector norm sandwich without equal-endpoint assumptions.

## Scope and missing implication
These bounds concern ONE actual sector only. They do NOT construct a feasible flat seven-factor patch from a nearby nonflat patch: adjoining site angles, face circumradius inequalities, width domains and hubnorm may fail under projection. Thus C870's flat-domain maximum cannot yet be applied to the projected data. Any collar exclusion needs either an enlarged-domain objective bound or a domain-preserving projection with controlled objective change. A Lipschitz bound on the flat objective alone does not supply that interface.

This replaces no claim; member r17 deformation equations and claimed C842 alpha-gap were erroneous and withdrawn/nonbearing. C842 excludes exact endpoint flatness only, with no recorded explicit epsilon gap.
