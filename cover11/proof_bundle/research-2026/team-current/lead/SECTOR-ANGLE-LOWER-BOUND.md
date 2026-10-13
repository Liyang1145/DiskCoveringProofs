# Sector angle bounded away from zero: exact chord-coordinate derivation

Let P=(k,h),Q=(k,−h) be unit-circle endpoints, k=cos(w/2)>0,h=sin(w/2)>0,w<pi. Inward ring center c=(x,y) has |c|<=s=sqrt(1−R²)<=k (because w<=2asinR). Write H=k−x>=0. If H>0, oriented sector angle alpha=angle(P−c,Q−c) lies(0,pi) and
 cot alpha=[(k−x)²+y²−h²]/[2h(k−x)]
          =k/h−(1−|c|²)/(2hH).
Consequently cot alpha<=k/h, so alpha>=w/2. This is equivalent to |c|<=1 with H>0; no circumcircle theorem needed.

More strongly 1−|c|²>=R² and H<=k+s, giving
 cot alpha<=k/h−R²/[2h(k+s)]
             =[(k+s)²−h²]/[2h(k+s)].
Thus **alpha>=2atan(h/(k+s))**, equality for c=(−s,0). This equality configuration need not satisfy endpointdistance<=R; bound is necessary, not sharp over actual covering sectors. ForH=0 the inwardnorm/chord inequalities force c=(k,0), k=s, hence alpha=pi (well-defined distinct endpoints); bound remains valid by continuity.

At relevantR in[3/8,U],w>=g=2pi−16asinU>0.0466, obtain uniform alpha>=w/2>=g/2>0.0233. This rules out alpha0 limits in genuine inward diagrams and their closures. Alpha=pi remains possible; no uniform positive height claimed.

Structural use: in compact necessary-angle search domain replace0<=alpha<=pi by g/2<=alpha<=pi. Withgamma endpoint radii in[1/37999,37999], chord norm cannot vanish even before explicitellbound, since ell²=(u−v)²+4uv sin²(alpha/2)>0. For sector L,T=atan2(v sin alpha,u−v cos alpha), etc., simultaneous(x,y)zero impossible; atalpha=pi both numerator0 anddenominatorpositive. Allsectorangle functions andoddwidth map therefore continuous onthe compactnecessarydomain. Logratio functionspolefree with explicitgamma,widthbounds. This only removes singularsearchinterfaces; sharpoptimum remainsopen.
