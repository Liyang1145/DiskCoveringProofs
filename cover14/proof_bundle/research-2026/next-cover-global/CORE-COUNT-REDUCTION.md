# n14: only ten or eleven boundary-active disks

**Analytic theorem, global over arbitrary covers.** Let 0<r≤U=0.33173203427623414<1/3. If14 closed radius-r disks cover D={|p|≤1}, project all centers into D. The resulting cover has exactly k∈{10,11} disks intersecting S1. Tangencies count active; repeated centers are allowed. This does not assert projection preserves activity.

## Projection
For c=tv,t>1,|v|=1 and |p|≤1, |p-c|²−|p-v|²=(t−1)(t+1−2p·v)≥0. Thus projection cannot lose coverage. For projected centers c, activity is equivalent to |c|≥1−r; inactive centers satisfy strict |c|<1−r.

## At least ten active disks
A radius-r disk meeting S1 has connected circular arc intersection of halfwidth α with cosα=(1+t²−r²)/(2t)≥sqrt(1−r²), by completing (t−sqrt(1−r²))²≥0. Hence α≤asin r. A t=0 disk misses S1 since r<1.

We need no numerical trigonometry: sin(π/9)>1/3. Indeed 17/50<π/9<π/2 since π>31/10, and sin(17/50)≥17/50−(17/50)^3/6=250087/750000>1/3 (Taylor lower bound, or integrate cos x≥1−x²/2). Therefore asin r<π/9. Nine arcs each of length at most2asin r have total length strictly less than2π, even before overlaps. Thus k≥10.

## At least three inactive disks
Set a=1−2U>U≥r. For any |p|<a and active c,

    |p−c| ≥ |c|−|p| > (1−r)−a = 2U−r ≥ r.

Consequently only inactive disks cover the open core B(0,a). Their finite union is closed, so they cover its closure. Suppose at most two inactive disks do this. Each radius-r disk meets the circle |p|=a in an arc strictly shorter than a semicircle, or misses it: for nonzero center h, membership implies

    p·h ≥ (a²+|h|²−r²)/2 > 0,

and in fact its angular halfwidth is strictly belowπ/2. A disk centered at0 misses this circle because r<a. Two such arcs have total length<2π and cannot cover the core circle. Contradiction. Therefore14−k≥3, so k≤11.

The closure step is essential: strict ring exclusion is asserted on the open core, not at all boundary points. No inner-root replacement, symmetry, general position, or optimality premise was used.

## Consequence and missing implication
All arbitrary covers below the saved C411 upper bound lie in exactly two classes after projection:

- k10, four strictly inactive hubs;
- k11, three strictly inactive hubs.

To prove the n14 optimum one must still define and attain the exact candidate radius, prove the sharp k10 lower bound over its entire class, and handle the whole k11 class. This reduction does not solve any of those obligations. Unlike n12, r<1/3 itself already eliminates the one- and two-hub cases.
