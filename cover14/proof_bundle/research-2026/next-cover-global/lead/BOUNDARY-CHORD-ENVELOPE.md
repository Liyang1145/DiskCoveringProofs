# Valid asymmetric endpoint-chord envelope (replaces false symmetric bound)

Let x,y be endpoints of any covered unit-circle arc of lengthθ∈[0,π], with u=x−c,v=y−c, |u|,|v|≤r and included minor angleα∈[0,π]. For lengths a,b∈[0,r], the squared chord a²+b²−2ab cosα is convex in each coordinate. Its maximum over the square is at a corner, hence

    |x−y| ≤ max(r,2r sin(α/2)).

Consequently

    θ ≤ max(2asin(r/2), 2asin(r sin(α/2))).

The extra r term is ESSENTIAL: it covers strongly unequal endpoint distances, precisely the failure mode of the withdrawn symmetric subarc inequality. It applies even without innernorm normalization, providedθ,α are the minor angles as established in the safearea reduction.

At fixed U=.33173203427623414 set f(α)=2asin(U sin(α/2)), A=2asin(U/2). Then

 f'(α)=U cos(α/2)/sqrt(1−U²sin²(α/2)),
 f''(α)=−U(1−U²)sin(α/2)/[2(1−U²sin²(α/2))^(3/2)]≤0.

Using the tangent at exact α0=121/50=2.42, interval constants certify

    A<167/500=.334,
    0<f'(α0)<31/250=.124,
    f(α0)−α0 f'(α0)<167/500.

Thus the single rational affine envelope is VALID over allα∈[0,π]:

    θ ≤ max(A,f(α)) ≤ 167/500 +(31/250)α.

Forqboundaryowners, Σθ=2π therefore forces

    Σα_i ≥ K_q=(2π−q·167/500)/(31/250).

K10≈23.735,K11≈21.041. A stronger version keeps θ≤min(L,.334+.124α), but the simple totalangle lowerbound is already a strong missing coupling. Candidate actualcover Σα≈25.553 passes. Safearea optimizer proposals for ALLpreviouslyretainedgraphclasses violate the new inequality, which motivates a bounded new relaxation test—not a claim those graphs are impossible.

Certificate sign: for μ≥0 and Σα≥K, objective≤objective+μ(Σα−K). Thus add μ to each boundaryangle slope and subtract μK in the supportplane constant. RetainB t=2π1 and allangles∈[0,π]. Any rational μ,y,t0 yields rigorous upperbound after the same exact sine supportingplane calculation. Negative bound excludes the graph, not optimizer status.
