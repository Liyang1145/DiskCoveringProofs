# Exact boundary viewing-angle envelope under inner normalization

## Object and theorem
Fix0<r<1/3, s=sqrt(1−r²), u=asinr. A diskcenter |c|≤s covers a unitcircle arc oflengthθ∈[0,2u]. Letα∈[0,π] be its viewingangle fromc, as in the safearea reduction. Then the SHARP necessary bound is

 θ ≤ max(a_r(α),b_r(α)),
 a_r(α)=α−acos(s cosα)+u,
 b_r(α)=2asin(r sin(α/2)).

Unlike the earlier endpoint-corner bound, this vanishes atα=0 and has no artificial constant plateau. Each branch is attained by an explicit normalizeddisk. No globalcoverrealizability follows from this singlearc theorem.

## Complete extremizer proof for fixedθ
The casesθ=0 andθ=2u followbycontinuity; atθ=2u the two radiusr disks centered at thearcendpoints intersect at onepointc=(s,0), givingα=π. Assume0<θ<2u. Put h=θ/2, v=sinh>0, H=cosh>s and rotateendpoints to x±=(H,±v). Reflect so c=(H−d,b), b≥0. Innernorm gives d≥H−s>0; coveringthefarendpoint gives d²+(b+v)²≤r². Put D=sqrt(r²−v²); thus d∈[H−s,D]. Throughoutthisinterval d<H (sinceD≤r<H).

For fixedd thelargestfeasibleb is

 B(d)=min(sqrt(s²−(H−d)²), sqrt(r²−d²)−v).

Thefirstbranch increasesstrictly, theseconddecreasesstrictly. At leftendpoint thefirstis0 andthesecondpositive; at rightendpoint thesecondis0 andthefirstpositive. Hence exactlyonecrossingd*=r(rH−sv), b*=s(rH−sv). This followsalso bysubtractingthetwoactivecircleequations: Hd+vb=r²−v².

The viewingangle satisfies

 cotα=(d²+b²−v²)/(2dv).

Sincecotdecreasesstrictlyon(0,π), minimizingα is maximizingthisexpression. It increaseswithb², so useB(d). Onthenorm-limitedbranch,

 cotα=H/v−r²/(2vd),

which increasesstrictlywithd. Onthedisk-limitedbranch,

 cotα=[r²−2v sqrt(r²−d²)]/(2vd),
 derivative=r²/d² · [1/sqrt(r²−d²)−1/(2v)].

Thebracketincreaseswithd. ThusanyinteriorcriticalpointisaMINIMUM, neveramaximum. Themaximumoverthewholefeasibleintervalisthereforeattainedatoneoftwochoices:
1. d=D,b=0: bothendpointdistancesr, α_sym=2asin(v/r).
2. d=d*,b=b*: oneendpointdistancer and|c|=s.
Nootherendpointorinteriorbranchisomitted.

## Inverting the two branches
Choice1immediatelygivesθ=b_r(α).
Forchoice2rotatec to(s,0); thefarendpoint is atunitcircleangle−u andtheotheratθ−u. Itsrayfromc has direction(sinα,−cosα). If itsunitcircleangleist, theperpendicularrayprojectiongives cos(t−α)=s cosα. The branchwitht−α∈[−π,0] is

 t=α−acos(s cosα), θ=t+u=a_r(α).

Bothfunctionsarestrictlyincreasingfrom0to2u. For a, a'=1−s sinα/sqrt(1−s²cos²α)>0 because thedenominatorsquaredminus s²sin²α isr²>0. Thebderivative ispositiveforα<π. Thereforeminimizingαatfixedθ andtheninvertingyieldsθ≤max(a,b), withattainmentoneachbranchwhereitdominates.

## Certified affine majorants without interval differentiation
b_risconcaveon[0,π], asprovedinBOUNDARY-CHORD-ENVELOPE.md.

 a_r''(α)=−s r²cosα/[1−s²cos²α]^(3/2),

so a isconcaveon[0,π/2] andconvexon[π/2,π]. A tangentline to a atsomeα_a∈(0,π/2) majorizesitsfirsthalf. Ifthatlinealsoexceeds a(π)=2u, convexity ensuresitmajorizesitssecondhalf. A rationalaffineline dominatingthistangentANDa b-tangent onthewhole[0,π] thereforeboundsmax(a,b). This offers cleanintervalcertificateconditions, withoutgridcertification.

Numericonly common-tangentproposal: α_a≈.45791016104521126, α_b≈1.7697954935880709, slope≈.21739391912922756, intercept≈.13449226539291315. Notyetanexactcertifiedline. Moreusefultangentfamiliesmayretainbbranchcurvature ratherthanreplacingthewholeenvelopebyoneline.

Scope: analytic singlearc extremizerclassification; no newcatalogueexclusionsyet. RootCC2 independently assigned the branchendpointaudit.

## Fixed-U transfer
Forfixedα, ∂a_r/∂r=[1−r cosα/sqrt(1−(1−r²)cos²α)]/sqrt(1−r²)≥0, because thedenominatorsquaredminus r²cos²α is sin²α≥0. Also b_r increaseswithr. Thus a_r≤a_U,b_r≤b_U forr≤U even though thenormalizedcenterbound depends onr. Foroutwardclip radii slightlyaboveU, firstpass thecompactanglelimit tor, THEN applymonotonicity. No silentchange fromsqrt(1−r²)tosqrt(1−U²) isallowed.

## Certified use and catalogue result
`innernorm_line_certificate.py` proves the rational line a,b≤.135+.218α by directed intervals; independent exactFraction constants in `innernorm_fraction_constants.py` certify the same five strict signs. Combined with C1211's old line and cap, use h(α)=min(.135+.218α,.333272257+.123099267α,.676277969). This is concave piecewiseaffine, with rational orderedbreakpoints. The support of bα+μh(α) for μ≥0 is the maximum at the two breakpoints and0,π. Analyticcertificate interface unchanged from AREA-CAPPED-CHORD.md.

One boundedpass through1086 C1211 systems removes120 more:25q10m4+95q11m3. Retained **966=341q10m4+625q11m3**, explicit `innernorm-retained.json`. `innernorm-combined-catalogue.jsonl` storesallplanes and metadatahashes. Independent exactFraction replay ALL120 passes (`innernorm-combined-catalogue-fraction-replay.json`), as do12 calibrationplanes. Neitheroptimizer convergence nor memberidentity is a premise. The geometricproof here is leadanalytic; member initially issued falseobjections and laterwithdrewall, asrecordedinDEAD.md. No independent graphreduction audit claimed.

Next structural obligation is joint boundaryarea/perimeter support (`BOUNDARY-AREA-PERIMETER-JOINT.md`), which avoids taking incompatible cornermaxima separately. The sharpglobalcoveringradius is still unproved.
