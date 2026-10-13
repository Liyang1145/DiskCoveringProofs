# Strict separation bound from core coverage and inactivity

Analytic lemma, global over normalized k10 covers at exact rational U. No dual certificate is a premise. Let a0=1−2U>0. Suppose two radius-U disks centered at h1,h2 cover B(0,a0), and both |hj|<1−U. Then |h1−h2|<2U.

Proof. For coincident centers the assertion is immediate. Otherwise rotate, reflect, and relabel to write h1=(x−s,y), h2=(x+s,y), with x,y≥0, s=|h1−h2|/2>0. If x≥a0, inactivity of h2 gives x+s≤|h2|<1−U, hence s<1−U−a0=U. If 0≤x<a0, the point p=(x,−sqrt(a0²−x²)) lies in the core. It has equal squared distances s²+(y+sqrt(a0²−x²))² to the hubs. Since it is covered by their union, this quantity is at most U². The square added to s² is strictly positive because x<a0 and y≥0; hence s<U. Both cases are strict. QED.

Consequences: the entire d≥2U k10 branch is empty by elementary geometry, independently of C998. The case x=a0 belongs in the first case, so no artificial equality or generic-position argument is needed. The s=U face in a closed relaxed computational root contains no legal k10 cover. Thus atom intersection normals are never antiparallel at any legal point in the remaining chart. This simplifies a bearing dependency; it does not eliminate the unresolved k10 boxes with 1/20<s<U.

Independent derivation appeared in members/structure/global-interface-audit.md §(3); this version explicitly separates x=a0 and uses strict positivity in the second case. Older separated-hub connectedness/onehub-capacity argument remains valid but is not needed for this branch.
