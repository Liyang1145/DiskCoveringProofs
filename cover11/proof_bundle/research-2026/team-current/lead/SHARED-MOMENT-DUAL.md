# Shared first-and-second moment dual (round3 work in progress)

Scope: remaining q1 balanced(6,6) graphs, core starts0,2. Original unconditional n11 optimum still open.

True side matching imposes both y_f sin A=y_g sin B and y_f²sin² A=y_g²sin² B, where y=rho/R∈[0,1]. Similarly switch-to-sector endpoint radius copies match in both first and second power. The first equation implies the second on genuine geometry, but keeping both before factor decoupling strengthens weak duality. Add21 free side-first multipliers z[73:94] and18 free radius-copy-first multipliers z[94:112] to the existing C817 dual. Constant unchanged. Face factor is linear angle part+Q(A,B), where Q=max_{0<=y<=1}(A y²+B y), A is the previous squared-radius coefficient, B=sum signed new side multipliers*sin(opposite angle). Switch factor likewise has B=−side-first*sin b+two copy-first multipliers. Ring factors add −copy-left-first*u−copy-right-first*v.

Q is analytic: endpoints0,A+B; if A<0 and0<B<−2A also vertex−B²/(4A). Q is monotone in each coefficient since y,y²>=0, giving interval enclosure Q([a0,a1],[b0,b1])⊂[Q(a0,b0),Q(a1,b1)]. Maximizers are also nondecreasing in each coefficient: for y2>y1, increasing A or B strictly increases the difference Ay2²+By2−Ay1²−By1 unless increment zero. Ties use a full enclosing minimizer/maximizer interval. This bounds radii of maximizers and supports an interval envelope-gradient enclosure by Danskin's theorem / directional derivative of a maximum. On boxes fully inside the triangular angle domain, compute gradient at fixed radius in that interval; centered mean-value bound follows from local Lipschitz envelope even at ties. Boundary-crossing boxes use the direct enclosure. Ring gradients add only constant first-moment derivatives to C817's kernel.

Audit: check_shared_moment_symbolic.py independently assembles all first/second side/radius formal atoms, checks exact rational coefficient cancellation and two graph orbits {0,1,4,5},{2,3,6,7}.

Diagnostics:
- Individual outside-six owned widths >=2(pi−asin(2R)−5asin R) and consequent switch lower radii give no improvement to prior finite dual, though valid.
- Ear-radius8-box tests: upper bins remain above pi; ear-angle8 then24 slices leave middle-angle gaps. No exclusion.
- Ear capacity improved from2R toR+rho_ear also did not improve sampled optimum.
- First/second matching N60,NR10 proposal gave3.13194,3.13465; the start2 continuous certificate attempt actually returned3.164374>pi. This is an honest failure of that coefficient set, not a theorem disproof. Largest missed maxima at interior ring radii plus switch cap removal; grids were NOT certificates. `compare_moment_factors.py` quantifies discrepancies.
- Next: proposal with dense ring radius grid and uncapped switches, matching certificate domains. Do not promote sampled dual outputs.

Files: shared_moment_dual.py, shared_moment_dense.py (proposals), certify_shared_moments.py (interval verifier), check_shared_moment_symbolic.py (exact formal control).

Final dense coefficients certified at tolerance.00004: start0 area<3.135494, start2<3.139813, both<pi. Full coverage/controls/conclusion in Q1-BALANCED-EXCLUSION.md. First/second matching successfully excludes both balanced q1 graphs; coarse-grid errors remain historical diagnostic failures, not bearing premises.
