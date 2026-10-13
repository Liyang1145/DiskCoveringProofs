# k9 metric class ledger

Original target unrestricted12 disks. This ledger concerns k9 after the same-arc inner-root reduction and duplicate hub merge, m=1..3. It does not assume the input is symmetric or nondegenerate.

Geometric/combination source: members/nine-topology/{K9-DUAL-DISK.md,K9-TYPE-LIST.md,graphs.json,gen_graphs.py}. Each polygon face of the clipped dual is triangulated with duplicated original witness, hence exact≤r constraints. Hub count m1 givesM1; m2 givesM2; m3 gives T3,T2,P4,P3,P2. This is a covering-to-relaxed-network implication; no realization of arbitrary relaxed assignments is required. Lead inspected/corrected facet-connectivity and boundary-spoke arguments and invalid original-m2-trivalence premise.

Metric status:
- M1(1),M2(4),T2(4),P4(20),P3(16),P2(4): all49 passed exact outward-rational interval Taylor certificates. `evidence/network-certified-{graph_id}.json`. Smallest excess energy aboveU² among these≈.004517111744283579 at P3-3-2-4.
- T3 noncandidate6:117,126,135,144,225,234 certified by `evidence/network-certified-{digits}.json`; smallest margin≈.0002926037875967265 at234, κ=1/50.
- T3 candidate333: sharp stress lower bound r* follows ROOT-AND-NETWORK-BRIDGE.md, conditional identities now have isolated F,G,H,T root from root_t_certificate.py; independent audit pending. Do not replace this sharp theorem with approximate scout energy.

All55 NONCANDIDATE networks thus have strict lower radius>U according to the exact certificates and analytic Taylor inference. Root r*<U. The cover→network exhaustive reduction and arithmetic kernel remain under independent review before synthesizing an accepted k9 theorem. The ideal candidate upper coverage is also pending, as are BOTH k10/k11 exclusions.

Reproduction:
1. py -3 -B lead/triangle_batch.py (relative paths when running inside this folder need adjustment; standard workspace paths below).
2. py -3 -B research-2026/n12-global/lead/general_network_batch.py all
3. py -3 -B research-2026/n12-global/lead/network_interval_certificate.py 234 1/50
4. py -3 -B research-2026/n12-global/lead/root_t_certificate.py
Evidence proposals are not theorems; verification can run on saved rational weights/reference without optimization.

Batch bookkeeping: the first general `all` run's family exclusion compared'T3' with catalogue'T3 (lead-owned)', so it harmlessly processed all56 rather than49. Its automatic κ=.021 for234 was too weak for Taylor bound; this is an algorithmic inconclusive result, superseded for that graph by already successful κ=.020 certificate. Candidate333 properly failed strict>U exclusion. Neither is a counterexample. Filter fixed subsequently; raw general-batch-all.json remains provenance.
