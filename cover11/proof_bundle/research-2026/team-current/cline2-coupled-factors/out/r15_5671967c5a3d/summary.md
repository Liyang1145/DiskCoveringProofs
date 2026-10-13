# R15 joint-patch factor bounds (joint_nested_frozen.json)
coefficient sha256 = `5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb`
certifier = lead/certify_joint_rest_tight.py (kernel lead/certify_q0_closure.py, dps=30, C844 filter, per-factor budgets)

sum of present uppers = **-1.524205123108**
all 22 present and digest-clean: **True**
missing: []
digest mismatches: []

source hashes captured at launch: see summary.json `source_hashes`

| fi | factor | upper | lower_probe | evals | budget_ended | digest_ok |
|---|---|---|---|---|---|---|
| 0 | face0 | 0.3413027967429324 | 0.3412827985097411 | 12291 | False | True |
| 3 | face3 | 0.33911062922752655 | 0.33909063372788756 | 3633 | False | True |
| 4 | face4 | -0.2603453981107087 | -0.2603646349067799 | 1097 | False | True |
| 5 | face5 | -0.016982176657950928 | -0.017002030081283245 | 1027 | False | True |
| 6 | face6 | -0.05335241614363209 | -0.05337222569147212 | 2027 | False | True |
| 7 | face7 | -0.016951217443736778 | -0.016970746887509665 | 1065 | False | True |
| 8 | face8 | -0.2603454622120701 | -0.26036533190206146 | 1277 | False | True |
| 9 | face9 | 0.16107808114822725 | 0.16105808668810534 | 20209 | False | True |
| 10 | face10 | 0.16018700972299357 | 0.16016701407441664 | 21253 | False | True |
| 11 | switch0 | 2.0002210378923662e-05 | 2.7289974150546984e-08 | 1411 | False | True |
| 14 | switch3 | 1.9951263031208914e-05 | 4.188476284583149e-09 | 1411 | False | True |
| 15 | switch4 | 1.9717507446096554e-05 | 5.55731982572445e-08 | 1291 | False | True |
| 16 | switch5 | 0.1293400989065974 | 0.12932011589065326 | 611 | False | True |
| 17 | switch6 | 1.9817239190319613e-05 | 2.418569556707344e-09 | 1211 | False | True |
| 18 | switch7 | 0.13020305920540254 | 0.1301831095172223 | 623 | False | True |
| 19 | switch8 | 1.9853416430433903e-05 | 3.831215479037999e-08 | 1291 | False | True |
| 20 | ring0 | -0.548677388561477 | -0.5487573734996875 | 16945 | False | True |
| 24 | ring4 | -0.5571787901629601 | -0.557258750667122 | 19717 | False | True |
| 25 | ring5 | -0.45520995848631624 | -0.45528994163830505 | 33043 | False | True |
| 26 | ring6 | -0.05475261592029134 | -0.054832537119449624 | 7227 | False | True |
| 27 | ring7 | -0.10161960645889918 | -0.10169960401101923 | 109329 | False | True |
| 28 | ring8 | -0.4601111095399978 | -0.4601910779429876 | 25247 | False | True |

SCOPE.  These are the 22 remaining patch factors under the CURRENT frozen
coefficients.  They are NOT a bound on the patch or the global objective, and the
Q0 complement is NOT claimed covered.  The two separate quantities are:
  * LOCAL patch (Q0 ridge box only, conditional): 28.10439974622152  (C854)
  * ENTIRE patch as currently loose:             28.315358592526042
No sharp global bound and no flat-sector-2 exclusion is claimed.