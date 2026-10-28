import N11Formalization.SourceFineBPointPacket
import N11Formalization.SourceNColumnProposal

/-! Integer packet for C(rhs-M*centre), with rhs and M*centre combined
BEFORE bounding. Fine coordinate endpoints, candidate45 binding,164 force-row
endpoint bindings and164 residual checks must all pass the kernel. No true N
or residual membership is assumed; semantic consumption is separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineNResidualPacket
open N11Formalization SourceN2 SourceFineBPointPacket SourceB41Proposal
section
-- Evaluator stack depth only; default heartbeats and kernel rules unchanged.
set_option maxRecDepth 10000

def QN : Fin 45 → Fin 4 → ℤ :=
 ![![3644885,-6250581,16581743,-1206197],![-36618202,-24352353,-18608115,-30012064],
   ![-29531141,-19639216,-15006714,-24203550],![7641196,29846136,-8390200,998476],
   ![20520990,-25719678,-22529699,-34997033],![0,0,0,100000000],
   ![-37808496,29583113,152,83115674],![0,0,100000000,0],
   ![41388656,-32384395,88318967,24901715],![33389477,79737897,-20098413,20088965],
   ![0,100000000,0,0],![-27446519,-25867970,-8988772,-26176838],
   ![-10221146,4399929,-3347819,29673919],![19869272,-21983762,-28951686,-30790069],
   ![24637620,-27259558,-35899686,-38179255],![3644599,-6250090,16580440,-1206102],
   ![2538273,-4352862,11547412,-839987],![2538465,-4353191,11548286,-840051],
   ![100000000,0,0,0],![52089722,0,0,0],![67743131,0,0,0],
   ![-88312959,8937478,53158875,25108070],![-46003650,4655677,27691318,13079200],
   ![-59827638,6054697,36012494,17009469],![-32064327,-21323871,-16293992,-26279735],
   ![-46309969,-30797708,-23533139,-37955379],![-63636544,-42320472,-32337911,-52156139],
   ![-52092790,40759804,209,14507149],![-42810470,33496888,172,11922147],
   ![-68355415,53484433,275,19036074],![46866935,-36670854,-188,28197753],
   ![37805363,-29580661,-152,22745807],![42809939,-33496473,-172,25756839],
   ![-33388328,26124570,20097721,-20088274],![-41389175,32384802,24913740,-24902028],
   ![-37807975,29582705,22758077,-22747379],![37806826,8097498,-22757385,22746687],
   ![46004017,9853180,-27691591,27678573],![60367515,12929566,-36337533,36320452],
   ![31158680,-34474590,-45401579,-48284502],![21573661,-23869533,-31435166,-33431246],
   ![42817520,-47374166,-62389774,-66351419],![2089843,-3583853,9507361,-691589],
   ![2090000,-3584122,9508074,-691641],![2588161,-4438413,11774367,-856496]]

theorem QN_dep (j : Fin 41) (a : Fin 4) :
    QN (dep j) a=SourceNColumnProposal.YN j a := by
  fin_cases j <;> rfl
theorem QN_free (b a : Fin 4) :
    QN (freeCol b) a=if b=a then 100000000 else 0 := by
  fin_cases b <;> fin_cases a <;> decide +kernel

def loEntry (i : Fin 41) (e : Fin 45) : ℤ :=
  if i.val=40 then 100000000 else
    let node := 9+i.val/2
    let q : Fin 2 := ⟨i.val%2,by omega⟩
    let dl := PL (srcEdgeV2 e) q-PH (srcEdgeW2 e) q
    let dh := PH (srcEdgeV2 e) q-PL (srcEdgeW2 e) q
    (if (srcEdgeV2 e).val=node then dl else 0)+
      (if (srcEdgeW2 e).val=node then -dh else 0)
def hiEntry (i : Fin 41) (e : Fin 45) : ℤ :=
  if i.val=40 then 100000000 else
    let node := 9+i.val/2
    let q : Fin 2 := ⟨i.val%2,by omega⟩
    let dl := PL (srcEdgeV2 e) q-PH (srcEdgeW2 e) q
    let dh := PH (srcEdgeV2 e) q-PL (srcEdgeW2 e) q
    (if (srcEdgeV2 e).val=node then dh else 0)+
      (if (srcEdgeW2 e).val=node then -dl else 0)

def forceLo (i : Fin 41) (a : Fin 4) : ℤ :=
  ∑ e : Fin 45, QN e a*(if 0≤QN e a then loEntry i e else hiEntry i e)
def forceHi (i : Fin 41) (a : Fin 4) : ℤ :=
  ∑ e : Fin 45, QN e a*(if 0≤QN e a then hiEntry i e else loEntry i e)

def FL : Fin 41 → Fin 4 → ℤ :=
 ![![-715051045,1134550983,-3209477975,218917221],
   ![-2328469055,3845533686,-10540590776,750604148],
   ![24549325658,16334882590,12488887497,20121323727],
   ![-38707938917,-25744673701,-19679519950,-31706979187],
   ![17949976282,-13535822816,-3254157793,-8479593165],
   ![-4250272114,-21541036608,-8633090921,-17529028381],
   ![3548121685,-4362007438,-2026604,-120645473679],
   ![33270219707,-26792684329,-13529740,-50073528383],
   ![-14051700755,7864641955,-57324894815,-8474918123],
   ![-8247364661,6092592578,-108719690912,-4940536033],
   ![-4887891899,-120273250382,1893947235,-2961427732],
   ![29387663004,45703156865,-18162966186,17663207962],
   ![-18543840952,-5785462813,6763921742,-9646287430],
   ![-279388015,14695903697,9152721017,23800035198],
   ![-17015101146,18267161267,24057686634,25599367756],
   ![-26053598005,28363653628,37375846442,39742325989],
   ![-710540621,1124757216,-3225210066,226223196],
   ![2676230332,-4734742854,12215710378,-913713083],
   ![777728425,-12574635977,10445414790,-9057903021],
   ![-2825278802,-46291523506,-7051206774,-23538783698],
   ![-252174852,19036833816,1127435225,19385978541],
   ![-19179054846,47138693105,23739869662,54399855180],
   ![-16357036971,0,0,0],![131042167992,0,0,0],
   ![13894670883,-1461603316,-8697828239,-4104595137],
   ![9917650557,-1037018394,-6218946630,-2923481145],
   ![-3115269221,-2087879990,-1584626678,-2570976252],
   ![-47357290148,-31472299802,-24048702953,-38804378007],
   ![-64100130175,48960545999,-4734606,17403872486],
   ![-81886758580,63103901684,-22876721,22469868324],
   ![74026586799,-61107821825,2014444,44567002581],
   ![46498245491,-37005515656,13526120,27983632597],
   ![-68971889927,51142291513,39368844502,-41488972916],
   ![-30150371571,23041710313,17703862506,-18144102402],
   ![55248715632,11849581576,-34095108456,33254222192],
   ![-11922187637,-2555293768,6555221556,-7147621007],
   ![1131285471,-2340668522,-3056702599,-3263483415],
   ![10972966242,-12721310511,-16710663572,-17778300211],
   ![3157455025,-5533527171,14380454667,-1089550812],
   ![4642206311,-8098515779,21081787573,-1565488102],
   ![200000000,100000000,-300000000,-400000000]]
def FH : Fin 41 → Fin 4 → ℤ :=
 ![![-666307875,1218140209,-2987729781,235047735],
   ![-2253387140,3974290989,-10199019251,775450909],
   ![25328460454,16853033801,12884817097,20759898046],
   ![-38116123711,-25351096406,-19378779746,-31221930908],
   ![19556928153,-12426208968,-2801381580,-7700040976],
   ![-3143021236,-20807908672,-8368210819,-17041256879],
   ![5558162011,-2789259080,-2018536,-118526098934],
   ![34257300393,-26020346827,-13525776,-48741952992],
   ![-10008627919,11028128809,-52297571129,-6042380829],
   ![-7808618894,6435887523,-108142563613,-4676562198],
   ![-3112783051,-118098976066,2962453668,-1893423601],
   ![30225985223,46933802248,-17658347736,18167589194],
   ![-17151576330,-5085953288,7830257886,-8373161437],
   ![691205738,15129460707,9855486208,24609898032],
   ![-16490880251,18847169812,24821533378,26411717475],
   ![-25655410298,28804216517,37956049150,40359370586],
   ![-661801191,1208340028,-3003478890,242352468],
   ![2751306511,-4605995386,12557255808,-888868227],
   ![4019146459,-10457033181,11360456115,-7376286963],
   ![-1551758280,-45572987945,-6691697363,-22951044252],
   ![976582228,19882825430,2122655580,20491704477],
   ![-18599786211,47547910484,24272536566,54899459841],
   ![-15717371265,0,0,0],![131462000845,0,0,0],
   ![14459585295,-1404432656,-8357785115,-3943985519],
   ![10288420722,-999495586,-5995766193,-2818068266],
   ![-1680423069,-1133658373,-855487038,-1394984747],
   ![-46600433869,-30968964569,-23664094531,-38184063032],
   ![-62561443785,50164485271,-4728424,17832376185],
   ![-80674589540,64052358706,-22871851,22807441283],
   ![78072545426,-57942077004,2030696,47001276148],
   ![47276257481,-36396763154,13529244,28451727851],
   ![-65398707220,53938114674,41519680871,-39339147601],
   ![-29463276656,23579325104,18117451416,-17730707913],
   ![56607571008,12140622382,-33277161047,34071785095],
   ![-10851688977,-2326013450,7199595947,-6503549528],
   ![2096698902,-1272515675,-1649990438,-1767447416],
   ![11482204029,-12157879576,-15968648840,-16989168801],
   ![3206422735,-5449552893,14603224349,-1073345996],
   ![4726605723,-7953779999,21465747333,-1537557922],
   ![200000000,100000000,-300000000,-400000000]]

def RowBinding (i : Fin 41) : Prop :=
  ∀ a : Fin 4,forceLo i a=FL i a ∧ forceHi i a=FH i a
private theorem bind0 : RowBinding 0 := by intro a; fin_cases a <;> decide +kernel
private theorem bind1 : RowBinding 1 := by intro a; fin_cases a <;> decide +kernel
private theorem bind2 : RowBinding 2 := by intro a; fin_cases a <;> decide +kernel
private theorem bind3 : RowBinding 3 := by intro a; fin_cases a <;> decide +kernel
private theorem bind4 : RowBinding 4 := by intro a; fin_cases a <;> decide +kernel
private theorem bind5 : RowBinding 5 := by intro a; fin_cases a <;> decide +kernel
private theorem bind6 : RowBinding 6 := by intro a; fin_cases a <;> decide +kernel
private theorem bind7 : RowBinding 7 := by intro a; fin_cases a <;> decide +kernel
private theorem bind8 : RowBinding 8 := by intro a; fin_cases a <;> decide +kernel
private theorem bind9 : RowBinding 9 := by intro a; fin_cases a <;> decide +kernel
private theorem bind10 : RowBinding 10 := by intro a; fin_cases a <;> decide +kernel
private theorem bind11 : RowBinding 11 := by intro a; fin_cases a <;> decide +kernel
private theorem bind12 : RowBinding 12 := by intro a; fin_cases a <;> decide +kernel
private theorem bind13 : RowBinding 13 := by intro a; fin_cases a <;> decide +kernel
private theorem bind14 : RowBinding 14 := by intro a; fin_cases a <;> decide +kernel
private theorem bind15 : RowBinding 15 := by intro a; fin_cases a <;> decide +kernel
private theorem bind16 : RowBinding 16 := by intro a; fin_cases a <;> decide +kernel
private theorem bind17 : RowBinding 17 := by intro a; fin_cases a <;> decide +kernel
private theorem bind18 : RowBinding 18 := by intro a; fin_cases a <;> decide +kernel
private theorem bind19 : RowBinding 19 := by intro a; fin_cases a <;> decide +kernel
private theorem bind20 : RowBinding 20 := by intro a; fin_cases a <;> decide +kernel
private theorem bind21 : RowBinding 21 := by intro a; fin_cases a <;> decide +kernel
private theorem bind22 : RowBinding 22 := by intro a; fin_cases a <;> decide +kernel
private theorem bind23 : RowBinding 23 := by intro a; fin_cases a <;> decide +kernel
private theorem bind24 : RowBinding 24 := by intro a; fin_cases a <;> decide +kernel
private theorem bind25 : RowBinding 25 := by intro a; fin_cases a <;> decide +kernel
private theorem bind26 : RowBinding 26 := by intro a; fin_cases a <;> decide +kernel
private theorem bind27 : RowBinding 27 := by intro a; fin_cases a <;> decide +kernel
private theorem bind28 : RowBinding 28 := by intro a; fin_cases a <;> decide +kernel
private theorem bind29 : RowBinding 29 := by intro a; fin_cases a <;> decide +kernel
private theorem bind30 : RowBinding 30 := by intro a; fin_cases a <;> decide +kernel
private theorem bind31 : RowBinding 31 := by intro a; fin_cases a <;> decide +kernel
private theorem bind32 : RowBinding 32 := by intro a; fin_cases a <;> decide +kernel
private theorem bind33 : RowBinding 33 := by intro a; fin_cases a <;> decide +kernel
private theorem bind34 : RowBinding 34 := by intro a; fin_cases a <;> decide +kernel
private theorem bind35 : RowBinding 35 := by intro a; fin_cases a <;> decide +kernel
private theorem bind36 : RowBinding 36 := by intro a; fin_cases a <;> decide +kernel
private theorem bind37 : RowBinding 37 := by intro a; fin_cases a <;> decide +kernel
private theorem bind38 : RowBinding 38 := by intro a; fin_cases a <;> decide +kernel
private theorem bind39 : RowBinding 39 := by intro a; fin_cases a <;> decide +kernel
private theorem bind40 : RowBinding 40 := by intro a; fin_cases a <;> decide +kernel

theorem force_binding (i : Fin 41) (a : Fin 4) :
    forceLo i a=FL i a ∧ forceHi i a=FH i a := by
  fin_cases i
  · exact bind0 a
  · exact bind1 a
  · exact bind2 a
  · exact bind3 a
  · exact bind4 a
  · exact bind5 a
  · exact bind6 a
  · exact bind7 a
  · exact bind8 a
  · exact bind9 a
  · exact bind10 a
  · exact bind11 a
  · exact bind12 a
  · exact bind13 a
  · exact bind14 a
  · exact bind15 a
  · exact bind16 a
  · exact bind17 a
  · exact bind18 a
  · exact bind19 a
  · exact bind20 a
  · exact bind21 a
  · exact bind22 a
  · exact bind23 a
  · exact bind24 a
  · exact bind25 a
  · exact bind26 a
  · exact bind27 a
  · exact bind28 a
  · exact bind29 a
  · exact bind30 a
  · exact bind31 a
  · exact bind32 a
  · exact bind33 a
  · exact bind34 a
  · exact bind35 a
  · exact bind36 a
  · exact bind37 a
  · exact bind38 a
  · exact bind39 a
  · exact bind40 a

def EL (i : Fin 41) (a : Fin 4) : ℤ :=
  -(∑ r : Fin 41,CN i r*(if 0≤CN i r then FH r a else FL r a))
def EH (i : Fin 41) (a : Fin 4) : ℤ :=
  -(∑ r : Fin 41,CN i r*(if 0≤CN i r then FL r a else FH r a))

def ResidualRow (i : Fin 41) : Prop :=
  ∀ a : Fin 4,max |EL i a| |EH i a|≤50000000000000000000
private theorem err0 : ResidualRow 0 := by intro a; fin_cases a <;> decide +kernel
private theorem err1 : ResidualRow 1 := by intro a; fin_cases a <;> decide +kernel
private theorem err2 : ResidualRow 2 := by intro a; fin_cases a <;> decide +kernel
private theorem err3 : ResidualRow 3 := by intro a; fin_cases a <;> decide +kernel
private theorem err4 : ResidualRow 4 := by intro a; fin_cases a <;> decide +kernel
private theorem err5 : ResidualRow 5 := by intro a; fin_cases a <;> decide +kernel
private theorem err6 : ResidualRow 6 := by intro a; fin_cases a <;> decide +kernel
private theorem err7 : ResidualRow 7 := by intro a; fin_cases a <;> decide +kernel
private theorem err8 : ResidualRow 8 := by intro a; fin_cases a <;> decide +kernel
private theorem err9 : ResidualRow 9 := by intro a; fin_cases a <;> decide +kernel
private theorem err10 : ResidualRow 10 := by intro a; fin_cases a <;> decide +kernel
private theorem err11 : ResidualRow 11 := by intro a; fin_cases a <;> decide +kernel
private theorem err12 : ResidualRow 12 := by intro a; fin_cases a <;> decide +kernel
private theorem err13 : ResidualRow 13 := by intro a; fin_cases a <;> decide +kernel
private theorem err14 : ResidualRow 14 := by intro a; fin_cases a <;> decide +kernel
private theorem err15 : ResidualRow 15 := by intro a; fin_cases a <;> decide +kernel
private theorem err16 : ResidualRow 16 := by intro a; fin_cases a <;> decide +kernel
private theorem err17 : ResidualRow 17 := by intro a; fin_cases a <;> decide +kernel
private theorem err18 : ResidualRow 18 := by intro a; fin_cases a <;> decide +kernel
private theorem err19 : ResidualRow 19 := by intro a; fin_cases a <;> decide +kernel
private theorem err20 : ResidualRow 20 := by intro a; fin_cases a <;> decide +kernel
private theorem err21 : ResidualRow 21 := by intro a; fin_cases a <;> decide +kernel
private theorem err22 : ResidualRow 22 := by intro a; fin_cases a <;> decide +kernel
private theorem err23 : ResidualRow 23 := by intro a; fin_cases a <;> decide +kernel
private theorem err24 : ResidualRow 24 := by intro a; fin_cases a <;> decide +kernel
private theorem err25 : ResidualRow 25 := by intro a; fin_cases a <;> decide +kernel
private theorem err26 : ResidualRow 26 := by intro a; fin_cases a <;> decide +kernel
private theorem err27 : ResidualRow 27 := by intro a; fin_cases a <;> decide +kernel
private theorem err28 : ResidualRow 28 := by intro a; fin_cases a <;> decide +kernel
private theorem err29 : ResidualRow 29 := by intro a; fin_cases a <;> decide +kernel
private theorem err30 : ResidualRow 30 := by intro a; fin_cases a <;> decide +kernel
private theorem err31 : ResidualRow 31 := by intro a; fin_cases a <;> decide +kernel
private theorem err32 : ResidualRow 32 := by intro a; fin_cases a <;> decide +kernel
private theorem err33 : ResidualRow 33 := by intro a; fin_cases a <;> decide +kernel
private theorem err34 : ResidualRow 34 := by intro a; fin_cases a <;> decide +kernel
private theorem err35 : ResidualRow 35 := by intro a; fin_cases a <;> decide +kernel
private theorem err36 : ResidualRow 36 := by intro a; fin_cases a <;> decide +kernel
private theorem err37 : ResidualRow 37 := by intro a; fin_cases a <;> decide +kernel
private theorem err38 : ResidualRow 38 := by intro a; fin_cases a <;> decide +kernel
private theorem err39 : ResidualRow 39 := by intro a; fin_cases a <;> decide +kernel
private theorem err40 : ResidualRow 40 := by intro a; fin_cases a <;> decide +kernel

theorem all_residuals (i : Fin 41) (a : Fin 4) :
    max |EL i a| |EH i a|≤50000000000000000000 := by
  fin_cases i
  · exact err0 a
  · exact err1 a
  · exact err2 a
  · exact err3 a
  · exact err4 a
  · exact err5 a
  · exact err6 a
  · exact err7 a
  · exact err8 a
  · exact err9 a
  · exact err10 a
  · exact err11 a
  · exact err12 a
  · exact err13 a
  · exact err14 a
  · exact err15 a
  · exact err16 a
  · exact err17 a
  · exact err18 a
  · exact err19 a
  · exact err20 a
  · exact err21 a
  · exact err22 a
  · exact err23 a
  · exact err24 a
  · exact err25 a
  · exact err26 a
  · exact err27 a
  · exact err28 a
  · exact err29 a
  · exact err30 a
  · exact err31 a
  · exact err32 a
  · exact err33 a
  · exact err34 a
  · exact err35 a
  · exact err36 a
  · exact err37 a
  · exact err38 a
  · exact err39 a
  · exact err40 a

end
end N11Formalization.SourceFineNResidualPacket
#check @N11Formalization.SourceFineNResidualPacket.QN_dep
#check @N11Formalization.SourceFineNResidualPacket.QN_free
#check @N11Formalization.SourceFineNResidualPacket.force_binding
#check @N11Formalization.SourceFineNResidualPacket.all_residuals
#print axioms N11Formalization.SourceFineNResidualPacket.all_residuals
