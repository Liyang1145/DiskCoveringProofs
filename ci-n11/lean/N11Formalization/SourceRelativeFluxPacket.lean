import N11Formalization.SourceRelativeFluxGeometry

/-! Exact rational actual flux/G input readouts at scale10^9.
All literal shapes and72+36 outwardContains obligations plus integer norm
comparisons must pass Lean. No floating equality or diagnostic premise. -/
set_option autoImplicit false
namespace N11Formalization.SourceRelativeFluxPacket
open N11Formalization RatInterval SourceRelativeFluxGeometry
open SourceActiveMatrixIntervals SourceBPointPacket SourceRelativeNormPacket
noncomputable section
set_option maxRecDepth 10000

def FL : Fin 9 → Fin 4 → Fin 2 → ℤ :=
 ![![![739098,-102352],![1064384,122355],![735438,-467452],![787501,66716]],![![-543817,240032],![-1009757,88056],![-223709,596450],![-501721,369095]],![![285945,219916],![-961082,-158292],![-480028,240952],![-2366786,-1457855]],![![-490834,-895796],![788128,537697],![114793,-2759814],![1990495,1341149]],![![844997,161325],![1873587,-1660926],![-60846,2759773],![759423,-223868]],![![-925660,316141],![-2210968,1428265],![-354223,-225963],![-994722,115587]],![![190190,-135782],![-489986,-343846],![-328880,-698312],![-1102070,-237711]],![![-120307,84113],![707460,-151408],![889267,438692],![1245717,-101199]],![![-99465,-20567],![90983,-25223],![-415153,-21127],![45607,-23362]]]

def FH : Fin 9 → Fin 4 → Fin 2 → ℤ :=
 ![![![767413,-75858],![1099117,154857],![764547,-440210],![819642,96791]],![![-512619,282280],![-971431,139924],![-191716,639783],![-466323,417040]],![![307369,235158],![-934699,-139486],![-458022,256612],![-2341960,-1440049]],![![-469302,-880446],![814451,556444],![137149,-2743802],![2015135,1358769]],![![868895,202849],![1902959,-1609951],![-36133,2802577],![786449,-176827]],![![-904094,331525],![-2184254,1447402],![-332244,-210329],![-970256,133034]],![![221298,-93625],![-451795,-292113],![-296876,-654968],![-1066515,-189609]],![![-92092,110507],![742136,-118963],![918401,465958],![1277930,-71052]],![![-67013,20579],![130759,25208],![-381767,21182],![82450,23353]]]

def GLo : Fin 9 → Fin 4 → ℤ :=
 ![![1112702,1213787,1643881,924206],![-1157861,-2038796,-627750,-1113524],![700927,-1885916,-682998,-5508607],![-2029918,1592012,-5022063,3989578],![-359223,-4515475,5136081,-1009861],![1909348,5150592,424796,1868070],![-410883,978545,776883,2165414],![-37881,-830187,-1929669,-1626431],![-41161,-50422,-42373,-46710]]

def GHi : Fin 9 → Fin 4 → ℤ :=
 ![![1190092,1308734,1723469,1012051],![-1083855,-1947883,-551855,-1029554],![752478,-1822377,-630034,-5448563],![-1985118,1646727,-4975323,4041053],![-264199,-4398662,5234199,-902260],![1961316,5215157,477680,1927003],![-337110,1069133,852812,2249765],![39188,-735423,-1850003,-1538355],![41139,50450,42272,46727]]


def FB (k : Fin 9) (a : Fin 4) (c : Fin 2) : RatInterval :=
  intv ((FL k a c : ℚ)/1000000000) ((FH k a c : ℚ)/1000000000)
def GB (k : Fin 9) (a : Fin 4) : RatInterval :=
  intv ((GLo k a : ℚ)/1000000000) ((GHi k a : ℚ)/1000000000)

private theorem p0_0 : pointI (anchorNode 0) 0 = intv (-73577/100000 : ℚ) (-73574/100000) := rfl
private theorem p0_1 : pointI (anchorNode 0) 1 = intv (-67726/100000 : ℚ) (-67723/100000) := rfl
private theorem s0_0_0 : pointI (spokeNode 0 0) 0 = intv (-76472/100000 : ℚ) (-76469/100000) := rfl
private theorem s0_0_1 : pointI (spokeNode 0 0) 1 = intv (-29838/100000 : ℚ) (-29835/100000) := rfl
private theorem n0_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 0 = intv (219530/1000000000 : ℚ) (288444/1000000000) := rfl
private theorem n0_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 1 = intv (-380532/1000000000 : ℚ) (-296069/1000000000) := rfl
private theorem n0_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 2 = intv (1180480/1000000000 : ℚ) (1251210/1000000000) := rfl
private theorem n0_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 3 = intv (-234495/1000000000 : ℚ) (-156238/1000000000) := rfl
private theorem s0_1_0 : pointI (spokeNode 0 1) 0 = intv (-35580/100000 : ℚ) (-35577/100000) := rfl
private theorem s0_1_1 : pointI (spokeNode 0 1) 1 = intv (-67363/100000 : ℚ) (-67360/100000) := rfl
private theorem n0_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 0 = intv (-1997508/1000000000 : ℚ) (-1928594/1000000000) := rfl
private theorem n0_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 1 = intv (-2914944/1000000000 : ℚ) (-2830480/1000000000) := rfl
private theorem n0_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 2 = intv (-1916544/1000000000 : ℚ) (-1845814/1000000000) := rfl
private theorem n0_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 3 = intv (-2168842/1000000000 : ℚ) (-2090586/1000000000) := rfl
private theorem fb0_0_0 : FB 0 0 0 = intv (739098/1000000000 : ℚ) (767413/1000000000) := rfl
private theorem fb0_0_1 : FB 0 0 1 = intv (-102352/1000000000 : ℚ) (-75858/1000000000) := rfl
private theorem fb0_1_0 : FB 0 1 0 = intv (1064384/1000000000 : ℚ) (1099117/1000000000) := rfl
private theorem fb0_1_1 : FB 0 1 1 = intv (122355/1000000000 : ℚ) (154857/1000000000) := rfl
private theorem fb0_2_0 : FB 0 2 0 = intv (735438/1000000000 : ℚ) (764547/1000000000) := rfl
private theorem fb0_2_1 : FB 0 2 1 = intv (-467452/1000000000 : ℚ) (-440210/1000000000) := rfl
private theorem fb0_3_0 : FB 0 3 0 = intv (787501/1000000000 : ℚ) (819642/1000000000) := rfl
private theorem fb0_3_1 : FB 0 3 1 = intv (66716/1000000000 : ℚ) (96791/1000000000) := rfl
private theorem gb0_0 : GB 0 0 = intv (1112702/1000000000 : ℚ) (1190092/1000000000) := rfl
private theorem gb0_1 : GB 0 1 = intv (1213787/1000000000 : ℚ) (1308734/1000000000) := rfl
private theorem gb0_2 : GB 0 2 = intv (1643881/1000000000 : ℚ) (1723469/1000000000) := rfl
private theorem gb0_3 : GB 0 3 = intv (924206/1000000000 : ℚ) (1012051/1000000000) := rfl
private theorem p1_0 : pointI (anchorNode 1) 0 = intv (-14460/100000 : ℚ) (-14457/100000) := rfl
private theorem p1_1 : pointI (anchorNode 1) 1 = intv (-98951/100000 : ℚ) (-98948/100000) := rfl
private theorem s1_0_0 : pointI (spokeNode 1 0) 0 = intv (-35580/100000 : ℚ) (-35577/100000) := rfl
private theorem s1_0_1 : pointI (spokeNode 1 0) 1 = intv (-67363/100000 : ℚ) (-67360/100000) := rfl
private theorem n1_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 0 = intv (-1617580/1000000000 : ℚ) (-1548666/1000000000) := rfl
private theorem n1_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 1 = intv (-2358961/1000000000 : ℚ) (-2274498/1000000000) := rfl
private theorem n1_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 2 = intv (-1552462/1000000000 : ℚ) (-1481732/1000000000) := rfl
private theorem n1_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 3 = intv (-1756659/1000000000 : ℚ) (-1678403/1000000000) := rfl
private theorem s1_1_0 : pointI (spokeNode 1 1) 0 = intv (9482/100000 : ℚ) (9485/100000) := rfl
private theorem s1_1_1 : pointI (spokeNode 1 1) 1 = intv (-69444/100000 : ℚ) (-69441/100000) := rfl
private theorem n1_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 0 = intv (775252/1000000000 : ℚ) (844166/1000000000) := rfl
private theorem n1_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 1 = intv (2051571/1000000000 : ℚ) (2136034/1000000000) := rfl
private theorem n1_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 2 = intv (-506081/1000000000 : ℚ) (-435350/1000000000) := rfl
private theorem n1_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 3 = intv (467416/1000000000 : ℚ) (545672/1000000000) := rfl
private theorem fb1_0_0 : FB 1 0 0 = intv (-543817/1000000000 : ℚ) (-512619/1000000000) := rfl
private theorem fb1_0_1 : FB 1 0 1 = intv (240032/1000000000 : ℚ) (282280/1000000000) := rfl
private theorem fb1_1_0 : FB 1 1 0 = intv (-1009757/1000000000 : ℚ) (-971431/1000000000) := rfl
private theorem fb1_1_1 : FB 1 1 1 = intv (88056/1000000000 : ℚ) (139924/1000000000) := rfl
private theorem fb1_2_0 : FB 1 2 0 = intv (-223709/1000000000 : ℚ) (-191716/1000000000) := rfl
private theorem fb1_2_1 : FB 1 2 1 = intv (596450/1000000000 : ℚ) (639783/1000000000) := rfl
private theorem fb1_3_0 : FB 1 3 0 = intv (-501721/1000000000 : ℚ) (-466323/1000000000) := rfl
private theorem fb1_3_1 : FB 1 3 1 = intv (369095/1000000000 : ℚ) (417040/1000000000) := rfl
private theorem gb1_0 : GB 1 0 = intv (-1157861/1000000000 : ℚ) (-1083855/1000000000) := rfl
private theorem gb1_1 : GB 1 1 = intv (-2038796/1000000000 : ℚ) (-1947883/1000000000) := rfl
private theorem gb1_2 : GB 1 2 = intv (-627750/1000000000 : ℚ) (-551855/1000000000) := rfl
private theorem gb1_3 : GB 1 3 = intv (-1113524/1000000000 : ℚ) (-1029554/1000000000) := rfl
private theorem p2_0 : pointI (anchorNode 2) 0 = intv (40459/100000 : ℚ) (40462/100000) := rfl
private theorem p2_1 : pointI (anchorNode 2) 1 = intv (-91450/100000 : ℚ) (-91447/100000) := rfl
private theorem s2_0_0 : pointI (spokeNode 2 0) 0 = intv (9482/100000 : ℚ) (9485/100000) := rfl
private theorem s2_0_1 : pointI (spokeNode 2 0) 1 = intv (-69444/100000 : ℚ) (-69441/100000) := rfl
private theorem n2_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 0 = intv (281831/1000000000 : ℚ) (350745/1000000000) := rfl
private theorem n2_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 1 = intv (-1898906/1000000000 : ℚ) (-1814443/1000000000) := rfl
private theorem n2_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 2 = intv (-1425940/1000000000 : ℚ) (-1355209/1000000000) := rfl
private theorem n2_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 3 = intv (-3071544/1000000000 : ℚ) (-2993288/1000000000) := rfl
private theorem s2_1_0 : pointI (spokeNode 2 1) 0 = intv (61580/100000 : ℚ) (61583/100000) := rfl
private theorem s2_1_1 : pointI (spokeNode 2 1) 1 = intv (-59862/100000 : ℚ) (-59859/100000) := rfl
private theorem n2_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 0 = intv (-940675/1000000000 : ℚ) (-940674/1000000000) := rfl
private theorem n2_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 1 = intv (1764816/1000000000 : ℚ) (1764817/1000000000) := rfl
private theorem n2_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 2 = intv (181172/1000000000 : ℚ) (181173/1000000000) := rfl
private theorem n2_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 3 = intv (6699589/1000000000 : ℚ) (6699590/1000000000) := rfl
private theorem fb2_0_0 : FB 2 0 0 = intv (285945/1000000000 : ℚ) (307369/1000000000) := rfl
private theorem fb2_0_1 : FB 2 0 1 = intv (219916/1000000000 : ℚ) (235158/1000000000) := rfl
private theorem fb2_1_0 : FB 2 1 0 = intv (-961082/1000000000 : ℚ) (-934699/1000000000) := rfl
private theorem fb2_1_1 : FB 2 1 1 = intv (-158292/1000000000 : ℚ) (-139486/1000000000) := rfl
private theorem fb2_2_0 : FB 2 2 0 = intv (-480028/1000000000 : ℚ) (-458022/1000000000) := rfl
private theorem fb2_2_1 : FB 2 2 1 = intv (240952/1000000000 : ℚ) (256612/1000000000) := rfl
private theorem fb2_3_0 : FB 2 3 0 = intv (-2366786/1000000000 : ℚ) (-2341960/1000000000) := rfl
private theorem fb2_3_1 : FB 2 3 1 = intv (-1457855/1000000000 : ℚ) (-1440049/1000000000) := rfl
private theorem gb2_0 : GB 2 0 = intv (700927/1000000000 : ℚ) (752478/1000000000) := rfl
private theorem gb2_1 : GB 2 1 = intv (-1885916/1000000000 : ℚ) (-1822377/1000000000) := rfl
private theorem gb2_2 : GB 2 2 = intv (-682998/1000000000 : ℚ) (-630034/1000000000) := rfl
private theorem gb2_3 : GB 2 3 = intv (-5508607/1000000000 : ℚ) (-5448563/1000000000) := rfl
private theorem p3_0 : pointI (anchorNode 3) 0 = intv (92557/100000 : ℚ) (92560/100000) := rfl
private theorem p3_1 : pointI (anchorNode 3) 1 = intv (-37856/100000 : ℚ) (-37853/100000) := rfl
private theorem s3_0_0 : pointI (spokeNode 3 0) 0 = intv (61580/100000 : ℚ) (61583/100000) := rfl
private theorem s3_0_1 : pointI (spokeNode 3 0) 1 = intv (-59862/100000 : ℚ) (-59859/100000) := rfl
private theorem n3_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 0 = intv (-1729437/1000000000 : ℚ) (-1660523/1000000000) := rfl
private theorem n3_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 1 = intv (2538604/1000000000 : ℚ) (2623068/1000000000) := rfl
private theorem n3_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 2 = intv (-382953/1000000000 : ℚ) (-312222/1000000000) := rfl
private theorem n3_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 3 = intv (6407024/1000000000 : ℚ) (6485280/1000000000) := rfl
private theorem s3_1_0 : pointI (spokeNode 3 1) 0 = intv (89251/100000 : ℚ) (89254/100000) := rfl
private theorem s3_1_1 : pointI (spokeNode 3 1) 1 = intv (-1/100000 : ℚ) (2/100000) := rfl
private theorem n3_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 0 = intv (1360779/1000000000 : ℚ) (1360780/1000000000) := rfl
private theorem n3_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 1 = intv (55130/1000000000 : ℚ) (55131/1000000000) := rfl
private theorem n3_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 2 = intv (7067274/1000000000 : ℚ) (7067275/1000000000) := rfl
private theorem n3_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 3 = intv (181172/1000000000 : ℚ) (181173/1000000000) := rfl
private theorem fb3_0_0 : FB 3 0 0 = intv (-490834/1000000000 : ℚ) (-469302/1000000000) := rfl
private theorem fb3_0_1 : FB 3 0 1 = intv (-895796/1000000000 : ℚ) (-880446/1000000000) := rfl
private theorem fb3_1_0 : FB 3 1 0 = intv (788128/1000000000 : ℚ) (814451/1000000000) := rfl
private theorem fb3_1_1 : FB 3 1 1 = intv (537697/1000000000 : ℚ) (556444/1000000000) := rfl
private theorem fb3_2_0 : FB 3 2 0 = intv (114793/1000000000 : ℚ) (137149/1000000000) := rfl
private theorem fb3_2_1 : FB 3 2 1 = intv (-2759814/1000000000 : ℚ) (-2743802/1000000000) := rfl
private theorem fb3_3_0 : FB 3 3 0 = intv (1990495/1000000000 : ℚ) (2015135/1000000000) := rfl
private theorem fb3_3_1 : FB 3 3 1 = intv (1341149/1000000000 : ℚ) (1358769/1000000000) := rfl
private theorem gb3_0 : GB 3 0 = intv (-2029918/1000000000 : ℚ) (-1985118/1000000000) := rfl
private theorem gb3_1 : GB 3 1 = intv (1592012/1000000000 : ℚ) (1646727/1000000000) := rfl
private theorem gb3_2 : GB 3 2 = intv (-5022063/1000000000 : ℚ) (-4975323/1000000000) := rfl
private theorem gb3_3 : GB 3 3 = intv (3989578/1000000000 : ℚ) (4041053/1000000000) := rfl
private theorem p4_0 : pointI (anchorNode 4) 0 = intv (92557/100000 : ℚ) (92560/100000) := rfl
private theorem p4_1 : pointI (anchorNode 4) 1 = intv (37853/100000 : ℚ) (37856/100000) := rfl
private theorem s4_0_0 : pointI (spokeNode 4 0) 0 = intv (89251/100000 : ℚ) (89254/100000) := rfl
private theorem s4_0_1 : pointI (spokeNode 4 0) 1 = intv (-1/100000 : ℚ) (2/100000) := rfl
private theorem n4_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 0 = intv (1932726/1000000000 : ℚ) (2001640/1000000000) := rfl
private theorem n4_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 1 = intv (-773555/1000000000 : ℚ) (-689092/1000000000) := rfl
private theorem n4_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 2 = intv (6796849/1000000000 : ℚ) (6867579/1000000000) := rfl
private theorem n4_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 3 = intv (828337/1000000000 : ℚ) (906593/1000000000) := rfl
private theorem s4_1_0 : pointI (spokeNode 4 1) 0 = intv (61580/100000 : ℚ) (61583/100000) := rfl
private theorem s4_1_1 : pointI (spokeNode 4 1) 1 = intv (59859/100000 : ℚ) (59862/100000) := rfl
private theorem n4_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 0 = intv (2521985/1000000000 : ℚ) (2590899/1000000000) := rfl
private theorem n4_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 1 = intv (6131544/1000000000 : ℚ) (6216008/1000000000) := rfl
private theorem n4_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 2 = intv (-921063/1000000000 : ℚ) (-850332/1000000000) := rfl
private theorem n4_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 3 = intv (2363478/1000000000 : ℚ) (2441734/1000000000) := rfl
private theorem fb4_0_0 : FB 4 0 0 = intv (844997/1000000000 : ℚ) (868895/1000000000) := rfl
private theorem fb4_0_1 : FB 4 0 1 = intv (161325/1000000000 : ℚ) (202849/1000000000) := rfl
private theorem fb4_1_0 : FB 4 1 0 = intv (1873587/1000000000 : ℚ) (1902959/1000000000) := rfl
private theorem fb4_1_1 : FB 4 1 1 = intv (-1660926/1000000000 : ℚ) (-1609951/1000000000) := rfl
private theorem fb4_2_0 : FB 4 2 0 = intv (-60846/1000000000 : ℚ) (-36133/1000000000) := rfl
private theorem fb4_2_1 : FB 4 2 1 = intv (2759773/1000000000 : ℚ) (2802577/1000000000) := rfl
private theorem fb4_3_0 : FB 4 3 0 = intv (759423/1000000000 : ℚ) (786449/1000000000) := rfl
private theorem fb4_3_1 : FB 4 3 1 = intv (-223868/1000000000 : ℚ) (-176827/1000000000) := rfl
private theorem gb4_0 : GB 4 0 = intv (-359223/1000000000 : ℚ) (-264199/1000000000) := rfl
private theorem gb4_1 : GB 4 1 = intv (-4515475/1000000000 : ℚ) (-4398662/1000000000) := rfl
private theorem gb4_2 : GB 4 2 = intv (5136081/1000000000 : ℚ) (5234199/1000000000) := rfl
private theorem gb4_3 : GB 4 3 = intv (-1009861/1000000000 : ℚ) (-902260/1000000000) := rfl
private theorem p5_0 : pointI (anchorNode 5) 0 = intv (40459/100000 : ℚ) (40462/100000) := rfl
private theorem p5_1 : pointI (anchorNode 5) 1 = intv (91447/100000 : ℚ) (91450/100000) := rfl
private theorem s5_0_0 : pointI (spokeNode 5 0) 0 = intv (61580/100000 : ℚ) (61583/100000) := rfl
private theorem s5_0_1 : pointI (spokeNode 5 0) 1 = intv (59859/100000 : ℚ) (59862/100000) := rfl
private theorem n5_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 0 = intv (2089958/1000000000 : ℚ) (2089959/1000000000) := rfl
private theorem n5_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 1 = intv (6436709/1000000000 : ℚ) (6436710/1000000000) := rfl
private theorem n5_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 2 = intv (55130/1000000000 : ℚ) (55131/1000000000) := rfl
private theorem n5_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 3 = intv (1764816/1000000000 : ℚ) (1764817/1000000000) := rfl
private theorem s5_1_0 : pointI (spokeNode 5 1) 0 = intv (9482/100000 : ℚ) (9485/100000) := rfl
private theorem s5_1_1 : pointI (spokeNode 5 1) 1 = intv (69441/100000 : ℚ) (69444/100000) := rfl
private theorem n5_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 0 = intv (-1562869/1000000000 : ℚ) (-1493955/1000000000) := rfl
private theorem n5_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 1 = intv (-2747827/1000000000 : ℚ) (-2663364/1000000000) := rfl
private theorem n5_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 2 = intv (-1105799/1000000000 : ℚ) (-1035069/1000000000) := rfl
private theorem n5_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 3 = intv (-2007494/1000000000 : ℚ) (-1929238/1000000000) := rfl
private theorem fb5_0_0 : FB 5 0 0 = intv (-925660/1000000000 : ℚ) (-904094/1000000000) := rfl
private theorem fb5_0_1 : FB 5 0 1 = intv (316141/1000000000 : ℚ) (331525/1000000000) := rfl
private theorem fb5_1_0 : FB 5 1 0 = intv (-2210968/1000000000 : ℚ) (-2184254/1000000000) := rfl
private theorem fb5_1_1 : FB 5 1 1 = intv (1428265/1000000000 : ℚ) (1447402/1000000000) := rfl
private theorem fb5_2_0 : FB 5 2 0 = intv (-354223/1000000000 : ℚ) (-332244/1000000000) := rfl
private theorem fb5_2_1 : FB 5 2 1 = intv (-225963/1000000000 : ℚ) (-210329/1000000000) := rfl
private theorem fb5_3_0 : FB 5 3 0 = intv (-994722/1000000000 : ℚ) (-970256/1000000000) := rfl
private theorem fb5_3_1 : FB 5 3 1 = intv (115587/1000000000 : ℚ) (133034/1000000000) := rfl
private theorem gb5_0 : GB 5 0 = intv (1909348/1000000000 : ℚ) (1961316/1000000000) := rfl
private theorem gb5_1 : GB 5 1 = intv (5150592/1000000000 : ℚ) (5215157/1000000000) := rfl
private theorem gb5_2 : GB 5 2 = intv (424796/1000000000 : ℚ) (477680/1000000000) := rfl
private theorem gb5_3 : GB 5 3 = intv (1868070/1000000000 : ℚ) (1927003/1000000000) := rfl
private theorem p6_0 : pointI (anchorNode 6) 0 = intv (-14460/100000 : ℚ) (-14457/100000) := rfl
private theorem p6_1 : pointI (anchorNode 6) 1 = intv (98948/100000 : ℚ) (98951/100000) := rfl
private theorem s6_0_0 : pointI (spokeNode 6 0) 0 = intv (9482/100000 : ℚ) (9485/100000) := rfl
private theorem s6_0_1 : pointI (spokeNode 6 0) 1 = intv (69441/100000 : ℚ) (69444/100000) := rfl
private theorem n6_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 0 = intv (-681193/1000000000 : ℚ) (-612279/1000000000) := rfl
private theorem n6_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 1 = intv (549206/1000000000 : ℚ) (633669/1000000000) := rfl
private theorem n6_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 2 = intv (-354865/1000000000 : ℚ) (-284135/1000000000) := rfl
private theorem n6_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 3 = intv (2116636/1000000000 : ℚ) (2194892/1000000000) := rfl
private theorem s6_1_0 : pointI (spokeNode 6 1) 0 = intv (-35580/100000 : ℚ) (-35577/100000) := rfl
private theorem s6_1_1 : pointI (spokeNode 6 1) 1 = intv (67360/100000 : ℚ) (67363/100000) := rfl
private theorem n6_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 0 = intv (206549/1000000000 : ℚ) (275463/1000000000) := rfl
private theorem n6_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 1 = intv (-1601352/1000000000 : ℚ) (-1516889/1000000000) := rfl
private theorem n6_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 2 = intv (-1878986/1000000000 : ℚ) (-1808256/1000000000) := rfl
private theorem n6_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 3 = intv (-2729267/1000000000 : ℚ) (-2651011/1000000000) := rfl
private theorem fb6_0_0 : FB 6 0 0 = intv (190190/1000000000 : ℚ) (221298/1000000000) := rfl
private theorem fb6_0_1 : FB 6 0 1 = intv (-135782/1000000000 : ℚ) (-93625/1000000000) := rfl
private theorem fb6_1_0 : FB 6 1 0 = intv (-489986/1000000000 : ℚ) (-451795/1000000000) := rfl
private theorem fb6_1_1 : FB 6 1 1 = intv (-343846/1000000000 : ℚ) (-292113/1000000000) := rfl
private theorem fb6_2_0 : FB 6 2 0 = intv (-328880/1000000000 : ℚ) (-296876/1000000000) := rfl
private theorem fb6_2_1 : FB 6 2 1 = intv (-698312/1000000000 : ℚ) (-654968/1000000000) := rfl
private theorem fb6_3_0 : FB 6 3 0 = intv (-1102070/1000000000 : ℚ) (-1066515/1000000000) := rfl
private theorem fb6_3_1 : FB 6 3 1 = intv (-237711/1000000000 : ℚ) (-189609/1000000000) := rfl
private theorem gb6_0 : GB 6 0 = intv (-410883/1000000000 : ℚ) (-337110/1000000000) := rfl
private theorem gb6_1 : GB 6 1 = intv (978545/1000000000 : ℚ) (1069133/1000000000) := rfl
private theorem gb6_2 : GB 6 2 = intv (776883/1000000000 : ℚ) (852812/1000000000) := rfl
private theorem gb6_3 : GB 6 3 = intv (2165414/1000000000 : ℚ) (2249765/1000000000) := rfl
private theorem p7_0 : pointI (anchorNode 7) 0 = intv (-73577/100000 : ℚ) (-73574/100000) := rfl
private theorem p7_1 : pointI (anchorNode 7) 1 = intv (67723/100000 : ℚ) (67726/100000) := rfl
private theorem s7_0_0 : pointI (spokeNode 7 0) 0 = intv (-35580/100000 : ℚ) (-35577/100000) := rfl
private theorem s7_0_1 : pointI (spokeNode 7 0) 1 = intv (67360/100000 : ℚ) (67363/100000) := rfl
private theorem n7_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 0 = intv (264387/1000000000 : ℚ) (333301/1000000000) := rfl
private theorem n7_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 1 = intv (-1975519/1000000000 : ℚ) (-1891056/1000000000) := rfl
private theorem n7_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 2 = intv (-2321429/1000000000 : ℚ) (-2250699/1000000000) := rfl
private theorem n7_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 3 = intv (-3374863/1000000000 : ℚ) (-3296607/1000000000) := rfl
private theorem s7_1_0 : pointI (spokeNode 7 1) 0 = intv (-76472/100000 : ℚ) (-76469/100000) := rfl
private theorem s7_1_1 : pointI (spokeNode 7 1) 1 = intv (29835/100000 : ℚ) (29838/100000) := rfl
private theorem n7_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 0 = intv (219510/1000000000 : ℚ) (288424/1000000000) := rfl
private theorem n7_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 1 = intv (-380506/1000000000 : ℚ) (-296043/1000000000) := rfl
private theorem n7_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 2 = intv (1180384/1000000000 : ℚ) (1251115/1000000000) := rfl
private theorem n7_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 3 = intv (-234479/1000000000 : ℚ) (-156223/1000000000) := rfl
private theorem fb7_0_0 : FB 7 0 0 = intv (-120307/1000000000 : ℚ) (-92092/1000000000) := rfl
private theorem fb7_0_1 : FB 7 0 1 = intv (84113/1000000000 : ℚ) (110507/1000000000) := rfl
private theorem fb7_1_0 : FB 7 1 0 = intv (707460/1000000000 : ℚ) (742136/1000000000) := rfl
private theorem fb7_1_1 : FB 7 1 1 = intv (-151408/1000000000 : ℚ) (-118963/1000000000) := rfl
private theorem fb7_2_0 : FB 7 2 0 = intv (889267/1000000000 : ℚ) (918401/1000000000) := rfl
private theorem fb7_2_1 : FB 7 2 1 = intv (438692/1000000000 : ℚ) (465958/1000000000) := rfl
private theorem fb7_3_0 : FB 7 3 0 = intv (1245717/1000000000 : ℚ) (1277930/1000000000) := rfl
private theorem fb7_3_1 : FB 7 3 1 = intv (-101199/1000000000 : ℚ) (-71052/1000000000) := rfl
private theorem gb7_0 : GB 7 0 = intv (-37881/1000000000 : ℚ) (39188/1000000000) := rfl
private theorem gb7_1 : GB 7 1 = intv (-830187/1000000000 : ℚ) (-735423/1000000000) := rfl
private theorem gb7_2 : GB 7 2 = intv (-1929669/1000000000 : ℚ) (-1850003/1000000000) := rfl
private theorem gb7_3 : GB 7 3 = intv (-1626431/1000000000 : ℚ) (-1538355/1000000000) := rfl
private theorem p8_0 : pointI (anchorNode 8) 0 = intv (-100001/100000 : ℚ) (-99998/100000) := rfl
private theorem p8_1 : pointI (anchorNode 8) 1 = intv (-1/100000 : ℚ) (2/100000) := rfl
private theorem s8_0_0 : pointI (spokeNode 8 0) 0 = intv (-76472/100000 : ℚ) (-76469/100000) := rfl
private theorem s8_0_1 : pointI (spokeNode 8 0) 1 = intv (29835/100000 : ℚ) (29838/100000) := rfl
private theorem n8_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 0 = intv (142417/1000000000 : ℚ) (211332/1000000000) := rfl
private theorem n8_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 1 = intv (-277822/1000000000 : ℚ) (-193359/1000000000) := rfl
private theorem n8_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 2 = intv (811341/1000000000 : ℚ) (882071/1000000000) := rfl
private theorem n8_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 3 = intv (-175180/1000000000 : ℚ) (-96924/1000000000) := rfl
private theorem s8_1_0 : pointI (spokeNode 8 1) 0 = intv (-76472/100000 : ℚ) (-76469/100000) := rfl
private theorem s8_1_1 : pointI (spokeNode 8 1) 1 = intv (-29838/100000 : ℚ) (-29835/100000) := rfl
private theorem n8_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 0 = intv (142431/1000000000 : ℚ) (211345/1000000000) := rfl
private theorem n8_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 1 = intv (-277840/1000000000 : ℚ) (-193377/1000000000) := rfl
private theorem n8_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 2 = intv (811405/1000000000 : ℚ) (882135/1000000000) := rfl
private theorem n8_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 3 = intv (-175190/1000000000 : ℚ) (-96934/1000000000) := rfl
private theorem fb8_0_0 : FB 8 0 0 = intv (-99465/1000000000 : ℚ) (-67013/1000000000) := rfl
private theorem fb8_0_1 : FB 8 0 1 = intv (-20567/1000000000 : ℚ) (20579/1000000000) := rfl
private theorem fb8_1_0 : FB 8 1 0 = intv (90983/1000000000 : ℚ) (130759/1000000000) := rfl
private theorem fb8_1_1 : FB 8 1 1 = intv (-25223/1000000000 : ℚ) (25208/1000000000) := rfl
private theorem fb8_2_0 : FB 8 2 0 = intv (-415153/1000000000 : ℚ) (-381767/1000000000) := rfl
private theorem fb8_2_1 : FB 8 2 1 = intv (-21127/1000000000 : ℚ) (21182/1000000000) := rfl
private theorem fb8_3_0 : FB 8 3 0 = intv (45607/1000000000 : ℚ) (82450/1000000000) := rfl
private theorem fb8_3_1 : FB 8 3 1 = intv (-23362/1000000000 : ℚ) (23353/1000000000) := rfl
private theorem gb8_0 : GB 8 0 = intv (-41161/1000000000 : ℚ) (41139/1000000000) := rfl
private theorem gb8_1 : GB 8 1 = intv (-50422/1000000000 : ℚ) (50450/1000000000) := rfl
private theorem gb8_2 : GB 8 2 = intv (-42373/1000000000 : ℚ) (42272/1000000000) := rfl
private theorem gb8_3 : GB 8 3 = intv (-46710/1000000000 : ℚ) (46727/1000000000) := rfl

private theorem fcert0_0_0 : Contains (FB 0 0 0) (fluxBox 0 0 0) := by
  simp only [fb0_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_0,n0_1_0,p0_0,s0_0_0,s0_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert0_0_1 : Contains (FB 0 0 1) (fluxBox 0 0 1) := by
  simp only [fb0_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_0,n0_1_0,p0_1,s0_0_1,s0_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert0_1_0 : Contains (FB 0 1 0) (fluxBox 0 1 0) := by
  simp only [fb0_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_1,n0_1_1,p0_0,s0_0_0,s0_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert0_1_1 : Contains (FB 0 1 1) (fluxBox 0 1 1) := by
  simp only [fb0_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_1,n0_1_1,p0_1,s0_0_1,s0_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert0_2_0 : Contains (FB 0 2 0) (fluxBox 0 2 0) := by
  simp only [fb0_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_2,n0_1_2,p0_0,s0_0_0,s0_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert0_2_1 : Contains (FB 0 2 1) (fluxBox 0 2 1) := by
  simp only [fb0_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_2,n0_1_2,p0_1,s0_0_1,s0_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert0_3_0 : Contains (FB 0 3 0) (fluxBox 0 3 0) := by
  simp only [fb0_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_3,n0_1_3,p0_0,s0_0_0,s0_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert0_3_1 : Contains (FB 0 3 1) (fluxBox 0 3 1) := by
  simp only [fb0_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n0_0_3,n0_1_3,p0_1,s0_0_1,s0_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_0_0 : Contains (FB 1 0 0) (fluxBox 1 0 0) := by
  simp only [fb1_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_0,n1_1_0,p1_0,s1_0_0,s1_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_0_1 : Contains (FB 1 0 1) (fluxBox 1 0 1) := by
  simp only [fb1_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_0,n1_1_0,p1_1,s1_0_1,s1_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_1_0 : Contains (FB 1 1 0) (fluxBox 1 1 0) := by
  simp only [fb1_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_1,n1_1_1,p1_0,s1_0_0,s1_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_1_1 : Contains (FB 1 1 1) (fluxBox 1 1 1) := by
  simp only [fb1_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_1,n1_1_1,p1_1,s1_0_1,s1_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_2_0 : Contains (FB 1 2 0) (fluxBox 1 2 0) := by
  simp only [fb1_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_2,n1_1_2,p1_0,s1_0_0,s1_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_2_1 : Contains (FB 1 2 1) (fluxBox 1 2 1) := by
  simp only [fb1_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_2,n1_1_2,p1_1,s1_0_1,s1_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_3_0 : Contains (FB 1 3 0) (fluxBox 1 3 0) := by
  simp only [fb1_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_3,n1_1_3,p1_0,s1_0_0,s1_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert1_3_1 : Contains (FB 1 3 1) (fluxBox 1 3 1) := by
  simp only [fb1_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n1_0_3,n1_1_3,p1_1,s1_0_1,s1_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_0_0 : Contains (FB 2 0 0) (fluxBox 2 0 0) := by
  simp only [fb2_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_0,n2_1_0,p2_0,s2_0_0,s2_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_0_1 : Contains (FB 2 0 1) (fluxBox 2 0 1) := by
  simp only [fb2_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_0,n2_1_0,p2_1,s2_0_1,s2_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_1_0 : Contains (FB 2 1 0) (fluxBox 2 1 0) := by
  simp only [fb2_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_1,n2_1_1,p2_0,s2_0_0,s2_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_1_1 : Contains (FB 2 1 1) (fluxBox 2 1 1) := by
  simp only [fb2_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_1,n2_1_1,p2_1,s2_0_1,s2_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_2_0 : Contains (FB 2 2 0) (fluxBox 2 2 0) := by
  simp only [fb2_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_2,n2_1_2,p2_0,s2_0_0,s2_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_2_1 : Contains (FB 2 2 1) (fluxBox 2 2 1) := by
  simp only [fb2_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_2,n2_1_2,p2_1,s2_0_1,s2_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_3_0 : Contains (FB 2 3 0) (fluxBox 2 3 0) := by
  simp only [fb2_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_3,n2_1_3,p2_0,s2_0_0,s2_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert2_3_1 : Contains (FB 2 3 1) (fluxBox 2 3 1) := by
  simp only [fb2_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n2_0_3,n2_1_3,p2_1,s2_0_1,s2_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_0_0 : Contains (FB 3 0 0) (fluxBox 3 0 0) := by
  simp only [fb3_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_0,n3_1_0,p3_0,s3_0_0,s3_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_0_1 : Contains (FB 3 0 1) (fluxBox 3 0 1) := by
  simp only [fb3_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_0,n3_1_0,p3_1,s3_0_1,s3_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_1_0 : Contains (FB 3 1 0) (fluxBox 3 1 0) := by
  simp only [fb3_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_1,n3_1_1,p3_0,s3_0_0,s3_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_1_1 : Contains (FB 3 1 1) (fluxBox 3 1 1) := by
  simp only [fb3_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_1,n3_1_1,p3_1,s3_0_1,s3_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_2_0 : Contains (FB 3 2 0) (fluxBox 3 2 0) := by
  simp only [fb3_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_2,n3_1_2,p3_0,s3_0_0,s3_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_2_1 : Contains (FB 3 2 1) (fluxBox 3 2 1) := by
  simp only [fb3_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_2,n3_1_2,p3_1,s3_0_1,s3_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_3_0 : Contains (FB 3 3 0) (fluxBox 3 3 0) := by
  simp only [fb3_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_3,n3_1_3,p3_0,s3_0_0,s3_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert3_3_1 : Contains (FB 3 3 1) (fluxBox 3 3 1) := by
  simp only [fb3_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n3_0_3,n3_1_3,p3_1,s3_0_1,s3_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_0_0 : Contains (FB 4 0 0) (fluxBox 4 0 0) := by
  simp only [fb4_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_0,n4_1_0,p4_0,s4_0_0,s4_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_0_1 : Contains (FB 4 0 1) (fluxBox 4 0 1) := by
  simp only [fb4_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_0,n4_1_0,p4_1,s4_0_1,s4_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_1_0 : Contains (FB 4 1 0) (fluxBox 4 1 0) := by
  simp only [fb4_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_1,n4_1_1,p4_0,s4_0_0,s4_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_1_1 : Contains (FB 4 1 1) (fluxBox 4 1 1) := by
  simp only [fb4_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_1,n4_1_1,p4_1,s4_0_1,s4_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_2_0 : Contains (FB 4 2 0) (fluxBox 4 2 0) := by
  simp only [fb4_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_2,n4_1_2,p4_0,s4_0_0,s4_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_2_1 : Contains (FB 4 2 1) (fluxBox 4 2 1) := by
  simp only [fb4_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_2,n4_1_2,p4_1,s4_0_1,s4_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_3_0 : Contains (FB 4 3 0) (fluxBox 4 3 0) := by
  simp only [fb4_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_3,n4_1_3,p4_0,s4_0_0,s4_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert4_3_1 : Contains (FB 4 3 1) (fluxBox 4 3 1) := by
  simp only [fb4_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n4_0_3,n4_1_3,p4_1,s4_0_1,s4_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_0_0 : Contains (FB 5 0 0) (fluxBox 5 0 0) := by
  simp only [fb5_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_0,n5_1_0,p5_0,s5_0_0,s5_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_0_1 : Contains (FB 5 0 1) (fluxBox 5 0 1) := by
  simp only [fb5_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_0,n5_1_0,p5_1,s5_0_1,s5_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_1_0 : Contains (FB 5 1 0) (fluxBox 5 1 0) := by
  simp only [fb5_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_1,n5_1_1,p5_0,s5_0_0,s5_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_1_1 : Contains (FB 5 1 1) (fluxBox 5 1 1) := by
  simp only [fb5_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_1,n5_1_1,p5_1,s5_0_1,s5_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_2_0 : Contains (FB 5 2 0) (fluxBox 5 2 0) := by
  simp only [fb5_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_2,n5_1_2,p5_0,s5_0_0,s5_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_2_1 : Contains (FB 5 2 1) (fluxBox 5 2 1) := by
  simp only [fb5_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_2,n5_1_2,p5_1,s5_0_1,s5_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_3_0 : Contains (FB 5 3 0) (fluxBox 5 3 0) := by
  simp only [fb5_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_3,n5_1_3,p5_0,s5_0_0,s5_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert5_3_1 : Contains (FB 5 3 1) (fluxBox 5 3 1) := by
  simp only [fb5_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n5_0_3,n5_1_3,p5_1,s5_0_1,s5_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_0_0 : Contains (FB 6 0 0) (fluxBox 6 0 0) := by
  simp only [fb6_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_0,n6_1_0,p6_0,s6_0_0,s6_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_0_1 : Contains (FB 6 0 1) (fluxBox 6 0 1) := by
  simp only [fb6_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_0,n6_1_0,p6_1,s6_0_1,s6_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_1_0 : Contains (FB 6 1 0) (fluxBox 6 1 0) := by
  simp only [fb6_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_1,n6_1_1,p6_0,s6_0_0,s6_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_1_1 : Contains (FB 6 1 1) (fluxBox 6 1 1) := by
  simp only [fb6_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_1,n6_1_1,p6_1,s6_0_1,s6_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_2_0 : Contains (FB 6 2 0) (fluxBox 6 2 0) := by
  simp only [fb6_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_2,n6_1_2,p6_0,s6_0_0,s6_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_2_1 : Contains (FB 6 2 1) (fluxBox 6 2 1) := by
  simp only [fb6_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_2,n6_1_2,p6_1,s6_0_1,s6_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_3_0 : Contains (FB 6 3 0) (fluxBox 6 3 0) := by
  simp only [fb6_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_3,n6_1_3,p6_0,s6_0_0,s6_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert6_3_1 : Contains (FB 6 3 1) (fluxBox 6 3 1) := by
  simp only [fb6_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n6_0_3,n6_1_3,p6_1,s6_0_1,s6_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_0_0 : Contains (FB 7 0 0) (fluxBox 7 0 0) := by
  simp only [fb7_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_0,n7_1_0,p7_0,s7_0_0,s7_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_0_1 : Contains (FB 7 0 1) (fluxBox 7 0 1) := by
  simp only [fb7_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_0,n7_1_0,p7_1,s7_0_1,s7_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_1_0 : Contains (FB 7 1 0) (fluxBox 7 1 0) := by
  simp only [fb7_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_1,n7_1_1,p7_0,s7_0_0,s7_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_1_1 : Contains (FB 7 1 1) (fluxBox 7 1 1) := by
  simp only [fb7_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_1,n7_1_1,p7_1,s7_0_1,s7_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_2_0 : Contains (FB 7 2 0) (fluxBox 7 2 0) := by
  simp only [fb7_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_2,n7_1_2,p7_0,s7_0_0,s7_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_2_1 : Contains (FB 7 2 1) (fluxBox 7 2 1) := by
  simp only [fb7_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_2,n7_1_2,p7_1,s7_0_1,s7_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_3_0 : Contains (FB 7 3 0) (fluxBox 7 3 0) := by
  simp only [fb7_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_3,n7_1_3,p7_0,s7_0_0,s7_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert7_3_1 : Contains (FB 7 3 1) (fluxBox 7 3 1) := by
  simp only [fb7_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n7_0_3,n7_1_3,p7_1,s7_0_1,s7_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_0_0 : Contains (FB 8 0 0) (fluxBox 8 0 0) := by
  simp only [fb8_0_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_0,n8_1_0,p8_0,s8_0_0,s8_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_0_1 : Contains (FB 8 0 1) (fluxBox 8 0 1) := by
  simp only [fb8_0_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_0,n8_1_0,p8_1,s8_0_1,s8_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_1_0 : Contains (FB 8 1 0) (fluxBox 8 1 0) := by
  simp only [fb8_1_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_1,n8_1_1,p8_0,s8_0_0,s8_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_1_1 : Contains (FB 8 1 1) (fluxBox 8 1 1) := by
  simp only [fb8_1_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_1,n8_1_1,p8_1,s8_0_1,s8_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_2_0 : Contains (FB 8 2 0) (fluxBox 8 2 0) := by
  simp only [fb8_2_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_2,n8_1_2,p8_0,s8_0_0,s8_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_2_1 : Contains (FB 8 2 1) (fluxBox 8 2 1) := by
  simp only [fb8_2_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_2,n8_1_2,p8_1,s8_0_1,s8_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_3_0 : Contains (FB 8 3 0) (fluxBox 8 3 0) := by
  simp only [fb8_3_0,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_3,n8_1_3,p8_0,s8_0_0,s8_1_0]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]
private theorem fcert8_3_1 : Contains (FB 8 3 1) (fluxBox 8 3 1) := by
  simp only [fb8_3_1,fluxBox,sumI,Fin.sum_univ_two,chordBox,
    n8_0_3,n8_1_3,p8_1,s8_0_1,s8_1_1]
  norm_num [Contains,RatInterval.sub,RatInterval.mul,intv,ofRat]

theorem FB_contains (k : Fin 9) (a : Fin 4) (c : Fin 2) :
    Contains (FB k a c) (fluxBox k a c) := by
  fin_cases k <;> fin_cases a <;> fin_cases c
  · exact fcert0_0_0
  · exact fcert0_0_1
  · exact fcert0_1_0
  · exact fcert0_1_1
  · exact fcert0_2_0
  · exact fcert0_2_1
  · exact fcert0_3_0
  · exact fcert0_3_1
  · exact fcert1_0_0
  · exact fcert1_0_1
  · exact fcert1_1_0
  · exact fcert1_1_1
  · exact fcert1_2_0
  · exact fcert1_2_1
  · exact fcert1_3_0
  · exact fcert1_3_1
  · exact fcert2_0_0
  · exact fcert2_0_1
  · exact fcert2_1_0
  · exact fcert2_1_1
  · exact fcert2_2_0
  · exact fcert2_2_1
  · exact fcert2_3_0
  · exact fcert2_3_1
  · exact fcert3_0_0
  · exact fcert3_0_1
  · exact fcert3_1_0
  · exact fcert3_1_1
  · exact fcert3_2_0
  · exact fcert3_2_1
  · exact fcert3_3_0
  · exact fcert3_3_1
  · exact fcert4_0_0
  · exact fcert4_0_1
  · exact fcert4_1_0
  · exact fcert4_1_1
  · exact fcert4_2_0
  · exact fcert4_2_1
  · exact fcert4_3_0
  · exact fcert4_3_1
  · exact fcert5_0_0
  · exact fcert5_0_1
  · exact fcert5_1_0
  · exact fcert5_1_1
  · exact fcert5_2_0
  · exact fcert5_2_1
  · exact fcert5_3_0
  · exact fcert5_3_1
  · exact fcert6_0_0
  · exact fcert6_0_1
  · exact fcert6_1_0
  · exact fcert6_1_1
  · exact fcert6_2_0
  · exact fcert6_2_1
  · exact fcert6_3_0
  · exact fcert6_3_1
  · exact fcert7_0_0
  · exact fcert7_0_1
  · exact fcert7_1_0
  · exact fcert7_1_1
  · exact fcert7_2_0
  · exact fcert7_2_1
  · exact fcert7_3_0
  · exact fcert7_3_1
  · exact fcert8_0_0
  · exact fcert8_0_1
  · exact fcert8_1_0
  · exact fcert8_1_1
  · exact fcert8_2_0
  · exact fcert8_2_1
  · exact fcert8_3_0
  · exact fcert8_3_1

theorem FB_mem (k : Fin 9) (a : Fin 4) (c : Fin 2) :
    (FB k a c).Mem ((F a (ResumeLocalIncidence.siteMap k)).ofLp c) :=
  mem_of_contains (FB_contains k a c) (fluxBox_mem k a c)

def gInput (k : Fin 9) (a : Fin 4) : RatInterval :=
  mul (ofRat 2) (add
    (mul (FB k a 0) (neg (pointI (anchorNode k) 1)))
    (mul (FB k a 1) (pointI (anchorNode k) 0)))

theorem gInput_mem (k : Fin 9) (a : Fin 4) :
    (gInput k a).Mem (G (ResumeLocalIncidence.siteMap k) a) := by
  rw [G_flux,PinTangentGeometry.inner_coords,tangent_source_zero,tangent_source_one]
  have hU0 := pointI_mem (anchorNode k) 0
  have hU1 := pointI_mem (anchorNode k) 1
  dsimp only [anchorNode] at hU0 hU1
  rw [SourceN2.srcX2_anchor] at hU0 hU1
  exact mul_mem (ofRat_mem 2) (add_mem
    (mul_mem (FB_mem k a 0) (neg_mem hU1))
    (mul_mem (FB_mem k a 1) hU0))

private theorem gcert0_0 : Contains (GB 0 0) (gInput 0 0) := by
  simp only [gb0_0,gInput,fb0_0_0,fb0_0_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert0_1 : Contains (GB 0 1) (gInput 0 1) := by
  simp only [gb0_1,gInput,fb0_1_0,fb0_1_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert0_2 : Contains (GB 0 2) (gInput 0 2) := by
  simp only [gb0_2,gInput,fb0_2_0,fb0_2_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert0_3 : Contains (GB 0 3) (gInput 0 3) := by
  simp only [gb0_3,gInput,fb0_3_0,fb0_3_1,p0_0,p0_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert1_0 : Contains (GB 1 0) (gInput 1 0) := by
  simp only [gb1_0,gInput,fb1_0_0,fb1_0_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert1_1 : Contains (GB 1 1) (gInput 1 1) := by
  simp only [gb1_1,gInput,fb1_1_0,fb1_1_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert1_2 : Contains (GB 1 2) (gInput 1 2) := by
  simp only [gb1_2,gInput,fb1_2_0,fb1_2_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert1_3 : Contains (GB 1 3) (gInput 1 3) := by
  simp only [gb1_3,gInput,fb1_3_0,fb1_3_1,p1_0,p1_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert2_0 : Contains (GB 2 0) (gInput 2 0) := by
  simp only [gb2_0,gInput,fb2_0_0,fb2_0_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert2_1 : Contains (GB 2 1) (gInput 2 1) := by
  simp only [gb2_1,gInput,fb2_1_0,fb2_1_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert2_2 : Contains (GB 2 2) (gInput 2 2) := by
  simp only [gb2_2,gInput,fb2_2_0,fb2_2_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert2_3 : Contains (GB 2 3) (gInput 2 3) := by
  simp only [gb2_3,gInput,fb2_3_0,fb2_3_1,p2_0,p2_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert3_0 : Contains (GB 3 0) (gInput 3 0) := by
  simp only [gb3_0,gInput,fb3_0_0,fb3_0_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert3_1 : Contains (GB 3 1) (gInput 3 1) := by
  simp only [gb3_1,gInput,fb3_1_0,fb3_1_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert3_2 : Contains (GB 3 2) (gInput 3 2) := by
  simp only [gb3_2,gInput,fb3_2_0,fb3_2_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert3_3 : Contains (GB 3 3) (gInput 3 3) := by
  simp only [gb3_3,gInput,fb3_3_0,fb3_3_1,p3_0,p3_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert4_0 : Contains (GB 4 0) (gInput 4 0) := by
  simp only [gb4_0,gInput,fb4_0_0,fb4_0_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert4_1 : Contains (GB 4 1) (gInput 4 1) := by
  simp only [gb4_1,gInput,fb4_1_0,fb4_1_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert4_2 : Contains (GB 4 2) (gInput 4 2) := by
  simp only [gb4_2,gInput,fb4_2_0,fb4_2_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert4_3 : Contains (GB 4 3) (gInput 4 3) := by
  simp only [gb4_3,gInput,fb4_3_0,fb4_3_1,p4_0,p4_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert5_0 : Contains (GB 5 0) (gInput 5 0) := by
  simp only [gb5_0,gInput,fb5_0_0,fb5_0_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert5_1 : Contains (GB 5 1) (gInput 5 1) := by
  simp only [gb5_1,gInput,fb5_1_0,fb5_1_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert5_2 : Contains (GB 5 2) (gInput 5 2) := by
  simp only [gb5_2,gInput,fb5_2_0,fb5_2_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert5_3 : Contains (GB 5 3) (gInput 5 3) := by
  simp only [gb5_3,gInput,fb5_3_0,fb5_3_1,p5_0,p5_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert6_0 : Contains (GB 6 0) (gInput 6 0) := by
  simp only [gb6_0,gInput,fb6_0_0,fb6_0_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert6_1 : Contains (GB 6 1) (gInput 6 1) := by
  simp only [gb6_1,gInput,fb6_1_0,fb6_1_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert6_2 : Contains (GB 6 2) (gInput 6 2) := by
  simp only [gb6_2,gInput,fb6_2_0,fb6_2_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert6_3 : Contains (GB 6 3) (gInput 6 3) := by
  simp only [gb6_3,gInput,fb6_3_0,fb6_3_1,p6_0,p6_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert7_0 : Contains (GB 7 0) (gInput 7 0) := by
  simp only [gb7_0,gInput,fb7_0_0,fb7_0_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert7_1 : Contains (GB 7 1) (gInput 7 1) := by
  simp only [gb7_1,gInput,fb7_1_0,fb7_1_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert7_2 : Contains (GB 7 2) (gInput 7 2) := by
  simp only [gb7_2,gInput,fb7_2_0,fb7_2_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert7_3 : Contains (GB 7 3) (gInput 7 3) := by
  simp only [gb7_3,gInput,fb7_3_0,fb7_3_1,p7_0,p7_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert8_0 : Contains (GB 8 0) (gInput 8 0) := by
  simp only [gb8_0,gInput,fb8_0_0,fb8_0_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert8_1 : Contains (GB 8 1) (gInput 8 1) := by
  simp only [gb8_1,gInput,fb8_1_0,fb8_1_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert8_2 : Contains (GB 8 2) (gInput 8 2) := by
  simp only [gb8_2,gInput,fb8_2_0,fb8_2_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]
private theorem gcert8_3 : Contains (GB 8 3) (gInput 8 3) := by
  simp only [gb8_3,gInput,fb8_3_0,fb8_3_1,p8_0,p8_1]
  norm_num [Contains,RatInterval.add,RatInterval.mul,RatInterval.neg,intv,ofRat]

theorem GB_contains (k : Fin 9) (a : Fin 4) : Contains (GB k a) (gInput k a) := by
  fin_cases k <;> fin_cases a
  · exact gcert0_0
  · exact gcert0_1
  · exact gcert0_2
  · exact gcert0_3
  · exact gcert1_0
  · exact gcert1_1
  · exact gcert1_2
  · exact gcert1_3
  · exact gcert2_0
  · exact gcert2_1
  · exact gcert2_2
  · exact gcert2_3
  · exact gcert3_0
  · exact gcert3_1
  · exact gcert3_2
  · exact gcert3_3
  · exact gcert4_0
  · exact gcert4_1
  · exact gcert4_2
  · exact gcert4_3
  · exact gcert5_0
  · exact gcert5_1
  · exact gcert5_2
  · exact gcert5_3
  · exact gcert6_0
  · exact gcert6_1
  · exact gcert6_2
  · exact gcert6_3
  · exact gcert7_0
  · exact gcert7_1
  · exact gcert7_2
  · exact gcert7_3
  · exact gcert8_0
  · exact gcert8_1
  · exact gcert8_2
  · exact gcert8_3

theorem GB_mem (k : Fin 9) (a : Fin 4) :
    (GB k a).Mem (G (ResumeLocalIncidence.siteMap k) a) :=
  mem_of_contains (GB_contains k a) (gInput_mem k a)

def fmag (k : Fin 9) (a : Fin 4) (c : Fin 2) : ℤ :=
  max (-FL k a c) (FH k a c)
def gmag (k : Fin 9) (a : Fin 4) : ℤ := max (-GLo k a) (GHi k a)

theorem flux_readout :
    (∑ k : Fin 9, ∑ a : Fin 4, ∑ c : Fin 2, (fmag k a c)^2) ≤
      (429 : ℤ)^2*400000000 := by decide

theorem G_readout :
    (∑ k : Fin 8, ∑ a : Fin 4, (gmag (Fin.castSucc k) a)^2) ≤
      (15363 : ℤ)^2*1000000 := by decide

end
end N11Formalization.SourceRelativeFluxPacket
#check @N11Formalization.SourceRelativeFluxPacket.FB_mem
#check @N11Formalization.SourceRelativeFluxPacket.GB_mem
#print axioms N11Formalization.SourceRelativeFluxPacket.flux_readout
#print axioms N11Formalization.SourceRelativeFluxPacket.G_readout
