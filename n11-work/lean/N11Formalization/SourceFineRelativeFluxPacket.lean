import N11Formalization.SourceFineRelativeFluxGeometry

/-! Exact rational actual flux/G input readouts at scale10^9.
Fine SAME-source literal shapes and72+36 outwardContains obligations plus integer norm
comparisons must pass Lean. No floating equality or diagnostic premise. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineRelativeFluxPacket
open N11Formalization RatInterval SourceFineRelativeFluxGeometry
open _root_.N11Formalization.SourceRelativeFluxGeometry hiding
  chordBox chordBox_mem fluxBox fluxBox_mem GBox GBox_mem
open SourceActiveMatrixIntervals SourceFineBPointPacket SourceFineRelativeNIntervals
noncomputable section
set_option maxRecDepth 10000

def FL : Fin 9 → Fin 4 → Fin 2 → ℤ :=
 ![![![753070,-89254],![1081523,138423],![749805,-453984],![803363,81580]],![![-528417,260896],![-990839,113673],![-207916,617845],![-484246,392771]],![![296516,227442],![-948045,-148999],![-469163,248691],![-2354484,-1449053]],![![-480202,-888216],![801130,546968],![125847,-2751856],![2002676,1349887]],![![856805,181819],![1888103,-1635791],![-48630,2780931],![772772,-200653]],![![-914999,323732],![-2197735,1437710],![-343372,-218249],![-982632,124194]],![![205549,-114966],![-471132,-318306],![-313083,-676911],![-1084522,-213967]],![![-106375,97144],![724574,-135401],![903645,452136],![1261611,-86338]],![![-83442,-254],![110621,-321],![-398673,-246],![63796,-296]]]

def FH : Fin 9 → Fin 4 → Fin 2 → ℤ :=
 ![![![753424,-88923],![1081956,138829],![750168,-453645],![803764,81956]],![![-528027,261424],![-990362,114320],![-207516,618387],![-483804,393371]],![![296785,227633],![-947716,-148765],![-468888,248887],![-2354179,-1448836]],![![-479933,-888025],![801458,547201],![126124,-2751660],![2002981,1350105]],![![857102,182336],![1888466,-1635157],![-48324,2781463],![773109,-200066]],![![-914731,323923],![-2197406,1437945],![-343097,-218053],![-982327,124411]],![![205938,-114438],![-470655,-317659],![-312683,-676369],![-1084079,-213367]],![![-106021,97475],![725007,-134996],![904008,452476],![1262012,-85962]],![![-83035,262],![111119,311],![-398256,284],![64258,289]]]

def GLo : Fin 9 → Fin 4 → ℤ :=
 ![![1150882,1260632,1683151,967554],![-1121325,-1993914,-590281,-1072067],![726371,-1854528,-656845,-5478903],![-2007791,1619053,-4998870,4015064],![-312323,-4457854,5184554,-956752],![1934994,5182431,450906,1897156],![-374457,1023276,814379,2207075],![170,-783374,-1890300,-1582900],![-525,-623,-569,-579]]

def GHi : Fin 9 → Fin 4 → ℤ :=
 ![![1151850,1261817,1684143,968652],![-1120400,-1992782,-589332,-1071017],![727019,-1853736,-656182,-5478169],![-2007233,1619734,-4998297,4015699],![-311140,-4456405,5185772,-955410],![1935639,5183224,451569,1897890],![-373533,1024408,815329,2208126],![1137,-782190,-1889307,-1581802],![509,643,493,593]]


def FB (k : Fin 9) (a : Fin 4) (c : Fin 2) : RatInterval :=
  intv ((FL k a c : ℚ)/1000000000) ((FH k a c : ℚ)/1000000000)
def GB (k : Fin 9) (a : Fin 4) : RatInterval :=
  intv ((GLo k a : ℚ)/1000000000) ((GHi k a : ℚ)/1000000000)

private theorem p0_0 : pointI (anchorNode 0) 0 = intv (-73575385/100000000 : ℚ) (-73575382/100000000) := rfl
private theorem p0_1 : pointI (anchorNode 0) 1 = intv (-67724908/100000000 : ℚ) (-67724905/100000000) := rfl
private theorem s0_0_0 : pointI (spokeNode 0 0) 0 = intv (-76470619/100000000 : ℚ) (-76470616/100000000) := rfl
private theorem s0_0_1 : pointI (spokeNode 0 0) 1 = intv (-29836983/100000000 : ℚ) (-29836979/100000000) := rfl
private theorem n0_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 0 = intv (253555/1000000000 : ℚ) (254418/1000000000) := rfl
private theorem n0_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 1 = intv (-338829/1000000000 : ℚ) (-337772/1000000000) := rfl
private theorem n0_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 2 = intv (1215402/1000000000 : ℚ) (1216287/1000000000) := rfl
private theorem n0_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (0,0))) 3 = intv (-195856/1000000000 : ℚ) (-194877/1000000000) := rfl
private theorem s0_1_0 : pointI (spokeNode 0 1) 0 = intv (-35578741/100000000 : ℚ) (-35578738/100000000) := rfl
private theorem s0_1_1 : pointI (spokeNode 0 1) 1 = intv (-67361113/100000000 : ℚ) (-67361110/100000000) := rfl
private theorem n0_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 0 = intv (-1963482/1000000000 : ℚ) (-1962620/1000000000) := rfl
private theorem n0_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 1 = intv (-2873240/1000000000 : ℚ) (-2872184/1000000000) := rfl
private theorem n0_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 2 = intv (-1881621/1000000000 : ℚ) (-1880736/1000000000) := rfl
private theorem n0_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (0,1))) 3 = intv (-2130204/1000000000 : ℚ) (-2129224/1000000000) := rfl
private theorem fb0_0_0 : FB 0 0 0 = intv (753070/1000000000 : ℚ) (753424/1000000000) := rfl
private theorem fb0_0_1 : FB 0 0 1 = intv (-89254/1000000000 : ℚ) (-88923/1000000000) := rfl
private theorem fb0_1_0 : FB 0 1 0 = intv (1081523/1000000000 : ℚ) (1081956/1000000000) := rfl
private theorem fb0_1_1 : FB 0 1 1 = intv (138423/1000000000 : ℚ) (138829/1000000000) := rfl
private theorem fb0_2_0 : FB 0 2 0 = intv (749805/1000000000 : ℚ) (750168/1000000000) := rfl
private theorem fb0_2_1 : FB 0 2 1 = intv (-453984/1000000000 : ℚ) (-453645/1000000000) := rfl
private theorem fb0_3_0 : FB 0 3 0 = intv (803363/1000000000 : ℚ) (803764/1000000000) := rfl
private theorem fb0_3_1 : FB 0 3 1 = intv (81580/1000000000 : ℚ) (81956/1000000000) := rfl
private theorem gb0_0 : GB 0 0 = intv (1150882/1000000000 : ℚ) (1151850/1000000000) := rfl
private theorem gb0_1 : GB 0 1 = intv (1260632/1000000000 : ℚ) (1261817/1000000000) := rfl
private theorem gb0_2 : GB 0 2 = intv (1683151/1000000000 : ℚ) (1684143/1000000000) := rfl
private theorem gb0_3 : GB 0 3 = intv (967554/1000000000 : ℚ) (968652/1000000000) := rfl
private theorem p1_0 : pointI (anchorNode 1) 0 = intv (-14458443/100000000 : ℚ) (-14458439/100000000) := rfl
private theorem p1_1 : pointI (anchorNode 1) 1 = intv (-98949248/100000000 : ℚ) (-98949246/100000000) := rfl
private theorem s1_0_0 : pointI (spokeNode 1 0) 0 = intv (-35578741/100000000 : ℚ) (-35578738/100000000) := rfl
private theorem s1_0_1 : pointI (spokeNode 1 0) 1 = intv (-67361113/100000000 : ℚ) (-67361110/100000000) := rfl
private theorem n1_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 0 = intv (-1583555/1000000000 : ℚ) (-1582692/1000000000) := rfl
private theorem n1_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 1 = intv (-2317258/1000000000 : ℚ) (-2316201/1000000000) := rfl
private theorem n1_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 2 = intv (-1517539/1000000000 : ℚ) (-1516654/1000000000) := rfl
private theorem n1_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (1,0))) 3 = intv (-1718020/1000000000 : ℚ) (-1717041/1000000000) := rfl
private theorem s1_1_0 : pointI (spokeNode 1 1) 0 = intv (9483654/100000000 : ℚ) (9483657/100000000) := rfl
private theorem s1_1_1 : pointI (spokeNode 1 1) 1 = intv (-69442413/100000000 : ℚ) (-69442411/100000000) := rfl
private theorem n1_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 0 = intv (809278/1000000000 : ℚ) (810140/1000000000) := rfl
private theorem n1_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 1 = intv (2093274/1000000000 : ℚ) (2094331/1000000000) := rfl
private theorem n1_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 2 = intv (-471158/1000000000 : ℚ) (-470273/1000000000) := rfl
private theorem n1_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (1,1))) 3 = intv (506054/1000000000 : ℚ) (507033/1000000000) := rfl
private theorem fb1_0_0 : FB 1 0 0 = intv (-528417/1000000000 : ℚ) (-528027/1000000000) := rfl
private theorem fb1_0_1 : FB 1 0 1 = intv (260896/1000000000 : ℚ) (261424/1000000000) := rfl
private theorem fb1_1_0 : FB 1 1 0 = intv (-990839/1000000000 : ℚ) (-990362/1000000000) := rfl
private theorem fb1_1_1 : FB 1 1 1 = intv (113673/1000000000 : ℚ) (114320/1000000000) := rfl
private theorem fb1_2_0 : FB 1 2 0 = intv (-207916/1000000000 : ℚ) (-207516/1000000000) := rfl
private theorem fb1_2_1 : FB 1 2 1 = intv (617845/1000000000 : ℚ) (618387/1000000000) := rfl
private theorem fb1_3_0 : FB 1 3 0 = intv (-484246/1000000000 : ℚ) (-483804/1000000000) := rfl
private theorem fb1_3_1 : FB 1 3 1 = intv (392771/1000000000 : ℚ) (393371/1000000000) := rfl
private theorem gb1_0 : GB 1 0 = intv (-1121325/1000000000 : ℚ) (-1120400/1000000000) := rfl
private theorem gb1_1 : GB 1 1 = intv (-1993914/1000000000 : ℚ) (-1992782/1000000000) := rfl
private theorem gb1_2 : GB 1 2 = intv (-590281/1000000000 : ℚ) (-589332/1000000000) := rfl
private theorem gb1_3 : GB 1 3 = intv (-1072067/1000000000 : ℚ) (-1071017/1000000000) := rfl
private theorem p2_0 : pointI (anchorNode 2) 0 = intv (40460867/100000000 : ℚ) (40460870/100000000) := rfl
private theorem p2_1 : pointI (anchorNode 2) 1 = intv (-91448993/100000000 : ℚ) (-91448991/100000000) := rfl
private theorem s2_0_0 : pointI (spokeNode 2 0) 0 = intv (9483654/100000000 : ℚ) (9483657/100000000) := rfl
private theorem s2_0_1 : pointI (spokeNode 2 0) 1 = intv (-69442413/100000000 : ℚ) (-69442411/100000000) := rfl
private theorem n2_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 0 = intv (315856/1000000000 : ℚ) (316719/1000000000) := rfl
private theorem n2_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 1 = intv (-1857203/1000000000 : ℚ) (-1856146/1000000000) := rfl
private theorem n2_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 2 = intv (-1391017/1000000000 : ℚ) (-1390132/1000000000) := rfl
private theorem n2_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (2,0))) 3 = intv (-3032906/1000000000 : ℚ) (-3031926/1000000000) := rfl
private theorem s2_1_0 : pointI (spokeNode 2 1) 0 = intv (61581165/100000000 : ℚ) (61581169/100000000) := rfl
private theorem s2_1_1 : pointI (spokeNode 2 1) 1 = intv (-59860858/100000000 : ℚ) (-59860855/100000000) := rfl
private theorem n2_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 0 = intv (-940675/1000000000 : ℚ) (-940674/1000000000) := rfl
private theorem n2_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 1 = intv (1764816/1000000000 : ℚ) (1764817/1000000000) := rfl
private theorem n2_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 2 = intv (181172/1000000000 : ℚ) (181173/1000000000) := rfl
private theorem n2_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (2,1))) 3 = intv (6699589/1000000000 : ℚ) (6699590/1000000000) := rfl
private theorem fb2_0_0 : FB 2 0 0 = intv (296516/1000000000 : ℚ) (296785/1000000000) := rfl
private theorem fb2_0_1 : FB 2 0 1 = intv (227442/1000000000 : ℚ) (227633/1000000000) := rfl
private theorem fb2_1_0 : FB 2 1 0 = intv (-948045/1000000000 : ℚ) (-947716/1000000000) := rfl
private theorem fb2_1_1 : FB 2 1 1 = intv (-148999/1000000000 : ℚ) (-148765/1000000000) := rfl
private theorem fb2_2_0 : FB 2 2 0 = intv (-469163/1000000000 : ℚ) (-468888/1000000000) := rfl
private theorem fb2_2_1 : FB 2 2 1 = intv (248691/1000000000 : ℚ) (248887/1000000000) := rfl
private theorem fb2_3_0 : FB 2 3 0 = intv (-2354484/1000000000 : ℚ) (-2354179/1000000000) := rfl
private theorem fb2_3_1 : FB 2 3 1 = intv (-1449053/1000000000 : ℚ) (-1448836/1000000000) := rfl
private theorem gb2_0 : GB 2 0 = intv (726371/1000000000 : ℚ) (727019/1000000000) := rfl
private theorem gb2_1 : GB 2 1 = intv (-1854528/1000000000 : ℚ) (-1853736/1000000000) := rfl
private theorem gb2_2 : GB 2 2 = intv (-656845/1000000000 : ℚ) (-656182/1000000000) := rfl
private theorem gb2_3 : GB 2 3 = intv (-5478903/1000000000 : ℚ) (-5478169/1000000000) := rfl
private theorem p3_0 : pointI (anchorNode 3) 0 = intv (92558379/100000000 : ℚ) (92558381/100000000) := rfl
private theorem p3_1 : pointI (anchorNode 3) 1 = intv (-37854278/100000000 : ℚ) (-37854275/100000000) := rfl
private theorem s3_0_0 : pointI (spokeNode 3 0) 0 = intv (61581165/100000000 : ℚ) (61581169/100000000) := rfl
private theorem s3_0_1 : pointI (spokeNode 3 0) 1 = intv (-59860858/100000000 : ℚ) (-59860855/100000000) := rfl
private theorem n3_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 0 = intv (-1695411/1000000000 : ℚ) (-1694549/1000000000) := rfl
private theorem n3_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 1 = intv (2580308/1000000000 : ℚ) (2581364/1000000000) := rfl
private theorem n3_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 2 = intv (-348030/1000000000 : ℚ) (-347145/1000000000) := rfl
private theorem n3_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (3,0))) 3 = intv (6445662/1000000000 : ℚ) (6446642/1000000000) := rfl
private theorem s3_1_0 : pointI (spokeNode 3 1) 0 = intv (89252163/100000000 : ℚ) (89252183/100000000) := rfl
private theorem s3_1_1 : pointI (spokeNode 3 1) 1 = intv (0/100000000 : ℚ) (0/100000000) := rfl
private theorem n3_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 0 = intv (1360779/1000000000 : ℚ) (1360780/1000000000) := rfl
private theorem n3_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 1 = intv (55130/1000000000 : ℚ) (55131/1000000000) := rfl
private theorem n3_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 2 = intv (7067274/1000000000 : ℚ) (7067275/1000000000) := rfl
private theorem n3_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (3,1))) 3 = intv (181172/1000000000 : ℚ) (181173/1000000000) := rfl
private theorem fb3_0_0 : FB 3 0 0 = intv (-480202/1000000000 : ℚ) (-479933/1000000000) := rfl
private theorem fb3_0_1 : FB 3 0 1 = intv (-888216/1000000000 : ℚ) (-888025/1000000000) := rfl
private theorem fb3_1_0 : FB 3 1 0 = intv (801130/1000000000 : ℚ) (801458/1000000000) := rfl
private theorem fb3_1_1 : FB 3 1 1 = intv (546968/1000000000 : ℚ) (547201/1000000000) := rfl
private theorem fb3_2_0 : FB 3 2 0 = intv (125847/1000000000 : ℚ) (126124/1000000000) := rfl
private theorem fb3_2_1 : FB 3 2 1 = intv (-2751856/1000000000 : ℚ) (-2751660/1000000000) := rfl
private theorem fb3_3_0 : FB 3 3 0 = intv (2002676/1000000000 : ℚ) (2002981/1000000000) := rfl
private theorem fb3_3_1 : FB 3 3 1 = intv (1349887/1000000000 : ℚ) (1350105/1000000000) := rfl
private theorem gb3_0 : GB 3 0 = intv (-2007791/1000000000 : ℚ) (-2007233/1000000000) := rfl
private theorem gb3_1 : GB 3 1 = intv (1619053/1000000000 : ℚ) (1619734/1000000000) := rfl
private theorem gb3_2 : GB 3 2 = intv (-4998870/1000000000 : ℚ) (-4998297/1000000000) := rfl
private theorem gb3_3 : GB 3 3 = intv (4015064/1000000000 : ℚ) (4015699/1000000000) := rfl
private theorem p4_0 : pointI (anchorNode 4) 0 = intv (92558379/100000000 : ℚ) (92558381/100000000) := rfl
private theorem p4_1 : pointI (anchorNode 4) 1 = intv (37854276/100000000 : ℚ) (37854278/100000000) := rfl
private theorem s4_0_0 : pointI (spokeNode 4 0) 0 = intv (89252163/100000000 : ℚ) (89252183/100000000) := rfl
private theorem s4_0_1 : pointI (spokeNode 4 0) 1 = intv (0/100000000 : ℚ) (0/100000000) := rfl
private theorem n4_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 0 = intv (1966752/1000000000 : ℚ) (1967615/1000000000) := rfl
private theorem n4_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 1 = intv (-731852/1000000000 : ℚ) (-730795/1000000000) := rfl
private theorem n4_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 2 = intv (6831771/1000000000 : ℚ) (6832657/1000000000) := rfl
private theorem n4_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (4,0))) 3 = intv (866975/1000000000 : ℚ) (867954/1000000000) := rfl
private theorem s4_1_0 : pointI (spokeNode 4 1) 0 = intv (61581165/100000000 : ℚ) (61581169/100000000) := rfl
private theorem s4_1_1 : pointI (spokeNode 4 1) 1 = intv (59860855/100000000 : ℚ) (59860858/100000000) := rfl
private theorem n4_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 0 = intv (2556011/1000000000 : ℚ) (2556873/1000000000) := rfl
private theorem n4_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 1 = intv (6173248/1000000000 : ℚ) (6174304/1000000000) := rfl
private theorem n4_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 2 = intv (-886140/1000000000 : ℚ) (-885255/1000000000) := rfl
private theorem n4_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (4,1))) 3 = intv (2402117/1000000000 : ℚ) (2403096/1000000000) := rfl
private theorem fb4_0_0 : FB 4 0 0 = intv (856805/1000000000 : ℚ) (857102/1000000000) := rfl
private theorem fb4_0_1 : FB 4 0 1 = intv (181819/1000000000 : ℚ) (182336/1000000000) := rfl
private theorem fb4_1_0 : FB 4 1 0 = intv (1888103/1000000000 : ℚ) (1888466/1000000000) := rfl
private theorem fb4_1_1 : FB 4 1 1 = intv (-1635791/1000000000 : ℚ) (-1635157/1000000000) := rfl
private theorem fb4_2_0 : FB 4 2 0 = intv (-48630/1000000000 : ℚ) (-48324/1000000000) := rfl
private theorem fb4_2_1 : FB 4 2 1 = intv (2780931/1000000000 : ℚ) (2781463/1000000000) := rfl
private theorem fb4_3_0 : FB 4 3 0 = intv (772772/1000000000 : ℚ) (773109/1000000000) := rfl
private theorem fb4_3_1 : FB 4 3 1 = intv (-200653/1000000000 : ℚ) (-200066/1000000000) := rfl
private theorem gb4_0 : GB 4 0 = intv (-312323/1000000000 : ℚ) (-311140/1000000000) := rfl
private theorem gb4_1 : GB 4 1 = intv (-4457854/1000000000 : ℚ) (-4456405/1000000000) := rfl
private theorem gb4_2 : GB 4 2 = intv (5184554/1000000000 : ℚ) (5185772/1000000000) := rfl
private theorem gb4_3 : GB 4 3 = intv (-956752/1000000000 : ℚ) (-955410/1000000000) := rfl
private theorem p5_0 : pointI (anchorNode 5) 0 = intv (40460867/100000000 : ℚ) (40460870/100000000) := rfl
private theorem p5_1 : pointI (anchorNode 5) 1 = intv (91448991/100000000 : ℚ) (91448993/100000000) := rfl
private theorem s5_0_0 : pointI (spokeNode 5 0) 0 = intv (61581165/100000000 : ℚ) (61581169/100000000) := rfl
private theorem s5_0_1 : pointI (spokeNode 5 0) 1 = intv (59860855/100000000 : ℚ) (59860858/100000000) := rfl
private theorem n5_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 0 = intv (2089958/1000000000 : ℚ) (2089959/1000000000) := rfl
private theorem n5_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 1 = intv (6436709/1000000000 : ℚ) (6436710/1000000000) := rfl
private theorem n5_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 2 = intv (55130/1000000000 : ℚ) (55131/1000000000) := rfl
private theorem n5_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (5,0))) 3 = intv (1764816/1000000000 : ℚ) (1764817/1000000000) := rfl
private theorem s5_1_0 : pointI (spokeNode 5 1) 0 = intv (9483654/100000000 : ℚ) (9483657/100000000) := rfl
private theorem s5_1_1 : pointI (spokeNode 5 1) 1 = intv (69442411/100000000 : ℚ) (69442413/100000000) := rfl
private theorem n5_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 0 = intv (-1528843/1000000000 : ℚ) (-1527981/1000000000) := rfl
private theorem n5_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 1 = intv (-2706124/1000000000 : ℚ) (-2705067/1000000000) := rfl
private theorem n5_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 2 = intv (-1070877/1000000000 : ℚ) (-1069992/1000000000) := rfl
private theorem n5_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (5,1))) 3 = intv (-1968855/1000000000 : ℚ) (-1967876/1000000000) := rfl
private theorem fb5_0_0 : FB 5 0 0 = intv (-914999/1000000000 : ℚ) (-914731/1000000000) := rfl
private theorem fb5_0_1 : FB 5 0 1 = intv (323732/1000000000 : ℚ) (323923/1000000000) := rfl
private theorem fb5_1_0 : FB 5 1 0 = intv (-2197735/1000000000 : ℚ) (-2197406/1000000000) := rfl
private theorem fb5_1_1 : FB 5 1 1 = intv (1437710/1000000000 : ℚ) (1437945/1000000000) := rfl
private theorem fb5_2_0 : FB 5 2 0 = intv (-343372/1000000000 : ℚ) (-343097/1000000000) := rfl
private theorem fb5_2_1 : FB 5 2 1 = intv (-218249/1000000000 : ℚ) (-218053/1000000000) := rfl
private theorem fb5_3_0 : FB 5 3 0 = intv (-982632/1000000000 : ℚ) (-982327/1000000000) := rfl
private theorem fb5_3_1 : FB 5 3 1 = intv (124194/1000000000 : ℚ) (124411/1000000000) := rfl
private theorem gb5_0 : GB 5 0 = intv (1934994/1000000000 : ℚ) (1935639/1000000000) := rfl
private theorem gb5_1 : GB 5 1 = intv (5182431/1000000000 : ℚ) (5183224/1000000000) := rfl
private theorem gb5_2 : GB 5 2 = intv (450906/1000000000 : ℚ) (451569/1000000000) := rfl
private theorem gb5_3 : GB 5 3 = intv (1897156/1000000000 : ℚ) (1897890/1000000000) := rfl
private theorem p6_0 : pointI (anchorNode 6) 0 = intv (-14458443/100000000 : ℚ) (-14458439/100000000) := rfl
private theorem p6_1 : pointI (anchorNode 6) 1 = intv (98949246/100000000 : ℚ) (98949248/100000000) := rfl
private theorem s6_0_0 : pointI (spokeNode 6 0) 0 = intv (9483654/100000000 : ℚ) (9483657/100000000) := rfl
private theorem s6_0_1 : pointI (spokeNode 6 0) 1 = intv (69442411/100000000 : ℚ) (69442413/100000000) := rfl
private theorem n6_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 0 = intv (-647167/1000000000 : ℚ) (-646305/1000000000) := rfl
private theorem n6_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 1 = intv (590909/1000000000 : ℚ) (591966/1000000000) := rfl
private theorem n6_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 2 = intv (-319943/1000000000 : ℚ) (-319058/1000000000) := rfl
private theorem n6_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (6,0))) 3 = intv (2155274/1000000000 : ℚ) (2156253/1000000000) := rfl
private theorem s6_1_0 : pointI (spokeNode 6 1) 0 = intv (-35578741/100000000 : ℚ) (-35578738/100000000) := rfl
private theorem s6_1_1 : pointI (spokeNode 6 1) 1 = intv (67361110/100000000 : ℚ) (67361113/100000000) := rfl
private theorem n6_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 0 = intv (240575/1000000000 : ℚ) (241438/1000000000) := rfl
private theorem n6_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 1 = intv (-1559649/1000000000 : ℚ) (-1558592/1000000000) := rfl
private theorem n6_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 2 = intv (-1844063/1000000000 : ℚ) (-1843178/1000000000) := rfl
private theorem n6_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (6,1))) 3 = intv (-2690629/1000000000 : ℚ) (-2689649/1000000000) := rfl
private theorem fb6_0_0 : FB 6 0 0 = intv (205549/1000000000 : ℚ) (205938/1000000000) := rfl
private theorem fb6_0_1 : FB 6 0 1 = intv (-114966/1000000000 : ℚ) (-114438/1000000000) := rfl
private theorem fb6_1_0 : FB 6 1 0 = intv (-471132/1000000000 : ℚ) (-470655/1000000000) := rfl
private theorem fb6_1_1 : FB 6 1 1 = intv (-318306/1000000000 : ℚ) (-317659/1000000000) := rfl
private theorem fb6_2_0 : FB 6 2 0 = intv (-313083/1000000000 : ℚ) (-312683/1000000000) := rfl
private theorem fb6_2_1 : FB 6 2 1 = intv (-676911/1000000000 : ℚ) (-676369/1000000000) := rfl
private theorem fb6_3_0 : FB 6 3 0 = intv (-1084522/1000000000 : ℚ) (-1084079/1000000000) := rfl
private theorem fb6_3_1 : FB 6 3 1 = intv (-213967/1000000000 : ℚ) (-213367/1000000000) := rfl
private theorem gb6_0 : GB 6 0 = intv (-374457/1000000000 : ℚ) (-373533/1000000000) := rfl
private theorem gb6_1 : GB 6 1 = intv (1023276/1000000000 : ℚ) (1024408/1000000000) := rfl
private theorem gb6_2 : GB 6 2 = intv (814379/1000000000 : ℚ) (815329/1000000000) := rfl
private theorem gb6_3 : GB 6 3 = intv (2207075/1000000000 : ℚ) (2208126/1000000000) := rfl
private theorem p7_0 : pointI (anchorNode 7) 0 = intv (-73575385/100000000 : ℚ) (-73575382/100000000) := rfl
private theorem p7_1 : pointI (anchorNode 7) 1 = intv (67724905/100000000 : ℚ) (67724908/100000000) := rfl
private theorem s7_0_0 : pointI (spokeNode 7 0) 0 = intv (-35578741/100000000 : ℚ) (-35578738/100000000) := rfl
private theorem s7_0_1 : pointI (spokeNode 7 0) 1 = intv (67361110/100000000 : ℚ) (67361113/100000000) := rfl
private theorem n7_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 0 = intv (298413/1000000000 : ℚ) (299276/1000000000) := rfl
private theorem n7_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 1 = intv (-1933816/1000000000 : ℚ) (-1932759/1000000000) := rfl
private theorem n7_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 2 = intv (-2286507/1000000000 : ℚ) (-2285622/1000000000) := rfl
private theorem n7_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (7,0))) 3 = intv (-3336224/1000000000 : ℚ) (-3335245/1000000000) := rfl
private theorem s7_1_0 : pointI (spokeNode 7 1) 0 = intv (-76470619/100000000 : ℚ) (-76470616/100000000) := rfl
private theorem s7_1_1 : pointI (spokeNode 7 1) 1 = intv (29836979/100000000 : ℚ) (29836983/100000000) := rfl
private theorem n7_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 0 = intv (253535/1000000000 : ℚ) (254398/1000000000) := rfl
private theorem n7_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 1 = intv (-338803/1000000000 : ℚ) (-337746/1000000000) := rfl
private theorem n7_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 2 = intv (1215307/1000000000 : ℚ) (1216192/1000000000) := rfl
private theorem n7_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (7,1))) 3 = intv (-195841/1000000000 : ℚ) (-194862/1000000000) := rfl
private theorem fb7_0_0 : FB 7 0 0 = intv (-106375/1000000000 : ℚ) (-106021/1000000000) := rfl
private theorem fb7_0_1 : FB 7 0 1 = intv (97144/1000000000 : ℚ) (97475/1000000000) := rfl
private theorem fb7_1_0 : FB 7 1 0 = intv (724574/1000000000 : ℚ) (725007/1000000000) := rfl
private theorem fb7_1_1 : FB 7 1 1 = intv (-135401/1000000000 : ℚ) (-134996/1000000000) := rfl
private theorem fb7_2_0 : FB 7 2 0 = intv (903645/1000000000 : ℚ) (904008/1000000000) := rfl
private theorem fb7_2_1 : FB 7 2 1 = intv (452136/1000000000 : ℚ) (452476/1000000000) := rfl
private theorem fb7_3_0 : FB 7 3 0 = intv (1261611/1000000000 : ℚ) (1262012/1000000000) := rfl
private theorem fb7_3_1 : FB 7 3 1 = intv (-86338/1000000000 : ℚ) (-85962/1000000000) := rfl
private theorem gb7_0 : GB 7 0 = intv (170/1000000000 : ℚ) (1137/1000000000) := rfl
private theorem gb7_1 : GB 7 1 = intv (-783374/1000000000 : ℚ) (-782190/1000000000) := rfl
private theorem gb7_2 : GB 7 2 = intv (-1890300/1000000000 : ℚ) (-1889307/1000000000) := rfl
private theorem gb7_3 : GB 7 3 = intv (-1582900/1000000000 : ℚ) (-1581802/1000000000) := rfl
private theorem p8_0 : pointI (anchorNode 8) 0 = intv (-100000000/100000000 : ℚ) (-99999999/100000000) := rfl
private theorem p8_1 : pointI (anchorNode 8) 1 = intv (-2/100000000 : ℚ) (2/100000000) := rfl
private theorem s8_0_0 : pointI (spokeNode 8 0) 0 = intv (-76470619/100000000 : ℚ) (-76470616/100000000) := rfl
private theorem s8_0_1 : pointI (spokeNode 8 0) 1 = intv (29836979/100000000 : ℚ) (29836983/100000000) := rfl
private theorem n8_0_0 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 0 = intv (176443/1000000000 : ℚ) (177306/1000000000) := rfl
private theorem n8_0_1 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 1 = intv (-236119/1000000000 : ℚ) (-235062/1000000000) := rfl
private theorem n8_0_2 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 2 = intv (846264/1000000000 : ℚ) (847149/1000000000) := rfl
private theorem n8_0_3 : NB (HarmonicSourceTransport.srcFlat (.inl (8,0))) 3 = intv (-136541/1000000000 : ℚ) (-135562/1000000000) := rfl
private theorem s8_1_0 : pointI (spokeNode 8 1) 0 = intv (-76470619/100000000 : ℚ) (-76470616/100000000) := rfl
private theorem s8_1_1 : pointI (spokeNode 8 1) 1 = intv (-29836983/100000000 : ℚ) (-29836979/100000000) := rfl
private theorem n8_1_0 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 0 = intv (176457/1000000000 : ℚ) (177319/1000000000) := rfl
private theorem n8_1_1 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 1 = intv (-236137/1000000000 : ℚ) (-235080/1000000000) := rfl
private theorem n8_1_2 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 2 = intv (846328/1000000000 : ℚ) (847213/1000000000) := rfl
private theorem n8_1_3 : NB (HarmonicSourceTransport.srcFlat (.inl (8,1))) 3 = intv (-136552/1000000000 : ℚ) (-135573/1000000000) := rfl
private theorem fb8_0_0 : FB 8 0 0 = intv (-83442/1000000000 : ℚ) (-83035/1000000000) := rfl
private theorem fb8_0_1 : FB 8 0 1 = intv (-254/1000000000 : ℚ) (262/1000000000) := rfl
private theorem fb8_1_0 : FB 8 1 0 = intv (110621/1000000000 : ℚ) (111119/1000000000) := rfl
private theorem fb8_1_1 : FB 8 1 1 = intv (-321/1000000000 : ℚ) (311/1000000000) := rfl
private theorem fb8_2_0 : FB 8 2 0 = intv (-398673/1000000000 : ℚ) (-398256/1000000000) := rfl
private theorem fb8_2_1 : FB 8 2 1 = intv (-246/1000000000 : ℚ) (284/1000000000) := rfl
private theorem fb8_3_0 : FB 8 3 0 = intv (63796/1000000000 : ℚ) (64258/1000000000) := rfl
private theorem fb8_3_1 : FB 8 3 1 = intv (-296/1000000000 : ℚ) (289/1000000000) := rfl
private theorem gb8_0 : GB 8 0 = intv (-525/1000000000 : ℚ) (509/1000000000) := rfl
private theorem gb8_1 : GB 8 1 = intv (-623/1000000000 : ℚ) (643/1000000000) := rfl
private theorem gb8_2 : GB 8 2 = intv (-569/1000000000 : ℚ) (493/1000000000) := rfl
private theorem gb8_3 : GB 8 3 = intv (-579/1000000000 : ℚ) (593/1000000000) := rfl

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
end N11Formalization.SourceFineRelativeFluxPacket
#check @N11Formalization.SourceFineRelativeFluxPacket.FB_mem
#check @N11Formalization.SourceFineRelativeFluxPacket.GB_mem
#print axioms N11Formalization.SourceFineRelativeFluxPacket.flux_readout
#print axioms N11Formalization.SourceFineRelativeFluxPacket.G_readout
