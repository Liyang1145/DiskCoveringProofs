import N11Formalization.SourceFineNEnclosure
import N11Formalization.SourceRelativeMetric

/-! Finer memberships of UNCHANGED exact SAME9R/10 N.
All180 finite outward comparisons are required, not assumed proposals. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineRelativeNIntervals
open N11Formalization RatInterval SourceActiveMatrixIntervals
open _root_.N11Formalization.SourceRelativeMetric hiding rawBox rawBox_mem metricBox metricBox_mem
noncomputable section
set_option maxRecDepth 10000

def rawBox (e : Fin 45) (a : Fin 4) : RatInterval :=
  match columnSlot e with
  | .inl i => SourceFineNEnclosure.dependentBox i a
  | .inr b => ofRat (if b=a then 1 else 0)
theorem rawBox_mem (e : Fin 45) (a : Fin 4) :
    (rawBox e a).Mem (SourceNormalizedKernel.N e a) := by
  unfold rawBox SourceNormalizedKernel.N
  rw [columnSlot_inverse]
  rcases columnSlot e with i | b
  · exact SourceFineNEnclosure.dependentBox_mem i a
  · by_cases hb : b=a
    · simp only [if_pos hb]
      simpa only [Rat.cast_one] using ofRat_mem (1 : ℚ)
    · simp only [if_neg hb]
      simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)

def metricBox (e : Fin 45) (a : Fin 4) : RatInterval :=
  sumI (fun b : Fin 4 => mul (rawBox e b) (ofRat (R b a)))
theorem metricBox_mem (e : Fin 45) (a : Fin 4) :
    (metricBox e a).Mem (sourceN e a) :=
  sumI_mem (fun b => mul_mem (rawBox_mem e b) (ofRat_mem (R b a)))

def NL : Fin 45 → Fin 4 → ℤ :=
 ![![253555,-338829,1215402,-195856],![-1963482,-2873240,-1881621,-2130204],![-1583555,-2317258,-1517539,-1718020],![809278,2093274,-471158,506054],![315856,-1857203,-1391017,-3032906],![-940675,1764816,181172,6699589],![-1695411,2580308,-348030,6445662],![1360779,55130,7067274,181172],![1966752,-731852,6831771,866975],![2556011,6173248,-886140,2402117],![2089958,6436709,55130,1764816],![-1528843,-2706124,-1070877,-1968855],![-647167,590909,-319943,2155274],![240575,-1559649,-1844063,-2690629],![298413,-1933816,-2286507,-3336224],![253535,-338803,1215307,-195841],![176443,-236119,846264,-136541],![176457,-236137,846328,-136552],![4050436,2089958,1360779,-940675],![2109430,1088125,708384,-490484],![2743461,1415275,921392,-637732],![-2903512,-798536,2605112,2766425],![-1512693,-416223,1356833,1440841],![-1967124,-541139,1764691,1873958],![-1719355,-2515987,-1647676,-1865350],![-2483044,-3633563,-2379514,-2693877],![-3411898,-4992840,-3269629,-3701590],![-1395016,1790368,-660542,2180790],![-1146517,1471252,-542920,1792111],![-1830385,2349461,-866616,2861754],![866227,-883787,668170,800605],![698661,-713011,538896,645716],![791205,-807328,610292,731259],![-344360,639791,943585,-534784],![-426776,793230,1169802,-662817],![-389887,724550,1068547,-605509],![1176494,1699722,-1048627,1269482],![1431673,2068367,-1275892,1544834],![1878808,2714323,-1674116,2027319],![377511,-2445517,-2891580,-4219123],![261249,-1693391,-2002210,-2921389],![518928,-3360373,-3973375,-5797636],![145195,-194498,696678,-112506],![145206,-194512,696730,-112514],![179920,-240749,862905,-139215]]

def NH : Fin 45 → Fin 4 → ℤ :=
 ![![254418,-337772,1216287,-194877],![-1962620,-2872184,-1880736,-2129224],![-1582692,-2316201,-1516654,-1717041],![810140,2094331,-470273,507033],![316719,-1856146,-1390132,-3031926],![-940674,1764817,181173,6699590],![-1694549,2581364,-347145,6446642],![1360780,55131,7067275,181173],![1967615,-730795,6832657,867954],![2556873,6174304,-885255,2403096],![2089959,6436710,55131,1764817],![-1527981,-2705067,-1069992,-1967876],![-646305,591966,-319058,2156253],![241438,-1558592,-1843178,-2689649],![299276,-1932759,-2285622,-3335245],![254398,-337746,1216192,-194862],![177306,-235062,847149,-135562],![177319,-235080,847213,-135573],![4050437,2089959,1360780,-940674],![2110292,1089182,709269,-489505],![2744324,1416332,922277,-636753],![-2902649,-797479,2605997,2767404],![-1511831,-415166,1357718,1441820],![-1966262,-540082,1765576,1874937],![-1718493,-2514930,-1646791,-1864371],![-2482182,-3632506,-2378629,-2692897],![-3411035,-4991783,-3268744,-3700611],![-1394153,1791425,-659657,2181769],![-1145655,1472309,-542035,1793091],![-1829523,2350518,-865731,2862733],![867089,-882730,669055,801584],![699524,-711955,539781,646695],![792068,-806271,611177,732238],![-343498,640847,944470,-533805],![-425914,794287,1170688,-661838],![-389024,725607,1069432,-604530],![1177357,1700779,-1047742,1270461],![1432535,2069424,-1275007,1545813],![1879671,2715380,-1673231,2028298],![378374,-2444460,-2890695,-4218144],![262111,-1692334,-2001324,-2920410],![519791,-3359317,-3972490,-5796657],![146058,-193441,697563,-111526],![146069,-193455,697616,-111535],![180782,-239692,863790,-138236]]

def NB (e : Fin 45) (a : Fin 4) : RatInterval :=
  intv ((NL e a : ℚ)/1000000000) ((NH e a : ℚ)/1000000000)
private theorem r0_0 : R 0 0=(5977389212899689600/1475739525896764129280 : ℚ) := rfl
private theorem r0_1 : R 0 1=(3084234978919466880/1475739525896764129280 : ℚ) := rfl
private theorem r0_2 : R 0 2=(2008156729907682720/1475739525896764129280 : ℚ) := rfl
private theorem r0_3 : R 0 3=(-1388190849679244160/1475739525896764129280 : ℚ) := rfl
private theorem r1_0 : R 1 0=(3084234978919466880/1475739525896764129280 : ℚ) := rfl
private theorem r1_1 : R 1 1=(9498906412506436608/1475739525896764129280 : ℚ) := rfl
private theorem r1_2 : R 1 2=(81357739426959030/1475739525896764129280 : ℚ) := rfl
private theorem r1_3 : R 1 3=(2604409099499393280/1475739525896764129280 : ℚ) := rfl
private theorem r2_0 : R 2 0=(2008156729907683008/1475739525896764129280 : ℚ) := rfl
private theorem r2_1 : R 2 1=(81357739426959498/1475739525896764129280 : ℚ) := rfl
private theorem r2_2 : R 2 2=(10429456537443393792/1475739525896764129280 : ℚ) := rfl
private theorem r2_3 : R 2 3=(267363491656565880/1475739525896764129280 : ℚ) := rfl
private theorem r3_0 : R 3 0=(-1388190849679243872/1475739525896764129280 : ℚ) := rfl
private theorem r3_1 : R 3 1=(2604409099499393280/1475739525896764129280 : ℚ) := rfl
private theorem r3_2 : R 3 2=(267363491656566096/1475739525896764129280 : ℚ) := rfl
private theorem r3_3 : R 3 3=(9886849369067412864/1475739525896764129280 : ℚ) := rfl
private theorem raw0_0 : rawBox 0 0=intv (3644885/100000000-1/19600 : ℚ) (3644885/100000000+1/19600) := rfl
private theorem raw0_1 : rawBox 0 1=intv (-6250581/100000000-1/19600 : ℚ) (-6250581/100000000+1/19600) := rfl
private theorem raw0_2 : rawBox 0 2=intv (16581743/100000000-1/19600 : ℚ) (16581743/100000000+1/19600) := rfl
private theorem raw0_3 : rawBox 0 3=intv (-1206197/100000000-1/19600 : ℚ) (-1206197/100000000+1/19600) := rfl
private theorem n0_0 : NB 0 0=intv (253555/1000000000 : ℚ) (254418/1000000000) := rfl
private theorem n0_1 : NB 0 1=intv (-338829/1000000000 : ℚ) (-337772/1000000000) := rfl
private theorem n0_2 : NB 0 2=intv (1215402/1000000000 : ℚ) (1216287/1000000000) := rfl
private theorem n0_3 : NB 0 3=intv (-195856/1000000000 : ℚ) (-194877/1000000000) := rfl
private theorem raw1_0 : rawBox 1 0=intv (-36618202/100000000-1/19600 : ℚ) (-36618202/100000000+1/19600) := rfl
private theorem raw1_1 : rawBox 1 1=intv (-24352353/100000000-1/19600 : ℚ) (-24352353/100000000+1/19600) := rfl
private theorem raw1_2 : rawBox 1 2=intv (-18608115/100000000-1/19600 : ℚ) (-18608115/100000000+1/19600) := rfl
private theorem raw1_3 : rawBox 1 3=intv (-30012064/100000000-1/19600 : ℚ) (-30012064/100000000+1/19600) := rfl
private theorem n1_0 : NB 1 0=intv (-1963482/1000000000 : ℚ) (-1962620/1000000000) := rfl
private theorem n1_1 : NB 1 1=intv (-2873240/1000000000 : ℚ) (-2872184/1000000000) := rfl
private theorem n1_2 : NB 1 2=intv (-1881621/1000000000 : ℚ) (-1880736/1000000000) := rfl
private theorem n1_3 : NB 1 3=intv (-2130204/1000000000 : ℚ) (-2129224/1000000000) := rfl
private theorem raw2_0 : rawBox 2 0=intv (-29531141/100000000-1/19600 : ℚ) (-29531141/100000000+1/19600) := rfl
private theorem raw2_1 : rawBox 2 1=intv (-19639216/100000000-1/19600 : ℚ) (-19639216/100000000+1/19600) := rfl
private theorem raw2_2 : rawBox 2 2=intv (-15006714/100000000-1/19600 : ℚ) (-15006714/100000000+1/19600) := rfl
private theorem raw2_3 : rawBox 2 3=intv (-24203550/100000000-1/19600 : ℚ) (-24203550/100000000+1/19600) := rfl
private theorem n2_0 : NB 2 0=intv (-1583555/1000000000 : ℚ) (-1582692/1000000000) := rfl
private theorem n2_1 : NB 2 1=intv (-2317258/1000000000 : ℚ) (-2316201/1000000000) := rfl
private theorem n2_2 : NB 2 2=intv (-1517539/1000000000 : ℚ) (-1516654/1000000000) := rfl
private theorem n2_3 : NB 2 3=intv (-1718020/1000000000 : ℚ) (-1717041/1000000000) := rfl
private theorem raw3_0 : rawBox 3 0=intv (7641196/100000000-1/19600 : ℚ) (7641196/100000000+1/19600) := rfl
private theorem raw3_1 : rawBox 3 1=intv (29846136/100000000-1/19600 : ℚ) (29846136/100000000+1/19600) := rfl
private theorem raw3_2 : rawBox 3 2=intv (-8390200/100000000-1/19600 : ℚ) (-8390200/100000000+1/19600) := rfl
private theorem raw3_3 : rawBox 3 3=intv (998476/100000000-1/19600 : ℚ) (998476/100000000+1/19600) := rfl
private theorem n3_0 : NB 3 0=intv (809278/1000000000 : ℚ) (810140/1000000000) := rfl
private theorem n3_1 : NB 3 1=intv (2093274/1000000000 : ℚ) (2094331/1000000000) := rfl
private theorem n3_2 : NB 3 2=intv (-471158/1000000000 : ℚ) (-470273/1000000000) := rfl
private theorem n3_3 : NB 3 3=intv (506054/1000000000 : ℚ) (507033/1000000000) := rfl
private theorem raw4_0 : rawBox 4 0=intv (20520990/100000000-1/19600 : ℚ) (20520990/100000000+1/19600) := rfl
private theorem raw4_1 : rawBox 4 1=intv (-25719678/100000000-1/19600 : ℚ) (-25719678/100000000+1/19600) := rfl
private theorem raw4_2 : rawBox 4 2=intv (-22529699/100000000-1/19600 : ℚ) (-22529699/100000000+1/19600) := rfl
private theorem raw4_3 : rawBox 4 3=intv (-34997033/100000000-1/19600 : ℚ) (-34997033/100000000+1/19600) := rfl
private theorem n4_0 : NB 4 0=intv (315856/1000000000 : ℚ) (316719/1000000000) := rfl
private theorem n4_1 : NB 4 1=intv (-1857203/1000000000 : ℚ) (-1856146/1000000000) := rfl
private theorem n4_2 : NB 4 2=intv (-1391017/1000000000 : ℚ) (-1390132/1000000000) := rfl
private theorem n4_3 : NB 4 3=intv (-3032906/1000000000 : ℚ) (-3031926/1000000000) := rfl
private theorem raw5_0 : rawBox 5 0=intv (0 : ℚ) (0) := rfl
private theorem raw5_1 : rawBox 5 1=intv (0 : ℚ) (0) := rfl
private theorem raw5_2 : rawBox 5 2=intv (0 : ℚ) (0) := rfl
private theorem raw5_3 : rawBox 5 3=intv (1 : ℚ) (1) := rfl
private theorem n5_0 : NB 5 0=intv (-940675/1000000000 : ℚ) (-940674/1000000000) := rfl
private theorem n5_1 : NB 5 1=intv (1764816/1000000000 : ℚ) (1764817/1000000000) := rfl
private theorem n5_2 : NB 5 2=intv (181172/1000000000 : ℚ) (181173/1000000000) := rfl
private theorem n5_3 : NB 5 3=intv (6699589/1000000000 : ℚ) (6699590/1000000000) := rfl
private theorem raw6_0 : rawBox 6 0=intv (-37808496/100000000-1/19600 : ℚ) (-37808496/100000000+1/19600) := rfl
private theorem raw6_1 : rawBox 6 1=intv (29583113/100000000-1/19600 : ℚ) (29583113/100000000+1/19600) := rfl
private theorem raw6_2 : rawBox 6 2=intv (152/100000000-1/19600 : ℚ) (152/100000000+1/19600) := rfl
private theorem raw6_3 : rawBox 6 3=intv (83115674/100000000-1/19600 : ℚ) (83115674/100000000+1/19600) := rfl
private theorem n6_0 : NB 6 0=intv (-1695411/1000000000 : ℚ) (-1694549/1000000000) := rfl
private theorem n6_1 : NB 6 1=intv (2580308/1000000000 : ℚ) (2581364/1000000000) := rfl
private theorem n6_2 : NB 6 2=intv (-348030/1000000000 : ℚ) (-347145/1000000000) := rfl
private theorem n6_3 : NB 6 3=intv (6445662/1000000000 : ℚ) (6446642/1000000000) := rfl
private theorem raw7_0 : rawBox 7 0=intv (0 : ℚ) (0) := rfl
private theorem raw7_1 : rawBox 7 1=intv (0 : ℚ) (0) := rfl
private theorem raw7_2 : rawBox 7 2=intv (1 : ℚ) (1) := rfl
private theorem raw7_3 : rawBox 7 3=intv (0 : ℚ) (0) := rfl
private theorem n7_0 : NB 7 0=intv (1360779/1000000000 : ℚ) (1360780/1000000000) := rfl
private theorem n7_1 : NB 7 1=intv (55130/1000000000 : ℚ) (55131/1000000000) := rfl
private theorem n7_2 : NB 7 2=intv (7067274/1000000000 : ℚ) (7067275/1000000000) := rfl
private theorem n7_3 : NB 7 3=intv (181172/1000000000 : ℚ) (181173/1000000000) := rfl
private theorem raw8_0 : rawBox 8 0=intv (41388656/100000000-1/19600 : ℚ) (41388656/100000000+1/19600) := rfl
private theorem raw8_1 : rawBox 8 1=intv (-32384395/100000000-1/19600 : ℚ) (-32384395/100000000+1/19600) := rfl
private theorem raw8_2 : rawBox 8 2=intv (88318967/100000000-1/19600 : ℚ) (88318967/100000000+1/19600) := rfl
private theorem raw8_3 : rawBox 8 3=intv (24901715/100000000-1/19600 : ℚ) (24901715/100000000+1/19600) := rfl
private theorem n8_0 : NB 8 0=intv (1966752/1000000000 : ℚ) (1967615/1000000000) := rfl
private theorem n8_1 : NB 8 1=intv (-731852/1000000000 : ℚ) (-730795/1000000000) := rfl
private theorem n8_2 : NB 8 2=intv (6831771/1000000000 : ℚ) (6832657/1000000000) := rfl
private theorem n8_3 : NB 8 3=intv (866975/1000000000 : ℚ) (867954/1000000000) := rfl
private theorem raw9_0 : rawBox 9 0=intv (33389477/100000000-1/19600 : ℚ) (33389477/100000000+1/19600) := rfl
private theorem raw9_1 : rawBox 9 1=intv (79737897/100000000-1/19600 : ℚ) (79737897/100000000+1/19600) := rfl
private theorem raw9_2 : rawBox 9 2=intv (-20098413/100000000-1/19600 : ℚ) (-20098413/100000000+1/19600) := rfl
private theorem raw9_3 : rawBox 9 3=intv (20088965/100000000-1/19600 : ℚ) (20088965/100000000+1/19600) := rfl
private theorem n9_0 : NB 9 0=intv (2556011/1000000000 : ℚ) (2556873/1000000000) := rfl
private theorem n9_1 : NB 9 1=intv (6173248/1000000000 : ℚ) (6174304/1000000000) := rfl
private theorem n9_2 : NB 9 2=intv (-886140/1000000000 : ℚ) (-885255/1000000000) := rfl
private theorem n9_3 : NB 9 3=intv (2402117/1000000000 : ℚ) (2403096/1000000000) := rfl
private theorem raw10_0 : rawBox 10 0=intv (0 : ℚ) (0) := rfl
private theorem raw10_1 : rawBox 10 1=intv (1 : ℚ) (1) := rfl
private theorem raw10_2 : rawBox 10 2=intv (0 : ℚ) (0) := rfl
private theorem raw10_3 : rawBox 10 3=intv (0 : ℚ) (0) := rfl
private theorem n10_0 : NB 10 0=intv (2089958/1000000000 : ℚ) (2089959/1000000000) := rfl
private theorem n10_1 : NB 10 1=intv (6436709/1000000000 : ℚ) (6436710/1000000000) := rfl
private theorem n10_2 : NB 10 2=intv (55130/1000000000 : ℚ) (55131/1000000000) := rfl
private theorem n10_3 : NB 10 3=intv (1764816/1000000000 : ℚ) (1764817/1000000000) := rfl
private theorem raw11_0 : rawBox 11 0=intv (-27446519/100000000-1/19600 : ℚ) (-27446519/100000000+1/19600) := rfl
private theorem raw11_1 : rawBox 11 1=intv (-25867970/100000000-1/19600 : ℚ) (-25867970/100000000+1/19600) := rfl
private theorem raw11_2 : rawBox 11 2=intv (-8988772/100000000-1/19600 : ℚ) (-8988772/100000000+1/19600) := rfl
private theorem raw11_3 : rawBox 11 3=intv (-26176838/100000000-1/19600 : ℚ) (-26176838/100000000+1/19600) := rfl
private theorem n11_0 : NB 11 0=intv (-1528843/1000000000 : ℚ) (-1527981/1000000000) := rfl
private theorem n11_1 : NB 11 1=intv (-2706124/1000000000 : ℚ) (-2705067/1000000000) := rfl
private theorem n11_2 : NB 11 2=intv (-1070877/1000000000 : ℚ) (-1069992/1000000000) := rfl
private theorem n11_3 : NB 11 3=intv (-1968855/1000000000 : ℚ) (-1967876/1000000000) := rfl
private theorem raw12_0 : rawBox 12 0=intv (-10221146/100000000-1/19600 : ℚ) (-10221146/100000000+1/19600) := rfl
private theorem raw12_1 : rawBox 12 1=intv (4399929/100000000-1/19600 : ℚ) (4399929/100000000+1/19600) := rfl
private theorem raw12_2 : rawBox 12 2=intv (-3347819/100000000-1/19600 : ℚ) (-3347819/100000000+1/19600) := rfl
private theorem raw12_3 : rawBox 12 3=intv (29673919/100000000-1/19600 : ℚ) (29673919/100000000+1/19600) := rfl
private theorem n12_0 : NB 12 0=intv (-647167/1000000000 : ℚ) (-646305/1000000000) := rfl
private theorem n12_1 : NB 12 1=intv (590909/1000000000 : ℚ) (591966/1000000000) := rfl
private theorem n12_2 : NB 12 2=intv (-319943/1000000000 : ℚ) (-319058/1000000000) := rfl
private theorem n12_3 : NB 12 3=intv (2155274/1000000000 : ℚ) (2156253/1000000000) := rfl
private theorem raw13_0 : rawBox 13 0=intv (19869272/100000000-1/19600 : ℚ) (19869272/100000000+1/19600) := rfl
private theorem raw13_1 : rawBox 13 1=intv (-21983762/100000000-1/19600 : ℚ) (-21983762/100000000+1/19600) := rfl
private theorem raw13_2 : rawBox 13 2=intv (-28951686/100000000-1/19600 : ℚ) (-28951686/100000000+1/19600) := rfl
private theorem raw13_3 : rawBox 13 3=intv (-30790069/100000000-1/19600 : ℚ) (-30790069/100000000+1/19600) := rfl
private theorem n13_0 : NB 13 0=intv (240575/1000000000 : ℚ) (241438/1000000000) := rfl
private theorem n13_1 : NB 13 1=intv (-1559649/1000000000 : ℚ) (-1558592/1000000000) := rfl
private theorem n13_2 : NB 13 2=intv (-1844063/1000000000 : ℚ) (-1843178/1000000000) := rfl
private theorem n13_3 : NB 13 3=intv (-2690629/1000000000 : ℚ) (-2689649/1000000000) := rfl
private theorem raw14_0 : rawBox 14 0=intv (24637620/100000000-1/19600 : ℚ) (24637620/100000000+1/19600) := rfl
private theorem raw14_1 : rawBox 14 1=intv (-27259558/100000000-1/19600 : ℚ) (-27259558/100000000+1/19600) := rfl
private theorem raw14_2 : rawBox 14 2=intv (-35899686/100000000-1/19600 : ℚ) (-35899686/100000000+1/19600) := rfl
private theorem raw14_3 : rawBox 14 3=intv (-38179255/100000000-1/19600 : ℚ) (-38179255/100000000+1/19600) := rfl
private theorem n14_0 : NB 14 0=intv (298413/1000000000 : ℚ) (299276/1000000000) := rfl
private theorem n14_1 : NB 14 1=intv (-1933816/1000000000 : ℚ) (-1932759/1000000000) := rfl
private theorem n14_2 : NB 14 2=intv (-2286507/1000000000 : ℚ) (-2285622/1000000000) := rfl
private theorem n14_3 : NB 14 3=intv (-3336224/1000000000 : ℚ) (-3335245/1000000000) := rfl
private theorem raw15_0 : rawBox 15 0=intv (3644599/100000000-1/19600 : ℚ) (3644599/100000000+1/19600) := rfl
private theorem raw15_1 : rawBox 15 1=intv (-6250090/100000000-1/19600 : ℚ) (-6250090/100000000+1/19600) := rfl
private theorem raw15_2 : rawBox 15 2=intv (16580440/100000000-1/19600 : ℚ) (16580440/100000000+1/19600) := rfl
private theorem raw15_3 : rawBox 15 3=intv (-1206102/100000000-1/19600 : ℚ) (-1206102/100000000+1/19600) := rfl
private theorem n15_0 : NB 15 0=intv (253535/1000000000 : ℚ) (254398/1000000000) := rfl
private theorem n15_1 : NB 15 1=intv (-338803/1000000000 : ℚ) (-337746/1000000000) := rfl
private theorem n15_2 : NB 15 2=intv (1215307/1000000000 : ℚ) (1216192/1000000000) := rfl
private theorem n15_3 : NB 15 3=intv (-195841/1000000000 : ℚ) (-194862/1000000000) := rfl
private theorem raw16_0 : rawBox 16 0=intv (2538273/100000000-1/19600 : ℚ) (2538273/100000000+1/19600) := rfl
private theorem raw16_1 : rawBox 16 1=intv (-4352862/100000000-1/19600 : ℚ) (-4352862/100000000+1/19600) := rfl
private theorem raw16_2 : rawBox 16 2=intv (11547412/100000000-1/19600 : ℚ) (11547412/100000000+1/19600) := rfl
private theorem raw16_3 : rawBox 16 3=intv (-839987/100000000-1/19600 : ℚ) (-839987/100000000+1/19600) := rfl
private theorem n16_0 : NB 16 0=intv (176443/1000000000 : ℚ) (177306/1000000000) := rfl
private theorem n16_1 : NB 16 1=intv (-236119/1000000000 : ℚ) (-235062/1000000000) := rfl
private theorem n16_2 : NB 16 2=intv (846264/1000000000 : ℚ) (847149/1000000000) := rfl
private theorem n16_3 : NB 16 3=intv (-136541/1000000000 : ℚ) (-135562/1000000000) := rfl
private theorem raw17_0 : rawBox 17 0=intv (2538465/100000000-1/19600 : ℚ) (2538465/100000000+1/19600) := rfl
private theorem raw17_1 : rawBox 17 1=intv (-4353191/100000000-1/19600 : ℚ) (-4353191/100000000+1/19600) := rfl
private theorem raw17_2 : rawBox 17 2=intv (11548286/100000000-1/19600 : ℚ) (11548286/100000000+1/19600) := rfl
private theorem raw17_3 : rawBox 17 3=intv (-840051/100000000-1/19600 : ℚ) (-840051/100000000+1/19600) := rfl
private theorem n17_0 : NB 17 0=intv (176457/1000000000 : ℚ) (177319/1000000000) := rfl
private theorem n17_1 : NB 17 1=intv (-236137/1000000000 : ℚ) (-235080/1000000000) := rfl
private theorem n17_2 : NB 17 2=intv (846328/1000000000 : ℚ) (847213/1000000000) := rfl
private theorem n17_3 : NB 17 3=intv (-136552/1000000000 : ℚ) (-135573/1000000000) := rfl
private theorem raw18_0 : rawBox 18 0=intv (1 : ℚ) (1) := rfl
private theorem raw18_1 : rawBox 18 1=intv (0 : ℚ) (0) := rfl
private theorem raw18_2 : rawBox 18 2=intv (0 : ℚ) (0) := rfl
private theorem raw18_3 : rawBox 18 3=intv (0 : ℚ) (0) := rfl
private theorem n18_0 : NB 18 0=intv (4050436/1000000000 : ℚ) (4050437/1000000000) := rfl
private theorem n18_1 : NB 18 1=intv (2089958/1000000000 : ℚ) (2089959/1000000000) := rfl
private theorem n18_2 : NB 18 2=intv (1360779/1000000000 : ℚ) (1360780/1000000000) := rfl
private theorem n18_3 : NB 18 3=intv (-940675/1000000000 : ℚ) (-940674/1000000000) := rfl
private theorem raw19_0 : rawBox 19 0=intv (52089722/100000000-1/19600 : ℚ) (52089722/100000000+1/19600) := rfl
private theorem raw19_1 : rawBox 19 1=intv (0/100000000-1/19600 : ℚ) (0/100000000+1/19600) := rfl
private theorem raw19_2 : rawBox 19 2=intv (0/100000000-1/19600 : ℚ) (0/100000000+1/19600) := rfl
private theorem raw19_3 : rawBox 19 3=intv (0/100000000-1/19600 : ℚ) (0/100000000+1/19600) := rfl
private theorem n19_0 : NB 19 0=intv (2109430/1000000000 : ℚ) (2110292/1000000000) := rfl
private theorem n19_1 : NB 19 1=intv (1088125/1000000000 : ℚ) (1089182/1000000000) := rfl
private theorem n19_2 : NB 19 2=intv (708384/1000000000 : ℚ) (709269/1000000000) := rfl
private theorem n19_3 : NB 19 3=intv (-490484/1000000000 : ℚ) (-489505/1000000000) := rfl
private theorem raw20_0 : rawBox 20 0=intv (67743131/100000000-1/19600 : ℚ) (67743131/100000000+1/19600) := rfl
private theorem raw20_1 : rawBox 20 1=intv (0/100000000-1/19600 : ℚ) (0/100000000+1/19600) := rfl
private theorem raw20_2 : rawBox 20 2=intv (0/100000000-1/19600 : ℚ) (0/100000000+1/19600) := rfl
private theorem raw20_3 : rawBox 20 3=intv (0/100000000-1/19600 : ℚ) (0/100000000+1/19600) := rfl
private theorem n20_0 : NB 20 0=intv (2743461/1000000000 : ℚ) (2744324/1000000000) := rfl
private theorem n20_1 : NB 20 1=intv (1415275/1000000000 : ℚ) (1416332/1000000000) := rfl
private theorem n20_2 : NB 20 2=intv (921392/1000000000 : ℚ) (922277/1000000000) := rfl
private theorem n20_3 : NB 20 3=intv (-637732/1000000000 : ℚ) (-636753/1000000000) := rfl
private theorem raw21_0 : rawBox 21 0=intv (-88312959/100000000-1/19600 : ℚ) (-88312959/100000000+1/19600) := rfl
private theorem raw21_1 : rawBox 21 1=intv (8937478/100000000-1/19600 : ℚ) (8937478/100000000+1/19600) := rfl
private theorem raw21_2 : rawBox 21 2=intv (53158875/100000000-1/19600 : ℚ) (53158875/100000000+1/19600) := rfl
private theorem raw21_3 : rawBox 21 3=intv (25108070/100000000-1/19600 : ℚ) (25108070/100000000+1/19600) := rfl
private theorem n21_0 : NB 21 0=intv (-2903512/1000000000 : ℚ) (-2902649/1000000000) := rfl
private theorem n21_1 : NB 21 1=intv (-798536/1000000000 : ℚ) (-797479/1000000000) := rfl
private theorem n21_2 : NB 21 2=intv (2605112/1000000000 : ℚ) (2605997/1000000000) := rfl
private theorem n21_3 : NB 21 3=intv (2766425/1000000000 : ℚ) (2767404/1000000000) := rfl
private theorem raw22_0 : rawBox 22 0=intv (-46003650/100000000-1/19600 : ℚ) (-46003650/100000000+1/19600) := rfl
private theorem raw22_1 : rawBox 22 1=intv (4655677/100000000-1/19600 : ℚ) (4655677/100000000+1/19600) := rfl
private theorem raw22_2 : rawBox 22 2=intv (27691318/100000000-1/19600 : ℚ) (27691318/100000000+1/19600) := rfl
private theorem raw22_3 : rawBox 22 3=intv (13079200/100000000-1/19600 : ℚ) (13079200/100000000+1/19600) := rfl
private theorem n22_0 : NB 22 0=intv (-1512693/1000000000 : ℚ) (-1511831/1000000000) := rfl
private theorem n22_1 : NB 22 1=intv (-416223/1000000000 : ℚ) (-415166/1000000000) := rfl
private theorem n22_2 : NB 22 2=intv (1356833/1000000000 : ℚ) (1357718/1000000000) := rfl
private theorem n22_3 : NB 22 3=intv (1440841/1000000000 : ℚ) (1441820/1000000000) := rfl
private theorem raw23_0 : rawBox 23 0=intv (-59827638/100000000-1/19600 : ℚ) (-59827638/100000000+1/19600) := rfl
private theorem raw23_1 : rawBox 23 1=intv (6054697/100000000-1/19600 : ℚ) (6054697/100000000+1/19600) := rfl
private theorem raw23_2 : rawBox 23 2=intv (36012494/100000000-1/19600 : ℚ) (36012494/100000000+1/19600) := rfl
private theorem raw23_3 : rawBox 23 3=intv (17009469/100000000-1/19600 : ℚ) (17009469/100000000+1/19600) := rfl
private theorem n23_0 : NB 23 0=intv (-1967124/1000000000 : ℚ) (-1966262/1000000000) := rfl
private theorem n23_1 : NB 23 1=intv (-541139/1000000000 : ℚ) (-540082/1000000000) := rfl
private theorem n23_2 : NB 23 2=intv (1764691/1000000000 : ℚ) (1765576/1000000000) := rfl
private theorem n23_3 : NB 23 3=intv (1873958/1000000000 : ℚ) (1874937/1000000000) := rfl
private theorem raw24_0 : rawBox 24 0=intv (-32064327/100000000-1/19600 : ℚ) (-32064327/100000000+1/19600) := rfl
private theorem raw24_1 : rawBox 24 1=intv (-21323871/100000000-1/19600 : ℚ) (-21323871/100000000+1/19600) := rfl
private theorem raw24_2 : rawBox 24 2=intv (-16293992/100000000-1/19600 : ℚ) (-16293992/100000000+1/19600) := rfl
private theorem raw24_3 : rawBox 24 3=intv (-26279735/100000000-1/19600 : ℚ) (-26279735/100000000+1/19600) := rfl
private theorem n24_0 : NB 24 0=intv (-1719355/1000000000 : ℚ) (-1718493/1000000000) := rfl
private theorem n24_1 : NB 24 1=intv (-2515987/1000000000 : ℚ) (-2514930/1000000000) := rfl
private theorem n24_2 : NB 24 2=intv (-1647676/1000000000 : ℚ) (-1646791/1000000000) := rfl
private theorem n24_3 : NB 24 3=intv (-1865350/1000000000 : ℚ) (-1864371/1000000000) := rfl
private theorem raw25_0 : rawBox 25 0=intv (-46309969/100000000-1/19600 : ℚ) (-46309969/100000000+1/19600) := rfl
private theorem raw25_1 : rawBox 25 1=intv (-30797708/100000000-1/19600 : ℚ) (-30797708/100000000+1/19600) := rfl
private theorem raw25_2 : rawBox 25 2=intv (-23533139/100000000-1/19600 : ℚ) (-23533139/100000000+1/19600) := rfl
private theorem raw25_3 : rawBox 25 3=intv (-37955379/100000000-1/19600 : ℚ) (-37955379/100000000+1/19600) := rfl
private theorem n25_0 : NB 25 0=intv (-2483044/1000000000 : ℚ) (-2482182/1000000000) := rfl
private theorem n25_1 : NB 25 1=intv (-3633563/1000000000 : ℚ) (-3632506/1000000000) := rfl
private theorem n25_2 : NB 25 2=intv (-2379514/1000000000 : ℚ) (-2378629/1000000000) := rfl
private theorem n25_3 : NB 25 3=intv (-2693877/1000000000 : ℚ) (-2692897/1000000000) := rfl
private theorem raw26_0 : rawBox 26 0=intv (-63636544/100000000-1/19600 : ℚ) (-63636544/100000000+1/19600) := rfl
private theorem raw26_1 : rawBox 26 1=intv (-42320472/100000000-1/19600 : ℚ) (-42320472/100000000+1/19600) := rfl
private theorem raw26_2 : rawBox 26 2=intv (-32337911/100000000-1/19600 : ℚ) (-32337911/100000000+1/19600) := rfl
private theorem raw26_3 : rawBox 26 3=intv (-52156139/100000000-1/19600 : ℚ) (-52156139/100000000+1/19600) := rfl
private theorem n26_0 : NB 26 0=intv (-3411898/1000000000 : ℚ) (-3411035/1000000000) := rfl
private theorem n26_1 : NB 26 1=intv (-4992840/1000000000 : ℚ) (-4991783/1000000000) := rfl
private theorem n26_2 : NB 26 2=intv (-3269629/1000000000 : ℚ) (-3268744/1000000000) := rfl
private theorem n26_3 : NB 26 3=intv (-3701590/1000000000 : ℚ) (-3700611/1000000000) := rfl
private theorem raw27_0 : rawBox 27 0=intv (-52092790/100000000-1/19600 : ℚ) (-52092790/100000000+1/19600) := rfl
private theorem raw27_1 : rawBox 27 1=intv (40759804/100000000-1/19600 : ℚ) (40759804/100000000+1/19600) := rfl
private theorem raw27_2 : rawBox 27 2=intv (209/100000000-1/19600 : ℚ) (209/100000000+1/19600) := rfl
private theorem raw27_3 : rawBox 27 3=intv (14507149/100000000-1/19600 : ℚ) (14507149/100000000+1/19600) := rfl
private theorem n27_0 : NB 27 0=intv (-1395016/1000000000 : ℚ) (-1394153/1000000000) := rfl
private theorem n27_1 : NB 27 1=intv (1790368/1000000000 : ℚ) (1791425/1000000000) := rfl
private theorem n27_2 : NB 27 2=intv (-660542/1000000000 : ℚ) (-659657/1000000000) := rfl
private theorem n27_3 : NB 27 3=intv (2180790/1000000000 : ℚ) (2181769/1000000000) := rfl
private theorem raw28_0 : rawBox 28 0=intv (-42810470/100000000-1/19600 : ℚ) (-42810470/100000000+1/19600) := rfl
private theorem raw28_1 : rawBox 28 1=intv (33496888/100000000-1/19600 : ℚ) (33496888/100000000+1/19600) := rfl
private theorem raw28_2 : rawBox 28 2=intv (172/100000000-1/19600 : ℚ) (172/100000000+1/19600) := rfl
private theorem raw28_3 : rawBox 28 3=intv (11922147/100000000-1/19600 : ℚ) (11922147/100000000+1/19600) := rfl
private theorem n28_0 : NB 28 0=intv (-1146517/1000000000 : ℚ) (-1145655/1000000000) := rfl
private theorem n28_1 : NB 28 1=intv (1471252/1000000000 : ℚ) (1472309/1000000000) := rfl
private theorem n28_2 : NB 28 2=intv (-542920/1000000000 : ℚ) (-542035/1000000000) := rfl
private theorem n28_3 : NB 28 3=intv (1792111/1000000000 : ℚ) (1793091/1000000000) := rfl
private theorem raw29_0 : rawBox 29 0=intv (-68355415/100000000-1/19600 : ℚ) (-68355415/100000000+1/19600) := rfl
private theorem raw29_1 : rawBox 29 1=intv (53484433/100000000-1/19600 : ℚ) (53484433/100000000+1/19600) := rfl
private theorem raw29_2 : rawBox 29 2=intv (275/100000000-1/19600 : ℚ) (275/100000000+1/19600) := rfl
private theorem raw29_3 : rawBox 29 3=intv (19036074/100000000-1/19600 : ℚ) (19036074/100000000+1/19600) := rfl
private theorem n29_0 : NB 29 0=intv (-1830385/1000000000 : ℚ) (-1829523/1000000000) := rfl
private theorem n29_1 : NB 29 1=intv (2349461/1000000000 : ℚ) (2350518/1000000000) := rfl
private theorem n29_2 : NB 29 2=intv (-866616/1000000000 : ℚ) (-865731/1000000000) := rfl
private theorem n29_3 : NB 29 3=intv (2861754/1000000000 : ℚ) (2862733/1000000000) := rfl
private theorem raw30_0 : rawBox 30 0=intv (46866935/100000000-1/19600 : ℚ) (46866935/100000000+1/19600) := rfl
private theorem raw30_1 : rawBox 30 1=intv (-36670854/100000000-1/19600 : ℚ) (-36670854/100000000+1/19600) := rfl
private theorem raw30_2 : rawBox 30 2=intv (-188/100000000-1/19600 : ℚ) (-188/100000000+1/19600) := rfl
private theorem raw30_3 : rawBox 30 3=intv (28197753/100000000-1/19600 : ℚ) (28197753/100000000+1/19600) := rfl
private theorem n30_0 : NB 30 0=intv (866227/1000000000 : ℚ) (867089/1000000000) := rfl
private theorem n30_1 : NB 30 1=intv (-883787/1000000000 : ℚ) (-882730/1000000000) := rfl
private theorem n30_2 : NB 30 2=intv (668170/1000000000 : ℚ) (669055/1000000000) := rfl
private theorem n30_3 : NB 30 3=intv (800605/1000000000 : ℚ) (801584/1000000000) := rfl
private theorem raw31_0 : rawBox 31 0=intv (37805363/100000000-1/19600 : ℚ) (37805363/100000000+1/19600) := rfl
private theorem raw31_1 : rawBox 31 1=intv (-29580661/100000000-1/19600 : ℚ) (-29580661/100000000+1/19600) := rfl
private theorem raw31_2 : rawBox 31 2=intv (-152/100000000-1/19600 : ℚ) (-152/100000000+1/19600) := rfl
private theorem raw31_3 : rawBox 31 3=intv (22745807/100000000-1/19600 : ℚ) (22745807/100000000+1/19600) := rfl
private theorem n31_0 : NB 31 0=intv (698661/1000000000 : ℚ) (699524/1000000000) := rfl
private theorem n31_1 : NB 31 1=intv (-713011/1000000000 : ℚ) (-711955/1000000000) := rfl
private theorem n31_2 : NB 31 2=intv (538896/1000000000 : ℚ) (539781/1000000000) := rfl
private theorem n31_3 : NB 31 3=intv (645716/1000000000 : ℚ) (646695/1000000000) := rfl
private theorem raw32_0 : rawBox 32 0=intv (42809939/100000000-1/19600 : ℚ) (42809939/100000000+1/19600) := rfl
private theorem raw32_1 : rawBox 32 1=intv (-33496473/100000000-1/19600 : ℚ) (-33496473/100000000+1/19600) := rfl
private theorem raw32_2 : rawBox 32 2=intv (-172/100000000-1/19600 : ℚ) (-172/100000000+1/19600) := rfl
private theorem raw32_3 : rawBox 32 3=intv (25756839/100000000-1/19600 : ℚ) (25756839/100000000+1/19600) := rfl
private theorem n32_0 : NB 32 0=intv (791205/1000000000 : ℚ) (792068/1000000000) := rfl
private theorem n32_1 : NB 32 1=intv (-807328/1000000000 : ℚ) (-806271/1000000000) := rfl
private theorem n32_2 : NB 32 2=intv (610292/1000000000 : ℚ) (611177/1000000000) := rfl
private theorem n32_3 : NB 32 3=intv (731259/1000000000 : ℚ) (732238/1000000000) := rfl
private theorem raw33_0 : rawBox 33 0=intv (-33388328/100000000-1/19600 : ℚ) (-33388328/100000000+1/19600) := rfl
private theorem raw33_1 : rawBox 33 1=intv (26124570/100000000-1/19600 : ℚ) (26124570/100000000+1/19600) := rfl
private theorem raw33_2 : rawBox 33 2=intv (20097721/100000000-1/19600 : ℚ) (20097721/100000000+1/19600) := rfl
private theorem raw33_3 : rawBox 33 3=intv (-20088274/100000000-1/19600 : ℚ) (-20088274/100000000+1/19600) := rfl
private theorem n33_0 : NB 33 0=intv (-344360/1000000000 : ℚ) (-343498/1000000000) := rfl
private theorem n33_1 : NB 33 1=intv (639791/1000000000 : ℚ) (640847/1000000000) := rfl
private theorem n33_2 : NB 33 2=intv (943585/1000000000 : ℚ) (944470/1000000000) := rfl
private theorem n33_3 : NB 33 3=intv (-534784/1000000000 : ℚ) (-533805/1000000000) := rfl
private theorem raw34_0 : rawBox 34 0=intv (-41389175/100000000-1/19600 : ℚ) (-41389175/100000000+1/19600) := rfl
private theorem raw34_1 : rawBox 34 1=intv (32384802/100000000-1/19600 : ℚ) (32384802/100000000+1/19600) := rfl
private theorem raw34_2 : rawBox 34 2=intv (24913740/100000000-1/19600 : ℚ) (24913740/100000000+1/19600) := rfl
private theorem raw34_3 : rawBox 34 3=intv (-24902028/100000000-1/19600 : ℚ) (-24902028/100000000+1/19600) := rfl
private theorem n34_0 : NB 34 0=intv (-426776/1000000000 : ℚ) (-425914/1000000000) := rfl
private theorem n34_1 : NB 34 1=intv (793230/1000000000 : ℚ) (794287/1000000000) := rfl
private theorem n34_2 : NB 34 2=intv (1169802/1000000000 : ℚ) (1170688/1000000000) := rfl
private theorem n34_3 : NB 34 3=intv (-662817/1000000000 : ℚ) (-661838/1000000000) := rfl
private theorem raw35_0 : rawBox 35 0=intv (-37807975/100000000-1/19600 : ℚ) (-37807975/100000000+1/19600) := rfl
private theorem raw35_1 : rawBox 35 1=intv (29582705/100000000-1/19600 : ℚ) (29582705/100000000+1/19600) := rfl
private theorem raw35_2 : rawBox 35 2=intv (22758077/100000000-1/19600 : ℚ) (22758077/100000000+1/19600) := rfl
private theorem raw35_3 : rawBox 35 3=intv (-22747379/100000000-1/19600 : ℚ) (-22747379/100000000+1/19600) := rfl
private theorem n35_0 : NB 35 0=intv (-389887/1000000000 : ℚ) (-389024/1000000000) := rfl
private theorem n35_1 : NB 35 1=intv (724550/1000000000 : ℚ) (725607/1000000000) := rfl
private theorem n35_2 : NB 35 2=intv (1068547/1000000000 : ℚ) (1069432/1000000000) := rfl
private theorem n35_3 : NB 35 3=intv (-605509/1000000000 : ℚ) (-604530/1000000000) := rfl
private theorem raw36_0 : rawBox 36 0=intv (37806826/100000000-1/19600 : ℚ) (37806826/100000000+1/19600) := rfl
private theorem raw36_1 : rawBox 36 1=intv (8097498/100000000-1/19600 : ℚ) (8097498/100000000+1/19600) := rfl
private theorem raw36_2 : rawBox 36 2=intv (-22757385/100000000-1/19600 : ℚ) (-22757385/100000000+1/19600) := rfl
private theorem raw36_3 : rawBox 36 3=intv (22746687/100000000-1/19600 : ℚ) (22746687/100000000+1/19600) := rfl
private theorem n36_0 : NB 36 0=intv (1176494/1000000000 : ℚ) (1177357/1000000000) := rfl
private theorem n36_1 : NB 36 1=intv (1699722/1000000000 : ℚ) (1700779/1000000000) := rfl
private theorem n36_2 : NB 36 2=intv (-1048627/1000000000 : ℚ) (-1047742/1000000000) := rfl
private theorem n36_3 : NB 36 3=intv (1269482/1000000000 : ℚ) (1270461/1000000000) := rfl
private theorem raw37_0 : rawBox 37 0=intv (46004017/100000000-1/19600 : ℚ) (46004017/100000000+1/19600) := rfl
private theorem raw37_1 : rawBox 37 1=intv (9853180/100000000-1/19600 : ℚ) (9853180/100000000+1/19600) := rfl
private theorem raw37_2 : rawBox 37 2=intv (-27691591/100000000-1/19600 : ℚ) (-27691591/100000000+1/19600) := rfl
private theorem raw37_3 : rawBox 37 3=intv (27678573/100000000-1/19600 : ℚ) (27678573/100000000+1/19600) := rfl
private theorem n37_0 : NB 37 0=intv (1431673/1000000000 : ℚ) (1432535/1000000000) := rfl
private theorem n37_1 : NB 37 1=intv (2068367/1000000000 : ℚ) (2069424/1000000000) := rfl
private theorem n37_2 : NB 37 2=intv (-1275892/1000000000 : ℚ) (-1275007/1000000000) := rfl
private theorem n37_3 : NB 37 3=intv (1544834/1000000000 : ℚ) (1545813/1000000000) := rfl
private theorem raw38_0 : rawBox 38 0=intv (60367515/100000000-1/19600 : ℚ) (60367515/100000000+1/19600) := rfl
private theorem raw38_1 : rawBox 38 1=intv (12929566/100000000-1/19600 : ℚ) (12929566/100000000+1/19600) := rfl
private theorem raw38_2 : rawBox 38 2=intv (-36337533/100000000-1/19600 : ℚ) (-36337533/100000000+1/19600) := rfl
private theorem raw38_3 : rawBox 38 3=intv (36320452/100000000-1/19600 : ℚ) (36320452/100000000+1/19600) := rfl
private theorem n38_0 : NB 38 0=intv (1878808/1000000000 : ℚ) (1879671/1000000000) := rfl
private theorem n38_1 : NB 38 1=intv (2714323/1000000000 : ℚ) (2715380/1000000000) := rfl
private theorem n38_2 : NB 38 2=intv (-1674116/1000000000 : ℚ) (-1673231/1000000000) := rfl
private theorem n38_3 : NB 38 3=intv (2027319/1000000000 : ℚ) (2028298/1000000000) := rfl
private theorem raw39_0 : rawBox 39 0=intv (31158680/100000000-1/19600 : ℚ) (31158680/100000000+1/19600) := rfl
private theorem raw39_1 : rawBox 39 1=intv (-34474590/100000000-1/19600 : ℚ) (-34474590/100000000+1/19600) := rfl
private theorem raw39_2 : rawBox 39 2=intv (-45401579/100000000-1/19600 : ℚ) (-45401579/100000000+1/19600) := rfl
private theorem raw39_3 : rawBox 39 3=intv (-48284502/100000000-1/19600 : ℚ) (-48284502/100000000+1/19600) := rfl
private theorem n39_0 : NB 39 0=intv (377511/1000000000 : ℚ) (378374/1000000000) := rfl
private theorem n39_1 : NB 39 1=intv (-2445517/1000000000 : ℚ) (-2444460/1000000000) := rfl
private theorem n39_2 : NB 39 2=intv (-2891580/1000000000 : ℚ) (-2890695/1000000000) := rfl
private theorem n39_3 : NB 39 3=intv (-4219123/1000000000 : ℚ) (-4218144/1000000000) := rfl
private theorem raw40_0 : rawBox 40 0=intv (21573661/100000000-1/19600 : ℚ) (21573661/100000000+1/19600) := rfl
private theorem raw40_1 : rawBox 40 1=intv (-23869533/100000000-1/19600 : ℚ) (-23869533/100000000+1/19600) := rfl
private theorem raw40_2 : rawBox 40 2=intv (-31435166/100000000-1/19600 : ℚ) (-31435166/100000000+1/19600) := rfl
private theorem raw40_3 : rawBox 40 3=intv (-33431246/100000000-1/19600 : ℚ) (-33431246/100000000+1/19600) := rfl
private theorem n40_0 : NB 40 0=intv (261249/1000000000 : ℚ) (262111/1000000000) := rfl
private theorem n40_1 : NB 40 1=intv (-1693391/1000000000 : ℚ) (-1692334/1000000000) := rfl
private theorem n40_2 : NB 40 2=intv (-2002210/1000000000 : ℚ) (-2001324/1000000000) := rfl
private theorem n40_3 : NB 40 3=intv (-2921389/1000000000 : ℚ) (-2920410/1000000000) := rfl
private theorem raw41_0 : rawBox 41 0=intv (42817520/100000000-1/19600 : ℚ) (42817520/100000000+1/19600) := rfl
private theorem raw41_1 : rawBox 41 1=intv (-47374166/100000000-1/19600 : ℚ) (-47374166/100000000+1/19600) := rfl
private theorem raw41_2 : rawBox 41 2=intv (-62389774/100000000-1/19600 : ℚ) (-62389774/100000000+1/19600) := rfl
private theorem raw41_3 : rawBox 41 3=intv (-66351419/100000000-1/19600 : ℚ) (-66351419/100000000+1/19600) := rfl
private theorem n41_0 : NB 41 0=intv (518928/1000000000 : ℚ) (519791/1000000000) := rfl
private theorem n41_1 : NB 41 1=intv (-3360373/1000000000 : ℚ) (-3359317/1000000000) := rfl
private theorem n41_2 : NB 41 2=intv (-3973375/1000000000 : ℚ) (-3972490/1000000000) := rfl
private theorem n41_3 : NB 41 3=intv (-5797636/1000000000 : ℚ) (-5796657/1000000000) := rfl
private theorem raw42_0 : rawBox 42 0=intv (2089843/100000000-1/19600 : ℚ) (2089843/100000000+1/19600) := rfl
private theorem raw42_1 : rawBox 42 1=intv (-3583853/100000000-1/19600 : ℚ) (-3583853/100000000+1/19600) := rfl
private theorem raw42_2 : rawBox 42 2=intv (9507361/100000000-1/19600 : ℚ) (9507361/100000000+1/19600) := rfl
private theorem raw42_3 : rawBox 42 3=intv (-691589/100000000-1/19600 : ℚ) (-691589/100000000+1/19600) := rfl
private theorem n42_0 : NB 42 0=intv (145195/1000000000 : ℚ) (146058/1000000000) := rfl
private theorem n42_1 : NB 42 1=intv (-194498/1000000000 : ℚ) (-193441/1000000000) := rfl
private theorem n42_2 : NB 42 2=intv (696678/1000000000 : ℚ) (697563/1000000000) := rfl
private theorem n42_3 : NB 42 3=intv (-112506/1000000000 : ℚ) (-111526/1000000000) := rfl
private theorem raw43_0 : rawBox 43 0=intv (2090000/100000000-1/19600 : ℚ) (2090000/100000000+1/19600) := rfl
private theorem raw43_1 : rawBox 43 1=intv (-3584122/100000000-1/19600 : ℚ) (-3584122/100000000+1/19600) := rfl
private theorem raw43_2 : rawBox 43 2=intv (9508074/100000000-1/19600 : ℚ) (9508074/100000000+1/19600) := rfl
private theorem raw43_3 : rawBox 43 3=intv (-691641/100000000-1/19600 : ℚ) (-691641/100000000+1/19600) := rfl
private theorem n43_0 : NB 43 0=intv (145206/1000000000 : ℚ) (146069/1000000000) := rfl
private theorem n43_1 : NB 43 1=intv (-194512/1000000000 : ℚ) (-193455/1000000000) := rfl
private theorem n43_2 : NB 43 2=intv (696730/1000000000 : ℚ) (697616/1000000000) := rfl
private theorem n43_3 : NB 43 3=intv (-112514/1000000000 : ℚ) (-111535/1000000000) := rfl
private theorem raw44_0 : rawBox 44 0=intv (2588161/100000000-1/19600 : ℚ) (2588161/100000000+1/19600) := rfl
private theorem raw44_1 : rawBox 44 1=intv (-4438413/100000000-1/19600 : ℚ) (-4438413/100000000+1/19600) := rfl
private theorem raw44_2 : rawBox 44 2=intv (11774367/100000000-1/19600 : ℚ) (11774367/100000000+1/19600) := rfl
private theorem raw44_3 : rawBox 44 3=intv (-856496/100000000-1/19600 : ℚ) (-856496/100000000+1/19600) := rfl
private theorem n44_0 : NB 44 0=intv (179920/1000000000 : ℚ) (180782/1000000000) := rfl
private theorem n44_1 : NB 44 1=intv (-240749/1000000000 : ℚ) (-239692/1000000000) := rfl
private theorem n44_2 : NB 44 2=intv (862905/1000000000 : ℚ) (863790/1000000000) := rfl
private theorem n44_3 : NB 44 3=intv (-139215/1000000000 : ℚ) (-138236/1000000000) := rfl
private theorem cert0_0 : Contains (NB 0 0) (metricBox 0 0) := by
  simp only [n0_0,metricBox,sumI,Fin.sum_univ_four,raw0_0,raw0_1,raw0_2,raw0_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert0_1 : Contains (NB 0 1) (metricBox 0 1) := by
  simp only [n0_1,metricBox,sumI,Fin.sum_univ_four,raw0_0,raw0_1,raw0_2,raw0_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert0_2 : Contains (NB 0 2) (metricBox 0 2) := by
  simp only [n0_2,metricBox,sumI,Fin.sum_univ_four,raw0_0,raw0_1,raw0_2,raw0_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert0_3 : Contains (NB 0 3) (metricBox 0 3) := by
  simp only [n0_3,metricBox,sumI,Fin.sum_univ_four,raw0_0,raw0_1,raw0_2,raw0_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert1_0 : Contains (NB 1 0) (metricBox 1 0) := by
  simp only [n1_0,metricBox,sumI,Fin.sum_univ_four,raw1_0,raw1_1,raw1_2,raw1_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert1_1 : Contains (NB 1 1) (metricBox 1 1) := by
  simp only [n1_1,metricBox,sumI,Fin.sum_univ_four,raw1_0,raw1_1,raw1_2,raw1_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert1_2 : Contains (NB 1 2) (metricBox 1 2) := by
  simp only [n1_2,metricBox,sumI,Fin.sum_univ_four,raw1_0,raw1_1,raw1_2,raw1_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert1_3 : Contains (NB 1 3) (metricBox 1 3) := by
  simp only [n1_3,metricBox,sumI,Fin.sum_univ_four,raw1_0,raw1_1,raw1_2,raw1_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert2_0 : Contains (NB 2 0) (metricBox 2 0) := by
  simp only [n2_0,metricBox,sumI,Fin.sum_univ_four,raw2_0,raw2_1,raw2_2,raw2_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert2_1 : Contains (NB 2 1) (metricBox 2 1) := by
  simp only [n2_1,metricBox,sumI,Fin.sum_univ_four,raw2_0,raw2_1,raw2_2,raw2_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert2_2 : Contains (NB 2 2) (metricBox 2 2) := by
  simp only [n2_2,metricBox,sumI,Fin.sum_univ_four,raw2_0,raw2_1,raw2_2,raw2_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert2_3 : Contains (NB 2 3) (metricBox 2 3) := by
  simp only [n2_3,metricBox,sumI,Fin.sum_univ_four,raw2_0,raw2_1,raw2_2,raw2_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert3_0 : Contains (NB 3 0) (metricBox 3 0) := by
  simp only [n3_0,metricBox,sumI,Fin.sum_univ_four,raw3_0,raw3_1,raw3_2,raw3_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert3_1 : Contains (NB 3 1) (metricBox 3 1) := by
  simp only [n3_1,metricBox,sumI,Fin.sum_univ_four,raw3_0,raw3_1,raw3_2,raw3_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert3_2 : Contains (NB 3 2) (metricBox 3 2) := by
  simp only [n3_2,metricBox,sumI,Fin.sum_univ_four,raw3_0,raw3_1,raw3_2,raw3_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert3_3 : Contains (NB 3 3) (metricBox 3 3) := by
  simp only [n3_3,metricBox,sumI,Fin.sum_univ_four,raw3_0,raw3_1,raw3_2,raw3_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert4_0 : Contains (NB 4 0) (metricBox 4 0) := by
  simp only [n4_0,metricBox,sumI,Fin.sum_univ_four,raw4_0,raw4_1,raw4_2,raw4_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert4_1 : Contains (NB 4 1) (metricBox 4 1) := by
  simp only [n4_1,metricBox,sumI,Fin.sum_univ_four,raw4_0,raw4_1,raw4_2,raw4_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert4_2 : Contains (NB 4 2) (metricBox 4 2) := by
  simp only [n4_2,metricBox,sumI,Fin.sum_univ_four,raw4_0,raw4_1,raw4_2,raw4_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert4_3 : Contains (NB 4 3) (metricBox 4 3) := by
  simp only [n4_3,metricBox,sumI,Fin.sum_univ_four,raw4_0,raw4_1,raw4_2,raw4_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert5_0 : Contains (NB 5 0) (metricBox 5 0) := by
  simp only [n5_0,metricBox,sumI,Fin.sum_univ_four,raw5_0,raw5_1,raw5_2,raw5_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert5_1 : Contains (NB 5 1) (metricBox 5 1) := by
  simp only [n5_1,metricBox,sumI,Fin.sum_univ_four,raw5_0,raw5_1,raw5_2,raw5_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert5_2 : Contains (NB 5 2) (metricBox 5 2) := by
  simp only [n5_2,metricBox,sumI,Fin.sum_univ_four,raw5_0,raw5_1,raw5_2,raw5_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert5_3 : Contains (NB 5 3) (metricBox 5 3) := by
  simp only [n5_3,metricBox,sumI,Fin.sum_univ_four,raw5_0,raw5_1,raw5_2,raw5_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert6_0 : Contains (NB 6 0) (metricBox 6 0) := by
  simp only [n6_0,metricBox,sumI,Fin.sum_univ_four,raw6_0,raw6_1,raw6_2,raw6_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert6_1 : Contains (NB 6 1) (metricBox 6 1) := by
  simp only [n6_1,metricBox,sumI,Fin.sum_univ_four,raw6_0,raw6_1,raw6_2,raw6_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert6_2 : Contains (NB 6 2) (metricBox 6 2) := by
  simp only [n6_2,metricBox,sumI,Fin.sum_univ_four,raw6_0,raw6_1,raw6_2,raw6_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert6_3 : Contains (NB 6 3) (metricBox 6 3) := by
  simp only [n6_3,metricBox,sumI,Fin.sum_univ_four,raw6_0,raw6_1,raw6_2,raw6_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert7_0 : Contains (NB 7 0) (metricBox 7 0) := by
  simp only [n7_0,metricBox,sumI,Fin.sum_univ_four,raw7_0,raw7_1,raw7_2,raw7_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert7_1 : Contains (NB 7 1) (metricBox 7 1) := by
  simp only [n7_1,metricBox,sumI,Fin.sum_univ_four,raw7_0,raw7_1,raw7_2,raw7_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert7_2 : Contains (NB 7 2) (metricBox 7 2) := by
  simp only [n7_2,metricBox,sumI,Fin.sum_univ_four,raw7_0,raw7_1,raw7_2,raw7_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert7_3 : Contains (NB 7 3) (metricBox 7 3) := by
  simp only [n7_3,metricBox,sumI,Fin.sum_univ_four,raw7_0,raw7_1,raw7_2,raw7_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert8_0 : Contains (NB 8 0) (metricBox 8 0) := by
  simp only [n8_0,metricBox,sumI,Fin.sum_univ_four,raw8_0,raw8_1,raw8_2,raw8_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert8_1 : Contains (NB 8 1) (metricBox 8 1) := by
  simp only [n8_1,metricBox,sumI,Fin.sum_univ_four,raw8_0,raw8_1,raw8_2,raw8_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert8_2 : Contains (NB 8 2) (metricBox 8 2) := by
  simp only [n8_2,metricBox,sumI,Fin.sum_univ_four,raw8_0,raw8_1,raw8_2,raw8_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert8_3 : Contains (NB 8 3) (metricBox 8 3) := by
  simp only [n8_3,metricBox,sumI,Fin.sum_univ_four,raw8_0,raw8_1,raw8_2,raw8_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert9_0 : Contains (NB 9 0) (metricBox 9 0) := by
  simp only [n9_0,metricBox,sumI,Fin.sum_univ_four,raw9_0,raw9_1,raw9_2,raw9_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert9_1 : Contains (NB 9 1) (metricBox 9 1) := by
  simp only [n9_1,metricBox,sumI,Fin.sum_univ_four,raw9_0,raw9_1,raw9_2,raw9_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert9_2 : Contains (NB 9 2) (metricBox 9 2) := by
  simp only [n9_2,metricBox,sumI,Fin.sum_univ_four,raw9_0,raw9_1,raw9_2,raw9_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert9_3 : Contains (NB 9 3) (metricBox 9 3) := by
  simp only [n9_3,metricBox,sumI,Fin.sum_univ_four,raw9_0,raw9_1,raw9_2,raw9_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert10_0 : Contains (NB 10 0) (metricBox 10 0) := by
  simp only [n10_0,metricBox,sumI,Fin.sum_univ_four,raw10_0,raw10_1,raw10_2,raw10_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert10_1 : Contains (NB 10 1) (metricBox 10 1) := by
  simp only [n10_1,metricBox,sumI,Fin.sum_univ_four,raw10_0,raw10_1,raw10_2,raw10_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert10_2 : Contains (NB 10 2) (metricBox 10 2) := by
  simp only [n10_2,metricBox,sumI,Fin.sum_univ_four,raw10_0,raw10_1,raw10_2,raw10_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert10_3 : Contains (NB 10 3) (metricBox 10 3) := by
  simp only [n10_3,metricBox,sumI,Fin.sum_univ_four,raw10_0,raw10_1,raw10_2,raw10_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert11_0 : Contains (NB 11 0) (metricBox 11 0) := by
  simp only [n11_0,metricBox,sumI,Fin.sum_univ_four,raw11_0,raw11_1,raw11_2,raw11_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert11_1 : Contains (NB 11 1) (metricBox 11 1) := by
  simp only [n11_1,metricBox,sumI,Fin.sum_univ_four,raw11_0,raw11_1,raw11_2,raw11_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert11_2 : Contains (NB 11 2) (metricBox 11 2) := by
  simp only [n11_2,metricBox,sumI,Fin.sum_univ_four,raw11_0,raw11_1,raw11_2,raw11_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert11_3 : Contains (NB 11 3) (metricBox 11 3) := by
  simp only [n11_3,metricBox,sumI,Fin.sum_univ_four,raw11_0,raw11_1,raw11_2,raw11_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert12_0 : Contains (NB 12 0) (metricBox 12 0) := by
  simp only [n12_0,metricBox,sumI,Fin.sum_univ_four,raw12_0,raw12_1,raw12_2,raw12_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert12_1 : Contains (NB 12 1) (metricBox 12 1) := by
  simp only [n12_1,metricBox,sumI,Fin.sum_univ_four,raw12_0,raw12_1,raw12_2,raw12_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert12_2 : Contains (NB 12 2) (metricBox 12 2) := by
  simp only [n12_2,metricBox,sumI,Fin.sum_univ_four,raw12_0,raw12_1,raw12_2,raw12_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert12_3 : Contains (NB 12 3) (metricBox 12 3) := by
  simp only [n12_3,metricBox,sumI,Fin.sum_univ_four,raw12_0,raw12_1,raw12_2,raw12_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert13_0 : Contains (NB 13 0) (metricBox 13 0) := by
  simp only [n13_0,metricBox,sumI,Fin.sum_univ_four,raw13_0,raw13_1,raw13_2,raw13_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert13_1 : Contains (NB 13 1) (metricBox 13 1) := by
  simp only [n13_1,metricBox,sumI,Fin.sum_univ_four,raw13_0,raw13_1,raw13_2,raw13_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert13_2 : Contains (NB 13 2) (metricBox 13 2) := by
  simp only [n13_2,metricBox,sumI,Fin.sum_univ_four,raw13_0,raw13_1,raw13_2,raw13_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert13_3 : Contains (NB 13 3) (metricBox 13 3) := by
  simp only [n13_3,metricBox,sumI,Fin.sum_univ_four,raw13_0,raw13_1,raw13_2,raw13_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert14_0 : Contains (NB 14 0) (metricBox 14 0) := by
  simp only [n14_0,metricBox,sumI,Fin.sum_univ_four,raw14_0,raw14_1,raw14_2,raw14_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert14_1 : Contains (NB 14 1) (metricBox 14 1) := by
  simp only [n14_1,metricBox,sumI,Fin.sum_univ_four,raw14_0,raw14_1,raw14_2,raw14_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert14_2 : Contains (NB 14 2) (metricBox 14 2) := by
  simp only [n14_2,metricBox,sumI,Fin.sum_univ_four,raw14_0,raw14_1,raw14_2,raw14_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert14_3 : Contains (NB 14 3) (metricBox 14 3) := by
  simp only [n14_3,metricBox,sumI,Fin.sum_univ_four,raw14_0,raw14_1,raw14_2,raw14_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert15_0 : Contains (NB 15 0) (metricBox 15 0) := by
  simp only [n15_0,metricBox,sumI,Fin.sum_univ_four,raw15_0,raw15_1,raw15_2,raw15_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert15_1 : Contains (NB 15 1) (metricBox 15 1) := by
  simp only [n15_1,metricBox,sumI,Fin.sum_univ_four,raw15_0,raw15_1,raw15_2,raw15_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert15_2 : Contains (NB 15 2) (metricBox 15 2) := by
  simp only [n15_2,metricBox,sumI,Fin.sum_univ_four,raw15_0,raw15_1,raw15_2,raw15_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert15_3 : Contains (NB 15 3) (metricBox 15 3) := by
  simp only [n15_3,metricBox,sumI,Fin.sum_univ_four,raw15_0,raw15_1,raw15_2,raw15_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert16_0 : Contains (NB 16 0) (metricBox 16 0) := by
  simp only [n16_0,metricBox,sumI,Fin.sum_univ_four,raw16_0,raw16_1,raw16_2,raw16_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert16_1 : Contains (NB 16 1) (metricBox 16 1) := by
  simp only [n16_1,metricBox,sumI,Fin.sum_univ_four,raw16_0,raw16_1,raw16_2,raw16_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert16_2 : Contains (NB 16 2) (metricBox 16 2) := by
  simp only [n16_2,metricBox,sumI,Fin.sum_univ_four,raw16_0,raw16_1,raw16_2,raw16_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert16_3 : Contains (NB 16 3) (metricBox 16 3) := by
  simp only [n16_3,metricBox,sumI,Fin.sum_univ_four,raw16_0,raw16_1,raw16_2,raw16_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert17_0 : Contains (NB 17 0) (metricBox 17 0) := by
  simp only [n17_0,metricBox,sumI,Fin.sum_univ_four,raw17_0,raw17_1,raw17_2,raw17_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert17_1 : Contains (NB 17 1) (metricBox 17 1) := by
  simp only [n17_1,metricBox,sumI,Fin.sum_univ_four,raw17_0,raw17_1,raw17_2,raw17_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert17_2 : Contains (NB 17 2) (metricBox 17 2) := by
  simp only [n17_2,metricBox,sumI,Fin.sum_univ_four,raw17_0,raw17_1,raw17_2,raw17_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert17_3 : Contains (NB 17 3) (metricBox 17 3) := by
  simp only [n17_3,metricBox,sumI,Fin.sum_univ_four,raw17_0,raw17_1,raw17_2,raw17_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert18_0 : Contains (NB 18 0) (metricBox 18 0) := by
  simp only [n18_0,metricBox,sumI,Fin.sum_univ_four,raw18_0,raw18_1,raw18_2,raw18_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert18_1 : Contains (NB 18 1) (metricBox 18 1) := by
  simp only [n18_1,metricBox,sumI,Fin.sum_univ_four,raw18_0,raw18_1,raw18_2,raw18_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert18_2 : Contains (NB 18 2) (metricBox 18 2) := by
  simp only [n18_2,metricBox,sumI,Fin.sum_univ_four,raw18_0,raw18_1,raw18_2,raw18_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert18_3 : Contains (NB 18 3) (metricBox 18 3) := by
  simp only [n18_3,metricBox,sumI,Fin.sum_univ_four,raw18_0,raw18_1,raw18_2,raw18_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert19_0 : Contains (NB 19 0) (metricBox 19 0) := by
  simp only [n19_0,metricBox,sumI,Fin.sum_univ_four,raw19_0,raw19_1,raw19_2,raw19_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert19_1 : Contains (NB 19 1) (metricBox 19 1) := by
  simp only [n19_1,metricBox,sumI,Fin.sum_univ_four,raw19_0,raw19_1,raw19_2,raw19_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert19_2 : Contains (NB 19 2) (metricBox 19 2) := by
  simp only [n19_2,metricBox,sumI,Fin.sum_univ_four,raw19_0,raw19_1,raw19_2,raw19_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert19_3 : Contains (NB 19 3) (metricBox 19 3) := by
  simp only [n19_3,metricBox,sumI,Fin.sum_univ_four,raw19_0,raw19_1,raw19_2,raw19_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert20_0 : Contains (NB 20 0) (metricBox 20 0) := by
  simp only [n20_0,metricBox,sumI,Fin.sum_univ_four,raw20_0,raw20_1,raw20_2,raw20_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert20_1 : Contains (NB 20 1) (metricBox 20 1) := by
  simp only [n20_1,metricBox,sumI,Fin.sum_univ_four,raw20_0,raw20_1,raw20_2,raw20_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert20_2 : Contains (NB 20 2) (metricBox 20 2) := by
  simp only [n20_2,metricBox,sumI,Fin.sum_univ_four,raw20_0,raw20_1,raw20_2,raw20_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert20_3 : Contains (NB 20 3) (metricBox 20 3) := by
  simp only [n20_3,metricBox,sumI,Fin.sum_univ_four,raw20_0,raw20_1,raw20_2,raw20_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert21_0 : Contains (NB 21 0) (metricBox 21 0) := by
  simp only [n21_0,metricBox,sumI,Fin.sum_univ_four,raw21_0,raw21_1,raw21_2,raw21_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert21_1 : Contains (NB 21 1) (metricBox 21 1) := by
  simp only [n21_1,metricBox,sumI,Fin.sum_univ_four,raw21_0,raw21_1,raw21_2,raw21_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert21_2 : Contains (NB 21 2) (metricBox 21 2) := by
  simp only [n21_2,metricBox,sumI,Fin.sum_univ_four,raw21_0,raw21_1,raw21_2,raw21_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert21_3 : Contains (NB 21 3) (metricBox 21 3) := by
  simp only [n21_3,metricBox,sumI,Fin.sum_univ_four,raw21_0,raw21_1,raw21_2,raw21_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert22_0 : Contains (NB 22 0) (metricBox 22 0) := by
  simp only [n22_0,metricBox,sumI,Fin.sum_univ_four,raw22_0,raw22_1,raw22_2,raw22_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert22_1 : Contains (NB 22 1) (metricBox 22 1) := by
  simp only [n22_1,metricBox,sumI,Fin.sum_univ_four,raw22_0,raw22_1,raw22_2,raw22_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert22_2 : Contains (NB 22 2) (metricBox 22 2) := by
  simp only [n22_2,metricBox,sumI,Fin.sum_univ_four,raw22_0,raw22_1,raw22_2,raw22_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert22_3 : Contains (NB 22 3) (metricBox 22 3) := by
  simp only [n22_3,metricBox,sumI,Fin.sum_univ_four,raw22_0,raw22_1,raw22_2,raw22_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert23_0 : Contains (NB 23 0) (metricBox 23 0) := by
  simp only [n23_0,metricBox,sumI,Fin.sum_univ_four,raw23_0,raw23_1,raw23_2,raw23_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert23_1 : Contains (NB 23 1) (metricBox 23 1) := by
  simp only [n23_1,metricBox,sumI,Fin.sum_univ_four,raw23_0,raw23_1,raw23_2,raw23_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert23_2 : Contains (NB 23 2) (metricBox 23 2) := by
  simp only [n23_2,metricBox,sumI,Fin.sum_univ_four,raw23_0,raw23_1,raw23_2,raw23_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert23_3 : Contains (NB 23 3) (metricBox 23 3) := by
  simp only [n23_3,metricBox,sumI,Fin.sum_univ_four,raw23_0,raw23_1,raw23_2,raw23_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert24_0 : Contains (NB 24 0) (metricBox 24 0) := by
  simp only [n24_0,metricBox,sumI,Fin.sum_univ_four,raw24_0,raw24_1,raw24_2,raw24_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert24_1 : Contains (NB 24 1) (metricBox 24 1) := by
  simp only [n24_1,metricBox,sumI,Fin.sum_univ_four,raw24_0,raw24_1,raw24_2,raw24_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert24_2 : Contains (NB 24 2) (metricBox 24 2) := by
  simp only [n24_2,metricBox,sumI,Fin.sum_univ_four,raw24_0,raw24_1,raw24_2,raw24_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert24_3 : Contains (NB 24 3) (metricBox 24 3) := by
  simp only [n24_3,metricBox,sumI,Fin.sum_univ_four,raw24_0,raw24_1,raw24_2,raw24_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert25_0 : Contains (NB 25 0) (metricBox 25 0) := by
  simp only [n25_0,metricBox,sumI,Fin.sum_univ_four,raw25_0,raw25_1,raw25_2,raw25_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert25_1 : Contains (NB 25 1) (metricBox 25 1) := by
  simp only [n25_1,metricBox,sumI,Fin.sum_univ_four,raw25_0,raw25_1,raw25_2,raw25_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert25_2 : Contains (NB 25 2) (metricBox 25 2) := by
  simp only [n25_2,metricBox,sumI,Fin.sum_univ_four,raw25_0,raw25_1,raw25_2,raw25_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert25_3 : Contains (NB 25 3) (metricBox 25 3) := by
  simp only [n25_3,metricBox,sumI,Fin.sum_univ_four,raw25_0,raw25_1,raw25_2,raw25_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert26_0 : Contains (NB 26 0) (metricBox 26 0) := by
  simp only [n26_0,metricBox,sumI,Fin.sum_univ_four,raw26_0,raw26_1,raw26_2,raw26_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert26_1 : Contains (NB 26 1) (metricBox 26 1) := by
  simp only [n26_1,metricBox,sumI,Fin.sum_univ_four,raw26_0,raw26_1,raw26_2,raw26_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert26_2 : Contains (NB 26 2) (metricBox 26 2) := by
  simp only [n26_2,metricBox,sumI,Fin.sum_univ_four,raw26_0,raw26_1,raw26_2,raw26_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert26_3 : Contains (NB 26 3) (metricBox 26 3) := by
  simp only [n26_3,metricBox,sumI,Fin.sum_univ_four,raw26_0,raw26_1,raw26_2,raw26_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert27_0 : Contains (NB 27 0) (metricBox 27 0) := by
  simp only [n27_0,metricBox,sumI,Fin.sum_univ_four,raw27_0,raw27_1,raw27_2,raw27_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert27_1 : Contains (NB 27 1) (metricBox 27 1) := by
  simp only [n27_1,metricBox,sumI,Fin.sum_univ_four,raw27_0,raw27_1,raw27_2,raw27_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert27_2 : Contains (NB 27 2) (metricBox 27 2) := by
  simp only [n27_2,metricBox,sumI,Fin.sum_univ_four,raw27_0,raw27_1,raw27_2,raw27_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert27_3 : Contains (NB 27 3) (metricBox 27 3) := by
  simp only [n27_3,metricBox,sumI,Fin.sum_univ_four,raw27_0,raw27_1,raw27_2,raw27_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert28_0 : Contains (NB 28 0) (metricBox 28 0) := by
  simp only [n28_0,metricBox,sumI,Fin.sum_univ_four,raw28_0,raw28_1,raw28_2,raw28_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert28_1 : Contains (NB 28 1) (metricBox 28 1) := by
  simp only [n28_1,metricBox,sumI,Fin.sum_univ_four,raw28_0,raw28_1,raw28_2,raw28_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert28_2 : Contains (NB 28 2) (metricBox 28 2) := by
  simp only [n28_2,metricBox,sumI,Fin.sum_univ_four,raw28_0,raw28_1,raw28_2,raw28_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert28_3 : Contains (NB 28 3) (metricBox 28 3) := by
  simp only [n28_3,metricBox,sumI,Fin.sum_univ_four,raw28_0,raw28_1,raw28_2,raw28_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert29_0 : Contains (NB 29 0) (metricBox 29 0) := by
  simp only [n29_0,metricBox,sumI,Fin.sum_univ_four,raw29_0,raw29_1,raw29_2,raw29_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert29_1 : Contains (NB 29 1) (metricBox 29 1) := by
  simp only [n29_1,metricBox,sumI,Fin.sum_univ_four,raw29_0,raw29_1,raw29_2,raw29_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert29_2 : Contains (NB 29 2) (metricBox 29 2) := by
  simp only [n29_2,metricBox,sumI,Fin.sum_univ_four,raw29_0,raw29_1,raw29_2,raw29_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert29_3 : Contains (NB 29 3) (metricBox 29 3) := by
  simp only [n29_3,metricBox,sumI,Fin.sum_univ_four,raw29_0,raw29_1,raw29_2,raw29_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert30_0 : Contains (NB 30 0) (metricBox 30 0) := by
  simp only [n30_0,metricBox,sumI,Fin.sum_univ_four,raw30_0,raw30_1,raw30_2,raw30_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert30_1 : Contains (NB 30 1) (metricBox 30 1) := by
  simp only [n30_1,metricBox,sumI,Fin.sum_univ_four,raw30_0,raw30_1,raw30_2,raw30_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert30_2 : Contains (NB 30 2) (metricBox 30 2) := by
  simp only [n30_2,metricBox,sumI,Fin.sum_univ_four,raw30_0,raw30_1,raw30_2,raw30_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert30_3 : Contains (NB 30 3) (metricBox 30 3) := by
  simp only [n30_3,metricBox,sumI,Fin.sum_univ_four,raw30_0,raw30_1,raw30_2,raw30_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert31_0 : Contains (NB 31 0) (metricBox 31 0) := by
  simp only [n31_0,metricBox,sumI,Fin.sum_univ_four,raw31_0,raw31_1,raw31_2,raw31_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert31_1 : Contains (NB 31 1) (metricBox 31 1) := by
  simp only [n31_1,metricBox,sumI,Fin.sum_univ_four,raw31_0,raw31_1,raw31_2,raw31_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert31_2 : Contains (NB 31 2) (metricBox 31 2) := by
  simp only [n31_2,metricBox,sumI,Fin.sum_univ_four,raw31_0,raw31_1,raw31_2,raw31_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert31_3 : Contains (NB 31 3) (metricBox 31 3) := by
  simp only [n31_3,metricBox,sumI,Fin.sum_univ_four,raw31_0,raw31_1,raw31_2,raw31_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert32_0 : Contains (NB 32 0) (metricBox 32 0) := by
  simp only [n32_0,metricBox,sumI,Fin.sum_univ_four,raw32_0,raw32_1,raw32_2,raw32_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert32_1 : Contains (NB 32 1) (metricBox 32 1) := by
  simp only [n32_1,metricBox,sumI,Fin.sum_univ_four,raw32_0,raw32_1,raw32_2,raw32_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert32_2 : Contains (NB 32 2) (metricBox 32 2) := by
  simp only [n32_2,metricBox,sumI,Fin.sum_univ_four,raw32_0,raw32_1,raw32_2,raw32_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert32_3 : Contains (NB 32 3) (metricBox 32 3) := by
  simp only [n32_3,metricBox,sumI,Fin.sum_univ_four,raw32_0,raw32_1,raw32_2,raw32_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert33_0 : Contains (NB 33 0) (metricBox 33 0) := by
  simp only [n33_0,metricBox,sumI,Fin.sum_univ_four,raw33_0,raw33_1,raw33_2,raw33_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert33_1 : Contains (NB 33 1) (metricBox 33 1) := by
  simp only [n33_1,metricBox,sumI,Fin.sum_univ_four,raw33_0,raw33_1,raw33_2,raw33_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert33_2 : Contains (NB 33 2) (metricBox 33 2) := by
  simp only [n33_2,metricBox,sumI,Fin.sum_univ_four,raw33_0,raw33_1,raw33_2,raw33_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert33_3 : Contains (NB 33 3) (metricBox 33 3) := by
  simp only [n33_3,metricBox,sumI,Fin.sum_univ_four,raw33_0,raw33_1,raw33_2,raw33_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert34_0 : Contains (NB 34 0) (metricBox 34 0) := by
  simp only [n34_0,metricBox,sumI,Fin.sum_univ_four,raw34_0,raw34_1,raw34_2,raw34_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert34_1 : Contains (NB 34 1) (metricBox 34 1) := by
  simp only [n34_1,metricBox,sumI,Fin.sum_univ_four,raw34_0,raw34_1,raw34_2,raw34_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert34_2 : Contains (NB 34 2) (metricBox 34 2) := by
  simp only [n34_2,metricBox,sumI,Fin.sum_univ_four,raw34_0,raw34_1,raw34_2,raw34_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert34_3 : Contains (NB 34 3) (metricBox 34 3) := by
  simp only [n34_3,metricBox,sumI,Fin.sum_univ_four,raw34_0,raw34_1,raw34_2,raw34_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert35_0 : Contains (NB 35 0) (metricBox 35 0) := by
  simp only [n35_0,metricBox,sumI,Fin.sum_univ_four,raw35_0,raw35_1,raw35_2,raw35_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert35_1 : Contains (NB 35 1) (metricBox 35 1) := by
  simp only [n35_1,metricBox,sumI,Fin.sum_univ_four,raw35_0,raw35_1,raw35_2,raw35_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert35_2 : Contains (NB 35 2) (metricBox 35 2) := by
  simp only [n35_2,metricBox,sumI,Fin.sum_univ_four,raw35_0,raw35_1,raw35_2,raw35_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert35_3 : Contains (NB 35 3) (metricBox 35 3) := by
  simp only [n35_3,metricBox,sumI,Fin.sum_univ_four,raw35_0,raw35_1,raw35_2,raw35_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert36_0 : Contains (NB 36 0) (metricBox 36 0) := by
  simp only [n36_0,metricBox,sumI,Fin.sum_univ_four,raw36_0,raw36_1,raw36_2,raw36_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert36_1 : Contains (NB 36 1) (metricBox 36 1) := by
  simp only [n36_1,metricBox,sumI,Fin.sum_univ_four,raw36_0,raw36_1,raw36_2,raw36_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert36_2 : Contains (NB 36 2) (metricBox 36 2) := by
  simp only [n36_2,metricBox,sumI,Fin.sum_univ_four,raw36_0,raw36_1,raw36_2,raw36_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert36_3 : Contains (NB 36 3) (metricBox 36 3) := by
  simp only [n36_3,metricBox,sumI,Fin.sum_univ_four,raw36_0,raw36_1,raw36_2,raw36_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert37_0 : Contains (NB 37 0) (metricBox 37 0) := by
  simp only [n37_0,metricBox,sumI,Fin.sum_univ_four,raw37_0,raw37_1,raw37_2,raw37_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert37_1 : Contains (NB 37 1) (metricBox 37 1) := by
  simp only [n37_1,metricBox,sumI,Fin.sum_univ_four,raw37_0,raw37_1,raw37_2,raw37_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert37_2 : Contains (NB 37 2) (metricBox 37 2) := by
  simp only [n37_2,metricBox,sumI,Fin.sum_univ_four,raw37_0,raw37_1,raw37_2,raw37_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert37_3 : Contains (NB 37 3) (metricBox 37 3) := by
  simp only [n37_3,metricBox,sumI,Fin.sum_univ_four,raw37_0,raw37_1,raw37_2,raw37_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert38_0 : Contains (NB 38 0) (metricBox 38 0) := by
  simp only [n38_0,metricBox,sumI,Fin.sum_univ_four,raw38_0,raw38_1,raw38_2,raw38_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert38_1 : Contains (NB 38 1) (metricBox 38 1) := by
  simp only [n38_1,metricBox,sumI,Fin.sum_univ_four,raw38_0,raw38_1,raw38_2,raw38_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert38_2 : Contains (NB 38 2) (metricBox 38 2) := by
  simp only [n38_2,metricBox,sumI,Fin.sum_univ_four,raw38_0,raw38_1,raw38_2,raw38_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert38_3 : Contains (NB 38 3) (metricBox 38 3) := by
  simp only [n38_3,metricBox,sumI,Fin.sum_univ_four,raw38_0,raw38_1,raw38_2,raw38_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert39_0 : Contains (NB 39 0) (metricBox 39 0) := by
  simp only [n39_0,metricBox,sumI,Fin.sum_univ_four,raw39_0,raw39_1,raw39_2,raw39_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert39_1 : Contains (NB 39 1) (metricBox 39 1) := by
  simp only [n39_1,metricBox,sumI,Fin.sum_univ_four,raw39_0,raw39_1,raw39_2,raw39_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert39_2 : Contains (NB 39 2) (metricBox 39 2) := by
  simp only [n39_2,metricBox,sumI,Fin.sum_univ_four,raw39_0,raw39_1,raw39_2,raw39_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert39_3 : Contains (NB 39 3) (metricBox 39 3) := by
  simp only [n39_3,metricBox,sumI,Fin.sum_univ_four,raw39_0,raw39_1,raw39_2,raw39_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert40_0 : Contains (NB 40 0) (metricBox 40 0) := by
  simp only [n40_0,metricBox,sumI,Fin.sum_univ_four,raw40_0,raw40_1,raw40_2,raw40_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert40_1 : Contains (NB 40 1) (metricBox 40 1) := by
  simp only [n40_1,metricBox,sumI,Fin.sum_univ_four,raw40_0,raw40_1,raw40_2,raw40_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert40_2 : Contains (NB 40 2) (metricBox 40 2) := by
  simp only [n40_2,metricBox,sumI,Fin.sum_univ_four,raw40_0,raw40_1,raw40_2,raw40_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert40_3 : Contains (NB 40 3) (metricBox 40 3) := by
  simp only [n40_3,metricBox,sumI,Fin.sum_univ_four,raw40_0,raw40_1,raw40_2,raw40_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert41_0 : Contains (NB 41 0) (metricBox 41 0) := by
  simp only [n41_0,metricBox,sumI,Fin.sum_univ_four,raw41_0,raw41_1,raw41_2,raw41_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert41_1 : Contains (NB 41 1) (metricBox 41 1) := by
  simp only [n41_1,metricBox,sumI,Fin.sum_univ_four,raw41_0,raw41_1,raw41_2,raw41_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert41_2 : Contains (NB 41 2) (metricBox 41 2) := by
  simp only [n41_2,metricBox,sumI,Fin.sum_univ_four,raw41_0,raw41_1,raw41_2,raw41_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert41_3 : Contains (NB 41 3) (metricBox 41 3) := by
  simp only [n41_3,metricBox,sumI,Fin.sum_univ_four,raw41_0,raw41_1,raw41_2,raw41_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert42_0 : Contains (NB 42 0) (metricBox 42 0) := by
  simp only [n42_0,metricBox,sumI,Fin.sum_univ_four,raw42_0,raw42_1,raw42_2,raw42_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert42_1 : Contains (NB 42 1) (metricBox 42 1) := by
  simp only [n42_1,metricBox,sumI,Fin.sum_univ_four,raw42_0,raw42_1,raw42_2,raw42_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert42_2 : Contains (NB 42 2) (metricBox 42 2) := by
  simp only [n42_2,metricBox,sumI,Fin.sum_univ_four,raw42_0,raw42_1,raw42_2,raw42_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert42_3 : Contains (NB 42 3) (metricBox 42 3) := by
  simp only [n42_3,metricBox,sumI,Fin.sum_univ_four,raw42_0,raw42_1,raw42_2,raw42_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert43_0 : Contains (NB 43 0) (metricBox 43 0) := by
  simp only [n43_0,metricBox,sumI,Fin.sum_univ_four,raw43_0,raw43_1,raw43_2,raw43_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert43_1 : Contains (NB 43 1) (metricBox 43 1) := by
  simp only [n43_1,metricBox,sumI,Fin.sum_univ_four,raw43_0,raw43_1,raw43_2,raw43_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert43_2 : Contains (NB 43 2) (metricBox 43 2) := by
  simp only [n43_2,metricBox,sumI,Fin.sum_univ_four,raw43_0,raw43_1,raw43_2,raw43_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert43_3 : Contains (NB 43 3) (metricBox 43 3) := by
  simp only [n43_3,metricBox,sumI,Fin.sum_univ_four,raw43_0,raw43_1,raw43_2,raw43_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert44_0 : Contains (NB 44 0) (metricBox 44 0) := by
  simp only [n44_0,metricBox,sumI,Fin.sum_univ_four,raw44_0,raw44_1,raw44_2,raw44_3,r0_0,r1_0,r2_0,r3_0]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert44_1 : Contains (NB 44 1) (metricBox 44 1) := by
  simp only [n44_1,metricBox,sumI,Fin.sum_univ_four,raw44_0,raw44_1,raw44_2,raw44_3,r0_1,r1_1,r2_1,r3_1]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert44_2 : Contains (NB 44 2) (metricBox 44 2) := by
  simp only [n44_2,metricBox,sumI,Fin.sum_univ_four,raw44_0,raw44_1,raw44_2,raw44_3,r0_2,r1_2,r2_2,r3_2]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem cert44_3 : Contains (NB 44 3) (metricBox 44 3) := by
  simp only [n44_3,metricBox,sumI,Fin.sum_univ_four,raw44_0,raw44_1,raw44_2,raw44_3,r0_3,r1_3,r2_3,r3_3]
  norm_num [Contains,RatInterval.mul,ofRat,intv]

theorem NB_contains (e : Fin 45) (a : Fin 4) : Contains (NB e a) (metricBox e a) := by
  fin_cases e <;> fin_cases a
  · exact cert0_0
  · exact cert0_1
  · exact cert0_2
  · exact cert0_3
  · exact cert1_0
  · exact cert1_1
  · exact cert1_2
  · exact cert1_3
  · exact cert2_0
  · exact cert2_1
  · exact cert2_2
  · exact cert2_3
  · exact cert3_0
  · exact cert3_1
  · exact cert3_2
  · exact cert3_3
  · exact cert4_0
  · exact cert4_1
  · exact cert4_2
  · exact cert4_3
  · exact cert5_0
  · exact cert5_1
  · exact cert5_2
  · exact cert5_3
  · exact cert6_0
  · exact cert6_1
  · exact cert6_2
  · exact cert6_3
  · exact cert7_0
  · exact cert7_1
  · exact cert7_2
  · exact cert7_3
  · exact cert8_0
  · exact cert8_1
  · exact cert8_2
  · exact cert8_3
  · exact cert9_0
  · exact cert9_1
  · exact cert9_2
  · exact cert9_3
  · exact cert10_0
  · exact cert10_1
  · exact cert10_2
  · exact cert10_3
  · exact cert11_0
  · exact cert11_1
  · exact cert11_2
  · exact cert11_3
  · exact cert12_0
  · exact cert12_1
  · exact cert12_2
  · exact cert12_3
  · exact cert13_0
  · exact cert13_1
  · exact cert13_2
  · exact cert13_3
  · exact cert14_0
  · exact cert14_1
  · exact cert14_2
  · exact cert14_3
  · exact cert15_0
  · exact cert15_1
  · exact cert15_2
  · exact cert15_3
  · exact cert16_0
  · exact cert16_1
  · exact cert16_2
  · exact cert16_3
  · exact cert17_0
  · exact cert17_1
  · exact cert17_2
  · exact cert17_3
  · exact cert18_0
  · exact cert18_1
  · exact cert18_2
  · exact cert18_3
  · exact cert19_0
  · exact cert19_1
  · exact cert19_2
  · exact cert19_3
  · exact cert20_0
  · exact cert20_1
  · exact cert20_2
  · exact cert20_3
  · exact cert21_0
  · exact cert21_1
  · exact cert21_2
  · exact cert21_3
  · exact cert22_0
  · exact cert22_1
  · exact cert22_2
  · exact cert22_3
  · exact cert23_0
  · exact cert23_1
  · exact cert23_2
  · exact cert23_3
  · exact cert24_0
  · exact cert24_1
  · exact cert24_2
  · exact cert24_3
  · exact cert25_0
  · exact cert25_1
  · exact cert25_2
  · exact cert25_3
  · exact cert26_0
  · exact cert26_1
  · exact cert26_2
  · exact cert26_3
  · exact cert27_0
  · exact cert27_1
  · exact cert27_2
  · exact cert27_3
  · exact cert28_0
  · exact cert28_1
  · exact cert28_2
  · exact cert28_3
  · exact cert29_0
  · exact cert29_1
  · exact cert29_2
  · exact cert29_3
  · exact cert30_0
  · exact cert30_1
  · exact cert30_2
  · exact cert30_3
  · exact cert31_0
  · exact cert31_1
  · exact cert31_2
  · exact cert31_3
  · exact cert32_0
  · exact cert32_1
  · exact cert32_2
  · exact cert32_3
  · exact cert33_0
  · exact cert33_1
  · exact cert33_2
  · exact cert33_3
  · exact cert34_0
  · exact cert34_1
  · exact cert34_2
  · exact cert34_3
  · exact cert35_0
  · exact cert35_1
  · exact cert35_2
  · exact cert35_3
  · exact cert36_0
  · exact cert36_1
  · exact cert36_2
  · exact cert36_3
  · exact cert37_0
  · exact cert37_1
  · exact cert37_2
  · exact cert37_3
  · exact cert38_0
  · exact cert38_1
  · exact cert38_2
  · exact cert38_3
  · exact cert39_0
  · exact cert39_1
  · exact cert39_2
  · exact cert39_3
  · exact cert40_0
  · exact cert40_1
  · exact cert40_2
  · exact cert40_3
  · exact cert41_0
  · exact cert41_1
  · exact cert41_2
  · exact cert41_3
  · exact cert42_0
  · exact cert42_1
  · exact cert42_2
  · exact cert42_3
  · exact cert43_0
  · exact cert43_1
  · exact cert43_2
  · exact cert43_3
  · exact cert44_0
  · exact cert44_1
  · exact cert44_2
  · exact cert44_3

theorem NB_mem (e : Fin 45) (a : Fin 4) : (NB e a).Mem (sourceN e a) :=
  mem_of_contains (NB_contains e a) (metricBox_mem e a)

end
end N11Formalization.SourceFineRelativeNIntervals
#check @N11Formalization.SourceFineRelativeNIntervals.NB_mem
#print axioms N11Formalization.SourceFineRelativeNIntervals.NB_mem
