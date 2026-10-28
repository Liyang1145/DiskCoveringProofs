import N11Formalization.SourceRelativeMetric
import N11Formalization.SourceCompactStressIntervals

/-! Integer/rational outward row-norm packet for SAME transformed N and SAME
actual positive45 stress. This packet's tables require actual interval
containment and finite comparisons; no diagnostic inequality is a premise.
Real norm semantics is a subsequent consumer; coercivity is not claimed. -/
set_option autoImplicit false
namespace N11Formalization.SourceRelativeNormPacket
open N11Formalization RatInterval SourceRelativeMetric
open SourceNEnclosure SourceNColumnProposal SourceActiveMatrixIntervals
section
-- Local evaluator stack depth only; default heartbeats/kernel unchanged.
set_option maxRecDepth 10000

def NL : Fin 45 → Fin 4 → ℤ :=
 ![![219530,-380532,1180480,-234495],
   ![-1997508,-2914944,-1916544,-2168842],
   ![-1617580,-2358961,-1552462,-1756659],
   ![775252,2051571,-506081,467416],
   ![281831,-1898906,-1425940,-3071544],
   ![-940675,1764816,181172,6699589],
   ![-1729437,2538604,-382953,6407024],
   ![1360779,55130,7067274,181172],
   ![1932726,-773555,6796849,828337],
   ![2521985,6131544,-921063,2363478],
   ![2089958,6436709,55130,1764816],
   ![-1562869,-2747827,-1105799,-2007494],
   ![-681193,549206,-354865,2116636],
   ![206549,-1601352,-1878986,-2729267],
   ![264387,-1975519,-2321429,-3374863],
   ![219510,-380506,1180384,-234479],
   ![142417,-277822,811341,-175180],
   ![142431,-277840,811405,-175190],
   ![4050436,2089958,1360779,-940675],
   ![2075404,1046422,673461,-529123],
   ![2709435,1373572,886470,-676371],
   ![-2937538,-840239,2570190,2727787],
   ![-1546719,-457926,1321910,1402203],
   ![-2001150,-582842,1729769,1835319],
   ![-1753381,-2557690,-1682599,-1903989],
   ![-2517070,-3675266,-2414437,-2732515],
   ![-3445923,-5034543,-3304551,-3740229],
   ![-1429041,1748665,-695465,2142151],
   ![-1180543,1429549,-577843,1753473],
   ![-1864411,2307758,-901538,2823115],
   ![832201,-925490,633247,761967],
   ![664635,-754715,503973,607078],
   ![757179,-849031,575369,692621],
   ![-378386,598088,908662,-573422],
   ![-460802,751527,1134880,-701455],
   ![-423912,682847,1033624,-644147],
   ![1142469,1658019,-1083550,1230843],
   ![1397647,2026664,-1310815,1506196],
   ![1844782,2672620,-1709039,1988681],
   ![343485,-2487220,-2926503,-4257762],
   ![227223,-1735094,-2037132,-2960028],
   ![484902,-3402077,-4008298,-5836275],
   ![111170,-236201,661756,-151144],
   ![111180,-236215,661808,-151152],
   ![145894,-282452,827982,-177854]]

def NH : Fin 45 → Fin 4 → ℤ :=
 ![![288444,-296069,1251210,-156238],
   ![-1928594,-2830480,-1845814,-2090586],
   ![-1548666,-2274498,-1481732,-1678403],
   ![844166,2136034,-435350,545672],
   ![350745,-1814443,-1355209,-2993288],
   ![-940674,1764817,181173,6699590],
   ![-1660523,2623068,-312222,6485280],
   ![1360780,55131,7067275,181173],
   ![2001640,-689092,6867579,906593],
   ![2590899,6216008,-850332,2441734],
   ![2089959,6436710,55131,1764817],
   ![-1493955,-2663364,-1035069,-1929238],
   ![-612279,633669,-284135,2194892],
   ![275463,-1516889,-1808256,-2651011],
   ![333301,-1891056,-2250699,-3296607],
   ![288424,-296043,1251115,-156223],
   ![211332,-193359,882071,-96924],
   ![211345,-193377,882135,-96934],
   ![4050437,2089959,1360780,-940674],
   ![2144318,1130885,744192,-450867],
   ![2778350,1458035,957200,-598114],
   ![-2868624,-755776,2640920,2806043],
   ![-1477805,-373463,1392641,1480459],
   ![-1932236,-498379,1800499,1913575],
   ![-1684467,-2473227,-1611868,-1825733],
   ![-2448156,-3590803,-2343707,-2654259],
   ![-3377009,-4950080,-3233821,-3661972],
   ![-1360127,1833128,-624734,2220407],
   ![-1111629,1514012,-507112,1831729],
   ![-1795497,2392221,-830808,2901371],
   ![901115,-841027,703978,840223],
   ![733549,-670251,574704,685334],
   ![826093,-764568,646100,770877],
   ![-309472,682551,979393,-495166],
   ![-391888,835990,1205610,-623199],
   ![-354998,767310,1104355,-565891],
   ![1211383,1742482,-1012819,1309099],
   ![1466561,2111127,-1240084,1584452],
   ![1913696,2757083,-1638308,2066937],
   ![412399,-2402757,-2855772,-4179506],
   ![296137,-1650631,-1966402,-2881772],
   ![553816,-3317613,-3937567,-5758018],
   ![180084,-151738,732486,-72888],
   ![180095,-151752,732538,-72896],
   ![214808,-197989,898713,-99598]]

def NB (e : Fin 45) (a : Fin 4) : RatInterval :=
  intv ((NL e a : ℚ)/1000000000) ((NH e a : ℚ)/1000000000)

private theorem rshape0_0 : R 0 0 = (5977389212899689600 : ℚ)/1475739525896764129280 := rfl
private theorem rshape0_1 : R 0 1 = (3084234978919466880 : ℚ)/1475739525896764129280 := rfl
private theorem rshape0_2 : R 0 2 = (2008156729907682720 : ℚ)/1475739525896764129280 := rfl
private theorem rshape0_3 : R 0 3 = (-1388190849679244160 : ℚ)/1475739525896764129280 := rfl
private theorem rshape1_0 : R 1 0 = (3084234978919466880 : ℚ)/1475739525896764129280 := rfl
private theorem rshape1_1 : R 1 1 = (9498906412506436608 : ℚ)/1475739525896764129280 := rfl
private theorem rshape1_2 : R 1 2 = (81357739426959030 : ℚ)/1475739525896764129280 := rfl
private theorem rshape1_3 : R 1 3 = (2604409099499393280 : ℚ)/1475739525896764129280 := rfl
private theorem rshape2_0 : R 2 0 = (2008156729907683008 : ℚ)/1475739525896764129280 := rfl
private theorem rshape2_1 : R 2 1 = (81357739426959498 : ℚ)/1475739525896764129280 := rfl
private theorem rshape2_2 : R 2 2 = (10429456537443393792 : ℚ)/1475739525896764129280 := rfl
private theorem rshape2_3 : R 2 3 = (267363491656565880 : ℚ)/1475739525896764129280 := rfl
private theorem rshape3_0 : R 3 0 = (-1388190849679243872 : ℚ)/1475739525896764129280 := rfl
private theorem rshape3_1 : R 3 1 = (2604409099499393280 : ℚ)/1475739525896764129280 := rfl
private theorem rshape3_2 : R 3 2 = (267363491656566096 : ℚ)/1475739525896764129280 := rfl
private theorem rshape3_3 : R 3 3 = (9886849369067412864 : ℚ)/1475739525896764129280 := rfl
private theorem rawshape0_0 : rawBox 0 0 = intv ((3644885 : ℚ)/100000000-1/245) ((3644885 : ℚ)/100000000+1/245) := rfl
private theorem nbshape0_0 : NB 0 0 = intv ((219530 : ℚ)/1000000000) ((288444 : ℚ)/1000000000) := rfl
private theorem rawshape0_1 : rawBox 0 1 = intv ((-6250581 : ℚ)/100000000-1/245) ((-6250581 : ℚ)/100000000+1/245) := rfl
private theorem nbshape0_1 : NB 0 1 = intv ((-380532 : ℚ)/1000000000) ((-296069 : ℚ)/1000000000) := rfl
private theorem rawshape0_2 : rawBox 0 2 = intv ((16581743 : ℚ)/100000000-1/245) ((16581743 : ℚ)/100000000+1/245) := rfl
private theorem nbshape0_2 : NB 0 2 = intv ((1180480 : ℚ)/1000000000) ((1251210 : ℚ)/1000000000) := rfl
private theorem rawshape0_3 : rawBox 0 3 = intv ((-1206197 : ℚ)/100000000-1/245) ((-1206197 : ℚ)/100000000+1/245) := rfl
private theorem nbshape0_3 : NB 0 3 = intv ((-234495 : ℚ)/1000000000) ((-156238 : ℚ)/1000000000) := rfl
private theorem rawshape1_0 : rawBox 1 0 = intv ((-36618202 : ℚ)/100000000-1/245) ((-36618202 : ℚ)/100000000+1/245) := rfl
private theorem nbshape1_0 : NB 1 0 = intv ((-1997508 : ℚ)/1000000000) ((-1928594 : ℚ)/1000000000) := rfl
private theorem rawshape1_1 : rawBox 1 1 = intv ((-24352353 : ℚ)/100000000-1/245) ((-24352353 : ℚ)/100000000+1/245) := rfl
private theorem nbshape1_1 : NB 1 1 = intv ((-2914944 : ℚ)/1000000000) ((-2830480 : ℚ)/1000000000) := rfl
private theorem rawshape1_2 : rawBox 1 2 = intv ((-18608115 : ℚ)/100000000-1/245) ((-18608115 : ℚ)/100000000+1/245) := rfl
private theorem nbshape1_2 : NB 1 2 = intv ((-1916544 : ℚ)/1000000000) ((-1845814 : ℚ)/1000000000) := rfl
private theorem rawshape1_3 : rawBox 1 3 = intv ((-30012064 : ℚ)/100000000-1/245) ((-30012064 : ℚ)/100000000+1/245) := rfl
private theorem nbshape1_3 : NB 1 3 = intv ((-2168842 : ℚ)/1000000000) ((-2090586 : ℚ)/1000000000) := rfl
private theorem rawshape2_0 : rawBox 2 0 = intv ((-29531141 : ℚ)/100000000-1/245) ((-29531141 : ℚ)/100000000+1/245) := rfl
private theorem nbshape2_0 : NB 2 0 = intv ((-1617580 : ℚ)/1000000000) ((-1548666 : ℚ)/1000000000) := rfl
private theorem rawshape2_1 : rawBox 2 1 = intv ((-19639216 : ℚ)/100000000-1/245) ((-19639216 : ℚ)/100000000+1/245) := rfl
private theorem nbshape2_1 : NB 2 1 = intv ((-2358961 : ℚ)/1000000000) ((-2274498 : ℚ)/1000000000) := rfl
private theorem rawshape2_2 : rawBox 2 2 = intv ((-15006714 : ℚ)/100000000-1/245) ((-15006714 : ℚ)/100000000+1/245) := rfl
private theorem nbshape2_2 : NB 2 2 = intv ((-1552462 : ℚ)/1000000000) ((-1481732 : ℚ)/1000000000) := rfl
private theorem rawshape2_3 : rawBox 2 3 = intv ((-24203550 : ℚ)/100000000-1/245) ((-24203550 : ℚ)/100000000+1/245) := rfl
private theorem nbshape2_3 : NB 2 3 = intv ((-1756659 : ℚ)/1000000000) ((-1678403 : ℚ)/1000000000) := rfl
private theorem rawshape3_0 : rawBox 3 0 = intv ((7641196 : ℚ)/100000000-1/245) ((7641196 : ℚ)/100000000+1/245) := rfl
private theorem nbshape3_0 : NB 3 0 = intv ((775252 : ℚ)/1000000000) ((844166 : ℚ)/1000000000) := rfl
private theorem rawshape3_1 : rawBox 3 1 = intv ((29846136 : ℚ)/100000000-1/245) ((29846136 : ℚ)/100000000+1/245) := rfl
private theorem nbshape3_1 : NB 3 1 = intv ((2051571 : ℚ)/1000000000) ((2136034 : ℚ)/1000000000) := rfl
private theorem rawshape3_2 : rawBox 3 2 = intv ((-8390200 : ℚ)/100000000-1/245) ((-8390200 : ℚ)/100000000+1/245) := rfl
private theorem nbshape3_2 : NB 3 2 = intv ((-506081 : ℚ)/1000000000) ((-435350 : ℚ)/1000000000) := rfl
private theorem rawshape3_3 : rawBox 3 3 = intv ((998476 : ℚ)/100000000-1/245) ((998476 : ℚ)/100000000+1/245) := rfl
private theorem nbshape3_3 : NB 3 3 = intv ((467416 : ℚ)/1000000000) ((545672 : ℚ)/1000000000) := rfl
private theorem rawshape4_0 : rawBox 4 0 = intv ((20520990 : ℚ)/100000000-1/245) ((20520990 : ℚ)/100000000+1/245) := rfl
private theorem nbshape4_0 : NB 4 0 = intv ((281831 : ℚ)/1000000000) ((350745 : ℚ)/1000000000) := rfl
private theorem rawshape4_1 : rawBox 4 1 = intv ((-25719678 : ℚ)/100000000-1/245) ((-25719678 : ℚ)/100000000+1/245) := rfl
private theorem nbshape4_1 : NB 4 1 = intv ((-1898906 : ℚ)/1000000000) ((-1814443 : ℚ)/1000000000) := rfl
private theorem rawshape4_2 : rawBox 4 2 = intv ((-22529699 : ℚ)/100000000-1/245) ((-22529699 : ℚ)/100000000+1/245) := rfl
private theorem nbshape4_2 : NB 4 2 = intv ((-1425940 : ℚ)/1000000000) ((-1355209 : ℚ)/1000000000) := rfl
private theorem rawshape4_3 : rawBox 4 3 = intv ((-34997033 : ℚ)/100000000-1/245) ((-34997033 : ℚ)/100000000+1/245) := rfl
private theorem nbshape4_3 : NB 4 3 = intv ((-3071544 : ℚ)/1000000000) ((-2993288 : ℚ)/1000000000) := rfl
private theorem rawshape5_0 : rawBox 5 0 = ofRat 0 := rfl
private theorem nbshape5_0 : NB 5 0 = intv ((-940675 : ℚ)/1000000000) ((-940674 : ℚ)/1000000000) := rfl
private theorem rawshape5_1 : rawBox 5 1 = ofRat 0 := rfl
private theorem nbshape5_1 : NB 5 1 = intv ((1764816 : ℚ)/1000000000) ((1764817 : ℚ)/1000000000) := rfl
private theorem rawshape5_2 : rawBox 5 2 = ofRat 0 := rfl
private theorem nbshape5_2 : NB 5 2 = intv ((181172 : ℚ)/1000000000) ((181173 : ℚ)/1000000000) := rfl
private theorem rawshape5_3 : rawBox 5 3 = ofRat 1 := rfl
private theorem nbshape5_3 : NB 5 3 = intv ((6699589 : ℚ)/1000000000) ((6699590 : ℚ)/1000000000) := rfl
private theorem rawshape6_0 : rawBox 6 0 = intv ((-37808496 : ℚ)/100000000-1/245) ((-37808496 : ℚ)/100000000+1/245) := rfl
private theorem nbshape6_0 : NB 6 0 = intv ((-1729437 : ℚ)/1000000000) ((-1660523 : ℚ)/1000000000) := rfl
private theorem rawshape6_1 : rawBox 6 1 = intv ((29583113 : ℚ)/100000000-1/245) ((29583113 : ℚ)/100000000+1/245) := rfl
private theorem nbshape6_1 : NB 6 1 = intv ((2538604 : ℚ)/1000000000) ((2623068 : ℚ)/1000000000) := rfl
private theorem rawshape6_2 : rawBox 6 2 = intv ((152 : ℚ)/100000000-1/245) ((152 : ℚ)/100000000+1/245) := rfl
private theorem nbshape6_2 : NB 6 2 = intv ((-382953 : ℚ)/1000000000) ((-312222 : ℚ)/1000000000) := rfl
private theorem rawshape6_3 : rawBox 6 3 = intv ((83115674 : ℚ)/100000000-1/245) ((83115674 : ℚ)/100000000+1/245) := rfl
private theorem nbshape6_3 : NB 6 3 = intv ((6407024 : ℚ)/1000000000) ((6485280 : ℚ)/1000000000) := rfl
private theorem rawshape7_0 : rawBox 7 0 = ofRat 0 := rfl
private theorem nbshape7_0 : NB 7 0 = intv ((1360779 : ℚ)/1000000000) ((1360780 : ℚ)/1000000000) := rfl
private theorem rawshape7_1 : rawBox 7 1 = ofRat 0 := rfl
private theorem nbshape7_1 : NB 7 1 = intv ((55130 : ℚ)/1000000000) ((55131 : ℚ)/1000000000) := rfl
private theorem rawshape7_2 : rawBox 7 2 = ofRat 1 := rfl
private theorem nbshape7_2 : NB 7 2 = intv ((7067274 : ℚ)/1000000000) ((7067275 : ℚ)/1000000000) := rfl
private theorem rawshape7_3 : rawBox 7 3 = ofRat 0 := rfl
private theorem nbshape7_3 : NB 7 3 = intv ((181172 : ℚ)/1000000000) ((181173 : ℚ)/1000000000) := rfl
private theorem rawshape8_0 : rawBox 8 0 = intv ((41388656 : ℚ)/100000000-1/245) ((41388656 : ℚ)/100000000+1/245) := rfl
private theorem nbshape8_0 : NB 8 0 = intv ((1932726 : ℚ)/1000000000) ((2001640 : ℚ)/1000000000) := rfl
private theorem rawshape8_1 : rawBox 8 1 = intv ((-32384395 : ℚ)/100000000-1/245) ((-32384395 : ℚ)/100000000+1/245) := rfl
private theorem nbshape8_1 : NB 8 1 = intv ((-773555 : ℚ)/1000000000) ((-689092 : ℚ)/1000000000) := rfl
private theorem rawshape8_2 : rawBox 8 2 = intv ((88318967 : ℚ)/100000000-1/245) ((88318967 : ℚ)/100000000+1/245) := rfl
private theorem nbshape8_2 : NB 8 2 = intv ((6796849 : ℚ)/1000000000) ((6867579 : ℚ)/1000000000) := rfl
private theorem rawshape8_3 : rawBox 8 3 = intv ((24901715 : ℚ)/100000000-1/245) ((24901715 : ℚ)/100000000+1/245) := rfl
private theorem nbshape8_3 : NB 8 3 = intv ((828337 : ℚ)/1000000000) ((906593 : ℚ)/1000000000) := rfl
private theorem rawshape9_0 : rawBox 9 0 = intv ((33389477 : ℚ)/100000000-1/245) ((33389477 : ℚ)/100000000+1/245) := rfl
private theorem nbshape9_0 : NB 9 0 = intv ((2521985 : ℚ)/1000000000) ((2590899 : ℚ)/1000000000) := rfl
private theorem rawshape9_1 : rawBox 9 1 = intv ((79737897 : ℚ)/100000000-1/245) ((79737897 : ℚ)/100000000+1/245) := rfl
private theorem nbshape9_1 : NB 9 1 = intv ((6131544 : ℚ)/1000000000) ((6216008 : ℚ)/1000000000) := rfl
private theorem rawshape9_2 : rawBox 9 2 = intv ((-20098413 : ℚ)/100000000-1/245) ((-20098413 : ℚ)/100000000+1/245) := rfl
private theorem nbshape9_2 : NB 9 2 = intv ((-921063 : ℚ)/1000000000) ((-850332 : ℚ)/1000000000) := rfl
private theorem rawshape9_3 : rawBox 9 3 = intv ((20088965 : ℚ)/100000000-1/245) ((20088965 : ℚ)/100000000+1/245) := rfl
private theorem nbshape9_3 : NB 9 3 = intv ((2363478 : ℚ)/1000000000) ((2441734 : ℚ)/1000000000) := rfl
private theorem rawshape10_0 : rawBox 10 0 = ofRat 0 := rfl
private theorem nbshape10_0 : NB 10 0 = intv ((2089958 : ℚ)/1000000000) ((2089959 : ℚ)/1000000000) := rfl
private theorem rawshape10_1 : rawBox 10 1 = ofRat 1 := rfl
private theorem nbshape10_1 : NB 10 1 = intv ((6436709 : ℚ)/1000000000) ((6436710 : ℚ)/1000000000) := rfl
private theorem rawshape10_2 : rawBox 10 2 = ofRat 0 := rfl
private theorem nbshape10_2 : NB 10 2 = intv ((55130 : ℚ)/1000000000) ((55131 : ℚ)/1000000000) := rfl
private theorem rawshape10_3 : rawBox 10 3 = ofRat 0 := rfl
private theorem nbshape10_3 : NB 10 3 = intv ((1764816 : ℚ)/1000000000) ((1764817 : ℚ)/1000000000) := rfl
private theorem rawshape11_0 : rawBox 11 0 = intv ((-27446519 : ℚ)/100000000-1/245) ((-27446519 : ℚ)/100000000+1/245) := rfl
private theorem nbshape11_0 : NB 11 0 = intv ((-1562869 : ℚ)/1000000000) ((-1493955 : ℚ)/1000000000) := rfl
private theorem rawshape11_1 : rawBox 11 1 = intv ((-25867970 : ℚ)/100000000-1/245) ((-25867970 : ℚ)/100000000+1/245) := rfl
private theorem nbshape11_1 : NB 11 1 = intv ((-2747827 : ℚ)/1000000000) ((-2663364 : ℚ)/1000000000) := rfl
private theorem rawshape11_2 : rawBox 11 2 = intv ((-8988772 : ℚ)/100000000-1/245) ((-8988772 : ℚ)/100000000+1/245) := rfl
private theorem nbshape11_2 : NB 11 2 = intv ((-1105799 : ℚ)/1000000000) ((-1035069 : ℚ)/1000000000) := rfl
private theorem rawshape11_3 : rawBox 11 3 = intv ((-26176838 : ℚ)/100000000-1/245) ((-26176838 : ℚ)/100000000+1/245) := rfl
private theorem nbshape11_3 : NB 11 3 = intv ((-2007494 : ℚ)/1000000000) ((-1929238 : ℚ)/1000000000) := rfl
private theorem rawshape12_0 : rawBox 12 0 = intv ((-10221146 : ℚ)/100000000-1/245) ((-10221146 : ℚ)/100000000+1/245) := rfl
private theorem nbshape12_0 : NB 12 0 = intv ((-681193 : ℚ)/1000000000) ((-612279 : ℚ)/1000000000) := rfl
private theorem rawshape12_1 : rawBox 12 1 = intv ((4399929 : ℚ)/100000000-1/245) ((4399929 : ℚ)/100000000+1/245) := rfl
private theorem nbshape12_1 : NB 12 1 = intv ((549206 : ℚ)/1000000000) ((633669 : ℚ)/1000000000) := rfl
private theorem rawshape12_2 : rawBox 12 2 = intv ((-3347819 : ℚ)/100000000-1/245) ((-3347819 : ℚ)/100000000+1/245) := rfl
private theorem nbshape12_2 : NB 12 2 = intv ((-354865 : ℚ)/1000000000) ((-284135 : ℚ)/1000000000) := rfl
private theorem rawshape12_3 : rawBox 12 3 = intv ((29673919 : ℚ)/100000000-1/245) ((29673919 : ℚ)/100000000+1/245) := rfl
private theorem nbshape12_3 : NB 12 3 = intv ((2116636 : ℚ)/1000000000) ((2194892 : ℚ)/1000000000) := rfl
private theorem rawshape13_0 : rawBox 13 0 = intv ((19869272 : ℚ)/100000000-1/245) ((19869272 : ℚ)/100000000+1/245) := rfl
private theorem nbshape13_0 : NB 13 0 = intv ((206549 : ℚ)/1000000000) ((275463 : ℚ)/1000000000) := rfl
private theorem rawshape13_1 : rawBox 13 1 = intv ((-21983762 : ℚ)/100000000-1/245) ((-21983762 : ℚ)/100000000+1/245) := rfl
private theorem nbshape13_1 : NB 13 1 = intv ((-1601352 : ℚ)/1000000000) ((-1516889 : ℚ)/1000000000) := rfl
private theorem rawshape13_2 : rawBox 13 2 = intv ((-28951686 : ℚ)/100000000-1/245) ((-28951686 : ℚ)/100000000+1/245) := rfl
private theorem nbshape13_2 : NB 13 2 = intv ((-1878986 : ℚ)/1000000000) ((-1808256 : ℚ)/1000000000) := rfl
private theorem rawshape13_3 : rawBox 13 3 = intv ((-30790069 : ℚ)/100000000-1/245) ((-30790069 : ℚ)/100000000+1/245) := rfl
private theorem nbshape13_3 : NB 13 3 = intv ((-2729267 : ℚ)/1000000000) ((-2651011 : ℚ)/1000000000) := rfl
private theorem rawshape14_0 : rawBox 14 0 = intv ((24637620 : ℚ)/100000000-1/245) ((24637620 : ℚ)/100000000+1/245) := rfl
private theorem nbshape14_0 : NB 14 0 = intv ((264387 : ℚ)/1000000000) ((333301 : ℚ)/1000000000) := rfl
private theorem rawshape14_1 : rawBox 14 1 = intv ((-27259558 : ℚ)/100000000-1/245) ((-27259558 : ℚ)/100000000+1/245) := rfl
private theorem nbshape14_1 : NB 14 1 = intv ((-1975519 : ℚ)/1000000000) ((-1891056 : ℚ)/1000000000) := rfl
private theorem rawshape14_2 : rawBox 14 2 = intv ((-35899686 : ℚ)/100000000-1/245) ((-35899686 : ℚ)/100000000+1/245) := rfl
private theorem nbshape14_2 : NB 14 2 = intv ((-2321429 : ℚ)/1000000000) ((-2250699 : ℚ)/1000000000) := rfl
private theorem rawshape14_3 : rawBox 14 3 = intv ((-38179255 : ℚ)/100000000-1/245) ((-38179255 : ℚ)/100000000+1/245) := rfl
private theorem nbshape14_3 : NB 14 3 = intv ((-3374863 : ℚ)/1000000000) ((-3296607 : ℚ)/1000000000) := rfl
private theorem rawshape15_0 : rawBox 15 0 = intv ((3644599 : ℚ)/100000000-1/245) ((3644599 : ℚ)/100000000+1/245) := rfl
private theorem nbshape15_0 : NB 15 0 = intv ((219510 : ℚ)/1000000000) ((288424 : ℚ)/1000000000) := rfl
private theorem rawshape15_1 : rawBox 15 1 = intv ((-6250090 : ℚ)/100000000-1/245) ((-6250090 : ℚ)/100000000+1/245) := rfl
private theorem nbshape15_1 : NB 15 1 = intv ((-380506 : ℚ)/1000000000) ((-296043 : ℚ)/1000000000) := rfl
private theorem rawshape15_2 : rawBox 15 2 = intv ((16580440 : ℚ)/100000000-1/245) ((16580440 : ℚ)/100000000+1/245) := rfl
private theorem nbshape15_2 : NB 15 2 = intv ((1180384 : ℚ)/1000000000) ((1251115 : ℚ)/1000000000) := rfl
private theorem rawshape15_3 : rawBox 15 3 = intv ((-1206102 : ℚ)/100000000-1/245) ((-1206102 : ℚ)/100000000+1/245) := rfl
private theorem nbshape15_3 : NB 15 3 = intv ((-234479 : ℚ)/1000000000) ((-156223 : ℚ)/1000000000) := rfl
private theorem rawshape16_0 : rawBox 16 0 = intv ((2538273 : ℚ)/100000000-1/245) ((2538273 : ℚ)/100000000+1/245) := rfl
private theorem nbshape16_0 : NB 16 0 = intv ((142417 : ℚ)/1000000000) ((211332 : ℚ)/1000000000) := rfl
private theorem rawshape16_1 : rawBox 16 1 = intv ((-4352862 : ℚ)/100000000-1/245) ((-4352862 : ℚ)/100000000+1/245) := rfl
private theorem nbshape16_1 : NB 16 1 = intv ((-277822 : ℚ)/1000000000) ((-193359 : ℚ)/1000000000) := rfl
private theorem rawshape16_2 : rawBox 16 2 = intv ((11547412 : ℚ)/100000000-1/245) ((11547412 : ℚ)/100000000+1/245) := rfl
private theorem nbshape16_2 : NB 16 2 = intv ((811341 : ℚ)/1000000000) ((882071 : ℚ)/1000000000) := rfl
private theorem rawshape16_3 : rawBox 16 3 = intv ((-839987 : ℚ)/100000000-1/245) ((-839987 : ℚ)/100000000+1/245) := rfl
private theorem nbshape16_3 : NB 16 3 = intv ((-175180 : ℚ)/1000000000) ((-96924 : ℚ)/1000000000) := rfl
private theorem rawshape17_0 : rawBox 17 0 = intv ((2538465 : ℚ)/100000000-1/245) ((2538465 : ℚ)/100000000+1/245) := rfl
private theorem nbshape17_0 : NB 17 0 = intv ((142431 : ℚ)/1000000000) ((211345 : ℚ)/1000000000) := rfl
private theorem rawshape17_1 : rawBox 17 1 = intv ((-4353191 : ℚ)/100000000-1/245) ((-4353191 : ℚ)/100000000+1/245) := rfl
private theorem nbshape17_1 : NB 17 1 = intv ((-277840 : ℚ)/1000000000) ((-193377 : ℚ)/1000000000) := rfl
private theorem rawshape17_2 : rawBox 17 2 = intv ((11548286 : ℚ)/100000000-1/245) ((11548286 : ℚ)/100000000+1/245) := rfl
private theorem nbshape17_2 : NB 17 2 = intv ((811405 : ℚ)/1000000000) ((882135 : ℚ)/1000000000) := rfl
private theorem rawshape17_3 : rawBox 17 3 = intv ((-840051 : ℚ)/100000000-1/245) ((-840051 : ℚ)/100000000+1/245) := rfl
private theorem nbshape17_3 : NB 17 3 = intv ((-175190 : ℚ)/1000000000) ((-96934 : ℚ)/1000000000) := rfl
private theorem rawshape18_0 : rawBox 18 0 = ofRat 1 := rfl
private theorem nbshape18_0 : NB 18 0 = intv ((4050436 : ℚ)/1000000000) ((4050437 : ℚ)/1000000000) := rfl
private theorem rawshape18_1 : rawBox 18 1 = ofRat 0 := rfl
private theorem nbshape18_1 : NB 18 1 = intv ((2089958 : ℚ)/1000000000) ((2089959 : ℚ)/1000000000) := rfl
private theorem rawshape18_2 : rawBox 18 2 = ofRat 0 := rfl
private theorem nbshape18_2 : NB 18 2 = intv ((1360779 : ℚ)/1000000000) ((1360780 : ℚ)/1000000000) := rfl
private theorem rawshape18_3 : rawBox 18 3 = ofRat 0 := rfl
private theorem nbshape18_3 : NB 18 3 = intv ((-940675 : ℚ)/1000000000) ((-940674 : ℚ)/1000000000) := rfl
private theorem rawshape19_0 : rawBox 19 0 = intv ((52089722 : ℚ)/100000000-1/245) ((52089722 : ℚ)/100000000+1/245) := rfl
private theorem nbshape19_0 : NB 19 0 = intv ((2075404 : ℚ)/1000000000) ((2144318 : ℚ)/1000000000) := rfl
private theorem rawshape19_1 : rawBox 19 1 = intv ((0 : ℚ)/100000000-1/245) ((0 : ℚ)/100000000+1/245) := rfl
private theorem nbshape19_1 : NB 19 1 = intv ((1046422 : ℚ)/1000000000) ((1130885 : ℚ)/1000000000) := rfl
private theorem rawshape19_2 : rawBox 19 2 = intv ((0 : ℚ)/100000000-1/245) ((0 : ℚ)/100000000+1/245) := rfl
private theorem nbshape19_2 : NB 19 2 = intv ((673461 : ℚ)/1000000000) ((744192 : ℚ)/1000000000) := rfl
private theorem rawshape19_3 : rawBox 19 3 = intv ((0 : ℚ)/100000000-1/245) ((0 : ℚ)/100000000+1/245) := rfl
private theorem nbshape19_3 : NB 19 3 = intv ((-529123 : ℚ)/1000000000) ((-450867 : ℚ)/1000000000) := rfl
private theorem rawshape20_0 : rawBox 20 0 = intv ((67743131 : ℚ)/100000000-1/245) ((67743131 : ℚ)/100000000+1/245) := rfl
private theorem nbshape20_0 : NB 20 0 = intv ((2709435 : ℚ)/1000000000) ((2778350 : ℚ)/1000000000) := rfl
private theorem rawshape20_1 : rawBox 20 1 = intv ((0 : ℚ)/100000000-1/245) ((0 : ℚ)/100000000+1/245) := rfl
private theorem nbshape20_1 : NB 20 1 = intv ((1373572 : ℚ)/1000000000) ((1458035 : ℚ)/1000000000) := rfl
private theorem rawshape20_2 : rawBox 20 2 = intv ((0 : ℚ)/100000000-1/245) ((0 : ℚ)/100000000+1/245) := rfl
private theorem nbshape20_2 : NB 20 2 = intv ((886470 : ℚ)/1000000000) ((957200 : ℚ)/1000000000) := rfl
private theorem rawshape20_3 : rawBox 20 3 = intv ((0 : ℚ)/100000000-1/245) ((0 : ℚ)/100000000+1/245) := rfl
private theorem nbshape20_3 : NB 20 3 = intv ((-676371 : ℚ)/1000000000) ((-598114 : ℚ)/1000000000) := rfl
private theorem rawshape21_0 : rawBox 21 0 = intv ((-88312959 : ℚ)/100000000-1/245) ((-88312959 : ℚ)/100000000+1/245) := rfl
private theorem nbshape21_0 : NB 21 0 = intv ((-2937538 : ℚ)/1000000000) ((-2868624 : ℚ)/1000000000) := rfl
private theorem rawshape21_1 : rawBox 21 1 = intv ((8937478 : ℚ)/100000000-1/245) ((8937478 : ℚ)/100000000+1/245) := rfl
private theorem nbshape21_1 : NB 21 1 = intv ((-840239 : ℚ)/1000000000) ((-755776 : ℚ)/1000000000) := rfl
private theorem rawshape21_2 : rawBox 21 2 = intv ((53158875 : ℚ)/100000000-1/245) ((53158875 : ℚ)/100000000+1/245) := rfl
private theorem nbshape21_2 : NB 21 2 = intv ((2570190 : ℚ)/1000000000) ((2640920 : ℚ)/1000000000) := rfl
private theorem rawshape21_3 : rawBox 21 3 = intv ((25108070 : ℚ)/100000000-1/245) ((25108070 : ℚ)/100000000+1/245) := rfl
private theorem nbshape21_3 : NB 21 3 = intv ((2727787 : ℚ)/1000000000) ((2806043 : ℚ)/1000000000) := rfl
private theorem rawshape22_0 : rawBox 22 0 = intv ((-46003650 : ℚ)/100000000-1/245) ((-46003650 : ℚ)/100000000+1/245) := rfl
private theorem nbshape22_0 : NB 22 0 = intv ((-1546719 : ℚ)/1000000000) ((-1477805 : ℚ)/1000000000) := rfl
private theorem rawshape22_1 : rawBox 22 1 = intv ((4655677 : ℚ)/100000000-1/245) ((4655677 : ℚ)/100000000+1/245) := rfl
private theorem nbshape22_1 : NB 22 1 = intv ((-457926 : ℚ)/1000000000) ((-373463 : ℚ)/1000000000) := rfl
private theorem rawshape22_2 : rawBox 22 2 = intv ((27691318 : ℚ)/100000000-1/245) ((27691318 : ℚ)/100000000+1/245) := rfl
private theorem nbshape22_2 : NB 22 2 = intv ((1321910 : ℚ)/1000000000) ((1392641 : ℚ)/1000000000) := rfl
private theorem rawshape22_3 : rawBox 22 3 = intv ((13079200 : ℚ)/100000000-1/245) ((13079200 : ℚ)/100000000+1/245) := rfl
private theorem nbshape22_3 : NB 22 3 = intv ((1402203 : ℚ)/1000000000) ((1480459 : ℚ)/1000000000) := rfl
private theorem rawshape23_0 : rawBox 23 0 = intv ((-59827638 : ℚ)/100000000-1/245) ((-59827638 : ℚ)/100000000+1/245) := rfl
private theorem nbshape23_0 : NB 23 0 = intv ((-2001150 : ℚ)/1000000000) ((-1932236 : ℚ)/1000000000) := rfl
private theorem rawshape23_1 : rawBox 23 1 = intv ((6054697 : ℚ)/100000000-1/245) ((6054697 : ℚ)/100000000+1/245) := rfl
private theorem nbshape23_1 : NB 23 1 = intv ((-582842 : ℚ)/1000000000) ((-498379 : ℚ)/1000000000) := rfl
private theorem rawshape23_2 : rawBox 23 2 = intv ((36012494 : ℚ)/100000000-1/245) ((36012494 : ℚ)/100000000+1/245) := rfl
private theorem nbshape23_2 : NB 23 2 = intv ((1729769 : ℚ)/1000000000) ((1800499 : ℚ)/1000000000) := rfl
private theorem rawshape23_3 : rawBox 23 3 = intv ((17009469 : ℚ)/100000000-1/245) ((17009469 : ℚ)/100000000+1/245) := rfl
private theorem nbshape23_3 : NB 23 3 = intv ((1835319 : ℚ)/1000000000) ((1913575 : ℚ)/1000000000) := rfl
private theorem rawshape24_0 : rawBox 24 0 = intv ((-32064327 : ℚ)/100000000-1/245) ((-32064327 : ℚ)/100000000+1/245) := rfl
private theorem nbshape24_0 : NB 24 0 = intv ((-1753381 : ℚ)/1000000000) ((-1684467 : ℚ)/1000000000) := rfl
private theorem rawshape24_1 : rawBox 24 1 = intv ((-21323871 : ℚ)/100000000-1/245) ((-21323871 : ℚ)/100000000+1/245) := rfl
private theorem nbshape24_1 : NB 24 1 = intv ((-2557690 : ℚ)/1000000000) ((-2473227 : ℚ)/1000000000) := rfl
private theorem rawshape24_2 : rawBox 24 2 = intv ((-16293992 : ℚ)/100000000-1/245) ((-16293992 : ℚ)/100000000+1/245) := rfl
private theorem nbshape24_2 : NB 24 2 = intv ((-1682599 : ℚ)/1000000000) ((-1611868 : ℚ)/1000000000) := rfl
private theorem rawshape24_3 : rawBox 24 3 = intv ((-26279735 : ℚ)/100000000-1/245) ((-26279735 : ℚ)/100000000+1/245) := rfl
private theorem nbshape24_3 : NB 24 3 = intv ((-1903989 : ℚ)/1000000000) ((-1825733 : ℚ)/1000000000) := rfl
private theorem rawshape25_0 : rawBox 25 0 = intv ((-46309969 : ℚ)/100000000-1/245) ((-46309969 : ℚ)/100000000+1/245) := rfl
private theorem nbshape25_0 : NB 25 0 = intv ((-2517070 : ℚ)/1000000000) ((-2448156 : ℚ)/1000000000) := rfl
private theorem rawshape25_1 : rawBox 25 1 = intv ((-30797708 : ℚ)/100000000-1/245) ((-30797708 : ℚ)/100000000+1/245) := rfl
private theorem nbshape25_1 : NB 25 1 = intv ((-3675266 : ℚ)/1000000000) ((-3590803 : ℚ)/1000000000) := rfl
private theorem rawshape25_2 : rawBox 25 2 = intv ((-23533139 : ℚ)/100000000-1/245) ((-23533139 : ℚ)/100000000+1/245) := rfl
private theorem nbshape25_2 : NB 25 2 = intv ((-2414437 : ℚ)/1000000000) ((-2343707 : ℚ)/1000000000) := rfl
private theorem rawshape25_3 : rawBox 25 3 = intv ((-37955379 : ℚ)/100000000-1/245) ((-37955379 : ℚ)/100000000+1/245) := rfl
private theorem nbshape25_3 : NB 25 3 = intv ((-2732515 : ℚ)/1000000000) ((-2654259 : ℚ)/1000000000) := rfl
private theorem rawshape26_0 : rawBox 26 0 = intv ((-63636544 : ℚ)/100000000-1/245) ((-63636544 : ℚ)/100000000+1/245) := rfl
private theorem nbshape26_0 : NB 26 0 = intv ((-3445923 : ℚ)/1000000000) ((-3377009 : ℚ)/1000000000) := rfl
private theorem rawshape26_1 : rawBox 26 1 = intv ((-42320472 : ℚ)/100000000-1/245) ((-42320472 : ℚ)/100000000+1/245) := rfl
private theorem nbshape26_1 : NB 26 1 = intv ((-5034543 : ℚ)/1000000000) ((-4950080 : ℚ)/1000000000) := rfl
private theorem rawshape26_2 : rawBox 26 2 = intv ((-32337911 : ℚ)/100000000-1/245) ((-32337911 : ℚ)/100000000+1/245) := rfl
private theorem nbshape26_2 : NB 26 2 = intv ((-3304551 : ℚ)/1000000000) ((-3233821 : ℚ)/1000000000) := rfl
private theorem rawshape26_3 : rawBox 26 3 = intv ((-52156139 : ℚ)/100000000-1/245) ((-52156139 : ℚ)/100000000+1/245) := rfl
private theorem nbshape26_3 : NB 26 3 = intv ((-3740229 : ℚ)/1000000000) ((-3661972 : ℚ)/1000000000) := rfl
private theorem rawshape27_0 : rawBox 27 0 = intv ((-52092790 : ℚ)/100000000-1/245) ((-52092790 : ℚ)/100000000+1/245) := rfl
private theorem nbshape27_0 : NB 27 0 = intv ((-1429041 : ℚ)/1000000000) ((-1360127 : ℚ)/1000000000) := rfl
private theorem rawshape27_1 : rawBox 27 1 = intv ((40759804 : ℚ)/100000000-1/245) ((40759804 : ℚ)/100000000+1/245) := rfl
private theorem nbshape27_1 : NB 27 1 = intv ((1748665 : ℚ)/1000000000) ((1833128 : ℚ)/1000000000) := rfl
private theorem rawshape27_2 : rawBox 27 2 = intv ((209 : ℚ)/100000000-1/245) ((209 : ℚ)/100000000+1/245) := rfl
private theorem nbshape27_2 : NB 27 2 = intv ((-695465 : ℚ)/1000000000) ((-624734 : ℚ)/1000000000) := rfl
private theorem rawshape27_3 : rawBox 27 3 = intv ((14507149 : ℚ)/100000000-1/245) ((14507149 : ℚ)/100000000+1/245) := rfl
private theorem nbshape27_3 : NB 27 3 = intv ((2142151 : ℚ)/1000000000) ((2220407 : ℚ)/1000000000) := rfl
private theorem rawshape28_0 : rawBox 28 0 = intv ((-42810470 : ℚ)/100000000-1/245) ((-42810470 : ℚ)/100000000+1/245) := rfl
private theorem nbshape28_0 : NB 28 0 = intv ((-1180543 : ℚ)/1000000000) ((-1111629 : ℚ)/1000000000) := rfl
private theorem rawshape28_1 : rawBox 28 1 = intv ((33496888 : ℚ)/100000000-1/245) ((33496888 : ℚ)/100000000+1/245) := rfl
private theorem nbshape28_1 : NB 28 1 = intv ((1429549 : ℚ)/1000000000) ((1514012 : ℚ)/1000000000) := rfl
private theorem rawshape28_2 : rawBox 28 2 = intv ((172 : ℚ)/100000000-1/245) ((172 : ℚ)/100000000+1/245) := rfl
private theorem nbshape28_2 : NB 28 2 = intv ((-577843 : ℚ)/1000000000) ((-507112 : ℚ)/1000000000) := rfl
private theorem rawshape28_3 : rawBox 28 3 = intv ((11922147 : ℚ)/100000000-1/245) ((11922147 : ℚ)/100000000+1/245) := rfl
private theorem nbshape28_3 : NB 28 3 = intv ((1753473 : ℚ)/1000000000) ((1831729 : ℚ)/1000000000) := rfl
private theorem rawshape29_0 : rawBox 29 0 = intv ((-68355415 : ℚ)/100000000-1/245) ((-68355415 : ℚ)/100000000+1/245) := rfl
private theorem nbshape29_0 : NB 29 0 = intv ((-1864411 : ℚ)/1000000000) ((-1795497 : ℚ)/1000000000) := rfl
private theorem rawshape29_1 : rawBox 29 1 = intv ((53484433 : ℚ)/100000000-1/245) ((53484433 : ℚ)/100000000+1/245) := rfl
private theorem nbshape29_1 : NB 29 1 = intv ((2307758 : ℚ)/1000000000) ((2392221 : ℚ)/1000000000) := rfl
private theorem rawshape29_2 : rawBox 29 2 = intv ((275 : ℚ)/100000000-1/245) ((275 : ℚ)/100000000+1/245) := rfl
private theorem nbshape29_2 : NB 29 2 = intv ((-901538 : ℚ)/1000000000) ((-830808 : ℚ)/1000000000) := rfl
private theorem rawshape29_3 : rawBox 29 3 = intv ((19036074 : ℚ)/100000000-1/245) ((19036074 : ℚ)/100000000+1/245) := rfl
private theorem nbshape29_3 : NB 29 3 = intv ((2823115 : ℚ)/1000000000) ((2901371 : ℚ)/1000000000) := rfl
private theorem rawshape30_0 : rawBox 30 0 = intv ((46866935 : ℚ)/100000000-1/245) ((46866935 : ℚ)/100000000+1/245) := rfl
private theorem nbshape30_0 : NB 30 0 = intv ((832201 : ℚ)/1000000000) ((901115 : ℚ)/1000000000) := rfl
private theorem rawshape30_1 : rawBox 30 1 = intv ((-36670854 : ℚ)/100000000-1/245) ((-36670854 : ℚ)/100000000+1/245) := rfl
private theorem nbshape30_1 : NB 30 1 = intv ((-925490 : ℚ)/1000000000) ((-841027 : ℚ)/1000000000) := rfl
private theorem rawshape30_2 : rawBox 30 2 = intv ((-188 : ℚ)/100000000-1/245) ((-188 : ℚ)/100000000+1/245) := rfl
private theorem nbshape30_2 : NB 30 2 = intv ((633247 : ℚ)/1000000000) ((703978 : ℚ)/1000000000) := rfl
private theorem rawshape30_3 : rawBox 30 3 = intv ((28197753 : ℚ)/100000000-1/245) ((28197753 : ℚ)/100000000+1/245) := rfl
private theorem nbshape30_3 : NB 30 3 = intv ((761967 : ℚ)/1000000000) ((840223 : ℚ)/1000000000) := rfl
private theorem rawshape31_0 : rawBox 31 0 = intv ((37805363 : ℚ)/100000000-1/245) ((37805363 : ℚ)/100000000+1/245) := rfl
private theorem nbshape31_0 : NB 31 0 = intv ((664635 : ℚ)/1000000000) ((733549 : ℚ)/1000000000) := rfl
private theorem rawshape31_1 : rawBox 31 1 = intv ((-29580661 : ℚ)/100000000-1/245) ((-29580661 : ℚ)/100000000+1/245) := rfl
private theorem nbshape31_1 : NB 31 1 = intv ((-754715 : ℚ)/1000000000) ((-670251 : ℚ)/1000000000) := rfl
private theorem rawshape31_2 : rawBox 31 2 = intv ((-152 : ℚ)/100000000-1/245) ((-152 : ℚ)/100000000+1/245) := rfl
private theorem nbshape31_2 : NB 31 2 = intv ((503973 : ℚ)/1000000000) ((574704 : ℚ)/1000000000) := rfl
private theorem rawshape31_3 : rawBox 31 3 = intv ((22745807 : ℚ)/100000000-1/245) ((22745807 : ℚ)/100000000+1/245) := rfl
private theorem nbshape31_3 : NB 31 3 = intv ((607078 : ℚ)/1000000000) ((685334 : ℚ)/1000000000) := rfl
private theorem rawshape32_0 : rawBox 32 0 = intv ((42809939 : ℚ)/100000000-1/245) ((42809939 : ℚ)/100000000+1/245) := rfl
private theorem nbshape32_0 : NB 32 0 = intv ((757179 : ℚ)/1000000000) ((826093 : ℚ)/1000000000) := rfl
private theorem rawshape32_1 : rawBox 32 1 = intv ((-33496473 : ℚ)/100000000-1/245) ((-33496473 : ℚ)/100000000+1/245) := rfl
private theorem nbshape32_1 : NB 32 1 = intv ((-849031 : ℚ)/1000000000) ((-764568 : ℚ)/1000000000) := rfl
private theorem rawshape32_2 : rawBox 32 2 = intv ((-172 : ℚ)/100000000-1/245) ((-172 : ℚ)/100000000+1/245) := rfl
private theorem nbshape32_2 : NB 32 2 = intv ((575369 : ℚ)/1000000000) ((646100 : ℚ)/1000000000) := rfl
private theorem rawshape32_3 : rawBox 32 3 = intv ((25756839 : ℚ)/100000000-1/245) ((25756839 : ℚ)/100000000+1/245) := rfl
private theorem nbshape32_3 : NB 32 3 = intv ((692621 : ℚ)/1000000000) ((770877 : ℚ)/1000000000) := rfl
private theorem rawshape33_0 : rawBox 33 0 = intv ((-33388328 : ℚ)/100000000-1/245) ((-33388328 : ℚ)/100000000+1/245) := rfl
private theorem nbshape33_0 : NB 33 0 = intv ((-378386 : ℚ)/1000000000) ((-309472 : ℚ)/1000000000) := rfl
private theorem rawshape33_1 : rawBox 33 1 = intv ((26124570 : ℚ)/100000000-1/245) ((26124570 : ℚ)/100000000+1/245) := rfl
private theorem nbshape33_1 : NB 33 1 = intv ((598088 : ℚ)/1000000000) ((682551 : ℚ)/1000000000) := rfl
private theorem rawshape33_2 : rawBox 33 2 = intv ((20097721 : ℚ)/100000000-1/245) ((20097721 : ℚ)/100000000+1/245) := rfl
private theorem nbshape33_2 : NB 33 2 = intv ((908662 : ℚ)/1000000000) ((979393 : ℚ)/1000000000) := rfl
private theorem rawshape33_3 : rawBox 33 3 = intv ((-20088274 : ℚ)/100000000-1/245) ((-20088274 : ℚ)/100000000+1/245) := rfl
private theorem nbshape33_3 : NB 33 3 = intv ((-573422 : ℚ)/1000000000) ((-495166 : ℚ)/1000000000) := rfl
private theorem rawshape34_0 : rawBox 34 0 = intv ((-41389175 : ℚ)/100000000-1/245) ((-41389175 : ℚ)/100000000+1/245) := rfl
private theorem nbshape34_0 : NB 34 0 = intv ((-460802 : ℚ)/1000000000) ((-391888 : ℚ)/1000000000) := rfl
private theorem rawshape34_1 : rawBox 34 1 = intv ((32384802 : ℚ)/100000000-1/245) ((32384802 : ℚ)/100000000+1/245) := rfl
private theorem nbshape34_1 : NB 34 1 = intv ((751527 : ℚ)/1000000000) ((835990 : ℚ)/1000000000) := rfl
private theorem rawshape34_2 : rawBox 34 2 = intv ((24913740 : ℚ)/100000000-1/245) ((24913740 : ℚ)/100000000+1/245) := rfl
private theorem nbshape34_2 : NB 34 2 = intv ((1134880 : ℚ)/1000000000) ((1205610 : ℚ)/1000000000) := rfl
private theorem rawshape34_3 : rawBox 34 3 = intv ((-24902028 : ℚ)/100000000-1/245) ((-24902028 : ℚ)/100000000+1/245) := rfl
private theorem nbshape34_3 : NB 34 3 = intv ((-701455 : ℚ)/1000000000) ((-623199 : ℚ)/1000000000) := rfl
private theorem rawshape35_0 : rawBox 35 0 = intv ((-37807975 : ℚ)/100000000-1/245) ((-37807975 : ℚ)/100000000+1/245) := rfl
private theorem nbshape35_0 : NB 35 0 = intv ((-423912 : ℚ)/1000000000) ((-354998 : ℚ)/1000000000) := rfl
private theorem rawshape35_1 : rawBox 35 1 = intv ((29582705 : ℚ)/100000000-1/245) ((29582705 : ℚ)/100000000+1/245) := rfl
private theorem nbshape35_1 : NB 35 1 = intv ((682847 : ℚ)/1000000000) ((767310 : ℚ)/1000000000) := rfl
private theorem rawshape35_2 : rawBox 35 2 = intv ((22758077 : ℚ)/100000000-1/245) ((22758077 : ℚ)/100000000+1/245) := rfl
private theorem nbshape35_2 : NB 35 2 = intv ((1033624 : ℚ)/1000000000) ((1104355 : ℚ)/1000000000) := rfl
private theorem rawshape35_3 : rawBox 35 3 = intv ((-22747379 : ℚ)/100000000-1/245) ((-22747379 : ℚ)/100000000+1/245) := rfl
private theorem nbshape35_3 : NB 35 3 = intv ((-644147 : ℚ)/1000000000) ((-565891 : ℚ)/1000000000) := rfl
private theorem rawshape36_0 : rawBox 36 0 = intv ((37806826 : ℚ)/100000000-1/245) ((37806826 : ℚ)/100000000+1/245) := rfl
private theorem nbshape36_0 : NB 36 0 = intv ((1142469 : ℚ)/1000000000) ((1211383 : ℚ)/1000000000) := rfl
private theorem rawshape36_1 : rawBox 36 1 = intv ((8097498 : ℚ)/100000000-1/245) ((8097498 : ℚ)/100000000+1/245) := rfl
private theorem nbshape36_1 : NB 36 1 = intv ((1658019 : ℚ)/1000000000) ((1742482 : ℚ)/1000000000) := rfl
private theorem rawshape36_2 : rawBox 36 2 = intv ((-22757385 : ℚ)/100000000-1/245) ((-22757385 : ℚ)/100000000+1/245) := rfl
private theorem nbshape36_2 : NB 36 2 = intv ((-1083550 : ℚ)/1000000000) ((-1012819 : ℚ)/1000000000) := rfl
private theorem rawshape36_3 : rawBox 36 3 = intv ((22746687 : ℚ)/100000000-1/245) ((22746687 : ℚ)/100000000+1/245) := rfl
private theorem nbshape36_3 : NB 36 3 = intv ((1230843 : ℚ)/1000000000) ((1309099 : ℚ)/1000000000) := rfl
private theorem rawshape37_0 : rawBox 37 0 = intv ((46004017 : ℚ)/100000000-1/245) ((46004017 : ℚ)/100000000+1/245) := rfl
private theorem nbshape37_0 : NB 37 0 = intv ((1397647 : ℚ)/1000000000) ((1466561 : ℚ)/1000000000) := rfl
private theorem rawshape37_1 : rawBox 37 1 = intv ((9853180 : ℚ)/100000000-1/245) ((9853180 : ℚ)/100000000+1/245) := rfl
private theorem nbshape37_1 : NB 37 1 = intv ((2026664 : ℚ)/1000000000) ((2111127 : ℚ)/1000000000) := rfl
private theorem rawshape37_2 : rawBox 37 2 = intv ((-27691591 : ℚ)/100000000-1/245) ((-27691591 : ℚ)/100000000+1/245) := rfl
private theorem nbshape37_2 : NB 37 2 = intv ((-1310815 : ℚ)/1000000000) ((-1240084 : ℚ)/1000000000) := rfl
private theorem rawshape37_3 : rawBox 37 3 = intv ((27678573 : ℚ)/100000000-1/245) ((27678573 : ℚ)/100000000+1/245) := rfl
private theorem nbshape37_3 : NB 37 3 = intv ((1506196 : ℚ)/1000000000) ((1584452 : ℚ)/1000000000) := rfl
private theorem rawshape38_0 : rawBox 38 0 = intv ((60367515 : ℚ)/100000000-1/245) ((60367515 : ℚ)/100000000+1/245) := rfl
private theorem nbshape38_0 : NB 38 0 = intv ((1844782 : ℚ)/1000000000) ((1913696 : ℚ)/1000000000) := rfl
private theorem rawshape38_1 : rawBox 38 1 = intv ((12929566 : ℚ)/100000000-1/245) ((12929566 : ℚ)/100000000+1/245) := rfl
private theorem nbshape38_1 : NB 38 1 = intv ((2672620 : ℚ)/1000000000) ((2757083 : ℚ)/1000000000) := rfl
private theorem rawshape38_2 : rawBox 38 2 = intv ((-36337533 : ℚ)/100000000-1/245) ((-36337533 : ℚ)/100000000+1/245) := rfl
private theorem nbshape38_2 : NB 38 2 = intv ((-1709039 : ℚ)/1000000000) ((-1638308 : ℚ)/1000000000) := rfl
private theorem rawshape38_3 : rawBox 38 3 = intv ((36320452 : ℚ)/100000000-1/245) ((36320452 : ℚ)/100000000+1/245) := rfl
private theorem nbshape38_3 : NB 38 3 = intv ((1988681 : ℚ)/1000000000) ((2066937 : ℚ)/1000000000) := rfl
private theorem rawshape39_0 : rawBox 39 0 = intv ((31158680 : ℚ)/100000000-1/245) ((31158680 : ℚ)/100000000+1/245) := rfl
private theorem nbshape39_0 : NB 39 0 = intv ((343485 : ℚ)/1000000000) ((412399 : ℚ)/1000000000) := rfl
private theorem rawshape39_1 : rawBox 39 1 = intv ((-34474590 : ℚ)/100000000-1/245) ((-34474590 : ℚ)/100000000+1/245) := rfl
private theorem nbshape39_1 : NB 39 1 = intv ((-2487220 : ℚ)/1000000000) ((-2402757 : ℚ)/1000000000) := rfl
private theorem rawshape39_2 : rawBox 39 2 = intv ((-45401579 : ℚ)/100000000-1/245) ((-45401579 : ℚ)/100000000+1/245) := rfl
private theorem nbshape39_2 : NB 39 2 = intv ((-2926503 : ℚ)/1000000000) ((-2855772 : ℚ)/1000000000) := rfl
private theorem rawshape39_3 : rawBox 39 3 = intv ((-48284502 : ℚ)/100000000-1/245) ((-48284502 : ℚ)/100000000+1/245) := rfl
private theorem nbshape39_3 : NB 39 3 = intv ((-4257762 : ℚ)/1000000000) ((-4179506 : ℚ)/1000000000) := rfl
private theorem rawshape40_0 : rawBox 40 0 = intv ((21573661 : ℚ)/100000000-1/245) ((21573661 : ℚ)/100000000+1/245) := rfl
private theorem nbshape40_0 : NB 40 0 = intv ((227223 : ℚ)/1000000000) ((296137 : ℚ)/1000000000) := rfl
private theorem rawshape40_1 : rawBox 40 1 = intv ((-23869533 : ℚ)/100000000-1/245) ((-23869533 : ℚ)/100000000+1/245) := rfl
private theorem nbshape40_1 : NB 40 1 = intv ((-1735094 : ℚ)/1000000000) ((-1650631 : ℚ)/1000000000) := rfl
private theorem rawshape40_2 : rawBox 40 2 = intv ((-31435166 : ℚ)/100000000-1/245) ((-31435166 : ℚ)/100000000+1/245) := rfl
private theorem nbshape40_2 : NB 40 2 = intv ((-2037132 : ℚ)/1000000000) ((-1966402 : ℚ)/1000000000) := rfl
private theorem rawshape40_3 : rawBox 40 3 = intv ((-33431246 : ℚ)/100000000-1/245) ((-33431246 : ℚ)/100000000+1/245) := rfl
private theorem nbshape40_3 : NB 40 3 = intv ((-2960028 : ℚ)/1000000000) ((-2881772 : ℚ)/1000000000) := rfl
private theorem rawshape41_0 : rawBox 41 0 = intv ((42817520 : ℚ)/100000000-1/245) ((42817520 : ℚ)/100000000+1/245) := rfl
private theorem nbshape41_0 : NB 41 0 = intv ((484902 : ℚ)/1000000000) ((553816 : ℚ)/1000000000) := rfl
private theorem rawshape41_1 : rawBox 41 1 = intv ((-47374166 : ℚ)/100000000-1/245) ((-47374166 : ℚ)/100000000+1/245) := rfl
private theorem nbshape41_1 : NB 41 1 = intv ((-3402077 : ℚ)/1000000000) ((-3317613 : ℚ)/1000000000) := rfl
private theorem rawshape41_2 : rawBox 41 2 = intv ((-62389774 : ℚ)/100000000-1/245) ((-62389774 : ℚ)/100000000+1/245) := rfl
private theorem nbshape41_2 : NB 41 2 = intv ((-4008298 : ℚ)/1000000000) ((-3937567 : ℚ)/1000000000) := rfl
private theorem rawshape41_3 : rawBox 41 3 = intv ((-66351419 : ℚ)/100000000-1/245) ((-66351419 : ℚ)/100000000+1/245) := rfl
private theorem nbshape41_3 : NB 41 3 = intv ((-5836275 : ℚ)/1000000000) ((-5758018 : ℚ)/1000000000) := rfl
private theorem rawshape42_0 : rawBox 42 0 = intv ((2089843 : ℚ)/100000000-1/245) ((2089843 : ℚ)/100000000+1/245) := rfl
private theorem nbshape42_0 : NB 42 0 = intv ((111170 : ℚ)/1000000000) ((180084 : ℚ)/1000000000) := rfl
private theorem rawshape42_1 : rawBox 42 1 = intv ((-3583853 : ℚ)/100000000-1/245) ((-3583853 : ℚ)/100000000+1/245) := rfl
private theorem nbshape42_1 : NB 42 1 = intv ((-236201 : ℚ)/1000000000) ((-151738 : ℚ)/1000000000) := rfl
private theorem rawshape42_2 : rawBox 42 2 = intv ((9507361 : ℚ)/100000000-1/245) ((9507361 : ℚ)/100000000+1/245) := rfl
private theorem nbshape42_2 : NB 42 2 = intv ((661756 : ℚ)/1000000000) ((732486 : ℚ)/1000000000) := rfl
private theorem rawshape42_3 : rawBox 42 3 = intv ((-691589 : ℚ)/100000000-1/245) ((-691589 : ℚ)/100000000+1/245) := rfl
private theorem nbshape42_3 : NB 42 3 = intv ((-151144 : ℚ)/1000000000) ((-72888 : ℚ)/1000000000) := rfl
private theorem rawshape43_0 : rawBox 43 0 = intv ((2090000 : ℚ)/100000000-1/245) ((2090000 : ℚ)/100000000+1/245) := rfl
private theorem nbshape43_0 : NB 43 0 = intv ((111180 : ℚ)/1000000000) ((180095 : ℚ)/1000000000) := rfl
private theorem rawshape43_1 : rawBox 43 1 = intv ((-3584122 : ℚ)/100000000-1/245) ((-3584122 : ℚ)/100000000+1/245) := rfl
private theorem nbshape43_1 : NB 43 1 = intv ((-236215 : ℚ)/1000000000) ((-151752 : ℚ)/1000000000) := rfl
private theorem rawshape43_2 : rawBox 43 2 = intv ((9508074 : ℚ)/100000000-1/245) ((9508074 : ℚ)/100000000+1/245) := rfl
private theorem nbshape43_2 : NB 43 2 = intv ((661808 : ℚ)/1000000000) ((732538 : ℚ)/1000000000) := rfl
private theorem rawshape43_3 : rawBox 43 3 = intv ((-691641 : ℚ)/100000000-1/245) ((-691641 : ℚ)/100000000+1/245) := rfl
private theorem nbshape43_3 : NB 43 3 = intv ((-151152 : ℚ)/1000000000) ((-72896 : ℚ)/1000000000) := rfl
private theorem rawshape44_0 : rawBox 44 0 = intv ((2588161 : ℚ)/100000000-1/245) ((2588161 : ℚ)/100000000+1/245) := rfl
private theorem nbshape44_0 : NB 44 0 = intv ((145894 : ℚ)/1000000000) ((214808 : ℚ)/1000000000) := rfl
private theorem rawshape44_1 : rawBox 44 1 = intv ((-4438413 : ℚ)/100000000-1/245) ((-4438413 : ℚ)/100000000+1/245) := rfl
private theorem nbshape44_1 : NB 44 1 = intv ((-282452 : ℚ)/1000000000) ((-197989 : ℚ)/1000000000) := rfl
private theorem rawshape44_2 : rawBox 44 2 = intv ((11774367 : ℚ)/100000000-1/245) ((11774367 : ℚ)/100000000+1/245) := rfl
private theorem nbshape44_2 : NB 44 2 = intv ((827982 : ℚ)/1000000000) ((898713 : ℚ)/1000000000) := rfl
private theorem rawshape44_3 : rawBox 44 3 = intv ((-856496 : ℚ)/100000000-1/245) ((-856496 : ℚ)/100000000+1/245) := rfl
private theorem nbshape44_3 : NB 44 3 = intv ((-177854 : ℚ)/1000000000) ((-99598 : ℚ)/1000000000) := rfl

private theorem box0_0 : Contains (NB 0 0) (metricBox 0 0) := by
  simp only [nbshape0_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape0_0,rawshape0_1,rawshape0_2,rawshape0_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box0_1 : Contains (NB 0 1) (metricBox 0 1) := by
  simp only [nbshape0_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape0_0,rawshape0_1,rawshape0_2,rawshape0_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box0_2 : Contains (NB 0 2) (metricBox 0 2) := by
  simp only [nbshape0_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape0_0,rawshape0_1,rawshape0_2,rawshape0_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box0_3 : Contains (NB 0 3) (metricBox 0 3) := by
  simp only [nbshape0_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape0_0,rawshape0_1,rawshape0_2,rawshape0_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box1_0 : Contains (NB 1 0) (metricBox 1 0) := by
  simp only [nbshape1_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape1_0,rawshape1_1,rawshape1_2,rawshape1_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box1_1 : Contains (NB 1 1) (metricBox 1 1) := by
  simp only [nbshape1_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape1_0,rawshape1_1,rawshape1_2,rawshape1_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box1_2 : Contains (NB 1 2) (metricBox 1 2) := by
  simp only [nbshape1_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape1_0,rawshape1_1,rawshape1_2,rawshape1_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box1_3 : Contains (NB 1 3) (metricBox 1 3) := by
  simp only [nbshape1_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape1_0,rawshape1_1,rawshape1_2,rawshape1_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box2_0 : Contains (NB 2 0) (metricBox 2 0) := by
  simp only [nbshape2_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape2_0,rawshape2_1,rawshape2_2,rawshape2_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box2_1 : Contains (NB 2 1) (metricBox 2 1) := by
  simp only [nbshape2_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape2_0,rawshape2_1,rawshape2_2,rawshape2_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box2_2 : Contains (NB 2 2) (metricBox 2 2) := by
  simp only [nbshape2_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape2_0,rawshape2_1,rawshape2_2,rawshape2_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box2_3 : Contains (NB 2 3) (metricBox 2 3) := by
  simp only [nbshape2_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape2_0,rawshape2_1,rawshape2_2,rawshape2_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box3_0 : Contains (NB 3 0) (metricBox 3 0) := by
  simp only [nbshape3_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape3_0,rawshape3_1,rawshape3_2,rawshape3_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box3_1 : Contains (NB 3 1) (metricBox 3 1) := by
  simp only [nbshape3_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape3_0,rawshape3_1,rawshape3_2,rawshape3_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box3_2 : Contains (NB 3 2) (metricBox 3 2) := by
  simp only [nbshape3_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape3_0,rawshape3_1,rawshape3_2,rawshape3_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box3_3 : Contains (NB 3 3) (metricBox 3 3) := by
  simp only [nbshape3_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape3_0,rawshape3_1,rawshape3_2,rawshape3_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box4_0 : Contains (NB 4 0) (metricBox 4 0) := by
  simp only [nbshape4_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape4_0,rawshape4_1,rawshape4_2,rawshape4_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box4_1 : Contains (NB 4 1) (metricBox 4 1) := by
  simp only [nbshape4_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape4_0,rawshape4_1,rawshape4_2,rawshape4_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box4_2 : Contains (NB 4 2) (metricBox 4 2) := by
  simp only [nbshape4_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape4_0,rawshape4_1,rawshape4_2,rawshape4_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box4_3 : Contains (NB 4 3) (metricBox 4 3) := by
  simp only [nbshape4_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape4_0,rawshape4_1,rawshape4_2,rawshape4_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box5_0 : Contains (NB 5 0) (metricBox 5 0) := by
  simp only [nbshape5_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape5_0,rawshape5_1,rawshape5_2,rawshape5_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box5_1 : Contains (NB 5 1) (metricBox 5 1) := by
  simp only [nbshape5_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape5_0,rawshape5_1,rawshape5_2,rawshape5_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box5_2 : Contains (NB 5 2) (metricBox 5 2) := by
  simp only [nbshape5_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape5_0,rawshape5_1,rawshape5_2,rawshape5_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box5_3 : Contains (NB 5 3) (metricBox 5 3) := by
  simp only [nbshape5_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape5_0,rawshape5_1,rawshape5_2,rawshape5_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box6_0 : Contains (NB 6 0) (metricBox 6 0) := by
  simp only [nbshape6_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape6_0,rawshape6_1,rawshape6_2,rawshape6_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box6_1 : Contains (NB 6 1) (metricBox 6 1) := by
  simp only [nbshape6_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape6_0,rawshape6_1,rawshape6_2,rawshape6_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box6_2 : Contains (NB 6 2) (metricBox 6 2) := by
  simp only [nbshape6_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape6_0,rawshape6_1,rawshape6_2,rawshape6_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box6_3 : Contains (NB 6 3) (metricBox 6 3) := by
  simp only [nbshape6_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape6_0,rawshape6_1,rawshape6_2,rawshape6_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box7_0 : Contains (NB 7 0) (metricBox 7 0) := by
  simp only [nbshape7_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape7_0,rawshape7_1,rawshape7_2,rawshape7_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box7_1 : Contains (NB 7 1) (metricBox 7 1) := by
  simp only [nbshape7_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape7_0,rawshape7_1,rawshape7_2,rawshape7_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box7_2 : Contains (NB 7 2) (metricBox 7 2) := by
  simp only [nbshape7_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape7_0,rawshape7_1,rawshape7_2,rawshape7_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box7_3 : Contains (NB 7 3) (metricBox 7 3) := by
  simp only [nbshape7_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape7_0,rawshape7_1,rawshape7_2,rawshape7_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box8_0 : Contains (NB 8 0) (metricBox 8 0) := by
  simp only [nbshape8_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape8_0,rawshape8_1,rawshape8_2,rawshape8_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box8_1 : Contains (NB 8 1) (metricBox 8 1) := by
  simp only [nbshape8_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape8_0,rawshape8_1,rawshape8_2,rawshape8_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box8_2 : Contains (NB 8 2) (metricBox 8 2) := by
  simp only [nbshape8_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape8_0,rawshape8_1,rawshape8_2,rawshape8_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box8_3 : Contains (NB 8 3) (metricBox 8 3) := by
  simp only [nbshape8_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape8_0,rawshape8_1,rawshape8_2,rawshape8_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box9_0 : Contains (NB 9 0) (metricBox 9 0) := by
  simp only [nbshape9_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape9_0,rawshape9_1,rawshape9_2,rawshape9_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box9_1 : Contains (NB 9 1) (metricBox 9 1) := by
  simp only [nbshape9_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape9_0,rawshape9_1,rawshape9_2,rawshape9_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box9_2 : Contains (NB 9 2) (metricBox 9 2) := by
  simp only [nbshape9_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape9_0,rawshape9_1,rawshape9_2,rawshape9_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box9_3 : Contains (NB 9 3) (metricBox 9 3) := by
  simp only [nbshape9_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape9_0,rawshape9_1,rawshape9_2,rawshape9_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box10_0 : Contains (NB 10 0) (metricBox 10 0) := by
  simp only [nbshape10_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape10_0,rawshape10_1,rawshape10_2,rawshape10_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box10_1 : Contains (NB 10 1) (metricBox 10 1) := by
  simp only [nbshape10_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape10_0,rawshape10_1,rawshape10_2,rawshape10_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box10_2 : Contains (NB 10 2) (metricBox 10 2) := by
  simp only [nbshape10_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape10_0,rawshape10_1,rawshape10_2,rawshape10_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box10_3 : Contains (NB 10 3) (metricBox 10 3) := by
  simp only [nbshape10_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape10_0,rawshape10_1,rawshape10_2,rawshape10_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box11_0 : Contains (NB 11 0) (metricBox 11 0) := by
  simp only [nbshape11_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape11_0,rawshape11_1,rawshape11_2,rawshape11_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box11_1 : Contains (NB 11 1) (metricBox 11 1) := by
  simp only [nbshape11_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape11_0,rawshape11_1,rawshape11_2,rawshape11_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box11_2 : Contains (NB 11 2) (metricBox 11 2) := by
  simp only [nbshape11_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape11_0,rawshape11_1,rawshape11_2,rawshape11_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box11_3 : Contains (NB 11 3) (metricBox 11 3) := by
  simp only [nbshape11_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape11_0,rawshape11_1,rawshape11_2,rawshape11_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box12_0 : Contains (NB 12 0) (metricBox 12 0) := by
  simp only [nbshape12_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape12_0,rawshape12_1,rawshape12_2,rawshape12_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box12_1 : Contains (NB 12 1) (metricBox 12 1) := by
  simp only [nbshape12_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape12_0,rawshape12_1,rawshape12_2,rawshape12_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box12_2 : Contains (NB 12 2) (metricBox 12 2) := by
  simp only [nbshape12_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape12_0,rawshape12_1,rawshape12_2,rawshape12_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box12_3 : Contains (NB 12 3) (metricBox 12 3) := by
  simp only [nbshape12_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape12_0,rawshape12_1,rawshape12_2,rawshape12_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box13_0 : Contains (NB 13 0) (metricBox 13 0) := by
  simp only [nbshape13_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape13_0,rawshape13_1,rawshape13_2,rawshape13_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box13_1 : Contains (NB 13 1) (metricBox 13 1) := by
  simp only [nbshape13_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape13_0,rawshape13_1,rawshape13_2,rawshape13_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box13_2 : Contains (NB 13 2) (metricBox 13 2) := by
  simp only [nbshape13_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape13_0,rawshape13_1,rawshape13_2,rawshape13_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box13_3 : Contains (NB 13 3) (metricBox 13 3) := by
  simp only [nbshape13_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape13_0,rawshape13_1,rawshape13_2,rawshape13_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box14_0 : Contains (NB 14 0) (metricBox 14 0) := by
  simp only [nbshape14_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape14_0,rawshape14_1,rawshape14_2,rawshape14_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box14_1 : Contains (NB 14 1) (metricBox 14 1) := by
  simp only [nbshape14_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape14_0,rawshape14_1,rawshape14_2,rawshape14_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box14_2 : Contains (NB 14 2) (metricBox 14 2) := by
  simp only [nbshape14_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape14_0,rawshape14_1,rawshape14_2,rawshape14_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box14_3 : Contains (NB 14 3) (metricBox 14 3) := by
  simp only [nbshape14_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape14_0,rawshape14_1,rawshape14_2,rawshape14_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box15_0 : Contains (NB 15 0) (metricBox 15 0) := by
  simp only [nbshape15_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape15_0,rawshape15_1,rawshape15_2,rawshape15_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box15_1 : Contains (NB 15 1) (metricBox 15 1) := by
  simp only [nbshape15_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape15_0,rawshape15_1,rawshape15_2,rawshape15_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box15_2 : Contains (NB 15 2) (metricBox 15 2) := by
  simp only [nbshape15_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape15_0,rawshape15_1,rawshape15_2,rawshape15_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box15_3 : Contains (NB 15 3) (metricBox 15 3) := by
  simp only [nbshape15_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape15_0,rawshape15_1,rawshape15_2,rawshape15_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box16_0 : Contains (NB 16 0) (metricBox 16 0) := by
  simp only [nbshape16_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape16_0,rawshape16_1,rawshape16_2,rawshape16_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box16_1 : Contains (NB 16 1) (metricBox 16 1) := by
  simp only [nbshape16_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape16_0,rawshape16_1,rawshape16_2,rawshape16_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box16_2 : Contains (NB 16 2) (metricBox 16 2) := by
  simp only [nbshape16_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape16_0,rawshape16_1,rawshape16_2,rawshape16_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box16_3 : Contains (NB 16 3) (metricBox 16 3) := by
  simp only [nbshape16_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape16_0,rawshape16_1,rawshape16_2,rawshape16_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box17_0 : Contains (NB 17 0) (metricBox 17 0) := by
  simp only [nbshape17_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape17_0,rawshape17_1,rawshape17_2,rawshape17_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box17_1 : Contains (NB 17 1) (metricBox 17 1) := by
  simp only [nbshape17_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape17_0,rawshape17_1,rawshape17_2,rawshape17_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box17_2 : Contains (NB 17 2) (metricBox 17 2) := by
  simp only [nbshape17_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape17_0,rawshape17_1,rawshape17_2,rawshape17_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box17_3 : Contains (NB 17 3) (metricBox 17 3) := by
  simp only [nbshape17_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape17_0,rawshape17_1,rawshape17_2,rawshape17_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box18_0 : Contains (NB 18 0) (metricBox 18 0) := by
  simp only [nbshape18_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape18_0,rawshape18_1,rawshape18_2,rawshape18_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box18_1 : Contains (NB 18 1) (metricBox 18 1) := by
  simp only [nbshape18_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape18_0,rawshape18_1,rawshape18_2,rawshape18_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box18_2 : Contains (NB 18 2) (metricBox 18 2) := by
  simp only [nbshape18_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape18_0,rawshape18_1,rawshape18_2,rawshape18_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box18_3 : Contains (NB 18 3) (metricBox 18 3) := by
  simp only [nbshape18_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape18_0,rawshape18_1,rawshape18_2,rawshape18_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box19_0 : Contains (NB 19 0) (metricBox 19 0) := by
  simp only [nbshape19_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape19_0,rawshape19_1,rawshape19_2,rawshape19_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box19_1 : Contains (NB 19 1) (metricBox 19 1) := by
  simp only [nbshape19_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape19_0,rawshape19_1,rawshape19_2,rawshape19_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box19_2 : Contains (NB 19 2) (metricBox 19 2) := by
  simp only [nbshape19_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape19_0,rawshape19_1,rawshape19_2,rawshape19_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box19_3 : Contains (NB 19 3) (metricBox 19 3) := by
  simp only [nbshape19_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape19_0,rawshape19_1,rawshape19_2,rawshape19_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box20_0 : Contains (NB 20 0) (metricBox 20 0) := by
  simp only [nbshape20_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape20_0,rawshape20_1,rawshape20_2,rawshape20_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box20_1 : Contains (NB 20 1) (metricBox 20 1) := by
  simp only [nbshape20_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape20_0,rawshape20_1,rawshape20_2,rawshape20_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box20_2 : Contains (NB 20 2) (metricBox 20 2) := by
  simp only [nbshape20_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape20_0,rawshape20_1,rawshape20_2,rawshape20_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box20_3 : Contains (NB 20 3) (metricBox 20 3) := by
  simp only [nbshape20_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape20_0,rawshape20_1,rawshape20_2,rawshape20_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box21_0 : Contains (NB 21 0) (metricBox 21 0) := by
  simp only [nbshape21_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape21_0,rawshape21_1,rawshape21_2,rawshape21_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box21_1 : Contains (NB 21 1) (metricBox 21 1) := by
  simp only [nbshape21_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape21_0,rawshape21_1,rawshape21_2,rawshape21_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box21_2 : Contains (NB 21 2) (metricBox 21 2) := by
  simp only [nbshape21_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape21_0,rawshape21_1,rawshape21_2,rawshape21_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box21_3 : Contains (NB 21 3) (metricBox 21 3) := by
  simp only [nbshape21_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape21_0,rawshape21_1,rawshape21_2,rawshape21_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box22_0 : Contains (NB 22 0) (metricBox 22 0) := by
  simp only [nbshape22_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape22_0,rawshape22_1,rawshape22_2,rawshape22_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box22_1 : Contains (NB 22 1) (metricBox 22 1) := by
  simp only [nbshape22_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape22_0,rawshape22_1,rawshape22_2,rawshape22_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box22_2 : Contains (NB 22 2) (metricBox 22 2) := by
  simp only [nbshape22_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape22_0,rawshape22_1,rawshape22_2,rawshape22_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box22_3 : Contains (NB 22 3) (metricBox 22 3) := by
  simp only [nbshape22_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape22_0,rawshape22_1,rawshape22_2,rawshape22_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box23_0 : Contains (NB 23 0) (metricBox 23 0) := by
  simp only [nbshape23_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape23_0,rawshape23_1,rawshape23_2,rawshape23_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box23_1 : Contains (NB 23 1) (metricBox 23 1) := by
  simp only [nbshape23_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape23_0,rawshape23_1,rawshape23_2,rawshape23_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box23_2 : Contains (NB 23 2) (metricBox 23 2) := by
  simp only [nbshape23_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape23_0,rawshape23_1,rawshape23_2,rawshape23_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box23_3 : Contains (NB 23 3) (metricBox 23 3) := by
  simp only [nbshape23_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape23_0,rawshape23_1,rawshape23_2,rawshape23_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box24_0 : Contains (NB 24 0) (metricBox 24 0) := by
  simp only [nbshape24_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape24_0,rawshape24_1,rawshape24_2,rawshape24_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box24_1 : Contains (NB 24 1) (metricBox 24 1) := by
  simp only [nbshape24_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape24_0,rawshape24_1,rawshape24_2,rawshape24_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box24_2 : Contains (NB 24 2) (metricBox 24 2) := by
  simp only [nbshape24_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape24_0,rawshape24_1,rawshape24_2,rawshape24_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box24_3 : Contains (NB 24 3) (metricBox 24 3) := by
  simp only [nbshape24_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape24_0,rawshape24_1,rawshape24_2,rawshape24_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box25_0 : Contains (NB 25 0) (metricBox 25 0) := by
  simp only [nbshape25_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape25_0,rawshape25_1,rawshape25_2,rawshape25_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box25_1 : Contains (NB 25 1) (metricBox 25 1) := by
  simp only [nbshape25_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape25_0,rawshape25_1,rawshape25_2,rawshape25_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box25_2 : Contains (NB 25 2) (metricBox 25 2) := by
  simp only [nbshape25_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape25_0,rawshape25_1,rawshape25_2,rawshape25_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box25_3 : Contains (NB 25 3) (metricBox 25 3) := by
  simp only [nbshape25_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape25_0,rawshape25_1,rawshape25_2,rawshape25_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box26_0 : Contains (NB 26 0) (metricBox 26 0) := by
  simp only [nbshape26_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape26_0,rawshape26_1,rawshape26_2,rawshape26_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box26_1 : Contains (NB 26 1) (metricBox 26 1) := by
  simp only [nbshape26_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape26_0,rawshape26_1,rawshape26_2,rawshape26_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box26_2 : Contains (NB 26 2) (metricBox 26 2) := by
  simp only [nbshape26_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape26_0,rawshape26_1,rawshape26_2,rawshape26_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box26_3 : Contains (NB 26 3) (metricBox 26 3) := by
  simp only [nbshape26_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape26_0,rawshape26_1,rawshape26_2,rawshape26_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box27_0 : Contains (NB 27 0) (metricBox 27 0) := by
  simp only [nbshape27_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape27_0,rawshape27_1,rawshape27_2,rawshape27_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box27_1 : Contains (NB 27 1) (metricBox 27 1) := by
  simp only [nbshape27_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape27_0,rawshape27_1,rawshape27_2,rawshape27_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box27_2 : Contains (NB 27 2) (metricBox 27 2) := by
  simp only [nbshape27_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape27_0,rawshape27_1,rawshape27_2,rawshape27_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box27_3 : Contains (NB 27 3) (metricBox 27 3) := by
  simp only [nbshape27_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape27_0,rawshape27_1,rawshape27_2,rawshape27_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box28_0 : Contains (NB 28 0) (metricBox 28 0) := by
  simp only [nbshape28_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape28_0,rawshape28_1,rawshape28_2,rawshape28_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box28_1 : Contains (NB 28 1) (metricBox 28 1) := by
  simp only [nbshape28_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape28_0,rawshape28_1,rawshape28_2,rawshape28_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box28_2 : Contains (NB 28 2) (metricBox 28 2) := by
  simp only [nbshape28_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape28_0,rawshape28_1,rawshape28_2,rawshape28_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box28_3 : Contains (NB 28 3) (metricBox 28 3) := by
  simp only [nbshape28_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape28_0,rawshape28_1,rawshape28_2,rawshape28_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box29_0 : Contains (NB 29 0) (metricBox 29 0) := by
  simp only [nbshape29_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape29_0,rawshape29_1,rawshape29_2,rawshape29_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box29_1 : Contains (NB 29 1) (metricBox 29 1) := by
  simp only [nbshape29_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape29_0,rawshape29_1,rawshape29_2,rawshape29_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box29_2 : Contains (NB 29 2) (metricBox 29 2) := by
  simp only [nbshape29_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape29_0,rawshape29_1,rawshape29_2,rawshape29_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box29_3 : Contains (NB 29 3) (metricBox 29 3) := by
  simp only [nbshape29_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape29_0,rawshape29_1,rawshape29_2,rawshape29_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box30_0 : Contains (NB 30 0) (metricBox 30 0) := by
  simp only [nbshape30_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape30_0,rawshape30_1,rawshape30_2,rawshape30_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box30_1 : Contains (NB 30 1) (metricBox 30 1) := by
  simp only [nbshape30_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape30_0,rawshape30_1,rawshape30_2,rawshape30_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box30_2 : Contains (NB 30 2) (metricBox 30 2) := by
  simp only [nbshape30_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape30_0,rawshape30_1,rawshape30_2,rawshape30_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box30_3 : Contains (NB 30 3) (metricBox 30 3) := by
  simp only [nbshape30_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape30_0,rawshape30_1,rawshape30_2,rawshape30_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box31_0 : Contains (NB 31 0) (metricBox 31 0) := by
  simp only [nbshape31_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape31_0,rawshape31_1,rawshape31_2,rawshape31_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box31_1 : Contains (NB 31 1) (metricBox 31 1) := by
  simp only [nbshape31_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape31_0,rawshape31_1,rawshape31_2,rawshape31_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box31_2 : Contains (NB 31 2) (metricBox 31 2) := by
  simp only [nbshape31_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape31_0,rawshape31_1,rawshape31_2,rawshape31_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box31_3 : Contains (NB 31 3) (metricBox 31 3) := by
  simp only [nbshape31_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape31_0,rawshape31_1,rawshape31_2,rawshape31_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box32_0 : Contains (NB 32 0) (metricBox 32 0) := by
  simp only [nbshape32_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape32_0,rawshape32_1,rawshape32_2,rawshape32_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box32_1 : Contains (NB 32 1) (metricBox 32 1) := by
  simp only [nbshape32_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape32_0,rawshape32_1,rawshape32_2,rawshape32_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box32_2 : Contains (NB 32 2) (metricBox 32 2) := by
  simp only [nbshape32_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape32_0,rawshape32_1,rawshape32_2,rawshape32_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box32_3 : Contains (NB 32 3) (metricBox 32 3) := by
  simp only [nbshape32_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape32_0,rawshape32_1,rawshape32_2,rawshape32_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box33_0 : Contains (NB 33 0) (metricBox 33 0) := by
  simp only [nbshape33_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape33_0,rawshape33_1,rawshape33_2,rawshape33_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box33_1 : Contains (NB 33 1) (metricBox 33 1) := by
  simp only [nbshape33_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape33_0,rawshape33_1,rawshape33_2,rawshape33_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box33_2 : Contains (NB 33 2) (metricBox 33 2) := by
  simp only [nbshape33_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape33_0,rawshape33_1,rawshape33_2,rawshape33_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box33_3 : Contains (NB 33 3) (metricBox 33 3) := by
  simp only [nbshape33_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape33_0,rawshape33_1,rawshape33_2,rawshape33_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box34_0 : Contains (NB 34 0) (metricBox 34 0) := by
  simp only [nbshape34_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape34_0,rawshape34_1,rawshape34_2,rawshape34_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box34_1 : Contains (NB 34 1) (metricBox 34 1) := by
  simp only [nbshape34_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape34_0,rawshape34_1,rawshape34_2,rawshape34_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box34_2 : Contains (NB 34 2) (metricBox 34 2) := by
  simp only [nbshape34_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape34_0,rawshape34_1,rawshape34_2,rawshape34_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box34_3 : Contains (NB 34 3) (metricBox 34 3) := by
  simp only [nbshape34_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape34_0,rawshape34_1,rawshape34_2,rawshape34_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box35_0 : Contains (NB 35 0) (metricBox 35 0) := by
  simp only [nbshape35_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape35_0,rawshape35_1,rawshape35_2,rawshape35_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box35_1 : Contains (NB 35 1) (metricBox 35 1) := by
  simp only [nbshape35_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape35_0,rawshape35_1,rawshape35_2,rawshape35_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box35_2 : Contains (NB 35 2) (metricBox 35 2) := by
  simp only [nbshape35_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape35_0,rawshape35_1,rawshape35_2,rawshape35_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box35_3 : Contains (NB 35 3) (metricBox 35 3) := by
  simp only [nbshape35_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape35_0,rawshape35_1,rawshape35_2,rawshape35_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box36_0 : Contains (NB 36 0) (metricBox 36 0) := by
  simp only [nbshape36_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape36_0,rawshape36_1,rawshape36_2,rawshape36_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box36_1 : Contains (NB 36 1) (metricBox 36 1) := by
  simp only [nbshape36_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape36_0,rawshape36_1,rawshape36_2,rawshape36_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box36_2 : Contains (NB 36 2) (metricBox 36 2) := by
  simp only [nbshape36_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape36_0,rawshape36_1,rawshape36_2,rawshape36_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box36_3 : Contains (NB 36 3) (metricBox 36 3) := by
  simp only [nbshape36_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape36_0,rawshape36_1,rawshape36_2,rawshape36_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box37_0 : Contains (NB 37 0) (metricBox 37 0) := by
  simp only [nbshape37_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape37_0,rawshape37_1,rawshape37_2,rawshape37_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box37_1 : Contains (NB 37 1) (metricBox 37 1) := by
  simp only [nbshape37_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape37_0,rawshape37_1,rawshape37_2,rawshape37_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box37_2 : Contains (NB 37 2) (metricBox 37 2) := by
  simp only [nbshape37_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape37_0,rawshape37_1,rawshape37_2,rawshape37_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box37_3 : Contains (NB 37 3) (metricBox 37 3) := by
  simp only [nbshape37_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape37_0,rawshape37_1,rawshape37_2,rawshape37_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box38_0 : Contains (NB 38 0) (metricBox 38 0) := by
  simp only [nbshape38_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape38_0,rawshape38_1,rawshape38_2,rawshape38_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box38_1 : Contains (NB 38 1) (metricBox 38 1) := by
  simp only [nbshape38_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape38_0,rawshape38_1,rawshape38_2,rawshape38_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box38_2 : Contains (NB 38 2) (metricBox 38 2) := by
  simp only [nbshape38_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape38_0,rawshape38_1,rawshape38_2,rawshape38_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box38_3 : Contains (NB 38 3) (metricBox 38 3) := by
  simp only [nbshape38_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape38_0,rawshape38_1,rawshape38_2,rawshape38_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box39_0 : Contains (NB 39 0) (metricBox 39 0) := by
  simp only [nbshape39_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape39_0,rawshape39_1,rawshape39_2,rawshape39_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box39_1 : Contains (NB 39 1) (metricBox 39 1) := by
  simp only [nbshape39_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape39_0,rawshape39_1,rawshape39_2,rawshape39_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box39_2 : Contains (NB 39 2) (metricBox 39 2) := by
  simp only [nbshape39_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape39_0,rawshape39_1,rawshape39_2,rawshape39_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box39_3 : Contains (NB 39 3) (metricBox 39 3) := by
  simp only [nbshape39_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape39_0,rawshape39_1,rawshape39_2,rawshape39_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box40_0 : Contains (NB 40 0) (metricBox 40 0) := by
  simp only [nbshape40_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape40_0,rawshape40_1,rawshape40_2,rawshape40_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box40_1 : Contains (NB 40 1) (metricBox 40 1) := by
  simp only [nbshape40_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape40_0,rawshape40_1,rawshape40_2,rawshape40_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box40_2 : Contains (NB 40 2) (metricBox 40 2) := by
  simp only [nbshape40_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape40_0,rawshape40_1,rawshape40_2,rawshape40_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box40_3 : Contains (NB 40 3) (metricBox 40 3) := by
  simp only [nbshape40_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape40_0,rawshape40_1,rawshape40_2,rawshape40_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box41_0 : Contains (NB 41 0) (metricBox 41 0) := by
  simp only [nbshape41_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape41_0,rawshape41_1,rawshape41_2,rawshape41_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box41_1 : Contains (NB 41 1) (metricBox 41 1) := by
  simp only [nbshape41_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape41_0,rawshape41_1,rawshape41_2,rawshape41_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box41_2 : Contains (NB 41 2) (metricBox 41 2) := by
  simp only [nbshape41_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape41_0,rawshape41_1,rawshape41_2,rawshape41_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box41_3 : Contains (NB 41 3) (metricBox 41 3) := by
  simp only [nbshape41_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape41_0,rawshape41_1,rawshape41_2,rawshape41_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box42_0 : Contains (NB 42 0) (metricBox 42 0) := by
  simp only [nbshape42_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape42_0,rawshape42_1,rawshape42_2,rawshape42_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box42_1 : Contains (NB 42 1) (metricBox 42 1) := by
  simp only [nbshape42_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape42_0,rawshape42_1,rawshape42_2,rawshape42_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box42_2 : Contains (NB 42 2) (metricBox 42 2) := by
  simp only [nbshape42_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape42_0,rawshape42_1,rawshape42_2,rawshape42_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box42_3 : Contains (NB 42 3) (metricBox 42 3) := by
  simp only [nbshape42_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape42_0,rawshape42_1,rawshape42_2,rawshape42_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box43_0 : Contains (NB 43 0) (metricBox 43 0) := by
  simp only [nbshape43_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape43_0,rawshape43_1,rawshape43_2,rawshape43_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box43_1 : Contains (NB 43 1) (metricBox 43 1) := by
  simp only [nbshape43_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape43_0,rawshape43_1,rawshape43_2,rawshape43_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box43_2 : Contains (NB 43 2) (metricBox 43 2) := by
  simp only [nbshape43_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape43_0,rawshape43_1,rawshape43_2,rawshape43_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box43_3 : Contains (NB 43 3) (metricBox 43 3) := by
  simp only [nbshape43_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape43_0,rawshape43_1,rawshape43_2,rawshape43_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box44_0 : Contains (NB 44 0) (metricBox 44 0) := by
  simp only [nbshape44_0,metricBox,sumI,Fin.sum_univ_four,
    rawshape44_0,rawshape44_1,rawshape44_2,rawshape44_3,
    rshape0_0,rshape1_0,rshape2_0,rshape3_0,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box44_1 : Contains (NB 44 1) (metricBox 44 1) := by
  simp only [nbshape44_1,metricBox,sumI,Fin.sum_univ_four,
    rawshape44_0,rawshape44_1,rawshape44_2,rawshape44_3,
    rshape0_1,rshape1_1,rshape2_1,rshape3_1,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box44_2 : Contains (NB 44 2) (metricBox 44 2) := by
  simp only [nbshape44_2,metricBox,sumI,Fin.sum_univ_four,
    rawshape44_0,rawshape44_1,rawshape44_2,rawshape44_3,
    rshape0_2,rshape1_2,rshape2_2,rshape3_2,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]
private theorem box44_3 : Contains (NB 44 3) (metricBox 44 3) := by
  simp only [nbshape44_3,metricBox,sumI,Fin.sum_univ_four,
    rawshape44_0,rawshape44_1,rawshape44_2,rawshape44_3,
    rshape0_3,rshape1_3,rshape2_3,rshape3_3,Fin.reduceFinMk]
  norm_num [Contains,RatInterval.mul,ofRat,intv]

theorem NB_contains (e : Fin 45) (a : Fin 4) : Contains (NB e a) (metricBox e a) := by
  fin_cases e <;> fin_cases a
  · exact box0_0
  · exact box0_1
  · exact box0_2
  · exact box0_3
  · exact box1_0
  · exact box1_1
  · exact box1_2
  · exact box1_3
  · exact box2_0
  · exact box2_1
  · exact box2_2
  · exact box2_3
  · exact box3_0
  · exact box3_1
  · exact box3_2
  · exact box3_3
  · exact box4_0
  · exact box4_1
  · exact box4_2
  · exact box4_3
  · exact box5_0
  · exact box5_1
  · exact box5_2
  · exact box5_3
  · exact box6_0
  · exact box6_1
  · exact box6_2
  · exact box6_3
  · exact box7_0
  · exact box7_1
  · exact box7_2
  · exact box7_3
  · exact box8_0
  · exact box8_1
  · exact box8_2
  · exact box8_3
  · exact box9_0
  · exact box9_1
  · exact box9_2
  · exact box9_3
  · exact box10_0
  · exact box10_1
  · exact box10_2
  · exact box10_3
  · exact box11_0
  · exact box11_1
  · exact box11_2
  · exact box11_3
  · exact box12_0
  · exact box12_1
  · exact box12_2
  · exact box12_3
  · exact box13_0
  · exact box13_1
  · exact box13_2
  · exact box13_3
  · exact box14_0
  · exact box14_1
  · exact box14_2
  · exact box14_3
  · exact box15_0
  · exact box15_1
  · exact box15_2
  · exact box15_3
  · exact box16_0
  · exact box16_1
  · exact box16_2
  · exact box16_3
  · exact box17_0
  · exact box17_1
  · exact box17_2
  · exact box17_3
  · exact box18_0
  · exact box18_1
  · exact box18_2
  · exact box18_3
  · exact box19_0
  · exact box19_1
  · exact box19_2
  · exact box19_3
  · exact box20_0
  · exact box20_1
  · exact box20_2
  · exact box20_3
  · exact box21_0
  · exact box21_1
  · exact box21_2
  · exact box21_3
  · exact box22_0
  · exact box22_1
  · exact box22_2
  · exact box22_3
  · exact box23_0
  · exact box23_1
  · exact box23_2
  · exact box23_3
  · exact box24_0
  · exact box24_1
  · exact box24_2
  · exact box24_3
  · exact box25_0
  · exact box25_1
  · exact box25_2
  · exact box25_3
  · exact box26_0
  · exact box26_1
  · exact box26_2
  · exact box26_3
  · exact box27_0
  · exact box27_1
  · exact box27_2
  · exact box27_3
  · exact box28_0
  · exact box28_1
  · exact box28_2
  · exact box28_3
  · exact box29_0
  · exact box29_1
  · exact box29_2
  · exact box29_3
  · exact box30_0
  · exact box30_1
  · exact box30_2
  · exact box30_3
  · exact box31_0
  · exact box31_1
  · exact box31_2
  · exact box31_3
  · exact box32_0
  · exact box32_1
  · exact box32_2
  · exact box32_3
  · exact box33_0
  · exact box33_1
  · exact box33_2
  · exact box33_3
  · exact box34_0
  · exact box34_1
  · exact box34_2
  · exact box34_3
  · exact box35_0
  · exact box35_1
  · exact box35_2
  · exact box35_3
  · exact box36_0
  · exact box36_1
  · exact box36_2
  · exact box36_3
  · exact box37_0
  · exact box37_1
  · exact box37_2
  · exact box37_3
  · exact box38_0
  · exact box38_1
  · exact box38_2
  · exact box38_3
  · exact box39_0
  · exact box39_1
  · exact box39_2
  · exact box39_3
  · exact box40_0
  · exact box40_1
  · exact box40_2
  · exact box40_3
  · exact box41_0
  · exact box41_1
  · exact box41_2
  · exact box41_3
  · exact box42_0
  · exact box42_1
  · exact box42_2
  · exact box42_3
  · exact box43_0
  · exact box43_1
  · exact box43_2
  · exact box43_3
  · exact box44_0
  · exact box44_1
  · exact box44_2
  · exact box44_3

def mag (e : Fin 45) (a : Fin 4) : ℤ := max (-NL e a) (NH e a)
def RowOK (e : Fin 45) : Prop :=
  40000*(∑ a : Fin 4,(mag e a)^2) ≤
    980100*(SourceCompactStressIntervals.loN e)^2
instance rowDecidable (e : Fin 45) : Decidable (RowOK e) := by
  unfold RowOK
  infer_instance

private theorem row0 : RowOK 0 := by decide
private theorem row1 : RowOK 1 := by decide
private theorem row2 : RowOK 2 := by decide
private theorem row3 : RowOK 3 := by decide
private theorem row4 : RowOK 4 := by decide
private theorem row5 : RowOK 5 := by decide
private theorem row6 : RowOK 6 := by decide
private theorem row7 : RowOK 7 := by decide
private theorem row8 : RowOK 8 := by decide
private theorem row9 : RowOK 9 := by decide
private theorem row10 : RowOK 10 := by decide
private theorem row11 : RowOK 11 := by decide
private theorem row12 : RowOK 12 := by decide
private theorem row13 : RowOK 13 := by decide
private theorem row14 : RowOK 14 := by decide
private theorem row15 : RowOK 15 := by decide
private theorem row16 : RowOK 16 := by decide
private theorem row17 : RowOK 17 := by decide
private theorem row18 : RowOK 18 := by decide
private theorem row19 : RowOK 19 := by decide
private theorem row20 : RowOK 20 := by decide
private theorem row21 : RowOK 21 := by decide
private theorem row22 : RowOK 22 := by decide
private theorem row23 : RowOK 23 := by decide
private theorem row24 : RowOK 24 := by decide
private theorem row25 : RowOK 25 := by decide
private theorem row26 : RowOK 26 := by decide
private theorem row27 : RowOK 27 := by decide
private theorem row28 : RowOK 28 := by decide
private theorem row29 : RowOK 29 := by decide
private theorem row30 : RowOK 30 := by decide
private theorem row31 : RowOK 31 := by decide
private theorem row32 : RowOK 32 := by decide
private theorem row33 : RowOK 33 := by decide
private theorem row34 : RowOK 34 := by decide
private theorem row35 : RowOK 35 := by decide
private theorem row36 : RowOK 36 := by decide
private theorem row37 : RowOK 37 := by decide
private theorem row38 : RowOK 38 := by decide
private theorem row39 : RowOK 39 := by decide
private theorem row40 : RowOK 40 := by decide
private theorem row41 : RowOK 41 := by decide
private theorem row42 : RowOK 42 := by decide
private theorem row43 : RowOK 43 := by decide
private theorem row44 : RowOK 44 := by decide

theorem all_rows (e : Fin 45) : RowOK e := by
  fin_cases e
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42
  · exact row43
  · exact row44

theorem loN_nonneg : ∀ e : Fin 45, 0 ≤ SourceCompactStressIntervals.loN e := by decide

end
end N11Formalization.SourceRelativeNormPacket
#check @N11Formalization.SourceRelativeNormPacket.NB_contains
#check @N11Formalization.SourceRelativeNormPacket.all_rows
#print axioms N11Formalization.SourceRelativeNormPacket.NB_contains
#print axioms N11Formalization.SourceRelativeNormPacket.all_rows
