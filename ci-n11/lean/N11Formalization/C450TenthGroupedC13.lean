import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6252027129:ℚ)/10000000000),((3259028091:ℚ)/5000000000),((-2619028091:ℚ)/12400000000),((-12996081387:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6047660299:ℚ)/10000000000),((5014209551111472563996275006998504792864057879210857660103:ℚ)/211715856250000000000000000000000000000000000000000000000000),((1749011872637283840050423:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((101403463:ℚ)/156250000),((3377946333:ℚ)/5000000000),((-2737946333:ℚ)/12875000000),((-71403463:ℚ)/556250000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5473168519:ℚ)/10000000000),((650751838724514608654275664430079400637499949795091:ℚ)/27699206161499023437500000000000000000000000000000000),((1673111184952853579103687:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6727595141:ℚ)/10000000000),((1718700517:ℚ)/2500000000),((-1398700517:ℚ)/6675000000),((-14422785423:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2419256629:ℚ)/5000000000),((556091884165737171040979687788964862783575429082080278751:ℚ)/24081853181250000000000000000000000000000000000000000000000),((398614761715425883836887:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6846474713:ℚ)/10000000000),((3496852991:ℚ)/5000000000),((-2856852991:ℚ)/13587500000),((-14779424139:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4490683761:ℚ)/10000000000),((472369408574396326511381973608840830429119407011577747201:ℚ)/20516200200781250000000000000000000000000000000000000000000),((1556641377325985985799823:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3482674913:ℚ)/5000000000),((7053155969:ℚ)/10000000000),((-824736567:ℚ)/3950000000),((-7568024739:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((82314239:ℚ)/200000000),((122329365727883784019654729816729367182988676930123527159:ℚ)/5354338982476806640625000000000000000000000000000000000000),((6069454460547555882926863:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7024785781:ℚ)/10000000000),((444537793:ℚ)/625000000),((-364537793:ℚ)/1742968750),((-5104785781:ℚ)/37500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3915624167:ℚ)/10000000000),((196629226784268524563235788652990614555197259398554781203:ℚ)/8616971969604492187500000000000000000000000000000000000000),((23413871048094004859617:ℚ)/902500000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3542110353:ℚ)/5000000000),((7172052169:ℚ)/10000000000),((-5892052169:ℚ)/28125000000),((-7746331059:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1852667331:ℚ)/5000000000),((585018191821502841586061671894665606030195085052344649:ℚ)/25667646479736328125000000000000000000000000000000000000),((5918499573393515373561663:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((3571827313:ℚ)/5000000000),((1446299689:ℚ)/2000000000),((-1190299689:ℚ)/5672500000),((-7835481939:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3482991957:ℚ)/10000000000),((60422225389537683916638012314711840637573741826112924461261:ℚ)/2654010273200000000000000000000000000000000000000000000000000),((233724007269826638946943:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((1440617513:ℚ)/2000000000),((911367943:ℚ)/1250000000),((-751367943:ℚ)/3575000000),((-1056617513:ℚ)/7690000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3246115841:ℚ)/10000000000),((98471132762674688397721568933477283244964875516037:ℚ)/4329957947021484375000000000000000000000000000000000),((90121137191929195246567:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7262519549:ℚ)/10000000000),((918798437:ℚ)/1250000000),((-758798437:ℚ)/3604687500),((-16027558647:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2991250887:ℚ)/10000000000),((515279646881533187038553588297643986215126586196631047913519:ℚ)/22681238014556250000000000000000000000000000000000000000000000),((88944645835696210571327:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((7321950601:ℚ)/10000000000),((7409830329:ℚ)/10000000000),((-6129830329:ℚ)/29075000000),((-16205851803:ℚ)/117250000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2713327557:ℚ)/10000000000),((37988032828497152604130002534864320147178035357037927460997:ℚ)/1673787214941406250000000000000000000000000000000000000000000),((5617213809832525927115103:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7381380743:ℚ)/10000000000),((746927207:ℚ)/1000000000),((-618927207:ℚ)/2931250000),((-5461380743:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2404357311:ℚ)/10000000000),((145184165330880170227927445472609431692759420882632515639:ℚ)/6402999887500000000000000000000000000000000000000000000000),((55420221791714690158367:ℚ)/2310400000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7440809997:ℚ)/10000000000),((7588152379:ℚ)/10000000000),((-6308152379:ℚ)/29550000000),((-16562429991:ℚ)/120100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((410069137:ℚ)/2000000000),((36406981007445546223594524973445147338557149346177888184571:ℚ)/1599692575298437500000000000000000000000000000000000000000000),((288070348991116520647437:ℚ)/12160000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((944958241:ℚ)/1250000000),((7707028623:ℚ)/10000000000),((-6427028623:ℚ)/30025000000),((-2114874723:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((515355007:ℚ)/5000000000),((604795449975556249636329355907298226984198994097579191097:ℚ)/26621502050781250000000000000000000000000000000000000000000),((174721908381479:ℚ)/7600000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3839259277:ℚ)/5000000000),((8182496527:ℚ)/10000000000),((-6902496527:ℚ)/30500000000),((-2879259277:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((29794504757628124208296328041027333050951958822469741401:ℚ)/1280707200000000000000000000000000000000000000000000000000),((364003:ℚ)/16000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((4076949467:ℚ)/5000000000),((2520980789:ℚ)/2500000000),((-81517807:ℚ)/300000000),((-9350848401:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((240606874767751706264380670952512264290361941265219033833:ℚ)/9600000000000000000000000000000000000000000000000000000000),((364003:ℚ)/16000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10055058777:ℚ)/10000000000),((6942798563:ℚ)/5000000000),((-6302798563:ℚ)/20000000000),((-8135058777:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((17395308260935193755517313661038693689044997765265594003:ℚ)/622950400000000000000000000000000000000000000000000000000),((364003:ℚ)/16000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC13
#check @N11Formalization.C450TenthGroupedC13.bound
#print axioms N11Formalization.C450TenthGroupedC13.valid0
#print axioms N11Formalization.C450TenthGroupedC13.valid1
#print axioms N11Formalization.C450TenthGroupedC13.valid2
#print axioms N11Formalization.C450TenthGroupedC13.valid3
#print axioms N11Formalization.C450TenthGroupedC13.valid4
#print axioms N11Formalization.C450TenthGroupedC13.valid5
#print axioms N11Formalization.C450TenthGroupedC13.valid6
#print axioms N11Formalization.C450TenthGroupedC13.valid7
#print axioms N11Formalization.C450TenthGroupedC13.valid8
#print axioms N11Formalization.C450TenthGroupedC13.valid9
#print axioms N11Formalization.C450TenthGroupedC13.valid10
#print axioms N11Formalization.C450TenthGroupedC13.valid11
#print axioms N11Formalization.C450TenthGroupedC13.valid12
#print axioms N11Formalization.C450TenthGroupedC13.valid13
#print axioms N11Formalization.C450TenthGroupedC13.valid14
#print axioms N11Formalization.C450TenthGroupedC13.valid15
#print axioms N11Formalization.C450TenthGroupedC13.valid16
#print axioms N11Formalization.C450TenthGroupedC13.bound
#print axioms N11Formalization.C450TenthGroupedC13.endpoint_checks
