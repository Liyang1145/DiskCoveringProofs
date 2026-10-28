import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((211053177:ℚ)/312500000),((872861959:ℚ)/1250000000),((-5215757631:ℚ)/12400000000),((-126053177:ℚ)/394921875),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2382072187:ℚ)/5000000000),((686725104040833980305346125692855027:ℚ)/2383280000000000000000000000000000000),((249501319880259516574869:ℚ)/902500000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6874483207:ℚ)/10000000000),((3521612277:ℚ)/5000000000),((-7044836831:ℚ)/16850000000),((-4154483207:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2202515437:ℚ)/5000000000),((532179300421836704768039865681364828795099424696798471:ℚ)/1868786767578125000000000000000000000000000000000000000),((249269446349222290700299089:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6934844897:ℚ)/10000000000),((7103535421:ℚ)/10000000000),((-42811818789:ℚ)/102050000000),((-4214844897:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4214918877:ℚ)/10000000000),((5822637815226527211956546480756474722398875788375388937:ℚ)/20437872406250000000000000000000000000000000000000000000),((246130832466246377231572449:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6995187939:ℚ)/10000000000),((7163828783:ℚ)/10000000000),((-43354459047:ℚ)/103000000000),((-388653449:ℚ)/1181250000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2008221027:ℚ)/5000000000),((7603858533725015130014101386032217677917159084060074927:ℚ)/26677905273437500000000000000000000000000000000000000000),((242973098059549837450296681:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7055512859:ℚ)/10000000000),((7224105131:ℚ)/10000000000),((-14632315393:ℚ)/34650000000),((-4335512859:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3808286459:ℚ)/10000000000),((11887939300961058515104852957030269158829845302073581:ℚ)/41688281250000000000000000000000000000000000000000000),((239796233963809105815624441:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7115820167:ℚ)/10000000000),((910545617:ℚ)/1250000000),((-5554910553:ℚ)/13112500000),((-4395820167:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3588761751:ℚ)/10000000000),((4020232853325039160200958448953603563162502526891675193:ℚ)/14090828234863281250000000000000000000000000000000000000),((236600231158573539738152529:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7176110351:ℚ)/10000000000),((7344608653:ℚ)/10000000000),((-44981477877:ℚ)/105850000000),((-1485370117:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3355630511:ℚ)/10000000000),((528982065291471419916590076680581871832251220351131849253:ℚ)/1853073361914062500000000000000000000000000000000000000000),((233385081116356084888616961:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((3618191941:ℚ)/5000000000),((92560459:ℚ)/125000000),((-189681377:ℚ)/445000000),((-2258191941:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((621164593:ℚ)/2000000000),((157308909689864014387248785392450605199611356352233:ℚ)/550757031250000000000000000000000000000000000000000),((57537693892640700526354041:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((3648320607:ℚ)/5000000000),((7465049559:ℚ)/10000000000),((-46065446031:ℚ)/107750000000),((-2288320607:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2834926313:ℚ)/10000000000),((2234503769458783982693373871126726136509773630904373006319:ℚ)/7818651464843750000000000000000000000000000000000000000000),((56724326636050500209878689:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((229902587:ℚ)/312500000),((3792715583:ℚ)/5000000000),((-23574440247:ℚ)/54350000000),((-144902587:ℚ)/432031250),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2536183271:ℚ)/10000000000),((18131492877178912250856366429371168631226680424070217927:ℚ)/62713159326171875000000000000000000000000000000000000000),((218383463260310678461509:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((747732031:ℚ)/1000000000),((782602861:ℚ)/1000000000),((-4931425749:ℚ)/11060000000),((-475732031:ℚ)/1430000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((449801069:ℚ)/2500000000),((356945907256838909998721825435868591861838823164568283:ℚ)/1207945550000000000000000000000000000000000000000000000),((2170218432613458323556321:ℚ)/9241600000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((38590119:ℚ)/50000000),((8786572479:ℚ)/10000000000),((-57959152311:ℚ)/114400000000),((-24990119:ℚ)/81000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1076316407171639667570783850596448347:ℚ)/3271840000000000000000000000000000000),((29115489:ℚ)/128000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8678927607:ℚ)/10000000000),((10701580149:ℚ)/10000000000),((-25064740447:ℚ)/43200000000),((-5958927607:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((18906449759378706996717952893820513:ℚ)/51840000000000000000000000000000000),((29115489:ℚ)/128000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((84755561:ℚ)/80000000),((226861141:ℚ)/156250000),((-1711750269:ℚ)/2500000000),((-62995561:ℚ)/220800000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((345231696697142868110461636570587:ℚ)/781250000000000000000000000000000),((29115489:ℚ)/128000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC08
#check @N11Formalization.C450Source35GroupedC08.bound
#print axioms N11Formalization.C450Source35GroupedC08.valid0
#print axioms N11Formalization.C450Source35GroupedC08.valid1
#print axioms N11Formalization.C450Source35GroupedC08.valid2
#print axioms N11Formalization.C450Source35GroupedC08.valid3
#print axioms N11Formalization.C450Source35GroupedC08.valid4
#print axioms N11Formalization.C450Source35GroupedC08.valid5
#print axioms N11Formalization.C450Source35GroupedC08.valid6
#print axioms N11Formalization.C450Source35GroupedC08.valid7
#print axioms N11Formalization.C450Source35GroupedC08.valid8
#print axioms N11Formalization.C450Source35GroupedC08.valid9
#print axioms N11Formalization.C450Source35GroupedC08.valid10
#print axioms N11Formalization.C450Source35GroupedC08.valid11
#print axioms N11Formalization.C450Source35GroupedC08.valid12
#print axioms N11Formalization.C450Source35GroupedC08.valid13
#print axioms N11Formalization.C450Source35GroupedC08.bound
#print axioms N11Formalization.C450Source35GroupedC08.endpoint_checks
