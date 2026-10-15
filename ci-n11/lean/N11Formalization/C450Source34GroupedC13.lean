import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6310408231:ℚ)/10000000000),((1303628403:ℚ)/2000000000),((-279628403:ℚ)/4960000000),((2188775307:ℚ)/99200000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1182240579:ℚ)/2000000000),((16152355735717575782289929335497621:ℚ)/762649600000000000000000000000000000),((-2587628402768977146465381:ℚ)/40960000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6431791211:ℚ)/10000000000),((3319675351:ℚ)/5000000000),((-253225117:ℚ)/4212500000),((608208789:ℚ)/33700000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((5618174327:ℚ)/10000000000),((696339940750133253485121771992805496141873742203269:ℚ)/29199793243408203125000000000000000000000000000000000),((-1035859792196003600520980501:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6553073921:ℚ)/10000000000),((3380233821:ℚ)/5000000000),((-820233821:ℚ)/12875000000),((1460778237:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5311076873:ℚ)/10000000000),((1374852084885449520883312179557865998345630284047797:ℚ)/52105283737182617187500000000000000000000000000000000),((-1138200287997859584034101821:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((6674262037:ℚ)/10000000000),((213156041:ℚ)/312500000),((-53156041:ℚ)/819531250),((1097213889:ℚ)/104900000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((498726553:ℚ)/1000000000),((46496807910255103473945312988564042224168040450111:ℚ)/1720071806013584136962890625000000000000000000000000),((-1241158447357282219169933589:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((168370557:ℚ)/250000000),((6881497923:ℚ)/10000000000),((-1761497923:ℚ)/26462500000),((22888329:ℚ)/2646250000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((150563483:ℚ)/312500000),((2451549837380620324828429681668535060321695803544718193:ℚ)/86862813839721679687500000000000000000000000000000000000),((-808043786585514161048869:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((1698840203:ℚ)/2500000000),((6941982053:ℚ)/10000000000),((-607327351:ℚ)/8900000000),((61159797:ℚ)/8900000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4643196961:ℚ)/10000000000),((388452628324559904034134126536411984557736585570108069:ℚ)/13218168750000000000000000000000000000000000000000000000),((-84046071609652557556764629:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((856984779:ℚ)/1250000000),((350122313:ℚ)/500000000),((-94122313:ℚ)/1346875000),((69045663:ℚ)/13468750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((446209791:ℚ)/1000000000),((466165788422344838134898693641439202815872741038929:ℚ)/15270803642272949218750000000000000000000000000000000),((-21824375587565033125614421:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((6916375113:ℚ)/10000000000),((176572277:ℚ)/250000000),((-48572277:ℚ)/679375000),((370874661:ℚ)/108700000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((267120753:ℚ)/625000000),((3875567948678803799276969512726467180185499228741:ℚ)/122486639308929443359375000000000000000000000000000),((-1448939047165716655000598989:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3488401781:ℚ)/5000000000),((7123317031:ℚ)/10000000000),((-2003317031:ℚ)/27412500000),((31598219:ℚ)/18275000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((815575161:ℚ)/2000000000),((97998386179743137838722437514850632028853370738069021:ℚ)/2994039294433593750000000000000000000000000000000000000),((-375308120797701206459613141:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7037194731:ℚ)/10000000000),((7244114303:ℚ)/10000000000),((-2124114303:ℚ)/27650000000),((8415807:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((30980933:ℚ)/80000000),((95567263902300744686220110119541558531627588222770551:ℚ)/2696307031250000000000000000000000000000000000000000000),((-1553666848964462169996555541:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7157924293:ℚ)/10000000000),((7364841863:ℚ)/10000000000),((-748280621:ℚ)/9375000000),((-353772879:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3427555601:ℚ)/10000000000),((192993095004277549877704228154391401319235549191195197:ℚ)/5149841308593750000000000000000000000000000000000000000),((-1659008792561184635364356469:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7278586503:ℚ)/10000000000),((7606101723:ℚ)/10000000000),((-2486101723:ℚ)/28600000000),((-1211099:ℚ)/200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((583731099:ℚ)/2000000000),((4667038374554076596547555072766055541958343194848831593:ℚ)/109657762500000000000000000000000000000000000000000000000),((-1764983334882469513683616429:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3759861131:ℚ)/5000000000),((62776977:ℚ)/80000000),((-21816977:ℚ)/236400000),((-719583393:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((22730491:ℚ)/156250000),((57985668720947024404564079489645657372144127071:ℚ)/1257411600000000000000000000000000000000000000000),((-494709385721593706237776341:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3880313317:ℚ)/5000000000),((4164265559:ℚ)/5000000000),((-1604265559:ℚ)/15250000000),((-40034813:ℚ)/2400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((305623256724662199140184639460832412642359063545672727:ℚ)/5541528320312500000000000000000000000000000000000000000),((-142011447:ℚ)/1024000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8241824789:ℚ)/10000000000),((1024798871:ℚ)/1000000000),((-170932957:ℚ)/1080000000),((-3605474367:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((135897239934834112626762502080219916442782300977623:ℚ)/1476225000000000000000000000000000000000000000000000),((-142011447:ℚ)/1024000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5080322569:ℚ)/5000000000),((7035343879:ℚ)/5000000000),((-4475343879:ℚ)/20000000000),((-1560322569:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((294051481017249690280301687812129149:ℚ)/2000000000000000000000000000000000000),((-142011447:ℚ)/1024000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC13
#check @N11Formalization.C450Source34GroupedC13.bound
#print axioms N11Formalization.C450Source34GroupedC13.valid0
#print axioms N11Formalization.C450Source34GroupedC13.valid1
#print axioms N11Formalization.C450Source34GroupedC13.valid2
#print axioms N11Formalization.C450Source34GroupedC13.valid3
#print axioms N11Formalization.C450Source34GroupedC13.valid4
#print axioms N11Formalization.C450Source34GroupedC13.valid5
#print axioms N11Formalization.C450Source34GroupedC13.valid6
#print axioms N11Formalization.C450Source34GroupedC13.valid7
#print axioms N11Formalization.C450Source34GroupedC13.valid8
#print axioms N11Formalization.C450Source34GroupedC13.valid9
#print axioms N11Formalization.C450Source34GroupedC13.valid10
#print axioms N11Formalization.C450Source34GroupedC13.valid11
#print axioms N11Formalization.C450Source34GroupedC13.valid12
#print axioms N11Formalization.C450Source34GroupedC13.valid13
#print axioms N11Formalization.C450Source34GroupedC13.valid14
#print axioms N11Formalization.C450Source34GroupedC13.valid15
#print axioms N11Formalization.C450Source34GroupedC13.bound
#print axioms N11Formalization.C450Source34GroupedC13.endpoint_checks
