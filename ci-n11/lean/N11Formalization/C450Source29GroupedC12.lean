import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((159529457:ℚ)/250000000),((669897679:ℚ)/1000000000),((-324297679:ℚ)/1984000000),((-47529457:ℚ)/643750000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1435492547:ℚ)/2500000000),((2941879321152008472800060079860389633:ℚ)/20712830992384000000000000000000000000),((-7555907697535854049499:ℚ)/144400000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((264880007:ℚ)/400000000),((6819351907:ℚ)/10000000000),((-3363351907:ℚ)/20600000000),((-85680007:ℚ)/1049000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((160287181:ℚ)/312500000),((32999067117993084895356885132509664839206791645704468331303:ℚ)/234851149126367187500000000000000000000000000000000000000000),((-68279774588460469459:ℚ)/1024000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((6742319061:ℚ)/10000000000),((1734917013:ℚ)/2500000000),((-870917013:ℚ)/5245000000),((-2262319061:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((959340073:ℚ)/2000000000),((9081571678179206365207292553653877292560473059378496935313:ℚ)/64289347458250781250000000000000000000000000000000000000000),((-51240058413357922776284713:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((1372516211:ℚ)/2000000000),((699980501:ℚ)/1000000000),((-354380501:ℚ)/2136000000),((-476516211:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2220808613:ℚ)/5000000000),((4771892259641695844599050265225298340841321832477450853107:ℚ)/33943729469212800000000000000000000000000000000000000000000),((-750613075072429553816371:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6922691681:ℚ)/10000000000),((7059928397:ℚ)/10000000000),((-3603928397:ℚ)/21550000000),((-2442691681:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2126918187:ℚ)/5000000000),((10417740482999536234011832187257979540571032742886991385259057:ℚ)/73906209541311718750000000000000000000000000000000000000000000),((-19612081014333774860359611:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3491394607:ℚ)/5000000000),((3560019287:ℚ)/5000000000),((-1832019287:ℚ)/10870000000),((-1251394607:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((811594091:ℚ)/2000000000),((113669707130960429806462061333962801149257953349286291271529:ℚ)/804275196736620703125000000000000000000000000000000000000000),((-5115393259539716826379099:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7042874001:ℚ)/10000000000),((7180135891:ℚ)/10000000000),((-3724135891:ℚ)/21930000000),((-2562874001:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3852781171:ℚ)/10000000000),((66428096393490833259175270817830282410113271029023940652557:ℚ)/468789331246818750000000000000000000000000000000000000000000),((-177123041291357040919273:ℚ)/1920000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((7102946379:ℚ)/10000000000),((3650146637:ℚ)/5000000000),((-1922146637:ℚ)/11060000000),((-2622946379:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((909171273:ℚ)/2500000000),((14033368351068243076775194752067506368456540732841992999:ℚ)/97843589550000000000000000000000000000000000000000000000),((-66506348255350402034570473:ℚ)/693120000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((3611527597:ℚ)/5000000000),((7420403103:ℚ)/10000000000),((-1321467701:ℚ)/7500000000),((-124684327:ℚ)/1300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3162704701:ℚ)/10000000000),((64222646383216975234084719068986721270239996401732014449:ℚ)/445605468750000000000000000000000000000000000000000000000),((-5971744774461314574275059:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3671559061:ℚ)/5000000000),((766048947:ℚ)/1000000000),((-420448947:ℚ)/2288000000),((-1431559061:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1303694591:ℚ)/5000000000),((321228982382843590716339720849173170326001405350642083869:ℚ)/2178922549689600000000000000000000000000000000000000000000),((-6404045893611220794041571:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((1895778839:ℚ)/2500000000),((7900412243:ℚ)/10000000000),((-4444412243:ℚ)/23640000000),((-775778839:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((133341271:ℚ)/2000000000),((137045316963073504258799029517556747521401601711442084628709:ℚ)/921729227029200000000000000000000000000000000000000000000000),((-1819230988473545200697771:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7822954717:ℚ)/10000000000),((4189912827:ℚ)/5000000000),((-2461912827:ℚ)/12200000000),((-371439413:ℚ)/3600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((35570224909954631101994761315684458984766311952630284527:ℚ)/229818262500000000000000000000000000000000000000000000000),((-2032901:ℚ)/16000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8302216379:ℚ)/10000000000),((514662197:ℚ)/500000000),((-341862197:ℚ)/1296000000),((-3822216379:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((469012206379168503872095192834095717414713531894219:ℚ)/2550916800000000000000000000000000000000000000000000),((-2032901:ℚ)/16000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10215174707:ℚ)/10000000000),((14108928013:ℚ)/10000000000),((-10652928013:ℚ)/32000000000),((-5735174707:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((8748836295966001493056848027537495386611:ℚ)/39002112000000000000000000000000000000000),((-2032901:ℚ)/16000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC12
#check @N11Formalization.C450Source29GroupedC12.bound
#print axioms N11Formalization.C450Source29GroupedC12.valid0
#print axioms N11Formalization.C450Source29GroupedC12.valid1
#print axioms N11Formalization.C450Source29GroupedC12.valid2
#print axioms N11Formalization.C450Source29GroupedC12.valid3
#print axioms N11Formalization.C450Source29GroupedC12.valid4
#print axioms N11Formalization.C450Source29GroupedC12.valid5
#print axioms N11Formalization.C450Source29GroupedC12.valid6
#print axioms N11Formalization.C450Source29GroupedC12.valid7
#print axioms N11Formalization.C450Source29GroupedC12.valid8
#print axioms N11Formalization.C450Source29GroupedC12.valid9
#print axioms N11Formalization.C450Source29GroupedC12.valid10
#print axioms N11Formalization.C450Source29GroupedC12.valid11
#print axioms N11Formalization.C450Source29GroupedC12.valid12
#print axioms N11Formalization.C450Source29GroupedC12.valid13
#print axioms N11Formalization.C450Source29GroupedC12.bound
#print axioms N11Formalization.C450Source29GroupedC12.endpoint_checks
