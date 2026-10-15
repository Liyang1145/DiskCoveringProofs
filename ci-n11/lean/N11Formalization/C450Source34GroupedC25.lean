import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((5360688201:ℚ)/10000000000),((712667631:ℚ)/1250000000),((7920688201:ℚ)/12875000000),((9054008679:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3939371583:ℚ)/5000000000),((-432537013544266317199030431215436109328197408189548335689:ℚ)/1227389200000000000000000000000000000000000000000000000000),((-9523653267907876783385911:ℚ)/21660000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((1400453349:ℚ)/2500000000),((5942311527:ℚ)/10000000000),((2040453349:ℚ)/3337500000),((74600803743:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3710279653:ℚ)/5000000000),((-159933052097727284882396115076843631433668271642979503280813:ℚ)/455872045312500000000000000000000000000000000000000000000000),((-18842154652571187461621597:ℚ)/43320000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((5842675109:ℚ)/10000000000),((1212540773:ℚ)/2000000000),((8402675109:ℚ)/13587500000),((5045622319:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3469379759:ℚ)/5000000000),((-879082515473439591938136938283634654924651372217234272641:ℚ)/2452164169600000000000000000000000000000000000000000000000),((-250843880818620240423249:ℚ)/577600000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((2981508017:ℚ)/5000000000),((77287983:ℚ)/125000000),((4261508017:ℚ)/6912500000),((959591847:ℚ)/1358750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6687337307:ℚ)/10000000000),((-6918725072888620764862572346135548739825008052373921:ℚ)/19352889010810852050781250000000000000000000000000000),((-187013988153106917589703:ℚ)/433200000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6083301233:ℚ)/10000000000),((3151659423:ℚ)/5000000000),((2881100411:ℚ)/4687500000),((38924934807:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3213884023:ℚ)/5000000000),((-4416387612619270447536227263445704150018342168327512973:ℚ)/12386160424804687500000000000000000000000000000000000000),((-9292901335475789499375769:ℚ)/21660000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((7754417:ℚ)/12500000),((642354727:ℚ)/1000000000),((10954417:ℚ)/17875000),((2631064181:ℚ)/3750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3079495089:ℚ)/5000000000),((-16762599312135210815114330746813017443657437319047391051:ℚ)/47131347656250000000000000000000000000000000000000000000),((-61555016659592861208999:ℚ)/144400000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3161857917:ℚ)/5000000000),((408982907:ℚ)/625000000),((4441857917:ℚ)/7268750000),((5000846163:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5879709129:ℚ)/10000000000),((-85697560159100631168455115241597600151019338558446874483:ℚ)/241537836718750000000000000000000000000000000000000000000),((-1528625667068743087500641:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6443850449:ℚ)/10000000000),((6663859:ℚ)/10000000),((3001283483:ℚ)/4925000000),((81094731:ℚ)/116300000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((698539763:ℚ)/1250000000),((-171400068738001676188081754030759700124103152451999:ℚ)/484200681498437500000000000000000000000000000000000),((-194312679998527860477:ℚ)/462080000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3281969897:ℚ)/5000000000),((6783947003:ℚ)/10000000000),((4561969897:ℚ)/7506250000),((27391841009:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5282780609:ℚ)/10000000000),((-617368970282151210513603237743510271946459096992567047087:ℚ)/1747860337500000000000000000000000000000000000000000000000),((-6028808052599313096865379:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((1336797213:ℚ)/2000000000),((3451996323:ℚ)/5000000000),((1848797213:ℚ)/3050000000),((41627966907:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4960449387:ℚ)/10000000000),((-29099740457386244901491208612774422554732004974683008545111:ℚ)/82556046610156250000000000000000000000000000000000000000000),((-472430027006910803564851:ℚ)/1140000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3401995659:ℚ)/5000000000),((714396469:ℚ)/1000000000),((4681995659:ℚ)/7862500000),((8541568221:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((230888693:ℚ)/500000000),((-614942416082783252108279629137859711331922301275139545817:ℚ)/1784638112500000000000000000000000000000000000000000000000),((-29323508389669439101783:ℚ)/72200000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((3521943177:ℚ)/5000000000),((7383789631:ℚ)/10000000000),((4801943177:ℚ)/8100000000),((87574106679:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1924617613:ℚ)/5000000000),((-9362116808888482706937591022622544038034832043104921674859:ℚ)/27239882850000000000000000000000000000000000000000000000000),((-5766719166030830092680891:ℚ)/14440000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((1456727787:ℚ)/2000000000),((929837009:ℚ)/1000000000),((1968727787:ℚ)/4000000000),((3493511027:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((361932741:ℚ)/1250000000),((-386172191659805168763316621390145059423995997244744953:ℚ)/1511654400000000000000000000000000000000000000000000000),((-76520759049641213:ℚ)/194560000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((2299441727:ℚ)/2500000000),((3278851553:ℚ)/2500000000),((979813909:ℚ)/2300000000),((34789663977:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-71328319357138288132246918051797549389:ℚ)/368000000000000000000000000000000000000),((-10191627:ℚ)/25600000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC25
#check @N11Formalization.C450Source34GroupedC25.bound
#print axioms N11Formalization.C450Source34GroupedC25.valid0
#print axioms N11Formalization.C450Source34GroupedC25.valid1
#print axioms N11Formalization.C450Source34GroupedC25.valid2
#print axioms N11Formalization.C450Source34GroupedC25.valid3
#print axioms N11Formalization.C450Source34GroupedC25.valid4
#print axioms N11Formalization.C450Source34GroupedC25.valid5
#print axioms N11Formalization.C450Source34GroupedC25.valid6
#print axioms N11Formalization.C450Source34GroupedC25.valid7
#print axioms N11Formalization.C450Source34GroupedC25.valid8
#print axioms N11Formalization.C450Source34GroupedC25.valid9
#print axioms N11Formalization.C450Source34GroupedC25.valid10
#print axioms N11Formalization.C450Source34GroupedC25.valid11
#print axioms N11Formalization.C450Source34GroupedC25.valid12
#print axioms N11Formalization.C450Source34GroupedC25.valid13
#print axioms N11Formalization.C450Source34GroupedC25.bound
#print axioms N11Formalization.C450Source34GroupedC25.endpoint_checks
