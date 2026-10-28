import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((1216495417:ℚ)/2000000000),((6621935143:ℚ)/10000000000),((56:ℚ)/445),((20701935143:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3214788459:ℚ)/5000000000),((64212577899182167998451023556805049511627:ℚ)/483275798528000000000000000000000000000000),((-500009836254318586713538239:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((262478673:ℚ)/400000000),((3430636103:ℚ)/5000000000),((48:ℚ)/395),((10470636103:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5287928677:ℚ)/10000000000),((189784452756580809882932464744516821143158534548020684531881:ℚ)/1484902641037500000000000000000000000000000000000000000000000),((-134772154780626323205167999:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3400738659:ℚ)/5000000000),((3490446841:ℚ)/5000000000),((224:ℚ)/1875),((10530446841:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((578149099:ℚ)/1250000000),((14255027186960320865946813105402182611071410476014680843:ℚ)/113244895312500000000000000000000000000000000000000000000),((-139648150272405105112209791:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6921181013:ℚ)/10000000000),((7100485901:ℚ)/10000000000),((84:ℚ)/715),((7060161967:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2129325273:ℚ)/5000000000),((5418626493405072003870669990813772062690060445765379235311:ℚ)/43203735351562500000000000000000000000000000000000000000000),((-568022110840050426187621511:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7040852659:ℚ)/10000000000),((3610025159:ℚ)/5000000000),((672:ℚ)/5815),((10650025159:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((192992601:ℚ)/500000000),((1123814691974300197428306416195737683108341652259811926669523:ℚ)/8989072131325000000000000000000000000000000000000000000000000),((-144359611875343308712465791:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1790123463:ℚ)/2500000000),((7339588291:ℚ)/10000000000),((112:ℚ)/985),((21419588291:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3417481387:ℚ)/10000000000),((2973083782269973719273599988615587007144925785453321319497373:ℚ)/23846883563798046875000000000000000000000000000000000000000000),((-586841745144410263484225191:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7280106081:ℚ)/10000000000),((7578589911:ℚ)/10000000000),((168:ℚ)/1525),((21658589911:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((582339727:ℚ)/2000000000),((1200639669528862958970364720784647639007637616596019286361673:ℚ)/9601346114887500000000000000000000000000000000000000000000000),((-1786693153440843030029478493:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((1503849827:ℚ)/2000000000),((8056326709:ℚ)/10000000000),((14:ℚ)/135),((22136326709:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((729519803:ℚ)/5000000000),((2408548983448517129518769024429065020255017989771373702209:ℚ)/19151521875000000000000000000000000000000000000000000000000),((-32396424881655769:ℚ)/97280000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((3998621737:ℚ)/5000000000),((2491164387:ℚ)/2500000000),((21:ℚ)/250),((6011164387:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((433790890650484248841189337223390556689442142000256781:ℚ)/3321506250000000000000000000000000000000000000000000000),((-43096627:ℚ)/128000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((4953178291:ℚ)/5000000000),((13774411061:ℚ)/10000000000),((7:ℚ)/115),((27854411061:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20316058772666535400316490135456149713609:ℚ)/135424000000000000000000000000000000000000),((-43096627:ℚ)/128000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC17
#check @N11Formalization.C450Source23GroupedC17.bound
#print axioms N11Formalization.C450Source23GroupedC17.valid0
#print axioms N11Formalization.C450Source23GroupedC17.valid1
#print axioms N11Formalization.C450Source23GroupedC17.valid2
#print axioms N11Formalization.C450Source23GroupedC17.valid3
#print axioms N11Formalization.C450Source23GroupedC17.valid4
#print axioms N11Formalization.C450Source23GroupedC17.valid5
#print axioms N11Formalization.C450Source23GroupedC17.valid6
#print axioms N11Formalization.C450Source23GroupedC17.valid7
#print axioms N11Formalization.C450Source23GroupedC17.valid8
#print axioms N11Formalization.C450Source23GroupedC17.valid9
#print axioms N11Formalization.C450Source23GroupedC17.bound
#print axioms N11Formalization.C450Source23GroupedC17.endpoint_checks
