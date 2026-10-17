import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7128216351:ℚ)/10000000000),((7373813811:ℚ)/10000000000),((-74739579543:ℚ)/99200000000),((-15944649053:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((885507619:ℚ)/2500000000),((25984075274151271392683560208516480180723:ℚ)/55170173449500000000000000000000000000000),((688338985994192263945121661:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((7248138823:ℚ)/10000000000),((3746746049:ℚ)/5000000000),((-38147698637:ℚ)/50550000000),((-16304416469:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((763701873:ℚ)/2500000000),((355691814650833630871188275390563987601771055077547733164101:ℚ)/757445755999755859375000000000000000000000000000000000000000),((688367648233937124977722669:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7368017421:ℚ)/10000000000),((951642047:ℚ)/1250000000),((-9731346611:ℚ)/12875000000),((-16664052263:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((495423747:ℚ)/2000000000),((2187805322375831595767641045909494871297176796413997134527:ℚ)/4671549898239517211914062500000000000000000000000000000000),((688213316929262409760396101:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7487854571:ℚ)/10000000000),((7732748489:ℚ)/10000000000),((-79405730357:ℚ)/104900000000),((-17023563713:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((860011943:ℚ)/5000000000),((2265024291206796765495467902451188026605380265421333470675699:ℚ)/4848428703556250000000000000000000000000000000000000000000000),((1902336902862097453576141:ℚ)/2560000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7607652527:ℚ)/10000000000),((2052726939:ℚ)/2500000000),((-7135150069:ℚ)/8900000000),((-1580268871:ℚ)/2600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((432486497847165943378567202073650697058846646725717161631:ℚ)/870121850000000000000000000000000000000000000000000000000),((94923377:ℚ)/128000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((8086492089:ℚ)/10000000000),((286440803:ℚ)/312500000),((-278520949:ℚ)/325000000),((-18819476267:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1581907728676502603221546907747837313803908181505483492209:ℚ)/2993784300000000000000000000000000000000000000000000000000),((94923377:ℚ)/128000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4521403481:ℚ)/5000000000),((2768380427:ℚ)/2500000000),((-30708945551:ℚ)/32400000000),((-10844210443:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((440396992504755020812584733237076112807402208550044704569:ℚ)/759375000000000000000000000000000000000000000000000000000),((94923377:ℚ)/128000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((5475906041:ℚ)/5000000000),((7441103361:ℚ)/5000000000),(-1:ℚ),((-13707718123:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((632233:ℚ)/1000000),((94923377:ℚ)/128000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC04
#check @N11Formalization.C450Source35GroupedC04.bound
#print axioms N11Formalization.C450Source35GroupedC04.valid0
#print axioms N11Formalization.C450Source35GroupedC04.valid1
#print axioms N11Formalization.C450Source35GroupedC04.valid2
#print axioms N11Formalization.C450Source35GroupedC04.valid3
#print axioms N11Formalization.C450Source35GroupedC04.valid4
#print axioms N11Formalization.C450Source35GroupedC04.valid5
#print axioms N11Formalization.C450Source35GroupedC04.valid6
#print axioms N11Formalization.C450Source35GroupedC04.valid7
#print axioms N11Formalization.C450Source35GroupedC04.bound
#print axioms N11Formalization.C450Source35GroupedC04.endpoint_checks
