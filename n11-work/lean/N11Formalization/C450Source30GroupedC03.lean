import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7075525117:ℚ)/10000000000),((7308745037:ℚ)/10000000000),((-42201215259:ℚ)/49600000000),((-73421826521:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((467100493:ℚ)/1250000000),((756075923660137210093979159862672081431:ℚ)/1913637650000000000000000000000000000000),((310016266181048482522750629:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7194926533:ℚ)/10000000000),((1842088431:ℚ)/2500000000),((-10654619017:ℚ)/12637500000),((-74974044929:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((51244023:ℚ)/156250000),((163321231697185066173146284378002507850202805836035137683681:ℚ)/419710870367724609375000000000000000000000000000000000000000),((58234226588311317261538103:ℚ)/69312000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((906827259:ℚ)/1250000000),((1856989519:ℚ)/2500000000),((-827609741:ℚ)/981250000),((-9468754367:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3026332161:ℚ)/10000000000),((32574032390809920792825486110873902538274457724914019921:ℚ)/83768622558593750000000000000000000000000000000000000000),((19446822440995579121506301:ℚ)/23104000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3657151863:ℚ)/5000000000),((7487558211:ℚ)/10000000000),((-43452907477:ℚ)/51500000000),((-38262974219:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2750619077:ℚ)/10000000000),((1693853870127836502649566619188423832645643291869900327:ℚ)/4358888418960571289062500000000000000000000000000000000),((935148356925642638767165583:ℚ)/1108992000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3686991829:ℚ)/5000000000),((3773577123:ℚ)/5000000000),((-3133577123:ℚ)/3712500000),((-38650893777:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((122244783:ℚ)/500000000),((104014763530797120531910758632585648613328040361231908662499:ℚ)/267838463088281250000000000000000000000000000000000000000000),((234212566946291607898060367:ℚ)/277248000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((297346321:ℚ)/400000000),((1533266891:ℚ)/2000000000),((-8940868237:ℚ)/10490000000),((-3123102173:ℚ)/4272000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1048031779:ℚ)/5000000000),((22330781600333911766277646637537115104889064633745397727:ℚ)/56794558540800000000000000000000000000000000000000000000),((4332227:ℚ)/5120000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((944123833:ℚ)/1250000000),((1017863961:ℚ)/1250000000),((-6005047727:ℚ)/6675000000),((-9953609829:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((222563719:ℚ)/2000000000),((2055611737544935581341009195700870556759256237730235270997:ℚ)/4879770431250000000000000000000000000000000000000000000000),((4332227:ℚ)/5120000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((8030126401:ℚ)/10000000000),((9095508959:ℚ)/10000000000),((-54708562713:ℚ)/57200000000),((-85831643213:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8121239454500014357956988252682500016977423716450883247867:ℚ)/18013881600000000000000000000000000000000000000000000000000),((4332227:ℚ)/5120000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((4491821149:ℚ)/5000000000),((27498047:ℚ)/25000000),(-1:ℚ),((-49113674937:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((95019096106944574562749681129775120053968358294365953083:ℚ)/200000000000000000000000000000000000000000000000000000000),((4332227:ℚ)/5120000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((1361082779:ℚ)/1250000000),((14803568637:ℚ)/10000000000),(-1:ℚ),((-15374076127:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((286196323909525825718370411377403431:ℚ)/584016000000000000000000000000000000),((4332227:ℚ)/5120000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source30 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC03
#check @N11Formalization.C450Source30GroupedC03.bound
#print axioms N11Formalization.C450Source30GroupedC03.valid0
#print axioms N11Formalization.C450Source30GroupedC03.valid1
#print axioms N11Formalization.C450Source30GroupedC03.valid2
#print axioms N11Formalization.C450Source30GroupedC03.valid3
#print axioms N11Formalization.C450Source30GroupedC03.valid4
#print axioms N11Formalization.C450Source30GroupedC03.valid5
#print axioms N11Formalization.C450Source30GroupedC03.valid6
#print axioms N11Formalization.C450Source30GroupedC03.valid7
#print axioms N11Formalization.C450Source30GroupedC03.valid8
#print axioms N11Formalization.C450Source30GroupedC03.valid9
#print axioms N11Formalization.C450Source30GroupedC03.bound
#print axioms N11Formalization.C450Source30GroupedC03.endpoint_checks
