import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5740575569:ℚ)/10000000000),((3142906297:ℚ)/5000000000),((7180575569:ℚ)/13350000000),((34366156673:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((111660193:ℚ)/156250000),((-183235624040681594460393519697453:ℚ)/297408796875000000000000000000000000),((-2526840236975439113514419:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((621785787:ℚ)/1000000000),((1304863919:ℚ)/2000000000),((765785787:ℚ)/1382500000),((14175775271:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6126288699:ℚ)/10000000000),((-64248100402011223576781296550577150320573310839613:ℚ)/8257440283203125000000000000000000000000000000000000),((-204589914402486242047263:ℚ)/577600000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((10330209:ℚ)/16000000),((6762759299:ℚ)/10000000000),((12634209:ℚ)/22880000),((73024833691:ℚ)/110600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5557144167:ℚ)/10000000000),((-311975769579302059018026927567880220306142871:ℚ)/37429849600000000000000000000000000000000000000),((-5135336162197471546189733:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((267793401:ℚ)/400000000),((6881955993:ℚ)/10000000000),((325393401:ℚ)/581500000),((74097603937:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4930373289:ℚ)/10000000000),((-1734028757445116935989176324933646433215790829511:ℚ)/153616967480468750000000000000000000000000000000000),((-15495723738724304510563351:ℚ)/43320000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3407019351:ℚ)/5000000000),((7001138247:ℚ)/10000000000),((1375673117:ℚ)/2462500000),((75170244223:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4588012427:ℚ)/10000000000),((-399318159954567811912964175028539216921819239707601:ℚ)/34997740173339843750000000000000000000000000000000000),((-15525297060823473541216141:ℚ)/43320000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6933227713:ℚ)/10000000000),((111254793:ℚ)/156250000),((8373227713:ℚ)/15012500000),((1191293137:ℚ)/1846875000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2110058467:ℚ)/5000000000),((-365068611891816403978090078348094549848686408899131141:ℚ)/31719792498779296875000000000000000000000000000000000000),((-7777175477378791593340823:ℚ)/21660000000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((3526201379:ℚ)/5000000000),((1447892431:ℚ)/2000000000),((4246201379:ℚ)/7625000000),((15463031879:ℚ)/24020000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((119352537:ℚ)/312500000),((-16052593759930694664492952793642478302357405527353309:ℚ)/1385382080078125000000000000000000000000000000000000000),((-207771810386047260686863:ℚ)/577600000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((448222781:ℚ)/625000000),((3679302531:ℚ)/5000000000),((538222781:ℚ)/967968750),((39193722779:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((674749473:ℚ)/2000000000),((-458383705188415696065429439691820253991964800537:ℚ)/39364209584891796112060546875000000000000000000000),((-3902725467768805903176889:ℚ)/10830000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3645356771:ℚ)/5000000000),((1869434011:ℚ)/2500000000),((4365356771:ℚ)/7862500000),((19864906099:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2862678593:ℚ)/10000000000),((-17329197703446019293917672784561719002679313155669:ℚ)/1483310395479202270507812500000000000000000000000000),((-1303199962148679349725347:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((296394019:ℚ)/400000000),((7715964341:ℚ)/10000000000),((353994019:ℚ)/648000000),((81603679069:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1120819049:ℚ)/5000000000),((-298621985554933689391065232361238624606968282903:ℚ)/31492800000000000000000000000000000000000000000000),((-14070578988283309:ℚ)/38912000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3824045073:ℚ)/5000000000),((962054107:ℚ)/1000000000),((4544045073:ℚ)/10000000000),((9874486963:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1201020273298798914989137794639427:ℚ)/93750000000000000000000000000000000),((-46565743:ℚ)/128000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((2388184571:ℚ)/2500000000),((13425905849:ℚ)/10000000000),((2748184571:ℚ)/6900000000),((132993152641:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((200513475243962810726291:ℚ)/5951250000000000000000000),((-46565743:ℚ)/128000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC25
#check @N11Formalization.C450Source20GroupedC25.bound
#print axioms N11Formalization.C450Source20GroupedC25.valid0
#print axioms N11Formalization.C450Source20GroupedC25.valid1
#print axioms N11Formalization.C450Source20GroupedC25.valid2
#print axioms N11Formalization.C450Source20GroupedC25.valid3
#print axioms N11Formalization.C450Source20GroupedC25.valid4
#print axioms N11Formalization.C450Source20GroupedC25.valid5
#print axioms N11Formalization.C450Source20GroupedC25.valid6
#print axioms N11Formalization.C450Source20GroupedC25.valid7
#print axioms N11Formalization.C450Source20GroupedC25.valid8
#print axioms N11Formalization.C450Source20GroupedC25.valid9
#print axioms N11Formalization.C450Source20GroupedC25.valid10
#print axioms N11Formalization.C450Source20GroupedC25.valid11
#print axioms N11Formalization.C450Source20GroupedC25.bound
#print axioms N11Formalization.C450Source20GroupedC25.endpoint_checks
