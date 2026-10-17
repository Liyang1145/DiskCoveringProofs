import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((6022722249:ℚ)/10000000000),((3273648299:ℚ)/5000000000),((27028166747:ℚ)/106800000000),((4473648299:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6559588789:ℚ)/10000000000),((16159984786498929433221500278561266769:ℚ)/424754119800000000000000000000000000000),((-560788369691196136462449:ℚ)/3040000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3249835521:ℚ)/5000000000),((6785579169:ℚ)/10000000000),((14229506563:ℚ)/55300000000),((3061859723:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5448213861:ℚ)/10000000000),((1764786729665961891417407017157211535787089697083400867593:ℚ)/50527937090859375000000000000000000000000000000000000000000),((-7017768055639611209933867:ℚ)/36480000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6738044441:ℚ)/10000000000),((863087567:ℚ)/1250000000),((29174133323:ℚ)/112500000000),((1163087567:ℚ)/3456250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4808873913:ℚ)/10000000000),((1255298428161605930342776592534383598462428009544477:ℚ)/37324367351531982421875000000000000000000000000000000),((-37300809271205534896161:ℚ)/190000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6857208897:ℚ)/10000000000),((702380951:ℚ)/1000000000),((29531626691:ℚ)/114400000000),((942380951:ℚ)/2812500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2229019503:ℚ)/5000000000),((2372845301920256280436750648056265400862433019736180379:ℚ)/71083645820617675781250000000000000000000000000000000000),((-24105552874272849741449:ℚ)/121600000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6976359517:ℚ)/10000000000),((1428581341:ℚ)/2000000000),((29889078551:ℚ)/116300000000),((1908581341:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4079348827:ℚ)/10000000000),((37827318810338932075559652839852779950182825255259111683:ℚ)/1140920693591250000000000000000000000000000000000000000000),((-97353314218571784045569:ℚ)/486400000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((7095496983:ℚ)/10000000000),((900306383:ℚ)/1250000000),((30246490949:ℚ)/117250000000),((1200306383:ℚ)/3634375000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((732828431:ℚ)/2000000000),((10094082725030552591625667296025542746318330812934614559:ℚ)/309354325414777100086212158203125000000000000000000000000),((-38402950673521874802961:ℚ)/190000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((894382623:ℚ)/1250000000),((7261992689:ℚ)/10000000000),((3803147869:ℚ)/14775000000),((9661992689:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3438748093:ℚ)/10000000000),((5591000309770648723472393039138712800849330259426897898937:ℚ)/171815990835328102111816406250000000000000000000000000000000),((-2469410872669805859127129:ℚ)/12160000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7214621933:ℚ)/10000000000),((1845267:ℚ)/2500000),((30603865799:ℚ)/120100000000),((815089:ℚ)/2462500),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((63963787:ℚ)/200000000),((2647069149429686353825335403510643869936378539569:ℚ)/80769240678024902343750000000000000000000000000000),((-930116538500733541:ℚ)/4560000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1466746993:ℚ)/2000000000),((7500133137:ℚ)/10000000000),((6192240979:ℚ)/24400000000),((9900133137:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2654858937:ℚ)/10000000000),((256634026927698068310478487550191857282387506433912296961:ℚ)/7868623192530517578125000000000000000000000000000000000000),((-7510534113356799444733643:ℚ)/36480000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7452836639:ℚ)/10000000000),((7738234747:ℚ)/10000000000),((31318509917:ℚ)/125800000000),((10138234747:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1971112193:ℚ)/10000000000),((7249787891311356281631930793007246581241786831219529026891:ℚ)/219245580617675781250000000000000000000000000000000000000000),((-2526925346911299:ℚ)/12160000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((480687999:ℚ)/625000000),((159526019:ℚ)/200000000),((2002063997:ℚ)/8100000000),((207526019:ℚ)/629000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((246291245337732960111998817701120211978158982280451:ℚ)/7503486112265625000000000000000000000000000000000000),((-3364973:ℚ)/16000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7929139803:ℚ)/10000000000),((9879859791:ℚ)/10000000000),((32747419409:ℚ)/160000000000),((4093286597:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((716291305064934721992400452625110437980297246373647:ℚ)/18452812500000000000000000000000000000000000000000000),((-3364973:ℚ)/16000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((1966622147:ℚ)/2000000000),((6842016391:ℚ)/5000000000),((7691866441:ℚ)/44160000000),((8042016391:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5803070080534555983722306611225338749:ℚ)/119025000000000000000000000000000000000),((-3364973:ℚ)/16000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC20
#check @N11Formalization.C450Source16GroupedC20.bound
#print axioms N11Formalization.C450Source16GroupedC20.valid0
#print axioms N11Formalization.C450Source16GroupedC20.valid1
#print axioms N11Formalization.C450Source16GroupedC20.valid2
#print axioms N11Formalization.C450Source16GroupedC20.valid3
#print axioms N11Formalization.C450Source16GroupedC20.valid4
#print axioms N11Formalization.C450Source16GroupedC20.valid5
#print axioms N11Formalization.C450Source16GroupedC20.valid6
#print axioms N11Formalization.C450Source16GroupedC20.valid7
#print axioms N11Formalization.C450Source16GroupedC20.valid8
#print axioms N11Formalization.C450Source16GroupedC20.valid9
#print axioms N11Formalization.C450Source16GroupedC20.valid10
#print axioms N11Formalization.C450Source16GroupedC20.valid11
#print axioms N11Formalization.C450Source16GroupedC20.valid12
#print axioms N11Formalization.C450Source16GroupedC20.bound
#print axioms N11Formalization.C450Source16GroupedC20.endpoint_checks
