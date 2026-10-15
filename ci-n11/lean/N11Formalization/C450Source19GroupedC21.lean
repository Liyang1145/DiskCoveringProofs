import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((5937160739:ℚ)/10000000000),((6472448723:ℚ)/10000000000),((8657160739:ℚ)/26700000000),((8776448723:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1348404033:ℚ)/2000000000),((2182487702236975731714812895327527026031:ℚ)/46394476658688000000000000000000000000000),((-394994588611515409912707109:ℚ)/1478656000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6414868219:ℚ)/10000000000),((6711072321:ℚ)/10000000000),((9134868219:ℚ)/27650000000),((3005024107:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1131967011:ℚ)/2000000000),((87397036453390429507128029398661163408237965696959342078973:ℚ)/2069624303241600000000000000000000000000000000000000000000000),((-1230302034626541540112220183:ℚ)/4435968000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6653581337:ℚ)/10000000000),((6949620779:ℚ)/10000000000),((9373581337:ℚ)/28600000000),((9253620779:ℚ)/22120000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((630482859:ℚ)/1250000000),((629233697771284366761032559482260176336994225722241387557:ℚ)/15200786801200000000000000000000000000000000000000000000000),((-417037934174858140938935861:ℚ)/1478656000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3446106643:ℚ)/5000000000),((220902161:ℚ)/312500000),((4806106643:ℚ)/14537500000),((292902161:ℚ)/715000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4349996991:ℚ)/10000000000),((91703690838622706006223494133501900737477573039273830471:ℚ)/2317495158857226562500000000000000000000000000000000000000),((-414597315368208298274041:ℚ)/1444000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1752875333:ℚ)/2500000000),((1437620281:ℚ)/2000000000),((2432875333:ℚ)/7387500000),((1898420281:ℚ)/4652000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3961175009:ℚ)/10000000000),((719928575417266655354972596630819166353066060967275896479:ℚ)/18314406576996900000000000000000000000000000000000000000000),((-17119535537783695883634381:ℚ)/59146240000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3565385983:ℚ)/5000000000),((7307318309:ℚ)/10000000000),((4925385983:ℚ)/15012500000),((9611318309:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((883080677:ℚ)/2500000000),((13963349372842181626787368644821400080703675132752263706760571:ℚ)/357297274602565200000000000000000000000000000000000000000000000),((-431418309798524784931129301:ℚ)/1478656000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((3625013011:ℚ)/5000000000),((1856630147:ℚ)/2500000000),((4985013011:ℚ)/15250000000),((2432630147:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1523270077:ℚ)/5000000000),((195805268292393900627336252870429437055429005815697285559:ℚ)/5035918843219531250000000000000000000000000000000000000000),((-27177340215251283645531589:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((184231607:ℚ)/250000000),((239527623:ℚ)/312500000),((252231607:ℚ)/786250000),((311527623:ℚ)/762500000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1235209303:ℚ)/5000000000),((10898008122066598745817527941743058486546168563042677451:ℚ)/274056975772094726562500000000000000000000000000000000000),((-3601544286952373:ℚ)/12160000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7607696293:ℚ)/10000000000),((1975799099:ℚ)/2500000000),((3442565431:ℚ)/10800000000),((2551799099:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((14915959697679069757026841346879908473357586826143037429:ℚ)/377953374543750000000000000000000000000000000000000000000),((-154361099:ℚ)/512000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((3923036673:ℚ)/5000000000),((9808301461:ℚ)/10000000000),((5283036673:ℚ)/20000000000),((12112301461:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1017774163334031527683461674310427227185444121042373931:ℚ)/20407334400000000000000000000000000000000000000000000000),((-154361099:ℚ)/512000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((1218947979:ℚ)/1250000000),((3403571133:ℚ)/2500000000),((1558947979:ℚ)/6900000000),((3979571133:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((13295630851094507537357710015599525409:ℚ)/203136000000000000000000000000000000000),((-154361099:ℚ)/512000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC21
#check @N11Formalization.C450Source19GroupedC21.bound
#print axioms N11Formalization.C450Source19GroupedC21.valid0
#print axioms N11Formalization.C450Source19GroupedC21.valid1
#print axioms N11Formalization.C450Source19GroupedC21.valid2
#print axioms N11Formalization.C450Source19GroupedC21.valid3
#print axioms N11Formalization.C450Source19GroupedC21.valid4
#print axioms N11Formalization.C450Source19GroupedC21.valid5
#print axioms N11Formalization.C450Source19GroupedC21.valid6
#print axioms N11Formalization.C450Source19GroupedC21.valid7
#print axioms N11Formalization.C450Source19GroupedC21.valid8
#print axioms N11Formalization.C450Source19GroupedC21.valid9
#print axioms N11Formalization.C450Source19GroupedC21.valid10
#print axioms N11Formalization.C450Source19GroupedC21.bound
#print axioms N11Formalization.C450Source19GroupedC21.endpoint_checks
