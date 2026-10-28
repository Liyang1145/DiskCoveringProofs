import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((802858797:ℚ)/1250000000),((3359929987:ℚ)/5000000000),((-18079509909:ℚ)/49600000000),((-1688576391:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2820084841:ℚ)/5000000000),((4044249879003013925613868352988820834302859716906465003:ℚ)/51688441467285156250000000000000000000000000000000000000),((1727230291488348626805839:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((266462463:ℚ)/400000000),((6839204097:ℚ)/10000000000),((-36994428679:ℚ)/103000000000),((-568987389:ℚ)/2098000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2511046151:ℚ)/5000000000),((113018605474332361437211241821329459999949728860527569:ℚ)/1486187835587500000000000000000000000000000000000000000),((169373352926689376146199:ℚ)/1478656000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((339043729:ℚ)/500000000),((6958526927:ℚ)/10000000000),((-37829688489:ℚ)/104900000000),((-243043729:ℚ)/890000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4685581853:ℚ)/10000000000),((87715280677439320890958420469635964983734279488852123:ℚ)/1155488251562500000000000000000000000000000000000000000),((258764855635142222992311:ℚ)/2310400000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((1380033483:ℚ)/2000000000),((884728699:ℚ)/1250000000),((-1611033631:ℚ)/4450000000),((-2988100449:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2162547337:ℚ)/5000000000),((54143878820523362034797707271771706728940926344160935923:ℚ)/714428311043750000000000000000000000000000000000000000000),((4045868351148174431495519:ℚ)/36966400000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7019441147:ℚ)/10000000000),((3568736847:ℚ)/5000000000),((-19541157929:ℚ)/54350000000),((-5099441147:ℚ)/18275000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3934010399:ℚ)/10000000000),((775647297306537002767126275756449392889482767886874302383:ℚ)/10366251160083007812500000000000000000000000000000000000000),((98780627620224633259282239:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7079071163:ℚ)/10000000000),((7197113141:ℚ)/10000000000),((-13166597329:ℚ)/36550000000),((-15477213489:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3724001441:ℚ)/10000000000),((902766347342524048226924005124748516447993227221157288913:ℚ)/12072377694042968750000000000000000000000000000000000000000),((97595014004157330357726399:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((713869677:ℚ)/1000000000),((3628374027:ℚ)/5000000000),((-19958618189:ℚ)/55300000000),((-1565609031:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3502055613:ℚ)/10000000000),((2801139507696239766155616595438810099480783910814673701:ℚ)/37480372877337646484375000000000000000000000000000000000),((964076824413741116421359:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((3599159041:ℚ)/5000000000),((146327571:ℚ)/200000000),((-806692997:ℚ)/2231000000),((-2639159041:ℚ)/9375000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((81643379:ℚ)/250000000),((10056845630686559552900908330562046091081654783592497199:ℚ)/134640187025070190429687500000000000000000000000000000000),((23804657764283331525843351:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((907241901:ℚ)/1250000000),((7376004739:ℚ)/10000000000),((-40752033173:ℚ)/112500000000),((-2001725703:ℚ)/7090625000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((376456609:ℚ)/1250000000),((1247514995552109700076395906382585261567531580316847:ℚ)/16710707343578338623046875000000000000000000000000000),((1469185282231273048705871:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((1463509651:ℚ)/2000000000),((7435626731:ℚ)/10000000000),((-41169387117:ℚ)/113450000000),((-294411723:ℚ)/1040000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2734857033:ℚ)/10000000000),((1190245756461432213321329950114693999274251081024505589:ℚ)/15951977600000000000000000000000000000000000000000000000),((3713414467862211202613871:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((295086293:ℚ)/400000000),((3777429267:ℚ)/5000000000),((-21002004869:ℚ)/57200000000),((-654858879:ℚ)/2326000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2427584253:ℚ)/10000000000),((77049756151356780679948081365244204957543573668399129:ℚ)/1022474535550000000000000000000000000000000000000000000),((146625824454135644565279:ℚ)/1478656000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((7496363927:ℚ)/10000000000),((3837037379:ℚ)/5000000000),((-21419261653:ℚ)/58150000000),((-5576363927:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1653325751:ℚ)/10000000000),((1045646889151858622321056826957687903089679802788894785407:ℚ)/13893076248437500000000000000000000000000000000000000000000),((89247515860502150029588359:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((951944471:ℚ)/1250000000),((1582492679:ℚ)/2000000000),((-8901448753:ℚ)/23640000000),((-2135833413:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((41828243344362404973678083921627166121964385722906144267:ℚ)/545840539550781250000000000000000000000000000000000000000),((3018029:ℚ)/32000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((981737243:ℚ)/1250000000),((4194541771:ℚ)/5000000000),((-23921792397:ℚ)/61000000000),((-741737243:ℚ)/2700000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3242636831456035769517648253554644406425581932224027:ℚ)/41006250000000000000000000000000000000000000000000000),((3018029:ℚ)/32000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((4165216711:ℚ)/5000000000),((10294019243:ℚ)/10000000000),((-20392711567:ℚ)/43200000000),((-9615650133:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((329303155402167826592027792084713762905296889830671434559:ℚ)/3600000000000000000000000000000000000000000000000000000000),((3018029:ℚ)/32000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((1023511147:ℚ)/1000000000),((1762475517:ℚ)/1250000000),((-10977328619:ℚ)/20000000000),((-831511147:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((24592055134649003073649337050312021756916387119192147:ℚ)/233606400000000000000000000000000000000000000000000000),((3018029:ℚ)/32000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC10
#check @N11Formalization.C450Source19GroupedC10.bound
#print axioms N11Formalization.C450Source19GroupedC10.valid0
#print axioms N11Formalization.C450Source19GroupedC10.valid1
#print axioms N11Formalization.C450Source19GroupedC10.valid2
#print axioms N11Formalization.C450Source19GroupedC10.valid3
#print axioms N11Formalization.C450Source19GroupedC10.valid4
#print axioms N11Formalization.C450Source19GroupedC10.valid5
#print axioms N11Formalization.C450Source19GroupedC10.valid6
#print axioms N11Formalization.C450Source19GroupedC10.valid7
#print axioms N11Formalization.C450Source19GroupedC10.valid8
#print axioms N11Formalization.C450Source19GroupedC10.valid9
#print axioms N11Formalization.C450Source19GroupedC10.valid10
#print axioms N11Formalization.C450Source19GroupedC10.valid11
#print axioms N11Formalization.C450Source19GroupedC10.valid12
#print axioms N11Formalization.C450Source19GroupedC10.valid13
#print axioms N11Formalization.C450Source19GroupedC10.valid14
#print axioms N11Formalization.C450Source19GroupedC10.valid15
#print axioms N11Formalization.C450Source19GroupedC10.bound
#print axioms N11Formalization.C450Source19GroupedC10.endpoint_checks
