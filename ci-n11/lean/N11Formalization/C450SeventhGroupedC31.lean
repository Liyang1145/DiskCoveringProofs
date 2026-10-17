import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((186701171:ℚ)/312500000),((3249648859:ℚ)/5000000000),((1356908197:ℚ)/1668750000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6663060671:ℚ)/10000000000),((-2741391100449716726532830741642839:ℚ)/185880498046875000000000000000000000),((-12927364151123225494295531:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1289895501:ℚ)/2000000000),((134736437:ℚ)/200000000),((9349268507:ℚ)/11060000000),((139856437:ℚ)/142400000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5574337787:ℚ)/10000000000),((-211854270726647626165091597759501953089133627457756921:ℚ)/12683428275000000000000000000000000000000000000000000000),((-20594777695747987663819:ℚ)/147865600000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((3343497729:ℚ)/5000000000),((856947913:ℚ)/1250000000),((24204484103:ℚ)/28125000000),((380977677:ℚ)/395000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((619015421:ℚ)/1250000000),((-408651310407648403226234863604456866952640837843558229:ℚ)/23174285888671875000000000000000000000000000000000000000),((-802739614983447373554419:ℚ)/5776000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((340287699:ℚ)/500000000),((3487172189:ℚ)/5000000000),((2462013893:ℚ)/2860000000),((3615172189:ℚ)/3750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((115314139:ℚ)/250000000),((-117177569547274854654863381431951260814616020924687:ℚ)/6645925000000000000000000000000000000000000000000000),((-12815872830859704463181371:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6924512219:ℚ)/10000000000),((3516862389:ℚ)/5000000000),((16690528511:ℚ)/19225000000),((10934587167:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4248027907:ℚ)/10000000000),((-47038771397218010871035935401449315319588797468477:ℚ)/2602138189315795898437500000000000000000000000000000),((-12801870279512908298656971:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1745972809:ℚ)/2500000000),((709310509:ℚ)/1000000000),((12621809663:ℚ)/14537500000),((734910509:ℚ)/769000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((405429561:ℚ)/1000000000),((-173506221601314095338769673055603660916521794855385063:ℚ)/9601060467529296875000000000000000000000000000000000000),((-511514121181200663512731:ℚ)/3696640000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((1760817547:ℚ)/2500000000),((1788121329:ℚ)/2500000000),((12725722829:ℚ)/14656250000),((5556363987:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1925696913:ℚ)/5000000000),((-533228205834410149383648242183620033274331640709404343:ℚ)/29514801692962646484375000000000000000000000000000000000),((-3193455270125902265613891:ℚ)/23104000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1775662269:ℚ)/2500000000),((7182175397:ℚ)/10000000000),((12829635883:ℚ)/14715625000),((22314526191:ℚ)/23450000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((3637784687:ℚ)/10000000000),((-32129201852908789223562643945133472710157910271845673:ℚ)/1757350913143157958984375000000000000000000000000000000),((-51067198375239735033572459:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((111442789:ℚ)/156250000),((7211865457:ℚ)/10000000000),((805099523:ℚ)/923437500),((22403596371:ℚ)/23545000000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1763179713:ℚ)/5000000000),((-3748436549739231218558966591305388299804969061309:ℚ)/205064883828163146972656250000000000000000000000000),((-51039097729043843542429699:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((7162027901:ℚ)/10000000000),((7241555497:ℚ)/10000000000),((51734195307:ℚ)/59337500000),((7497555497:ℚ)/7880000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((341145337:ℚ)/1000000000),((-11932077646657782414340210793343964116916976983485834163:ℚ)/652886601092529296875000000000000000000000000000000000000),((-51010982382510784833891859:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((7191717291:ℚ)/10000000000),((7271245517:ℚ)/10000000000),((51942021037:ℚ)/59575000000),((22581736551:ℚ)/23735000000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((411587701:ℚ)/1250000000),((-36221230095916690243216580101201407247781264763302810911:ℚ)/1982272835009765625000000000000000000000000000000000000000),((-50982852335670304765234139:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3610703333:ℚ)/5000000000),((7330625497:ℚ)/10000000000),((26074923331:ℚ)/30025000000),((22759876491:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((99052231:ℚ)/312500000),((-1145268522302607090947550530854032468353276654210237353:ℚ)/63439584997558593750000000000000000000000000000000000000),((-50926548141186063876471859:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((728078537:ℚ)/1000000000),((3695002699:ℚ)/5000000000),((1752183253:ℚ)/2017500000),((11469008097:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1454291759:ℚ)/5000000000),((-347378991926428447030910722154378338448477285708791:ℚ)/19246506701660156250000000000000000000000000000000000),((-12717546286219849600866251:ℚ)/92416000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((7340164017:ℚ)/10000000000),((931173153:ℚ)/1250000000),((52981148119:ℚ)/61000000000),((963173153:ℚ)/1008750000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((655606161:ℚ)/2500000000),((-38399320462359915314242291777418451773517628986398134357:ℚ)/2127946875000000000000000000000000000000000000000000000000),((-793965052237227782696259:ℚ)/5776000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7399542607:ℚ)/10000000000),((1892036163:ℚ)/2500000000),((53396798249:ℚ)/61950000000),((5868108489:ℚ)/6100000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((575464421:ℚ)/2500000000),((-363859998158957390086332565727399926557790763033663809:ℚ)/20638182714843750000000000000000000000000000000000000000),((-3168796457722386317311419:ℚ)/23104000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((7518299621:ℚ)/10000000000),((1537380759:ℚ)/2000000000),((54228097347:ℚ)/62900000000),((1588580759:ℚ)/1652000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1467607979:ℚ)/10000000000),((-13390875549054575513764070878797373764166552663852923:ℚ)/759454922485351562500000000000000000000000000000000000),((-4386287:ℚ)/32000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((954632053:ℚ)/1250000000),((3962210639:ℚ)/5000000000),((764713819:ℚ)/900000000),((12270631917:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-4270730179682346003017412287369065971494276876371:ℚ)/253125000000000000000000000000000000000000000000000),((-4386287:ℚ)/32000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((7874569431:ℚ)/10000000000),((4912265621:ℚ)/5000000000),((56721986017:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-2821130589680603629971918437938438801469786256333570859:ℚ)/300000000000000000000000000000000000000000000000000000000),((-4386287:ℚ)/32000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((9774651241:ℚ)/10000000000),((3406165081:ℚ)/2500000000),((70022558687:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-921982096166931975966076227365074669:ℚ)/168196608000000000000000000000000000000),((-4386287:ℚ)/32000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC31
#check @N11Formalization.C450SeventhGroupedC31.bound
#print axioms N11Formalization.C450SeventhGroupedC31.valid0
#print axioms N11Formalization.C450SeventhGroupedC31.valid1
#print axioms N11Formalization.C450SeventhGroupedC31.valid2
#print axioms N11Formalization.C450SeventhGroupedC31.valid3
#print axioms N11Formalization.C450SeventhGroupedC31.valid4
#print axioms N11Formalization.C450SeventhGroupedC31.valid5
#print axioms N11Formalization.C450SeventhGroupedC31.valid6
#print axioms N11Formalization.C450SeventhGroupedC31.valid7
#print axioms N11Formalization.C450SeventhGroupedC31.valid8
#print axioms N11Formalization.C450SeventhGroupedC31.valid9
#print axioms N11Formalization.C450SeventhGroupedC31.valid10
#print axioms N11Formalization.C450SeventhGroupedC31.valid11
#print axioms N11Formalization.C450SeventhGroupedC31.valid12
#print axioms N11Formalization.C450SeventhGroupedC31.valid13
#print axioms N11Formalization.C450SeventhGroupedC31.valid14
#print axioms N11Formalization.C450SeventhGroupedC31.valid15
#print axioms N11Formalization.C450SeventhGroupedC31.valid16
#print axioms N11Formalization.C450SeventhGroupedC31.valid17
#print axioms N11Formalization.C450SeventhGroupedC31.valid18
#print axioms N11Formalization.C450SeventhGroupedC31.bound
#print axioms N11Formalization.C450SeventhGroupedC31.endpoint_checks
