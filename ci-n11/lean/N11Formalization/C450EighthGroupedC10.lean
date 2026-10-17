import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((785750847:ℚ)/1250000000),((1638768583:ℚ)/2500000000),((-10511380081:ℚ)/24800000000),((-2077252541:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((373035683:ℚ)/625000000),((2447897678586993352468377977829457212460128257595088111:ℚ)/155065324401855468750000000000000000000000000000000000000),((70281888357970510559414447:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((6523654189:ℚ)/10000000000),((6792749717:ℚ)/10000000000),((-43709248019:ℚ)/103000000000),((-17330962567:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2693507623:ℚ)/5000000000),((385311538963608730448298384674419628982354442853704371983:ℚ)/24506484862500000000000000000000000000000000000000000000000),((58836401324468965228269213:ℚ)/778240000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((3380645551:ℚ)/5000000000),((3455791403:ℚ)/5000000000),((-22270539821:ℚ)/53400000000),((-9021936653:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((296395177:ℚ)/625000000),((171175803111209058438110219551023589664401118553112087691:ℚ)/11162942360058593750000000000000000000000000000000000000000),((277551892530256268625306407:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((3440052983:ℚ)/5000000000),((697099827:ℚ)/1000000000),((-4495698789:ℚ)/10870000000),((-9200158949:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4387647827:ℚ)/10000000000),((176702310822819755820780364516918039469469266632865214247:ℚ)/11662032555093383789062500000000000000000000000000000000000),((33191189307246979107624101:ℚ)/443596800000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((3469756277:ℚ)/5000000000),((3515206519:ℚ)/5000000000),((-22686445633:ℚ)/54825000000),((-9289268831:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4199881873:ℚ)/10000000000),((68566477229140669197068110613242873376337251613780681809:ℚ)/4527141635266113281250000000000000000000000000000000000000),((276186323943902004207116303:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((34994593:ℚ)/50000000),((7089827127:ℚ)/10000000000),((-45788789889:ℚ)/110600000000),((-93783779:ℚ)/278875000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4003866873:ℚ)/10000000000),((70929402965302056769744876821672535843652508032741:ℚ)/4685046609667205810546875000000000000000000000000000),((3309367506480585189931273901:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((1764581029:ℚ)/2500000000),((7119533923:ℚ)/10000000000),((-45996737461:ℚ)/111550000000),((-4733743087:ℚ)/14003125000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3798322153:ℚ)/10000000000),((23054477487376544751741602646691058124849878475731971839:ℚ)/1531491094406669616699218750000000000000000000000000000000),((1101211969295755917306361367:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7088026679:ℚ)/10000000000),((1787310139:ℚ)/2500000000),((-11551170973:ℚ)/28006250000),((-19024080037:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((922870099:ℚ)/2500000000),((879175629298187294737829138321803235675344981332113044153:ℚ)/58412235975265502929687500000000000000000000000000000000000),((68775226980815798025181383:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((1779432279:ℚ)/2500000000),((1794736757:ℚ)/2500000000),((-11603157299:ℚ)/28125000000),((-4778296837:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1790801697:ℚ)/5000000000),((794661475302410514320855599127475667675256460516021937:ℚ)/52805402961158752441406250000000000000000000000000000000),((68724782226359905707665127:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((7147431427:ℚ)/10000000000),((7208653341:ℚ)/10000000000),((-46620573387:ℚ)/112975000000),((-19202294281:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3468402193:ℚ)/10000000000),((193920019106663738337284987796438321663201966656071093617:ℚ)/12888010493547607421875000000000000000000000000000000000000),((3296371863245905400005848389:ℚ)/44359680000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-7:ℚ)/16),((-3:ℚ)/8),((7177133613:ℚ)/10000000000),((7238359497:ℚ)/10000000000),((-46828516479:ℚ)/113450000000),((-19291400839:ℚ)/56962500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3351539457:ℚ)/10000000000),((13144106930810283626554605174144566984310500637157155668831:ℚ)/873696072169665527343750000000000000000000000000000000000000),((3293957844111120039918056621:ℚ)/44359680000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((3603417839:ℚ)/5000000000),((3634032749:ℚ)/5000000000),((-23518229243:ℚ)/56962500000),((-9690253517:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((807654327:ℚ)/2500000000),((3340730856053045872161610213562396484549006147189117977909:ℚ)/222093521650000000000000000000000000000000000000000000000000),((274295624084864948799788023:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-7:ℚ)/16),((-3:ℚ)/8),((7236537621:ℚ)/10000000000),((3648885673:ℚ)/5000000000),((-2147472701:ℚ)/5200000000),((-19469612863:ℚ)/57437500000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3105160987:ℚ)/10000000000),((694660587348668042474959188948611008568196231409241579519:ℚ)/46188218385314941406250000000000000000000000000000000000000),((274095066506843543075900367:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1816559861:ℚ)/2500000000),((3663738521:ℚ)/5000000000),((-23726169647:ℚ)/57437500000),((-4889679583:ℚ)/14418750000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((743649067:ℚ)/2500000000),((30341559450579844077461501108786895542791028824463897:ℚ)/2017714215359151363372802734375000000000000000000000000),((273894814254485425186588143:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((145918823:ℚ)/200000000),((7386887989:ℚ)/10000000000),((-47868215923:ℚ)/115350000000),((-392956469:ℚ)/1163000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((88694301:ℚ)/312500000),((114248572047646445557349810362001892382550608943014723:ℚ)/7560412671518750000000000000000000000000000000000000000),((1095081830452840911144871783:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((7355344213:ℚ)/10000000000),((465393647:ℚ)/625000000),((-3017755529:ℚ)/7268750000),((-2832290377:ℚ)/8375000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((508847837:ℚ)/2000000000),((193505189099043106752308516196522473397787243864292397031:ℚ)/12809596032714843750000000000000000000000000000000000000000),((4271438875343790241007007:ℚ)/57760000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((370737341:ℚ)/500000000),((7505708147:ℚ)/10000000000),((-48699957029:ℚ)/117250000000),((-1000212023:ℚ)/2955000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1106234471:ℚ)/5000000000),((95182562254906937287402200117449669500665705851873687:ℚ)/6302953014257812500000000000000000000000000000000000000),((1091899758090419061851406007:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((934268623:ℚ)/1250000000),((3871670951:ℚ)/5000000000),((-25181696657:ℚ)/59100000000),((-2522805869:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((227796847:ℚ)/1250000000),((25425131985374380004266725818130400082410672852898774813:ℚ)/1637521618652343750000000000000000000000000000000000000000),((2242354534805911:ℚ)/30400000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((1542350681:ℚ)/2000000000),((4109292931:ℚ)/5000000000),((-26845050517:ℚ)/61000000000),((-4179052043:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((4430467012152176465071935530117234026206434959413682363:ℚ)/276632755200000000000000000000000000000000000000000000000),((75208893:ℚ)/1024000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((1637388773:ℚ)/2000000000),((2529832453:ℚ)/2500000000),((-16748827171:ℚ)/32400000000),((-4464166319:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((12789705876312117505761378477418771428160019158819481531:ℚ)/691200000000000000000000000000000000000000000000000000000),((75208893:ℚ)/1024000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10087524691:ℚ)/10000000000),((1740025367:ℚ)/1250000000),((-11700177569:ℚ)/20000000000),((-28022574073:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((133333291084103298331175032144296032480568061402153051277:ℚ)/6307372800000000000000000000000000000000000000000000000000),((75208893:ℚ)/1024000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC10
#check @N11Formalization.C450EighthGroupedC10.bound
#print axioms N11Formalization.C450EighthGroupedC10.valid0
#print axioms N11Formalization.C450EighthGroupedC10.valid1
#print axioms N11Formalization.C450EighthGroupedC10.valid2
#print axioms N11Formalization.C450EighthGroupedC10.valid3
#print axioms N11Formalization.C450EighthGroupedC10.valid4
#print axioms N11Formalization.C450EighthGroupedC10.valid5
#print axioms N11Formalization.C450EighthGroupedC10.valid6
#print axioms N11Formalization.C450EighthGroupedC10.valid7
#print axioms N11Formalization.C450EighthGroupedC10.valid8
#print axioms N11Formalization.C450EighthGroupedC10.valid9
#print axioms N11Formalization.C450EighthGroupedC10.valid10
#print axioms N11Formalization.C450EighthGroupedC10.valid11
#print axioms N11Formalization.C450EighthGroupedC10.valid12
#print axioms N11Formalization.C450EighthGroupedC10.valid13
#print axioms N11Formalization.C450EighthGroupedC10.valid14
#print axioms N11Formalization.C450EighthGroupedC10.valid15
#print axioms N11Formalization.C450EighthGroupedC10.valid16
#print axioms N11Formalization.C450EighthGroupedC10.valid17
#print axioms N11Formalization.C450EighthGroupedC10.valid18
#print axioms N11Formalization.C450EighthGroupedC10.valid19
#print axioms N11Formalization.C450EighthGroupedC10.valid20
#print axioms N11Formalization.C450EighthGroupedC10.bound
#print axioms N11Formalization.C450EighthGroupedC10.endpoint_checks
