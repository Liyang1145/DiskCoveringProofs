import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6362549917:ℚ)/10000000000),((6644835373:ℚ)/10000000000),((-18974506119:ℚ)/24800000000),((-65508049087:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2893470321:ℚ)/5000000000),((17256353683462619526770707550646058831174645238193076339897:ℚ)/1011368700800000000000000000000000000000000000000000000000000),((2359283637872063980531670227:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3300070171:ℚ)/5000000000),((845454207:ℚ)/1250000000),((-2416362621:ℚ)/3218750000),((-34060771881:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5187501677:ℚ)/10000000000),((925133983958603000394288764237876633753705802228535579123:ℚ)/57336706329679489135742187500000000000000000000000000000000),((110673443111349802466111761:ℚ)/693120000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((839866637:ℚ)/1250000000),((6882430219:ℚ)/10000000000),((-19687290657:ℚ)/26225000000),((-8678533007:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4862956923:ℚ)/10000000000),((32412525291570712536376158994477761928105902018463106942519:ℚ)/2009042108070336914062500000000000000000000000000000000000000),((2362798445943116586752637443:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((6837724329:ℚ)/10000000000),((1388365577:ℚ)/2000000000),((-1324365577:ℚ)/1780000000),((-70734967619:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4517132661:ℚ)/10000000000),((1205272768279733290263610364311645804722519520035151733:ℚ)/76731882661523437500000000000000000000000000000000000000),((94547465371136455084999627:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6897119399:ℚ)/10000000000),((3500612577:ℚ)/5000000000),((-10021837731:ℚ)/13468750000),((-71388313389:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((866930611:ℚ)/2000000000),((283486130216962764661780260082125804219297499283525850281813:ℚ)/18043508188796806335449218750000000000000000000000000000000000),((1773433962974404729766780881:ℚ)/11089920000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6956514119:ℚ)/10000000000),((7060622037:ℚ)/10000000000),((-20221866111:ℚ)/27175000000),((-24013885103:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((828935419:ℚ)/2000000000),((263310374035377667103330931313001717093277672603502177985937:ℚ)/16755733265346264648437500000000000000000000000000000000000000),((7096423185286617420987044041:ℚ)/44359680000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7015908497:ℚ)/10000000000),((7090320337:ℚ)/10000000000),((-6770320337:ℚ)/9137500000),((-72694993467:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3946118587:ℚ)/10000000000),((14352502814095062284284557957685494811896865024509402359639:ℚ)/925239175099032592773437500000000000000000000000000000000000),((2365923707060599311464805947:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((176140139:ℚ)/250000000),((445001159:ℚ)/625000000),((-1275003477:ℚ)/1720703125),((-260791647:ℚ)/395000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1921603141:ℚ)/5000000000),((98662062681796662534911636309774986948158107211529359917:ℚ)/6359193214298784732818603515625000000000000000000000000000),((9243648311504243394330603:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3537651271:ℚ)/5000000000),((357485833:ℚ)/500000000),((-1024457499:ℚ)/1382500000),((-12224721327:ℚ)/18512500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1868803063:ℚ)/5000000000),((140522555265399489586530184902244366784332384445462311853:ℚ)/9055773738503344726562500000000000000000000000000000000000),((5917062942926231427164107:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3552499721:ℚ)/5000000000),((1435882937:ℚ)/2000000000),((-1371882937:ℚ)/1851250000),((-36837496931:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((907270753:ℚ)/2500000000),((191445414666026376782060304396251822641551745062457957959:ℚ)/12335432746868439483642578125000000000000000000000000000000),((94691093413123364995367147:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3567348131:ℚ)/5000000000),((7209112621:ℚ)/10000000000),((-20667337863:ℚ)/27887500000),((-37000829441:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1758682949:ℚ)/5000000000),((1689962868720858362942402133287894517416758076605093954716641:ℚ)/108872613008126050292968750000000000000000000000000000000000000),((2367730442239673388344835283:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7164393003:ℚ)/10000000000),((1809702617:ℚ)/2500000000),((-5189107851:ℚ)/7001562500),((-74328323033:ℚ)/112500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1701069819:ℚ)/5000000000),((10790318344109171631854443460920966602672242831182494083:ℚ)/695040221016025543212890625000000000000000000000000000000),((148011531118544899757806507:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3597044833:ℚ)/5000000000),((7268508229:ℚ)/10000000000),((-6948508229:ℚ)/9375000000),((-37327493163:ℚ)/56487500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3283034237:ℚ)/10000000000),((544308729795078598936265986767381617106981766604153057083849:ℚ)/35055589485168457031250000000000000000000000000000000000000000),((2368639502336688706483043683:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7223786251:ℚ)/10000000000),((7298205903:ℚ)/10000000000),((-20934617709:ℚ)/28243750000),((-74981648761:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3159610497:ℚ)/10000000000),((28145291871296181641624646077543765013696017089232252763887:ℚ)/1812408514630094905853271484375000000000000000000000000000000),((7107286366607883528951903601:ℚ)/44359680000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7253482761:ℚ)/10000000000),((7327903493:ℚ)/10000000000),((-21023710479:ℚ)/28362500000),((-10758330053:ℚ)/16275000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((757835103:ℚ)/2500000000),((938609155841692185248921844294360262881971323532176954553057:ℚ)/60433190254215197753906250000000000000000000000000000000000000),((2369552357532389318532489187:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1820794799:ℚ)/2500000000),((7357600999:ℚ)/10000000000),((-7037600999:ℚ)/9493750000),((-18908742789:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((579515971:ℚ)/2000000000),((4215288295524093751094826034263950215057157267370700199:ℚ)/271369115901184082031250000000000000000000000000000000000),((2370010208317911147615345963:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1828218889:ℚ)/2500000000),((7416995763:ℚ)/10000000000),((-148888023:ℚ)/200000000),((-18990407779:ℚ)/28837500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((10771599:ℚ)/39062500),((54503293837411043832635039252777852637940464504563:ℚ)/3465005859375000000000000000000000000000000000000000),((7112786268857929621150413241:ℚ)/44359680000000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3686134029:ℚ)/5000000000),((1869097551:ℚ)/2500000000),((-1789097551:ℚ)/2403125000),((-38307474319:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2454203911:ℚ)/10000000000),((1845583024197163888062045762097830828710418632898087110597:ℚ)/117319048286155891418457031250000000000000000000000000000000),((444722081159339944407282289:ℚ)/2772480000000000000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7431660273:ℚ)/10000000000),((7595178149:ℚ)/10000000000),((-21825534447:ℚ)/29075000000),((-77268263003:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((84346373:ℚ)/400000000),((24011980164098506445523503712774143239251105750472762345249:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((2373707172018851105318822563:ℚ)/14786560000000000000000000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((3775221937:ℚ)/5000000000),((783275049:ℚ)/1000000000),((-751275049:ℚ)/985000000),((-39287441307:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((45703887:ℚ)/400000000),((1122687114577650052544253932126224067192449129158544949:ℚ)/66676014686718750000000000000000000000000000000000000000),((164389393:ℚ)/1024000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((3894003967:ℚ)/5000000000),((4153941221:ℚ)/5000000000),((-11981823663:ℚ)/15250000000),((-4510449293:ℚ)/7200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((32645446296512070018734948707763635913195721135376498649:ℚ)/1795455175781250000000000000000000000000000000000000000000),((164389393:ℚ)/1024000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((413156239:ℚ)/500000000),((2041656971:ℚ)/2000000000),((-1977656971:ℚ)/2160000000),((-4320718629:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((302081018153572152520515260428184005914527868045431:ℚ)/11809800000000000000000000000000000000000000000000000),((164389393:ℚ)/1024000000)⟩
theorem valid21 : Valid eighth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2540870283:ℚ)/2500000000),((14008757193:ℚ)/10000000000),(-1:ℚ),((-26829573113:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((48549669014080177806322811:ℚ)/1523520000000000000000000000),((164389393:ℚ)/1024000000)⟩
theorem valid22 : Valid eighth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC05
#check @N11Formalization.C450EighthGroupedC05.bound
#print axioms N11Formalization.C450EighthGroupedC05.valid0
#print axioms N11Formalization.C450EighthGroupedC05.valid1
#print axioms N11Formalization.C450EighthGroupedC05.valid2
#print axioms N11Formalization.C450EighthGroupedC05.valid3
#print axioms N11Formalization.C450EighthGroupedC05.valid4
#print axioms N11Formalization.C450EighthGroupedC05.valid5
#print axioms N11Formalization.C450EighthGroupedC05.valid6
#print axioms N11Formalization.C450EighthGroupedC05.valid7
#print axioms N11Formalization.C450EighthGroupedC05.valid8
#print axioms N11Formalization.C450EighthGroupedC05.valid9
#print axioms N11Formalization.C450EighthGroupedC05.valid10
#print axioms N11Formalization.C450EighthGroupedC05.valid11
#print axioms N11Formalization.C450EighthGroupedC05.valid12
#print axioms N11Formalization.C450EighthGroupedC05.valid13
#print axioms N11Formalization.C450EighthGroupedC05.valid14
#print axioms N11Formalization.C450EighthGroupedC05.valid15
#print axioms N11Formalization.C450EighthGroupedC05.valid16
#print axioms N11Formalization.C450EighthGroupedC05.valid17
#print axioms N11Formalization.C450EighthGroupedC05.valid18
#print axioms N11Formalization.C450EighthGroupedC05.valid19
#print axioms N11Formalization.C450EighthGroupedC05.valid20
#print axioms N11Formalization.C450EighthGroupedC05.valid21
#print axioms N11Formalization.C450EighthGroupedC05.valid22
#print axioms N11Formalization.C450EighthGroupedC05.bound
#print axioms N11Formalization.C450EighthGroupedC05.endpoint_checks
