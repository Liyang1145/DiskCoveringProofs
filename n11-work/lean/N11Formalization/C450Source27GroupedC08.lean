import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6639218189:ℚ)/10000000000),((273798807:ℚ)/400000000),((-1824189263:ℚ)/3968000000),((-4559218189:ℚ)/12637500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1016566331:ℚ)/2000000000),((3269761223156673168942864556151951887973538021423341671:ℚ)/14483097448730468750000000000000000000000000000000000000),((3219887438372532526658770433:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((3379560733:ℚ)/5000000000),((6964814361:ℚ)/10000000000),((-46683329249:ℚ)/101100000000),((-2339560733:ℚ)/6437500000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2374285267:ℚ)/5000000000),((127054072743682721836556666158685531380495923446394565483:ℚ)/561903379821777343750000000000000000000000000000000000000),((787751418840218757424379297:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6878981597:ℚ)/10000000000),((1756180313:ℚ)/2500000000),((-11805622817:ℚ)/25750000000),((-4798981597:ℚ)/12993750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((548891127:ℚ)/1250000000),((26234951718591859264123227335971684971964917263773290311:ℚ)/117689987311935424804687500000000000000000000000000000000),((8536121548556561425407737:ℚ)/40960000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1734724059:ℚ)/2500000000),((7084618381:ℚ)/10000000000),((-47761565429:ℚ)/103950000000),((-1214724059:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((210093513:ℚ)/500000000),((8510896916326442254587074630068742892944153999305449481:ℚ)/38144312370157241821289062500000000000000000000000000000),((190411733338942970408708913:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6998800969:ℚ)/10000000000),((223265813:ℚ)/312500000),((-1509392317:ℚ)/3278125000),((-4918800969:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((80085279:ℚ)/200000000),((3391548446573708927627761485034868418500985484290909120287:ℚ)/15186515286311340332031250000000000000000000000000000000000),((3011489305145822925343166953:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((1764674017:ℚ)/2500000000),((3587223177:ℚ)/5000000000),((-24285008593:ℚ)/52925000000),((-1244674017:ℚ)/3322656250),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((949250483:ℚ)/2500000000),((53828651291469510765528381801320641064026803535067218281:ℚ)/242676162601126730442047119140625000000000000000000000000),((186015281826583957503166297:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((7088640087:ℚ)/10000000000),((1440876883:ℚ)/2000000000),((-9767891947:ℚ)/21265000000),((-5008640087:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1844621431:ℚ)/5000000000),((1169596258963099030761309686246107925818597637735742345751:ℚ)/5270331721289062500000000000000000000000000000000000000000),((2958567197712105918083053737:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3559290897:ℚ)/5000000000),((7234320229:ℚ)/10000000000),((-49108882061:ℚ)/106800000000),((-2519290897:ℚ)/6704687500),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((715680303:ℚ)/2000000000),((581610862346479910629875301090173487193187074315994779:ℚ)/2619543843425437808036804199218750000000000000000000000),((735213316107870385941129657:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((3574260611:ℚ)/5000000000),((3632126913:ℚ)/5000000000),((-24689142217:ℚ)/53637500000),((-2534260611:ℚ)/6734375000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3464181361:ℚ)/10000000000),((7107278150789984120438880451872025567286332953280231707:ℚ)/31995614467281848192214965820312500000000000000000000000),((730775674649171220040763233:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7178458401:ℚ)/10000000000),((7324114489:ℚ)/10000000000),((-49917030401:ℚ)/107750000000),((-5098458401:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1673117869:ℚ)/5000000000),((1512996031634062019274916741057810901343091178885855700377:ℚ)/6757342917395019531250000000000000000000000000000000000000),((2905315491037172505261261273:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((723832613:ℚ)/1000000000),((1476793327:ℚ)/2000000000),((-10091139943:ℚ)/21740000000),((-515832613:ℚ)/1370625000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3097449871:ℚ)/10000000000),((36295909334002993602189539825932191598696576517315839:ℚ)/161972674376296997070312500000000000000000000000000000),((28696311144921882427948337:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7127134:ℚ)/9765625),((3721905243:ℚ)/5000000000),((-25497147187:ℚ)/54825000000),((-81534144:ℚ)/216015625),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((8836419:ℚ)/31250000),((161373883509302053640624197485324994237392759227717:ℚ)/719569784047780558466911315917968750000000000000000),((10810089345512216259727:ℚ)/56406250000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((3679017943:ℚ)/5000000000),((94543427:ℚ)/125000000),((-650890843:ℚ)/1382500000),((-2639017943:ℚ)/7031250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((253012921:ℚ)/1000000000),((356086293240255810575313487134515529085891133825981539:ℚ)/1564377453178167343139648437500000000000000000000000000),((699455565187327336464126377:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((1869428211:ℚ)/2500000000),((1536621429:ℚ)/2000000000),((-10629592861:ℚ)/22500000000),((-1349428211:ℚ)/3575000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((898157883:ℚ)/5000000000),((195222083422612977054591730807822172075265540893729231:ℚ)/856701269531250000000000000000000000000000000000000000),((170339134180230682364728833:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7597358661:ℚ)/10000000000),((8639230257:ℚ)/10000000000),((-61753072313:ℚ)/114400000000),((-5517358661:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((52730617:ℚ)/2000000000),((37689368488755846109112343142303434957642591724724148383:ℚ)/140733450000000000000000000000000000000000000000000000000),((2652442256856879042061074033:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4276785317:ℚ)/5000000000),((1318495333:ℚ)/1250000000),((-9866457997:ℚ)/16200000000),((-3236785317:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((50371994120636996146502893594326692917441399543296963137:ℚ)/168750000000000000000000000000000000000000000000000000000),((183575083:ℚ)/1024000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((523121471:ℚ)/500000000),((14358185001:ℚ)/10000000000),((-113223665009:ℚ)/160000000000),((-139707157:ℚ)/460000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1202757768972658431106658129983421839977731030135419659096727:ℚ)/3385600000000000000000000000000000000000000000000000000000000),((183575083:ℚ)/1024000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source27 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source27 nn0 nn1 Qcell ((4291:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source27 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC08
#check @N11Formalization.C450Source27GroupedC08.bound
#print axioms N11Formalization.C450Source27GroupedC08.valid0
#print axioms N11Formalization.C450Source27GroupedC08.valid1
#print axioms N11Formalization.C450Source27GroupedC08.valid2
#print axioms N11Formalization.C450Source27GroupedC08.valid3
#print axioms N11Formalization.C450Source27GroupedC08.valid4
#print axioms N11Formalization.C450Source27GroupedC08.valid5
#print axioms N11Formalization.C450Source27GroupedC08.valid6
#print axioms N11Formalization.C450Source27GroupedC08.valid7
#print axioms N11Formalization.C450Source27GroupedC08.valid8
#print axioms N11Formalization.C450Source27GroupedC08.valid9
#print axioms N11Formalization.C450Source27GroupedC08.valid10
#print axioms N11Formalization.C450Source27GroupedC08.valid11
#print axioms N11Formalization.C450Source27GroupedC08.valid12
#print axioms N11Formalization.C450Source27GroupedC08.valid13
#print axioms N11Formalization.C450Source27GroupedC08.valid14
#print axioms N11Formalization.C450Source27GroupedC08.valid15
#print axioms N11Formalization.C450Source27GroupedC08.valid16
#print axioms N11Formalization.C450Source27GroupedC08.bound
#print axioms N11Formalization.C450Source27GroupedC08.endpoint_checks
