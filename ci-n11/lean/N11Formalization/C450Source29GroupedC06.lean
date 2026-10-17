import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6817411983:ℚ)/10000000000),((3518093583:ℚ)/5000000000),((-30059029413:ℚ)/49600000000),((-5025411983:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4577980129:ℚ)/10000000000),((501753620631635533799175961:ℚ)/1584287550000000000000000000),((52090873259080643485377313:ℚ)/122880000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((6937254109:ℚ)/10000000000),((887006941:ℚ)/1250000000),((-7597076351:ℚ)/12637500000),((-5145254109:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((841432767:ℚ)/2000000000),((836855629503204727764561012456129603799483731646128983:ℚ)/2673317645654296875000000000000000000000000000000000000),((6216489466221705555804439099:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6997159717:ℚ)/10000000000),((7155914679:ℚ)/10000000000),((-61435061469:ℚ)/102050000000),((-5205159717:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4009800301:ℚ)/10000000000),((174470595434537245838528521896759725518055402154241987593:ℚ)/557563951750000000000000000000000000000000000000000000000),((6190297406927249807104599531:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7057055407:ℚ)/10000000000),((7215764873:ℚ)/10000000000),((-62093413603:ℚ)/103000000000),((-1755018469:ℚ)/3465000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((11883819:ℚ)/31250000),((32723074250689405847585881843824768200356428282384967:ℚ)/104613322055053710937500000000000000000000000000000000),((6163903595891393782447928771:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7116941457:ℚ)/10000000000),((7245686689:ℚ)/10000000000),((-62422553579:ℚ)/103950000000),((-5324941457:ℚ)/10442500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3584558689:ℚ)/10000000000),((4602516641856507375289924654262521852595695979789135506123:ℚ)/14796123870254589843750000000000000000000000000000000000000),((18411924034631725909895072713:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((142937619:ℚ)/200000000),((7275606359:ℚ)/10000000000),((-62751669949:ℚ)/104425000000),((-107097619:ℚ)/209800000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1735266173:ℚ)/5000000000),((74980345357524647197323666306899037757129327410512447:ℚ)/241079867543650000000000000000000000000000000000000000),((7348721457985647684568657:ℚ)/17743872000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7176818133:ℚ)/10000000000),((7305523911:ℚ)/10000000000),((-63080763021:ℚ)/104900000000),((-5384818133:ℚ)/10537500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1676400637:ℚ)/5000000000),((795197977557187521281530918348552518018384770127295931131:ℚ)/2557095887219238281250000000000000000000000000000000000000),((18331531901592512358374085793:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1801688259:ℚ)/2500000000),((3667719687:ℚ)/5000000000),((-10568305519:ℚ)/17562500000),((-1353688259:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((50483747:ℚ)/156250000),((1214319143928272813268690182466890922718287627811780093:ℚ)/3905352110233886718750000000000000000000000000000000000),((1143194299979985827706243697:ℚ)/2772480000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7236685691:ℚ)/10000000000),((1848816037:ℚ)/2500000000),((-16016976407:ℚ)/26462500000),((-5444685691:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((3104523291:ℚ)/10000000000),((3777717201372245646555650933490680428758954319025639947169:ℚ)/12088596921300000000000000000000000000000000000000000000000),((6083511443683609291963763499:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((7296544379:ℚ)/10000000000),((7455080903:ℚ)/10000000000),((-64725889933:ℚ)/106800000000),((-5504544379:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((14176909:ℚ)/50000000),((652199030873628201173280103753898039536425583321428809077:ℚ)/2087579941113281250000000000000000000000000000000000000000),((6056310421946756951247268139:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1839098609:ℚ)/2500000000),((7514889851:ℚ)/10000000000),((-65383788361:ℚ)/107750000000),((-1391098609:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2538742957:ℚ)/10000000000),((16884824255554658551542831270383508361623829487650541939:ℚ)/54058743339160156250000000000000000000000000000000000000),((376806721894354068671668099:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7416236091:ℚ)/10000000000),((7634485143:ℚ)/10000000000),((-66699336573:ℚ)/108700000000),((-5624236091:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2203521547:ℚ)/10000000000),((543522324060051079496403928240236271094821862984147423051:ℚ)/1723360816865625000000000000000000000000000000000000000000),((18003908435276542237065924097:ℚ)/44359680000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3767947537:ℚ)/5000000000),((1968397661:ℚ)/2500000000),((-17332374271:ℚ)/27650000000),((-2871947537:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((649874729:ℚ)/5000000000),((207818011108374916972892250492744132683327991682755680309:ℚ)/646834588400000000000000000000000000000000000000000000000),((1486371916860959623541955651:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((311004859:ℚ)/400000000),((8829063223:ℚ)/10000000000),((-79839695453:ℚ)/114400000000),((-26591651:ℚ)/57600000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((140394906359523662387077487862871:ℚ)/395366400000000000000000000000000),((409643177:ℚ)/1024000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8731005521:ℚ)/10000000000),((10736870123:ℚ)/10000000000),((-100825571353:ℚ)/129600000000),((-6939005521:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((10098339960400860959229235214055813089:ℚ)/25920000000000000000000000000000000000),((409643177:ℚ)/1024000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((664962367:ℚ)/625000000),((7273005881:ℚ)/5000000000),((-71363064691:ℚ)/80000000000),((-184320789:ℚ)/460000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((47487876195079368970459:ℚ)/105800000000000000000000),((409643177:ℚ)/1024000000)⟩
theorem valid15 : Valid source29 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source29 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source29 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source29 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC06
#check @N11Formalization.C450Source29GroupedC06.bound
#print axioms N11Formalization.C450Source29GroupedC06.valid0
#print axioms N11Formalization.C450Source29GroupedC06.valid1
#print axioms N11Formalization.C450Source29GroupedC06.valid2
#print axioms N11Formalization.C450Source29GroupedC06.valid3
#print axioms N11Formalization.C450Source29GroupedC06.valid4
#print axioms N11Formalization.C450Source29GroupedC06.valid5
#print axioms N11Formalization.C450Source29GroupedC06.valid6
#print axioms N11Formalization.C450Source29GroupedC06.valid7
#print axioms N11Formalization.C450Source29GroupedC06.valid8
#print axioms N11Formalization.C450Source29GroupedC06.valid9
#print axioms N11Formalization.C450Source29GroupedC06.valid10
#print axioms N11Formalization.C450Source29GroupedC06.valid11
#print axioms N11Formalization.C450Source29GroupedC06.valid12
#print axioms N11Formalization.C450Source29GroupedC06.valid13
#print axioms N11Formalization.C450Source29GroupedC06.valid14
#print axioms N11Formalization.C450Source29GroupedC06.valid15
#print axioms N11Formalization.C450Source29GroupedC06.bound
#print axioms N11Formalization.C450Source29GroupedC06.endpoint_checks
