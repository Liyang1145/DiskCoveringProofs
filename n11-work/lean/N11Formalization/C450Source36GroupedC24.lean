import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((5380296043:ℚ)/10000000000),((178914733:ℚ)/312500000),((59422072301:ℚ)/103000000000),((266414733:ℚ)/387500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7842280533:ℚ)/10000000000),((-6996621592414939177807658985870273163282417219186459:ℚ)/18728472900390625000000000000000000000000000000000000),((-47560360213075477542763:ℚ)/112812500000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5622294379:ℚ)/10000000000),((5967015699:ℚ)/10000000000),((61116060653:ℚ)/106800000000),((8767015699:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3690297851:ℚ)/5000000000),((-165341609544932951665273143052549950901426279449399390337:ℚ)/445187544250488281250000000000000000000000000000000000000),((-1507412104894298933245531:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((146599103:ℚ)/250000000),((6087773683:ℚ)/10000000000),((1570193721:ℚ)/2717500000),((8887773683:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((689484219:ℚ)/1000000000),((-1021540916775453088951480091015279861117046915570464622247:ℚ)/2694028018359375000000000000000000000000000000000000000000),((-1508043644100745781091259:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((2992343453:ℚ)/5000000000),((3104230489:ℚ)/5000000000),((31826404171:ℚ)/55300000000),((4504230489:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6641211181:ℚ)/10000000000),((-3199661965110462221421323085509972627000156647319631337:ℚ)/8466888942229747772216796875000000000000000000000000000),((-374995474438829845559651:ℚ)/902500000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((381583767:ℚ)/625000000),((3164540641:ℚ)/5000000000),((4031086369:ℚ)/7031250000),((4564540641:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3189616307:ℚ)/5000000000),((-13668931273977938123202890564748467778094471340514001:ℚ)/36287579369544982910156250000000000000000000000000000),((-372900569617745442638211:ℚ)/902500000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3112963923:ℚ)/5000000000),((1597341849:ℚ)/2500000000),((32670747461:ℚ)/56725000000),((2297341849:ℚ)/3515625000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6107798251:ℚ)/10000000000),((-292703362869105696369202372814135512704050965359461581:ℚ)/770250800997018814086914062500000000000000000000000000),((-93216902626640397899231:ℚ)/225625000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((3143099013:ℚ)/5000000000),((3224819017:ℚ)/5000000000),((2529361007:ℚ)/4400000000),((4624819017:ℚ)/7090625000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((5968123183:ℚ)/10000000000),((-4649140170634667703486231440652805179457867645278871227:ℚ)/12254518718624114990234375000000000000000000000000000000),((-371770271059761587677059:ℚ)/902500000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((3173226503:ℚ)/5000000000),((1642533611:ℚ)/2500000000),((33092585521:ℚ)/58150000000),((212957601:ℚ)/325000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((233022083:ℚ)/400000000),((-46715188321462659393305623921294487843101793186592003:ℚ)/124761279296875000000000000000000000000000000000000000),((-92118161756534954153351:ℚ)/225625000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6466918901:ℚ)/10000000000),((104540211:ℚ)/156250000),((22342810769:ℚ)/39400000000),((296580422:ℚ)/454296875),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5530804239:ℚ)/10000000000),((-10776766855027789354535240130674600656479225269115483:ℚ)/28860609620716422796249389648437500000000000000000000),((-45767470342006924765653:ℚ)/112812500000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6587328469:ℚ)/10000000000),((3405479007:ℚ)/5000000000),((67871299283:ℚ)/120100000000),((4805479007:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((652675311:ℚ)/1250000000),((-422671443431746170495734248478473696542732713292846005941:ℚ)/1134871720600891113281250000000000000000000000000000000000),((-363727677971943577368619:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((3353842229:ℚ)/5000000000),((693129059:ℚ)/1000000000),((34356895603:ℚ)/61000000000),((973129059:ℚ)/1501250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2447266051:ℚ)/5000000000),((-239627063135052341113606420042927081348953398090161631:ℚ)/644969114141845703125000000000000000000000000000000000),((-14449457960659431400811:ℚ)/36100000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6827989437:ℚ)/10000000000),((1434361919:ℚ)/2000000000),((69555926059:ℚ)/125800000000),((1994361919:ℚ)/3050000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4546388927:ℚ)/10000000000),((-15189543428023852204760319147997643734970341107016237633:ℚ)/41827455761718750000000000000000000000000000000000000000),((-56629389468065232312291:ℚ)/144400000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((1413691169:ℚ)/2000000000),((7412148371:ℚ)/10000000000),((14247838183:ℚ)/25920000000),((10212148371:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((752440531:ℚ)/2000000000),((-9631407069863926337650953810540217396712330066733986287:ℚ)/26601448095703125000000000000000000000000000000000000000),((-1393598328258474033647771:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3654372609:ℚ)/5000000000),((9329939549:ℚ)/10000000000),((36460608263:ℚ)/80000000000),((1347771061:ℚ)/1800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1388709937:ℚ)/5000000000),((-14843854988033544868479116185700780373395530469146847:ℚ)/54675000000000000000000000000000000000000000000000000),((-2903225885577051:ℚ)/7600000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((9226227881:ℚ)/10000000000),((410959553:ℚ)/312500000),((28781198389:ℚ)/73600000000),((498459553:ℚ)/625000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2780629127341359407780438982567633145350871252488037:ℚ)/13160705566406250000000000000000000000000000000000000),((-6201497:ℚ)/16000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC24
#check @N11Formalization.C450Source36GroupedC24.bound
#print axioms N11Formalization.C450Source36GroupedC24.valid0
#print axioms N11Formalization.C450Source36GroupedC24.valid1
#print axioms N11Formalization.C450Source36GroupedC24.valid2
#print axioms N11Formalization.C450Source36GroupedC24.valid3
#print axioms N11Formalization.C450Source36GroupedC24.valid4
#print axioms N11Formalization.C450Source36GroupedC24.valid5
#print axioms N11Formalization.C450Source36GroupedC24.valid6
#print axioms N11Formalization.C450Source36GroupedC24.valid7
#print axioms N11Formalization.C450Source36GroupedC24.valid8
#print axioms N11Formalization.C450Source36GroupedC24.valid9
#print axioms N11Formalization.C450Source36GroupedC24.valid10
#print axioms N11Formalization.C450Source36GroupedC24.valid11
#print axioms N11Formalization.C450Source36GroupedC24.valid12
#print axioms N11Formalization.C450Source36GroupedC24.valid13
#print axioms N11Formalization.C450Source36GroupedC24.valid14
#print axioms N11Formalization.C450Source36GroupedC24.bound
#print axioms N11Formalization.C450Source36GroupedC24.endpoint_checks
