import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((636140363:ℚ)/1000000000),((6646451373:ℚ)/10000000000),((-44925159611:ℚ)/49600000000),((-7885824719:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5789697761:ℚ)/10000000000),((10872391927077740041654994092118820121389:ℚ)/809094960640000000000000000000000000000000),((919677390444483824354253463:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3299472043:ℚ)/5000000000),((676522037:ℚ)/1000000000),((-4575654259:ℚ)/5150000000),((-40973136559:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((324417221:ℚ)/625000000),((22713611050826556552573784232950998229585636393536129579:ℚ)/1834774602549743652343750000000000000000000000000000000000),((8502584038634312938021:ℚ)/51200000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((3358856607:ℚ)/5000000000),((688398869:ℚ)/1000000000),((-4658792083:ℚ)/5245000000),((-13915045297:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((973278053:ℚ)/2000000000),((44146204288774839566602533902049249408319279174633973507:ℚ)/3571630414347265625000000000000000000000000000000000000000),((3073281466335763735697389:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((6836481661:ℚ)/10000000000),((108490197:ℚ)/156250000),((-734431379:ℚ)/834375000),((-85034261593:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((226043853:ℚ)/500000000),((12018666111432710645654395849360890813097701922365702113:ℚ)/1011601968682193756103515625000000000000000000000000000000),((225234993189618695854423:ℚ)/1353750000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6895865641:ℚ)/10000000000),((700275637:ℚ)/1000000000),((-4741929459:ℚ)/5387500000),((-85806253333:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2169289517:ℚ)/5000000000),((6858000822793445081004746307239700393861250692469088639491:ℚ)/577392262041497802734375000000000000000000000000000000000000),((3077137187728584212219181:ℚ)/18483200000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((869406183:ℚ)/1250000000),((353106999:ℚ)/500000000),((-2391748993:ℚ)/2717500000),((-3607426793:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((829761457:ℚ)/2000000000),((74610853796667629939291392390204983315098650925681705731:ℚ)/6283399974504849243164062500000000000000000000000000000000),((2309300781443112072617647:ℚ)/13862400000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((3507316567:ℚ)/5000000000),((7091831729:ℚ)/10000000000),((-2826048359:ℚ)/3225000000),((-43675115371:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((246905079:ℚ)/625000000),((22037761488926269829331774681717305444136549610230268957:ℚ)/1892006132958984375000000000000000000000000000000000000000),((308003363410616932462941109:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((440270307:ℚ)/625000000),((3560761721:ℚ)/5000000000),((-24125332047:ℚ)/27531250000),((-5483513991:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((769539627:ℚ)/2000000000),((33182866105268126397273924310213808176655312193640691618721:ℚ)/2848918560005855560302734375000000000000000000000000000000000),((77025000076304590598208709:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1414803331:ℚ)/2000000000),((3575607559:ℚ)/5000000000),((-24229252913:ℚ)/27650000000),((-17624443303:ℚ)/22215000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1871118689:ℚ)/5000000000),((723254262337586335749794888724826631802257756697946330817533:ℚ)/62096734206880078125000000000000000000000000000000000000000000),((77049170384866814837424069:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((177592709:ℚ)/250000000),((179522669:ℚ)/250000000),((-1216658683:ℚ)/1388437500),((-2212705217:ℚ)/2788750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3633865403:ℚ)/10000000000),((484884441853893777596596570548261778356425027780987702663:ℚ)/41632085520680983257293701171875000000000000000000000000000),((192683379451857918912989:ℚ)/1155200000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((713340003:ℚ)/1000000000),((3605299183:ℚ)/5000000000),((-24437094281:ℚ)/27887500000),((-8889420039:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((704462601:ℚ)/2000000000),((689125316783679887902966210827940568956835664196957289861743:ℚ)/59169898373981549072265625000000000000000000000000000000000000),((77097544262265507114713461:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((1432618333:ℚ)/2000000000),((7240289937:ℚ)/10000000000),((-49082029559:ℚ)/56012500000),((-17856038329:ℚ)/22500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3407267313:ℚ)/10000000000),((1726842765681101781964763195364272234315045207993422277:ℚ)/148275247150085449218750000000000000000000000000000000000),((925460973962505089978862943:ℚ)/5544960000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((224774477:ℚ)/312500000),((3634990737:ℚ)/5000000000),((-24644935159:ℚ)/28125000000),((-2802068201:ℚ)/3530468750),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3288361183:ℚ)/10000000000),((16534179624167461937653638262664504866377473674814461933054319:ℚ)/1419751374149322509765625000000000000000000000000000000000000000),((231437887456048020482325343:ℚ)/1386240000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((722247483:ℚ)/1000000000),((7299672977:ℚ)/10000000000),((-49497710839:ℚ)/56487500000),((-9005217279:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3165159013:ℚ)/10000000000),((8442520241310650574689338460337977840100638633665563874186319:ℚ)/724963405852037962341308593750000000000000000000000000000000000),((308680752910596287261730421:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7252166361:ℚ)/10000000000),((7329364447:ℚ)/10000000000),((-49705551129:ℚ)/56725000000),((-30146054231:ℚ)/37975000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3037137489:ℚ)/10000000000),((613041998883315644320624320284879315919934065372230628779249:ℚ)/52644023510338572265625000000000000000000000000000000000000000),((308777700231544982897701141:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((3640928929:ℚ)/5000000000),((1839763971:ℚ)/2500000000),((-12478347797:ℚ)/14240625000),((-45412076077:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((36295733:ℚ)/125000000),((446543986057183423304840250109029421212360488821440176519:ℚ)/38347627923646545410156250000000000000000000000000000000000),((57914004732017851291755127:ℚ)/346560000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3655774661:ℚ)/5000000000),((7418438661:ℚ)/10000000000),((-4575370057:ℚ)/5200000000),((-45605070593:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((276393131:ℚ)/1000000000),((2310338194981582151869907251227094037863443367393733022571:ℚ)/194883017550000000000000000000000000000000000000000000000000),((927206424929844223268054887:ℚ)/5544960000000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7370932153:ℚ)/10000000000),((747782131:ℚ)/1000000000),((-1691491639:ℚ)/1922500000),((-91982117989:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2461428181:ℚ)/10000000000),((14238137912119073569312639485056206548755064495458173919:ℚ)/1201347054450236328125000000000000000000000000000000000000),((3092631021335337221375389:ℚ)/18483200000000000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((928789357:ℚ)/1250000000),((5934833:ℚ)/7812500),((-80587662:ℚ)/90859375),((-11594261641:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1058550267:ℚ)/5000000000),((160593520815414994373399053543125457830574355845689467:ℚ)/13099484379527735710144042968750000000000000000000000000),((188996717579207488061:ℚ)/1128125000000000000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((7549079889:ℚ)/10000000000),((1566822941:ℚ)/2000000000),((-3549253529:ℚ)/3940000000),((-94298038557:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4632929:ℚ)/40000000),((27830831423920158848330387787062425395536219138533686683:ℚ)/2133632469975000000000000000000000000000000000000000000000),((4288967:ℚ)/25600000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((973326069:ℚ)/1250000000),((4154583313:ℚ)/5000000000),((-28282083191:ℚ)/30500000000),((-4057746299:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((234385809681480211894735645850340959590631465418781686271:ℚ)/16159096582031250000000000000000000000000000000000000000000),((4288967:ℚ)/25600000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((4130830417:ℚ)/5000000000),((510466249:ℚ)/500000000),(-1:ℚ),((-51780795421:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((47026193657266445927950493397150271:ℚ)/2400000000000000000000000000000000000),((4288967:ℚ)/25600000)⟩
theorem valid21 : Valid seventh packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10161820287:ℚ)/10000000000),((14009510863:ℚ)/10000000000),(-1:ℚ),((-42754554577:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5879071945448085784527823:ℚ)/270848000000000000000000000),((4288967:ℚ)/25600000)⟩
theorem valid22 : Valid seventh packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC03
#check @N11Formalization.C450SeventhGroupedC03.bound
#print axioms N11Formalization.C450SeventhGroupedC03.valid0
#print axioms N11Formalization.C450SeventhGroupedC03.valid1
#print axioms N11Formalization.C450SeventhGroupedC03.valid2
#print axioms N11Formalization.C450SeventhGroupedC03.valid3
#print axioms N11Formalization.C450SeventhGroupedC03.valid4
#print axioms N11Formalization.C450SeventhGroupedC03.valid5
#print axioms N11Formalization.C450SeventhGroupedC03.valid6
#print axioms N11Formalization.C450SeventhGroupedC03.valid7
#print axioms N11Formalization.C450SeventhGroupedC03.valid8
#print axioms N11Formalization.C450SeventhGroupedC03.valid9
#print axioms N11Formalization.C450SeventhGroupedC03.valid10
#print axioms N11Formalization.C450SeventhGroupedC03.valid11
#print axioms N11Formalization.C450SeventhGroupedC03.valid12
#print axioms N11Formalization.C450SeventhGroupedC03.valid13
#print axioms N11Formalization.C450SeventhGroupedC03.valid14
#print axioms N11Formalization.C450SeventhGroupedC03.valid15
#print axioms N11Formalization.C450SeventhGroupedC03.valid16
#print axioms N11Formalization.C450SeventhGroupedC03.valid17
#print axioms N11Formalization.C450SeventhGroupedC03.valid18
#print axioms N11Formalization.C450SeventhGroupedC03.valid19
#print axioms N11Formalization.C450SeventhGroupedC03.valid20
#print axioms N11Formalization.C450SeventhGroupedC03.valid21
#print axioms N11Formalization.C450SeventhGroupedC03.valid22
#print axioms N11Formalization.C450SeventhGroupedC03.bound
#print axioms N11Formalization.C450SeventhGroupedC03.endpoint_checks
