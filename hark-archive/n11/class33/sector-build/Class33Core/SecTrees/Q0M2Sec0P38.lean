import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P38
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(11/16 : Rat),(3/4 : Rat),(5/16 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 1 (23/32 : Rat),.L (426897/524288 : Rat) (552305/524288 : Rat) (162875/1048576 : Rat) (26413/131072 : Rat),.L (220761/262144 : Rat) (71105/65536 : Rat) (84251/524288 : Rat) (217721/1048576 : Rat),.S 1 (23/32 : Rat),.S 0 (19/8 : Rat),.L (229925/262144 : Rat) (1115141/1048576 : Rat) (87781/524288 : Rat) (106673/524288 : Rat),.S 2 (11/32 : Rat),.L (952867/1048576 : Rat) (1097133/1048576 : Rat) (45489/262144 : Rat) (104927/524288 : Rat),.L (981433/1048576 : Rat) (17607/16384 : Rat) (187469/1048576 : Rat) (107809/524288 : Rat),.S 0 (19/8 : Rat),.L (949717/1048576 : Rat) (574175/524288 : Rat) (45337/262144 : Rat) (219793/1048576 : Rat),.S 2 (11/32 : Rat),.L (491939/524288 : Rat) (141263/131072 : Rat) (187941/1048576 : Rat) (108125/524288 : Rat),.L (1012255/1048576 : Rat) (1159791/1048576 : Rat) (193423/1048576 : Rat) (3469/16384 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P38
