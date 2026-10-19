import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P498
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(3/4 : Rat),(25/32 : Rat),(13/16 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 2 (27/32 : Rat),.S 1 (49/64 : Rat),.L (789439/524288 : Rat) (1688427/1048576 : Rat) (304237/1048576 : Rat) (326029/1048576 : Rat),.S 2 (53/64 : Rat),.L (1594803/1048576 : Rat) (1688109/1048576 : Rat) (76849/262144 : Rat) (162983/524288 : Rat),.L (1610475/1048576 : Rat) (1704645/1048576 : Rat) (77627/262144 : Rat) (82317/262144 : Rat),.S 1 (49/64 : Rat),.L (402565/262144 : Rat) (860745/524288 : Rat) (310465/1048576 : Rat) (166317/524288 : Rat),.S 2 (55/64 : Rat),.L (1626161/1048576 : Rat) (860589/524288 : Rat) (313625/1048576 : Rat) (83143/262144 : Rat),.L (1641861/1048576 : Rat) (1737709/1048576 : Rat) (79187/262144 : Rat) (41985/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P498
