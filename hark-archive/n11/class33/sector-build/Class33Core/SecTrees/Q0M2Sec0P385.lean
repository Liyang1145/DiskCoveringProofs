import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P385
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(29/32 : Rat),(19/32 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (39/64 : Rat),.S 1 (113/128 : Rat),.L (741761/524288 : Rat) (783879/524288 : Rat) (285379/1048576 : Rat) (151017/524288 : Rat),.L (1491451/1048576 : Rat) (1576019/1048576 : Rat) (286943/1048576 : Rat) (303671/1048576 : Rat),.S 1 (113/128 : Rat),.L (1499285/1048576 : Rat) (395985/262144 : Rat) (288489/1048576 : Rat) (152621/524288 : Rat),.L (1507207/1048576 : Rat) (796101/524288 : Rat) (145027/524288 : Rat) (306881/1048576 : Rat),.S 2 (39/64 : Rat),.S 1 (115/128 : Rat),.L (1499383/1048576 : Rat) (1584279/1048576 : Rat) (288509/1048576 : Rat) (305309/1048576 : Rat),.L (1507317/1048576 : Rat) (1592539/1048576 : Rat) (290075/1048576 : Rat) (76737/262144 : Rat),.S 1 (115/128 : Rat),.L (378783/262144 : Rat) (800231/524288 : Rat) (291619/1048576 : Rat) (38565/131072 : Rat),.L (380765/262144 : Rat) (804361/524288 : Rat) (146593/524288 : Rat) (310161/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P385
