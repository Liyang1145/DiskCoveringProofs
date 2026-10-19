import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P254
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(11/16 : Rat),(3/4 : Rat),(1/2 : Rat),(9/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 1 (23/32 : Rat),.L (1005845/1048576 : Rat) (9915/8192 : Rat) (24023/131072 : Rat) (243311/1048576 : Rat),.L (129095/131072 : Rat) (650867/524288 : Rat) (49347/262144 : Rat) (249683/1048576 : Rat),.S 1 (23/32 : Rat),.S 0 (19/8 : Rat),.L (1094869/1048576 : Rat) (1282859/1048576 : Rat) (104707/524288 : Rat) (122997/524288 : Rat),.S 2 (17/32 : Rat),.L (1127695/1048576 : Rat) (319417/262144 : Rat) (215781/1048576 : Rat) (61245/262144 : Rat),.L (1157513/1048576 : Rat) (1308207/1048576 : Rat) (55393/262144 : Rat) (250949/1048576 : Rat),.S 0 (19/8 : Rat),.L (280859/262144 : Rat) (1315713/1048576 : Rat) (214955/1048576 : Rat) (252417/1048576 : Rat),.S 2 (17/32 : Rat),.L (1157623/1048576 : Rat) (1310431/1048576 : Rat) (110797/524288 : Rat) (251383/1048576 : Rat),.L (593637/524288 : Rat) (670465/524288 : Rat) (227359/1048576 : Rat) (257353/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P254
