import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P467
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(21/32 : Rat),(11/16 : Rat)⟩
def toks : List Tok := [.S 1 (63/64 : Rat),.S 2 (43/64 : Rat),.S 1 (125/128 : Rat),.L (1641677/1048576 : Rat) (54113/32768 : Rat) (39589/131072 : Rat) (83665/262144 : Rat),.L (824807/524288 : Rat) (869935/524288 : Rat) (79573/262144 : Rat) (42039/131072 : Rat),.S 1 (125/128 : Rat),.L (828709/524288 : Rat) (1747817/1048576 : Rat) (159923/524288 : Rat) (21119/65536 : Rat),.L (416337/262144 : Rat) (219509/131072 : Rat) (160713/524288 : Rat) (169779/524288 : Rat),.S 2 (43/64 : Rat),.S 1 (127/128 : Rat),.L (103597/65536 : Rat) (437031/262144 : Rat) (2499/8192 : Rat) (337965/1048576 : Rat),.L (832747/524288 : Rat) (878189/524288 : Rat) (321455/1048576 : Rat) (339619/1048576 : Rat),.S 1 (127/128 : Rat),.L (1673281/1048576 : Rat) (882163/524288 : Rat) (323007/1048576 : Rat) (85303/262144 : Rat),.L (1681217/1048576 : Rat) (443145/262144 : Rat) (162295/524288 : Rat) (85717/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P467
