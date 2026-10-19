import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P564
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(21/8 : Rat),(27/32 : Rat),(7/8 : Rat),(7/8 : Rat),(29/32 : Rat)⟩
def toks : List Tok := [.S 0 (41/16 : Rat),.S 1 (55/64 : Rat),.S 0 (81/32 : Rat),.L (1700403/1048576 : Rat) (1776497/1048576 : Rat) (328419/1048576 : Rat) (171827/524288 : Rat),.L (854431/524288 : Rat) (446295/262144 : Rat) (330109/1048576 : Rat) (345397/1048576 : Rat),.S 0 (81/32 : Rat),.L (1715995/1048576 : Rat) (1792029/1048576 : Rat) (331535/1048576 : Rat) (86693/262144 : Rat),.L (1724533/1048576 : Rat) (1800793/1048576 : Rat) (166621/524288 : Rat) (174267/524288 : Rat),.S 1 (55/64 : Rat),.S 0 (83/32 : Rat),.L (429225/262144 : Rat) (1793431/1048576 : Rat) (82929/262144 : Rat) (173527/524288 : Rat),.L (431129/262144 : Rat) (56289/32768 : Rat) (333239/1048576 : Rat) (348625/1048576 : Rat),.S 0 (83/32 : Rat),.L (866323/524288 : Rat) (1809121/1048576 : Rat) (334865/1048576 : Rat) (171/512 : Rat),.S 2 (57/64 : Rat),.L (435083/262144 : Rat) (900459/524288 : Rat) (84101/262144 : Rat) (348559/1048576 : Rat),.L (877939/524288 : Rat) (1817011/1048576 : Rat) (169759/524288 : Rat) (351795/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P564
