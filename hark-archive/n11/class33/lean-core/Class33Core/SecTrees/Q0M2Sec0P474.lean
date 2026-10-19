import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P474
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(11/16 : Rat),(23/32 : Rat)⟩
def toks : List Tok := [.S 1 (61/64 : Rat),.S 2 (45/64 : Rat),.S 1 (121/128 : Rat),.L (820749/524288 : Rat) (1730995/1048576 : Rat) (79169/262144 : Rat) (41817/131072 : Rat),.L (1649413/1048576 : Rat) (1739253/1048576 : Rat) (79563/262144 : Rat) (336189/1048576 : Rat),.S 1 (121/128 : Rat),.L (1657287/1048576 : Rat) (1747203/1048576 : Rat) (79955/262144 : Rat) (337781/1048576 : Rat),.L (1665195/1048576 : Rat) (438865/262144 : Rat) (321395/1048576 : Rat) (339435/1048576 : Rat),.S 2 (45/64 : Rat),.S 1 (123/128 : Rat),.L (1657329/1048576 : Rat) (873755/524288 : Rat) (79957/262144 : Rat) (168921/524288 : Rat),.L (1665249/1048576 : Rat) (877883/524288 : Rat) (160703/524288 : Rat) (42437/131072 : Rat),.S 1 (123/128 : Rat),.L (836553/524288 : Rat) (1763717/1048576 : Rat) (80743/262144 : Rat) (170545/524288 : Rat),.L (420255/262144 : Rat) (885987/524288 : Rat) (324551/1048576 : Rat) (171373/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P474
