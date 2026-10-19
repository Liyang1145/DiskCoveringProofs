import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P446
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(29/32 : Rat),(15/16 : Rat),(11/16 : Rat),(23/32 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (45/64 : Rat),.S 1 (117/128 : Rat),.L (804935/524288 : Rat) (1697959/1048576 : Rat) (77597/262144 : Rat) (81983/262144 : Rat),.L (1617773/1048576 : Rat) (1706219/1048576 : Rat) (155979/524288 : Rat) (164791/524288 : Rat),.S 1 (117/128 : Rat),.L (812841/524288 : Rat) (1714165/1048576 : Rat) (156765/524288 : Rat) (165585/524288 : Rat),.L (1633579/1048576 : Rat) (861213/524288 : Rat) (315101/1048576 : Rat) (166411/524288 : Rat),.S 2 (45/64 : Rat),.S 1 (119/128 : Rat),.L (812839/524288 : Rat) (1714479/1048576 : Rat) (313529/1048576 : Rat) (331233/1048576 : Rat),.L (1633587/1048576 : Rat) (1722737/1048576 : Rat) (157551/524288 : Rat) (83221/262144 : Rat),.S 1 (119/128 : Rat),.L (820739/524288 : Rat) (1730685/1048576 : Rat) (1237/4096 : Rat) (167237/524288 : Rat),.L (1649381/1048576 : Rat) (27171/16384 : Rat) (318245/1048576 : Rat) (336127/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P446
