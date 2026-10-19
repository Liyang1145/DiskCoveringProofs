import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P490
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(11/4 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(1 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (3 : Rat),.S 1 (31/32 : Rat),.S 2 (31/32 : Rat),.L (1825759/1048576 : Rat) (2031881/1048576 : Rat) (353555/1048576 : Rat) (395359/1048576 : Rat),.L (1855939/1048576 : Rat) (2065165/1048576 : Rat) (359637/1048576 : Rat) (201085/524288 : Rat),.S 2 (31/32 : Rat),.L (1855939/1048576 : Rat) (2065165/1048576 : Rat) (359637/1048576 : Rat) (201085/524288 : Rat),.L (1886617/1048576 : Rat) (2 : Rat) (365833/1048576 : Rat) (102183/262144 : Rat),.L (473813/262144 : Rat) (2 : Rat) (91895/262144 : Rat) (102183/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P490
