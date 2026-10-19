import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P53
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(11/16 : Rat),(3/4 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (15/16 : Rat),.S 1 (23/32 : Rat),.L (169341/131072 : Rat) (1741335/1048576 : Rat) (32507/131072 : Rat) (168303/524288 : Rat),.S 0 (11/4 : Rat),.S 2 (29/32 : Rat),.L (1509701/1048576 : Rat) (870051/524288 : Rat) (145273/524288 : Rat) (336359/1048576 : Rat),.L (769683/524288 : Rat) (443353/262144 : Rat) (296411/1048576 : Rat) (343035/1048576 : Rat),.L (749041/524288 : Rat) (443353/262144 : Rat) (72063/262144 : Rat) (343035/1048576 : Rat),.S 1 (23/32 : Rat),.L (352689/262144 : Rat) (451973/262144 : Rat) (67763/262144 : Rat) (349961/1048576 : Rat),.S 0 (11/4 : Rat),.S 2 (31/32 : Rat),.L (784577/524288 : Rat) (1806703/1048576 : Rat) (302309/1048576 : Rat) (174861/524288 : Rat),.L (1599059/1048576 : Rat) (1839975/1048576 : Rat) (308241/1048576 : Rat) (356419/1048576 : Rat),.L (1557177/1048576 : Rat) (1839975/1048576 : Rat) (299937/1048576 : Rat) (356419/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P53
