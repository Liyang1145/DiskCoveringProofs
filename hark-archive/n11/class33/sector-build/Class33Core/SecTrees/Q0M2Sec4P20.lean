import Class33Core.SecTrees.Q0M2Sec4Base
namespace Class33Core.SecTrees.Q0M2Sec4.P20
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec4
def box : Box := ⟨(1 : Rat),(3/2 : Rat),(1/2 : Rat),(3/4 : Rat),(1/2 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (5/4 : Rat),.S 1 (5/8 : Rat),.S 2 (5/8 : Rat),.L (61709/131072 : Rat) (395927/524288 : Rat) (93923/1048576 : Rat) (75487/524288 : Rat),.L (275971/524288 : Rat) (894731/1048576 : Rat) (26261/262144 : Rat) (170753/1048576 : Rat),.S 2 (5/8 : Rat),.L (275971/524288 : Rat) (894731/1048576 : Rat) (26261/262144 : Rat) (170753/1048576 : Rat),.L (308545/524288 : Rat) (946239/1048576 : Rat) (29373/262144 : Rat) (180679/1048576 : Rat),.S 1 (5/8 : Rat),.S 2 (5/8 : Rat),.L (599897/1048576 : Rat) (461533/524288 : Rat) (57103/524288 : Rat) (176211/1048576 : Rat),.L (335353/524288 : Rat) (1034681/1048576 : Rat) (127749/1048576 : Rat) (1545/8192 : Rat),.S 2 (5/8 : Rat),.L (335353/524288 : Rat) (1034681/1048576 : Rat) (127749/1048576 : Rat) (1545/8192 : Rat),.S 0 (11/8 : Rat),.L (758775/1048576 : Rat) (1017315/1048576 : Rat) (144625/1048576 : Rat) (97201/524288 : Rat),.L (205519/262144 : Rat) (546343/524288 : Rat) (156777/1048576 : Rat) (6531/32768 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec4.P20
