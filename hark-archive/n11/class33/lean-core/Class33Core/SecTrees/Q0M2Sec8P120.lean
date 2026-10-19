import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P120
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(1/2 : Rat),(5/8 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 1 (9/16 : Rat),.S 2 (15/16 : Rat),.L (596365/524288 : Rat) (1590515/1048576 : Rat) (57105/262144 : Rat) (153273/524288 : Rat),.L (625259/524288 : Rat) (1657945/1048576 : Rat) (3745/16384 : Rat) (19997/65536 : Rat),.S 2 (15/16 : Rat),.S 0 (11/4 : Rat),.S 1 (19/32 : Rat),.L (1362809/1048576 : Rat) (1613305/1048576 : Rat) (32705/131072 : Rat) (311071/1048576 : Rat),.L (1391885/1048576 : Rat) (1645267/1048576 : Rat) (267345/1048576 : Rat) (317427/1048576 : Rat),.L (1345973/1048576 : Rat) (413189/262144 : Rat) (64585/262144 : Rat) (159459/524288 : Rat),.S 0 (11/4 : Rat),.S 1 (19/32 : Rat),.L (1423603/1048576 : Rat) (419955/262144 : Rat) (273577/1048576 : Rat) (40539/131072 : Rat),.L (726201/524288 : Rat) (1711795/1048576 : Rat) (279245/1048576 : Rat) (41337/131072 : Rat),.L (1405273/1048576 : Rat) (860121/524288 : Rat) (134987/524288 : Rat) (332385/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P120
