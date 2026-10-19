import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P183
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(15/16 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 2 (9/16 : Rat),.S 1 (29/32 : Rat),.L (596365/524288 : Rat) (1556739/1048576 : Rat) (57105/262144 : Rat) (299851/1048576 : Rat),.L (1221527/1048576 : Rat) (1590515/1048576 : Rat) (58507/262144 : Rat) (153273/524288 : Rat),.S 1 (29/32 : Rat),.S 0 (11/4 : Rat),.S 2 (19/32 : Rat),.L (1362809/1048576 : Rat) (98751/65536 : Rat) (32705/131072 : Rat) (19029/65536 : Rat),.L (1391885/1048576 : Rat) (1611973/1048576 : Rat) (267345/1048576 : Rat) (310807/1048576 : Rat),.L (1345973/1048576 : Rat) (202369/131072 : Rat) (64585/262144 : Rat) (312193/1048576 : Rat),.S 0 (11/4 : Rat),.S 2 (19/32 : Rat),.L (2721/2048 : Rat) (1613305/1048576 : Rat) (267593/1048576 : Rat) (311071/1048576 : Rat),.L (177761/131072 : Rat) (1645267/1048576 : Rat) (273279/1048576 : Rat) (317427/1048576 : Rat),.L (1375553/1048576 : Rat) (413189/262144 : Rat) (264139/1048576 : Rat) (159459/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P183
