import Class33Core.SecTrees.Q0M2Sec2Base
namespace Class33Core.SecTrees.Q0M2Sec2.P46
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec2
def box : Box := ⟨(15/8 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 0 (31/16 : Rat),.S 1 (29/32 : Rat),.S 2 (29/32 : Rat),.L (91705/65536 : Rat) (197427/131072 : Rat) (4409/16384 : Rat) (304345/1048576 : Rat),.L (1493251/1048576 : Rat) (1607407/1048576 : Rat) (143649/524288 : Rat) (77475/262144 : Rat),.S 2 (29/32 : Rat),.L (1493251/1048576 : Rat) (1607407/1048576 : Rat) (143649/524288 : Rat) (77475/262144 : Rat),.L (1519683/1048576 : Rat) (1633855/1048576 : Rat) (292519/1048576 : Rat) (78789/262144 : Rat),.S 1 (29/32 : Rat),.S 2 (29/32 : Rat),.L (749877/524288 : Rat) (1613043/1048576 : Rat) (144291/524288 : Rat) (311019/1048576 : Rat),.L (381575/262144 : Rat) (410397/262144 : Rat) (293827/1048576 : Rat) (316695/1048576 : Rat),.S 2 (29/32 : Rat),.L (381575/262144 : Rat) (410397/262144 : Rat) (293827/1048576 : Rat) (316695/1048576 : Rat),.S 0 (63/32 : Rat),.L (389975/262144 : Rat) (1644737/1048576 : Rat) (75119/262144 : Rat) (158661/524288 : Rat),.L (1576333/1048576 : Rat) (1661733/1048576 : Rat) (75933/262144 : Rat) (160353/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec2.P46
