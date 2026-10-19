import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P145
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(5/16 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (7/16 : Rat) (839603/1048576 : Rat) (87263/1048576 : Rat) (160147/1048576 : Rat),.S 0 (3/2 : Rat),.L (41779/65536 : Rat) (518547/524288 : Rat) (15915/131072 : Rat) (198227/1048576 : Rat),.L (409723/524288 : Rat) (1223733/1048576 : Rat) (9767/65536 : Rat) (234459/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P145
