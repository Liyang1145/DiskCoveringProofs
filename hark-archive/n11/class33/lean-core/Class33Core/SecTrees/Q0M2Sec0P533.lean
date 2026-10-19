import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P533
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(3/4 : Rat),(13/16 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (17/8 : Rat),.S 2 (15/16 : Rat),.L (43937/32768 : Rat) (1639339/1048576 : Rat) (135057/524288 : Rat) (316247/1048576 : Rat),.L (1459647/1048576 : Rat) (1701201/1048576 : Rat) (8771/32768 : Rat) (82145/262144 : Rat),.S 2 (15/16 : Rat),.S 1 (25/32 : Rat),.L (1459439/1048576 : Rat) (1662155/1048576 : Rat) (280631/1048576 : Rat) (320791/1048576 : Rat),.L (1487595/1048576 : Rat) (211391/131072 : Rat) (143091/524288 : Rat) (40821/131072 : Rat),.S 1 (25/32 : Rat),.L (1516111/1048576 : Rat) (862327/524288 : Rat) (291813/1048576 : Rat) (333267/1048576 : Rat),.L (771943/524288 : Rat) (1753441/1048576 : Rat) (297305/1048576 : Rat) (169515/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P533
