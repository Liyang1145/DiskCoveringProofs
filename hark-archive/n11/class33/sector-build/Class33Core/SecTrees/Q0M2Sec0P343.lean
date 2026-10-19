import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P343
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/16 : Rat) (884761/1048576 : Rat) (3113/262144 : Rat) (84417/524288 : Rat),.S 0 (3/2 : Rat),.L (172677/262144 : Rat) (1234529/1048576 : Rat) (131579/1048576 : Rat) (236563/1048576 : Rat),.S 0 (7/4 : Rat),.L (62109/65536 : Rat) (341249/262144 : Rat) (94923/524288 : Rat) (131035/524288 : Rat),.S 2 (11/16 : Rat),.L (279737/262144 : Rat) (1436915/1048576 : Rat) (53521/262144 : Rat) (276197/1048576 : Rat),.L (1167325/1048576 : Rat) (744331/524288 : Rat) (223479/1048576 : Rat) (143197/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P343
