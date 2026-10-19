import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P34
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(11/16 : Rat),(3/4 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 1 (23/32 : Rat),.S 0 (9/4 : Rat),.L (807397/1048576 : Rat) (16441/16384 : Rat) (76979/524288 : Rat) (201155/1048576 : Rat),.S 2 (9/32 : Rat),.L (216069/262144 : Rat) (263729/262144 : Rat) (164891/1048576 : Rat) (50419/262144 : Rat),.L (13895/16384 : Rat) (1085595/1048576 : Rat) (169703/1048576 : Rat) (207617/1048576 : Rat),.S 0 (9/4 : Rat),.L (837459/1048576 : Rat) (542701/524288 : Rat) (79867/524288 : Rat) (51895/262144 : Rat),.S 2 (9/32 : Rat),.L (6995/8192 : Rat) (272031/262144 : Rat) (170873/1048576 : Rat) (52027/262144 : Rat),.L (460049/524288 : Rat) (559407/524288 : Rat) (87819/524288 : Rat) (214059/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P34
