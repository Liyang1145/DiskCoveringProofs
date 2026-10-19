import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P172
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(27/32 : Rat),(7/8 : Rat),(3/8 : Rat),(13/32 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (1192429/1048576 : Rat) (81583/65536 : Rat) (114181/524288 : Rat) (250385/1048576 : Rat),.L (1209723/1048576 : Rat) (164619/131072 : Rat) (14483/65536 : Rat) (252659/1048576 : Rat),.S 0 (21/8 : Rat),.L (1206825/1048576 : Rat) (1321115/1048576 : Rat) (57791/262144 : Rat) (126737/524288 : Rat),.L (612311/524288 : Rat) (666529/524288 : Rat) (234631/1048576 : Rat) (255811/1048576 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (1208253/1048576 : Rat) (1321773/1048576 : Rat) (115721/524288 : Rat) (126801/524288 : Rat),.L (1225637/1048576 : Rat) (1333461/1048576 : Rat) (234829/1048576 : Rat) (127945/524288 : Rat),.S 0 (21/8 : Rat),.L (305655/262144 : Rat) (1337557/1048576 : Rat) (234241/1048576 : Rat) (64173/262144 : Rat),.L (620257/524288 : Rat) (1349569/1048576 : Rat) (7429/32768 : Rat) (129523/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P172
