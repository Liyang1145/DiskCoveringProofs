import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P218
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(29/32 : Rat),(15/16 : Rat),(3/8 : Rat),(13/32 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (1255811/1048576 : Rat) (1371097/1048576 : Rat) (30089/131072 : Rat) (131633/524288 : Rat),.L (318363/262144 : Rat) (1382969/1048576 : Rat) (61039/262144 : Rat) (265595/1048576 : Rat),.S 0 (21/8 : Rat),.L (79381/65536 : Rat) (1386877/1048576 : Rat) (60875/262144 : Rat) (266363/1048576 : Rat),.S 0 (43/16 : Rat),.L (650971/524288 : Rat) (1383001/1048576 : Rat) (124861/524288 : Rat) (132801/524288 : Rat),.L (1309981/1048576 : Rat) (347817/262144 : Rat) (125647/524288 : Rat) (267225/1048576 : Rat),.S 2 (25/64 : Rat),.S 0 (21/8 : Rat),.L (1271691/1048576 : Rat) (86721/65536 : Rat) (60953/262144 : Rat) (66623/262144 : Rat),.L (1289413/1048576 : Rat) (1399467/1048576 : Rat) (247273/1048576 : Rat) (268835/1048576 : Rat),.S 0 (21/8 : Rat),.L (642975/524288 : Rat) (701657/524288 : Rat) (246597/1048576 : Rat) (134795/524288 : Rat),.L (1304203/1048576 : Rat) (707791/524288 : Rat) (62541/262144 : Rat) (272001/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P218
