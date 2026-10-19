import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P124
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(31/32 : Rat),(1 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (7/32 : Rat),.S 0 (9/4 : Rat),.L (267395/262144 : Rat) (1252539/1048576 : Rat) (102257/524288 : Rat) (240075/1048576 : Rat),.S 0 (19/8 : Rat),.L (1114819/1048576 : Rat) (1260089/1048576 : Rat) (213283/1048576 : Rat) (60387/262144 : Rat),.L (141215/131072 : Rat) (79817/65536 : Rat) (108087/524288 : Rat) (1913/8192 : Rat),.S 0 (9/4 : Rat),.L (1086795/1048576 : Rat) (319621/262144 : Rat) (207849/1048576 : Rat) (245139/1048576 : Rat),.S 0 (19/8 : Rat),.L (1138601/1048576 : Rat) (160867/131072 : Rat) (217899/1048576 : Rat) (123395/524288 : Rat),.L (1155609/1048576 : Rat) (163241/131072 : Rat) (110601/524288 : Rat) (250503/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P124
