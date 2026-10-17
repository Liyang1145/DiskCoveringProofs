import N11Formalization.FlashCosineLeaf284Oracle

set_option autoImplicit false
open N11Formalization
open N11Formalization.FlashCosineLeaf284Bridge
open N11Formalization.FlashCosineLeaf284Oracle

#check @wNum
#check @wDen
#eval (List.ofFn (fun f : Fin 6 =>
  List.ofFn (fun k : Fin 36 => wNum f k)))
#eval (List.ofFn (fun f : Fin 6 =>
  List.ofFn (fun k : Fin 36 => wDen f k)))
#eval (List.ofFn (fun f : Fin 6 => beta f))
