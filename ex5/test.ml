type b =
  | Zero
  | One
  | Plus of b * b
  | Mult of b * b

type v =
  | Unit
  | Left of v
  | Right of v
  | Pair of v * v

type iso =
  | Zeroe
  | Zeroi
  | Swap_p
  | Assocr_p
  | Assocl_p
  | Unite
  | Uniti
  | Swap_m
  | Assocr_m
  | Assocl_m
  | Distrib_z
  | Factor_z
  | Distrib
  | Factor

type c =
  | Iso of iso
  | Id
  | Sym of c
  | Comp of c * c
  | CPlus of c * c
  | CMult of c * c

type contexts =
  | Box
  | Fst of contexts * c
  | Snd of c * contexts
  | L_m of contexts * c * v
  | R_m of c * v * contexts
  | L_p of contexts * c
  | R_p of c * contexts
  
type states =
  | Begin of c * v * contexts
  | End of c * v * contexts
      
let eval : iso -> v -> v = fun i v ->
  match (i,v) with
    (Swap_p,Left v') -> Right v'
  | (Swap_p,Right v') -> Left v'
  | (Assocl_p,Left v') -> Left (Left v')
  | (Assocl_p,Right (Left v')) -> Left (Right v')
  | (Assocl_p,Right (Right v')) -> Left (Right v')
  | (Assocr_p,Left (Left v')) -> Left v'
  | (Assocr_p,Left (Right v')) -> Right (Left v')
  | (Assocr_p,Right v') -> Right (Right v')
  | (Unite,Pair (Unit,v')) -> v'
  | (Uniti,v') -> Pair (Unit,v')
  | (Swap_m,Pair (v1,v2)) -> Pair (v2,v1)
  | (Assocl_m,Pair (v1,Pair (v2,v3))) -> Pair (Pair (v1,v2),v3)
  | (Assocr_m,Pair (Pair (v1,v2),v3)) -> Pair (v1,Pair(v2,v3))
  | (Distrib,Pair (Left v1,v3)) -> Left (Pair (v1,v3))
  | (Distrib,Pair (Right v2,v3)) -> Right (Pair (v2,v3))
  | (Factor,Left (Pair (v1,v3))) -> Pair (Left v1,v3)
  | (Factor,Right (Pair (v2,v3))) -> Pair (Right v2,v3)

let rule : states -> states = fun st ->
  match st with
  | Begin (Iso iso, v, C) -> let v' = eval iso v in
			     End (Iso iso, v', C)
  | Begin ()
