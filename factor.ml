(* Recall that d divides n iff [n mod d = 0] *)
let factors n =
  if n < 2 then invalid_arg "factors: input must be >= 2"
  else
    let rec aux d n =
      if n = 1 then []
      else if n mod d = 0 then d :: aux d (n / d)
      else aux (d + 1) n
    in
    aux 2 n;;