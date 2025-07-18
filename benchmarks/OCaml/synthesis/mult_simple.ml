(*let rec mult x y = if y = 0 then 0 else x + mult x (y-1)*)
let rec mult x y = [%syn "x : int, y : int, mult : int -> int -> int |- int"]

let main x y =
  let s1 = mult x y in
  let s2 = mult (x + 1) y in
  assert(s1 + y = s2)
