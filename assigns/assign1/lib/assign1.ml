open Stdlib320
let is_perfect n =
  let rec sum_divisors acc d =
    if d = n then acc
    else if n mod d = 0 then sum_divisors (acc + d) (d + 1)
    else sum_divisors acc (d + 1)
  in
  sum_divisors 0 1 = n

let rec min_sos n =
  let rec aux m =
    if m * m > n then n
    else min (1 + min_sos (n - m * m)) (aux (m + 1))
  in
  aux 1

let num_occurs ~sub s =
  let len_sub = String.length sub in
  let len_s = String.length s in
  let rec aux i count =
    if i + len_sub > len_s then count
    else
      let count = if String.sub s i len_sub = sub then count + 1 else count in
      aux (i + 1) count
  in
  aux 0 0