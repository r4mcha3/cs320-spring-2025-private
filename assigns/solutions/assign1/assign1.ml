let is_perfect (n : int) : bool =
  let sum_of_divisors : int =
    let rec loop (acc : int) (i : int) : int =
      if i = n
      then acc
      else if n mod i = 0
      then loop (acc + i) (i + 1)
      else loop acc (i + 1)
    in loop 0 1
  in n = sum_of_divisors

let int_sqrt (n : int) : int =
  let rec loop (i : int) : int =
    if i * i >= n
    then i
    else loop (i + 1)
  in loop 0

let is_perfect_square (n : int) : bool =
  let s = int_sqrt n in
  s * s = n

let rec min_sos (n : int) : int =
  let rec loop (curr : int) (i : int) : int =
    if i > n / 2
    then curr
    else
      let next = min_sos i + min_sos (n - i) in
      let curr = if next < curr then next else curr in
      loop curr (i + 1)
  in
  if n = 0
  then 0
  else if is_perfect_square n
  then 1
  else loop n 1

let num_occurs ~sub:(sub : string) (s : string) : int =
  let sub_len = String.length sub in
  let last_index = String.length s - sub_len in
  let rec loop (acc : int) (i : int) : int =
    if i > last_index
    then acc
    else
      let incr =
        if sub = String.sub s i sub_len
        then 1
        else 0
      in loop (acc + incr) (i + 1)
  in loop 0 0
