
let hanoi n =
  let num_to_peg i =
    if i = 0
    then "left peg"
    else if i = 1
    then "middle peg"
    else if i = 2
    then "right peg"
    else assert false
  in
  let rec go i j n =
    if n = 0
    then ()
    else
      let k =
        let i, j = min i j, max i j in
        if i = 0 && j = 1
        then 2
        else if i = 0 && j = 2
        then 1
        else if i = 1 && j = 2
        then 0
        else assert false
      in
      let _ = go i k (n - 1) in
      let _ = print_endline ("move disk from " ^ num_to_peg i ^ " to " ^ num_to_peg j) in
      let _ = go k i (n - 1) in
      ()
  in go 0 2 n

let is_palindromic n =
  let rec pow10 n =
    if 0 <= n && n < 10
    then 1
    else 10 * pow10 (n / 10)
  in
  let rec reverse n =
    if 0 <= n && n < 10
    then n
    else
      let last_digit = n mod 10 in
      let back = reverse (n / 10) in
      last_digit * (pow10 n) + back
  in n > 0 && n = reverse n

let print_triples n =
  let rec loop i j k =
    let _ =
      if i * i + j * j = k * k
      then
        let i_str = string_of_int i in
        let j_str = string_of_int j in
        let k_str = string_of_int k in
        print_endline (i_str ^ " " ^ j_str ^ " " ^ k_str)
      else ()
    in
    if k <= n
    then loop i j (k + 1)
    else if j <= n
    then loop i (j + 1) (j + 1)
    else if i <= n
    then loop (i + 1) (i + 1) (i + 1)
    else ()
  in loop 1 1 1

let hourglass =
  let rec go i n =
    let indent = String.make i ' ' in
    if n = 0
    then indent ^ "*"
    else
      let line = indent ^ String.make (2 * n + 1) '*' in
      line ^ "\n"
      ^ go (i + 1) (n - 1) ^ "\n"
      ^ line
  in go 0
