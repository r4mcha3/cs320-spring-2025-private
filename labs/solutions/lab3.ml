
let split_on_char ?(ignore_trailing=false) (c : char) (s : string) : string list =
  let len = String.length s in
  let sub curr next = String.sub s curr (next - curr) in
  let rec go curr next =
    if curr >= len
    then if ignore_trailing then [] else [""]
    else if next >= len
    then [sub curr next]
    else if s.[next] = c
    then sub curr next :: go (next + 1) (next + 1)
    else go curr (next + 1)
  in go 0 0

let table_of_string (s : string) : string list list =
  let lines = split_on_char ~ignore_trailing:true '\n' s in
  let rec go l =
    match l with
    | [] -> []
    | line :: l -> split_on_char '\t' line :: go l
  in go lines

let row_value (row : string list) (i : int) : string =
  let rec go row i =
    match row with
    | [] -> ""
    | v :: row ->
       if i < 0
       then ""
       else if i = 0
       then v
       else go row (i - 1)
  in go row i

let col_by_index (table: string list list) (i : int) : string list =
  let rec go l =
    match l with
    | [] -> []
    | row :: l -> row_value row i :: go l
  in go table

let index (v : string) (row : string list) : int option =
  let rec go acc row =
    match row with
    | [] -> None
    | x :: row ->
     if x = v
     then Some acc
     else go (acc + 1) row
  in go 0 row

let get_col (table : string list list) (row_id: string) : string list option =
  match table with
  | [] -> Some []
  | row :: table -> (
    match index row_id row with
    | None -> None
    | Some i -> Some (col_by_index table i)
  )
