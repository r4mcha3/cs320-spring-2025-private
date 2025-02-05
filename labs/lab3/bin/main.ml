let usage = "USAGE: dune exec lab3 COL_ID < TSV_FILE"

let () =
  if Array.length (Sys.argv) <> 2
  then print_endline usage
  else
    let col_id = Sys.argv.(1) in
    let table_str = Stdlib320.read () in
    let table = Lab3.table_of_string table_str in
    let col = Lab3.get_col table col_id in
    match col with
    | None -> print_endline (col_id ^ " is not a column of the input table")
    | Some col -> print_endline (String.concat "\n" col)
