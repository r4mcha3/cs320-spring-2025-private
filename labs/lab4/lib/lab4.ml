
type token =
  | Lparen
  | Rparen
  | Atom of string

let is_space = function
  | ' ' | '\012' | '\n' | '\r' | '\t' -> true
  | _ -> false

let tokenize s =
  let rec go out i =
    if i >= String.length s
    then List.rev out
    else if is_space s.[i]
    then go out (i + 1)
    else if s.[i] = '('
    then go (Lparen :: out) (i + 1)
    else if s.[i] = ')'
    then go (Rparen :: out) (i + 1)
    else go' out i (i + 1)
  and go' out i j =
    if j >= String.length s
       || is_space s.[j]
       || s.[j] = '('
       || s.[j] = ')'
    then go (Atom (String.sub s i (j - i)) :: out) j
    else go' out i (j + 1)
  in go [] 0

let ntree_of_toks (_toks : token list) : string ntree = assert false

let parse s = s |> tokenize |> ntree_of_toks

let sexpr_of_ntree (_t : string ntree) : string = assert false
