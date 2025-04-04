{
open Parser

exception Error of string
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read =
  parse
  | whitespace { read lexbuf }
  | "true"     { TRUE }
  | "false"    { FALSE }
  | "()"       { UNIT }
  | "if"       { IF }
  | "then"     { THEN }
  | "else"     { ELSE }
  | "let"      { LET }
  | "in"       { IN }
  | "fun"      { FUN }
  | "->"       { ARROW }
  | "rec"      { REC }

  (* Binary ops *)
  | "+"        { PLUS }
  | "-"        { MINUS }
  | "*"        { TIMES }
  | "/"        { DIVIDE }
  | "mod"      { MOD }
  | "<="       { LE }
  | "<"        { LT }
  | ">="       { GE }
  | ">"        { GT }
  | "="        { EQ }
  | "<>"       { NEQ }
  | "&&"       { AND }
  | "||"       { OR }

  | "("        { LPAREN }
  | ")"        { RPAREN }

  | num as n   { NUM (int_of_string n) }
  | var as v   { VAR v }

  | eof        { EOF }

  | _ as c     { raise (Error ("Unexpected character: " ^ String.make 1 c)) }
