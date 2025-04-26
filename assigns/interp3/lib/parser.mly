%{
open Utils

let mk_func ty args body =
  let body =
    match ty with
    | None -> body
    | Some ty -> Annot (body, ty)
  in
  List.fold_right
    (fun (x, ty) acc -> Fun (x, ty, acc))
    args
    body

let mk_list e es =
  List.fold_right (fun x acc -> Bop (Cons, x, acc)) es e
%}

%token EOF
%token <int> INT
%token <float> FLOAT
%token <string> VAR

%token LET REC EQ IN COLON
%token FUN MATCH WITH ALT
%token IF THEN ELSE
%token LPAREN RPAREN
%token LBRACKET RBRACKET SEMICOLON
%token TUNIT TINT TFLOAT TBOOL TLIST TOPTION
%token <string> TVAR
%token ARROW

%token TRUE FALSE
%token ADD SUB STAR DIV MOD
%token ADDF SUBF MULF DIVF POW
%token CONS LT LTE GT GTE EQ NEQ AND OR COMMA
%token SOME NONE ASSERT

%nonassoc TLIST
%nonassoc TOPTION
%right ARROW
%nonassoc COMMA
%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%right CONS
%left ADD ADDF SUB SUBF
%left STAR MULF DIV DIVF MOD
%left POW

%start <Utils.prog> prog

%%

prog:
  | ls = toplet* EOF { ls }

toplet:
  | LET rc=REC? name=VAR args=arg* ty=annot? EQ binding=expr
    { {
      is_rec = Option.is_some rc;
      name;
      binding = mk_func ty args binding;
    } }

annot:
  | COLON ty=ty { ty }

ty:
  | TUNIT { TUnit }
  | TINT { TInt }
  | TFLOAT { TFloat }
  | TBOOL { TBool }
  | TLIST ty=ty { TList ty }
  | TOPTION ty=ty { TOption ty }
  | TVAR v { TVar v }
  | LPAREN ty=ty RPAREN { ty }
  | ty1=ty ARROW ty2=ty { TFun (ty1, ty2) }
  | ty1=ty STAR ty2=ty { TPair (ty1, ty2) }

arg:
  | x=VAR { (x, None) }
  | LPAREN x=VAR ty=annot RPAREN { (x, Some ty) }

expr:
  | LET rc=REC? name=VAR args=arg* ty=annot? EQ binding=expr IN body=expr
    { Let {
        is_rec = Option.is_some rc;
        name;
        binding = mk_func ty args binding;
        body;
      }
    }
  | FUN args=arg* ARROW body=expr
    { mk_func None args body }
  | MATCH e=expr WITH cases=match_cases
    { cases e }
  | IF cond=expr THEN e1=expr ELSE e2=expr
    { If (cond, e1, e2) }
  | e=expr2 { e }

match_cases:
  | ALT PAT_SOME some_name=VAR ARROW some_case=expr ALT NONE ARROW none_case=expr
    { fun matched -> OptMatch { matched; some_name; some_case; none_case } }
  | ALT PAT_CONS hd=VAR CONS tl=VAR ARROW cons_case=expr ALT LBRACKET RBRACKET ARROW nil_case=expr
    { fun matched -> ListMatch { matched; hd_name=hd; tl_name=tl; cons_case; nil_case } }
  | ALT PAT_PAIR x=VAR COMMA y=VAR ARROW case=expr
    { fun matched -> PairMatch { matched; fst_name=x; snd_name=y; case } }

%inline PAT_SOME:
  | SOME

%inline PAT_CONS:
  | VAR

%inline PAT_PAIR:
  | VAR

expr2:
  | e1=expr2 op=bop e2=expr2
    { Bop (op, e1, e2) }
  | ASSERT e=expr3
    { Assert e }
  | SOME e=expr3
    { ESome e }
  | es=expr3+
    { List.fold_left (fun acc e -> App (acc, e)) (List.hd es) (List.tl es) }

list_item:
  | SEMICOLON e=expr { e }

expr3:
  | LPAREN RPAREN { Unit }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | NONE { ENone }
  | LBRACKET RBRACKET { Nil }
  | LBRACKET e=expr es=list_item* RBRACKET
    { mk_list e es }
  | n=INT { Int n }
  | n=FLOAT { Float n }
  | x=VAR { Var x }
  | LPAREN e=expr annot=annot? RPAREN
    {
      match annot with
      | None -> e
      | Some ty -> Annot (e, ty)
    }

%inline bop:
  | ADD { Add }
  | SUB { Sub }
  | STAR { Mul }
  | DIV { Div }
  | MOD { Mod }
  | ADDF { AddF }
  | SUBF { SubF }
  | MULF { MulF }
  | DIVF { DivF }
  | POW { PowF }
  | CONS { Cons }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQ { Eq }
  | NEQ { Neq }
  | AND { And }
  | OR { Or }
  | COMMA { Comma }