%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token TRUE FALSE UNIT
%token IF THEN ELSE
%token LET IN
%token FUN ARROW
%token PLUS MINUS TIMES DIVIDE MOD
%token LT LE GT GE EQ NEQ
%token AND OR
%token LPAREN RPAREN
%token EOF
%token REC

%start <Utils.prog> prog
%type <expr> expr

%left OR
%left AND
%nonassoc LT LE GT GE EQ NEQ
%left PLUS MINUS
%left TIMES DIVIDE MOD

%%

prog:
  | expr EOF { $1 }

expr:
  | IF expr THEN expr ELSE expr     { If ($2, $4, $6) }
  | LET VAR EQ expr IN expr         { Let ($2, $4, $6) }
  | FUN VAR ARROW expr              { Fun ($2, $4) }
  | expr1                           { $1 }

expr1:
  | expr1 OR expr1                  { Bop (Or, $1, $3) }
  | expr1 AND expr1                 { Bop (And, $1, $3) }
  | expr1 LT expr1                  { Bop (Lt, $1, $3) }
  | expr1 LE expr1                  { Bop (Lte, $1, $3) }
  | expr1 GT expr1                  { Bop (Gt, $1, $3) }
  | expr1 GE expr1                  { Bop (Gte, $1, $3) }
  | expr1 EQ expr1                  { Bop (Eq, $1, $3) }
  | expr1 NEQ expr1                 { Bop (Neq, $1, $3) }
  | expr1 PLUS expr1                { Bop (Add, $1, $3) }
  | expr1 MINUS expr1               { Bop (Sub, $1, $3) }
  | expr1 TIMES expr1               { Bop (Mul, $1, $3) }
  | expr1 DIVIDE expr1              { Bop (Div, $1, $3) }
  | expr1 MOD expr1                 { Bop (Mod, $1, $3) }
  | expr1 expr2                     { App ($1, $2) }
  | expr2                           { $1 }

expr2:
  | NUM                             { Num $1 }
  | VAR                             { Var $1 }
  | TRUE                            { True }
  | FALSE                           { False }
  | UNIT                            { Unit }
  | LPAREN expr RPAREN              { $2 }
