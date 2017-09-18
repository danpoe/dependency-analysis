
%{
  open Printf
  open Parser_utils
%}

%token <string> ID
%token <int> LEVEL
%token COMMA SEMICOLON
%token LBRACKET RBRACKET
%token LPAR RPAR
%token LBRACE RBRACE
%token ASSIGNOP RETASSIGNOP
%token NULL
%token SEP
%token EOF

%start input
%type <Parser_utils.dep_prog> input

%%

input:   prog { $1 }

/* Program */

prog:    funcs SEP base { ($1, $3) }
funcs:   func { [$1] } | func funcs { $1::$2 }

/* Abstractions */

abs:     item { [$1] } | item COMMA abs { $1::$3 }
item:    LBRACKET fields RBRACKET { $2 }
fields:  field { [$1] } | field SEMICOLON fields { $1::$3 }
field:   ID COMMA LEVEL { ($1, $3) }
absext:  abs { $1 } | NULL { [] }

/* Assignment */

assign:  abs ASSIGNOP absext SEMICOLON { Assign ($1, $3) }

/* Call */

absexts: absext { [$1] } | absext SEMICOLON absexts { $1::$3 }
args:    { [] } | absexts { $1 }
call:    absext RETASSIGNOP ID LPAR args RPAR SEMICOLON { Call ($1, $3, $5) }

/* Functions */

seq:     { [] } | op seq { $1::$2 }
op:      assign { $1 } | call { $1 }
par:     LBRACKET ID COMMA LEVEL RBRACKET { ($2, $4) }
parlist: par { [$1] } | par SEMICOLON parlist { $1::$3 }
pars:    { [] } | parlist { $1 }
rets:    args { $1 }
func:    ID LPAR pars RPAR LPAR rets RPAR LBRACE seq RBRACE
         { {name=$1; pars=$3; rets=$6; ops=$9} }

/* Base */

base:    { [] } | absexts { $1 }

%%

