
{
  open Parser
}

let digit = ['0'-'9']
let symbol = ['a'-'z' 'A'-'Z' '0'-'9' ':' '_' '#' '$' '\'']

rule token = parse
  | ' '* '#' (symbol | ' ' | ',')* '\n' { token lexbuf }
  | [' ' '\t' '\n'] { token lexbuf }
  | ',' { COMMA }
  | ';' { SEMICOLON }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '(' { LPAR }
  | ')' { RPAR }
  | ":=" { ASSIGNOP }
  | "r=" { RETASSIGNOP }
  | "<0>" { NULL }
  | "!!!!" { SEP }
  | digit+ as num { LEVEL (int_of_string num) }
  | symbol+ as sym { ID (sym) }
  | eof { EOF }

