
(* Abstractions *)
type field = string * int
type item = field list
type abs = item list

(* Operations *)
type op = Assign of abs * abs | Call of abs * string * abs list

(* Functions *)
type func = {name: string; pars: field list; rets: abs list; ops: op list}
type prog = func list

(* Complete dependency program *)
type dep_prog = prog * (abs list)

