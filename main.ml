
open Printf
open Parser_utils

(* ********* *)
(* Constants *)
(* ********* *)

let ht_size = 5000

(* data structure for sda *)
type ds_types = DsTypeSet | DsTypeHash
let ds_type = DsTypeSet

(* ******* *)
(* Cmdline *)
(* ******* *)

(* pretty print program *)
let c_pp = ref false
(* self check *)
let c_sc = ref false
(* stats *)
let c_stats = ref false
(* ids *)
let c_ids = ref false
(* max level, exclusive *)
let c_max_level = ref 10
(* max length *)
let c_max_len = ref 4
(* print progress info *)
let c_progress = ref false
(* compact data structures *)
let c_compact = ref false
(* maximum number of iterations *)
let c_iterations = ref (-1)
(* simple dependency analysis *)
let c_sda = ref false
(* global dependency analysis *)
let c_gda = ref false
(* dependency program file *)
let file = ref ""

let usage = "Usage: " ^ Sys.argv.(0) ^ " [<options>] <arg>"

let speclist = [
  ("-p", Arg.Set c_pp, "pretty print program");
  ("-s", Arg.Set c_sc, "self check");
  ("-stats", Arg.Set c_stats, "show stats");
  ("-ids", Arg.Set c_ids, "show ids");
  ("-max_level", Arg.Set_int c_max_level, "max level");
  ("-max_len", Arg.Set_int c_max_len, "max length");
  ("-progress", Arg.Set c_progress, "print progress info");
  ("-compact", Arg.Set c_compact, "compact data structures");
  ("-iterations", Arg.Set_int c_iterations, "maximum number of iterations");
  ("-sda", Arg.Set c_sda, "simple dependency analysis");
  ("-gda", Arg.Set c_gda, "global dependency analysis")
]

(* ************************* *)
(* Error handling and status *)
(* ************************* *)

let dep_error (msg : string) =
  print_endline ("Error: " ^ msg);
  exit 1

let dep_check (b: bool) (msg: string) =
  if not b then dep_error msg

let print_progress (msg : string) =
  if !c_progress then print_endline msg

(* ***** *)
(* Utils *)
(* ***** *)

(* slicing, indices are inclusive *)
let slice_basic l (i1 : int) (i2 : int) =
  assert (i1 >= 0);
  assert (i2 >= -1);
  if i2 < i1 then [] else begin
    assert (i1 >= 0);
    assert (i2 >= 0);
    assert (i1 <= i2);
    let n = List.length l in
    assert (n >= 1);
    assert (i1 < n);
    assert (i2 < n);
    let rec cut_prefix l (i : int) =
      if i > 0 then cut_prefix (List.tl l) (i - 1) else l
    in
    let rec cut_suffix l (i : int) =
      if i >= 0 then (List.hd l)::cut_suffix (List.tl l) (i - 1) else []
    in
    let l = cut_prefix l i1 in
    let l = cut_suffix l (i2 - i1) in
    l
  end

(* slicing, second index is exclusive *)
let slice (l : 'a list) (i1 : int option) (i2 : int option) : 'a list =
  let n = List.length l in
  if n = 0 then [] else
  begin
    match i1, i2 with
    | None, None -> l
    | Some i, None -> slice_basic l i (n - 1)
    | None, Some i -> slice_basic l 0 (i-1)
    | Some i1, Some i2 -> slice_basic l i1 (i2-1)
  end

let tup3_fst (a, _, _) = a
let tup3_snd (_, a, _) = a
let tup3_trd (_, _, a) = a

let swallow a = ()

let get (a : 'a option) =
  match a with
  | Some b -> b
  | None -> assert false

(* cartesian product of lists *)
let cross (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list =
  let cross_one a l =
    List.map (fun b -> (a, b)) l
  in
  List.flatten (List.map (fun a -> cross_one a l2) l1)

(* compact list *)
let compact (l : 'a list) (p : 'a -> 'a -> bool) : 'a list =
  let rec compact_aux l_pre l_rest : 'a list =
    if l_rest = [] then
      l_pre
    else
      let hd = List.hd l_rest in
      let l_rest' = List.tl l_rest in
      let b = (List.exists (p hd) l_pre) || (List.exists (p hd) l_rest') in
      if b then compact_aux l_pre l_rest' else compact_aux (hd::l_pre) l_rest'
  in
  compact_aux [] l

(* *********** *)
(* String sets *)
(* *********** *)

(* string set *)
module SS = Set.Make(String)

module type ISS = sig
  type t
  val create : unit -> t
  val add : string -> t -> unit
  val add_all : string list -> t -> unit
  val mem : string -> t -> bool
  val mem_any : string list -> t -> bool
  val length : t -> int
  val as_list : t -> string list
  val as_set : t -> SS.t
  val pp : t -> string
end

module IDS1 = struct
  type t = SS.t ref
  let create () = ref SS.empty
  let add id ss = ss := SS.add id !ss
  let add_all ids ss = ss := List.fold_right (fun id ss -> SS.add id ss) ids !ss
  let mem id ss = SS.mem id !ss
  let mem_any ids ss = List.exists (fun id -> SS.mem id !ss) ids
  let length ss = SS.cardinal !ss
  let as_list ss = SS.elements !ss
  let as_set ss = !ss
  let pp ss = String.concat "\n" (as_list ss)
end

module IDS2 = struct
  type t = (string, unit) Hashtbl.t
  let create() = Hashtbl.create ht_size
  let add id ht = Hashtbl.replace ht id ()
  let add_all ids ht = List.iter (fun id -> Hashtbl.replace ht id ()) ids
  let mem id ht = Hashtbl.mem ht id
  let mem_any ids ht = List.exists (fun id -> Hashtbl.mem ht id) ids
  let length ht = Hashtbl.length ht
  let as_list ht = Hashtbl.fold (fun id _ l -> id::l) ht []
  let as_set ht = Hashtbl.fold (fun id _ ss -> SS.add id ss) ht SS.empty
  let pp ht = String.concat "\n" (as_list ht)
end

(* ************************* *)
(* Global dependency program *)
(* ************************* *)

(* ---- *)
(* type *)
(* ---- *)

(* abstractions *)
type g_level = LN of int | LA | LB | LB0
type g_field = string option * g_level
type g_item = g_field list
type g_abs = g_item list

(* operations *)
type g_op = GAssign of g_abs * g_abs | GCall of g_abs * string * g_abs list

(* functions *)
type g_func =
  {name: string; pars: g_field list; rets: g_abs list; ops: g_op list}
type g_prog = g_func list

(* complete dependency program *)
type g_dep_prog = g_prog * (g_abs list)

(* -------- *)
(* misc ops *)
(* -------- *)

let is_assign = function
  | GAssign (_, _) -> true
  | _ -> false

let is_call = function
  | GCall (_, _, _) -> true
  | _ -> false

(* ------------------ *)
(* program statistics *)
(* ------------------ *)

let count_ops (p : g_prog) (pred : g_op -> bool) =
  let cnt (f : g_func) =
    let l = List.filter pred f.ops in
    List.length l
  in
  List.fold_right (fun a b -> a + b) (List.map cnt p) 0

let count_assignments (p : g_prog) = count_ops p is_assign

let count_calls (p : g_prog) = count_ops p is_call

let count_funcs (p : g_prog) =
  List.length p

(* --------------- *)
(* Pretty printing *)
(* --------------- *)

let pp_level l =
  match l with
  (* >= 0, < max_level *)
  | LN n -> string_of_int n
  (* >= max_level *)
  | LA -> "LA"
  (* > 0 *)
  | LB -> "LB"
  (* >= 0 *)
  | LB0 -> "LB0"

let pp_aid (aid : string option) =
  match aid with
  | Some id -> id
  | None -> "<t>"

let pp_par (par: g_field) : string =
  "[" ^ (pp_aid (fst par)) ^ ", " ^ (pp_level (snd par)) ^ "]"

let pp_pars (pars: g_field list) : string =
  String.concat "; " (List.map pp_par pars)

let pp_field (f: g_field) : string =
  let id = match (fst f) with | Some id -> id | None -> "<t>" in
  id ^ ", " ^ (pp_level (snd f))

let pp_item (i: g_item) : string =
  "[" ^ (String.concat "; " (List.map pp_field i)) ^ "]"

let pp_abs (a: g_abs) : string =
  if List.length a = 0 then "<0>" else String.concat ", " (List.map pp_item a)

let pp_args (al : g_abs list) : string =
  (String.concat "; " (List.map pp_abs al))

let pp_rets (al : g_abs list) : string =
  pp_args al

let pp_op (o: g_op) : string =
  match o with
  | GAssign (a1, a2)  -> "  " ^ (pp_abs a1) ^ " := " ^ (pp_abs a2) ^ ";"
  | GCall (r, id, al) -> "  " ^ (pp_abs r) ^ " r= " ^ id ^ "(" ^ (pp_args al) ^
                        ");"

let pp_ops (ops: g_op list) : string =
  String.concat "\n" (List.map pp_op ops)

let pp_func (f: g_func) : string =
  f.name ^ "(" ^ (pp_pars f.pars) ^ ")\n(" ^ (pp_rets f.rets) ^ ")\n{\n" ^
  (pp_ops f.ops) ^ "\n}\n"

let pp_prog (p : g_prog) : string =
  String.concat "\n" (List.map pp_func p)

let pp_dep_prog (p : g_dep_prog) : string =
  let s1 = pp_prog (fst p) in
  let s2 = String.concat ";\n" (List.map pp_abs (snd p)) in
  s1 ^ "\n!!!!\n\n" ^ s2

let pp_stats (p : g_dep_prog) : string =
  let na = count_assignments (fst p) in
  let nc = count_calls (fst p) in
  let nf = count_funcs (fst p) in
  "Number of assignments: " ^ (string_of_int na) ^ "\n" ^
  "Number of calls: " ^ (string_of_int nc) ^ "\n" ^
  "Number of functions: " ^ (string_of_int nf)

let pp_id_set (ss : SS.t) =
  String.concat "\n" (SS.elements ss)

(* -------------- *)
(* level handling *)
(* -------------- *)

let smaller (l1 : g_level) (l2 : g_level) : bool=
  match l1, l2 with
  (* same *)
  | LN n1, LN n2 -> n1 < n2
  | LA,    LA    -> true
  | LB,    LB    -> true
  | LB0,   LB0   -> true
  (* different *)
  | LN n, LA   -> true
  | LA,   LN n -> false
  | LN n, LB   -> true
  | LB,   LN n -> n >= 2
  | LN n, LB0  -> true
  | LB0,  LN n -> n >= 1
  | LA,   LB   -> true
  | LB,   LA   -> true
  | LA,   LB0  -> true
  | LB0,  LA   -> true
  | LB,   LB0  -> true
  | LB0,  LB   -> true

let greater (l1 : g_level) (l2 : g_level) : bool = smaller l2 l1

let smaller_or_equal l1 l2 =
  match l1, l2 with
  (* same *)
  | LN n1, LN n2 -> n1 <= n2
  | LA,    LA    -> true
  | LB,    LB    -> true
  | LB0,   LB0   -> true
  (* different *)
  | LN n, LA   -> true
  | LA,   LN n -> false
  | LN n, LB   -> true
  | LB,   LN n -> n >= 1
  | LN n, LB0  -> true
  | LB0,  LN n -> true
  | LA,   LB   -> true
  | LB,   LA   -> true
  | LA,   LB0  -> true
  | LB0,  LA   -> true
  | LB,   LB0  -> true
  | LB0,  LB   -> true

let greater_or_equal (l1 : g_level) (l2 : g_level) : bool =
  smaller_or_equal l2 l1

let rec level_add (l1 : g_level) (l2 : g_level) : g_level =
  match l1, l2 with
  (* same *)
  | LN n1, LN n2 ->
      let sum = n1 + n2 in
      if sum >= !c_max_level then LA else LN sum
  | LA, LA -> LA
  | LB, LB -> LB
  | LB0, LB0 -> LB0
  (* different *)
  | LN n, LA -> LA
  | LN n, LB -> if n >= !c_max_level-1 then LA else LB
  | LN n, LB0 -> if n >= 1 then LB else LB0
  | LA, LB -> LA
  | LA, LB0 -> LA
  | LB, LB0 -> LB
  (* switch order *)
  | _ -> level_add l2 l1

let level_sub (l1 : g_level) (l2 : g_level) : g_level =
  assert (greater_or_equal l1 l2);
  match l1, l2 with
  (* same *)
  | LN n1, LN n2 -> assert (n1 >= n2); LN (n1 - n2)
  | LA,    LA -> LB0
  | LB,    LB -> LB0
  | LB0,   LB0 -> LB0
  (* different *)
  | LN n, LA   -> assert false
  | LA,   LN n -> assert (n < !c_max_level); if n = 0 then LA else LB
  | LN n, LB   -> LB0
  | LB,   LN n -> if n = 0 then LB else LB0
  | LN n, LB0  -> LB0
  | LB0,  LN n -> LB0
  | LA,   LB   -> LB0
  | LB,   LA   -> LB0
  | LA,   LB0  -> LB0
  | LB0,  LA   -> LB0
  | LB,   LB0  -> LB0
  | LB0,  LB   -> LB0

let level_limit (l : g_level) : g_level =
  match l with
  | LN n -> if n >= !c_max_level then LA else LN n
  | _ -> l 

let levels_overlap (l1 : g_level) (l2 : g_level) : bool =
  smaller_or_equal l1 l2 && smaller_or_equal l2 l1

(* -------------------- *)
(* conversion to global *)
(* -------------------- *)

let top_field = None, LN 0

let get_level (n : int) : g_level = LN n

let field_to_global (f : field) : g_field =
  Some (fst f), LN (snd f)

let abs_to_global (a : abs) : g_abs =
  List.map (List.map field_to_global) a

let op_to_global (o : op) : g_op =
  match o with
  | Assign (a1, a2) -> GAssign (abs_to_global a1, abs_to_global a2)
  | Call (r, i, a)  -> GCall (abs_to_global r, i, List.map abs_to_global a)

let func_to_global (f : func) : g_func =
  {name = f.name;
   pars = List.map field_to_global f.pars;
   rets = List.map abs_to_global f.rets;
   ops = List.map op_to_global f.ops}

let dep_prog_to_global (dp : dep_prog) : g_dep_prog =
  let fs, st = dp in
  List.map func_to_global fs, List.map abs_to_global st

(* ------------ *)
(* limit global *)
(* ------------ *)

let field_limit (a : g_field) : g_field =
  if a = top_field then a else
  (fst a, level_limit (snd a))

let item_limit (a : g_item) : g_item =
  let a = List.map field_limit a in
  let n = List.length a in
  if n > !c_max_len then
    (slice a None (Some (!c_max_len-1))) @ [top_field]
  else a

let abs_limit (a : g_abs) : g_abs =
  List.map item_limit a

let op_limit (o : g_op) : g_op =
  match o with
  | GAssign (a1, a2) -> GAssign (abs_limit a1, abs_limit a2)
  | GCall (r, i, a)  -> GCall (abs_limit r, i, List.map abs_limit a)

let func_limit (f : g_func) : g_func =
  {name = f.name;
   pars = List.map field_limit f.pars;
   rets = List.map abs_limit f.rets;
   ops = List.map op_limit f.ops}

let dep_prog_limit (dp : g_dep_prog) : g_dep_prog =
  let fs, st = dp in
  List.map func_limit fs, List.map abs_limit st

let item_limited (a : g_item) : bool =
  let a' = item_limit a in
  a = a'

(* ----------------------- *)
(* program well-formedness *)
(* ----------------------- *)

let well_formed_par (f : g_field) : bool =
  (f <> top_field) &&
  (String.length (get (fst f))) > 0 &&
  ((snd f) = LN 1)

let well_formed_item (i : g_item) : bool =
  let n = List.length i in
  if n <= 1 then true else begin
    let i' = slice i None (Some (n-1)) in
    List.for_all (function | (_, LN j) -> j > 0 | _ -> true) i'
  end

let well_formed_op (o: g_op) (p: g_prog) : bool =
  match o with
  | GAssign (a1, a2) ->
      List.length a1 > 0 &&
      List.for_all well_formed_item a1 &&
      List.for_all well_formed_item a2
  | GCall (r, id, a) ->
      let funcs = List.map (fun f -> f.name) p in
      List.mem id funcs &&
      List.for_all well_formed_item r &&
      List.for_all (List.for_all well_formed_item) a

let well_formed_func (f : g_func) (p : g_prog) : bool =
  (* all operations well-formed *)
  let wf = List.for_all (fun o -> well_formed_op o p) f.ops in
  (* name is set *)
  let wf = wf && (String.length f.name) > 0 in
  (* all parameters well-formed *)
  let wf = wf && (List.for_all well_formed_par f.pars) in
  wf

let well_formed (dp : g_dep_prog) : unit =
  let p, st = dp in
  assert (List.length p > 0);
  assert (List.exists (fun f -> f.name = "main") p);
  assert (List.for_all (fun f -> well_formed_func f p) p);
  (* functions exist only once *)
  let ids = List.map (fun f -> f.name) p in
  let ss = SS.empty in
  let ss = List.fold_right SS.add ids ss in
  assert (SS.cardinal ss = List.length ids);
  (* starting abs are well-formed *)
  assert (List.for_all (List.for_all well_formed_item) st)

(* ************************** *)
(* Simple dependency analysis *)
(* ************************** *)

(* ----- *)
(* Basic *)
(* ----- *)

let identifiers (a : g_abs) : string list =
  List.map (fun l -> get (fst (List.hd l))) a

let identifiers2 (al : g_abs list) : string list =
  List.flatten (List.map identifiers al)

let insert (ss : SS.t) (sl : string list) : SS.t =
  List.fold_right SS.add sl ss

let get_func (p : g_prog) (id : string) : g_func =
  List.find (fun f -> f.name = id) p

let wrap (l : 'a list) : 'a list list =
  List.map (fun el -> [el]) l

let rec multiply (el : 'a) (n : int) : 'a list =
  assert (n >= 0);
  if n > 0 then el::(multiply el (n-1)) else []

(* ----------- *)
(* Compute ids *)
(* ----------- *)

module SDA (IDS : ISS) = struct
  let update_assign (a : g_abs * g_abs) (ds : IDS.t) : bool =
    let ids = (identifiers (fst a)) @ (identifiers (snd a)) in
    let b = IDS.mem_any ids ds in
    let n1 = IDS.length ds in
    if b then IDS.add_all ids ds;
    let n2 = IDS.length ds in
    n2 > n1

  let update_call (c : g_abs * string * g_abs list) (p: g_prog) (ds : IDS.t) :
    bool =
    let lhs, id, args = c in
    (* called function *)
    let f = get_func p id in
    let (rets : g_abs list) = f.rets in
    let (pars : g_abs list) = wrap (wrap f.pars) in
    (* ignore call when number of args does not match numbers of pars *)
    if (List.length args <> List.length pars) then false else
    begin
      assert ((List.length args) = (List.length pars));
      (* handle arguments like assignments *)
      let n1 = IDS.length ds in
      let pairs = List.combine pars args in
      List.iter (fun p -> swallow (update_assign p ds)) pairs;
      (* handle returns like assignments *)
      let lhss = multiply lhs (List.length rets) in
      assert (List.length lhss = List.length rets);
      let pairs = List.combine lhss rets in
      List.iter (fun p -> swallow (update_assign p ds)) pairs;
      let n2 = IDS.length ds in
      n2 > n1
    end

  let update_function (f : g_func) (p : g_prog) (ds : IDS.t) : bool =
    let update_op (o : g_op) (ds : IDS.t) : bool =
      match o with
      | GAssign (a1, a2) -> update_assign (a1, a2) ds
      | GCall (r, s, al) -> update_call (r, s, al) p ds
    in
    let n1 = IDS.length ds in
    List.iter (fun o -> swallow (update_op o ds)) f.ops;
    let n2 = IDS.length ds in
    n2 > n1

  let sda_fixpoint (p : g_prog) (ids : string list) : int * SS.t =
    let rec sda_fixpoint_aux (p : g_prog) (ds : IDS.t) (n : int) : int =
      print_progress ("sda fixpoint iteration: " ^ (string_of_int n));
      let n1 = IDS.length ds in
      (* iterate over functions once and update set *)
      List.iter (fun f -> swallow (update_function f p ds)) p;
      let n2 = IDS.length ds in
      print_progress ("id set size: " ^ (string_of_int n2));
      if n2 > n1 then sda_fixpoint_aux p ds (n+1) else n
    in
    let ds = IDS.create () in
    IDS.add_all ids ds;
    let its = sda_fixpoint_aux p ds 1 in
    let ss = IDS.as_set ds in
    its, ss
end

(* --------- *)
(* Filtering *)
(* --------- *)

(* Filter assignments *)

let filter_assignments (p: g_prog) (ss : SS.t) : g_prog =
  let pred_op (o : g_op) (ss : SS.t) : bool =
    match o with
    | GAssign (a1, a2) -> List.exists (fun id -> SS.mem id ss) (identifiers a1)
    | _ -> true
  in
  let filter_assignments_aux (f : g_func) (ss : SS.t) : g_func =
    let ops = List.filter (fun op -> pred_op op ss) f.ops in
    { f with ops = ops }
  in
  List.map (fun f -> filter_assignments_aux f ss) p

(* Filter calls *)

let rec ids_fixpoint (p : g_prog) (ids : SS.t) : SS.t =
  let calls_id (f : g_func) (id : string) : bool =
    List.exists (function | GCall (r, i, a) -> i = id | _ -> false) f.ops
  in
  let calls_any_id (f : g_func) (ids : SS.t) : bool =
    SS.exists (calls_id f) ids
  in
  let update_ids (f : g_func) (ids : SS.t) : SS.t =
    if calls_any_id f ids then SS.add f.name ids else ids 
  in
  let n1 = SS.cardinal ids in
  let (ids : SS.t) = List.fold_right update_ids p ids in
  let n2 = SS.cardinal ids in
  if n2 > n1 then ids_fixpoint p ids else ids

let func_ids (p : g_prog) (p' : g_prog) : SS.t =
  assert (count_assignments p' <= count_assignments p);
  let has_assign (f : g_func) =
    List.exists is_assign f.ops
  in
  let (start_funcs : g_func list) = List.filter has_assign p' in
  let (start_ids : string list) = List.map (fun f -> f.name) start_funcs in
  let start_set = SS.empty in
  let start_set = List.fold_right SS.add start_ids start_set in
  ids_fixpoint p' start_set

let filter_calls (p : g_prog) (p' : g_prog) =
  assert (count_assignments p' <= count_assignments p);
  let pred_op (o : g_op) (ids : SS.t) =
    match o with
    | GCall (r, i, a) -> SS.mem i ids
    | _ -> true
  in
  let filter_calls_aux (f : g_func) (ids : SS.t) : g_func =
    let ops = List.filter (fun o -> pred_op o ids) f.ops in
    { f with ops = ops }
  in
  let ids = func_ids p p' in
  List.map (fun f -> filter_calls_aux f ids) p'

(* Filter functions *)

let filter_funcs (p : g_prog) : g_prog =
  List.filter (fun f -> (List.length f.ops) > 0) p

(* ----------- *)
(* Entry point *)
(* ----------- *)

let sda (dp : g_dep_prog) : int * g_dep_prog =
  let (p : g_prog) = fst dp in
  let (st : g_abs list) = snd dp in
  (* starting symbols *)
  let (start : string list) = identifiers2 st in
  (* compute ids via fixpoint *)
  let n, (ss : SS.t) =
    match ds_type with
    | DsTypeSet  -> let module SDA = SDA(IDS1) in SDA.sda_fixpoint p start 
    | DsTypeHash -> let module SDA = SDA(IDS2) in SDA.sda_fixpoint p start
  in
  if !c_ids then begin
    print_endline "*** Ids:";
    print_endline ("Number of ids: " ^ string_of_int (SS.cardinal ss));
    print_endline "List of ids:";
    SS.iter print_endline ss
  end;
  (* filter assignments *)
  let p' = filter_assignments p ss in
  assert (count_assignments p' <= count_assignments p);
  (* filter calls *)
  let p' = filter_calls p p' in
  assert (count_calls p' <= count_calls p);
  (* filter functions *)
  let p' = filter_funcs p' in
  assert (count_funcs p' <= count_funcs p);
  (* new dependency program *)
  n, (p', st)

(* ************************** *)
(* Global dependency analysis *)
(* ************************** *)

(* ----- *)
(* basic *)
(* ----- *)

(* identifier of first field *)
let get_head (item : g_item) : string =
  assert (List.length item > 0);
  let hd = List.hd item in
  assert (hd <> top_field);
  let id = fst hd in
  match id with
  | Some a -> a
  | None -> assert false

(* -------------------- *)
(* items data structure *)
(* -------------------- *)

(* item set *)
module IS = Set.Make(
  struct
    type t = g_item
    let compare = compare
  end)

(* item data structure *)
module IDS3 = struct

  (* hash table, sum of value entries *)
  type t = (string, IS.t) Hashtbl.t * int ref

  let create () = Hashtbl.create ht_size, ref 0

  let add (item : g_item) (ds : t) : unit =
    let id = get_head item in
    let ht, n = ds in
    let cur = try Hashtbl.find ht id
              with Not_found -> IS.empty in
    let n1 = IS.cardinal cur in
    let cur = IS.add item cur in
    let n2 = IS.cardinal cur in
    Hashtbl.replace ht id cur;
    n := !n + (n2 - n1)

  let add_all (abs : g_abs) (ds : t) : unit =
    List.iter (fun item -> add item ds) abs

  let add_if (item : g_item) (f : g_item -> g_item -> bool) (ds : t) : unit =
    let id = get_head item in
    let ht, n = ds in
    let cur = try Hashtbl.find ht id
              with Not_found -> IS.empty in
    let b = IS.exists (f item) cur in
    if not b then begin
      let cur = IS.add item cur in
      Hashtbl.replace ht id cur;
      n := !n + 1
    end

  let add_if_all (abs : g_abs) (f : g_item -> g_item -> bool) (ds : t) : unit =
    List.iter (fun item -> add_if item f ds) abs

  let get (id : string) (ds : t) : IS.t =
    assert (String.length id > 0);
    try Hashtbl.find (fst ds) id
    with Not_found -> IS.empty

  let get2 (item : g_item) (ds : t) : IS.t =
    assert (List.length item > 0);
    let id = get_head item in
    get id ds

  let to_set ds : IS.t =
    Hashtbl.fold (fun id v ss -> IS.union v ss) (fst ds) IS.empty

  let to_list ds : g_item list =
    Hashtbl.fold (fun id v l -> (IS.elements v) @ l) (fst ds) []

  let pp ds = String.concat "\n" (List.map pp_item (to_list ds))

  let length ds = !(snd ds)

  let compact (p: g_item -> g_item -> bool) (ds : t) : unit =
    let ht, n = ds in
    let f k v =
      let n1 = IS.cardinal v in
      let vl = IS.elements v in
      let vl = compact vl p in
      let is = List.fold_right IS.add vl IS.empty in
      let n2 = IS.cardinal is in
      n := !n - (n1 - n2);
      Some is
    in
    Hashtbl.filter_map_inplace f ht

  let check ds =
    assert (length ds = List.length (to_list ds));
    assert (length ds = IS.cardinal (to_set ds));

end

(* ------------ *)
(* gda fixpoint *)
(* ------------ *)

(* dependency handling *)

let fields_overlap (a : g_field) (b : g_field) : bool =
  let id1, l1 = a in
  let id2, l2 = b in
  a = top_field || b = top_field || (id1 = id2 && levels_overlap l1 l2)

(* field may not be a dereference *)
let no_deref (a : g_field) : bool =
  let id, l = a in
  a = top_field || smaller_or_equal l (LN 1)

let field_can_affect (a : g_field) (b : g_field) : bool =
  let id1, l1 = a in
  let id2, l2 = b in
  a = top_field || b = top_field || (id1 = id2 && smaller_or_equal l1 l2)

let can_affect (a : g_item) (b : g_item) : bool =
  let n1 = List.length a in
  let n2 = List.length b in
  assert (n1 > 0);
  assert (n2 > 0);
  if n1 <= n2 then begin
    let i = n1-1 in (* last index *)
    let a' = slice a None (Some i) in
    let b' = slice b None (Some i) in
    (List.for_all2 fields_overlap a' b') &&
    field_can_affect (List.nth a i) (List.nth b i)
  end else begin
    assert (n1 > n2);
    let a' = slice a None (Some n2) in
    let b' = slice b None (Some n2) in
    (List.for_all2 fields_overlap a' b') &&
    (List.for_all no_deref (slice a (Some n2) None))
  end

let field_takes_address (a : g_field) (b : g_field) : bool =
  let id1, l1 = a in
  let id2, l2 = b in
  a = top_field || b = top_field || (id1 = id2 && smaller l1 l2)

let takes_address (a : g_item) (b : g_item) : bool =
  let n1 = List.length a in
  let n2 = List.length b in
  assert (n1 > 0);
  assert (n2 > 0);
  if n1 <= n2 then begin
    let i = n1-1 in (* last index *)
    let a' = slice a None (Some i) in
    let b' = slice b None (Some i) in
    (List.for_all2 fields_overlap a' b') &&
    field_takes_address (List.nth a i) (List.nth b i)
  end else begin
    assert (n1 > n2);
    let a' = slice a None (Some n2) in
    let b' = slice b None (Some n2) in
    let c1 = List.for_all2 fields_overlap a' b' in
    let c2 = List.for_all no_deref (slice a (Some n2) (Some (n1-1))) in
    let f = List.nth a (n1-1) in
    let c3 = f = top_field || smaller_or_equal (snd f) (LN 0) in
    c1 && c2 && c3
  end

(* compute a - b *)
let subtract (a : g_item) (b : g_item) : g_level * g_item =
  assert (can_affect b a);
  let n1 = List.length a in
  let n2 = List.length b in
  if n1 <= n2 then begin
    if (List.nth a (n1-1)) = top_field then
      (LB0, [top_field])
    else if (List.nth b (n1-1)) = top_field then begin
      assert (List.nth a (n1-1) <> top_field);
      assert (n1 = n2);
      (snd (List.nth a (n1-1)), [])
    end else begin
      assert (List.nth a (n1-1) <> top_field);
      assert (List.nth b (n1-1) <> top_field);
      let l1 = snd (List.nth a (n1-1)) in
      let l2 = snd (List.nth b (n1-1)) in
      (level_sub l1 l2, [])
    end
  end else begin
    assert (n1 > n2);
    if (List.nth b (n2-1)) <> top_field then begin
      let l1 = snd (List.nth a (n2-1)) in
      let l2 = snd (List.nth b (n2-1)) in
      (level_sub l1 l2, slice a (Some n2) None)
    end else
      (LB0, [top_field])
  end

let add (a : g_item) (l : g_level) (b : g_item) : g_item =
  let n = List.length a in
  assert (n >= 1);
  if (List.nth a (n-1)) = top_field then
    a
  else
    let a' = slice a None (Some (n-1)) in
    let id = fst (List.nth a (n-1)) in
    let l' = snd (List.nth a (n-1)) in
    let l' = level_add l' l in
    let c = a' @ [id, l'] @ b in
    item_limit c

let compact_ds ds : bool =
  if !c_compact then begin
    let n1 = IDS3.length ds in
    print_progress ("item ds size (before compaction): " ^
      (string_of_int n1));
    IDS3.compact can_affect ds;
    let n2 = IDS3.length ds in
    n1 <> n2
  end else false

let handle (a : g_abs) (b : g_abs) (ds : IDS3.t)
           (f : g_item -> g_item -> bool) : bool =
  let handle_aux (i : g_item) (ds : IDS3.t) (f : g_item -> g_item -> bool) :
    (g_level * g_item) list =
    let is = IDS3.get2 i ds in
    let il = IS.elements is in
    let il = List.filter (f i) il in
    List.map (fun a -> subtract a i) il
  in
  let diffs = List.flatten (List.map (fun a -> handle_aux a ds f) a) in
  if List.length diffs = 0 then false else begin
    let pairs = cross b diffs in
    let items = List.map (fun (b, (n, a)) -> add b n a) pairs in
    let n1 = IDS3.length ds in
    IDS3.add_if_all items can_affect ds;
    IDS3.add_if_all b can_affect ds;
    let n2 = IDS3.length ds in
    n2 > n1
  end

(* handle operations *)

let update_assign_global (a : g_abs * g_abs) (ds : IDS3.t) : bool =
  let a, b = a in
  let b1 = handle a b ds can_affect in
  let b2 = handle b a ds takes_address in
  b1 || b2

let update_call_global (c : g_abs * string * g_abs list) (p: g_prog)
                       (ds : IDS3.t) : bool =
  let lhs, id, args = c in
  (* called function *)
  let f = get_func p id in
  let (rets : g_abs list) = f.rets in
  let (pars : g_abs list) = wrap (wrap f.pars) in
  (* ignore call when number of args does not match numbers of pars *)
  if (List.length args <> List.length pars) then false else
  begin
    assert ((List.length args) = (List.length pars));
    (* handle arguments like assignments *)
    let n1 = IDS3.length ds in
    let pairs = List.combine pars args in
    List.iter (fun p -> swallow (update_assign_global p ds)) pairs;
    (* handle returns like assignments *)
    let lhss = multiply lhs (List.length rets) in
    assert (List.length lhss = List.length rets);
    let pairs = List.combine lhss rets in
    List.iter (fun p -> swallow (update_assign_global p ds)) pairs;
    let n2 = IDS3.length ds in
    n2 > n1
  end

let update_function_global (f : g_func) (p : g_prog) (ds : IDS3.t) : bool =
  let update_op (o : g_op) (ds : IDS3.t) : bool =
    match o with
    | GAssign (a1, a2) -> update_assign_global (a1, a2) ds
    | GCall (r, s, al) -> update_call_global (r, s, al) p ds
  in
  let n1 = IDS3.length ds in
  List.iter (fun o -> swallow (update_op o ds)) f.ops;
  let n2 = IDS3.length ds in
  n2 > n1

(* compute item set via fixpoint *)

let gda_fixpoint (p : g_prog) (ds : IDS3.t) =
  let rec gda_fixpoint_aux (p : g_prog) (ds : IDS3.t) (n : int) : int =
    print_progress ("gda fixpoint iteration: " ^ (string_of_int n));
    let n1 = IDS3.length ds in
    (* iterate over functions once and update set *)
    List.iter (fun f -> swallow (update_function_global f p ds)) p;
    let b = compact_ds ds in
    let n2 = IDS3.length ds in
    print_progress ("item ds size: " ^ (string_of_int n1));
    if (b || n2 > n1) && (!c_iterations = -1 || n < !c_iterations) then
      gda_fixpoint_aux p ds (n+1)
    else
      n
  in
  gda_fixpoint_aux p ds 1

(* --------- *)
(* filtering *)
(* --------- *)

(* filter assignments *)

let filter_assignments_global (p: g_prog) (ds : IDS3.t) : g_prog =
  let pred_op (o : g_op) (ds : IDS3.t) : bool =
    match o with
    | GAssign (a1, _) ->
      let f (i : g_item) (ds : IDS3.t) =
        let (is : IS.t) = IDS3.get2 i ds in
        IS.exists (can_affect i) is
      in
      List.exists (fun i -> f i ds) a1
    | _ -> true
  in
  let filter_assignments_aux (f : g_func) (ds : IDS3.t) : g_func =
    let ops = List.filter (fun op -> pred_op op ds) f.ops in
    { f with ops = ops }
  in
  List.map (fun f -> filter_assignments_aux f ds) p

(* ----------- *)
(* entry point *)
(* ----------- *)

let gda (dp : g_dep_prog) =
  print_progress "global dependency analysis";
  let (p : g_prog) = fst dp in
  let (st : g_abs list) = snd dp in
  (* starting symbols *)
  let ds = IDS3.create () in
  List.iter (fun abs -> IDS3.add_all abs ds) st;
  (* do fixpoint *)
  print_progress "starting fixpoint";
  let n = gda_fixpoint p ds in
  if !c_ids then begin
    print_endline "*** Ids:";
    print_endline ("Number of ids: " ^ string_of_int !(snd ds));
    print_endline "List of ids:";
    print_endline (IDS3.pp ds)
  end;
  print_progress "starting filtering";
  (* filter assignments *)
  let p' = filter_assignments_global p ds in
  assert (count_assignments p' <= count_assignments p);
  (* filter calls *)
  let p' = filter_calls p p' in
  (* filter functions *)
  let p' = filter_funcs p' in
  assert (count_funcs p' <= count_funcs p);
  (* new dependency program *)
  n, (p', st) 

(* **** *)
(* Main *)
(* **** *)

let self_check (dp: g_dep_prog) =
  let s = pp_dep_prog dp in
  let lexbuf = Lexing.from_string s in
  try 
    let (dp' : dep_prog) = Parser.input Lexer.token lexbuf in
    let (dp' : g_dep_prog) = dep_prog_to_global dp' in
    assert (dp = dp')
  with Parsing.Parse_error -> printf "Self check parse error\n"; exit 1

let doit (dp: g_dep_prog) =
  well_formed dp;
  dep_check (!c_max_level >= 0) "max level < 0";
  dep_check (!c_max_len >= 1) "max length < 1";
  dep_check (not (!c_sda && !c_gda)) "both sda and gda specified";
  if !c_stats && not !c_sda && not !c_gda then begin
    print_endline "*** Statistics:";
    print_endline (pp_stats dp);
  end;
  if !c_pp && not !c_sda && not !c_gda then begin
    print_endline (pp_dep_prog dp);
    exit 0
  end;
  if !c_sc then begin
    self_check dp;
    exit 0
  end;
  if !c_sda then begin
    let n, dp = sda dp in
    if !c_stats then begin
      print_endline "*** Statistics:";
      print_endline ("Id iterations: " ^ (string_of_int n));
      print_endline (pp_stats dp);
    end;
    if !c_pp then begin
      print_endline "*** Program:";
      print_endline (pp_dep_prog dp);
    end;
    exit 0
  end;
  if !c_gda then begin
    let dp = dep_prog_limit dp in
    let n, dp = gda dp in
    if !c_stats then begin
      print_endline "*** Statistics:";
      print_endline ("Id iterations: " ^ (string_of_int n));
      print_endline (pp_stats dp);
    end;
    if !c_pp then begin
      print_endline "*** Program:";
      print_endline (pp_dep_prog dp);
    end;
    exit 0
  end;
  ()

let main () =
  Arg.parse speclist (fun arg -> file := arg) usage;
  let in_chan = open_in !file in
  let lexbuf = Lexing.from_channel in_chan in
  try
    let (dp : dep_prog) = Parser.input Lexer.token lexbuf in
    let (dp : g_dep_prog) = dep_prog_to_global dp in
    close_in in_chan;
    doit dp
  with Parsing.Parse_error -> print_endline "Parse error"; exit 1

let () =
  main ()

