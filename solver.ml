open Base

module NonTerminal = Char
module Terminal = Char
type nonterminal = NonTerminal.t
type terminal = Terminal.t

module Symbol = struct
  module T = struct
    type t = N of NonTerminal.t | T of Terminal.t
    [@@deriving compare, sexp]
  end
  include T
  include Comparator.Make(T)
end
type symbol = Symbol.t = N of NonTerminal.t | T of Terminal.t

module SymbolList = struct
  module T = struct
    type t = Symbol.t list
    [@@deriving compare, sexp]
  end
  include T
  include Comparator.Make(T)
end

type production = nonterminal * SymbolList.t

let rec compute_fixed_point fn init eq =
  let res = fn init in
  if (eq res init) then init else compute_fixed_point fn res eq

let is_t = function
  | N _ -> false
  | T _ -> true
let extract_nt = function
  | N nt -> nt
  | T _ -> assert false
let extract_name = function
  | N nt -> nt
  | T t -> t

type nonterminal_set = Set.M(NonTerminal).t [@@deriving sexp]
type terminal_set = Set.M(Terminal).t [@@deriving sexp]

type nullable_map = bool Map.M(NonTerminal).t [@@deriving sexp]
let nullable_map_equal = Map.equal Bool.equal

type nullable_dependency_map = nonterminal_set list Map.M(NonTerminal).t
                               [@@deriving sexp]

let append_nullable_dep nt (l : symbol list) (deps_map : nullable_dependency_map) =
  let nts : nonterminal_set =
    l |> List.rev_map ~f:extract_nt
      |> Set.of_list (module NonTerminal) in
  Map.add_multi deps_map ~key:nt ~data:nts

let make_nullables (prods : production list) : nullable_map =
  let rec _make_initial
    (map : nullable_map)
    (deps_map : nullable_dependency_map)
    : production list -> nullable_map * nullable_dependency_map = function
      | [] -> (map, deps_map)
      | (nt, rhs) :: tl_prods ->
          let is_rhs_nullable deps_map = function
            | [] -> (true, deps_map)
            | l -> if List.exists l ~f:is_t
                   then (false, deps_map)
                   else (false, append_nullable_dep nt l deps_map)
          in
          match Map.find map nt with
          | None | Some false ->
              let nullable, deps_map' = is_rhs_nullable deps_map rhs in
              let map' = Map.set map ~key:nt ~data:nullable in
              _make_initial map' deps_map' tl_prods
          | Some true -> _make_initial map deps_map tl_prods
  in
  let init_map, deps_map =
    _make_initial (Map.empty (module NonTerminal)) (Map.empty (module NonTerminal)) prods in
  let updater (map : nullable_map) : nullable_map =
    let is_currently_nullable nt = Map.find_exn map nt in
    let get_next_nullable ~key:nt ~data:old_nullable =
      if old_nullable then old_nullable
      else match Map.find deps_map nt with
        | None -> old_nullable
        | Some deps_list ->
            List.exists deps_list ~f:(Set.for_all ~f:is_currently_nullable)
    in
    Map.mapi map ~f:get_next_nullable
  in
  compute_fixed_point updater init_map nullable_map_equal

type ('k, 'kcomp, 'v, 'vcomp) set_map = ('k, ('v, 'vcomp) Set.t, 'kcomp) Map.t
let set_map_equal = Map.equal Set.equal

type terminal_set_map = Set.M(Terminal).t Map.M(NonTerminal).t [@@deriving sexp]
type nonterminal_set_map = Set.M(NonTerminal).t Map.M(NonTerminal).t
                           [@@deriving sexp]

let union_set_map (map : ('k, 'kcomp, 'v, 'vcomp) set_map) key set =
  let updater = function
    | None -> set
    | Some existing -> Set.union set existing in
  Map.update map key ~f:updater

let add_set_map (comparator : ('v, 'vcomp) Set.comparator)
                (map : ('k, 'kcomp, 'v, 'vcomp) set_map)
                ~key ~data =
  union_set_map map key (Set.singleton comparator data)

let ensure_set_map (comparator : ('v, 'vcomp) Set.comparator)
                   (map : ('k, 'kcomp, 'v, 'vcomp) set_map) key =
  union_set_map map key (Set.empty comparator)

(* Bubble up all dependencies for one iteration. *)
let iterative_updater (deps_map : ('k, 'kcomp, 'k, 'kcomp) set_map)
                      (map : ('k, 'kcomp, 'v, 'vcomp) set_map)
                      : ('k, 'kcomp, 'v, 'vcomp) set_map =
  let get_current = Map.find_exn map in
  let get_next ~key:nt ~data:old_set =
    match Map.find deps_map nt with
      | None -> old_set
      | Some deps ->
          let merge prev dep = Set.union prev (get_current dep) in
          Set.fold deps ~init:old_set ~f:merge
  in
  Map.mapi map ~f:get_next

let make_first_set (nullable_map : nullable_map) (prods : production list)
                   : terminal_set_map =
  let rec _make_initial
    (map : terminal_set_map)
    (deps_map : nonterminal_set_map)
    : production list -> terminal_set_map * nonterminal_set_map = function
      | [] -> (map, deps_map)
      | (nt, []) :: tl_prods ->
          let map' = ensure_set_map (module Terminal) map nt in
          _make_initial map' deps_map tl_prods
      | (nt, T rhs_t :: _) :: tl_prods ->
          let map' = add_set_map (module Terminal) map ~key:nt ~data:rhs_t in
          _make_initial map' deps_map tl_prods
      | (nt, N rhs_nt :: rhs_rest) :: tl_prods ->
          let deps_map' = add_set_map (module NonTerminal) deps_map ~key:nt ~data:rhs_nt in
          let prods' = if Map.find_exn nullable_map rhs_nt
                       then ((nt, rhs_rest) :: tl_prods)
                       else tl_prods in
          _make_initial map deps_map' prods'
  in
  let init_map, deps_map =
    _make_initial (Map.empty (module Terminal))
                  (Map.empty (module NonTerminal)) prods in
  compute_fixed_point (iterative_updater deps_map) init_map set_map_equal

let rec is_fragment_nullable (nullable_map : nullable_map) = function
  | [] -> true
  | T _ :: _ -> false
  | N nt :: rest -> Map.find_exn nullable_map nt &&
                      is_fragment_nullable nullable_map rest

let first_set_of_fragment (nullable_map : nullable_map)
                          (first_set_map : terminal_set_map)
                          (frag : symbol list) : terminal_set =
  let is_nullable = Map.find_exn nullable_map in
  let first_set_of_nt = Map.find_exn first_set_map in
  let rec _first_set_acc existing = function
    | [] -> existing
    | T t :: _ -> Set.add existing t
    | N nt :: rest ->
        let with_nt_first_set =
          Set.union existing (first_set_of_nt nt) in
        if is_nullable nt
        then _first_set_acc with_nt_first_set rest
        else with_nt_first_set in
  _first_set_acc (Set.empty (module Terminal)) frag

let make_follow_set (nullable_map : nullable_map)
                    (first_set_map : terminal_set_map)
                    (start_symbol : nonterminal)
                    (prods : production list) : terminal_set_map =
  let is_fragment_nullable = is_fragment_nullable nullable_map in
  let get_first_set = first_set_of_fragment nullable_map first_set_map in
  let rec _make_initial
    (map : terminal_set_map)
    (deps_map : nonterminal_set_map)
    : production list -> terminal_set_map * nonterminal_set_map = function
      | [] -> (map, deps_map)
      | (nt, []) :: tl_prods ->
          let map' = ensure_set_map (module Terminal) map nt in
          _make_initial map' deps_map tl_prods
      | (nt, T _ :: rhs_rest) :: tl_prods ->
          let prods' = (nt, rhs_rest) :: tl_prods in
          _make_initial map deps_map prods'
      | (nt, N rhs_nt :: rhs_rest) :: tl_prods ->
          let first_set = get_first_set rhs_rest in
          let map' = union_set_map map rhs_nt first_set in
          let deps_map' =
            if is_fragment_nullable rhs_rest
            then add_set_map (module NonTerminal) deps_map ~key:rhs_nt ~data:nt
            else deps_map in
          let prods' = (nt, rhs_rest) :: tl_prods in
          _make_initial map' deps_map' prods'
  in
  let start_map =
    Map.singleton (module NonTerminal)
      start_symbol (Set.singleton (module Terminal) '$') in
  let init_map, deps_map =
    _make_initial start_map (Map.empty (module NonTerminal)) prods in
  compute_fixed_point (iterative_updater deps_map) init_map set_map_equal

module ParsingTableEntry = struct
  module T = struct
    type t = NonTerminal.t * Terminal.t
    [@@deriving compare, sexp]
  end
  include T
  include Comparator.Make(T)
end
type parsing_table = Set.M(SymbolList).t Map.M(ParsingTableEntry).t
                     [@@deriving sexp]

let make_ll1_table (nullable_map : nullable_map)
                   (first_set_map : terminal_set_map)
                   (follow_set_map : terminal_set_map)
                   (prods : production list) : parsing_table =
  let get_first_set = first_set_of_fragment nullable_map first_set_map in
  let get_follow_set = Map.find_exn follow_set_map in
  let rec _make_table tbl = function
    | [] -> tbl
    | (nt, rhs) :: rest_prods ->
        let add_rhs_to_entries terminal_set rhs tbl =
          Set.fold terminal_set ~init:tbl
            ~f:(fun tbl t ->
              add_set_map (module SymbolList) tbl ~key:(nt, t) ~data:rhs)
        in
        let tbl' = add_rhs_to_entries (get_first_set rhs) rhs tbl in
        let tbl'' =
          if is_fragment_nullable nullable_map rhs
          then add_rhs_to_entries (get_follow_set nt) rhs tbl'
          else tbl'
        in
        _make_table tbl'' rest_prods
  in
  _make_table (Map.empty (module ParsingTableEntry)) prods

let make_rules orig_str : production list =
  let separate_same_nt (nt, rhses) =
    Sequence.of_list rhses |> Sequence.map ~f:(fun rhs -> (nt, rhs))
  in
  let classify rhs : symbol list =
    if String.equal rhs "ε" then []
    else
      String.to_list_rev rhs
        |> List.rev_map ~f:(fun ch -> if Char.equal ch (Char.lowercase ch)
                                      then T ch
                                      else N ch)
  in
  String.split orig_str ~on:'\n'
    |> Sequence.of_list
    |> Sequence.map ~f:(Nsplit.nsplit ~by:" :== ")
    |> Sequence.filter_map ~f:(function | (lhs :: rhs :: []) -> Some (lhs, rhs)
                                        | [] -> None
                                        | _ -> assert false)
    |> Sequence.map ~f:(fun (lhs, rhs) ->
         (assert (String.length lhs = 1); String.get lhs 0,
          Nsplit.nsplit rhs ~by:" | "))
    |> Sequence.concat_map ~f:separate_same_nt
    |> Sequence.map ~f:(fun (nt, rhs) -> (nt, classify rhs))
    |> Sequence.to_list
