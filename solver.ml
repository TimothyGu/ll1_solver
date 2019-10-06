type nonterminal = char
type terminal = char
type symbol = N of nonterminal | T of terminal
type production = nonterminal * (symbol list)

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

module NonTerminalKey =
  struct
    type t = nonterminal
    let compare = compare
  end
module NonTerminalMap = Map.Make(NonTerminalKey)
module NonTerminalSet = Set.Make(NonTerminalKey)

module TerminalKey =
  struct
    type t = terminal
    let compare = compare
  end
module TerminalSet = Set.Make(TerminalKey)

type nonterminal_set = NonTerminalSet.t
type terminal_set = TerminalSet.t

type nullable_map = bool NonTerminalMap.t
let nullable_map_equal : nullable_map -> nullable_map -> bool =
  NonTerminalMap.equal (=)

type nullable_dependency_map = nonterminal_set list NonTerminalMap.t

let append_nullable_dep nt (l : symbol list) (deps_map : nullable_dependency_map) =
  let nts : nonterminal_set =
    l |> List.map extract_nt
      |> NonTerminalSet.of_list in
  let updater = function
    | None -> Some [nts]
    | Some existing -> Some (nts :: existing)
  in
  NonTerminalMap.update nt updater deps_map

let make_nullables (prods : production list) : nullable_map =
  let rec _make_initial
    (map : nullable_map)
    (deps_map : nullable_dependency_map)
    : production list -> nullable_map * nullable_dependency_map = function
      | [] -> (map, deps_map)
      | (nt, rhs) :: tl_prods ->
          let is_rhs_nullable deps_map = function
            | [] -> (true, deps_map)
            | l -> if List.exists is_t l
                   then (false, deps_map)
                   else (false, append_nullable_dep nt l deps_map)
          in
          match NonTerminalMap.find_opt nt map with
          | None | Some false ->
              let nullable, deps_map' = is_rhs_nullable deps_map rhs in
              let map' = NonTerminalMap.add nt nullable map in
              _make_initial map' deps_map' tl_prods
          | Some true -> _make_initial map deps_map tl_prods
  in
  let init_map, deps_map =
    _make_initial NonTerminalMap.empty NonTerminalMap.empty prods in
  let updater (map : nullable_map) : nullable_map =
    let is_currently_nullable nt = NonTerminalMap.find nt map in
    let get_next_nullable nt old_nullable =
      if old_nullable then old_nullable
      else match NonTerminalMap.find_opt nt deps_map with
        | None -> old_nullable
        | Some deps_list ->
            List.exists (NonTerminalSet.for_all is_currently_nullable) deps_list
    in
    NonTerminalMap.mapi get_next_nullable map
  in
  compute_fixed_point updater init_map nullable_map_equal

type terminal_set_map = terminal_set NonTerminalMap.t
let terminal_set_map_equal : terminal_set_map -> terminal_set_map -> bool =
  NonTerminalMap.equal TerminalSet.equal

type nonterminal_set_map = nonterminal_set NonTerminalMap.t

let union_terminal_set nt (set : terminal_set) (map : terminal_set_map) =
  let updater = function
    | None -> Some set
    | Some existing -> Some (TerminalSet.union set existing) in
  NonTerminalMap.update nt updater map

let append_terminal nt t (map : terminal_set_map) =
  union_terminal_set nt (TerminalSet.singleton t) map

let ensure_terminal_set nt (map : terminal_set_map) =
  union_terminal_set nt TerminalSet.empty map

let append_nonterminal nt dep (deps_map : nonterminal_set_map) =
  let updater = function
    | None -> Some (NonTerminalSet.singleton dep)
    | Some existing -> Some (NonTerminalSet.add dep existing) in
  NonTerminalMap.update nt updater deps_map

let make_first_set (nullable_map : nullable_map) (prods : production list)
                   : terminal_set_map =
  let rec _make_initial
    (map : terminal_set_map)
    (deps_map : nonterminal_set_map)
    : production list -> terminal_set_map * nonterminal_set_map = function
      | [] -> (map, deps_map)
      | (nt, []) :: tl_prods ->
          let map' = ensure_terminal_set nt map in
          _make_initial map' deps_map tl_prods
      | (nt, T rhs_t :: _) :: tl_prods ->
          let map' = append_terminal nt rhs_t map in
          _make_initial map' deps_map tl_prods
      | (nt, N rhs_nt :: rhs_rest) :: tl_prods ->
          let deps_map' = append_nonterminal nt rhs_nt deps_map in
          let next_prods = if NonTerminalMap.find rhs_nt nullable_map
                           then ((nt, rhs_rest) :: tl_prods)
                           else tl_prods in
          _make_initial map deps_map' next_prods
  in
  let init_map, deps_map =
    _make_initial NonTerminalMap.empty NonTerminalMap.empty prods in
  let updater (map : terminal_set_map) : terminal_set_map =
    let get_current_first_set nt = NonTerminalMap.find nt map in
    let get_next_first_set nt old_first_set =
      match NonTerminalMap.find_opt nt deps_map with
        | None -> old_first_set
        | Some deps ->
            let merge_dep_first_set dep prev =
              TerminalSet.union (get_current_first_set dep) prev in
            NonTerminalSet.fold merge_dep_first_set deps old_first_set
    in
    NonTerminalMap.mapi get_next_first_set map
  in
  compute_fixed_point updater init_map terminal_set_map_equal

let rec is_fragment_nullable (nullable_map : nullable_map) = function
  | [] -> true
  | T _ :: _ -> false
  | N nt :: rest -> NonTerminalMap.find nt nullable_map &&
                     is_fragment_nullable nullable_map rest

let first_set_of_fragment (nullable_map : nullable_map)
                          (first_set_map : terminal_set_map)
                          (frag : symbol list) : terminal_set =
  let is_nullable nt = NonTerminalMap.find nt nullable_map in
  let first_set_of_nt nt = NonTerminalMap.find nt first_set_map in
  let rec _first_set_acc existing = function
    | [] -> existing
    | T t :: _ -> TerminalSet.add t existing
    | N nt :: rest ->
        let with_nt_first_set =
          TerminalSet.union existing (first_set_of_nt nt) in
        if is_nullable nt
        then _first_set_acc with_nt_first_set rest
        else with_nt_first_set in
  _first_set_acc TerminalSet.empty frag

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
          let map' = ensure_terminal_set nt map in
          _make_initial map' deps_map tl_prods
      | (nt, T _ :: rhs_rest) :: tl_prods ->
          let next_prods = (nt, rhs_rest) :: tl_prods in
          _make_initial map deps_map next_prods
      | (nt, N rhs_nt :: rhs_rest) :: tl_prods ->
          let first_set = get_first_set rhs_rest in
          let map' = union_terminal_set rhs_nt first_set map in
          let deps_map' =
            if is_fragment_nullable rhs_rest
            then append_nonterminal rhs_nt nt deps_map
            else deps_map in
          let next_prods = (nt, rhs_rest) :: tl_prods in
          _make_initial map' deps_map' next_prods
  in
  let start_map =
    NonTerminalMap.singleton start_symbol (TerminalSet.singleton '$') in
  let init_map, deps_map = _make_initial start_map NonTerminalMap.empty prods in
  let updater (map : terminal_set_map) : terminal_set_map =
    let get_current_follow_set nt = NonTerminalMap.find nt map in
    let get_next_follow_set nt old_follow_set =
      match NonTerminalMap.find_opt nt deps_map with
        | None -> old_follow_set
        | Some deps ->
            let merge dep prev =
              TerminalSet.union (get_current_follow_set dep) prev in
            NonTerminalSet.fold merge deps old_follow_set
    in
    NonTerminalMap.mapi get_next_follow_set map in
  compute_fixed_point updater init_map terminal_set_map_equal

module ParsingTableMap = 
  Map.Make(
    struct
      type t = nonterminal * terminal
      let compare = compare
    end)
type parsing_table = symbol list list ParsingTableMap.t

let make_ll1_table (nullable_map : nullable_map)
                   (first_set_map : terminal_set_map)
                   (follow_set_map : terminal_set_map)
                   (prods : production list) : parsing_table =
  let get_first_set = first_set_of_fragment nullable_map first_set_map in
  let get_follow_set nt = NonTerminalMap.find nt follow_set_map in
  let append_rhs (nt, t) (rhs : symbol list) (tbl : parsing_table)
                 : parsing_table =
    let updater = function
      | None -> Some [rhs]
      | Some existing -> Some (rhs :: existing)
    in
    ParsingTableMap.update (nt, t) updater tbl
  in
  let rec _make_table tbl = function
    | [] -> tbl
    | (nt, rhs) :: rest_prods ->
        let add_rhs_to_entries terminal_set rhs tbl =
          TerminalSet.fold (fun t -> append_rhs (nt, t) rhs) terminal_set tbl in
        let tbl' = add_rhs_to_entries (get_first_set rhs) rhs tbl in
        let tbl'' =
          if is_fragment_nullable nullable_map rhs
          then add_rhs_to_entries (get_follow_set nt) rhs tbl'
          else tbl'
        in
        _make_table tbl'' rest_prods
  in
  _make_table ParsingTableMap.empty prods

let make_rules orig_str : production list =
  let separate_same_nt (nt, rhses) =
    List.to_seq rhses |> Seq.map (fun rhs -> (nt, rhs))
  in
  let classify rhs : symbol list =
    if rhs = "ε" then []
    else
      String.to_seq rhs
        |> Seq.map (fun ch -> if ch = Char.lowercase_ascii ch
                              then T ch
                              else N ch)
        |> List.of_seq
  in
  String.split_on_char '\n' orig_str
    |> List.to_seq
    |> Seq.map (Str.split (Str.regexp " :== "))
    |> Seq.filter_map (function | (lhs :: rhs :: []) -> Some (lhs, rhs)
                                | [] -> None
                                | _ -> assert false)
    |> Seq.map (fun (lhs, rhs) ->
         (assert (String.length lhs = 1); String.get lhs 0,
          Str.split (Str.regexp " | ") rhs))
    |> Seq.flat_map separate_same_nt
    |> Seq.map (fun (nt, rhs) -> (nt, classify rhs))
    |> List.of_seq
