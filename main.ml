open Solver
open Printf

let orig_str = Batteries.IO.read_all Batteries.IO.stdin

let rules = make_rules orig_str;;

let string_of_chars (chars : char list) =
  let buf = Buffer.create (List.length chars) in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf
let string_of_t_set (t_set : terminal_set) = 
  let buf = Buffer.create (TerminalSet.cardinal t_set) in
  TerminalSet.iter (Buffer.add_char buf) t_set;
  Buffer.contents buf
let string_of_nt_set (nt_set : nonterminal_set) = 
  let buf = Buffer.create (NonTerminalSet.cardinal nt_set) in
  NonTerminalSet.iter (Buffer.add_char buf) nt_set;
  Buffer.contents buf

let print_nullable_map : nullable_map -> unit =
  NonTerminalMap.iter (printf "%c -> %b\n")
let print_nullable_dependency_map : nullable_dependency_map -> unit =
  NonTerminalMap.iter (fun nt deps_list ->
    printf "%c -> %s\n"
           nt
           (deps_list
              |> List.map (fun deps -> "[" ^ string_of_nt_set deps ^ "]")
              |> String.concat ", "))
let print_terminal_set_map : terminal_set_map -> unit =
  NonTerminalMap.iter (fun nt terminal_set ->
    printf "%c -> [%s]\n" nt (string_of_t_set terminal_set))
let print_nonterminal_set_map : nonterminal_set_map -> unit =
  NonTerminalMap.iter (fun nt deps ->
    printf "%c -> [%s]\n" nt (string_of_nt_set deps))
let print_parsing_table : parsing_table -> unit =
  ParsingTableMap.iter (fun (nt, t) rhs_set ->
    printf "(%c,%c) -> [%s]\n" nt t
      (rhs_set
         |> List.map (fun (rhs : symbol list) ->
              if rhs = [] then "ε"
              else rhs |> List.map extract_name |> string_of_chars)
         |> String.concat ", "))

let nullable_map = make_nullables rules;;
printf "nullable map:\n";
print_nullable_map nullable_map;;

let first_set_map = make_first_set nullable_map rules;;
printf "first set map:\n";
print_terminal_set_map first_set_map;;

let follow_set_map = make_follow_set nullable_map first_set_map 'A' rules;;
printf "follow set map:\n";
print_terminal_set_map follow_set_map;;

let ll1_table = make_ll1_table nullable_map first_set_map follow_set_map rules;;
printf "table:\n";
print_parsing_table ll1_table;;
