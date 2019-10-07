open Base
open Stdio
open Solver

let orig_str = In_channel.input_all stdin;;

let rules = make_rules orig_str;;

let string_of_chars (chars : char list) =
  let buf = Buffer.create (List.length chars) in
  List.iter chars ~f:(Buffer.add_char buf);
  Buffer.contents buf
let string_of_char_set set = 
  let buf = Buffer.create (Set.length set) in
  Set.iter set ~f:(Buffer.add_char buf);
  Buffer.contents buf

let print_nullable_map : nullable_map -> unit =
  Map.iteri ~f:(fun ~key ~data -> printf "%c -> %b\n" key data)
let print_nullable_dependency_map : nullable_dependency_map -> unit =
  Map.iteri ~f:(fun ~key:nt ~data:deps_list ->
    printf "%c -> %s\n"
           nt
           (deps_list
              |> List.map ~f:(fun deps -> "[" ^ string_of_char_set deps ^ "]")
              |> String.concat ~sep:", "))
let print_char_set_map : terminal_set_map -> unit =
  Map.iteri ~f:(fun ~key ~data ->
    printf "%c -> [%s]\n" key (string_of_char_set data))
let print_parsing_table : parsing_table -> unit =
  Map.iteri ~f:(fun ~key:(nt, t) ~data:rhs_set ->
    printf "(%c,%c) -> [%s]\n" nt t
      (Set.to_list rhs_set
         |> List.map ~f:(fun (rhs : symbol list) ->
              if List.is_empty rhs then "ε"
              else rhs |> List.map ~f:extract_name |> string_of_chars)
         |> String.concat ~sep:", "))

let nullable_map = make_nullables rules;;
printf "nullable map:\n";
print_nullable_map nullable_map;;

let first_set_map = make_first_set nullable_map rules;;
printf "first set map:\n";
print_char_set_map first_set_map;;

let follow_set_map = make_follow_set nullable_map first_set_map 'A' rules;;
printf "follow set map:\n";
print_char_set_map follow_set_map;;

let ll1_table = make_ll1_table nullable_map first_set_map follow_set_map rules;;
printf "table:\n";
print_parsing_table ll1_table;;
