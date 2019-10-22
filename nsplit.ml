(* Adapted from
 * https://github.com/ocaml-batteries-team/batteries-included/blob/2e73d11628627010edb5ac463581db36296d19a3/src/batString.mlv
 * to use base rather than the built-in OCaml standard library, in October 2019.
 *
 * Licensed under LGPL version 2.1 or later. *)

open Base

let rfind_from str pos sub =
  let sublen = String.length sub and len = String.length str in
  if pos + 1 < 0 || pos + 1 > len then assert false ;
  (* invalid_arg "rfind_from"; *)
  (* 0 <= pos + 1 <= length str *)
  if sublen = 0 then Some (pos + 1)
  else
    (* length sub > 0 *)
    (* (pos + 1 - sublen) <= length str - length sub < length str *)
    let rec find ~str ~sub i =
      if i < 0 then None
      else
        (* 0 <= i <= length str - length sub < length str *)
        let rec loop ~str ~sub i j =
          if j = sublen then Some i
          else if
            (* 0 <= j < length sub *)
            (* ==> 0 <= i + j < length str *)
            Char.(String.unsafe_get str (i + j) <> String.unsafe_get sub j)
          then find ~str ~sub (i - 1)
          else loop ~str ~sub i (j + 1)
        in
        loop ~str ~sub i 0
    in
    find ~str ~sub (pos - sublen + 1)

(*
   An implementation of [nsplit] in one pass.

   This implementation traverses the string backwards, hence building the list
   of substrings from the end to the beginning, so as to avoid a call to [List.rev].
*)
let nsplit str ~by:sep =
  if equal_string str "" then []
  else if equal_string sep "" then assert false
    (* invalid_arg "String.nsplit: empty sep not allowed" *)
  else
    (* str is non empty *)
    let seplen = String.length sep in
    let rec aux acc ofs =
      if ofs >= 0 then
        match rfind_from str ofs sep with
        | Some idx ->
            (* sep found *)
            let end_of_sep = idx + seplen - 1 in
            if end_of_sep = ofs (* sep at end of str *) then
              aux ("" :: acc) (idx - 1)
            else
              let token =
                String.sub str ~pos:(end_of_sep + 1) ~len:(ofs - end_of_sep)
              in
              aux (token :: acc) (idx - 1)
        | None ->
            (* sep NOT found *)
            String.sub str ~pos:0 ~len:(ofs + 1) :: acc
      else
        (* Negative ofs: the last sep started at the beginning of str *)
        "" :: acc
    in
    aux [] (String.length str - 1)
