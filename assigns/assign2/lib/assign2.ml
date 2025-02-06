open Stdlib320

type int_list_or_string_list =
  | IntList of int list
  | StringList of string list

type int_or_string =
  | Int of int
  | String of string

type recipe = {
  name : string;
  ingrs : string list;
}

let convert (lst : int_or_string list) : int_list_or_string_list list =
  let rec aux acc current lst =
    match lst, current with
    | [], Some (IntList il) -> List.rev (IntList (List.rev il) :: acc)
    | [], Some (StringList sl) -> List.rev (StringList (List.rev sl) :: acc)
    | [], None -> List.rev acc
    | (Int x)::xs, Some (IntList il) -> aux acc (Some (IntList (x::il))) xs
    | (String s)::xs, Some (StringList sl) -> aux acc (Some (StringList (s::sl))) xs
    | (Int x)::xs, Some (StringList sl) -> aux (StringList (List.rev sl) :: acc) (Some (IntList [x])) xs
    | (String s)::xs, Some (IntList il) -> aux (IntList (List.rev il) :: acc) (Some (StringList [s])) xs
    | (Int x)::xs, None -> aux acc (Some (IntList [x])) xs
    | (String s)::xs, None -> aux acc (Some (StringList [s])) xs
  in
  aux [] None lst

let recipes_by_ingrs (recs : recipe list) (ingrs : string list) : recipe list =
  let rec subset lst1 lst2 =
    match lst1 with
    | [] -> true
    | x::xs -> List.mem x lst2 && subset xs lst2
  in
  List.filter (fun r -> subset r.ingrs ingrs) recs
