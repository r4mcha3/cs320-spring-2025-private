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

type mem_status = 
  | Free
  | Occupied

type memory = (mem_status * int) list

type alloc_result = 
  | Success of int * memory
  | Invalid_size

type free_result = 
  | Success of memory
  | Invalid_position

let convert (lst : int_or_string list) : int_list_or_string_list list =
  let rec aux acc current = function
    | [] -> (match current with None -> acc | Some v -> v :: acc)
    | Int x :: xs -> (match current with
        | Some (IntList ints) -> aux acc (Some (IntList (x :: ints))) xs
        | Some (StringList strs) -> aux (StringList (List.rev strs) :: acc) (Some (IntList [x])) xs
        | None -> aux acc (Some (IntList [x])) xs)
    | String s :: xs -> (match current with
        | Some (StringList strs) -> aux acc (Some (StringList (s :: strs))) xs
        | Some (IntList ints) -> aux (IntList (List.rev ints) :: acc) (Some (StringList [s])) xs
        | None -> aux acc (Some (StringList [s])) xs)
  in
  List.rev (aux [] None lst)

let recipes_by_ingrs (recs : recipe list) (ingrs : string list) : recipe list =
  let rec subset lst1 lst2 =
    match lst1 with
    | [] -> true
    | x :: xs -> List.mem x lst2 && subset xs lst2
  in
  let rec filter_recipes acc = function
    | [] -> List.rev acc
    | r :: rs ->
        if subset r.ingrs ingrs then filter_recipes (r :: acc) rs
        else filter_recipes acc rs
  in
  filter_recipes [] recs

let rec rev_append l1 l2 =
  match l1 with
  | [] -> l2
  | x :: xs -> rev_append xs (x :: l2)

let allocate (size : int) (mem : memory) : alloc_result =
  if size <= 0 then Invalid_size else
  let rec find_slot pos acc = function
    | [] -> Invalid_size
    | (Free, n) :: rest when n >= size ->
        let updated = if n = size then (Occupied, size) :: rest
                      else (Occupied, size) :: (Free, n - size) :: rest in
        Success (pos, List.rev_append acc updated)
    | (status, n) :: rest -> find_slot (pos + n) ((status, n) :: acc) rest
  in
  find_slot 0 [] mem

let free (pos : int) (mem : memory) : free_result =
  let rec free_helper acc current_pos = function
    | [] -> Invalid_position
    | (Occupied, n) :: rest when current_pos = pos ->
        let new_mem = (Free, n) :: rest in
        let rec merge mem =
          match mem with
          | (Free, n1) :: (Free, n2) :: rest -> merge ((Free, n1 + n2) :: rest)
          | chunk :: rest -> chunk :: merge rest
          | [] -> []
        in
        Success (List.rev_append acc (merge new_mem))
    | (status, n) :: rest -> free_helper ((status, n) :: acc) (current_pos + n) rest
  in
  if pos < 0 then Invalid_position else free_helper [] 0 mem
