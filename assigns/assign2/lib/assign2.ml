open Stdlib320

type int_list_or_string_list = 
  | IntList of int list
  | StringList of string list

 type int_or_string = 
  | Int of int
  | String of string

let convert (lst : int_or_string list) : int_list_or_string_list list =
  let rec aux acc current = function
    | [] -> (match current with None -> acc | Some group -> group :: acc)
    | Int x :: rest ->
      (match current with
       | Some (IntList ints) -> aux acc (Some (IntList (x :: ints))) rest
       | Some (StringList strs) -> aux (StringList (List.rev strs) :: acc) (Some (IntList [x])) rest
       | None -> aux acc (Some (IntList [x])) rest)
    | String s :: rest ->
      (match current with
       | Some (StringList strs) -> aux acc (Some (StringList (s :: strs))) rest
       | Some (IntList ints) -> aux (IntList (List.rev ints) :: acc) (Some (StringList [s])) rest
       | None -> aux acc (Some (StringList [s])) rest)
  in
  List.rev (aux [] None lst)

type recipe = {
  name : string;
  ingrs : string list;
}

let recipes_by_ingrs (recs : recipe list) (ingrs : string list) : recipe list =
  let contains_all ings1 ings2 = List.for_all (fun i -> List.mem i ings2) ings1 in
  List.filter (fun r -> contains_all r.ingrs ingrs) recs

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

let allocate (size : int) (mem : memory) : alloc_result =
  if size <= 0 then Invalid_size
  else
    let rec find_fit pos acc = function
      | [] -> Invalid_size
      | (Free, fsize) :: rest when fsize >= size ->
        let occupied_chunk = (Occupied, size) in
        let remaining_free = fsize - size in
        let updated_mem =
          if remaining_free > 0 then (occupied_chunk :: (Free, remaining_free) :: rest)
          else (occupied_chunk :: rest)
        in
        Success (pos, List.rev_append acc updated_mem)
      | chunk :: rest -> find_fit (pos + snd chunk) (chunk :: acc) rest
    in
    find_fit 0 [] mem

let free (pos : int) (mem : memory) : free_result =
  if pos < 0 then Invalid_position
  else
    let rec free_chunk acc current_pos = function
      | [] -> Invalid_position
      | (Occupied, size) :: rest when current_pos = pos ->
        let new_mem = List.rev_append acc ((Free, size) :: rest) in
        let rec merge_free = function
          | (Free, s1) :: (Free, s2) :: tl -> merge_free ((Free, s1 + s2) :: tl)
          | hd :: tl -> hd :: merge_free tl
          | [] -> []
        in
        Success (merge_free new_mem)
      | chunk :: rest -> free_chunk (chunk :: acc) (current_pos + snd chunk) rest
    in
    free_chunk [] 0 mem
