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
  let contains_all ingr_list recipe =
    List.for_all (fun ingr -> List.mem ingr ingrs) recipe.ingrs
  in
  List.filter (contains_all ingrs) recs

let allocate (size : int) (mem : memory) : alloc_result =
  if size <= 0 then Invalid_size
  else
    let rec find_position pos acc = function
      | [] -> Invalid_size
      | (Free, fsize) :: rest when fsize >= size ->
          let new_chunk = (Occupied, size) in
          let remaining = if fsize > size then [(Free, fsize - size)] else [] in
          Success (pos, List.rev_append acc (new_chunk :: remaining @ rest))
      | chunk :: rest -> find_position (pos + snd chunk) (chunk :: acc) rest
    in
    find_position 0 [] mem

let free (pos : int) (mem : memory) : free_result =
  if pos < 0 then Invalid_position
  else
    let rec update_mem acc curr_pos = function
      | [] -> Invalid_position
      | (Occupied, size) :: rest when curr_pos = pos ->
          let updated_mem = List.rev_append acc ((Free, size) :: rest) in
          let rec merge_adjacent = function
            | (Free, s1) :: (Free, s2) :: tl -> merge_adjacent ((Free, s1 + s2) :: tl)
            | hd :: tl -> hd :: merge_adjacent tl
            | [] -> []
          in
          Success (merge_adjacent updated_mem)
      | chunk :: rest -> update_mem (chunk :: acc) (curr_pos + snd chunk) rest
    in
    update_mem [] 0 mem
