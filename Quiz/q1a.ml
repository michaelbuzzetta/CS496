(* Quiz 1 - 31 January 2024

   Student name 1: Michael Buzzetta
   Student name 2:

*)

(*
    Throughout this code I referenced the notes from canvas, 
    as well as concept explinations from websites such as W3Schools and StackOverflow
    No code was copied directly from any online resources
*)

(* Notes: 
    a. You may add helper functions.
    b. "let rec" allows your function to be recursive, but it doesn't
    have to be. 
*)

(* Sample Directed Graph *)

let ex = [(1, 2); (2, 3); (3, 1); (3, 4)]


(*
  1 <------ 3
  |      //||
  |     /   | 
  |    /    | 
 \/  /     \/
  2        4
*)
       
(** [sub l1 l2] returns the list resulting from subtracting every 
    element in [l2] from [l1].
    Eg. sub [1;2] [] => [1; 2]
    Eg. sub [1;2;1] [1] => [2]
    Eg. sub [1;2] [2;3;1] => []
*)
let rec sub l1 l2 =
  match l1 with
  | [] -> []
  | hd :: tl -> if List.mem hd l2 then sub tl l2 else hd :: sub tl l2

    
(** [outgoing g n] returns the list of all the nodes that are
    immediate neighbors of [n] in [g].
    Eg. outgoing ex 3 => [1,4] 
*)
let rec outgoing_nodes g n =
  List.fold_left
    (fun acc (src, dest) -> if src = n then dest :: acc else if dest = n then src :: acc else acc)
    [] g

(** [nodes g] returns the list of nodes of the graph [g] without duplicates. 
   The order of the nodes in the list is irrelevant.
   eg. nodes ex => [1,2,3,4] 
*)
let rec nodes g =
  List.fold_left
    (fun acc (src, dest) -> src :: dest :: acc)
    [] g
  |> List.sort_uniq compare

(** [degree g] returns the degree of [g]. The degree of a graph is 
    the maximum number of outgoing edges that any node has. 
*)
let rec degree g =
  let count_occurrences acc (_, dest) = 
    let dest_count = try List.assoc dest acc with Not_found -> 0 in
    (dest, dest_count + 1) :: acc in

  List.fold_left count_occurrences [] g
  |> List.map snd
  |> List.fold_left max 0

(** [remove g n] removes node [n] and all the edges involving [n], from
   the graph [g].
   Eg. remove ex 2 =>  [(3, 1); (3, 4)] 
*)
let rec remove g n =
  List.filter (fun (src, dest) -> src <> n && dest <> n) g
  
(** [reachable g n] returns the list of all the reachable nodes from
   node [n] in [g]. (Extra-credit)
   Eg. reachable ex 3 => [1,4,2,3] 
*)

let rec reachable g n =
  let rec explore visited current =
    match current with
    | [] -> visited
    | hd :: tl ->
        if List.mem hd visited then explore visited tl
        else explore (hd :: visited) (outgoing_nodes g hd @ tl)
  in
  explore [] [n]
  
  
  