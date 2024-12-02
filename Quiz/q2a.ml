(* 
   Quiz 2 - 7 Feb 2022
   Name1: Michael Buzzetta
   Name2:
*)

type 'a btree = Empty | Node of 'a * 'a btree * 'a btree

let t1 = Node(30,Node(20,Node(10,Empty,Empty),Empty),Empty)
let t2 = Node(4,
              Node(3,
                   Node(2,
                        Node(1,Empty,Empty),
                        Empty),
                   Empty),
              Node(5,
                   Empty,
                   Node(6,
                        Empty,
                        Node(7,Empty,Empty))))

let t3 = Node(12,
              Node(7,Empty,Empty),
              Node(24,
                   Node(18,Empty,Empty),
                   Empty))

(** Implement [level t i] which returns a list with all the nodes in
   [t] at level [i]. You may assume that [i] is greater than 0.
   1 is the first level. 
   If the level is greater than the height of the tree, then 
   it should return the empty list.
   Eg.
# level t2 1 ==> [4]
# level t2 2 ==> [3; 5]
# level t2 3 ==> [2; 6] 
# level t2 33 ==> [] 
*)
let rec level t i = 
  let rec aux t current_level =
    match t with
    | Empty -> []
    | Node (data, left, right) ->
        if current_level = i then [data]
        else aux left (current_level + 1) @ aux right (current_level + 1)
  in aux t 1

(** Implement [levels t] which returns a list of lists, namely a list of the lists of nodes at each level. More precisely, the list at index i consists of all the items in [t] at level i+1.
   Eg. # levels t2 ==> [[4]; [3; 5]; [2; 6]; [1; 7]]
*)
                         
let rec levels t =
  let rec level_list t i =
    level t i :: level_list t (i + 1)
  in level_list t 1

(** Implement [pbt h d] that generates a perfect binary tree of a given height whose nodes contain [d] as
    data. The height is [h] is an integer greater or equal to zero.
    Eg.
 pbt 3 "a" ==>
 Node ("a", Node ("a", Node ("a", Empty, Empty), Node ("a", Empty, Empty)),
 Node ("a", Node ("a", Empty, Empty), Node ("a", Empty, Empty)))
   Eg.
   # pbt 0 3 ==> Empty
*)
let rec pbt h d =
  if h < 0 then Empty
  else if h = 0 then Node (d, Empty, Empty)
  else let subtree = pbt (h - 1) d in
    Node (d, subtree, subtree)

           
(** Implement [paths_to_leaves t] which returns a list with all the paths from the root to a leaf 
    Eg. 
    # paths_to_leaves t2 => [[0; 0; 0]; [1; 1; 1]] 
*)      
let rec paths_to_leaves t =
  let rec aux path acc = function
    | Empty -> acc
    | Node (data, Empty, Empty) -> (List.rev (data :: path)) :: acc
    | Node (data, lt, rt) ->
        aux (data :: path) (aux path acc lt) rt
  in aux [] [] t
                         
(** Implement [paths t] which returns a list with all the paths from the root to any node. If the tree is empty, then paths returns the empty list.
    Eg. 
    # paths t2 => [[0; 0; 0]; [0; 0]; [0]; [1; 1; 1]; [1; 1];
    [1]; []]    
*)  
let rec paths t =
  let rec aux path acc = function
    | Empty -> acc
    | Node (data, lt, rt) ->
        let current_path = data :: path in
        current_path :: (aux current_path (aux path acc lt) rt)
  in aux [] [] t

