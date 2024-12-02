(*
   Homework 2
   I pledge my honor that I have abided by the stevens honor system
   Michael Buzzetta
*)

(* 
   This assignment was completed with the help of CA's during office hours
   Chris Kang
*)

type 'a gt = Node of 'a*('a gt) list

let mk_leaf (n : 'a) : 'a gt = Node(n, [])

(*Copied form Canvas)*)
let t : int gt =
  Node (33,
        [Node (12,[]);
         Node (77, 
               [Node (37, 
                      [Node (14, [])]); 
                Node (48, []); 
                Node (103, [])])
        ])

(*
   This function gets the height of the tree
   h variable for height
*)
let rec height (h : 'a gt) : int =
  match h with
  | Node(_, []) -> 1
  | Node(_, x) -> 1 + List.fold_left max 0 (List.map height x) 

(*
   This function gets the size of the tree
   s variable for size
*)
let rec size (s : 'a gt) : int =
  match s with
  | Node(_, []) -> 1
  | Node(_, x) -> 1 + List.fold_left (+) 0 (List.map size x)

(*
   This function gets the number of paths from the root 
   to the leaves of the tree
*)
let rec paths_to_leaves (Node(d,ch) : 'a gt) : int list list = 
   let rec iterator x y =
      match y with
      |[] -> []
      |h::t -> (List.map(fun path -> x :: path) (paths_to_leaves h)) @ (iterator (x + 1) t) in
   match (Node(d,ch)) with
      |Node(x, []) -> [[]]
      |Node(x, y) -> iterator 0 y

(*Helper Function*)
let rec is_leaf_perfect_helper = function
  | [] -> 0
  | h::t -> h + is_leaf_perfect_helper t

(*
   This function checks if the tree is perfect
   pt variable for perfect tree   
*)
let rec is_leaf_perfect (pt : 'a gt) : bool =
  let length_p = List.map List.length @@ paths_to_leaves pt in
  match length_p with
  | [] -> false
  | h::t -> if h = (is_leaf_perfect_helper length_p)/h 
      then 
        true 
      else 
        false

(*This function returns the preorder traversal of the tree*)
let rec preorder (Node(d,ch) : 'a gt ) : int list =
  match Node(d, ch) with
  | Node(_, []) -> [d]  
  | Node(_, x) -> d::(List.flatten(List.map preorder ch))

(*This function returns a mirrored version of the tree*)
let rec mirror (Node(d,ch) : 'a gt) : 'a gt =
  match Node(d, ch) with 
  | Node(_, []) -> Node(d, [])
  | Node(_, x) -> Node(d, List.rev(List.map mirror ch))

(*This function maps the tree*)
let rec map (f : 'a -> 'b) (Node(d,ch) : 'a gt) : 'b gt =
  (Node(f d, List.map(map f) ch))

(*This function folds to reduce the tree *)  
let rec fold : ('a -> 'b list -> 'b) -> 'a gt -> 'b =
  fun f (Node(d,ch)) ->
    f d (List.map(fold f) ch)

(*This function does the same thing as mirror, but uses fold*)
let rec mirror' (t : 'a gt) : 'a gt = 
  fold(fun i rs -> Node(i, List.rev rs)) t

(*This function returns the max number of children of one of the nodes*)
let rec degree (t : 'a gt) : int = 
  match t with
  | Node(_, []) -> 0
  | Node(_, ch) -> max(List.length ch) (List.fold_left max 0 (List.map degree ch))

