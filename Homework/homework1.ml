(*
   Homework 1
   I pledge my honor that I have abided by the stevens honor system
   Michael Buzzetta
*)

(* 
   This assignment was completed with the help of CA's during office hours
   Chris Kang
   Jessica Sabatino
   Haolin Chen
*)

type program = int list
    
let letter_e=[0;2;2;3;3;5;5;4;3;5;4;3;3;5;5;1] 
                                              

(*
   If the input is 0 or 1, the input is unedited
   If the input is 2 or 3, add 2 to the input
   If the input is 4 or 5, subtract 2 from the input
*)
let rec mirror_image(letter_e : int list) :int list =
  match letter_e with
  | [] -> []
  | 2::m -> 4::(mirror_image m)
  | 3::m -> 5::(mirror_image m)
  | 4::m -> 2::(mirror_image m)
  | 5::m -> 3::(mirror_image m)
  | x::m-> x::(mirror_image m)
               
(*
   If the input is 0 or 1, the input is unedited
   If the input is 2, add 3 to the input
   if the input is 3 or 5, subtract 1 from the input
   If the input is 4, add 1 to the input
*)
let rec rotate_90_letter(letter_e : int list) : int list =
  match letter_e with 
  | [] -> []
  | 2::r -> 3::(rotate_90_letter r)
  | 3::r -> 4::(rotate_90_letter r)
  | 4::r -> 5::(rotate_90_letter r)
  | 5::r -> 2::(rotate_90_letter r)
  | x::r -> x::(rotate_90_letter r)

(*rotate_90_word helper*)
let rec rotate_90_word_helper: int -> int = fun num->
  match num with
  | 2 -> 3
  | 3 -> 4
  | 4 -> 5
  | 5 -> 2
  | x -> x
  
(*helper function 2*)
let rec rotate_90_word_helper2(temp : int list) : int list =
  List.map (rotate_90_word_helper) temp

(*
   If the input is 0 or 1, the input is unedited
   If the input is 2, 3, or 4, add 1 to the input
   If the input is 5, subtract 3 from the input
*)
let rec rotate_90_word(letter_e : int list list) : int list list =
  List.map (rotate_90_word_helper2) letter_e

(*
   repeats the inputs a set number of times   
*)
let rec repeat(iterations : int) (input :'a) : 'a list =
  match iterations with
  | 0 ->[]
  |_-> input::(repeat(iterations-1) input)

(*
   calls a function that recreates what p drew, but larger by N-degrees
   uses map
*)
let pantograph (n : int) (p : int list) : int list =
  let m = (List.map (fun x -> 
      if x > 1 
      then repeat n x 
      else [x]) p) in
  List.fold_left (fun x y -> x @ y) [] m

(*does not use map*)
let rec pantograph_nm (n : int) (p : int list) : int list =
  match p with
  | [] -> []
  | 0::nm -> 0::pantograph_nm n nm
  | 1::nm -> 1::pantograph_nm n nm
   

(*uses fold*)
let pantograph_f (n : int) (p : int list) : int list = 
  let f = (List.map (fun x -> 
      if x > 1 
      then repeat n x 
      else [x]) p) in
  List.fold_left (fun x y -> x @ y) [] f

(*
   if the input is 2, move north (x, y+1)
   if the input is 3, move east (x+1, y)
   if the input is 4, move south (x, y-1)
   if the input is 5, move west (x-1, y)
   Takes in directions and outputs coordinates
*)
let rec coverage ((x,y) : int * int) (letter_e : int list) :  (int * int) list = 
  match letter_e with
  | [] -> (x,y)::[]
  | 2::c -> (x,y)::(coverage (x,y+1) c)
  | 3::c -> (x,y)::(coverage (x+1,y) c)
  | 4::c -> (x,y)::(coverage (x,y-1) c)
  | 5::c -> (x,y)::(coverage (x-1,y) c)
  | _::c -> (x,y)::(coverage (x,y) c)

(*compress helper function that count the duplicates*)
let rec compress_help (e: int) (ch : int list) : int*(int list) =
  match ch with
  | [] -> (0,[])
  | h::t -> if (h=e) then let (c,new_l) = (compress_help e t) in (c+1,new_l)
      else (0,ch)
   
 
 (*
   counts the number of adjacent copies 
   x,numberOfTimes 
*)
let rec compress (letter_e : int list) : ( int * int ) list = 
  match letter_e with
  | [] -> []
  | h::t -> let (c,new_l) = compress_help h letter_e in
      (h, c)::(compress new_l)

(*
   uncompresses list
   without map 
*)
let rec uncompress (comp : (int*int) list) : int list = 
  match comp with
  | [] -> []
  | (n, amt)::t -> (repeat amt n) @ (uncompress t)
 
(*with map*)
let rec uncompress_m (comp : (int*int) list) : int list =
  let uc = (List.map (fun (x,n) -> repeat n x) comp) in
  List.fold_left (fun x y -> x @ y) [] uc

(*with fold*)
let rec uncompress_f (comp : (int*int) list) : int list =
  let ucf = (List.map (fun (x,n) -> repeat n x) comp) in
  List.fold_left (fun x y -> x @ y) [] ucf

(*optimize helper function that trackes the current position of the pen*)
let rec optimize_helper (list : program) (position : int) : program =
  match list with
  | [] -> []
  | 0::t -> if position=0 then (optimize_helper t 0) else 0::(optimize_helper t 0)
  | 1::t -> if position=1 then (optimize_helper t 1) else 1::(optimize_helper t 1)
  | x::t -> x::optimize_helper t position
 
 
(*optimize*)
let rec optimize (list : program) : program = 
  optimize_helper list 1