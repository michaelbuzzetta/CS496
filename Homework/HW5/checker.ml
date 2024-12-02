(*Names: Michael Buzzetta and Aidan Ouckama*)
(*Pledge: I pledge my honor that I have abided by the Stevens Honor System.*)

open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result =
  fun e ->
  match e with
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error "LetRec: Type of recursive function does not match
declaration")
   | Pair(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    return @@ PairType(t1,t2)
  | Unpair(id1,id2,e1,e2) ->
    chk_expr e1 >>= fun t ->
    (match t with
     | PairType(t1,t2) ->
    extend_tenv id1 t1 >>+
    extend_tenv id2 t2 >>+
    chk_expr e2
     | _ -> error "unpair: expected a pair")
      
  (* EXPLICIT-REFS *)
  | BeginEnd([]) ->
    return UnitType
  | BeginEnd(es) ->
    chk_exprs es >>= fun l ->
      return UnitType
  | NewRef(e) ->
    chk_expr e >>= fun t ->
      return @@ RefType t
  | DeRef(e) ->
    chk_expr e >>= fun t ->
      (match t with
      | RefType t1 -> return @@ t1
      | _ -> error "deref: Expected a reference type")
  | SetRef(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
      (match t1 with
      | RefType t1 -> return UnitType
      | _ -> error "setref: Expected a reference and a value")

  (* list *)
  | EmptyList(None) ->
      error "emptylist: expected a type"
  | EmptyList(Some t) ->
      return @@ ListType t
  | Cons(h, t) ->
    chk_expr h >>= fun hd ->
    chk_expr t >>= fun tl ->
      (match tl with
      | ListType t -> if (hd==t) then return @@ ListType t else error "cons: type of head and tail do not match"
      | _ -> error "cons: expected a listtype some t")
  | IsEmpty(e) ->
    chk_expr e >>= fun t ->
      (match t with
      | ListType t -> return BoolType
      | TreeType t -> return BoolType
      | _ -> error "isempty: expected a list or a tree")
  | Hd(e) ->
    chk_expr e >>= fun t ->
      (match t with
      | ListType t -> return t
      | _ -> error "hd: expected a listtype")
  | Tl(e) ->
    chk_expr e >>= fun t ->
      (match t with
      | ListType t -> return @@ ListType t
      | _ -> error "tl: expected a listtype")

  (* tree *)
  | EmptyTree(None) ->
      error "emptytree: expected a tree"
  | EmptyTree(Some t) ->
      return @@ TreeType t
  | Node(de, le, re) ->
      chk_expr de >>= fun n1 ->
      chk_expr le >>= fun n2 ->
      chk_expr re >>= fun n3 ->
        (match n2 with
          | TreeType t2 ->
            match n3 with
            | TreeType t3 ->
              if (n1==t2) then 
                if (n1==t3) then return @@ TreeType n1 else error "node: type of nodes do not match"
              else error "node: type of nodes do not match"
            | _ -> error "node: expected a tree"
          | _ -> error "node: expected a tree")
  | CaseT(target,emptycase,id1,id2,id3,nodecase) ->
      chk_expr target >>= fun t ->
      chk_expr emptycase >>= fun ec ->
      (match t with
      | TreeType d -> 
        extend_tenv id1 d >>+
        extend_tenv id2 t >>+
        extend_tenv id3 t >>+
        chk_expr nodecase >>= fun nc ->
        if ec=nc then return @@ ec
        else error "caset: emptycase type must match nodecase type"
      | _ -> error "caset: target must be a node"
      )
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_exprs =
  fun es ->
  match es with
  | [] -> return []
  | h::tl -> chk_expr h >>= fun t ->
    chk_exprs tl >>= fun ts ->
    return (t::ts)
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)