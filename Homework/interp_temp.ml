open Ds
open ReM
open Parser_plaf.Ast
open Parser_plaf.Parser

(*Michael Buzzetta
   I pledge my honor that I have abided by the Stevens Honor system*)

(* params * body * super * fields *)
type method_decl = string list*expr*string*string list

type method_env = (string*method_decl) list

type class_decl = string*string list*method_env

type class_env = ((string*class_decl) list)

(* Global holding the store *)
let g_store = Store.empty_store 20 (NumVal 0)

(* Global holding class declarations *)
let g_class_env : class_env ref = ref []


(* Initialize contents of g_class_env variable  *)
let name_mangle n es =
  n^"_"^string_of_int(List.length es)

let initialize_class_env cs =      
  let rec get_fields =
    fun cs c_name class_decls ->
      match class_decls with
      | [] -> []
      | Class (name, super, _, fields, _)::_ when name=c_name ->
        List.map fst fields :: get_fields cs super cs
      | Class (_, _, _, _, _)::cs' | Interface(_, _)::cs' ->
        get_fields cs c_name cs'
  in  
  let rec get_methods cs c_name fss = function
  | [] -> []
  | Class (name, super, _, _, methods)::_ when name=c_name ->
    List.map (fun (Method(n, _ret_type, pars, body)) ->
        let mangled_name = name_mangle n pars in
        (mangled_name, (List.map fst pars, body, super, List.flatten fss))
      ) methods @ get_methods cs super (List.tl fss) cs
  | Class (_, _, _, _, _)::cs' | Interface(_, _)::cs' ->
    get_methods cs c_name fss cs'
  in
  let rec initialize_class_env' cs = function
    | [] -> ()
    | Class (name, super, _, fields, methods)::cs'  ->
      let fss = (List.map fst fields) :: get_fields cs super cs
      in let ms = (List.map (fun (Method(n, _ret_type, pars, body)) ->
                              let mangled_name = name_mangle n pars in
                              (mangled_name, (List.map fst pars, body, super, List.flatten fss)))
                     methods) @ get_methods cs super (List.tl fss) cs
      in
      g_class_env := (name, (super, List.flatten fss, ms)) :: !g_class_env;
      initialize_class_env' cs cs'
    | Interface(_, _)::cs' ->
      initialize_class_env' cs cs'             
  in g_class_env := [("object", ("", [], []))];
  initialize_class_env' cs cs

let slice fs env =
  (* return env >>+ string_of_env >>= fun senv -> *)
  (* print_string  @@ "Slicing:" ^String.concat "," fs *)
  (*                  ^ "\n" ^ senv ^"\n"; *)
  let rec slice' fs acc env =
    match fs, env with
    | [],_ -> acc
    | id::ids, ExtendEnv(id',ev,tail) when id=id' ->
      slice' ids (ExtendEnv(id',ev,acc)) tail
    | _,_ -> failwith @@ 
      "slice: ids different or lists have different lengths "
  in
  let new_env = (slice' (List.rev fs) EmptyEnv env) 
  in (* print_string @@ "Result is:" ^(string_of_env' new_env) ^"\n"; *)
  return new_env

let new_env : string list -> env ea_result  =
  fun fs ->
  let rec new_env' fs =
    match fs with
    | [] -> lookup_env 
    | id::ids ->
      extend_env id (RefVal (Store.new_ref g_store (NumVal 0))) >>+
      new_env' ids
  in return EmptyEnv >>+ new_env' fs   

let lookup_method : string -> string -> class_env -> method_decl option =
  fun c_name m_name c_env ->
  match List.assoc_opt c_name c_env with
  | None -> None
  | Some (_super,_fs,ms) -> 
    List.assoc_opt m_name ms

let rec apply_method : string -> exp_val -> exp_val list ->
  method_decl -> exp_val ReM.result =
  fun m_name self args (pars,body,super,fs) ->
  let l = Store.new_ref g_store self (* allocate self *)
  and l_args = List.map (fun ev -> RefVal (Store.new_ref g_store ev)) args in
  let l' = Store.new_ref g_store (StringVal super) in
  if List.length args <> List.length pars then
    ReM.error (m_name ^ ": args and params have different lengths")
  else
    obj_of_objectVal self >>= fun (_c_name,env) ->
    slice fs env >>= fun sliced_env ->
    extend_env_list ("_super"::"_self"::pars) ((RefVal l')::(RefVal l)::l_args) >>= fun extended_env ->
    eval_expr body sliced_env >>= fun result -> ReM.return result
     
and
  is_subclass:string -> string -> class_env -> exp_val ea_result =
  fun id1 id2 class_env ->
  match List.assoc_opt id2 class_env with
  | None -> error ("is_subclass: class " ^ id2 ^ " not found!")
  | Some (_, _, _) -> (
    match List.assoc_opt id1 class_env with
    | None -> error ("is_subclass: class " ^ id1 ^ " not found!")
    | Some (_super, _, _) -> 
      if id1 = id2 then return (BoolVal true) (* classes are the same *)
      else if _super = "" then return (BoolVal false) (* reached the root class *)
      else if _super = id2 then return (BoolVal true) (* found the superclass *)
      else is_subclass _super id2 class_env (* check the superclass *)
    )
and   
  eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) -> return @@ NumVal n
  | Var(id) -> 
    apply_env id >>=
    int_of_refVal >>= fun l ->
    Store.deref g_store l >>= fun ev ->
    return ev
  | Add(e1, e2) ->
    eval_expr e1 >>= fun n1 ->
    int_of_numVal n1 >>= fun num1 ->
    eval_expr e2 >>= fun n2 ->
    int_of_numVal n2 >>= fun num2 ->
    return @@ NumVal (num1 + num2)
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1-n2)
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return @@ NumVal (n1*n2)
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return @@ NumVal (n1/n2)
  | Let(v,def,body) ->
    eval_expr def >>= fun ev ->
    let l = Store.new_ref g_store ev
    in extend_env v (RefVal l) >>+
    eval_expr body
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return @@ BoolVal (n = 0)
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return @@ PairVal(ev1,ev2)
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun p ->
    return @@ fst p
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun p ->
    return @@ snd p
  | Proc(id,_,e)  ->
    lookup_env >>= fun en ->
    return @@ ProcVal(id,e,en)
  | App(e1,e2)  ->
    eval_expr e1 >>= 
    clos_of_procVal >>= fun (id,e,en) ->
    eval_expr e2 >>= fun ev ->
    let l = Store.new_ref g_store ev
    in return en >>+
    extend_env id (RefVal l) >>+
    eval_expr e
  | Letrec([(id,par,_tParam,_tRes,e)],target) ->
    let l = Store.new_ref g_store UnitVal in
    extend_env id (RefVal l) >>+
    (lookup_env >>= fun env ->
     Store.set_ref g_store l (ProcVal(par,e,env)) >>= fun _ ->
     eval_expr target
    )
  (* Mutable references operations *)
  | Set(id,e) ->
    eval_expr e >>= fun ev ->
    apply_env id >>=
    int_of_refVal >>= fun l ->
    Store.set_ref g_store l ev >>= fun _ ->
    return UnitVal
  | BeginEnd([]) ->
    return UnitVal
  | BeginEnd(es) -> 
    eval_exprs es >>= fun vs ->
    return (List.hd (List.rev vs))
  (* SOOL operations *)
  | NewObject(c_name,es) ->
    eval_exprs es >>= fun args ->
    (match List.assoc_opt c_name !g_class_env with
     | None -> error ("NewObject: lookup_class: class "^c_name^" not found")
     | Some (_super,fields,methods) -> 
       new_env fields >>= fun env ->
       let self = ObjectVal(c_name,env)
       in (match List.assoc_opt (name_mangle "initialize" es) methods with
          | None -> return self
          | Some m -> apply_method (name_mangle "initialize" es) self args >>= fun _ ->
            return self))
  | Send(e,m_name,es) ->
    eval_expr e >>= fun self ->
    obj_of_objectVal self >>= fun (c_name,_) ->
    eval_exprs es >>= fun args ->
    let mangled_name = (name_mangle m_name args) in
    (match lookup_method c_name mangled_name !g_class_env with
     | None -> error ("Method "^mangled_name^" not found")
     | Some m -> apply_method mangled_name self args m)
  | Self ->
    eval_expr (Var "_self")
    | Super(m_name,es) ->
      eval_exprs es >>= fun args ->
      eval_expr (Var "_super") >>=
      string_of_stringVal >>= fun c_name ->
      eval_expr (Var "_self") >>= fun self ->
      let mangled_name = (name_mangle m_name args) in
      (match lookup_method c_name mangled_name !g_class_env with
       | None -> error ("Method not "^mangled_name^" found")
       | Some m -> apply_method mangled_name self args m)
  (* List operations* *)
  | List(es) ->
    eval_exprs es >>= fun args ->
    return @@ ListVal args
  | Cons(e1,e2) ->
    eval_expr e1 >>= fun ev ->
    eval_expr e2 >>=
    list_of_listVal >>= fun l ->
    return @@ ListVal (ev::l)
  | Hd(e) ->
    eval_expr e >>=
    list_of_listVal >>= fun l ->
    return @@ List.hd l
  | Tl(e) ->
    eval_expr e >>=
    list_of_listVal >>= fun l ->
    return @@ ListVal (List.tl l)
  | IsEmpty(e) ->
    eval_expr e >>=
    list_of_listVal >>= fun l ->
    return @@ BoolVal (l=[])
  (* New OfInstance *)
  | IsInstanceOf(e, id) ->
    eval_expr e >>= fun obj ->
    (match obj with
     | ObjectVal(c_name, _) ->
      is_subclass c_name id !g_class_env >>= fun result ->
      return result
     | _ -> error "IsInstanceOf: Operand is not an object"
    )
  (* Debug *)
  | Debug(_e) ->
    string_of_env >>= fun str_env ->
    let str_store = Store.string_of_store string_of_expval g_store
    in (print_endline (str_env^"\n"^str_store);
        error "Reached breakpoint")
  | _ -> failwith ("eval_expr: Not implemented: "^string_of_expr e)
and
  eval_exprs : expr list -> exp_val list ea_result =
  fun es ->
  match es with
  | [] -> return []
  | h::t ->
    eval_expr h >>= fun ev ->
    eval_exprs t >>= fun evs ->
    return (ev::evs)
and
  eval_prog : prog -> exp_val ea_result =
  fun (AProg(cs, e)) ->
  initialize_class_env cs;   (* Step 1 *) 
  eval_expr e                (* Step 2 *)


(** [interp s] evaluates program [s] *)
let interp (s: string) : exp_val result = 
  let c = s |> parse |> eval_prog in
  run c

(** [interpf file_name] evaluates program in file [file_name] *)
let interpf (file_name: string) : exp_val result = 
  let c = file_name |> parsef |> eval_prog in
  run c
