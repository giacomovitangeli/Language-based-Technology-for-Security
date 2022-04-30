open Source;;

type expt = Eint of int
    | Ebool of bool
    | Estring of string
    | Den of ide
    | Binop of binop*exp*exp
    | If of exp*exp*exp
    | Let of ide*exp*exp
    | Fun of ide * exp * permissiont list
    | Call of exp*exp;;
  
  
(* type checking *)
let typecheck (s : string) (v : value) : bool =
  match s with
  | "int" ->
      (match v with
      | Int(_) -> true
      | _ -> false)
  | "bool" ->
      (match v with
      | Bool(_) -> true
      | _ -> false)
  | "string" ->
      (match v with
      | String(_) -> true
      | _ -> false)
  | "fun" ->
      (match v with   (* check if the type of the value is a fun *)
      | Closure _ -> true
      | _ -> false )
  | _ -> true;;

let check_typet (ty : typet) : value -> bool =
  match ty with
  | IntType -> typecheck "int"
  | StringType -> typecheck "string"
  | BoolType -> typecheck "bool"
  | FunType(_,_) -> typecheck "fun";;

  (* sandbox *)
let rec execute (e:expt) (env: value env) (secure: permissionList): value =
  match e with
  | Eint n -> Int n
  | Ebool n -> Bool n
  | Estring s -> String s
  | Fun (x, body, permissions) -> Closure (x, body, env, permissions)  
  | Den i -> lookup env i
  |If(e1,e2,e3) ->
      (let g = (eval e1 env secure) in
          match typecheck "bool" g , g with
          | true, Bool(true) -> eval e2 env secure
          | false, Bool(false) -> eval e3 env secure
          | _, _ -> raise (DynamicTypeError "ifthenelse guard must be a boolean")
      )
  |Let(id, e1, e2) -> 
      let xval = eval e1 env secure in
      let env1 = bind env id xval in
      eval e2 env1 secure                   
  |Binop (op,e1,e2) -> (
      let e1 = eval e1 env secure in
      let e2 = eval e2 env secure in
          match op,e1,e2 with
          | Sum,Int n1, Int n2 -> Int (n1+n2)
          | Times,Int n1, Int n2 -> Int (n1 * n2)
          | Minus,Int n1, Int n2 -> Int (n1-n2)
          | Equal, Int n1, Int n2 -> Bool (n1 = n2)
          | Less, Int n1, Int n2 -> Bool (n1 < n2)
          | Greater, Int n1, Int n2 -> Bool (n1 > n2)
          | _ -> failwith "Invalid binary expression" )
  | Call(e1, e2) ->
      (let f = eval e1 env secure in
          match f with
          | Closuret(arg,body,tEnv, tt) ->
              let actualVal = eval e2 env secure  in
              if check_typet tt actualVal = true
                then (
                  let actualVal = bind tEnv arg actualVal in
                  eval body actualVal secure 
                )
              else raise (DynamicTypeError "Call: fail. unexpected actual parameter type")
          | _ -> failwith("error it isn't a closure") );;
      