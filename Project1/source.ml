exception DynamicTypeError of string (* run time error exception *)
                                	 
type 't env = (string * 't ) list

type ide = string;;

(* All binary operators are modelled with the type binop, to handle them in a more concise manner inside the interpreter *)
type binop = 
    | Sum 
    | Times 
    | Minus 
    | Equal 
    | Less 
    | Greater;;

(* kind of permissions *)
type permissiont =
    | Pread
    | Pwrite
    | Psend;;

(* permissionList stores the permissions of every function *)
type permissionList = (permissiont list) list;;

(* The language has been extended with booleans, Functions and functions calls and read, write,
open and send operations. These four represent a generic interaction with a system resource. *)
type exp = Eint of int
    | Ebool of bool
    | Estring of string
    | Den of ide
    | Binop of binop*exp*exp
    | If of exp*exp*exp
    | Let of ide*exp*exp
    | Fun of ide * exp * permissiont list
    | Call of exp*exp
    | Read of string
    | Write of string
    | Open of string
    | Send of string;;

type typet =
    | IntType
    | StringType
    | BoolType
    | FunType of typet * typet;;

type  value = 
    | Int of int
    | Bool of bool
    | String of string
    | Closure of  valueFun
    | Closuret of ide * exp * value env * typet
    and valueFun = ide * exp * value env * permissiont list;;

let rec lookup env x =
match env with
| [] -> failwith (x ^ " not found")
| (ide, value)::r -> if x = ide then value else lookup r x;;

let bind (env:value env) (x: ide) (v: value) = (x,v)::env;;

(* permissions management *)
let rec verify_singlePermission (pSraw:permissiont list) (pDem:permissiont) : bool =
    match pSraw with
    | [] -> false (* if remain the empty list means that we don't find the permission needed *)
    | x::r1 -> if  x = pDem then true else verify_singlePermission r1 pDem;;

let rec demandPermission (permStack:permissiont list) (demanded:permissiont list) : bool =
    match demanded with
    | [] -> true (* this design is for performance motivation, for the case of an empty permissions list *)
    | x::y -> match permStack with
    | [] -> false
    | z::u -> if verify_singlePermission permStack x then demandPermission permStack y else false;;

let rec superPrivilegesVerifier (permStack:permissionList) (demanded:permissiont list) : bool =
    match demanded with
    | [] -> true
    | _  -> match permStack with
    | [] -> true
    | x :: y -> demandPermission x demanded && superPrivilegesVerifier y demanded;;


(* interpreter *)
let rec eval (e: exp) (env: value env) (secure: permissionList) : value =
    match e with
    | Eint n -> Int n
    | Ebool n -> Bool n
    | Estring s -> String s
    | Fun (x, body, permissions) -> Closure (x, body, env, permissions)  
    | Den i -> lookup env i (* call the lookup function on the environment env for the identifier i *)
    |If(e1,e2,e3) ->(let g = (eval e1 env secure) in
        match g with
        | Bool(true) -> eval e2 env secure
        | Bool(false) -> eval e3 env secure
        | _ -> raise (DynamicTypeError "ifthenelse guard must be a boolean")
        )
    |Let(id, e1, e2) -> 
        let xval = eval e1 env secure in
        let env1 = bind env id xval in
        eval e2 env1 secure   				 
    | Read(s) -> if superPrivilegesVerifier secure [Pread] 
                    then String("call function Read with success") 
                    else failwith("Error read permission")
    | Write(s) -> if superPrivilegesVerifier secure [Pwrite] 
                    then String("call function Write with success") 
                    else failwith("Error write permission")
    (* Open permission is used to test the case of multiple permissions, 
    in particular it need both permissions Read and Write. *)
    | Open(s) -> if superPrivilegesVerifier secure [Pwrite;Pread] 
                    then String("call function Open with success") 
                    else failwith("Error open permission")
    | Send(s) -> if superPrivilegesVerifier secure [Psend] 
                    then String("call function Send with success") 
                    else failwith("Error send permission")
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
            | Closure(arg,body,tEnv,permissions) ->
                let actualVal = eval e2 env secure  in
                let secure_extended = permissions::secure in
                  (*
                    permissions are stored on a run time structure, 
                    when happens a call to an operation thet need the stack inspection is applied the verify of the privileges.
                  *)
                let actualEnv = bind tEnv arg actualVal in
                eval body actualEnv secure_extended
            | _ -> failwith("error it isn't a closure") );;
                    