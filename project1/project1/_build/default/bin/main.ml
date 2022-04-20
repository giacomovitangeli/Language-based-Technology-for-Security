exception DynamicTypeError of string (* eccezione per errore di tipo a run time *)
                                	 
type 'v t = (string * 'v ) list

let emptyenv = [];;

type ide = string;;

(* We model all binary operators with the type binop, so to handle them in a more concise manner inside the interpreter *)
type binop = Sum | Times | Minus | Equal | Less | Greater;;

(* tipo di permessi che possiamo trovare*)
type permissiont =
  | Pread
  | Pwrite
  | PSend;;

(* server per memorizzare i permessi delle varie funzioni *)
type permissionList = (permissiont list) list;;

(* The language has been extended with booleans, Functions and functions calls and read, write,
open operations. These three represent a generic interaction with a system resource.
They could also be represented as particular functions but i preferred to explicitly represent
them to have more clear examples. *)
type exp = Eint of int
     	| Ebool of bool
     	| Estring of string
     	| Den of ide
     	| Binop of binop*exp*exp
     	| If of exp*exp*exp
     	| Let of ide*exp*exp
     	| Fun of ide * exp * permissiont list
     	| Call of exp*exp
	(* Costruttore per un nuovo permesso *)
	(* prende due espressioni in quanto si potrebbe decidere di definire i
  	permission in modo dinamico con if else etc... *)
     	| NewPermission of exp * exp
	(* Costruttori dell'insieme dei permessi *)
     	| EmptySetPermissions (* costruttore di un insieme di permessi vuoto *)
	(* costruttore di un insieme costituito da un solo elemento
 	`expr` del tipo `tpermission` *)                      	 
     	| SingletonPermissions of exp
 	(* costruttore di un insieme di tipo `tpermission` a partire
  	da una lista di espressioni `set_expr` *)   	 
     	| PermissionsList of set_exp
     	| Read of string
     	| Write of string
     	| Open of string
     	| Send of string
     	| Execute of ide
 	(* Operazioni di base *)
     	| Intersection of exp * exp (* intersezione di due insiemi *)
     	| Difference of exp * exp (* differenza tra due insiemi *)
	(* Operazioni aggiuntive *)
     	| Insert of exp * exp (* inserisce un elemento in un insieme *)
     	| Remove of exp * exp (* rimuove un elemento da un insieme *)
     	| Contains of exp * exp (* verifica se un insieme contiene un elemento *)
     	| IsEmpty of exp (* verifica se un insieme è vuoto *)
and set_exp =
  | Empty (* insieme di permessi vuoto *)
  (* oppure è il cons di un espressione e del resto dell'insieme dei permessi *)   	 
  | Cons of exp * set_exp;;

(* The expression can be evaluated by the interpreter to an integer, a boolean, or a closure
which is the runtime value of functions expressions. *)
type  value = Int of int
        	| Bool of bool
        	| String of string
        	| Closure of  valueFun
        	| Permission of value * value (* il costruttore di un nuovo Permission  prende una stringa per il tipo di permesso e una stringa per la risorsa *)
        	| SetPermissions of set_val (* il costruttore di SetPermissions prende un valore dell'insieme *)
        	| Unbound
and valueFun = ide * exp * value t * permissiont list
and set_val =
  | EmptyV
  | ConsV of value * set_val;;
(* a closure is made of the function name, the function argument, the body of the function
   and the symbol table with the values captured. We assume for simplicity to have only one
   parameter per function, which is similar to function abstractions in the lambda calculus
where we obtain multi parameter functions by chaining single parameter ones.*)

let rec lookup (env:'v t) x =
  match env with
  | [] -> Unbound
  | (ide, value)::r -> if x = ide then value else lookup r x;;

let bind (env:'v t) (x, v) = (x,v)::env;;
 
(*
type typet =
  | IntType
  | StringType
  | BoolType
  | FunType of typet * typet
  | PermissionType of permissiont
  | SetPermissionsType of permissiont
and permissiont = ide * ide;;
*)

let typecheck (s : string) (v : value) : bool =
  match s with
	"int" ->
  	(match v with
     	Int(_) -> true
   	| _ -> false)|
	"bool" ->
  	(match v with
     	Bool(_) -> true
   	| _ -> false)|
	"string" ->
  	(match v with
     	String(_) -> true
   	| _ -> false)|
	"permission" ->
  	(match v with (* controllo se il valore passato è di tipo Permission*)
     	Permission _ -> true
   	| _        	-> false )|
	"fun" ->
  	(match v with   (* controllo se il valore passato è di tipo funval *)
     	Closure _ -> true
   	| _ -> false )|
	"setPermissions" ->
  	(match v with   (* controllo se il valore passato è di tipo SetPermissions *)
     	SetPermissions _ -> true
   	| _ -> false )|
	_ -> failwith("Not a valid type");;

(* gli passo uno dei tipi consentiti dal linguaggio e ritorna una funzione evt -> bool,
   sto facendo uso del currying questa è una funzione ausiliaria che consente di effettuare
   una chiamata parametrizzata al typechecker dinamico sulla base del tipo passato come
   parametro *)

   (*
   let check_typet (ty : typet) : value -> bool =
  match ty with
  | IntType                   	-> typecheck "int"
  | StringType                	-> typecheck "string"
  | BoolType                  	-> typecheck "bool"
  | FunType(_,_)              	-> typecheck "fun"
  | PermissionType(_)         	-> typecheck "permission"
  | SetPermissionsType(_)     	-> typecheck "setPermissions";;
*)

let rec set_contains (s: set_val) (v: value) : bool =
  match s with
  | EmptyV -> false
  | ConsV (v', _) when v' = v -> true
  | ConsV (_,s') -> set_contains s' v;;

let rec set_union (s1: set_val) (s2: set_val) : set_val =
  match s1 with
  | EmptyV -> s2 (* se l'insieme s1 è vuoto ritorno s2 *)
  | ConsV (v1, s1') ->
  	if set_contains s2 v1 (* se l'insieme s2 contiene il valore in testa al cons *)
  	then set_union s1' s2 (* unisco solo la parte rimanente di s1 in quanto sto facendo l'unione *)
  	else set_union s1' (ConsV(v1,s2));; (* se l'insieme s2 non contiene il valore v1 allora lo aggiungo *)

let rec set_intersection (s1: set_val) (s2: set_val) : set_val =
  match s1 with
  | EmptyV -> EmptyV
  | ConsV (v1,s1') ->
  	if set_contains s2 v1 (* se l'insieme s2 contiene il valore v1 allora ... *)
  	then ConsV(v1, (set_intersection s1' s2)) (* ritorno un insieme fatto da v1 e la chiamata ricorsiva, in quanto l'intersezione prende i valori comuni *)
  	else set_intersection s1' s2;; (* se il valore v1 non è comune ai 2 insiemi allora lo scarto *)

let rec set_difference (s1: set_val) (s2: set_val) : set_val =
  match s1 with
  | EmptyV -> EmptyV
  | ConsV (v1,s1') ->
  	if set_contains s2 v1 (* se l'insieme s2 contiene il valore v1 allora ... *)
  	then set_difference s1' s2 (* scarto il valore v1 e continuo facendo una chiamata ricorsiva *)
  	else ConsV(v1, (set_difference s1' s2));; (* se il valore v1 non è in s2 allora lo mantengo *)

let rec set_remove (s: set_val) (v: value) : set_val =
  match s with
  | EmptyV -> EmptyV
  | ConsV (v',s') when v' = v -> s' (* ho trovato l'elemento che volevo rimuovere *)
  | ConsV (v',s') -> ConsV(v', set_remove s' v);; (* l'elemento v' non è quello che voglio rimuovere dunque lo mantengo *)


(* interprete *)
let rec eval (e: exp) (env: value t) (secure: permissionList) : value =
  match e with
  | Eint n -> Int n
  | Ebool n -> Bool n
  | Estring s -> String s
  | Fun (x, body, permissions) -> Closure (x, body, env, permissions)  
  | Den i -> lookup env i (* effettuo un lookup nell'ambiente env per l'identificatore i *)
  |If(e1,e2,e3) ->
  	let g = (eval e1 env secure) in
  	(match ( typecheck "bool" g, g ) with
   	| (true, Bool(true)) -> eval e2 env secure
   	| (true, Bool(false)) -> eval e3 env secure
   	| _ -> failwith "If guard must evaluate to a boolean")
  	(*eval e2 (bind env id (eval e1 env secure)) secure*)
  |Let(id, e1, e2) -> let xval = eval e1 env secure in
  	let env1 = bind env id xval in
  	eval e2 env1 secure
  |Binop (op,e1,e2) -> (
  	let e1 = eval env e1 secure in
  	let e2 = eval env e2 secure in
  	match op,e1,e2 with
  	| Sum,Int n1, Int n2 -> Int (n1+n2)
  	| Times,Int n1, Int n2 -> Int (n1 * n2)
  	| Minus,Int n1, Int n2 -> Int (n1-n2)
  	| Equal, Int n1, Int n2 -> Bool (n1 = n2)
  	| Less, Int n1, Int n2 -> Bool (n1 < n2)
  	| Greater, Int n1, Int n2 -> Bool (n1 > n2)
  	| _ -> failwith "Invalid binary expression")
  | Call(e1, e2) ->
	(* il sec_manager che viene usato nella eval della espressione e1 (potrebbe essere una
  	espressione della sintassi astratta) sarebbe [] passato alla eval come secondo parametro
  	di volta in volta usato come stack per contenere tutti i permessi di tutte le funzioni *)
  	let f = eval e1 env secure in
  	match f with
  	| Closure(arg,body,tEnv,permissions) ->
   		 (* i privileges sono i permessi attuali della funzione *)
(*
  metterlo nella dichiarazione ha il problema che se una funzione viene dichiarata ma non viene
  chiamata i suoi privilegi vengono messi lo stesso sul security manager e quindi influiscono
  con i permessi delle altre funzioni che poi vengono invece chiamate.
  Dato che una funzione quando fa la call il suo record di attivazione viene messo sullo stack
  solo al momento della call, molto probabilmente deve avvenire nella call l'aggiunta del security
  manager però si ha il problema di sotto dell'esempio con le funzioni innestate in cui viene
  valutata prima quella più interna e poi quella più esterna. Abbiamo deciso di fare delle
  primitive già pronte che usano la stack inspection è più controllabile perchè lasciare i
  permessi direttamente via codice non è facile.
*)

        	(* secure è quello che nelle funzioni ausiliarie è stato chiamato permStack *)
      	let actualVal = eval e2 env secure  in
      	let secure_extended = permissions::secure in
        	(*
          	i permessi vengono salvati sulla struttura a run time che si occupa di memorizzarli poi, quando ci sarà
          	una chiamata ad una operazione che richiede la stack inspection viene fatto il controllo (vedere Read, Open e Write)
        	*)
      	let actualEnv = bind tEnv arg actualVal in
      	eval body actualEnv secure_extended
  	| _ -> failwith("errore non e' una closure")
  	| Read(s) -> if superPrivilegesVerifier secure [Pread] then String("chiamata la read con successo") else failwith("Errore permessi read")
  	| Write(s) -> if superPrivilegesVerifier secure [Pwrite] then String("chiamata la write con successo") else failwith("Errore permessi write")
  (* la Open è stata introdotta solo per testare il caso di operazione privilegiata con più permessi *)
  	| Open(s) -> if superPrivilegesVerifier secure [Pwrite;Pread] then String("chiamata la open con successo") else failwith("Errore permessi open")
  	| NewPermission (action, resource) -> let v1 = eval action env in
      	let v2 = eval resource env in
      	if typecheck "string" v1 (* controllo che entrambi i parametri siano di tipo stringa, si potrebbe generalizzare considerando che potrebbe
                                                                    	trattarsi di qualsiasi oggetto (socket, connessione a un db, etc...) *)
      	then Permission (v1, v2)
      	else raise (DynamicTypeError "Il tipo dell'action del permission deve essere di tipo string")   
	(* Costruttori dell'insieme di permessi *)
  	| EmptySetPermissions -> SetPermissions(EmptyV) (* costruttore di un insieme di permessi vuoto di tipo `ttype` *)
  	| SingletonPermissions exp -> (* costruttore di un insieme di permessi costituito da un solo elemento `expr` del tipo `ttype` *)
      	let v = eval exp env in (* valuto l'espressione costituente l'insieme nell'ambiente *)
      	if typecheck "permission" v
      	then SetPermissions(ConsV(v,EmptyV))
      	else raise (DynamicTypeError "Il tipo del singleton non corrisponde con quello del valore") 	 
  	| PermissionsList expr_list -> (* costruttore di un insieme di tipo `typet` a partire da una lista di espressioni (un cons di espressioni o un espressione vuota) `set_expr` *)
      	let set_v = set_eval expr_list env in (* valuto la lista delle espressioni passate per trasformarla in una lista di valori dell'insieme *)
                                                    	(* viene fatto anche il controllo dei tipi, grazie al t passato come parametro *)
      	SetPermissions(set_v)
  	| Intersection (set_e1, set_e2) -> (* intersezione di due insiemi *)
      	(
        	match eval set_e1 env, eval set_e2 env with
        	| SetPermissions(set_v1), SetPermissions(set_v2) ->
            	SetPermissions(set_intersection set_v1 set_v2) (* ritorno un SetPermissions di tipo t1=t2 e l'intersezione dei valori *)
        	| _, _ -> raise(DynamicTypeError "I tipi degli insiemi che si vogliono intersecare non combaciano")                       	 
      	)
  	| Difference (set_e1, set_e2) -> (* differenza di due insiemi *)
      	(
        	match eval set_e1 env, eval set_e2 env with
        	| SetPermissions(set_v1), SetPermissions(set_v2) -> (* se i tipi dei 2 insiemi combaciano posso fare la differenza *)
            	SetPermissions(set_difference set_v1 set_v2) (* ritorno un SetPermissions di tipo t1=t2 e la differenza dei valori *)
        	| _, _ -> raise(DynamicTypeError "I tipi degli insiemi di cui si vuole la differenza non combaciano")                       	 
      	)
	(* Operazioni aggiuntive *)
  	| Insert (elem, set_e) -> (* inserisce un elemento in un insieme *)
      	(
        	match eval set_e env with (* valuto l'espressione che forma l'insieme... *)
        	| SetPermissions(set_v) ->  (* estraggo il tipo e i valori dell'insieme *)
            	let v = eval elem env in (* valuto l'elemento da aggiungere ... *)
            	if typecheck "permission" v && not (set_contains set_v v) (* il tipo dell'insieme e dell'elemento valutato coincidono
                                                                                                          	e l'insieme valutato non contiene il valore dell'elemento ...*)
            	then SetPermissions(ConsV(v, set_v)) (* aggiungo l'elemento all'insieme *)
            	else SetPermissions(set_v) (* altrimenti ritorna l'insieme come prima *)
        	| _ -> raise(DynamicTypeError "Insert: ha fallito perchè non è stata chiamata su un insieme")                       	 
      	)
  	| Remove (elem, set_e) -> (* rimuove un elemento in un insieme *)
      	(
        	match eval set_e env with (* valuto l'espressione che forma l'insieme... *)
        	| SetPermissions(set_v) ->  (* estraggo il tipo e i valori dell'insieme *)
            	let v = eval elem env in (* valuto l'elemento da aggiungere ... *)
            	if typecheck "permission" v (* il tipo dell'insieme e dell'elemento valutato da rimuovere coincidono *)                                                          	 
            	then SetPermissions(set_remove set_v v) (* rimuovo l'elemento dall'insieme *)
            	else SetPermissions(set_v) (* altrimenti ritorna l'insieme come prima *)
        	| _ -> raise(DynamicTypeError "Remove: ha fallito perchè non è stata chiamata su un insieme")                       	 
      	)
  	| Contains (elem, set_e) -> (* verifica se un insieme contiene un elemento *)
      	(
        	match eval set_e env with
        	| SetPermissions(set_v) -> (* estraggo il tipo e i valori dell'insieme... *)
            	let v = eval elem env in (* valuto l'argomento da aggiungere *)
            	if typecheck "permission" v (* il tipo dell'insieme e dell'elemento valutato da verificare coincidono... *)
            	then Bool (set_contains set_v v)
            	else raise(DynamicTypeError "Contains: ha fallito perchè i tipi dell'insieme e dell'elemento non combaciano")
        	| _ -> raise(DynamicTypeError "Contains: ha fallito perchè non è stata chiamata su un insieme")  
      	)
  	| IsEmpty set_e -> (* verifica se un insieme è vuoto *)
      	(
        	match eval set_e env with
        	| SetPermissions(set_v) ->
            	if set_v = EmptyV
            	then Bool true
            	else Bool false
        	| _ -> raise(DynamicTypeError "Impossibile chiamare IsEmpty su qualcosa diverso dall'insieme")   
      	)
and set_eval (set_e: set_expr) (env: value t) : set_val =
  match set_e with
  | Empty -> EmptyV (* se l'insieme è vuoto ritorna l'evaluation type dell'insieme vuoto *)
  | Cons (e, set_e') -> (* decido di valutare prima il primo valore in testa così da evitare di chiamare la set_eval sul resto dell'insieme che è molto più grande in genere *)
  	let v = eval e env in
  	if typecheck "permission" v (* controllo il tipo *)
  	then
    	let set_v' = set_eval set_e' env in (* poi valuto il resto dell'insieme *)
    	if set_contains set_v' v (* se il nuovo valore calcolato è contenuto nel resto dell'insieme calcolato *)
    	then set_v'          	(*... non lo aggiunge dunque evito i duplicati! *)
    	else ConsV (v, set_v')   (*... altrimenti lo aggiunge tramite il cons *)
  	else raise(DynamicTypeError "Il tipo dell'insieme generato con of non corrisponde con quello del valore");;





