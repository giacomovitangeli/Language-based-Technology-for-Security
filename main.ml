exception DynamicTypeError of string (* eccezione per errore di tipo a run time *)
                                	 
type 't env = (string * 't ) list

let emptyenv = [];;

type ide = string;;

(* We model all binary operators with the type binop, so to handle them in a more concise manner inside the interpreter *)
type binop = Sum | Times | Minus | Equal | Less | Greater;;

(* tipo di permessi che possiamo trovare*)
type permissiont =
  | Pread
  | Pwrite
  | Psend;;

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
     	| Read of string
     	| Write of string
     	| Open of string
     	| Send of string;;

(* The expression can be evaluated by the interpreter to an integer, a boolean, or a closure
which is the runtime value of functions expressions. *)
type  value = Int of int
        	| Bool of bool
        	| String of string
        	| Closure of  valueFun
and valueFun = ide * exp * value env * permissiont list;;
(* a closure is made of the function name, the function argument, the body of the function
   and the symbol table with the values captured. We assume for simplicity to have only one
   parameter per function, which is similar to function abstractions in the lambda calculus
where we obtain multi parameter functions by chaining single parameter ones.*)

let rec lookup env x =
  match env with
  | [] -> failwith (x ^ " not found")
  | (ide, value)::r -> if x = ide then value else lookup r x;;

let bind (env:value env) (x: ide) (v: value) = (x,v)::env;;
 
(*type typet =
   | IntType
   | StringType
   | BoolType
   | FunType of typet * typet
   | PermissionType of permissiont
   | SetPermissionsType of permissiont
 and permissiont = ide * ide;; *)

(*let typecheck (s : string) (v : value) : bool =
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
 	_ -> failwith("Not a valid type");;*)

(* gli passo uno dei tipi consentiti dal linguaggio e ritorna una funzione evt -> bool,
   sto facendo uso del currying questa è una funzione ausiliaria che consente di effettuare
   una chiamata parametrizzata al typechecker dinamico sulla base del tipo passato come
   parametro *)
(*let check_typet (ty : typet) : value -> bool =
   match ty with
   | IntType                   	-> typecheck "int"
   | StringType                	-> typecheck "string"
   | BoolType                  	-> typecheck "bool"
   | FunType(_,_)              	-> typecheck "fun"
   | PermissionType(_)         	-> typecheck "permission"
   | SetPermissionsType(_)     	-> typecheck "setPermissions";;*)

(*let rec set_contains (s: set_val) (v: value) : bool =
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
*)
                                              	(*support functions*)

(* sono state introdotte queste 3 funzioni perchè il sec_manager è la struttura usata a run time
  per gestire la stack inspection e pensato come una lista di liste di permessi.
  Dunque si parte da una lista vuota, inizialmente a static time nessuno chiama nessuno,
  a run time quando una funzione viene invocata aggiungiamo la lista dei suoi permessi alla
  lista delle liste, il sec_manager. Questo stack continua a crescere fin tanto che non viene
  fatta la demand permission quando viene chiamata la primitiva di Read, Write, etc.. *)

let rec verify_singlePermission (pSraw:permissiont list) (pDem:permissiont) : bool =
  match pSraw with
  | [] -> false (* se arriviamo in fondo alla lista significa che non abbiamo trovato il permesso pDem *)
  | x::r1 -> if  x = pDem then true else verify_singlePermission r1 pDem;;

(* la demandPermission accetta come parametri:
   permStack: la lista di permessi della singola funzione che stiamo analizzando
   demanded: la lista di permessi da verificare, appartenenti alla funzione che ha chiamato
   una funzione privilegiata.
   Si occupa di verificare se tutto ciò che è presente nella demanded è nella lista estratta
   dallo stack.Dunque per ogni elemento in demanded viene chiamata la funzione
   verify_singlePermission.PER OTTENERE IL PERMESSO, OGNI ELEMENTO IN DEMANDED DEVE ESSERE
   IN OGNI LISTA DI PERMSTACk *)
let rec demandPermission (permStack:permissiont list) (demanded:permissiont list) : bool =
  match demanded with
  | [] -> true (* lasciato per motivi di performance nel caso di una lista di permessi vuota *)
  | x::y -> match permStack with (* x è una lista quindi... *)
	| [] -> false
	| z::u -> if verify_singlePermission permStack x then demandPermission permStack y else false;;

(* Questa funzione si occupa di fare il controllo dei privilegi. Accetta come parametro:
  permStack: una lista di liste di permessi che rappresenta i vari chiamanti ognuno con i propri
  permessi
  demanded: la lista di permessi che vogliamo verificare
  Viene verificato che ognuno dei demanded è presente all'interno del permStack, ma questo viene
  fatto solo dopo che con questa funzione si è staccato un record di lista dallo stack di tutte
  le liste, ovvero dal permStack. Se tutte le liste di liste di permessi hanno quella lista di
  permessi presentati dalla funzione che chiama l'operazione privilegiata, allora la stack
  inspection ha successo e la funzione può eseguire la funzione privilegiata. *)
let rec superPrivilegesVerifier (permStack:permissionList) (demanded:permissiont list) : bool =
  match demanded with
  | [] -> true
  | _  -> match permStack with
	| [] -> true
	| x :: y -> demandPermission x demanded && superPrivilegesVerifier y demanded;;

(* interprete *)
let rec eval (e: exp) (env: value env) (secure: permissionList) : value =
  match e with
  | Eint n -> Int n
  | Ebool n -> Bool n
  | Estring s -> String s
  | Fun (x, body, permissions) -> Closure (x, body, env, permissions)  
  | Den i -> lookup env i (* effettuo un lookup nell'ambiente env per l'identificatore i *)
  |If(e1,e2,e3) ->
  	(let g = (eval e1 env secure) in
   	match g with
   	| Bool(true) -> eval e2 env secure
   	| Bool(false) -> eval e3 env secure
   	| _ -> raise (DynamicTypeError "La guardia dell' ifthenelse deve essere di tipo booleano")
  	)
  	(*eval e2 (bind env id (eval e1 env secure)) secure*)
  |Let(id, e1, e2) -> let xval = eval e1 env secure in
  	let env1 = bind env id xval in
  	eval e2 env1 secure
    	(*
  Facciamo il controllo dei privilegi ogni qual volta si fa un azione privilegiata, quindi ogni volta che facciamo una read,
  una write o una open chiamiamo la funzione superPrivilegesVerifier che i permessi siano di Pread, Pwrite o entrambi. Se così
  non fosse falliamo.
*)   				 
  | Read(s) -> if superPrivilegesVerifier secure [Pread] then String("chiamata la read con successo") else failwith("Errore permessi read")
  | Write(s) -> if superPrivilegesVerifier secure [Pwrite] then String("chiamata la write con successo") else failwith("Errore permessi write")
  (* la Open è stata introdotta solo per testare il caso di operazione privilegiata con più permessi *)
  | Open(s) -> if superPrivilegesVerifier secure [Pwrite;Pread] then String("chiamata la open con successo") else failwith("Errore permessi open")
  | Send(s) -> if superPrivilegesVerifier secure [Psend] then String("chiamata la send con successo") else failwith("Errore permessi send")
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
	(* il sec_manager che viene usato nella eval della espressione e1 (potrebbe essere una
  	espressione della sintassi astratta) sarebbe [] passato alla eval come secondo parametro
  	di volta in volta usato come stack per contenere tutti i permessi di tutte le funzioni *)
  	(let f = eval e1 env secure in
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
   	| _ -> failwith("errore non e' una closure") );;
    	(* | _ -> failwith("errore non è una funzione che conosco");;*)
          	 

eval(    	(*Questa eval fallisce: il chiamante ha il permesso di read,
         	il chiamato ha il permesso di write e read e cerca di eseguire
         	una send che richiede i permessi di send*)
  Let("f", Fun("x", Let("g", Fun( "y", Send("1234"), [Pwrite;Pread]),	Call(Den "g",	Eint(2))), [Pread]), Call(Den "f", Eint(10)))) [] [];;



