open Source;;
open Sandbox;;
let emptyenv = [];;

(* compile with: ocamlc source.ml sandbox.ml main.ml *)

(*  
    eval succeed: caller function has read and send permissions,
    called function has the write, read and send permissions. 
    The caller want to esecute a send so need that kind of privilege.
    Else if caller function desn't have the send permission, the eval will fail. 
*)
eval(        
  Let("f",
    Fun("x",
      Let("g",
        Fun("y",
          Send("1234"),
          [Pwrite;Pread;Psend]
        ),
        Call(Den "g",Eint(2)
        )
      ),
      [Pread;Psend]
    ),
    Call(Den "f", Eint(10))
  )
) emptyenv [];;

(* execute((fun x = x+1) 5);; *)
execute(
  Let("f", 
    Fun("x", 
      Binop(Sum, Den "x", Eint 1), 
      []
    ), 
    Call(Den "f", Eint(5))
  )
) emptyenv [];;

(*
    let mysum = (fun x -> (fun y -> x + y));;
    execute(let result = mysum(5, 5));;
*)
execute(
  Let("res",
    Let("mysum",
      Fun("x",
        Fun("y",
          Binop(Sum, Den "x", Den "y"),
          [Pread]
        ),
        [Pread]
      ),
      Call(Den "mysum", Eint(5))
    ),
    Call(Den "res", Eint(5))
  )         
) emptyenv [];;

(*  
    let mypin = 12345;;
    execute(let result = myping in send(result));;

    next execute succeed, else if we reamove the send permission "Psend" 
    we cannot call the Send function so it returns error.    
*)
execute(
  Let("result", 
    Fun("send", 
      Send("mypin"), 
      [Psend]
    ),  
    Call(Den "result", Estring("12345"))
  )
) emptyenv [];;
