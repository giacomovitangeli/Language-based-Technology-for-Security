open Source;;
open Sandbox;;
let emptyenv = [];;

(* compile with ocamlc source.ml main.ml*)

(*
    eval succeed: caller function has read and send permissions,
    called function has the write, read and send permissions.
    The caller want to execute a send so need that kind of privilege.
    Else if caller function doesn't have the send permission, the eval will fail.
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

(*
    in the next lines we prove the following code: execute((fun x = x+1) 5);;
*)
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
    in the next lines we prove the following code:
    let mysum = (fun x -> (fun y -> x + y));;
    execute(let result = mysum(5, 5));;
    in the local environment we define the function mysum with some required permissions,
    when we call the function execute we try to use the local function define before.
    If the caller have the permissions we obtain the correct result, otherwise,
    the execute raise error.
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
    execute(let result = mypin in send(result));;

    we define the local variable mypin; next the function execute try to send mypin,
    if the send have the permission to send the function succeed, else (without the
    permission "Psend") the execute raise error.
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
