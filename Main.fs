(*
* TinyML
* Main.fs: main code
*)

module TinyML.Main

open System
open FSharp.Common
open TinyML.Ast

let parse_from_TextReader rd filename parser = Parsing.parse_from_TextReader SyntaxError rd filename (1, 1) parser Lexer.tokenize Parser.tokenTagToTokenId
    
let interpret_expr tenv venv e =
    #if DEBUG
    printfn "AST:\t%A\npretty:\t%s" e (pretty_expr e)
    #endif

    let t0,t1 = Typing.typeinfer_expr Typing.gamma0 e
    #if DEBUG
    printfn ""
    printfn "TYPE INFERENCE: "
    printfn ""

    //In presence of App there is a refresh of universal quantified variables
    //So I did a traslation of the 'greek' letter to avoid index too high.
    //In absence of App the value of controllApp will be 0 so the index will remain the same
    (* let rec controlApp e =
        match e with
        | App(e1,e2) -> 1
        | Lambda(x,None,e1) -> controlApp e1
        | Lambda(x,Some t,e1) -> controlApp e1
        | IfThenElse(e1,e2,None) -> Math.Max (controlApp e1,controlApp e2)
        | IfThenElse(e1,e2,Some e3) -> Math.Max(Math.Max(controlApp e1,controlApp e2),controlApp e3)
        | LetIn(s,e1) -> let (_,_,_,e2) = s
                         Math.Max(controlApp e1,controlApp e2)
        | Tuple(e1) -> match e1 with
                       | head :: tail -> Math.Max(controlApp(head),controlApp(Tuple(tail)))
                       | [] -> 0
        | _ -> 0

    let checkApp = controlApp e *)
    


    let rec scaleTypeVar v cont t = 
        match t with
        | TyArrow(t1,t2) -> TyArrow(scaleTypeVar v cont t1, scaleTypeVar v cont t2)
        | TyTuple ts -> TyTuple(List.map (scaleTypeVar v cont) ts)
        | TyName n -> TyName n
        | TyVar v2 -> if v2 = v then
                         TyVar cont
                      else 
                         TyVar v2

    let rec countTyVar t =
        match t with
        | TyArrow(t1,t2) -> countTyVar (t1) @ countTyVar (t2)
        | TyVar v -> [(v)]
        | _ -> []

    
    let rec convertTyVar (count : int list) (associated : int list) n t = 
          
          if n >= 0 then 
             let t = scaleTypeVar count[n] associated[n] t
             convertTyVar (count) (associated) (n - 1) t
          else t

    //Make sure the intersection between count and associated are an empty list
    let rec emptyList count associated t =
        if List.distinct(count @ associated).Length < count.Length + associated.Length then
           //Find the maximum index of count
           if count <> associated then
                let max = count.Item(count.Length - 1)
                let n = count.Length
                let newAs = [max+1 .. max+n]
                (newAs,convertTyVar (count) (newAs) (n - 1) (t))
           else 
              (count,t)
        else 
           (count,t)

    
    let count = countTyVar t0
    let count = List.distinct(count)
    let n = count.Length
    let associated = [0 .. n - 1]
    let (count,t0) = emptyList count associated t0
    let t0 = convertTyVar (count) (associated) (n - 1) (t0)
    
                        

    printfn "Inferred Type:\t%s" (pretty_ty t0)
    printfn ""

    
    #endif
    printfn "TYPE CHECKING: "


    //Convert the mutable list type in the environment for type checking
    let listTy = Typing.globalEnvironment

    //Transform Scheme Env in Type Env and pass it to the environment of Type Checking
    let rec prepareTenv l tenv =
        match l with
        | head :: tail -> let (s,Forall(i,t)) = head
                          let tenv = (s,t) :: tenv
                          prepareTenv tail tenv
        | [] -> tenv

    let tenv = prepareTenv listTy []


    let t = Typing.typecheck_expr tenv e

    let count = countTyVar t
    let count = List.distinct(count)
    let n = count.Length
    let associated = [0 .. n - 1]

    let (count,t) = emptyList (count) (associated) (t)

    let t = convertTyVar (count) (associated) (n - 1) (t)
    //let t = createScaleVariable count associated n t0 
    
    #if DEBUG
    printfn ""
    printfn "type:\t%s" (pretty_ty t)
    printfn ""
    printfn ""
    #endif
    


    printfn "EVALUATION: "

    let v = Eval.eval_expr venv e
    #if DEBUG
    printfn ""
    printfn "value:\t%s\n" (pretty_value v)
    printfn ""
    printfn ""
    #endif
    t, v

let trap f =
    try f ()
    with SyntaxError (msg, lexbuf) -> printfn "\nsyntax error: %s\nat token: %A\nlocation: %O" msg lexbuf.Lexeme lexbuf.EndPos
       | TypeError msg             -> printfn "\ntype error: %s" msg
       | UnexpectedError msg       -> printfn "\nunexpected error: %s" msg

let main_interpreter filename =
    trap <| fun () ->
        printfn "loading source file '%s'..." filename
        use fstr = new IO.FileStream (filename, IO.FileMode.Open)
        printfn "One"
        use rd = new IO.StreamReader (fstr)
        printfn "Two"
        let prg = parse_from_TextReader rd filename Parser.program
        printfn "Three"
        let t, v = interpret_expr [] [] prg
        printfn "type:\t%s\nvalue:\t%s" (pretty_ty t) (pretty_value v)

let main_interactive () =
    printfn "entering interactive mode..."
    let mutable tenv = Typing.gamma0
    let mutable venv = []
    while true do
        trap <| fun () ->
            printf "\n> "
            stdout.Flush ()
            let x, (t, v) =
                match parse_from_TextReader stdin "LINE" Parser.interactive with 
                | IExpr e ->
                    "it", interpret_expr tenv venv e

                | IBinding (_, x, _, _ as b) ->
                    let t, v = interpret_expr tenv venv (LetIn (b, Var x)) // TRICK: put the variable itself as body after the in
                    // update global environments
                    tenv <- (x, Forall([],t)) :: tenv
                    venv <- (x, v) :: venv
                    x, (t, v)

            printfn "val %s : %s = %s" x (pretty_ty t) (pretty_value v)
                
    
[<EntryPoint>]
let main argv =
    let r =
        try 
            if argv.Length < 2 then main_interactive ()
            else main_interpreter argv.[0]
            0
        with e -> printfn "\nexception caught: %O" e; 1
    Console.ReadLine () |> ignore
    r
