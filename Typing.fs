(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

type subst = (tyvar * ty) list

// TODO implement this

//Unification algorithm

//U(t1,t2), where t1 and t2 are two type names, if they are equal no substitution, else error
//U(variable,t) = variable is substituted by t if the variable doesn't belong to t
//U(t,variable) = variable is substituted by t if the variable doesn't belong to t
//U(t1->t2,t3->t4) = U(t1,t3) o U(t2,t4)

let rec unify (t1 : ty) (t2 : ty) : subst =
    //The first step: check the two Types
    match t1,t2 with
       | TyName tn1, TyName tn2 -> if tn1 = tn2 then [] else type_error "unify: cannot unify %s with %s" tn2 tn1
       | TyArrow (c1,c2) , TyArrow(d1,d2) -> unify c1 d1 @ unify c2 d2
       //They allow unification in all cases except if there are occurrences of tv in tn
       | tn,TyVar tv -> if not (Set.contains tv (freevars_ty tn)) then [(tv,tn)] else type_error "Cannot unify %s with %s" (pretty_ty tn) (pretty_ty (TyVar tv))
       | TyVar tv,tn -> if not (Set.contains tv (freevars_ty tn)) then [(tv,tn)] else type_error "Cannot unify %s with %s" (pretty_ty tn) (pretty_ty (TyVar tv))       
       | _ -> type_error "Unify cannot unify %s with %s" (pretty_ty t1) (pretty_ty t2) 

// TODO implement this

//Given a type t and a subst s
//1) if t is a TyName return the type t
//2) if t is a TyVar, I check the index of each subst and if it is equal to the TyVar then I return the type of the substitution, otherwise the type t
//3) if t is a TyArrow, I return a TyArrow with the application of the subst on the two elements t1 and t2 in an inductive way
//4) if t is a TyTuple then I apply a map function to each element of the tuple
let apply_subst (t : ty) (s : subst) : ty = 
    let rec apply_subst_item sub t =
        //tv is the tyvar and t0 is a ty
        let tv,t0 = sub
        match t with
        | TyName _ -> t
        | TyVar ttv -> if ttv = tv then t0 else t
        | TyArrow(t1,t2) -> TyArrow(apply_subst_item sub t1, apply_subst_item sub t2)
        | TyTuple(ts) -> TyTuple(List.map (apply_subst_item sub) ts)

    //Use List.foldBack to perform a calculation in a list which differs in the order in which
    //the list is traversed.
    //this operation provide an additional parameter called the accumulator which holds information
    //through the calculation.
    List.foldBack (apply_subst_item) s t

// TODO implement this

//This function compose subst lists with only one type for an index of variable
//In the case I have [(0,TyVar 0)] and [(0,TyName "int")] I got [(0,TyName "int")] in the final subst

let compose_subst (s1 : subst) (s2 : subst) : subst = 
    //I need to delete the duplicates 
    //The substitution I got is the element that are duplicates in s1 and s2
    


    let rec deleteDuplicate s1 s2 s1Complete s2Complete =
        match s1 with
        | (i,t) :: tail -> 
                          match s2 with
                          | (i2,t2) :: tail1 -> 
                                              if i2 = i then
                                                 match t,t2 with
                                                 | TyVar v,typ -> (i2,t2) :: deleteDuplicate s1 tail1 s1Complete s2Complete
                                                 | typ, TyVar v -> (i,t) :: deleteDuplicate s1 tail1 s1Complete s2Complete
                                              
                                                 | ty1,ty2 -> if ty1 = ty2 then
                                                                 (i,t) :: deleteDuplicate s1 tail1 s1Complete s2Complete
                                                              else 
                                                                 type_error "Compose_Substitution Error: Conflict in substitution %O with %O" (pretty_ty t) (pretty_ty t2)
                                              else 
                                                 deleteDuplicate s1 tail1 s1Complete s2Complete

                          | [] -> deleteDuplicate tail s2Complete s1Complete s2Complete

        | [] -> []

    let dupl = deleteDuplicate s1 s2 s1 s2

        //Now I add the remained substitutions that are not duplicated

    //I calculate a list of index
    let rec calculateIndex s = 
        match s with
        | head :: tail -> let (i,t) = head
                          i :: calculateIndex tail

        | [] -> []

    //I create a list of index tyvar duplicated
    let listIndex = calculateIndex dupl

    //Function to determine if a number is contained in a list of number
    let containsNumber number list = List.exists (fun elem -> elem = number) list

    let comp = s1 @ s2

    //I got a list of not duplicates
    let rec notDuplicate s duplicate= 
        match s with
        | head :: tail -> let (i,t) = head
                          if containsNumber i duplicate then
                             notDuplicate tail duplicate
                          else 
                             (i,t) :: notDuplicate tail duplicate

        | [] -> []

    let notdupl = notDuplicate comp listIndex 

    List.distinct notdupl @ dupl 

    //List.distinct s1 @ s2      
           

// type inference

//Environment prepoulated

//For example + is an operator of type int -> int -> int because when I do
//BinOp (item1,'+',item2) , App(App('+',item1),item2)
//I step: App(App(int -> int -> int, int), int)
//II step: App(int -> int, int) 
//III step: result: int

//I used monomorphic operators, so I defined a +. for float

let gamma0 = [
    ("+", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "int"))))
    ("-", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "int"))))
    ("*", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "int"))))
    ("/", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "int"))))
    ("%", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "int"))))
    ("+.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("-.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("*.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("/.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("%.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    (">", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "bool"))))
    (">=", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "bool"))))
    ("<", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "bool"))))
    ("<=", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "bool"))))
    ("<>", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "bool"))))
    ("=", Forall([],TyArrow (TyName "int", TyArrow (TyName "int", TyName "bool"))))
    (">.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    (">=.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("<.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("<=.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("<>.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("=.", Forall([],TyArrow (TyName "float", TyArrow (TyName "float", TyName "float"))))
    ("not", Forall([],TyArrow (TyName "bool", TyName "bool")))
    ("and", Forall([],TyArrow(TyName "bool",TyName "bool")))
    ("or", Forall([],TyArrow(TyName "bool",TyName "bool")))
    //("-", Forall([],TyArrow (TyName "int", TyName "int")))
]

//MUTABLE VARIABLES


//Var specify the index of the variables that must be added to the environment and the final substitution
let mutable (var : tyvar) = 0

//Global Environment where I can get the types of variables for the ty environment of type checking
let mutable globalEnvironment  = gamma0

//SUPPORT FUNCTION

//Function to print a list of substitution, for each element
let rec flowSub sub =
    match sub with
    | head :: tail -> printfn "ELEMENT: %O" head
                      flowSub tail
    | [] -> ()

//Function to apply the substitution to the environment

let rec updateEnvironment env sub =

    match env with
    | head :: tail -> let (s,Forall(i,t)) = head
                      (s,Forall(i,apply_subst (t) (sub))) :: updateEnvironment tail sub

                                                  
    | [] -> []


// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
     

    match e with
    //Base cases, Axiom of the type inference rules
    | Lit(LInt _) -> (TyInt,[])
    | Lit(LFloat _) -> (TyFloat,[])
    | Lit(LBool _) -> (TyBool,[])
    | Lit(LString _) -> (TyString,[])
    | Lit(LChar _) -> (TyChar,[])
    | Lit(LUnit _) -> (TyUnit,[])

    | Var(x) -> //Verify x is present in the environment
                
                //This function find is used to verify if x is present in the environment
                //If present return the type of x
                //else return an error because the variable is not bounder in the environment
                let rec find e v =
                    match e with
                    | x :: xs -> //Flow the environment and verify if name is equal to x and return the type associated
                                 let (name,Forall(tv,va)) = x
                                 if name = v then
                                    let final_type = va
                                    let final_subst = []
                                    (final_type,final_subst)
                                 else 
                                    find xs v
                    | [] -> //If the environment doesn't contain the variable, it is an undeclared Variable
                            unexpected_error "The variabile %O is not bounded to the environment!" x

                
                find env x
    
      //INDUCTIVE CASES

    | Lambda(x,Some t,e1) -> //Annotated Lambda Type Inference
                             
                             //Premises
                             //X : t
                             //e1 : T2
                             
                             //Final Result
                             //Lambda(x,Some t,e1) = t -> T2
                             
                             //I. Bind the variable in the environment
                             let T1 = t
                             let env = (x,Forall([],T1)) :: env
                             globalEnvironment <- (x,Forall([],T1)) :: globalEnvironment
                             
                             //II. Infer the expression e1
                             let (t_infer,s_infer) = typeinfer_expr (env) (e1)

                             //III. apply the subst s_infer to the type inferred
                             let app2 = apply_subst (t_infer) (s_infer)

                             //IV. Define the final type, the final_subst and apply the subst to final type
                             let final_type = TyArrow(t,app2)
                             let final_subst = s_infer
                             let final_type = apply_subst (final_type) (final_subst)


                             globalEnvironment <- updateEnvironment globalEnvironment final_subst  
                             //V. Return final type and final subst
                             (final_type,final_subst)
    
    
                             

    | Lambda(x, None, e1) -> //Unnanotated Lambda Type Inference
                             
                             //Premises
                             //X : T1
                             //e1 : T2
                             
                             //Final Result
                             //Lambda(x,None,e1) = T1 -> T2

                             //I. Bind the variable x in the environment
                             //In case of unannotated lambda I use a TyVar var
                             //I create a new fresh variable

                             let T1 = TyVar var
                             let env = (x,Forall([],T1)) :: env
                             globalEnvironment <- (x,Forall([],T1)) :: globalEnvironment
                             var <- var+1


                             //II. Infer the expression e1
                             let (t_infer,s_infer) = typeinfer_expr (env) (e1)
                             
                             
                             //III. apply the subst s_iinfer to T1 to verify if I discover something
                             //about the variable x
                             //apply s_infer also to app2 
                             let app1 = apply_subst (T1) (s_infer)
                             let app2 = apply_subst (t_infer) (s_infer)
                             
                             //IV. Define the Final Subst and the Final Type
                             //let final_subst = compose_subst (s_infer) (final_subst)
                             let final_subst = s_infer
                             let final_type = TyArrow(app1,app2)
                             let final_type = apply_subst (final_type) (final_subst)

                             //V. Update Environment with the type inferred for variable x
                             
                             globalEnvironment <- updateEnvironment globalEnvironment final_subst 
                             
                             //VI. Return the final_type and final_subst
                             (final_type,final_subst)
    
                            

    | IfThenElse(e1,e2,None) ->   //ifThenElse Type Inference Rule
                             
                                 //Premises
                                 //e1 : Bool
                                 //e2 : T1
                                 //e3 : Unit
                             
                                 //Final Result
                                 //IfThenElse(e1,e2,None) = T1
    
                                   let T1 = TyName "bool"

                                   //I. Infer the expression e1
                                   let (t_infer1,s_infer1) = typeinfer_expr (env) (e1)

                                   //II. Check with unification if the inferred type is
                                   //compatible with TyName "bool"
                                   let join1 = unify (T1) (t_infer1)
                                   let join1 = compose_subst (join1) (s_infer1)

                                   //III. Apply subst to the Local Environment
                                   let env = updateEnvironment env join1
                                   
                                   //IV. Infer the expression e2
                                   let (t_infer2,s_infer2) = typeinfer_expr (env) (e2)

                                   //V. compose all substitution and apply to the new inferred type
                                   let join2 = compose_subst (s_infer2) (join1)
                                   let app2 = apply_subst (t_infer2) (join2)
                                   

                                   //VI. the type of the 'else' part is Unit
                                   let app3 = TyUnit
                                    
                                   //VII. return the final type and the final substitution
                                   let final_type = app2
                                   let final_subst = join2

                                   globalEnvironment <- updateEnvironment globalEnvironment final_subst

                                   (final_type,final_subst)
    
                              

    | IfThenElse(e1,e2,Some e3) ->  //ifThenElse Type Inference Rule
                             
                                    //Premises
                                    //e1 : Bool
                                    //e2 : T
                                    //e3 : T
                             
                                    //Final Result
                                    //IfThenElse(e1,e2,None) = T
    
                                   let T1 = TyName "bool"

                                   //I. Infer the expression e1
                                   let (t_infer1,s_infer1) = typeinfer_expr (env) (e1)

                                   //II. Check with unification if the type inferred is compatible
                                   //with TyName "bool"
                                   let join1 = unify (T1) (t_infer1)
                                   let join1 = compose_subst (join1) (s_infer1)

                                   let env = updateEnvironment env join1

                                   //III. Infer the expression e2
                                   let (t_infer2,s_infer2) = typeinfer_expr (env) (e2)
                                   
                                   //IV. Compose all substitution and apply them on the new inferred type
                                   let join2 = compose_subst (s_infer2) (join1)
                                   let app2 = apply_subst (t_infer2) (join2)
                                   let env = updateEnvironment env join2

                                   //V. Infer the expression e3
                                   let (t_infer3,s_infer3) = typeinfer_expr (env) (e3)

                                   //VI. Compose all substitutions and apply to the new inferred type
                                   let join3 = compose_subst (join2) (s_infer3)
                                   let app3 = apply_subst (t_infer3) (join3)

                                   //VII. Unify the two types of if-else and check with unification
                                   //if compatible.
                                   //Then apply the substitution to app2 and app3
                                   let join4 = unify (app2) (app3)
                                   let join4 = compose_subst (join3) (join4)
                                   let app2 = apply_subst (app2) (join4)
                                   let app3 = apply_subst (app3) (join4)

                                   //VIII. Define the final type and the final substitution
                                   let final_type = app2
                                   let final_subst = join4

                                   //IX: Update Environment


                                   globalEnvironment <- updateEnvironment globalEnvironment final_subst
                                    
                                   //X. return the final type and the final substitution
                                   (final_type,final_subst)
                                                 
                                   
    | App(e1,e2) -> //APP Type Inference Rule
                    
                    //PREMISES
                    //e1 : T1 -> T2
                    //e2 : T1
                    
                    //Final Result
                    //APP(e1,e2) = T2


                    //let env = globalEnvironment
                    //I. Infer the expression e1


                    let (t_infer1,s_infer1) = typeinfer_expr (env) (e1)


                    //II. In the case I have a TyVar as t_infer1, I transform it in an Arrow Type
                    //The arrow type can be a domain and a codomain of different types
                    let rec transform t_infer1 s_infer1 = 
                        match t_infer1 with
                        | TyArrow(t1,t2) -> (t_infer1,s_infer1)
                        | TyVar v -> let t_infer1 = TyArrow(TyVar var,TyVar (var+1))
                                     var <- var+1
                                     var <- var+1
                                     let s_infer1 = [(v,t_infer1)]
                                     (t_infer1,s_infer1)
                        | TyTuple ts -> (t_infer1,s_infer1)
                        | TyName n -> (t_infer1,s_infer1)

                    let (t_infer1,s_infer1) = transform (t_infer1) (s_infer1)

                    //III. Get Type Variables to guarantee polymorphism
                    //The goal is taking the index of variables universal quantified and
                    //refresh them
                    //For example if I have 
                    //let f = fun x -> fun y -> fun z -> (x, y - 1, z) in (f 11 22 33, f "Hello" 10 false)
                    //x and z are universal quantified and in the first call I assign the two variables
                    //with TyName "int"
                    //in the second call I assign the two variables with TyName "string" and TyName "bool"
                    
                    let rec getTV env e1= 
                        match e1 with
                        | Var(x) -> 
                                    let rec mEnv env x = 
                                        match env with
                                        | head :: tail -> let (s,Forall(i,t)) = head
                                                          
                                                          if s = x then
                                                             i
                                                          else 
                                                             getTV tail e1

                                        | [] -> []
                                        
                                    mEnv env x

                        | _ -> []


                    let i = getTV env e1

                    //IV. REFRESH VARIABLES
                    //This part is used to guarantee polimorphism
                    //If In the environment I have (f,Forall([0],TyArrow(TyVar 0, TyName "int"))
                    //It creates new Type Variables that must be unified with new Types
                    //Generate TyArrow(TyVar 2, TyName "int") and the new list of variables universal quantified 
                    //[2]

                    //For Example If I have two function calls
                    //f 0
                    //f "Hello"
                    //I generated different type variables so I can work with different types
                    let rec createFreshVariable t i s  =
                        match i with
                        | head :: tail -> 
                                          
                                          let un = unify (TyVar var) (TyVar head)
                                          let s = compose_subst (s) (un)
                                          var <- var+1
                                          createFreshVariable t tail s 
                                            
                        | [] ->  apply_subst (t) (s)
                                 

                    let t_infer1 = createFreshVariable t_infer1 i []


                    //V. Apply the substitution to the type and to the environment 
                    let join1 = s_infer1
                    let app1 = apply_subst (t_infer1) (join1)
                    let env = updateEnvironment (env) (join1)

                    //VI. Infer the expression e2
                    let (t_infer2,s_infer2) = typeinfer_expr (env) (e2)
                     
                    //VII. Compose all substitution and apply it on the new inferred type
                    let join2 = compose_subst (s_infer2) (join1)
                    let app2 = apply_subst (t_infer2) (join2)


                    //VII. I did a function to manage this situation:
                    //In the case fun x -> x +. 4
                    //x will be TyName "float"
                    //4 will be TyName "int", but it must be TyName "float"
                    let rec checkFloatInt t1 t2 = 
                        match t1,t2 with
                        | TyName "float", TyName "int"
                        | TyName "int", TyName "float" -> (TyName "float",TyName "float")
                        | _ -> (t1,t2)

                    
                    let (t_infer2,newT2) = checkFloatInt (t_infer2) (app2)
                    
                    
                    //VIII. Check the type1 is an Arrow Type and return the two components of
                    //the arrow


                    let rec checkArrow t_infer1  = 
                        match t_infer1 with
                        | TyArrow(t1,t2) -> (t1,t2)
                        | _ -> type_error "The left part must be a domain!"
                               
                    let (t1,t2) = checkArrow app1

                    //IX. Unify the t1 with the second inferred type
                    let join3 = unify (t1) (t_infer2)
                    let join3 = compose_subst (join3) (join1)
                    let join3 = compose_subst (join3) (join2)
                    
                    
                    //X. Apply the substitution join3 to t2
                    let t2 = apply_subst (t2) (join3)
                    //XI. Return the final type and the final substitution
                    let final_type = t2
                    let final_subst = join3

                    //XII: Update Global Environment


                    globalEnvironment <- updateEnvironment globalEnvironment final_subst
                    

                    (final_type,final_subst)


    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
           //BinOp type inference rule
           //e1 : TyName int
           //e2 : TyName int
           
           //Final Result
           //BinOp(e1,'op',e2) -> TyName "int"


           //I have decided to treat operators as functions
           //so I can apply currification without having to define functions natively
            typeinfer_expr env (App(App(Var op,e1),e2))
           

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
            //BinOp type inference rule
            //e1 : TyName int
            //e2 : TyName int
           
            //Final Result
            //BinOp(e1,'op',e2) -> TyName "bool"
            

            typeinfer_expr env (App(App(Var op,e1),e2))

    | BinOp (e1, ("+." | "-." | "/." | "%." | "*." as op), e2) ->
           //BinOp type inference rule
           //e1 : TyName float
           //e2 : TyName float
           
           //Final Result
           //BinOp(e1,'op',e2) -> TyName "float"

            typeinfer_expr env (App(App(Var op,e1),e2))
           

    | BinOp (e1, ("<." | "<=." | ">." | ">=." | "=." | "<>." as op), e2) ->
            //BinOp type inference rule
            //e1 : TyName float
            //e2 : TyName float
           
            //Final Result
            //BinOp(e1,'op',e2) -> TyName "bool"
            

            typeinfer_expr env (App(App(Var op,e1),e2))

    | Let (x, tyo, e1, e2) -> 

            //LET TYPE INFERENCES RULES

            //Premises: 
            //x : tyo
            //e1 : T1

            //FINAL RESULT
            //e2 : T2 {e1 : T1, x: tyo}

            //Check if tyo is defined or not

            match tyo with

            | Some t -> //I. Binding the x in the environment
                        let T1 = t
                        let env = (x,Forall([],T1)) :: env
                        globalEnvironment <- (x,Forall([],T1)) :: globalEnvironment
                        
                        //II. Infer the expression e1
                        let (t_infer1,s_infer1) = typeinfer_expr (env) (e1)
                        
                        //III. Apply the substitution to the inferred type
                        let join2 = s_infer1
                        let app2 = apply_subst (t_infer1) (join2)

                        //IV. Update the environment so I can use the function in the 
                        //second expression after IN
                        //I Quantified Universally the Type Variables

                        let rec updateEnv app1 env x= 
                          match env with
                          | head :: tail -> let (s,Forall(i,t)) = head
                                            if s = x then
                                               (s,Forall(Set.toList(freevars_ty(app1)),app1)) :: updateEnv (app1) (tail) (x)
                                            else 
                                               head :: updateEnv (app1) (tail) (x)
                                            
                          | [] -> [] 

                        let env = updateEnv app2 env x

                        let final_subst_e1 = join2

                        //V. Infer the expression e2
                        let (t_infer2,s_infer2) = typeinfer_expr (env) (e2)


                        //VI. Compose all substitution and apply it on the new inferred type
                        let join3 = compose_subst (s_infer1) (s_infer2)
                        let app3 = apply_subst (t_infer2) (join3)

                        //VII. Define the final type and the final_subst
                        let final_type = app3
                        let final_subst = join3

                        //VIII. Update Environment
                        globalEnvironment <- updateEnvironment globalEnvironment final_subst_e1

                        //IX. Return the final type and the final subst
                        (final_type,final_subst)

            | None ->
                      //I. Define a new fresh variable and bind x in the environment
                      let T1 = TyVar var

                      //This variable store the starting index of tyvar in this specific let operation
                      //So I avoid to quantify universally TyVar of index less or equal to that index.
                      let localVar = var

                      //let env = globalEnvironment
                      let env = (x,Forall([],T1)) :: env
                      globalEnvironment <- (x,Forall([],T1)) :: globalEnvironment
                      var <- var+1

                      //II. Infer the expression e1
                      let (t_infer1,s_infer1) = typeinfer_expr (env) (e1)
                                       
                      
                      //III. Apply the substitution to the inferred type
                      let join1 = s_infer1
                      //let app1 = apply_subst (T1) (join1)
                      let app2 = apply_subst (t_infer1) (join1)


                      //IV. Update the environment so I can use the function x in the second
                      //expression after IN
                      //I quantified universally the type variables
                      let rec updateEnv app1 env x lv = 
                          match env with
                          | head :: tail -> let (s,Forall(i,t)) = head
                                            if s = x then
                                                 let freeVars = Set.toList(freevars_ty(app1))

                                                 //Without this part in the case of
                                                 //let f = fun x -> fun y -> let g = fun z -> (x, z + 1) in let h = fun t -> if x < 2 then t else y in g
                                                 //The variable x would be quantified universally in g
                                                 let rec deleteBoundedVar freevars lv = 
                                                     match freevars with
                                                     | h :: t -> if h <= lv then 
                                                                    deleteBoundedVar t lv
                                                                 else 
                                                                    h :: deleteBoundedVar t lv
                                                                    
                                                     | [] -> []
                                                 let freeVars = deleteBoundedVar freeVars lv
                                                 (s,Forall(freeVars,app1)) :: updateEnv (app1) (tail) (x) (lv)
                                            else 
                                               head :: updateEnv (app1) (tail) (x) (lv)
                          | [] -> [] 

                      let env = updateEnv app2 env x localVar

                      let final_subst_e1 = join1
                      
                      

                      //V. Infer the expression e2


                      let (t_infer2,s_infer2) = typeinfer_expr (env) (e2)
                      //VI. Compose all substitution and apply the substitution to the new inferred type
                      let join3 = compose_subst (join1) (s_infer2)
                      let app3 = apply_subst (t_infer2) (join3)

                      //VII. Define the final type and the final substitution
                      let final_type = app3
                      let final_subst = join3

                      //VIII. Update Global Environment
                      globalEnvironment <- updateEnvironment  globalEnvironment final_subst_e1

                      //IX. Return the final type and the final substitution
                      (final_type,final_subst)

    | LetRec (f, Some tf, e1, e2) ->
    
                      //LET REC TYPE INFERENCES RULES

                      //Premises: 
                      //f : tf
                      //e1 : T2 {f : Tf}

                      //FINAL RESULT
                      //e2 : T2 {e1 : T2, f: tf}

                      //I. Binding f to the environment
                      let T1 = tf
                      let env = (f,Forall([],T1)) :: env
                      globalEnvironment <- (f,Forall([],T1)) :: globalEnvironment
                      
                      //II. Infer the expression e1
                      let (t_infer1,s_infer1) = typeinfer_expr (env) (e1)

                      //III. Apply the substitution to the inferred type
                      let join2 = s_infer1
                      let app2 = apply_subst (t_infer1) (join2)

                      //Verify if the type T1 is unificable with app2
                      let join = unify (T1) (app2)
                      let join2 = compose_subst (join2) (join)

                      let final_subst_e1 = join2

                      let rec updateEnv app1 env x= 
                          match env with
                          | head :: tail -> let (s,Forall(i,t)) = head
                                            if s = x then
                                               (s,Forall(Set.toList(freevars_ty(app1)),app1)) :: updateEnv (app1) (tail) (x)
                                            else 
                                               head :: updateEnv (app1) (tail) (x)
                          | [] -> [] 

                      let env = updateEnv app2 env f

                      //IV. Infer the expression e2
                      let (t_infer2,s_infer2) = typeinfer_expr (env) (e2)

                      //V. Compose all substitution and apply it to the new inferred type
                      let join3 = compose_subst (join2) (s_infer2)
                      let app3 = apply_subst (t_infer2) (join3)

                      //VI. Define the final type and the final substitution

                      let final_type = app3
                      let final_subst = join3

                      //VII. Update global Environment
                      globalEnvironment <- updateEnvironment globalEnvironment final_subst_e1

                      (final_type,final_subst)
                        
                       

    | LetRec (f, None, e1, e2) -> 

                      //LET REC TYPE INFERENCES RULES

                      //Premises: 
                      //f : T1
                      //e1 : T2 {f : T1}

                      //FINAL RESULT
                      //e2 : T2 {e1 : T2, f: T1}

                      //The Initial Type of a LetRec must be an Arrow

                      //I. The function countLambda counts the number of parameters
                      //The size of the arrow depends on how many arguments there are
                      let rec countLambda e =
                          match e with
                          | Lambda(_,_,e1) -> 1 + (countLambda e1)
                          | App(e1,e2) -> countLambda(e1)+countLambda(e2)
                          | LetIn(_,e1) -> countLambda(e1)
                          | IfThenElse(e1,e2,None) -> countLambda(e1) + countLambda(e2)
                          | IfThenElse(e1,e2,Some e3) -> countLambda(e1) + countLambda(e2) + countLambda(e3)
                          | _ -> 0

                      let nLambda = countLambda e1
                      
                      //II. Create the arrow
                      let rec createStartingArrow n v =
                          if n > 0 then
                             TyArrow(TyVar v,createStartingArrow (n - 1) v)
                          else
                             TyVar v

                      let createArrow = createStartingArrow nLambda var

                      //III. Bind f in the environment with the Type Arrow created
                      let env = (f,Forall([],createArrow)) :: env
                      globalEnvironment <- (f,Forall([],createArrow)) :: globalEnvironment
                      var <- var+1

                      //IV. Infer the expression e1
                      let (t_infer1,s_infer1) = typeinfer_expr (env) (e1)
                      
                      //V. Apply the substitution to the inferred type
                      let join2 = s_infer1
                      let app2 = apply_subst (t_infer1) (join2)

                      //VI. Update the environment so I can use the function in the second
                      //expression after IN
                      let rec updateEnv app1 env x= 
                          match env with
                          | head :: tail -> let (s,Forall(i,t)) = head
                                            if s = x then
                                               (s,Forall(Set.toList(freevars_ty(app1)),app1)) :: updateEnv (app1) (tail) (x)
                                            else 
                                               head :: updateEnv (app1) (tail) (x)
                          | [] -> [] 

                      let env = updateEnv app2 env f

                      let final_subst_e1 = join2

                      //VII. Infer the expression e2
                      let (t_infer2,s_infer2) = typeinfer_expr (env) (e2)

                      //VIII. Compose all substitutions and apply it on the new inferred type
                      let join3 = compose_subst (join2) (s_infer2)
                      let app3 = apply_subst (t_infer2) (join3)

                      //IX. Define final type and final substitution
                      let final_type = app3
                      let final_subst = join3

                      //X. Update Global Environment
                      globalEnvironment <- updateEnvironment globalEnvironment final_subst_e1


                      //XI. Return final type and final substitution
                      (final_type,final_subst)
                        
 
    | UnOp ("not" as op, e) ->
           //UNOP TYPE INFERENCE RULE
           //e : bool

           //FINAL RESULT
           //UnOp("not",e) = bool
           typeinfer_expr env (App(Var op,e))
          
            
    | UnOp ("-" as op, e) ->
           //UNOP TYPE INFERENCE RULE
           //e : int

           //FINAL RESULT
           //UnOp("not",e) = int

           typeinfer_expr env (App(Var op,e))
        

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | Tuple ts -> //I. used the map function to infer the type of each element and return a new list with the inferred type

                  let rec map l env = 
                      match l with 
                      | head :: tail -> let (t_infer,s_infer) = typeinfer_expr (env) (head)
                                        let rec apply_subst_env env s_infer = 
                                            match env with
                                            | h :: ta -> let (s,Forall(i,t)) = h
                                                         (s,Forall(i,apply_subst (t) (s_infer))) :: apply_subst_env (ta) (s_infer)                                            
                                            | [] -> []

                                        let env = apply_subst_env env s_infer
                                        
                                        (t_infer,s_infer) :: map tail env
                                                       
                      | [] -> []

                 
                  let InferList = map ts env

                  let t = []
                  let s = []

                  //II. Create the Type
                  let rec createType res t =
                      
                      match res with
                      | head :: tail -> let (t1,s1) = head
                                        createType tail (t1 :: t)
                                    
                      | [] -> t

                  //III. Create the subst
                  let rec createSubst res s =
                      
                      match res with
                      | head :: tail -> let (t1,s1) = head
                                        let s2 = compose_subst (s1) (s)
                                        
                                        createSubst tail s2
                                    
                      | [] -> s

                  //IV. I call the two functions to create the final_type and final substitution
                  //I used List.rev because the results of the two function are in reverse order
                  let final_type = TyTuple (List.rev (createType InferList t))
                  let final_subst = List.rev (createSubst InferList s)

                  //V. Return the final type and the final substitution
                  (final_type,final_subst)
                  
                  

    | _ -> failwith "not implemented"

//Function to find the type of a variable in the type environment
let rec findType ls x =
    match ls with
    | head :: tail -> let (s,t) = head
                      if s = x then 
                         t
                      else 
                         findType tail x
    | [] -> TyUnit

    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
 

    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        
        try
          let _, t = List.find (fun (y, _) -> x = y) env
         
          t
        with
          | :? System.Collections.Generic.KeyNotFoundException -> printfn "Unbounded Variables not controllable!"; TyUnit


    | Lambda (x, None, e) -> 
                             let t1 = findType env x

                             match t1 with
                             | TyUnit -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
                             | _ -> let t2 = typecheck_expr ((x, t1) :: env) e
                                    TyArrow (t1, t2)
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
       
        match t1 with
        | TyArrow (l, r) -> //In case of polymorphism I must unify a TyVar with a Type t
                            if l <> t2 then
                               
                               
                               let un = unify (l) (t2)
                               let l = apply_subst (l) (un)
                               let r = apply_subst (r) (un)
                               if l = t2 then 
                                    r
                               else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
                            else 
                               r
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

              

    | Let (x, tyo, e1, e2) ->

        
        match tyo with
        | None -> let t1 = typecheck_expr env e1
                  typecheck_expr ((x, t1) :: env) e2
        | Some t ->  typecheck_expr ((x, t) :: env) e2
        
        

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        //let tf = findType globalEnvironment f
        let tf = findType env f
        match tf with
        | TyUnit -> unexpected_error "typecheck_expr: unannotated let rec is not supported"
        | _ -> 
                let env0 = (f, tf) :: env
                let t1 = typecheck_expr env0 e1
                match t1 with
                | TyArrow _ -> ()
                | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
                if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
                typecheck_expr env0 e2
        
        
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | TyVar a,TyVar b -> TyVar b
        | TyVar a, TyInt -> TyInt
        | TyVar a , TyFloat -> TyFloat
        | TyInt, TyVar a -> TyInt
        | TyFloat, TyVar a -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
