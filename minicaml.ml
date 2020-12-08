(*Exceptions*)
exception EmptyEnvironment
exception InvalidTypeDescriptor
exception RuntimeException
exception ApplyingNonFunctional
exception IncorrectParameterListLength
exception TypeException
exception InterpreterException
exception EmptySetException
exception WrongReturnTypeError


(*Types*)
type identifier = string

type 'a environment = identifier -> 'a

type typeDescriptor =
    | Integer
    | Boolean
    | String
    | Set of typeDescriptor

type expression =
    | IntImm of int
    | StringImm of string
    | BoolImm of bool
    | Times of expression * expression
    | Plus of expression * expression
    | Eq of expression * expression
    | IsZero of expression
    | Or of expression * expression
    | And of expression * expression
    | Not of expression
    | Den of identifier
    | If of expression * expression * expression
    | Let of identifier * expression * expression
    | Func of identifier list * expression
    | Apply of expression * expression list
    | EmptySet of typeDescriptor
    | SingletonSet of typeDescriptor * expression
    | SetOf of typeDescriptor * expression list
    | SetPut of expression * expression
    | SetRemove of expression * expression
    | SetIsEmpty of expression
    | SetContains of expression * expression
    | SetIsSubset of expression * expression
    | SetMin of expression
    | SetMax of expression
    | Print of expression
    | GreaterThan of expression * expression
    | LessThan of expression * expression
    | Forall of expression * expression
    | Exists of expression * expression
    | Filter of expression * expression
    | Map of expression * expression

type evaluationType =
    | Int of int
    | Bool of bool
    | Str of string
    | SetT of typeDescriptor * evaluationType list
    | Closure of identifier list * expression * evaluationType environment
    (*| Unbound*)




(*Environment*)

let emptyEvaluationEnvironment = fun (x: identifier) -> raise EmptyEnvironment

let bind (id: identifier) (v: 'a) (env: 'a environment) =
    fun (x: identifier) -> if x = id
        then v
        else env x

let rec bindList (ids: identifier list) (vs: 'a list) (env: 'a environment) =
    match (ids, vs) with
        | ([], []) -> env
        | (i::il, v::vl) -> bindList il vl (bind i v env)
        | _ -> raise IncorrectParameterListLength

let rec checkType (evType: evaluationType) (typeDesc: typeDescriptor) = match typeDesc with
    | Integer -> (match evType with
        | Int(_) -> true
        | _ -> false)
    | Boolean -> (match evType with
        | Bool(_) -> true
        | _ -> false)
    | String -> (match evType with
        | Str(_) -> true
        | _ -> false)
    | Set(tDesc) -> (match evType with
        | SetT(tDesc, elList) -> checkTypeMultiple tDesc elList
        | _ -> false)
    (*| _ -> raise InvalidTypeDescriptor*)

and checkTypeMultiple (tDesc: typeDescriptor) (elements: evaluationType list) =
    match elements with
        | [] -> true
        | el::els -> (checkType el tDesc) && (checkTypeMultiple tDesc els)

let rec getTypeDescriptor (evType: evaluationType) = match evType with
    | Int(_) -> Integer
    | Bool(_) -> Boolean
    | Str(_) -> String
    | SetT(x, _) -> Set(x)
    | Closure(_,_,_) -> raise RuntimeException


(*Print functions*)
let print_boolean (x: bool) = if x then (print_string "true") else print_string "false"

let rec printTypeDescriptor (tDesc: typeDescriptor) = match tDesc with
    | Integer -> print_string "Integer"
    | Boolean -> print_string "Boolean"
    | String -> print_string "String"
    | Set(x) -> print_string "Set(" ; printTypeDescriptor x ; print_string ")"

let rec printEvaluationType (evType: evaluationType) = match evType with
    | Int(x) -> print_int x
    | Bool(x) -> print_boolean x
    | Str(x) -> print_string x
    | SetT(_, x) -> print_string "SetT(" ; (let rec p l =
            match l with
                | [] -> print_string ""
                | x::[] -> printEvaluationType x
                | x::xs -> printEvaluationType x ; print_string ", " ; p xs
            in p x
        ) ; print_string ")"
    | Closure(id,body,_) -> print_string "Closure(" ;
        (let rec pID l = match l with
            | [] -> print_string ""
            | x::[] -> print_string x
            | x::xs -> print_string x ; print_string ", " ; pID xs
        in pID id);
        print_string ") <";
        print_string "expr";
        print_string ">"
    (*| Unbound -> print_string "Unbound"*)

(*Utility functions*)
let rec evtEquals (elem1: evaluationType) (elem2: evaluationType) = match (elem1, elem2) with
    | Int(a), Int(b) -> a=b
    | Bool(a), Bool(b) -> a=b
    | Str(a), Str(b) -> a=b
    | SetT(td1, els1), SetT(td2, els2) -> (td1 = td2) && (evtEqualsSet els1 els2)
    | _ -> raise TypeException

and contains (lst: evaluationType list) (elem: evaluationType) = match lst with
    | [] -> false
    | x::xs -> if (evtEquals x elem) then true else (contains xs elem)

and evtEqualsSet (ls1: evaluationType list) (ls2: evaluationType list) = match (ls1, ls2) with
    | ([], []) -> true
    | ([], x::xs) -> false
    | (x::xs, []) -> false
    | (x::xs, ys) -> (if (contains ys x) then (evtEqualsSet xs (listWithout ys x)) else false)

and listWithout (ls: evaluationType list) (el:evaluationType) = match ls with
    | [] -> []
    | x::xs -> (if (evtEquals x el)
        then x::(listWithout xs el)
        else (listWithout xs el))

let rec typeDepth (typeDesc: typeDescriptor) = match typeDesc with
    | Set(td) -> 1 + (typeDepth td)
    | _ -> 0

let rec listCount (ls: 'a list) = match ls with
    | [] -> 0
    | x::xs -> 1 + (listCount xs)

let rec evtGreaterThan (elem1: evaluationType) (elem2: evaluationType) = match (elem1, elem2) with
    | Int(a), Int(b) -> a>b
    | Bool(a), Bool(b) -> a && (not b)
    | Str(a), Str(b) -> a>b
    | SetT(td1, els1), SetT(td2, els2) -> (let tdp1 = (typeDepth td1) in let tdp2 = (typeDepth td2) in
        if tdp1>tdp2
            then true
            else if tdp2>tdp1
                then false
                else (listCount els1) > (listCount els2))
    | _ -> raise TypeException

let rec setIsSubset (lls: evaluationType list) (rls: evaluationType list) = match lls with
    | [] -> true
    | x::xs -> (contains rls x) && (setIsSubset xs rls)

let rec setMax (elems: evaluationType list) = match elems with
    | [] -> raise EmptySetException
    | x::[] -> x
    | x::xs -> (let y = setMax xs in if (evtGreaterThan x y) then x else y)

let rec setMin (elems: evaluationType list) = match elems with
    | [] -> raise EmptySetException
    | x::[] -> x
    | x::xs -> (let y = setMin xs in if (evtGreaterThan y x) then x else y)

(*Builtins*)
(*let binaryOperator (a: identifier) (b: identifier) (aT: typeDescriptor) (bT: typeDescriptor) (f: )*)
let intTimes x y = match (checkType x Integer, checkType y Integer, x, y) with
    | (true, true, Int(l), Int(r)) -> Int(l*r)
    | _ -> raise RuntimeException

let intPlus x y = match (checkType x Integer, checkType y Integer, x, y) with
    | (true, true, Int(l), Int(r)) -> Int(l+r)
    | _ -> raise RuntimeException


let boolOr x y = match (checkType x Boolean, checkType y Boolean, x, y) with
    | (true, true, Bool(l), Bool(r)) -> Bool(l || r)
    | _ -> raise RuntimeException

let boolAnd x y = match (checkType x Boolean, checkType y Boolean, x, y) with
    | (true, true, Bool(l), Bool(r)) -> Bool(l && r)
    | _ -> raise RuntimeException

let boolNot x = match (checkType x Boolean, x) with
    | (true, Bool(l)) -> Bool(not l)
    | _ -> raise RuntimeException


let setPut set element = match set with
    | SetT(td, elems) -> (
        if (checkType element td) then
            if (contains elems element) then
                set
            else
                SetT(td, element::elems)
        else
            raise TypeException)
    | _ -> raise TypeException

let setRemove set element = match set with
    | SetT(td, elems) -> (
        if (checkType element td) then
            SetT(td, listWithout elems element)
        else
            raise TypeException)
    | _ -> raise TypeException

(*Evaluation*)
let rec eval (e: expression) (env: evaluationType environment) = match e with
    | IntImm(n) -> Int(n)
    | BoolImm(b) -> Bool(b)
    | StringImm(s) -> Str(s)
    | Den(id) -> env id
    | Let(id, exp1, exp2) ->
        eval exp2 (bind id (eval exp1 env) env)
    | Times(exp1, exp2) -> intTimes (eval exp1 env) (eval exp2 env)
    | Plus(exp1, exp2) -> intPlus (eval exp1 env) (eval exp2 env)
    | Eq(exp1, exp2) -> Bool(evtEquals (eval exp1 env) (eval exp2 env))
    | IsZero(exp) -> Bool(evtEquals (eval exp env) (Int 0))
    | Or(exp1, exp2) -> boolOr (eval exp1 env) (eval exp2 env)
    | And(exp1, exp2) -> boolAnd (eval exp1 env) (eval exp2 env)
    | Not(exp) -> boolNot (eval exp env)
    | If(guard, b1, b2) -> (let g = eval guard env in
            (match (checkType g Boolean, g) with
                | (true, Bool(gev)) when gev -> eval b1 env
                | (true, Bool(gev)) when not gev -> eval b2 env
                | (_, _) -> raise TypeException
            )
        )
    | Func(identifiers, body) -> Closure(identifiers, body, env)
    | Apply(func, parameters) -> (let f = (eval func env) in match f with
            | Closure(identifiers, body, fenv) ->
                    eval body (bindList identifiers (List.map (fun x -> eval x env) parameters) (bind "rec" f fenv))
            | _ -> raise ApplyingNonFunctional
        )
    | EmptySet(typeDesc) -> SetT(typeDesc, [])
    | SingletonSet(typeDesc, expr) -> (let value = eval expr env in
        if (checkType value typeDesc) then
            SetT(typeDesc, [value])
        else
            raise TypeException)
    | SetOf(typeDesc, exprs) -> (let vals = List.map (fun x -> eval x env) exprs in
        if (checkTypeMultiple typeDesc vals) then
            SetT(typeDesc, vals)
        else
            raise TypeException)
    | SetPut(exp1, exp2) -> setPut (eval exp1 env) (eval exp2 env)
    | Print(exp) -> (let value = (eval exp env) in printEvaluationType value ; print_string "\n" ; value)
    | SetRemove(exp1, exp2) -> setRemove (eval exp1 env) (eval exp2 env)
    | SetIsEmpty(exp) -> (match (eval exp env) with
        | SetT(_, []) -> Bool(true)
        | SetT(_,_) -> Bool(false)
        | _ -> raise TypeException)
    | SetContains(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(tDesc, elems) -> (let value = (eval exp2 env) in
            if (checkType value tDesc)
                then Bool(contains elems value)
                else raise TypeException)
        | _ -> raise TypeException)
    | SetIsSubset(exp1, exp2) -> (match (eval exp1 env, eval exp2 env) with
        | (SetT(td1, els1), SetT(td2, els2)) -> (
            if (td1 = td2)
                then Bool(setIsSubset els1 els2)
                else raise TypeException
            )
        | _ -> raise TypeException)
    | SetMin(exp) -> (match (eval exp env) with
        | SetT(_, elems) -> setMin elems
        | _ -> raise TypeException)
    | SetMax(exp) -> (match (eval exp env) with
        | SetT(_, elems) -> setMax elems
        | _ -> raise TypeException)
    | GreaterThan(exp1, exp2) -> Bool(evtGreaterThan (eval exp1 env) (eval exp2 env))
    | LessThan(exp1, exp2) -> Bool(evtGreaterThan (eval exp2 env) (eval exp1 env))
    | Forall(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements)-> Bool(forall elements (eval exp2 env))
        | _ -> raise TypeException)
    | Exists(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements) -> Bool(exists elements (eval exp2 env))
        | _ -> raise TypeException)
    | Filter(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements) -> SetT(td, filter elements (eval exp2 env))
        | _ -> raise TypeException)
    | Map(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements) -> SetT(td, map elements (eval exp2 env))
        | _ -> raise TypeException)
(*
    | Filter of expression * expression
    | Map of expression * expression
*)
    (*| _ -> failwith ("not implemented yet")*)

and forall (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> true
    | x::xs -> ((
        match func with
            | Closure(params, body, fenv) -> (match (eval body (bind (List.hd params) x fenv)) with
                | Bool(b) -> b
                | _ -> raise WrongReturnTypeError)
            | _ -> raise TypeException) && (forall xs func))

and exists (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> false
    | x::xs -> ((
        match func with
            | Closure(params, body, fenv) -> (match (eval body (bind (List.hd params) x fenv)) with
                | Bool(b) -> b
                | _ -> raise WrongReturnTypeError)
            |_ -> raise TypeException) || (exists xs func))

and filter (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> []
    | x::xs -> if ((
        match func with
            | Closure(params, body, fenv) -> (match (eval body (bind (List.hd params) x fenv)) with
                | Bool (b) -> b
                | _ -> raise WrongReturnTypeError)
            | _ -> raise TypeException
        ))
        then x::(filter xs func)
        else (filter xs func)

and map (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> []
    | x::xs -> (match func with
        | Closure(params, body, fenv) -> (
            let els = map xs func in
            let newelem = (eval body (bind (List.hd params) x fenv)) in
            if (contains els newelem)
                then els
                else newelem::els)
        | _ -> raise TypeException)
(*Tests*)
(*
let x = Let("x", IntImm(10), Times(Den("x"), IntImm 7))
let v = printEvaluationType (eval x emptyEvaluationEnvironment)
let v = print_string "\n"
let x = IsZero(IntImm(0))
let v = printEvaluationType (eval x emptyEvaluationEnvironment)
let v = print_string "\n"
let x = Or(BoolImm(false), BoolImm(false))
let v = printEvaluationType (eval x emptyEvaluationEnvironment)
let v = print_string "\n"
let x = If(Or(BoolImm(false), BoolImm(false)), IntImm(10), IntImm(20))
let v = printEvaluationType (eval x emptyEvaluationEnvironment)
let v = print_string "\n"
let x = Let("f", Func(["a"; "b"], Times(Den("a"), Den("b"))), Apply(Den("f"), [IntImm(10); IntImm(4)]))
let x = Let("f", Func(["a"; "b"], Times(Den("a"), Den("b"))), Den("f"))
let v = printEvaluationType (eval x emptyEvaluationEnvironment)
let v = print_string "\n"

let x = SetT(Set(Integer), [SetT(Integer, [Int 1])])
let v = printEvaluationType x
let v = print_string "\n"

let td = printTypeDescriptor (getTypeDescriptor ( Int 10 ))

let x = eval (EmptySet(Integer)) emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n";;


let x = eval (SingletonSet(Integer, IntImm 7 )) emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n";;

let x = eval (SetOf(Integer, [IntImm 10; IntImm 20; Times(IntImm 5, IntImm 6)])) emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n";;

let x = eval (SetPut(SetOf(Integer, [IntImm 10; IntImm 20; Times(IntImm 5, IntImm 6)]), IntImm(10))) emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n";;

let recursive = (
    Let("r", Func(["n"],
        If(IsZero(Den("n")),
            Den("n"),
            Apply(Den("rec"), [Plus(Print(Den("n")), IntImm(-1))])
        )
    ),
    Apply(Den("r"), [IntImm 10])))

let x = eval recursive emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n";;
*)




exception AssertException

let print_debug (evt: evaluationType) =
    printEvaluationType evt;
    print_string "\n";
    printTypeDescriptor (getTypeDescriptor evt);
    print_string "\n"

let assertEquals (expr: expression) (evt: evaluationType) (debugPrint: bool) = let res = eval expr emptyEvaluationEnvironment in
    (if debugPrint then
        print_debug res
    else
        print_string "");

    if evtEquals res evt then
        print_string "Passed\n"
    else
        raise AssertException
;;

let assertEqualsDebug a b = assertEquals a b true;;

let sum = Plus(IntImm 10, IntImm 20);;
assertEqualsDebug sum (Int 30)

let fibonacci =
    Let("fibonacci",
        Func(["n"],
            If(Or(Eq(Den("n"), IntImm(1)), LessThan(Den("n"), IntImm(1))),
                IntImm(1),
                Plus(
                    Apply(
                        Den("rec"),
                        [Plus(Den("n"), IntImm(-1))]
                    ),
                    Apply(
                        Den("rec"),
                        [Plus(Den("n"), IntImm(-2))]
                    )
                )
            )
        ),
        Apply(Den("fibonacci"), [IntImm 10])
    );;

assertEqualsDebug fibonacci (Int 89)

let fibF =
    Func(["n"],
        If(Or(Eq(Den("n"), IntImm(1)), LessThan(Den("n"), IntImm(1))),
            IntImm(1),
            Plus(
                Apply(
                    Den("rec"),
                    [Plus(Den("n"), IntImm(-1))]
                ),
                Apply(
                    Den("rec"),
                    [Plus(Den("n"), IntImm(-2))]
                )
            )
        )
    )

let fibSet =
    Let("fibonacci", fibF,
        SetOf(Integer,[
            Apply(Den("fibonacci"), [IntImm 0]);
            Apply(Den("fibonacci"), [IntImm 1]);
            Apply(Den("fibonacci"), [IntImm 2]);
            Apply(Den("fibonacci"), [IntImm 3]);
            Apply(Den("fibonacci"), [IntImm 4]);
            Apply(Den("fibonacci"), [IntImm 5]);
            Apply(Den("fibonacci"), [IntImm 6]);
            Apply(Den("fibonacci"), [IntImm 7]);
            Apply(Den("fibonacci"), [IntImm 8]);
            Apply(Den("fibonacci"), [IntImm 9]);
        ])
    )
;;

print_debug (eval fibSet emptyEvaluationEnvironment)
