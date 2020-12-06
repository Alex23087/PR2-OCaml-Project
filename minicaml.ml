(*Exceptions*)
exception EmptyEnvironment
exception InvalidTypeDescriptor
exception RuntimeException
exception ApplyingNonFunctional
exception IncorrectParameterListLength
exception TypeException
exception InterpreterException


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
    | SetT(_,_), SetT(_,_) -> raise InterpreterException (*TODO Add set equality function*)

and contains (lst: evaluationType list) (elem: evaluationType) = match lst with
    | [] -> false
    | x::xs -> if (evtEquals x elem) then true else (contains xs elem)

(*Builtins*)
(*let binaryOperator (a: identifier) (b: identifier) (aT: typeDescriptor) (bT: typeDescriptor) (f: )*)
let intTimes x y = match (checkType x Integer, checkType y Integer, x, y) with
    | (true, true, Int(l), Int(r)) -> Int(l*r)
    | _ -> raise RuntimeException

let intPlus x y = match (checkType x Integer, checkType y Integer, x, y) with
    | (true, true, Int(l), Int(r)) -> Int(l+r)
    | _ -> raise RuntimeException

let intEq x y = match (checkType x Integer, checkType y Integer, x, y) with
    | (true, true, Int(l), Int(r)) -> Bool(l=r)
    | _ -> raise RuntimeException

let isZero = intEq (Int 0)


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
    | SetT(td, elems) ->(
        if (checkType element td) then
            if (contains elems element) then
                set
            else
                SetT(td, element::elems)
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
    | Eq(exp1, exp2) -> intEq (eval exp1 env) (eval exp2 env)
    | IsZero(exp) -> isZero (eval exp env)
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
(*
| SetPut of expression * expression
| SetRemove of expression * expression
| SetIsEmpty of expression
| SetContains of expression * expression
| SetIsSubset of expression * expression
| SetMin of expression
| SetMax of expression
*)
    (*| _ -> failwith ("not implemented yet")*)


(*Tests*)
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
print_string "\n"


let x = eval (SingletonSet(Integer, IntImm 7 )) emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n"

let x = eval (SetOf(Integer, [IntImm 10; IntImm 20; Times(IntImm 5, IntImm 6)])) emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n"

let x = eval (SetPut(SetOf(Integer, [IntImm 10; IntImm 20; Times(IntImm 5, IntImm 6)]), IntImm(10))) emptyEvaluationEnvironment;;
printEvaluationType x;
print_string "\n";
printTypeDescriptor (getTypeDescriptor x);
print_string "\n"
