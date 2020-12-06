(*Exceptions*)
exception EmptyEnvironment
exception InvalidTypeDescriptor
exception RuntimeException
exception ApplyingNonFunctional
exception IncorrectParameterListLength


(*Types*)
type identifier = string

type 'a environment = identifier -> 'a

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


type typeDescriptor =
    | Integer
    | Boolean
    | String
    | Set of typeDescriptor

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
        | SetT(tDesc, elList) -> (let rec checkSet (elements: evaluationType list) =
            match elements with
                | [] -> true
                | el::els -> (checkType el tDesc) && (checkSet els)
            in checkSet elList)
        | _ -> false)
    (*| _ -> raise InvalidTypeDescriptor*)

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

let printEvaluationType (evType: evaluationType) = match evType with
    | Int(x) -> print_int x
    | Bool(x) -> print_boolean x
    | Str(x) -> print_string x
    | SetT(x, _) -> print_string "SetT(" ; printTypeDescriptor x ; print_string ")"
    | Closure(_,_,_) -> print_string "Closure"
    (*| Unbound -> print_string "Unbound"*)


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
                | (_, _) -> raise RuntimeException
            )
        )
    | Func(identifiers, body) -> Closure(identifiers, body, env)
    | Apply(func, parameters) -> (match (eval func env) with
            | Closure(identifiers, body, fenv) ->
                    eval body (bindList identifiers (List.map (fun x -> eval x env) parameters) fenv)
            | _ -> raise ApplyingNonFunctional
        )
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
let v = printEvaluationType (eval x emptyEvaluationEnvironment)
let v = print_string "\n"

let x = SetT(Set(Integer), [SetT(Integer, [Int 1])])
let v = printEvaluationType x
let v = print_string "\n"

let td = printTypeDescriptor (getTypeDescriptor ( Int 10 ))
