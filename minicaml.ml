(*Exceptions*)
exception IdentifierNotFound
exception ApplyingNonFunctional
exception IncorrectParameterListLength
exception StaticTypeException
exception DynamicTypeException
exception EmptySetException
exception WrongReturnTypeException


(*Types*)
type identifier = string

type identifierList =
    | NoIdentifier
    | IdentifierList of identifier * identifierList

type 'a environment = identifier -> 'a

type typeDescriptor =
    | Integer
    | Boolean
    | String
    | Set of typeDescriptor
    | Closure of typeDescriptorList * typeDescriptor

and typeDescriptorList =
    | NoType
    | TypeDescriptorList of typeDescriptor * typeDescriptorList

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
    | Func of identifierList * typeDescriptorList * typeDescriptor * expression
    | Apply of expression * expressionList
    | EmptySet of typeDescriptor
    | SingletonSet of typeDescriptor * expression
    | SetOf of typeDescriptor * expressionList
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

and expressionList =
    | NoExpression
    | ExpressionList of expression * expressionList

type evaluationType =
    | Int of int
    | Bool of bool
    | Str of string
    | SetT of typeDescriptor * evaluationType list
    | ClosureT of identifierList * typeDescriptorList * typeDescriptor * expression * evaluationType environment
    (*| Unbound*)




(*Environment*)

let emptyEvaluationEnvironment = fun (x: identifier) -> raise IdentifierNotFound

let emptyTypeEnvironment = fun (x: identifier) -> raise IdentifierNotFound

let bind (id: identifier) (v: 'a) (env: 'a environment) =
    fun (x: identifier) -> if x = id
        then v
        else env x

let rec bindList (ids: identifierList) (vs: 'a list) (env: 'a environment) =
    match (ids, vs) with
        | (NoIdentifier, []) -> env
        | (IdentifierList(i, il), v::vl) -> bindList il vl (bind i v env)
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
    | Set(tDescTD) -> (match evType with
        | SetT(tDesc, elList) when tDescTD = tDesc -> checkTypeMultiple elList tDesc
        | _ -> false)
    | Closure(paramTDs, returnTD) -> (match evType with
        | ClosureT(_, paramTDs2, returnTD2, _, _) when ((paramTDs = paramTDs2) && (returnTD = returnTD2))-> true
        | _ -> false)

and checkTypeMultiple (elements: evaluationType list) (tDesc: typeDescriptor) =
    match elements with
        | [] -> true
        | el::els -> (checkType el tDesc) && (checkTypeMultiple els tDesc)

and checkTypeFunc (params: evaluationType list) (tDescs: typeDescriptorList) = match (params, tDescs) with
    | [], NoType -> true
    | [], TypeDescriptorList(_, _) -> false
    | x::xs, NoType -> false
    | x::xs, TypeDescriptorList(t, ts) -> ((checkType x t) && (checkTypeFunc xs ts))

let rec getTypeDescriptor (evType: evaluationType) = match evType with
    | Int(_) -> Integer
    | Bool(_) -> Boolean
    | Str(_) -> String
    | SetT(x, _) -> Set(x)
    | ClosureT(_, paramTDs, retTD, _, _) -> Closure(paramTDs, retTD)


(*Print functions*)
let print_boolean (x: bool) = if x then (print_string "true") else print_string "false"

let rec printTypeDescriptor (tDesc: typeDescriptor) = match tDesc with
    | Integer -> print_string "Integer"
    | Boolean -> print_string "Boolean"
    | String -> print_string "String"
    | Set(x) -> print_string "Set(" ; printTypeDescriptor x ; print_string ")"
    | Closure(paramTDs, retTD) -> print_string "Closure: " ; printTypeDescriptorList paramTDs ; print_string "-> " ; printTypeDescriptor retTD

and printTypeDescriptorList (tdList: typeDescriptorList) = match tdList with
    | NoType -> print_string "";
    | TypeDescriptorList(x, NoType) -> printTypeDescriptor x ; print_string " "
    | TypeDescriptorList(x, tdl) -> printTypeDescriptor x ; print_string " * " ; printTypeDescriptorList tdl

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
    | ClosureT(id, idTD, retTD, _, _) -> print_string "ClosureT(" ;
        (let rec pID l = match l with
            | NoIdentifier -> print_string ""
            | IdentifierList(x, NoIdentifier) -> print_string x
            | IdentifierList(x, xs) -> print_string x ; print_string ", " ; pID xs
        in pID id);
        (let rec pID l = match l with
            | NoType -> print_string ""
            | TypeDescriptorList(x, NoType) -> printTypeDescriptor x
            | TypeDescriptorList(x, xs) -> printTypeDescriptor x ; print_string ", " ; pID xs
        in pID idTD);   (*TODO:Check this function*)
        print_string ") <";
        print_string "expr";
        print_string ">"
    (*TODO: remove | Unbound -> print_string "Unbound"*)

let rec printEVTlist (l: evaluationType list) = match l with
    | [] -> print_string ""
    | x::xs -> printEvaluationType x ; printEVTlist xs

(*Utility functions*)
let rec evtEquals (elem1: evaluationType) (elem2: evaluationType) = match (elem1, elem2) with
    | Int(a), Int(b) -> a=b
    | Bool(a), Bool(b) -> a=b
    | Str(a), Str(b) -> a=b
    | SetT(td1, els1), SetT(td2, els2) -> (td1 = td2) && (evtEqualsSet els1 els2)
    | _ -> raise DynamicTypeException
    (*TODO: add closure equality maybe?*)

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
        then (listWithout xs el)
        else x::(listWithout xs el))

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
    | _ -> raise DynamicTypeException

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
    | _ -> raise DynamicTypeException

let intPlus x y = match (checkType x Integer, checkType y Integer, x, y) with
    | (true, true, Int(l), Int(r)) -> Int(l+r)
    | _ -> raise DynamicTypeException


let boolOr x y = match (checkType x Boolean, checkType y Boolean, x, y) with
    | (true, true, Bool(l), Bool(r)) -> Bool(l || r)
    | _ -> raise DynamicTypeException

let boolAnd x y = match (checkType x Boolean, checkType y Boolean, x, y) with
    | (true, true, Bool(l), Bool(r)) -> Bool(l && r)
    | _ -> raise DynamicTypeException

let boolNot x = match (checkType x Boolean, x) with
    | (true, Bool(l)) -> Bool(not l)
    | _ -> raise DynamicTypeException


let setPut set element = match set with
    | SetT(td, elems) -> (
        if (checkType element td) then
            if (contains elems element) then
                set
            else
                SetT(td, element::elems)
        else
            raise DynamicTypeException)
    | _ -> raise DynamicTypeException

let setRemove set element = match set with
    | SetT(td, elems) -> (
        if (checkType element td) then
            SetT(td, listWithout elems element)
        else
            raise DynamicTypeException)
    | _ -> raise DynamicTypeException

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
                | (_, _) -> raise DynamicTypeException
            )
        )
    | Func(identifiers, parameterTypes, outputType, body) -> ClosureT(identifiers, parameterTypes, outputType, body, env)
    | Apply(func, parameters) -> (let f = (eval func env) in match f with
            | ClosureT(identifiers, paramTDs, retTD, body, fenv) -> (let paramEVTs = (evalList parameters env) in
                    if (checkTypeFunc paramEVTs paramTDs)
                        then let returnValue = (eval body (bindList identifiers paramEVTs (bind "rec" f fenv))) in
                            if (checkType returnValue retTD)
                                then returnValue
                                else raise DynamicTypeException
                        else raise DynamicTypeException)
            | _ -> raise ApplyingNonFunctional
        )
    | EmptySet(typeDesc) -> SetT(typeDesc, [])
    | SingletonSet(typeDesc, expr) -> (let value = eval expr env in
        if (checkType value typeDesc) then
            SetT(typeDesc, [value])
        else
            raise DynamicTypeException)
    | SetOf(typeDesc, exprs) -> (let vals = evalList exprs env in
        if (checkTypeMultiple vals typeDesc) then
            (let rec addAll ls vs = match vs with       (*Adds all elements without duplicates*)
                | [] -> ls
                | x::xs -> if contains ls x then addAll ls xs else addAll (x::ls) xs
            in SetT(typeDesc, addAll [] vals))
        else
            raise DynamicTypeException)
    | SetPut(exp1, exp2) -> setPut (eval exp1 env) (eval exp2 env)
    | Print(exp) -> (let value = (eval exp env) in printEvaluationType value ; print_string "\n" ; value)
    | SetRemove(exp1, exp2) -> setRemove (eval exp1 env) (eval exp2 env)
    | SetIsEmpty(exp) -> (match (eval exp env) with
        | SetT(_, []) -> Bool(true)
        | SetT(_,_) -> Bool(false)
        | _ -> raise DynamicTypeException)
    | SetContains(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(tDesc, elems) -> (let value = (eval exp2 env) in
            if (checkType value tDesc)
                then Bool(contains elems value)
                else raise DynamicTypeException)
        | _ -> raise DynamicTypeException)
    | SetIsSubset(exp1, exp2) -> (match (eval exp1 env, eval exp2 env) with
        | (SetT(td1, els1), SetT(td2, els2)) -> (
            if (td1 = td2)
                then Bool(setIsSubset els1 els2)
                else raise DynamicTypeException
            )
        | _ -> raise DynamicTypeException)
    | SetMin(exp) -> (match (eval exp env) with
        | SetT(_, elems) -> setMin elems
        | _ -> raise DynamicTypeException)
    | SetMax(exp) -> (match (eval exp env) with
        | SetT(_, elems) -> setMax elems
        | _ -> raise DynamicTypeException)
    | GreaterThan(exp1, exp2) -> Bool(evtGreaterThan (eval exp1 env) (eval exp2 env))
    | LessThan(exp1, exp2) -> Bool(evtGreaterThan (eval exp2 env) (eval exp1 env))
    | Forall(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements)-> Bool(forall elements (eval exp2 env))
        | _ -> raise DynamicTypeException)
    | Exists(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements) -> Bool(exists elements (eval exp2 env))
        | _ -> raise DynamicTypeException)
    | Filter(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements) -> SetT(td, filter elements (eval exp2 env))
        | _ -> raise DynamicTypeException)
    | Map(exp1, exp2) -> (match (eval exp1 env) with
        | SetT(td, elements) -> SetT(td, map elements (eval exp2 env))
        | _ -> raise DynamicTypeException)
    (*TODO: remove | _ -> failwith ("not implemented yet")*)

and evalList (expressions: expressionList) (env: evaluationType environment) =
    match expressions with
        | NoExpression -> []
        | ExpressionList(x, xs) -> (eval x env)::(evalList xs env)

and forall (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> true
    | x::xs -> ((
        match func with
            | ClosureT(params, _, _, body, fenv) -> (match (eval body (bind (
                    match params with
                        | NoIdentifier -> raise DynamicTypeException
                        | IdentifierList(x, _) -> x
                    ) x fenv)) with
                | Bool(b) -> b
                | _ -> raise WrongReturnTypeException)
            | _ -> raise DynamicTypeException) && (forall xs func))

and exists (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> false
    | x::xs -> ((
        match func with
            | ClosureT(params, _, _, body, fenv) -> (match (eval body (bind (
                    match params with
                        | NoIdentifier -> raise DynamicTypeException
                        | IdentifierList(x, _) -> x
                    ) x fenv)) with
                | Bool(b) -> b
                | _ -> raise WrongReturnTypeException)
            |_ -> raise DynamicTypeException) || (exists xs func))

and filter (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> []
    | x::xs -> if ((
        match func with
            | ClosureT(params, _, _, body, fenv) -> (match (eval body (bind (
                    match params with
                        | NoIdentifier -> raise DynamicTypeException
                        | IdentifierList(x, _) -> x
                    ) x fenv)) with
                | Bool (b) -> b
                | _ -> raise WrongReturnTypeException)
            | _ -> raise DynamicTypeException
        ))
        then x::(filter xs func)
        else (filter xs func)

and map (elements: evaluationType list) (func: evaluationType) = match elements with
    | [] -> []
    | x::xs -> (match func with
        | ClosureT(params, _, _, body, fenv) -> (
            let els = map xs func in
            let newelem = (eval body (bind (
                    match params with
                        | NoIdentifier -> raise DynamicTypeException
                        | IdentifierList(x, _) -> x
                    ) x fenv)) in
            if (contains els newelem)
                then els
                else newelem::els)
        | _ -> raise DynamicTypeException)









let rec staticTypeCheck (expression: expression) (env: typeDescriptor environment) =
    match expression with
        | IntImm(_) -> Integer
        | StringImm(_) -> String
        | BoolImm(_) -> Boolean
        | Times(op1, op2) -> (match (staticTypeCheck op1 env, staticTypeCheck op2 env) with
            | Integer, Integer -> Integer
            | _,_ -> raise StaticTypeException)
        | Plus(op1, op2) -> (match (staticTypeCheck	op1 env, staticTypeCheck op2 env) with
            | Integer, Integer -> Integer
            | _,_ -> raise StaticTypeException)
        | Eq(_,_) -> Boolean
        | IsZero(op) -> (match (staticTypeCheck	op env) with
            | Integer -> Boolean
            | _ -> raise StaticTypeException)
        | Or(op1, op2) -> (match (staticTypeCheck op1 env, staticTypeCheck op2 env) with
            | Boolean, Boolean -> Boolean
            | _,_ -> raise StaticTypeException)
        | And(op1, op2) -> (match (staticTypeCheck op1 env, staticTypeCheck op2 env) with
            | Boolean, Boolean -> Boolean
            | _,_ -> raise StaticTypeException)
        | Not(op) -> (match (staticTypeCheck op env) with
            | Boolean -> Boolean
            | _ -> raise StaticTypeException)
        | Den(id) -> env id
        | If(guard, branch1, branch2) -> (match staticTypeCheck guard env with
            | Boolean -> (let type1 = staticTypeCheck branch1 env in let type2 = staticTypeCheck branch2 env in
                if type1=type2
                    then type1
                    else raise StaticTypeException)
            | _ -> raise StaticTypeException)
        | Let(id, assignment, block) -> staticTypeCheck block (bind id (staticTypeCheck assignment env) env)
        | Func(idList, paramTDs, returnTD, block) -> Closure(paramTDs, returnTD)
        | Apply(funcExpr, paramsExprs) -> (match (staticTypeCheck funcExpr env) with
            | Closure(paramTDs, returnTD) -> (let rec checkParams paramTypeDescList paramExprList = match (paramTypeDescList, paramExprList) with
                | NoType, NoExpression -> true
                | NoType, ExpressionList(_,_) -> false
                | TypeDescriptorList(_,_), NoExpression -> false
                | TypeDescriptorList(td, tdl), ExpressionList(exp, expl) -> (let expT = staticTypeCheck exp env in if td = expT then (checkParams tdl expl) else false)
                in if (checkParams paramTDs paramsExprs)
                    then returnTD
                    else raise StaticTypeException)
            | _ -> raise StaticTypeException)
        | EmptySet(typeDesc) -> Set(typeDesc)
        | SingletonSet(typeDesc, _) -> Set(typeDesc)
        | SetOf(typeDesc, _) -> Set(typeDesc)
        | SetPut(setExpr, valExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck valExpr env) with
            | Set(setTypeDesc), valTypeDesc -> Set(setTypeDesc)
            | _, _ -> raise StaticTypeException)
        | SetRemove(setExpr, valExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck valExpr env) with
            | Set(setTypeDesc), valTypeDesc when setTypeDesc = valTypeDesc -> Set(setTypeDesc)
            | _, _ -> raise StaticTypeException)
        | SetIsEmpty(setExpr) -> (match staticTypeCheck setExpr env with
            | Set(typeDesc) -> Boolean
            | _ -> raise StaticTypeException)
        | SetContains(setExpr, valExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck valExpr env) with
            | Set(setTypeDesc), valTypeDesc when setTypeDesc = valTypeDesc -> Boolean
            | _, _ -> raise StaticTypeException)
        | SetIsSubset(setExpr, subsetExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck subsetExpr env) with
            | Set(setTypeDesc), Set(subsetTypeDesc) when setTypeDesc = subsetTypeDesc -> Boolean
            | _, _ -> raise StaticTypeException)
        | SetMin(setExpr) -> (match staticTypeCheck setExpr env with
            | Set(typeDesc) -> typeDesc
            | _ -> raise StaticTypeException)
        | SetMax(setExpr) -> (match staticTypeCheck setExpr env with
            | Set(typeDesc) -> typeDesc
            | _ -> raise StaticTypeException)
        | Print(expr) -> staticTypeCheck expr env
        | GreaterThan(expr1, expr2) -> (match (staticTypeCheck expr1 env, staticTypeCheck expr2 env) with
            | Integer, Integer -> Boolean
            | Boolean, Boolean -> Boolean
            | String, String -> Boolean
            | Set(_), Set(_) -> Boolean
            | _, _ -> raise StaticTypeException)
        | LessThan(expr1, expr2) -> (match (staticTypeCheck expr1 env, staticTypeCheck expr2 env) with
            | Integer, Integer -> Boolean
            | Boolean, Boolean -> Boolean
            | String, String -> Boolean
            | Set(_), Set(_) -> Boolean
            | _, _ -> raise StaticTypeException)
        | Forall(setExpr, funcExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck funcExpr env) with
            | Set(typeDesc), Closure(tdList, retTD) -> (match tdList with
                | TypeDescriptorList(td, NoType) when (td = typeDesc) && (retTD = Boolean) -> Boolean
                | _ -> raise StaticTypeException)
            | _ -> raise StaticTypeException)
        | Exists(setExpr, funcExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck funcExpr env) with
            | Set(typeDesc), Closure(tdList, retTD) -> (match tdList with
                | TypeDescriptorList(td, NoType) when (td = typeDesc) && (retTD = Boolean) -> Boolean
                | _ -> raise StaticTypeException)
            | _, _ -> raise StaticTypeException)
        | Filter(setExpr, funcExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck funcExpr env) with
            | Set(typeDesc), Closure(tdList, retTD) -> (match tdList with
                | TypeDescriptorList(td, NoType) when (td = typeDesc) && (retTD = Boolean) -> Set(typeDesc)
                | _ -> raise StaticTypeException)
            | _, _ -> raise StaticTypeException)
        | Map(setExpr, funcExpr) -> (match (staticTypeCheck setExpr env, staticTypeCheck funcExpr env) with
            | Set(typeDesc), Closure(tdList, retTD) -> (match tdList with
                | TypeDescriptorList(td, NoType) when (td = typeDesc) -> Set(retTD)
                | _ -> raise StaticTypeException)
            | _, _ -> raise StaticTypeException)
