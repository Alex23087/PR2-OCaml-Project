#use "minicaml.ml";;

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


(*Fibonacci*)
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

let assertDynamicTypeException (expr: expression) (debugPrint: bool) =
    try let res = eval expr emptyEvaluationEnvironment in
        (if debugPrint then
            print_debug res
        else
            print_string ""); raise AssertException
    with DynamicTypeException -> print_string "Passed\n"
;;

let assertDynamicTypeExceptionDebug a = assertDynamicTypeException a true;;


(*Fibonacci
let sum = Plus(IntImm 10, IntImm 20);;
assertEqualsDebug sum (Int 30)

let fibonacci =
    Let("fibonacci",
        Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer,
            If(Or(Eq(Den("n"), IntImm(1)), LessThan(Den("n"), IntImm(1))),
                IntImm(1),
                Plus(
                    Apply(
                        Den("rec"),
                        ExpressionList(Plus(Den("n"), IntImm(-1)), NoExpression)
                    ),
                    Apply(
                        Den("rec"),
                        ExpressionList(Plus(Den("n"), IntImm(-2)), NoExpression)
                    )
                )
            )
        ),
        Apply(Den("fibonacci"), ExpressionList(IntImm 10, NoExpression))
    );;

assertEqualsDebug fibonacci (Int 89)

let fibF =
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer,
        If(Or(Eq(Den("n"), IntImm(1)), LessThan(Den("n"), IntImm(1))),
            IntImm(1),
            Plus(
                Apply(
                    Den("rec"),
                    ExpressionList(Plus(Den("n"), IntImm(-1)), NoExpression)
                ),
                Apply(
                    Den("rec"),
                    ExpressionList(Plus(Den("n"), IntImm(-2)), NoExpression)
                )
            )
        )
    )

let fibSet =
    Let("fibonacci", fibF,
        SetOf(Integer,
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 0, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 1, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 2, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 3, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 4, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 5, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 6, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 7, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 8, NoExpression)),
            ExpressionList(Apply(Den("fibonacci"), ExpressionList(IntImm 9, NoExpression)),
            NoExpression))))))))))
        )
    )
;;

(*print_debug (eval fibSet emptyEvaluationEnvironment)*)
EndFibonacci*)

(*printTypeDescriptor (staticTypeCheck (IntImm(10)) emptyTypeEnvironment) ; print_string "\n";;
printTypeDescriptor (staticTypeCheck (Func(IdentifierList("a", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer, Den("a"))) emptyTypeEnvironment) ; print_string "\n";;
printEvaluationType (eval (Let("f", Func(IdentifierList("a", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer, Den("a")), Apply(Den("f"), ExpressionList(IntImm 10, NoExpression)))) emptyEvaluationEnvironment) ; print_string "\n";;
printTypeDescriptor (Closure(TypeDescriptorList(Integer, TypeDescriptorList(Integer, NoType)), Integer)) ; print_string "\n";;

printEvaluationType (eval (Let("f", Func(IdentifierList("a", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer, Den("a")), Apply(Den("f"), ExpressionList(IntImm 10, NoExpression)))) emptyEvaluationEnvironment) ; print_string "\n";;
printEvaluationType (eval (Let("f", Func(IdentifierList("a", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer, Den("a")), Apply(Den("f"), ExpressionList(IntImm 10, NoExpression)))) emptyEvaluationEnvironment) ; print_string "\n";;*)





(*Expressions Tests*)




(*Immediates*)
assertEquals (IntImm 10) (Int 10) false;;
assertEquals (StringImm "test") (Str "test") false;;
assertEquals (BoolImm true) (Bool true) false;;

(*Times*)
assertEquals (Times(IntImm 10, IntImm 4)) (Int 40) false;;
assertDynamicTypeException (Times(IntImm 10, BoolImm true)) false;;

(*Plus*)
assertEquals (Plus(IntImm 10, IntImm 4)) (Int 14) false;;
assertDynamicTypeException (Plus(IntImm 10, BoolImm true)) false;;

(*Eq*)
assertEquals (Eq(IntImm 10, IntImm 10)) (Bool true) false;;
assertEquals (Eq(BoolImm true, BoolImm false)) (Bool false) false;;
assertEquals (Eq(StringImm "a", StringImm "a")) (Bool true) false;;
assertEquals (Eq(
    SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, ExpressionList(IntImm 20, NoExpression)))),
    SetOf(Integer, ExpressionList(IntImm 20, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression))))))
    (Bool true) false;;
assertDynamicTypeException (Eq(IntImm(10), BoolImm true)) false;;

(*IsZero*)
assertEquals (IsZero(IntImm 0)) (Bool true) false;;
assertDynamicTypeException (IsZero(BoolImm true)) false;;

(*Or*)
assertEquals (Or(BoolImm true, BoolImm false)) (Bool true) false;;
assertDynamicTypeException (Or(BoolImm false, IntImm 0)) false;;

(*And*)
assertEquals (And(BoolImm true, BoolImm false)) (Bool false) false;;
assertDynamicTypeException (And(BoolImm false, IntImm 0)) false;;

(*Not*)
assertEquals (Not(BoolImm false)) (Bool true) false;;
assertDynamicTypeException (Not(IntImm 0)) false;;

(*If*)
assertEquals (If(BoolImm true, BoolImm false, BoolImm true)) (Bool false) false;;
assertDynamicTypeException (If(IntImm 0, BoolImm false, BoolImm true)) false;;

(*Let + Den*)
assertEquals (Let("a", IntImm 10, Den("a"))) (Int 10) false;;

(*Func + Apply*)
assertEquals (
        Apply(
            Func(
                IdentifierList("n", NoIdentifier),
                TypeDescriptorList(Integer, NoType),
                Integer,
                Den("n")
            ),
            ExpressionList(IntImm 10, NoExpression)
        )
    )
    (Int 10) false;;

assertDynamicTypeException (    (*Passing wrongly typed parameter*)
        Apply(
            Func(
                IdentifierList("n", NoIdentifier),
                TypeDescriptorList(Integer, NoType),
                Integer,
                Den("n")
            ),
            ExpressionList(StringImm "test", NoExpression)
        )
    )
    false;;

assertDynamicTypeException (    (*Passing wrong return type*)
        Apply(
            Func(
                IdentifierList("n", NoIdentifier),
                TypeDescriptorList(Integer, NoType),
                String,
                Den("n")
            ),
            ExpressionList(IntImm 10, NoExpression)
        )
    )
    false;;

(*EmptySet*)
assertEquals (EmptySet(Integer)) (SetT(Integer, [])) false;;

(*SingletonSet*)
assertEquals (SingletonSet(Integer, IntImm 10)) (SetT(Integer, [Int 10])) false;;
assertDynamicTypeException (SingletonSet(Integer, BoolImm true)) false;;

(*SetOf*)
assertEquals (SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression)))) (SetT(Integer, [Int 20; Int 10])) false;;
assertEquals (SetOf(Integer, NoExpression)) (SetT(Integer, [])) false;;
assertDynamicTypeException (SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(BoolImm false, NoExpression)))) false;;


(*TODO: finish expressions tests

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
*)

(*SetPut*)
assertEquals (SetPut(EmptySet(Integer), IntImm 10)) (SetT(Integer, [Int 10])) false;;
assertEquals (SetPut(SingletonSet(Integer, IntImm 10), IntImm 10)) (SetT(Integer, [Int 10])) false;;
assertDynamicTypeException (SetPut(EmptySet(Integer), BoolImm false)) false;;

(*SetRemove*)
assertEquals (SetRemove(SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression))), IntImm 20)) (SetT(Integer, [Int 10])) false;;
assertEquals (SetRemove(SingletonSet(Integer, IntImm 10), IntImm 20)) (SetT(Integer, [Int 10])) false;;
assertDynamicTypeException (SetRemove(SingletonSet(Integer, IntImm 10), BoolImm false)) false;;

(*SetIsEmpty*)
assertEquals (SetIsEmpty(EmptySet(Integer))) (Bool true) false;;
assertEquals (SetIsEmpty(SingletonSet(Integer, IntImm 10))) (Bool false) false;;
