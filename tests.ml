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


(*Fibonacci
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
        Func(IdentifierList("n", NoIdentifier),
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
    Func(IdentifierList("n", NoIdentifier),
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

print_debug (eval fibSet emptyEvaluationEnvironment)
EndFibonacci*)

printTypeDescriptor (staticTypeCheck (IntImm(10)) emptyTypeEnvironment) ; print_string "\n";;
printTypeDescriptor (staticTypeCheck (Func(IdentifierList("a", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer, Den("a"))) emptyTypeEnvironment) ; print_string "\n";;
printTypeDescriptor (staticTypeCheck (Let("f", Func(IdentifierList("a", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer, Den("a")), Apply(Den("f"), ExpressionList(IntImm 10, NoExpression)))) emptyTypeEnvironment) ; print_string "\n";;
printTypeDescriptor (Closure(TypeDescriptorList(Integer, TypeDescriptorList(Integer, NoType)), Integer)) ; print_string "\n";;
