#use "minicaml.ml";;

(*Test Utility Functions*)
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

let assertDynamicTypeException (expr: expression) (debugPrint: bool) =
    try let res = eval expr emptyEvaluationEnvironment in
        (if debugPrint then
            print_debug res
        else
            print_string ""); raise AssertException
    with DynamicTypeException -> print_string "Passed\n"
;;

let assertEmptySetException (expr: expression) (debugPrint: bool) =
    try let res = eval expr emptyEvaluationEnvironment in
        (if debugPrint then
            print_debug res
        else
            print_string ""); raise AssertException
    with EmptySetException -> print_string "Passed\n"
;;

let assertWrongReturnTypeException (expr: expression) (debugPrint: bool) =
    try let res = eval expr emptyEvaluationEnvironment in
        (if debugPrint then
            print_debug res
        else
            print_string ""); raise AssertException
    with WrongReturnTypeException -> print_string "Passed\n"
;;


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

(*SetPut*)
assertEquals (SetPut(EmptySet(Integer), IntImm 10)) (SetT(Integer, [Int 10])) false;;
assertEquals (SetPut(SingletonSet(Integer, IntImm 10), IntImm 10)) (SetT(Integer, [Int 10])) false;;
assertDynamicTypeException (SetPut(EmptySet(Integer), BoolImm false)) false;;
assertDynamicTypeException (SetPut(IntImm 10, IntImm 10)) false;;

(*SetRemove*)
assertEquals (SetRemove(SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression))), IntImm 20)) (SetT(Integer, [Int 10])) false;;
assertEquals (SetRemove(SingletonSet(Integer, IntImm 10), IntImm 20)) (SetT(Integer, [Int 10])) false;;
assertDynamicTypeException (SetRemove(SingletonSet(Integer, IntImm 10), BoolImm false)) false;;
assertDynamicTypeException (SetRemove(IntImm 10, IntImm	10)) false;;

(*SetIsEmpty*)
assertEquals (SetIsEmpty(EmptySet(Integer))) (Bool true) false;;
assertEquals (SetIsEmpty(SingletonSet(Integer, IntImm 10))) (Bool false) false;;
assertDynamicTypeException (SetIsEmpty(IntImm 10)) false;;

(*SetContains*)
assertEquals (SetContains(SingletonSet(Integer, IntImm 10), IntImm 10)) (Bool true) false;;
assertEquals (SetContains(SingletonSet(Integer, IntImm 10), IntImm 20)) (Bool false) false;;
assertEquals (SetContains(EmptySet(Integer), IntImm 20)) (Bool false) false;;
assertDynamicTypeException (SetContains(SingletonSet(Integer, IntImm 10), StringImm "test")) false;;
assertDynamicTypeException (SetContains(IntImm 10, IntImm 10)) false;;

(*SetIsSubset*)
assertEquals (SetIsSubset(
    SingletonSet(Integer, IntImm 10),
    SingletonSet(Integer, IntImm 10)))
    (Bool true) false;;
assertEquals (SetIsSubset(
    SingletonSet(Integer, IntImm 10),
    SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression)))))
    (Bool true) false;;
assertEquals (SetIsSubset(
    SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression))),
    SingletonSet(Integer, IntImm 10)))
    (Bool false) false;;
assertEquals (SetIsSubset(
    EmptySet(Integer),
    SingletonSet(Integer, IntImm 10)))
    (Bool true) false;;
assertDynamicTypeException (SetIsSubset(
    SingletonSet(Integer, IntImm 10),
    IntImm 10))
    false;;
assertDynamicTypeException (SetIsSubset(
    IntImm 10,
    SingletonSet(Integer, IntImm 10)))
    false;;
assertDynamicTypeException (SetIsSubset(
    BoolImm true,
    BoolImm true))
    false;;

(*SetMin*)
assertEquals (SetMin(
    SetOf(Integer,
        ExpressionList(IntImm 42, ExpressionList(IntImm 23, ExpressionList(IntImm 10, NoExpression))))))
    (Int 10)
    false;;
assertEquals (SetMin(
    SetOf(Boolean,
        ExpressionList(BoolImm true, ExpressionList(BoolImm false, NoExpression)))))
    (Bool false)
    false;;
assertEquals (SetMin(
    SetOf(String,
        ExpressionList(StringImm "c", ExpressionList(StringImm "a", ExpressionList(StringImm "b", NoExpression))))))
    (Str "a")
    false;;
assertEquals (SetMin(
    SetOf(Set(Integer),
        ExpressionList(
            SetOf(Integer, ExpressionList(IntImm 42, ExpressionList(IntImm 23, NoExpression))), ExpressionList(
            SetOf(Integer, ExpressionList(IntImm 42, ExpressionList(IntImm 23, ExpressionList(IntImm 13, NoExpression)))), ExpressionList(
            SingletonSet(Integer, IntImm 10), NoExpression))))))
    (SetT(Integer, [Int 10]))
    false;;
assertDynamicTypeException (SetMin(
    SingletonSet(Closure(NoType, Integer), Func(NoIdentifier, NoType, Integer, IntImm 10))))
    false;;
assertDynamicTypeException (SetMin(
    SetOf(Closure(NoType, Integer), ExpressionList(Func(NoIdentifier, NoType, Integer, IntImm 10), ExpressionList(Func(NoIdentifier, NoType, Integer, IntImm 10), NoExpression)))))
    false;;
assertEmptySetException (SetMin(EmptySet(Integer))) false;;

(*SetMax*)
assertEquals (SetMax(
    SetOf(Integer,
        ExpressionList(IntImm 42, ExpressionList(IntImm 23, ExpressionList(IntImm 10, NoExpression))))))
    (Int 42)
    false;;
assertEquals (SetMax(
    SetOf(Boolean,
        ExpressionList(BoolImm true, ExpressionList(BoolImm false, NoExpression)))))
    (Bool true)
    false;;
assertEquals (SetMax(
    SetOf(String,
        ExpressionList(StringImm "c", ExpressionList(StringImm "a", ExpressionList(StringImm "b", NoExpression))))))
    (Str "c")
    false;;
assertEquals (SetMax(
    SetOf(Set(Integer),
        ExpressionList(
            SetOf(Integer, ExpressionList(IntImm 42, ExpressionList(IntImm 23, NoExpression))), ExpressionList(
            SetOf(Integer, ExpressionList(IntImm 42, ExpressionList(IntImm 23, ExpressionList(IntImm 13, NoExpression)))), ExpressionList(
            SingletonSet(Integer, IntImm 10), NoExpression))))))
    (SetT(Integer, [Int 13; Int 23; Int 42]))
    false;;
assertDynamicTypeException (SetMax(
    SingletonSet(Closure(NoType, Integer), Func(NoIdentifier, NoType, Integer, IntImm 10))))
    false;;
assertDynamicTypeException (SetMax(
    SetOf(Closure(NoType, Integer), ExpressionList(Func(NoIdentifier, NoType, Integer, IntImm 10), ExpressionList(Func(NoIdentifier, NoType, Integer, IntImm 10), NoExpression)))))
    false;;
assertEmptySetException (SetMax(EmptySet(Integer))) false;;

(*GreaterThan*)
assertEquals (GreaterThan(IntImm 10, IntImm 9)) (Bool true) false;;
assertEquals (GreaterThan(BoolImm false, BoolImm true)) (Bool false) false;;
assertEquals (GreaterThan(StringImm "test", StringImm "a")) (Bool true) false;;
assertEquals (GreaterThan(
    SingletonSet(Integer, IntImm 10),
    SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression)))))
    (Bool false)
    false;;
assertEquals (GreaterThan(
    SingletonSet(Integer, IntImm 10),
    SingletonSet(Set(Integer), SingletonSet(Integer, IntImm 10))))
    (Bool false)
    false;;
assertDynamicTypeException (GreaterThan(
    Func(NoIdentifier, NoType, Integer, IntImm 10),
    Func(NoIdentifier, NoType, Integer, IntImm 10)))
    false;;
assertDynamicTypeException (GreaterThan(IntImm 10, BoolImm false)) false;;

(*LessThan*)
assertEquals (LessThan(IntImm 10, IntImm 9)) (Bool false) false;;
assertEquals (LessThan(BoolImm false, BoolImm true)) (Bool true) false;;
assertEquals (LessThan(StringImm "test", StringImm "a")) (Bool false) false;;
assertEquals (LessThan(
    SingletonSet(Integer, IntImm 10),
    SetOf(Integer, ExpressionList(IntImm 10, ExpressionList(IntImm 20, NoExpression)))))
    (Bool true)
    false;;
assertEquals (LessThan(
    SingletonSet(Integer, IntImm 10),
    SingletonSet(Set(Integer), SingletonSet(Integer, IntImm 10))))
    (Bool true)
    false;;
assertDynamicTypeException (LessThan(
    Func(NoIdentifier, NoType, Integer, IntImm 10),
    Func(NoIdentifier, NoType, Integer, IntImm 10)))
    false;;
assertDynamicTypeException (LessThan(IntImm 10, BoolImm false)) false;;

(*ForAll*)
assertEquals (Forall(
    SetOf(Integer,
        ExpressionList(IntImm 42,
        ExpressionList(IntImm 22,
        ExpressionList(IntImm 10, NoExpression)))),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Boolean,   (*IsEven function*)
        Eq(Times(Divide(Den "n", IntImm 2), IntImm 2), Den "n"))
    ))
    (Bool true)
    false;;
assertEquals (Forall(
    SingletonSet(Boolean, BoolImm true),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Boolean, NoType), Boolean, Den "b")))
    (Bool true)
    false;;
assertDynamicTypeException (Forall(
    SingletonSet(Boolean, BoolImm true),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Boolean,   (*IsEven function*)
            Eq(Times(Divide(Den "n", IntImm 2), IntImm 2), Den "n"))
        ))
    false;;
assertWrongReturnTypeException (Forall(
    SingletonSet(Boolean, BoolImm true),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Boolean, NoType), Integer, IntImm 10)))
    false;;

(*Exists*)
assertEquals (Exists(
    SetOf(Integer,
        ExpressionList(IntImm 42,
        ExpressionList(IntImm 23,
        ExpressionList(IntImm 10, NoExpression)))),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Boolean,   (*IsOdd function*)
        Not(Eq(Times(Divide(Den "n", IntImm 2), IntImm 2), Den "n")))
    ))
    (Bool true)
    false;;
assertEquals (Exists(
    SingletonSet(Boolean, BoolImm false),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Boolean, NoType), Boolean, Den "b")))
    (Bool false)
    false;;
assertDynamicTypeException (Exists(
    SingletonSet(Boolean, BoolImm true),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Boolean,   (*IsEven function*)
            Eq(Times(Divide(Den "n", IntImm 2), IntImm 2), Den "n"))
        ))
    false;;
assertWrongReturnTypeException (Exists(
    SingletonSet(Boolean, BoolImm true),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Boolean, NoType), Integer, IntImm 10)))
    false;;

(*Filter*)
assertEquals (Filter(
    SetOf(Integer,
        ExpressionList(IntImm 10,
        ExpressionList(IntImm 23,
        ExpressionList(IntImm 42, NoExpression)))),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Boolean,   (*IsOdd function*)
        Not(Eq(Times(Divide(Den "n", IntImm 2), IntImm 2), Den "n")))
    ))
    (SetT(Integer, [Int 23]))
    false;;
assertEquals (Filter(
    SetOf(Boolean, ExpressionList(BoolImm false, ExpressionList(BoolImm true, NoExpression))),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Boolean, NoType), Boolean, Den "b")))
    (SetT(Boolean, [Bool true]))
    false;;
assertDynamicTypeException (Filter(
    SetOf(Boolean, ExpressionList(BoolImm false, ExpressionList(BoolImm true, NoExpression))),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Integer, NoType), Boolean, BoolImm true)))
    true;;
assertWrongReturnTypeException (Filter(
    SetOf(Boolean, ExpressionList(BoolImm false, ExpressionList(BoolImm true, NoExpression))),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Boolean, NoType), Integer, IntImm 10)))
    false;;

(*Map*)
assertEquals (Map(
    SetOf(Integer,
        ExpressionList(IntImm 10,
        ExpressionList(IntImm 23,
        ExpressionList(IntImm 42, NoExpression)))),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Boolean,   (*IsEven function*)
            Eq(Times(Divide(Den "n", IntImm 2), IntImm 2), Den "n"))
        ))
    (SetT(Boolean, [Bool true; Bool false]))
    false;;
assertEquals (Map(
    SetOf(Integer,
        ExpressionList(IntImm 10,
        ExpressionList(IntImm 23,
        ExpressionList(IntImm 42, NoExpression)))),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer,   (*IsEven function*)
            Times(Den "n", IntImm 6))
        ))
    (SetT(Integer, [Int 60; Int 252; Int 138]))
    false;;
assertEquals (Map(
    SetOf(Boolean, ExpressionList(BoolImm true, ExpressionList(BoolImm false, NoExpression))),
    Func(IdentifierList("b", NoIdentifier), TypeDescriptorList(Boolean, NoType), Integer, IntImm 10)))
    (SetT(Integer, [Int 10]))
    false;;
assertDynamicTypeException (Map(
    SetOf(Boolean, ExpressionList(BoolImm true, ExpressionList(BoolImm false, NoExpression))),
    Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Integer, Den "n")))
    true;;

(*SetUnion*)
assertEquals (SetUnion(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Boolean, BoolImm false)))
    (SetT(Boolean, [Bool true; Bool false]))
    false;
assertEquals (SetUnion(
    SingletonSet(Boolean, BoolImm true),
    EmptySet(Boolean)))
    (SetT(Boolean, [Bool true]))
    false;
assertEquals (SetUnion(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Boolean, BoolImm true)))
    (SetT(Boolean, [Bool true]))
    false;
assertDynamicTypeException (SetUnion(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Integer, IntImm 10)))
    false;;

(*SetIntersection*)
assertEquals (SetIntersection(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Boolean, BoolImm false)))
    (SetT(Boolean, []))
    false;
assertEquals (SetIntersection(
    SingletonSet(Boolean, BoolImm true),
    EmptySet(Boolean)))
    (SetT(Boolean, []))
    false;
assertEquals (SetIntersection(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Boolean, BoolImm true)))
    (SetT(Boolean, [Bool true]))
    false;
assertDynamicTypeException (SetIntersection(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Integer, IntImm 10)))
    false;;

(*SetSubtraction*)
assertEquals (SetSubtraction(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Boolean, BoolImm false)))
    (SetT(Boolean, [Bool true]))
    false;
assertEquals (SetSubtraction(
    SingletonSet(Boolean, BoolImm true),
    EmptySet(Boolean)))
    (SetT(Boolean, [Bool true]))
    false;
assertEquals (SetSubtraction(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Boolean, BoolImm true)))
    (SetT(Boolean, []))
    false;
assertDynamicTypeException (SetSubtraction(
    SingletonSet(Boolean, BoolImm true),
    SingletonSet(Integer, IntImm 10)))
    false;;



(*Fibonacci*)
let sum = Plus(IntImm 10, IntImm 20);;
assertEquals sum (Int 30) false;;

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

assertEquals fibonacci (Int 89) false;;

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

let fibSet (x: int) =
    Let("fbs",
        Func(IdentifierList("n", NoIdentifier), TypeDescriptorList(Integer, NoType), Set(Integer),
            Let("fibonacci", fibF,
                If(Eq(Den "n", IntImm 0),
                    SingletonSet(Integer, Apply(Den "fibonacci", ExpressionList(Den "n", NoExpression))),
                    SetPut(
                        Apply(Den "rec", ExpressionList(Plus(Den "n", IntImm (-1)), NoExpression)),
                        Apply(Den "fibonacci", ExpressionList(Den "n", NoExpression))
                    )
                )
            )
        ),
        Print(Apply(Den "fbs", ExpressionList(IntImm x, NoExpression)))
    );;

eval (Print(fibF)) emptyEvaluationEnvironment;;
eval (Print(StringImm "Fibonacci set from f(0) until f(10):")) emptyEvaluationEnvironment;;
eval (fibSet 10) emptyEvaluationEnvironment;;
