module Fang.Lang

// variable: x, y
// abstraction: \x. (x + 1) ()
// application: (\x. x + 1) y

type VarName = string

type BType =
    Int of int

type ArithmeticFn =
    | Add
    | Sub
    | Mul
    | Div

module ArithmeticFn =
    let apply (fn: ArithmeticFn) (a: int) (b: int) : int =
        match fn with
        | Add -> a + b
        | Sub -> a - b
        | Mul -> a * b
        | Div -> a / b

type ComparisonFn = 
    | Less
    | Equal
    | Greater

module ComparisonFn =
    let apply (fn: ComparisonFn) (lhs: int) (rhs: int) : int =
        match fn with
        | Less -> if lhs < rhs then 1 else 0
        | Equal -> if lhs = rhs then 1 else 0
        | Greater -> if lhs > rhs then 1 else 0

type BuiltinFn =
    | Arithmetic of fn: ArithmeticFn * opA: Expr * opB: Expr
    | Comparison of fn: ComparisonFn * lhs: Expr * rhs: Expr

and Expr =
    | Var of VarName
    | Abs of var: VarName * body: Expr
    | App of expr: Expr * arg: Expr
    | AppLazy of expr: Expr * arg: Expr
    | Lit of BType
    | Builtin of BuiltinFn
    | Cond of pred: Expr * trueBranch: Expr * falseBranch: Expr

type EvalError = 
    | WrongType of Expr * expectedType: string

exception EvalException of  EvalError

module Expr =
    let asInt = function
        | Lit (BType.Int i) -> i
        | other -> raise (EvalException(WrongType(other, "int")))

    let asAbs = function
        | Abs (var, body) -> var, body
        | other -> raise (EvalException(WrongType(other, "lambda")))

    let rec subst (replaceWhat: VarName) (replaceFor: Expr) (expr: Expr) =
        let substFn = subst replaceWhat replaceFor
        match expr with
        | Lit _ -> expr
        | Builtin (Arithmetic (fn, opA, opB)) -> 
            Builtin (Arithmetic (fn, substFn opA, substFn opB))
        | Builtin (Comparison (fn, opA, opB)) -> 
            Builtin (Comparison (fn, substFn opA, substFn opB))
        | Cond (pred, t, f) ->  Cond (substFn pred, substFn t, substFn f)
        | App (expr, arg) -> App (substFn expr, substFn arg)
        | AppLazy (expr, arg) -> App (substFn expr, substFn arg)
        | Var boundName ->
            if boundName = replaceWhat then replaceFor else expr
        | Abs (boundName, body) ->
            if boundName = replaceWhat then expr else Abs (boundName, substFn body)

let rec eval (expr: Expr) : Expr =
    match expr with
    | Lit _ -> expr
    | Builtin (Arithmetic(fn, opA, opB)) -> 
        let valA = eval opA |> Expr.asInt
        let valB = eval opB |> Expr.asInt
        Lit (BType.Int (ArithmeticFn.apply fn valA valB))
    | Builtin (Comparison(fn, lhs, rhs)) -> 
        let lhs = eval lhs |> Expr.asInt
        let rhs = eval rhs |> Expr.asInt
        Lit (BType.Int (ComparisonFn.apply fn lhs rhs)) 
    | Cond(pred, trueBranch, falseBranch) -> 
        let valPred = eval pred |> Expr.asInt
        if valPred <> 0 then eval trueBranch else eval falseBranch
    | Abs _ ->
        // option 1: reduce body, return simplified abstraction
        // option 2: return as-is
        expr 
    | App (expr, arg) -> 
        let lambdaVar, lambdaBody = eval expr |> Expr.asAbs
        // evaluate the argument first
        // call by value evaluation strategy
        let valArg = eval arg
        Expr.subst lambdaVar valArg lambdaBody |> eval
    | AppLazy (expr, arg) -> 
        let lambdaVar, lambdaBody = eval expr |> Expr.asAbs
        // \x. x + 1
        // lambdaVar = x, lambdaBody = x + 1
        // substitute free occurences of x inside the body (reduction of the term)
        // main part of the interpreter
        // substitute the variable for the unevaluated argument (lazy)
        // call by name evaluation strategy
        // defer evaluating the argument until we actually need to
        Expr.subst lambdaVar arg lambdaBody |> eval
    | Var _ -> expr

module Ex =
    let lit (n: int) = Lit (BType.Int n)

    let incrFn = 
        Abs(
            var = "x",//
            body = Builtin (Arithmetic (Add, Var "x", lit 1))
        )

    let incrApp (n: int) = App(expr = incrFn, arg = lit n)

    let subFn =
        Abs(var = "x", body = Abs(var = "y", body = Builtin (Arithmetic(Sub, Var "x", Var "y"))))

    let subApp  (x: int) (y: int) =
        App(App(subFn, lit x), lit y)

    // let fib n = if n < 2 then 1 else fib (n - 1) + fib (n - 2)
    // no current way to bind the name to something
    // y-combinator
    // fix point combinator
    // emulate recursion in the lambda calculus
    // eager combinator vs lazy combinator

    // (x x) apply x to x is what makes it lazy
    // would recurse forever in an eager language
    let lazyFixpoint =
        // Y = \f. (\x. f (x x)) (\x. f (x x))
        // \x. f (x x)
        let innerAbs  = Abs (
            var = "x", 
            body = App (expr = Var "f", arg = App (expr = Var "x", arg = Var "x")))
        Abs (var = "f", body = App(expr = innerAbs, arg = innerAbs))

    // indirection in the argument to f
    // uses a lambda abstraction to supspend x
    let eagerFixpoint =
        // Y = \f. (\x. f (\v. x x v)) (\x. f (\v. x x v))
        // (\v. x x v)
        let indirection = Abs(
            var = "v",
            body = App(App(Var "x", Var "x"), Var "v"))
        // \x. f (x x)
        let innerAbs  = Abs (
            var = "x", 
            body = App (expr = Var "f", arg = indirection)
        )
        Abs (var = "f", body = App(expr = innerAbs, arg = innerAbs))

    let fibStep = 
        // \f. \x. if n < 2 then 1 else f (x - 1) + f (x - 2)
        let xMinus n = 
            Builtin(Arithmetic(Sub, Var "x", lit n))

        let falseBranch = 
            Builtin(Arithmetic(Add, App(Var "f", xMinus 1), App(Var "f", xMinus 2)))
        
        Abs (
            var = "f",
            body = Abs (
                var = "x", 
                body = Cond(
                    pred = Builtin(Comparison(Less, Var "x", lit 2)),
                    trueBranch = lit 1,
                    falseBranch = falseBranch
                )
            )
        )
    
    let fib (n: int) =
        let fn = App (eagerFixpoint, fibStep)
        App (fn, lit n)