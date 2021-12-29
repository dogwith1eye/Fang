module Fang.Program

let evalPrint expr =
    let start = System.DateTime.Now
    let result = Lang.eval expr
    let finish = System.DateTime.Now
    let duration = finish - start
    printfn $"[{duration.TotalMilliseconds}]>> {result}"

evalPrint (Lang.Ex.incrApp 42)
evalPrint (Lang.Ex.subApp 42 2)
evalPrint (Lang.Ex.fib 30)