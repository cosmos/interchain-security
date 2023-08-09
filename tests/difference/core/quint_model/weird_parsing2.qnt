module main {
    var myMap: int -> int

    action op1(a: int): bool =
        myMap' =  myMap.set(3,a)

    action op2(b: int): bool =
        myMap' = myMap.set(1,b)

    action noop(): bool =
        myMap' = myMap

    // not working
    action main(boolean: bool): bool =
        if(boolean){
            noop
        } else {
            op1(2)
        }

    // not working
    // action main2(boolean: bool): bool =
    //     if(boolean){
    //         op1()
    //     } else {
    //         op2()
    //     }

    // not working
    // action main2(boolean: bool): bool =
    //     any {
    //         op1(),
    //         op2()
    //     }

    // fine
    // action main3(boolean: bool): bool =
    //     if(boolean){
    //         myMap' = myMap
    //     } else {
    //         myMap' = myMap.set(3,4)
    //     }
}