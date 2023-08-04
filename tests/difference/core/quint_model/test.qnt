module weird_parsing {
    var channel: List[int]

    pure def MyTrue = true
    action CoolAction(boolean: bool): bool = 
    any {
        all {
            boolean == MyTrue,
            channel' = channel
        },
        all {
            not(boolean),
            channel' = channel
        }
    }
}