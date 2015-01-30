open Hekate

[<EntryPoint>]
let main _ = 
    
    let g =
           Context (Adj [("down", Node 2)], Node 3, "c", Adj [("up", Node 1)])
        ^& Context (Adj [("right", Node 1)], Node 2, "b", Adj [("left", Node 1)])
        ^& Context (Adj [], Node 1, "a", Adj [])
        ^& Empty

    let empty = isEmpty g
    let nodes = nodes g
    let rev = grev g
    let undir = undir g

    0
