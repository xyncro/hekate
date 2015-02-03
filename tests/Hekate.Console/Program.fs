open Hekate

[<EntryPoint>]
let main _ =
    
    let g1 =
        Graph.empty
        |> Graph.add ([], 3, 'c', [])
        |> Graph.add ([], 2, 'b', [("down", 3)])
        |> Graph.add ([("left", 2); ("up", 3)], 1, 'a', [("right", 2)])

    let empty = Graph.isEmpty g1
    let nodes = Graph.nodes g1
    let nodesL = Graph.nodesLabelled g1

    0
