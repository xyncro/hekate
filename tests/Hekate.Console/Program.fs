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
    let edges = Graph.edges g1
    let nodeCount = Graph.countNodes g1
    let edgeCount = Graph.countEdges g1
    let contains1 = Graph.containsNode 1 g1
    let contains4 = Graph.containsNode 4 g1
    let n1 = Graph.tryFind 1 g1
    let n4 = Graph.tryFind 4 g1

    let g2 = Graph.mapNodes (string) g1
 
    0
