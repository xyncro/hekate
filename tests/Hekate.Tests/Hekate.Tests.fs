module Hekate.Tests

open Hekate
open NUnit.Framework
open Swensen.Unquote

(* Fixtures *)

let private g1 =
    Graph.empty

let private g2 =
    Graph.create 
        [ 1, "one"
          2, "two"
          3, "three" ]
        [ 2, 1, "left"
          3, 1, "up"
          1, 2, "right"
          2, 3, "down" ]

(* Construction *)

[<Test>]
let ``addNode behaves correctly`` () =
    let g3 = Graph.addNode (4, "four") g2

    Graph.countNodes g3 =? 4
    Graph.countEdges g3 =? 4

[<Test>]
let ``removeNode behaves correctly`` () =
    let g3 = Graph.removeNode 1 g2

    Graph.countNodes g3 =? 2
    Graph.countEdges g3 =? 1

[<Test>]
let ``addEdge behaves correctly`` () =
    let g3 = Graph.addEdge (1, 3, "down") g2

    Graph.countNodes g3 =? 3
    Graph.countEdges g3 =? 5

[<Test>]
let ``removeEdge behaves correctly`` () =
    let g3 = Graph.removeEdge (2, 1) g2

    Graph.countNodes g3 =? 3
    Graph.countEdges g3 =? 3

(* Queries *)

[<Test>]
let ``containsNode behaves correctly`` () =
    Graph.containsNode 1 g2 =? true
    Graph.containsNode 4 g2 =? false

[<Test>]
let ``isEmpty behaves correctly`` () =
    Graph.isEmpty g1 =? true
    Graph.isEmpty g2 =? false

(* Mapping *)

[<Test>]
let ``mapNodes behaves correctly`` () =
    let g3 = Graph.mapNodes (fun (n: string) -> n.ToUpper ()) g2

    snd (Graph.findNode 1 g2) =? "one"
    snd (Graph.findNode 1 g3) =? "ONE"

(* Projection *)

[<Test>]
let ``nodes behaves correctly`` () =
    List.length (Graph.nodes g2) =? 3

[<Test>]
let ``edges behaves correctly`` () =
    List.length (Graph.edges g2) =? 4

(* Inspection *)

[<Test>]
let ``tryFindNode behaves correctly`` () =
    Graph.tryFindNode 1 g2 =? Some (1, "one")
    Graph.tryFindNode 4 g2 =? None

[<Test>]
let ``findNode behaves correctly`` () =
    Graph.findNode 1 g2 =? (1, "one")
    raises<exn> <@ Graph.findNode 4 g2 @>