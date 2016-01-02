module Hekate.Tests

open Hekate
open Swensen.Unquote
open Xunit

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

[<Fact>]
let ``addNode behaves correctly`` () =
    let g3 = Graph.addNode (4, "four") g2

    Graph.countNodes g3 =! 4
    Graph.countEdges g3 =! 4

[<Fact>]
let ``removeNode behaves correctly`` () =
    let g3 = Graph.removeNode 1 g2

    Graph.countNodes g3 =! 2
    Graph.countEdges g3 =! 1

[<Fact>]
let ``addEdge behaves correctly`` () =
    let g3 = Graph.addEdge (1, 3, "down") g2

    Graph.countNodes g3 =! 3
    Graph.countEdges g3 =! 5

[<Fact>]
let ``removeEdge behaves correctly`` () =
    let g3 = Graph.removeEdge (2, 1) g2

    Graph.countNodes g3 =! 3
    Graph.countEdges g3 =! 3

(* Queries *)

[<Fact>]
let ``containsEdge behaves correctly`` () =
    Graph.containsEdge 1 2 g2 =! true
    Graph.containsEdge 1 3 g2 =! false

[<Fact>]
let ``containsNode behaves correctly`` () =
    Graph.containsNode 1 g2 =! true
    Graph.containsNode 4 g2 =! false

[<Fact>]
let ``isEmpty behaves correctly`` () =
    Graph.isEmpty g1 =! true
    Graph.isEmpty g2 =! false

(* Mapping *)

[<Fact>]
let ``mapEdges behaves correctly`` () =
    let g3 = Graph.mapEdges (fun v1 v2 (e: string) -> sprintf "%i.%i.%s" v1 v2 e) g2

    Graph.findEdge 1 2 g3 =! (1, 2, "1.2.right")

[<Fact>]
let ``mapNodes behaves correctly`` () =
    let g3 = Graph.mapNodes (fun _ (n: string) -> n.ToUpper ()) g2

    snd (Graph.findNode 1 g2) =! "one"
    snd (Graph.findNode 1 g3) =! "ONE"

(* Projection *)

[<Fact>]
let ``nodes behaves correctly`` () =
    List.length (Graph.nodes g2) =! 3

[<Fact>]
let ``edges behaves correctly`` () =
    List.length (Graph.edges g2) =! 4

(* Inspection *)

[<Fact>]
let ``tryFindNode behaves correctly`` () =
    Graph.tryFindNode 1 g2 =! Some (1, "one")
    Graph.tryFindNode 4 g2 =! None

[<Fact>]
let ``findNode behaves correctly`` () =
    Graph.findNode 1 g2 =! (1, "one")
    raises<exn> <@ Graph.findNode 4 g2 @>

[<Fact>]
let ``rev behaves correctly`` () =
    let g3 = Graph.rev g2
    let g4 = Graph.removeEdge (1, 3) g3

    Graph.countEdges g3 =! 4
    Graph.countEdges g4 =! 3

(* Adjacency/Degree *)

[<Fact>]
let ``neighbours behaves correctly`` () =
    Graph.neighbours 1 g2
        =! Some [ 2, "left"
                  3, "up"
                  2, "right" ]

[<Fact>]
let ``successors behaves correctly`` () =
    Graph.successors 1 g2
        =! Some [ 2, "right" ]

[<Fact>]
let ``predecessors behaves correctly`` () =
    Graph.predecessors 1 g2 
        =! Some [ 2, "left"
                  3, "up" ]

[<Fact>]
let ``outward behaves correctly`` () =
    Graph.outward 1 g2 
        =! Some [ 1, 2, "right" ]

[<Fact>]
let ``inward behaves correctly`` () =
    Graph.inward 1 g2 
        =! Some [ 2, 1, "left"
                  3, 1, "up" ]

[<Fact>]
let ``degree behaves correctly`` () =
    Graph.degree 1 g2 
        =! Some 3

[<Fact>]
let ``outwardDegree behaves correctly`` () =
    Graph.outwardDegree 1 g2 
        =! Some 1

[<Fact>]
let ``inwardDegree behaves correctly`` () =
    Graph.inwardDegree 1 g2 
        =! Some 2