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
let ``Nodes.add behaves correctly`` () =
    let g3 = Graph.Nodes.add (4, "four") g2

    Graph.Nodes.count g3 =! 4
    Graph.Nodes.count g3 =! 4

[<Fact>]
let ``Nodes.remove behaves correctly`` () =
    let g3 = Graph.Nodes.remove 1 g2

    Graph.Nodes.count g3 =! 2
    Graph.Edges.count g3 =! 1

[<Fact>]
let ``Edges.add behaves correctly`` () =
    let g3 = Graph.Edges.add (1, 3, "down") g2

    Graph.Nodes.count g3 =! 3
    Graph.Edges.count g3 =! 5

[<Fact>]
let ``Edges.remove behaves correctly`` () =
    let g3 = Graph.Edges.remove (2, 1) g2

    Graph.Nodes.count g3 =! 3
    Graph.Edges.count g3 =! 3

(* Queries *)

[<Fact>]
let ``Edges.contains behaves correctly`` () =
    Graph.Edges.contains 1 2 g2 =! true
    Graph.Edges.contains 1 3 g2 =! false

[<Fact>]
let ``Nodes.contains behaves correctly`` () =
    Graph.Nodes.contains 1 g2 =! true
    Graph.Nodes.contains 4 g2 =! false

[<Fact>]
let ``isEmpty behaves correctly`` () =
    Graph.isEmpty g1 =! true
    Graph.isEmpty g2 =! false

(* Mapping *)

[<Fact>]
let ``Edges.map behaves correctly`` () =
    let g3 = Graph.Edges.map (fun v1 v2 (e: string) -> sprintf "%i.%i.%s" v1 v2 e) g2

    Graph.Edges.find 1 2 g3 =! (1, 2, "1.2.right")

[<Fact>]
let ``Nodes.map behaves correctly`` () =
    let g3 = Graph.Nodes.map (fun _ (n: string) -> n.ToUpper ()) g2

    snd (Graph.Nodes.find 1 g2) =! "one"
    snd (Graph.Nodes.find 1 g3) =! "ONE"

[<Fact>]
let ``Nodes.mapFold behaves correctly`` () =
    let s, g3 = Graph.Nodes.mapFold (fun s _ (n: string) -> n.ToUpper (), s + 1) 0 g2

    snd (Graph.Nodes.find 1 g2) =! "one"
    snd (Graph.Nodes.find 1 g3) =! "ONE"
    s =! 3

(* Projection *)

[<Fact>]
let ``Nodes.toList behaves correctly`` () =
    List.length (Graph.Nodes.toList g2) =! 3

[<Fact>]
let ``Edges.toList behaves correctly`` () =
    List.length (Graph.Edges.toList g2) =! 4

(* Inspection *)

[<Fact>]
let ``Nodes.tryFind behaves correctly`` () =
    Graph.Nodes.tryFind 1 g2 =! Some (1, "one")
    Graph.Nodes.tryFind 4 g2 =! None

[<Fact>]
let ``Nodes.find behaves correctly`` () =
    Graph.Nodes.find 1 g2 =! (1, "one")
    raises<exn> <@ Graph.Nodes.find 4 g2 @>

[<Fact>]
let ``rev behaves correctly`` () =
    let g3 = Graph.rev g2
    let g4 = Graph.Edges.remove (1, 3) g3

    Graph.Edges.count g3 =! 4
    Graph.Edges.count g4 =! 3

(* Adjacency/Degree *)

[<Fact>]
let ``Nodes.neighbours behaves correctly`` () =
    Graph.Nodes.neighbours 1 g2
        =! Some [ 2, "left"
                  3, "up"
                  2, "right" ]

[<Fact>]
let ``Nodes.successors behaves correctly`` () =
    Graph.Nodes.successors 1 g2
        =! Some [ 2, "right" ]

[<Fact>]
let ``Nodes.predecessors behaves correctly`` () =
    Graph.Nodes.predecessors 1 g2 
        =! Some [ 2, "left"
                  3, "up" ]

[<Fact>]
let ``Nodes.outward behaves correctly`` () =
    Graph.Nodes.outward 1 g2 
        =! Some [ 1, 2, "right" ]

[<Fact>]
let ``Nodes.inward behaves correctly`` () =
    Graph.Nodes.inward 1 g2 
        =! Some [ 2, 1, "left"
                  3, 1, "up" ]

[<Fact>]
let ``Nodes.degree behaves correctly`` () =
    Graph.Nodes.degree 1 g2 
        =! Some 3

[<Fact>]
let ``Nodes.outwardDegree behaves correctly`` () =
    Graph.Nodes.outwardDegree 1 g2 
        =! Some 1

[<Fact>]
let ``Nodes.inwardDegree behaves correctly`` () =
    Graph.Nodes.inwardDegree 1 g2 
        =! Some 2