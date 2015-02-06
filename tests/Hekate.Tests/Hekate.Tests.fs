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

(* Decomposition *)

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

