[<AutoOpen>]
module Hekate.Types

type Graph<'v,'e> =
    { Vertices: Vertex<'v> list
      Edges: Edge<'e> list }

and Vertex<'v> =
    { Data: 'v }

and Edge<'e> =
    { Data: 'e }