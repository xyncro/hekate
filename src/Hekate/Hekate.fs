module Hekate

(* Introduction

   A library for working with graphs in a purely functional way, based
   on ideas from papers on inductive graphs and functional algorithms,
   principally by Martin Erwig. Those papers are particularly relevant to
   understanding the internals of this library.

   The following papers are referenced in commentary throughout the code:

   [Erwig:2001ho]: Inductive Graphs and Functional Graph Algorithms
                   http://dl.acm.org/citation.cfm?id=968434.968437

   The library is spiritually similar to the Haskell FGL library, which
   is unsurprising given that it was originally written by Erwig et al,
   based on [Erwig:2001ho]. However, we simplify some aspects and change
   others due to our own needs and type system.

   [FGL]: http://hackage.haskell.org/package/fgl

   There are some significant differences between Hekate and FGL:
   
   - Hekate does not have a concept of
     an unlabelled graph, either in terms of nodes or edges, and thus does
     not draw the FGL distinction between types Node, LNode, etc.

   - Hekate implements the underlying representation using a M type which
     is parameterized by key and value types, we allow node IDs to be of any
     type supporting comparison. Our graph type is this parameterized by the
     types of the node IDs, node labels, and edge labels.

   - Hekate does not draw a distinction between static and dynamic graphs.
     The Graph<_,_,_> type is always dynamic.

   NOTE: [Erwig:2001ho] defines various functions and algorithms implemented using
   the Basic Graph Operations. These are interesting, and usually the best way
   to understand the principle of the implementation, but they are not always the
   most efficient way to implement the function, depending on the underlying data
   structure representation. *)

open System
open Aether
open Aether.Operators

(* Aliases *)

module L = List
module M = Map
module O = Option

(* Prelude

   Useful utility functions used throughout Hekate. *)

let private flip f a b =
    f b a

let private swap (a, b) =
    (b, a)

(* Definitional Types and Lenses

   Types defining data structures which form the logical programming model
   defined by the inductive definition of graphs, along with a set of lenses
   for access to nested data structures. *)

type Node<'v> =
    'v

type Edge<'v> =
    'v * 'v

type LNode<'v,'a> =
    'v * 'a

type LEdge<'v,'b> =
    'v * 'v * 'b

type Adj<'v,'b> =
    ('b * 'v) list

type Context<'v,'a,'b> =
    Adj<'v,'b> * 'v * 'a * Adj<'v,'b>

let private pred_ : Lens<Context<'v,_,'b>, Adj<'v,'b>> =
    (fun (p, _, _, _) -> p), (fun p (_, v, l, s) -> (p, v, l, s))

let private val_ : Lens<Context<'v,_,_>, 'v> =
    (fun (_, v, _, _) -> v), (fun v (p, _, l, s) -> (p, v, l, s))

let private succ_ : Lens<Context<'v,_,'b>, Adj<'v,'b>> =
    (fun (_, _, _, s) -> s), (fun s (p, v, l, _) -> (p, v, l, s))

(* Representational Types and Lenses

   Types used for the underlying implementation of the graph, modelling the
   logically defined inductive definition as an optimized map, with sub-maps
   defining node adjacencies. *)

type MAdj<'v,'b> when 'v: comparison =
    Map<'v,'b>

type MContext<'v,'a,'b> when 'v: comparison =
    MAdj<'v,'b> * 'a * MAdj<'v,'b>

type MGraph<'v,'a,'b> when 'v: comparison =
    Map<'v, MContext<'v,'a,'b>>

type Graph<'v,'a,'b> when 'v: comparison =
    MGraph<'v,'a,'b>

let private mpred_ : Lens<MContext<'v,_,'b>, MAdj<'v,'b>> =
    (fun (p, _, _) -> p), (fun p (_, l, s) -> (p, l, s))

let private msucc_ : Lens<MContext<'v,_,'b>, MAdj<'v,'b>> =
    (fun (_, _, s) -> s), (fun s (p, l, _) -> (p, l, s))

(* Mappings

   Mapping functions between the two definitional and representational data
   structure families, used when translating between algorithmic operations applied
   to the definitional model, and modifications to the underlying data structure of
   the optmized representational model. *)

let private fromAdj<'v,'b when 'v: comparison> : Adj<'v,'b> -> MAdj<'v,'b> =
    L.map swap >> M.ofList

let private toAdj<'v,'b when 'v: comparison> : MAdj<'v,'b> -> Adj<'v,'b> =
    M.toList >> L.map swap

let private fromContext<'v,'a,'b when 'v: comparison> : Context<'v,'a,'b> -> MContext<'v,'a,'b> =
    fun (p, _, l, s) -> fromAdj p, l, fromAdj s

let private toContext<'v,'a,'b when 'v: comparison> v : MContext<'v,'a,'b> -> Context<'v,'a,'b> =
    fun (p, l, s) -> toAdj p, v, l, toAdj s

(* Construction

   The functions "Empty" and "&", forming the two basic construction
   functions for the inductive definition of a graph, as defined in the
   table of Basic Graph Operations in [Erwig:2001ho].

   "Empty" is defined as "empty", and "&" is defined as the function
   "compose". *)

type Id<'v> =
    'v -> 'v

let private empty : Graph<'v,'a,'b> =
    M.empty

let private composeGraph c v p s =
        Optic.set (M.value_ v) (Some (fromContext c))
     >> flip (L.fold (fun g (b, v') -> (M.add v b ^% (M.key_ v' >?> msucc_)) g)) p
     >> flip (L.fold (fun g (b, v') -> (M.add v b ^% (M.key_ v' >?> mpred_)) g)) s

let private compose (c: Context<'v,'a,'b>) : Id<Graph<'v,'a,'b>> =
    composeGraph c (c ^. val_) (c ^. pred_) (c ^. succ_)

(* Decomposition

   Functions for decomposing an existent graph through a process
   of matching, as defined in the table of Basic Graph Operations
   in [Erqig:2001ho].

   The Empty-match function is named "isEmpty" and forms part of the public
   API for Hekate and is thus defined later in the Graph module. The "&-match"
   function becomes "decompose", and the "&v" function becomes "decomposeSpecific", to
   better align with F# expectations. *)

let private decomposeContext v =
        M.remove v ^% mpred_
     >> M.remove v ^% msucc_
     >> toContext v

let private decomposeGraph v p s =
        M.remove v
     >> flip (L.fold (fun g (_, a) -> (M.remove v ^% (M.key_ a >?> msucc_)) g)) p
     >> flip (L.fold (fun g (_, a) -> (M.remove v ^% (M.key_ a >?> mpred_)) g)) s

let private decomposeSpecific v (g: Graph<'v,'a,'b>) =
    match M.tryFind v g with
    | Some mc ->
        let c = decomposeContext v mc
        let g = decomposeGraph v (c ^. pred_) (c ^. succ_) g

        Some c, g
    | _ ->
        None, g

let private decompose (g: Graph<'v,'a,'b>) : Context<'v,'a,'b> option * Graph<'v,'a,'b> =
    match M.tryFindKey (fun _ _ -> true) g with
    | Some v -> decomposeSpecific v g
    | _ -> None, g

let private isEmpty<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> bool =
    M.isEmpty

(* Functions

   Useful functions defined in terms of the Basic Graph Operations, though
   not expected to be used directly. *)

let rec private ufold f u =
       decompose
    >> function | Some c, g -> f c (ufold f u g)
                | _ -> u

let private fold f xs : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
    flip (L.fold (flip f)) xs

(* Graph

   The "public" API to Hekate is exposed as the Graph[.[Edges|Nodes]] modules,
   providing an API stylistically similar to common F# modules like List, Map, etc.

   F# naming conventions have been applied where relevant, in contrast to
   either FGL or [Erwig:2001ho]. *)

[<RequireQualifiedAccess>]
module Graph =

    [<RequireQualifiedAccess>]
    module Edges =

        (* Operations *)

        let add ((v1, v2, e): LEdge<'v,'b>) =
                M.add v2 e ^% (M.key_ v1 >?> msucc_)
             >> M.add v1 e ^% (M.key_ v2 >?> mpred_)

        let addMany es =
                fold add es

        let remove ((v1, v2): Edge<'v>) =
                decomposeSpecific v1
             >> function | Some (p, v, l, s), g -> compose (p, v, l, L.filter (fun (_, v') -> v' <> v2) s) g
                         | _, g -> g

        let removeMany es =
                fold remove es

        (* Properties *)

        let count<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
                M.toList 
             >> L.map (fun (_, (_, _, s)) -> (M.toList >> L.length) s)
             >> L.sum

        (* Map *)

        let map mapping : Graph<'v,'a,'b> -> Graph<'v,'a,'c> =
                M.map (fun v (p, l, s) ->
                    M.map (fun v' x -> mapping v' v x) p,
                    l,
                    M.map (fun v' x -> mapping v v' x) s)

        (* Projection *)

        let toList<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LEdge<'v,'b> list =
                M.toList 
             >> L.map (fun (v, (_, _, s)) -> (M.toList >> L.map (fun (v', b) -> v, v', b)) s) 
             >> L.concat

        (* Query*)

        let contains v1 v2 : Graph<'v,'a,'b> -> bool =
                M.tryFind v1
             >> O.bind (fun (_, _, s) -> M.tryFind v2 s)
             >> O.isSome


        let tryFind v1 v2 : Graph<'v,'a,'b> -> LEdge<'v,'b> option =
                M.tryFind v1
             >> O.bind (fun (_, _, s) -> M.tryFind v2 s)
             >> O.map (fun b -> (v1, v2, b))

        let find v1 v2 =
                tryFind v1 v2
             >> function | Some e -> e
                         | _ -> failwith (sprintf "Edge %A %A Not Found" v1 v2)

    [<RequireQualifiedAccess>]
    module Nodes =

        (* Operations*)

        let add ((v, l): LNode<'v,'a>) =
                M.add v (M.empty, l, M.empty)

        let addMany ns =
                fold add ns

        let remove v =
                decomposeSpecific v
             >> snd

        let removeMany vs =
                fold remove vs

        (* Properties *)

        let count<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
                M.toList
             >> L.length

        (* Map *)

        let map mapping : Graph<'v,'a,'b> -> Graph<'v,'c,'b> =
                M.map (fun v (p, l, s) ->
                    p, mapping v l, s)

        let mapFold mapping state : Graph<'v,'a,'b> -> 's * Graph<'v,'c,'b> =
                M.toList
             >> L.mapFold (fun state (v, (p, l, s)) -> mapping state v l |> fun (c, state) -> (v, (p, c, s)), state) state
             >> fun (graph, state) -> state, Map.ofList graph

        (* Projection *)

        let toList<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LNode<'v,'a> list =
                M.toList
             >> L.map (fun (v, (_, l, _)) -> v, l)

        (* Query*)

        let contains v : Graph<'v,'a,'b> -> bool =
                M.containsKey v

        let tryFind v : Graph<'v,'a,'b> -> LNode<'v,'a> option =
                M.tryFind v
             >> O.map (fun (_, l, _) -> v, l)

        let find v =
                tryFind v 
             >> function | Some n -> n 
                         | _ -> failwith (sprintf "Node %A Not Found" v)

        (* Adjacency and Degree *)

        let neighbours v =
                M.tryFind v
             >> O.map (fun (p, _, s) -> M.toList p @ M.toList s)

        let successors v =
                M.tryFind v
             >> O.map (fun (_, _, s) -> M.toList s)

        let predecessors v =
                M.tryFind v
             >> O.map (fun (p, _, _) -> M.toList p)

        let outward v =
                M.tryFind v
             >> O.map (fun (_, _, s) -> (M.toList >> L.map (fun (v', b) -> v, v', b)) s)

        let inward v =
                M.tryFind v
             >> O.map (fun (p, _, _) -> (M.toList >> L.map (fun (v', b) -> v', v, b)) p)

        let degree v =
                M.tryFind v
             >> O.map (fun (p, _, s) -> (M.toList >> L.length) p + (M.toList >> L.length) s)

        let outwardDegree v =
                M.tryFind v
             >> O.map (fun (_, _, s) -> (M.toList >> L.length) s)

        let inwardDegree v =
                M.tryFind v
             >> O.map (fun (p, _, _) -> (M.toList >> L.length) p)

    (* Operations *)

    let create ns es : Graph<'v,'a,'b> =
        (Nodes.addMany ns >> Edges.addMany es) empty

    let empty =
        empty

    (* Properties *)

    let isEmpty<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> bool =
        isEmpty

    (* Mapping *)

    let map f : Graph<'v,'a,'b> -> Graph<'v,'c,'d> =
        M.map (fun v mc -> (toContext v >> f >> fromContext) mc)

    let rev<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
        M.map (fun _ (p, l, s) -> (s, l, p))

    (* Obsolete (Deprecated) Functions

       To be removed in the 4.0 release of Hekate after adequate
       transition time. *)

    (* Operations *)

    [<Obsolete ("Use Graph.Edges.add instead.")>]
    let addEdge =
        Edges.add

    [<Obsolete ("Use Graph.Edges.addMany instead.")>]
    let addEdges =
        Edges.addMany

    [<Obsolete ("Use Graph.Nodes.add instead.")>]
    let addNode =
        Nodes.add

    [<Obsolete ("Use Graph.Nodes.addMany instead.")>]
    let addNodes =
        Nodes.addMany

    [<Obsolete ("Use Graph.Edges.remove instead.")>]
    let removeEdge =
        Edges.remove

    [<Obsolete ("Use Graph.Edges.removeMany instead.")>]
    let removeEdges =
        Edges.removeMany

    [<Obsolete ("Use Graph.Nodes.remove instead.")>]
    let removeNode =
        Nodes.remove

    [<Obsolete ("Use Graph.Nodes.removeMany instead.")>]
    let removeNodes =
        Nodes.removeMany

    (* Properties *)

    [<Obsolete ("Use Graph.Edges.count instead.")>]
    let countEdges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
        Edges.count

    [<Obsolete ("Use Graph.Nodes.count instead.")>]
    let countNodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
        Nodes.count

    (* Map *)

    [<Obsolete ("Use Graph.Edges.map instead.")>]
    let mapEdges =
        Edges.map

    [<Obsolete ("Use Graph.Nodes.map instead.")>]
    let mapNodes =
        Nodes.map

    (* Projection *)

    [<Obsolete ("Use Graph.Edges.toList instead.")>]
    let edges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LEdge<'v,'b> list =
        Edges.toList

    [<Obsolete ("Use Graph.Nodes.toList instead.")>]
    let nodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LNode<'v,'a> list =
        Nodes.toList

    (* Query *)

    [<Obsolete ("Use Graph.Edges.contains instead.")>]
    let containsEdge =
        Edges.contains

    [<Obsolete ("Use Graph.Nodes.contains instead.")>]
    let containsNode =
        Nodes.contains

    [<Obsolete ("Use Graph.Edges.find instead.")>]
    let findEdge =
        Edges.find

    [<Obsolete ("Use Graph.Nodes.find instead.")>]
    let findNode =
        Nodes.find

    [<Obsolete ("Use Graph.Edges.tryFind instead.")>]
    let tryFindEdge =
        Edges.tryFind

    [<Obsolete ("Use Graph.Nodes.tryFind instead.")>]
    let tryFindNode =
        Nodes.tryFind

    (* Adjacency and Degree *)

    [<Obsolete ("Use Graph.Nodes.neighbours instead.")>]
    let neighbours =
        Nodes.neighbours

    [<Obsolete ("Use Graph.Nodes.successors instead.")>]
    let successors =
        Nodes.successors

    [<Obsolete ("Use Graph.Nodes.predecessors instead.")>]
    let predecessors =
        Nodes.predecessors

    [<Obsolete ("Use Graph.Nodes.outward instead.")>]
    let outward =
        Nodes.outward

    [<Obsolete ("Use Graph.Nodes.inward instead.")>]
    let inward =
        Nodes.inward

    [<Obsolete ("Use Graph.Nodes.degree instead.")>]
    let degree =
        Nodes.degree

    [<Obsolete ("Use Graph.Nodes.outwardDegree instead.")>]
    let outwardDegree =
        Nodes.outwardDegree

    [<Obsolete ("Use Graph.Nodes.inwardDegree instead.")>]
    let inwardDegree =
        Nodes.inwardDegree