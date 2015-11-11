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
   structure representation.

   As a useful exercise we implement the functions both "classically" using only
   the Basic Graph Operations (or functions derived from them) and in an optimized
   fashion if possible given our underlying representation.

   It should be possible to use the classical versions with any representation which
   implements the Basic Graph Operations, if people wish to experiment with other
   representations (a simple series of inductive terms, for example).

   The two alternatives are provided based on the "inductive" compiler directive. *)

open Aether
open Aether.Operators

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
    List.map swap >> Map.ofList

let private toAdj<'v,'b when 'v: comparison> : MAdj<'v,'b> -> Adj<'v,'b> =
    Map.toList >> List.map swap

let private fromContext<'v,'a,'b when 'v: comparison> : Context<'v,'a,'b> -> MContext<'v,'a,'b> =
    fun (p, _, l, s) -> fromAdj p, l, fromAdj s

let private toContext<'v,'a,'b when 'v: comparison> v : MContext<'v,'a,'b> -> Context<'v,'a,'b> =
    fun (p, l, s) -> toAdj p, v, l, toAdj s

(* Isomorphisms

   Isomorphisms between data structures from the definitional and
   representational type families. *)

let private mcontext_ v : Iso<MContext<'v,'a,'b>, Context<'v,'a,'b>> =
    toContext v, fromContext

(* Construction

   The functions "Empty" and "&", forming the two basic construction
   functions for the inductive definition fo a graph, as defined in the
   table of Basic Graph Operations in [Erwig:2001ho].

   "Empty" is defined as "empty", and "&" is defined as the function
   "compose". *)

let private compMAdj_ l a v =
    key_ a >?-> l >??> key_ v

let private composeGraph c v p s =
       c ^?= (key_ v <?-> mcontext_ v)
    >> flip (List.fold (fun g (l, a) -> (l ^?= compMAdj_ msucc_ a v) g)) p
    >> flip (List.fold (fun g (l, a) -> (l ^?= compMAdj_ mpred_ a v) g)) s

let private compose (c: Context<'v,'a,'b>) : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
    composeGraph c (c ^. val_) (c ^. pred_) (c ^. succ_)

let private empty : Graph<'v,'a,'b> =
    Map.empty

(* Decomposition

   Functions for decomposing an existent graph through a process
   of matching, as defined in the table of Basic Graph Operations
   in [Erqig:2001ho].
   
   The Empty-match function is named "isEmpty" and forms part of the public
   API for Hekate and is thus defined later in the Graph module. The "&-match"
   function becomes "decompose", and the "&v" function becomes "decomposeSpecific", to
   better align with F# expectations. *)

let private dec_ l a =
    key_ a >?-> l

let private decomposeContext v =
       Map.remove v ^%= mpred_
    >> Map.remove v ^%= msucc_ 
    >> toContext v

let private decomposeGraph v p s =
       Map.remove v
    >> flip (List.fold (fun g (_, a) -> (Map.remove v ^?%= dec_ msucc_ a) g)) p
    >> flip (List.fold (fun g (_, a) -> (Map.remove v ^?%= dec_ mpred_ a) g)) s

let private decomposeSpecific v (g: Graph<'v,'a,'b>) =
    match Map.tryFind v g with
    | Some mc ->
        let c = decomposeContext v mc
        let g = decomposeGraph v (c ^. pred_) (c ^. succ_) g

        Some c, g
    | _ ->
        None, g

let private decompose (g: Graph<'v,'a,'b>) =
    match Map.tryFindKey (fun _ _ -> true) g with
    | Some v -> decomposeSpecific v g
    | _ -> None, g

let private isEmpty<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> bool =
    Map.isEmpty

(* Functions

   Useful functions defined in terms of the Basic Graph Operations, though
   not expected to be used directly. *)

let rec private ufold f u =
       decompose
    >> function | Some c, g -> f c (ufold f u g)
                | _ -> u

let private fold f xs : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
    flip (List.fold (flip f)) xs

(* Graph

   The "public" API to Hekate is exposed as the Graph module, providing
   a API stylistically similar to common F# modules like List, Map, etc.

   F# naming conventions have been applied where relevant, in contrast to
   either FGL or [Erwig:2001ho]. *)

module Graph =

    (* Construction *)

    let addNode ((v, l): LNode<'v,'a>) =
        Map.add v (Map.empty, l, Map.empty)

    let removeNode v =
            decomposeSpecific v 
         >> snd

    let addEdge ((v1, v2, e): LEdge<'v,'b>) =
            Map.add v2 e ^?%= (key_ v1 >?-> msucc_)
         >> Map.add v1 e ^?%= (key_ v2 >?-> mpred_)

    let removeEdge ((v1, v2): Edge<'v>) =
            decomposeSpecific v1
         >> function | Some (p, v, l, s), g -> compose (p, v, l, List.filter (fun (_, v') -> v' <> v2) s) g
                     | _, g -> g

    let addNodes ns =
        fold addNode ns

    let removeNodes ns =
        fold removeNode ns

    let addEdges es =
        fold addEdge es

    let removeEdges es =
        fold removeEdge es

    (* Creation *)

    let create ns es : Graph<'v,'a,'b> =
        (addNodes ns >> addEdges es) empty

    let empty =
        empty

    (* Properties *)

    let isEmpty<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> bool =
        isEmpty

    let containsNode v : Graph<'v,'a,'b> -> bool =
        Map.containsKey v

    let containsEdge v1 v2 : Graph<'v,'a,'b> -> bool =
            Map.tryFind v1
         >> Option.bind (fun (_, _, s) -> Map.tryFind v2 s)
         >> Option.isSome

    let countNodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
            Map.toList 
         >> List.length

    let countEdges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
            Map.toList 
         >> List.map (fun (_, (_, _, s)) -> (Map.toList >> List.length) s)
         >> List.sum

    (* Mapping *)

    let map f : Graph<'v,'a,'b> -> Graph<'v,'c,'d> =
        Map.map (fun v mc -> (toContext v >> f >> fromContext) mc)

    let mapNodes f : Graph<'v,'a,'b> -> Graph<'v,'c,'b> =
        Map.map (fun v (p, l, s) ->
            p, f v l, s)

    let mapEdges f : Graph<'v,'a,'b> -> Graph<'v,'a,'c> =
        Map.map (fun v (p, l, s) ->
            Map.map (fun v' x -> f v' v x) p,
            l,
            Map.map (fun v' x -> f v v' x) s)

    (* Projection *)

    let nodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LNode<'v,'a> list =
           Map.toList
        >> List.map (fun (v, (_, l, _)) -> v, l)

    let edges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LEdge<'v,'b> list =
           Map.toList 
        >> List.map (fun (v, (_, _, s)) -> (Map.toList >> List.map (fun (v', b) -> v, v', b)) s) 
        >> List.concat

    let rev<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
        Map.map (fun _ (p, l, s) -> (s, l, p))

    (* Query *)

    let tryFindEdge v1 v2 : Graph<'v,'a,'b> -> LEdge<'v,'b> option =
            Map.tryFind v1
         >> Option.bind (fun (_, _, s) -> Map.tryFind v2 s)
         >> Option.map (fun b -> (v1, v2, b))

    let findEdge v1 v2 =
            tryFindEdge v1 v2
         >> function | Some e -> e
                     | _ -> failwith (sprintf "Edge %A %A Not Found" v1 v2)

    let tryFindNode v : Graph<'v,'a,'b> -> LNode<'v,'a> option =
            Map.tryFind v
         >> Option.map (fun (_, l, _) -> v, l)

    let findNode v =
            tryFindNode v 
         >> function | Some n -> n 
                     | _ -> failwith (sprintf "Node %A Not Found" v)

    (* Adjacency/Degree *)

    let neighbours v =
            Map.tryFind v
         >> Option.map (fun (p, _, s) -> Map.toList p @ Map.toList s)

    let successors v =
            Map.tryFind v
         >> Option.map (fun (_, _, s) -> Map.toList s)

    let predecessors v =
            Map.tryFind v
         >> Option.map (fun (p, _, _) -> Map.toList p)

    let outward v =
            Map.tryFind v
         >> Option.map (fun (_, _, s) -> (Map.toList >> List.map (fun (v', b) -> v, v', b)) s)

    let inward v =
            Map.tryFind v
         >> Option.map (fun (p, _, _) -> (Map.toList >> List.map (fun (v', b) -> v', v, b)) p)

    let degree v =
            Map.tryFind v
         >> Option.map (fun (p, _, s) -> (Map.toList >> List.length) p + (Map.toList >> List.length) s)

    let outwardDegree v =
            Map.tryFind v
         >> Option.map (fun (_, _, s) -> (Map.toList >> List.length) s)

    let inwardDegree v =
            Map.tryFind v
         >> Option.map (fun (p, _, _) -> (Map.toList >> List.length) p)