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
     The Graph<_,_,_> type is always dynamic. *)

open Aether
open Aether.Operators

(* Prelude

   Useful utility functions used throughout Hekate. *)

let private flip f a b =
    f b a

let private swap (a, b) =
    (b, a)

let private mapSnd f _ a =
    f a

(* Aliases
   For concision using commonly used modules, we alias L and M to
   L and M respectively. *)

module L = List
module M = Map

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

let private predLens : Lens<Context<'v,_,'b>, Adj<'v,'b>> =
    (fun (p, _, _, _) -> p), (fun p (_, v, l, s) -> (p, v, l, s))

let private valLens : Lens<Context<'v,_,_>, 'v> =
    (fun (_, v, _, _) -> v), (fun v (p, _, l, s) -> (p, v, l, s))

let private succLens : Lens<Context<'v,_,'b>, Adj<'v,'b>> =
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

let private mpredLens : Lens<MContext<'v,_,'b>, MAdj<'v,'b>> =
    (fun (p, _, _) -> p), (fun p (_, l, s) -> (p, l, s))

let private msuccLens : Lens<MContext<'v,_,'b>, MAdj<'v,'b>> =
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

(* Isomorphisms

   Isomorphisms between data structures from the definitional and
   representational type families. *)

let private mcontextIso v : Iso<MContext<'v,'a,'b>, Context<'v,'a,'b>> =
    toContext v, fromContext

(* Construction

   The functions "Empty" and "&", forming the two basic construction
   functions for the inductive definition fo a graph, as defined in the
   table of Basic Graph Operations in [Erwig:2001ho].

   "Empty" is defined as "empty", and "&" is defined as the function
   "cons" (as it is spritually similar to a list-like cons operation).
   "empty" is provided in a later part of Hekate, directly within the
   Graph module.

   We move away from the operator syntax with the expectation that
   the add function is pipe-friendly. *)

let private conMAdjPLens l a v =
    mapPLens a >?-> l >??> mapPLens v

let private consGraph c v p s =
       setPL (mapPLens v <?-> mcontextIso v) c
    >> flip (L.fold (fun g (l, a) -> setPL (conMAdjPLens msuccLens a v) l g)) p
    >> flip (L.fold (fun g (l, a) -> setPL (conMAdjPLens mpredLens a v) l g)) s

let private cons (c: Context<'v,'a,'b>) : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
    consGraph c (getL valLens c) (getL predLens c) (getL succLens c)

(* Decomposition

   Functions for decomposing an existent graph through a process
   of matching, as defined in the table of Basic Graph Operations
   in [Erqig:2001ho].
   
   The Empty-match function is named "isEmpty" and forms part of the public
   API for Hekate and is thus defined later in the Graph module. The "&-match"
   function becomes "decompose", and the "&v" function becomes "decomposeSpecific", to
   better align with F# expectations. In this case "decompose" is felt to be
   a better choice of verb than "match", both due to the nature of the function
   and the overloading of meaning of the "match" verb within F#. *)

let private decPLens l a =
    mapPLens a >?-> l

let private decomposeContext v =
       modL mpredLens (M.remove v) 
    >> modL msuccLens (M.remove v) 
    >> toContext v

let private decomposeGraph v p s =
       M.remove v
    >> flip (L.fold (fun g (_, a) -> modPL (decPLens msuccLens a) (M.remove v) g)) p
    >> flip (L.fold (fun g (_, a) -> modPL (decPLens mpredLens a) (M.remove v) g)) s

let private decomposeSpecific v (g: Graph<'v,'a,'b>) =
    match M.tryFind v g with
    | Some mc ->
        let c = decomposeContext v mc
        let g = decomposeGraph v (getL predLens c) (getL succLens c) g

        Some c, g
    | _ ->
        None, g

let private decompose (g: Graph<'v,'a,'b>) =
    match M.tryFindKey (fun _ _ -> true) g with
    | Some v -> decomposeSpecific v g
    | _ -> None, g

(* Graph

   The "public" API to Hekate is exposed as the Graph module, providing
   a API stylistically similar to common F# modules like List, Map, etc.

   F# naming conventions have been applied where relevant, in contrast to
   either FGL or [Erwig:2001ho]. *)



// TODO: Implement classical inductive versions of functions, then
// replace with optimized where possible. Write preamble to detail this.



module Graph =

    (* Construction

       Functions for constructing graphs, or for constructing new graphs
       by adding or removing nodes or edges of existing graphs. "empty" is the
       "Empty" function from the [Erwig:2001ho] table of Basic Graph
       Operations.

       Due to our underlying representation we can implement
       optimized versions of some of these functions (particularly the addition
       functions) by using the properties of our representation, instead of more
       normal basic approaches using "construct". *)

    let addNode ((v, l): LNode<'v,'a>) =
        cons ([], v, l, [])

    let removeNode v =
           decomposeSpecific v 
        >> snd

    let addEdge ((v1, v2, e): LEdge<'v,'b>) =
           decomposeSpecific v1
        >> function | Some (p, v, l, s), g -> cons (p, v, l, (e, v2) :: s) g
                    | _, g -> g

    let removeEdge ((v1, v2): Edge<'v>) =
           decomposeSpecific v1
        >> function | Some (p, v, l, s), g -> cons (p, v, l, L.filter (fun (_, v') -> v' <> v2) s) g
                    | _, g -> g

    (* Multipliers *)

    let private fold f xs : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
        flip (L.fold (flip f)) xs

    let addNodes ns =
        fold addNode ns

    let removeNodes ns =
        fold removeNode ns

    let addEdges es =
        fold addEdge es

    let removeEdges es =
        fold removeEdge es

    (* Creation *)

    let empty : Graph<'v,'a,'b> =
        M.empty

    let create ns es : Graph<'v,'a,'b> =
        (addNodes ns >> addEdges es) empty

    (* Queries

       Functions for querying properties of a graph, such as emptiness,
       number of nodes, edges, etc. *)

    let isEmpty<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> bool =
#if optimize
        M.isEmpty
#else
           decompose
        >> function | Some _, _ -> false
                    | _ -> true
#endif

    let containsNode v : Graph<'v,'a,'b> -> bool =
#if optimize
        M.containsKey v
#else
           decomposeSpecific v
        >> function | Some _, _ -> true
                    | _ -> false
#endif

    let countNodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
#if optimize
           M.toList 
        >> L.length
#else
        let rec count i =
               decompose
            >> function | Some _, g -> count (i + 1) g
                        | _ -> i 

        count 0
#endif

    let countEdges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
           M.toList 
        >> L.map (fun (_, (_, _, s)) -> (M.toList >> L.length) s)
        >> L.sum

    (* Mapping

       Functions for mapping over contexts, or parts of contexts. Again, given
       an optimized representation, we use functions for the underlying data
       structure. Strictly speaking the functions mapNodes and mapEdges map over
       node and edge *labels*, but for clarity this is assumed. *)

    let map f : Graph<'v,'a,'b> -> Graph<'v,'c,'d> =
        M.map (fun v mc -> (toContext v >> f >> fromContext) mc)

    let mapNodes f : Graph<'v,'a,'b> -> Graph<'v,'c,'b> =
        M.map (mapSnd (fun (p, l, s) -> p, f l, s))

    let mapEdges f : Graph<'v,'a,'b> -> Graph<'v,'a,'c> =
        M.map (mapSnd (fun (p, l, s) -> M.map (mapSnd f) p, l, M.map (mapSnd f) s))

    (* Projection

       Functions for projects of a graph, either to elements of a graph or to a new
       graph. As we are using an optimized representation, these functions can be
       implemented in a more efficient way than the standard application of ufold,
       using the functions for the underlying representation data structure. *)

    let nodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LNode<'v,'a> list =
           M.toList
        >> L.map (fun (v, (_, l, _)) -> v, l)

    let edges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LEdge<'v,'b> list =
           M.toList 
        >> L.map (fun (v, (_, _, s)) -> (M.toList >> L.map (fun (v', b) -> v, v', b)) s) 
        >> L.concat

    let rev<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
        M.map (fun _ (p, l, s) -> (s, l, p))

    (* Inspection

       Functions for inspecting graphs, and common properties of nodes and
       edges within a graph. *)

    let tryFindNode v : Graph<'v,'a,'b> -> LNode<'v,'a> option =
           M.tryFind v
        >> Option.map (fun (_, l, _) -> v, l)

    let findNode v =
           tryFindNode v 
        >> function | Some n -> n 
                    | _ -> failwith (sprintf "Node %A Not Found" v)