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

   - Hekate implements the underlying representation using a Map type which
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

   For concision using commonly used modules, we alias List and Map to
   L and M respectively. *)

module L = List
module M = Map 

(* Definitional Types and Lenses

   Types defining data structures which form the logical programming model
   defined by the inductive definition of graphs, along with a set of lenses
   for access to nested data structures. *)

type Node<'v,'a> =
    'v * 'a

type Edge<'v,'b> =
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

(* Graph

   The "public" API to Hekate is exposed as the Graph module, providing
   a API stylistically similar to common F# modules like List, Map, etc.

   F# naming conventions have been applied where relevant, in contrast to
   either FGL or [Erwig:2001ho]. *)

module Graph =

    (* Construction

       The functions "Empty" and "&", forming the two basic construction
       functions for the inductive definition fo a graph, as defined in the
       table of Basic Graph Operations in [Erwig:2001ho].

       "Empty" is defined as "empty", and "&" is defined as the function
       "add". We move away from the operator syntax with the expectation that
       the add function is pipe-friendly.

       The functions are not exposed externally, but are used as the basis of
       higher level functions exposed in later sections. *)

    let private addPLens l a v =
        mapPLens a >?-> l >??> mapPLens v

    let private mapGraphAdd c v p s =
           setPL (mapPLens v <?-> mcontextIso v) c
        >> flip (L.fold (fun g (l, a) -> setPL (addPLens msuccLens a v) l g)) p
        >> flip (L.fold (fun g (l, a) -> setPL (addPLens mpredLens a v) l g)) s

    let add c : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
        mapGraphAdd c (getL valLens c) (getL predLens c) (getL succLens c)

    let empty : Graph<'v,'a,'b> =
        M.empty

    (* Decomposition

       Functions for decomposing an existent graph through a process
       of matching, as defined in the table of Basic Graph Operations
       in [Erqig:2001ho].
   
       The Empty-match function is named "isEmpty", the "&-match" function
       becomes "extractAny", and the "&v" function becomes "extractSpecific", to
       better align with F# expectations. In this case "extract" is felt to be
       a better choice of verb than "match", both due to the nature of the function
       and the overloading of meaning of the "match" verb within F#. *)

    let private extPLens l a =
        mapPLens a >?-> l

    let private mapContextExtract v =
           modL mpredLens (M.remove v) 
        >> modL msuccLens (M.remove v) 
        >> toContext v

    let private mapGraphExtract v p s =
           Map.remove v
        >> flip (L.fold (fun g (_, a) -> modPL (extPLens msuccLens a) (M.remove v) g)) p
        >> flip (L.fold (fun g (_, a) -> modPL (extPLens mpredLens a) (M.remove v) g)) s

    let private extractSpecific v (g: Graph<'v,'a,'b>) =
        match M.tryFind v g with
        | Some mc ->
            let c = mapContextExtract v mc
            let g = mapGraphExtract v (getL predLens c) (getL succLens c) g

            Some c, g
        | _ ->
            None, g

    let isEmpty (g: Graph<_,_,_>) =
        M.isEmpty g

    (* Maps

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

       Functions for listing elements of a graph. As we are using
       an optimized representation, these functions can be implemented in a more
       efficient way than the standard application of ufold, using the functions
       for the underlying representation data structure. *)

    let nodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> Node<'v,'a> list =
           M.toList
        >> L.map (fun (v, (_, l, _)) -> v, l)
        

    let edges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> Edge<'v,'b> list =
           M.toList 
        >> L.map (fun (v, (_, _, s)) -> (M.toList >> L.map (fun (v', b) -> v, v', b)) s) 
        >> L.concat

    let containsNode v : Graph<'v,'a,'b> -> bool =
        M.containsKey v

    let countNodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
           M.toList 
        >> L.length

    let countEdges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
           M.toList 
        >> L.map (fun (_, (_, _, s)) -> (M.toList >> L.length) s) 
        >> L.sum

    (* Inspection

       Functions for inspecting graphs, and common properties of nodes and
       edges within a graph. *)

    let tryFind v : Graph<'v,'a,'b> -> Node<'v,'a> option =
        M.tryFind v >> Option.map (fun (_, l, _) -> v, l)

    let find v =
        tryFind v >> function | Some n -> n | _ -> failwith (sprintf "Node %s Not Found" v)