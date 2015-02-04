module Hekate

(* Introduction

   A library for working with graphs in a purely functional way, based
   on ideas from papers on inductive graphs and functional algorithms,
   principally by Martin Erwig. Those papers are particularly relevant to
   understanding the internals of this library.

   The following papers are referenced in commentary throughout the code:

   [Erwig:2001ho]: Inductive Graphs and Functional Graph Algorithms
                   http://dl.acm.org/citation.cfm?id=968434.968437 *)

open Aether
open Aether.Operators

(* Prelude *)

let private flip f a b =
    f b a

let private swap (a, b) =
    (b, a)

(* Aliases

   For concision using commonly used modules, we alias List and Map to
   L and M respectively. *)

module L = List
module M = Map 

(* Definitional Types and Lenses

   Types defining data structures which form the logical programming model
   defined by the inductive definition of graphs, along with a set of lenses
   for access to nested data structures. *)

type Value =
    int

type Adj<'b> =
    ('b * Value) list

type Context<'a,'b> =
    Adj<'b> * Value * 'a * Adj<'b>

let private predLens : Lens<Context<_,'b>, Adj<'b>> =
    (fun (p, _, _, _) -> p), (fun p (_, v, l, s) -> (p, v, l, s))

let private valLens : Lens<Context<_,'b>, Value> =
    (fun (_, v, _, _) -> v), (fun v (p, _, l, s) -> (p, v, l, s))

let private succLens : Lens<Context<_,'b>, Adj<'b>> =
    (fun (_, _, _, s) -> s), (fun s (p, v, l, _) -> (p, v, l, s))

(* Representational Types and Lenses

   Types used for the underlying implementation of the graph, modelling the
   logically defined inductive definition as an optimized map, with sub-maps
   defining node adjacencies. *)

type MAdj<'b> =
    Map<Value,'b>

type MContext<'a,'b> =
    MAdj<'b> * 'a * MAdj<'b>

type MGraph<'a,'b> =
    Map<Value, MContext<'a,'b>>

type Graph<'a,'b> =
    MGraph<'a,'b>

let private mpredLens : Lens<MContext<_,'b>, MAdj<'b>> =
    (fun (p, _, _) -> p), (fun p (_, l, s) -> (p, l, s))

let private mvalLens : Lens<MContext<'a,_>, 'a> =
    (fun (_, l, _) -> l), (fun l (p, _, s) -> (p, l, s))

let private msuccLens : Lens<MContext<_,'b>, MAdj<'b>> =
    (fun (_, _, s) -> s), (fun s (p, l, _) -> (p, l, s))

(* Mappings

   Mapping functions between the two definitional and representational data
   structure families, used when translating between algorithmic operations applied
   to the definitional model, and modifications to the underlying data structure of
   the optmized representational model. *)

let private fromAdj<'b> : Adj<'b> -> MAdj<'b> =
    L.map swap >> M.ofList

let private toAdj<'b> : MAdj<'b> -> Adj<'b> =
    M.toList >> L.map swap

let private fromContext<'a,'b> : Context<'a,'b> -> MContext<'a,'b> =
    fun (p, _, l, s) -> fromAdj p, l, fromAdj s

let private toContext<'a,'b> v : MContext<'a,'b> -> Context<'a,'b> =
    fun (p, l, s) -> toAdj p, v, l, toAdj s

(* Isomorphisms

   Isomorphisms between data structures from the definitional and
   representational type families. *)

let private mcontextIso v : Iso<MContext<'a,'b>, Context<'a,'b>> =
    toContext v, fromContext

(* Graph *)

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

    let add c =
        mapGraphAdd c (getL valLens c) (getL predLens c) (getL succLens c)

    let empty : MGraph<'a,'b> =
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

    let private extractSpecific v (g: MGraph<'a,'b>) =
        match M.tryFind v g with
        | Some mc ->
            let c = mapContextExtract v mc
            let g = mapGraphExtract v (getL predLens c) (getL succLens c) g

            Some c, g
        | _ ->
            None, g

    let isEmpty (g: MGraph<_,_>) =
        M.isEmpty g

    (* Listing

       Functions for listing elements of a graph. As we are using
       an optimized representation, these functions can be implemented in a more
       efficient way than the standard application of ufold, using the functions
       for the underlying representation data structure. *)

    let nodesLabelled<'a,'b> : MGraph<'a,'b> -> (Value * 'a) list =
        M.toList >> L.map (fun (v, (_, l, _)) -> v, l)

    let nodes<'a,'b> : MGraph<'a,'b> -> Value list =
        nodesLabelled >> L.map fst

    (* Mapping

       Functions for mapping over contexts, or parts of contexts. Again, given
       an optimized representation, we use functions for the underlying data
       structure. *)

    let map f : MGraph<'a,'b> -> MGraph<'a,'b> =
        M.map (fun v mc -> (toContext v >> f >> fromContext) mc)

    let mapNodes f : MGraph<'a,'b> -> MGraph<'a,'b> =
        M.map (fun _ mc -> modL mvalLens f mc)

    let mapEdges f : MGraph<'a,'b> -> MGraph<'a,'b> =
        M.map (fun _ mc -> (modL mpredLens (M.map f) >> modL msuccLens (M.map f)) mc)
