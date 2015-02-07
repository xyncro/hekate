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

let private mapFst f (a, b) =
    (f a, b)

let private mapSnd f (a, b) =
    (a, f b)

let private mapOne f a _ =
    f a

let private mapTwo f _ b =
    f b

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
   "compose". *)

let private compMAdjPLens l a v =
    mapPLens a >?-> l >??> mapPLens v

let private composeGraph c v p s =
       setPL (mapPLens v <?-> mcontextIso v) c
    >> flip (L.fold (fun g (l, a) -> setPL (compMAdjPLens msuccLens a v) l g)) p
    >> flip (L.fold (fun g (l, a) -> setPL (compMAdjPLens mpredLens a v) l g)) s

let private compose (c: Context<'v,'a,'b>) : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
    composeGraph c (getL valLens c) (getL predLens c) (getL succLens c)

let private empty : Graph<'v,'a,'b> =
    M.empty

(* Decomposition

   Functions for decomposing an existent graph through a process
   of matching, as defined in the table of Basic Graph Operations
   in [Erqig:2001ho].
   
   The Empty-match function is named "isEmpty" and forms part of the public
   API for Hekate and is thus defined later in the Graph module. The "&-match"
   function becomes "decompose", and the "&v" function becomes "decomposeSpecific", to
   better align with F# expectations. *)

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

let private isEmpty<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> bool =
    M.isEmpty

(* Functions

   Useful functions defined in terms of the Basic Graph Operations, though
   not expected to be used directly. *)

let private context v =
       decomposeSpecific v
    >> function | Some c, _ -> Some c
                | _ -> None

let rec private ufold f u =
       decompose
    >> function | Some c, g -> f c (ufold f u g)
                | _ -> u

(* Graph

   The "public" API to Hekate is exposed as the Graph module, providing
   a API stylistically similar to common F# modules like List, Map, etc.

   F# naming conventions have been applied where relevant, in contrast to
   either FGL or [Erwig:2001ho]. *)

module Graph =

    (* Construction *)

    let private fold f xs : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
        flip (L.fold (flip f)) xs

    let addNode ((v, l): LNode<'v,'a>) =
#if inductive
        compose ([], v, l, [])
#else
        M.add v (Map.empty, l, Map.empty)
#endif

    let removeNode v =
           decomposeSpecific v 
        >> snd

    let addEdge ((v1, v2, e): LEdge<'v,'b>) =
#if inductive
           decomposeSpecific v1
        >> function | Some (p, v, l, s), g -> compose (p, v, l, (e, v2) :: s) g
                    | _, g -> g
#else
           modPL (mapPLens v1 >?-> msuccLens) (M.add v2 e)
        >> modPL (mapPLens v2 >?-> mpredLens) (M.add v1 e)
#endif

    let removeEdge ((v1, v2): Edge<'v>) =
           decomposeSpecific v1
        >> function | Some (p, v, l, s), g -> compose (p, v, l, L.filter (fun (_, v') -> v' <> v2) s) g
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
#if inductive
           context v
        >> Option.isSome
#else
        M.containsKey v
#endif

    let countNodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
#if inductive
        ufold (fun _ i -> 
            i + 1) 0
#else
           M.toList 
        >> L.length
#endif

    let countEdges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> int =
#if inductive
        ufold (fun (p, _, _, s) i -> 
            i + L.length p + L.length s) 0
#else
           M.toList 
        >> L.map (fun (_, (_, _, s)) -> (M.toList >> L.length) s)
        >> L.sum
#endif

    (* Mapping *)

    let map f : Graph<'v,'a,'b> -> Graph<'v,'c,'d> =
#if inductive
        ufold (fun c g -> 
            compose (f c) g) empty
#else
        M.map (fun v mc -> (toContext v >> f >> fromContext) mc)
#endif

    let mapNodes f : Graph<'v,'a,'b> -> Graph<'v,'c,'b> =
#if inductive
        map (fun (p, v, l, s) -> 
            (p, v, f l, s))
#else
        M.map (mapTwo (fun (p, l, s) -> p, f l, s))
#endif

    let mapEdges f : Graph<'v,'a,'b> -> Graph<'v,'a,'c> =
#if inductive
        map (fun (p, v, l, s) -> 
            (L.map (mapFst f) p, v, l, L.map (mapFst f) s))
#else
        M.map (mapTwo (fun (p, l, s) -> M.map (mapTwo f) p, l, M.map (mapTwo f) s))
#endif

    (* Projection *)

    let nodes<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LNode<'v,'a> list =
#if inductive
        ufold (fun (_, v, l, _) ns -> 
            (v, l) :: ns) []
#else
           M.toList
        >> L.map (fun (v, (_, l, _)) -> v, l)
#endif

    let edges<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> LEdge<'v,'b> list =
#if inductive
        ufold (fun (p, v, _, s) es -> 
              L.map (fun (l, v') -> v', v, l) p 
            @ L.map (fun (l, v') -> v, v', l) s 
            @ es) []
#else
           M.toList 
        >> L.map (fun (v, (_, _, s)) -> (M.toList >> L.map (fun (v', b) -> v, v', b)) s) 
        >> L.concat
#endif

    let rev<'v,'a,'b when 'v: comparison> : Graph<'v,'a,'b> -> Graph<'v,'a,'b> =
#if inductive
        map (fun (p, v, l, s) -> 
            (s, v, l, p))
#else
        M.map (fun _ (p, l, s) -> (s, l, p))
#endif

    (* Query *)

    let tryFindNode v : Graph<'v,'a,'b> -> LNode<'v,'a> option =
#if inductive
           context v
        >> Option.map (fun (_, _, l, _) -> v, l)
#else
           M.tryFind v
        >> Option.map (fun (_, l, _) -> v, l)
#endif

    let findNode v =
           tryFindNode v 
        >> function | Some n -> n 
                    | _ -> failwith (sprintf "Node %A Not Found" v)

    (* Adjacency/Degree *)

    let neighbours v =
#if inductive
           context v
        >> Option.map (fun (p, _, _, s) -> L.map swap p @ L.map swap s)
#else
           M.tryFind v
        >> Option.map (fun (p, _, s) -> M.toList p @ M.toList s)
#endif

    let successors v =
#if inductive
           context v
        >> Option.map (fun (_, _, _, s) -> L.map swap s)
#else
           M.tryFind v
        >> Option.map (fun (_, _, s) -> M.toList s)
#endif

    let predecessors v =
#if inductive
           context v
        >> Option.map (fun (p, _, _, _) -> L.map swap p)
#else
           M.tryFind v
        >> Option.map (fun (p, _, _) -> M.toList p)
#endif

    let outward v =
#if inductive
           context v
        >> Option.map (fun (_, _, _, s) -> L.map (fun (b, v') -> v, v', b) s)
#else
           M.tryFind v
        >> Option.map (fun (_, _, s) -> (M.toList >> L.map (fun (v', b) -> v, v', b)) s)
#endif

    let inward v =
#if inductive
           context v
        >> Option.map (fun (p, _, _, _) -> L.map (fun (b, v') -> v', v, b) p)
#else
           M.tryFind v
        >> Option.map (fun (p, _, _) -> (M.toList >> L.map (fun (v', b) -> v', v, b)) p)
#endif

    let degree v =
#if inductive
           context v
        >> Option.map (fun (p, _, _, s) -> L.length p + L.length s)
#else
           M.tryFind v
        >> Option.map (fun (p, _, s) -> (M.toList >> L.length) p + (M.toList >> L.length) s)
#endif

    let outwardDegree v =
#if inductive
           context v
        >> Option.map (fun (_, _, _, s) -> L.length s)
#else
           M.tryFind v
        >> Option.map (fun (_, _, s) -> (M.toList >> L.length) s)
#endif

    let inwardDegree v =
#if inductive
           context v
        >> Option.map (fun (p, _, _, _) -> L.length p)
#else
           M.tryFind v
        >> Option.map (fun (p, _, _) -> (M.toList >> L.length) p)
#endif
