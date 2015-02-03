module Hekate

(* Introduction

   A library for working with graphs in a purely functional way, based
   on ideas from papers on inductive graphs and functional algorithms,
   principally by Martin Erwig. Those papers are particularly relevant to
   understanding the internals of this library.

   The following papers are referenced in commentary throughout the code:

   [Erwig:2001ho]: Inductive Graphs and Functional Graph Algorithms
                   http://dl.acm.org/citation.cfm?id=968434.968437 *)

(* Types

   Types based on the type representations of an inductively
   defined graph as defined in [Erwig:2001ho], extended to parameterize
   the type of identifier, allowing for a choice of identifying type
   beyond a simple integer.

   Single case unions are used to provide some additional safety
   and for some structure which may be useful in further extension
   via patterns, lenses, etc.

   Generic type parameters should be interpreted as follows:

   'i - the type of the Identifier (an integer in [Erwig:2001ho]
   'e - the type of the value associated with an edge, stored as part
        of an adjacency (Adj<_,_>) list.
   'n - the type of the value associated with a node (a character
        in [Erqig:2001ho] *)

type Node<'i> =
    | Node of 'i

type Adj<'e,'i> =
    | Adj of ('e * Node<'i>) list

type Context<'n,'e,'i> =
    | Context of Adj<'e,'i> * Node<'i> * 'n * Adj<'e,'i>

type Graph<'n,'e,'i> =
    | Graph of Context<'n,'e,'i> * Graph<'n,'e,'i>
    | Empty

(* Operators

   The & function from the [Erwig:2001ho] is defined as a custom
   operator (which is a function with infix form in F# anyway).

   To avoid overloading the existing & and to obtain the correct right
   associativity required for &, the & function is defined as the ^&
   operator. *)

let (^&) c g =
    Graph (c, g)

(* Functions *)

let isEmpty =
    function | Empty -> true
             | _ -> false

let rec ufold f u =
    function | Empty -> u
             | Graph (c, g) -> f c (ufold f u g)

let gmap f =
    ufold (fun c -> 
        (fun g -> (f c) ^& g)) Empty

let nodes g =
    ufold (fun (Context (_, v, _, _)) -> 
        (fun vs -> v :: vs)) [] g

let grev g =
    gmap (fun (Context (p, v, l, s)) -> 
        Context (s, v, l, p)) g

let undir g =
    gmap (fun (Context (Adj p, v, l, Adj s)) ->
        let ps = Adj (p @ s) in Context (ps, v, l, ps)) g

let suc (Context (_, _, _, Adj s)) =
    List.map snd s

// Experimental

let rec mmatch n =
    function | Graph ((Context (p, v, l, s)), g) when v = n -> Some (Context (p, v, l, s)), g
             | Graph (_, g) -> mmatch n g
             | Empty -> None, Empty

let gsuc n g =
    match mmatch n g with
    | Some (Context (_ , _, _, Adj s)), _ -> List.map snd s
    | _ -> []


