(* file name: prim.mli
   created by: Daniel Winograd-Cort
   Last modified: 4/13/2017
   
   Description:
   This file contains code for converting Fuzz to OCaml (i.e., compilation)
*)

open Types

val curatorMemFileName : string ref
val runCompiled : string -> term -> (string, string) result