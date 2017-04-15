(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Support.FileInfo
open Types

(* A helper function to modify the index of a variable.
var_shift : int         -- all variables with index greater than or equal to this value will be shifted
         -> int         -- the amount to shift (add) by
         -> var_info    -- var_info to shift
         -> var_info    -- Updated var_info *)
val var_shift : int -> int -> var_info -> var_info

val var_from_binder : int -> binder_info -> var_info

(* ---------------------------------------------------------------------- *)
(* AST Mapping *)

(* Shift all the open indexes by n *)
val ty_shiftTy  : int -> int -> ty -> ty
(* val tm_shiftTm  : int -> int -> term -> term *)

(* Apply a function to all term variables *)
val ty_mapTm : (int -> info -> var_info -> term) -> int -> ty -> ty
val si_mapTm : (int -> info -> var_info -> term) -> int -> si -> si

(* Capture avoiding sub, the term must be dependent on the number of
   binders under it is replaced *)
val ty_substTy  : ty -> int -> int -> ty -> ty
val tm_substTy  : ty -> int -> int -> term -> term

(* Unfold a mu type *)
val ty_unfold : ty -> ty

val tm_substTm : term -> int -> int -> term -> term
val ty_substTm : term -> int -> int -> ty -> ty

val tmEq : term -> term -> bool
val tmIsVal : term -> bool
val tyIsVal : ty -> bool

val tmInfo : term -> info
