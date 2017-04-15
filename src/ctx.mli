(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Types

val empty_context : context

(* Name based functions for the parser *)
val lookup_var   : string -> context -> (var_info * ty) option
val lookup_tyvar : string -> context -> var_info option

val extend_ctx_with_var     : string -> ty -> context -> (int * context)
val extend_ctx_with_tyvar   : string -> context -> (int * context)

val extend_ctx_with_var'    : string -> ty -> context -> context
val extend_ctx_with_tyvar'  : string -> context -> context

val access_var      : context -> int -> (var_info * ty)
val access_tyvar    : context -> int -> var_info

val modify_var : int -> ((var_info * ty) -> (var_info * ty))
    -> context -> context

val merge_ctx : context -> context -> context
