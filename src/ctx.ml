(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

open Types
open Syntax

(* ---------------------------------------------------------------------- *)
(* Context *)

(* A default empty context *)
let empty_context = { var_ctx = []; tyvar_ctx = []; }

let addVarToContext (v : (var_info * ty))
    (ctx : context) : context = 
  { ctx with var_ctx = v :: ctx.var_ctx; }

let addTyVarToContext (v : var_info) (ctx : context) : context = 
  { ctx with tyvar_ctx = v :: ctx.tyvar_ctx; }

(* ---------------------------------------------------------------------- *)
(* Context lookup for variables. *)
let lookup_var id ctx =
  let rec inner lst = 
    match lst with
        []                -> None
      | ((v,_) as r) :: l ->
        if v.v_name = id then Some r else inner l
  in inner ctx.var_ctx

(* Context lookup for type variables. *)
let lookup_tyvar id ctx = 
  let rec inner lst = 
    match lst with
        []    -> None
      | v::l  ->
        if v.v_name = id then Some v else inner l
  in inner ctx.tyvar_ctx

(* ---------------------------------------------------------------------- *)
(* Context shifting *)

(* Shift the type variable indexes wherever they are found in the context. *)
let ctx_ty_shift (n : int) (d : int) (ctx : context) = 
  {
    var_ctx = List.map (fun (v, ty) -> (v, ty_shiftTy n d ty)) ctx.var_ctx;
    tyvar_ctx = List.map (var_shift n d) ctx.tyvar_ctx;
  }

let ctx_var_shift (n : int) (d : int) (ctx : context) = 
  {
    var_ctx = List.map (fun (v, ty) -> (var_shift n d v, ty)) ctx.var_ctx;
    tyvar_ctx = ctx.tyvar_ctx;
  }

let extend_ctx_with_var (id : string) (bi : ty) (c : context) : (int * context) = 
  let size = (List.length c.var_ctx) + 1 in
  let new_var = {
    v_name  = id;
    v_type  = BiVar;
    v_index = 0;
    v_size  = size;
  } in (size, addVarToContext (new_var, bi) (ctx_var_shift 0 1 c))
  

let extend_ctx_with_tyvar (id : string) (c : context) : (int * context) =
  let size = (List.length c.tyvar_ctx) + 1 in
  let new_var = {
    v_name = id;
    v_type = BiTyVar;
    v_index = 0;
    v_size = size;
  } in (size, addTyVarToContext new_var (ctx_ty_shift 0 1 c))

let extend_ctx_with_var' id bi c = snd (extend_ctx_with_var id bi c)
let extend_ctx_with_tyvar' id  c = snd (extend_ctx_with_tyvar id  c)

(* Accessing to the variable in the context *)
let access_var   ctx i =
  if i > List.length ctx.var_ctx then
    Support.Error.message 1 Support.Options.General Support.FileInfo.dummyinfo "OOB access to var_ctx.  Context = %a" Print.pp_context ctx;
  List.nth ctx.var_ctx   i
let access_tyvar ctx i =
  if i > List.length ctx.tyvar_ctx then
    Support.Error.message 1 Support.Options.General Support.FileInfo.dummyinfo "OOB access to tyvar_ctx.  Context = %a" Print.pp_context ctx;
  List.nth ctx.tyvar_ctx   i

let modify_var (i : int) 
    (f : (var_info * ty) -> (var_info * ty))
    (ctx : context) : context = let foo i' v = if i = i' then f v else v
  in { ctx with var_ctx = List.mapi foo ctx.var_ctx; }
      

let merge_ctx = fun (ctx1 : context) (ctx2 : context) ->
  { var_ctx   = ctx1.var_ctx @ ctx2.var_ctx;
    tyvar_ctx = ctx1.tyvar_ctx @ ctx2.tyvar_ctx }
