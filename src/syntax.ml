(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Types
(* open Format *)
open Support.FileInfo

(* ---------------------------------------------------------------------- *)
(* Abstract Syntax Tree for sensitivities, terms and types                *)
(* ---------------------------------------------------------------------- *)

(* A helper function to modify the index of a variable.
var_shift : int         -- all variables with index greater than or equal to this value will be shifted
         -> int         -- the amount to shift (add) by
         -> var_info    -- var_info to shift
         -> var_info    -- Updated var_info *)
let var_shift o n v = { v with
  v_index = if o <= v.v_index then v.v_index + n else v.v_index;
  v_size  = v.v_size  + n;
}

let var_from_binder (index : int) (b : binder_info) : var_info = {
  v_index = index;
  v_name  = b.b_name;
  v_size  = b.b_size;
  v_type  = b.b_type;
}


(* ---------------------------------------------------------------------- *)
(* AST Mapping *)

(* Once again because of the potentially cyclic structure of the AST
   (that is, terms can contain sensitivites and sensitivites can contain 
   types), we define our ability to map over the AST in a mutually 
   recursive way.
   Note that these maps keep track of the type level Debruijn indeces. *)

(* Map over the terms of a sensitivity type *)
let rec si_map
  (ftm : term -> term)  (* The action to take on embedded terms *)
  (si : si)             (* The sensitivity to map over *)
  : si =
    let fsi si = si_map ftm si in
    match si with
    | SiInfty         -> si
    | SiZero          -> si
    | SiConst c       -> si
    | SiTerm  t       -> SiTerm (ftm t)
    | SiAdd  (s1, s2) -> SiAdd  (fsi s1, fsi s2)
    | SiMult (s1, s2) -> SiMult (fsi s1, fsi s2)
    | SiLub  (s1, s2) -> SiLub  (fsi s1, fsi s2)

(* Map over types *)
let rec ty_map
  (ntm : int)                   (* The number of regular variable binders deep we are *)
  (nty : int)                   (* The number of type variable binders deep we are *)
  (fv  : int -> int -> var_info -> ty) (* The action on type variables *)
  (fsi : int -> int -> si -> si)       (* The action on sesitivities *)
  (ty  : ty)                    (* The type to map over *)
  : ty = 
    let fty ntm nty ty = ty_map ntm nty fv fsi ty in
    match ty with
      TyVar v                 -> fv ntm nty v
    | TyPrim tp               -> TyPrim tp
    | TyPrim1 (tp, ty)        -> TyPrim1 (tp, fty ntm nty ty)
    (* ADT *)
    | TyUnion(ty1, ty2)       -> TyUnion    (fty ntm nty ty1, fty ntm nty ty2)
    | TyTensor(ty1, ty2)      -> TyTensor   (fty ntm nty ty1, fty ntm nty ty2)
    | TyAmpersand(ty1, ty2)   -> TyAmpersand(fty ntm nty ty1, fty ntm nty ty2)
    (* *)
    | TyLollipop(ty1, s, ty2) -> TyLollipop(fty ntm nty ty1, fsi ntm nty s, fty (ntm+1) nty ty2)
    
    | TyMu(b, ty)             -> TyMu(b, fty ntm (nty+1) ty)
    (* *)
    | TyForall(b, ty)         -> TyForall(b, fty ntm (nty+1) ty)
    (* We simply recurse down the abstraction and the argument,
     * incrementing the indices will be done when we encounter a forall
     * type. *)
    | TyTyApp(ty_abs, ty_arg) -> TyTyApp(fty ntm nty ty_abs, fty ntm nty ty_arg)

let rec tm_map
  (ntm : int)               (* The number of regular variable binders deep we are *)
  (nty : int)               (* The number of type variable binders deep we are *)
  (fv  : int -> int -> info -> var_info -> term) (* The action on regular variables *)
  (fty : int -> int -> ty -> ty)   (* Action to take on types *)
  (fsi : int -> int -> si -> si)   (* Action to take on sensitivites *)
  (tm : term)               (* The term to map over *)
  : term = 
  let ftm ntm nty tm = tm_map ntm nty fv fty fsi tm in
  match tm with
  | TmVar (i, v)                    ->
    fv ntm nty i v
  
  | TmPrim(i, p) ->
    TmPrim(i, p)
    
  | TmPrimFun(i, s,             ty, ttslst)  ->
    let ttslst' = List.map (fun (tm, ty, si) -> (ftm ntm nty tm, fty ntm nty ty, fsi ntm nty si)) ttslst in
    TmPrimFun(i, s, fty ntm nty ty, ttslst')
  
  | TmRecFun(i, bi,                 ty,                 tm, isRec)  ->
    TmRecFun(i, bi, fty (ntm+1) nty ty, ftm (ntm+1) nty tm, isRec)
  
  | TmPVal(i, tm) ->
    TmPVal(i, ftm ntm nty tm)
  
  | TmUnPVal(i, tm) ->
    TmUnPVal(i, ftm ntm nty tm)
  
  | TmBag(i,             ty,                        tmlst) ->
    TmBag(i, fty ntm nty ty, List.map (ftm ntm nty) tmlst)
  
  | TmVector(i,             ty,                        tmlst) ->
    TmVector(i, fty ntm nty ty, List.map (ftm ntm nty) tmlst)
  
  | TmPair(i,             tm1,             tm2)   ->
    TmPair(i, ftm ntm nty tm1, ftm ntm nty tm2)
  
  | TmTensDest(i, bi_x, bi_y,             tm,                 tm_i)   ->
    TmTensDest(i, bi_x, bi_y, ftm ntm nty tm, ftm (ntm+2) nty tm_i)
  
  | TmAmpersand(i,             tm1,             tm2)  ->
    TmAmpersand(i, ftm ntm nty tm1, ftm ntm nty tm2)
  
  | TmLeft(i,             tm,             ty)    ->
    TmLeft(i, ftm ntm nty tm, fty ntm nty ty)
  
  | TmRight(i,             tm,             ty)   ->
    TmRight(i, ftm ntm nty tm, fty ntm nty ty)
  
  | TmUnionCase(i,             tm, bi_l,                 tm_l, bi_r,                 tm_r)   ->
    TmUnionCase(i, ftm ntm nty tm, bi_l, ftm (ntm+1) nty tm_l, bi_r, ftm (ntm+1) nty tm_r)
  
  (* Abstraction and application *)
  | TmAbs(i, bi, (            si,             ty),                            orty,                 tm)  ->
    TmAbs(i, bi, (fsi ntm nty si, fty ntm nty ty), (Option.map (fty ntm nty)) orty, ftm (ntm+1) nty tm)
  
  | TmApp(i,             tm1,             tm2)    ->
    TmApp(i, ftm ntm nty tm1, ftm ntm nty tm2)
  
  (*  *)
  | TmLet(i, bi,             si,             tm,                 tm_i)  ->
    TmLet(i, bi, fsi ntm nty si, ftm ntm nty tm, ftm (ntm+1) nty tm_i)
  
  | TmStmt(i,             tm1,             tm2)  ->
    TmStmt(i, ftm ntm nty tm1, ftm ntm nty tm2)
  
  | TmSample(i, bi,             tm,                 tm_i) ->
    TmSample(i, bi, ftm ntm nty tm, ftm (ntm+1) nty tm_i)
  
  (* Recursive datatypes *)
  | TmFold(i,             ty,             tm)    ->
    TmFold(i, fty ntm nty ty, ftm ntm nty tm)
  
  | TmUnfold(i,             tm)    ->
    TmUnfold(i, ftm ntm nty tm)
  
  (* Type definition *)
  | TmTypedef(i, bi,                 ty,                 tm) ->
    TmTypedef(i, bi, fty ntm (nty+1) ty, ftm ntm (nty+1) tm)
  
  (* Type abstraction and application *)
  | TmTyApp (i,             tm,             ty)  ->
    TmTyApp (i, ftm ntm nty tm, fty ntm nty ty)
  
  | TmTyAbs (i, bi,                 tm)    ->
    TmTyAbs (i, bi, ftm ntm (nty+1) tm)
  
  (* Convenience *)
  | TmIfThenElse (i,             b,             t,             e)    ->
    TmIfThenElse (i, ftm ntm nty b, ftm ntm nty t, ftm ntm nty e)




(* ---------------------------------------------------------------------- *)
(* Convenient functions *)



(* Shift all of the type variables by the given amount *)
let rec ty_shiftTy (o : int) (n : int) (ty : ty) : ty = 
  let fv  _ k v  = TyVar (var_shift k n v)      in
  let fsi _ k si = si_shiftTy k n si            in
  ty_map 0 o fv fsi ty

and si_shiftTy (o : int) (n : int) (si : si) : si =
  si_map (tm_shiftTy o n) si

and tm_shiftTy (o : int) (n : int) (tm : term) : term = 
  let fv _ _ i v = TmVar(i,v)          in
  let fty _ k ty = ty_shiftTy k n ty in
  let fsi _ k si = si_shiftTy k n si in
  tm_map 0 o fv fty fsi tm


(* Shift all of the regular variables by the given amount *)
let rec tm_shiftTm (o : int) (n : int) (tm : term) : term = 
  let fv  k _ i v = TmVar (i, var_shift k n v) in
  let fty k _ ty = ty_shiftTm k n ty         in
  let fsi k _ si = si_shiftTm k n si         in
  tm_map o 0 fv fty fsi tm

and ty_shiftTm (o : int) (n : int) (ty : ty) : ty = 
  let fv _ _ v = TyVar v  in
  ty_map o 0 fv (fun k _ -> si_shiftTm k n) ty

and si_shiftTm (o : int) (n : int) (si : si) : si =
  si_map (tm_shiftTm o n) si


let rec tm_mapTm (f : int -> info -> var_info -> term) (k : int) (tm : term) : term = 
  let fv  ktm _ = f ktm in
  let fty ktm _ ty = ty_mapTm f ktm ty in
  let fsi ktm _ si = si_mapTm f ktm si in
  tm_map k 0 fv fty fsi tm
and ty_mapTm f k ty = 
  let fv _ _ v = TyVar v in
  ty_map k 0 fv (fun ktm _ -> si_mapTm f ktm) ty
and si_mapTm f k si = si_map (tm_mapTm f k) si




(* This performs a substitution of the form ty[t/x] for type variables.
   It can be called on types (ty_substTy) or terms (tm_substTy).  *)
let rec ty_substTy
    (t : ty)    (* The type to replace the variable with. *)
    (ktm : int) (* Initially, call with 0. *)
    (x : int)   (* The Debruijn index of the type variable we are replacing. *)
    (ty : ty)   (* The input type over which we are doing the substitution. *)
    : ty =
  let fv ktm kty v = 
    if kty = v.v_index then
      ty_shiftTm 0 ktm (ty_shiftTy 0 kty t)
    else
      TyVar (var_shift kty (-1) v)    in
  let fsi ktm kty si = si_substTy t ktm kty si  in
  ty_map ktm x fv fsi ty

and si_substTy (t : ty) (ktm : int) (x : int) (si : si) : si =
  si_map (tm_substTy t ktm x) si

and tm_substTy (t : ty) (ktm : int) (x : int) (tm : term) : term =
  let fv _ _ i v = TmVar(i,v) in
  tm_map ktm x fv (ty_substTy t) (si_substTy t) tm

(* ty_unfold is used to unfold mu types *)
let ty_unfold ty = match ty with
  | TyMu(b, ty_i) -> ty_substTy (TyMu (b, ty_i)) 0 0 ty_i
  | _             -> ty


(* This performs a substitution of the form tm[t/x] for variables. *)
let rec tm_substTm
    (t : term)  (* The term to replace the variable with. *)
    (x : int)   (* The Debruijn index of the variable we are replacing. *)
    (kty : int) (* Initially, call with 0. *)
    (tm : term) (* The input term over which we are doing the substitution. *)
    : term =
  let fv ktm kty i v = if ktm = v.v_index
    then tm_shiftTy 0 kty (tm_shiftTm 0 ktm t)
    else TmVar (i, var_shift ktm (-1) v) in
  let fty k kty ty = ty_substTm t k kty ty  in
  let fsi k kty si = si_substTm t k kty si  in
  tm_map x kty fv fty fsi tm

and ty_substTm (t : term) (x : int) (kty : int) (ty : ty) : ty = 
  let fv _ _ v = TyVar v in
  ty_map x kty fv (si_substTm t) ty
and si_substTm (t : term) (x : int) (kty : int) (si : si) : si = 
  si_map (tm_substTm t x kty) si




(************************************************************************)
(* Syntactic equality *)

let rec for_all2 p lst1 lst2 = match lst1,lst2 with
  | x::xs,y::ys -> p x y && for_all2 p xs ys
  | _ -> true

(* This is a special equality that makes sure like numbers are equal even if their types don't match *)
let rec primTmEq (t1 : term_prim) (t2 : term_prim) : bool =
  match t1, t2 with
  | PrimTNum(n1),     PrimTClipped(n2) -> n1 = n2
  | PrimTNum(n1),     PrimTInt(n2)     -> n1 = float_of_int n2
  | PrimTClipped(n1), PrimTNum(n2)     -> n1 = n2
  | PrimTClipped(n1), PrimTInt(n2)     -> n1 = float_of_int n2
  | PrimTInt(n1),     PrimTNum(n2)     -> float_of_int n1 = n2
  | PrimTInt(n1),     PrimTClipped(n2) -> float_of_int n1 = n2
  | _,_ -> t1 = t2

let rec tmEq (t1 : term) (t2 : term) : bool = 
  match t1, t2 with
  | TmVar(_,v1), 
    TmVar(_,v2) -> v1.v_index = v2.v_index
  | TmPrim(_,p1), 
    TmPrim(_,p2) -> p1 = p2
  | TmPrimFun(_,_,ty1,ttsl1), 
    TmPrimFun(_,_,ty2,ttsl2) -> tyEq ty1 ty2 && for_all2 
        (fun (tm1,ty1,si1) (tm2,ty2,si2) -> tmEq tm1 tm2 && tyEq ty1 ty2 && siEq si1 si2) ttsl1 ttsl2
  | TmPVal(_, tm1),
    TmPVal(_, tm2) -> tmEq tm1 tm2 (* NOTE: Probabilistic values are compared on structural equality only *)
  | TmUnPVal(_, tm1),
    TmUnPVal(_, tm2) -> tmEq tm1 tm2
  | TmBag(_, ty1, tml1), 
    TmBag(_, ty2, tml2) -> tyEq ty1 ty2 && for_all2 tmEq tml1 tml2
  | TmVector(_, ty1, tml1), 
    TmVector(_, ty2, tml2) -> tyEq ty1 ty2 && for_all2 tmEq tml1 tml2
  | TmPair(_, t1a, t1b),
    TmPair(_, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmTensDest(_, _, _, t1a, t1b),
    TmTensDest(_, _, _, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmAmpersand(_, t1a, t1b),
    TmAmpersand(_, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmLeft(_, tm1, ty1),
    TmLeft(_, tm2, ty2) -> tyEq ty1 ty2 && tmEq tm1 tm2
  | TmRight(_, tm1, ty1),
    TmRight(_, tm2, ty2) -> tyEq ty1 ty2 && tmEq tm1 tm2
  | TmUnionCase(_, t1a, _, t1b, _, t1c),
    TmUnionCase(_, t2a, _, t2b, _, t2c) -> tmEq t1a t2a && tmEq t1b t2b && tmEq t1c t2c
  | TmApp(_, t1a, t1b),
    TmApp(_, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmAbs(_, _, (si1, ty1), tyo1, t1),
    TmAbs(_, _, (si2, ty2), tyo2, t2) -> siEq si1 si2 && tyEq ty1 ty2 
                                      && (match tyo1, tyo2 with Some t, Some t' -> tyEq t t' | _,_ -> tyo1 = tyo2)
                                      && tmEq t1 t2
  | TmFold(_, ty1, tm1),
    TmFold(_, ty2, tm2) -> tyEq ty1 ty2 && tmEq tm1 tm2
  | TmUnfold(_, tm1),
    TmUnfold(_, tm2) -> tmEq tm1 tm2
  | TmLet(_, _, si1, t1a, t1b),
    TmLet(_, _, si2, t2a, t2b) -> siEq si1 si2 && tmEq t1a t2a && tmEq t1b t2b
  | TmStmt(_, t1a, t1b),
    TmStmt(_, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmRecFun(_, _, ty1, t1, b1),
    TmRecFun(_, _, ty2, t2, b2) -> tyEq ty1 ty2 && tmEq t1 t2 && (b1 = b2)
  | TmSample(_, _, t1a, t1b),
    TmSample(_, _, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmTyAbs(_, _, tm1),
    TmTyAbs(_, _, tm2) -> tmEq tm1 tm2
  | TmTyApp(_, tm1, ty1),
    TmTyApp(_, tm2, ty2) -> tmEq tm1 tm2 && tyEq ty1 ty2 
  | TmTypedef(_, _, ty1, tm1),
    TmTypedef(_, _, ty2, tm2) -> tyEq ty1 ty2 && tmEq tm1 tm2
  | TmIfThenElse(_, t1a, t1b, t1c),
    TmIfThenElse(_, t2a, t2b, t2c) -> tmEq t1a t2a && tmEq t1b t2b && tmEq t1c t2c
  | _,_ -> false

and tyEq (t1 : ty) (t2 : ty) : bool = 
  match t1, t2 with
  | TyVar v1, 
    TyVar v2 -> v1.v_index = v2.v_index
  | TyPrim p1,
    TyPrim p2 -> p1 = p2
  | TyPrim1(p1, ty1),
    TyPrim1(p2, ty2) -> p1 = p2 && tyEq ty1 ty2
  | TyUnion(ty1a, ty1b),
    TyUnion(ty2a, ty2b) -> tyEq ty1a ty2a && tyEq ty1b ty2b
  | TyTensor(ty1a, ty1b),
    TyTensor(ty2a, ty2b) -> tyEq ty1a ty2a && tyEq ty1b ty2b
  | TyAmpersand(ty1a, ty1b),
    TyAmpersand(ty2a, ty2b) -> tyEq ty1a ty2a && tyEq ty1b ty2b
  | TyLollipop(ty1a, si1, ty1b),
    TyLollipop(ty2a, si2, ty2b) -> tyEq ty1a ty2a && siEq si1 si2 && tyEq ty1b ty2b
  | TyMu(_, ty1),
    TyMu(_, ty2) -> tyEq ty1 ty2
  | TyForall(_, ty1),
    TyForall(_, ty2) -> tyEq ty1 ty2
  | TyTyApp(TyForall(_, abs), arg),
    ty2 -> tyEq (ty_substTy arg 0 0 abs) ty2
  | ty1,
    TyTyApp(TyForall(_, abs), arg) -> tyEq ty1 (ty_substTy arg 0 0 abs)
  | _,_ -> false

and siEq (s1 : si) (s2 : si) : bool = 
  match s1, s2 with
  | SiInfty, SiInfty -> true
  | SiZero, SiZero -> true
  | SiZero, SiConst f2 -> 0.0 = f2
  | SiConst f1, SiZero -> f1 = 0.0
  | SiConst f1, SiConst f2 -> f1 = f2
  | SiTerm t1, SiTerm t2 -> tmEq t1 t2
  | SiAdd(si1a, si1b),
    SiAdd(si2a, si2b) -> siEq si1a si2a && siEq si1b si2b
  | SiMult(si1a, si1b),
    SiMult(si2a, si2b) -> siEq si1a si2a && siEq si1b si2b
  | SiLub(si1a, si1b),
    SiLub(si2a, si2b) -> siEq si1a si2a && siEq si1b si2b
  | _,_ -> false

(************************************************************************)
(* Valuation *)

let rec tmIsVal (t : term) : bool = match t with
  | TmPrim(_,_)     -> true
  | TmPVal(_,_)     -> true
  | TmBag(_,_,_)    -> true
  | TmVector(_,_,_) -> true
  | TmPair(_,t1,t2) -> tmIsVal t1 && tmIsVal t2
  | TmAmpersand(_, t1, t2)  -> tmIsVal t1 && tmIsVal t2
  | TmLeft(_,t,_)   -> tmIsVal t
  | TmRight(_,t,_)  -> tmIsVal t
  | TmAbs(_,_,_,_,_)    -> true
  | TmFold(_,_,_)   -> true
  | TmTyAbs(_,_,_)  -> true
  | _               -> false

let rec tyIsVal (t : ty) : bool = match t with
  | TyVar _             -> false
  | TyPrim  _           -> true
  | TyPrim1(_, t)       -> tyIsVal t
  | TyUnion(t1, t2)     -> tyIsVal t1 && tyIsVal t2
  | TyTensor(t1, t2)    -> tyIsVal t1 && tyIsVal t2
  | TyAmpersand(t1, t2) -> tyIsVal t1 && tyIsVal t2
  | TyLollipop(t1,_,t2) -> tyIsVal t1 && tyIsVal t2
  | TyMu(_,t)           -> true
  | TyForall(_,_)       -> true
  (* TODO: do we want to simplify and then check if it's a value? *)
  | TyTyApp(TyForall(_, abs), arg) -> tyIsVal (ty_substTy arg 0 0 abs)
  | _ -> false



(************************************************************************)
(* File info extraction *)

let tmInfo t = match t with
    TmVar(fi, _)                -> fi
  | TmPrim(fi, _)               -> fi
  | TmPrimFun(fi, _, _, _)      -> fi
  
  | TmPVal(fi, _)               -> fi
  | TmUnPVal(fi, _)             -> fi
  | TmBag(fi, _, _)             -> fi
  | TmVector(fi, _, _)          -> fi

  | TmPair(fi, _, _)            -> fi
  | TmTensDest(fi,_,_,_,_)      -> fi

  | TmAmpersand(fi,_,_)         -> fi
  | TmLeft(fi,_,_)              -> fi
  | TmRight(fi,_,_)             -> fi
  | TmUnionCase(fi,_,_,_,_,_)   -> fi

  (* Abstraction and application *)
  | TmAbs(fi,_,_,_,_)           -> fi
  | TmApp(fi, _, _)             -> fi

  (* Bindings *)
  | TmLet(fi,_,_,_,_)           -> fi
  | TmStmt(fi,_,_)              -> fi
  | TmRecFun(fi,_,_,_,_)        -> fi
  | TmSample(fi,_,_,_)          -> fi

  (* Recursive datatypes *)
  | TmFold(fi,_,_)              -> fi
  | TmUnfold(fi,_)              -> fi

  (* Type abstraction and application *)
  | TmTyApp (fi, _, _)          -> fi
  | TmTyAbs (fi, _, _)          -> fi

  (* Misc *)
  | TmTypedef(fi,_,_,_)         -> fi

  (* Convenience *)
  | TmIfThenElse (fi,_,_,_)     -> fi
