(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
   
   Type checking and synthesis engine for Fuzz.
*)
open Types
open Syntax
open Print

open Support.FileInfo

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y


let typing_error fi = Support.Error.error_msg    Support.Options.TypeChecker fi
let typing_error_pp = Support.Error.error_msg_pp Support.Options.TypeChecker

let ty_warning fi = Support.Error.message 1 Support.Options.TypeChecker fi
let ty_info    fi = Support.Error.message 2 Support.Options.TypeChecker fi
let ty_info2   fi = Support.Error.message 3 Support.Options.TypeChecker fi
let ty_debug   fi = Support.Error.message 4 Support.Options.TypeChecker fi
let ty_debug2  fi = Support.Error.message 5 Support.Options.TypeChecker fi
let ty_debug3  fi = Support.Error.message 6 Support.Options.TypeChecker fi


(* Reader/Error monad for type-checking *)
module TypeCheckMonad = struct
  open Ctx
  
  let (>>=) (m : 'a checker) (f : 'a -> 'b checker) : 'b checker =
    fun inp ->
      match m inp with
      | Ok res  -> f res inp
      | Error e -> Error e
  
  let (>>) m f = m >>= fun _ -> f
  
  let return (x : 'a) : 'a checker = fun _ -> Ok x
  
  let rec mapM (f : 'a -> 'b checker) (lst : 'a list) : ('b list) checker = 
    match lst with
      | []    -> return []
      | x::xs -> f x        >>= fun y  ->
                 mapM f xs  >>= fun ys ->
                 return (y::ys)
  
  let rec mapM2 (f : 'a -> 'b -> 'c checker) (lstA : 'a list) (lstB : 'b list) : ('c list) checker = 
    match lstA, lstB with
      | x::xs, y::ys -> f x y         >>= fun z  ->
                        mapM2 f xs ys >>= fun zs ->
                        return (z::zs)
      | _   -> return []
  
  let fail (i : info) (e : ty_error_elem) : 'a checker = fun (_,d,_,_) ->
    Error (d, { i = i; v = e })
  
  let failToResult (m : 'a checker) : (('a, int * ty_error_elem withinfo) result) checker =
    fun inp -> Ok (m inp)
  
  let on_error (on_err : 'a checker) (m : 'a checker) : 'a checker =
    fun inp -> match m inp with
      | Ok res -> Ok res
      | Error e -> on_err inp
  
  let get_ctx : context checker =
    fun (ctx,d,b,p) -> Ok ctx
  
  let get_pinfo : ((int * pinterp) option) checker =
    fun (ctx,d,b,pinfo) -> Ok pinfo
  
  let with_pinfo (pinfo : (int * pinterp) option) (m : 'a checker) : 'a checker =
    fun (ctx,d,b,p) -> m (ctx, d, b, pinfo)
  
  let should_check_sens (ifnot : 'a checker) (ifso : 'a checker) : 'a checker =
    fun ((ctx,d,b,p) as inp) -> if b then ifso inp else ifnot inp
  
  let get_ctx_length : int checker =
    get_ctx >>= fun ctx ->
    return @@ List.length ctx.var_ctx
  
  let get_depth : int checker = 
    fun (ctx,d,b,p) -> Ok d
  
  let with_depth (depth : int) (m : 'a checker) : 'a checker = 
    fun (ctx,d,b,p) -> m (ctx, depth, b, p)
  
  let deeper (m : 'a checker) : 'a checker =
    fun (ctx,d,b,p) -> m (ctx, d+1, b, p)
  
  let with_new_ctx (f : context -> context) (m : 'a checker) : 'a checker =
    fun (ctx,d,b,p) -> m (f ctx,d,b,p)
  
  (* Extend the context with a type binding and run a computation *)
  let with_extended_ty_ctx (v : string) (m : 'a checker) : 'a checker =
    with_new_ctx (extend_ctx_with_tyvar' v) m
  
  (* Extend the context with a value binding and run a computation. The
     computation is assumed to produce a list of results, one for each
     variable in the extended context. That list is destructed, and the
     result corresponding to the new variable is returned separately for
     convenience. *)
  let with_extended_ctx (i : info) (v : string) (ty : ty) (m : ('a * 'b list) checker) :
      ('a * 'b * 'b list) checker =
    with_new_ctx (extend_ctx_with_var' v ty) m >>= fun (res, res_ext_ctx) ->
    match res_ext_ctx with
    | res_v :: res_ctx -> return (res, res_v, res_ctx)
    | [] -> fail i @@ Internal "Computation on extended context didn't produce enough results"
  
  (* Similar to the one above, but with two variables. vx has index 1 in
     the extended context, while vy has index 0. The order of the
     returned results matches those of the arguments. *)
  let with_extended_ctx_2 (i : info)
      (vx : string) (tyx : ty) (vy : string) (tyy : ty)
      (m : ('a * 'b list) checker) : ('a * 'b * 'b * 'b list) checker =
    with_new_ctx (fun ctx -> extend_ctx_with_var' vy tyy
                            (extend_ctx_with_var' vx tyx ctx)) m >>= fun (res, res_ext_ctx) ->
    match res_ext_ctx with
    | res_y :: res_x :: res_ctx -> return (res, res_x, res_y, res_ctx)
    | _ -> fail i @@ Internal "Computation on extended context didn't produce enough results"
  
  (* Get the type of the given variable *)
  let get_var_ty (v : var_info) : ty checker =
    get_ctx >>= fun ctx ->
    return @@ snd (access_var ctx v.v_index)

  (* Recursively normalize type-application *)
  let rec ty_normalize_app (ty : ty) : ty checker =
    match ty with
    | TyTyApp(TyForall(_, abs), arg) ->
       ty_normalize_app abs >>= fun abs' ->
       ty_normalize_app arg >>= fun arg' ->
       ty_normalize_app @@ ty_substTy arg' 0 0 abs'
    | TyTyApp(t1, t2) ->
       ty_normalize_app t1 >>= fun t1' ->
       ty_normalize_app t2 >>= fun t2' ->
       ty_normalize_app @@ TyTyApp(t1', t2')
    | TyPrim1 (prim, ty) ->
       ty_normalize_app ty >>= fun ty' ->
       return @@ TyPrim1(prim, ty')
    | TyUnion(tl, tr) ->
       ty_normalize_app tl >>= fun tl' ->
       ty_normalize_app tr >>= fun tr' ->
       return @@ TyUnion(tl', tr')
    | TyTensor(tl, tr) ->
       ty_normalize_app tl >>= fun tl' ->
       ty_normalize_app tr >>= fun tr' ->
       return @@ TyTensor(tl', tr')
    | TyAmpersand(tl, tr) ->
       ty_normalize_app tl >>= fun tl' ->
       ty_normalize_app tr >>= fun tr' ->
       return @@ TyAmpersand(tl', tr')
    | TyLollipop (targ, si, tbody) ->
       ty_normalize_app targ  >>= fun targ' ->
       ty_normalize_app tbody >>= fun tbody' ->
       return @@ TyLollipop(targ', si, tbody')
    | TyMu (bi, ty) ->
       ty_normalize_app ty >>= fun ty' ->
       return @@ TyMu(bi, ty')
    | TyForall (bi, ty) ->
       ty_normalize_app ty >>= fun ty' ->
       return @@ TyForall(bi, ty')
    | _ -> return ty
end

module TypeSens = struct
  open TypeCheckMonad
  
  (* Constants *)
  let si_zero  = SiZero
  let si_nearzero = SiConst 0.0
  let si_one   = SiConst 1.0
  let si_infty = SiInfty
  
  let rec si_simpl' (si : si) : si checker = match si with
    | SiInfty   -> return @@ si
    | SiZero    -> return @@ si
    | SiConst _ -> return @@ si (* This value should be direct from the lexer/parser, so it should be good *)
    | SiTerm(TmPrim(_, PrimTNum(f)) as t) -> 
        begin match classify_float f with
          | FP_normal     when f >= 0.0 -> return @@ SiConst f
          | FP_subnormal  when f >= 0.0 -> return @@ SiConst f
          | FP_zero                     -> return @@ si_zero
          | FP_infinite   when f >= 0.0 -> return si_infty
          | _ -> fail (tmInfo t) @@ BadSensTerm t
        end
    | SiTerm(TmPrim(_, PrimTInt(i))) when i > 0 -> return @@ SiConst (float_of_int i)
    | SiTerm(TmPrim(_, PrimTInt(i))) when i = 0 -> return @@ si_zero
    | SiTerm(TmPrim(_, PrimTInt(_)) as t)       -> fail (tmInfo t) @@ BadSensTerm t
    | SiTerm(TmPrim(_, PrimTBool(b))) -> return @@ if b then si_infty else si_zero
    | SiTerm(t) -> fail (tmInfo t) @@ UnevalSensTerm t
    | SiAdd (si1, si2)  ->
        si_simpl' si1 >>= fun si1 ->
        si_simpl' si2 >>= fun si2 ->
        begin match si1, si2 with
          | SiInfty, _  -> return @@ SiInfty
          | _, SiInfty  -> return @@ SiInfty
          | SiZero, s -> return @@ s
          | s, SiZero -> return @@ s
          | SiConst x1, SiConst x2 -> return @@ SiConst (x1 +. x2)
          | _   -> fail dummyinfo @@ Internal "Bad state when adding sensitivities"
        end
    | SiMult(si1, si2)  -> 
        si_simpl' si1 >>= fun si1 ->
        si_simpl' si2 >>= fun si2 ->
        begin match si1, si2 with
          | SiZero, _ -> return @@ si_zero
          | _, SiZero -> return @@ si_zero
          | SiInfty, _  -> return @@ SiInfty
          | _, SiInfty  -> return @@ SiInfty
          | SiConst x1, SiConst x2 -> return @@ SiConst (x1 *. x2)
          | _   -> fail dummyinfo @@ Internal "Bad state when multiplying sensitivities"
        end
    | SiLub (si1, si2)  -> 
        si_simpl' si1 >>= fun si1 ->
        si_simpl' si2 >>= fun si2 ->
        begin match si1, si2 with
          | SiInfty, _            -> return @@ SiInfty
          | _, SiInfty            -> return @@ SiInfty
          | SiZero, s -> return @@ s
          | s, SiZero -> return @@ s
          | SiConst x, SiConst y  -> return @@ SiConst (max x y)
          | _   -> fail dummyinfo @@ Internal "Bad state when LUBing sensitivities"
        end
    
  let si_simpl (si : si) : si checker = 
    should_check_sens (return si) @@
    si_simpl' si
  
  let rec si_simpl_ty' (ty : ty) : ty checker = 
    match ty with
    | TyVar v                 -> return ty
    | TyPrim tp               -> return ty
    | TyPrim1 (tp, ty)        -> si_simpl_ty' ty  >>= fun ty' ->
                                 return @@ TyPrim1 (tp, ty')
                                                   
    | TyUnion (ty1, ty2)      -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl_ty' ty2 >>= fun ty2 ->
                                 return @@ TyUnion    (ty1, ty2)
                                                      
    | TyTensor(ty1, ty2)      -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl_ty' ty2 >>= fun ty2 ->
                                 return @@ TyTensor   (ty1, ty2)
                                                      
    | TyAmpersand(ty1, ty2)   -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl_ty' ty2 >>= fun ty2 ->
                                 return @@ TyAmpersand(ty1, ty2)
                                                      
    | TyLollipop(ty1, s, ty2) -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl' s      >>= fun s   ->
                                 si_simpl_ty' ty2 >>= fun ty2 ->
                                 return @@ TyLollipop(ty1, s, ty2)
                                                     
    | TyMu(b, ty)             -> si_simpl_ty' ty  >>= fun ty  -> return @@ TyMu(b, ty)
                                                                               
    | TyForall(b, ty)         -> si_simpl_ty' ty  >>= fun ty  -> return @@ TyForall(b, ty)
                                                                                   
    | TyTyApp(TyForall(_, abs), arg)
                              -> ty_normalize_app ty >>= fun ty' ->
                              si_simpl_ty' ty'
    | _ -> return ty
    
  let si_simpl_ty (ty : ty) : ty checker = 
    should_check_sens (return ty) @@
    si_simpl_ty' ty
  
  (* Check that the first sensitivity is less than the second *)
  let check_sens_leq i (sil : si) (sir : si) : unit checker =
    should_check_sens (return ()) @@ begin
    si_simpl' sil >>= fun sil ->
    si_simpl' sir >>= fun sir ->
    let res = match sil, sir with
      | _, SiInfty  -> true
      | SiZero, _   -> true
      | SiConst l, SiConst r -> (* Test whether l <= r taking floating point issues into effect. *)
          begin let x = r -. l in match classify_float x with
            | FP_infinite when x > 0.0 -> true
            | FP_normal   when x > 0.0 -> true
            | FP_subnormal             -> true
            | FP_zero                  -> true
            | _                        -> false
          end
      | _, _ -> false
    in if res then return () else fail i @@ SensError(sil, sir)
    end
  
  (* A list only with zero sensitivities *)
  let rec zeros (n : int) : si list =
    if n = 0 then [] else si_zero :: zeros (n - 1)
  
  (* A list with zero sensitivities, except for one variable *)
  (* Note that this has to be kept in sync with the actual ctx *)
  let singleton (n : int) (v : var_info) : si list =
    let rec aux n l =
      if n = 0 then l
      else let si = if n = v.v_index + 1 then si_one else si_zero in
           aux (n - 1) (si :: l) in
    aux n []
  
  let si_add  (si1 : si) (si2 : si) : si = SiAdd (si1, si2)
  let si_mult (si1 : si) (si2 : si) : si = SiMult(si1, si2)
  let si_lub  (si1 : si) (si2 : si) : si = SiLub (si1, si2)
  
  let add_sens (sis1 : si list) (sis2 : si list) : (si list) =
    List.map2 si_add sis1 sis2
  
  let scale_sens (si : si) (sis : si list) : (si list) =
    List.map (si_mult si) sis
  
  let lub_sens (sis1 : si list) (sis2 : si list) : (si list) =
    List.map2 si_lub sis1 sis2
  
end

module TypeInf = struct
  (* This is good for return, eq, etc... it should be extended
     systematically instead of the current hack *)
  let infer_tyapp_very_simple (i : info) (ty : ty) (ty_arg : ty) : (ty * si) option =
    match ty with
    | TyLollipop(TyVar v, si, tyb) ->
      if v.v_index = 0 then
        let nt = ty_substTy ty_arg 0 0 tyb in
        ty_debug i "==> Inferring type application from @[%a@] to @[%a@]" pp_type tyb pp_type nt;
        Some (nt, si)
      else
        None
    | TyLollipop(TyPrim1 (t, TyVar v), si, tyb) ->
      begin match ty_arg with
      | TyPrim1 (t1, ty_arg') ->
        if v.v_index = 0 && t1 = t then
          let nt = ty_substTy ty_arg' 0 0 tyb in
          ty_debug i "==> Inferring container type application from @[%a@] to @[%a@]" pp_type tyb pp_type nt;
          Some (nt, si)
        else
          None
      | _ -> None
      end
    | _ -> None

end

module TypeSub = struct
  open Ctx
  open TypeCheckMonad
  
  let check_prim_sub (ty_1 : ty_prim) (ty_2 : ty_prim) : bool =
    match ty_1, ty_2 with
    | PrimClipped, PrimNum  -> true
    | PrimInt, PrimNum      -> true
    | _   when ty_1 = ty_2  -> true
    | _                     -> false

                                 
  (* Check whether ty_1 is a subtype of ty_2. *)
  let check_type_sub (i : info) (ty_1 : ty) (ty_2 : ty) : unit checker =
    let fail = fail i @@ NotSubtype (ty_1, ty_2) in 
    let rec inner (ty_1 : ty) (ty_2 : ty) : unit checker =
      match ty_1, ty_2 with
      | TyVar v1, TyVar v2   ->
        if v1.v_index = v2.v_index then return () else fail
  
      | TyPrim p1, TyPrim p2 -> if check_prim_sub p1 p2 then return () else fail
  
      | TyPrim1(pl, tyl), TyPrim1(pr, tyr) ->
        if pl = pr then inner tyl tyr else fail
  
      | TyUnion(tyl1, tyl2), TyUnion(tyr1, tyr2) ->
        inner tyl1 tyr1 >>
        inner tyl2 tyr2
  
      | TyTensor(tyl1, tyl2), TyTensor(tyr1, tyr2) ->
        inner tyl1 tyr1 >>
        inner tyl2 tyr2
  
      | TyAmpersand(tyl1, tyl2), TyAmpersand(tyr1, tyr2) ->
        inner tyl1 tyr1 >>
        inner tyl2 tyr2
  
      | TyLollipop(tyl1, sil, tyl2), TyLollipop(tyr1, sir, tyr2) ->
        inner tyr1 tyl1 >>
        inner tyl2 tyr2 >>
        TypeSens.check_sens_leq i sil sir
  
      | TyMu(_bl, tyl), TyMu(_br, tyr) ->
        inner tyl tyr
  
      | TyForall(_bl, tyl), TyForall(_br, tyr) ->
        (*with_new_ctx (extend_ctx_with_tyvar' bl.b_name)*) (inner tyl tyr)

      | _, _ -> fail
    in ty_normalize_app ty_1 >>= fun ty_1 ->
       ty_normalize_app ty_2 >>= fun ty_2 ->
       inner ty_1 ty_2
  
  let find_super_type (i : info) (ty_1 : ty) (ty_2 : ty) : ty checker =
    failToResult (check_type_sub i ty_1 ty_2) >>= fun ty1subty2 ->
    failToResult (check_type_sub i ty_2 ty_1) >>= fun ty2subty1 ->
    match ty1subty2, ty2subty1 with
    | Ok (),   Ok ()   -> return ty_1
    | Ok (),   Error _ -> return ty_1
    | Error _, Ok ()   -> return ty_2
    | Error _, Error _ -> fail i @@ TypeMismatch (ty_1, ty_2)
  
  let check_type_equal (i : info) (ty_1 : ty) (ty_2 : ty) : unit checker =
    failToResult (check_type_sub i ty_1 ty_2) >>= fun ty1subty2 ->
    failToResult (check_type_sub i ty_2 ty_1) >>= fun ty2subty1 ->
    match ty1subty2, ty2subty1 with
    | Ok (), Ok ()  -> return ()
    | _,     _      -> fail i @@ TypeMismatch (ty_1, ty_2)
  
  (* Check whether ty is compatible (modulo subtyping) with annotation
     ann, returning the resulting type. *)
  let check_type_ann (i : info) (ann : ty option) (ty : ty) : ty checker =
    match ann with
    | Some ty' -> check_type_sub i ty ty' >> return ty'
    | None -> return ty

  (* Check that the type is a type application. Return the type under the 
     forall. *)
  let check_ty_app_shape i ty_arr =
    ty_normalize_app ty_arr >>= fun ty_arr ->
    match ty_arr with
    | TyForall(_b, ty)    -> return ty
    | _                   -> fail i @@ WrongShape(ty_arr, "forall")

  let check_app i ty_arr ty_arg =
    get_depth >>= fun d ->
    ty_debug i "<-> [%3d] Application of @[%a@] to @[%a@]" d pp_type ty_arr pp_type ty_arg;
    match ty_arr with
    (* Here we do inference of type applications *)
    | TyForall(_bi, ty)   ->
      let tso = TypeInf.infer_tyapp_very_simple i ty ty_arg in
      begin match tso with
        | Some ts -> return ts
        | None    -> fail i @@ CannotApply(ty, ty_arg)
      end
    | TyLollipop(tya, si, tyb) ->
      check_type_sub i ty_arg tya >>
      return (tyb, si)
    | _                        -> fail i @@ CannotApply(ty_arr, ty_arg)

  let check_fuzz_shape i ty =
    ty_normalize_app ty >>= fun ty ->
    match ty with
    | TyPrim1 (Prim1Fuzzy, ty) -> return ty
    | _                        -> fail i @@ WrongShape (ty, "fuzzy")

  let check_bag_shape i ty =
    ty_normalize_app ty >>= fun ty ->
    match ty with
    | TyPrim1 (Prim1Bag, ty)   -> return ty
    | _                        -> fail i @@ WrongShape (ty, "bag")

  let check_vector_shape i ty =
    ty_normalize_app ty >>= fun ty ->
    match ty with
    | TyPrim1 (Prim1Vector, ty) -> return ty
    | _                         -> fail i @@ WrongShape (ty, "vector")

  let check_token_shape i ty =
    ty_normalize_app ty >>= fun ty ->
    match ty with
    | TyPrim1 (Prim1Token, ty) -> return ty
    | _                        -> fail i @@ WrongShape (ty, "token")

  let check_tensor_shape i ty =
    ty_normalize_app ty >>= fun ty ->
    match ty with
    | TyTensor(ty1, ty2) -> return (ty1, ty2)
    | _                  -> fail i @@ WrongShape (ty, "tensor")

  let check_union_shape i ty =
    ty_normalize_app ty >>= fun ty ->
    match ty with
    | TyUnion(ty1, ty2) -> return (ty1, ty2)
    | _                 -> fail i @@ WrongShape (ty, "union")

  let rec check_mu_shape i ty =
    ty_normalize_app ty >>= fun ty' ->
    match ty' with
    | TyMu(_, _)          -> return (ty_unfold ty')
    | _                   -> fail i @@ WrongShape (ty', "mu")

end


(**********************************************************************)
(* Main typing routines                                               *)
(**********************************************************************)
open TypeSens
open TypeSub
open TypeCheckMonad

let reportSensitivity (fi : info) (bi : binder_info) (si : si) : si checker =
  should_check_sens (return si) @@
  si_simpl si >>= fun si ->
  Support.Error.message 7 Support.Options.TypeChecker fi
    "### Inferred sensitivity for binder @[%a@] is @[%a@]" pp_binfo bi pp_si si;
  return si

let reportSensitivityT (fi : info) (tm : term) (si : si) : si checker =
  should_check_sens (return si) @@
  si_simpl si >>= fun si ->
  Support.Error.message 7 Support.Options.TypeChecker fi
    "### Inferred sensitivity for primfun term @[%a@] is @[%a@]" pp_term tm pp_si si;
  return si


let type_of_prim (t : term_prim) : ty = match t with
    PrimTUnit       -> TyPrim PrimUnit
  | PrimTNum _      -> TyPrim PrimNum
  | PrimTInt _      -> TyPrim PrimInt
  | PrimTBool _     -> TyPrim PrimBool
  | PrimTString  _  -> TyPrim PrimString
  | PrimTClipped _  -> TyPrim PrimClipped
  | PrimTToken(_,ty) -> TyPrim1 (Prim1Token, ty)


(* Given a term t and a context ctx for that term, check whether t is
   typeable under ctx, returning a type for t, a list of synthesized
   sensitivities for ctx, and a list of constraints that need to be
   satisfied in order for the type to be valid. Raises an error if it
   detects that no typing is possible.
   This is a version that uses no partial evaluation and is not "fixed". *)
let type_of_untied (recur : term -> (ty * si list) checker) (t : term) : (ty * si list) checker  =
  get_depth >>= fun d ->
  ty_debug (tmInfo t) "--> [%3d] Enter type_of: @[%10a@]" d
    (limit_boxes pp_term) t;

  (deeper @@ match t with
  (* Variables *)
  | TmVar(i, v)  ->
    get_ctx_length              >>= fun len ->
    get_var_ty v                >>= fun ty  -> 
    return (ty, singleton len v)

  (* Primitive terms *)
  | TmPrim(_, pt) ->
    get_ctx_length >>= fun len ->
    return (type_of_prim pt, zeros len)

  | TmPrimFun(i, s, ty, ttslst) ->
    ty_debug i "--> [%3d] Type checking primfun %s" d s;
    si_simpl_ty ty >>= fun ty ->
    mapM (fun (tm,ety,esi) -> 
      reportSensitivityT i tm esi >>= fun esi ->
      recur tm >>= fun (aty, asi) ->
      ty_debug i "--> [%3d] %s Verifying that type %a is a subtype of type %a" d s pp_type aty pp_type ety;
      check_type_sub i aty ety >>
      return (scale_sens esi asi)) ttslst >>= fun sislst ->
    get_ctx_length >>= fun len ->
    let sis = List.fold_left add_sens (zeros len) sislst in
    return (ty, sis)
  
  | TmPVal(i, t) -> 
    recur t >>= fun (ty_t, sis_t) ->
    return (TyPrim1 (Prim1Fuzzy, ty_t), sis_t)
  
  | TmUnPVal(i, t) -> 
    recur t >>= fun (ty_t, sis_t) ->
    check_fuzz_shape i ty_t >>= fun ty_t' ->
    return (ty_t', sis_t)
  
  | TmBag(i, ty, tmlst) -> 
    check_bag_shape i ty >>= fun ity ->
    mapM (fun tm -> 
      recur tm >>= fun (aty, _) ->
      check_type_sub i aty ity) tmlst >>
    get_ctx_length >>= fun len ->
    return (ty, zeros len)
    
  | TmVector(i, ty, tmlst) -> 
    check_vector_shape i ty >>= fun ity ->
    mapM (fun tm -> 
      recur tm >>= fun (aty, _) ->
      check_type_sub i aty ity) tmlst >>
    get_ctx_length >>= fun len ->
    return (ty, zeros len)
    
  (************************************************************)
  (* Abstraction and Application *)
  (* λ (x :[si] tya_x) : tya_tm { tm } *)
  | TmAbs(i, b_x, (sia_x, tya_x), otya_tm, tm) ->

    si_simpl sia_x                                    >>= fun sia_x ->
    with_extended_ctx i b_x.b_name tya_x (recur tm) >>= fun (ty_tm, si_x, sis) ->

    reportSensitivity i b_x si_x >>= fun si_x ->

    check_type_ann i otya_tm ty_tm                  >>
    check_sens_leq i si_x sia_x                     >>
    return (TyLollipop (tya_x, sia_x, ty_tm), sis)

  (* tm1 !ᵢβ → α, tm2: β *)
  | TmApp(i, tm1, tm2)                              ->

    recur tm1 >>= fun (ty1, sis1) ->
    recur tm2 >>= fun (ty2, sis2) ->

    (* Checks that ty1 has shape !ᵢβ → α, and that ty2 is an instance of β.
       Returns α and the sensitivity inside ty1 *)
    check_app i ty1 ty2 >>= fun (tya, r) ->

    (* We scale by the sensitivity in the type, which comes from an annotation *)
    return (tya, add_sens sis1 (scale_sens r sis2))

  (************************************************************)
  (* Identical to app + lam, this rule exists in order to avoid too
     many type annotations! *)
  (* let x [: sia_x] = tm_x in e *)
  | TmLet(i, x, sia_x, tm_x, e)                   ->

    recur tm_x >>= fun (ty_x, sis_x)  ->

    ty_debug i "### Type of binder %a is %a" pp_binfo x pp_type ty_x;

    with_extended_ctx i x.b_name ty_x (recur e) >>= fun (ty_e, si_x, sis_e) ->
    reportSensitivity i x si_x         >>= fun si_x ->
    check_sens_leq i si_x sia_x                   >>
    return (ty_e, add_sens sis_e (scale_sens si_x sis_x))

  (* Identical to let being used precisely once, this rule exists in order to 
     simplify assert statements. *)
  (* tm1; tm2 *)
  | TmStmt(i, tm1, tm2) ->

    recur tm1 >>= fun (_ty, sis_1)  ->
    recur tm2 >>= fun (ty,  sis_2)  ->

    return (ty, add_sens sis_1 sis_2)

  (* function x <args ...> : tya_x { tm_x }; e *)
  | TmRecFun(i, x, tya_x, tm_x, _)                      ->

    with_extended_ctx i x.b_name tya_x (recur tm_x) >>= fun (ty_x, si_x, sis_x) ->

    check_type_sub i ty_x tya_x >>

(*    ty_debug i "### Type of binder %a is %a" pp_binfo x pp_type ty_x;*)
    return (ty_x, sis_x)

  (* sample b_x = tm_x; e *)
  | TmSample(i, b_x, tm_x, e)                              ->

    recur tm_x            >>= fun (ty_x, sis_x) ->
    check_fuzz_shape i ty_x >>= fun ty_x ->

    with_extended_ctx i b_x.b_name ty_x (recur e) >>= fun (ty_e, si_x, sis_e) ->

(*     ty_debug i "### [%3d] Sample for binder @[%a@] with sens @[%a@]" d pp_binfo b_x pp_si si_x; *)
    reportSensitivity i b_x si_x >>= fun si_x ->

    check_fuzz_shape i ty_e                         >>

    (* The inferred sensitivity of x can be ignored. Once the result
       of a differentially private computation has been published, it
       can be used without any restriction. *)
    return (ty_e, add_sens sis_x sis_e)

  (* Tensor and & *)
  | TmPair(i, e1, e2) ->

    recur e1 >>= fun (ty1, sis1) ->
    recur e2 >>= fun (ty2, sis2) ->

    return @@ (TyTensor(ty1, ty2), add_sens sis1 sis2)

  | TmAmpersand(i, tm1, tm2)      ->

    recur tm1 >>= fun (ty1, sis1) ->
    recur tm2 >>= fun (ty2, sis2) ->

    return (TyAmpersand(ty1, ty2), lub_sens sis1 sis2)

  (************************************************************)
  (* Data type manipulation *)
  | TmFold(i, ty, tm)               ->

    check_mu_shape i ty             >>= fun ty_unf ->
    recur tm                      >>= fun (ty_tm, sis_tm) ->
    check_type_sub i ty_tm ty_unf >>
    return (ty, sis_tm)

  | TmUnfold (i, tm)                ->

    recur tm                      >>= fun (ty_tm, sis_tm) ->
    check_mu_shape i ty_tm          >>= fun ty_unf ->
    return (ty_unf, sis_tm)

  (* Type Alias
     typedef n = tdef_ty; tm *)
  | TmTypedef(i, n, tdef_ty, tm)    ->

    ty_debug3 i "--> [%3d] Calling typedef %a = %a on term %a" d pp_binfo n pp_type tdef_ty pp_term tm;

    (* We just substitute the type for the variable. *)
    recur (tm_substTy (ty_shiftTy 0 (-1) tdef_ty) 0 0 tm)

  (* let (x,y) = e in e' *)
  | TmTensDest(i, x, y, e, t) ->

    recur e >>= fun (ty_e, sis_e) ->
    check_tensor_shape i ty_e >>= fun (ty_x, ty_y) ->

    (* Extend context with x and y *)
    with_extended_ctx_2 i x.b_name ty_x y.b_name ty_y (recur t) >>= fun (ty_t, si_x, si_y, sis_t) ->

    reportSensitivity i x si_x   >>= fun si_x ->
    reportSensitivity i y si_y   >>= fun si_y ->

    return (ty_t, add_sens sis_t (scale_sens (si_lub si_x si_y) sis_e))
  
  | TmLeft(i, t, tyr) ->
    recur t >>= fun (ty_t, sis_t) ->
    return (TyUnion(ty_t, tyr), sis_t)

  | TmRight(i, t, tyl) ->
    recur t >>= fun (ty_t, sis_t) ->
    return (TyUnion(tyl, ty_t), sis_t)

  (* case e of inl(x) => e_l | inr(y) e_r *)
  | TmUnionCase(i, e, b_x, e_l, b_y, e_r)      ->

    recur e >>= fun (ty_e, sis_e) ->

    check_union_shape i ty_e >>= fun (ty1, ty2) ->

    with_extended_ctx i b_x.b_name ty1 (recur e_l) >>= fun (tyl, si_x, sis_l) ->
    with_extended_ctx i b_y.b_name ty2 (recur e_r) >>= fun (tyr, si_y, sis_r) ->
    
    reportSensitivity i b_x si_x          >>= fun si_x ->
    reportSensitivity i b_y si_y          >>= fun si_y ->
    
    find_super_type i tyr tyl >>= fun tysup ->

    return (tysup, add_sens (lub_sens sis_l sis_r) (scale_sens (si_lub si_nearzero (si_lub si_x si_y)) sis_e))

  (* Type/Sensitivity Abstraction and Application *)
  | TmTyAbs(i, bi, tm) ->

    with_extended_ty_ctx bi.b_name (recur tm) >>= fun (ty, sis) ->
    return (TyForall(bi, ty), sis)

  | TmTyApp(i, tm, ty_app) ->

    recur tm                >>= fun (ty_t, sis) ->
    check_ty_app_shape i ty_t >>= fun (ty_i) ->

    return (ty_substTy ty_app 0 0 ty_i, sis)

  (* b must have type bool and the two branches must have matching types *)
  | TmIfThenElse(i, b, thent, elset)    ->

    recur b >>= fun (tyb, sisb) ->
    recur thent >>= fun (tythen, sisthen) ->
    recur elset >>= fun (tyelse, siselse) ->
    
    find_super_type i tythen tyelse >>= fun tysup ->
    (match tyb with
      | TyPrim (PrimBool) -> return ()
      | _                 -> fail i @@ TypeMismatch (tyb, TyPrim (PrimBool))) >>

    return (tysup, add_sens (lub_sens sisthen siselse) sisb)

  ) >>= fun (ty, sis) ->
  (* We limit pp_term *)
  ty_debug (tmInfo t) "<-- [%3d] Exit  type_of: @[%a@] with type @[%a@]" d
  (limit_boxes pp_term) t pp_type ty;
  
  return (ty, sis)

(* The main typing function.  Uses partial evaluation. *)
let rec type_of (t : term) : (ty * si list) checker =
  get_depth >>= fun d ->
  failToResult (type_of_untied type_of t) >>= fun res ->
  match res with
  | Ok v    -> return v
  | Error (d',e) -> begin
      get_pinfo >>= fun pinfo ->
      match pinfo with
      | Some (l,pinterp) when l > 0 -> begin
          ty_debug (tmInfo t) "--> [%3d] Attempting PE due to error: %a" d (pp_tyerr d') e.v;
          get_ctx >>= fun ctx ->
          match pinterp ctx l t with
          | Some (l',t') ->
              ty_debug (tmInfo t) "<-- [%3d] PE succeeded after %i steps (%i remaining) with new term: %a" d (l-l') l' pp_term t';
              on_error (with_depth d' @@ fail (e.i) (e.v)) (with_pinfo (Some (l',pinterp)) (type_of t'))
          | None ->
              ty_debug (tmInfo t) "<-- [%3d] PE unsuccessful at reducing term.  Throwing error higher up ..." d;
              with_depth d' @@ fail (e.i) (e.v)
          end
      | _ -> with_depth d' @@ fail (e.i) (e.v)
      end

let get_type (sensCheck : bool) (program : term) : ty =
  match type_of program (Ctx.empty_context, 0, sensCheck, None) with
  | Ok (ty, _sis) -> ty
  | Error (dep,e) -> typing_error_pp e.i (pp_tyerr dep) e.v

let ty_normalize_app = TypeCheckMonad.ty_normalize_app
