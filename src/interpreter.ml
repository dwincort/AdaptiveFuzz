(* file name: interpreter.ml
   created by: Daniel Winograd-Cort
   Last modified: 12/15/2015
   
   Description:
   This file contains code for interpreting SFuzz terms.
*)
open Format

open Print
open Types
open Syntax

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

module Opt = Support.Options
module Err = Support.Error

let interp_error = Err.error_msg Opt.Interpreter Support.FileInfo.dummyinfo

let interp_warning fi = Err.message 1 Opt.Interpreter fi
let interp_info    fi = Err.message 2 Opt.Interpreter fi
let interp_info2   fi = Err.message 3 Opt.Interpreter fi
let interp_debug   fi = Err.message 4 Opt.Interpreter fi
let interp_debug2  fi = Err.message 5 Opt.Interpreter fi
let interp_debug3  fi = Err.message 6 Opt.Interpreter fi
let interp_messageNoFi n = Err.message n Opt.Interpreter Support.FileInfo.dummyinfo

let pp_term = limit_boxes pp_term

let ty_normalize_app = Tycheck.ty_normalize_app

(* State monad for the context for interpreting *)
module InterpMonad = struct
  open Composedp
    
  let (>>=) (m : 'a interpreter) (f : 'a -> 'b interpreter) : 'b interpreter =
    fun ((db, pe, ctx) as inp) -> match m inp with
      | (db', pe', Ok a)    -> f a (db', pe', ctx)
      | (_,_, Error _) as e -> e
  
  let (>>) m f = m >>= fun _ -> f
  
  let return (x : 'a) : 'a interpreter = fun (db, pe, _) -> (db, pe, Ok x)
  
  let rec mapM (f : 'a -> 'b interpreter) (lst : 'a list) : ('b list) interpreter = 
    match lst with
      | []    -> return []
      | x::xs -> f x        >>= fun y  ->
                 mapM f xs  >>= fun ys ->
                 return (y::ys)
  
  let rec mapMSi (f : term -> term interpreter) (si : si) : si interpreter = 
    match si with
    | SiInfty         -> return @@ si
    | SiZero          -> return @@ si
    | SiConst c       -> return @@ si
    | SiTerm  t       -> f t >>= fun x -> return @@ SiTerm x
    | SiAdd  (s1, s2) -> mapMSi f s1 >>= fun s1 -> mapMSi f s2 >>= fun s2 -> return @@ SiAdd  (s1, s2)
    | SiMult (s1, s2) -> mapMSi f s1 >>= fun s1 -> mapMSi f s2 >>= fun s2 -> return @@ SiMult (s1, s2)
    | SiLub  (s1, s2) -> mapMSi f s1 >>= fun s1 -> mapMSi f s2 >>= fun s2 -> return @@ SiLub  (s1, s2)
  
  let rec mapMTy (f : term -> term interpreter) (ty : ty) : ty interpreter = 
    match ty with
    | TyVar v                 -> return ty
    | TyPrim tp               -> return ty
    | TyPrim1 (tp, ty)        -> mapMTy f ty >>= fun ty' -> return @@ TyPrim1 (tp, ty')
    | TyUnion (ty1, ty2)      -> mapMTy f ty1 >>= fun ty1 -> mapMTy f ty2 >>= fun ty2 -> return @@ TyUnion    (ty1, ty2)
    | TyTensor(ty1, ty2)      -> mapMTy f ty1 >>= fun ty1 -> mapMTy f ty2 >>= fun ty2 -> return @@ TyTensor   (ty1, ty2)
    | TyAmpersand(ty1, ty2)   -> mapMTy f ty1 >>= fun ty1 -> mapMTy f ty2 >>= fun ty2 -> return @@ TyAmpersand(ty1, ty2)
    | TyLollipop(ty1, s, ty2) -> mapMTy f ty1 >>= fun ty1 -> 
                                 mapMSi f s   >>= fun s   ->
                                 mapMTy f ty2 >>= fun ty2 -> return @@ TyLollipop(ty1, s, ty2)
    | TyMu(b, ty)             -> mapMTy f ty >>= fun ty -> return @@ TyMu(b, ty)
    | TyForall(b, ty)         -> mapMTy f ty >>= fun ty -> return @@ TyForall(b, ty)
    | TyTyApp(abs, arg)       -> mapMTy f abs >>= fun abs ->
                                 mapMTy f arg >>= fun arg ->
                                 return @@ TyTyApp(abs, arg)
  
  (* Failing should never happen.  It is always due to either a type problem, which means the 
     type checker has failed, or a primitive problem. *)
  let fail (message : string) : 'a interpreter = fun (db, pe, _) -> (db, pe, Error message)
  let fail_pp (args : ('b, formatter, unit, 'a interpreter) format4) : 'b = kasprintf fail args
  
  let withFailTerm (tm : term) (m : term interpreter) : term interpreter = 
    fun ((_, pe, _) as inp) -> match m inp with
      | (_, _, Ok _) as res -> res
      | (db, pe', Error s) when Option.is_some pe ->
          interp_messageNoFi 4 "--- Skipping failure \"%s\";@ reverting to state %a." s pp_term tm;
          (db, pe, Ok tm) (* FIXME: Should this be pe or pe'? *)
      | res -> res
  
  let isInPartial : bool interpreter = 
    fun (db, pe, _) -> (db, pe, Ok (Option.is_some pe))
  
  let decLim : unit interpreter =
    fun (db, pe, _) -> match pe with
      | None -> (db, None, Ok ())
      | Some l -> if l <= 0 then (db, Some l, Error "Partial Evaluation Limit reached")
                            else (db, Some (l-1), Ok ())
  
  let attemptRedZone (sens : epsilon) : bool interpreter =
    fun (o, pe, _) -> match o with
      | None -> (o, pe, Error "**Interpreter** Tried to store a sensitivity when no DB was loaded")
      | Some (db, budget, _, silist) -> begin
          let silist' = (sens, 0.0) :: silist           in
          match simpleOrAdvancedFilter budget silist' with
            | None -> (o, pe, Ok false)
            | Some est -> (Some (db, budget, est, silist'), pe, Ok true)
          end
  
  let getDB : term interpreter = 
    fun (o, pe, _) -> match o with
      | None -> (o, pe, Error "**Interpreter** No database loaded")
      | Some (db,_,_,_) -> (o, pe, Ok db)
  
  let storeDB (db : term) (budget : ed) : unit interpreter = 
    fun (db_init, pe, _) -> if Option.is_some pe
      then begin interp_messageNoFi 1 "Trying to storeDB in red zone.  Quietly skipping ...";
                 (db_init, pe, Ok ())
      end else (Some (db, budget, budget, []), pe, Ok ())
  
  let getDelta : float interpreter = 
    fun (db, pe, _) -> match db with
      | None -> (db, pe, Error "**Interpreter** Tried to get remaining epsilon budget when no DB was loaded")
      | Some (_, _, (_, del), _) -> (db, pe, Ok del)
  
  let getEpsilon : epsilon interpreter = 
    fun (db, pe, _) -> match db with
      | None -> (db, pe, Error "**Interpreter** Tried to get remaining epsilon budget when no DB was loaded")
      | Some (_, _, (eps, _), _) -> (db, pe, Ok eps)
  
  let getTCtx : context interpreter = 
    fun (db, pe, ctx) -> (db, pe, Ok ctx)
  
  let checkerToInterpreter (c : 'a checker) : 'a interpreter = 
    getTCtx >>= fun ctx ->
    match c (ctx, 0, false, None) with 
      | Error (d,e) -> fail_pp "TYPE FAIL: %a %a"
            Support.FileInfo.pp_fileinfo e.Support.FileInfo.i 
            (pp_tyerr d) e.Support.FileInfo.v
      | Ok res -> return res

end

open InterpMonad

  

(* This function does some simple type inference.
   We expect the term f to be an abstraction with one free type variable, 
   and we return a term with that variable filled in such that the argument 
   is now applicable to the abstraction.
   Note that for this simple version, we demand that f be a value 
   abstraction (NOT a type abstraction) and that its argument must fully 
   determine the type variable immediately. *)
let appTypeInfer (f : term) (arg : term) : term interpreter = 
  checkerToInterpreter (Tycheck.type_of arg) >>= fun (ty_arg,_) ->
  match f with
  | TmAbs(_,_,(_,expectedTy),_,tm) -> begin match expectedTy, ty_arg with
      | TyVar v, _ -> if v.v_index = 0 then return (tm_substTy ty_arg 0 0 f)
                      else fail "**Interpreter** Bad type inference"
      | TyPrim1 (t, TyVar v), TyPrim1 (t', ty_arg') ->
            if v.v_index = 0 && t' = t then return (tm_substTy ty_arg' 0 0 f)
                      else fail "**Interpreter** Bad type inference"
      | _,_ -> fail "**Interpreter** Bad type inference"
      end
  | _ -> fail "**Interpreter** Bad type inference"

(* val interp : term -> value interpreter *)
let rec interp (t : term) : term interpreter = 
  withFailTerm t @@
  match t with
  (* A primitive term is fully evaluated.  Do nothing. *)
  | TmPrim(i,pt) -> return t
  
  (* When we come to a primitive function, we have a list of terms (and their 
     types) that are the arguments.  If all of these arguments are values 
     (as should be the case all the time in regular evaluation), then we 
     look up and execute the primitive with its arguments.  However, if we 
     are in partial evaluation mode, they may not all be values, in which 
     case, we fail. *)
  | TmPrimFun(i, s, PrimFun f, ty, ttslst)  ->
(*      mapM (fun (tm,ty,si) -> interp tm >>= fun tm -> 
                              return (tm,ty,si)) ttslst >>= fun ttslst ->
      withFailTerm (TmPrimFun(i, s, ty, ttslst))*)
     let tmlst = List.map (fun (tm,_,_) -> tm) ttslst in
     checkerToInterpreter (ty_normalize_app ty) >>= fun ty' ->
     if List.for_all tmIsVal tmlst
     then (decLim >> f (TmPrimFun(i, s, PrimFun f, ty', ttslst)))
     else fail_pp "**Interpreter** Unevaluated arguments in %a." pp_term t
  
  (* Variables always fail (which will get caught during partial evaluation). *)
  | TmVar(i,v) -> fail @@ "**Interpreter** Unexpected var: "^v.v_name
  
  (* Probabilistic Values are basically just lazy boxes.  We open them with TmUnPVal *)
  | TmPVal(i,_) -> return t
  | TmUnPVal(i,t) -> 
      interp t >>= fun t ->
      withFailTerm (TmUnPVal(i,t))
      begin match t with
        | TmPVal(i, t') -> decLim >> interp t'
        | _ -> fail_pp "**Interpreter** TmUnPVal expected a Probabilistic Value but found %a." pp_term t
      end
  
  (* Bags are essentially primitives. *)
  (* The primitives should be defined such that there are no cases where bags have unevaluated
     terms in them.  They are entirely strict. *)
  | TmBag(i,ty,tmlst) -> checkerToInterpreter (ty_normalize_app ty) >>= fun ty' ->
                         return @@ TmBag(i, ty', tmlst)
  | TmVector(i,ty,tmlst) -> mapM interp tmlst >>= fun tmlst ->
                            checkerToInterpreter (ty_normalize_app ty) >>= fun ty' ->
                            return (TmVector(i, ty', tmlst))
  
  (* Pairs.  Interpret both parts and return them as a pair. *)
  | TmPair(i,t1,t2) -> 
      interp t1 >>= fun t1' ->
      interp t2 >>= fun t2' ->
      return @@ TmPair (i, t1', t2')
  
  (* Tensor Desctruction.  Interpret the argument expression.  If it is a 
     pair, substitute its constituent values for the variables in the body 
     and interpret that.  If not, fail.  However, if we are in partial mode, 
     first interpret the body (without any substitutions). *)
  | TmTensDest(i, b1, b2, tm, tBody) ->
      interp tm >>= fun tm -> 
      withFailTerm (TmTensDest(i, b1, b2, tm, tBody))
      begin match tm with
        | TmPair (i', t1, t2) -> decLim >> interp (tm_substTm t1 0 0 (tm_substTm t2 0 0 tBody))
        | _ -> fail_pp "**Interpreter** TensDest expected a pair but found %a." pp_term tm
      end
  
  (* & constructor.  Interpret both parts and return them as a pair. *)
  | TmAmpersand(i, t1, t2) ->
      interp t1 >>= fun t1' ->
      interp t2 >>= fun t2' ->
      return @@ TmAmpersand (i, t1', t2')
  
  (* Left and Right constructors for sum.  Interpret the body. *)
  | TmLeft (i, t, ty)   -> interp t >>= fun t ->
                           checkerToInterpreter (ty_normalize_app ty) >>= fun ty' ->
                           return (TmLeft (i, t, ty'))
  | TmRight(i, t, ty)   -> interp t >>= fun t ->
                           checkerToInterpreter (ty_normalize_app ty) >>= fun ty' ->
                           return (TmRight(i, t, ty))
  
  (* Interpret the scrutinee.  If it is a Left or Right value, do the proper 
     substitution into the body and interpret that.  Otherwise, fail.  If we 
     are in partial mode, interpret both branches, but do so in under-branch 
     mode (in which we do not unfold terms or make recursive calls. *)
  | TmUnionCase(i, tm, bl, tlBody, br, trBody) ->
      interp tm >>= fun tm -> 
      withFailTerm (TmUnionCase(i, tm, bl, tlBody, br, trBody))
      (*interp_debug3 i "--- Interpreting a union of: %a" pp_term tm;*)
      begin match tm with
        | TmLeft (i',tl,_) -> decLim >> interp (tm_substTm tl 0 0 tlBody)
        | TmRight(i',tr,_) -> decLim >> interp (tm_substTm tr 0 0 trBody)
        | _ -> fail_pp "**Interpreter** Union expected a sum value but found %a" pp_term tm
      end

  (* Function Application.  Interpret the argument and then the function 
     in standard strict style.  Then, match the function.  If it is an 
     abstraction, perform the substitution.  However, take care when 
     performing because, if we are in partial evaluation mode, the argument 
     may not be *really* fully evaluated, and any variables therein need 
     their indexes properly updated.
     If it is a type abstraction, then we are in a position where type 
     inference needs to be performed.  This is kind of hacky right now 
     (because type inference itself is a bit of a hack).
     Otherwise, fail. *)
  | TmApp(i, tf, ta) -> 
      interp ta >>= fun ta ->
      interp tf >>= fun tf ->
      withFailTerm (TmApp(i, tf, ta))
      begin match tf with
        | TmAbs(_,_,_,_,tm)   -> decLim >> interp (tm_substTm ta 0 0 tm) 
        | TmTyAbs(i', bi, tm) -> decLim >> appTypeInfer tm ta >>= fun tm -> interp (TmApp(i, tm, ta))
        | _ -> fail_pp "**Interpreter** Application expected a Lambda value but found %a." pp_term tf
      end
  
  (* Abstractions are values, but because there may be terms in their 
     types or sensitivity annotations, we do interpret those. *)
  | TmAbs(i, bi, (si, ty), tyo, tm) -> return t

  (* Recursive data types.  
     Always interpret under a fold.
     For unfolds, if we are in under-branch mode, then simply do not 
     look at the underlying term or expand.  In all other cases, 
     interpret the underlying term and expand. *)
  | TmFold(i, ty, tm) ->
     interp tm >>= fun tm ->
     checkerToInterpreter (ty_normalize_app ty) >>= fun ty' ->
     return @@ TmFold(i, ty', tm)
  | TmUnfold(i, tm)   ->
      interp tm >>= fun tm -> 
      withFailTerm (TmUnfold(i,tm))
      begin match tm with 
        | TmFold(_,_,tm') -> decLim >> return tm'
        | _ -> fail_pp "**Interpreter** Tried to unfold a non-folded term: %a" pp_term t
      end

  (* Bindings should always be propagated, but just like with 
     substitutions in abstractions, care needs to be taken to 
     deal with unevaluated terms due to partial evaluation. *)
  | TmLet(i, b, si, tm, tBody) ->
      interp tm >>= fun tm -> 
      decLim >> interp (tm_substTm tm 0 0 tBody)
  
  (* Statement bodies can be evaluated during partial evaluation, but the
     statement itself should not be removed. *)
  | TmStmt(i, tm1, tm2) ->
      interp tm1 >>= fun tm1 -> 
      interp tm2 >>= fun tm2 ->
      withFailTerm (TmStmt(i, tm1, tm2))
      begin if tmIsVal tm1 (* if tm1 has been fully reduced, then it is safe to remove *)
        then decLim >> return tm2
        else fail_pp "**Interpreter** A statement failed to evaluate to a value.  Found: %a" pp_term tm1
      end
  
  (* A recursive function should always be expanded except if we are in 
     the case where we are both in under-branch mode and this is a 
     recursive call.  To expand, substitute this recfun itself into 
     itself (but setting that it is now internally a recursive call). *)
  | TmRecFun(i, bi, ty, tm, isRec) ->
      let tm = tm_substTm (TmRecFun(i, bi, ty, tm, true)) 0 0 tm in
      decLim >> interp tm
  
  (* Sample is the bind of our probability monad. *)
  | TmSample(i, b, tm, tBody) ->
      interp tm >>= fun tm ->
      withFailTerm (TmSample (i,b,tm,tBody))
      begin match tm with
        | TmPVal(i', t) when tmIsVal t -> (* This is a distribution of 100% probability, i.e. a return.  We can treat it like a let. *)
            decLim >> interp (tm_substTm t 0 0 tBody)
        | TmPVal(i', t) ->
            decLim >> return (TmPVal (i, TmUnPVal (i, tm_substTm t 0 0 tBody))) (* Stay lazy -- do not interp after this substitution *)
        | _ -> fail_pp "**Interpreter** Sample expected a Probabilistic Value but found %a." pp_term tm
      end
  
  (* Type Abstraction and Applicacion.  In a regular evaluator, these 
     could be resolved as no-ops, but because of partial evaluation and 
     a potential for mid-execution type checking, these need to be 
     properly resolved.  Type abstractions are just abstractions and 
     remain as values.  Type application performs the type substitution 
     (or fails). *)
  | TmTyAbs(_, _, _) -> return t
  | TmTyApp(i, tm, ty) ->
      interp tm >>= fun tm ->
      withFailTerm (TmTyApp(i, tm, ty))
      begin checkerToInterpreter (ty_normalize_app ty) >>= fun ty ->
      match tyIsVal ty, tm with
        | true, TmTyAbs(i', bi, tm') -> decLim >> interp (tm_substTy ty 0 0 tm')
        | true,  _ -> fail_pp "**Interpreter** Type Application expected a TyLambda but found %a." pp_term tm
        | false, _ -> fail_pp "**Interpreter** Type Application expected a fully evaluated type but found %a." pp_type ty
      end
  
  (* Similar to type abstraction and application, this could be a no-op 
     if not for the potiential for mid-execution type checking.  Instead, 
     we perform a type substition just as we would in the type checker. *)
  | TmTypedef(i,b,ty,tm) -> 
      decLim >> interp (tm_substTy (ty_shiftTy 0 (-1) ty) 0 0 tm)
  
  (* IfThenElse terms are just a special syntax case of case expressions. *)
  | TmIfThenElse(i, test, tterm, eterm) ->
      interp test >>= fun b -> 
      withFailTerm (TmIfThenElse(i, b, tterm, eterm))
      begin match b with
        | TmPrim(_,PrimTBool(b')) -> decLim >> interp (if b' then tterm else eterm)
        | _ -> fail_pp "**Interpreter** If statement expected a Bool but found %a." pp_term b
      end


let pinterp (t : term) : term interpreter = match t with
  | TmPrimFun(i, s, pf, ty, ttslst)  ->
      mapM (fun (tm,ty,si) -> mapMTy interp ty >>= fun ty -> 
                              mapMSi interp si >>= fun si ->
                              return (tm,ty,si)) ttslst >>= fun ttslst ->
      interp (TmPrimFun(i, s, pf, ty, ttslst))
  
  | TmAbs(i, bi, (si, ty), tyo, tm) -> 
      mapMSi interp si >>= fun si ->
      mapMTy interp ty >>= fun ty ->
      (match tyo with
        | None -> return None
        | Some t -> mapMTy interp t >>= fun x -> return (Some x)
      ) >>= fun tyo ->
      return @@ TmAbs(i, bi, (si, ty), tyo, tm)
  
  | _ -> interp t


(* This function generates a pinterp for the type checker *)
let genPinterp ctx l t = match pinterp t (None, Some l, ctx) with
  | (_, Some l', Ok t') when l' < l -> Some (l', t')
  | _ -> None

(* Runs a program.  The program must output a string in the end, 
   and this will provide that string. *)
let run_interp (program : term) : string =
  match interp program (None, None, Ctx.empty_context) with
  | (_, _, Ok (TmPrim(_,PrimTString(s))))   -> s
  | (_, _, Ok _)    -> interp_error "%s" "Interpreter returned a non-string value"
  | (_, _, Error s) -> interp_error "%s" s

