/* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*/
%{

open Types
open Syntax

open Support.FileInfo

let parser_error   fi = Support.Error.error_msg   Support.Options.Parser fi
let parser_warning fi = Support.Error.message   1 Support.Options.Parser fi
let parser_info    fi = Support.Error.message   2 Support.Options.Parser fi

let si_zero  = SiZero
let si_one   = SiConst 1.0
let si_infty = SiInfty

(* look for a variable in the current context *)
let existing_var fi id ctx =
  match Ctx.lookup_var id ctx with
      None            -> parser_error fi "Identifier %s is unbound" id
    | Some (var, _bi) -> var

let existing_tyvar fi id ctx =
  match Ctx.lookup_tyvar id ctx with
      None      -> parser_error fi "Type %s is unbound" id
    | Some var  -> var

let dummyTy = TyPrim PrimUnit

(* Wrap extend here in order to avoid mutually recursive
   dependencies *)
(* TODO: Do these really need to be wrapped?
   More importantly, let's use the non-primed version of these Ctx 
   functions and get the sizes right in the binders (see below). *)
let extend_var id ctx =
  Ctx.extend_ctx_with_var' id dummyTy ctx

let extend_ty_var id ctx =
  Ctx.extend_ctx_with_tyvar' id ctx

(* Create a new binder *)
(* TODO: set the proper b_size !!! *)
let nb_prim  n = {b_name = n; b_type = BiVar;   b_size = -1; b_prim = true;}
let nb_var   n = {b_name = n; b_type = BiVar;   b_size = -1; b_prim = false;}
let nb_tyvar n = {b_name = n; b_type = BiTyVar; b_size = -1; b_prim = false;}

(* From a list of arguments to a type *)
let rec qf_to_type qf ty = match qf with
    []              -> ty
  | (_, n) :: qfl   -> TyForall(nb_tyvar n, qf_to_type qfl ty)

let rec list_to_type l ret_ty = match l with
    []                        -> ret_ty
  | (ty, si, _n, _i) :: tyl   -> TyLollipop (ty, si, list_to_type tyl ret_ty)

let from_args_to_type qf arg_list ret_ty =
  qf_to_type qf (list_to_type arg_list ret_ty)

(* From a list of arguments to a term *)
let rec qf_to_term qf tm = match qf with
    []              -> tm
  | (i, n) :: qfl   -> TmTyAbs (i, nb_tyvar n, qf_to_term qfl tm)

let rec list_to_term l body = match l with
    []                    -> body
  | (ty, si, n, i) :: tml -> TmAbs (i, nb_var n, (si, ty), None, list_to_term tml body)

let from_args_to_term qf arg_list body =
  qf_to_term qf (list_to_term arg_list body)

let mkNewVarsInType ty ctx = 
  let f k i v = TmVar(i, var_shift 0 k (existing_var i v.v_name ctx)) in
  ty_mapTm f 0 ty

let mkNewVarsInSi si ctx = 
  let f k i v = TmVar(i, var_shift 0 k (existing_var i v.v_name ctx)) in
  si_mapTm f 0 si

(* When we're making this list for primFuns, the type may have terms in it (e.g. 
   SiTerms).  They must be appropriately indexed, so we remake them with the 
   current (potentially extended) context.  We do this with mkNewVarsInType. *)
let rec args_to_args_list fi arg_list ctx = match arg_list with
  | []      -> []
  | (ty, si, n, i) :: arg_list' -> (TmVar(fi, existing_var fi n ctx), mkNewVarsInType ty ctx, mkNewVarsInSi si ctx) 
                                 :: args_to_args_list fi arg_list' ctx

let mk_infix ctx info op t1 t2 =
  match Ctx.lookup_var op ctx with
      None      -> parser_error info "The primitive infix operator %s is not in scope" op
    | Some(v,_) -> TmApp(info, TmApp(info, TmVar(info, v), t1), t2)

(* This takes a *reversed* list of arguments *)
let rec mk_prim_app_args info v arglist = match arglist with
  | []        -> v
  | (o :: op) -> TmApp(info, (mk_prim_app_args info v op), o)

let mk_prim_app ctx info prim arglist =
  match Ctx.lookup_var prim ctx with
    None      -> parser_error info "Primitive %s is not in scope" prim
  | Some(v,_) -> mk_prim_app_args info (TmVar(info, v)) (List.rev arglist)

let rec mk_prim_app_ty_args info v arglist = match arglist with
  | []        -> v
  | (o :: op) -> TmTyApp(info, (mk_prim_app_ty_args info v op), o)

let mk_prim_ty_app ctx info prim arglist =
  match Ctx.lookup_var prim ctx with
    None      -> parser_error info "Primitive %s is not in scope" prim
  | Some(v,_) -> mk_prim_app_ty_args info (TmVar(info, v)) (List.rev arglist)

let mk_lambda info bi oty term = TmAbs(info, bi, oty, None, term)

let rec remove_quantifiers ty = match ty with
    TyForall(_,ty_i) -> remove_quantifiers ty_i
  | _ -> ty

(* Find the hole, which is the unit value at the bottom of the file, and replace
   it with the supplied term *)
let rec prepend_import import tm =
      match import with
       | TmPrim (_, PrimTUnit) -> tm
       | TmStmt (i, expr, next_tm) -> TmStmt (i, expr, prepend_import next_tm tm)
       | TmLet  (i, b, si, tm1, next_tm) ->
                TmLet (i, b, si, tm1, prepend_import next_tm tm)
       | TmTensDest(i, b1, b2, tm1, next_tm) ->
                TmTensDest(i, b1, b2, tm1, prepend_import next_tm tm)
       | TmSample(i, b, e, next_tm) ->
       	 	TmSample(i, b, e, prepend_import next_tm tm)
       | TmTypedef(i, b, ty, next_tm) ->
       	 	TmTypedef(i, b, ty, prepend_import next_tm tm)
       | _ -> tm (*parser_error dummyinfo "Found import at the wrong place."*)

%}

/* ---------------------------------------------------------------------- */
/* Preliminaries */

/* Keyword tokens */
%token <Support.FileInfo.info> ADD
%token <Support.FileInfo.info> AMP
%token <Support.FileInfo.info> AND
%token <Support.FileInfo.info> ARROW
%token <Support.FileInfo.info> COLON
%token <Support.FileInfo.info> CONS
%token <Support.FileInfo.info> COMMA
%token <Support.FileInfo.info> DOLLAR
%token <Support.FileInfo.info> LBRACE
%token <Support.FileInfo.info> QUESTION
%token <Support.FileInfo.info> SEMI
%token <Support.FileInfo.info> RBRACE
%token <Support.FileInfo.info> EQUAL
%token <Support.FileInfo.info> HAT
%token <Support.FileInfo.info> BEQUAL
%token <Support.FileInfo.info> DBLARROW
%token <Support.FileInfo.info> SUB
%token <Support.FileInfo.info> MUL
%token <Support.FileInfo.info> DIV
%token <Support.FileInfo.info> LPAREN
%token <Support.FileInfo.info> RPAREN
%token <Support.FileInfo.info> LT
%token <Support.FileInfo.info> GT
%token <Support.FileInfo.info> LBRACK
%token <Support.FileInfo.info> RBRACK
%token <Support.FileInfo.info> PIPE
%token <Support.FileInfo.info> OR
%token <Support.FileInfo.info> BANG
%token <Support.FileInfo.info> LOLLIPOP
%token <Support.FileInfo.info> TRUE
%token <Support.FileInfo.info> FALSE
%token <Support.FileInfo.info> INF
%token <Support.FileInfo.info> INL
%token <Support.FileInfo.info> INR
%token <Support.FileInfo.info> FUZZY
%token <Support.FileInfo.info> FUN
%token <Support.FileInfo.info> UNIONCASE
%token <Support.FileInfo.info> OF
%token <Support.FileInfo.info> FOLD
%token <Support.FileInfo.info> UNFOLD
%token <Support.FileInfo.info> MU
%token <Support.FileInfo.info> LET
%token <Support.FileInfo.info> TYPEDEF
%token <Support.FileInfo.info> SAMPLE
%token <Support.FileInfo.info> FUNCTION
%token <Support.FileInfo.info> PRIMITIVE
%token <Support.FileInfo.info> SET
%token <Support.FileInfo.info> BAG
%token <Support.FileInfo.info> VECTOR
%token <Support.FileInfo.info> TOKEN
%token <Support.FileInfo.info> IF
%token <Support.FileInfo.info> THEN
%token <Support.FileInfo.info> ELSE
%token <Support.FileInfo.info> EOF
%token <Support.FileInfo.info> BOOL
%token <Support.FileInfo.info> NUM
%token <Support.FileInfo.info> STRING
%token <Support.FileInfo.info> SIZE
%token <Support.FileInfo.info> SENS
%token <Support.FileInfo.info> TYPE
%token <Support.FileInfo.info> FORALL
%token <Support.FileInfo.info> CLIPPED
%token <Support.FileInfo.info> INT
%token <Support.FileInfo.info> DOT
%token <Support.FileInfo.info> DOTMUL
%token <Support.FileInfo.info> DOTDIV
%token <Support.FileInfo.info> ZERO
%token <Support.FileInfo.info> SUCC

/* Identifier and constant value tokens */
%token <string Support.FileInfo.withinfo> ID
%token <int    Support.FileInfo.withinfo> INTV
%token <float  Support.FileInfo.withinfo> FLOATV
%token <string Support.FileInfo.withinfo> STRINGV

/* Token for included program */
%token <(Types.term * Types.context) Support.FileInfo.withinfo> IMPORT


/* ---------------------------------------------------------------------- */
/* Fuzz grammar                                                           */
/* ---------------------------------------------------------------------- */

%start body
%type < (Types.term * Types.context) > body
%%

/* ---------------------------------------------------------------------- */
/* Main body of the parser definition                                     */
/* ---------------------------------------------------------------------- */

body :
  Imports Term EOF
      { let imports = List.map (fun item -> item.v) $1 in
      	let imported_tms  = List.map fst imports       in
	let imported_ctxs = List.map snd imports       in
	let initial_ctx   = List.fold_left Ctx.merge_ctx
	    		    		   Ctx.empty_context
					   imported_ctxs in
	let (term, final_ctx) = $2 initial_ctx           in
	let final_term = List.fold_right prepend_import imported_tms term in
	(*
	List.map (fun item -> Format.print_string ((fst item).v_name ^ "\n"))
		 initial_ctx.var_ctx;
        Format.print_int (List.length initial_ctx.var_ctx);
	Format.print_string "\n";
	*)
        (final_term, final_ctx)
      }

Imports :
  /* Nothing */
    { [] }
  | IMPORT Imports
    { $1 :: $2 }

PrimSpec :
    STRINGV
      { $1 }

Term :
    Expr SEMI Term
      {
        fun ctx -> let (tm, next_ctx) = $3 ctx in (TmStmt($2, $1 ctx, tm), next_ctx)
      }
  | ID SensAnn EQUAL Expr SEMI Term
      {
        fun ctx ->
          let ctx' = extend_var $1.v ctx        in
	  let (tm, next_ctx) = $6 ctx'          in
          (TmLet($1.i, (nb_var $1.v), $2 ctx, $4 ctx, tm), next_ctx)
      }
  | LET LPAREN ID COMMA ID RPAREN EQUAL Expr SEMI Term
      { fun ctx ->
        (* TODO, what happens with let (x,x) = ...? *)
        let ctx_x   = extend_var $3.v ctx          in
        let ctx_xy  = extend_var $5.v ctx_x        in
	let (tm, next_ctx) = $10 ctx_xy            in
        (TmTensDest($1, (nb_var $3.v), (nb_var $5.v), $8 ctx, tm), next_ctx)
      }
  | SAMPLE ID EQUAL Expr SEMI Term
      { fun ctx ->
        let ctx' = extend_var $2.v ctx        in
      	let (tm, next_ctx) = $6 ctx'          in
        (TmSample ($2.i, (nb_var $2.v), $4 ctx, tm), next_ctx)
      }
  | TYPEDEF ID EQUAL Type SEMI Term
      {
        fun ctx ->
        let ctx_let = extend_ty_var $2.v ctx in
	let (tm, next_ctx) = $6 ctx_let      in
        (TmTypedef($1, (nb_tyvar $2.v), $4 ctx_let, tm), next_ctx)
      }
  | PRIMITIVE ID Quantifiers Arguments COLON Type LBRACE PrimSpec RBRACE Term
      { fun ctx ->
        let ctx_let          = extend_var $2.v ctx                          in
        let (qf,   ctx_qf)   = $3 ctx                                       in
        let (args, ctx_args) = $4 ctx_qf                                    in
        let arglst           = args_to_args_list $1 args ctx_args           in
        let body             = TmPrimFun($8.i, $8.v, $6 ctx_args, arglst)   in
        let f_term           = from_args_to_term qf args body               in
	let (next_tm, next_ctx)     = $10 ctx_let			    in

        (TmLet($1, nb_prim $2.v, si_infty, f_term, next_tm), next_ctx)
      }
  | FUNCTION ID Quantifiers Arguments COLON Type LBRACE Term RBRACE Term
      {
        fun ctx ->
        let ctx_let          = extend_var $2.v ctx        in
        let (qf,   ctx_qf)   = $3 ctx_let                 in
        let (args, ctx_args) = $4 ctx_qf                  in
        let f_type           = from_args_to_type qf args ($6 ctx_args) in
        let f_term           = from_args_to_term qf args (fst ($8 ctx_args)) in
        let recfun           = TmRecFun ($2.i, nb_var $2.v, f_type, f_term, false) in
	let (next_tm, next_ctx) = $10 ctx_let  	      	  in
        (TmLet($2.i, nb_var $2.v, si_infty, recfun, next_tm), next_ctx)
      }
  | LogOrTerm
      { fun ctx -> ($1 ctx, ctx) }

Argument :
    LPAREN ID COLON MaybeSensitivity Type RPAREN
      { fun ctx -> ([($5 ctx, $4 ctx, $2.v, $2.i)], extend_var $2.v ctx) }

/*
   Arguments returns a tuple of (arg, ctx), where arg is the list of
   arguments ready to build a higher-order type, including quantifiers.
*/
Arguments :
  /* Nothing */
    { fun ctx -> ([], ctx) }
  | Argument Arguments
      { fun ctx ->
          let (l,  ctx')  = $1 ctx in
          let (l2, ctx'') = $2 ctx' in
          (l @ l2, ctx'')
      }

Expr :
      LogOrTerm
      { $1 }

LogOrTerm : /* Logical Or Term */
    LogOrTerm OR LogAndTerm
      { fun ctx -> mk_infix ctx $2 "op_lor" ($1 ctx) ($3 ctx) }
  | LogAndTerm
      { $1 }

LogAndTerm: /* Logical And Term */
    LogAndTerm AND BequalTerm
      { fun ctx -> mk_infix ctx $2 "op_land" ($1 ctx) ($3 ctx) }
  | BequalTerm
      { $1 }

BequalTerm :
    BequalTerm BEQUAL RelTerm
      { fun ctx -> mk_infix ctx $2 "op_eq" ($1 ctx) ($3 ctx) }
  | BequalTerm BANG EQUAL RelTerm
      { fun ctx -> mk_infix ctx $2 "op_neq" ($1 ctx) ($4 ctx) }
  | RelTerm
      { $1 }

RelTerm :
    RelTerm LT AddTerm
      { fun ctx -> mk_infix ctx $2 "op_lt" ($1 ctx) ($3 ctx) }
  | RelTerm GT AddTerm
      { fun ctx -> mk_infix ctx $2 "op_gt" ($1 ctx) ($3 ctx) }
  | RelTerm LT EQUAL AddTerm
      { fun ctx -> mk_infix ctx $2 "op_lte" ($1 ctx) ($4 ctx) }
  | RelTerm GT EQUAL AddTerm
      { fun ctx -> mk_infix ctx $2 "op_gte" ($1 ctx) ($4 ctx) }
  | AddTerm
      { $1 }

AddTerm :
    AddTerm ADD MulTerm
      { fun ctx -> mk_infix ctx $2 "op_add"  ($1 ctx) ($3 ctx) }
  | AddTerm ADD DOT MulTerm
      { fun ctx -> mk_infix ctx $2 "op_iadd" ($1 ctx) ($4 ctx) }
  | AddTerm SUB MulTerm
      { fun ctx -> mk_infix ctx $2 "op_sub"  ($1 ctx) ($3 ctx) }
  | AddTerm SUB DOT MulTerm
      { fun ctx -> mk_infix ctx $2 "op_isub" ($1 ctx) ($4 ctx) }
  | AddTerm HAT MulTerm
      { fun ctx -> mk_infix ctx $2 "string_concat" ($1 ctx) ($3 ctx) }
  | MulTerm
      { $1 }

MulTerm :
    MulTerm MUL FTerm
      { fun ctx -> mk_infix ctx $2 "op_mul"  ($1 ctx) ($3 ctx) }
  | MulTerm MUL DOT FTerm
      { fun ctx -> mk_infix ctx $2 "op_imul" ($1 ctx) ($4 ctx) }
  | MulTerm DIV FTerm
      { fun ctx -> mk_infix ctx $2 "op_div"  ($1 ctx) ($3 ctx) }
  | MulTerm DIV DOT FTerm
      { fun ctx -> mk_infix ctx $2 "op_idiv" ($1 ctx) ($4 ctx) }
  | FTerm
      { $1 }

FTerm :
  | FOLD LBRACK Type RBRACK STerm
      { fun ctx -> TmFold($1, $3 ctx, $5 ctx) }
  | UNFOLD STerm
      { fun ctx -> TmUnfold($1, $2 ctx) }
  | STerm
      { $1 }

STerm :
    IF Expr THEN LBRACE Term RBRACE ELSE LBRACE Term RBRACE
      { fun ctx -> TmIfThenElse($1, $2 ctx, fst ($5 ctx), fst ($9 ctx)) }
  | UNIONCASE Expr OF LBRACE INL LPAREN ID RPAREN DBLARROW Term PIPE INR LPAREN ID RPAREN DBLARROW Term RBRACE
      { fun ctx ->
        let ctx_l = extend_var $7.v  ctx in
        let ctx_r = extend_var $14.v ctx in
        TmUnionCase($1, $2 ctx, nb_var $7.v, fst ($10 ctx_l), nb_var $14.v, fst ($17 ctx_r)) }

  | FUN LPAREN ID SensType RPAREN MaybeType LBRACE Term RBRACE
      { fun ctx -> TmAbs($1, nb_var $3.v, $4 ctx, $6 ctx, fst ($8 (extend_var $3.v ctx))) }
  | INL LBRACK Type RBRACK LBRACK Type RBRACK LBRACE Term RBRACE
      { fun ctx -> TmLeft($1, fst ($9 ctx), $6 ctx)  }
  | INR LBRACK Type RBRACK LBRACK Type RBRACK LBRACE Term RBRACE
      { fun ctx -> TmRight($1, fst ($9 ctx), $3 ctx)  }
  | FExpr
      { $1 }

FExpr :
    TFExpr
      { $1 }
  | FExpr TFExpr
      { fun ctx -> let e1 = $1 ctx in let e2 = $2 ctx in TmApp(tmInfo e1, e1, e2) }

/* Type application */
TFExpr:
    AExpr
      { $1 }
  | TFExpr LBRACK Type RBRACK
      { fun ctx -> TmTyApp($2, $1 ctx, $3 ctx) }

/* Sugar for n-ary tuples */
PairSeq:
    Term COMMA Term
      { fun ctx -> TmPair($2, fst ($1 ctx), fst ($3 ctx))  }
  | Term COMMA PairSeq
      { fun ctx -> TmPair($2, fst ($1 ctx), $3 ctx)  }

AExpr:
    TRUE
      { fun _cx -> TmPrim ($1, PrimTBool true) }
  | FALSE
      { fun _cx -> TmPrim ($1, PrimTBool false) }
  | LPAREN RPAREN
      { fun _cx -> TmPrim ($1, PrimTUnit) }
  | ID
      { fun ctx -> TmVar($1.i, existing_var $1.i $1.v ctx) }
  | LPAREN Term RPAREN
      { fun ctx -> fst ($2 ctx) }
  | LPAREN PairSeq RPAREN
      { fun ctx -> $2 ctx }
  | LPAREN PIPE Term COMMA Term PIPE RPAREN
      { fun ctx -> TmAmpersand($1, fst ($3 ctx), fst ($5 ctx)) }
  | STRINGV
      { fun _cx -> TmPrim($1.i, PrimTString $1.v) }
  | FLOATV
      { fun _cx -> TmPrim($1.i, PrimTNum $1.v) }
  | INTV
      { fun _cx -> TmPrim($1.i, PrimTInt $1.v) }

/* Sensitivities and sizes */
SensTerm :
    LBRACK Term RBRACK
      { fun ctx -> SiTerm (fst ($2 ctx)) }
  | INTV
      { fun _cx -> SiConst (float_of_int $1.v) }
  | FLOATV
      { fun _cx -> SiConst $1.v }

SensType :
  | COLON MaybeSensitivity Type
      { fun ctx -> ($2 ctx, $3 ctx) }

SensAnn :
    /* nothing */
      { fun _cx -> si_infty }
  | COLON MaybeSensitivity
      { fun ctx -> $2 ctx }

MaybeSensitivity:
    /* nothing */
      { fun _cx -> si_infty }
  | LBRACK RBRACK
      { fun _cx -> si_one }
  | LBRACK SensTerm RBRACK
      { $2 }

QuantifierList :
    ID
      { fun ctx -> ([($1.i, $1.v)], extend_ty_var $1.v ctx) }
  | ID COMMA QuantifierList
      { fun ctx -> let ctx' = extend_ty_var $1.v ctx in
                   let (qlst, ctx'') = $3 ctx' in
                   (($1.i, $1.v) :: qlst, ctx'')
      }

Quantifiers :
  /* Nothing */
    { fun ctx -> ([], ctx) }
  | FORALL LPAREN QuantifierList RPAREN
    { $3 }

MaybeType:
    {fun _ctx -> None}
  | COLON Type
      {fun ctx -> Some ($2 ctx)}

TypeApp :
    LPAREN Type RPAREN LBRACK Type RBRACK
    { fun ctx -> let ty_abs  = $2 ctx in
      	      	 let ty_body = $5 ctx in
		 TyTyApp(ty_abs, ty_body)
    }
  | ID LBRACK Type RBRACK
    { fun ctx ->
      let ty_var_info = existing_tyvar $1.i $1.v ctx in
      TyTyApp(TyVar(ty_var_info), $3 ctx)
    }
  | TypeApp LBRACK Type RBRACK
    { fun ctx -> let ty_abs  = $1 ctx in
      	         let ty_body = $3 ctx in
		 TyTyApp(ty_abs, ty_body)
    }

Type :
    AType BAG
      { fun ctx -> TyPrim1 (Prim1Bag, ($1 ctx)) }
  | AType VECTOR
      { fun ctx -> TyPrim1 (Prim1Vector, ($1 ctx)) }
  | AType TOKEN
      { fun ctx -> TyPrim1 (Prim1Token, ($1 ctx)) }
  | MU ID DBLARROW Type
      { fun ctx -> TyMu(nb_tyvar $2.v, $4 (extend_ty_var $2.v ctx)) }
  | ComplexType
      { $1 }

ComplexType :
    AType ARROW ComplexType
      { fun ctx -> TyLollipop($1 ctx, si_infty, $3 ctx) }
  | AType ADD ComplexType
      { fun ctx -> TyUnion($1 ctx, $3 ctx) }
  | AType LOLLIPOP ComplexType
      { fun ctx -> TyLollipop($1 ctx, si_one, $3 (extend_var "__dummy" ctx)) }
  | AType LOLLIPOP LBRACK SensTerm RBRACK ComplexType
      { fun ctx -> TyLollipop($1 ctx, $4 ctx, $6 (extend_var "__dummy" ctx)) }
  | FUZZY Type
      { fun ctx -> TyPrim1 (Prim1Fuzzy, ($2 ctx)) }
  | AType
      { $1 }
  | Quantifiers DOT Type
      { fun ctx ->
        (* qf is of type [(Support.FileInfo.info, string)] *)
      	let (qf, qf_ctx) = $1 ctx    in
	let ty_body = $3 qf_ctx in
        qf_to_type qf ty_body
      }

TPairSeq:
    Type COMMA Type
      { fun ctx -> TyTensor($1 ctx, $3 ctx) }
  | Type COMMA TPairSeq
      { fun ctx -> TyTensor($1 ctx, $3 ctx) }

AType :
    LPAREN Type RPAREN
      { $2 }
  | ID
      { fun ctx -> TyVar (existing_tyvar $1.i $1.v ctx) }
  | BOOL
      { fun _cx -> TyPrim PrimBool }
  | NUM
      { fun _cx -> TyPrim PrimNum }
  | INT
      { fun _cx -> TyPrim PrimInt }
  | STRING
      { fun _cx -> TyPrim PrimString }
  | CLIPPED
      { fun _cx -> TyPrim PrimClipped }
  | LPAREN RPAREN
      { fun _cx -> TyPrim PrimUnit }
  | LPAREN TPairSeq RPAREN
      { fun ctx -> $2 ctx }
  | LPAREN PIPE Type COMMA Type PIPE RPAREN
      { fun ctx -> TyAmpersand($3 ctx, $5 ctx) }
  | TypeApp
      { $1 }