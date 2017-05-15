(* file name: conversion.ml
   created by: Daniel Winograd-Cort
   Last modified: 5/6/2017
   
   Description:
   This file contains conversion functions for communication between processes.
   Ideally, these functions would use Marshal, but this is causing some problems.
   The main functions are:
     val marshal ppf ty =
     val unmarshal : info -> ty -> string -> term option
*)

open Types
open Support.FileInfo
open Option
open Print


let di = dummyinfo
let fprintf = Format.fprintf

module Mkers = struct
  (* The make functions turn an ocaml value into a term *)
  let mkBool i b   = TmPrim (i, PrimTBool b)
  let mkNum i n    = TmPrim (i, PrimTNum n)
  let mkClipped i c = TmPrim (i, PrimTClipped (if c > 1.0 then 1.0 else if c < 0.0 then 0.0 else c))
  let mkInt i n    = TmPrim (i, PrimTInt n)
  let mkString i s = TmPrim (i, PrimTString s)
  let mkBag i (ty, l) = TmBag (i, ty, l)
  let mkBag' mkA i (ty, l) = TmBag (i, ty, List.map (mkA i) l)
  let mkVector i (ty, l) = TmVector (i, ty, l)
  let mkToken i (n,ty)  = TmPrim (i, PrimTToken (n,ty))
  let mkPair mk1 mk2 i (t1, t2) = TmPair (i, mk1 i t1, mk2 i t2)
  let mkSum mkl mkr i (tyl, tyr, x) = match x with
    | Left l  -> TmLeft (i, mkl i l, tyr)
    | Right r -> TmRight(i, mkr i r, tyl)
  let mkPVal mk i t  = TmPVal (i, mk i t)
  let mkAny _i t   = t
  let mkUnit i _   = TmPrim (i, PrimTUnit)
  
  let rec mkListWithType mkA i (ty, lsttype, lst) = 
    match lst with
    | [] -> TmFold(i, lsttype, TmLeft(i, TmPrim(i, PrimTUnit), TyTensor(ty, lsttype)))
    | x::xs -> TmFold(i, lsttype, TmRight(i, TmPair(i, mkA i x, mkListWithType mkA i (ty, lsttype, xs)), TyPrim PrimUnit))
  let mkList mkA i (ty, lst) =
    let lsttype = TyMu({b_name = "XX"; b_type = BiTyVar; b_size = -1; b_prim = false;}, TyUnion
            (TyPrim PrimUnit, TyTensor(ty, TyVar
                ({v_index = 0; v_name = "XX"; v_size = -1; v_type = BiTyVar;})))) in
    mkListWithType mkA i (ty, lsttype, lst)

end

open Mkers


(*
let marshalFromString (s : string) : 'a option = 
  try
    Some (Marshal.from_string s 0)
  with Invalid_argument s -> 
    (printMsg di "%s" s; None)

let rec unMarshalTerm (i : info) (ty : ty) (obj : 'a) : term option = match ty with
  | TyPrim PrimNum  -> Some (mkNum i (Obj.magic obj))
  | TyPrim PrimInt  -> Some (mkInt i (Obj.magic obj))
  | TyPrim PrimUnit -> Some (mkUnit i ())
  | TyPrim PrimBool -> Some (mkBool i (Obj.magic obj))
  | TyPrim PrimString   -> Some (mkString i (Obj.magic obj))
  | TyPrim PrimClipped  -> Some (mkClipped i (Obj.magic obj))
  | TyPrim1 (Prim1Token, t) -> Some (mkToken i (Obj.magic obj, t))
  | TyPrim1 (Prim1Bag, t) -> let v = Option.opt_bind_list (List.map (unMarshalTerm i t) (Obj.magic obj)) in
        Option.map (fun lst -> mkBag i (ty,lst)) v
  | TyPrim1 (Prim1Vector, t) -> let v = Option.opt_bind_list (List.map (unMarshalTerm i t) (Array.to_list (Obj.magic obj))) in
        Option.map (fun lst -> mkVector i (ty,lst)) v
  | TyTensor(t1,t2) -> let (v1,v2) = Obj.magic obj in
                       Option.obind (unMarshalTerm i t1 v1) (fun tm1 ->
                       Option.obind (unMarshalTerm i t2 v2) (fun tm2 ->
                       Some (TmPair(i,tm1,tm2))))
  | TyAmpersand(t1,t2) -> let (v1,v2) = Obj.magic obj in
                       Option.obind (unMarshalTerm i t1 v1) (fun tm1 ->
                       Option.obind (unMarshalTerm i t2 v2) (fun tm2 ->
                       Some (TmAmpersand(i,tm1,tm2))))
  | TyUnion(t1,t2) -> begin match Obj.magic obj with
                      | Left a  -> Option.map (fun tm -> TmLeft (i,tm,t2)) (unMarshalTerm i t1 a)
                      | Right b -> Option.map (fun tm -> TmRight(i,tm,t1)) (unMarshalTerm i t2 b)
                      end
  | _ -> None

let marshal ppf ty = fprintf ppf "%s" "(fun a -> Marshal.to_string a [])"
let unmarshal (i : info) (typ : ty) (a : string) : term option =
  Option.obind (marshalFromString a) (unMarshalTerm i typ)

*)



let stringToFloat (s : string) : float = 
  try
    float_of_string s
  with Failure _ -> 0.

let stringToInt (s : string) : int = 
  try
    int_of_string s
  with Failure _ -> 0

let stringToBool (s : string) : bool = 
  try
    bool_of_string s
  with Failure _ -> false


let rec stringToFuzz (i : info) (ty : ty) (s : string) : term option = match ty with
  | TyPrim PrimNum  -> Some (mkNum i (stringToFloat s))
  | TyPrim PrimInt  -> Some (mkInt i (stringToInt s))
  | TyPrim PrimUnit -> Some (mkUnit i ())
  | TyPrim PrimBool -> Some (mkBool i (stringToBool s))
  | TyPrim PrimString   -> Some (mkString i s)
  | TyPrim PrimClipped  -> Some (mkClipped i (stringToFloat s))
  | TyPrim1 (Prim1Token, t) -> Some (mkToken i (stringToInt s, t))
  | TyPrim1 (Prim1Bag,    t) -> map (fun lst -> mkBag    i (ty, lst))
        (opt_bind_list (List.map (stringToFuzz i t) (Str.split (Str.regexp "[ \t]+") s)))
  | TyPrim1 (Prim1Vector, t) -> map (fun lst -> mkVector i (ty, lst))
        (opt_bind_list (List.map (stringToFuzz i t) (Str.split (Str.regexp "[ \t]+") s)))
  | TyUnion (tyl,tyr) -> begin match String.sub s 0 4 with
      | "inl " -> map (fun l -> TmLeft  (i, l, tyr)) (stringToFuzz i tyl (String.sub s 4 (String.length s - 4)))
      | "inr " -> map (fun r -> TmRight (i, r, tyl)) (stringToFuzz i tyr (String.sub s 4 (String.length s - 4)))
      | _ -> None
      end
  (* FIXME: Tensor product reading only works if there's no nesting.
     This should all really be either marshaling or proper parsing. *)
  | TyTensor (tyl,tyr) -> begin match Str.split (Str.regexp_string ",") (String.sub s 1 (String.length s - 2)) with
      | s1::s2::[] -> obind (stringToFuzz i tyl s1) (fun tml ->
                      obind (stringToFuzz i tyr s2) (fun tmr ->
                      Some (TmPair (i, tml, tmr))))
      | _ -> None
      end
  | _ -> None


let rec marshal ppf ty = match ty with
  | TyPrim PrimNum  -> fprintf ppf "%s" "string_of_float"
  | TyPrim PrimInt  -> fprintf ppf "%s" "(fun i -> string_of_int (truncate i))"
  | TyPrim PrimUnit -> fprintf ppf "%s" "(fun _ -> \"()\")"
  | TyPrim PrimBool -> fprintf ppf "%s" "string_of_bool"
  | TyPrim PrimString   -> fprintf ppf ""
  | TyPrim PrimClipped  -> fprintf ppf "%s" "string_of_float"
  | TyPrim1 (Prim1Token, t) -> fprintf ppf "%s" "string_of_int"
  | TyPrim1 (Prim1Bag, t) -> fprintf ppf "(fun lst -> String.concat \" \" (List.map %a lst))"
        marshal t
  | TyPrim1 (Prim1Vector, t) -> fprintf ppf "(fun a -> Array.fold_right (fun x -> fun xs -> (%a x) ^ \" \" ^ xs) a \"\")"
        marshal t
  | TyTensor (t1, t2) -> fprintf ppf "(fun xy -> \"(\"^(%a (fst xy))^\", \"^(%a (snd xy))^\")\")"
        marshal t1 marshal t2
  | TyUnion  (t1, t2) -> fprintf ppf "(fun u -> (match u with Left x -> \"inl \"^(%a x) | Right x -> \"inr \"^(%a x)))"
        marshal t1 marshal t2
  | _ -> Format.printf "**Conversion** marshal found unsupported output type: %a\n" pp_type ty;
         failwith "marshal Error"

let unmarshal = stringToFuzz



