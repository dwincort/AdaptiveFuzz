(* file name: codegen.ml
   created by: Daniel Winograd-Cort
   Last modified: 5/6/2017
   
   Description:
   This file generates ml code from Fuzz code (compilation).
*)

open Format

open Types
open Print

let curatorMemFileName = ref "curatormem.cmem"
(* Use the below line for profiling *)
(* let genversion = ref ".p.native" *)
let genversion = ref ".native"


let fileLines (maxLines : int) chan = 
  let lines = ref [] in
  try
    for i=1 to maxLines; do
      lines := input_line chan :: !lines
    done;
    close_in chan;
    List.rev !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines

let pwrap (s : string) : string = "("^s^")"

let gen_primitive (t : term_prim) : string =
  match t with
    PrimTUnit        -> "()"
  | PrimTNum(r)      -> pwrap (string_of_float r)
  | PrimTClipped(r)  -> pwrap (string_of_float r)
  | PrimTInt(n)      -> pwrap (string_of_int   n ^ ".0")
  | PrimTBool(b)     -> string_of_bool  b
  | PrimTString(s)   -> "\""^String.escaped s^"\""
  | PrimTToken(n,ty) -> pwrap (string_of_int   n)


let rec gen_term ppf t =
  match t with
  | TmVar (_, v)  -> fprintf ppf "__%s" v.v_name

  | TmPrim (_, prim) -> fprintf ppf "%s" (gen_primitive prim)

  | TmPrimFun (_i, s, _, _, lst) ->
      fprintf ppf "(%s %a)" s (pp_list_generic gen_term "" "" " ") (List.map (fun (t,_,_) -> t) lst)
  
  | TmRecFun (_i, bi, _ty, tm, _) ->
      fprintf ppf "(let rec __%s = %a in __%s)" bi.b_name gen_term tm bi.b_name
  
  | TmPVal   (_i, tm) -> fprintf ppf "(fun () -> %a)" gen_term tm
  | TmUnPVal (_i, tm) -> fprintf ppf "(%a ())" gen_term tm
  
  | TmBag    (_i, _ty, tmlist) -> fprintf ppf "%a" (pp_list_generic gen_term "[" "]" ";") tmlist
  | TmVector (_i, _ty, tmlist) -> fprintf ppf "(Array.of_list %a)" (pp_list_generic gen_term "[" "]" ";") tmlist
  | TmPair (_i, e1, e2) -> fprintf ppf "(%a,%a)" gen_term e1 gen_term e2
  | TmTensDest (_,  b_x, b_y, tm_e1, tm_e2) ->
      fprintf ppf "(match %a with (__%s,__%s) ->@\n @[%a@])"
        gen_term tm_e1 b_x.b_name b_y.b_name gen_term tm_e2
  | TmAmpersand (_i, e1, e2) -> fprintf ppf "(%a,%a)" gen_term e1 gen_term e2

  | TmLeft  (_i, tm, _ty) -> fprintf ppf "(Left  %a)" gen_term tm
  | TmRight (_i, tm, _ty) -> fprintf ppf "(Right %a)" gen_term tm
  | TmUnionCase (_, tm_e, bi_l, tm_l, bi_r, tm_r) ->
      fprintf ppf "(match %a with @[<v>| Left __%s -> %a @,| Right __%s -> %a)@]"
        gen_term tm_e bi_l.b_name gen_term tm_l bi_r.b_name gen_term tm_r

  (* Regular Abstraction and Applicacion *)
  | TmApp (_, f, a)  -> fprintf ppf "(@[%a@\n%a@])" gen_term f gen_term a
  | TmAbs (_, b, _sty, _t2, body) ->
      fprintf ppf "(fun __%s ->@\n @[%a@])" b.b_name gen_term body

  (* Recursive data types *)
  | TmFold(_i, _, tm) -> fprintf ppf "@[(Obj.magic %a)@]" gen_term tm
  | TmUnfold (_i, tm) -> fprintf ppf "@[(Obj.magic %a)@]" gen_term tm

  (* Bindings *)
  | TmLet (_, bi, _s, e1, e2) -> fprintf ppf "(let __%s = %a in@\n %a)" bi.b_name gen_term e1 gen_term e2
  | TmStmt (_, tm1, tm2) -> fprintf ppf "(%a;@\n %a)" gen_term tm1 gen_term tm2
  | TmSample (_, bi,  e1, e2) -> fprintf ppf "(fun () -> (let __%s = %a () in@\n %a) ())" bi.b_name gen_term e1 gen_term e2

  (* Type Abstraction and Applicacion *)
  | TmTyAbs (_i,_bi,tm) -> gen_term ppf tm
  | TmTyApp (_i,tm,_ty) -> gen_term ppf tm

  (* Type definitions *)
  | TmTypedef (_i,_tn,_ty,tm) -> gen_term ppf tm
  
  (* Convenience *)
  | TmIfThenElse (_, tmb, tmt, tme) -> fprintf ppf "(if %a then %a else %a)" gen_term tmb gen_term tmt gen_term tme



let codeFormat : ('a, Format.formatter, unit) format =
"open Primml

let body _ = %a

let main () =
  Math.noNoise := %B;
  curatormem := readCmemFromFile 1000 \"%s\";
  Random.self_init ();
  (try
    Printf.printf \"%%s\\n\" (%a (body ()))
  with Sys_error s -> Printf.printf \"Error: %%s\\n\" s);
  writeCmemToFile \"%s\" !curatormem;
  ()

let res = main ();
"


let progToFile (fn : string) (program : term) (ty : ty) : unit =
  let oc = open_out fn in
  let ocf = formatter_of_out_channel oc in
  fprintf ocf codeFormat gen_term program (!Math.noNoise) (!curatorMemFileName) Conversion.marshal ty (!curatorMemFileName);
  close_out oc;
  ()


let runCompiled (fn : string) (i : Support.FileInfo.info) (program : term) (ty : ty) : (term, string) result = 
  let file = "src/"^fn^".ml" in
  let native = "src/"^fn^(!genversion) in
  let exec = "./"^fn^(!genversion) in
  progToFile file program ty;
  let buildResults,buildOutput = Unix.pipe () in
  ignore (Unix.waitpid [] (Unix.create_process
      "ocamlbuild" [|"ocamlbuild" ; "-use-ocamlfind" ; "-pkg" ; "unix,str" ; native |]
      Unix.stdin buildOutput buildOutput));
  Unix.close buildOutput;
  let build_ic = Unix.in_channel_of_descr buildResults in
  let s' = String.concat "\n\t" (fileLines 100 build_ic) in
  close_in build_ic;
  match (Util.contains s' "Error:") with
  | Some n -> Error s'
  | None -> 
    let progResults,progOutput = Unix.pipe () in
    ignore (Unix.waitpid [] (Unix.create_process
        exec [| exec |]
        Unix.stdin progOutput progOutput));
    Unix.close progOutput;
    let ic = Unix.in_channel_of_descr progResults in
    let s = String.concat "" (fileLines 100 ic) in
    close_in ic;
    (*Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo
      "Result from compiled data zone: %s" s; *)
    match (Util.contains s "Error:") with
    | Some n -> Error s
    | None -> begin match Conversion.unmarshal i ty s with
      | Some tm -> Ok tm
      | None -> Error ("Could not unmarshal: "^s)
      end

