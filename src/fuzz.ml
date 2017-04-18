(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Unix

open Types

open Support.Options
open Support.Error

let infile     = ref ("" : string)

let programArgs = ref (None, None, None)
let setDBMaxSize i = match !programArgs with
  (_, n, s) -> programArgs := (Some i, n, s)
let setEpsilon n = match !programArgs with
  (i, _, s) -> programArgs := (i, Some n, s)
let setFN s = match !programArgs with
  (i, n, _) -> programArgs := (i, n, Some s)
let retainCMem = ref false

let argDefs = [
  "-dbsize",           Arg.Int  (fun i -> setDBMaxSize i), "Set Database size argument" ;
  "-e",                Arg.Float (fun n -> setEpsilon n), "Set epsilon argument" ;
  "-fn",               Arg.String (fun s -> setFN s), "Set filename argument" ;
  "-plim",             Arg.Int  (fun i -> Prim.pinterpLimit := i), "Set max number of steps for partial evaluation" ;
  "-rzfile",           Arg.String (fun s -> Prim.rzFileName := s), "Set the name for the redZoneTemp file" ;
  "-curfile",          Arg.String (fun s -> Codegen.curatorMemFileName := s), "Set the name for the curator memory file" ;
  
  "--no-noise",        Arg.Unit (fun () -> Math.noNoise := true), "Disable noise, making all laplace calls return 0" ;
  "--no-compiler",     Arg.Unit (fun () -> Prim.useCompiler := false), "Disable compilation, making all red zone calls interpreted" ;
  "--retainCMem",      Arg.Unit (fun () -> retainCMem := true), "Do not refresh the curator memory file before running" ;
  
  "-v",                Arg.Int  (fun l  -> debug_options := {!debug_options with level = l} ),       "Set printing level to n (1 Warning [2 Info], 3+ Debug)" ;
  "--verbose",         Arg.Int  (fun l  -> debug_options := {!debug_options with level = l} ),       "Set printing level to n (1 Warning [2 Info], 3+ Debug)" ;
  
  "--disable-types",   Arg.Unit (fun () -> comp_disable TypeChecker ), "Disable type checking and inference" ;
  "--disable-interp",  Arg.Unit (fun () -> comp_disable Interpreter ), "Disable interpreter" ;
  
  "--disable-unicode", Arg.Unit (fun () -> debug_options := {!debug_options with unicode = false} ), "Disable unicode printing" ;
  "--enable-annot",    Arg.Unit (fun () -> debug_options := {!debug_options with pr_ann  = true} ),  "Enable printing of type annotations" ;
  "--print-var-full",  Arg.Unit (fun () -> debug_options := {!debug_options with var_output = PrVarBoth} ), "Print names and indexes of variables" ;
  "--print-var-index", Arg.Unit (fun () -> debug_options := {!debug_options with var_output = PrVarIndex}), "Print just indexes of variables" ;
]

let dp = Support.FileInfo.dummyinfo
let main_error = error_msg General

let main_warning fi = message 1 General fi
let main_info    fi = message 2 General fi
let main_info2   fi = message 3 General fi
let main_debug   fi = message 4 General fi

let parseArgs () =
  let inFile = ref (None : string option) in
  Arg.parse argDefs
     (fun s ->
       match !inFile with
         Some(_) -> main_error dp "You must specify exactly one input file"
       | None -> inFile := Some(s))
     "Usage: fuzz [options] inputfile";
  match !inFile with
      None    -> main_error dp "No input file specified (use --help to display usage info)"; ""
    | Some(s) -> s

(* Parse the input *)
let parse file =
  let fd = Unix.openfile file [Unix.O_RDONLY] 0o640 in
  let lexbuf = Lexer.create file (Unix.in_channel_of_descr fd) in
  let program =
    try Parser.body Lexer.main lexbuf
    with Parsing.Parse_error -> error_msg Parser (Lexer.info lexbuf) "Parse error" in
  Parsing.clear_parser();
  Unix.close fd;
  program

(* Main must be db_source -> fuzzy string *)
let check_main_type ty =
  let (dbsizeArg, epsArg, fnArg) = !programArgs in
  let ty = match ty,dbsizeArg with
    | ty, None -> ty
    | TyLollipop (TyPrim PrimInt, _, ty), Some _ -> ty
    | _, _ -> TyPrim PrimUnit in
  let ty = match ty,epsArg with
    | ty, None -> ty
    | TyLollipop (TyPrim PrimNum, _, ty), Some _ -> ty
    | _, _ -> TyPrim PrimUnit in
  let ty = match ty,fnArg with
    | ty, None -> ty
    | TyLollipop (TyPrim PrimString, _, ty), Some _ -> ty
    | _, _ -> TyPrim PrimUnit in
  match ty with
    | TyPrim PrimString -> ()
    | _ -> main_error dp "The type of the program is wrong"

let type_check program =
  main_info  dp "Beginning type checking ...";
  let ty = Tycheck.get_type false program  in

  main_info  dp "Type of the program: @[%a@]" Print.pp_type ty;
  
  if comp_enabled Interpreter then check_main_type ty else ()  


(* Must use this *)
(* let get_tty_size = () *)

(* === The main function === *)
let main () =

  (* Set the program start time *)
  Support.Error.programStartTime := Unix.gettimeofday ();

  (* Setup the pretty printing engine *)

  let fmt_margin =
    try
      snd (Util.get_terminal_size ())
    with _ ->
      main_warning dp "Failed to get terminal size value.";
      120
  in

  let set_pp fmt =
    Format.pp_set_ellipsis_text fmt "[...]";
    Format.pp_set_margin fmt (fmt_margin + 1); (* Don't ever ask *)
    Format.pp_set_max_indent fmt fmt_margin    in

  set_pp Format.std_formatter;
  set_pp Format.err_formatter;

  (* Read the command-line arguments *)
  infile  := parseArgs();

  let (program, _) = parse !infile             in
  main_info  dp "Program parsed.";

  (* Print the results of the parsing phase *)
  main_debug dp "Parsed program:@\n@[%a@]@." Print.pp_term program;

  if comp_enabled TypeChecker then
    type_check program;

  if comp_enabled Interpreter then
    (* Set up Randomness *)
    Random.self_init ();
    
    (* Set up the curator memory file *)
    if !Prim.useCompiler then
      (if !retainCMem then
        ignore (Sys.command ("touch "^(!Codegen.curatorMemFileName)))
       else
        ignore (Sys.command ("> "^(!Codegen.curatorMemFileName))));
      
    let di = Support.FileInfo.dummyinfo in
    let (dbsizeArg, epsArg, fnArg) = !programArgs in
    let program = match dbsizeArg with
      | None -> program
      | Some dbSize -> TmApp(di, program, TmPrim(di, PrimTInt dbSize)) in
    let program = match epsArg with
      | None -> program
      | Some eps -> TmApp(di, program, TmPrim(di, PrimTNum eps)) in
    let program = match fnArg with
      | None -> program
      | Some fn -> TmApp(di, program, TmPrim(di, PrimTString fn))
    in let outputStr = Interpreter.run_interp program in
    main_info dp "The result of the program: %s" outputStr;
  ()

(* === Call the main function and catch any exceptions === *)

let res =
  try main();
      0
  with Exit x -> x
let () = exit res

