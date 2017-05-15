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

let programArgs = ref []
let retainCMem = ref false

let argDefs = [
  "-args",             Arg.Rest (fun s -> programArgs := !programArgs @ [s]), "Provide program arguments (must come last)" ;

  "-plim",             Arg.Set_int Prim.pinterpLimit, "Set max number of steps for partial evaluation" ;
  "-rzfile",           Arg.Set_string Prim.rzFileName, "Set the name for the dataZoneTemp file" ;
  "-curfile",          Arg.Set_string Codegen.curatorMemFileName, "Set the name for the curator memory file" ;

  "--no-noise",        Arg.Set Math.noNoise, "Disable noise, making all laplace calls return 0, etc." ;
  "--no-compiler",     Arg.Clear Prim.useCompiler, "Disable compilation, making all data zone calls interpreted" ;
  "--retainCMem",      Arg.Set retainCMem, "Do not refresh the curator memory file before running" ;
  
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
    try Parser.body Lexer.main2 lexbuf
    with Parsing.Parse_error -> error_msg Parser (Lexer.maininfo lexbuf) "Parse error" in
  Parsing.clear_parser();
  Unix.close fd;
  program

(* Main must be db_source -> fuzzy string *)
let check_main_type ty =
  match ty with
    | TyPrim PrimString -> ()
    | TyLollipop (TyPrim1 (Prim1Vector, TyPrim PrimString), _, TyPrim PrimString) -> ()
    | _ -> main_error dp "A runnable program must have the type 'string' or 'string vector -> string'."

let type_check program =
  main_info  dp "Beginning type checking ...";
  let ty = Tycheck.get_type false program  in

  main_info  dp "Type of the program: @[%a@]" Print.pp_type ty;
  
  if comp_enabled Interpreter then check_main_type ty else ();
  ty



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

  let programWithArgs = TmApp(dp, program, TmVector(dp, TyPrim1 (Prim1Vector, TyPrim PrimString), 
            List.map (fun s -> TmPrim(dp, PrimTString s)) !programArgs)) in
  
  let program =
    if comp_enabled TypeChecker then
      match type_check program with
      | TyPrim PrimString -> program
      | TyLollipop (TyPrim1 (Prim1Vector, TyPrim PrimString), _, TyPrim PrimString) -> programWithArgs
      | _ -> main_error dp "The type of the program is impossibly wrong"; program
    else
      (if !programArgs == [] then program else programWithArgs)

  in if comp_enabled Interpreter then
    (* Set up Randomness *)
    Random.self_init ();

    (* Set up the curator memory file *)
    if !Prim.useCompiler then
      (if !retainCMem then
        ignore (Sys.command ("touch "^(!Codegen.curatorMemFileName)))
       else
        ignore (Sys.command ("> "^(!Codegen.curatorMemFileName))));

    let outputStr = Interpreter.run_interp program in
    main_info dp "The result of the program: %s" outputStr;
  ()

(* === Call the main function and catch any exceptions === *)

let res =
  try main();
      0
  with Exit x -> x
let () = exit res
