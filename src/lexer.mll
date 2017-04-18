(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
{
open Support.FileInfo
open Support.Error
open Sys

let lex_error fi s = error_msg Support.Options.Lexer fi "%s" s

let reservedWords = [
  (* Symbols *)
  ("$", fun i -> Parser.DOLLAR i);
  (";", fun i -> Parser.SEMI i);
  ("^", fun i -> Parser.HAT i);
  ("?", fun i -> Parser.QUESTION i);
  ("{", fun i -> Parser.LBRACE i);
  ("}", fun i -> Parser.RBRACE i);
  (":", fun i -> Parser.COLON i);
  (",", fun i -> Parser.COMMA i);
  ("=", fun i -> Parser.EQUAL i);
  ("==", fun i -> Parser.BEQUAL i);
  ("->", fun i -> Parser.ARROW i);
  ("=>", fun i -> Parser.DBLARROW i);
  ("+", fun i -> Parser.ADD i);
  ("-", fun i -> Parser.SUB i);
  ("*", fun i -> Parser.MUL i);
  ("/", fun i -> Parser.DIV i);
  ("(", fun i -> Parser.LPAREN i);
  (")", fun i -> Parser.RPAREN i);
  ("<", fun i -> Parser.LT i);
  (">", fun i -> Parser.GT i);
  ("[", fun i -> Parser.LBRACK i);
  ("]", fun i -> Parser.RBRACK i);
  ("|", fun i -> Parser.PIPE i);
  ("&", fun i -> Parser.AMP i);
  ("||", fun i -> Parser.OR i);
  ("&&", fun i -> Parser.AND i);
  ("!", fun i -> Parser.BANG i);
  (".", fun i -> Parser.DOT i);

  (* Keywords *)
  ("true", fun i -> Parser.TRUE i);
  ("false", fun i -> Parser.FALSE i);
  ("inf", fun i -> Parser.INF i);
  ("fuzzy", fun i -> Parser.FUZZY i);
  ("fun", fun i -> Parser.FUN i);
  ("case", fun i -> Parser.UNIONCASE i);
  ("inl", fun i -> Parser.INL i);
  ("inr", fun i -> Parser.INR i);
  ("of", fun i -> Parser.OF i);
  ("fold", fun i -> Parser.FOLD i);
  ("unfold", fun i -> Parser.UNFOLD i);
  ("mu", fun i -> Parser.MU i);
  ("let", fun i -> Parser.LET i);
  ("typedef", fun i -> Parser.TYPEDEF i);
  ("sample", fun i -> Parser.SAMPLE i);
  ("function", fun i -> Parser.FUNCTION i);
  ("primitive", fun i -> Parser.PRIMITIVE i);
  ("clipped", fun i -> Parser.CLIPPED i);
  ("set", fun i -> Parser.SET i);
  ("bag", fun i -> Parser.BAG i);
  ("vector", fun i -> Parser.VECTOR i);
  ("token", fun i -> Parser.TOKEN i);
  ("if", fun i -> Parser.IF i);
  ("then", fun i -> Parser.THEN i);
  ("else", fun i -> Parser.ELSE i);
  ("bool", fun i -> Parser.BOOL i);
  ("num", fun i -> Parser.NUM i);
  ("string", fun i -> Parser.STRING i);
  ("type", fun i -> Parser.TYPE i);
  ("forall", fun i -> Parser.FORALL i);
  ("int", fun i -> Parser.INT i);
]

(* Support functions *)

type buildfun = info -> Parser.token
let (symbolTable : (string,buildfun) Hashtbl.t) = Hashtbl.create 1024
let _ =
  List.iter (fun (str,f) -> Hashtbl.add symbolTable str f) reservedWords

let createID i str =
  try (Hashtbl.find symbolTable str) i
  with _ -> Parser.ID {i=i;v=str}

let lineno   = ref 1
and depth    = ref 0
and start    = ref 0

and filename = ref ""
and startLex = ref dummyinfo

let create inFile stream =
  if not (Filename.is_implicit inFile) then filename := inFile
  else filename := Filename.concat (Sys.getcwd()) inFile;
  lineno := 1; start := 0; Lexing.from_channel stream

let newline lexbuf = incr lineno; start := (Lexing.lexeme_start lexbuf)

let info lexbuf =
  createInfo (!filename) (!lineno) (Lexing.lexeme_start lexbuf - !start)

let text = Lexing.lexeme

let stringBuffer = ref (Bytes.create 2048)
let stringEnd = ref 0

let resetStr () = stringEnd := 0

let addStr ch =
  let x = !stringEnd in
  let buffer = !stringBuffer
in
  if x = Bytes.length buffer then
    begin
      let newBuffer = Bytes.create (x*2) in
      Bytes.blit buffer 0 newBuffer 0 x;
      Bytes.set newBuffer x ch;
      stringBuffer := newBuffer;
      stringEnd := x+1
    end
  else
    begin
      Bytes.set buffer x ch;
      stringEnd := x+1
    end

let getStr () = Bytes.sub (!stringBuffer) 0 (!stringEnd)

let extractLineno yytext offset =
  int_of_string (String.sub yytext offset (String.length yytext - offset))
}


(* The main body of the lexical analyzer *)

rule main = parse
  [' ' '\009' '\012']+     { main lexbuf }

| [' ' '\009' '\012']*("\r")?"\n" { newline lexbuf; main lexbuf }

| "*/" { lex_error (info lexbuf) "Unmatched end of comment" }

| "/*" { depth := 1; startLex := info lexbuf; comment lexbuf; main lexbuf }

| "//" [^ '\n']* { main lexbuf }

| "# " ['0'-'9']+
    { lineno := extractLineno (text lexbuf) 2 - 1; getFile lexbuf }

| "# line " ['0'-'9']+
    { lineno := extractLineno (text lexbuf) 7 - 1; getFile lexbuf }

| ['0'-'9']+
    { Parser.INTV{i=info lexbuf; v=int_of_string (text lexbuf)} }

| ['0'-'9']+ '.' ['0'-'9']+
    { Parser.FLOATV{i=info lexbuf; v=float_of_string (text lexbuf)} }

| "-o" { Parser.LOLLIPOP(info lexbuf) }

| ['A'-'Z' 'a'-'z' '_']
  ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*
    { createID (info lexbuf) (text lexbuf) }

| ":=" | "<:" | "<-" | "->" | "=>" | "==>"
| "{|" | "|}" | "<|" | "|>" | "[|" | "|]" | "=="
    { createID (info lexbuf) (text lexbuf) }

| ['~' '%' '\\' '+' '-' '&' '|' ':' '@' '`' '$']+
    { createID (info lexbuf) (text lexbuf) }

| ['*' '#' '/' '!' '?' '^' '(' ')' '{' '}' '[' ']' '<' '>' '.' ';' '_' ','
   '=' '\'']
    { createID (info lexbuf) (text lexbuf) }

| "\"" { resetStr(); startLex := info lexbuf; string lexbuf }

| "import \"" ([^'"' '\n']* as filename) '"'
{
    let fn = begin match file_exists filename, file_exists ("lib/"^filename) with
              | true, _ -> filename
              | false, true -> "lib/"^filename
              | false, false -> failwith ("Failed to import file: "^filename^".  Checked in . and lib/")
             end in
    let c = open_in fn in
    let imported_lb = Lexing.from_channel c in
    let (p, context) = Parser.body main imported_lb in
    Parser.IMPORT({i = info lexbuf; v = (p, context)})
}

| eof { Parser.EOF(info lexbuf) }

| _  { lex_error (info lexbuf) "Illegal character" }

and comment = parse
  "/*"
    { depth := succ !depth; comment lexbuf }
| "*/"
    { depth := pred !depth; if !depth > 0 then comment lexbuf }
| eof
    { lex_error (!startLex) "Comment not terminated" }
| [^ '\n']
    { comment lexbuf }
| "\n"
    { newline lexbuf; comment lexbuf }

and getFile = parse
  " "* "\"" { getName lexbuf }

and getName = parse
  [^ '"' '\n']+ { filename := (text lexbuf); finishName lexbuf }

and finishName = parse
  '"' [^ '\n']* { main lexbuf }

and string = parse
  '"'  { Parser.STRINGV {i = !startLex; v=getStr()} }
| '\\' { addStr(escaped lexbuf); string lexbuf }
| '\n' { addStr '\n'; newline lexbuf; string lexbuf }
| eof  { lex_error (!startLex) "String not terminated" }
| _    { addStr (Lexing.lexeme_char lexbuf 0); string lexbuf }

and escaped = parse
  'n'	 { '\n' }
| 't'	 { '\t' }
| '\\'	 { '\\' }
| '"'    { '\034'  }
| '\''	 { '\'' }
| ['0'-'9']['0'-'9']['0'-'9']
    {
      let x = int_of_string(text lexbuf) in
      if x > 255 then
	lex_error (info lexbuf) "Illegal character constant"
      else
	Char.chr x
    }
| [^ '"' '\\' 't' 'n' '\'']
    { lex_error (info lexbuf) "Illegal character constant" }

(*  *)
