{

open System
open FSharp.Text.Lexing

open FSharp.Common.Parsing
open FSharp.Common.Parsing.LexYacc
open TinyML.Ast
open TinyML.Parser

let trim c lexbuf = let s = lexeme lexbuf in s.TrimStart [|c|]

}

let whitespace = [' ' '\t' ]
let newline = ('\n' | "\r\n")
let digit = ['0'-'9'] 
let nat = digit+
let ureal = digit* '.' digit+ | digit+ '.' digit*
let sreal = ['-']? ureal
let real = sreal | sreal 'e' int | int 'e' int | sreal 'f'
let int = ['-']? nat
let long = int 'l'
let quoted = "\"" [^'"']* "\""

let idbody = ['a'-'z' 'A'-'Z' '0'-'9' '_']*['\'']*	
let Uid = ['A'-'Z'] idbody
let Lid = ['a'-'z' '_'] idbody
let id = Uid | Lid

rule comment level = parse
	| "(*"          	{ comment (level + 1) lexbuf }
	| "*)"	            { if level = 0 then tokenize lexbuf else comment (level - 1) lexbuf }
    | "*)"				{ tokenize lexbuf }
	| newline			{ newline lexbuf; comment level lexbuf } 
	| _					{ comment level lexbuf }

and linecomment = parse
    | newline           { newline lexbuf; tokenize lexbuf }
    | _                 { linecomment lexbuf }

and tokenize = parse
	| eof				{ EOF }
	| whitespace		{ tokenize lexbuf }
	| newline			{ newline lexbuf; tokenize lexbuf }

	| "//"				{ linecomment lexbuf }
	| "(*"          	{ comment 0 lexbuf }
     
	| '+'			{ PLUS }
	| '-'			{ MINUS }
	| '*'			{ STAR }
	| '/'			{ SLASH }
	| '%'			{ PERCENT }
	| '='			{ EQ }
	| "<>"			{ NEQ }
	| '<'			{ LT }
	| '>'			{ GT }
	| "<="			{ LEQ }
	| ">="			{ GEQ }
	| "or"			{ OR }
	| "and"			{ AND }
	| "not"			{ NOT }
    | '+.'			{ PLUSFLOAT }
	| '-.'			{ MINUSFLOAT }
	| '*.'			{ STARFLOAT }
	| '/.'			{ SLASHFLOAT }
	| '%.'			{ PERCENTFLOAT }
	| '=.'			{ EQFLOAT }
	| "<>."			{ NEQFLOAT }
	| '<.'			{ LTFLOAT }
	| '>.'			{ GTFLOAT }
	| "<=."			{ LEQFLOAT }
	| ">=."			{ GEQFLOAT }

	// keywords
	| "if"			{ IF }
	| "then"        { THEN }
	| "else"		{ ELSE }
	| "true"		{ TRUE }
	| "false"		{ FALSE }
	| "fun"			{ FUN }
	| "->"			{ ARROW }
	| "let"			{ LET }
	| "rec"			{ REC }
	| "in"			{ IN }
    
	// brakets
	| '('			{ BRA }
	| ')'			{ KET }

	// punctuation
	| ':'			{ COLON }
	| ";;"			{ SEMICOLON2 }
	| ','			{ COMMA }

	// literals
	| "\"" [^'"']* "\""		{ let s = lexeme lexbuf in STRING (s.Trim [|'\"'|]) }
	| '\'' [^'\''] '\''		{ let s = lexeme lexbuf in CHAR ((s.Trim [|'\''|]).Chars 0) }
    | real                  { FLOAT (parse_float (lexeme lexbuf)) }
	| int   	    		{ INT (Int32.Parse (lexeme lexbuf)) }

	// identifiers
	| id 		            { ID (lexeme lexbuf) }
