(***********************************************************)
(*       Lab3: LISP Parser                                 *)
(*                                                         *)
(*       Carter King   
         March 11th, 2021                                  *)
(*       COMP 360: Programming Languages                   *)
(*                                                         *)
(***********************************************************)

exception LexerError;
exception ParseOK;
exception ParseError of string;

(***********************************************************)
(* type declarations                                       *)
(***********************************************************)

datatype sign =
    Plus
  | Minus
;

datatype atom =
  T
| NIL
| Int of int
| Ident of string
;

datatype token =
  Lparen
| Rparen
| Dot
| Sign of sign
| Atom of atom
;

datatype sexp =
    AtomExp of atom
  | Sexp of sexp * sexp;


(***********************************************************)
(* printing functions                                      *)
(***********************************************************)

(* function: print_tokens - prints out a token stream  *)
fun print_tokens [] = print("\n")
  | print_tokens (Lparen :: t) = (print("Lparen "); print_tokens(t))
  | print_tokens (Rparen :: t) = (print("Rparen "); print_tokens(t))
  | print_tokens (Dot :: t) = (print("Dot "); print_tokens(t))
  | print_tokens (Sign(Plus) :: t) = (print("Plus "); print_tokens(t))
  | print_tokens (Sign(Minus) :: t) = (print("Minus "); print_tokens(t))
  | print_tokens (Atom(a) :: t) =
  (case a of
   T => (print("Atom(T) "); print_tokens(t))
   | NIL => (print("Atom(NIL) "); print_tokens(t))
   | Int i => (print("Atom(Int(" ^ Int.toString(i) ^ ")) "); print_tokens(t))
   | Ident s => (print("Atom(Ident(" ^ s ^ ")) "); print_tokens(t)))
  ;

(* function: string_of_op -  converts an operator token to a string *)
fun string_of_op Plus = "+"
 |  string_of_op Minus = "-";


(* function: is_list - predicate function returning true if s-expression is a list *)
fun is_list (Sexp(h, AtomExp(NIL))) = true
 |  is_list (Sexp(h, t)) = is_list t
 |  is_list _ = false;


(* function: string_of_atom - converts a primitive atom to a string *)
fun string_of_atom T = "T"
  | string_of_atom NIL = "NIL"
  | string_of_atom (Int(x)) = Int.toString(x)
  | string_of_atom (Ident(x)) = x
;

(* function: string_of_token - converts a lexer token to a string *)
fun string_of_token Lparen = "("
  | string_of_token Rparen = ")"
  | string_of_token Dot    = "."
  | string_of_token (Sign(x)) = string_of_op x
  | string_of_token (Atom(x)) = string_of_atom x
;

(* function: print_list - prints an s-expression in list format. Checks if is_list in case it's a part of the 
   recursive call and may be a list of dotted pairs. Prints empty string if AE(NIL) is received *)
fun print_list (Sexp(a, AtomExp(NIL))) = print_list a (* last element of the list, no need to call on AtomExp(NIL *)
  | print_list (Sexp(a, b)) = if (is_list (Sexp(a, b))) then (print_list a; print(" "); print_list b) 
                              else print_sexp (Sexp(a, b))
  | print_list (AtomExp(NIL)) = print("")
  | print_list (AtomExp(d)) = print(string_of_atom (d))



(* function: print_sexp - prints an s-expression in either dotted or list format. Checks if list each time called to ensure 
   not a dotted pair with one side a list. Handles the parentheses printing for itself and print_list. Handles
   AtomExp(NIL) as well, printing empty string. *)
and
  print_sexp (Sexp(a, b)) = if is_list (Sexp(a, b)) then (print("("); print_list (Sexp(a, b)); print(")")) 
                          else (print("("); print_sexp a; print (" . "); print_sexp b; print(")"))
| print_sexp (AtomExp(NIL)) =  (print("("); print(""); print(")"))
| print_sexp (AtomExp(d)) = print(string_of_atom (d)) 
;                                                     


(***********************************************************)
(* lexer implementation                                    *)
(***********************************************************)

fun spaces (#" " :: t)  = spaces t
  | spaces (#"\t" :: t) = spaces t
  | spaces (#"\n" :: t) = spaces t
  | spaces l = l
;

fun char_to_int(c) =
   let
      val copt = Int.fromString(Char.toString(c))
   in
      (case copt of
        SOME(vv) => vv
      | NONE => raise LexerError)
   end
;


fun lexid (s, []) = (s, [])
  | lexid (s, h::t) =
      if Char.isAlphaNum(h) then
        lexid(s ^ Char.toString(h), t)
      else
        (s, h::t)
;


fun lexint (v, []) = (v, [])
  | lexint (v, h::t) =
  if Char.isDigit(h) then
     lexint((10*v)+char_to_int(h), t)
  else
     (v, h::t)
;


fun  lexer( #"(" :: t) =   Lparen :: lexer(t)
  |  lexer( #")" :: t) =  Rparen :: lexer(t)
  |  lexer( #"." :: t) =  Dot :: lexer(t)
  |  lexer( #"-" :: t) =  Sign(Minus) :: lexer(t)
  |  lexer( #"+" :: t) =  Sign(Plus) :: lexer(t)
  |  lexer( h::t ) =
        if Char.isAlpha(h) then
          let
             val (idstr,tt) = lexid(Char.toString(h), t)
          in
            (case (String.map Char.toLower idstr) of
                  "nil" => Atom(NIL) :: lexer (tt)
                | "t"   => Atom(T) :: lexer (tt)
                | _   => Atom(Ident(idstr)) :: lexer(tt))
          end
        else if Char.isDigit(h) then
          let
             val (intval, tt) = lexint(char_to_int(h), t)
          in
             Atom(Int(intval)) :: lexer(tt)
          end
        else if Char.isSpace(h) then
          lexer(spaces(t))
        else
          raise LexerError
   |   lexer [] = []
;


(***********************************************************)
(* parser implementation                                   *)
(***********************************************************)

(* function: check_sign - both validates and combines sign and integer token pairs *)
fun check_sign (Sign(Minus)::(Atom(Int(i)))::rest) = (AtomExp(Int(~i)),rest)
 |  check_sign (Sign(Plus)::(Atom(Int(i)))::rest) = (AtomExp(Int(i)),rest)
 |  check_sign _ = raise ParseError "+/- sign may only be used with integer literals";


(* function: parse_sexp - top-level parser: takes stream of tokens, returns sexp-tree *)
(* S ::= E *)
fun parse_sexp [] = raise ParseOK
 |  parse_sexp exp = parse_exp exp

(* E ::= atom | '(' X         
   returns a a 2-tuple containg and sexp * remaining tokens
   Doesn't create a Sexp tuple because just handles returning of AEs *)
and
    parse_exp (Sign(x) :: tks)  = check_sign (Sign(x) :: tks)
  | parse_exp (Atom(Int(i)) :: tks)  = (AtomExp(Int(i)), tks)
  | parse_exp (Atom(Ident(i)) :: tks) = (AtomExp(Ident(i)), tks)
  | parse_exp (Atom(T) :: tks) = (AtomExp(T), tks)
  | parse_exp (Atom(Nil) :: tks) = (AtomExp(NIL), tks)
  | parse_exp (Lparen :: tks) = parse_x tks
  | parse_exp (_ :: tks) = raise ParseError "parse_exp receiving neither atom nor Lparen"
  | parse_exp [] = raise ParseError "parse_exp receiving empty list"
(* X ::= E Y | ')'   
   Handles the empty list if it receives an immediate Rparen
   Otherwise, returns the 2-tuple of the S-expression created from calling 
   rule E and rule Y sequentially  * with the remaining tokens *)
and
    parse_x (Rparen :: tks) = (AtomExp(NIL), tks) (* empty list *)
  | parse_x (e :: tks) = 
      let
        val (exp, ls) = parse_exp (e :: tks)
        val (exp2, ls2) = parse_y ls
        val rest = parse_rparen ls2
      in
        (Sexp(exp, exp2),rest) 
      end
  | parse_x [] = raise ParseError "parse_x receiving empty list"

(* Y ::= '.' E ')' | R ')'    
   Handles the Dot matching and calls rule X otherwise*)
and
    parse_y (Dot :: tks) = parse_exp tks
  | parse_y (x :: tks) = parse_r (x::tks) 
  | parse_y [] = raise ParseError "parse_ receiving empty list"

(* R ::= E R | empty  
   Only called if parsing a list, so returns 2-tuple (AE(NIL), rest of tokens) if receives empty list signified
   by matching an Rparen. Otherwise it creates and returns a new S-expression containing the results of 
   rule E and rule R. *)
and
    parse_r (Rparen :: tks)  = (AtomExp(NIL), (Rparen :: tks))
  | parse_r (x :: tks) =
      let
        val (exp, ls) = parse_exp (x::tks)
        val (exp2, ls2) = parse_r ls
      in
        (Sexp(exp, exp2), ls2)
      end
  | parse_r [] = raise ParseError "parse_r receiving empty list"

(* convenience production for right parens 
   Solely matches the Rparen and returns the rest of the tokens remaining*)
and
    parse_rparen (Rparen :: tks) = tks
  | parse_rparen [] = raise ParseError "parse_rparen receiving empty list"
  | parse_rparen (_ :: tks) = raise ParseError "parse_rparen not receiving right paren"
;


(*****************************************)
(* helper routines                       *)
(*****************************************)

fun get_sexp [] = (AtomExp(NIL),[])
 |  get_sexp s = parse_sexp s
;

fun next_sexp [] = OS.Process.exit(OS.Process.success)
 | next_sexp s =
   let
      val (e,rest) = get_sexp s
   in
      (print_sexp e;
       print "\n";
       next_sexp rest
       handle ParseError msg => print ("Parse Error: " ^ msg ^ "\n")
            | ParseOK => OS.Process.exit(OS.Process.success))
   end

fun reader(copt: char option, is, l) =
  case copt of
    NONE    => (TextIO.closeIn is; l)
  | SOME(c) => reader (TextIO.input1 is, is, (l@[c]))
  ;


(*****************************************)
(* main                                  *)
(*****************************************)
val args = CommandLine.arguments();
val ins = TextIO.openIn(hd(args));

let
   val (sexp,ts) = get_sexp(lexer(reader(TextIO.input1 ins, ins, [])));
in
   (print_sexp(sexp);
    print "\n";
    next_sexp ts)
end;


