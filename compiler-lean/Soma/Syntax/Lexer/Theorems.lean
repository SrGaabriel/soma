import Soma.Syntax.Lexer

namespace Soma.Syntax

/-- Count LayoutStart tokens -/
def countLayoutStart (tokens : Array Token) : Nat :=
  tokens.foldl (fun acc t => if t.kind == .layoutStart then acc + 1 else acc) 0

/-- Count LayoutEnd tokens -/
def countLayoutEnd (tokens : Array Token) : Nat :=
  tokens.foldl (fun acc t => if t.kind == .layoutEnd then acc + 1 else acc) 0

/-- Check that layout tokens are balanced -/
def checkLayoutBalanced (tokens : Array Token) : Bool :=
  countLayoutStart tokens == countLayoutEnd tokens

end Soma.Syntax

-- Basic cases
open Soma.Syntax in #guard checkLayoutBalanced (lex "").1
open Soma.Syntax in #guard checkLayoutBalanced (lex "x").1
open Soma.Syntax in #guard checkLayoutBalanced (lex "1 + 2").1

-- Single block
open Soma.Syntax in #guard checkLayoutBalanced (lex "def foo\n  x").1

-- Multiple items in block
open Soma.Syntax in #guard checkLayoutBalanced (lex "def foo\n  x\n  y\n  z").1

-- Nested blocks
open Soma.Syntax in #guard checkLayoutBalanced (lex "def foo\n  case x\n    | a => 1\n    | b => 2").1

-- Deep nesting
open Soma.Syntax in #guard checkLayoutBalanced (lex "def f\n  case x\n    | a =>\n      case y\n        | b => 1").1

-- Dedent back to outer level
open Soma.Syntax in #guard checkLayoutBalanced (lex "def f\n  x\ndef g\n  y").1

-- Complex real-world pattern
open Soma.Syntax in #guard checkLayoutBalanced (lex "def factorial n =\n  case n\n    | 0 => 1\n    | _ => n * factorial (n - 1)").1
