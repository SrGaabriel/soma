import Soma.Syntax.Source

namespace Soma.Syntax

inductive TokenKind where
  -- Literals
  | number
  | string (value : String)
  | true_
  | false_

  -- Identifiers
  | lowerIdent
  | upperIdent
  | varSymbol    -- Operators like +, -, *, ==, etc.

  -- Keywords
  | kw_def
  | kw_let
  | kw_in
  | kw_case
  | kw_if
  | kw_then
  | kw_else
  | kw_data
  | kw_struct
  | kw_trait
  | kw_instance
  | kw_where
  | kw_with
  | kw_use       -- import
  | kw_export
  | kw_intrinsic
  | kw_forall
  | kw_bind
  | kw_compose

  -- Punctuation
  | leftParen    -- (
  | rightParen   -- )
  | leftBrace    -- {
  | rightBrace   -- }
  | leftBracket  -- [
  | rightBracket -- ]
  | leftAngle    -- <
  | rightAngle   -- >
  | comma        -- ,
  | colon        -- :
  | doubleColon  -- ::
  | equals       -- =
  | pipe         -- |
  | at           -- @
  | underscore   -- _
  | lambda       -- \ or λ
  | forallSymbol -- ∀
  | dollar       -- $
  | slash        -- /

  -- Arrows
  | arrow        -- ->
  | fatArrow     -- =>
  | leftArrow    -- <-

  -- Layout tokens (inserted by layout pass)
  | layoutStart
  | layoutSep
  | layoutEnd

  -- Special
  | eof
  | error
  deriving Repr, Inhabited

/-- Check if two TokenKinds are equal (ignoring string content for basic equality) -/
def TokenKind.beq : TokenKind → TokenKind → Bool
  | .number, .number => true
  | .string s1, .string s2 => s1 == s2
  | .true_, .true_ => true
  | .false_, .false_ => true
  | .lowerIdent, .lowerIdent => true
  | .upperIdent, .upperIdent => true
  | .varSymbol, .varSymbol => true
  | .kw_def, .kw_def => true
  | .kw_let, .kw_let => true
  | .kw_in, .kw_in => true
  | .kw_case, .kw_case => true
  | .kw_if, .kw_if => true
  | .kw_then, .kw_then => true
  | .kw_else, .kw_else => true
  | .kw_data, .kw_data => true
  | .kw_struct, .kw_struct => true
  | .kw_trait, .kw_trait => true
  | .kw_instance, .kw_instance => true
  | .kw_where, .kw_where => true
  | .kw_with, .kw_with => true
  | .kw_use, .kw_use => true
  | .kw_export, .kw_export => true
  | .kw_intrinsic, .kw_intrinsic => true
  | .kw_forall, .kw_forall => true
  | .kw_bind, .kw_bind => true
  | .kw_compose, .kw_compose => true
  | .leftParen, .leftParen => true
  | .rightParen, .rightParen => true
  | .leftBrace, .leftBrace => true
  | .rightBrace, .rightBrace => true
  | .leftBracket, .leftBracket => true
  | .rightBracket, .rightBracket => true
  | .leftAngle, .leftAngle => true
  | .rightAngle, .rightAngle => true
  | .comma, .comma => true
  | .colon, .colon => true
  | .doubleColon, .doubleColon => true
  | .equals, .equals => true
  | .pipe, .pipe => true
  | .at, .at => true
  | .underscore, .underscore => true
  | .lambda, .lambda => true
  | .forallSymbol, .forallSymbol => true
  | .dollar, .dollar => true
  | .slash, .slash => true
  | .arrow, .arrow => true
  | .fatArrow, .fatArrow => true
  | .leftArrow, .leftArrow => true
  | .layoutStart, .layoutStart => true
  | .layoutSep, .layoutSep => true
  | .layoutEnd, .layoutEnd => true
  | .eof, .eof => true
  | .error, .error => true
  | _, _ => false

instance : BEq TokenKind where
  beq := TokenKind.beq

/-- Human-readable description of a token kind -/
def TokenKind.describe : TokenKind → String
  | .number => "a number"
  | .string _ => "a string"
  | .true_ => "'true'"
  | .false_ => "'false'"
  | .lowerIdent => "an identifier"
  | .upperIdent => "a type name"
  | .varSymbol => "an operator"
  | .kw_def => "'def'"
  | .kw_let => "'let'"
  | .kw_in => "'in'"
  | .kw_case => "'case'"
  | .kw_if => "'if'"
  | .kw_then => "'then'"
  | .kw_else => "'else'"
  | .kw_data => "'data'"
  | .kw_struct => "'struct'"
  | .kw_trait => "'trait'"
  | .kw_instance => "'instance'"
  | .kw_where => "'where'"
  | .kw_with => "'with'"
  | .kw_use => "'use'"
  | .kw_export => "'export'"
  | .kw_intrinsic => "'intrinsic'"
  | .kw_forall => "'forall'"
  | .kw_bind => "'bind'"
  | .kw_compose => "'compose'"
  | .leftParen => "'('"
  | .rightParen => "')'"
  | .leftBrace => "'{'"
  | .rightBrace => "'}'"
  | .leftBracket => "'['"
  | .rightBracket => "']'"
  | .leftAngle => "'<'"
  | .rightAngle => "'>'"
  | .comma => "','"
  | .colon => "':'"
  | .doubleColon => "'::'"
  | .equals => "'='"
  | .pipe => "'|'"
  | .at => "'@'"
  | .underscore => "'_'"
  | .lambda => "'\\'"
  | .forallSymbol => "'∀'"
  | .dollar => "'$'"
  | .slash => "'/'"
  | .arrow => "'->'"
  | .fatArrow => "'=>'"
  | .leftArrow => "'<-'"
  | .layoutStart => "layout start"
  | .layoutSep => "layout separator"
  | .layoutEnd => "layout end"
  | .eof => "end of file"
  | .error => "error"

instance : ToString TokenKind where
  toString := TokenKind.describe

/-- User-friendly description for error messages (avoids technical layout terms) -/
def TokenKind.userFriendly : TokenKind → String
  | .layoutStart => "start of indented block"
  | .layoutSep => "end of line"
  | .layoutEnd => "end of indented block"
  | .eof => "end of file"
  | other => other.describe

/-- A token with its span and text -/
structure Token where
  kind : TokenKind
  span : Span
  text : String
  deriving Repr, Inhabited

instance : ToString Token where
  toString tok := s!"Token({tok.kind}, \"{tok.text}\", {tok.span})"

instance : BEq Token where
  beq a b := a.kind == b.kind && a.text == b.text

/-- Get the byte length of a token -/
def Token.length (tok : Token) : Nat :=
  tok.span.length

/-- Check if a token is a layout token -/
def Token.isLayout (tok : Token) : Bool :=
  match tok.kind with
  | .layoutStart | .layoutSep | .layoutEnd => true
  | _ => false

/-- Check if a token is a keyword -/
def Token.isKeyword (tok : Token) : Bool :=
  match tok.kind with
  | .kw_def | .kw_let | .kw_in | .kw_case | .kw_if | .kw_then | .kw_else
  | .kw_data | .kw_struct | .kw_trait | .kw_instance | .kw_where | .kw_with
  | .kw_use | .kw_export | .kw_intrinsic | .kw_forall | .kw_bind | .kw_compose
  | .true_ | .false_ => true
  | _ => false

/-- Lookup table for keywords -/
def keywordMap : List (String × TokenKind) :=
  [ ("def", .kw_def)
  , ("let", .kw_let)
  , ("in", .kw_in)
  , ("case", .kw_case)
  , ("if", .kw_if)
  , ("then", .kw_then)
  , ("else", .kw_else)
  , ("data", .kw_data)
  , ("struct", .kw_struct)
  , ("trait", .kw_trait)
  , ("instance", .kw_instance)
  , ("where", .kw_where)
  , ("with", .kw_with)
  , ("use", .kw_use)
  , ("export", .kw_export)
  , ("intrinsic", .kw_intrinsic)
  , ("forall", .kw_forall)
  , ("bind", .kw_bind)
  , ("compose", .kw_compose)
  , ("true", .true_)
  , ("false", .false_)
  ]

/-- Look up a keyword by name -/
def lookupKeyword (name : String) : Option TokenKind :=
  keywordMap.lookup name

end Soma.Syntax
