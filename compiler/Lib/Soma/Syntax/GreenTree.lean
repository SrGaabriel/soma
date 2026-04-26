import Soma.Syntax.SyntaxKind
import Std.Data.HashMap

namespace Soma.Syntax

/-- Token kinds -/
inductive TokenKind where
  | number
  | string (value : String)
  | true_
  | false_
  | lowerIdent
  | upperIdent
  | varSymbol
  | kw_def | kw_theorem | kw_let | kw_in | kw_case | kw_if | kw_then | kw_else
  | kw_inductive | kw_struct | kw_trait | kw_instance | kw_where
  | kw_use | kw_pub | kw_forall | kw_bind | kw_compose
  | kw_abbrev
  | leftParen | rightParen | leftBrace | rightBrace | leftBracket | rightBracket
  | leftAngle | rightAngle | comma | colon | doubleColon | colonEquals | equals | pipe | dot
  | at | underscore | lambda | forallSymbol | dollar | slash | hash
  | arrow | fatArrow | leftArrow
  | times         -- '×' for dependent pair types
  | omega         -- 'ω' for unrestricted quantity
  | layoutStart | layoutSep | layoutEnd
  | whitespace | comment  -- Trivia tokens for accurate span tracking
  | eof | error
  deriving BEq, Hashable, Repr, Inhabited

namespace TokenKind

def describe : TokenKind → String
  | .number => "number"
  | .string _ => "string"
  | .true_ => "'true'"
  | .false_ => "'false'"
  | .lowerIdent => "identifier"
  | .upperIdent => "type name"
  | .varSymbol => "operator"
  | .kw_def => "'def'"
  | .kw_theorem => "'theorem'"
  | .kw_let => "'let'"
  | .kw_in => "'in'"
  | .kw_case => "'case'"
  | .kw_if => "'if'"
  | .kw_then => "'then'"
  | .kw_else => "'else'"
  | .kw_inductive => "'inductive'"
  | .kw_struct => "'record'"
  | .kw_trait => "'trait'"
  | .kw_instance => "'instance'"
  | .kw_where => "'where'"
  | .kw_use => "'use'"
  | .kw_pub => "'pub'"
  | .kw_forall => "'forall'"
  | .kw_bind => "'bind'"
  | .kw_compose => "'compose'"
  | .kw_abbrev => "'abbrev'"
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
  | .colonEquals => "':='"
  | .equals => "'='"
  | .pipe => "'|'"
  | .dot => "'.'"
  | .at => "'@'"
  | .underscore => "'_'"
  | .lambda => "'\\'"
  | .forallSymbol => "'∀'"
  | .dollar => "'$'"
  | .slash => "'/'"
  | .hash => "'#'"
  | .arrow => "'->'"
  | .fatArrow => "'=>'"
  | .leftArrow => "'<-'"
  | .times => "'×'"
  | .omega => "'ω'"
  | .layoutStart => "start of block"
  | .layoutSep => "newline"
  | .layoutEnd => "end of block"
  | .whitespace => "whitespace"
  | .comment => "comment"
  | .eof => "end of file"
  | .error => "error"

instance : ToString TokenKind := ⟨describe⟩

def isKeyword : TokenKind → Bool
  | .kw_def | .kw_theorem | .kw_let | .kw_in | .kw_case | .kw_if | .kw_then | .kw_else
  | .kw_inductive | .kw_struct | .kw_trait | .kw_instance | .kw_where
  | .kw_use | .kw_pub | .kw_forall | .kw_bind | .kw_compose
  | .kw_abbrev | .true_ | .false_ => true
  | _ => false

def isLayout : TokenKind → Bool
  | .layoutStart | .layoutSep | .layoutEnd | .whitespace | .comment => true
  | _ => false

/-- Check if token is a name-like identifier (variable, type name, or operator) -/
def isNameLike : TokenKind → Bool
  | .lowerIdent | .upperIdent | .varSymbol => true
  | _ => false

end TokenKind

/-- Keyword lookup table -/
def keywordMap : List (String × TokenKind) :=
  [ ("def", .kw_def), ("theorem", .kw_theorem), ("let", .kw_let), ("in", .kw_in), ("match", .kw_case)
  , ("if", .kw_if), ("then", .kw_then), ("else", .kw_else)
  , ("inductive", .kw_inductive), ("record", .kw_struct), ("class", .kw_trait)
  , ("instance", .kw_instance), ("where", .kw_where)
  , ("use", .kw_use), ("pub", .kw_pub)
  , ("bind", .kw_bind), ("compose", .kw_compose)
  , ("alias", .kw_abbrev)
  , ("true", .true_), ("false", .false_)
  ]

def lookupKeyword (name : String) : Option TokenKind :=
  keywordMap.lookup name

/-- Raw kind unifying tokens and syntax nodes -/
inductive RawKind where
  -- Tokens (leaves)
  | token (tk : TokenKind)
  -- Nodes (interior)
  | node (sk : SyntaxKind)
  deriving BEq, Hashable, Repr, Inhabited

/-- A green node in the syntax tree -/
inductive GreenNode where
  /-- A token (leaf node) -/
  | token (kind : TokenKind) (text : String)
  /-- An interior node with children -/
  | node (kind : SyntaxKind) (children : Array GreenNode) (width : Nat)
  /-- An error node (parser recovered) -/
  | error (message : String) (children : Array GreenNode) (width : Nat)
  /-- A missing node (expected but not found) -/
  | missing (expected : SyntaxKind)
  deriving Repr, Inhabited

namespace GreenNode

/-- Compute the width (byte length) of a green node -/
def width : GreenNode → Nat
  | .token _ text => text.utf8ByteSize
  | .node _ _ w => w
  | .error _ _ w => w
  | .missing _ => 0

/-- Compute width from children (used when constructing nodes) -/
def childrenWidth (children : Array GreenNode) : Nat :=
  children.foldl (fun acc child => acc + child.width) 0

/-- Smart constructor for interior nodes -/
def mkNode (kind : SyntaxKind) (children : Array GreenNode) : GreenNode :=
  .node kind children (childrenWidth children)

/-- Smart constructor for error nodes -/
def mkError (message : String) (children : Array GreenNode) : GreenNode :=
  .error message children (childrenWidth children)

/-- Get children of a node (empty for tokens/missing) -/
def children : GreenNode → Array GreenNode
  | .token _ _ => #[]
  | .node _ cs _ => cs
  | .error _ cs _ => cs
  | .missing _ => #[]

/-- Check if this is a token -/
def isToken : GreenNode → Bool
  | .token _ _ => true
  | _ => false

/-- Check if this is a trivia token (whitespace or comment) -/
def isTrivia : GreenNode → Bool
  | .token .whitespace _ => true
  | .token .comment _ => true
  | _ => false

/-- Check if this is an error node -/
def isError : GreenNode → Bool
  | .error _ _ _ => true
  | .missing _ => true
  | _ => false

/-- Get the token kind if this is a token -/
def tokenKind? : GreenNode → Option TokenKind
  | .token k _ => some k
  | _ => none

/-- Get the syntax kind if this is an interior node -/
def syntaxKind? : GreenNode → Option SyntaxKind
  | .node k _ _ => some k
  | _ => none

/-- Get the text if this is a token -/
def text? : GreenNode → Option String
  | .token _ t => some t
  | _ => none

/-- Get the raw kind (unified token/syntax kind) -/
def rawKind : GreenNode → RawKind
  | .token k _ => .token k
  | .node k _ _ => .node k
  | .error _ _ _ => .node .sourceFile  -- Error nodes don't have a specific kind
  | .missing k => .node k

/-- Check if any descendant has an error -/
partial def hasErrors : GreenNode → Bool
  | .error _ _ _ => true
  | .missing _ => true
  | .token _ _ => false
  | .node _ children _ => children.any hasErrors

/-- Count all nodes in the tree -/
partial def nodeCount : GreenNode → Nat
  | .token _ _ => 1
  | .node _ children _ => 1 + children.foldl (fun acc c => acc + c.nodeCount) 0
  | .error _ children _ => 1 + children.foldl (fun acc c => acc + c.nodeCount) 0
  | .missing _ => 1

/-- Hash a green node for content-addressing -/
partial def contentHash : GreenNode → UInt64
  | .token kind text =>
      let kindHash := hash kind
      let textHash := hash text
      mixHash kindHash textHash
  | .node kind children _ =>
      let kindHash := hash kind
      let childHashes := children.map contentHash
      childHashes.foldl mixHash kindHash
  | .error msg children _ =>
      let msgHash := hash msg
      let childHashes := children.map contentHash
      childHashes.foldl mixHash msgHash
  | .missing expected =>
      hash expected

instance : BEq GreenNode where
  beq a b := a.contentHash == b.contentHash

instance : Hashable GreenNode where
  hash := contentHash

/-- Strip all triviaToken wrappers from a green tree, replacing each with its inner token -/
partial def stripTrivia : GreenNode → GreenNode
  | .token k t => .token k t
  | .node .triviaToken children _ =>
      if h : 0 < children.size then
        let lastIdx := children.size - 1
        stripTrivia (children[lastIdx]'(by omega))
      else .node .triviaToken #[] 0
  | .node kind children w =>
      let strippedChildren := children.map stripTrivia
      .node kind strippedChildren (childrenWidth strippedChildren)
  | .error msg children w =>
      let strippedChildren := children.map stripTrivia
      .error msg strippedChildren (childrenWidth strippedChildren)
  | .missing expected => .missing expected

/-- Pretty-print the tree structure -/
partial def debugPrint (n : GreenNode) (indent : Nat := 0) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  match n with
  | .token kind text =>
      s!"{pad}TOKEN {kind} \"{text}\"\n"
  | .node kind children _ =>
      let header := s!"{pad}{kind} (width={n.width})\n"
      let childStrs := children.map (debugPrint · (indent + 2))
      header ++ String.join childStrs.toList
  | .error msg children _ =>
      let header := s!"{pad}ERROR: {msg}\n"
      let childStrs := children.map (debugPrint · (indent + 2))
      header ++ String.join childStrs.toList
  | .missing expected =>
      s!"{pad}MISSING {expected}\n"

end GreenNode

/-- Builder state for constructing green trees -/
structure GreenBuilder where
  /-- Cache of interned nodes by hash -/
  cache : Std.HashMap UInt64 GreenNode := {}
  deriving Inhabited

namespace GreenBuilder

/-- Intern a node, returning the cached version if it exists -/
def intern (b : GreenBuilder) (node : GreenNode) : GreenBuilder × GreenNode :=
  let h := node.contentHash
  match b.cache.get? h with
  | some existing => (b, existing)
  | none => ({ cache := b.cache.insert h node }, node)

/-- Create a token node -/
def token (b : GreenBuilder) (kind : TokenKind) (text : String) : GreenBuilder × GreenNode :=
  b.intern (.token kind text)

/-- Create an interior node -/
def node (b : GreenBuilder) (kind : SyntaxKind) (children : Array GreenNode) : GreenBuilder × GreenNode :=
  b.intern (GreenNode.mkNode kind children)

/-- Create an error node -/
def error (b : GreenBuilder) (msg : String) (children : Array GreenNode) : GreenBuilder × GreenNode :=
  b.intern (GreenNode.mkError msg children)

/-- Create a missing node -/
def missing (b : GreenBuilder) (expected : SyntaxKind) : GreenBuilder × GreenNode :=
  b.intern (.missing expected)

end GreenBuilder

end Soma.Syntax
