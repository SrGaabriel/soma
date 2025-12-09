import Soma

namespace Test.Lexer

open Soma.Syntax in
def run : IO Unit := do
  IO.println "=== Lexer Tests ==="

  -- Test 1: Simple identifier
  let (tokens, diags) := lex "hello"
  IO.println s!"Test 1 (identifier): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 2: Keywords
  let (tokens, diags) := lex "def let case if then else"
  IO.println s!"Test 2 (keywords): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 3: Numbers and operators
  let (tokens, diags) := lex "42 + 10 - 5"
  IO.println s!"Test 3 (numbers/ops): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 4: String literal
  let (tokens, diags) := lex "\"hello world\""
  IO.println s!"Test 4 (string): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 5: Arrows and punctuation
  let (tokens, diags) := lex "x -> y => z :: w"
  IO.println s!"Test 5 (arrows): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 6: Comments
  let (tokens, diags) := lex "x // this is a comment\ny"
  IO.println s!"Test 6 (line comment): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 7: Layout (simple)
  let (tokens, diags) := lex "def foo\n  x\n  y"
  IO.println s!"Test 7 (layout): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 8: Parens and brackets
  let (tokens, diags) := lex "(a, [b, c], {d})"
  IO.println s!"Test 8 (brackets): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 9: Lambda and forall
  let (tokens, diags) := lex "\\x -> x"
  IO.println s!"Test 9 (lambda): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 10: More realistic code
  let code := "def factorial n =
  case n
    | 0 => 1
    | _ => n * factorial (n - 1)"
  let (tokens, diags) := lex code
  IO.println s!"Test 10 (realistic): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  IO.println "=== Tests Complete ==="

end Test.Lexer
