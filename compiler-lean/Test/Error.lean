import Soma.Logging.Error
import Soma.Syntax.Source
import Soma.Syntax.Diagnostic

namespace Test.Error

open Soma.Syntax
open Soma.Logging.Error

def run : IO Unit := do
  -- Test 1: Two stacked labels at exact same span
  IO.eprintln "=== Test 1: Two stacked labels at same span ==="
  let source1 := "fn main() {\n    let x = 1\n}"
  let sf1 := SourceFile.create ⟨0⟩ "test.soma" source1

  let loc1Start : SourceLoc := { file := ⟨0⟩, byteOffset := 20, line := 2, column := 9 }
  let loc1End : SourceLoc := { file := ⟨0⟩, byteOffset := 21, line := 2, column := 10 }
  let span1 := { start := loc1Start, stop := loc1End : Span }

  let diag1 : Diagnostic := {
    severity := .error
    code := some "E0001"
    message := "two labels same span"
    labels := #[
      Label.primary span1 "first message",
      Label.secondary span1 "second message"
    ]
    notes := #[]
    help := none
  }
  IO.eprintln (renderDiagnostic diag1 sf1)
  IO.eprintln ""

  -- Test 2: Three stacked labels at same span
  IO.eprintln "=== Test 2: Three stacked labels at same span ==="
  let diag2 : Diagnostic := {
    severity := .warning
    code := some "W0002"
    message := "three labels same span"
    labels := #[
      Label.primary span1 "first",
      Label.secondary span1 "second",
      Label.secondary span1 "third"
    ]
    notes := #[]
    help := none
  }
  IO.eprintln (renderDiagnostic diag2 sf1)
  IO.eprintln ""

  -- Test 3: Two labels at different columns (should NOT stack, no overlap)
  IO.eprintln "=== Test 3: Two labels at different columns (no overlap) ==="
  let source3 := "let result = foo + bar\n"
  let sf3 := SourceFile.create ⟨0⟩ "test.soma" source3

  let fooStart : SourceLoc := { file := ⟨0⟩, byteOffset := 13, line := 1, column := 14 }
  let fooEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 16, line := 1, column := 17 }
  let barStart : SourceLoc := { file := ⟨0⟩, byteOffset := 19, line := 1, column := 20 }
  let barEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 22, line := 1, column := 23 }

  let diag3 : Diagnostic := {
    severity := .error
    code := none
    message := "type mismatch"
    labels := #[
      Label.primary { start := fooStart, stop := fooEnd } "Int",
      Label.secondary { start := barStart, stop := barEnd } "String"
    ]
    notes := #[]
    help := none
  }
  IO.eprintln (renderDiagnostic diag3 sf3)
  IO.eprintln ""

  -- Test 4: Two overlapping labels (different start, but ranges overlap)
  IO.eprintln "=== Test 4: Two overlapping labels ==="
  let source4 := "let value = something\n"
  let sf4 := SourceFile.create ⟨0⟩ "test.soma" source4

  let overlapStart1 : SourceLoc := { file := ⟨0⟩, byteOffset := 12, line := 1, column := 13 }
  let overlapEnd1 : SourceLoc := { file := ⟨0⟩, byteOffset := 17, line := 1, column := 18 }
  let overlapStart2 : SourceLoc := { file := ⟨0⟩, byteOffset := 14, line := 1, column := 15 }
  let overlapEnd2 : SourceLoc := { file := ⟨0⟩, byteOffset := 21, line := 1, column := 22 }

  let diag4 : Diagnostic := {
    severity := .error
    code := none
    message := "overlapping spans"
    labels := #[
      Label.primary { start := overlapStart1, stop := overlapEnd1 } "starts here",
      Label.secondary { start := overlapStart2, stop := overlapEnd2 } "extends further"
    ]
    notes := #[]
    help := none
  }
  IO.eprintln (renderDiagnostic diag4 sf4)
  IO.eprintln ""

  -- Test 5: Multi-line span (end column less than start - goes left)
  IO.eprintln "=== Test 5: Multi-line span (end indented less than start) ==="
  let source5 := "def closure =\n      let x = 1\n      let y = 2\n  unknown\n"
  let sf5 := SourceFile.create ⟨0⟩ "test.soma" source5

  let mlStart : SourceLoc := { file := ⟨0⟩, byteOffset := 20, line := 2, column := 7 }
  let mlEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 50, line := 4, column := 10 }

  let diag5 : Diagnostic := {
    severity := .error
    code := some "E0425"
    message := "end column < start column"
    labels := #[
      Label.primary { start := mlStart, stop := mlEnd } "block spans here"
    ]
    notes := #[]
    help := none
  }
  IO.eprintln (renderDiagnostic diag5 sf5)
  IO.eprintln ""

  -- Test 6: Multi-line span (end column greater than start - goes right)
  IO.eprintln "=== Test 6: Multi-line span (end indented more than start) ==="
  let source6 := "fn outer() {\n  inner(\n      deeply_nested\n  )\n}\n"
  let sf6 := SourceFile.create ⟨0⟩ "test.soma" source6

  let ml2Start : SourceLoc := { file := ⟨0⟩, byteOffset := 14, line := 2, column := 3 }
  let ml2End : SourceLoc := { file := ⟨0⟩, byteOffset := 40, line := 3, column := 20 }

  let diag6 : Diagnostic := {
    severity := .error
    code := none
    message := "end column > start column"
    labels := #[
      Label.primary { start := ml2Start, stop := ml2End } "span goes right"
    ]
    notes := #[]
    help := none
  }
  IO.eprintln (renderDiagnostic diag6 sf6)
  IO.eprintln ""

  -- Test 7: Multi-line span with single-line label on same diagnostic
  IO.eprintln "=== Test 7: Multi-line + single-line labels combined ==="
  let source7 := "fn foo(x: Int) {\n  let y = x + 1\n  return y\n}\n"
  let sf7 := SourceFile.create ⟨0⟩ "test.soma" source7

  let paramStart : SourceLoc := { file := ⟨0⟩, byteOffset := 7, line := 1, column := 8 }
  let paramEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 13, line := 1, column := 14 }
  let bodyStart : SourceLoc := { file := ⟨0⟩, byteOffset := 19, line := 2, column := 3 }
  let bodyEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 45, line := 3, column := 11 }

  let diag7 : Diagnostic := {
    severity := .error
    code := none
    message := "mixed span types"
    labels := #[
      Label.primary { start := bodyStart, stop := bodyEnd } "multi-line body",
      Label.secondary { start := paramStart, stop := paramEnd } "parameter here"
    ]
    notes := #["This combines both span types"]
    help := some "Consider refactoring"
  }
  IO.eprintln (renderDiagnostic diag7 sf7)
  IO.eprintln ""

  -- Test 8: FINAL BOSS - Complex scenario with multiple crossing spans
  IO.eprintln "=== Test 8: FINAL BOSS - Complex crossings ==="
  let source8 := "fn complex(a: Int, b: String, c: Bool) {\n    let result = compute(a, b, c)\n    match result {\n        Ok(v) => process(v),\n        Err(e) => handle(e)\n    }\n}\n"
  let sf8 := SourceFile.create ⟨0⟩ "test.soma" source8

  -- Multiple labels on same line at same column (3 stacked)
  let aStart : SourceLoc := { file := ⟨0⟩, byteOffset := 11, line := 1, column := 12 }
  let aEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 12, line := 1, column := 13 }

  -- Multi-line span from line 2 to line 5 (body of function)
  let bodyStart : SourceLoc := { file := ⟨0⟩, byteOffset := 45, line := 2, column := 5 }
  let bodyEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 150, line := 5, column := 24 }

  -- Another multi-line span that overlaps (match block lines 3-6)
  let matchStart : SourceLoc := { file := ⟨0⟩, byteOffset := 75, line := 3, column := 5 }
  let matchEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 160, line := 6, column := 6 }

  -- Single label on line 4
  let okStart : SourceLoc := { file := ⟨0⟩, byteOffset := 100, line := 4, column := 9 }
  let okEnd : SourceLoc := { file := ⟨0⟩, byteOffset := 103, line := 4, column := 14 }

  let diag8 : Diagnostic := {
    severity := .error
    code := some "E9999"
    message := "the final boss of diagnostics"
    labels := #[
      Label.primary { start := aStart, stop := aEnd } "param a",
      Label.secondary { start := aStart, stop := aEnd } "also here",
      Label.secondary { start := aStart, stop := aEnd } "and here too",
      Label.primary { start := bodyStart, stop := bodyEnd } "function body spans here",
      Label.secondary { start := matchStart, stop := matchEnd } "match block overlaps",
      Label.secondary { start := okStart, stop := okEnd } "Ok variant"
    ]
    notes := #["This tests stacked labels + overlapping multi-line spans", "Good luck!"]
    help := some "If this renders correctly, you've won"
  }
  IO.eprintln (renderDiagnostic diag8 sf8)

end Test.Error
