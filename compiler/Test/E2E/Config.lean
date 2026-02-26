namespace Test.E2E

/-- Configuration for E2E tests -/
structure Config where
  /-- Timeout for execution in milliseconds -/
  runTimeout : Nat := 10000
  /-- Whether to keep temporary directories after tests -/
  keepTemp : Bool := true
  deriving Repr

namespace Config

/-- Create a default configuration -/
def default : Config := {}

end Config
end Test.E2E
