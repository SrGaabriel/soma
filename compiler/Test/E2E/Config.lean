namespace Test.E2E

/-- Configuration for E2E tests -/
structure Config where
  /-- Path to sysroot directory -/
  sysroot : System.FilePath
  /-- Timeout for execution in milliseconds -/
  runTimeout : Nat := 10000
  /-- Whether to keep temporary directories after tests -/
  keepTemp : Bool := false
  deriving Repr

namespace Config

/-- Find the sysroot directory -/
def findSysroot : IO (Option System.FilePath) := do
  if let some envPath ← IO.getEnv "SOMA_SYSROOT" then
    let path : System.FilePath := envPath
    if ← path.pathExists then
      return some path

  let relativePath : System.FilePath := "../runtime"
  if ← relativePath.pathExists then
    return some relativePath

  return none

/-- Create a default configuration by auto-discovering paths -/
def discover : IO (Except String Config) := do
  let sysroot ← findSysroot

  match sysroot with
  | none =>
    return .error "Could not find sysroot. Set SOMA_SYSROOT or ensure ../runtime exists."
  | some r =>
    return .ok { sysroot := r }

end Config
end Test.E2E
