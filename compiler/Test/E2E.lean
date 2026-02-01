import Test.E2E.Config
import Test.E2E.Fixtures
import Test.E2E.Runner
import Test.Fixtures

namespace Test.E2E

open Test.Fixtures (TestRunner)

/-- Run all E2E tests with auto-discovered configuration -/
def run : IO TestRunner := do
  IO.println "=== E2E Tests ==="

  match ← Config.discover with
  | .error msg =>
    IO.println s!"  Skipping E2E tests: {msg}"
    return TestRunner.init
  | .ok config =>
    IO.println s!"  Using sysroot: {config.sysroot}"
    IO.println ""
    runAll config

end Test.E2E
