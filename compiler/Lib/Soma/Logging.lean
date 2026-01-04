/-
  Soma Compiler - Logging Module

  Re-exports all logging functionality.
-/

import Soma.Logging.Error

namespace Soma.Logging

-- Re-export from submodules
export Soma.Logging.Error (
  renderDiagnostic
  renderDiagnostics
  printDiagnostic
  printDiagnostics
  renderSummary
)

end Soma.Logging
