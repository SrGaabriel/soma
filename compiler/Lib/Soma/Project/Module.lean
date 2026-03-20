import Soma.Syntax

namespace Soma.Project

open Soma.Syntax

/-- A qualified module name with package and path components -/
structure ModuleName where
  /-- The package this module belongs to -/
  package : String
  /-- Path components within the package (like ["Data", "List"]) -/
  path : Array String
  deriving Repr, Hashable

namespace ModuleName

instance : BEq ModuleName where
  beq m1 m2 := m1.package == m2.package && m1.path == m2.path

instance : Ord ModuleName where
  compare m1 m2 :=
    match compare m1.package m2.package with
    | .eq => compare m1.path.toList m2.path.toList
    | other => other

/-- Parse a module name from a string like "myapp/Utils/String" -/
def parse (s : String) : Option ModuleName :=
  let parts := s.splitOn "/"
  match parts with
  | [] => none
  | [single] => some { package := single, path := #[] }
  | pkg :: rest => some { package := pkg, path := rest.toArray }

/-- Convert to the canonical string representation -/
def toString (m : ModuleName) : String :=
  if m.path.isEmpty then m.package
  else m.package ++ "/" ++ String.intercalate "/" m.path.toList

instance : ToString ModuleName := ⟨ModuleName.toString⟩

/-- The last component of the path, or package name if path is empty -/
def baseName (m : ModuleName) : String :=
  m.path.back?.getD m.package

/-- Check if this is the prelude module -/
def isPrelude (m : ModuleName) : Bool :=
  m.package == "stdlib" && m.path == #["prelude"]

/-- Create module name from package and relative path -/
def fromParts (package : String) (path : Array String) : ModuleName :=
  { package, path }

/-- Create from a simple qualified string -/
def fromString (s : String) : ModuleName :=
  parse s |>.getD { package := s, path := #[] }

/-- Convert to namespace path segments for the namespace tree -/
def toNamespace (m : ModuleName) : Array String :=
  #[m.package] ++ m.path

end ModuleName

/-- Information about a parsed module, ready for type checking -/
structure ModuleInfo where
  /-- Qualified module name -/
  name : ModuleName
  /-- Absolute file path -/
  path : System.FilePath
  /-- Original source content (for error messages) -/
  content : String
  /-- Source file object (for span resolution) -/
  sourceFile : SourceFile
  /-- Parsed AST -/
  ast : Module
  /-- Content hash for incremental compilation (optional) -/
  contentHash : Option UInt64 := none
  deriving Repr

namespace ModuleInfo

/-- Get the string representation of the module name -/
def nameStr (m : ModuleInfo) : String := m.name.toString

/-- Extract import declarations from the AST -/
def imports (m : ModuleInfo) : Array QualName :=
  m.ast.decls.filterMap fun decl =>
    match decl with
    | .use _ path _ _ => some path
    | _ => none

/-- Collect all pub use items -/
def pubUseItems (m : ModuleInfo) : Array (QualName × Array QualName) :=
  m.ast.decls.filterMap fun decl =>
    match decl with
    | .use true path items _ => some (path, items)
    | _ => none

/-- Check if this module has any pub use declarations -/
def hasPubUses (m : ModuleInfo) : Bool :=
  m.ast.decls.any fun decl =>
    match decl with
    | .use true _ _ _ => true
    | _ => false

end ModuleInfo

end Soma.Project
