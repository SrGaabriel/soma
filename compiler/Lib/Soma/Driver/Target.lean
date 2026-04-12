import Kenosis

namespace Soma.Driver

open Kenosis

/-- Target operating system -/
inductive TargetOS where
  | windows
  | linux
  | macos
  | freebsd
  | none
  | custom (name : String)
  deriving Repr, BEq, Inhabited

namespace TargetOS

def toString : TargetOS → String
  | .windows => "windows"
  | .linux => "linux"
  | .macos => "macos"
  | .freebsd => "freebsd"
  | .none => "none"
  | .custom name => name

instance : ToString TargetOS := ⟨toString⟩

def fromString : String → TargetOS
  | "windows" => .windows
  | "linux" => .linux
  | "macos" | "darwin" => .macos
  | "freebsd" => .freebsd
  | "none" | "" => .none
  | name => .custom name

instance : Serialize TargetOS where
  serialize os := Serialize.serialize os.toString

instance : Deserialize TargetOS where
  deserialize := do
    let s : String ← Deserialize.deserialize
    pure (TargetOS.fromString s)

/-- Whether this OS uses the Windows x64 calling convention -/
def isWindowsABI : TargetOS → Bool
  | .windows => true
  | _ => false

/-- Whether this OS uses Mach-O object format -/
def isMachO : TargetOS → Bool
  | .macos => true
  | _ => false

end TargetOS

/-- Target architecture -/
inductive TargetArch where
  | x86_64
  | aarch64
  | riscv64
  | wasm32
  | wasm64
  | custom (name : String)
  deriving Repr, BEq, Inhabited

namespace TargetArch

def toString : TargetArch → String
  | .x86_64 => "x86_64"
  | .aarch64 => "aarch64"
  | .riscv64 => "riscv64"
  | .wasm32 => "wasm32"
  | .wasm64 => "wasm64"
  | .custom name => name

instance : ToString TargetArch := ⟨toString⟩

def fromString : String → TargetArch
  | "x86_64" | "x86-64" | "amd64" => .x86_64
  | "aarch64" | "arm64" => .aarch64
  | "riscv64" => .riscv64
  | "wasm32" => .wasm32
  | "wasm64" => .wasm64
  | name => .custom name

instance : Serialize TargetArch where
  serialize a := Serialize.serialize a.toString

instance : Deserialize TargetArch where
  deserialize := do
    let s : String ← Deserialize.deserialize
    pure (TargetArch.fromString s)

/-- Default pointer width in bits for this architecture -/
def defaultPointerWidth : TargetArch → Nat
  | .wasm32 => 32
  | _ => 64

end TargetArch

/-- Endianness -/
inductive Endian where
  | little
  | big
  deriving Repr, BEq, Inhabited

namespace Endian

def toString : Endian → String
  | .little => "little"
  | .big => "big"

instance : ToString Endian := ⟨toString⟩

def fromString : String → Endian
  | "big" => .big
  | _ => .little

instance : Serialize Endian where
  serialize e := Serialize.serialize e.toString

instance : Deserialize Endian where
  deserialize := do
    let s : String ← Deserialize.deserialize
    pure (Endian.fromString s)

end Endian

/-- Target specification describing the platform -/
structure TargetSpec where
  /-- LLVM target triple -/
  llvmTarget : String
  /-- LLVM data layout string -/
  dataLayout : String := ""
  /-- Pointer width in bits (32 or 64) -/
  pointerWidth : Nat := 64
  /-- Architecture -/
  arch : TargetArch := .x86_64
  /-- Operating system -/
  os : TargetOS := .none
  /-- Environment/ABI -/
  env : String := ""
  /-- Byte order -/
  endian : Endian := .little
  deriving Repr, Inhabited, Serialize, Deserialize, BEq

namespace TargetSpec

def x86_64_windows_gnu : TargetSpec := {
  llvmTarget := "x86_64-w64-mingw32"
  dataLayout := "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
  arch := .x86_64, os := .windows, env := "gnu"
}

def x86_64_linux_gnu : TargetSpec := {
  llvmTarget := "x86_64-pc-linux-gnu"
  dataLayout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
  arch := .x86_64, os := .linux, env := "gnu"
}

def x86_64_linux_musl : TargetSpec := {
  llvmTarget := "x86_64-pc-linux-musl"
  dataLayout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
  arch := .x86_64, os := .linux, env := "musl"
}

def x86_64_macos : TargetSpec := {
  llvmTarget := "x86_64-apple-darwin"
  dataLayout := "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
  arch := .x86_64, os := .macos
}

def aarch64_linux_gnu : TargetSpec := {
  llvmTarget := "aarch64-unknown-linux-gnu"
  dataLayout := "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
  arch := .aarch64, os := .linux, env := "gnu"
}

def aarch64_macos : TargetSpec := {
  llvmTarget := "aarch64-apple-darwin"
  dataLayout := "e-m:o-i64:64-i128:128-n32:64-S128-Fn32"
  arch := .aarch64, os := .macos
}

def wasm32 : TargetSpec := {
  llvmTarget := "wasm32-unknown-unknown"
  dataLayout := "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20"
  pointerWidth := 32, arch := .wasm32
}

/-- Look up a built-in target by name -/
def fromName? (name : String) : Option TargetSpec :=
  match name with
  | "x86_64-windows-gnu" | "x86_64-w64-mingw32" => some x86_64_windows_gnu
  | "x86_64-linux-gnu" | "x86_64-pc-linux-gnu" => some x86_64_linux_gnu
  | "x86_64-linux-musl" | "x86_64-pc-linux-musl" => some x86_64_linux_musl
  | "x86_64-macos" | "x86_64-apple-darwin" => some x86_64_macos
  | "aarch64-linux-gnu" | "aarch64-unknown-linux-gnu" => some aarch64_linux_gnu
  | "aarch64-macos" | "aarch64-apple-darwin" => some aarch64_macos
  | "wasm32" | "wasm32-unknown-unknown" => some wasm32
  | _ => none

/-- Auto-detect the host target -/
def hostTarget : TargetSpec :=
  if System.Platform.isWindows then x86_64_windows_gnu
  else
    let t := System.Platform.target
    let isArm64 := t.startsWith "aarch64" || t.startsWith "arm64"
    let isDarwin := t.find (· == 'd') != t.endPos
    if isArm64 then
      if isDarwin then aarch64_macos
      else aarch64_linux_gnu
    else
      if isDarwin then x86_64_macos
      else x86_64_linux_gnu

/-- Load a custom target spec from a JSON file -/
def fromJsonFile (path : System.FilePath) : IO (Except String TargetSpec) := do
  let contents ← IO.FS.readFile path
  match Json.decode contents with
  | .ok spec => pure (.ok spec)
  | .error e => pure (.error s!"Failed to parse target spec '{path}': {e}")

/-- Resolve a target from a --target flag value -/
def resolve (targetFlag : Option String) : IO TargetSpec := do
  match targetFlag with
  | none => pure hostTarget
  | some name =>
    match fromName? name with
    | some spec => pure spec
    | none =>
      if name.endsWith ".json" then
        match ← fromJsonFile ⟨name⟩ with
        | .ok spec => pure spec
        | .error e =>
          IO.eprintln s!"warning: {e}, using as raw triple"
          pure { hostTarget with llvmTarget := name }
      else
        pure { hostTarget with llvmTarget := name }

end TargetSpec

end Soma.Driver
