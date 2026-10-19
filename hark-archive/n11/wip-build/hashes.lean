import Lean
import Lean.Elab.ParseImportsFast
open Lean
open System hiding SearchPath

def isPart (mod : Name) : Bool := #[`Mathlib, `Batteries, `BatteriesRecycling, `Aesop, `Cli, `ImportGraph,
  `LeanSearchClient, `Plausible, `Qq, `ProofWidgets, `Archive, `Counterexamples, `MathlibTest,
  `Requests, `OpenAIClient, `Reap, `Canonical, `Duper, `Auto, `PremiseSelection, `Hammer].contains mod.getRoot

def hashFileContents (c : String) : UInt64 := hash c.crlfToLf

structure St where
  cache : Std.HashMap Name (Option UInt64) := {}

partial def getHash (sp : SearchPath) (root : UInt64) (mod : Name) (f : FilePath) : StateT St IO (Option UInt64) := do
  match (← get).cache[mod]? with
  | some h => return h
  | none =>
    if !(← f.pathExists) then
      IO.eprintln s!"missing {f}"; modify fun s => {s with cache := s.cache.insert mod none}; return none
    let content ← IO.FS.readFile f
    let res ← Lean.parseImports' content mod.toString
    let imps := res.imports.filter (isPart ·.module)
    let mut hs := #[]
    for imp in imps do
      let fi ← Lean.findLean sp imp.module
      match ← getHash sp root imp.module fi with
      | some h => hs := hs.push h
      | none => modify fun s => {s with cache := s.cache.insert mod none}; return none
    let filePath := mkFilePath (mod.components.map toString) |>.withExtension "lean"
    let pathHash := hash filePath.components
    let h := hash <| root :: pathHash :: hashFileContents content :: hs.toList
    modify fun s => {s with cache := s.cache.insert mod (some h)}
    return some h

def main (args : List String) : IO Unit := do
  let ml : FilePath := args[0]!
  let pks := args.drop 1
  let sp : SearchPath := [ml] ++ pks.map FilePath.mk
  let rootFiles := [ml / "lakefile.lean", ml / "lean-toolchain", ml / "lake-manifest.json"]
  let hashes ← rootFiles.mapM fun p => hashFileContents <$> IO.FS.readFile p
  let root : UInt64 := hash ((5 : UInt64) :: hashes)
  let (_, st) ← (getHash sp root `Mathlib (ml / "Mathlib.lean")).run {}
  for (m, h?) in st.cache.toList do
    match h? with
    | some h => IO.println s!"{m} {h.toNat}"
    | none => IO.println s!"{m} NONE"
