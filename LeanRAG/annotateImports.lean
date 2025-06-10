import Cli
import LeanRAG.stateComments
import TrainingData.InfoTree.Basic
import TrainingData.InfoTree.TacticInvocation.Basic
import ImportGraph.RequiredModules
import Lake.Load
import Lake
import Mathlib.Lean.CoreM
import Batteries
import Lean

import Lean.Elab.Frontend

open Lean Core Elab IO Meta Term Command Tactic Cli

/- Adds comments about the goal state of the proof after each tactic -/
def insertStateComments (step:CompilationStep) : IO String := do
  /- Get relevant tactic nodes -/
  let tactics := step.trees
    |>.flatMap InfoTree.retainTacticInfo
    |>.flatMap InfoTree.retainOriginal
    |>.flatMap InfoTree.retainSubstantive
    |>.flatMap InfoTree.tactics

  let tacticStates ← tactics.mapM TacticInvocation.rangeAndStates
  let separatedStates := dropEnclosed tacticStates |>.filter fun ⟨⟨⟨l₁, _⟩, ⟨l₂, _⟩⟩, _, _⟩  => l₁ = l₂
  let formattedStates := (separatedStates.map fun ⟨r, sb, sa⟩ => (r, formatState sb (some 80), formatState sa (some 80)))

  let mut src := ({str := step.src.str, startPos := 0, stopPos := step.src.stopPos} : Substring).toString.splitOn "\n"
  let mut inserted : Std.HashSet Nat := Std.HashSet.ofList [10000000]

  /- insert each of the goal states into the existing proof string -/
  for item in formattedStates.reverse do
    let ⟨⟨⟨l, c⟩, _⟩, sb, sa⟩ := item
    if sa.contains "🎉 no goals" then
      src := src.insertIdx l <| stateComment sa c
    if inserted.contains (l-1) then
      src := src.set (l-1) <| stateComment sb c
    else
      src := src.insertIdx (l-1) <| stateComment sb c
      inserted := inserted.insert (l-1)
  let out := ("\n".intercalate src)
  let trim_out := ({str := out, startPos := step.src.startPos, stopPos := out.endPos}:Substring).toString
  return trim_out

/- Helper function to return plaintext of a theorem annotated with goal states -/
def annotateTheorems (targetModule : Name) (decls : Option (List Name)) : IO (List String) := do
  searchPathRef.set compile_time_search_path%
  try
    let fileName := (← findLean targetModule).toString

    /- Process the actual source code from our module -/
    let steps := Lean.Elab.IO.processInput' (← moduleSource targetModule) none ({}) fileName
    let targets := steps.bind fun c => (MLList.ofList c.diff).map fun i => (c, i)

    let mut annotatedTheorems := []

    for (cmd, ci) in targets do
      let ci_name_stem := ci.name.toString.splitOn "." |>.getLast! |>.toName
      if ((decls.isSome && !(decls.get!.contains ci_name_stem))) then
        continue
      let state_comments ← insertStateComments cmd
      /- TODO: why is it repeating a bunch of theorems? It gives them weird names like "1" and "_" but they have the same content??? -/
      if (!annotatedTheorems.contains state_comments) then
        annotatedTheorems := annotatedTheorems ++ [state_comments]

    return annotatedTheorems
  catch _ =>
    return []

/- Sends annotated theorems to the Python process over HTTP -/
def sendCurlInfo (endpoint : String) (module : Name) (theorems : IO (List String)) : IO Bool:= do
  let jsonPayload : Json := Json.mkObj [
      ("filename", Json.str <| (← (findLean module)).toString),
      ("theorems", Json.arr <| Array.mk <| (← theorems).map fun x => Json.str x)
    ]
  let args := #[
    "-X", "POST",
    "-H", "Content-Type: application/json",
    "-d", s!"{jsonPayload.compress}",
    endpoint
  ]
  let _ ← IO.Process.output { cmd := "curl", args := args }
  return true

def sendCurlDefault := sendCurlInfo "http://localhost:8000/"

def sendInfoStdout (module : Name) (theorems : IO (List String)) : IO Bool:= do
  let jsonPayload : Json := Json.mkObj [
      ("filename", Json.str <| (← (findLean module)).toString),
      ("theorems", Json.arr <| Array.mk <| (← theorems).map fun x => Json.str x)
    ]
  IO.println s!"{jsonPayload.compress}"
  return true

def formatInfo (module : Name) (theorems : IO (List String)) : IO String:= do
  let jsonPayload : Json := Json.mkObj [
      ("filename", Json.str <| (← (findLean module)).toString),
      ("theorems", Json.arr <| Array.mk <| (← theorems).map fun x => Json.str x)
    ]
  return jsonPayload.compress

-- def mathlibPathDefault : IO String := do
--   return (← IO.Process.output { cmd := "pwd", args := #[] }).stdout.trim ++ "/.lake/packages/mathlib/Mathlib"

-- /- Yields a list of all modules in Mathlib -/
-- def getMathlibModules (mathlibPath : IO String) : IO (List Name) := do
--   let paths := (← IO.Process.output { cmd := "find", args := #[← mathlibPath, "-type", "f", "-name", "*.lean", "-print"] }).stdout.splitOn "\n"
--   -- This is a pretty jank way of doing this, will figure out a better way later
--   -- TODO: also filter out deprecated stuff?
--   let modules := paths.map fun x => x.splitOn "/mathlib/" |>.getLast! |>.map (fun c => if c == '/' then '.' else c) |>.splitOn ".lean" |>.get! 0 |>.toName
--   return modules

-- def chunk (chunkSize : Nat) (l : List α) := (
--   List.foldl (fun (acc) (n) => match acc with
--     | [] => []
--     | a::acc =>
--       if a.length < chunkSize then (n::a)::acc else [n]::a::acc) [[]] l)

-- def annotateMathlibStdio : IO Unit := do
--   let modules := (← getMathlibModules mathlibPathDefault)
--   let processModule := fun (module : Name) => do
--     let theorems := annotateTheorems module none
--     if (!(← theorems).isEmpty) then
--       -- sendInfoStdout module theorems
--       return formatInfo module theorems
--     else return pure ""

--   -- Cringe version
--   let out ← modules.mapM processModule

--   -- Extreme version ( !!! takes 50+GB of memory !!!)
--   -- let num_threads := 5
--   -- let batch_size := 100
--   -- let batches := chunk batch_size modules
--   -- for b in batches do
--   --   let thread_tasks := chunk (batch_size/num_threads) b
--   --   let results := thread_tasks.map (fun c => IO.asTask (prio := Task.Priority.dedicated) do
--   --     let out ← c.mapM processModule
--   --     return out)
--   --   let formatted ← results.mapM fun (t : BaseIO _) => do
--   --     IO.ofExcept <| (← t).get

--   --   for f in formatted do
--   --     for line in f do
--   --       IO.println (← line)

-- def annotateMathlibCurl (endpoint : String): IO Unit := do
--   let num_threads := 1
--   let modules := (← getMathlibModules mathlibPathDefault)
--   let processModule := fun (module : Name)  => do
--     let theorems := annotateTheorems module none
--     if (!(← theorems).isEmpty) then
--       let _ ← sendCurlInfo endpoint module theorems
--       return
--     else
--       return
--   let chunked := chunk (modules.length / num_threads + 1) modules
--   let results := chunked.map (fun c => IO.asTask (prio := Task.Priority.dedicated) do
--       let _ ← c.mapM processModule
--       return)
--   let _ ← results.mapM fun (t : BaseIO _) => do
--     IO.ofExcept <| (← t).get

--   /- Tell the server we're done -/
--   let jsonPayload : Json := Json.mkObj [
--     ("status", Json.str "done")
--     ]
--   let args := #[
--     "-X", "POST",
--     "-H", "Content-Type: application/json",
--     "-d", s!"{jsonPayload.compress}",
--     endpoint
--   ]
--   let _ ← IO.Process.output { cmd := "curl", args := args }
--   return ()

/- Adapted from ntp-toolkit repository -/
-- def getImports (module : Name) := do
--   searchPathRef.set compile_time_search_path%
  -- let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  -- let test ← CoreM.withImportModules #[module] (options:=options) do
  --   let env ← getEnv
  --   let allModulesSorted := env.allImportedModuleNames.qsort (·.toString < ·.toString)
  --   return allModulesSorted
  -- return test
  -- let env ← getEnv "test"
  -- let test := Lean.Environment.imports env

def annotateImports (_ : Name) : IO Unit :=
  return

def main (args : List String) : IO UInt32 := do
  let options := Options.empty.insert `maxHeartbeats (0 : Nat)
  let modules := match args with
  | [] => #[`Mathlib]
  | args => args.toArray.map fun s => s.toName
  searchPathRef.set compile_time_search_path%
  CoreM.withImportModules modules (options := options) do
    let env ← getEnv
    let allModulesSorted := env.allImportedModuleNames.qsort (·.toString < ·.toString)
    let directlyImportedModules := env.imports.map (·.module)
    for module in allModulesSorted do
      let json := Json.mkObj [
        ("name", Json.str s!"{module}"),
        ("isDirect", Json.bool (directlyImportedModules.contains module))
      ]
      IO.println json.compress
  return 0

-- def main : IO Unit := do annotateMathlibStdio
-- def main : IO Unit := do annotateMathlibCurl "http://localhost:8000/"

-- #eval getImports `temp.temp
-- #eval main ["temp.temp"]
/- lake exe AnnotateTheorems -/
