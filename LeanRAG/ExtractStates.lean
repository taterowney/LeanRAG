/-
Extracts proof states from constants in the environment
-/

import LeanRAG.States

open Lean Meta Core Cli

def extractStatesMain (args : Cli.Parsed) : IO UInt32 := do
  let module := args.positionalArg! "module" |>.as! ModuleName
  let results ← allProofStatesFromModule module none true
  for result in results do
    IO.println (toJson result).compress
  return 0

def extract_states : Cmd := `[Cli|
  extract_states VIA extractStatesMain; ["0.0.1"]
  "Print a jsonl file of all theorems in a module along with their initial states and proofs."

  ARGS:
    module : ModuleName; "Lean module to compile and extract states from."
]

-- /-- `lake exe extract_states` -/
def main (args : List String) : IO UInt32 :=
  extract_states.validate args

-- #eval main ["LeanRAG.Test"]
