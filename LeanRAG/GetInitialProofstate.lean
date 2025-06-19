import LeanRAG.States

open Cli Lean Meta Core

def getInitialProofstateMain (args : Cli.Parsed) : IO UInt32 := do
  let module := args.positionalArg! "module" |>.as! ModuleName
  let thmName := args.positionalArg! "thmName" |>.as! String |>.toName
  let results ← allProofStatesFromModule module (some [thmName]) true
  for result in results do
    IO.println <| (toJson result).getObjValD "initialProofState" |>.compress
  return 0

def getInitialProofstate : Cmd := `[Cli|
  get_initial_proofstate VIA getInitialProofstateMain; ["0.0.1"]
  "Print a jsonl file of all theorems in a module along with their initial states and proofs."

  ARGS:
    module : ModuleName; "Lean module to compile and extract states from."
    thmName : String; "Name of a theorem to extract the initial proof state for."
]

-- /-- `lake exe get_initial_proofstate` -/
def main (args : List String) : IO UInt32 :=
  getInitialProofstate.validate args

-- #eval main ["LeanRAG.Test", "one_plus_one_eq_two"]
