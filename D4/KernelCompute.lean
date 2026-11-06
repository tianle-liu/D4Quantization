import Lean.Elab.Tactic.ElabTerm

/-!+# Kernel-only reflexivity for closed computational equalities

`kernel_rfl` constructs `Eq.refl` of the right-hand side and submits it,
with the stated equality as its type, to Lean's ordinary kernel through
`Meta.mkAuxLemma`. The kernel must check definitional equality of both
sides before the auxiliary theorem can be used. No evaluator, decidable
equality procedure, additional axiom, or unchecked proof is involved.

Unlike the usual `rfl` tactic, the elaborator does not first repeat that
potentially expensive definitional-equality computation. The resulting
kernel-checked theorem also prevents later rechecking of the computation.
-/

open Lean Meta Elab Tactic

/-- Close a syntactic, closed equality by kernel-checked computation.
Free variables, metavariables, and unsafe dependencies are rejected. -/
elab "kernel_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let expectedType := (← instantiateMVars (← goal.getType)).consumeMData
  if expectedType.hasFVar || expectedType.hasMVar || expectedType.hasLooseBVars then
    throwError "kernel_rfl requires a closed equality without metavariables"
  let .app (.app (.app (.const ``Eq [u]) α) _) rhs := expectedType
    | throwError "kernel_rfl requires an equality as its target"
  let proof := mkApp2 (mkConst ``Eq.refl [u]) α rhs
  let env ← getEnv
  if env.hasUnsafe expectedType || env.hasUnsafe proof then
    throwError "kernel_rfl does not accept unsafe dependencies"
  let levelsInType := (collectLevelParams {} expectedType).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
  -- Synchronous checking is essential: failure must reject this tactic here.
  let lemmaName ← withOptions (Elab.async.set · false) do
    mkAuxLemma lemmaLevels expectedType proof
  goal.assign (mkConst lemmaName (lemmaLevels.map .param))
  replaceMainGoal []
