import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong

/-!
# Structural Injectivity Theorems

A bunch of important structural theorems about the definitional equality relation
that are difficult to prove due to the interaction between transitivity, type
conversion (defeqDF), and well-formed defeqs (extra).

## IsDefEqU.sort_inv

States that if two sort expressions `(.sort u)` and `(.sort v)` are definitionally
equal (share a common type `A`), then their universe levels are equivalent (`u ≈ v`).

### Proof Strategy

Prove by induction on the `IsDefEq` derivation:

1. **sortDF**: Direct — the constructor requires `l ≈ l'` by definition.

2. **symm**: Swap the levels and use IH, then apply `symm` to the equivalence.

3. **trans**: If `(.sort u) ≡ e₂ : A` and `e₂ ≡ (.sort v) : A`, then `e₂` must
   also be a sort `(.sort u₂)` (because it has a sort as its type in the
   definitional equality relation). Then `u ≈ u₂` from the first half and
   `u₂ ≈ v` from the second half, giving `u ≈ v` by transitivity.
   The hard part is proving `e₂` is a sort.

4. **defeqDF**: If `A ≡ B : .sort u'` and `(.sort u) ≡ (.sort v) : A`, then
   both `A` and `B` are sorts. Apply IH to the type equality to get the level
   relationship between `A`'s and `B`'s sort levels, then apply IH to the main
   equality.

5. **bvar/constDF/appDF/lamDF/beta/eta**: Impossible — these constructors produce
   types that are never sorts (Lookup types, instantiated constant types,
   instantiated body types, or Pi types).

6. **forallEDF**: Impossible — the LHS is `.forallE A body`, never `.sort u`.

7. **proofIrrel**: Impossible — the type is `p` where `p : .sort .zero`,
   and `p` itself is never a sort.

8. **extra**: In well-formed environments (via `VEnv.WF`), defeqs are created
   from `VDefVal.toDefEq`, which always has `.const name (params uvars)` as
   the LHS. Since `.sort u ≠ .const _ _`, this case is impossible.

### Open Challenges

- The `trans` case requires proving that intermediate terms in the derivation
  are also sorts. This needs a stronger induction hypothesis that simultaneously
  proves: "if an IsDefEq judgment has a sort type, then both sides are sorts."

- The `defeqDF` case similarly requires knowing that `A` and `B` (the types being
  converted between) are sorts.

- A mutual induction or a well-founded recursion on the derivation size might
  be needed to handle these cases properly.
-/

namespace Lean4Lean
namespace VEnv

/-- If two sort expressions are definitionally equal (share a common type),
    then their universe levels are equivalent. -/
theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v :=
  sorry

theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  let ⟨_, eq⟩ := h1
  let ⟨h2, h3⟩ := (eq.strong henv hΓ).hasType'
  let ⟨_, h2⟩ := h2.stratify
  let ⟨_, h3⟩ := h3.stratify
  let ⟨⟨_, a1, _⟩, _, a2, _⟩ := IsDefEqU.forallE_inv_stratified henv hΓ h1 h2 h3
  ⟨⟨_, a1⟩, _, a2⟩

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := sorry
