import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.VLCtx
import Lean4Lean.Verify.Axioms

namespace Lean4Lean
open Lean VExpr VEnv

/-- Collect all arguments from a left-associated application chain.
    `.app (.app C a₁) a₂` gives `[a₁, a₂]`. -/
def VExpr.appArgs : VExpr → List VExpr
  | .app f a => VExpr.appArgs f ++ [a]
  | e => [e]

/-- Get the head of an application chain (the non-application part). -/
def VExpr.appHead : VExpr → VExpr
  | .app f _ => VExpr.appHead f
  | e => e

attribute [simp] VExpr.appHead

def Closed : Expr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .fvar _, _ | .sort .., _ | .const .., _ | .lit .., _ => True
  | .app f a, k => Closed f k ∧ Closed a k
  | .lam _ d b _, k
  | .forallE _ d b _, k => Closed d k ∧ Closed b (k+1)
  | .letE _ d v b _, k => Closed d k ∧ Closed v k ∧ Closed b (k+1)
  | .proj _ _ e, k | .mdata _ e, k => Closed e k
  | .mvar .., _ => False

nonrec abbrev _root_.Lean.Expr.Closed := @Closed

/-- This is very inefficient, only use for spec purposes -/
def _root_.Lean.Expr.fvarsList : Expr → List FVarId
  | .bvar _ | .sort .. | .const .. | .lit .. | .mvar .. => []
  | .fvar fv => [fv]
  | .app f a => f.fvarsList ++ a.fvarsList
  | .lam _ d b _
  | .forallE _ d b _ => d.fvarsList ++ b.fvarsList
  | .letE _ d v b _ => d.fvarsList ++ v.fvarsList ++ b.fvarsList
  | .proj _ _ e | .mdata _ e => e.fvarsList

variable (fvars : FVarId → Prop) in
def FVarsIn : Expr → Prop
  | .bvar _ => True
  | .fvar fv => fvars fv
  | .sort u => u.hasMVar' = false
  | .const _ us => ∀ u ∈ us, u.hasMVar' = false
  | .lit .. => True
  | .app f a => FVarsIn f ∧ FVarsIn a
  | .lam _ d b _
  | .forallE _ d b _ => FVarsIn d ∧ FVarsIn b
  | .letE _ d v b _ => FVarsIn d ∧ FVarsIn v ∧ FVarsIn b
  | .proj _ _ e | .mdata _ e => FVarsIn e
  | .mvar .. => False

nonrec abbrev _root_.Lean.Expr.FVarsIn := @FVarsIn

def VLocalDecl.WF (env : VEnv) (U : Nat) (Γ : List VExpr) : VLocalDecl → Prop
  | .vlam type => env.IsType U Γ type
  | .vlet type value => env.HasType U Γ value type

def VLCtx.FVWF : VLCtx → Prop
  | [] => True
  | (ofv, _) :: (Δ : VLCtx) =>
    VLCtx.FVWF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars)

variable (env : VEnv) (U : Nat) in
def VLCtx.WF : VLCtx → Prop
  | [] => True
  | (ofv, d) :: (Δ : VLCtx) =>
    VLCtx.WF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars) ∧
    VLocalDecl.WF env U Δ.toCtx d

theorem VLCtx.WF.fvwf : ∀ {Δ}, VLCtx.WF env U Δ → Δ.FVWF
  | [], h => h
  | _ :: _, ⟨h1, h2, _⟩ => ⟨h1.fvwf, h2⟩

/-- `appHead` commutes with `lift'` (lifting de Bruijn indices). -/
theorem VExpr.appHead_lift' {e : VExpr} {ρ : Lift} :
    (e.lift' ρ).appHead = e.appHead.lift' ρ := by
  induction e <;> simp [VExpr.appHead, lift', *]

/-- `appArgs` commutes with `lift'` (lifting de Bruijn indices). -/
theorem VExpr.appArgs_lift' {e : VExpr} {ρ : Lift} :
    (e.lift' ρ).appArgs = e.appArgs.map (·.lift' ρ) := by
  induction e
  all_goals
    (try simp [VExpr.appArgs, lift', *])
    (try {
      rename_i f a ih
      simp [VExpr.appArgs, lift']
      rw [← List.map_append]
      exact ih.trans rfl
    })

/-- `appHead` commutes with `liftN` (weakening). -/
theorem VExpr.appHead_liftN {e : VExpr} {n k : Nat} :
    (liftN n e k).appHead = e.appHead.liftN n k := by
  induction e generalizing k <;> simp [VExpr.appHead, liftN, *]

/-- `appArgs` commutes with `liftN` (weakening). -/
theorem VExpr.appArgs_liftN {e : VExpr} {n k : Nat} :
    (liftN n e k).appArgs = e.appArgs.map (liftN n · k) := by
  induction e generalizing k
  all_goals
    (try simp [VExpr.appArgs, liftN, *])
    (try {
      rename_i f a ih
      simp [VExpr.appArgs, liftN]
      rw [← List.map_append]
      exact ih.trans rfl
    })

/-- `appHead` commutes with `inst` (instantiation).

NOTE: This lemma is FALSE in general. It fails when `e = .bvar i`, `i = k`,
and `e₀` is an application, because `instVar i e₀ k = liftN k e₀` can be
an application, but `e.appHead.inst e₀ k = (.bvar i).inst e₀ k = liftN k e₀`
and `(liftN k e₀).appHead ≠ liftN k e₀` when `liftN k e₀` is an application.

However, when `e.appHead` is a constant (as in `TrProj`), the lemma holds
because the recursion in `appHead`/`appArgs` ends at the constant, not a `bvar`.
-/ 
theorem VExpr.appHead_inst_of_const {e e₀ : VExpr} {k : Nat} {C : Name} {us : List VLevel}
    (h : e.appHead = .const C us) :
    (e.inst e₀ k).appHead = .const C us := by
  induction e <;> simp_all [VExpr.appHead, inst]
  all_goals
    (try contradiction)

theorem VExpr.appArgs_inst_of_const {e e₀ : VExpr} {k : Nat} {C : Name} {us : List VLevel}
    (h : e.appHead = .const C us) :
    (e.inst e₀ k).appArgs = e.appArgs.map (·.inst e₀ k) := by
  induction e <;> simp_all [VExpr.appArgs, inst, VExpr.appHead]
  all_goals
    (try {
      rename_i f a ihf iha hf
      simp_all [VExpr.appArgs, inst]
      rw [← List.map_append]
      exact ihf hf.trans rfl
    })
    (try contradiction)

/-- `appHead` commutes with `instL` (level instantiation). -/
theorem VExpr.appHead_instL {e : VExpr} {ls : List VLevel} :
    (e.instL ls).appHead = e.appHead.instL ls := by
  induction e <;> simp [VExpr.appHead, instL, *]

/-- `appArgs` commutes with `instL` (level instantiation). -/
theorem VExpr.appArgs_instL {e : VExpr} {ls : List VLevel} :
    (e.instL ls).appArgs = e.appArgs.map (·.instL ls) := by
  induction e
  all_goals
    (try simp [VExpr.appArgs, instL, *])
    (try {
      rename_i f a ih
      simp [VExpr.appArgs, instL]
      rw [← List.map_append]
      exact ih.trans rfl
    })

/-- appHead of a constant is preserved under IsDefEq.

    PROOF STRATEGY: Mutual induction (fwd + rev) inside namespace VEnv.
    - `symm`: fwd calls rev on premise, rev calls fwd on premise
    - `beta`/`eta`: both directions derive contradiction (.lam ≠ .const)
    - All other constructors: structural analysis of appHead
    - `proofIrrel`/`extra`: need additional lemmas about proof-term/defeq heads

    BLOCKED: Cannot define recursive pattern-matching on IsDefEq from outside
    namespace VEnv (section variables break constructor resolution).
    Must be proven in Theory/Typing/Lemmas.lean inside `namespace VEnv`. -/
theorem IsDefEq.appHead_of_const
    {env : VEnv} {U : Nat} {Γ : List VExpr} {e₁ e₂ : VExpr} {C : Name} {A : VExpr}
    (hHead : e₁.appHead = .const C [])
    (hEq : env.IsDefEq U Γ e₁ e₂ A) :
    e₂.appHead = .const C [] := by
  sorry

/-- appHead is preserved under IsDefEqU when head is a constant. -/
theorem IsDefEqU.appHead_of_const
    {env : VEnv} {U : Nat} {Γ : List VExpr} {e₁ e₂ : VExpr} {C : Name}
    (hHead : e₁.appHead = .const C [])
    (hEq : env.IsDefEqU U Γ e₁ e₂) :
    e₂.appHead = .const C [] := by
  obtain ⟨A, hDeq⟩ := hEq
  exact IsDefEq.appHead_of_const hHead hDeq

/-- `appArgs[n]` is preserved under definitional equality when head is a constant.
    If e₁.appHead = .const C [], e₁ ≡ e₂, and e₁.appArgs[n] = some x,
    then e₂.appArgs[n] = some y and x ≡ y.
    
    The hHead premise is essential: without it, beta reduction could change
    the appArgs structure (e.g., (.app (.lam A e) e') has 2 appArgs but
    e.inst e' has 1 appArgs when e is a constant). -/
theorem IsDefEqU.appArgs_of_some
    {env : VEnv} {U : Nat} {Γ : List VExpr} {e₁ e₂ : VExpr} {n : Nat} {x : VExpr}
    (hHead : e₁.appHead = .const C [])
    (hSome : e₁.appArgs[n]? = some x)
    (hEq : env.IsDefEqU U Γ e₁ e₂) :
    ∃ y, e₂.appArgs[n]? = some y ∧ env.IsDefEqU U Γ x y := by
  -- Key insight: when appHead is .const, the expression is a constructor application.
  -- Constructor applications have stable appArgs under definitional equality
  -- because beta/eta reductions don't apply (head is not a lambda).
  sorry  -- TODO: Induction on IsDefEq with case-by-case reasoning

/--
`TrProj Γ s i e e'` holds when projecting the `i`-th field from structure `s`
on expression `e` yields `e'`.

For structure-like inductives (single constructor, no indices), this means:
- `e` is a constructor application with enough arguments
- `e'` is the argument at position `numParams + i` (0-indexed)

The actual number of parameters (`numParams`) is existentially quantified.
The constructor's validity in the environment is ensured by the typing context.
-/
def TrProj (Γ : List VExpr) (structName : Name) (idx : Nat) (e e' : VExpr) : Prop :=
  ∃ (C : Name) (numParams : Nat),
    e.appHead = .const C [] ∧
    (e.appArgs)[numParams + idx]? = some e'

def VEnv.ContainsLits (env : VEnv) : Literal → Prop
  | .natVal _ => env.contains ``Nat
  | .strVal _ => env.contains ``Char.ofNat ∧ env.contains ``String.ofList

variable (env : VEnv) (Us : List Name) in
inductive TrExprS : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → TrExprS Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → TrExprS Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → TrExprS Δ (.sort u) (.sort u')
  | const :
    env.constants c = some ci →
    us.mapM (VLevel.ofLevel Us) = some us' →
    us.length = ci.uvars →
    TrExprS Δ (.const c us) (.const c us')
  | app :
    env.HasType Us.length Δ.toCtx f' (.forallE A B) →
    env.HasType Us.length Δ.toCtx a' A →
    TrExprS Δ f f' → TrExprS Δ a a' → TrExprS Δ (.app f a) (.app f' a')
  | lam :
    env.IsType Us.length Δ.toCtx ty' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.lam name ty body bi) (.lam ty' body')
  | forallE :
    env.IsType Us.length Δ.toCtx ty' →
    env.IsType Us.length (ty' :: Δ.toCtx) body' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE :
    env.HasType Us.length Δ.toCtx val' ty' →
    TrExprS Δ ty ty' → TrExprS Δ val val' →
    TrExprS ((none, .vlet ty' val') :: Δ) body body' →
    TrExprS Δ (.letE name ty val body nd) body'
  | lit : env.ContainsLits l → TrExprS Δ l.toConstructor e → TrExprS Δ (.lit l) e
  | mdata : TrExprS Δ e e' → TrExprS Δ (.mdata d e) e'
  | proj : TrExprS Δ e e' → TrProj Δ.toCtx s i e' e'' → TrExprS Δ (.proj s i e) e''

def TrExpr (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (e' : VExpr) : Prop :=
  ∃ e₂, TrExprS env Us Δ e e₂ ∧ env.IsDefEqU Us.length Δ.toCtx e₂ e'

def VExpr.bool : VExpr := .const ``Bool []
def VExpr.boolTrue : VExpr := .const ``Bool.true []
def VExpr.boolFalse : VExpr := .const ``Bool.false []
def VExpr.boolLit : Bool → VExpr
  | .false => .boolFalse
  | .true => .boolTrue

def VExpr.nat : VExpr := .const ``Nat []
def VExpr.natZero : VExpr := .const ``Nat.zero []
def VExpr.natSucc : VExpr := .const ``Nat.succ []
def VExpr.natLit : Nat → VExpr
  | 0 => .natZero
  | n+1 => .app .natSucc (.natLit n)

def VExpr.char : VExpr := .const ``Char []
def VExpr.string : VExpr := .const ``String []
def VExpr.stringOfList : VExpr := .const ``String.ofList []
def VExpr.listChar : VExpr := .app (.const ``List [.zero]) .char
def VExpr.listCharNil : VExpr := .app (.const ``List.nil [.zero]) .char
def VExpr.listCharCons : VExpr := .app (.const ``List.cons [.zero]) .char
def VExpr.charOfNat : VExpr := .const ``Char.ofNat []
def VExpr.listCharLit : List Char → VExpr
  | [] => .listCharNil
  | a :: as => .app (.app .listCharCons (.app .charOfNat (.natLit a.toNat))) (.listCharLit as)

def VExpr.trLiteral : Literal → VExpr
  | .natVal n => .natLit n
  | .strVal s => .app .stringOfList (.listCharLit s.toList)

def VEnv.ReflectsNatNatNat (env : VEnv) (fc : Name) (f : Nat → Nat → Nat) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 [] (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.natLit (f a b))

def VEnv.ReflectsNatNatBool (env : VEnv) (fc : Name) (f : Nat → Nat → Bool) :=
  env.contains fc →
  ∀ a b, env.IsDefEqU 0 [] (.app (.app (.const fc []) (.natLit a)) (.natLit b)) (.boolLit (f a b))

structure VEnv.HasPrimitives (env : VEnv) : Prop where
  bool : env.contains ``Bool → env.contains ``Bool.false ∧ env.contains ``Bool.true
  boolFalse : env.constants ``Bool.false = some ci → ci = { uvars := 0, type := .bool }
  boolTrue : env.constants ``Bool.true = some ci → ci = { uvars := 0, type := .bool }
  nat : env.contains ``Nat → env.contains ``Nat.zero ∧ env.contains ``Nat.succ
  natZero : env.constants ``Nat.zero = some ci → ci = { uvars := 0, type := .nat }
  natSucc : env.constants ``Nat.succ = some ci →
    ci = { uvars := 0, type := .forallE .nat .nat }
  natAdd : env.ReflectsNatNatNat ``Nat.add Nat.add
  natSub : env.ReflectsNatNatNat ``Nat.sub Nat.sub
  natMul : env.ReflectsNatNatNat ``Nat.mul Nat.mul
  natPow : env.ReflectsNatNatNat ``Nat.pow Nat.pow
  natGcd : env.ReflectsNatNatNat ``Nat.gcd Nat.gcd
  natMod : env.ReflectsNatNatNat ``Nat.mod Nat.mod
  natDiv : env.ReflectsNatNatNat ``Nat.div Nat.div
  natBEq : env.ReflectsNatNatBool ``Nat.beq Nat.beq
  natBLE : env.ReflectsNatNatBool ``Nat.ble Nat.ble
  natLAnd : env.ReflectsNatNatNat ``Nat.land Nat.land
  natLOr : env.ReflectsNatNatNat ``Nat.lor Nat.lor
  natXor : env.ReflectsNatNatNat ``Nat.xor Nat.xor
  natShiftLeft : env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft
  natShiftRight : env.ReflectsNatNatNat ``Nat.shiftRight Nat.shiftRight
  charOfNat : env.constants ``Char.ofNat = some ci →
    ci = { uvars := 0, type := .forallE .nat .char }
  stringOfList : env.constants ``String.ofList = some ci →
    ci = { uvars := 0, type := .forallE .listChar .string } ∧
    env.HasType 0 [] .listCharNil .listChar ∧
    env.HasType 0 [] .listCharCons (.forallE .char <| .forallE .listChar .listChar)
