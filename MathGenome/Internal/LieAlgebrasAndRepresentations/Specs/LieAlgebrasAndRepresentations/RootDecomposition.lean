import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.MaximalTori
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.KillingCriterion
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! LA-D02, notes/005/lie-algebras-and-representations.tex, lines 1619–1644.
The standing hypotheses are at lines 1546–1553. Root spaces here are ordinary
simultaneous eigenspaces, indexed by the complex linear dual of H. The set of
roots excludes zero. Option indexes the Cartan summand together with the root
summands, so IsInternal expresses the displayed direct-sum decomposition,
including when L is the zero algebra. -/

universe u
namespace Specs.LieAlgebrasAndRepresentations.RootDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- All weights, including zero and weights absent from the root set. -/
def rootSpace_value (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) : Submodule ℂ L :=
  (LieModule.weightSpace L α).toSubmodule

def rootSpace_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  (H : LieSubalgebra ℂ L), Module.Dual ℂ H → Submodule ℂ L

def rootSet_value (H : LieSubalgebra ℂ L) : Set (Module.Dual ℂ H) :=
  {α | α ≠ 0 ∧ rootSpace_value H α ≠ ⊥}

def rootSet_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  (H : LieSubalgebra ℂ L), Set (Module.Dual ℂ H)

def rootSummand_value (H : LieSubalgebra ℂ L) :
    Option (rootSet_value H) → Submodule ℂ L
  | none => H.toSubmodule
  | some α => rootSpace_value H α.val

def rootSummand_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  (H : LieSubalgebra ℂ L), Option (rootSet_value H) → Submodule ℂ L

noncomputable def rootPairing_value (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) :
    rootSpace_value H α →ₗ[ℂ] Module.Dual ℂ (rootSpace_value H (-α)) :=
  (TraceCriterion.killingForm_value ℂ L).domRestrict₁₂
    (rootSpace_value H α) (rootSpace_value H (-α))

def rootPairing_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H),
    rootSpace_value H α →ₗ[ℂ] Module.Dual ℂ (rootSpace_value H (-α))

def mem_rootSpace_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) (x : L),
    x ∈ rootSpace_value H α ↔ ∀ h : H, ⁅(h : L), x⁆ = α h • x

def rootSet_finite_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L), MaximalTori.IsToral_value H → (rootSet_value H).Finite

def rootSpace_zero_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H →
      rootSpace_value H 0 = H.toSubmodule

def root_decomposition_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H →
      letI : DecidableEq (Option (rootSet_value H)) := Classical.decEq _
      DirectSum.IsInternal (rootSummand_value H)

def rootSpace_eq_bot_of_not_mem_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H),
    α ≠ 0 → α ∉ rootSet_value H → rootSpace_value H α = ⊥

def rootSpace_bracket_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L) (α β : Module.Dual ℂ H) (x y : L),
    x ∈ rootSpace_value H α → y ∈ rootSpace_value H β →
      ⁅x, y⁆ ∈ rootSpace_value H (α + β)

def rootSpace_killing_orthogonal_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (α β : Module.Dual ℂ H) (x y : L),
    x ∈ rootSpace_value H α → y ∈ rootSpace_value H β → α + β ≠ 0 →
      TraceCriterion.killingForm_value ℂ L x y = 0

def rootPairing_perfect_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H →
      ∀ α : Module.Dual ℂ H, (rootPairing_value H α).IsPerfPair

def killingForm_restrict_toral_nondegenerate_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ H : LieSubalgebra ℂ L, MaximalTori.IsMaximalToral_value H →
      ((TraceCriterion.killingForm_value ℂ L).restrict H.toSubmodule).Nondegenerate

end Specs.LieAlgebrasAndRepresentations.RootDecomposition
