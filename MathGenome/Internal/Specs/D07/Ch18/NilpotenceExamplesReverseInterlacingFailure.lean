import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
import MathGenome.Internal.Specs.D07.Ch18.NilpotenceCriteria

/-! The reverse-interlacing counterexample of paper.tex:5213–5227.
The dihedral group is the full group of plane isometries preserving an octagon,
with arbitrary center and nonzero first-vertex displacement. The equivalence
below identifies its generators with the actual rotation and reflection.
`C₂` is the additive cyclic group Z/2Z, written multiplicatively.
Lower terms use γ₁ = G; exact class means least upper-series termination.
-/
noncomputable section
namespace Specs.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure

open Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
open Specs.D07.Ch18.CentralSeries Specs.D07.Ch18.NilpotenceCriteria
open scoped ComplexConjugate

abbrev Octagon (c a : ℂ) := symmetryGroup (vertices 8 c a)
abbrev C₂ := Multiplicative (ZMod 2)

/-- All computations in the actual geometric group, and its product with C₂. -/
def GeometricCounterexample : Prop :=
  ∀ (c a : ℂ), a ≠ 0 →
    Finite (Octagon c a) ∧ Nat.card (Octagon c a) = 16 ∧
    ∃ e : DihedralGroup 8 ≃* Octagon c a,
      let r := e (DihedralGroup.r 1)
      let s := e (DihedralGroup.sr 0)
      (∀ z : ℂ, (r : ℂ ≃ᵢ ℂ) z = c + root 8 * (z - c)) ∧
      (∀ z : ℂ, (s : ℂ ≃ᵢ ℂ) z = c + a * conj ((z - c) / a)) ∧
      r ^ 8 = 1 ∧ s ^ 2 = 1 ∧ s * r * s = r⁻¹ ∧
      lowerValue (Octagon c a) 2 = Subgroup.zpowers (r ^ 2) ∧
      lowerValue (Octagon c a) 3 = Subgroup.zpowers (r ^ 4) ∧
      lowerValue (Octagon c a) 4 = ⊥ ∧
      hasClassValue (Octagon c a) 3 ∧
      hasClassValue (Octagon c a × C₂) 3 ∧
      (⊥ : Subgroup (Octagon c a)).prod (⊤ : Subgroup C₂) ≤
        upperValue (Octagon c a × C₂) 1 ∧
      lowerValue (Octagon c a × C₂) 2 =
        (Subgroup.zpowers (r ^ 2)).prod (⊥ : Subgroup C₂) ∧
      ¬ upperValue (Octagon c a × C₂) 1 ≤ lowerValue (Octagon c a × C₂) 2

end Specs.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure
