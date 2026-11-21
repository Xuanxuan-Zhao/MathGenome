import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompactConjugation
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsConjugations

/-! LA-J03, notes/005, lines 4695–4701 and 4716–4745.
The general correspondence between real forms and conjugations is in
`RealFormsConjugations`. -/

open scoped TensorProduct

universe u

namespace Specs.LieAlgebrasAndRepresentations.CompactRealForm

open _root_.LieAlgebrasAndRepresentations.RealForms
open CompactConjugation (CompactIndex asRoot opposite)
open ChevalleyBasis (Root)
open SerreRelations (simple)
open MaximalTori (IsMaximalToral_value)
open RootDecomposition (rootSet_value rootSpace_value)
open RootForm (coroot_value)
open SolvableRadical (IsSemisimple_value)
open TraceCriterion (killingForm_value)

/-- The compact form built from compatible Chevalley data, including the
fixed real basis and the natural scalar-extension isomorphism. -/
def compact_chevalley_real_formType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∃ (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ)
      (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H)
      (x : Root H → L) (b : Module.Basis (simple H φ ⊕ Root H) ℂ L)
      (ω : Conjugation L) (c : Module.Basis (CompactIndex H φ) ℝ ω.fixed)
      (e : (ℂ ⊗[ℝ] ω.fixed) ≃ₗ⁅ℂ⁆ L),
      IsMaximalToral_value H ∧ (∀ α ∈ rootSet_value H, φ α ≠ 0) ∧
      (∀ α, x α ∈ rootSpace_value H α.val ∧ x α ≠ 0) ∧
      (∀ α, ⁅x α, x (opposite negRoot α)⁆ = (coroot_value H α.val : L)) ∧
      (∀ α, ∃ k : ℝ, 0 < k ∧
        killingForm_value ℂ L (x α) (x (opposite negRoot α)) = (k : ℂ)) ∧
      (∀ i, b (.inl i) = (coroot_value H i.val : L)) ∧
      (∀ α, b (.inr α) = x α) ∧
      (∀ i j k, ∃ z : ℤ, b.repr ⁅b i, b j⁆ k = (z : ℂ)) ∧
      (∀ i : simple H φ,
        ω.map (coroot_value H i.val : L) = -(coroot_value H i.val : L)) ∧
      (∀ α, ω.map (x α) = -x (opposite negRoot α)) ∧
      (∀ i : simple H φ, (c (.inl i) : L) = Complex.I • (coroot_value H i.val : L)) ∧
      (∀ α, (c (.inr (.inl α)) : L) =
        x (asRoot α) - x (opposite negRoot (asRoot α))) ∧
      (∀ α, (c (.inr (.inr α)) : L) =
        Complex.I • (x (asRoot α) + x (opposite negRoot (asRoot α)))) ∧
      (∀ v w : ω.fixed, killingForm_value ℂ L (v : L) (w : L) =
        (killingForm_value ℝ ω.fixed v w : ℂ)) ∧
      (∀ v : ω.fixed, v ≠ 0 → killingForm_value ℝ ω.fixed v v < 0) ∧
      (∀ (a : ℂ) (v : ω.fixed), e (a ⊗ₜ[ℝ] v) = a • (v : L))

/-- Existence of a compact real form, expressed in the common real-form interface. -/
def compact_real_formType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∃ ω : Conjugation L, IsRealForm ω.fixed ∧
      ∀ v : ω.fixed, v ≠ 0 → killingForm_value ℝ ω.fixed v v < 0

end Specs.LieAlgebrasAndRepresentations.CompactRealForm
