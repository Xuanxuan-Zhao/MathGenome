import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ChevalleyBasis
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.LinearAlgebra.BilinearMap

/-! The Lie-algebra assertions of the compact-form lemma (notes/005,
supp:compact-form-flag). -/

universe u

namespace Specs.LieAlgebrasAndRepresentations.CompactConjugation

open ChevalleyBasis RootDecomposition RootForm SerreRelations
open scoped ComplexConjugate

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The original bracket with scalars restricted to the reals. -/
@[reducible] def realLieAlgebra : LieAlgebra ℝ L where
  toModule := Module.complexToReal L
  lie_smul r x y := show ⁅x, (r : ℂ) • y⁆ = (r : ℂ) • ⁅x, y⁆ from lie_smul _ _ _

attribute [local instance] realLieAlgebra

abbrev ConjugateMap (L : Type u) [LieRing L] [LieAlgebra ℂ L] := L →ₗ⋆[ℂ] L

def PreservesBracket (τ : ConjugateMap L) : Prop :=
  ∀ v w, τ ⁅v, w⁆ = ⁅τ v, τ w⁆

/-- The fixed points with their induced real Lie algebra structure. -/
def fixed (τ : ConjugateMap L) (hτ : PreservesBracket τ) : LieSubalgebra ℝ L where
  carrier := {v | τ v = v}
  zero_mem' := map_zero τ
  add_mem' hv hw := (map_add τ _ _).trans (congrArg₂ (· + ·) hv hw)
  smul_mem' r v hv := by
    change τ ((r : ℂ) • v) = (r : ℂ) • v
    rw [map_smulₛₗ]
    change conj (r : ℂ) • τ v = (r : ℂ) • v
    exact congrArg₂ (· • ·) (Complex.conj_ofReal r) hv
  lie_mem' hv hw := (hτ _ _).trans (congrArg₂ (fun v w : L => ⁅v, w⁆) hv hw)

@[simp] theorem mem_fixed (τ : ConjugateMap L) (hτ : PreservesBracket τ) (v : L) :
    v ∈ fixed τ hτ ↔ τ v = v := Iff.rfl

abbrev PositiveRoot (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :=
  positive H φ

abbrev CompactIndex (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) :=
  simple H φ ⊕ (PositiveRoot H φ ⊕ PositiveRoot H φ)

def asRoot {H : LieSubalgebra ℂ L} {φ : Module.Dual ℂ H →ₗ[ℝ] ℝ}
    (α : PositiveRoot H φ) : Root H := ⟨α.val, α.property.1⟩

def opposite {H : LieSubalgebra ℂ L}
    (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H) (α : Root H) : Root H :=
  ⟨-α.val, negRoot α⟩

/-- The underlying real vector subspace of the standard Borel. -/
noncomputable def borelReal (H : LieSubalgebra ℂ L) (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ) : Submodule ℝ L :=
  (H.toSubmodule ⊔ ⨆ α : PositiveRoot H φ, rootSpace_value H α.val).restrictScalars ℝ

/-- Linear in the first variable and conjugate-linear in the second. -/
noncomputable def hermitian (τ : ConjugateMap L) : L →ₗ[ℂ] L →ₗ⋆[ℂ] ℂ :=
  -(TraceCriterion.killingForm_value ℂ L).compl₂ τ

def constructionType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (φ : Module.Dual ℂ H →ₗ[ℝ] ℝ), (∀ α ∈ rootSet_value H, φ α ≠ 0) →
    ∃ (negRoot : ∀ α : Root H, -α.val ∈ rootSet_value H)
      (x : Root H → L)
      (b : Module.Basis (simple H φ ⊕ Root H) ℂ L)
      (τ : ConjugateMap L) (hτ : PreservesBracket τ)
      (c : Module.Basis (CompactIndex H φ) ℝ (fixed τ hτ)),
      (∀ α, x α ∈ rootSpace_value H α.val ∧ x α ≠ 0) ∧
      (∀ α, ⁅x α, x (opposite negRoot α)⁆ = (coroot_value H α.val : L)) ∧
      (∀ i, b (.inl i) = (coroot_value H i.val : L)) ∧
      (∀ α, b (.inr α) = x α) ∧
      (∀ i j k, ∃ z : ℤ, b.repr ⁅b i, b j⁆ k = (z : ℂ)) ∧
      Function.Involutive τ ∧
      (∀ i : simple H φ, τ (coroot_value H i.val : L) = -(coroot_value H i.val : L)) ∧
      (∀ α, τ (x α) = -x (opposite negRoot α)) ∧
      (∀ i : simple H φ, (c (.inl i) : L) = Complex.I • (coroot_value H i.val : L)) ∧
      (∀ α, (c (.inr (.inl α)) : L) = x (asRoot α) - x (opposite negRoot (asRoot α))) ∧
      (∀ α, (c (.inr (.inr α)) : L) = Complex.I • (x (asRoot α) + x (opposite negRoot (asRoot α)))) ∧
      (∀ v w : fixed τ hτ, TraceCriterion.killingForm_value ℂ L (v : L) (w : L) =
        (TraceCriterion.killingForm_value ℝ (fixed τ hτ) v w : ℂ)) ∧
      (∀ v : fixed τ hτ, v ≠ 0 → TraceCriterion.killingForm_value ℝ (fixed τ hτ) v v < 0) ∧
      (∀ v w, hermitian τ v w = conj (hermitian τ w v)) ∧
      (∀ v : L, v ≠ 0 → 0 < (hermitian τ v v).re) ∧
      ∀ ψ : Module.Dual ℂ H →ₗ[ℝ] ℝ, (∀ α ∈ rootSet_value H, ψ α ≠ 0) →
        (fixed τ hτ).toSubmodule ⊔ borelReal H ψ = ⊤

/-- Existence without choosing a Cartan subalgebra or positive roots in advance. -/
def existsCompactConjugationType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∃ (H : LieSubalgebra ℂ L) (_ : MaximalTori.IsMaximalToral_value H)
      (τ : ConjugateMap L) (hτ : PreservesBracket τ),
      Function.Involutive τ ∧
      (∀ v : fixed τ hτ, v ≠ 0 → TraceCriterion.killingForm_value ℝ (fixed τ hτ) v v < 0) ∧
      (∀ v w, hermitian τ v w = conj (hermitian τ w v)) ∧
      (∀ v : L, v ≠ 0 → 0 < (hermitian τ v v).re) ∧
      ∀ ψ : Module.Dual ℂ H →ₗ[ℝ] ℝ, (∀ α ∈ rootSet_value H, ψ α ≠ 0) →
        (fixed τ hτ).toSubmodule ⊔ borelReal H ψ = ⊤

end Specs.LieAlgebrasAndRepresentations.CompactConjugation
