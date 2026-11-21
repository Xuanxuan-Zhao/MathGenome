import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.RegularQuotient
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Independent statement of the regular minimal-generator reduction in CM-19.
The residue field is the original R/m, with its actual induced R/(x)-action.
The equality to the natural number n-1 includes finiteness over R/(x). -/

universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay

lemma residueField_quotient_torsion {R : Type u} [CommRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    Module.IsTorsionBySet R (IsLocalRing.ResidueField R) (Ideal.span {x}) := by
  rw [Module.isTorsionBySet_iff_subset_annihilator]
  change Ideal.span {x} ≤ Module.annihilator R (R ⧸ IsLocalRing.maximalIdeal R)
  rw [Ideal.annihilator_quotient]
  exact Ideal.span_le.mpr (by simpa using hx)

/-- The quotient action on the original residue field, induced by R/(x) → R/m. -/
@[instance_reducible] noncomputable def residueFieldQuotientModule
    {R : Type u} [CommRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    Module (R ⧸ Ideal.span {x}) (IsLocalRing.ResidueField R) :=
  (residueField_quotient_torsion x hx).module

namespace Specs

def residueField_projectiveDimension_quotientType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ), 0 < n →
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (n : WithBot ℕ∞) →
    ∀ (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R),
      x ∉ (IsLocalRing.maximalIdeal R) ^ 2 → IsSMulRegular R x →
      letI := residueFieldQuotientModule x hx
      projectiveDimension (ModuleCat.of (R ⧸ Ideal.span {x})
        (IsLocalRing.ResidueField R)) = ((n - 1 : ℕ) : WithBot ℕ∞)

end Specs
end AdvCommAlg.CohenMacaulay
