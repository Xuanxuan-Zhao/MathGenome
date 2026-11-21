import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergData
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleTotalization

/-! HA-G00: the Cartan–Eilenberg definition, with the signed totalization
of HA-B01. The four resolutions use the augmentation of the same bicomplex. -/

universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace AdvancedHomologicalAlgebra.CartanEilenbergData

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A bounded below Cartan–Eilenberg injective double resolution of K.
In particular, boundaries, cycles and cohomology are resolved with their
induced augmentations, in addition to the individual terms of K. -/
def CartanEilenbergResolution (K : CochainComplex C ℤ) := ResolutionData K

/-- Boundedness of the input follows from the horizontal support bound
and the monic augmentation of each term. -/
theorem sourceBoundedBelow : Specs.SourceBoundedBelow.{v, u} := by
  intro C _ _ K R
  obtain ⟨L, hL⟩ := R.boundedBelow
  refine ⟨L, fun p hp => ?_⟩
  have : Mono (R.augmentation.f p) := (R.terms p).mono
  exact IsZero.of_mono (R.augmentation.f p) (hL p 0 hp)

/-- The total complex uses the fixed commuting convention of HA-B01. -/
noncomputable def totalComplex {K : CochainComplex C ℤ} (R : CartanEilenbergResolution K)
    [R.bicomplex.HasTotal (ComplexShape.up ℤ)] : CochainComplex C ℤ :=
  DoubleTotalization.totalSum R.bicomplex

/-- The component formula makes the sign (-1)^p explicit. -/
theorem totalDifferential : Specs.TotalDifferential.{v, u} := by
  intro C _ _ K R _ p q
  exact DoubleTotalization.sumDifferential R.bicomplex p (p + 1) q (q + 1)
    (p + q) (p + q + 1) rfl rfl rfl (by omega) (by omega)

end AdvancedHomologicalAlgebra.CartanEilenbergData
