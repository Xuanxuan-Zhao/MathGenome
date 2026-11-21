import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.Submodule

/-! CM-15, paper.tex:3771–3777 and 3819–3830.
`EssFiniteType k K` for fields means finite generation as a field, as
proved by `IntermediateField.fg_top_iff`. No separability is required.
The tensor product has its canonical commutative ring structure, including
when the coefficient algebra is the zero ring. -/
universe u
open scoped TensorProduct
namespace AdvCommAlg.CohenMacaulay.Specs

/-- Noetherianness is independent of the CM assertion. -/
def finitelyGeneratedFieldExtension_noetherianType : Prop :=
  ∀ (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [IsNoetherianRing R]
    [Algebra.EssFiniteType k K], IsNoetherianRing (R ⊗[k] K)

/-- Canonical Noetherianness used only to type the CM predicate below. -/
theorem fieldTensorNoetherian (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [IsNoetherianRing R]
    [Algebra.EssFiniteType k K] : IsNoetherianRing (R ⊗[k] K) :=
  Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)

noncomputable def finitelyGeneratedFieldExtension_cohenMacaulay_iffType : Prop :=
  ∀ (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [IsNoetherianRing R]
    [Algebra.EssFiniteType k K],
  letI := fieldTensorNoetherian k R K
  CohenMacaulayRingValue (R ⊗[k] K) ↔ CohenMacaulayRingValue R

end AdvCommAlg.CohenMacaulay.Specs
