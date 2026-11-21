import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FinitelyGeneratedFieldExtension
import Mathlib.RingTheory.TensorProduct.Finite

/-! CM-15: the full disjunction for scalar extension by an arbitrary field.
Finite type refers to algebra generation; `EssFiniteType k K` for the
field extension is equivalent to finite generation as a field. -/
universe u
open scoped TensorProduct
namespace AdvCommAlg.CohenMacaulay.Specs

def fieldExtension_noetherianType : Prop :=
  ∀ (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [IsNoetherianRing R],
    Algebra.FiniteType k R ∨ Algebra.EssFiniteType k K →
    IsNoetherianRing (R ⊗[k] K)

/-- Noetherianness used to type the original CM assertion. -/
theorem fieldExtensionTensorNoetherian (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [IsNoetherianRing R]
    (h : Algebra.FiniteType k R ∨ Algebra.EssFiniteType k K) :
    IsNoetherianRing (R ⊗[k] K) := by
  rcases h with h | h
  · letI := h
    letI : IsNoetherianRing (K ⊗[k] R) := Algebra.EssFiniteType.isNoetherianRing K _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k K R).toRingEquiv
  · letI := h
    exact fieldTensorNoetherian k R K

noncomputable def fieldExtension_cohenMacaulay_iffType : Prop :=
  ∀ (k R K : Type u) [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [IsNoetherianRing R]
    (h : Algebra.FiniteType k R ∨ Algebra.EssFiniteType k K),
    letI := fieldExtensionTensorNoetherian k R K h
    CohenMacaulayRingValue (R ⊗[k] K) ↔ CohenMacaulayRingValue R

end AdvCommAlg.CohenMacaulay.Specs
