import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorMonoidal
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.BoundedAboveFlatTensor

/-! Bounded-above complexes of flat modules are K-flat. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits

universe u

/-- A bounded-above cochain complex with flat terms tensors every acyclic
cochain complex to an acyclic complex. -/
theorem boundedAboveFlat_isKFlat (R : Type u) [CommRing R] (F : Comp.{u} R)
    (hflat : ∀ q : ℤ, Module.Flat R (F.X q))
    (hbound : ∃ N : ℤ, ∀ q : ℤ, N < q → IsZero (F.X q)) :
    IsKFlat F := by
  obtain ⟨N, hN⟩ := hbound
  have hle : F.IsStrictlyLE N := (CochainComplex.isStrictlyLE_iff F N).2 hN
  intro A hA
  have h : (tensorComplex F A).Acyclic :=
    CommutativeAlgebraNotes.boundedAboveFlatTensorAcyclic R F hflat ⟨N, hle⟩ A hA
  intro n
  exact (h n).of_iso (cochainTensorBraiding F A)

end DerivedFormalization
