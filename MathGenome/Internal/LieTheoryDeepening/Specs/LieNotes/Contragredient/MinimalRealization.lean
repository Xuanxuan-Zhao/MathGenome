import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanData

/-! The three conclusions of the minimal realization lemma over `ℂ`. -/

namespace Specs.LieNotes.Contragredient.MinimalRealization

open CartanData

universe u v w

/-- Every generalized Cartan matrix has a minimal realization over `ℂ`. -/
def ExistsMinimalRealization : Prop :=
  ∀ {I : Type u} [Fintype I] {A : Matrix I I ℤ}, IsGeneralizedCartanMatrix A →
    ∃ (H : Type u) (add : AddCommGroup H) (mod : @Module ℂ H _ add.toAddCommMonoid),
      letI := add
      letI := mod
      ∃ R : Realization A H, R.IsMinimal

/-- Minimal realizations of the same matrix are isomorphic with their labelled coroots and roots. -/
def MinimalRealizationEquiv : Prop :=
  ∀ {I : Type u} [Fintype I] {A : Matrix I I ℤ}
    {H : Type v} [AddCommGroup H] [Module ℂ H]
    {H' : Type w} [AddCommGroup H'] [Module ℂ H']
    (R : Realization A H) (R' : Realization A H'), R.IsMinimal → R'.IsMinimal →
    ∃ e : H ≃ₗ[ℂ] H',
      (∀ i, e (R.h i) = R'.h i) ∧ (∀ i, (R'.α i).comp e.toLinearMap = R.α i)

/-- The intersection of the root kernels has dimension the corank of the Cartan matrix. -/
def MinimalRealizationCommonKernelFinrank : Prop :=
  ∀ {I : Type u} [Fintype I] {A : Matrix I I ℤ}
    {H : Type v} [AddCommGroup H] [Module ℂ H] (R : Realization A H), R.IsMinimal →
    Module.finrank ℂ ↥(⨅ i, LinearMap.ker (R.α i)) =
      Fintype.card I - (A.map fun a : ℤ => (a : ℂ)).rank

end Specs.LieNotes.Contragredient.MinimalRealization
