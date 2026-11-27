import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.EmbeddingProblem

/-! Proposition IG02 for the absolute Galois group of a chosen separable closure. -/

namespace Specs.GaloisFormalization.IG

open GH.KrullLayers

universe u v w x

noncomputable section

variable {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
variable {B : Type w} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]

/-- The problem with the prescribed restriction as its lower map. -/
def prescribedProblem (E : FiniteGaloisIntermediateField k Ω)
    (π : B →ₜ* Gal(E/k)) (hπ : Function.Surjective π) :
    FiniteEmbeddingProblem Gal(Ω/k) B Gal(E/k) where
  rho := restrict E
  pi := π
  rho_surjective := by
    change Function.Surjective (AlgEquiv.restrictNormalHom E.toIntermediateField :
      Gal(Ω/k) →* Gal(E/k))
    exact AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := E.toIntermediateField) Ω
  pi_surjective := hπ

set_option linter.checkUnivs false in
def prescribedProblem_type :=
  ∀ {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    {B : Type w} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (E : FiniteGaloisIntermediateField k Ω)
    (π : B →ₜ* Gal(E/k)), Function.Surjective π →
      FiniteEmbeddingProblem Gal(Ω/k) B Gal(E/k)

/-- A weak solution factors through the finite Galois group of its kernel's fixed field. -/
def weakSolution_fixedField_type : Prop :=
  ∀ {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    {B : Type w} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (E : FiniteGaloisIntermediateField k Ω)
    (π : B →ₜ* Gal(E/k)) (hπ : Function.Surjective π)
    (s : (prescribedProblem E π hπ).WeakSolution),
    ∃ (L : FiniteGaloisIntermediateField k Ω) (hEL : E ≤ L) (ι : Gal(L/k) →* B),
      L.toIntermediateField = IntermediateField.fixedField s.lift.toMonoidHom.ker ∧
      Function.Injective ι ∧
      π.toMonoidHom.comp ι = (transition hEL).toMonoidHom ∧
      ι.comp (restrict L).toMonoidHom = s.lift.toMonoidHom ∧
      (FiniteEmbeddingProblem.isProperValue s ↔ ∃ e : Gal(L/k) ≃* B, e.toMonoidHom = ι)

/-- Composing the injection with restriction gives a weak solution with the indicated field. -/
def weakSolution_of_extension_type : Prop :=
  ∀ {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    {B : Type w} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (E : FiniteGaloisIntermediateField k Ω)
    (π : B →ₜ* Gal(E/k)) (hπ : Function.Surjective π)
    (L : FiniteGaloisIntermediateField k Ω) (hEL : E ≤ L) (ι : Gal(L/k) →* B),
    Function.Injective ι → π.toMonoidHom.comp ι = (transition hEL).toMonoidHom →
    ∃ s : (prescribedProblem E π hπ).WeakSolution,
      s.lift.toMonoidHom = ι.comp (restrict L).toMonoidHom ∧
      L.toIntermediateField = IntermediateField.fixedField s.lift.toMonoidHom.ker ∧
      (FiniteEmbeddingProblem.isProperValue s ↔ ∃ e : Gal(L/k) ≃* B, e.toMonoidHom = ι)

/-- The prescribed quotient is trivial exactly for the base field. -/
def layerGroup_subsingleton_iff_type : Prop :=
  ∀ {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (E : FiniteGaloisIntermediateField k Ω), Subsingleton Gal(E/k) ↔
    E = (⊥ : FiniteGaloisIntermediateField k Ω)

/-- With trivial prescribed quotient, proper solutions are precisely realizations of the group. -/
def properSolution_iff_realization_type : Prop :=
  ∀ {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    {B : Type w} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (E : FiniteGaloisIntermediateField k Ω) [Subsingleton Gal(E/k)]
    (π : B →ₜ* Gal(E/k)) (hπ : Function.Surjective π),
    (∃ s : (prescribedProblem E π hπ).WeakSolution, FiniteEmbeddingProblem.isProperValue s) ↔
      ∃ L : FiniteGaloisIntermediateField k Ω, Nonempty (Gal(L/k) ≃* B)

/-- A finite Galois realization can be transported into the chosen separable closure. -/
def realization_in_separableClosure_type : Prop :=
  ∀ {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    {B : Type w} [Group B]
    (K : Type x) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K],
    (Gal(K/k) ≃* B) → ∃ L : FiniteGaloisIntermediateField k Ω,
      Nonempty (K ≃ₐ[k] L) ∧ Nonempty (Gal(L/k) ≃* B)

end

end Specs.GaloisFormalization.IG
