import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanData
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Existence, uniqueness up to isomorphism, and the common kernel of a minimal realization. -/

namespace LieNotes.Contragredient

universe u v w

variable {I : Type u} [Fintype I] {A : Matrix I I ℤ}
variable {H : Type v} [AddCommGroup H] [Module ℂ H]
variable {H' : Type w} [AddCommGroup H'] [Module ℂ H']

private theorem independent_iff_surjective_evaluation (α : I → Module.Dual ℂ H) :
    LinearIndependent ℂ α ↔ Function.Surjective (LinearMap.pi α) := by
  let f := LinearMap.ltoFun ℂ H ℂ ℂ
  have hf : Function.Injective f := fun _ _ e => LinearMap.ext (congrFun e)
  rw [← LinearMap.range_eq_top, ← Submodule.span_eq (LinearMap.range (LinearMap.pi α)),
    LinearMap.coe_range]
  change LinearIndependent ℂ α ↔
    Submodule.span ℂ (Set.range (flip (f ∘ α))) = ⊤
  rw [span_flip_eq_top_iff_linearIndependent]
  exact ⟨fun h => h.map' f (LinearMap.ker_eq_bot.mpr hf), LinearIndependent.of_comp f⟩

/-- The map sending the formal coroot basis to the rows of the complex Cartan matrix. -/
private noncomputable def cartanRowMap (A : Matrix I I ℤ) : (I →₀ ℂ) →ₗ[ℂ] I → ℂ :=
  Finsupp.linearCombination ℂ (A.map fun a : ℤ => (a : ℂ)).row

private theorem model_finrank (E : Submodule ℂ (I → ℂ))
    (hE : IsCompl (LinearMap.range (cartanRowMap A)) E) :
    Module.finrank ℂ ((I →₀ ℂ) × E) = 2 * Fintype.card I - (A.map fun a : ℤ => (a : ℂ)).rank := by
  have h := Submodule.finrank_add_eq_of_isCompl hE
  rw [cartanRowMap, Finsupp.range_linearCombination, ← Matrix.rank_eq_finrank_span_row,
    Module.finrank_pi] at h
  rw [Module.finrank_prod, Module.finrank_finsupp_self]
  omega

/-- Adjoin a complement of the row space to the space with formal coroot basis. -/
theorem exists_minimal_realization (_hA : IsGeneralizedCartanMatrix A) :
    ∃ (H : Type u) (add : AddCommGroup H) (mod : @Module ℂ H _ add.toAddCommMonoid),
      letI := add
      letI := mod
      ∃ R : Realization A H, R.IsMinimal := by
  obtain ⟨E, hE⟩ := (LinearMap.range (cartanRowMap A)).exists_isCompl
  let T := (cartanRowMap A).coprod E.subtype
  have hT : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, Submodule.range_subtype]
    exact hE.sup_eq_top
  let R : Realization A ((I →₀ ℂ) × E) :=
    { h := fun i => (Finsupp.single i 1, 0)
      α := fun i => (LinearMap.proj (R := ℂ) i).comp T
      h_independent :=
        (Finsupp.linearIndependent_single_one (ι := I) (R := ℂ)).map' (LinearMap.inl ℂ (I →₀ ℂ) E)
          (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
      α_independent := (independent_iff_surjective_evaluation _).mpr hT
      pairing := fun i j => by
        change ((cartanRowMap A).coprod E.subtype (Finsupp.single i 1, 0)) j = _
        simp [cartanRowMap, Finsupp.linearCombination_single, Matrix.row_apply] }
  exact ⟨_, inferInstance, inferInstance, R, inferInstance, model_finrank E hE⟩

/-- A section of the evaluation on a complement gives coordinates in the same model
for every minimal realization. -/
private theorem equiv_model (R : Realization A H) (hR : R.IsMinimal)
    (E : Submodule ℂ (I → ℂ)) (hE : IsCompl (LinearMap.range (cartanRowMap A)) E) :
    ∃ e : ((I →₀ ℂ) × E) ≃ₗ[ℂ] H,
      (∀ i, e (Finsupp.single i 1, 0) = R.h i) ∧
      ∀ x, LinearMap.pi R.α (e x) = (cartanRowMap A).coprod E.subtype x := by
  let : FiniteDimensional ℂ H := hR.1
  let T := LinearMap.pi R.α
  have hT : Function.Surjective T := (independent_iff_surjective_evaluation _).mp R.α_independent
  obtain ⟨s, hs⟩ := T.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hT)
  let J := Finsupp.linearCombination ℂ R.h
  let F := J.coprod (s.comp E.subtype)
  have hrows : T ∘ R.h = (A.map fun a : ℤ => (a : ℂ)).row := by
    funext i j
    exact R.pairing i j
  have hF (x : (I →₀ ℂ) × E) :
      T (F x) = (cartanRowMap A).coprod E.subtype x := by
    change T (J x.1 + s x.2) = cartanRowMap A x.1 + (x.2 : I → ℂ)
    rw [map_add, Finsupp.apply_linearCombination, hrows]
    exact congrArg (cartanRowMap A x.1 + ·) (DFunLike.congr_fun hs (x.2 : I → ℂ))
  have hF_inj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hy : cartanRowMap A x.1 + (x.2 : I → ℂ) = 0 := by
      simpa only [hF, LinearMap.coprod_apply, Submodule.subtype_apply, map_zero] using
        congrArg T hx
    have hx₂ : x.2 = 0 := by
      have hm : (x.2 : I → ℂ) ∈ LinearMap.range (cartanRowMap A) := by
        rw [add_comm, add_eq_zero_iff_eq_neg] at hy
        rw [hy]
        exact Submodule.neg_mem _ ⟨x.1, rfl⟩
      exact Subtype.ext (Submodule.disjoint_def.mp hE.disjoint _ hm x.2.property)
    have hx₁ : J x.1 = 0 := by simpa [F, hx₂] using hx
    exact Prod.ext (R.h_independent.finsuppLinearCombination_injective
      (hx₁.trans J.map_zero.symm)) hx₂
  have hdim : Module.finrank ℂ ((I →₀ ℂ) × E) = Module.finrank ℂ H :=
    (model_finrank E hE).trans hR.2.symm
  have hF_surj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hF_inj
  refine ⟨LinearEquiv.ofBijective F ⟨hF_inj, hF_surj⟩, ?_, hF⟩
  intro i
  change F (Finsupp.single i 1, 0) = R.h i
  simp [F, J]

/-- Any two minimal realizations give the same labelled Cartan data up to isomorphism. -/
theorem minimal_realization_equiv (R : Realization A H) (R' : Realization A H')
    (hR : R.IsMinimal) (hR' : R'.IsMinimal) :
    ∃ e : H ≃ₗ[ℂ] H',
      (∀ i, e (R.h i) = R'.h i) ∧ (∀ i, (R'.α i).comp e.toLinearMap = R.α i) := by
  obtain ⟨E, hE⟩ := (LinearMap.range (cartanRowMap A)).exists_isCompl
  obtain ⟨e, he, hα⟩ := equiv_model R hR E hE
  obtain ⟨e', he', hα'⟩ := equiv_model R' hR' E hE
  refine ⟨e.symm.trans e', ?_, ?_⟩
  · intro i
    change e' (e.symm (R.h i)) = R'.h i
    rw [← he i, e.symm_apply_apply, he' i]
  · intro i
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    change R'.α i (e' (e.symm (e y))) = R.α i (e y)
    rw [e.symm_apply_apply]
    exact congrFun ((hα' y).trans (hα y).symm) i

/-- Rank-nullity for the evaluation map computes the dimension of the common root kernel. -/
theorem minimal_realization_common_kernel_finrank (R : Realization A H) (hR : R.IsMinimal) :
    Module.finrank ℂ ↥(⨅ i, LinearMap.ker (R.α i)) =
      Fintype.card I - (A.map fun a : ℤ => (a : ℂ)).rank := by
  let : FiniteDimensional ℂ H := hR.1
  have hT := (independent_iff_surjective_evaluation _).mp R.α_independent
  have h := (LinearMap.pi R.α).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hT, finrank_top, Module.finrank_pi, LinearMap.ker_pi, hR.2] at h
  omega

end LieNotes.Contragredient
