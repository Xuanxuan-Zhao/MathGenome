import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.EmbeddingProblem
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The prescribed quotient extension of a finite embedding problem. -/

namespace GaloisFormalization.IG

open GH.KrullLayers IntermediateField

universe u v w x

noncomputable section

variable {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
variable {B : Type w} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]

/-- The finite embedding problem with the actual restriction to the prescribed layer. -/
def prescribedProblem (E : FiniteGaloisIntermediateField k Ω)
    (π : B →ₜ* Gal(E/k)) (hπ : Function.Surjective π) :
    FiniteEmbeddingProblem Gal(Ω/k) B Gal(E/k) where
  rho := restrict E
  pi := π
  rho_surjective := restrict_surjective E
  pi_surjective := hπ

variable (E : FiniteGaloisIntermediateField k Ω)
  (π : B →ₜ* Gal(E/k)) (hπ : Function.Surjective π)

private theorem surjective_iff_equiv {G H : Type*} [Group G] [Group H]
    (ι : G →* H) (hi : Function.Injective ι) :
    Function.Surjective ι ↔ ∃ e : G ≃* H, e.toMonoidHom = ι := by
  constructor
  · intro hs
    exact ⟨MulEquiv.ofBijective ι ⟨hi, hs⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.surjective

/-- The fixed field of the kernel of a weak solution is its finite Galois solution field. -/
theorem weakSolution_fixedField (s : (prescribedProblem E π hπ).WeakSolution) :
    ∃ (L : FiniteGaloisIntermediateField k Ω) (hEL : E ≤ L) (ι : Gal(L/k) →* B),
      L.toIntermediateField = fixedField s.lift.toMonoidHom.ker ∧
      Function.Injective ι ∧
      π.toMonoidHom.comp ι = (transition hEL).toMonoidHom ∧
      ι.comp (restrict L).toMonoidHom = s.lift.toMonoidHom ∧
      (s.IsProper ↔ ∃ e : Gal(L/k) ≃* B, e.toMonoidHom = ι) := by
  let f := s.lift.toMonoidHom
  have hopen : IsOpen (f.ker : Set Gal(Ω/k)) :=
    (isOpen_discrete ({1} : Set B)).preimage s.lift.continuous
  have hfix : (fixedField f.ker).fixingSubgroup = f.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨f.ker, f.ker.isClosed_of_isOpen hopen⟩
  have hfield : FiniteDimensional k (fixedField f.ker) ∧ IsGalois k (fixedField f.ker) := by
    apply (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois _).mp
    rw [hfix]
    exact ⟨hopen, inferInstance⟩
  let L : FiniteGaloisIntermediateField k Ω :=
    { toIntermediateField := fixedField f.ker
      finiteDimensional := hfield.1
      isGalois := hfield.2 }
  have hker : layerKernel L = f.ker := hfix
  have hEL : E ≤ L := by
    apply layerKernel_le_iff.mp
    rw [hker, ← restrict_ker]
    intro σ hσ
    change f σ = 1 at hσ
    change restrict E σ = 1
    calc
      restrict E σ = π (f σ) := (FiniteEmbeddingProblem.WeakSolution.commutes_apply s σ).symm
      _ = 1 := by rw [hσ, map_one]
  obtain ⟨q, hq⟩ := (quotient_restriction L).exists
  let e := QuotientGroup.quotientMulEquivOfEq hker
  let ι := (QuotientGroup.kerLift f).comp (e.toMonoidHom.comp q.symm.toMonoidHom)
  have hinj : Function.Injective ι :=
    (QuotientGroup.kerLift_injective f).comp (e.injective.comp q.symm.injective)
  have hlift (σ : Gal(Ω/k)) : ι (restrict L σ) = f σ := by
    rw [← hq σ]
    change QuotientGroup.kerLift f (e (q.symm (q (QuotientGroup.mk σ)))) = f σ
    rw [q.symm_apply_apply]
    exact QuotientGroup.kerLift_mk f σ
  have hcomm : π.toMonoidHom.comp ι = (transition hEL).toMonoidHom := by
    ext1 τ
    obtain ⟨σ, rfl⟩ := restrict_surjective L τ
    change π (ι (restrict L σ)) = transition hEL (restrict L σ)
    rw [hlift]
    exact (FiniteEmbeddingProblem.WeakSolution.commutes_apply s σ).trans
      (DFunLike.congr_fun (restrict_comp hEL) σ)
  refine ⟨L, hEL, ι, rfl, hinj, hcomm, MonoidHom.ext hlift, ?_⟩
  rw [← surjective_iff_equiv ι hinj]
  change Function.Surjective f ↔ Function.Surjective ι
  constructor
  · intro hf b
    obtain ⟨σ, hσ⟩ := hf b
    exact ⟨restrict L σ, (hlift σ).trans hσ⟩
  · intro hi
    simpa only [Function.comp_def, hlift] using hi.comp (restrict_surjective L)

/-- A finite Galois extension and compatible injection give a weak solution by restriction. -/
theorem weakSolution_of_extension (L : FiniteGaloisIntermediateField k Ω)
    (hEL : E ≤ L) (ι : Gal(L/k) →* B) (hinj : Function.Injective ι)
    (hcomm : π.toMonoidHom.comp ι = (transition hEL).toMonoidHom) :
    ∃ s : (prescribedProblem E π hπ).WeakSolution,
      s.lift.toMonoidHom = ι.comp (restrict L).toMonoidHom ∧
      L.toIntermediateField = fixedField s.lift.toMonoidHom.ker ∧
      (s.IsProper ↔ ∃ e : Gal(L/k) ≃* B, e.toMonoidHom = ι) := by
  let i : Gal(L/k) →ₜ* B := ⟨ι, continuous_of_discreteTopology⟩
  let s : (prescribedProblem E π hπ).WeakSolution :=
    { lift := i.comp (restrict L)
      commutes := by
        ext1 σ
        change π (ι (restrict L σ)) = restrict E σ
        exact (DFunLike.congr_fun hcomm (restrict L σ)).trans
          (DFunLike.congr_fun (restrict_comp hEL) σ).symm }
  refine ⟨s, rfl, ?_, ?_⟩
  · change L.toIntermediateField = fixedField (ι.comp (restrict L).toMonoidHom).ker
    rw [MonoidHom.ker_comp_of_injective _ _ hinj, restrict_ker, fixedField_layerKernel]
  · rw [← surjective_iff_equiv ι hinj]
    change Function.Surjective (ι ∘ restrict L) ↔ Function.Surjective ι
    exact ⟨Function.Surjective.of_comp, fun h => h.comp (restrict_surjective L)⟩

/-- A Galois layer has trivial automorphism group exactly when it is the base layer. -/
theorem layerGroup_subsingleton_iff : Subsingleton Gal(E/k) ↔
    E = (⊥ : FiniteGaloisIntermediateField k Ω) := by
  constructor
  · intro h
    have hker : (restrict E).toMonoidHom.ker = ⊤ := by
      ext σ
      exact ⟨fun _ => Subgroup.mem_top _, fun _ => h.elim _ _⟩
    apply le_antisymm _ bot_le
    apply layerKernel_le_iff.mp
    rw [layerKernel_bot, ← restrict_ker, hker]
  · rintro rfl
    have heq (σ : Gal(Ω/k)) : restrict (⊥ : FiniteGaloisIntermediateField k Ω) σ = 1 := by
      change σ ∈ (restrict (⊥ : FiniteGaloisIntermediateField k Ω)).toMonoidHom.ker
      rw [restrict_ker, layerKernel_bot]
      exact Subgroup.mem_top _
    refine ⟨fun τ υ => ?_⟩
    obtain ⟨σ, rfl⟩ := restrict_surjective (⊥ : FiniteGaloisIntermediateField k Ω) τ
    obtain ⟨δ, rfl⟩ := restrict_surjective (⊥ : FiniteGaloisIntermediateField k Ω) υ
    exact (heq σ).trans (heq δ).symm

/-- With trivial prescribed quotient, proper solutions exist exactly when the group is realized. -/
theorem properSolution_iff_realization (E : FiniteGaloisIntermediateField k Ω)
    [Subsingleton Gal(E/k)] (π : B →ₜ* Gal(E/k)) (hπ : Function.Surjective π) :
    (∃ s : (prescribedProblem E π hπ).WeakSolution, s.IsProper) ↔
      ∃ L : FiniteGaloisIntermediateField k Ω, Nonempty (Gal(L/k) ≃* B) := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨L, _, _, _, _, _, _, hproper⟩ := weakSolution_fixedField E π hπ s
    obtain ⟨e, _⟩ := hproper.mp hs
    exact ⟨L, ⟨e⟩⟩
  · rintro ⟨L, ⟨e⟩⟩
    have hEL : E ≤ L := (layerGroup_subsingleton_iff E).mp inferInstance ▸ bot_le
    have hcomm : π.toMonoidHom.comp e.toMonoidHom = (transition hEL).toMonoidHom := by
      ext1 τ
      exact Subsingleton.elim _ _
    obtain ⟨s, _, _, hproper⟩ :=
      weakSolution_of_extension E π hπ L hEL e.toMonoidHom e.injective hcomm
    exact ⟨s, hproper.mpr ⟨e, rfl⟩⟩

omit [Finite B] [TopologicalSpace B] [DiscreteTopology B] in
/-- A finite Galois realization embeds in the chosen separable closure with the same group. -/
theorem realization_in_separableClosure (K : Type x) [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (e : Gal(K/k) ≃* B) :
    ∃ L : FiniteGaloisIntermediateField k Ω,
      Nonempty (K ≃ₐ[k] L) ∧ Nonempty (Gal(L/k) ≃* B) := by
  let _ : IsSepClosed Ω := IsSepClosure.sep_closed k
  let f : K →ₐ[k] Ω := IsSepClosed.lift
  let i := f.equivFieldRange
  let L : FiniteGaloisIntermediateField k Ω :=
    { toIntermediateField := f.fieldRange
      finiteDimensional := FiniteDimensional.of_surjective i.toLinearMap i.surjective
      isGalois := IsGalois.of_algEquiv i }
  exact ⟨L, ⟨i⟩, ⟨i.symm.autCongr.trans e⟩⟩

end

end GaloisFormalization.IG
