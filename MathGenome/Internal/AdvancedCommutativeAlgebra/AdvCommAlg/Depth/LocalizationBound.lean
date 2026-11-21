import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.AssociatedPrimeBound
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.LocalizationBound
import Mathlib.RingTheory.Finiteness.Small

/-! DP-10: depth after prime localization, with the full dimension term. -/

universe u v w
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma maximalIdeal_smul_top_ne_top (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
  (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm

/-- Depth is invariant under changing the presentation of a finite module. -/
lemma depth_eq_of_linearEquiv {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    (e : M ≃ₗ[R] N) : depth R M = depth R N := by
  rw [depth_eq_grade, depth_eq_grade,
    grade_of_smul_ne_top _ _ (maximalIdeal_smul_top_ne_top M),
    grade_of_smul_ne_top _ _ (maximalIdeal_smul_top_ne_top N)]
  congr 1
  ext n
  constructor
  · rintro ⟨xs, hxs, hmem, rfl⟩
    exact ⟨xs, (e.isRegular_congr xs).mp hxs, hmem, rfl⟩
  · rintro ⟨xs, hxs, hmem, rfl⟩
    exact ⟨xs, (e.isRegular_congr xs).mpr hxs, hmem, rfl⟩

/-- A maximal regular sequence in `p` leaves a quotient with an associated
prime containing `p`. The associated-prime depth bound controls the remainder. -/
lemma exists_regular_depth_le_length_add_coheight
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (p : Ideal R) [p.IsPrime] :
    ∃ xs : List R, IsRegular M xs ∧ (∀ a ∈ xs, a ∈ p) ∧
      depth R M ≤ (xs.length : ℕ∞) + Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
  have hpm : p ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal_of_isPrime p
  have hm := maximalIdeal_smul_top_ne_top (R := R) M
  have hp : p • (⊤ : Submodule R M) ≠ ⊤ :=
    ne_top_of_le_ne_top hm (Submodule.smul_mono_left hpm)
  obtain ⟨xs, hxs⟩ := exists_maximalRegular_extension p M hp []
    (IsRegular.nil R M) (by simp)
  simp only [List.nil_append] at hxs
  let Q := M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)
  have hQ : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hxs.1.top_ne_smul.symm
  letI := hQ
  have hQp : p • (⊤ : Submodule R Q) ≠ ⊤ := by
    intro he
    apply hp
    have h := congrArg (Submodule.comap (Submodule.mkQ
      (Ideal.ofList xs • (⊤ : Submodule R M)))) he
    have hle : Ideal.ofList xs • (⊤ : Submodule R M) ≤ p • ⊤ :=
      Submodule.smul_mono_left (Ideal.span_le.mpr hxs.2.1)
    simpa [Submodule.comap_smul_top_of_surjective p _ (Submodule.mkQ_surjective _),
      sup_eq_left.mpr hle] using h
  have hz : grade p Q = 0 := by
    apply (grade_zero_iff_no_regular p Q hQp).mpr
    intro a ha hreg
    apply hxs.2.2 a ha
    apply (regular_append_iff M xs [a]).mpr
    refine ⟨hxs.1.toIsWeaklyRegular, ?_⟩
    refine ⟨(isWeaklyRegular_singleton_iff Q a).mpr hreg, ?_⟩
    exact (ne_top_of_le_ne_top hQp (Submodule.smul_mono_left
      (Ideal.span_le.mpr (by simpa using ha)))).symm
  obtain ⟨q, hq, hpq⟩ := (grade_zero_iff_exists_associatedPrime p Q hQp).mp hz
  have hdim (J : Ideal R) (hJ : J.IsPrime) :
      (Order.coheight (⟨J, hJ⟩ : PrimeSpectrum R) : WithBot ℕ∞) =
        ringKrullDim (R ⧸ J) := by
    rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
    rfl
  have hbound := depth_le_dim_quotient_of_associatedPrime R Q q hq
  rw [← hdim q hq.isPrime] at hbound
  have hbound' : depth R Q ≤ Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R) :=
    (WithBot.coe_le_coe.mp hbound).trans (Order.coheight_anti hpq)
  have hdrop : depth R Q = depth R M - xs.length :=
    grade_quotient_regular M (IsLocalRing.maximalIdeal R) hm xs hxs.1
      (fun a ha => hpm (hxs.2.1 a ha))
  refine ⟨xs, hxs.1, hxs.2.1, ?_⟩
  rw [hdrop] at hbound'
  exact (tsub_le_iff_right.mp hbound').trans_eq (add_comm _ _)

/-- The sharp depth bound at every prime, including primes outside the support. -/
theorem depth_le_localized_depth_add_dim
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (p : Ideal R) [p.IsPrime] :
    (depth R M : WithBot ℕ∞) ≤
      (depth (Localization.AtPrime p) (LocalizedModule.AtPrime p M) : WithBot ℕ∞) +
        ringKrullDim (R ⧸ p) := by
  have hdim : (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum R) : WithBot ℕ∞) =
      ringKrullDim (R ⧸ p) := by
    rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
    rfl
  rw [← hdim, ← WithBot.coe_add, WithBot.coe_le_coe]
  by_cases hloc : Nontrivial (LocalizedModule.AtPrime p M)
  · letI := hloc
    -- Finite modules are small over their coefficient ring. This lets the
    -- same-universe upstream grade-drop theorem apply without restricting M.
    letI : Small.{u} M := Module.Finite.small R M
    let U := Shrink.{u} M
    let e : U ≃ₗ[R] M := Shrink.linearEquiv R M
    letI : Nontrivial U := e.toEquiv.nontrivial
    obtain ⟨xs, hreg, hmem, hbound⟩ :=
      exists_regular_depth_le_length_add_coheight U p
    rw [depth_eq_of_linearEquiv e] at hbound
    have hregM : IsRegular M xs := (e.isRegular_congr xs).mp hreg
    have hregLoc := RegularSequence.regular_localizedModule M p xs
      (Ideal.span_le.mpr hmem) hregM
    have hmemLoc : ∀ a ∈ xs.map (algebraMap R (Localization.AtPrime p)),
        a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ (hmem b hb)
    have hlen : (xs.length : ℕ∞) ≤
        depth (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
      rw [depth_eq_grade, grade_of_smul_ne_top _ _
        (maximalIdeal_smul_top_ne_top (R := Localization.AtPrime p)
          (LocalizedModule.AtPrime p M))]
      exact le_sSup ⟨xs.map (algebraMap R (Localization.AtPrime p)),
        hregLoc, hmemLoc, by simp⟩
    exact hbound.trans (add_le_add hlen le_rfl)
  · letI : Subsingleton (LocalizedModule.AtPrime p M) :=
      not_nontrivial_iff_subsingleton.mp hloc
    rw [depth_eq_top_of_subsingleton (Localization.AtPrime p) (LocalizedModule.AtPrime p M)]
    simp

end AdvCommAlg.Depth
