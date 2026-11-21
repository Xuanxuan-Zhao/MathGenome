import MathGenome.Internal.Specs.D05.Foundations.RealFactorization
import MathGenome.Internal.D05.Foundations.Fta
import MathGenome.Internal.D05.Foundations.Factorization
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace D05.Foundations.RealFactorization
open Polynomial Complex
open scoped ComplexConjugate

theorem conjugateRoots : D05.Specs.RealFactorization.conjugateRoots := by
  intro p z
  simp only [IsRoot, eval_map_algebraMap]
  rw [aeval_conj]
  exact map_eq_zero_iff _ (starRingEnd ℂ).injective

theorem conjugateMultiplicity : D05.Specs.RealFactorization.conjugateMultiplicity := by
  intro p z
  have hfix : (p.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) =
      p.map (algebraMap ℝ ℂ) := by
    ext n
    simp
  simpa only [hfix] using
    (eq_rootMultiplicity_map (p := p.map (algebraMap ℝ ℂ))
      (starRingEnd ℂ).injective z).symm

theorem conjugatePair : D05.Specs.RealFactorization.conjugatePair := by
  intro z
  dsimp [conjugateQuadratic]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_mul, Polynomial.map_C]
  change X ^ 2 - C ((2 * z.re : ℝ) : ℂ) * X + C ((‖z‖ ^ 2 : ℝ) : ℂ) = _
  rw [← add_conj, map_add, Complex.ofReal_pow, ← mul_conj', map_mul]
  ring

theorem quadraticProperties : D05.Specs.RealFactorization.quadraticProperties := by
  intro z hz
  have hdeg : (conjugateQuadratic z).natDegree = 2 := by
    dsimp [conjugateQuadratic]
    rw [natDegree_add_C, natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by norm_num)
  refine ⟨?_, hdeg, ?_⟩
  · change (conjugateQuadratic z).leadingCoeff = 1
    rw [leadingCoeff, hdeg]
    simp only [conjugateQuadratic, coeff_add, coeff_sub, coeff_X_pow,
      coeff_C_mul, coeff_X, coeff_C]
    norm_num
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_pos_of_ne_zero hz]

/-- A nonreal root and its distinct conjugate give relatively prime linear
factors. Their real product therefore divides the original real polynomial. -/
theorem quadratic_dvd_of_root (p : Polynomial ℝ) {z : ℂ}
    (h0 : (p.map (algebraMap ℝ ℂ)).IsRoot z) (hz : z.im ≠ 0) :
    conjugateQuadratic z ∣ p := by
  rw [← map_dvd_map' (algebraMap ℝ ℂ), conjugatePair z]
  apply IsCoprime.mul_dvd
  · exact isCoprime_X_sub_C_of_isUnit_sub <| .mk0 _ <|
      sub_ne_zero.mpr (fun h => hz (conj_eq_iff_im.mp h.symm))
  · exact dvd_iff_isRoot.mpr h0
  · exact dvd_iff_isRoot.mpr ((conjugateRoots p z).mpr h0)

/-- FTA and irreducibility classify each monic irreducible real factor. -/
theorem irreducible_factor_shape (p : Polynomial ℝ) (hm : p.Monic)
    (hi : Irreducible p) :
    (∃ r : ℝ, p = X - C r) ∨
      ∃ z : ℂ, z.im ≠ 0 ∧ p = conjugateQuadratic z := by
  obtain ⟨z, hz⟩ := Fta.existsRoot (p.map (algebraMap ℝ ℂ)) (by
    rw [natDegree_map]
    exact hm.natDegree_pos_of_not_isUnit hi.not_isUnit)
  by_cases hzim : z.im = 0
  · left
    have hzreal : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hzim]
    have hreal : p.IsRoot z.re := by
      have h : aeval (z.re : ℂ) p = 0 := by
        rw [hzreal, ← eval_map_algebraMap]
        exact hz
      have he : aeval (z.re : ℂ) p = ((p.eval z.re : ℝ) : ℂ) := by
        exact eval₂_at_apply (p := p) (algebraMap ℝ ℂ) z.re
      rw [he] at h
      exact Complex.ofReal_injective h
    have hdvd : X - C z.re ∣ p := dvd_iff_isRoot.mpr hreal
    have hnu : ¬ IsUnit ((X : Polynomial ℝ) - C z.re) := by
      intro h
      have := natDegree_eq_zero_of_isUnit h
      simp at this
    exact ⟨z.re, eq_of_monic_of_associated hm (monic_X_sub_C _) <|
      (hi.dvd_iff.mp hdvd).resolve_left hnu⟩
  · right
    have hprops := quadraticProperties z hzim
    have hnu : ¬ IsUnit (conjugateQuadratic z) := by
      intro h
      have := natDegree_eq_zero_of_isUnit h
      rw [hprops.2.1] at this
      contradiction
    exact ⟨z, hzim, eq_of_monic_of_associated hm hprops.1 <|
      (hi.dvd_iff.mp (quadratic_dvd_of_root p hz hzim)).resolve_left hnu⟩

/-- Partition the entire multiset of irreducibles without deleting repeated
occurrences. Each occurrence contributes one linear or one quadratic factor. -/
theorem split_irreducible_factors (s : Multiset (Polynomial ℝ))
    (hs : ∀ q ∈ s, q.Monic ∧ Irreducible q) :
    ∃ (rs : Multiset ℝ) (zs : Multiset ℂ), (∀ z ∈ zs, z.im ≠ 0) ∧
      s.prod = (rs.map (fun r => (X : Polynomial ℝ) - C r)).prod *
        (zs.map conjugateQuadratic).prod := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | @cons q s ih =>
    obtain ⟨rs, zs, hzs, hprod⟩ := ih (fun r hr => hs r (Multiset.mem_cons_of_mem hr))
    have hq := hs q (Multiset.mem_cons_self q s)
    rcases irreducible_factor_shape q hq.1 hq.2 with ⟨r, hr⟩ | ⟨z, hz, hqz⟩
    · refine ⟨r ::ₘ rs, zs, hzs, ?_⟩
      simp only [Multiset.prod_cons, Multiset.map_cons]
      rw [hr, hprod]
      ring
    · refine ⟨rs, z ::ₘ zs, ?_, ?_⟩
      · intro w hw
        rcases Multiset.mem_cons.mp hw with rfl | hw
        · exact hz
        · exact hzs w hw
      · simp only [Multiset.prod_cons, Multiset.map_cons]
        rw [hqz, hprod]
        ring

theorem realFactorization : D05.Specs.RealFactorization.realFactorization := by
  intro p hp
  obtain ⟨u, s, hs, hprod⟩ := Factorization.factorization ℝ p hp
  obtain ⟨c, hc, hu⟩ := (Factorization.unitsAreConstants ℝ u).mp u.isUnit
  obtain ⟨rs, zs, hzs, hsprod⟩ := split_irreducible_factors s hs
  refine ⟨c, rs, zs, hc, hzs, ?_⟩
  rw [hprod, hu, hsprod]
  ring

theorem constantFactorization : D05.Specs.RealFactorization.constantFactorization := by
  intro c _
  simp

end D05.Foundations.RealFactorization
