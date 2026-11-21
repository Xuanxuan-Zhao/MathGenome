import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.PowerIteration
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators DirectSum NNReal
open Filter
namespace NumAnalysis206.PowerIteration
open MatrixDefinitions PowerIterationDefinitions

variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]
  [FiniteDimensional K E]

lemma mem_otherEigenvalues (T : Module.End K E) (lam μ : K) :
    μ ∈ otherEigenvalues T lam ↔ μ ≠ lam ∧ T.HasEigenvalue μ := by
  classical
  let : DecidableEq K := Classical.decEq K
  let : DecidableEq E := Classical.decEq E
  simp [otherEigenvalues]

omit [FiniteDimensional K E] in
lemma component_on_eigenspace (T : Module.End K E) (hT : IsDiagonalizable T)
    {μ : K} {x : E} (hx : x ∈ T.eigenspace μ) (ν : K) :
    spectralComponent T hT ν x = if ν = μ then x else 0 := by
  classical
  let : DecidableEq K := Classical.decEq K
  let : DecidableEq E := Classical.decEq E
  let h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    T.eigenspaces_iSupIndep hT
  by_cases hn : ν = μ
  · subst ν
    simp only [ite_true]
    exact congrArg Subtype.val (h.ofBijective_coeLinearMap_of_mem hx)
  · rw [ite_eq_right hn]
    exact congrArg Subtype.val (h.ofBijective_coeLinearMap_of_mem_ne (Ne.symm hn) hx)

lemma sum_components (T : Module.End K E) (hT : IsDiagonalizable T) (x : E) :
    ∑ μ ∈ T.finite_hasEigenvalue.toFinset, spectralComponent T hT μ x = x := by
  classical
  let : DecidableEq K := Classical.decEq K
  let : DecidableEq E := Classical.decEq E
  let d := eigenspaceDecomposition T hT x
  have hd : d.support ⊆ T.finite_hasEigenvalue.toFinset := by
    intro μ hμ
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    change T.eigenspace μ ≠ ⊥
    intro hz
    have hm0 : (d μ : E) = 0 := by
      simpa only [hz, Submodule.mem_bot] using (d μ).property
    have : d μ = 0 := Subtype.ext hm0
    exact (DFinsupp.mem_support_iff.mp hμ) this
  have hs := MatrixData.eigenspaceDecomposition_recompose T hT x
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum] at hs
  change (∑ μ ∈ d.support, (d μ : E)) = x at hs
  apply Eq.trans ?_ hs
  change (∑ μ ∈ T.finite_hasEigenvalue.toFinset, (d μ : E)) = _
  symm
  apply Finset.sum_subset hd
  intro μ _ hμ
  have : d μ = 0 := DFinsupp.notMem_support_iff.mp hμ
  change (d μ : E) = 0
  rw [this]
  rfl

omit [FiniteDimensional K E] in
lemma pow_component (T : Module.End K E) (hT : IsDiagonalizable T)
    (μ : K) (x : E) (j : ℕ) :
    (T ^ j) (spectralComponent T hT μ x) = μ ^ j • spectralComponent T hT μ x := by
  by_cases hx : spectralComponent T hT μ x = 0
  · simp [hx]
  · exact Module.End.HasEigenvector.pow_apply
      ⟨MatrixData.spectralComponent_mem T hT μ x, hx⟩ j

lemma component_pow (T : Module.End K E) (hT : IsDiagonalizable T)
    (μ : K) (hμ : T.HasEigenvalue μ) (x : E) (j : ℕ) :
    spectralComponent T hT μ ((T ^ j) x) = μ ^ j • spectralComponent T hT μ x := by
  classical
  conv_lhs => rw [← sum_components T hT x]
  rw [map_sum, map_sum]
  simp_rw [pow_component, map_smul,
    component_on_eigenspace T hT (MatrixData.spectralComponent_mem T hT _ x)]
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp [hμ]

lemma iterates_ne_zero (T : Module.End K E) (hT : IsDiagonalizable T)
    (lam : K) (hlam : lam ≠ 0) (x : E) (hp : spectralComponent T hT lam x ≠ 0)
    (j : ℕ) : (T ^ j) x ≠ 0 := by
  have heig : T.HasEigenvalue lam :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨MatrixData.spectralComponent_mem T hT lam x, hp⟩
  intro hz
  have hc := component_pow T hT lam heig x j
  rw [hz, map_zero] at hc
  exact (smul_ne_zero (pow_ne_zero j hlam) hp) hc.symm

lemma scaled_pow_expansion (T : Module.End K E) (hT : IsDiagonalizable T)
    (lam : K) (hlam : lam ≠ 0) (heig : T.HasEigenvalue lam) (x : E) (j : ℕ) :
    (lam⁻¹ ^ j) • ((T ^ j) x) = spectralComponent T hT lam x +
      ∑ μ ∈ otherEigenvalues T lam, (μ / lam) ^ j • spectralComponent T hT μ x := by
  classical
  have hmem : lam ∈ T.finite_hasEigenvalue.toFinset := by simpa
  calc
    _ = ∑ μ ∈ T.finite_hasEigenvalue.toFinset,
        (μ / lam) ^ j • spectralComponent T hT μ x := by
      conv_lhs => rw [← sum_components T hT x]
      rw [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      rw [pow_component, smul_smul, ← mul_pow]
      congr 2
      simp [div_eq_mul_inv, mul_comm]
    _ = _ := by
      rw [← Finset.add_sum_erase _ _ hmem]
      simp only [div_self hlam, one_pow, one_smul, otherEigenvalues]

lemma convergenceRatio_nonneg (T : Module.End K E) (lam : K) :
    0 ≤ convergenceRatio T lam := NNReal.coe_nonneg _

lemma ratio_le (T : Module.End K E) (lam μ : K) (hμ : μ ∈ otherEigenvalues T lam) :
    ‖μ / lam‖ ≤ convergenceRatio T lam := by
  exact_mod_cast (Finset.le_sup (f := fun μ => ‖μ / lam‖₊) hμ)

lemma convergenceRatio_lt_one (T : Module.End K E) (lam : K) (hlam : lam ≠ 0)
    (hdom : ∀ μ, T.HasEigenvalue μ → μ ≠ lam → ‖μ‖ < ‖lam‖) :
    convergenceRatio T lam < 1 := by
  classical
  change ((otherEigenvalues T lam).sup (fun μ => ‖μ / lam‖₊) : ℝ≥0) < 1
  norm_cast
  apply (Finset.sup_lt_iff (show (0 : ℝ≥0) < 1 by norm_num)).mpr
  intro μ hμ
  obtain ⟨hne, he⟩ := (mem_otherEigenvalues T lam μ).mp hμ
  change ‖μ / lam‖ < (1 : ℝ)
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hlam)]
  exact hdom μ he hne

lemma scaled_pow_error (T : Module.End K E) (hT : IsDiagonalizable T)
    (lam : K) (hlam : lam ≠ 0) (heig : T.HasEigenvalue lam) (x : E) (j : ℕ) :
    ‖(lam⁻¹ ^ j) • ((T ^ j) x) - spectralComponent T hT lam x‖ ≤
      convergenceRatio T lam ^ j * remainderSize T hT lam x := by
  rw [scaled_pow_expansion T hT lam hlam heig x j, add_sub_cancel_left]
  calc
    _ ≤ ∑ μ ∈ otherEigenvalues T lam, ‖(μ / lam) ^ j • spectralComponent T hT μ x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ μ ∈ otherEigenvalues T lam,
        convergenceRatio T lam ^ j * ‖spectralComponent T hT μ x‖ := by
      apply Finset.sum_le_sum
      intro μ hμ
      rw [norm_smul, norm_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ratio_le T lam μ hμ) j)
        (norm_nonneg _)
    _ = _ := by rw [remainderSize, Finset.mul_sum]

omit [FiniteDimensional K E] in
lemma norm_unitVector {x : E} (hx : x ≠ 0) : ‖unitVector (K := K) x‖ = 1 := by
  simp [unitVector, norm_smul, hx]

omit [FiniteDimensional K E] in
lemma norm_smul_unitVector (x : E) : (‖x‖ : K) • unitVector (K := K) x = x := by
  by_cases hx : x = 0
  · simp [hx, unitVector]
  · rw [unitVector, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast norm_ne_zero_iff.mpr hx

omit [FiniteDimensional K E] in
lemma unitVector_error {y p : E} (hy : y ≠ 0) (hp : p ≠ 0) :
    ‖unitVector (K := K) y - unitVector (K := K) p‖ ≤ 2 * ‖y - p‖ / ‖p‖ := by
  have hid : (‖p‖ : K) • (unitVector (K := K) y - unitVector (K := K) p) =
      (y - p) + ((‖p‖ - ‖y‖ : ℝ) : K) • unitVector (K := K) y := by
    rw [RCLike.ofReal_sub, sub_smul, smul_sub, norm_smul_unitVector, norm_smul_unitVector]
    abel
  have hnorm : ‖p‖ * ‖unitVector (K := K) y - unitVector (K := K) p‖ ≤ 2 * ‖y - p‖ := by
    calc
      _ = ‖(‖p‖ : K) • (unitVector (K := K) y - unitVector (K := K) p)‖ := by
        simp [norm_smul]
      _ = _ := congrArg norm hid
      _ ≤ ‖y - p‖ + ‖((‖p‖ - ‖y‖ : ℝ) : K) • unitVector (K := K) y‖ := norm_add_le _ _
      _ = ‖y - p‖ + |‖p‖ - ‖y‖| := by rw [norm_smul, norm_unitVector hy, RCLike.norm_ofReal, mul_one]
      _ ≤ 2 * ‖y - p‖ := by
        have h := abs_norm_sub_norm_le y p
        rw [abs_sub_comm] at h
        linarith
  exact (le_div_iff₀ (norm_pos_iff.mpr hp)).mpr (by nlinarith)

omit [FiniteDimensional K E] in
lemma unitVector_smul (a : K) (x : E) :
    unitVector (K := K) (a • x) = (a / (‖a‖ : K)) • unitVector (K := K) x := by
  simp only [unitVector, norm_smul, RCLike.ofReal_mul, mul_inv_rev, smul_smul, div_eq_mul_inv]
  congr 1
  ring

omit [FiniteDimensional K E] in
lemma correctedDirection_eq (T : Module.End K E) (lam : K) (x : E) (j : ℕ) :
    correctedDirection T lam x j = unitVector (K := K) ((lam⁻¹ ^ j) • ((T ^ j) x)) := by
  rw [unitVector_smul]
  unfold correctedDirection
  congr 1
  simp only [norm_pow, norm_inv, RCLike.ofReal_pow, RCLike.ofReal_inv, inv_pow,
    inv_inv, div_eq_mul_inv]
  rw [mul_pow]
  ring

lemma direction_error (T : Module.End K E) (hT : IsDiagonalizable T)
    (lam : K) (hlam : lam ≠ 0) (x : E) (hp : spectralComponent T hT lam x ≠ 0) (j : ℕ) :
    ‖correctedDirection T lam x j - unitVector (K := K) (spectralComponent T hT lam x)‖ ≤
      2 * convergenceRatio T lam ^ j * remainderSize T hT lam x /
        ‖spectralComponent T hT lam x‖ := by
  have heig : T.HasEigenvalue lam := Module.End.hasEigenvalue_of_hasEigenvector
    ⟨MatrixData.spectralComponent_mem T hT lam x, hp⟩
  rw [correctedDirection_eq]
  apply (unitVector_error (smul_ne_zero (pow_ne_zero j (inv_ne_zero hlam))
    (iterates_ne_zero T hT lam hlam x hp j)) hp).trans
  apply (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hp)).mpr
  have he := scaled_pow_error T hT lam hlam heig x j
  linarith

theorem power_iteration : Specs.NumAnalysis206.PowerIteration.power_iteration := by
  intro K _ n A hA lam x hlam hdom hp
  have h0 := convergenceRatio_nonneg A.toEuclideanLin lam
  have hlt := convergenceRatio_lt_one A.toEuclideanLin lam hlam hdom
  have hbig : Asymptotics.IsBigO atTop
      (fun j : ℕ => correctedDirection A.toEuclideanLin lam x j -
        unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x))
      (fun j : ℕ => convergenceRatio A.toEuclideanLin lam ^ j) := by
    apply Asymptotics.IsBigO.of_bound
      (2 * remainderSize A.toEuclideanLin hA lam x / ‖spectralComponent A.toEuclideanLin hA lam x‖)
    apply Eventually.of_forall
    intro j
    calc
      _ ≤ 2 * convergenceRatio A.toEuclideanLin lam ^ j *
          remainderSize A.toEuclideanLin hA lam x / ‖spectralComponent A.toEuclideanLin hA lam x‖ :=
        direction_error A.toEuclideanLin hA lam hlam x hp j
      _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 j)]; ring
  exact ⟨iterates_ne_zero A.toEuclideanLin hA lam hlam x hp,
    ⟨h0, hlt⟩, (fun j _ => direction_error A.toEuclideanLin hA lam hlam x hp j),
    tendsto_sub_nhds_zero_iff.mp (hbig.trans_tendsto
      (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt)), hbig⟩

lemma convergenceRatio_eq_zero (T : Module.End K E) (lam : K)
    (hz : ∀ μ, T.HasEigenvalue μ → μ ≠ lam → μ = 0) :
    convergenceRatio T lam = 0 := by
  classical
  apply le_antisymm ?_ (convergenceRatio_nonneg T lam)
  change ((otherEigenvalues T lam).sup (fun μ => ‖μ / lam‖₊) : ℝ≥0) ≤ 0
  norm_cast
  apply Finset.sup_le
  intro μ hμ
  obtain ⟨hne, he⟩ := (mem_otherEigenvalues T lam μ).mp hμ
  simp [hz μ he hne]

theorem exact_when_other_eigenvalues_zero :
    Specs.NumAnalysis206.PowerIteration.exact_when_other_eigenvalues_zero := by
  intro K _ n A hA lam x hlam hz hp
  have hr := convergenceRatio_eq_zero A.toEuclideanLin lam hz
  refine ⟨hr, fun j hj => ?_⟩
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  have h := direction_error A.toEuclideanLin hA lam hlam x hp j
  simpa [hr, zero_pow (show j ≠ 0 by omega)] using h

theorem exact_single_eigenvalue : Specs.NumAnalysis206.PowerIteration.exact_single_eigenvalue := by
  intro K _ n A hA lam x hlam hone hp
  classical
  have hempty : otherEigenvalues A.toEuclideanLin lam = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro μ hμ
    obtain ⟨hne, he⟩ := (mem_otherEigenvalues A.toEuclideanLin lam μ).mp hμ
    exact hne (hone μ he)
  have hr : convergenceRatio A.toEuclideanLin lam = 0 := by
    simp [convergenceRatio, hempty]
  have hsize : remainderSize A.toEuclideanLin hA lam x = 0 := by
    simp [remainderSize, hempty]
  refine ⟨hr, fun j => ?_⟩
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  simpa [hsize] using direction_error A.toEuclideanLin hA lam hlam x hp j

theorem real_phase_is_sign : Specs.NumAnalysis206.PowerIteration.real_phase_is_sign := by
  intro lam hlam
  by_cases hpos : 0 < lam
  · rw [ite_eq_left hpos, Real.norm_eq_abs, abs_of_pos hpos, div_self hlam]
  · have hneg : lam < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hlam
    rw [ite_eq_right hpos, Real.norm_eq_abs, abs_of_neg hneg, neg_div, div_self hlam]

end NumAnalysis206.PowerIteration
