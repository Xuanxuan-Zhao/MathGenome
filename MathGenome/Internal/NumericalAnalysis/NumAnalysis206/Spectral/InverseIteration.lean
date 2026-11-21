import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.InverseIteration
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.PowerIteration
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Residual

noncomputable section
open scoped BigOperators NNReal
open Filter
namespace NumAnalysis206.InverseIteration
open MatrixDefinitions PowerIterationDefinitions InverseIterationDefinitions
variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [NormedSpace K E]
  [FiniteDimensional K E]

lemma shiftedEquiv_apply (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T) (v : E) :
    shiftedEquiv T μ hμ v = T v - μ • v := rfl

lemma solve_eq (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T) (v : E) :
    T (inverseMap T μ hμ v) - μ • inverseMap T μ hμ v = v :=
  (shiftedEquiv T μ hμ).apply_symm_apply v

lemma inverseMap_injective (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T) :
    Function.Injective (inverseMap T μ hμ) := (shiftedEquiv T μ hμ).symm.injective

omit [FiniteDimensional K E] in
lemma eigenvalue_sub_ne_zero (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T)
    {ν : K} (hν : T.HasEigenvalue ν) : ν - μ ≠ 0 := by
  intro hz
  exact hμ ((sub_eq_zero.mp hz) ▸ hν.mem_spectrum)

lemma inverse_component (T : Module.End K E) (hT : IsDiagonalizable T)
    (μ : K) (hμ : μ ∉ spectrum K T) (ν : K) (x : E) :
    inverseMap T μ hμ (spectralComponent T hT ν x) =
      (ν - μ)⁻¹ • spectralComponent T hT ν x := by
  by_cases hp : spectralComponent T hT ν x = 0
  · simp [hp]
  have hv := MatrixData.spectralComponent_mem T hT ν x
  have hn := eigenvalue_sub_ne_zero T μ hμ
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hp⟩)
  apply (shiftedEquiv T μ hμ).injective
  change (shiftedEquiv T μ hμ) ((shiftedEquiv T μ hμ).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, shiftedEquiv_apply,
    Module.End.mem_eigenspace_iff.mp hv, ← sub_smul, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma inverse_pow_component (T : Module.End K E) (hT : IsDiagonalizable T)
    (μ : K) (hμ : μ ∉ spectrum K T) (ν : K) (x : E) (j : ℕ) :
    (inverseMap T μ hμ ^ j) (spectralComponent T hT ν x) =
      ((ν - μ)⁻¹ ^ j) • spectralComponent T hT ν x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, inverse_component, smul_smul,
      pow_succ]

lemma inverse_iterates_ne_zero (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T)
    {x : E} (hx : x ≠ 0) (j : ℕ) : (inverseMap T μ hμ ^ j) x ≠ 0 := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact fun hz => ih ((inverseMap_injective T μ hμ) (hz.trans (map_zero _).symm))

omit [FiniteDimensional K E] in
lemma unitVector_ne_zero {x : E} (hx : x ≠ 0) : unitVector (K := K) x ≠ 0 := by
  have hn : (‖x‖ : K) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  exact smul_ne_zero (inv_ne_zero hn) hx

omit [FiniteDimensional K E] in
lemma unitVector_map_unitVector (B : Module.End K E) {x : E} (hx : x ≠ 0) :
    unitVector (K := K) (B (unitVector (K := K) x)) = unitVector (K := K) (B x) := by
  have hn : (‖x‖ : K) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  change unitVector (K := K) (B (((‖x‖ : K)⁻¹) • x)) = _
  rw [map_smul, PowerIteration.unitVector_smul]
  simp [norm_inv, hn]

lemma normalizedIterate_eq (B : Module.End K E) (x : E)
    (hx : ∀ j : ℕ, (B ^ j) x ≠ 0) (j : ℕ) :
    normalizedIterate B x j = unitVector (K := K) ((B ^ j) x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [normalizedIterate, ih, unitVector_map_unitVector B (hx j), pow_succ', Module.End.mul_apply]


omit [FiniteDimensional K E] in
lemma initial_ne_zero (T : Module.End K E) (hT : IsDiagonalizable T)
    (lam : K) {x : E} (hp : spectralComponent T hT lam x ≠ 0) : x ≠ 0 := by
  intro hx
  exact hp (by simp [hx])

lemma scaled_inverse_pow_expansion (T : Module.End K E) (hT : IsDiagonalizable T)
    (μ : K) (hμ : μ ∉ spectrum K T) (lam : K) (heig : T.HasEigenvalue lam)
    (x : E) (j : ℕ) :
    ((lam - μ) ^ j) • ((inverseMap T μ hμ ^ j) x) = spectralComponent T hT lam x +
      ∑ ν ∈ otherEigenvalues T lam,
        ((lam - μ) / (ν - μ)) ^ j • spectralComponent T hT ν x := by
  classical
  have hmem : lam ∈ T.finite_hasEigenvalue.toFinset := by simpa
  have hn := eigenvalue_sub_ne_zero T μ hμ heig
  calc
    _ = ∑ ν ∈ T.finite_hasEigenvalue.toFinset,
        ((lam - μ) / (ν - μ)) ^ j • spectralComponent T hT ν x := by
      conv_lhs => rw [← PowerIteration.sum_components T hT x]
      rw [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ν _
      rw [inverse_pow_component, smul_smul, ← mul_pow, div_eq_mul_inv]
    _ = _ := by
      rw [← Finset.add_sum_erase _ _ hmem]
      simp only [div_self hn, one_pow, one_smul, otherEigenvalues]

lemma inverseRatio_nonneg (T : Module.End K E) (μ lam : K) :
    0 ≤ inverseRatio T μ lam := NNReal.coe_nonneg _

lemma inverse_ratio_le (T : Module.End K E) (μ lam ν : K)
    (hν : ν ∈ otherEigenvalues T lam) :
    ‖(lam - μ) / (ν - μ)‖ ≤ inverseRatio T μ lam := by
  exact_mod_cast (Finset.le_sup (f := fun ν => ‖(lam - μ) / (ν - μ)‖₊) hν)

lemma inverseRatio_lt_one (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T) (lam : K)
    (hc : ∀ ν, T.HasEigenvalue ν → ν ≠ lam → ‖lam - μ‖ < ‖ν - μ‖) :
    inverseRatio T μ lam < 1 := by
  classical
  change ((otherEigenvalues T lam).sup (fun ν => ‖(lam - μ) / (ν - μ)‖₊) : ℝ≥0) < 1
  norm_cast
  apply (Finset.sup_lt_iff (show (0 : ℝ≥0) < 1 by norm_num)).mpr
  intro ν hν
  obtain ⟨hne, he⟩ := (PowerIteration.mem_otherEigenvalues T lam ν).mp hν
  change ‖(lam - μ) / (ν - μ)‖ < (1 : ℝ)
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (eigenvalue_sub_ne_zero T μ hμ he))]
  exact hc ν he hne

lemma scaled_inverse_pow_error (T : Module.End K E) (hT : IsDiagonalizable T)
    (μ : K) (hμ : μ ∉ spectrum K T) (lam : K) (heig : T.HasEigenvalue lam)
    (x : E) (j : ℕ) :
    ‖((lam - μ) ^ j) • ((inverseMap T μ hμ ^ j) x) - spectralComponent T hT lam x‖ ≤
      inverseRatio T μ lam ^ j * remainderSize T hT lam x := by
  rw [scaled_inverse_pow_expansion T hT μ hμ lam heig x j, add_sub_cancel_left]
  calc
    _ ≤ ∑ ν ∈ otherEigenvalues T lam,
        ‖((lam - μ) / (ν - μ)) ^ j • spectralComponent T hT ν x‖ := norm_sum_le _ _
    _ ≤ ∑ ν ∈ otherEigenvalues T lam,
        inverseRatio T μ lam ^ j * ‖spectralComponent T hT ν x‖ := by
      apply Finset.sum_le_sum
      intro ν hν
      rw [norm_smul, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (inverse_ratio_le T μ lam ν hν) j) (norm_nonneg _)
    _ = _ := by rw [remainderSize, Finset.mul_sum]

lemma inverseDirection_eq (T : Module.End K E) (μ : K) (hμ : μ ∉ spectrum K T)
    (lam : K) {x : E} (hx : x ≠ 0) (j : ℕ) :
    inverseDirection T μ hμ lam x j =
      unitVector (K := K) (((lam - μ) ^ j) • ((inverseMap T μ hμ ^ j) x)) := by
  unfold inverseDirection
  rw [normalizedIterate_eq _ _ (inverse_iterates_ne_zero T μ hμ hx)]
  exact (PowerIteration.correctedDirection_eq (inverseMap T μ hμ) ((lam - μ)⁻¹) x j).trans
    (by simp only [inv_inv])

lemma inverse_direction_error (T : Module.End K E) (hT : IsDiagonalizable T)
    (μ : K) (hμ : μ ∉ spectrum K T) (lam : K) (x : E)
    (hp : spectralComponent T hT lam x ≠ 0) (j : ℕ) :
    ‖inverseDirection T μ hμ lam x j - unitVector (K := K) (spectralComponent T hT lam x)‖ ≤
      2 * inverseRatio T μ lam ^ j * remainderSize T hT lam x /
        ‖spectralComponent T hT lam x‖ := by
  have heig : T.HasEigenvalue lam := Module.End.hasEigenvalue_of_hasEigenvector
    ⟨MatrixData.spectralComponent_mem T hT lam x, hp⟩
  have hn := eigenvalue_sub_ne_zero T μ hμ heig
  have hx := initial_ne_zero T hT lam hp
  rw [inverseDirection_eq T μ hμ lam hx]
  apply (PowerIteration.unitVector_error (smul_ne_zero (pow_ne_zero j hn)
    (inverse_iterates_ne_zero T μ hμ hx j)) hp).trans
  apply (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hp)).mpr
  have he := scaled_inverse_pow_error T hT μ hμ lam heig x j
  linarith

theorem inverse_iteration : Specs.NumAnalysis206.InverseIteration.inverse_iteration := by
  intro K _ n A hA μ hμ lam x hc hp
  have hx := initial_ne_zero A.toEuclideanLin hA lam hp
  have hn := inverse_iterates_ne_zero A.toEuclideanLin μ hμ hx
  have h0 := inverseRatio_nonneg A.toEuclideanLin μ lam
  have hlt := inverseRatio_lt_one A.toEuclideanLin μ hμ lam hc
  have hbig : Asymptotics.IsBigO atTop
      (fun j : ℕ => inverseDirection A.toEuclideanLin μ hμ lam x j -
        unitVector (K := K) (spectralComponent A.toEuclideanLin hA lam x))
      (fun j : ℕ => inverseRatio A.toEuclideanLin μ lam ^ j) := by
    apply Asymptotics.IsBigO.of_bound
      (2 * remainderSize A.toEuclideanLin hA lam x / ‖spectralComponent A.toEuclideanLin hA lam x‖)
    apply Eventually.of_forall
    intro j
    calc
      _ ≤ 2 * inverseRatio A.toEuclideanLin μ lam ^ j *
          remainderSize A.toEuclideanLin hA lam x / ‖spectralComponent A.toEuclideanLin hA lam x‖ :=
        inverse_direction_error A.toEuclideanLin hA μ hμ lam x hp j
      _ = _ := by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 j)]; ring
  refine ⟨?_, ⟨h0, hlt⟩, (fun j => inverse_direction_error A.toEuclideanLin hA μ hμ lam x hp j),
    tendsto_sub_nhds_zero_iff.mp (hbig.trans_tendsto
      (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt)), hbig⟩
  intro j
  have heq := normalizedIterate_eq (inverseMap A.toEuclideanLin μ hμ) x hn j
  refine ⟨hn j, heq, ?_, solve_eq _ _ _ _⟩
  intro hz
  have hz' := (inverseMap_injective A.toEuclideanLin μ hμ) (hz.trans (map_zero _).symm)
  rw [heq] at hz'
  exact unitVector_ne_zero (hn j) hz'

theorem exact_single_eigenvalue : Specs.NumAnalysis206.InverseIteration.exact_single_eigenvalue := by
  intro K _ n A hA μ hμ lam x hone hp
  classical
  have hempty : otherEigenvalues A.toEuclideanLin lam = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ν hν
    obtain ⟨hne, he⟩ := (PowerIteration.mem_otherEigenvalues A.toEuclideanLin lam ν).mp hν
    exact hne (hone ν he)
  have hr : inverseRatio A.toEuclideanLin μ lam = 0 := by
    simp [inverseRatio, hempty]
  have hsize : remainderSize A.toEuclideanLin hA lam x = 0 := by
    simp [remainderSize, hempty]
  refine ⟨hr, fun j => ?_⟩
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  simpa [hsize] using inverse_direction_error A.toEuclideanLin hA μ hμ lam x hp j

theorem rounded_solve_bound : Specs.NumAnalysis206.InverseIteration.rounded_solve_bound := by
  intro K _ n A μ hμ x y yhat r hy hyhat
  have he : shiftedEquiv A.toEuclideanLin μ hμ y = x := hy
  have hr : x - shiftedEquiv A.toEuclideanLin μ hμ yhat = r := by
    rw [shiftedEquiv_apply, hyhat]
    abel
  have h := Conditioning.residual_absolute_bound (shiftedEquiv A.toEuclideanLin μ hμ) y yhat x he
  change ‖yhat - y‖ ≤ _ * ‖x - shiftedEquiv A.toEuclideanLin μ hμ yhat‖ at h
  simpa only [hr] using h

end NumAnalysis206.InverseIteration
