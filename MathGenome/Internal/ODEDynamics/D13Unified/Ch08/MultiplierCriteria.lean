import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.MultiplierCriteria
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.Translation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch08.MatrixPowerCriteria
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

noncomputable section
open Set
open scoped Matrix.Norms.Operator
namespace D13Unified.Ch08.MultiplierCriteria
open Specs.D13Unified.Ch08.Monodromy
open D13Unified.Ch08.MatrixPowerCriteria
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

lemma matrix_norm_le_of_mulVec_bound (M : Matrix (Fin n) (Fin n) 𝕂)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖M.mulVec x‖ ≤ C * ‖x‖) : ‖M‖ ≤ C := by
  rw [Matrix.linfty_opNorm_eq_opNorm]
  exact ContinuousLinearMap.opNorm_le_bound _ hC h

lemma principal_nat_period (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hp : Function.Periodic A T) (k : ℕ) :
    principalMatrixValue A ((k : ℝ) * T) = monodromyValue A T ^ k := by
  have h := Translation.integer_translation 𝕂 n A T hA hT hp (k : ℤ) 0
  simpa only [Int.cast_natCast, add_zero, zpow_natCast,
    (Monodromy.principal_properties 𝕂 n A hA).1, one_mul] using h

lemma period_decomposition {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) :
    ∃ k : ℕ, ∃ r : ℝ, r ∈ Icc 0 T ∧ t = (k : ℝ) * T + r := by
  let k : ℕ := ⌊t / T⌋₊
  have hk : (k : ℝ) ≤ t / T := Nat.floor_le (div_nonneg ht hT.le)
  have hk' : t / T < (k : ℝ) + 1 := Nat.lt_floor_add_one (t / T)
  refine ⟨k, t - (k : ℝ) * T, ⟨?_, ?_⟩, by ring⟩
  · exact sub_nonneg.mpr ((le_div_iff₀ hT).mp hk)
  · have := (div_lt_iff₀ hT).mp hk'
    nlinarith

lemma principal_compact_bound (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (hA : Continuous A) (T : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Icc 0 T, ‖principalMatrixValue A r‖ ≤ B := by
  have hc : Continuous (fun r => ‖principalMatrixValue A r‖) :=
    (Monodromy.continuous_U A hA 0).norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro r hr
  exact (hB (mem_image_of_mem _ hr)).trans (le_max_left _ _)

lemma uniform_bound_of_powerBounded (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hp : Function.Periodic A T)
    (hM : PowerBounded (monodromyValue A T)) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 0 ≤ t → ‖principalMatrixValue A t‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := principal_compact_bound A hA T
  obtain ⟨C, hc⟩ := hM
  refine ⟨B * max C 1, mul_pos hB (lt_of_lt_of_le zero_lt_one (le_max_right _ _)), ?_⟩
  intro t ht
  obtain ⟨k, r, hr, rfl⟩ := period_decomposition hT ht
  have h := Translation.integer_translation 𝕂 n A T hA hT hp (k : ℤ) r
  simp only [Int.cast_natCast, zpow_natCast] at h
  rw [h]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hb r hr) ((hc k).trans (le_max_left _ _)) (norm_nonneg _) hB.le)

lemma lyapunovStable_of_uniform_bound (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (h : ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 0 ≤ t → ‖principalMatrixValue A t‖ ≤ B) :
    LyapunovStable A := by
  obtain ⟨B, hB, hb⟩ := h
  intro ε hε
  refine ⟨ε / B, div_pos hε hB, fun x hx t ht => ?_⟩
  calc
    ‖(principalMatrixValue A t).mulVec x‖ ≤ ‖principalMatrixValue A t‖ * ‖x‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    _ ≤ B * ‖x‖ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
    _ < ε := by have := (lt_div_iff₀ hB).mp hx; nlinarith

lemma uniform_bound_of_lyapunovStable (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (h : LyapunovStable A) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 0 ≤ t → ‖principalMatrixValue A t‖ ≤ B := by
  obtain ⟨δ, hδ, hd⟩ := h 1 zero_lt_one
  refine ⟨2 / δ, div_pos (by norm_num) hδ, fun t ht => ?_⟩
  rw [Matrix.linfty_opNorm_eq_opNorm]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  have hs : ‖(δ / 2 : ℝ) • x‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hx, mul_one]
    linarith
  have hv := hd ((δ / 2 : ℝ) • x) hs t ht
  rw [Matrix.mulVec_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at hv
  change ‖(principalMatrixValue A t).mulVec x‖ ≤ 2 / δ
  apply (le_div_iff₀ hδ).mpr
  nlinarith

lemma lyapunov_iff_powerBounded (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hp : Function.Periodic A T) :
    LyapunovStable A ↔ PowerBounded (monodromyValue A T) := by
  constructor
  · intro h
    obtain ⟨B, _, hb⟩ := uniform_bound_of_lyapunovStable A h
    refine ⟨B, ?_⟩
    intro k
    rw [← principal_nat_period A hA T hT hp k]
    exact hb _ (mul_nonneg (Nat.cast_nonneg _) hT.le)
  · intro h
    exact lyapunovStable_of_uniform_bound A (uniform_bound_of_powerBounded A hA T hT hp h)

/-- Sampling the continuous-time exponential estimate at kT gives a geometric
bound, including k=0 and the zero-dimensional system. -/
lemma geometric_of_exponentiallyStable (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hp : Function.Periodic A T)
    (h : ExponentiallyStable A) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ GeometricBound (monodromyValue A T) r := by
  obtain ⟨C, hC, α, hα, hb⟩ := h
  refine ⟨Real.exp (-α * T), Real.exp_pos _, ?_, C, hC, fun k => ?_⟩
  · rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hα) hT
  · rw [← principal_nat_period A hA T hT hp k]
    have he : Real.exp (-α * ((k : ℝ) * T)) = Real.exp (-α * T) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [← he]
    exact matrix_norm_le_of_mulVec_bound _ (by positivity)
      (hb _ (mul_nonneg (Nat.cast_nonneg _) hT.le))

/-- The compact part of each period changes only the prefactor. The rate
α=-log(r)/T is positive, and the residual time costs at most exp(αT). -/
lemma exponentiallyStable_of_geometric (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hp : Function.Periodic A T)
    (h : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ GeometricBound (monodromyValue A T) r) :
    ExponentiallyStable A := by
  obtain ⟨r, hr, hr1, C, hC, hc⟩ := h
  obtain ⟨B, hB, hb⟩ := principal_compact_bound A hA T
  let α : ℝ := -Real.log r / T
  have hα : 0 < α := div_pos (neg_pos.mpr (Real.log_neg hr hr1)) hT
  have hαT : α * T = -Real.log r := div_mul_cancel₀ _ hT.ne'
  refine ⟨B * C * Real.exp (α * T), by positivity, α, hα, fun t ht x => ?_⟩
  obtain ⟨k, s, hs, hts⟩ := period_decomposition hT ht
  have hx := Translation.integer_translation 𝕂 n A T hA hT hp (k : ℤ) s
  simp only [Int.cast_natCast, zpow_natCast] at hx
  have he : r ^ k ≤ Real.exp (α * T) * Real.exp (-α * t) := by
    calc
      r ^ k = Real.exp ((k : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr]
      _ ≤ Real.exp (α * T + -α * t) := by
        apply Real.exp_le_exp.mpr
        have hh : (k : ℝ) * Real.log r = -α * t + α * s := by
          rw [hts]
          nlinarith [hαT]
        rw [hh]
        nlinarith [mul_le_mul_of_nonneg_left hs.2 hα.le]
      _ = Real.exp (α * T) * Real.exp (-α * t) := Real.exp_add _ _
  have hnorm : ‖principalMatrixValue A t‖ ≤
      B * C * Real.exp (α * T) * Real.exp (-α * t) := by
    calc
      ‖principalMatrixValue A t‖ = ‖principalMatrixValue A s * monodromyValue A T ^ k‖ :=
        congrArg norm (hts ▸ hx)
      _ ≤ ‖principalMatrixValue A s‖ * ‖monodromyValue A T ^ k‖ := norm_mul_le _ _
      _ ≤ B * (C * r ^ k) :=
        mul_le_mul (hb s hs) (hc k) (norm_nonneg _) hB.le
      _ ≤ B * (C * (Real.exp (α * T) * Real.exp (-α * t))) := by gcongr
      _ = _ := by ring
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))

lemma exponential_iff_geometric (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (hA : Continuous A) (T : ℝ) (hT : 0 < T) (hp : Function.Periodic A T) :
    ExponentiallyStable A ↔
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ GeometricBound (monodromyValue A T) r :=
  ⟨geometric_of_exponentiallyStable A hA T hT hp,
    exponentiallyStable_of_geometric A hA T hT hp⟩

/-- Identify the actual multiset roots with the spectrum used by the power
criteria, through the checked characteristic-polynomial/eigenvalue API. -/
lemma mem_roots_iff_spectrum (M : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    μ ∈ M.charpoly.roots ↔ μ ∈ spectrum ℂ M := by
  rw [Polynomial.mem_roots M.charpoly_monic.ne_zero,
    ← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact eigenvalueBridge M μ

lemma roots_strict_iff (M : Matrix (Fin n) (Fin n) ℂ) :
    (∀ μ ∈ M.charpoly.roots, ‖μ‖ < 1) ↔ StrictSpectrum M := by
  simp only [StrictSpectrum, mem_roots_iff_spectrum]

lemma roots_jordan_iff (M : Matrix (Fin n) (Fin n) ℂ) :
    ((∀ μ ∈ M.charpoly.roots, ‖μ‖ ≤ 1) ∧ UnitJordanChainsTrivial M) ↔
      JordanPowerCondition M := by
  simp only [JordanPowerCondition, mem_roots_iff_spectrum]

theorem complex_exponential_criterion :
    Specs.D13Unified.Ch08.MultiplierCriteria.ComplexExponentialCriterion := by
  intro n A T hA hT hp
  exact (exponential_iff_geometric A hA T hT hp).trans
    ((geometricCriterion _).trans (roots_strict_iff _).symm)

theorem real_exponential_criterion :
    Specs.D13Unified.Ch08.MultiplierCriteria.RealExponentialCriterion := by
  intro n A T hA hT hp
  exact (exponential_iff_geometric A hA T hT hp).trans
    ((realGeometricCriterion _).trans (roots_strict_iff _).symm)

theorem complex_lyapunov_criterion :
    Specs.D13Unified.Ch08.MultiplierCriteria.ComplexLyapunovCriterion := by
  intro n A T hA hT hp
  exact (lyapunov_iff_powerBounded A hA T hT hp).trans
    ((jordanBoundedCriterion _).trans (roots_jordan_iff _).symm)

theorem real_lyapunov_criterion :
    Specs.D13Unified.Ch08.MultiplierCriteria.RealLyapunovCriterion := by
  intro n A T hA hT hp
  exact (lyapunov_iff_powerBounded A hA T hT hp).trans
    ((realJordanBoundedCriterion _).trans (roots_jordan_iff _).symm)

theorem complex_instability :
    Specs.D13Unified.Ch08.MultiplierCriteria.ComplexInstability := by
  intro n A T hA hT hp hbad hstable
  obtain ⟨hμ, hchain⟩ := (complex_lyapunov_criterion n A T hA hT hp).mp hstable
  rcases hbad with ⟨μ, hm, hnorm⟩ | hc
  · exact (not_lt_of_ge (hμ μ hm)) hnorm
  · exact hc hchain

theorem real_instability :
    Specs.D13Unified.Ch08.MultiplierCriteria.RealInstability := by
  intro n A T hA hT hp hbad hstable
  obtain ⟨hμ, hchain⟩ := (real_lyapunov_criterion n A T hA hT hp).mp hstable
  rcases hbad with ⟨μ, hm, hnorm⟩ | hc
  · exact (not_lt_of_ge (hμ μ hm)) hnorm
  · exact hc hchain

/-- Transfer a uniform exponential estimate between equivalent nonnegative
size functions. This applies in particular to any equivalent state norm. -/
lemma exponential_estimate_transport {V : Type} (F : ℝ → V → V)
    (N P : V → ℝ)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hPN : ∀ x, P x ≤ c * N x) (hNP : ∀ x, N x ≤ d * P x)
    (h : ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x, N (F t x) ≤ C * Real.exp (-α * t) * N x) :
    ∃ C : ℝ, 0 < C ∧ ∃ α : ℝ, 0 < α ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x, P (F t x) ≤ C * Real.exp (-α * t) * P x := by
  obtain ⟨C, hC, α, hα, hb⟩ := h
  refine ⟨c * C * d, by positivity, α, hα, fun t ht x => ?_⟩
  calc
    P (F t x) ≤ c * N (F t x) := hPN _
    _ ≤ c * (C * Real.exp (-α * t) * N x) :=
      mul_le_mul_of_nonneg_left (hb t ht x) hc.le
    _ ≤ c * (C * Real.exp (-α * t) * (d * P x)) := by
      gcongr
      exact hNP x
    _ = _ := by ring

lemma lyapunov_estimate_transport {V : Type} (F : ℝ → V → V)
    (N P : V → ℝ) (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hPN : ∀ x, P x ≤ c * N x) (hNP : ∀ x, N x ≤ d * P x)
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x, N x < δ → ∀ t : ℝ, 0 ≤ t → N (F t x) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x, P x < δ → ∀ t : ℝ, 0 ≤ t → P (F t x) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ε / c) (div_pos hε hc)
  refine ⟨δ / d, div_pos hδ hd, fun x hx t ht => ?_⟩
  have hNx : N x < δ := (hNP x).trans_lt (by
    simpa only [mul_comm] using (lt_div_iff₀ hd).mp hx)
  calc
    P (F t x) ≤ c * N (F t x) := hPN _
    _ < ε := by have := (lt_div_iff₀ hc).mp (hb x hNx t ht); nlinarith

/-- The infinity norm used for matrix calculations imposes no restriction on
the fixed finite-dimensional norm in the source theorem. -/
theorem norm_independence :
    Specs.D13Unified.Ch08.MultiplierCriteria.NormIndependence := by
  intro 𝕂 _ n E _ _ e A
  let c : ℝ := max ‖e.toContinuousLinearMap‖ 1
  let d : ℝ := max ‖e.symm.toContinuousLinearMap‖ 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hPN (x : Fin n → 𝕂) : ‖e x‖ ≤ c * ‖x‖ :=
    (e.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hNP (x : Fin n → 𝕂) : ‖x‖ ≤ d * ‖e x‖ := by
    calc
      ‖x‖ = ‖e.symm (e x)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ d * ‖e x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  let F := fun t x => (principalMatrixValue A t).mulVec x
  exact ⟨⟨exponential_estimate_transport F _ _
      c d hc hd hPN hNP,
    exponential_estimate_transport F _ _
      d c hd hc hNP hPN⟩,
    ⟨lyapunov_estimate_transport F _ _ c d hc hd hPN hNP,
      lyapunov_estimate_transport F _ _ d c hd hc hNP hPN⟩⟩

end D13Unified.Ch08.MultiplierCriteria
