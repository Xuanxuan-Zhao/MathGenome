import MathGenome.Internal.MultivariableAnalysis.D04.C01.EuclideanInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.CoordinateEstimates

/-! The Euclidean norm and coordinate sequence criteria, including dimension zero.
Completeness below is obtained by assembling the limits of real Cauchy sequences.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace D04

/-- Each coordinate is bounded by the maximum, with no nonempty-index hypothesis. -/
theorem coordinate_norm_le_maxNorm {n : ℕ} (x : E n) (i : Fin n) :
    ‖x i‖ ≤ maxNorm x := by
  rw [maxNorm_eq_coordinate_norm]
  exact norm_le_pi_norm (coordinates n x) i

theorem maxNorm_nonneg {n : ℕ} (x : E n) : 0 ≤ maxNorm x := by
  rw [maxNorm_eq_coordinate_norm]
  exact norm_nonneg _

/-- The maximum norm is at most the shared Euclidean norm. -/
theorem maxNorm_le_norm {n : ℕ} (x : E n) : maxNorm x ≤ ‖x‖ := by
  rw [maxNorm_eq_coordinate_norm]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (PiLp.norm_apply_le x)

/-- The sharp dimension-dependent comparison, also valid for the empty coordinate set. -/
theorem norm_le_sqrt_mul_maxNorm {n : ℕ} (x : E n) :
    ‖x‖ ≤ Real.sqrt (n : ℝ) * maxNorm x := by
  rw [norm_coordinates]
  calc
    Real.sqrt (∑ i, x i ^ 2) ≤ Real.sqrt (∑ _i : Fin n, maxNorm x ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      have h := coordinate_norm_le_maxNorm x i
      rw [Real.norm_eq_abs] at h
      exact (sq_abs (x i)).symm.trans_le
        (sq_le_sq₀ (abs_nonneg _) (maxNorm_nonneg x) |>.mpr h)
    _ = Real.sqrt ((n : ℝ) * maxNorm x ^ 2) := by simp
    _ = Real.sqrt (n : ℝ) * maxNorm x := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (maxNorm_nonneg x)]

theorem norm_triangle {n : ℕ} (x y : E n) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

theorem norm_reverse_triangle {n : ℕ} (x y : E n) :
    |‖x‖ - ‖y‖| ≤ ‖x - y‖ :=
  abs_norm_sub_norm_le x y

/-- The `PiLp` topology is the product topology of the same real coordinates. -/
theorem tendsto_iff_coordinate_tendsto {n : ℕ} (s : ℕ → E n) (x : E n) :
    Tendsto s atTop (𝓝 x) ↔ ∀ i : Fin n, Tendsto (fun k => s k i) atTop (𝓝 (x i)) := by
  constructor
  · intro h i
    exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt.tendsto.comp h
  · intro h
    have hc : Tendsto (fun k => fun i : Fin n => s k i) atTop (𝓝 (fun i => x i)) :=
      tendsto_pi_nhds.mpr h
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).continuousAt.tendsto.comp hc

/-- In particular the sequence criterion concerns convergence in the Euclidean norm. -/
theorem norm_tendsto_iff_coordinate_tendsto {n : ℕ} (s : ℕ → E n) (x : E n) :
    Tendsto (fun k => ‖s k - x‖) atTop (𝓝 0) ↔
      ∀ i : Fin n, Tendsto (fun k => s k i) atTop (𝓝 (x i)) := by
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  exact tendsto_iff_coordinate_tendsto s x

/-- Only scalar completeness is used to choose these limits. Empty coordinates
produce the unique vector of dimension zero without a separate assumption. -/
theorem coordinate_cauchySeq_has_limit {n : ℕ} (s : ℕ → E n)
    (h : ∀ i : Fin n, CauchySeq (fun k => s k i)) :
    ∃ x : E n, Tendsto s atTop (𝓝 x) := by
  have hr : ∀ i : Fin n, ∃ a : ℝ, Tendsto (fun k => s k i) atTop (𝓝 a) :=
    fun i => cauchySeq_tendsto_of_complete (h i)
  choose a ha using hr
  refine ⟨WithLp.toLp 2 a, (tendsto_iff_coordinate_tendsto s _).mpr ?_⟩
  exact ha

theorem cauchySeq_iff_coordinate_cauchySeq {n : ℕ} (s : ℕ → E n) :
    CauchySeq s ↔ ∀ i : Fin n, CauchySeq (fun k => s k i) := by
  constructor
  · intro h i
    rw [Metric.cauchySeq_iff] at h ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun k hk l hl => ?_⟩
    have hb := PiLp.norm_apply_le (s k - s l) i
    simpa only [dist_eq_norm, PiLp.sub_apply] using
      hb.trans_lt (by simpa only [dist_eq_norm] using hN k hk l hl)
  · intro h
    obtain ⟨x, hx⟩ := coordinate_cauchySeq_has_limit s h
    exact hx.cauchySeq

theorem cauchySeq_has_limit {n : ℕ} (s : ℕ → E n) (h : CauchySeq s) :
    ∃ x : E n, Tendsto s atTop (𝓝 x) :=
  coordinate_cauchySeq_has_limit s ((cauchySeq_iff_coordinate_cauchySeq s).mp h)

theorem euclidean_complete (n : ℕ) : CompleteSpace (E n) :=
  Metric.complete_of_cauchySeq_tendsto (fun s hs => cauchySeq_has_limit s hs)

end D04
