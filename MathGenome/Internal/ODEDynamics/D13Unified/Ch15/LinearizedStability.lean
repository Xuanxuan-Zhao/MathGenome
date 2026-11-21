import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LinearizedStability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.AdaptedNorm
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Module Filter
open scoped Topology Matrix.Norms.Operator
namespace D13Unified.Ch15.LinearizedStability
open D13Unified.Ch15.AdaptedNorm
open D13Unified.Ch15.DiscreteDefinitions
open D13Unified.Ch08.MatrixPowerCriteria

/-- Differentiability controls the nonlinear remainder in any equivalent norm. -/
lemma local_seminorm_contraction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → E} {z : E} {A : E →L[ℝ] E}
    (hF : HasFDerivAt F A z) (hfix : F z = z)
    (p : Seminorm ℝ E) (hp : Equivalent p) {a q : ℝ} (haq : a < q)
    (hA : ∀ v, p (A v) ≤ a * p v) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, ‖x - z‖ < r → p (F x - z) ≤ q * p (x - z) := by
  obtain ⟨C, hC, D, hD, hcomp⟩ := hp
  let ε := (q - a) / (D * C)
  have hε : 0 < ε := div_pos (sub_pos.mpr haq) (mul_pos hD hC)
  obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff.mp (hF.isLittleO.def hε)
  refine ⟨r, hr, fun x hx => ?_⟩
  have herr : ‖F x - F z - A (x - z)‖ ≤ ε * ‖x - z‖ :=
    hrem (by simpa only [dist_eq_norm] using hx)
  have heq : D * ε * C = q - a := by
    dsimp [ε]
    field_simp
  have herror : p (F x - F z - A (x - z)) ≤ (q - a) * p (x - z) := by
    calc
      _ ≤ D * ‖F x - F z - A (x - z)‖ := (hcomp _).2
      _ ≤ D * (ε * ‖x - z‖) := mul_le_mul_of_nonneg_left herr hD.le
      _ ≤ D * (ε * (C * p (x - z))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcomp _).1 hε.le) hD.le
      _ = _ := by rw [← mul_assoc, ← mul_assoc, heq]
  calc
    p (F x - z) = p (A (x - z) + (F x - F z - A (x - z))) := by
      congr 1
      rw [hfix]
      abel
    _ ≤ p (A (x - z)) + p (F x - F z - A (x - z)) := map_add_le_add p _ _
    _ ≤ a * p (x - z) + (q - a) * p (x - z) := add_le_add (hA _) herror
    _ = q * p (x - z) := by ring

/-- A local radial contraction in an equivalent norm traps a neighborhood,
and gives a geometric estimate in the original norm. -/
lemma iterate_bound_of_local_contraction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : E → E) (z : E) (U : Set E) (hU : U ∈ 𝓝 z)
    (p : Seminorm ℝ E) (hp : Equivalent p) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {r : ℝ} (hr : 0 < r)
    (hstep : ∀ x, ‖x - z‖ < r → p (F x - z) ≤ q * p (x - z)) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖x - z‖ < δ → ∀ n : ℕ,
      F^[n] x ∈ U ∧ ‖F^[n] x - z‖ ≤ C * q ^ n * ‖x - z‖ := by
  obtain ⟨C, hC, D, hD, hcomp⟩ := hp
  obtain ⟨s, hs, hsU⟩ := Metric.mem_nhds_iff.mp hU
  let t := min r s
  have ht : 0 < t := lt_min hr hs
  let δ := t / (C * D)
  have hδ : 0 < δ := div_pos ht (mul_pos hC hD)
  refine ⟨C * D, mul_pos hC hD, δ, hδ, fun x hx => ?_⟩
  have hinit : C * p (x - z) < t := by
    calc
      _ ≤ C * (D * ‖x - z‖) := mul_le_mul_of_nonneg_left (hcomp _).2 hC.le
      _ = (C * D) * ‖x - z‖ := by ring
      _ < t := (lt_div_iff₀ (mul_pos hC hD)).mp hx |> (by simpa [mul_comm] using ·)
  have hiter : ∀ n : ℕ, p (F^[n] x - z) ≤ q ^ n * p (x - z) := by
    intro n
    induction n with
    | zero => simp
    | succ n ihn =>
      have hnorm : ‖F^[n] x - z‖ < r := by
        calc
          _ ≤ C * p (F^[n] x - z) := (hcomp _).1
          _ ≤ C * (q ^ n * p (x - z)) := mul_le_mul_of_nonneg_left ihn hC.le
          _ ≤ C * p (x - z) := mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_left (apply_nonneg p _) (pow_le_one₀ hq.le hq1.le)) hC.le
          _ < t := hinit
          _ ≤ r := min_le_left _ _
      calc
        p (F^[n + 1] x - z) = p (F (F^[n] x) - z) := by rw [Function.iterate_succ_apply']
        _ ≤ q * p (F^[n] x - z) := hstep _ hnorm
        _ ≤ q * (q ^ n * p (x - z)) := mul_le_mul_of_nonneg_left ihn hq.le
        _ = q ^ (n + 1) * p (x - z) := by rw [pow_succ]; ring
  intro n
  have hsmall : ‖F^[n] x - z‖ < t := by
    calc
      _ ≤ C * p (F^[n] x - z) := (hcomp _).1
      _ ≤ C * (q ^ n * p (x - z)) := mul_le_mul_of_nonneg_left (hiter n) hC.le
      _ ≤ C * p (x - z) := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (apply_nonneg p _) (pow_le_one₀ hq.le hq1.le)) hC.le
      _ < t := hinit
  constructor
  · apply hsU
    show dist (F^[n] x) z < s
    rw [dist_eq_norm]
    exact hsmall.trans_le (min_le_right _ _)
  · calc
      _ ≤ C * p (F^[n] x - z) := (hcomp _).1
      _ ≤ C * (q ^ n * p (x - z)) := mul_le_mul_of_nonneg_left (hiter n) hC.le
      _ ≤ C * (q ^ n * (D * ‖x - z‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcomp _).2 (pow_nonneg hq.le n)) hC.le
      _ = _ := by ring

/-- The quantitative definition implies Lyapunov stability and attraction,
without any additional continuity assumption. -/
lemma stability_of_exponential_estimate {E : Type*} [NormedAddCommGroup E]
    {F : E → E} {z : E} (h : LocallyExponentiallyStable F z) :
    LyapunovStable F z ∧ AsymptoticallyStable F z := by
  obtain ⟨C, hC, q, hq, hq1, δ, hδ, hbound⟩ := h
  have hstable : LyapunovStable F z := by
    intro ε hε
    refine ⟨min δ (ε / C), lt_min hδ (div_pos hε hC), fun x hx n => ?_⟩
    rw [dist_eq_norm] at hx ⊢
    calc
      ‖F^[n] x - z‖ ≤ C * q ^ n * ‖x - z‖ := hbound x (hx.trans_le (min_le_left _ _)) n
      _ ≤ C * ‖x - z‖ := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hC.le (pow_le_one₀ hq.le hq1.le)) (norm_nonneg _)
      _ < ε := (lt_div_iff₀ hC).mp (hx.trans_le (min_le_right _ _)) |>
        (by simpa [mul_comm] using ·)
  have hattract : AttractsNeighborhood F z := by
    refine ⟨δ, hδ, fun x hx => ?_⟩
    rw [dist_eq_norm] at hx
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (hbound x hx)
    have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul C).mul_const ‖x - z‖
    simpa using ht
  exact ⟨hstable, hstable, hattract⟩

/-- Linearized attraction (paper.tex, `d13:15:linearized-stability`), retaining the actual open domain. -/
theorem linearizedAttraction : Specs.D13Unified.Ch15.LinearizedStability.linearizedAttraction := by
  intro E _ _ _ d b F U z hU hz hF hfix hρ
  let M := complexify (LinearMap.toMatrix b b (fderiv ℝ F z).toLinearMap)
  let R := spectralRadius ℂ M
  have hR : R < 1 := hρ
  have hRtop : R ≠ ⊤ := ne_top_of_lt (hR.trans_le le_top)
  have hRreal : R.toReal < 1 := by
    simpa using ENNReal.toReal_strict_mono (by simp : (1 : ENNReal) ≠ ⊤) hR
  obtain ⟨a, hRa, ha1⟩ := exists_between hRreal
  have ha : 0 < a := ENNReal.toReal_nonneg.trans_lt hRa
  have hRa' : R < ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_toReal hRtop]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).mpr hRa
  obtain ⟨p, hp, hA, _⟩ := upperReal b (fderiv ℝ F z).toLinearMap a hRa'
  obtain ⟨q, haq, hq1⟩ := exists_between ha1
  have hq : 0 < q := ha.trans haq
  have hderiv : HasFDerivAt F (fderiv ℝ F z) z :=
    hF.differentiableOn_one.hasFDerivAt (hU.mem_nhds hz)
  obtain ⟨r, hr, hstep⟩ := local_seminorm_contraction hderiv hfix p hp haq hA
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    iterate_bound_of_local_contraction F z U (hU.mem_nhds hz) p hp hq hq1 hr hstep
  have hexp : LocallyExponentiallyStable F z :=
    ⟨C, hC, q, hq, hq1, δ, hδ, fun x hx n => (hbound x hx n).2⟩
  obtain ⟨hstable, hasymptotic⟩ := stability_of_exponential_estimate hexp
  exact ⟨⟨C, hC, q, hq, hq1, δ, hδ, hbound⟩, hexp, hstable, hasymptotic⟩

end D13Unified.Ch15.LinearizedStability
