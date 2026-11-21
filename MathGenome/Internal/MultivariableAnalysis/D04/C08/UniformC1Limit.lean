import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.UniformC1Limit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Filter Topology
namespace D04

private theorem c1_data {m k : ℕ} {f : E m → E k} {B : Set (E m)}
    (hf : ∃ U : Set (E m), IsOpen U ∧ B ⊆ U ∧ CrOn 1 U f) :
    (∀ x ∈ B, HasFDerivAt f (totalDerivative f x) x) ∧
      ContinuousOn (totalDerivative f) B := by
  obtain ⟨U, hU, hBU, hf⟩ := hf
  change TotalDifferentiableOn U f ∧ ContinuousOn (totalDerivative f) U at hf
  refine ⟨fun x hx => ?_, hf.2.mono hBU⟩
  obtain ⟨A, hA⟩ := hf.1 x (hBU hx)
  rw [totalDerivative_eq U f A x hA]
  exact (hasTotalDerivative_iff_hasFDerivAt U f A x hU (hBU hx)).mp hA

/-- The segment mean-value bound applied to the difference of two maps. -/
private theorem c1_difference_bound {m k : ℕ} (p : E m) (r : ℝ) (hr : 0 ≤ r)
    (f g : E m → E k) (df dg : E m → E m →L[ℝ] E k)
    (hf : ∀ x ∈ Metric.closedBall p r, HasFDerivAt f (df x) x)
    (hg : ∀ x ∈ Metric.closedBall p r, HasFDerivAt g (dg x) x)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Metric.closedBall p r, ‖df x - dg x‖ ≤ C)
    (x : E m) (hx : x ∈ Metric.closedBall p r) :
    ‖f x - g x‖ ≤ ‖f p - g p‖ + r * C := by
  have hv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy => ((hf y hy).sub (hg y hy)).hasFDerivWithinAt) hb
    (convex_closedBall p r) (Metric.mem_closedBall_self hr) hx
  have hxnorm : ‖x - p‖ ≤ r := by simpa [dist_eq_norm] using hx
  calc
    ‖f x - g x‖ ≤ ‖f p - g p‖ + ‖(f x - g x) - (f p - g p)‖ :=
      norm_le_insert' _ _
    _ ≤ ‖f p - g p‖ + C * ‖x - p‖ := add_le_add_right hv _
    _ ≤ ‖f p - g p‖ + r * C := by nlinarith [mul_le_mul_of_nonneg_left hxnorm hC]

/-- Uniform Cauchy convergence on the whole closed ball, including its boundary. -/
private theorem c1_uniformCauchy {m k : ℕ} (p : E m) (r : ℝ) (hr : 0 ≤ r)
    (f : ℕ → E m → E k) (G : E m → E m →L[ℝ] E k)
    (hf : ∀ j, ∃ U : Set (E m), IsOpen U ∧ Metric.closedBall p r ⊆ U ∧ CrOn 1 U (f j))
    (ha : ∃ a : E k, Tendsto (fun j => f j p) atTop (𝓝 a))
    (hG : TendstoUniformlyOn (fun j => totalDerivative (f j)) G atTop
      (Metric.closedBall p r)) : UniformCauchySeqOn f atTop (Metric.closedBall p r) := by
  obtain ⟨a, ha⟩ := ha
  have hc := Metric.cauchySeq_iff.mp ha.cauchySeq
  have hd := Metric.uniformCauchySeqOn_iff.mp hG.uniformCauchySeqOn
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  let δ := ε / (2 * (r + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := hd δ hδ
  refine ⟨max N M, fun j hj l hl x hx => ?_⟩
  have hbase := hN j (le_trans (le_max_left _ _) hj) l (le_trans (le_max_left _ _) hl)
  have hbound : ∀ y ∈ Metric.closedBall p r,
      ‖totalDerivative (f j) y - totalDerivative (f l) y‖ ≤ δ := by
    intro y hy
    have hh := hM j (le_trans (le_max_right _ _) hj) l (le_trans (le_max_right _ _) hl) y hy
    simpa [dist_eq_norm] using hh.le
  have he := c1_difference_bound p r hr (f j) (f l) _ _
    (c1_data (hf j)).1 (c1_data (hf l)).1 δ hδ.le hbound x hx
  rw [dist_eq_norm] at hbase ⊢
  have hdr : r * δ < ε / 2 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (r + 1))).mpr
    nlinarith
  linarith

/-- Uniform C¹ limit on a closed Euclidean ball. The differentiation theorem
used below is proved from segment mean-value bounds for difference quotients;
it asserts a total Fréchet derivative, not merely coordinate derivatives. -/
theorem uniform_c1_limit : Specs.D04.C08.UniformC1Limit.uniform_c1_limitType := by
  intro m k p r hr f G hf ha hG
  have hc := c1_uniformCauchy p r hr f G hf ha hG
  have hpw : ∀ x : E m, ∃ y : E k, x ∈ Metric.closedBall p r →
      Tendsto (fun j => f j x) atTop (𝓝 y) := by
    intro x
    by_cases hx : x ∈ Metric.closedBall p r
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hc.cauchySeq hx)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose F hF using hpw
  have hFu : TendstoUniformlyOn f F atTop (Metric.closedBall p r) :=
    hc.tendstoUniformlyOn_of_tendsto hF
  have hGc : ContinuousOn G (Metric.closedBall p r) :=
    hG.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun j => (c1_data (hf j)).2)))
  have hD : ∀ x ∈ interior (Metric.closedBall p r), HasFDerivAt F (G x) x := by
    intro x hx
    exact hasFDerivAt_of_tendstoUniformlyOn isOpen_interior
      (hG.mono interior_subset)
      (fun j y hy => (c1_data (hf j)).1 y (interior_subset hy))
      (fun y hy => hF y (interior_subset hy)) hx
  have htotal : ∀ x ∈ interior (Metric.closedBall p r),
      HasTotalDerivative (interior (Metric.closedBall p r)) F (G x) x := by
    intro x hx
    exact (hasTotalDerivative_iff_hasFDerivAt _ _ _ _ isOpen_interior hx).mpr (hD x hx)
  have heq : EqOn (totalDerivative F) G (interior (Metric.closedBall p r)) := by
    intro x hx
    exact (hD x hx).fderiv
  refine ⟨F, hFu, hGc, ?_, fun x hx => ⟨htotal x hx, heq hx⟩⟩
  change TotalDifferentiableOn _ F ∧ ContinuousOn (totalDerivative F) _
  exact ⟨fun x hx => ⟨G x, htotal x hx⟩,
    (hGc.mono interior_subset).congr (fun x hx => heq hx)⟩

/-- The quantitative uniform Cauchy estimate, with actual real suprema. -/
theorem uniform_c1_cauchy_estimate :
    Specs.D04.C08.UniformC1Limit.uniform_c1_cauchy_estimateType := by
  intro m k p r hr f hf j l
  let B := Metric.closedBall p r
  let d := fun x => ‖totalDerivative (f j) x - totalDerivative (f l) x‖
  have hp : p ∈ B := Metric.mem_closedBall_self hr
  have hdc : ContinuousOn d B := ((c1_data (hf j)).2.sub (c1_data (hf l)).2).norm
  have hdb : BddAbove (d '' B) := (isCompact_closedBall p r).bddAbove_image hdc
  have hdn : 0 ≤ sSup (d '' B) :=
    (norm_nonneg _).trans (le_csSup hdb (mem_image_of_mem d hp))
  apply csSup_le (Nonempty.image _ ⟨p, hp⟩)
  rintro _ ⟨x, hx, rfl⟩
  exact c1_difference_bound p r hr (f j) (f l) _ _
    (c1_data (hf j)).1 (c1_data (hf l)).1 (sSup (d '' B)) hdn
    (fun y hy => le_csSup hdb (mem_image_of_mem d hy)) x hx

/-- The radius-zero specialization does not impose positive-dimensional
nontriviality on the main uniform convergence theorem. -/
theorem uniform_c1_zero_radius :
    Specs.D04.C08.UniformC1Limit.uniform_c1_zero_radiusType := by
  intro m k p f F
  rw [Metric.closedBall_zero]
  refine ⟨tendstoUniformlyOn_singleton_iff_tendsto, ?_⟩
  intro hm
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact interior_singleton p

/-- All zero-dimensional derivative operators vanish, including the limiting G. -/
theorem uniform_c1_zero_dimension :
    Specs.D04.C08.UniformC1Limit.uniform_c1_zero_dimensionType := by
  intro k p r hr F G
  have hB : Metric.closedBall p r = univ := by
    ext x
    simp [Subsingleton.elim x p, hr]
  rw [hB, interior_univ]
  have hd : ∀ x, HasFDerivAt F (0 : E 0 →L[ℝ] E k) x :=
    fun x => hasFDerivAt_of_subsingleton F x
  refine ⟨rfl, ?_, fun x => ⟨(hd x).fderiv, Subsingleton.elim _ _⟩⟩
  change TotalDifferentiableOn univ F ∧ ContinuousOn (totalDerivative F) univ
  refine ⟨fun x hx => ⟨0,
    (hasTotalDerivative_iff_hasFDerivAt _ _ _ _ isOpen_univ hx).mpr (hd x)⟩, ?_⟩
  exact continuousOn_const.congr (fun x _ => (hd x).fderiv)

end D04
