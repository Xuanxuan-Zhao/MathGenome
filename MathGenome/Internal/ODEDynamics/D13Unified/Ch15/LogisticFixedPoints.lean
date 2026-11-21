import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LogisticFixedPoints
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LinearizedStability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LinearizedInstability
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology
namespace D13Unified.Ch15.LogisticFixedPoints
open D13Unified.Ch15.DiscreteDefinitions

abbrev logisticMap : Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMapType :=
  Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap

lemma hasDerivAt_map (μ x : ℝ) : HasDerivAt (logisticMap μ) (μ * (1 - 2 * x)) x := by
  convert ((hasDerivAt_id x).const_mul μ).mul
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1 <;> try (funext y)
  all_goals dsimp [logisticMap, Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap]
  all_goals ring

theorem intervalInvariant : Specs.D13Unified.Ch15.LogisticFixedPoints.intervalInvariant := by
  intro μ hμ hμ4 y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change 0 ≤ μ * x * (1 - x) ∧ μ * x * (1 - x) ≤ 1
  have hnonneg : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hquarter : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  constructor
  · nlinarith [mul_nonneg hμ hnonneg]
  · nlinarith [mul_le_mul_of_nonneg_left hquarter hμ]

theorem fixedPoints_zeroParameter : Specs.D13Unified.Ch15.LogisticFixedPoints.fixedPoints_zeroParameter := by
  intro x
  simp [Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap, eq_comm]

theorem fixedPoints_nonzeroParameter : Specs.D13Unified.Ch15.LogisticFixedPoints.fixedPoints_nonzeroParameter := by
  intro μ hμ x
  change μ * x * (1 - x) = x ↔ x = 0 ∨ x = 1 - μ⁻¹
  constructor
  · intro h
    have hf : x * (μ * (1 - x) - 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hf with hx | hx
    · exact Or.inl hx
    · right
      apply (mul_left_cancel₀ hμ)
      field_simp
      nlinarith
  · rintro (rfl | rfl)
    · ring
    · field_simp
      ring

theorem coincident_fixedPoints : Specs.D13Unified.Ch15.LogisticFixedPoints.coincident_fixedPoints := by
  intro μ hμ
  constructor
  · intro h
    have hi : μ⁻¹ = 1 := by linarith
    have := mul_inv_cancel₀ hμ
    rw [hi, mul_one] at this
    exact this
  · rintro rfl
    norm_num

theorem secondFixedPoint_mem : Specs.D13Unified.Ch15.LogisticFixedPoints.secondFixedPoint_mem := by
  intro μ hμ
  have hp : 0 < μ := by linarith
  have hi : μ⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr hμ
  exact ⟨by linarith, by linarith [inv_pos.mpr hp]⟩

theorem derivative_zero : Specs.D13Unified.Ch15.LogisticFixedPoints.derivative_zero := by
  intro μ
  simpa using hasDerivAt_map μ 0

theorem derivative_second : Specs.D13Unified.Ch15.LogisticFixedPoints.derivative_second := by
  intro μ hμ
  convert hasDerivAt_map μ (1 - μ⁻¹) using 1
  field_simp
  ring

/-- Scalar derivative contraction, with the canonical exponential and asymptotic conclusions. -/
lemma attracting_of_derivative {F : ℝ → ℝ} {p d : ℝ}
    (hfix : F p = p) (hd : HasDerivAt F d p) (hlt : ‖d‖ < 1) :
    LocallyExponentiallyStable F p ∧ AsymptoticallyStable F p := by
  let q := (‖d‖ + 1) / 2
  have hq : 0 < q := by dsimp only [q]; positivity
  have hdq : ‖d‖ < q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  have hp : AdaptedNorm.Equivalent (normSeminorm ℝ ℝ) :=
    ⟨1, by norm_num, 1, by norm_num, by intro v; simp⟩
  obtain ⟨r, hr, hstep⟩ := LinearizedStability.local_seminorm_contraction
    hd.hasFDerivAt hfix (normSeminorm ℝ ℝ) hp hdq (by
      intro v
      simp [norm_mul, mul_comm])
  obtain ⟨C, hC, δ, hδ, hbound⟩ := LinearizedStability.iterate_bound_of_local_contraction
    F p Set.univ (by simp) (normSeminorm ℝ ℝ) hp hq hq1 hr hstep
  have he : LocallyExponentiallyStable F p :=
    ⟨C, hC, q, hq, hq1, δ, hδ, fun x hx n => (hbound x hx n).2⟩
  exact ⟨he, (LinearizedStability.stability_of_exponential_estimate he).2⟩

/-- A derivative larger than one in modulus expands distance locally, hence every
punctured orbit has a finite first exit, not just a selected unstable orbit. -/
lemma repelling_of_derivative {F : ℝ → ℝ} {p d : ℝ}
    (hfix : F p = p) (hd : HasDerivAt F d p) (hgt : 1 < ‖d‖) :
    Repelling F p := by
  let η := (‖d‖ - 1) / 2
  let c := (‖d‖ + 1) / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  have hc : 1 < c := by dsimp only [c]; linarith
  obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff.mp (hd.hasFDerivAt.isLittleO.def hη)
  have hstep : ∀ x, ‖x - p‖ < r → c * ‖x - p‖ ≤ ‖F x - p‖ := by
    intro x hx
    have he := hrem (by simpa only [dist_eq_norm] using hx)
    have he' : ‖F x - p - (x - p) * d‖ ≤ η * ‖x - p‖ := by
      simpa [hfix] using he
    have ht := norm_sub_le (F x - p - (x - p) * d) (F x - p)
    have hn : ‖(F x - p - (x - p) * d) - (F x - p)‖ = ‖d‖ * ‖x - p‖ := by
      rw [sub_sub_cancel_left, norm_neg, norm_mul, mul_comm]
    rw [hn] at ht
    dsimp only [η, c] at *
    nlinarith
  refine ⟨r, hr, fun x hxpos hxr => ?_⟩
  let G := fun v => F (p + v) - p
  obtain ⟨N, hN, hexit, hprior⟩ := LinearizedInstability.firstExit_of_cone
    G (fun v : ℝ => ‖v‖) (fun _ => 0) r c 1 hc (by norm_num)
    (by intro v; simp) (by
      intro v hv _
      refine ⟨norm_nonneg _, ?_⟩
      simpa [G] using hstep (p + v) (by simpa using hv))
    (x - p) hxr (norm_nonneg _) hxpos
  refine ⟨N, hN, ?_, ?_⟩
  · simpa [G, LinearizedInstability.translated_iterate] using hexit
  · intro n hn
    simpa [G, LinearizedInstability.translated_iterate] using hprior n hn

lemma Repelling.not_lyapunovStable {F : ℝ → ℝ} {p : ℝ} (h : Repelling F p) :
    ¬ LyapunovStable F p := by
  obtain ⟨r, hr, hexit⟩ := h
  intro hs
  obtain ⟨δ, hδ, hstay⟩ := hs r hr
  let t := min δ r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ r]
  have htr : t < r := by dsimp [t]; linarith [min_le_right δ r]
  have hn : ‖(p + t) - p‖ = t := by simp [Real.norm_eq_abs, ht.le]
  obtain ⟨N, _, hN, _⟩ := hexit (p + t) (by rw [hn]; exact ht) (by rw [hn]; exact htr)
  have hh := hstay (p + t) (by rw [dist_eq_norm, hn]; exact htδ) N
  rw [dist_eq_norm] at hh
  exact hh.not_ge hN

theorem zero_attracting : Specs.D13Unified.Ch15.LogisticFixedPoints.zero_attracting := by
  intro μ hμ hμ1
  apply attracting_of_derivative (by simp [Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap]) (derivative_zero μ)
  simpa [Real.norm_eq_abs, abs_of_nonneg hμ] using hμ1

theorem second_attracting : Specs.D13Unified.Ch15.LogisticFixedPoints.second_attracting := by
  intro μ hμ1 hμ3
  have hμ : μ ≠ 0 := by linarith
  apply attracting_of_derivative ((fixedPoints_nonzeroParameter μ hμ _).mpr (Or.inr rfl))
    (derivative_second μ hμ)
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

theorem zero_repelling : Specs.D13Unified.Ch15.LogisticFixedPoints.zero_repelling := by
  intro μ hμ1
  have h : Repelling (logisticMap μ) 0 := repelling_of_derivative
    (by simp [Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap])
    (derivative_zero μ) (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hμ1)
  exact ⟨h, h.not_lyapunovStable⟩

theorem second_repelling : Specs.D13Unified.Ch15.LogisticFixedPoints.second_repelling := by
  intro μ hμ3
  have hμ : μ ≠ 0 := by linarith
  have h : Repelling (logisticMap μ) (1 - μ⁻¹) := repelling_of_derivative
    ((fixedPoints_nonzeroParameter μ hμ _).mpr (Or.inr rfl)) (derivative_second μ hμ)
    (by rw [Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
  exact ⟨h, h.not_lyapunovStable⟩

end D13Unified.Ch15.LogisticFixedPoints

