import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.SecantConvergence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SecantError
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace NumAnalysis206.Newton
open Set Filter
open scoped Topology
open NumAnalysis206.Approximation
open Specs.NumAnalysis206.Newton
open Specs.NumAnalysis206.Newton.SecantConvergence (RunProperties)

private theorem mem_radius_interval {p R r x : ℝ} (hrR : r ≤ R) (hx : |x - p| ≤ r) :
    x ∈ Icc (p - R) (p + R) := by
  have h := abs_le.mp hx
  constructor <;> linarith

/-- One non-root step is admissible, quantitatively contracts the current
error, and supplies a distinct next node still in the smaller interval. -/
private theorem secant_step_control
    {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ} {p R m M r : ℝ}
    (hD : IntervalJet (p - R) (p + R) 2 f D) (hp : f p = 0)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (p - R) (p + R), m ≤ |D 1 t| ∧ |D 2 t| ≤ M)
    (hr : 0 < r) (hrR : r ≤ R) (hq : M / (2 * m) * r < 1)
    {u v : ℝ} (hu : |u - p| ≤ r) (hv : |v - p| ≤ r)
    (huv : u ≠ v) (hfu : f u ≠ 0) (hfv : f v ≠ 0) :
    m ≤ |secantSlopeValue f u v| ∧
    |secantStepValue f u v - p| ≤ M / (2 * m) * |(v - p) * (u - p)| ∧
    |secantStepValue f u v - p| ≤ (M / (2 * m) * r) * |v - p| ∧
    |secantStepValue f u v - p| ≤ r ∧ secantStepValue f u v ≠ v := by
  have hui := mem_radius_interval hrR hu
  have hvi := mem_radius_interval hrR hv
  have hs := secant_slope_lower f D (p - R) (p + R) m u v hD
    (fun t ht => (hb t ht).1) hui hvi huv
  have hsne : secantSlopeValue f u v ≠ 0 := abs_pos.mp (hm.trans_le hs)
  have hup : u ≠ p := fun h => hfu (h ▸ hp)
  have hvp : v ≠ p := fun h => hfv (h ▸ hp)
  have hR : 0 ≤ R := hr.le.trans hrR
  have he := secant_error_bound f D (p - R) (p + R) m M p u v hD hp hm hM hb
    ⟨by linarith, by linarith⟩ hui hvi huv hup hvp
  have hC : 0 ≤ M / (2 * m) := by positivity
  have hc : |secantStepValue f u v - p| ≤ (M / (2 * m) * r) * |v - p| := by
    calc
      _ ≤ M / (2 * m) * |(v - p) * (u - p)| := he
      _ = (M / (2 * m) * |v - p|) * |u - p| := by rw [abs_mul]; ring
      _ ≤ (M / (2 * m) * |v - p|) * r :=
        mul_le_mul_of_nonneg_left hu (mul_nonneg hC (abs_nonneg _))
      _ = _ := by ring
  refine ⟨hs, he, hc, ?_, secantStep_ne_current f u v hfv hsne⟩
  exact hc.trans ((mul_le_mul_of_nonneg_right hq.le (abs_nonneg _)).trans (by simpa using hv))

/-- The state sequence is constructed by the shared exact iteration, rather
than assumed to be well-defined or convergent. -/
theorem secant_interval_convergence :
    Specs.NumAnalysis206.Newton.SecantConvergence.intervalConvergence := by
  classical
  intro f D p R m M r hD hp hm hM hb hr hrR hq u v hu hv huv
  let X := secantIteratesValue f u v
  have hzero : X 0 = (u, v) := rfl
  have hnext (n : ℕ) : X (n + 1) = secantTransitionValue f (X n) := rfl
  have hC : 0 ≤ M / (2 * m) := by positivity
  have hq0 : 0 ≤ M / (2 * m) * r := mul_nonneg hC hr.le
  have hi : ∀ n, |(X n).1 - p| ≤ r ∧ |(X n).2 - p| ≤ r ∧
      secantStateValidValue f (X n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hu, hv, ?_⟩
      change f u = 0 ∨ f v = 0 ∨ (u ≠ v ∧ secantSlopeValue f u v ≠ 0)
      by_cases hfu : f u = 0
      · exact Or.inl hfu
      by_cases hfv : f v = 0
      · exact Or.inr (Or.inl hfv)
      have hs := (secant_step_control hD hp hm hM hb hr hrR hq hu hv huv hfu hfv).1
      exact Or.inr (Or.inr ⟨huv, abs_pos.mp (hm.trans_le hs)⟩)
    | succ n ih =>
      by_cases hfu : f (X n).1 = 0
      · rw [hnext, secantTransition_of_first_root f (X n).1 (X n).2 hfu]
        exact ⟨ih.1, ih.1, Or.inl hfu⟩
      by_cases hfv : f (X n).2 = 0
      · rw [hnext, secantTransition_of_second_root f (X n).1 (X n).2 hfu hfv]
        exact ⟨ih.2.1, ih.2.1, Or.inl hfv⟩
      have hvalid := (secantStateValid_of_nonroots f (X n).1 (X n).2 hfu hfv).mp ih.2.2
      obtain ⟨hs, he, hc, hn, hne⟩ :=
        secant_step_control hD hp hm hM hb hr hrR hq ih.1 ih.2.1 hvalid.1 hfu hfv
      rw [hnext, secantTransition_of_nonroots f (X n).1 (X n).2 hfu hfv]
      refine ⟨ih.2.1, hn, Or.inr (Or.inr ⟨hne.symm, ?_⟩)⟩
      have hsnew := secant_slope_lower f D (p - R) (p + R) m
        (X n).2 (secantStepValue f (X n).1 (X n).2) hD (fun t ht => (hb t ht).1)
        (mem_radius_interval hrR ih.2.1) (mem_radius_interval hrR hn) hne.symm
      exact abs_pos.mp (hm.trans_le hsnew)
  have hcontrol (n : ℕ) (hfu : f (X n).1 ≠ 0) (hfv : f (X n).2 ≠ 0) :=
    secant_step_control hD hp hm hM hb hr hrR hq (hi n).1 (hi n).2.1
      ((secantStateValid_of_nonroots f (X n).1 (X n).2 hfu hfv).mp (hi n).2.2).1 hfu hfv
  change RunProperties f p r m M u v
  refine ⟨hi, ?_, ?_, ?_⟩
  · intro n hfu hfv
    obtain ⟨hs, he, hc, hn, hne⟩ := hcontrol n hfu hfv
    exact ⟨hs, (hnext n).trans (secantTransition_of_nonroots f _ _ hfu hfv), hne, he⟩
  · intro hMzero
    change f (X 1).1 = 0 ∨ f (X 1).2 = 0
    by_cases hfu : f u = 0
    · rw [show X 1 = (u, u) from secantTransition_of_first_root f u v hfu]
      exact Or.inl hfu
    by_cases hfv : f v = 0
    · rw [show X 1 = (v, v) from secantTransition_of_second_root f u v hfu hfv]
      exact Or.inl hfv
    have he := (hcontrol 0 hfu hfv).2.1
    have hstep : secantStepValue f u v = p := by
      change |secantStepValue f u v - p| ≤ _ at he
      rw [hMzero, zero_div, zero_mul] at he
      exact sub_eq_zero.mp (abs_nonpos_iff.mp he)
    rw [show X 1 = (v, secantStepValue f u v) from
      secantTransition_of_nonroots f u v hfu hfv]
    exact Or.inr (hstep ▸ hp)
  · by_cases hstop : ∃ N, SuccessfulSecantStopValue f N X
    · exact Or.inl hstop
    right
    have hnr (n : ℕ) : f (X n).1 ≠ 0 ∧ f (X n).2 ≠ 0 := by
      constructor
      · intro h; exact hstop ⟨n, Or.inl h⟩
      · intro h; exact hstop ⟨n, Or.inr h⟩
    have hrec (n : ℕ) : X (n + 1) = ((X n).2, secantStepValue f (X n).1 (X n).2) :=
      (hnext n).trans (secantTransition_of_nonroots f _ _ (hnr n).1 (hnr n).2)
    have hgeom (n : ℕ) : |(X n).2 - p| ≤ (M / (2 * m) * r) ^ n * |v - p| := by
      apply le_geom hq0 n
      intro k hk
      rw [hrec]
      exact (hcontrol k (hnr k).1 (hnr k).2).2.2.1
    have ht : Tendsto (fun n => (X n).2) atTop (𝓝 p) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const |v - p|
      simp only [zero_mul] at hlim
      apply squeeze_zero (fun n => dist_nonneg)
        (fun n => by simpa only [Real.dist_eq] using hgeom n) hlim
    have htfirst : Tendsto (fun n => (X n).1) atTop (𝓝 p) := by
      apply (tendsto_add_atTop_iff_nat 1).mp
      simpa only [hrec] using ht
    refine ⟨?_, htfirst, ht⟩
    intro n
    have hvalid := (secantStateValid_of_nonroots f (X n).1 (X n).2 (hnr n).1 (hnr n).2).mp
      (hi n).2.2
    exact ⟨(hnr n).1, (hnr n).2, hvalid⟩

/-- Every distinct starting pair in one sufficiently small closed neighborhood
has the proved stopping-or-convergence behavior, using only C² at the root. -/
theorem secant_local_convergence :
    Specs.NumAnalysis206.Newton.SecantConvergence.localConvergence := by
  intro f p hf hp hn
  obtain ⟨R, m, M, hR, hm, hM, hD, hb⟩ := secant_local_bounds f p hf hn
  let C := M / (2 * m)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let r := min R (1 / (C + 1))
  have hr : 0 < r := lt_min hR (one_div_pos.mpr (by linarith))
  have hrR : r ≤ R := min_le_left _ _
  have hqr : C * r < 1 := by
    have hsmall : r * (C + 1) ≤ 1 :=
      (le_div_iff₀ (by linarith : 0 < C + 1)).mp (min_le_right R (1 / (C + 1)))
    nlinarith
  refine ⟨R, m, M, r, hR, hm, hM, hr, hrR, hqr, hD, hb, ?_⟩
  have hb' : ∀ t ∈ Icc (p - R) (p + R),
      m ≤ |iteratedDeriv 1 f t| ∧ |iteratedDeriv 2 f t| ≤ M := by
    simpa [iteratedDeriv_succ] using hb
  intro u v hu hv huv
  exact secant_interval_convergence f (fun j => iteratedDeriv j f) p R m M r
    hD hp hm hM hb' hr hrR hqr u v hu hv huv

end NumAnalysis206.Newton
