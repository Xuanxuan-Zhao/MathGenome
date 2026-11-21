import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarnackInequality
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicFoundation
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open Complex Metric Real Filter Set InnerProductSpace
open scoped Topology

namespace D12Complex.HarnackInequality

/-- The elementary two-sided bound for the Poisson kernel on a circle. -/
lemma poisson_kernel_bounds {a z ζ : ℂ} {s : ℝ}
    (hz : ‖z - a‖ < s) (hζ : ‖ζ - a‖ = s) :
    (s - ‖z - a‖) / (s + ‖z - a‖) ≤ poissonKernel a z ζ ∧
    poissonKernel a z ζ ≤ (s + ‖z - a‖) / (s - ‖z - a‖) := by
  let r := ‖z - a‖
  have hr : 0 ≤ r := norm_nonneg _
  have hs : 0 < s := lt_of_le_of_lt hr hz
  have hminus : 0 < s - r := sub_pos.mpr hz
  have hplus : 0 < s + r := by positivity
  have hlo : s - r ≤ ‖ζ - z‖ := by
    have ht := norm_sub_norm_le (ζ - a) (z - a)
    rw [hζ] at ht
    simpa only [sub_sub_sub_cancel_right] using ht
  have hhi : ‖ζ - z‖ ≤ s + r := by
    calc
      ‖ζ - z‖ = ‖(ζ - a) - (z - a)‖ := by congr 1; abel
      _ ≤ ‖ζ - a‖ + ‖z - a‖ := norm_sub_le _ _
      _ = s + r := by rw [hζ]
  have hd : 0 < ‖ζ - z‖ := lt_of_lt_of_le hminus hlo
  rw [poissonKernel_def, hζ, sub_sub_sub_cancel_right]
  change (s - r) / (s + r) ≤ (s ^ 2 - r ^ 2) / ‖ζ - z‖ ^ 2 ∧
    (s ^ 2 - r ^ 2) / ‖ζ - z‖ ^ 2 ≤ (s + r) / (s - r)
  constructor
  · apply (div_le_div_iff₀ hplus (sq_pos_of_pos hd)).mpr
    have hsq : ‖ζ - z‖ ^ 2 ≤ (s + r) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hminus.le (sub_nonneg.mpr hsq)]
  · apply (div_le_div_iff₀ (sq_pos_of_pos hd) hminus).mpr
    have hsq : (s - r) ^ 2 ≤ ‖ζ - z‖ ^ 2 := by nlinarith
    nlinarith [mul_nonneg hplus.le (sub_nonneg.mpr hsq)]

/-- Comparison on an interior circle; its closed disk lies in U. -/
lemma harnack_interior_circle {U : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u)
    (hn : ∀ w ∈ U, 0 ≤ u w) {a z : ℂ} {s : ℝ}
    (hs : 0 < s) (hsub : closedBall a s ⊆ U) (hz : z ∈ ball a s) :
    (s - ‖z - a‖) / (s + ‖z - a‖) * u a ≤ u z ∧
    u z ≤ (s + ‖z - a‖) / (s - ‖z - a‖) * u a := by
  have hh := ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hu.1).mp hu).mono hsub
  have hc : ContinuousOn u (sphere a s) :=
    hu.2.1.continuousOn.mono (sphere_subset_closedBall.trans hsub)
  have hi : CircleIntegrable u a s := hc.circleIntegrable hs.le
  have hw : z ∉ sphere a |s| := by
    simpa only [mem_sphere_iff_norm, abs_of_pos hs] using
      (show ‖z - a‖ < s by simpa only [mem_ball_iff_norm] using hz).ne
  have hk : ContinuousOn (poissonKernel a z) (sphere a s) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (by simpa only [abs_of_pos hs] using continuousOn_herglotzRieszKernel_sphere hw)
  have hki : CircleIntegrable (fun ζ => poissonKernel a z ζ * u ζ) a s :=
    (hk.mul hc).circleIntegrable hs.le
  have hm : circleAverage u a s = u a := by
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    simpa only [abs_of_pos hs] using hh
  have hp : circleAverage (fun ζ => poissonKernel a z ζ * u ζ) a s = u z := by
    exact hh.circleAverage_poissonKernel_smul hz
  have hscale (c : ℝ) : circleAverage (fun ζ => c * u ζ) a s = c * u a := by
    simpa only [smul_eq_mul, hm] using (circleAverage_fun_smul (a := c) (f := u) (c := a) (R := s))
  have hci (c : ℝ) : CircleIntegrable (fun ζ => c * u ζ) a s :=
    (continuousOn_const.mul hc).circleIntegrable hs.le
  constructor
  · rw [← hscale ((s - ‖z - a‖) / (s + ‖z - a‖)), ← hp]
    apply circleAverage_mono (hci _) hki
    intro ζ hζ
    have hζ' : ‖ζ - a‖ = s := by simpa [mem_sphere_iff_norm, abs_of_pos hs] using hζ
    exact mul_le_mul_of_nonneg_right
      (poisson_kernel_bounds (by simpa only [mem_ball_iff_norm] using hz) hζ').1
      (hn ζ (hsub (sphere_subset_closedBall (by simpa [abs_of_pos hs] using hζ))))
  · rw [← hscale ((s + ‖z - a‖) / (s - ‖z - a‖)), ← hp]
    apply circleAverage_mono hki (hci _)
    intro ζ hζ
    have hζ' : ‖ζ - a‖ = s := by simpa [mem_sphere_iff_norm, abs_of_pos hs] using hζ
    exact mul_le_mul_of_nonneg_right
      (poisson_kernel_bounds (by simpa only [mem_ball_iff_norm] using hz) hζ').2
      (hn ζ (hsub (sphere_subset_closedBall (by simpa [abs_of_pos hs] using hζ))))

/-- Pass through interior radii, so no radius-R boundary data are needed. -/
theorem harnack_disk : Specs.D12Complex.Ch13.HarnackInequality.harnack_disk_type := by
  intro u a R hR hu hn z hz
  have hr : ‖z - a‖ < R := by simpa only [mem_ball_iff_norm] using hz
  have hminus : R - ‖z - a‖ ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  have hplus : R + ‖z - a‖ ≠ 0 := ne_of_gt (by positivity)
  have hl : Tendsto (fun s : ℝ => (s - ‖z - a‖) / (s + ‖z - a‖) * u a)
      (𝓝[<] R) (𝓝 ((R - ‖z - a‖) / (R + ‖z - a‖) * u a)) :=
    (((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.add continuousAt_const) hplus).mul continuousAt_const).tendsto.mono_left
        nhdsWithin_le_nhds
  have hh : Tendsto (fun s : ℝ => (s + ‖z - a‖) / (s - ‖z - a‖) * u a)
      (𝓝[<] R) (𝓝 ((R + ‖z - a‖) / (R - ‖z - a‖) * u a)) :=
    (((continuousAt_id.add continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) hminus).mul continuousAt_const).tendsto.mono_left
        nhdsWithin_le_nhds
  have hb : ∀ᶠ s : ℝ in 𝓝[<] R,
      (s - ‖z - a‖) / (s + ‖z - a‖) * u a ≤ u z ∧
      u z ≤ (s + ‖z - a‖) / (s - ‖z - a‖) * u a := by
    filter_upwards [Ioo_mem_nhdsLT hr] with s hs
    exact harnack_interior_circle hu hn
      (lt_of_le_of_lt (norm_nonneg _) hs.1) (closedBall_subset_ball hs.2)
      (by simpa only [mem_ball_iff_norm] using hs.1)
  exact ⟨le_of_tendsto hl (hb.mono fun _ h => h.1),
    ge_of_tendsto hh (hb.mono fun _ h => h.2)⟩

/-- A fixed factor works throughout a sufficiently small disk, uniformly in u. -/
lemma local_harnack_comparison {Ω : Set ℂ} (hΩ : IsOpen Ω) {x : ℂ} (hx : x ∈ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ball x δ ⊆ Ω ∧
      ∀ y ∈ ball x δ, ∀ u : ℂ → ℝ, HarmonicOn Ω u →
        (∀ w ∈ Ω, 0 ≤ u w) → u y ≤ 3 * u x ∧ u x ≤ 3 * u y := by
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hΩ x hx
  refine ⟨R / 2, half_pos hR, (ball_subset_ball (by linarith)).trans hsub, ?_⟩
  intro y hy u hu hn
  have hur : HarmonicOn (ball x R) u :=
    ⟨isOpen_ball, hu.2.1.mono hsub, fun w hw => hu.2.2 w (hsub hw)⟩
  have hr : ‖y - x‖ < R / 2 := by simpa only [mem_ball_iff_norm] using hy
  have hrR : ‖y - x‖ < R := by linarith
  have hb := harnack_disk u x R hR hur (fun w hw => hn w (hsub hw)) y
    (by simpa only [mem_ball_iff_norm] using hrR)
  have hm : 0 < R - ‖y - x‖ := by linarith
  have hp : 0 < R + ‖y - x‖ := by positivity
  have hrup : (R + ‖y - x‖) / (R - ‖y - x‖) ≤ 3 :=
    (div_le_iff₀ hm).mpr (by linarith)
  have hrlo : (1 : ℝ) / 3 ≤ (R - ‖y - x‖) / (R + ‖y - x‖) :=
    (le_div_iff₀ hp).mpr (by linarith)
  have hnx := hn x hx
  refine ⟨hb.2.trans (mul_le_mul_of_nonneg_right hrup hnx), ?_⟩
  have hh := (mul_le_mul_of_nonneg_right hrlo hnx).trans hb.1
  linarith

/-- Existence of one comparison factor for every nonnegative harmonic function.
Both inequalities use multiplication, so zeros cause no division problem. -/
def HarnackComparable (Ω : Set ℂ) (x y : ℂ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ u : ℂ → ℝ, HarmonicOn Ω u →
    (∀ w ∈ Ω, 0 ≤ u w) → u y ≤ C * u x ∧ u x ≤ C * u y

lemma HarnackComparable.symm {Ω : Set ℂ} {x y : ℂ}
    (h : HarnackComparable Ω x y) : HarnackComparable Ω y x := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun u hu hn => ⟨(h u hu hn).2, (h u hu hn).1⟩⟩

lemma HarnackComparable.trans {Ω : Set ℂ} {x y z : ℂ}
    (hxy : HarnackComparable Ω x y) (hyz : HarnackComparable Ω y z) :
    HarnackComparable Ω x z := by
  obtain ⟨C, hC, hxy⟩ := hxy
  obtain ⟨D, hD, hyz⟩ := hyz
  have hC0 : 0 ≤ C := by linarith
  have hD0 : 0 ≤ D := by linarith
  refine ⟨C * D, one_le_mul_of_one_le_of_one_le hC hD, ?_⟩
  intro u hu hn
  obtain ⟨hy, hx⟩ := hxy u hu hn
  obtain ⟨hz, hy'⟩ := hyz u hu hn
  constructor
  · calc
      u z ≤ D * u y := hz
      _ ≤ D * (C * u x) := mul_le_mul_of_nonneg_left hy hD0
      _ = (C * D) * u x := by ring
  · calc
      u x ≤ C * u y := hx
      _ ≤ C * (D * u z) := mul_le_mul_of_nonneg_left hy' hC0
      _ = (C * D) * u z := by ring

/-- Open-and-closed propagation is a Harnack chain argument without choosing
individual polygon vertices. The comparison relation is locally universal. -/
lemma harnack_comparable_of_preconnected {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) {a b : ℂ} (ha : a ∈ Ω) (hb : b ∈ Ω) :
    HarnackComparable Ω a b := by
  apply hc.induction₂' (HarnackComparable Ω) ?_ ?_ ha hb
  · intro x hx
    obtain ⟨δ, hδ, _, hlocal⟩ := local_harnack_comparison hΩ hx
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [ball_mem_nhds x hδ] with y hy
    have hxy : HarnackComparable Ω x y := ⟨3, by norm_num, hlocal y hy⟩
    exact ⟨hxy, hxy.symm⟩
  · intro x y z _ _ _ hxy hyz
    exact hxy.trans hyz

/-- A neighborhood of each point has one factor relative to the basepoint. -/
lemma neighborhood_comparison {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {a : ℂ} (ha : a ∈ Ω) (x : Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ z ∈ ball (x : ℂ) δ, ∀ u : ℂ → ℝ, HarmonicOn Ω u →
        (∀ w ∈ Ω, 0 ≤ u w) → u z ≤ C * u a ∧ u a ≤ C * u z := by
  obtain ⟨δ, hδ, _, hlocal⟩ := local_harnack_comparison hΩ x.property
  obtain ⟨C, hC, hcomp⟩ := harnack_comparable_of_preconnected hΩ hc ha x.property
  refine ⟨δ, hδ, 3 * C, by linarith, ?_⟩
  intro z hz u hu hn
  obtain ⟨hzx, hxz⟩ := hlocal z hz u hu hn
  obtain ⟨hxa, hax⟩ := hcomp u hu hn
  have hC0 : 0 ≤ C := by linarith
  constructor
  · calc
      u z ≤ 3 * u x := hzx
      _ ≤ 3 * (C * u a) := mul_le_mul_of_nonneg_left hxa (by norm_num)
      _ = (3 * C) * u a := by ring
  · calc
      u a ≤ C * u x := hax
      _ ≤ C * (3 * u z) := mul_le_mul_of_nonneg_left hxz hC0
      _ = (3 * C) * u z := by ring

/-- A finite subcover makes the comparison constant uniform over K and u. -/
theorem harnack_compact : Specs.D12Complex.Ch13.HarnackInequality.harnack_compact_type := by
  classical
  intro Ω hΩ a ha K hK hKΩ
  choose δ hδ C hC hcomp using neighborhood_comparison hΩ.2.1 hΩ.2.2 ha
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : Ω => ball (x : ℂ) (δ x))
    (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hKΩ hz⟩, mem_ball_self (hδ _)⟩)
  let M : ℝ := 1 + ∑ x ∈ t, C x
  have hC0 (x : Ω) : 0 ≤ C x := (by norm_num : (0 : ℝ) ≤ 1).trans (hC x)
  have hM : 1 ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun x _ => hC0 x)
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨M, hM, ?_⟩
  intro u hu hn z hz
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (ht hz)
  obtain ⟨hzu, hau⟩ := hcomp x z hzx u hu hn
  have hxM : C x ≤ M := by
    have hsum : C x ≤ ∑ y ∈ t, C y := Finset.single_le_sum (fun y _ => hC0 y) hxt
    exact hsum.trans (le_add_of_nonneg_left zero_le_one)
  have hzu' : u z ≤ M * u a :=
    hzu.trans (mul_le_mul_of_nonneg_right hxM (hn a ha))
  have hau' : u a ≤ M * u z :=
    hau.trans (mul_le_mul_of_nonneg_right hxM (hn z (hKΩ hz)))
  refine ⟨?_, hzu'⟩
  exact (inv_mul_le_iff₀ hM0).mpr hau'

end D12Complex.HarnackInequality
