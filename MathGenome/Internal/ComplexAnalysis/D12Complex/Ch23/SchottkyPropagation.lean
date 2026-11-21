import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.SchottkyPropagation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.SchottkyControl
import Mathlib.Topology.Connected.Clopen
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The bounded-center step in the proof of Montel--Carathéodory,
paper.tex:4247–4262. We construct finite chains of disks whose closed
carriers lie in the domain, propagate the Schottky bound along the chain,
and take a finite open cover of each compact subset. No normality theorem
or bound at an unconnected second center is assumed.
-/

noncomputable section
open Set Metric
open scoped Topology BigOperators

namespace D12Complex.SchottkyPropagation

/-- One step uses a compactly contained disk and its proper half-radius subdisk. -/
def DiskStep (Ω : Set ℂ) (x y : ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ Ω ∧ ‖y - x‖ ≤ R / 2

/-- Local symmetric steps and connectedness give a finite chain from a to b. -/
theorem finite_disk_reachability (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) (a : ℂ) (ha : a ∈ Ω) (b : ℂ) (hb : b ∈ Ω) :
    Relation.ReflTransGen (DiskStep Ω) a b := by
  apply hc.induction₂' (fun x y => Relation.ReflTransGen (DiskStep Ω) x y) ?_ ?_ ha hb
  · intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds x (show 0 < r / 4 by linarith)] with y hy
    have hyx : dist y x < r / 4 := hy
    constructor
    · apply Relation.ReflTransGen.single
      refine ⟨r / 2, by linarith, ?_, ?_⟩
      · intro z hz
        apply hball
        simp only [mem_closedBall, mem_ball] at hz ⊢
        linarith
      · rw [← dist_eq_norm]
        linarith
    · apply Relation.ReflTransGen.single
      refine ⟨r / 2, by linarith, ?_, ?_⟩
      · intro z hz
        apply hball
        simp only [mem_closedBall, mem_ball] at hz ⊢
        have hd := dist_triangle z y x
        linarith
      · rw [← dist_eq_norm, dist_comm]
        linarith
  · intro x y z _ _ _ hxy hyz
    exact hxy.trans hyz

/-- Apply the established scaled Schottky estimate on one disk in Ω. -/
lemma bound_on_half_disk {Ω : Set ℂ} (b : ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hsub : ball b R ⊆ Ω)
    (f : ℂ → ℂ) (hf : HolomorphicOn Ω f)
    (hzero : ∀ z ∈ Ω, f z ≠ 0) (hone : ∀ z ∈ Ω, f z ≠ 1)
    (hcenter : ‖f b‖ ≤ A) (z : ℂ) (hz : ‖z - b‖ ≤ R / 2) :
    ‖f z‖ ≤ SchottkyControl.C A (1 / 2) := by
  apply SchottkyControl.scaled b R A (1 / 2) hR hA (by norm_num) (by norm_num)
    f ⟨isOpen_ball, fun w hw => hf.2 w (hsub hw)⟩
    (fun w hw => hzero w (hsub hw)) (fun w hw => hone w (hsub hw)) hcenter z
  simpa only [one_div, inv_mul_eq_div] using hz

/-- Induction through the finite disk chain gives a uniform bound at every point. -/
theorem point_bound (Ω : Set ℂ) (a : ℂ) (hΩ : IsDomain Ω) (ha : a ∈ Ω)
    (b : ℂ) (hb : b ∈ Ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : ℂ → ℂ,
      HolomorphicOn Ω f →
      (∀ z ∈ Ω, f z ≠ 0) → (∀ z ∈ Ω, f z ≠ 1) →
      ‖f a‖ ≤ 1 → ‖f b‖ ≤ A := by
  have hchain := finite_disk_reachability Ω hΩ.2.1 hΩ.2.2 a ha b hb
  clear hb
  induction hchain with
  | refl => exact ⟨1, zero_lt_one, fun _ _ _ _ hcenter => hcenter⟩
  | tail _ hstep ih =>
    obtain ⟨A, hA, hbound⟩ := ih
    obtain ⟨R, hR, hsub, hdist⟩ := hstep
    refine ⟨SchottkyControl.C A (1 / 2),
      lt_trans zero_lt_one (SchottkyControl.constant_gt_one A (1 / 2)), ?_⟩
    intro f hf hzero hone hcenter
    exact bound_on_half_disk _ R A hR hA
      (fun z hz => hsub (ball_subset_closedBall hz))
      f hf hzero hone (hbound f hf hzero hone hcenter) _ hdist

/-- Each point has a closed neighborhood disk with one bound for the whole family. -/
theorem local_bound : Specs.D12Complex.Ch23.SchottkyPropagation.local_bound_type := by
  intro Ω a hΩ ha b hb
  obtain ⟨A, hA, hbound⟩ := point_bound Ω a hΩ ha b hb
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hΩ.2.1 b hb
  refine ⟨R / 2, by linarith, ?_, SchottkyControl.C A (1 / 2),
    lt_trans zero_lt_one (SchottkyControl.constant_gt_one A (1 / 2)), ?_⟩
  · intro z hz
    apply hsub
    simp only [mem_closedBall, mem_ball] at hz ⊢
    linarith
  · intro f hf hzero hone hcenter z hz
    exact bound_on_half_disk b R A hR hA hsub f hf hzero hone
      (hbound f hf hzero hone hcenter) z
      (by simpa only [mem_closedBall, dist_eq_norm] using hz)

/-- Compactness turns the propagated local family bounds into a single finite bound. -/
theorem compact_bound : Specs.D12Complex.Ch23.SchottkyPropagation.compact_bound_type := by
  classical
  intro Ω a hΩ ha K hK hKΩ
  have hl : ∀ z : K, ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧
      ∀ f : ℂ → ℂ, HolomorphicOn Ω f →
        (∀ w ∈ Ω, f w ≠ 0) → (∀ w ∈ Ω, f w ≠ 1) →
        ‖f a‖ ≤ 1 → ∀ w ∈ ball (z : ℂ) r, ‖f w‖ ≤ M := by
    intro z
    obtain ⟨r, hr, _, M, hM, hbound⟩ := local_bound Ω a hΩ ha z (hKΩ z.property)
    exact ⟨r, hr, M, hM, fun f hf hzero hone hcenter w hw =>
      hbound f hf hzero hone hcenter w (ball_subset_closedBall hw)⟩
  choose r hr M hM hbound using hl
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => ball (z : ℂ) (r z))
    (fun _ => isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr _)⟩)
  have hsum : 0 ≤ ∑ z ∈ t, M z := Finset.sum_nonneg (fun z _ => (hM z).le)
  refine ⟨1 + ∑ z ∈ t, M z, by linarith, ?_⟩
  intro f hf hzero hone hcenter z hz
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (ht hz)
  exact (hbound x f hf hzero hone hcenter z hzx).trans
    ((Finset.single_le_sum (fun y _ => (hM y).le) hxt).trans (by linarith))

end D12Complex.SchottkyPropagation
