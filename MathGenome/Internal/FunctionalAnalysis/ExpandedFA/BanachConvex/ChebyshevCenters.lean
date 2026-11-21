import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.ChebyshevCenters
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The Chebyshev part of `fa2:p2:asymptotic-center`, paper.tex:8342–8399.
The radius is the shared real supremum defined in the independent Specs.
The existence proof uses completeness directly: uniform convexity makes every
near-infimum sequence Cauchy. This includes a zero infimum and the zero space.
-/
namespace ExpandedFA.BanachConvex.ChebyshevCenters
open Set Filter
universe u
noncomputable section
variable {X : Type u} [NormedAddCommGroup X] {A C : Set X}

lemma distances_bddAbove (hA : Bornology.IsBounded A) (x : X) :
    BddAbove ((fun a => ‖x - a‖) '' A) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hA
  refine ⟨‖x‖ + M, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (norm_sub_le x a).trans (add_le_add le_rfl (hM a ha))

lemma distance_le_radius (hA : Bornology.IsBounded A) {a : X} (ha : a ∈ A) (x : X) :
    ‖x - a‖ ≤ radius A x :=
  le_csSup (distances_bddAbove hA x) ⟨a, ha, rfl⟩

lemma radius_le (hA : A.Nonempty) {x : X} {r : ℝ}
    (h : ∀ a ∈ A, ‖x - a‖ ≤ r) : radius A x ≤ r := by
  apply csSup_le (hA.image _)
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

lemma radius_nonneg (hA : A.Nonempty) (hb : Bornology.IsBounded A) (x : X) :
    0 ≤ radius A x := by
  obtain ⟨a, ha⟩ := hA
  exact (norm_nonneg _).trans (distance_le_radius hb ha x)

lemma radius_le_add (hA : A.Nonempty) (hb : Bornology.IsBounded A) (x y : X) :
    radius A x ≤ ‖x - y‖ + radius A y := by
  apply radius_le hA
  intro a ha
  calc
    ‖x - a‖ ≤ ‖x - y‖ + ‖y - a‖ := norm_sub_le_norm_sub_add_norm_sub x y a
    _ ≤ _ := add_le_add le_rfl (distance_le_radius hb ha y)

lemma radius_lipschitz (hA : A.Nonempty) (hb : Bornology.IsBounded A) :
    LipschitzWith 1 (radius A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  have h₁ := radius_le_add hA hb x y
  have h₂ := radius_le_add hA hb y x
  rw [norm_sub_rev y x] at h₂
  constructor <;> linarith

lemma radius_coercive (hA : A.Nonempty) (hb : Bornology.IsBounded A) :
    RadiusCoercive A := by
  obtain ⟨a, ha⟩ := hA
  intro b
  refine ⟨b + ‖a‖ + 1, fun x hx => ?_⟩
  have h := norm_le_norm_sub_add x a
  have h' := distance_le_radius hb ha x
  linarith

variable [NormedSpace ℝ X]

lemma radius_convex (hA : A.Nonempty) (hb : Bornology.IsBounded A) :
    ConvexOn ℝ univ (radius A) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  apply radius_le hA
  intro a ha
  have h := (convexOn_univ_dist a).2 (mem_univ x) (mem_univ y) hs ht hst
  simp only [dist_eq_norm, smul_eq_mul] at h ⊢
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (distance_le_radius hb ha x) hs)
    (mul_le_mul_of_nonneg_left (distance_le_radius hb ha y) ht))

theorem radius_regularity : Spec.Regularity.{u} := by
  intro X _ _ A hA hb
  exact ⟨radius_convex hA hb, radius_lipschitz hA hb, radius_coercive hA hb⟩

/-- The uniform midpoint estimate on all radii up to a fixed upper bound. -/
lemma radius_midpoint_drop [UniformConvexSpace X]
    (hA : A.Nonempty) (hb : Bornology.IsBounded A)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R → R ≤ B →
      ∀ x y : X, radius A x ≤ R → radius A y ≤ R → ε ≤ ‖x - y‖ →
        radius A ((1 / 2 : ℝ) • (x + y)) ≤ R * (1 - δ) := by
  obtain ⟨d, hd, h⟩ :=
    exists_forall_closed_ball_dist_add_le_two_sub X (div_pos hε hB)
  refine ⟨d / 2, by linarith, ?_⟩
  intro R hR hRB x y hx hy hxy
  apply radius_le hA
  intro a ha
  have hx' : ‖R⁻¹ • (x - a)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), ← div_eq_inv_mul]
    exact (div_le_one hR).mpr ((distance_le_radius hb ha x).trans hx)
  have hy' : ‖R⁻¹ • (y - a)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), ← div_eq_inv_mul]
    exact (div_le_one hR).mpr ((distance_le_radius hb ha y).trans hy)
  have hsep : ε / B ≤ ‖R⁻¹ • (x - a) - R⁻¹ • (y - a)‖ := by
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hR.le), ← div_eq_inv_mul]
    exact (div_le_div_of_nonneg_left hε.le hR hRB).trans
      (div_le_div_of_nonneg_right hxy hR.le)
  have hh := h hx' hy' hsep
  rw [← smul_add, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le),
    ← div_eq_inv_mul, div_le_iff₀ hR] at hh
  have heq : (1 / 2 : ℝ) • (x + y) - a = (1 / 2 : ℝ) • ((x - a) + (y - a)) := by
    module
  rw [heq, norm_smul]
  norm_num
  nlinarith

/-- Points sufficiently close to the infimum have uniformly small separation. -/
lemma near_minimizers_close [UniformConvexSpace X]
    (hA : A.Nonempty) (hb : Bornology.IsBounded A) (hC : Convex ℝ C)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hmin : ∀ x ∈ C, ρ ≤ radius A x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ C, ∀ y ∈ C,
      radius A x < ρ + η → radius A y < ρ + η → ‖x - y‖ < ε := by
  by_cases hz : ρ = 0
  · subst ρ
    obtain ⟨a, ha⟩ := hA
    refine ⟨ε / 3, by linarith, ?_⟩
    intro x _ y _ hx hy
    have h := norm_sub_le_norm_sub_add_norm_sub x a y
    rw [norm_sub_rev a y] at h
    have h₁ := distance_le_radius hb ha x
    have h₂ := distance_le_radius hb ha y
    linarith
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hz)
  obtain ⟨δ, hδ, hdrop⟩ := radius_midpoint_drop hA hb hε (show 0 < ρ + 1 by linarith)
  let η := min 1 (ρ * δ / 2)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη₁ : η ≤ 1 := min_le_left _ _
  have hη₂ : η ≤ ρ * δ / 2 := min_le_right _ _
  refine ⟨η, hη, ?_⟩
  intro x hx y hy hrx hry
  by_contra hn
  have hm := hC hx hy (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  rw [← smul_add] at hm
  have hlo := hmin _ hm
  have hhi := hdrop (ρ + η) (by linarith) (by linarith) x y hrx.le hry.le (le_of_not_gt hn)
  nlinarith [mul_pos hη hδ]

lemma cauchy_of_radius_tendsto [UniformConvexSpace X]
    (hA : A.Nonempty) (hb : Bornology.IsBounded A) (hC : Convex ℝ C)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hmin : ∀ x ∈ C, ρ ≤ radius A x)
    {x : ℕ → X} (hx : ∀ n, x n ∈ C)
    (hlim : Tendsto (fun n => radius A (x n)) atTop (nhds ρ)) : CauchySeq x := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨η, hη, hclose⟩ := near_minimizers_close hA hb hC hρ hmin hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlim).2 (ρ + η) (by linarith))
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  exact hclose _ (hx m) _ (hx n) (hN m hm) (hN n hn)

/-- The completeness argument constructs a center without a reflexivity assumption. -/
lemma exists_center [UniformConvexSpace X] [CompleteSpace X]
    (hCne : C.Nonempty) (hclosed : IsClosed C) (hC : Convex ℝ C)
    (hA : A.Nonempty) (hb : Bornology.IsBounded A) : ∃ c, IsCenter C A c := by
  let S : Set ℝ := radius A '' C
  have hS : S.Nonempty := hCne.image _
  have hS0 : ∀ z ∈ S, (0 : ℝ) ≤ z := by
    rintro _ ⟨x, _, rfl⟩
    exact radius_nonneg hA hb x
  have hSb : BddBelow S := ⟨0, hS0⟩
  have hρ : 0 ≤ sInf S := le_csInf hS hS0
  have hmin : ∀ x ∈ C, sInf S ≤ radius A x :=
    fun x hx => csInf_le hSb ⟨x, hx, rfl⟩
  obtain ⟨v, _, hv, hvS⟩ := exists_seq_tendsto_sInf hS hSb
  choose x hx hval using hvS
  have hlim : Tendsto (fun n => radius A (x n)) atTop (nhds (sInf S)) := by
    simpa only [hval] using hv
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete
    (cauchy_of_radius_tendsto hA hb hC hρ hmin hx hlim)
  have hcC : c ∈ C := hclosed.mem_of_tendsto hc (Eventually.of_forall hx)
  have hrc : radius A c = sInf S := tendsto_nhds_unique
    (((radius_lipschitz hA hb).continuous.tendsto c).comp hc) hlim
  exact ⟨c, hcC, fun x hx => hrc ▸ hmin x hx⟩

lemma center_unique [UniformConvexSpace X]
    (hA : A.Nonempty) (hb : Bornology.IsBounded A) (hC : Convex ℝ C)
    {c d : X} (hc : IsCenter C A c) (hd : IsCenter C A d) : c = d := by
  by_contra hn
  have hε : 0 < ‖c - d‖ := norm_sub_pos_iff.mpr hn
  obtain ⟨η, hη, hclose⟩ := near_minimizers_close hA hb hC
    (radius_nonneg hA hb c) hc.2 hε
  have heq : radius A d = radius A c := le_antisymm (hd.2 c hc.1) (hc.2 d hd.1)
  have h := hclose c hc.1 d hd.1 (by linarith) (by linarith)
  exact (lt_irrefl _) h

theorem unique_center : Spec.UniqueCenter.{u} := by
  intro X _ _ _ _ C A hCne hclosed hC hA hb _hAC
  obtain ⟨c, hc⟩ := exists_center hCne hclosed hC hA hb
  exact ⟨c, hc, fun d hd => center_unique hA hb hC hd hc⟩

/-- Every minimizing sequence converges to the unique center in the original norm. -/
theorem minimizing_sequences : Spec.MinimizingSequences.{u} := by
  intro X _ _ _ _ C A _hCne _hclosed hC hA hb _hAC c hc x hx hlim
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨η, hη, hclose⟩ := near_minimizers_close hA hb hC
    (radius_nonneg hA hb c) hc.2 hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlim).2 (radius A c + η) (by linarith))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact hclose (x n) (hx n) c hc.1 (hN n hn) (by linarith)

/-- Positive diameter gives a genuinely smaller enclosing radius. -/
theorem radius_lt_diameter : Spec.StrictDiameter.{u} := by
  intro X _ _ _ _ C A _hCne _hclosed hC hA hb hAC c hc hd
  obtain ⟨a, ha, b, hbA, hab⟩ :
      ∃ a ∈ A, ∃ b ∈ A, Metric.diam A / 2 < ‖a - b‖ := by
    by_contra hn
    push Not at hn
    have hdiam := Metric.diam_le_of_forall_dist_le (s := A) (show 0 ≤ Metric.diam A / 2 by positivity)
      (fun a ha b hb => by simpa only [dist_eq_norm] using hn a ha b hb)
    linarith
  obtain ⟨δ, hδ, hdrop⟩ := radius_midpoint_drop hA hb (show 0 < Metric.diam A / 2 by linarith) hd
  have hra : radius A a ≤ Metric.diam A := radius_le hA (fun y hy => by
    simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hb ha hy)
  have hrb : radius A b ≤ Metric.diam A := radius_le hA (fun y hy => by
    simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hb hbA hy)
  have hm := hC (hAC ha) (hAC hbA) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  rw [← smul_add] at hm
  have hmin := hc.2 _ hm
  have hhi := hdrop (Metric.diam A) hd le_rfl a b hra hrb hab.le
  nlinarith [mul_pos hd hδ]

end
end ExpandedFA.BanachConvex.ChebyshevCenters
