import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.CenterLimitIdentification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.AsymptoticCenters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace ExpandedFA.BanachConvex.CenterLimitIdentification
open Set Filter
open scoped InnerProductSpace
universe u v
noncomputable section

theorem strong_radius : Spec.StrongRadius.{u} := by
  intro X _ s a hs x
  exact (tendsto_const_nhds.sub hs).norm.limsup_eq

theorem strong_center : Spec.StrongCenter.{u} := by
  intro X _ C s a hC hs ha
  have haC := hC.mem_of_tendsto ha (Eventually.of_forall hs)
  have hr := strong_radius X s a ha
  refine ⟨haC, ⟨haC, ?_⟩, ?_⟩
  · intro x _
    rw [hr, hr, sub_self, norm_zero]
    exact norm_nonneg _
  · intro c hc
    have h := hc.2 a haC
    rw [hr, hr, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- Adding a convergent real sequence commutes with limsup when the other
sequence is bounded on both sides. -/
lemma limsup_add_tendsto {u v : ℕ → ℝ} {b : ℝ}
    (hu : atTop.IsBoundedUnder (· ≤ ·) u)
    (hu' : atTop.IsBoundedUnder (· ≥ ·) u)
    (hv : Tendsto v atTop (nhds b)) :
    limsup (fun n => u n + v n) atTop = limsup u atTop + b := by
  apply le_antisymm
  · have h := limsup_add_le hu' hu hv.isBoundedUnder_ge.isCoboundedUnder_le
      hv.isBoundedUnder_le
    simpa only [Pi.add_def, hv.limsup_eq] using h
  · have h := le_limsup_add hu hu'.isCoboundedUnder_le hv.isBoundedUnder_le
      hv.isBoundedUnder_ge
    simpa only [Pi.add_def, hv.liminf_eq] using h

lemma radius_sq {X : Type u} [NormedAddCommGroup X] {s : ℕ → X}
    (hb : Bornology.IsBounded (range s)) (x : X) :
    AsymptoticCenters.radius s x ^ 2 = limsup (fun n => ‖x - s n‖ ^ 2) atTop := by
  have hm : Monotone (fun t : ℝ => (max t 0) ^ 2) := by
    intro t r h
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right _ h) 2
  have hc : Continuous (fun t : ℝ => (max t 0) ^ 2) :=
    (continuous_id.max continuous_const).pow 2
  have h := hm.map_limsup_of_continuousAt (fun n => ‖x - s n‖) hc.continuousAt
    (AsymptoticCenters.distances_bounded hb x) (AsymptoticCenters.distances_cobounded s x)
  change max (AsymptoticCenters.radius s x) 0 ^ 2 = _ at h
  rw [max_eq_left (AsymptoticCenters.radius_nonneg hb x)] at h
  simpa only [Function.comp_def, max_eq_left (norm_nonneg _)] using h

lemma squared_distances_bounded {X : Type u} [NormedAddCommGroup X] {s : ℕ → X}
    (hb : Bornology.IsBounded (range s)) (x : X) :
    atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖x - s n‖ ^ 2) := by
  obtain ⟨M, hM⟩ := AsymptoticCenters.distances_bounded hb x
  change ∀ᶠ n in atTop, ‖x - s n‖ ≤ M at hM
  exact isBoundedUnder_of_eventually_le
    (hM.mono fun n hn => pow_le_pow_left₀ (norm_nonneg _) hn 2)

/-- A continuous linear functional is continuous for the native weak topology. -/
lemma weak_scalar_test {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] {s : ℕ → H} {a : H}
    (hw : Tendsto (fun n => toWeakSpace 𝕜 H (s n)) atTop
      (nhds (toWeakSpace 𝕜 H a))) (f : H →L[𝕜] 𝕜) :
    Tendsto (fun n => f (s n)) atTop (nhds (f a)) := by
  exact ((WeakBilin.eval_continuous (topDualPairing 𝕜 H).flip f).tendsto
    (toWeakSpace 𝕜 H a)).comp hw

theorem weak_hilbert_radius : Spec.WeakHilbertRadius.{u, v} := by
  intro 𝕜 H _ _ _ s a hb hw x
  have hi : Tendsto (fun n => RCLike.re ⟪x - a, s n - a⟫_𝕜) atTop (nhds 0) := by
    have h := (weak_scalar_test hw (innerSL 𝕜 (x - a))).sub_const (⟪x - a, a⟫_𝕜)
    have h' := RCLike.reCLM.continuous.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, RCLike.reCLM_apply, innerSL_apply_apply,
      inner_sub_right, sub_self, map_zero] using h'
  have hv : Tendsto (fun n => ‖x - a‖ ^ 2 - 2 * RCLike.re ⟪x - a, s n - a⟫_𝕜)
      atTop (nhds (‖x - a‖ ^ 2)) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul 2)
  have heq : (fun n => ‖x - s n‖ ^ 2) =
      (fun n => ‖a - s n‖ ^ 2 +
        (‖x - a‖ ^ 2 - 2 * RCLike.re ⟪x - a, s n - a⟫_𝕜)) := by
    funext n
    have h := norm_sub_sq (𝕜 := 𝕜) (x - a) (s n - a)
    rw [sub_sub_sub_cancel_right] at h
    rw [h, norm_sub_rev a (s n)]
    ring
  rw [radius_sq hb x, heq, limsup_add_tendsto (squared_distances_bounded hb a)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => sq_nonneg ‖a - s n‖)) hv]
  simp only [norm_sub_rev a, add_comm]

/-- Projection proves the needed weak closedness: its separating inner product
is nonpositive on C, and hence at a weak limit; at the projected point it is
exactly the squared distance to C. -/
theorem weak_limit_mem_closed_convex : Spec.WeakLimitMembership.{u, v} := by
  intro 𝕜 H _ _ _ _ C s a hne hclosed hv hs hw
  let p := Hilbert.Projection.convexProjection 𝕜 H C hne hclosed hv a
  have hp := (Hilbert.Projection.eq_convexProjection_iff_variational
    𝕜 H C hne hclosed hv a p).mp rfl
  have hlim : Tendsto (fun n => RCLike.re ⟪a - p, s n - p⟫_𝕜) atTop
      (nhds (RCLike.re ⟪a - p, a - p⟫_𝕜)) := by
    have h := (weak_scalar_test hw (innerSL 𝕜 (a - p))).sub_const (⟪a - p, p⟫_𝕜)
    have h' := RCLike.reCLM.continuous.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, RCLike.reCLM_apply, innerSL_apply_apply,
      inner_sub_right] using h'
  have hn := le_of_tendsto hlim (Eventually.of_forall fun n => hp.2 (s n) (hs n))
  rw [inner_self_eq_norm_sq] at hn
  have hap : a = p := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (a - p)]))
  exact hap ▸ hp.1

theorem weak_hilbert_center : Spec.WeakHilbertCenter.{u, v} := by
  intro 𝕜 H _ _ _ _ C s a hne hclosed hv hb hs hw
  have haC := weak_limit_mem_closed_convex 𝕜 H C s a hne hclosed hv hs hw
  have hr := weak_hilbert_radius 𝕜 H s a hb hw
  have hra : AsymptoticCenters.radius s a ^ 2 =
      limsup (fun n => ‖s n - a‖ ^ 2) atTop := by
    simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add] using hr a
  have hac : AsymptoticCenters.IsCenter C s a := by
    refine ⟨haC, fun x _ => ?_⟩
    have hx := hr x
    have ha0 := AsymptoticCenters.radius_nonneg hb a
    have hx0 := AsymptoticCenters.radius_nonneg hb x
    nlinarith [sq_nonneg ‖x - a‖]
  refine ⟨haC, hac, ?_⟩
  intro c hc
  have heq := le_antisymm (hc.2 a haC) (hac.2 c hc.1)
  have h := hr c
  rw [heq, hra] at h
  have hn : ‖c - a‖ ^ 2 = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

end
end ExpandedFA.BanachConvex.CenterLimitIdentification
