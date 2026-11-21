import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.LinearGrowth
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.CompactEscape
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.Gronwall
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology

namespace D13Unified.Ch04.LinearGrowth
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.LinearGrowth
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma abs_le_between {s t r B : ℝ} (hs : |s| ≤ B) (ht : |t| ≤ B)
    (hr : r ∈ uIcc s t) : |r| ≤ B := by
  rcases le_total s t with h | h
  · rw [uIcc_of_le h] at hr
    exact abs_le.mpr ⟨(abs_le.mp hs).1.trans hr.1, hr.2.trans (abs_le.mp ht).2⟩
  · rw [uIcc_of_ge h] at hr
    exact abs_le.mpr ⟨(abs_le.mp ht).1.trans hr.1, hr.2.trans (abs_le.mp hs).2⟩

/-- Integrating the velocity bounds increments, without differentiating a norm. -/
lemma norm_sub_le_integral (F : ODE E) (I : TimeInterval) (x : ℝ → E)
    (hx : IsSolutionOn F I x) {l r a b : ℝ} (hl : l ∈ I.carrier)
    (hr : r ∈ I.carrier) (hlr : l ≤ r)
    (hgrowth : ∀ q ∈ Icc l r, ‖F.eval q (x q)‖ ≤ b * ‖x q‖ + a) :
    ‖x r - x l‖ ≤ ∫ q in l..r, (b * ‖x q‖ + a) := by
  have hsub : Icc l r ⊆ I.carrier := by
    simpa only [uIcc_of_le hlr] using I.ordConnected.uIcc_subset hl hr
  have hg : ContinuousOn (fun q => F.eval q (x q)) I.carrier :=
    F.continuousOn_eval.comp (continuousOn_id.prodMk hx.1) hx.2.1
  rw [← integral_eq_sub_on_interval I.ordConnected hx.1 hg hx.2.2 hl hr]
  apply intervalIntegral.norm_integral_le_of_norm_le hlr
  · exact Eventually.of_forall (fun q hq => hgrowth q ⟨hq.1.le, hq.2⟩)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlr]
    exact (continuousOn_const.mul (hx.1.mono hsub).norm).add continuousOn_const

/-- Unified two-sided estimate, with E's value at b=0 retained. -/
lemma growth_estimate (F : ODE E) (I : TimeInterval) (x : ℝ → E)
    (hx : IsSolutionOn F I x) (B a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrowth : ∀ r : ℝ, |r| ≤ B → ∀ y : E, ‖F.eval r y‖ ≤ a + b * ‖y‖)
    (s : ℝ) (hs : s ∈ I.carrier) (t : ℝ) (ht : t ∈ I.carrier)
    (hsB : |s| ≤ B) (htB : |t| ≤ B) :
    ‖x t‖ ≤ ‖x s‖ * Real.exp (b * |t - s|) +
      a * Specs.D13Unified.Ch05.Gronwall.EValue b |t - s| := by
  have hsub := I.ordConnected.uIcc_subset hs ht
  have hg : ∀ r ∈ uIcc s t, ‖F.eval r (x r)‖ ≤ b * ‖x r‖ + a := by
    intro r hr
    simpa only [add_comm] using hgrowth r (abs_le_between hsB htB hr) (x r)
  rcases le_total s t with hst | hts
  · rw [uIcc_of_le hst] at hsub hg
    have hineq : ∀ r ∈ Icc s t,
        ‖x r‖ ≤ ‖x s‖ + ∫ q in s..r, (b * ‖x q‖ + a) := by
      intro r hr
      have hi := norm_sub_le_integral F I x hx hs (hsub hr) hr.1
        (fun q hq => hg q ⟨hq.1, hq.2.trans hr.2⟩)
      calc
        ‖x r‖ = ‖x s + (x r - x s)‖ := by congr 1; abel
        _ ≤ ‖x s‖ + ‖x r - x s‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl hi
    have h := Ch05.Gronwall.constant_forward s t ‖x s‖ b a (fun r => ‖x r‖)
      hst (norm_nonneg _) hb ha (hx.1.mono hsub).norm (fun _ _ => norm_nonneg _)
      hineq t ⟨hst, le_rfl⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using h
  · rw [uIcc_of_ge hts] at hsub hg
    have hineq : ∀ r ∈ Icc t s,
        ‖x r‖ ≤ ‖x s‖ + ∫ q in r..s, (b * ‖x q‖ + a) := by
      intro r hr
      have hi := norm_sub_le_integral F I x hx (hsub hr) hs hr.2
        (fun q hq => hg q ⟨hr.1.trans hq.1, hq.2⟩)
      calc
        ‖x r‖ = ‖x s - (x s - x r)‖ := by congr 1; abel
        _ ≤ ‖x s‖ + ‖x s - x r‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add le_rfl hi
    exact Ch05.Gronwall.constant_backward t s ‖x s‖ b a (fun r => ‖x r‖)
      hts (norm_nonneg _) hb ha (hx.1.mono hsub).norm (fun _ _ => norm_nonneg _)
      hineq t ⟨le_rfl, hts⟩

theorem positive_estimate : positiveEstimateExpected.{u} := by
  intro E _ _ _ F I x hx B a b ha hb hg s hs t ht hsB htB
  have h := growth_estimate F I x hx B a b ha hb.le hg s hs t ht hsB htB
  simpa only [Specs.D13Unified.Ch05.Gronwall.EValue, ite_eq_right (ne_of_gt hb), mul_div_assoc]
    using h

theorem zero_estimate : zeroEstimateExpected.{u} := by
  intro E _ _ _ F I x hx B a ha hg s hs t ht hsB htB
  have h := growth_estimate F I x hx B a 0 ha le_rfl
    (by simpa only [zero_mul, add_zero] using hg) s hs t ht hsB htB
  simpa [Specs.D13Unified.Ch05.Gronwall.EValue] using h

/-- Every missing finite boundary point would violate compact escape. Thus
the actual maximal interval is closed as well as open, and equals ℝ. -/
theorem global_existence : globalExistenceExpected.{u} := by
  intro E _ _ _ F hF hU hgrowth x hmax
  obtain ⟨s, hs⟩ := x.interval.nonempty
  have hx : IsSolutionOn F x.interval.toTimeInterval x.representative :=
    (classical_iff_solutionOn F x.interval x.representative).mp x.isSolution
  have hclosed : IsClosed x.interval.carrier := by
    apply isClosed_of_closure_subset
    intro c hc
    by_contra hcI
    have : (𝓝[x.interval.carrier] c).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hc
    let B : ℝ := |s| + |c| + 2
    have hB : 0 < B := by dsimp [B]; positivity
    have hsB : |s| ≤ B := by dsimp [B]; linarith [abs_nonneg c]
    obtain ⟨a, b, ha, hb, hg⟩ := hgrowth B hB
    have hb' : 0 < b + 1 := by linarith
    have hg' : ∀ r : ℝ, |r| ≤ B → ∀ y : E,
        ‖F.eval r y‖ ≤ a + (b + 1) * ‖y‖ := by
      intro r hr y
      exact (hg r hr y).trans (by nlinarith [norm_nonneg y])
    let R := ‖x.representative s‖ * Real.exp ((b + 1) * (2 * B)) +
      a * (Real.exp ((b + 1) * (2 * B)) - 1) / (b + 1)
    let K : Set (ℝ × E) := Icc (-B) B ×ˢ closedBall 0 R
    have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 R)
    have hesc := CompactEscape.maximal_compact_escape F hF x hmax c hcI
      (𝓝[x.interval.carrier] c) nhdsWithin_le_nhds self_mem_nhdsWithin
      K hK (by rw [hU]; exact subset_univ _)
    have hnear : ∀ᶠ t in 𝓝[x.interval.carrier] c, |t - c| < 1 := by
      have hn : ∀ᶠ t in 𝓝 c, |t - c| < 1 := by
        filter_upwards [ball_mem_nhds c zero_lt_one] with t ht
        simpa only [mem_ball, Real.dist_eq] using ht
      exact hn.filter_mono nhdsWithin_le_nhds
    have hconf : ∀ᶠ t in 𝓝[x.interval.carrier] c,
        (t, x.representative t) ∈ K := by
      filter_upwards [hnear, self_mem_nhdsWithin] with t ht htI
      have htB : |t| ≤ B := by
        have := abs_add_le (t - c) c
        rw [sub_add_cancel] at this
        dsimp [B]
        linarith [abs_nonneg s]
      have hd : |t - s| ≤ 2 * B :=
        (abs_sub t s).trans (by linarith)
      have he : Real.exp ((b + 1) * |t - s|) ≤
          Real.exp ((b + 1) * (2 * B)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hb'.le)
      have hbound := positive_estimate F x.interval.toTimeInterval x.representative
        hx B a (b + 1) ha hb' hg' s hs t htI hsB htB
      have hbound' : ‖x.representative t‖ ≤ R := hbound.trans
        (add_le_add (mul_le_mul_of_nonneg_left he (norm_nonneg _))
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (sub_le_sub_right he 1) ha) hb'.le))
      exact ⟨abs_le.mp htB, by simpa only [mem_closedBall, dist_zero_right] using hbound'⟩
    obtain ⟨t, ht, ht'⟩ := (hesc.and hconf).exists
    exact ht ht'
  exact IsClopen.eq_univ ⟨hclosed, x.interval.isOpen⟩ x.interval.nonempty

end D13Unified.Ch04.LinearGrowth
