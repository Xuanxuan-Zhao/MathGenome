import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.CommonInterval
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.CompactTube
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.PerturbationResidual
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.CompactEscape
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D13Unified.Ch05.CommonInterval
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exponential kernel is bounded by its maximum times the interval length,
including the zero Lipschitz constant and zero elapsed time. -/
lemma E_le_mul_exp {L v : ℝ} (hL : 0 ≤ L) (hv : 0 ≤ v) :
    Gronwall.E L v ≤ v * Real.exp (L * v) := by
  have hi := Gronwall.integral_exp_kernel L 0 v
  simp only [sub_zero] at hi
  rw [← hi]
  calc
    (∫ r in (0 : ℝ)..v, Real.exp (L * (v - r))) ≤
        ∫ _r in (0 : ℝ)..v, Real.exp (L * v) := by
      apply intervalIntegral.integral_mono_on hv
      · exact (by fun_prop : Continuous (fun r : ℝ => Real.exp (L * (v-r)))).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro r hr
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by linarith [hr.1]) hL
    _ = v * Real.exp (L * v) := by simp

lemma quantitative_bound {a b s t L δ d ρ : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    (hsmall : Real.exp (L * (b-a)) * (d + δ * (b-a)) < ρ / 2) :
    d * Real.exp (L * |t-s|) + δ * Gronwall.E L |t-s| < ρ / 2 := by
  have hv : |t-s| ≤ b-a := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
  have hT : 0 ≤ b-a := sub_nonneg.mpr (hs.1.trans hs.2)
  have he : Real.exp (L * |t-s|) ≤ Real.exp (L * (b-a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv hL)
  calc
    d * Real.exp (L * |t-s|) + δ * Gronwall.E L |t-s| ≤
        d * Real.exp (L * |t-s|) + δ * (|t-s| * Real.exp (L * |t-s|)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (E_le_mul_exp hL (abs_nonneg _)) hδ)
    _ = (d + δ * |t-s|) * Real.exp (L * |t-s|) := by ring
    _ ≤ (d + δ * (b-a)) * Real.exp (L * (b-a)) :=
      mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hδ)) he
        (Real.exp_nonneg _) (by positivity)
    _ < ρ / 2 := by simpa only [mul_comm] using hsmall

/-- Continuous induction: a continuous quantity cannot cross a barrier if
its bound improves strictly whenever all preceding values satisfy the barrier. -/
lemma no_exit_forward {e : ℝ → ℝ} {s t ρ : ℝ} (_hst : s ≤ t)
    (he : ContinuousOn e (Icc s t)) (hs : e s ≤ ρ)
    (himprove : ∀ c ∈ Icc s t, (∀ r ∈ Icc s c, e r ≤ ρ) → e c < ρ) :
    ∀ r ∈ Icc s t, e r ≤ ρ := by
  have hclosed : IsClosed ({r | e r ≤ ρ} ∩ Icc s t) := by
    rw [inter_comm]
    exact he.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hs
  intro c hc hprev
  have hlt := himprove c ⟨hc.1, hc.2.le⟩ hprev
  have hnear : ∀ᶠ r in 𝓝[Icc s t] c, e r < ρ :=
    (he c ⟨hc.1, hc.2.le⟩).eventually (Iio_mem_nhds hlt)
  have hsub : 𝓝[>] c ≤ 𝓝[Icc s t] c := by
    apply nhdsWithin_le_of_mem
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc.2)] with r hr hrt
    exact ⟨hc.1.trans hr.le, hrt.le⟩
  exact (hnear.filter_mono hsub).mono fun _ hr => hr.le

/-- The same scalar barrier argument to the left of the initial time. -/
lemma no_exit_backward {e : ℝ → ℝ} {s t ρ : ℝ} (hts : t ≤ s)
    (he : ContinuousOn e (Icc t s)) (hs : e s ≤ ρ)
    (himprove : ∀ c ∈ Icc t s, (∀ r ∈ Icc c s, e r ≤ ρ) → e c < ρ) :
    ∀ r ∈ Icc t s, e r ≤ ρ := by
  have h := no_exit_forward (e := fun r => e (-r)) (s := -s) (t := -t)
    (neg_le_neg hts)
    (he.comp continuous_neg.continuousOn (by
      intro r hr; constructor <;> linarith [hr.1, hr.2]))
    (by simpa using hs) (by
      intro c hc hprev
      apply himprove (-c) (by constructor <;> linarith [hc.1, hc.2])
      intro r hr
      have h := hprev (-r) (by constructor <;> linarith [hr.1, hr.2])
      simpa using h)
  intro r hr
  have h := h (-r) (by constructor <;> linarith [hr.1, hr.2])
  simpa using h

/-- The sharp comparison on any already existing segment inside the tube. -/
lemma comparison_on_segment [FiniteDimensional ℝ E]
    (F G : ODE E) (I J : OpenTimeInterval) (x y : ℝ → E)
    (hx : classicalSolutionOnValue F I x) (hy : classicalSolutionOnValue G J y)
    {a b c d s t ρ L δ : ℝ} (hcd : c ≤ d)
    (hsub : Icc c d ⊆ Icc a b) (hI : Icc a b ⊆ I.carrier)
    (hJ : Icc c d ⊆ J.carrier) (hs : s ∈ Icc c d) (ht : t ∈ Icc c d)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hdom : closedTube x a b ρ ⊆ F.domain)
    (hlip : ∀ r ∈ Icc a b, ∀ z ∈ closedBall (x r) ρ,
      ∀ w ∈ closedBall (x r) ρ, ‖F.eval r z - F.eval r w‖ ≤ L * ‖z-w‖)
    (hdiff : ∀ q ∈ closedTube x a b ρ, ‖G.eval q.1 q.2 - F.eval q.1 q.2‖ ≤ δ)
    (htube : ∀ r ∈ Icc c d, ‖y r-x r‖ ≤ ρ) :
    ‖y t-x t‖ ≤ ‖y s-x s‖ * Real.exp (L * |t-s|) + δ * Gronwall.E L |t-s| := by
  have hx' : compactSolutionOnValue F c d x :=
    ⟨hcd, hx.1.continuousOn.mono (hsub.trans hI),
      fun r hr => hx.2.1 r (hI (hsub hr)),
      fun r hr => (hx.2.2 r (hI (hsub hr))).hasDerivWithinAt⟩
  have htube' : ∀ r ∈ Icc c d, (r, y r) ∈ closedTube x a b ρ :=
    fun r hr => ⟨hsub hr, htube r hr⟩
  have hv : ContinuousOn (fun r => G.eval r (y r)) (Icc c d) :=
    G.continuousOn_eval.comp (continuousOn_id.prodMk (hy.1.continuousOn.mono hJ))
      (fun r hr => hy.2.1 r (hJ hr))
  have h := PerturbationResidual.two_fields F G.eval (closedTube x a b ρ)
    c d s L δ x y hx' hs hL hδ (hy.1.continuousOn.mono hJ) hv
    (fun r hr => (hy.2.2 r (hJ hr)).hasDerivWithinAt)
    (fun r hr => hdom (htube' r hr)) htube'
    (fun r hr => hlip r (hsub hr) (x r) (mem_closedBall_self (by
      exact (norm_nonneg (y r-x r)).trans (htube r hr)))
      (y r) (by simpa only [mem_closedBall, dist_eq_norm] using htube r hr))
    (fun q hq => by simpa only [norm_sub_rev] using hdiff q hq) t ht
  simpa only [norm_sub_rev, mul_comm (Real.exp _), Gronwall.E] using h

/-- On its actual interval, a perturbed solution stays in the inner half-tube.
This conclusion does not assume that the solution exists on all of `[a,b]`. -/
lemma bound_on_existing_interval [FiniteDimensional ℝ E]
    (F G : ODE E) (I J : OpenTimeInterval) (x y : ℝ → E)
    (hx : classicalSolutionOnValue F I x) (hy : classicalSolutionOnValue G J y)
    {a b s ρ L δ : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hI : Icc a b ⊆ I.carrier) (hs : s ∈ Icc a b) (hsJ : s ∈ J.carrier)
    (hdom : closedTube x a b ρ ⊆ F.domain)
    (hlip : ∀ r ∈ Icc a b, ∀ z ∈ closedBall (x r) ρ,
      ∀ w ∈ closedBall (x r) ρ, ‖F.eval r z - F.eval r w‖ ≤ L * ‖z-w‖)
    (hdiff : ∀ q ∈ closedTube x a b ρ, ‖G.eval q.1 q.2 - F.eval q.1 q.2‖ ≤ δ)
    (hsmall : Real.exp (L * (b-a)) * (‖y s-x s‖ + δ * (b-a)) < ρ / 2) :
    ∀ t ∈ Icc a b ∩ J.carrier,
      ‖y t-x t‖ ≤ ‖y s-x s‖ * Real.exp (L * |t-s|) + δ * Gronwall.E L |t-s| ∧
      ‖y s-x s‖ * Real.exp (L * |t-s|) + δ * Gronwall.E L |t-s| < ρ / 2 := by
  let e : ℝ → ℝ := fun r => ‖y r-x r‖
  have hnum (t : ℝ) (ht : t ∈ Icc a b) :=
    quantitative_bound (t := t) hs ht hL hδ (norm_nonneg (y s-x s)) hsmall
  have hstart : e s < ρ / 2 := by
    simpa [e, Gronwall.E, Specs.D13Unified.Ch05.Gronwall.EValue] using hnum s hs
  have hinit : e s ≤ ρ := by linarith
  have hbound {c d : ℝ} (hcd : c ≤ d) (hab : Icc c d ⊆ Icc a b)
      (hJ : Icc c d ⊆ J.carrier) (hscd : s ∈ Icc c d)
      (hprev : ∀ r ∈ Icc c d, e r ≤ ρ) {r : ℝ} (hr : r ∈ Icc c d) : e r < ρ := by
    have h := comparison_on_segment F G I J x y hx hy hcd hab hI hJ hscd hr
      hL hδ hdom hlip hdiff hprev
    have hn := hnum r (hab hr)
    change e r ≤ _ at h
    linarith
  intro t ht
  rcases le_total s t with hst | hts
  · have hab : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.1.2
    have hJ : Icc s t ⊆ J.carrier := J.ordConnected.out hsJ ht.2
    have he : ContinuousOn e (Icc s t) :=
      ((hy.1.continuousOn.mono hJ).sub (hx.1.continuousOn.mono (hab.trans hI))).norm
    have hprev := no_exit_forward hst he hinit (by
      intro c hc hprev
      exact hbound hc.1 (Icc_subset_Icc hs.1 ((hab hc).2))
        (J.ordConnected.out hsJ (hJ hc)) ⟨le_rfl, hc.1⟩ hprev ⟨hc.1, le_rfl⟩)
    exact ⟨comparison_on_segment F G I J x y hx hy hst hab hI hJ
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hL hδ hdom hlip hdiff hprev, hnum t ht.1⟩
  · have hab : Icc t s ⊆ Icc a b := Icc_subset_Icc ht.1.1 hs.2
    have hJ : Icc t s ⊆ J.carrier := J.ordConnected.out ht.2 hsJ
    have he : ContinuousOn e (Icc t s) :=
      ((hy.1.continuousOn.mono hJ).sub (hx.1.continuousOn.mono (hab.trans hI))).norm
    have hprev := no_exit_backward hts he hinit (by
      intro c hc hprev
      exact hbound hc.2 (Icc_subset_Icc ((hab hc).1) hs.2)
        (J.ordConnected.out (hJ hc) hsJ) ⟨hc.2, le_rfl⟩ hprev ⟨le_rfl, hc.2⟩)
    exact ⟨comparison_on_segment F G I J x y hx hy hts hab hI hJ
      ⟨hts, le_rfl⟩ ⟨le_rfl, hts⟩ hL hδ hdom hlip hdiff hprev, hnum t ht.1⟩

/-- A maximal solution confined to a compact subset of its field domain
cannot have a missing limit time. Consequently its overlap with a closed
interval, if confined, is closed. -/
lemma closed_overlap_of_compact_confinement [FiniteDimensional ℝ E]
    (G : ODE E) (hG : G.LocallyLipschitzInState) (y : Solution G)
    (hmax : IsMaximal y) (a b : ℝ) (K : Set (ℝ × E))
    (hK : IsCompact K) (hKU : K ⊆ G.domain)
    (hconf : ∀ t ∈ Icc a b ∩ y.interval.carrier, (t, y.representative t) ∈ K) :
    IsClosed (Icc a b ∩ y.interval.carrier) := by
  apply isClosed_of_closure_subset
  intro c hc
  have hcAB : c ∈ Icc a b := (closure_minimal inter_subset_left isClosed_Icc) hc
  refine ⟨hcAB, ?_⟩
  by_contra hcJ
  let D := Icc a b ∩ y.interval.carrier
  have : (𝓝[D] c).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hc
  have hmem : y.interval.carrier ∈ 𝓝[D] c :=
    mem_of_superset self_mem_nhdsWithin inter_subset_right
  have hesc := Ch04.CompactEscape.maximal_compact_escape G hG y hmax c hcJ
    (𝓝[D] c) nhdsWithin_le_nhds hmem K hK hKU
  have hinside : ∀ᶠ t in 𝓝[D] c, (t, y.representative t) ∈ K := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hconf t ht
  obtain ⟨t, ht, ht'⟩ := (hesc.and hinside).exists
  exact ht ht'

/-- An open interval whose nonempty overlap with `[a,b]` is closed contains
that entire closed interval. This also covers the singleton case `a = b`. -/
lemma interval_subset_of_closed_overlap (J : OpenTimeInterval) {a b s : ℝ}
    (hs : s ∈ Icc a b) (hsJ : s ∈ J.carrier)
    (hclosed : IsClosed (Icc a b ∩ J.carrier)) : Icc a b ⊆ J.carrier := by
  let V : Set (Icc a b) := Subtype.val ⁻¹' J.carrier
  have hVc : IsClosed V := by
    have h := hclosed.preimage (continuous_subtype_val : Continuous (Subtype.val : Icc a b → ℝ))
    convert h using 1
    ext t
    exact ⟨fun ht => ⟨t.property, ht⟩, fun ht => ht.2⟩
  have hVo : IsOpen V := J.isOpen.preimage continuous_subtype_val
  let : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hV : V = univ := (show IsClopen V from ⟨hVc, hVo⟩).eq_univ ⟨⟨s, hs⟩, hsJ⟩
  intro t ht
  exact (show (⟨t, ht⟩ : Icc a b) ∈ V by rw [hV]; trivial)

/-- Persistence on the full compact reference interval, with no uniform
Lipschitz constant assumed for the perturbed fields. -/
theorem common_interval : Specs.D13Unified.Ch05.CommonInterval.commonIntervalExpected.{u} := by
  intro E _ _ _ F hF I x hx a b hab hI
  obtain ⟨ρ, L, hρ, hL, hK, hdom, hlip⟩ :=
    compact_solution_tube F hF I x hx a b hab hI
  refine ⟨ρ, L, hρ, hL, hK, hdom, hlip, ?_⟩
  intro G hGF hG δ hδ hdiff s ξ hs hsmall
  have hd : ‖ξ-x s‖ < ρ / 2 := by
    have h := quantitative_bound (t := s) hs hs hL hδ (norm_nonneg (ξ-x s)) hsmall
    simpa [Gronwall.E, Specs.D13Unified.Ch05.Gronwall.EValue] using h
  have hξ : (s, ξ) ∈ G.domain := by
    rw [hGF]
    exact hdom ⟨hs, hd.le.trans (by linarith)⟩
  obtain ⟨hy, hsJ, hys, hmax, _hend, hrestrict, _huniq⟩ :=
    ODE.canonical_solution G hG s ξ hξ
  let J := maximalIntervalValue G s ξ
  let y := solutionCurveValue G s ξ
  change y s = ξ at hys
  have hsmall' : Real.exp (L * (b-a)) * (‖y s-x s‖ + δ * (b-a)) < ρ / 2 := by
    rw [hys]
    exact hsmall
  have hbound := bound_on_existing_interval F G I J x y hx hy
    hρ hL hδ hI hs hsJ hdom hlip hdiff hsmall'
  have hclosed : IsClosed (Icc a b ∩ J.carrier) := by
    apply closed_overlap_of_compact_confinement G hG (⟨J, y, hy⟩ : Solution G) hmax
      a b (closedTube x a b ρ) hK
      (by rw [hGF]; exact hdom)
    intro t ht
    exact ⟨ht.1, (hbound t ht).1.trans ((hbound t ht).2.le.trans (by linarith))⟩
  have hfull := interval_subset_of_closed_overlap J hs hsJ hclosed
  refine ⟨hfull, ⟨hy, hsJ, hys⟩, fun J z hz => (hrestrict J z hz).2, ?_⟩
  intro t ht
  have h := hbound t ⟨ht, hfull ht⟩
  simpa only [hys, Gronwall.E] using h

end D13Unified.Ch05.CommonInterval
