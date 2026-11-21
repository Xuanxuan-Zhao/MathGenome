import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.OpenDomain
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.CommonInterval
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set Metric Filter Topology
namespace D13Unified.Ch05.OpenDomain
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap
open CommonInterval
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Uniformly small parameter perturbations on a compact time-state set.
Continuity is used only on the original joint domain. -/
lemma parameter_error (F : ParameterODE E P) {K : Set (ℝ × E)} (hK : IsCompact K)
    {p₀ : P} {c : ℝ} (hc : 0 < c)
    (hdom : K ×ˢ closedBall p₀ c ⊆ F.domain) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ p in 𝓝 p₀, p ∈ closedBall p₀ c ∧
      ∀ q ∈ K, ‖(F.atParameter p).eval q.1 q.2 -
        (F.atParameter p₀).eval q.1 q.2‖ ≤ δ := by
  have heval : ContinuousOn (fun z : (ℝ × E) × P => F.eval z.1.1 z.1.2 z.2)
      F.domain := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert F.continuous_field using 1
    funext z
    simp [ParameterODE.eval, parameterEvalValue, z.property]
  have hcont : ContinuousOn (fun z : P × (ℝ × E) => F.eval z.2.1 z.2.2 z.1)
      (ball p₀ c ×ˢ K) :=
    heval.comp (continuousOn_snd.prodMk continuousOn_fst)
      (fun z hz => hdom ⟨hz.2, ball_subset_closedBall hz.1⟩)
  obtain ⟨V, hV, hbound⟩ := hK.mem_uniformity_of_prod (f := fun (p : P) (q : ℝ × E) => F.eval q.1 q.2 p) hcont (mem_ball_self hc)
    (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_eq_nhds.mpr (ball_mem_nhds p₀ hc)] at hV
  filter_upwards [hV, ball_mem_nhds p₀ hc] with p hp hpc
  refine ⟨ball_subset_closedBall hpc, fun q hq => ?_⟩
  have h := hbound p hp q hq
  exact (show ‖F.eval q.1 q.2 p - F.eval q.1 q.2 p₀‖ < δ from
    by simpa only [Set.mem_ofPred_eq, dist_eq_norm] using h).le

/-- Persistence and the quantitative bound allow different slice domains.
The compact tube must lie in both actual domains. -/
lemma persistence (F G : ODE E) (hG : G.LocallyLipschitzInState)
    (I : OpenTimeInterval) (x : ℝ → E) (hx : classicalSolutionOnValue F I x)
    {a b s ρ L δ : ℝ} {ξ : E} (hρ : 0 < ρ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hI : Icc a b ⊆ I.carrier) (hs : s ∈ Icc a b)
    (hK : IsCompact (closedTube x a b ρ))
    (hdomF : closedTube x a b ρ ⊆ F.domain)
    (hdomG : closedTube x a b ρ ⊆ G.domain)
    (hlip : ∀ r ∈ Icc a b, ∀ z ∈ closedBall (x r) ρ,
      ∀ w ∈ closedBall (x r) ρ, ‖F.eval r z - F.eval r w‖ ≤ L * ‖z-w‖)
    (hdiff : ∀ q ∈ closedTube x a b ρ, ‖G.eval q.1 q.2 - F.eval q.1 q.2‖ ≤ δ)
    (hsmall : Real.exp (L * (b-a)) * (‖ξ-x s‖ + δ * (b-a)) < ρ / 2) :
    (s, ξ) ∈ G.domain ∧ Icc a b ⊆ (maximalIntervalValue G s ξ).carrier ∧
      ∀ t ∈ Icc a b, ‖solutionCurveValue G s ξ t-x t‖ ≤
        Real.exp (L * (b-a)) * (‖ξ-x s‖ + δ * (b-a)) := by
  have hd : ‖ξ-x s‖ < ρ / 2 := by
    have h := quantitative_bound (t := s) hs hs hL hδ (norm_nonneg (ξ-x s)) hsmall
    simpa [Gronwall.E, Specs.D13Unified.Ch05.Gronwall.EValue] using h
  have hξ : (s, ξ) ∈ G.domain := hdomG ⟨hs, hd.le.trans (by linarith)⟩
  obtain ⟨hy, hsJ, hys, hmax, _hend, _hrestrict, _huniq⟩ :=
    ODE.canonical_solution G hG s ξ hξ
  let J := maximalIntervalValue G s ξ
  let y := solutionCurveValue G s ξ
  change y s = ξ at hys
  have hsmall' : Real.exp (L * (b-a)) * (‖y s-x s‖ + δ * (b-a)) < ρ / 2 := by
    rw [hys]; exact hsmall
  have hbound := bound_on_existing_interval F G I J x y hx hy
    hρ hL hδ hI hs hsJ hdomF hlip hdiff hsmall'
  have hclosed : IsClosed (Icc a b ∩ J.carrier) := by
    apply closed_overlap_of_compact_confinement G hG (⟨J, y, hy⟩ : Solution G) hmax
      a b (closedTube x a b ρ) hK hdomG
    intro t ht
    exact ⟨ht.1, (hbound t ht).1.trans ((hbound t ht).2.le.trans (by linarith))⟩
  have hfull := interval_subset_of_closed_overlap J hs hsJ hclosed
  refine ⟨hξ, hfull, ?_⟩
  intro t ht
  have hsharp := (hbound t ⟨ht, hfull ht⟩).1
  rw [hys] at hsharp
  apply le_of_forall_pos_lt_add
  intro ε hε
  have h := quantitative_bound (ρ := 2 *
      (Real.exp (L * (b-a)) * (‖ξ-x s‖ + δ * (b-a)) + ε))
      hs ht hL hδ (norm_nonneg (ξ-x s)) (by linarith)
  exact hsharp.trans_lt (by linarith)

/-- Any two times in an open interval admit a compact interval with a margin
at both ends. -/
lemma compact_enclosure (I : OpenTimeInterval) {s t : ℝ}
    (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    ∃ a b : ℝ, s ∈ Ioo a b ∧ t ∈ Ioo a b ∧ Icc a b ⊆ I.carrier := by
  have hmin : min s t ∈ I.carrier := by
    rcases le_total s t with h | h
    · simpa [min_eq_left h] using hs
    · simpa [min_eq_right h] using ht
  have hmax : max s t ∈ I.carrier := by
    rcases le_total s t with h | h
    · simpa [max_eq_right h] using ht
    · simpa [max_eq_left h] using hs
  obtain ⟨l, u, hmin', hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (I.isOpen.mem_nhds hmin)
  obtain ⟨l', u', hmax', hsub'⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (I.isOpen.mem_nhds hmax)
  let a := (l + min s t) / 2
  let b := (max s t + u') / 2
  have ha : a < min s t := by dsimp [a]; linarith [hmin'.1]
  have hb : max s t < b := by dsimp [b]; linarith [hmax'.2]
  have haI : a ∈ I.carrier := hsub ⟨by dsimp [a]; linarith [hmin'.1], ha.trans hmin'.2⟩
  have hbI : b ∈ I.carrier := hsub' ⟨hmax'.1.trans hb, by dsimp [b]; linarith [hmax'.2]⟩
  exact ⟨a, b, ⟨ha.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb⟩,
    ⟨ha.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb⟩,
    I.ordConnected.out haI hbI⟩

/-- Whole compact-interval existence and uniformly small error for all nearby
starting times, states, and parameters. Each curve is the canonical curve for
its own actual parameter slice. -/
lemma nearby_initial_data (F : ParameterODE E P) (hF : F.LocallyLipschitzInState)
    (p₀ : P) (I : OpenTimeInterval) (x : ℝ → E)
    (hx : classicalParameterSolutionOnValue F p₀ I x)
    {a b s₀ : ℝ} {ξ₀ : E} (hs₀ : s₀ ∈ Ioo a b) (hξ₀ : x s₀ = ξ₀)
    (hI : Icc a b ⊆ I.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : (ℝ × E) × P in 𝓝 ((s₀, ξ₀), p₀),
      q ∈ F.domain ∧
      Icc a b ⊆ (parameterMaximalIntervalValue F q.1.1 q.1.2 q.2).carrier ∧
      ∀ t ∈ Icc a b,
        ‖parameterSolutionCurveValue F q.1.1 q.1.2 q.2 t - x t‖ < ε := by
  have hab : a ≤ b := hs₀.1.le.trans hs₀.2.le
  obtain ⟨ρ, c, L, hρ, hc, hL, _hprod, hdom, hlip⟩ :=
    compact_parameter_solution_tube F hF p₀ I x hx a b hab hI
  have hx' := (classicalParameterSolutionOn_iff F p₀ I x).mp hx
  have hK : IsCompact (closedTube x a b ρ) :=
    isCompact_closedTube (hx'.1.continuousOn.mono hI)
  let C := Real.exp (L * (b-a))
  let m := min (ρ / 2) ε
  have hm : 0 < m := lt_min (half_pos hρ) hε
  have hC : 0 ≤ C := Real.exp_nonneg _
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, C * (r + r * (b-a)) < m :=
    (show ContinuousAt (fun r : ℝ => C * (r + r * (b-a))) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa using hm))
  obtain ⟨l, u, h0, hu⟩ := hnear.exists_Ioo_subset
  let η := u / 2
  have hη : 0 < η := by dsimp [η]; linarith [h0.2]
  have hηsmall : C * (η + η * (b-a)) < m :=
    hu ⟨by dsimp [η]; linarith [h0.1, h0.2], by dsimp [η]; linarith [h0.2]⟩
  have hpar := parameter_error F hK hc hdom hη
  have hsI : s₀ ∈ I.carrier := hI ⟨hs₀.1.le, hs₀.2.le⟩
  have hxs : ContinuousAt x s₀ := hx'.1.continuousOn.continuousAt (I.isOpen.mem_nhds hsI)
  have hdcont : ContinuousAt (fun q : (ℝ × E) × P => ‖q.1.2 - x q.1.1‖)
      ((s₀, ξ₀), p₀) :=
    (((continuous_snd.comp continuous_fst).continuousAt).sub
      (hxs.comp ((continuous_fst.comp continuous_fst).continuousAt))).norm
  have hdnear : ∀ᶠ q : (ℝ × E) × P in 𝓝 ((s₀, ξ₀), p₀),
      ‖q.1.2 - x q.1.1‖ < η := hdcont.eventually
    (Iio_mem_nhds (by simpa [hξ₀] using hη))
  have hsnear : ∀ᶠ q : (ℝ × E) × P in 𝓝 ((s₀, ξ₀), p₀), q.1.1 ∈ Ioo a b :=
    ((continuous_fst.comp continuous_fst).tendsto _)
      (Ioo_mem_nhds hs₀.1 hs₀.2)
  have hpnear := (continuous_snd.tendsto ((s₀, ξ₀), p₀)) hpar
  filter_upwards [hdnear, hsnear, hpnear] with q hd hs hp
  have hnum : C * (‖q.1.2-x q.1.1‖ + η * (b-a)) < m :=
    (mul_le_mul_of_nonneg_left (add_le_add hd.le (le_refl (η * (b-a)))) hC).trans_lt hηsmall
  have hdom₀ : closedTube x a b ρ ⊆ (F.atParameter p₀).domain :=
    fun z hz => hdom ⟨hz, mem_closedBall_self hc.le⟩
  have hdomq : closedTube x a b ρ ⊆ (F.atParameter q.2).domain :=
    fun z hz => hdom ⟨hz, hp.1⟩
  have hlip₀ : ∀ r ∈ Icc a b, ∀ z ∈ closedBall (x r) ρ,
      ∀ w ∈ closedBall (x r) ρ,
      ‖(F.atParameter p₀).eval r z - (F.atParameter p₀).eval r w‖ ≤ L * ‖z-w‖ := by
    intro r hr z hz w hw
    exact hlip r hr z hz w hw p₀ (mem_closedBall_self hc.le)
  obtain ⟨hqU, hfull, hbound⟩ := persistence (F.atParameter p₀) (F.atParameter q.2)
    (ParameterODE.LocallyLipschitzInState.atParameter F hF q.2) I x hx'
    hρ hL hη.le hI ⟨hs.1.le, hs.2.le⟩ hK hdom₀ hdomq hlip₀ hp.2
    (hnum.trans_le (min_le_left _ _))
  exact ⟨hqU, hfull, fun t ht => (hbound t ht).trans_lt
    (hnum.trans_le (min_le_right _ _))⟩

/-- A full product neighborhood of any allowed datum lies in the actual
maximal domain, and the totalized value tends there to its reference value. -/
lemma local_control (F : ParameterODE E P) (hF : F.LocallyLipschitzInState)
    {q₀ : ℝ × ((ℝ × E) × P)} (hq₀ : q₀ ∈ parameterSolutionDomainValue F)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 q₀, q ∈ parameterSolutionDomainValue F ∧
      ‖parameterSolutionValueValue F q.1 q.2.1.1 q.2.1.2 q.2.2 -
        parameterSolutionValueValue F q₀.1 q₀.2.1.1 q₀.2.1.2 q₀.2.2‖ < ε := by
  let I := parameterMaximalIntervalValue F q₀.2.1.1 q₀.2.1.2 q₀.2.2
  let x := parameterSolutionCurveValue F q₀.2.1.1 q₀.2.1.2 q₀.2.2
  obtain ⟨hx, hsI, hξ, _⟩ := ParameterODE.canonical_solution F hF
    q₀.2.1.1 q₀.2.1.2 q₀.2.2 hq₀.1
  have hxP : classicalParameterSolutionOnValue F q₀.2.2 I x :=
    (classicalParameterSolutionOn_iff F q₀.2.2 I x).mpr hx
  obtain ⟨a, b, hs, ht, hI⟩ := compact_enclosure I hsI hq₀.2
  have hinit := nearby_initial_data F hF q₀.2.2 I x hxP hs hξ hI (half_pos hε)
  have hinit' := (continuous_snd.tendsto q₀) hinit
  have htnear : ∀ᶠ q : ℝ × ((ℝ × E) × P) in 𝓝 q₀, q.1 ∈ Ioo a b :=
    (continuous_fst.tendsto q₀) (Ioo_mem_nhds ht.1 ht.2)
  have hxt : ContinuousAt x q₀.1 :=
    hx.1.continuousOn.continuousAt (I.isOpen.mem_nhds hq₀.2)
  have hxnear : ∀ᶠ q : ℝ × ((ℝ × E) × P) in 𝓝 q₀,
      ‖x q.1-x q₀.1‖ < ε/2 :=
    (((hxt.comp continuous_fst.continuousAt).sub continuousAt_const).norm).eventually
      (Iio_mem_nhds (by simpa [x] using half_pos hε))
  have hv₀ := (ParameterODE.solutionValue_on_domain F hF
    q₀.1 q₀.2.1.1 q₀.2.1.2 q₀.2.2 hq₀).1
  filter_upwards [hinit', htnear, hxnear] with q hi hqt hxq
  have hqt' : q.1 ∈ Icc a b := ⟨hqt.1.le, hqt.2.le⟩
  have hq : q ∈ parameterSolutionDomainValue F := ⟨hi.1, hi.2.1 hqt'⟩
  refine ⟨hq, ?_⟩
  rw [(ParameterODE.solutionValue_on_domain F hF
    q.1 q.2.1.1 q.2.1.2 q.2.2 hq).1, hv₀]
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (parameterSolutionCurveValue F q.2.1.1 q.2.1.2 q.2.2 q.1) (x q.1) (x q₀.1)
  have herror := hi.2.2 q.1 hqt'
  change ‖parameterSolutionCurveValue F q.2.1.1 q.2.1.2 q.2.2 q.1 - x q₀.1‖ < ε
  linarith

/-- Openness in terminal time, initial time, initial state, and parameter. -/
theorem open_domain : Specs.D13Unified.Ch05.OpenDomain.openDomainExpected.{u,v} := by
  intro E _ _ _ P _ _ _ F hF
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  exact (local_control F hF hq (show (0 : ℝ) < 1 by norm_num)).mono fun _ h => h.1

/-- Joint continuity of Φ on the canonical maximal domain. -/
theorem continuous_solutionMap :
    Specs.D13Unified.Ch05.OpenDomain.continuousSolutionMapExpected.{u,v} := by
  intro E _ _ _ P _ _ _ F hF
  apply continuous_iff_continuousAt.mpr
  intro q
  have hval : ContinuousAt (fun r : ℝ × ((ℝ × E) × P) =>
      parameterSolutionValueValue F r.1 r.2.1.1 r.2.1.2 r.2.2) q.val := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    exact (local_control F hF q.property hε).mono fun r hr =>
      by simpa only [dist_eq_norm] using hr.2
  exact hval.comp continuous_subtype_val.continuousAt

end D13Unified.Ch05.OpenDomain
