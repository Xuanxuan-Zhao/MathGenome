import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.ResolventDecayObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.WeightedResolventEstimate
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Piecewise

noncomputable section
open MeasureTheory Filter Topology
open scoped FourierTransform ContDiff

namespace ExpandedFA.Semigroups.ResolventDecay
open Unbounded WeightedResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A bounded everywhere defined two-sided resolvent forces the original
exact-domain operator to have closed graph. Density is not needed. -/
lemma closed_of_resolvent (G : Operator ℂ H H) (z : ℂ)
    (h : Nonempty (ResolventInverse G z)) : G.IsClosed := by
  let R := h.some
  have heq : (G.graph : Set (H × H)) =
      {p | R.inverse (z • p.1 - p.2) = p.1} := by
    ext p
    constructor
    · intro hp
      obtain ⟨x, hx, hy⟩ := G.mem_graph_iff.mp hp
      change R.inverse (z • p.1 - p.2) = p.1
      rw [← hx, ← hy]
      exact R.left_inverse x
    · intro hp
      have hm : p.1 ∈ G.domain := hp ▸ R.mem_domain (z • p.1 - p.2)
      apply G.mem_graph_iff.mpr
      refine ⟨⟨p.1, hm⟩, rfl, ?_⟩
      have he : (⟨R.inverse (z • p.1 - p.2), R.mem_domain _⟩ : G.domain) =
          ⟨p.1, hm⟩ := Subtype.ext hp
      have hr := R.right_inverse (z • p.1 - p.2)
      rw [he, hp] at hr
      exact sub_right_inj.mp hr
  change IsClosed (G.graph : Set (H × H))
  rw [heq]
  exact isClosed_eq (R.inverse.continuous.comp
    ((continuous_const.smul continuous_fst).sub continuous_snd)) continuous_fst

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The case of a negative residual constant already forces the trajectory
to vanish; the source does not explicitly assume k ≥ 0. -/
lemma zero_of_negative_residual_constant {u r : ℝ → H} {k : ℝ}
    (hk : k < 0) (h : ∀ t ∈ Set.Ici (0 : ℝ), ‖r t‖ ≤ k * ‖u t‖) :
    ∀ t ∈ Set.Ici (0 : ℝ), u t = 0 := by
  intro t ht
  apply norm_eq_zero.mp
  have hp : 0 ≤ k * ‖u t‖ := (norm_nonneg _).trans (h t ht)
  by_contra hn
  have hpos : 0 < ‖u t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  exact (not_lt_of_ge hp) (mul_neg_of_neg_of_pos hk hpos)

/-- Unweighted coercivity for a shifted differential expression. This uses
only closedness, the graph Fourier identity, and the resolvent multiplier;
it does not require a dense domain. -/
lemma compact_shift_coercivity (G : Operator ℂ H H) (hG : G.IsClosed)
    (ξ d : ℝ) (hb : LineBound G ξ d) (v dv : ℝ → H)
    (hD : ∀ t, v t ∈ G.domain) (hv : LocalW12 v dv)
    (hs : HasCompactSupport v) (hg : MemLp (fun t => G ⟨v t, hD t⟩) 2) :
    d ^ 2 * (∫ t, ‖v t‖ ^ 2) ≤
      ∫ t, ‖dv t - (G ⟨v t, hD t⟩ - ξ • v t)‖ ^ 2 := by
  let g : ℝ → H := fun t => G ⟨v t, hD t⟩
  obtain ⟨hv1, hd1⟩ := hv.integrable_compact hs
  obtain ⟨hv2, hd2⟩ := hv.memLp_compact hs
  have hg1 : Integrable g := by
    apply integrable_of_locallyIntegrable_ae_zero
      (hg.locallyIntegrable (by norm_num)) hs
    apply Eventually.of_forall
    intro t ht
    have hz : (⟨v t, hD t⟩ : G.domain) = 0 := by
      apply Subtype.ext
      change v t = 0
      exact image_eq_zero_of_notMem_tsupport ht
    change G ⟨v t, hD t⟩ = 0
    rw [hz, G.map_zero]
  apply fourier_coercivity G ξ d hb v
    (fun t => dv t - (g t - ξ • v t)) hv1 hv2
    (hd1.sub (hg1.sub (hv1.smul ξ))) (hd2.sub (hg.sub (hv2.const_smul ξ)))
  intro s
  obtain ⟨h, hgraph⟩ := fourier_graph G hG v hD hv1 hg1 s
  change G ⟨𝓕 v s, h⟩ = 𝓕 g s at hgraph
  refine ⟨h, ?_⟩
  rw [fourier_sub_integrable (g := fun t => g t - ξ • v t) hd1 (hg1.sub (hv1.smul ξ)),
    fourier_sub_integrable (g := fun t => ξ • v t) hg1 (hv1.smul ξ),
    hv.fourier_derivative hs]
  have hscalar : 𝓕 (fun t => ξ • v t) s = ξ • 𝓕 v s := by
    simp only [Real.fourier_eq]
    simp_rw [smul_comm _ ξ, integral_smul]
  rw [hscalar, ← hgraph, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hc : (2 * Real.pi * Complex.I * s : ℂ) = Complex.I * (2 * Real.pi * s) := by
    ring
  rw [hc, add_smul]
  module

/-- The compact weighted estimate, with no density assumption. The shift in
the preceding lemma cancels the derivative of the exponential weight. -/
lemma compact_estimate_of_closed (G : Operator ℂ H H) (hG : G.IsClosed)
    (ξ d : ℝ) (hb : LineBound G ξ d) (w dw : ℝ → H)
    (hD : ∀ t, w t ∈ G.domain) (hw : LocalW12 w dw)
    (hs : HasCompactSupport w) (hg : MemLp (fun t => G ⟨w t, hD t⟩) 2) :
    d ^ 2 * energy ξ w ≤ energy ξ (residual G w dw hD) := by
  let v := weighted ξ w
  let hvD (t : ℝ) : v t ∈ G.domain :=
    smul_mem_domain_real G (Real.exp (-ξ * t)) (hD t)
  have hgv (t : ℝ) : G ⟨v t, hvD t⟩ =
      weighted ξ (fun s => G ⟨w s, hD s⟩) t :=
    operator_smul_real G (Real.exp (-ξ * t)) ⟨w t, hD t⟩ (hvD t)
  have hz : ∀ᵐ t, t ∉ tsupport w → G ⟨w t, hD t⟩ = 0 := by
    apply Eventually.of_forall
    intro t ht
    have hzero : (⟨w t, hD t⟩ : G.domain) = 0 := by
      apply Subtype.ext
      change w t = 0
      exact image_eq_zero_of_notMem_tsupport ht
    rw [hzero, G.map_zero]
  have hgv2 : MemLp (fun t => G ⟨v t, hvD t⟩) 2 := by
    simp_rw [hgv]
    exact (weighted_compact_data
      (fun _ _ => hg.mono_measure Measure.restrict_le_self) hs hz ξ).2
  have hc := compact_shift_coercivity G hG ξ d hb v
    (fun t => weighted ξ dw t - ξ • v t) hvD (hw.weighted ξ) hs.smul_left hgv2
  have he (t : ℝ) :
      (weighted ξ dw t - ξ • v t) - (G ⟨v t, hvD t⟩ - ξ • v t) =
      weighted ξ (residual G w dw hD) t := by
    rw [hgv]
    dsimp [weighted, WeightedResolvent.residual]
    rw [smul_sub]
    abel
  simp_rw [he] at hc
  simpa only [v, weighted_energy] using hc

/-- Full-line coercivity using the accepted cutoff convergence lemmas.
Closedness suffices; in particular no generator-density theorem is imported
or assumed in using this estimate for the source trajectory. -/
lemma cutoff_estimate_of_closed (G : Operator ℂ H H) (hG : G.IsClosed)
    (ξ d : ℝ) (hb : LineBound G ξ d) (w dw : ℝ → H)
    (hD : ∀ t, w t ∈ G.domain) (hw : LocalW12 w dw)
    (hg : Continuous (fun t => G ⟨w t, hD t⟩))
    (hw2 : MemLp (weighted ξ w) 2)
    (hr2 : MemLp (weighted ξ (WeightedResolvent.residual G w dw hD)) 2) :
    d ^ 2 * energy ξ w ≤ energy ξ (WeightedResolvent.residual G w dw hD) := by
  obtain ⟨C, hC, hCb⟩ := cutoffSeq_deriv_bound
  rw [← weighted_energy, ← weighted_energy]
  apply norm_sq_integral_le_of_cutoff hw2 hr2
    (fun n => (cutoffSeq_smooth n).continuous)
    (fun n => ((cutoffSeq_smooth n).deriv' (n := ∞)).continuous) hC
    (fun n t => by simpa only [Real.norm_eq_abs] using cutoffSeq_norm n t)
    (fun n t => by simpa only [Real.norm_eq_abs] using hCb n t)
    cutoffSeq_tendsto_one cutoffSeq_deriv_tendsto_zero
  intro n
  let hDn (t : ℝ) : cutoffSeq n t • w t ∈ G.domain :=
    smul_mem_domain_real G (cutoffSeq n t) (hD t)
  have hgn := cutoff_graph_memLp G w hD hg (cutoffSeq n)
    (cutoffSeq_smooth n).continuous (cutoffSeq_compact n) hDn
  have hn := compact_estimate_of_closed G hG ξ d hb _ _ hDn
    (hw.smul (cutoffSeq_smooth n)) (cutoffSeq_compact n).smul_right hgn
  rw [← weighted_energy, ← weighted_energy] at hn
  convert hn using 1
  · congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    dsimp only
    rw [weighted_smul]
  · apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    dsimp only
    simp only [weighted]
    rw [cutoff_residual G w dw hD (cutoffSeq n) hDn t, smul_add,
      smul_comm (Real.exp (-ξ * t)) (cutoffSeq n t),
      smul_comm (Real.exp (-ξ * t)) (deriv (cutoffSeq n) t)]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Continuous curves have all finite local square moments. -/
lemma continuous_memLp_Icc {f : ℝ → H} (hf : Continuous f) (a b : ℝ) :
    MemLp f 2 (volume.restrict (Set.Icc a b)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound (hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (Set.mem_image_of_mem _ ht)

/-- Classical continuously differentiable curves satisfy the upstream weak
local Sobolev interface. -/
lemma localW12_of_classical {w dw : ℝ → H} (hw : Continuous w)
    (hdw : Continuous dw) (hder : ∀ t, HasDerivAt w (dw t) t) : LocalW12 w dw := by
  refine ⟨continuous_memLp_Icc hw, continuous_memLp_Icc hdw, ?_⟩
  intro φ hφ hs
  have hdφ : Continuous (deriv φ) := (hφ.deriv' (n := ∞)).continuous
  have h1 : Integrable (fun t => deriv φ t • w t) :=
    (hdφ.smul hw).integrable_of_hasCompactSupport hs.deriv.smul_right
  have h2 : Integrable (fun t => φ t • dw t) :=
    (hφ.continuous.smul hdw).integrable_of_hasCompactSupport hs.smul_right
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun t => ((hφ.differentiable (by simp) t).hasDerivAt).smul (hder t))
    (h2.add h1)
    ((hφ.continuous.smul hw).integrable_of_hasCompactSupport hs.smul_right)
  rw [integral_add h2 h1] at h0
  exact eq_neg_of_add_eq_zero_right h0

/-- A continuous curve which is classically differentiable on each side of
zero has no boundary mass in its distributional derivative. -/
lemma localW12_of_piecewise_classical {w dw : ℝ → H} (hw : Continuous w)
    (hdw : ∀ a b, MemLp dw 2 (volume.restrict (Set.Icc a b)))
    (hder : ∀ t, t ≠ 0 → HasDerivAt w (dw t) t) : LocalW12 w dw := by
  refine ⟨continuous_memLp_Icc hw, hdw, ?_⟩
  intro φ hφ hs
  have hdφ : Continuous (deriv φ) := (hφ.deriv' (n := ∞)).continuous
  have h1 : Integrable (fun t => deriv φ t • w t) :=
    (hdφ.smul hw).integrable_of_hasCompactSupport hs.deriv.smul_right
  have h2 : Integrable (fun t => φ t • dw t) :=
    (locallyIntegrable_of_local_memLp hdw).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hs
  let F : ℝ → H := fun t => φ t • w t
  let dF : ℝ → H := fun t => φ t • dw t + deriv φ t • w t
  have hdF : ∀ t, t ≠ 0 → HasDerivAt F (dF t) t := fun t ht =>
    ((hφ.differentiable (by simp) t).hasDerivAt).smul (hder t ht)
  have hi : Integrable dF := h2.add h1
  have hc : Continuous F := hφ.continuous.smul hw
  have hsF : HasCompactSupport F := hs.smul_right
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hsF
  have hleft := integral_Iic_of_hasDerivAt_of_tendsto hc.continuousWithinAt
    (fun t ht => hdF t (ne_of_lt ht)) hi.integrableOn
    (hsF.filter_mono _root_.atBot_le_cocompact |>.tendsto)
  have hright := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt
    (fun t ht => hdF t (ne_of_gt ht)) hi.integrableOn
    (hsF.filter_mono _root_.atTop_le_cocompact |>.tendsto)
  have hz : (∫ t, dF t) = 0 := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn (b := 0), hleft, hright]
    simp
  change (∫ t, φ t • dw t + deriv φ t • w t) = 0 at hz
  rw [integral_add h2 h1] at hz
  exact eq_neg_of_add_eq_zero_right hz

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Constant continuation is continuous for a half-line continuous curve. -/
lemma continuous_nonnegative_extension {f : ℝ → H} (hf : ContinuousOn f (Set.Ici 0)) :
    Continuous (fun t : ℝ => f (max t 0)) := by
  exact hf.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Join two globally continuous pieces along zero. -/
lemma continuous_join {f g : ℝ → H} (hf : Continuous f) (hg : Continuous g)
    (h0 : f 0 = g 0) : Continuous (fun t : ℝ => if t ≤ 0 then f t else g t) := by
  apply hf.if_le hg continuous_id continuous_const
  intro t ht
  change t = 0 at ht
  subst t
  exact h0

/-- The compact negative-time extension used in the source proof. All
regularity assertions are proved, including the weak derivative at the join. -/
lemma trajectory_extension (G : Operator ℂ H H) (u du : ℝ → H)
    (hu : ContinuousOn u (Set.Ici 0)) (hdu : ContinuousOn du (Set.Ici 0))
    (hder : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt u (du t) (Set.Ici 0) t)
    (hD : ∀ t ∈ Set.Ici (0 : ℝ), u t ∈ G.domain)
    (hGu : Continuous (fun t : Set.Ici (0 : ℝ) => G ⟨u t, hD t t.property⟩)) :
    ∃ (w dw : ℝ → H) (hDw : ∀ t, w t ∈ G.domain),
      Continuous w ∧ LocalW12 w dw ∧ Continuous (fun t => G ⟨w t, hDw t⟩) ∧
      (∀ t, 0 ≤ t → w t = u t ∧ dw t = du t) ∧
      ∃ (v r : ℝ → H), Continuous v ∧ HasCompactSupport v ∧
        Continuous r ∧ HasCompactSupport r ∧
        (∀ t, t < 0 → w t = v t ∧ residual G w dw hDw t = r t) := by
  classical
  let ρ : ℝ → ℝ := cutoffBump
  have hρ : ContDiff ℝ ∞ ρ := cutoffBump.contDiff
  have hsρ : HasCompactSupport ρ := cutoffBump.hasCompactSupport
  have hρ0 : ρ 0 = 1 := cutoffBump.one_of_mem_closedBall (by simp [cutoffBump])
  let U : ℝ → H := fun t => u (max t 0)
  let D : ℝ → H := fun t => du (max t 0)
  have hU : Continuous U := continuous_nonnegative_extension hu
  have hDcont : Continuous D := continuous_nonnegative_extension hdu
  let v : ℝ → H := fun t => ρ t • u 0
  let dv : ℝ → H := fun t => deriv ρ t • u 0
  let w : ℝ → H := fun t => if t ≤ 0 then v t else U t
  let dw : ℝ → H := fun t => if t ≤ 0 then dv t else D t
  -- Assign the right derivative at zero; its value is irrelevant to the weak
  -- derivative, but agreement there is convenient for the parent.
  let dw' : ℝ → H := fun t => if t = 0 then du 0 else dw t
  have hv : Continuous v := hρ.continuous.smul continuous_const
  have hdv : Continuous dv := (hρ.deriv' (n := ∞)).continuous.smul continuous_const
  have hw : Continuous w := continuous_join hv hU (by simp [v, U, hρ0])
  have hwD (t : ℝ) : w t ∈ G.domain := by
    dsimp [w]
    split_ifs with ht
    · exact smul_mem_domain_real G (ρ t) (hD 0 (by simp))
    · exact hD (max t 0) (le_max_right t 0)
  have hdw (a b : ℝ) : MemLp dw' 2 (volume.restrict (Set.Icc a b)) := by
    have hp : MemLp dw 2 (volume.restrict (Set.Icc a b)) := by
      exact MemLp.piecewise (measurableSet_Iic.nullMeasurableSet)
        ((continuous_memLp_Icc hdv a b).mono_measure Measure.restrict_le_self)
        ((continuous_memLp_Icc hDcont a b).mono_measure Measure.restrict_le_self)
    apply hp.ae_eq
    filter_upwards [ae_restrict_of_ae (show ∀ᵐ t : ℝ, t ≠ 0 by rw [ae_iff]; simp)] with t ht
    simp [dw', ht]
  have hwder (t : ℝ) (ht : t ≠ 0) : HasDerivAt w (dw' t) t := by
    rcases lt_or_gt_of_ne ht with ht | ht
    · have he : w =ᶠ[𝓝 t] v := by
        filter_upwards [eventually_lt_nhds ht] with s hs
        simp [w, hs.le]
      simpa [dw', dw, ht.ne, ht.le] using
        ((hρ.differentiable (by simp) t).hasDerivAt.smul_const (u 0)).congr_of_eventuallyEq he
    · have he : w =ᶠ[𝓝 t] u := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        simp [w, U, not_le.mpr hs, max_eq_left hs.le]
      have hh := (hder t ht.le).hasDerivAt (Ici_mem_nhds ht)
      simpa [dw', dw, U, D, ht.ne', not_le.mpr ht, max_eq_left ht.le] using
        hh.congr_of_eventuallyEq he
  let g0 : H := G ⟨u 0, hD 0 (by simp)⟩
  let gU : ℝ → H := fun t => G ⟨u (max t 0), hD (max t 0) (le_max_right t 0)⟩
  have hgU : Continuous gU := hGu.comp
    ((continuous_id.max continuous_const).subtype_mk (fun t => le_max_right t 0))
  have hg (t : ℝ) : G ⟨w t, hwD t⟩ = if t ≤ 0 then ρ t • g0 else gU t := by
    split_ifs with ht
    · simpa only [w, v, ite_eq_left ht, g0] using
        operator_smul_real G (ρ t) ⟨u 0, hD 0 (by simp)⟩
          (by simpa [w, v, ht] using hwD t)
    · simp only [w, ite_eq_right ht, U, gU]
  refine ⟨w, dw', hwD, hw, localW12_of_piecewise_classical hw hdw hwder, ?_, ?_, ?_⟩
  · simp_rw [hg]
    exact continuous_join (hρ.continuous.smul continuous_const) hgU (by simp [gU, g0, hρ0])
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp [w, v, U, dw', hρ0]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      simp [w, U, dw', dw, D, ht0, not_le.mpr htpos, max_eq_left ht]
  · let r : ℝ → H := fun t => dv t - ρ t • g0
    refine ⟨v, r, hv, hsρ.smul_right, hdv.sub (hρ.continuous.smul continuous_const),
      hsρ.deriv.smul_right.sub hsρ.smul_right, ?_⟩
    intro t ht
    constructor
    · simp [w, ht.le]
    · simp only [WeightedResolvent.residual, hg, ite_eq_left ht.le]
      simp [dw', dw, r, ht.le, ht.ne]

omit [CompleteSpace H] in
lemma weighted_norm_sq (ξ : ℝ) (f : ℝ → H) (t : ℝ) :
    ‖weighted ξ f t‖ ^ 2 = ‖f t‖ ^ 2 * Real.exp (-2 * ξ * t) := by
  simp only [weighted, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-ξ * t) = -2 * ξ * t by ring, mul_comm]

/-- A finite nonnegative exponential moment gives the actual weighted L²
premise, rather than a Bochner integral with its default nonintegrable value. -/
lemma positive_weighted_memLp (u : ℝ → H) (hu : ContinuousOn u (Set.Ici 0))
    (ξ : ℝ) (_hξ : ξ < 0)
    (hf : (∫⁻ t in Set.Ici (0 : ℝ),
      ENNReal.ofReal (‖u t‖ ^ 2 * Real.exp ((-2 * ξ) * t))) ≠ ⊤) :
    MemLp (weighted ξ u) 2 (volume.restrict (Set.Ici 0)) := by
  have hc : ContinuousOn (weighted ξ u) (Set.Ici 0) :=
    (show Continuous (fun t : ℝ => Real.exp (-ξ * t)) by fun_prop).continuousOn.smul hu
  apply (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable measurableSet_Ici)).mpr
  refine ⟨(hc.aestronglyMeasurable measurableSet_Ici).norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun t => sq_nonneg _))]
  simpa only [weighted_norm_sq] using lt_top_iff_ne_top.mpr hf

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Glue a half-line L² curve to a square-integrable negative-time curve. -/
lemma memLp_of_half_lines {f v : ℝ → H}
    (hp : MemLp f 2 (volume.restrict (Set.Ici 0))) (hv : MemLp v 2)
    (he : ∀ t, t < 0 → f t = v t) : MemLp f 2 := by
  have hn : MemLp f 2 (volume.restrict (Set.Ici (0 : ℝ))ᶜ) := by
    apply (hv.mono_measure Measure.restrict_le_self).ae_eq
    filter_upwards [ae_restrict_mem measurableSet_Ici.compl] with t ht
    exact (he t (by simpa using ht)).symm
  have hh := MemLp.piecewise measurableSet_Ici.nullMeasurableSet hp hn
  simpa only [Set.piecewise_same] using hh

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma negative_energy_tendsto_zero (r : ℝ → H) (hr : Continuous r)
    (hs : HasCompactSupport r) (ξ : ℕ → ℝ) (hξ : Tendsto ξ atTop atBot) :
    Tendsto (fun n => ∫ t in Set.Iio (0 : ℝ),
      ‖r t‖ ^ 2 * Real.exp (-2 * ξ n * t)) atTop (𝓝 0) := by
  have hevent : ∀ᶠ n in atTop, ξ n < 0 := hξ.eventually (eventually_lt_atBot 0)
  have hi : Integrable (fun t => ‖r t‖ ^ 2) :=
    (hr.memLp_of_hasCompactSupport hs : MemLp r 2).integrable_norm_pow (by norm_num)
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Iio (0 : ℝ)))
    (F := fun n t => ‖r t‖ ^ 2 * Real.exp (-2 * ξ n * t))
    (f := fun _ => (0 : ℝ))
    (fun t => ‖r t‖ ^ 2)
    (Eventually.of_forall (fun n => by fun_prop))
    (hevent.mono (fun n hn => by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
      change t < 0 at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_of_le_one_right (sq_nonneg _)
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ -2 * ξ n := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos this ht.le)) hi.integrableOn
    (by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
      change t < 0 at ht
      have hm : Tendsto (fun n => -2 * ξ n * t) atTop atBot := by
        simpa only [mul_assoc, mul_comm (-2 : ℝ), mul_left_comm] using
          hξ.atBot_mul_const (show 0 < -2 * t by linarith)
      simpa using (Real.tendsto_exp_atBot.comp hm).const_mul (‖r t‖ ^ 2))
  simpa only [integral_zero] using hh

lemma weighted_energy_integrable {f : ℝ → H} {ξ : ℝ}
    (hf : MemLp (weighted ξ f) 2) :
    Integrable (fun t => ‖f t‖ ^ 2 * Real.exp (-2 * ξ * t)) := by
  exact (hf.integrable_norm_pow (by norm_num)).congr
    (Eventually.of_forall (weighted_norm_sq ξ f))

/-- Absorption of the residual bound on the positive half-line. -/
lemma half_line_energy_bound {w r : ℝ → H} {ξ d k : ℝ}
    (hξ : ξ ≤ 0) (hk : 0 ≤ k) (hkd : k ≤ d)
    (hw : MemLp (weighted ξ w) 2) (hr : MemLp (weighted ξ r) 2)
    (hw0 : IntegrableOn (fun t => ‖w t‖ ^ 2) (Set.Ici 0))
    (hres : ∀ t, 0 ≤ t → ‖r t‖ ≤ k * ‖w t‖)
    (hest : d ^ 2 * energy ξ w ≤ energy ξ r) :
    (d ^ 2 - k ^ 2) * (∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2) ≤
      ∫ t in Set.Iio (0 : ℝ), ‖r t‖ ^ 2 * Real.exp (-2 * ξ * t) := by
  have hiw := weighted_energy_integrable hw
  have hir := weighted_energy_integrable hr
  have hsplitw := intervalIntegral.integral_Iio_add_Ici
    (b := 0) hiw.integrableOn hiw.integrableOn
  have hsplitr := intervalIntegral.integral_Iio_add_Ici
    (b := 0) hir.integrableOn hir.integrableOn
  have hposr : (∫ t in Set.Ici (0 : ℝ), ‖r t‖ ^ 2 * Real.exp (-2 * ξ * t)) ≤
      k ^ 2 * (∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2 * Real.exp (-2 * ξ * t)) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hir.integrableOn (hiw.integrableOn.const_mul _) measurableSet_Ici
    intro t ht
    have h := hres t ht
    have hsq : ‖r t‖ ^ 2 ≤ k ^ 2 * ‖w t‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (r t)) h
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-2 * ξ * t)).le]
  have hposw : (∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2) ≤
      ∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2 * Real.exp (-2 * ξ * t) := by
    apply setIntegral_mono_on hw0 hiw.integrableOn measurableSet_Ici
    intro t ht
    apply le_mul_of_one_le_right (sq_nonneg _)
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg (by linarith) ht
  have hnegw : 0 ≤ ∫ t in Set.Iio (0 : ℝ), ‖w t‖ ^ 2 * Real.exp (-2 * ξ * t) :=
    integral_nonneg (fun _ => by positivity)
  have hgap : 0 ≤ d ^ 2 - k ^ 2 := by nlinarith
  dsimp only [energy] at hest
  rw [← hsplitw, ← hsplitr] at hest
  nlinarith [mul_nonneg (sq_nonneg d) hnegw,
    mul_le_mul_of_nonneg_left hposw hgap]

/-- Resolvent lines with a uniform bound obstruct superexponential decay,
with the original half-line regularity and arbitrary real residual constant. -/
theorem resolvent_decay_obstruction : Spec.DecayObstruction := by
  classical
  intro H _ _ _ G T hgen ξ hξ d hd hb u du hu hdu hder hD hGu k hk hres
  by_cases hk0 : 0 ≤ k
  · by_cases hzero : ∀ t ∈ Set.Ici (0 : ℝ), u t = 0
    · exact Or.inl hzero
    · right
      by_contra! hfinite
      have hclosed : G.IsClosed :=
        closed_of_resolvent G (ξ 0 + Complex.I * (0 : ℝ)) ((hb 0).2 0).1
      obtain ⟨w, dw, hDw, hw, hwloc, hGw, hmatch,
        v, rn, hv, hsv, hrn, hsrn, hneg⟩ :=
        trajectory_extension G u du hu hdu hder hD hGu
      let r : ℝ → H := WeightedResolvent.residual G w dw hDw
      have hrmeas : AEStronglyMeasurable r :=
        (locallyIntegrable_of_local_memLp hwloc.2.1).aestronglyMeasurable.sub
          hGw.aestronglyMeasurable
      have hrpos (t : ℝ) (ht : 0 ≤ t) : ‖r t‖ ≤ k * ‖w t‖ := by
        obtain ⟨hw', hdw'⟩ := hmatch t ht
        simpa only [r, WeightedResolvent.residual, hw', hdw'] using hres t ht
      have hwmoment (b : ℝ) (hb : 0 < b) :
          (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (‖w t‖ ^ 2 * Real.exp (b * t))) ≠ ⊤ := by
        rw [lintegral_congr_ae (show
          (fun t => ENNReal.ofReal (‖w t‖ ^ 2 * Real.exp (b * t))) =ᵐ[volume.restrict (Set.Ici 0)]
          (fun t => ENNReal.ofReal (‖u t‖ ^ 2 * Real.exp (b * t))) from by
            filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
            rw [(hmatch t ht).1])]
        exact hfinite b hb
      have hwp (a : ℝ) (ha : a < 0) : MemLp (weighted a w) 2 (volume.restrict (Set.Ici 0)) :=
        positive_weighted_memLp w hw.continuousOn a ha (hwmoment (-2 * a) (by linarith))
      have hww (a : ℝ) (ha : a < 0) : MemLp (weighted a w) 2 := by
        apply memLp_of_half_lines (hwp a ha)
          (((show Continuous (fun t : ℝ => Real.exp (-a * t)) by fun_prop).smul hv).memLp_of_hasCompactSupport hsv.smul_left)
        intro t ht
        simp only [weighted, (hneg t ht).1]
        rfl
      have hrp (a : ℝ) (ha : a < 0) : MemLp (weighted a r) 2 (volume.restrict (Set.Ici 0)) := by
        apply ((hwp a ha).const_smul k).of_le
          (((show Continuous (fun t : ℝ => Real.exp (-a * t)) by fun_prop).aestronglyMeasurable.smul
            hrmeas).mono_measure Measure.restrict_le_self)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        change ‖weighted a r t‖ ≤ ‖k • weighted a w t‖
        simp only [weighted, norm_smul, Real.norm_of_nonneg hk0,
          Real.norm_of_nonneg (Real.exp_pos _).le]
        nlinarith [mul_le_mul_of_nonneg_left (hrpos t ht) (Real.exp_pos (-a * t)).le]
      have hrr (a : ℝ) (ha : a < 0) : MemLp (weighted a r) 2 := by
        apply memLp_of_half_lines (hrp a ha)
          (((show Continuous (fun t : ℝ => Real.exp (-a * t)) by fun_prop).smul hrn).memLp_of_hasCompactSupport hsrn.smul_left)
        intro t ht
        simp only [weighted, show r t = rn t from (hneg t ht).2]
        rfl
      have hw0 : MemLp w 2 (volume.restrict (Set.Ici 0)) := by
        apply (hwp (-1) (by norm_num)).of_le
          (hw.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        rw [weighted, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        apply le_mul_of_one_le_left (norm_nonneg _)
        apply Real.one_le_exp_iff.mpr
        simpa using ht
      have hiw0 := hw0.integrable_norm_pow (show (2 : ℕ) ≠ 0 by norm_num)
      have hbound : ∀ᶠ n in atTop,
          (d ^ 2 - k ^ 2) * (∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2) ≤
            ∫ t in Set.Iio (0 : ℝ), ‖rn t‖ ^ 2 * Real.exp (-2 * ξ n * t) := by
        filter_upwards [hξ.eventually (eventually_lt_atBot 0)] with n hn
        have he := cutoff_estimate_of_closed G hclosed (ξ n) d (hb n) w dw hDw hwloc hGw
          (hww (ξ n) hn) (hrr (ξ n) hn)
        have hh := half_line_energy_bound hn.le hk0 hk.le (hww (ξ n) hn) (hrr (ξ n) hn)
          hiw0 hrpos he
        convert hh using 1
        apply setIntegral_congr_fun measurableSet_Iio
        intro t ht
        dsimp only
        rw [show r t = rn t from (hneg t ht).2]
      have hlim := negative_energy_tendsto_zero rn hrn hsrn ξ hξ
      have hle : (d ^ 2 - k ^ 2) * (∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2) ≤ 0 :=
        le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound
      have hgap : 0 < d ^ 2 - k ^ 2 := by nlinarith
      have hzeroIntegral : (∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2) = 0 := by
        have hi : 0 ≤ ∫ t in Set.Ici (0 : ℝ), ‖w t‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
        nlinarith
      have haezero : w =ᵐ[volume.restrict (Set.Ici 0)] (fun _ => 0) := by
        have hh := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (‖w t‖)) hiw0).mp hzeroIntegral
        filter_upwards [hh] with t ht
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp ht)
      have hzeroW : Set.EqOn w (fun _ => 0) (Set.Ici (0 : ℝ)) :=
        Measure.eqOn_of_ae_eq haezero hw.continuousOn continuousOn_const (by
          rw [interior_Ici, closure_Ioi])
      apply hzero
      intro t ht
      rw [← (hmatch t ht).1]
      exact hzeroW ht
  · left
    apply zero_of_negative_residual_constant (u := u)
      (r := fun t => if ht : t ∈ Set.Ici (0 : ℝ) then
        du t - G ⟨u t, hD t ht⟩ else 0) (lt_of_not_ge hk0)
    intro t ht
    simpa only [dite_eq_left ht] using hres t ht

end ExpandedFA.Semigroups.ResolventDecay
