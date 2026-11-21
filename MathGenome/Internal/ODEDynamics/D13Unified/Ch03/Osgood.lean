import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.RestrictionPasting
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.Osgood
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace D13Unified

theorem OsgoodModulus.nonneg {ω : ℝ → ℝ} (hω : OsgoodModulus ω)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ ω r := by
  simpa only [hω.zero] using hω.monotone (by simp) hr hr

theorem OsgoodModulus.continuousOn_inv {ω : ℝ → ℝ} (hω : OsgoodModulus ω) :
    ContinuousOn (fun r => (ω r)⁻¹) (Ioi 0) :=
  (hω.continuous.mono Ioi_subset_Ici_self).inv₀ (fun r hr => ne_of_gt (hω.positive r hr))

/-- The scalar integral comparison at the heart of Osgood's criterion. -/
theorem osgood_integral_zero {ω d : ℝ → ℝ} (hω : OsgoodModulus ω)
    {s T : ℝ} (hsT : s ≤ T) (hd : ContinuousOn d (Icc s T))
    (hd0 : ∀ t ∈ Icc s T, 0 ≤ d t)
    (hineq : ∀ t ∈ Icc s T, d t ≤ ∫ r in s..t, ω (d r)) : d T = 0 := by
  have hg : ContinuousOn (fun r => ω (d r)) (Icc s T) :=
    hω.continuous.comp hd hd0
  let v (ε t : ℝ) := ε + ∫ r in s..t, ω (d r)
  have hvpos (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Icc s T) : 0 < v ε t := by
    have hi := intervalIntegral.integral_nonneg (μ := volume) ht.1
      (fun r hr => hω.nonneg (hd0 r ⟨hr.1, hr.2.trans ht.2⟩))
    dsimp [v]; linarith
  have hvd (ε t : ℝ) (ht : t ∈ Icc s T) :
      HasDerivWithinAt (v ε) (ω (d t)) (Icc s T) t :=
    (hasDerivWithinAt_integral_on_interval ordConnected_Icc hg
      (left_mem_Icc.mpr hsT) ht).const_add ε
  have hbound (ε : ℝ) (hε : 0 < ε) :
      (∫ r in ε..v ε T, (ω r)⁻¹) ≤ T-s := by
    let H (u : ℝ) := ∫ r in ε..u, (ω r)⁻¹
    have hcomp (t : ℝ) (ht : t ∈ Icc s T) :
        HasDerivWithinAt (fun t => H (v ε t))
          ((ω (v ε t))⁻¹ * ω (d t)) (Icc s T) t := by
      exact (hasDerivWithinAt_integral_on_interval ordConnected_Ioi
        hω.continuousOn_inv hε (hvpos ε hε t ht)).comp t (hvd ε t ht)
        (fun r hr => hvpos ε hε r hr)
    have hb (t : ℝ) (ht : t ∈ Icc s T) :
        ‖(ω (v ε t))⁻¹ * ω (d t)‖ ≤ 1 := by
      have hvp := hω.positive (v ε t) (hvpos ε hε t ht)
      have hdp := hω.nonneg (hd0 t ht)
      have hdv : d t ≤ v ε t := by dsimp [v]; linarith [hineq t ht]
      have hm := hω.monotone (hd0 t ht) (le_of_lt (hvpos ε hε t ht)) hdv
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hvp.le) hdp)]
      calc
        (ω (v ε t))⁻¹ * ω (d t) ≤ (ω (v ε t))⁻¹ * ω (v ε t) :=
          mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hvp.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hvp)
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hcomp hb (convex_Icc s T)
      (left_mem_Icc.mpr hsT) (right_mem_Icc.mpr hsT)
    have hvs : v ε s = ε := by simp [v]
    simp only [hvs, H, intervalIntegral.integral_same, sub_zero, one_mul,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsT)] at hm
    exact (le_abs_self _).trans hm
  by_contra hn
  have hpos : 0 < d T := lt_of_le_of_ne (hd0 T (right_mem_Icc.mpr hsT)) (Ne.symm hn)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      T-s < ∫ r in ε..d T, (ω r)⁻¹ :=
    (hω.divergent (d T) hpos).eventually (eventually_gt_atTop (T-s))
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (d T) := Ioo_mem_nhdsGT hpos
  obtain ⟨ε, hlarge, hε⟩ := (hev.and heps).exists
  have hvT : d T ≤ v ε T := by
    calc
      d T ≤ ∫ r in s..T, ω (d r) := hineq T (right_mem_Icc.mpr hsT)
      _ ≤ v ε T := le_add_of_nonneg_left hε.1.le
  have hi : IntervalIntegrable (fun r => (ω r)⁻¹) volume ε (v ε T) :=
    (hω.continuousOn_inv.mono (by
      rw [uIcc_of_le (hε.2.le.trans hvT)]
      intro r hr; exact lt_of_lt_of_le hε.1 hr.1)).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_interval (le_refl ε) hε.2.le hvT
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact inv_nonneg.mpr (hω.nonneg (le_of_lt (hε.1.trans hr.1)))) hi
  linarith [hbound ε hε.1]

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Integral norm bound for the increment of the difference of two solutions. -/
theorem solution_difference_increment_bound (F : ODE E) (I : TimeInterval)
    {x y : ℝ → E} (hx : IsSolutionOn F I x) (hy : IsSolutionOn F I y)
    {ω : ℝ → ℝ} (hω : OsgoodModulus ω)
    (hbound : ∀ r ∈ I.carrier, ‖F.eval r (x r) - F.eval r (y r)‖ ≤ ω ‖x r-y r‖)
    {a b : ℝ} (ha : a ∈ I.carrier) (hb : b ∈ I.carrier) (hab : a ≤ b) :
    ‖(x b-y b) - (x a-y a)‖ ≤ ∫ r in a..b, ω ‖x r-y r‖ := by
  have hgx := F.continuousOn_eval.comp (continuousOn_id.prodMk hx.1) hx.2.1
  have hgy := F.continuousOn_eval.comp (continuousOn_id.prodMk hy.1) hy.2.1
  have heq := integral_eq_sub_on_interval I.ordConnected (hx.1.sub hy.1) (hgx.sub hgy)
    (fun r hr => (hx.2.2 r hr).sub (hy.2.2 r hr)) ha hb
  change (∫ r in a..b, F.eval r (x r) - F.eval r (y r)) =
    (x b-y b) - (x a-y a) at heq
  rw [← heq]
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · exact Filter.Eventually.of_forall (fun r hr => hbound r
      (I.ordConnected.out ha hb ⟨hr.1.le, hr.2⟩))
  · exact ((hω.continuous.comp (hx.1.sub hy.1).norm
      (fun r _ => norm_nonneg _)).mono
      (by simpa only [uIcc_of_le hab] using I.ordConnected.out ha hb)).intervalIntegrable

/-- Osgood uniqueness from a modulus estimate along the two actual graphs.
This stronger form does not require the graphs to fill a rectangular box. -/
theorem osgood_unique_of_bound (F : ODE E) (I : TimeInterval)
    (x y : ℝ → E) {ω : ℝ → ℝ} (hω : OsgoodModulus ω)
    (hx : IsSolutionOn F I x) (hy : IsSolutionOn F I y)
    (hbound : ∀ r ∈ I.carrier, ‖F.eval r (x r) - F.eval r (y r)‖ ≤ ω ‖x r-y r‖)
    (s : ℝ) (hs : s ∈ I.carrier) (hxy : x s = y s) : EqOn x y I.carrier := by
  intro t ht
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rcases le_total s t with hst | hts
  · have hsub := I.ordConnected.out hs ht
    apply osgood_integral_zero hω hst ((hx.1.sub hy.1).norm.mono hsub)
      (fun _ _ => norm_nonneg _)
    intro r hr
    simpa only [Pi.sub_apply, hxy, sub_self, sub_zero] using
      solution_difference_increment_bound F I hx hy hω hbound hs (hsub hr) hr.1
  · have hmap : MapsTo (fun r : ℝ => -r) (Icc (-s) (-t)) I.carrier := by
      intro r hr
      apply I.ordConnected.out ht hs
      constructor <;> linarith [hr.1, hr.2]
    have hdc := ((hx.1.sub hy.1).norm).comp continuous_neg.continuousOn hmap
    have hz := osgood_integral_zero hω (neg_le_neg hts) hdc (fun _ _ => norm_nonneg _)
      (by
        intro r hr
        have hrs : -r ≤ s := by linarith [hr.1]
        have hb := solution_difference_increment_bound F I hx hy hω hbound (hmap hr) hs hrs
        change ‖x (-r)-y (-r)‖ ≤ ∫ u in -s..r, (fun u => ω ‖x u-y u‖) (-u)
        rw [intervalIntegral.integral_comp_neg (fun u => ω ‖x u-y u‖), neg_neg]
        simpa only [hxy, sub_self, zero_sub, norm_neg] using hb)
    simpa only [Function.comp_apply, Pi.sub_apply, neg_neg] using hz

/-- Two solutions agree as long as both stay inside the controlled box.
In finite dimension the closed state ball and time interval are compact. -/
theorem osgood_box_unique (F : ODE E) (I : TimeInterval) (x y : ℝ → E)
    (c : ℝ) (z : E) (a b : ℝ) (ω : ℝ → ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (hω : OsgoodModulus ω) (hbox : OsgoodBox F c z a b ω)
    (hx : IsSolutionOn F I x) (hy : IsSolutionOn F I y)
    (htime : I.carrier ⊆ Icc (c-a) (c+a))
    (hxb : ∀ t ∈ I.carrier, x t ∈ Metric.closedBall z b)
    (hyb : ∀ t ∈ I.carrier, y t ∈ Metric.closedBall z b)
    (s : ℝ) (hs : s ∈ I.carrier) (hxy : x s = y s) : EqOn x y I.carrier :=
  osgood_unique_of_bound F I x y hω hx hy
    (fun t ht => hbox.2 t (htime ht) (x t) (hxb t ht) (y t) (hyb t ht)) s hs hxy

/-- Local agreement on both sides, restricted to the actual common domain. -/
theorem osgood_local_unique (F : ODE E) (I J : TimeInterval) (x y : ℝ → E)
    (hx : IsSolutionOn F I x) (hy : IsSolutionOn F J y)
    (s : ℝ) (hs : s ∈ I.carrier ∩ J.carrier) (hxy : x s = y s)
    (hloc : LocalOsgoodAt F s (x s)) :
    ∃ h > 0, EqOn x y ((I.carrier ∩ J.carrier) ∩ Ioo (s-h) (s+h)) := by
  obtain ⟨a, ha, b, hb, ω, hω, hbox⟩ := hloc
  let S := I.carrier ∩ J.carrier
  have hxs : Tendsto x (𝓝[S] s) (𝓝 (x s)) := (hx.1 s hs.1).mono inter_subset_left
  have hys : Tendsto y (𝓝[S] s) (𝓝 (x s)) := by
    rw [hxy]; exact (hy.1 s hs.2).mono inter_subset_right
  have hev := (hxs.eventually (Metric.ball_mem_nhds (x s) hb)).and
    (hys.eventually (Metric.ball_mem_nhds (x s) hb))
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let h := min a ε / 2
  have hh : 0 < h := by dsimp [h]; exact half_pos (lt_min ha hε)
  have hha : h ≤ a := by dsimp [h]; linarith [min_le_left a ε, lt_min ha hε]
  have hhe : h < ε := by dsimp [h]; linarith [min_le_right a ε, lt_min ha hε]
  let K : TimeInterval :=
    ⟨S ∩ Ioo (s-h) (s+h), ⟨s, hs, by constructor <;> linarith⟩,
      (I.ordConnected.inter J.ordConnected).inter ordConnected_Ioo⟩
  have hK (t : ℝ) (ht : t ∈ K.carrier) :
      t ∈ Icc (s-a) (s+a) ∧ x t ∈ Metric.closedBall (x s) b ∧
        y t ∈ Metric.closedBall (x s) b := by
    have ht' : t ∈ S ∩ Ioo (s-h) (s+h) := ht
    have hdist : dist t s < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht'.2.1, ht'.2.2]
    have hv := he ⟨hdist, ht'.1⟩
    exact ⟨⟨by linarith [ht'.2.1], by linarith [ht'.2.2]⟩,
      Metric.ball_subset_closedBall hv.1, Metric.ball_subset_closedBall hv.2⟩
  refine ⟨h, hh, ?_⟩
  exact osgood_box_unique F K x y s (x s) a b ω ha hb hω hbox
    (solutionOn_restrict F I K x (fun _ ht => ht.1.1) hx)
    (solutionOn_restrict F J K y (fun _ ht => ht.1.2) hy)
    (fun t ht => (hK t ht).1) (fun t ht => (hK t ht).2.1)
    (fun t ht => (hK t ht).2.2) s ⟨hs, by constructor <;> linarith⟩ hxy

/-- Propagation of local Osgood uniqueness along the whole common interval. -/
theorem osgood_interval_unique (F : ODE E) (I J : TimeInterval) (x y : ℝ → E)
    (hx : IsSolutionOn F I x) (hy : IsSolutionOn F J y)
    (hloc : ∀ t ∈ I.carrier ∩ J.carrier, x t = y t → LocalOsgoodAt F t (x t))
    (s : ℝ) (hs : s ∈ I.carrier ∩ J.carrier) (hxy : x s = y s) :
    EqOn x y (I.carrier ∩ J.carrier) := by
  let S := I.carrier ∩ J.carrier
  let C : Set S := {t | x t = y t}
  have : PreconnectedSpace S :=
    isPreconnected_iff_preconnectedSpace.mp (I.ordConnected.inter J.ordConnected).isPreconnected
  have hclosed : IsClosed C := isClosed_eq
    (hx.1.mono (show S ⊆ I.carrier from inter_subset_left)).domRestrict
    (hy.1.mono (show S ⊆ J.carrier from inter_subset_right)).domRestrict
  have hopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨h, hh, heq⟩ := osgood_local_unique F I J x y hx hy t t.property ht
      (hloc t t.property ht)
    have hnhds : (Subtype.val ⁻¹' Ioo ((t : ℝ)-h) (t+h) : Set S) ∈ 𝓝 t :=
      (isOpen_Ioo.preimage continuous_subtype_val).mem_nhds (by
        change (t : ℝ)-h < t ∧ (t : ℝ) < t+h
        constructor <;> linarith)
    exact mem_of_superset hnhds (fun r hr => heq ⟨r.property, hr⟩)
  have hC : C = univ := (show IsClopen C from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨s, hs⟩, hxy⟩
  intro t ht
  have hm : (⟨t, ht⟩ : S) ∈ C := hC.symm ▸ mem_univ _
  exact hm

end D13Unified
