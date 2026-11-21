import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.LeftRightNhds

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ExpandedFA.Sobolev.Calculus
open ExpandedFA.Distributions Lines

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem product_rule :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.ProductRule := by
  intro 𝕜 _ d Ω p _ u v g h hu hv hub hvb
  let μ := volume.restrict (Ω : Set (Domain d))
  have hm : MemLp (fun x => u x * v x) p μ := hub.mul (Lp.memLp v)
  have hk (i : Fin d) : MemLp (fun x => g i x * v x + u x * h i x) p μ :=
    ((Lp.memLp (g i)).mul hvb).add (hub.mul (Lp.memLp (h i)))
  let w := hm.toLp (fun x => u x * v x)
  let k := fun i => (hk i).toLp (fun x => g i x * v x + u x * h i x)
  have hw : w =ᵐ[μ] (fun x => u x * v x) := hm.coeFn_toLp
  have hke (i) : k i =ᵐ[μ] (fun x => g i x * v x + u x * h i x) := (hk i).coeFn_toLp
  refine ⟨w, k, ?_, hw, hke⟩
  obtain ⟨f, huf, hf⟩ := weak_to_acl u g hu
  obtain ⟨q, hvq, hq⟩ := weak_to_acl v h hv
  apply acl_to_weak w k (fun x => f x * q x)
  · exact hw.trans (huf.mul hvq)
  intro i
  filter_upwards [hf i, hq i, ae_on_fibers i huf, ae_on_fibers i hvq,
    ae_on_fibers i (hke i)] with y hfy hqy hufy hvqy hky
  refine ⟨?_, ?_⟩
  · intro a b hab
    convert! (hfy.1 a b hab).smul (hqy.1 a b hab) using 1
  filter_upwards [hfy.2, hqy.2, hufy, hvqy, hky] with t hft hqt hut hvt hkt
  convert! hft.mul hqt using 1
  simp only [hkt, hut, hvt]

/-- Composition with a Lipschitz map preserves the vanishing of a derivative,
even at a corner of the outer map. -/
theorem hasDerivAt_comp_zero {f F : ℝ → ℝ} {K : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith K F) (hf : HasDerivAt f 0 t) :
    HasDerivAt (F ∘ f) 0 t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  simp only [smul_zero, sub_zero, Function.comp_apply] at hf ⊢
  exact (Asymptotics.isBigO_of_le' (c := (K : ℝ)) (𝓝 0)
    (fun s => hF.norm_sub_le (f (t + s)) (f t))).trans_isLittleO hf

/-- A derivative on a level set vanishes away from the countably many points
isolated on the right. No measurability of f is needed for this line lemma. -/
theorem ae_derivative_zero_on_level (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ t ∂volume, f t = c → ∀ v, HasDerivAt f v t → v = 0 := by
  let s := {t | f t = c}
  have hc : {t ∈ s | 𝓝[s ∩ Ioi t] t = ⊥}.Countable :=
    countable_setOfPred_isolated_right_within
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hc.measure_zero (μ := volume))] with t ht htc v hv
  have hn : (𝓝[s ∩ Ioi t] t).NeBot := ⟨fun h => ht ⟨htc, h⟩⟩
  have hn' : (𝓝[s \ {t}] t).NeBot := hn.mono
    (nhdsWithin_mono t (fun z hz => ⟨hz.1, by simpa using ne_of_gt hz.2⟩))
  have hud : UniqueDiffWithinAt ℝ s t :=
    uniqueDiffWithinAt_iff_accPt.mpr (accPt_principal_iff_nhdsWithin.mpr hn')
  have hz : HasDerivWithinAt f 0 s t :=
    (hasDerivWithinAt_const t s c).congr (fun z hz => hz) htc
  exact (hv.hasDerivWithinAt.derivWithin hud).symm.trans (hz.derivWithin hud)

theorem chain_rule :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.ChainRule := by
  intro d Ω p _ u g F hu hF hbound hm
  obtain ⟨C, hC⟩ := hbound
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_deriv_le hFd
    (fun t => by exact_mod_cast hC t)
  let μ := volume.restrict (Ω : Set (Domain d))
  have hdf : MemLp (fun x => deriv F (u x)) ∞ μ :=
    memLp_top_of_bound ((hF.continuous_deriv (by decide)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)) C (Eventually.of_forall fun x => hC (u x))
  have hk (i : Fin d) : MemLp (fun x => deriv F (u x) * g i x) p μ :=
    hdf.mul (Lp.memLp (g i))
  let w := hm.toLp (fun x => F (u x))
  let k := fun i => (hk i).toLp (fun x => deriv F (u x) * g i x)
  have hw := hm.coeFn_toLp
  have hke (i) : k i =ᵐ[μ] (fun x => deriv F (u x) * g i x) := (hk i).coeFn_toLp
  refine ⟨w, k, ?_, hw, hke⟩
  obtain ⟨f, huf, hf⟩ := weak_to_acl u g hu
  apply acl_to_weak w k (F ∘ f)
  · exact hw.trans (huf.fun_comp F)
  intro i
  filter_upwards [hf i, ae_on_fibers i huf, ae_on_fibers i (hke i)]
    with y hfy huy hky
  refine ⟨fun a b hab => hLip.comp_absolutelyContinuousOnInterval (hfy.1 a b hab), ?_⟩
  filter_upwards [hfy.2, huy, hky] with t hft hut hkt
  convert! (hFd (f (coordinateLine i y t))).hasDerivAt.comp t hft using 1
  simp only [hkt, hut]

theorem chain_zero_condition :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.ChainZeroCondition := by
  intro d Ω p _ u F hF hbound hzero
  obtain ⟨C, hC⟩ := hbound
  have hLip : LipschitzWith C F := lipschitzWith_of_nnnorm_deriv_le
    (hF.differentiable (by decide)) (fun t => by exact_mod_cast hC t)
  exact hLip.comp_memLp hzero (Lp.memLp u)

/-- Converse Fubini for a measurable predicate, using the exact coordinate
measure-preserving equivalence from the ACL theorem. -/
theorem ae_of_ae_fibers (i : Fin d) {P : Domain d → Prop}
    (hP : MeasurableSet {x | P x})
    (h : ∀ᵐ y : Transverse i ∂volume,
      ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ), P (coordinateLine i y t)) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), P x := by
  let e := (coordinateEquiv i).trans (MeasurableEquiv.prodComm : ℝ × Transverse i ≃ᵐ Transverse i × ℝ)
  have he : MeasurePreserving e volume volume :=
    Measure.measurePreserving_swap.comp (coordinateEquiv_measurePreserving i)
  have hm : MeasurableSet {z : Transverse i × ℝ |
      e.symm z ∈ (Ω : Set (Domain d)) → P (e.symm z)} := by
    convert! (Ω.isOpen.measurableSet.compl.union hP).preimage e.symm.measurable using 1
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_union, mem_compl_iff, imp_iff_not_or]
  have hp : ∀ᵐ z : Transverse i × ℝ ∂volume,
      e.symm z ∈ (Ω : Set (Domain d)) → P (e.symm z) := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [h] with y hy
    have hes (t : ℝ) : e.symm (y, t) = coordinateLine i y t :=
      coordinateEquiv_symm_apply i t y
    filter_upwards [(ae_restrict_iff' (fiber Ω i y).isOpen.measurableSet).mp hy] with t ht
    rw [hes]
    exact ht
  apply (ae_restrict_iff' Ω.isOpen.measurableSet).mpr
  simpa only [MeasurableEquiv.symm_apply_apply] using he.quasiMeasurePreserving.ae hp

theorem level_set_rule :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.LevelSetRule := by
  intro d Ω p _ u g hu c i
  obtain ⟨f, huf, hf⟩ := weak_to_acl u g hu
  have hm : MeasurableSet {x | u x = c → g i x = 0} := by
    convert! ((Lp.stronglyMeasurable u).measurable (measurableSet_singleton c)).compl.union
      ((Lp.stronglyMeasurable (g i)).measurable (measurableSet_singleton 0)) using 1
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, mem_singleton_iff,
      imp_iff_not_or]
  apply ae_of_ae_fibers i hm
  filter_upwards [hf i, ae_on_fibers i huf] with y hfy huy
  filter_upwards [hfy.2, huy,
    (ae_derivative_zero_on_level (fun t => f (coordinateLine i y t)) c).filter_mono
      (ae_restrict_le)] with t hft hut hzt htc
  exact hzt (hut ▸ htc) _ hft

/-- A finite-corner Lipschitz chain rule. The slope is assigned zero at the
corners; the level-set lemma justifies that assignment for the composition. -/
theorem finite_corner_chain (u : DomainLp ℝ Ω p) (g : Fin d → DomainLp ℝ Ω p)
    (hu : HasWeakCoordinateDerivatives u g) (F θ : ℝ → ℝ) {K : ℝ≥0}
    (hLip : LipschitzWith K F) (hθm : Measurable θ)
    (hθb : ∃ C : ℝ≥0, ∀ t, ‖θ t‖ ≤ C) (E : Finset ℝ)
    (hθz : ∀ t ∈ E, θ t = 0)
    (hd : ∀ t, t ∉ E → HasDerivAt F (θ t) t)
    (hm : MemLp (fun x => F (u x)) p (volume.restrict (Ω : Set (Domain d)))) :
    ∃ (w : DomainLp ℝ Ω p) (k : Fin d → DomainLp ℝ Ω p),
      HasWeakCoordinateDerivatives w k ∧
      w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => F (u x)) ∧
      ∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
        (fun x => θ (u x) * g i x) := by
  let μ := volume.restrict (Ω : Set (Domain d))
  obtain ⟨C, hC⟩ := hθb
  have hθ : MemLp (fun x => θ (u x)) ∞ μ :=
    memLp_top_of_bound (hθm.comp_aemeasurable (Lp.aestronglyMeasurable u).aemeasurable
      |>.aestronglyMeasurable) C (Eventually.of_forall fun x => hC (u x))
  have hk (i : Fin d) : MemLp (fun x => θ (u x) * g i x) p μ :=
    hθ.mul (Lp.memLp (g i))
  let w := hm.toLp (fun x => F (u x))
  let k := fun i => (hk i).toLp (fun x => θ (u x) * g i x)
  have hw : w =ᵐ[μ] (fun x => F (u x)) := hm.coeFn_toLp
  have hke (i) : k i =ᵐ[μ] (fun x => θ (u x) * g i x) := (hk i).coeFn_toLp
  refine ⟨w, k, ?_, hw, hke⟩
  obtain ⟨f, huf, hf⟩ := weak_to_acl u g hu
  apply acl_to_weak w k (F ∘ f)
  · exact hw.trans (huf.fun_comp F)
  intro i
  filter_upwards [hf i, ae_on_fibers i huf, ae_on_fibers i (hke i)]
    with y hfy huy hky
  have hz : ∀ᵐ t ∂volume.restrict (fiber Ω i y : Set ℝ),
      ∀ c ∈ E, f (coordinateLine i y t) = c →
        ∀ v, HasDerivAt (fun s => f (coordinateLine i y s)) v t → v = 0 := by
    apply (eventually_all_finset E).mpr
    intro c hc
    exact (ae_derivative_zero_on_level (fun t => f (coordinateLine i y t)) c).filter_mono
      ae_restrict_le
  refine ⟨fun a b hab => hLip.comp_absolutelyContinuousOnInterval (hfy.1 a b hab), ?_⟩
  filter_upwards [hfy.2, huy, hky, hz] with t hft hut hkt hzt
  rw [hkt, hut]
  by_cases htE : f (coordinateLine i y t) ∈ E
  · have hg0 := hzt _ htE rfl _ hft
    simp only [hθz _ htE, zero_mul]
    exact hasDerivAt_comp_zero hLip (hg0 ▸ hft)
  · exact (hd _ htE).comp t hft


theorem absolute_value_rule :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.AbsoluteValueRule := by
  intro d Ω p _ u g hu
  let θ := fun t : ℝ => if 0 < t then (1 : ℝ) else if t < 0 then -1 else 0
  have hLip : LipschitzWith 1 (fun t : ℝ => |t|) := by
    convert! (lipschitzWith_one_norm (E := ℝ)) using 1
  have hθm : Measurable θ :=
    Measurable.ite measurableSet_Ioi measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have hθb : ∃ C : ℝ≥0, ∀ t, ‖θ t‖ ≤ C := by
    refine ⟨1, fun t => ?_⟩
    dsimp [θ]
    split_ifs <;> norm_num
  have hd : ∀ t : ℝ, t ∉ ({0} : Finset ℝ) → HasDerivAt (fun t : ℝ => |t|) (θ t) t := by
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rcases lt_or_gt_of_ne ht0 with ht | ht
    · simpa [θ, not_lt_of_gt ht, ht] using hasDerivAt_abs_neg ht
    · simpa only [θ, ht, ite_true] using hasDerivAt_abs_pos ht
  obtain ⟨w, k, hwk, hw, hk⟩ := finite_corner_chain u g hu (fun t => |t|) θ hLip hθm hθb
    {0} (by intro t ht; simp only [Finset.mem_singleton] at ht; subst t; simp [θ]) hd
    (hLip.comp_memLp (abs_zero) (Lp.memLp u))
  refine ⟨w, k, hwk, hw, fun i => ?_⟩
  filter_upwards [hk i] with x hx
  rw [hx]
  dsimp [θ]
  split_ifs <;> simp

/-- Positive part, with derivative zero on the zero level. -/
theorem positive_part_rule :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.PositivePartRule := by
  intro d Ω p _ u g hu
  let θ := fun t : ℝ => if 0 < t then (1 : ℝ) else 0
  have hLip : LipschitzWith 1 (fun t : ℝ => max 0 t) := LipschitzWith.id.const_max 0
  have hθm : Measurable θ := Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hθb : ∃ C : ℝ≥0, ∀ t, ‖θ t‖ ≤ C := by
    refine ⟨1, fun t => ?_⟩
    dsimp [θ]
    split_ifs <;> norm_num
  have hd : ∀ t : ℝ, t ∉ ({0} : Finset ℝ) → HasDerivAt (fun t : ℝ => max 0 t) (θ t) t := by
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rcases lt_or_gt_of_ne ht0 with ht | ht
    · have he : (fun s : ℝ => max 0 s) =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [eventually_lt_nhds ht] with s hs
        exact max_eq_left hs.le
      simpa [θ, not_lt_of_gt ht] using
        (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
    · have he : (fun s : ℝ => max 0 s) =ᶠ[𝓝 t] id := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        exact max_eq_right hs.le
      simpa only [θ, ht, ite_true] using (hasDerivAt_id t).congr_of_eventuallyEq he
  obtain ⟨w, k, hwk, hw, hk⟩ := finite_corner_chain u g hu (fun t => max 0 t) θ hLip hθm hθb
    {0} (by intro t ht; simp only [Finset.mem_singleton] at ht; subst t; simp [θ]) hd
    (hLip.comp_memLp (max_self 0) (Lp.memLp u))
  refine ⟨w, k, hwk, hw, fun i => ?_⟩
  filter_upwards [hk i] with x hx
  rw [hx]
  dsimp [θ]
  split_ifs <;> simp

/-- Clipping is 1-Lipschitz, including a degenerate clipping interval. -/
theorem truncation_lipschitz (a b : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max a (min b t)) :=
  (LipschitzWith.id.const_min b).const_max a

theorem truncation_zero_condition :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.TruncationZeroCondition := by
  intro d Ω p _ u a b ha hb
  exact (truncation_lipschitz a b).comp_memLp
    (by rw [min_eq_right hb, max_eq_right ha]) (Lp.memLp u)

theorem truncation_rule :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.TruncationRule := by
  intro d Ω p _ u g a b hab hu hm
  let θ := fun t : ℝ => if a < t ∧ t < b then (1 : ℝ) else 0
  have hθm : Measurable θ := Measurable.ite
    (measurableSet_Ioi.inter measurableSet_Iio) measurable_const measurable_const
  have hθb : ∃ C : ℝ≥0, ∀ t, ‖θ t‖ ≤ C := by
    refine ⟨1, fun t => ?_⟩
    dsimp [θ]
    split_ifs <;> norm_num
  have hθz : ∀ t ∈ ({a, b} : Finset ℝ), θ t = 0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [θ]
  have hd : ∀ t : ℝ, t ∉ ({a, b} : Finset ℝ) →
      HasDerivAt (fun t : ℝ => max a (min b t)) (θ t) t := by
    intro t ht
    have hta : t ≠ a := by aesop
    have htb : t ≠ b := by aesop
    by_cases hlt : t < a
    · have he : (fun s : ℝ => max a (min b s)) =ᶠ[𝓝 t] (fun _ => a) := by
        filter_upwards [eventually_lt_nhds hlt] with s hs
        rw [min_eq_right (hs.le.trans hab), max_eq_left hs.le]
      simpa [θ, not_lt_of_gt hlt] using (hasDerivAt_const t a).congr_of_eventuallyEq he
    have hat : a < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hta)
    by_cases hgt : b < t
    · have he : (fun s : ℝ => max a (min b s)) =ᶠ[𝓝 t] (fun _ => b) := by
        filter_upwards [eventually_gt_nhds hgt] with s hs
        rw [min_eq_left hs.le, max_eq_right hab]
      simpa [θ, not_lt_of_gt hgt] using (hasDerivAt_const t b).congr_of_eventuallyEq he
    have htb' : t < b := lt_of_le_of_ne (le_of_not_gt hgt) htb
    have he : (fun s : ℝ => max a (min b s)) =ᶠ[𝓝 t] id := by
      filter_upwards [eventually_gt_nhds hat, eventually_lt_nhds htb'] with s hs hs'
      rw [min_eq_right hs'.le, max_eq_right hs.le]
      rfl
    simpa [θ, hat, htb'] using (hasDerivAt_id t).congr_of_eventuallyEq he
  obtain ⟨w, k, hwk, hw, hk⟩ := finite_corner_chain u g hu
    (fun t => max a (min b t)) θ (truncation_lipschitz a b) hθm hθb {a, b} hθz hd hm
  refine ⟨w, k, hwk, hw, fun i => ?_⟩
  filter_upwards [hk i] with x hx
  rw [hx]
  dsimp [θ]
  split_ifs <;> simp

/-- The coordinate formulation used by all calculus rules is equivalent to
membership in the original derivative graph, via the accepted order-one bridge. -/
theorem first_order_graph_bridge :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.FirstOrderGraphBridge := by
  intro 𝕜 _ d Ω p _ u
  exact first_order_membership_iff u

/-- Negative part, also with zero derivative at the zero level. -/
theorem negative_part_rule :
    Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules.NegativePartRule := by
  intro d Ω p _ u g hu
  let θ := fun t : ℝ => if t < 0 then (-1 : ℝ) else 0
  have hLip : LipschitzWith 1 (fun t : ℝ => max 0 (-t)) :=
    LipschitzWith.id.neg.const_max 0
  have hθm : Measurable θ := Measurable.ite measurableSet_Iio measurable_const measurable_const
  have hθb : ∃ C : ℝ≥0, ∀ t, ‖θ t‖ ≤ C := by
    refine ⟨1, fun t => ?_⟩
    dsimp [θ]
    split_ifs <;> norm_num
  have hd : ∀ t : ℝ, t ∉ ({0} : Finset ℝ) →
      HasDerivAt (fun t : ℝ => max 0 (-t)) (θ t) t := by
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rcases lt_or_gt_of_ne ht0 with ht | ht
    · have he : (fun s : ℝ => max 0 (-s)) =ᶠ[𝓝 t] (fun s => -s) := by
        filter_upwards [eventually_lt_nhds ht] with s hs
        exact max_eq_right (neg_nonneg.mpr hs.le)
      simpa [θ, ht] using (hasDerivAt_id t).neg.congr_of_eventuallyEq he
    · have he : (fun s : ℝ => max 0 (-s)) =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        exact max_eq_left (neg_nonpos.mpr hs.le)
      simpa [θ, not_lt_of_gt ht] using (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
  obtain ⟨w, k, hwk, hw, hk⟩ := finite_corner_chain u g hu (fun t => max 0 (-t)) θ hLip hθm hθb
    {0} (by intro t ht; simp only [Finset.mem_singleton] at ht; subst t; simp [θ]) hd
    (hLip.comp_memLp (by simp) (Lp.memLp u))
  refine ⟨w, k, hwk, hw, fun i => ?_⟩
  filter_upwards [hk i] with x hx
  rw [hx]
  dsimp [θ]
  split_ifs <;> simp

end ExpandedFA.Sobolev.Calculus
