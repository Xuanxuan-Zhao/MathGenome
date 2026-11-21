import MathGenome.Internal.FourierSobolev.Specs.P102.U4.Truncations
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ACL
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevProductAndChainRules

import MathGenome.Internal.FourierSobolev.P102.U4.ACL
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace P102.U4
namespace Truncations

/-- Transfer the domain to ordinary product coordinates, preserving volume. -/
def productDomain {d : ℕ} (Ω : Opens (Space d)) : Opens (Fin d → ℝ) :=
  ⟨WithLp.toLp 2 ⁻¹' (Ω : Set (Space d)),
    Ω.isOpen.preimage (PiLp.continuous_toLp 2 _)⟩

/-- Fubini for the Euclidean coordinate lines used in the frozen ACL interface. -/
theorem ae_on_lines {d : ℕ} {Ω : Opens (Space d)} (j : Fin d)
    {P : Space d → Prop} (hP : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), P x) :
    ∀ᵐ z : ACL.Transverse j ∂volume,
      ∀ᵐ t ∂volume.restrict (ACL.fiber Ω j z), P (ACL.line j z t) := by
  have h := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hP
  have hp := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae h
  have hp' : ∀ᵐ x ∂volume.restrict (productDomain Ω : Set (Fin d → ℝ)),
      P (WithLp.toLp 2 x) :=
    (ae_restrict_iff' (productDomain Ω).isOpen.measurableSet).mpr hp
  exact ExpandedFA.Sobolev.Lines.ae_on_fibers (Ω := productDomain Ω)
    (P := fun x => P (WithLp.toLp 2 x)) j hp'

/-- Converse Fubini is applied to measurable ambient predicates. -/
theorem ae_of_ae_lines {d : ℕ} {Ω : Opens (Space d)} (j : Fin d)
    {P : Space d → Prop} (hP : MeasurableSet {x | P x})
    (h : ∀ᵐ z : ACL.Transverse j ∂volume,
      ∀ᵐ t ∂volume.restrict (ACL.fiber Ω j z), P (ACL.line j z t)) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), P x := by
  have hm : MeasurableSet {x : Fin d → ℝ | P (WithLp.toLp 2 x)} :=
    hP.preimage (PiLp.continuous_toLp 2 _).measurable
  have hp := ExpandedFA.Sobolev.Calculus.ae_of_ae_fibers (Ω := productDomain Ω) j hm h
  have hp' := (ae_restrict_iff' (productDomain Ω).isOpen.measurableSet).mp hp
  have he := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae hp'
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).mpr he

/-- A coordinate direction itself supplies the positive-dimension hypothesis. -/
theorem dimension_pos {d : ℕ} (j : Fin d) : 0 < d :=
  Nat.zero_lt_of_lt j.isLt

/-- The canonical Sobolev coordinate derivative has an ACL representative. -/
theorem representative (hACL : ACLExpected.Characterization)
    {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (j : Fin d) :
    ACL.HasRepresentative Ω j (sobolevUnderlying u) (sobolevFirstDerivative u j) := by
  apply (hACL d (dimension_pos j) ℝ Ω j _ _
    (domainLp_locallyIntegrable Ω p _) (domainLp_locallyIntegrable Ω p _)).mp
  exact sobolev_derivative_distribution Ω 1 p u (firstSobolevIndex j)

/-- Build the order-one graph from all its coordinate distribution equations. -/
theorem exists_sobolev_of_coordinates {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p) (g : Fin d → DomainLp ℝ Ω p)
    (h : ∀ j, distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω (g j)) :
    ∃ w : Sobolev ℝ Ω 1 p, sobolevUnderlying w = u ∧
      ∀ j, sobolevFirstDerivative w j = g j := by
  have hu : HasSobolevDerivatives Ω 1 p u := by
    intro α hα
    by_cases hz : α.card = 0
    · have ha : α = 0 := Multiset.card_eq_zero.mp hz
      exact ⟨u, ha ▸ derivative_zero d ℝ Ω _⟩
    · obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp (by omega : α.card = 1)
      exact ⟨g j, h j⟩
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (sobolev_range Ω 1 p) u).mpr hu
  refine ⟨w, hw, fun j => ?_⟩
  exact (sobolev_derivative_unique Ω 1 p w (firstSobolevIndex j) (g j)
    (by simpa only [hw, firstSobolevIndex] using h j)).symm

/-- Integrability of a Lipschitz composition under precisely the source's
zero-order alternatives. The shift by F(0) is used only for this estimate. -/
theorem composition_memLp {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p) (F : ℝ → ℝ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (ha : TruncationsExpected.Admissible (Ω := Ω) (p := p) F) :
    MemLp (fun x => F (u x)) p (volume.restrict (Ω : Set (Space d))) := by
  rcases ha with hz | hfin | rfl
  · exact hF.comp_memLp hz (Lp.memLp u)
  all_goals
    have hshift : LipschitzWith K (fun t => F t - F 0) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hF.dist_le_mul x y
    have hm := hshift.comp_memLp (sub_self _) (Lp.memLp u)
  · let : IsFiniteMeasure (volume.restrict (Ω : Set (Space d))) :=
      isFiniteMeasure_restrict.mpr hfin.ne
    exact (hm.add (memLp_const (F 0))).ae_eq
      (Eventually.of_forall fun x => sub_add_cancel (F (u x)) (F 0))
  · exact (hm.add (memLp_top_const (F 0))).ae_eq
      (Eventually.of_forall fun x => sub_add_cancel (F (u x)) (F 0))

/-- A finite-corner chain rule proved from the conditional ACL equivalence.
Only line calculus and the canonical derivative graph enter the proof. -/
theorem finite_corner_composition
    (hACL : ACLExpected.Characterization) (hConverse : ACLExpected.Converse)
    {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (F θ : ℝ → ℝ) {K : ℝ≥0}
    (hLip : LipschitzWith K F) (hθm : Measurable θ)
    (hθb : ∃ C : ℝ≥0, ∀ t, ‖θ t‖ ≤ C) (E : Finset ℝ)
    (hθz : ∀ t ∈ E, θ t = 0)
    (hd : ∀ t, t ∉ E → HasDerivAt F (θ t) t)
    (hm : MemLp (fun x => F (sobolevUnderlying u x)) p
      (volume.restrict (Ω : Set (Space d)))) :
    ∃ w : Sobolev ℝ Ω 1 p,
      sobolevUnderlying w =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => F (sobolevUnderlying u x)) ∧
      ∀ j, sobolevFirstDerivative w j =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => θ (sobolevUnderlying u x) * sobolevFirstDerivative u j x) := by
  let μ := volume.restrict (Ω : Set (Space d))
  obtain ⟨C, hC⟩ := hθb
  have hθ : MemLp (fun x => θ (sobolevUnderlying u x)) ∞ μ :=
    memLp_top_of_bound (hθm.comp_aemeasurable
      (Lp.aestronglyMeasurable (sobolevUnderlying u)).aemeasurable |>.aestronglyMeasurable)
        C (Eventually.of_forall fun x => hC _)
  have hk (j : Fin d) : MemLp
      (fun x => θ (sobolevUnderlying u x) * sobolevFirstDerivative u j x) p μ :=
    hθ.mul (Lp.memLp _)
  let v := hm.toLp (fun x => F (sobolevUnderlying u x))
  let k := fun j => (hk j).toLp
    (fun x => θ (sobolevUnderlying u x) * sobolevFirstDerivative u j x)
  have hv : v =ᵐ[μ] (fun x => F (sobolevUnderlying u x)) := hm.coeFn_toLp
  have hke (j) : k j =ᵐ[μ]
      (fun x => θ (sobolevUnderlying u x) * sobolevFirstDerivative u j x) :=
    (hk j).coeFn_toLp
  have hweak (j : Fin d) : distributionPartial {j} (regularDistribution Ω v) =
      regularDistribution Ω (k j) := by
    obtain ⟨f, huf, hf⟩ := representative hACL u j
    apply hConverse d (dimension_pos j) ℝ Ω j _ _
      (domainLp_locallyIntegrable Ω p _) (domainLp_locallyIntegrable Ω p _)
    refine ⟨F ∘ f, hv.trans (huf.fun_comp F), ?_⟩
    filter_upwards [hf, ae_on_lines j huf, ae_on_lines j (hke j)] with z hfz huz hkz
    have hz : ∀ᵐ t ∂volume.restrict (ACL.fiber Ω j z),
        ∀ c ∈ E, f (ACL.line j z t) = c → ∀ v,
          HasDerivAt (fun s => f (ACL.line j z s)) v t → v = 0 := by
      apply (eventually_all_finset E).mpr
      intro c hc
      exact (ExpandedFA.Sobolev.Calculus.ae_derivative_zero_on_level
        (fun t => f (ACL.line j z t)) c).filter_mono ae_restrict_le
    refine ⟨fun a b hab => hLip.comp_absolutelyContinuousOnInterval (hfz.1 a b hab), ?_⟩
    filter_upwards [hfz.2, huz, hkz, hz] with t hft hut hkt hzt
    rw [hkt, hut]
    by_cases htE : f (ACL.line j z t) ∈ E
    · have hg0 := hzt _ htE rfl _ hft
      simp only [hθz _ htE, zero_mul]
      exact ExpandedFA.Sobolev.Calculus.hasDerivAt_comp_zero hLip (hg0 ▸ hft)
    · exact (hd _ htE).comp t hft
  obtain ⟨w, hw, hwd⟩ := exists_sobolev_of_coordinates v k hweak
  exact ⟨w, hw ▸ hv, fun j => hwd j ▸ hke j⟩

/-- Indicator-slope specialization of the finite-corner chain rule. -/
theorem cutoff_composition
    (hACL : ACLExpected.Characterization) (hConverse : ACLExpected.Converse)
    {d : ℕ} {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev ℝ Ω 1 p) (F : ℝ → ℝ) (S : Set ℝ) {K : ℝ≥0}
    (hLip : LipschitzWith K F) (hS : MeasurableSet S) (E : Finset ℝ)
    (hE : ∀ t ∈ E, t ∉ S)
    (hd : ∀ t, t ∉ E → HasDerivAt F (if t ∈ S then 1 else 0) t)
    (ha : TruncationsExpected.Admissible (Ω := Ω) (p := p) F) :
    TruncationsExpected.CompositionResult u F S := by
  classical
  let θ := fun t : ℝ => if t ∈ S then (1 : ℝ) else 0
  have hθm : Measurable θ := Measurable.ite hS measurable_const measurable_const
  have hθb : ∃ C : ℝ≥0, ∀ t, ‖θ t‖ ≤ C := by
    refine ⟨1, fun t => ?_⟩
    dsimp [θ]
    split_ifs <;> norm_num
  have hθz : ∀ t ∈ E, θ t = 0 := fun t ht => ite_eq_right (hE t ht)
  obtain ⟨w, hw, hwd⟩ := finite_corner_composition hACL hConverse u F θ
    hLip hθm hθb E hθz hd (composition_memLp (sobolevUnderlying u) F hLip ha)
  refine ⟨w, hw, fun j => ?_⟩
  filter_upwards [hwd j] with x hx
  rw [hx]
  dsimp [θ]
  split_ifs <;> simp

end Truncations

open Truncations

/-- Conditional draft: vanishing of canonical derivatives on every fixed level. -/
theorem truncation_level_set_conditional
    (hACL : ACLExpected.Characterization) (_hConverse : ACLExpected.Converse)
    (_hDimensionOne : ACLExpected.DimensionOne) : TruncationsExpected.LevelSet := by
  intro d Ω p _ u c j
  have hm : MeasurableSet {x | sobolevUnderlying u x = c → sobolevFirstDerivative u j x = 0} := by
    convert ((Lp.stronglyMeasurable (sobolevUnderlying u)).measurable
      (measurableSet_singleton c)).compl.union
      ((Lp.stronglyMeasurable (sobolevFirstDerivative u j)).measurable
        (measurableSet_singleton 0)) using 1
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, mem_singleton_iff,
      imp_iff_not_or]
  apply Truncations.ae_of_ae_lines j hm
  obtain ⟨f, huf, hf⟩ := Truncations.representative hACL u j
  filter_upwards [hf, Truncations.ae_on_lines j huf] with z hfz huz
  filter_upwards [hfz.2, huz,
    (ExpandedFA.Sobolev.Calculus.ae_derivative_zero_on_level
      (fun t => f (ACL.line j z t)) c).filter_mono ae_restrict_le]
    with t hft hut hzt htc
  exact hzt (hut ▸ htc) _ hft


/-- Conditional draft: finite clipping with strict interior slope. -/
theorem truncation_rule_conditional
    (hACL : ACLExpected.Characterization) (hConverse : ACLExpected.Converse)
    (_hDimensionOne : ACLExpected.DimensionOne) : TruncationsExpected.Truncation := by
  intro d Ω p _ u a b hab ha
  classical
  have hadm : TruncationsExpected.Admissible (Ω := Ω) (p := p)
      (fun t => max a (min b t)) := by
    rcases ha with ⟨ha, hb⟩ | hfin | hp
    · exact Or.inl (by dsimp; rw [min_eq_right hb, max_eq_right ha])
    · exact Or.inr (Or.inl hfin)
    · exact Or.inr (Or.inr hp)
  have hd : ∀ t : ℝ, t ∉ ({a, b} : Finset ℝ) →
      HasDerivAt (fun s : ℝ => max a (min b s)) (if t ∈ Ioo a b then 1 else 0) t := by
    intro t ht
    have hta : t ≠ a := by aesop
    have htb : t ≠ b := by aesop
    by_cases hlt : t < a
    · have he : (fun s : ℝ => max a (min b s)) =ᶠ[𝓝 t] (fun _ => a) := by
        filter_upwards [eventually_lt_nhds hlt] with s hs
        rw [min_eq_right (hs.le.trans hab), max_eq_left hs.le]
      simpa [mem_Ioo, not_lt_of_gt hlt] using
        (hasDerivAt_const t a).congr_of_eventuallyEq he
    have hat : a < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hta)
    by_cases hgt : b < t
    · have he : (fun s : ℝ => max a (min b s)) =ᶠ[𝓝 t] (fun _ => b) := by
        filter_upwards [eventually_gt_nhds hgt] with s hs
        rw [min_eq_left hs.le, max_eq_right hab]
      simpa [mem_Ioo, not_lt_of_gt hgt] using
        (hasDerivAt_const t b).congr_of_eventuallyEq he
    have htb' : t < b := lt_of_le_of_ne (le_of_not_gt hgt) htb
    have he : (fun s : ℝ => max a (min b s)) =ᶠ[𝓝 t] id := by
      filter_upwards [eventually_gt_nhds hat, eventually_lt_nhds htb'] with s hs hs'
      rw [min_eq_right hs'.le, max_eq_right hs.le]
      rfl
    simpa [mem_Ioo, hat, htb'] using (hasDerivAt_id t).congr_of_eventuallyEq he
  exact Truncations.cutoff_composition hACL hConverse u _ (Ioo a b)
    (ExpandedFA.Sobolev.Calculus.truncation_lipschitz a b) measurableSet_Ioo {a, b}
    (by intro t ht; rcases Finset.mem_insert.mp ht with rfl | ht
        · simp
        · have : t = b := Finset.mem_singleton.mp ht
          subst t
          simp) (by
      intro t ht
      convert hd t ht using 1
      split_ifs <;> rfl) hadm

/-- Conditional draft: lower clipping, including the cutoff-level formula. -/
theorem lower_truncation_rule_conditional
    (hACL : ACLExpected.Characterization) (hConverse : ACLExpected.Converse)
    (_hDimensionOne : ACLExpected.DimensionOne) : TruncationsExpected.LowerTruncation := by
  intro d Ω p _ u a ha
  classical
  have hadm : TruncationsExpected.Admissible (Ω := Ω) (p := p) (fun t => max a t) := by
    rcases ha with ha | hfin | hp
    · exact Or.inl (max_eq_right ha)
    · exact Or.inr (Or.inl hfin)
    · exact Or.inr (Or.inr hp)
  have hd : ∀ t : ℝ, t ∉ ({a} : Finset ℝ) →
      HasDerivAt (fun s : ℝ => max a s) (if t ∈ Ioi a then 1 else 0) t := by
    intro t ht
    have hta : t ≠ a := by simpa using ht
    rcases lt_or_gt_of_ne hta with hlt | hgt
    · have he : (fun s : ℝ => max a s) =ᶠ[𝓝 t] (fun _ => a) := by
        filter_upwards [eventually_lt_nhds hlt] with s hs
        exact max_eq_left hs.le
      simpa [mem_Ioi, not_lt_of_gt hlt] using
        (hasDerivAt_const t a).congr_of_eventuallyEq he
    · have he : (fun s : ℝ => max a s) =ᶠ[𝓝 t] id := by
        filter_upwards [eventually_gt_nhds hgt] with s hs
        exact max_eq_right hs.le
      simpa [mem_Ioi, hgt] using (hasDerivAt_id t).congr_of_eventuallyEq he
  exact Truncations.cutoff_composition hACL hConverse u _ (Ioi a)
    (LipschitzWith.id.const_max a) measurableSet_Ioi {a}
    (by intro t ht; have : t = a := Finset.mem_singleton.mp ht; subst t; simp) hd hadm

/-- Conditional draft: upper clipping, including the cutoff-level formula. -/
theorem upper_truncation_rule_conditional
    (hACL : ACLExpected.Characterization) (hConverse : ACLExpected.Converse)
    (_hDimensionOne : ACLExpected.DimensionOne) : TruncationsExpected.UpperTruncation := by
  intro d Ω p _ u b ha
  classical
  have hadm : TruncationsExpected.Admissible (Ω := Ω) (p := p) (fun t => min b t) := by
    rcases ha with hb | hfin | hp
    · exact Or.inl (min_eq_right hb)
    · exact Or.inr (Or.inl hfin)
    · exact Or.inr (Or.inr hp)
  have hd : ∀ t : ℝ, t ∉ ({b} : Finset ℝ) →
      HasDerivAt (fun s : ℝ => min b s) (if t ∈ Iio b then 1 else 0) t := by
    intro t ht
    have htb : t ≠ b := by simpa using ht
    rcases lt_or_gt_of_ne htb with hlt | hgt
    · have he : (fun s : ℝ => min b s) =ᶠ[𝓝 t] id := by
        filter_upwards [eventually_lt_nhds hlt] with s hs
        exact min_eq_right hs.le
      simpa [mem_Iio, hlt] using (hasDerivAt_id t).congr_of_eventuallyEq he
    · have he : (fun s : ℝ => min b s) =ᶠ[𝓝 t] (fun _ => b) := by
        filter_upwards [eventually_gt_nhds hgt] with s hs
        exact min_eq_left hs.le
      simpa [mem_Iio, not_lt_of_gt hgt] using
        (hasDerivAt_const t b).congr_of_eventuallyEq he
  exact Truncations.cutoff_composition hACL hConverse u _ (Iio b)
    (LipschitzWith.id.const_min b) measurableSet_Iio {b}
    (by intro t ht; have : t = b := Finset.mem_singleton.mp ht; subst t; simp) hd hadm

end P102.U4

theorem _root_.«P102».«U4».«lower_truncation_rule» : _root_.«P102».«U4».«TruncationsExpected».«LowerTruncation» :=
  @_root_.«P102».«U4».«lower_truncation_rule_conditional» (@_root_.«P102».«U4».«acl_characterization») (@_root_.«P102».«U4».«acl_converse») (@_root_.«P102».«U4».«acl_dimensionOne»)
theorem _root_.«P102».«U4».«truncation_level_set» : _root_.«P102».«U4».«TruncationsExpected».«LevelSet» :=
  @_root_.«P102».«U4».«truncation_level_set_conditional» (@_root_.«P102».«U4».«acl_characterization») (@_root_.«P102».«U4».«acl_converse») (@_root_.«P102».«U4».«acl_dimensionOne»)
theorem _root_.«P102».«U4».«truncation_rule» : _root_.«P102».«U4».«TruncationsExpected».«Truncation» :=
  @_root_.«P102».«U4».«truncation_rule_conditional» (@_root_.«P102».«U4».«acl_characterization») (@_root_.«P102».«U4».«acl_converse») (@_root_.«P102».«U4».«acl_dimensionOne»)
theorem _root_.«P102».«U4».«upper_truncation_rule» : _root_.«P102».«U4».«TruncationsExpected».«UpperTruncation» :=
  @_root_.«P102».«U4».«upper_truncation_rule_conditional» (@_root_.«P102».«U4».«acl_characterization») (@_root_.«P102».«U4».«acl_converse») (@_root_.«P102».«U4».«acl_dimensionOne»)
