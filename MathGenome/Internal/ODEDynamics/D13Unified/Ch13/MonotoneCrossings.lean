import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.MonotoneCrossings
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.Nullclines
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.IndexJump
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Successive meetings retain the actual maximal interval. The analytic,
periodic and sequence arguments are separated from the planar index barrier. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch13.MonotoneCrossings
open Ch13.Nullclines Ch06.StateDerivative
open Specs.D13Unified.Ch13.MonotoneCrossings
open Specs.D13Unified.Ch13.Nullclines

/-- Signed height above the oriented supporting line. -/
def signedHeight : StraightSegment → Plane → ℝ := signedHeightValue

lemma signedHeight_point (S : StraightSegment) (u : ℝ) :
    signedHeight S (S.point u) = 0 := by
  change S.direction.1 * ((S.center.2 + u * S.direction.2) - S.center.2) -
    S.direction.2 * ((S.center.1 + u * S.direction.1) - S.center.1) = 0
  ring

lemma signedHeight_eq_zero_of_mem {S : StraightSegment} {p : Plane}
    (hp : p ∈ S.carrier) : signedHeight S p = 0 := by
  obtain ⟨u, _, rfl⟩ := hp
  exact signedHeight_point S u

lemma coordinate_injOn (S : StraightSegment) : Set.InjOn S.coordinate S.carrier := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ he
  change segmentCoordinateValue S (segmentPointValue S u) =
    segmentCoordinateValue S (segmentPointValue S v) at he
  rw [Ch13.Nullclines.coordinate_point S u, Ch13.Nullclines.coordinate_point S v] at he
  exact congrArg S.point he

lemma nonconstant_of_hit (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {t : ℝ} (ht : t ∈ (flowInterval F x).carrier)
    (hh : flow F t x ∈ S.toStraightSegment.carrier) : ¬ Ch11.Orbits.IsConstant F x := by
  intro hc
  have hxS : x ∈ S.toStraightSegment.carrier := by simpa only [hc t ht] using hh
  have he : F.eval x = 0 := (Ch11.Orbits.equilibrium_characterization F hF x hx).mpr hc
  have hn := S.transverse.2 x hxS
  apply hn
  change S.direction.1 * (F.eval x).2 - S.direction.2 * (F.eval x).1 = 0
  rw [he]
  simp

theorem repeated_intersection : RepeatedIntersection := by
  intro F hF x hx S a ha b hb hab hh he
  have hn := nonconstant_of_hit F hF hx S ha hh
  exact ⟨Ch11.Orbits.self_intersection_least_period F hF x hx hn a ha b hb
    (ne_of_lt hab) he,
    (Ch11.Orbits.self_intersection F hF x hx a ha b hb (ne_of_lt hab) he).2⟩

/-- Equal consecutive meetings repeat the same first-return time. This uses
uniqueness and succession alone, without any planar separation theorem. -/
lemma equal_successive_next (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    {S : StraightSegment} {a b c : ℝ} (hab : Successive F S x a b)
    (hbc : Successive F S x b c) (he : flow F a x = flow F b x) :
    c-b = b-a ∧ flow F b x = flow F c x := by
  have hp := (Ch11.Orbits.self_intersection F hF x hx a hab.first_time b
    hab.second_time (ne_of_lt hab.lt) he).2
  change ∀ r, flow F (r+(b-a)) x = flow F r x at hp
  have hc : c = b+(b-a) := by
    rcases lt_trichotomy c (b+(b-a)) with hlt | heq | hgt
    · have hmem : flow F (c-(b-a)) x ∈ S.carrier := by
        have hp' := hp (c-(b-a))
        rw [sub_add_cancel] at hp'
        rw [← hp']
        exact hbc.second_hit
      exact False.elim (hab.no_hit (c-(b-a)) ⟨by linarith [hbc.lt], by linarith⟩ hmem)
    · exact heq
    · exact False.elim (hbc.no_hit (b+(b-a)) ⟨by linarith [hab.lt], hgt⟩
        (by simpa only [hp b] using hab.second_hit))
  refine ⟨by linarith, ?_⟩
  rw [hc, hp b]

/-- The same first-return argument backwards through a preceding pair. -/
lemma equal_successive_prev (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    {S : StraightSegment} {a b c : ℝ} (hab : Successive F S x a b)
    (hbc : Successive F S x b c) (he : flow F b x = flow F c x) :
    b-a = c-b ∧ flow F a x = flow F b x := by
  have hp := (Ch11.Orbits.self_intersection F hF x hx b hbc.first_time c
    hbc.second_time (ne_of_lt hbc.lt) he).2
  change ∀ r, flow F (r+(c-b)) x = flow F r x at hp
  have ha : a = b-(c-b) := by
    rcases lt_trichotomy a (b-(c-b)) with hlt | heq | hgt
    · have hmem : flow F (b-(c-b)) x ∈ S.carrier := by
        have hp' := hp (b-(c-b))
        rw [sub_add_cancel] at hp'
        rw [← hp']
        exact hab.second_hit
      exact False.elim (hab.no_hit (b-(c-b)) ⟨hlt, by linarith [hbc.lt]⟩ hmem)
    · exact heq
    · exact False.elim (hbc.no_hit (a+(c-b)) ⟨by linarith, by linarith [hab.lt]⟩
        (by simpa only [hp a] using hab.first_hit))
  refine ⟨by linarith, ?_⟩
  have := hp a
  rw [ha] at this ⊢
  simpa using this.symm

/-- A distinct successive pair has an embedded orbit arc, INCLUDING endpoints.
An interior self-return would produce an earlier meeting of the segment. -/
lemma successive_arc_injective (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    {S : StraightSegment} {a b : ℝ} (hab : Successive F S x a b)
    (hne : flow F a x ≠ flow F b x) :
    Set.InjOn (fun t => flow F t x) (Icc a b) := by
  have hI : Icc a b ⊆ (flowInterval F x).carrier :=
    (flowInterval F x).ordConnected.out hab.first_time hab.second_time
  suffices h : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      u < v → flow F u x ≠ flow F v x by
    intro u hu v hv he
    rcases lt_trichotomy u v with hlt | heq | hgt
    · exact False.elim (h u hu v hv hlt he)
    · exact heq
    · exact False.elim (h v hv u hu hgt he.symm)
  intro u hu v hv huv he
  have hp := (Ch11.Orbits.self_intersection F hF x hx u (hI hu) v (hI hv)
    (ne_of_lt huv) he).2
  change ∀ r, flow F (r+(v-u)) x = flow F r x at hp
  have hlen : v-u < b-a := by
    by_contra hn
    have hua : u = a := by linarith [hu.1, hv.2]
    have hvb : v = b := by linarith [hu.1, hv.2]
    exact hne (by simpa [hua, hvb] using he)
  exact hab.no_hit (a+(v-u)) ⟨by linarith, by linarith⟩
    (by simpa only [hp a] using hab.first_hit)

/-- The scalar normal coordinate differentiates to the normal field component. -/
lemma signedHeight_hasDerivAt (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : StraightSegment) {t : ℝ} (ht : t ∈ (flowInterval F x).carrier) :
    HasDerivAt (fun r => signedHeight S (flow F r x))
      (normalComponent F S (flow F t x)) t := by
  let L : Plane →L[ℝ] ℝ := S.direction.1 • ContinuousLinearMap.snd ℝ ℝ ℝ -
    S.direction.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hd := ((L.hasFDerivAt).comp_hasDerivAt t ((flow_ivp F hF hx).1.2.2 t ht)).sub_const
    (L S.center)
  have he : (fun r => signedHeight S (flow F r x)) =
      (fun r => L (flow F r x) - L S.center) := by
    funext r
    simp [L, signedHeight, signedHeightValue, mul_sub]
    ring
  rw [he]
  exact hd

theorem local_crossing : LocalCrossing := by
  intro F hF x hx S t ht hh
  let N := normalComponent F S.toStraightSegment (flow F t x)
  have hN : N ≠ 0 := S.transverse.2 _ hh
  have hz : signedHeight S.toStraightSegment (flow F t x) = 0 :=
    signedHeight_eq_zero_of_mem hh
  have hd := signedHeight_hasDerivAt F hF hx S.toStraightSegment ht
  have hlim : Tendsto (fun r => N *
      (signedHeight S.toStraightSegment (flow F r x) / (r-t))) (𝓝[≠] t) (𝓝 (N*N)) := by
    simpa only [slope_def_field, hz, sub_zero] using
      (tendsto_const_nhds.mul hd.tendsto_slope)
  have he := hlim.eventually (Ioi_mem_nhds (mul_self_pos.mpr hN))
  have htime' : ∀ᶠ r in 𝓝 t, r ∈ (flowInterval F x).carrier :=
    (flowInterval F x).isOpen.mem_nhds ht
  have htime : ∀ᶠ r in 𝓝[≠] t, r ∈ (flowInterval F x).carrier :=
    htime'.filter_mono nhdsWithin_le_nhds
  filter_upwards [he, htime] with r hr hrt
  refine ⟨hrt, hr, ?_⟩
  intro hmem
  have hzero := signedHeight_eq_zero_of_mem hmem
  change 0 < N * (signedHeight S.toStraightSegment (flow F r x) / (r-t)) at hr
  rw [hzero, zero_div, mul_zero] at hr
  exact (lt_irrefl 0) hr

/-- The same normal orientation holds along the ENTIRE transverse segment. -/
lemma normal_sign_on_segment (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (S : TransverseSegment F) :
    (∀ p ∈ S.toStraightSegment.carrier, 0 < normalComponent F S.toStraightSegment p) ∨
    (∀ p ∈ S.toStraightSegment.carrier, normalComponent F S.toStraightSegment p < 0) := by
  have hpoint : Continuous S.toStraightSegment.point :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : IsPreconnected S.toStraightSegment.carrier :=
    isPreconnected_Icc.image _ hpoint.continuousOn
  have hfc : ContinuousOn F.eval S.toStraightSegment.carrier :=
    hF.continuousOn.mono S.transverse.1
  have hnc : ContinuousOn (normalComponent F S.toStraightSegment) S.toStraightSegment.carrier :=
    (continuousOn_const.mul hfc.snd).sub (continuousOn_const.mul hfc.fst)
  have hc : S.center ∈ S.toStraightSegment.carrier := by
    refine ⟨0, ⟨by linarith [S.radius_pos], S.radius_pos.le⟩, ?_⟩
    simp [segmentPointValue]
  have hn := S.transverse.2 S.center hc
  have hno : ∀ p ∈ S.toStraightSegment.carrier,
      normalComponent F S.toStraightSegment p ≠ 0 := S.transverse.2
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · right
    intro p hp
    by_contra h
    obtain ⟨q, hq, he⟩ := hpre.intermediate_value hc hp hnc
      (show (0 : ℝ) ∈ Icc (normalComponent F S.toStraightSegment S.center)
        (normalComponent F S.toStraightSegment p) from ⟨hneg.le, le_of_not_gt h⟩)
    exact hno q hq he
  · left
    intro p hp
    by_contra h
    obtain ⟨q, hq, he⟩ := hpre.intermediate_value hp hc hnc
      (show (0 : ℝ) ∈ Icc (normalComponent F S.toStraightSegment p)
        (normalComponent F S.toStraightSegment S.center) from ⟨le_of_not_gt h, hpos.le⟩)
    exact hno q hq he

/-- The orientation-preserving real-linear identification with the complex
plane used by the canonical winding index. -/
def planeComplex : Plane ≃L[ℝ] ℂ := Complex.equivRealProdCLM.symm

/-- Construct the actual piecewise C¹ orbit-arc/straight-chord closing curve.
The first half traverses the original trajectory with positive speed in time;
the second half goes from its endpoint back to its start. -/
lemma closing_curve_exists (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    {S : StraightSegment} {a b : ℝ} (hab : Successive F S x a b) :
    ∃ γ : D12Complex.PiecewiseC1Path,
      γ.path.a = 0 ∧ γ.path.b = 2 ∧ γ.IsClosed ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        γ s = planeComplex (flow F (a+(b-a)*s) x)) ∧
      (∀ s ∈ Icc (1 : ℝ) 2,
        γ s = planeComplex (flow F b x) +
          (s-1) • (planeComplex (flow F a x) - planeComplex (flow F b x))) := by
  have hI : Icc a b ⊆ (flowInterval F x).carrier :=
    (flowInterval F x).ordConnected.out hab.first_time hab.second_time
  let e := planeComplex
  have hc : ContDiffOn ℝ 1 (fun t => e (flow F t x)) (Icc a b) :=
    e.contDiff.comp_contDiffOn ((flow_ivp F hF hx).1.1.mono hI)
  let P : D12Complex.ComplexPath :=
    ⟨a, b, hab.lt.le, fun t => e (flow F t x), hc.continuousOn⟩
  let α : D12Complex.PiecewiseC1Path := ⟨P, ⟨D12Complex.C1Partition.single P hc⟩⟩
  let q := e (flow F b x)
  let p := e (flow F a x)
  have hlin : ContDiff ℝ 1 (fun t : ℝ => q + t • (p-q)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  let Q : D12Complex.ComplexPath :=
    ⟨0, 1, by norm_num, fun t => q + t • (p-q), hlin.continuous.continuousOn⟩
  let β : D12Complex.PiecewiseC1Path :=
    ⟨Q, ⟨D12Complex.C1Partition.single Q hlin.contDiffOn⟩⟩
  have hjoin : α.path.target = β.path.source := by
    change q = q + (0 : ℝ) • (p-q)
    simp
  obtain ⟨γ, hga, hgb, hα, hβ⟩ := D12Complex.PiecewiseC1Path.exists_concatenation α β hjoin
  have hf (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      γ s = planeComplex (flow F (a+(b-a)*s) x) := hα hs
  have hl (s : ℝ) (hs : s ∈ Icc (1 : ℝ) 2) :
      γ s = q + (s-1) • (p-q) := by
    simpa only [β, Q, D12Complex.PiecewiseC1Path.path, zero_add, sub_zero,
      one_mul] using hβ hs
  refine ⟨γ, hga, hgb, ?_, hf, hl⟩
  change γ γ.path.b = γ γ.path.a
  rw [hga, hgb, hl 2 (by norm_num), hf 0 (by norm_num)]
  simp [p, q, e]
  ring

/-- The closing curve has no points on the transverse segment apart from
its closing chord and the two orbit endpoints. This is an actual traversal
statement, rather than identification of paths with their image sets. -/
lemma closing_curve_no_segment_on_open_orbit (F : AutonomousODE Plane)
    {x : Plane} {S : StraightSegment} {a b : ℝ} (hab : Successive F S x a b)
    {γ : D12Complex.PiecewiseC1Path}
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1,
      γ s = planeComplex (flow F (a+(b-a)*s) x)) :
    ∀ s ∈ Ioo (0 : ℝ) 1, γ s ∉ planeComplex '' S.carrier := by
  intro s hs hmem
  obtain ⟨p, hp, he⟩ := hmem
  rw [hγ s ⟨hs.1.le, hs.2.le⟩] at he
  have hp' : p = flow F (a+(b-a)*s) x := planeComplex.injective he
  apply hab.no_hit (a+(b-a)*s) _ (hp' ▸ hp)
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hab.lt) hs.1]
  · nlinarith [mul_pos (sub_pos.mpr hab.lt) (sub_pos.mpr hs.2)]

/-- Straight segments are convex in the actual affine parametrization. -/
lemma segment_carrier_convex (S : StraightSegment) : Convex ℝ S.carrier := by
  have he : segmentPointValue S =
      AffineMap.lineMap S.center (S.center + S.direction) := by
    funext r
    simp [segmentPointValue, AffineMap.lineMap_apply_module', add_comm]
  change Convex ℝ (segmentPointValue S '' Icc (-S.radius) S.radius)
  rw [he]
  exact (convex_Icc (-S.radius) S.radius : Convex ℝ (Icc (-S.radius) S.radius)).affine_image _

/-- Until the next meeting, uniqueness excludes the entire old orbit arc.
This also handles periodic trajectories: no global injectivity is assumed. -/
lemma future_avoids_old_arc (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    {S : StraightSegment} {a b c : ℝ} (hab : Successive F S x a b)
    (hbc : Successive F S x b c) (hne : flow F a x ≠ flow F b x) :
    ∀ r ∈ Ioo b c, flow F r x ∉ (fun u => flow F u x) '' Icc a b := by
  intro r hr hmem
  obtain ⟨u, hu, he⟩ := hmem
  have hI : Icc a c ⊆ (flowInterval F x).carrier :=
    (flowInterval F x).ordConnected.out hab.first_time hbc.second_time
  have hp := (Ch11.Orbits.self_intersection F hF x hx u
    (hI ⟨hu.1, hu.2.trans hbc.lt.le⟩) r
    (hI ⟨hab.lt.le.trans hr.1.le, hr.2.le⟩) (by intro heq; linarith [hu.2, hr.1] : u ≠ r) he).2
  change ∀ v, flow F (v+(r-u)) x = flow F v x at hp
  have hhit : flow F (a+(r-u)) x ∈ S.carrier := by
    rw [hp a]
    exact hab.first_hit
  rcases lt_trichotomy (a+(r-u)) b with hlt | heq | hgt
  · exact hab.no_hit _ ⟨by linarith [hu.2, hr.1], hlt⟩ hhit
  · apply hne
    have h := hp a
    rw [heq] at h
    exact h.symm
  · exact hbc.no_hit _ ⟨hgt, by linarith [hu.1, hr.2]⟩ hhit

/-- A trace bound for any closing curve with the displayed two traversals. -/
lemma closing_curve_trace_subset (F : AutonomousODE Plane)
    {x : Plane} {S : StraightSegment} {a b : ℝ} (hab : Successive F S x a b)
    {γ : D12Complex.PiecewiseC1Path} (ha : γ.path.a = 0) (hb : γ.path.b = 2)
    (hfirst : ∀ s ∈ Icc (0 : ℝ) 1,
      γ s = planeComplex (flow F (a+(b-a)*s) x))
    (hlast : ∀ s ∈ Icc (1 : ℝ) 2,
      γ s = planeComplex (flow F b x) +
        (s-1) • (planeComplex (flow F a x) - planeComplex (flow F b x))) :
    γ.trace ⊆ planeComplex '' ((fun u => flow F u x) '' Icc a b ∪ S.carrier) := by
  rintro z ⟨s, hs, rfl⟩
  rw [ha, hb] at hs
  by_cases h : s ≤ 1
  · rw [hfirst s ⟨hs.1, h⟩]
    refine ⟨flow F (a+(b-a)*s) x, Or.inl ⟨a+(b-a)*s, ?_, rfl⟩, rfl⟩
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab.lt.le) hs.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab.lt.le) (sub_nonneg.mpr h)]
  · rw [hlast s ⟨le_of_not_ge h, hs.2⟩]
    refine ⟨flow F b x + (s-1) • (flow F a x - flow F b x), Or.inr ?_, ?_⟩
    · exact (segment_carrier_convex S).add_smul_sub_mem hab.second_hit hab.first_hit
        ⟨by linarith, by linarith [hs.2]⟩
    · simp only [map_add, map_smul, map_sub]

/-- No part of the future open excursion meets the old closed curve. -/
lemma future_avoids_closing_curve (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    {S : StraightSegment} {a b c : ℝ} (hab : Successive F S x a b)
    (hbc : Successive F S x b c) (hne : flow F a x ≠ flow F b x)
    {γ : D12Complex.PiecewiseC1Path}
    (htrace : γ.trace ⊆ planeComplex '' ((fun u => flow F u x) '' Icc a b ∪ S.carrier)) :
    ∀ r ∈ Ioo b c, planeComplex (flow F r x) ∉ γ.trace := by
  intro r hr hz
  obtain ⟨p, hp, he⟩ := htrace hz
  have he' : p = flow F r x := planeComplex.injective he
  rw [he'] at hp
  rcases hp with hp | hp
  · exact future_avoids_old_arc F hF hx hab hbc hne r hr hp
  · exact hbc.no_hit r hr hp

/-- The index along that whole future open excursion is constant. No Jordan
separation or classification of connected components is used. -/
lemma future_index_constant (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    {b c : ℝ} (hb : b ∈ (flowInterval F x).carrier)
    (hc : c ∈ (flowInterval F x).carrier) {γ : D12Complex.PiecewiseC1Path}
    (hclosed : γ.IsClosed)
    (havoid : ∀ r ∈ Ioo b c, planeComplex (flow F r x) ∉ γ.trace)
    {r s : ℝ} (hr : r ∈ Ioo b c) (hs : s ∈ Ioo b c) :
    Ch13.IndexJump.integerIndex γ (planeComplex (flow F r x)) =
      Ch13.IndexJump.integerIndex γ (planeComplex (flow F s x)) := by
  have hI : Ioo b c ⊆ (flowInterval F x).carrier := fun _ ht =>
    (flowInterval F x).ordConnected.out hb hc ⟨ht.1.le, ht.2.le⟩
  have hcont : ContinuousOn (fun t => planeComplex (flow F t x)) (Ioo b c) :=
    planeComplex.continuous.comp_continuousOn ((flow_ivp F hF hx).1.1.continuousOn.mono hI)
  apply Int.cast_injective (α := ℂ)
  rw [Ch13.IndexJump.integerIndex_cast γ hclosed _ (havoid r hr),
    Ch13.IndexJump.integerIndex_cast γ hclosed _ (havoid s hs)]
  exact Ch13.IndexJump.index_constant_on γ hclosed
    (isPreconnected_Ioo.image _ hcont) (by rintro _ ⟨t, ht, rfl⟩; exact havoid t ht)
    (mem_image_of_mem _ hr) (mem_image_of_mem _ hs)

lemma signedHeight_continuous (S : StraightSegment) : Continuous (signedHeight S) :=
  (continuous_const.mul (continuous_snd.sub continuous_const)).sub
    (continuous_const.mul (continuous_fst.sub continuous_const))

lemma signedHeight_affine (S : StraightSegment) (p q : Plane) (a b : ℝ)
    (hab : a+b=1) :
    signedHeight S (a • p + b • q) = a*signedHeight S p + b*signedHeight S q := by
  change S.direction.1 * (a*p.2+b*q.2-S.center.2) -
    S.direction.2 * (a*p.1+b*q.1-S.center.1) =
    a*(S.direction.1*(p.2-S.center.2)-S.direction.2*(p.1-S.center.1))+
    b*(S.direction.1*(q.2-S.center.2)-S.direction.2*(q.1-S.center.1))
  nlinarith [congrArg (fun t : ℝ => t*S.direction.1*S.center.2) hab,
    congrArg (fun t : ℝ => t*S.direction.2*S.center.1) hab]

lemma signedHeight_positive_isOpen (S : StraightSegment) (σ : ℝ) :
    IsOpen {y | 0 < σ*signedHeight S y} :=
  isOpen_lt continuous_const (continuous_const.mul (signedHeight_continuous S))

lemma signedHeight_positive_convex (S : StraightSegment) (σ : ℝ) :
    Convex ℝ {y | 0 < σ*signedHeight S y} := by
  intro p hp q hq a b ha hb hab
  change 0 < σ*signedHeight S (a • p+b • q)
  rw [signedHeight_affine S p q a b hab]
  have he : σ*(a*signedHeight S p+b*signedHeight S q) =
      a*(σ*signedHeight S p)+b*(σ*signedHeight S q) := by ring
  rw [he]
  rcases lt_or_eq_of_le ha with ha | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hp) (mul_nonneg hb hq.le)
  · have : b=1 := by linarith
    simpa [this] using hq

lemma signedHeight_neg_isOpen (S : StraightSegment) (σ : ℝ) :
    IsOpen {y | σ*signedHeight S y < 0} := by
  simpa only [neg_mul, neg_pos] using signedHeight_positive_isOpen S (-σ)

lemma signedHeight_neg_convex (S : StraightSegment) (σ : ℝ) :
    Convex ℝ {y | σ*signedHeight S y < 0} := by
  simpa only [neg_mul, neg_pos] using signedHeight_positive_convex S (-σ)

lemma HasDerivAt.eventually_positive_right {f : ℝ → ℝ} {d t σ : ℝ}
    (hf : HasDerivAt f d t) (hz : f t = 0) (hσ : 0 < σ * d) :
    ∀ᶠ r in 𝓝[>] t, 0 < σ * f r := by
  have hlim : Tendsto (fun r => σ * (f r / (r-t))) (𝓝[≠] t) (𝓝 (σ*d)) := by
    simpa only [slope_def_field, hz, sub_zero] using
      (tendsto_const_nhds.mul hf.tendsto_slope)
  have he : ∀ᶠ r in 𝓝[>] t, 0 < σ * (f r / (r-t)) :=
    (hlim.eventually (Ioi_mem_nhds hσ)).filter_mono
      (nhdsWithin_mono _ (fun _ hr => ne_of_gt hr))
  have hgt : ∀ᶠ r in 𝓝[>] t, t < r := self_mem_nhdsWithin
  filter_upwards [he, hgt] with r hr hrt
  have h := mul_pos hr (sub_pos.mpr hrt)
  simpa only [mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hrt.ne')] using h

lemma HasDerivAt.eventually_negative_left {f : ℝ → ℝ} {d t σ : ℝ}
    (hf : HasDerivAt f d t) (hz : f t = 0) (hσ : 0 < σ * d) :
    ∀ᶠ r in 𝓝[<] t, σ * f r < 0 := by
  have hlim : Tendsto (fun r => σ * (f r / (r-t))) (𝓝[≠] t) (𝓝 (σ*d)) := by
    simpa only [slope_def_field, hz, sub_zero] using
      (tendsto_const_nhds.mul hf.tendsto_slope)
  have he : ∀ᶠ r in 𝓝[<] t, 0 < σ * (f r / (r-t)) :=
    (hlim.eventually (Ioi_mem_nhds hσ)).filter_mono
      (nhdsWithin_mono _ (fun _ hr => ne_of_lt hr))
  have hlt : ∀ᶠ r in 𝓝[<] t, r < t := self_mem_nhdsWithin
  filter_upwards [he, hlt] with r hr hrt
  have h := mul_neg_of_pos_of_neg hr (sub_neg.mpr hrt)
  simpa only [mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hrt.ne)] using h

lemma choose_after_crossing (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {b c : ℝ}
    (hb : b ∈ (flowInterval F x).carrier)
    (hh : flow F b x ∈ S.toStraightSegment.carrier)
    (hbc : b < c) (σ : ℝ)
    (hσ : 0 < σ * normalComponent F S.toStraightSegment (flow F b x))
    (V : Set Plane) (hV : V ∈ 𝓝 (flow F b x)) :
    ∃ r ∈ Ioo b c, r ∈ (flowInterval F x).carrier ∧
      flow F r x ∈ V ∧ 0 < σ * signedHeight S.toStraightSegment (flow F r x) := by
  have hcross : ∀ᶠ r in 𝓝[>] b,
      r ∈ (flowInterval F x).carrier ∧
      0 < normalComponent F S.toStraightSegment (flow F b x) *
        (signedHeight S.toStraightSegment (flow F r x) / (r-b)) ∧
      flow F r x ∉ S.toStraightSegment.carrier :=
    (local_crossing F hF x hx S b hb hh).filter_mono
      (nhdsWithin_mono _ (fun _ hr => ne_of_gt hr))
  have hnear : ∀ᶠ r in 𝓝[>] b, flow F r x ∈ V :=
    (((flow_ivp F hF hx).1.2.2 b hb).continuousAt.eventually hV).filter_mono
      nhdsWithin_le_nhds
  have hlt' : ∀ᶠ r in 𝓝 b, r < c := Iio_mem_nhds hbc
  have hlt : ∀ᶠ r in 𝓝[>] b, r < c :=
    hlt'.filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ r in 𝓝[>] b, b < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hV', hrb, hrc⟩ := (hcross.and (hnear.and (hgt.and hlt))).exists
  refine ⟨r, ⟨hrb, hrc⟩, hr.1, hV', ?_⟩
  have hratio : 0 < σ * (signedHeight S.toStraightSegment (flow F r x) / (r-b)) := by
    rcases mul_pos_iff.mp hσ with h | h
    · exact mul_pos h.1 ((mul_pos_iff.mp hr.2.1).resolve_right
        (fun hn => (not_lt_of_ge h.2.le) hn.1)).2
    · exact mul_pos_of_neg_of_neg h.1 ((mul_pos_iff.mp hr.2.1).resolve_left
        (fun hn => (not_lt_of_ge hn.1.le) h.2)).2
  have h := mul_pos hratio (sub_pos.mpr hrb)
  simpa only [mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hrb.ne')] using h

lemma choose_before_crossing (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {b c : ℝ}
    (hc : c ∈ (flowInterval F x).carrier)
    (hh : flow F c x ∈ S.toStraightSegment.carrier)
    (hbc : b < c) (σ : ℝ)
    (hσ : 0 < σ * normalComponent F S.toStraightSegment (flow F c x))
    (V : Set Plane) (hV : V ∈ 𝓝 (flow F c x)) :
    ∃ r ∈ Ioo b c, r ∈ (flowInterval F x).carrier ∧
      flow F r x ∈ V ∧ σ * signedHeight S.toStraightSegment (flow F r x) < 0 := by
  have hcross : ∀ᶠ r in 𝓝[<] c,
      r ∈ (flowInterval F x).carrier ∧
      0 < normalComponent F S.toStraightSegment (flow F c x) *
        (signedHeight S.toStraightSegment (flow F r x) / (r-c)) ∧
      flow F r x ∉ S.toStraightSegment.carrier :=
    (local_crossing F hF x hx S c hc hh).filter_mono
      (nhdsWithin_mono _ (fun _ hr => ne_of_lt hr))
  have hnear : ∀ᶠ r in 𝓝[<] c, flow F r x ∈ V :=
    (((flow_ivp F hF hx).1.2.2 c hc).continuousAt.eventually hV).filter_mono
      nhdsWithin_le_nhds
  have hgt' : ∀ᶠ r in 𝓝 c, b < r := Ioi_mem_nhds hbc
  have hgt : ∀ᶠ r in 𝓝[<] c, b < r :=
    hgt'.filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r in 𝓝[<] c, r < c := self_mem_nhdsWithin
  obtain ⟨r, hr, hV', hrb, hrc⟩ := (hcross.and (hnear.and (hgt.and hlt))).exists
  refine ⟨r, ⟨hrb, hrc⟩, hr.1, hV', ?_⟩
  have hratio : 0 < σ * (signedHeight S.toStraightSegment (flow F r x) / (r-c)) := by
    rcases mul_pos_iff.mp hσ with h | h
    · exact mul_pos h.1 ((mul_pos_iff.mp hr.2.1).resolve_right
        (fun hn => (not_lt_of_ge h.2.le) hn.1)).2
    · exact mul_pos_of_neg_of_neg h.1 ((mul_pos_iff.mp hr.2.1).resolve_left
        (fun hn => (not_lt_of_ge hn.1.le) h.2)).2
  have h := mul_neg_of_pos_of_neg hratio (sub_neg.mpr hrc)
  simpa only [mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr hrc.ne)] using h


open Ch13.Nullclines Ch06.StateDerivative

lemma index_labels_incompatible (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {b c : ℝ}
    (hb : b ∈ (flowInterval F x).carrier)
    (hc : c ∈ (flowInterval F x).carrier)
    (hhb : flow F b x ∈ S.toStraightSegment.carrier)
    (hhc : flow F c x ∈ S.toStraightSegment.carrier)
    (hbc : b < c) (σ : ℝ)
    (hσb : 0 < σ * normalComponent F S.toStraightSegment (flow F b x))
    (hσc : 0 < σ * normalComponent F S.toStraightSegment (flow F c x))
    (γ : D12Complex.PiecewiseC1Path) (hγ : γ.IsClosed)
    (havoid : ∀ r ∈ Ioo b c, planeComplex (flow F r x) ∉ γ.trace)
    (Vb Vc : Set Plane)
    (hVb : Vb ∈ 𝓝 (flow F b x)) (hVc : Vc ∈ 𝓝 (flow F c x))
    (k κ : ℤ) (hκ : κ ≠ 0)
    (hlabelb : ∀ y ∈ Vb, 0 < σ * signedHeight S.toStraightSegment y →
      Ch13.IndexJump.integerIndex γ (planeComplex y) = k)
    (hlabelc : ∀ y ∈ Vc, σ * signedHeight S.toStraightSegment y < 0 →
      Ch13.IndexJump.integerIndex γ (planeComplex y) = k + κ) : False := by
  obtain ⟨r, hr, _, hrV, hrs⟩ :=
    choose_after_crossing F hF hx S hb hhb hbc σ hσb Vb hVb
  obtain ⟨s, hs, _, hsV, hss⟩ :=
    choose_before_crossing F hF hx S hc hhc hbc σ hσc Vc hVc
  have hi := future_index_constant F hF hx hb hc hγ havoid hr hs
  rw [hlabelb _ hrV hrs, hlabelc _ hsV hss] at hi
  apply hκ
  linarith

lemma exists_convex_open_avoiding_corridor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K A R V : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hR : IsClosed R) (hKR : Disjoint K R) (hAV : Disjoint A V)
    (hVo : IsOpen V) (hVv : Convex ℝ V) :
    ∃ ε : ℝ, 0 < ε ∧
      IsOpen (Metric.thickening ε K ∩ V) ∧
      Convex ℝ (Metric.thickening ε K ∩ V) ∧
      Disjoint (Metric.thickening ε K ∩ V) (A ∪ R) ∧
      ∀ p ∈ K, ∀ᶠ z in 𝓝 p, z ∈ V → z ∈ Metric.thickening ε K ∩ V := by
  obtain ⟨ε, hε, hsep⟩ := hKR.exists_thickenings hKc hR
  refine ⟨ε, hε, Metric.isOpen_thickening.inter hVo,
    (hKv.thickening ε).inter hVv, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro z hz hzAR
    rcases hzAR with hzA | hzR
    · exact (Set.disjoint_left.mp hAV) hzA hz.2
    · exact (Set.disjoint_left.mp hsep) hz.1 (Metric.self_subset_thickening hε R hzR)
  · intro p hp
    filter_upwards [Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hε K hp)]
      with z hz
    exact fun hzV => ⟨hz, hzV⟩

lemma one_sided_tube_index_constant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E → ℂ) (he : Continuous e)
    (γ : D12Complex.PiecewiseC1Path) (hclosed : γ.IsClosed)
    {K A R V : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hR : IsClosed R) (hKR : Disjoint K R) (hAV : Disjoint A V)
    (hVo : IsOpen V) (hVv : Convex ℝ V)
    (htrace : e ⁻¹' γ.trace ⊆ A ∪ R) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.thickening ε K ∩ V, e z ∉ γ.trace) ∧
      (∀ u ∈ Metric.thickening ε K ∩ V,
        ∀ v ∈ Metric.thickening ε K ∩ V,
        D13Unified.Ch13.IndexJump.integerIndex γ (e u) =
          D13Unified.Ch13.IndexJump.integerIndex γ (e v)) ∧
      ∀ p ∈ K, ∀ᶠ z in 𝓝 p, z ∈ V → z ∈ Metric.thickening ε K ∩ V := by
  obtain ⟨ε, hε, _, hconv, hdisj, hnear⟩ :=
    exists_convex_open_avoiding_corridor hKc hKv hR hKR hAV hVo hVv
  have havoid : ∀ z ∈ Metric.thickening ε K ∩ V, e z ∉ γ.trace := by
    intro z hz htracez
    exact (Set.disjoint_left.mp hdisj) hz (htrace htracez)
  refine ⟨ε, hε, havoid, ?_, hnear⟩
  intro u hu v hv
  apply Int.cast_injective (α := ℂ)
  rw [D13Unified.Ch13.IndexJump.integerIndex_cast γ hclosed _ (havoid u hu),
    D13Unified.Ch13.IndexJump.integerIndex_cast γ hclosed _ (havoid v hv)]
  exact D13Unified.Ch13.IndexJump.index_constant_on γ hclosed
    (hconv.isPreconnected.image e he.continuousOn)
    (by rintro z ⟨p, hp, rfl⟩; exact havoid p hp)
    (mem_image_of_mem e hu) (mem_image_of_mem e hv)

lemma one_sided_tube_index_constant_of_trace_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E → ℂ) (he : Continuous e)
    (γ : D12Complex.PiecewiseC1Path) (hclosed : γ.IsClosed)
    {K R V : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hR : IsClosed R) (hKR : Disjoint K R)
    (hVo : IsOpen V) (hVv : Convex ℝ V)
    (htrace : (e ⁻¹' γ.trace) ∩ V ⊆ R) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.thickening ε K ∩ V, e z ∉ γ.trace) ∧
      (∀ u ∈ Metric.thickening ε K ∩ V,
        ∀ v ∈ Metric.thickening ε K ∩ V,
        D13Unified.Ch13.IndexJump.integerIndex γ (e u) =
          D13Unified.Ch13.IndexJump.integerIndex γ (e v)) ∧
      ∀ p ∈ K, ∀ᶠ z in 𝓝 p, z ∈ V → z ∈ Metric.thickening ε K ∩ V := by
  apply one_sided_tube_index_constant e he γ hclosed hKc hKv hR hKR
    (A := Vᶜ) disjoint_compl_left hVo hVv
  intro z hz
  by_cases hzV : z ∈ V
  · exact Or.inr (htrace ⟨hz, hzV⟩)
  · exact Or.inl hzV

lemma positive_trace_compact_away_from_start (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {a b : ℝ}
    (hab : Successive F S.toStraightSegment x a b)
    (σ : ℝ) (hσ : 0 < σ * normalComponent F S.toStraightSegment (flow F b x))
    {K : Set Plane} (hKS : K ⊆ S.toStraightSegment.carrier)
    (haK : flow F a x ∉ K)
    {γ : D12Complex.PiecewiseC1Path}
    (htrace : γ.trace ⊆ planeComplex ''
      ((fun t => flow F t x) '' Icc a b ∪ S.toStraightSegment.carrier)) :
    ∃ R : Set Plane, IsCompact R ∧ Disjoint K R ∧
      (planeComplex ⁻¹' γ.trace) ∩
        {y | 0 < σ * signedHeight S.toStraightSegment y} ⊆ R := by
  have hneg := HasDerivAt.eventually_negative_left
    (signedHeight_hasDerivAt F hF hx S.toStraightSegment hab.second_time)
    (signedHeight_eq_zero_of_mem hab.second_hit) hσ
  obtain ⟨d, hd, hsign⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hab.lt).mp hneg
  obtain ⟨e, hde, heb⟩ := exists_between hd.2
  have hae : a < e := hd.1.trans_lt hde
  let R : Set Plane := (fun t => flow F t x) '' Icc a e
  have hI : Icc a b ⊆ (flowInterval F x).carrier :=
    (flowInterval F x).ordConnected.out hab.first_time hab.second_time
  have hR : IsCompact R := isCompact_Icc.image_of_continuousOn
    ((flow_ivp F hF hx).1.1.continuousOn.mono
      ((Icc_subset_Icc le_rfl heb.le).trans hI))
  refine ⟨R, hR, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro y hy ⟨t, ht, rfl⟩
    by_cases hta : t = a
    · exact haK (hta ▸ hy)
    · exact hab.no_hit t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2.trans_lt heb⟩ (hKS hy)
  · rintro y ⟨hytrace, hypos⟩
    change 0 < σ * signedHeight S.toStraightSegment y at hypos
    obtain ⟨z, hz, heq⟩ := htrace hytrace
    have hzy : z = y := planeComplex.injective heq
    rw [hzy] at hz
    rcases hz with ⟨t, ht, rfl⟩ | hyS
    · by_cases hte : t ≤ e
      · exact ⟨t, ⟨ht.1, hte⟩, rfl⟩
      · by_cases htb : t = b
        · exact False.elim (by simpa only [htb, signedHeight_eq_zero_of_mem hab.second_hit,
            mul_zero, lt_self_iff_false] using hypos)
        · have hn := hsign ⟨hde.trans (lt_of_not_ge hte),
            lt_of_le_of_ne ht.2 htb⟩
          change σ * signedHeight S.toStraightSegment (flow F t x) < 0 at hn
          exact False.elim ((not_lt_of_gt hypos) hn)
    · exact False.elim (by simpa only [signedHeight_eq_zero_of_mem hyS,
        mul_zero, lt_self_iff_false] using hypos)


lemma negative_trace_compact_away_from_end (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {a b : ℝ}
    (hab : Successive F S.toStraightSegment x a b)
    (σ : ℝ) (hσ : 0 < σ * normalComponent F S.toStraightSegment (flow F a x))
    {K : Set Plane} (hKS : K ⊆ S.toStraightSegment.carrier)
    (hbK : flow F b x ∉ K)
    {γ : D12Complex.PiecewiseC1Path}
    (htrace : γ.trace ⊆ planeComplex ''
      ((fun t => flow F t x) '' Icc a b ∪ S.toStraightSegment.carrier)) :
    ∃ R : Set Plane, IsCompact R ∧ Disjoint K R ∧
      (planeComplex ⁻¹' γ.trace) ∩
        {y | σ * signedHeight S.toStraightSegment y < 0} ⊆ R := by
  have hpos := HasDerivAt.eventually_positive_right
    (signedHeight_hasDerivAt F hF hx S.toStraightSegment hab.first_time)
    (signedHeight_eq_zero_of_mem hab.first_hit) hσ
  obtain ⟨d, hd, hsign⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab.lt).mp hpos
  obtain ⟨e, hae, hed⟩ := exists_between hd.1
  have heb : e < b := hed.trans_le hd.2
  let R : Set Plane := (fun t => flow F t x) '' Icc e b
  have hI : Icc a b ⊆ (flowInterval F x).carrier :=
    (flowInterval F x).ordConnected.out hab.first_time hab.second_time
  have hR : IsCompact R := isCompact_Icc.image_of_continuousOn
    ((flow_ivp F hF hx).1.1.continuousOn.mono
      ((Icc_subset_Icc hae.le le_rfl).trans hI))
  refine ⟨R, hR, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro y hy ⟨t, ht, rfl⟩
    by_cases htb : t = b
    · exact hbK (htb ▸ hy)
    · exact hab.no_hit t ⟨hae.trans_le ht.1, lt_of_le_of_ne ht.2 htb⟩ (hKS hy)
  · rintro y ⟨hytrace, hyneg⟩
    change σ * signedHeight S.toStraightSegment y < 0 at hyneg
    obtain ⟨z, hz, heq⟩ := htrace hytrace
    have hzy : z = y := planeComplex.injective heq
    rw [hzy] at hz
    rcases hz with ⟨t, ht, rfl⟩ | hyS
    · by_cases het : e ≤ t
      · exact ⟨t, ⟨het, ht.2⟩, rfl⟩
      · by_cases hta : t = a
        · exact False.elim (by simpa only [hta, signedHeight_eq_zero_of_mem hab.first_hit,
            mul_zero, lt_self_iff_false] using hyneg)
        · have hp := hsign ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),
            (lt_of_not_ge het).trans hed⟩
          change 0 < σ * signedHeight S.toStraightSegment (flow F t x) at hp
          exact False.elim ((not_lt_of_gt hp) hyneg)
    · exact False.elim (by simpa only [signedHeight_eq_zero_of_mem hyS,
        mul_zero, lt_self_iff_false] using hyneg)

open D12Complex Ch13.IndexJump

lemma norm_real_mul_unit (z η : ℂ) (hη : ‖η‖ = 1) : ‖z * η‖ = ‖z‖ := by
  rw [norm_mul, hη, mul_one]

def midpoint_straight_arc (γ : PiecewiseC1Path) (c η : ℂ) (l r : ℝ)
    (ha : γ.path.a = 0) (hb : γ.path.b = 2)
    (hη : ‖η‖ = 1) (hr : 0 < r) (hrl : r < l)
    (hchord : ∀ u ∈ Icc (1 : ℝ) 2,
      γ u = c + (((2*u-3)*l : ℝ) : ℂ) * η)
    (hfar : ∀ u ∈ Icc (0 : ℝ) 1, r ≤ ‖γ u-c‖) :
    SingleStraightArc γ c r c η := by
  let s : ℝ := 3/2-r/(2*l)
  let f : ℝ := 2*r/(l+r)
  have hl : 0 < l := hr.trans hrl
  have hlr : 0 < l+r := by positivity
  have hs1 : 1 < s := by
    have hdiv : r/(2*l) < 1/2 := (div_lt_iff₀ (by positivity : 0 < 2*l)).2 (by nlinarith)
    dsimp [s]; linarith
  have hs2 : s < 2 := by dsimp [s]; have : 0 < r/(2*l) := div_pos hr (by positivity); linarith
  have hf0 : 0 < f := div_pos (by positivity) hlr
  have hf1 : f < 1 := by dsimp [f]; rw [div_lt_one hlr]; linarith
  have heq (t : ℝ) : (2 * (s+(2-s)*t)-3)*l = -r+(l+r)*t := by
    dsimp [s]; field_simp; ring
  have hcoordf : -r+(l+r)*f = r := by dsimp [f]; field_simp; ring
  have hnorm (u : ℝ) : ‖c + (u : ℂ)*η-c‖ = |u| := by
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, hη, mul_one, Real.norm_eq_abs]
  refine ⟨hr, hη, by simpa using hr, s, ?_, f, hf0, hf1.trans (by norm_num),
    (fun t => -r+(l+r)*t), ?_, ?_, by simpa using neg_neg_of_pos hr,
    by simpa [hcoordf] using hr, ?_, ?_, ?_, ?_⟩
  · rw [ha,hb]; exact ⟨by linarith, hs2.le⟩
  · fun_prop
  · intro a ha b hb hab; dsimp; nlinarith
  · rw [hnorm]; simp [hr.le]
  · rw [hcoordf, hnorm, abs_of_pos hr]
  · intro t ht
    rw [cutTraversal, ite_eq_left (ht.2.trans hf1.le), hb]
    have hu : s+(2-s)*t ∈ Icc (1:ℝ) 2 := by
      constructor
      · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-s) ht.1]
      · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-s) (by linarith [ht.2] : 0 ≤ 1-t)]
    rw [hchord _ hu, heq]
  · intro t ht
    by_cases ht1 : t ≤ 1
    · rw [cutTraversal, ite_eq_left ht1, hb]
      have hu : s+(2-s)*t ∈ Icc (1:ℝ) 2 := by
        constructor
        · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-s) (hf0.le.trans ht.1)]
        · nlinarith [mul_nonneg (by linarith : 0 ≤ 2-s) (by linarith [ht.2] : 0 ≤ 1-t)]
      rw [hchord _ hu, heq, hnorm]
      apply le_trans _ (le_abs_self _)
      nlinarith [ht.1]
    · rw [cutTraversal, ite_eq_right ht1, ha]
      simp only [sub_zero, zero_add]
      have hu0 : 0 ≤ s*(t-1) := mul_nonneg (by linarith) (by linarith)
      have hus : s*(t-1) ≤ s := by nlinarith [mul_nonneg (by linarith : 0 ≤ s) (by linarith [ht.2] : 0 ≤ 2-t)]
      by_cases hu1 : s*(t-1) ≤ 1
      · exact hfar _ ⟨hu0,hu1⟩
      · rw [hchord _ ⟨by linarith, hus.trans hs2.le⟩, hnorm]
        apply le_trans _ (neg_le_abs _)
        have : (2*(s*(t-1))-3)*l ≤ -r := by
          calc
            _ ≤ (2*s-3)*l := by nlinarith
            _ = -r := by simpa using heq 0
        linarith

lemma midpoint_straight_arc_exists (γ : PiecewiseC1Path) (c η : ℂ) (l : ℝ)
    (ha : γ.path.a = 0) (hb : γ.path.b = 2)
    (hη : ‖η‖ = 1) (hl : 0 < l)
    (hchord : ∀ u ∈ Icc (1 : ℝ) 2,
      γ u = c + (((2*u-3)*l : ℝ) : ℂ) * η)
    (hnot : c ∉ γ '' Icc (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ r < l ∧ Nonempty (SingleStraightArc γ c r c η) := by
  let A : Set ℂ := γ '' Icc (0 : ℝ) 1
  have hcont : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    apply γ.path.continuousOn.mono
    rw [ha,hb]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hcomp : IsCompact A := isCompact_Icc.image_of_continuousOn hcont
  have hne : A.Nonempty := ⟨γ 0, ⟨0, by norm_num, rfl⟩⟩
  have hd : 0 < Metric.infDist c A := (hcomp.isClosed.notMem_iff_infDist_pos hne).1 hnot
  let r : ℝ := min l (Metric.infDist c A) / 2
  have hr : 0 < r := half_pos (lt_min hl hd)
  have hrl : r < l := by dsimp [r]; linarith [min_le_left l (Metric.infDist c A)]
  refine ⟨r, hr, hrl, ⟨midpoint_straight_arc γ c η l r ha hb hη hr hrl hchord ?_⟩⟩
  intro u hu
  have hdist : Metric.infDist c A ≤ ‖γ u-c‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using
      (Metric.infDist_le_dist_of_mem (x := c) (show γ u ∈ A from ⟨u, hu, rfl⟩))
  dsimp [r]
  linarith [min_le_right l (Metric.infDist c A)]

lemma midpoint_not_on_closed_arc {α : ℝ → ℂ} {p q : ℂ} {C : Set ℂ}
    (h0 : α 0 = p) (h1 : α 1 = q) (hne : p ≠ q)
    (hmid : (p+q)/2 ∈ C) (havoid : ∀ u ∈ Ioo (0 : ℝ) 1, α u ∉ C) :
    (p+q)/2 ∉ α '' Icc (0 : ℝ) 1 := by
  rintro ⟨u, hu, he⟩
  by_cases hu0 : u = 0
  · rw [hu0, h0] at he
    apply hne
    apply add_left_cancel (a := p)
    calc
      p+p = 2*p := by ring
      _ = 2*((p+q)/2) := congrArg (fun z : ℂ => 2*z) he
      _ = p+q := by ring
  by_cases hu1 : u = 1
  · rw [hu1, h1] at he
    apply hne
    apply add_right_cancel (b := q)
    calc
      p+q = 2*((p+q)/2) := by ring
      _ = 2*q := congrArg (fun z : ℂ => 2*z) he.symm
      _ = q+q := by ring
  exact havoid u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩
    (he.symm ▸ hmid)

lemma chord_midpoint_straight_arc_exists (γ : PiecewiseC1Path) (p q : ℂ)
    (ha : γ.path.a = 0) (hb : γ.path.b = 2) (hne : p ≠ q)
    (hchord : ∀ u ∈ Icc (1 : ℝ) 2, γ u = q + (u-1) • (p-q))
    (hnot : (p+q)/2 ∉ γ '' Icc (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ r < ‖p-q‖/2 ∧
      Nonempty (SingleStraightArc γ ((p+q)/2) r ((p+q)/2) ((p-q)/(‖p-q‖ : ℂ))) := by
  have hN : 0 < ‖p-q‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hNc : (‖p-q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hN)
  apply midpoint_straight_arc_exists γ ((p+q)/2) ((p-q)/(‖p-q‖ : ℂ)) (‖p-q‖/2)
    ha hb _ (half_pos hN) _ hnot
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    exact div_self (ne_of_gt hN)
  · intro u hu
    rw [hchord u hu, Complex.real_smul]
    push_cast
    field_simp
    ring

lemma straight_arc_anchor_jump (γ : PiecewiseC1Path) (hclosed : γ.IsClosed)
    (c η : ℂ) (r : ℝ) (hA : SingleStraightArc γ c r c η)
    {ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    let p := c + (ε : ℂ) * Complex.I * η
    let q := c - (ε : ℂ) * Complex.I * η
    p ∉ γ.trace ∧ q ∉ γ.trace ∧ integerIndex γ p = integerIndex γ q + 1 := by
  have hη : η ≠ 0 := by intro he; simpa [he] using hA.direction_unit
  have hnorm : ‖(ε : ℂ) * Complex.I * η‖ = ε := by
    simp [norm_mul, hA.direction_unit, abs_of_pos hε]
  apply index_jump γ hclosed c r c η hA
  · constructor
    · simpa only [add_sub_cancel_left] using hnorm.trans_lt hεr
    · simp [hη, mul_div_cancel_right₀, hε]
  · constructor
    · simpa only [sub_sub_cancel_left, norm_neg] using hnorm.trans_lt hεr
    · simp only [sub_sub_cancel_left, neg_div, mul_div_cancel_right₀ _ hη,
        Complex.neg_im, Complex.mul_I_im, Complex.ofReal_re]
      exact neg_neg_of_pos hε

namespace StraightEdgeAlgebra

lemma e_re (p : Plane) : (planeComplex p).re = p.1 := rfl
lemma e_im (p : Plane) : (planeComplex p).im = p.2 := rfl
lemma e_symm_fst (z : ℂ) : (planeComplex.symm z).1 = z.re := rfl
lemma e_symm_snd (z : ℂ) : (planeComplex.symm z).2 = z.im := rfl

lemma height_translate_I (S : StraightSegment) (z η : ℂ) (ε : ℝ) :
    signedHeightValue S (planeComplex.symm (z + (ε : ℂ)*Complex.I*η)) =
      signedHeightValue S (planeComplex.symm z) +
        ε * (η.re*S.direction.1+η.im*S.direction.2) := by
  change S.direction.1 * ((z + (ε : ℂ)*Complex.I*η).im - S.center.2) -
    S.direction.2 * ((z + (ε : ℂ)*Complex.I*η).re - S.center.1) = _
  dsimp [signedHeightValue]
  rw [e_symm_fst,e_symm_snd]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma height_midpoint (S : StraightSegment) {p q : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) :
    signedHeightValue S (planeComplex.symm ((planeComplex p+planeComplex q)/2)) = 0 := by
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨v, hv, rfl⟩ := hq
  change S.direction.1 * (((planeComplex (S.point u)+planeComplex (S.point v))/2).im-S.center.2) -
    S.direction.2 * (((planeComplex (S.point u)+planeComplex (S.point v))/2).re-S.center.1) = 0
  simp [planeComplex, StraightSegment.point, segmentPointValue, Complex.div_re,Complex.div_im]
  ring

lemma direction_dot_formula (S : StraightSegment) {p q : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) :
    let η := (planeComplex p-planeComplex q)/(‖planeComplex p-planeComplex q‖ : ℂ)
    η.re*S.direction.1+η.im*S.direction.2 =
      (S.coordinate p-S.coordinate q)*(S.direction.1^2+S.direction.2^2)/‖planeComplex p-planeComplex q‖ := by
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨v, hv, rfl⟩ := hq
  dsimp only
  have hcu : S.coordinate (segmentPointValue S u) = u := coordinate_point S u
  have hcv : S.coordinate (segmentPointValue S v) = v := coordinate_point S v
  rw [hcu,hcv]
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re,Complex.sub_im,
    e_re,e_im]
  change ((S.center.1+u*S.direction.1)-(S.center.1+v*S.direction.1)) / _ * _ +
    ((S.center.2+u*S.direction.2)-(S.center.2+v*S.direction.2)) / _ * _ = _
  ring

lemma coordinate_ne_of_ne (S : StraightSegment) {p q : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) (hne : p ≠ q) :
    S.coordinate p ≠ S.coordinate q := by
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨v, hv, rfl⟩ := hq
  have hcu : S.coordinate (segmentPointValue S u) = u := coordinate_point S u
  have hcv : S.coordinate (segmentPointValue S v) = v := coordinate_point S v
  rw [hcu,hcv]
  intro huv
  exact hne (congrArg S.point huv)

lemma direction_sq_positive (S : StraightSegment) :
    0 < S.direction.1^2+S.direction.2^2 := by
  have hn : S.direction.1 ≠ 0 ∨ S.direction.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact S.direction_ne_zero (Prod.ext h.1 h.2)
  rcases hn with hn | hn <;> nlinarith [sq_pos_of_ne_zero hn]

lemma direction_dot_ne_zero (S : StraightSegment) {p q : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) (hne : p ≠ q) :
    let η := (planeComplex p-planeComplex q)/(‖planeComplex p-planeComplex q‖ : ℂ)
    η.re*S.direction.1+η.im*S.direction.2 ≠ 0 := by
  dsimp only
  rw [direction_dot_formula S hp hq]
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.2 (coordinate_ne_of_ne S hp hq hne))
    (ne_of_gt (direction_sq_positive S)))
    (norm_ne_zero_iff.2 (sub_ne_zero.2 (fun h => hne (planeComplex.injective h))))

lemma complex_chord_direction_unit {p q : Plane} (hne : p ≠ q) :
    ‖(planeComplex p-planeComplex q)/(‖planeComplex p-planeComplex q‖ : ℂ)‖ = 1 := by
  have hN : 0 < ‖planeComplex p-planeComplex q‖ := norm_pos_iff.2
    (sub_ne_zero.2 (fun h => hne (planeComplex.injective h)))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,abs_of_pos hN,
    div_self (ne_of_gt hN)]

lemma direction_dot_pos_iff (S : StraightSegment) {p q : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) (hne : p ≠ q) :
    let η := (planeComplex p-planeComplex q)/(‖planeComplex p-planeComplex q‖ : ℂ)
    0 < η.re*S.direction.1+η.im*S.direction.2 ↔ S.coordinate q < S.coordinate p := by
  dsimp only
  rw [direction_dot_formula S hp hq,
    div_pos_iff_of_pos_right (norm_pos_iff.2 (sub_ne_zero.2 (fun h => hne (planeComplex.injective h)))),
    mul_pos_iff_of_pos_right (direction_sq_positive S),sub_pos]

lemma complex_midpoint_mem_carrier (S : StraightSegment) {p q : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) :
    planeComplex.symm ((planeComplex p+planeComplex q)/2) ∈ S.carrier := by
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨v, hv, rfl⟩ := hq
  refine ⟨(u+v)/2, ⟨by linarith [hu.1,hv.1],by linarith [hu.2,hv.2]⟩, ?_⟩
  apply planeComplex.injective
  simp only [planeComplex.apply_symm_apply]
  apply Complex.ext <;> simp [planeComplex,StraightSegment.point,segmentPointValue] <;> ring

lemma height_anchors (S : StraightSegment) {p q : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) (ε : ℝ) :
    let m := (planeComplex p+planeComplex q)/2
    let η := (planeComplex p-planeComplex q)/(‖planeComplex p-planeComplex q‖ : ℂ)
    let A := η.re*S.direction.1+η.im*S.direction.2
    signedHeightValue S (planeComplex.symm (m+(ε : ℂ)*Complex.I*η)) = ε*A ∧
    signedHeightValue S (planeComplex.symm (m-(ε : ℂ)*Complex.I*η)) = -ε*A := by
  dsimp only
  constructor
  · rw [height_translate_I, height_midpoint S hp hq, zero_add]
  · have hn := height_translate_I S ((planeComplex p+planeComplex q)/2)
        ((planeComplex p-planeComplex q)/(‖planeComplex p-planeComplex q‖ : ℂ)) (-ε)
    rw [height_midpoint S hp hq,zero_add] at hn
    simpa only [Complex.ofReal_neg, mul_neg, neg_mul, sub_eq_add_neg] using hn

end StraightEdgeAlgebra

lemma outgoing_index_corridor (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {a b : ℝ}
    (hab : Successive F S.toStraightSegment x a b)
    (σ : ℝ) (hσ : 0 < σ * normalComponent F S.toStraightSegment (flow F b x))
    {K : Set Plane} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKS : K ⊆ S.toStraightSegment.carrier) (haK : flow F a x ∉ K)
    {γ : D12Complex.PiecewiseC1Path} (hclosed : γ.IsClosed)
    (htrace : γ.trace ⊆ planeComplex ''
      ((fun t => flow F t x) '' Icc a b ∪ S.toStraightSegment.carrier)) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.thickening ε K ∩ {y | 0 < σ * signedHeight S.toStraightSegment y},
        planeComplex z ∉ γ.trace) ∧
      (∀ u ∈ Metric.thickening ε K ∩ {y | 0 < σ * signedHeight S.toStraightSegment y},
        ∀ v ∈ Metric.thickening ε K ∩ {y | 0 < σ * signedHeight S.toStraightSegment y},
        Ch13.IndexJump.integerIndex γ (planeComplex u) =
          Ch13.IndexJump.integerIndex γ (planeComplex v)) ∧
      ∀ p ∈ K, ∀ᶠ z in 𝓝 p, 0 < σ * signedHeight S.toStraightSegment z →
        z ∈ Metric.thickening ε K ∩ {y | 0 < σ * signedHeight S.toStraightSegment y} := by
  obtain ⟨R, hR, hKR, hRt⟩ :=
    positive_trace_compact_away_from_start F hF hx S hab σ hσ hKS haK htrace
  exact one_sided_tube_index_constant_of_trace_subset planeComplex planeComplex.continuous
    γ hclosed hKc hKv hR.isClosed hKR
    (signedHeight_positive_isOpen S.toStraightSegment σ)
    (signedHeight_positive_convex S.toStraightSegment σ) hRt

lemma incoming_index_corridor (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {a b : ℝ}
    (hab : Successive F S.toStraightSegment x a b)
    (σ : ℝ) (hσ : 0 < σ * normalComponent F S.toStraightSegment (flow F a x))
    {K : Set Plane} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKS : K ⊆ S.toStraightSegment.carrier) (hbK : flow F b x ∉ K)
    {γ : D12Complex.PiecewiseC1Path} (hclosed : γ.IsClosed)
    (htrace : γ.trace ⊆ planeComplex ''
      ((fun t => flow F t x) '' Icc a b ∪ S.toStraightSegment.carrier)) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.thickening ε K ∩ {y | σ * signedHeight S.toStraightSegment y < 0},
        planeComplex z ∉ γ.trace) ∧
      (∀ u ∈ Metric.thickening ε K ∩ {y | σ * signedHeight S.toStraightSegment y < 0},
        ∀ v ∈ Metric.thickening ε K ∩ {y | σ * signedHeight S.toStraightSegment y < 0},
        Ch13.IndexJump.integerIndex γ (planeComplex u) =
          Ch13.IndexJump.integerIndex γ (planeComplex v)) ∧
      ∀ p ∈ K, ∀ᶠ z in 𝓝 p, σ * signedHeight S.toStraightSegment z < 0 →
        z ∈ Metric.thickening ε K ∩ {y | σ * signedHeight S.toStraightSegment y < 0} := by
  obtain ⟨R, hR, hKR, hRt⟩ :=
    negative_trace_compact_away_from_end F hF hx S hab σ hσ hKS hbK htrace
  exact one_sided_tube_index_constant_of_trace_subset planeComplex planeComplex.continuous
    γ hclosed hKc hKv hR.isClosed hKR
    (signedHeight_neg_isOpen S.toStraightSegment σ)
    (signedHeight_neg_convex S.toStraightSegment σ) hRt

namespace StraightEdgeAlgebra
open Specs.D13Unified.Ch13.MonotoneCrossings

lemma side_sets_have_distinct_indices (γ : PiecewiseC1Path) (hclosed : γ.IsClosed)
    (S : StraightSegment) (m : Plane) (η : ℂ) (r σ : ℝ)
    (hA : SingleStraightArc γ (planeComplex m) r (planeComplex m) η)
    (hm : signedHeightValue S m = 0)
    (hdot : η.re*S.direction.1+η.im*S.direction.2 ≠ 0) (hσ : σ ≠ 0)
    (Uplus Uminus : Set Plane)
    (hplus : ∀ᶠ y in 𝓝 m, 0 < σ*signedHeightValue S y → y ∈ Uplus)
    (hminus : ∀ᶠ y in 𝓝 m, σ*signedHeightValue S y < 0 → y ∈ Uminus) :
    ∃ yp ∈ Uplus, ∃ yn ∈ Uminus,
      integerIndex γ (planeComplex yp) ≠ integerIndex γ (planeComplex yn) := by
  let a : ℝ → Plane := fun t => planeComplex.symm (planeComplex m+(t:ℂ)*Complex.I*η)
  let b : ℝ → Plane := fun t => planeComplex.symm (planeComplex m-(t:ℂ)*Complex.I*η)
  have hac : Continuous a := by dsimp [a]; fun_prop
  have hbc : Continuous b := by dsimp [b]; fun_prop
  have hat : Tendsto a (𝓝 (0 : ℝ)) (𝓝 m) := by
    simpa [a] using (hac.continuousAt (x := 0)).tendsto
  have hbt : Tendsto b (𝓝 (0 : ℝ)) (𝓝 m) := by
    simpa [b] using (hbc.continuousAt (x := 0)).tendsto
  have haa := hat.eventually (hplus.and hminus)
  have hbb := hbt.eventually (hplus.and hminus)
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (0 < σ*signedHeightValue S (a t) → a t ∈ Uplus) ∧
      (σ*signedHeightValue S (a t) < 0 → a t ∈ Uminus) ∧
      (0 < σ*signedHeightValue S (b t) → b t ∈ Uplus) ∧
      (σ*signedHeightValue S (b t) < 0 → b t ∈ Uminus) := by
    filter_upwards [haa.filter_mono nhdsWithin_le_nhds,
      hbb.filter_mono nhdsWithin_le_nhds] with t ht ht'
    exact ⟨ht.1,ht.2,ht'.1,ht'.2⟩
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hlt' : ∀ᶠ t in 𝓝 (0 : ℝ), t < r := Iio_mem_nhds hA.radius_pos
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r :=
    hlt'.filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hδpos, hδr⟩ := (he.and (hpos.and hlt)).exists
  have hha : signedHeightValue S (a δ) = δ*(η.re*S.direction.1+η.im*S.direction.2) := by
    dsimp [a]
    rw [height_translate_I, planeComplex.symm_apply_apply, hm, zero_add]
  have hhb : signedHeightValue S (b δ) = -δ*(η.re*S.direction.1+η.im*S.direction.2) := by
    have hh := height_translate_I S (planeComplex m) η (-δ)
    rw [planeComplex.symm_apply_apply,hm,zero_add] at hh
    simpa only [b,Complex.ofReal_neg,mul_neg,neg_mul,sub_eq_add_neg] using hh
  have hj := straight_arc_anchor_jump γ hclosed (planeComplex m) η r hA hδpos hδr
  have hab : integerIndex γ (planeComplex (a δ)) ≠ integerIndex γ (planeComplex (b δ)) := by
    intro heq
    have heq' : integerIndex γ (planeComplex m+(δ:ℂ)*Complex.I*η) =
        integerIndex γ (planeComplex m-(δ:ℂ)*Complex.I*η) := by simpa [a,b] using heq
    dsimp only at hj
    linarith [hj.2.2]
  have hne : σ*(η.re*S.direction.1+η.im*S.direction.2) ≠ 0 := mul_ne_zero hσ hdot
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨b δ, hδ.2.2.1 ?_, a δ, hδ.2.1 ?_, Ne.symm hab⟩
    · rw [hhb]
      nlinarith [mul_pos hδpos (neg_pos.2 hneg)]
    · rw [hha]
      nlinarith [mul_neg_of_pos_of_neg hδpos hneg]
  · refine ⟨a δ, hδ.1 ?_, b δ, hδ.2.2.2 ?_, hab⟩
    · rw [hha]
      nlinarith [mul_pos hδpos hpos]
    · rw [hhb]
      nlinarith [mul_neg_of_neg_of_pos (neg_neg_of_pos hδpos) hpos]

end StraightEdgeAlgebra

lemma point_coordinate_of_mem (S : StraightSegment) {p : Plane} (hp : p ∈ S.carrier) :
    S.point (S.coordinate p) = p := by
  obtain ⟨u, hu, rfl⟩ := hp
  change S.point (segmentCoordinateValue S (segmentPointValue S u)) = S.point u
  rw [Ch13.Nullclines.coordinate_point S u]

lemma coordinate_mem_of_mem (S : StraightSegment) {p : Plane} (hp : p ∈ S.carrier) :
    S.coordinate p ∈ Icc (-S.radius) S.radius := by
  obtain ⟨u, hu, rfl⟩ := hp
  change segmentCoordinateValue S (segmentPointValue S u) ∈ Icc (-S.radius) S.radius
  rw [Ch13.Nullclines.coordinate_point S u]
  exact hu

lemma transverse_corridor_bases (S : StraightSegment) {p q w : Plane}
    (hp : p ∈ S.carrier) (hq : q ∈ S.carrier) (hw : w ∈ S.carrier)
    (horder : (S.coordinate p < S.coordinate q ∧ S.coordinate w < S.coordinate q) ∨
      (S.coordinate q < S.coordinate p ∧ S.coordinate q < S.coordinate w)) :
    let m := S.point ((S.coordinate p + S.coordinate q) / 2)
    m = (1 / 2 : ℝ) • (p + q) ∧
    ∃ Kq Kw : Set Plane,
      IsCompact Kq ∧ Convex ℝ Kq ∧ Kq ⊆ S.carrier ∧
      m ∈ Kq ∧ q ∈ Kq ∧ p ∉ Kq ∧
      IsCompact Kw ∧ Convex ℝ Kw ∧ Kw ⊆ S.carrier ∧
      m ∈ Kw ∧ w ∈ Kw ∧ q ∉ Kw := by
  let u := S.coordinate p
  let v := S.coordinate q
  let z := S.coordinate w
  let mid := (u + v) / 2
  let m := S.point mid
  let K := fun a b : ℝ => S.point '' Icc (min a b) (max a b)
  have hu : u ∈ Icc (-S.radius) S.radius := coordinate_mem_of_mem S hp
  have hv : v ∈ Icc (-S.radius) S.radius := coordinate_mem_of_mem S hq
  have hz : z ∈ Icc (-S.radius) S.radius := coordinate_mem_of_mem S hw
  have hm : mid ∈ Icc (-S.radius) S.radius := by
    constructor <;> dsimp [mid] <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hpoint : Continuous S.point :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hKcompact (a b : ℝ) : IsCompact (K a b) :=
    isCompact_Icc.image hpoint
  have hKconvex (a b : ℝ) : Convex ℝ (K a b) := by
    have he : segmentPointValue S =
        AffineMap.lineMap S.center (S.center + S.direction) := by
      funext r
      simp [segmentPointValue, AffineMap.lineMap_apply_module', add_comm]
    change Convex ℝ (segmentPointValue S '' Icc (min a b) (max a b))
    rw [he]
    exact (convex_Icc (min a b) (max a b) :
      Convex ℝ (Icc (min a b) (max a b))).affine_image _
  have hKsubset (a b : ℝ) (ha : a ∈ Icc (-S.radius) S.radius)
      (hb : b ∈ Icc (-S.radius) S.radius) : K a b ⊆ S.carrier := by
    rintro y ⟨r, hr, rfl⟩
    exact ⟨r, ⟨(le_min ha.1 hb.1).trans hr.1,
      hr.2.trans (max_le ha.2 hb.2)⟩, rfl⟩
  have hKleft (a b : ℝ) : S.point a ∈ K a b :=
    ⟨a, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩
  have hKright (a b : ℝ) : S.point b ∈ K a b :=
    ⟨b, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
  have heqp : S.point u = p := point_coordinate_of_mem S hp
  have heqq : S.point v = q := point_coordinate_of_mem S hq
  have heqw : S.point z = w := point_coordinate_of_mem S hw
  have hmidpoint : m = (1 / 2 : ℝ) • (p + q) := by
    rw [← heqp, ← heqq]
    apply Prod.ext <;>
      simp [m, mid, StraightSegment.point, segmentPointValue] <;> ring
  refine ⟨hmidpoint, K mid v, K mid z, hKcompact _ _, hKconvex _ _,
    hKsubset _ _ hm hv, hKleft _ _, ?_, ?_,
    hKcompact _ _, hKconvex _ _, hKsubset _ _ hm hz, hKleft _ _, ?_, ?_⟩
  · rw [← heqq]
    exact hKright _ _
  · rintro ⟨r, hr, he⟩
    have hecoord : r = u := by
      calc r = S.coordinate (S.point r) := (Ch13.Nullclines.coordinate_point S r).symm
           _ = u := congrArg S.coordinate he
    rw [hecoord] at hr
    rcases horder with ⟨huv, hzv⟩ | ⟨hvu, hvz⟩
    · have h : u < min mid v := lt_min (by dsimp [mid, u, v]; linarith) huv
      exact (not_lt_of_ge hr.1) h
    · have h : max mid v < u := max_lt (by dsimp [mid, u, v]; linarith) hvu
      exact (not_lt_of_ge hr.2) h
  · rw [← heqw]
    exact hKright _ _
  · rintro ⟨r, hr, he⟩
    have hecoord : r = v := by
      calc r = S.coordinate (S.point r) := (Ch13.Nullclines.coordinate_point S r).symm
           _ = v := congrArg S.coordinate he
    rw [hecoord] at hr
    rcases horder with ⟨huv, hzv⟩ | ⟨hvu, hvz⟩
    · have h : max mid z < v := max_lt (by dsimp [mid, u, v]; linarith) hzv
      exact (not_lt_of_ge hr.2) h
    · have h : v < min mid z := lt_min (by dsimp [mid, u, v]; linarith) hvz
      exact (not_lt_of_ge hr.1) h


/-- The winding barrier excludes a third meeting on the side of the second
meeting containing the first. The two one-sided tubes carry different indices. -/
lemma successive_wrong_side_impossible (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {x : Plane} (hx : x ∈ F.domain)
    (S : TransverseSegment F) {a b c : ℝ}
    (hab : Successive F S.toStraightSegment x a b)
    (hbc : Successive F S.toStraightSegment x b c)
    (hwrong :
      (S.toStraightSegment.coordinate (flow F a x) < S.toStraightSegment.coordinate (flow F b x) ∧
       S.toStraightSegment.coordinate (flow F c x) < S.toStraightSegment.coordinate (flow F b x)) ∨
      (S.toStraightSegment.coordinate (flow F b x) < S.toStraightSegment.coordinate (flow F a x) ∧
       S.toStraightSegment.coordinate (flow F b x) < S.toStraightSegment.coordinate (flow F c x))) :
    False := by
  have hpq : flow F a x ≠ flow F b x := by
    intro he
    rcases hwrong with hw | hw
    · exact (ne_of_lt hw.1) (congrArg S.toStraightSegment.coordinate he)
    · exact (ne_of_lt hw.1) (congrArg S.toStraightSegment.coordinate he.symm)
  let m := S.toStraightSegment.point
    ((S.toStraightSegment.coordinate (flow F a x) +
      S.toStraightSegment.coordinate (flow F b x))/2)
  obtain ⟨hm, Kq, Kw, hKqc, hKqv, hKqS, hmq, hqq, hpKq,
      hKwc, hKwv, hKwS, hmw, hww, hqKw⟩ :=
    transverse_corridor_bases S.toStraightSegment hab.first_hit hab.second_hit hbc.second_hit hwrong
  have hme : planeComplex m =
      (planeComplex (flow F a x) + planeComplex (flow F b x))/2 := by
    change planeComplex (S.toStraightSegment.point _) = _
    rw [hm, map_smul, map_add, Complex.real_smul]
    push_cast
    ring
  have hmH : signedHeight S.toStraightSegment m = 0 :=
    signedHeight_eq_zero_of_mem (hKqS hmq)
  obtain ⟨σ, hσne, hσ⟩ : ∃ σ : ℝ, σ ≠ 0 ∧
      ∀ y ∈ S.toStraightSegment.carrier, 0 < σ * normalComponent F S.toStraightSegment y := by
    rcases normal_sign_on_segment F hF S with hpos | hneg
    · exact ⟨1, one_ne_zero, by intro y hy; simpa only [one_mul] using hpos y hy⟩
    · refine ⟨-1, by norm_num, ?_⟩
      intro y hy
      simpa only [neg_one_mul] using neg_pos.mpr (hneg y hy)
  obtain ⟨γ, hga, hgb, hclosed, hfirst, hlast⟩ := closing_curve_exists F hF hx hab
  have htrace := closing_curve_trace_subset F hab hga hgb hfirst hlast
  obtain ⟨εq, hεq, hqavoid, hqconst, hqnear⟩ :=
    outgoing_index_corridor F hF hx S hab σ (hσ _ hab.second_hit)
      hKqc hKqv hKqS hpKq hclosed htrace
  obtain ⟨εw, hεw, hwavoid, hwconst, hwnear⟩ :=
    incoming_index_corridor F hF hx S hab σ (hσ _ hab.first_hit)
      hKwc hKwv hKwS hqKw hclosed htrace
  have hzero : γ 0 = planeComplex (flow F a x) := by simpa using hfirst 0 (by norm_num)
  have hone : γ 1 = planeComplex (flow F b x) := by simpa using hfirst 1 (by norm_num)
  have hmidcarrier : (planeComplex (flow F a x)+planeComplex (flow F b x))/2 ∈
      planeComplex '' S.toStraightSegment.carrier := ⟨m, hKqS hmq, hme⟩
  have hnot := midpoint_not_on_closed_arc hzero hone
    (fun h => hpq (planeComplex.injective h)) hmidcarrier
    (closing_curve_no_segment_on_open_orbit F hab hfirst)
  obtain ⟨r, hr, _, ⟨hArc⟩⟩ := chord_midpoint_straight_arc_exists γ
    (planeComplex (flow F a x)) (planeComplex (flow F b x)) hga hgb
    (fun h => hpq (planeComplex.injective h)) hlast hnot
  let η := (planeComplex (flow F a x)-planeComplex (flow F b x)) /
    (‖planeComplex (flow F a x)-planeComplex (flow F b x)‖ : ℂ)
  have hArc' : SingleStraightArc γ (planeComplex m) r (planeComplex m) η := by
    simpa only [hme] using hArc
  have hdot : η.re*S.direction.1+η.im*S.direction.2 ≠ 0 :=
    StraightEdgeAlgebra.direction_dot_ne_zero S.toStraightSegment hab.first_hit hab.second_hit hpq
  obtain ⟨yp, hyp, yn, hyn, hindexne⟩ :=
    StraightEdgeAlgebra.side_sets_have_distinct_indices γ hclosed S.toStraightSegment m η r σ
      hArc' hmH hdot hσne _ _ (hqnear m hmq) (hwnear m hmw)
  obtain ⟨u, hu, _, huV, huH⟩ := choose_after_crossing F hF hx S hab.second_time
    hab.second_hit hbc.lt σ (hσ _ hab.second_hit) _ (hqnear _ hqq)
  have huTube := huV huH
  obtain ⟨v, hv, _, hvV, hvH⟩ := choose_before_crossing F hF hx S hbc.second_time
    hbc.second_hit hbc.lt σ (hσ _ hbc.second_hit) _ (hwnear _ hww)
  have hvTube := hvV hvH
  apply hindexne
  calc
    integerIndex γ (planeComplex yp) = integerIndex γ (planeComplex (flow F u x)) :=
      (hqconst _ huTube _ hyp).symm
    _ = integerIndex γ (planeComplex (flow F v x)) :=
      future_index_constant F hF hx hab.second_time hbc.second_time hclosed
        (future_avoids_closing_curve F hF hx hab hbc hpq htrace) hu hv
    _ = integerIndex γ (planeComplex yn) := hwconst _ hvTube _ hyn

/-- Consecutive distinct meetings keep the same strict direction in the
fixed affine coordinate. Repeated meetings are handled by uniqueness. -/
theorem successive_order : SuccessiveOrder := by
  intro F hF x hx S a b c hab hbc
  let u := fun t => S.toStraightSegment.coordinate (flow F t x)
  change (u a < u b → u b < u c) ∧ (u b < u a → u c < u b)
  have hequal : u b = u c → u a = u b := by
    intro he
    have hp : flow F b x = flow F c x :=
      coordinate_injOn S.toStraightSegment hab.second_hit hbc.second_hit he
    have hq := (equal_successive_prev F hF hx hab hbc hp).2
    exact congrArg S.toStraightSegment.coordinate hq
  constructor
  · intro hlt
    rcases lt_trichotomy (u b) (u c) with hbc' | he | hcb
    · exact hbc'
    · exact False.elim ((ne_of_lt hlt) (hequal he))
    · exact False.elim (successive_wrong_side_impossible F hF hx S hab hbc (Or.inl ⟨hlt,hcb⟩))
  · intro hlt
    rcases lt_trichotomy (u c) (u b) with hcb | he | hbc'
    · exact hcb
    · exact False.elim ((ne_of_gt hlt) (hequal he.symm))
    · exact False.elim (successive_wrong_side_impossible F hF hx S hab hbc (Or.inr ⟨hlt,hbc'⟩))


/-- Algebraic assembly: a three-meeting order barrier gives a single order
for every finite or infinite chronological sequence. The equal branch uses
uniqueness and the actual first-return period rather than an order assumption. -/
theorem monotone_intersections : MonotoneIntersections := by
  intro F hF x hx S K hK hK1 t hs
  let g := fun n => flow F (t n) x
  let u := fun n => S.toStraightSegment.coordinate (g n)
  have h₀ := hs 0 hK1
  by_cases he : g 0 = g 1
  · left
    have hstep : ∀ n, n+1 ∈ K → g n = g (n+1) := by
      intro n
      induction n with
      | zero => exact fun _ => he
      | succ n ih =>
        intro hn
        have hn' : n+1 ∈ K := hK (Nat.le_succ (n+1)) hn
        exact (equal_successive_next F hF hx (hs n hn') (hs (n+1) hn) (ih hn')).2
    refine ⟨?_, (repeated_intersection F hF x hx S (t 0) h₀.first_time
      (t 1) h₀.second_time h₀.lt h₀.first_hit he).1⟩
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (hstep n hn).symm.trans (ih (hK (Nat.le_succ n) hn))
  · have huc : u 0 ≠ u 1 := fun h => he
      (coordinate_injOn S.toStraightSegment h₀.first_hit h₀.second_hit h)
    rcases lt_or_gt_of_ne huc with hlt | hgt
    · right; left
      have hstep : ∀ n, n+1 ∈ K → u n < u (n+1) := by
        intro n
        induction n with
        | zero => exact fun _ => hlt
        | succ n ih =>
          intro hn
          have hn' : n+1 ∈ K := hK (Nat.le_succ (n+1)) hn
          exact (successive_order F hF x hx S (t n) (t (n+1)) (t (n+1+1))
            (hs n hn') (hs (n+1) hn)).1 (ih hn')
      exact strictMonoOn_of_lt_succ hK.ordConnected (fun n _ _ hn => hstep n hn)
    · right; right
      have hstep : ∀ n, n+1 ∈ K → u (n+1) < u n := by
        intro n
        induction n with
        | zero => exact fun _ => hgt
        | succ n ih =>
          intro hn
          have hn' : n+1 ∈ K := hK (Nat.le_succ (n+1)) hn
          exact (successive_order F hF x hx S (t n) (t (n+1)) (t (n+1+1))
            (hs n hn') (hs (n+1) hn)).2 (ih hn')
      exact strictAntiOn_of_succ_lt hK.ordConnected (fun n _ _ hn => hstep n hn)

/-- The vacuous cases do not force a periodicity conclusion. -/
theorem all_intersections : AllIntersections := by
  intro F hF x hx S K hK t hs
  by_cases h1 : 1 ∈ K
  · rcases monotone_intersections F hF x hx S K hK h1 t hs with hc | hm | ha
    · exact Or.inl ⟨hc.1, fun _ => hc.2⟩
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr ha)
  · right; left
    intro i hi j hj hij
    have hj1 : 1 ≤ j := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le i) hij)
    exact (h1 (hK hj1 hj)).elim

end D13Unified.Ch13.MonotoneCrossings
