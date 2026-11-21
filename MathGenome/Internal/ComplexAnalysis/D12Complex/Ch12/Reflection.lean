import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.Reflection
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.CirclesReflections
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Batteries.Tactic.OpenPrivate

/-! Rectangle Morera gluing, followed by Schwarz reflection. -/
noncomputable section
open Set Metric Complex Filter MeasureTheory
open scoped Topology Interval

namespace D12Complex.ReflectionDefinitions
abbrev extension := D12Complex.Reflection.extension
abbrev circleExtension := D12Complex.Reflection.circleExtension
end D12Complex.ReflectionDefinitions
namespace D12Complex.Reflection

private def boundary (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
  (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
  I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
  I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

private theorem boundary_zero_same_side {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z)
    (z w : ℂ) (hR : Rectangle z w ⊆ U)
    (hy : (0 ≤ z.im ∧ 0 ≤ w.im) ∨ (z.im ≤ 0 ∧ w.im ≤ 0)) :
    boundary f z w = 0 := by
  apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
  · exact hf.mono hR
  · intro x hx
    apply (hd x (hR ⟨⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩,
      ⟨le_of_lt hx.2.1, le_of_lt hx.2.2⟩⟩) ?_).differentiableWithinAt
    rcases hy with h | h
    · exact ne_of_gt (lt_of_le_of_lt (le_min h.1 h.2) hx.2.1)
    · exact ne_of_lt (lt_of_lt_of_le hx.2.2 (max_le h.1 h.2))

private theorem boundary_split {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Rectangle z w)) (h0 : 0 ∈ [[z.im, w.im]]) :
    boundary f z w = boundary f z (w.re : ℂ) + boundary f (z.re : ℂ) w := by
  have hi (a : ℝ) (ha : a ∈ [[z.re, w.re]]) :
      IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume z.im w.im := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (by fun_prop)
    intro y hy
    simpa [Rectangle, mem_reProdIm] using And.intro ha hy
  have hl := (hi z.re (left_mem_uIcc)).mono_set (uIcc_subset_uIcc_left h0)
  have hr := (hi w.re (right_mem_uIcc)).mono_set (uIcc_subset_uIcc_left h0)
  have hl' := (hi z.re (left_mem_uIcc)).mono_set (uIcc_subset_uIcc_right h0)
  have hr' := (hi w.re (right_mem_uIcc)).mono_set (uIcc_subset_uIcc_right h0)
  have hzl := intervalIntegral.integral_add_adjacent_intervals hl hl'
  have hwr := intervalIntegral.integral_add_adjacent_intervals hr hr'
  dsimp [boundary]
  simp only [zero_mul, add_zero]
  rw [← hzl, ← hwr, mul_add, mul_add]
  abel

theorem continuous_line_gluing :
    Specs.D12Complex.Ch12.Reflection.continuous_line_gluing_type := by
  intro U F hU hf hd
  have hcons : IsConservativeOn F U := by
    intro z w hR
    rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
    change boundary F z w = 0
    by_cases h0 : 0 ∈ [[z.im, w.im]]
    · rw [boundary_split (hf.mono hR) h0]
      have hR1 : Rectangle z (w.re : ℂ) ⊆ U := by
        apply Subset.trans ?_ hR
        rintro x hx
        exact ⟨by simpa using hx.1, (uIcc_subset_uIcc_left h0) (by simpa using hx.2)⟩
      have hR2 : Rectangle (z.re : ℂ) w ⊆ U := by
        apply Subset.trans ?_ hR
        rintro x hx
        exact ⟨by simpa using hx.1, (uIcc_subset_uIcc_right h0) (by simpa using hx.2)⟩
      have h1 := boundary_zero_same_side hf hd z (w.re : ℂ) hR1
        (by rcases le_total 0 z.im with h | h
            · exact Or.inl ⟨h, by simp⟩
            · exact Or.inr ⟨h, by simp⟩)
      have h2 := boundary_zero_same_side hf hd (z.re : ℂ) w hR2
        (by rcases le_total 0 w.im with h | h
            · exact Or.inl ⟨by simp, h⟩
            · exact Or.inr ⟨by simp, h⟩)
      rw [h1, h2, add_zero]
    · apply boundary_zero_same_side hf hd z w hR
      change ¬(min z.im w.im ≤ 0 ∧ 0 ≤ max z.im w.im) at h0
      rw [not_and_or, not_le, not_le] at h0
      rcases h0 with h | h
      · exact Or.inl ⟨le_of_lt (lt_of_lt_of_le h (min_le_left _ _)),
          le_of_lt (lt_of_lt_of_le h (min_le_right _ _))⟩
      · exact Or.inr ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) h),
          le_of_lt (lt_of_le_of_lt (le_max_right _ _) h)⟩
  have hdiff := (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp ⟨hcons, hf⟩
  exact ⟨hU, fun z hz => hdiff.differentiableAt (hU.mem_nhds hz)⟩

private theorem conj_mem_ball {c z : ℂ} {r : ℝ} (hc : c.im = 0)
    (hz : z ∈ ball c r) : star z ∈ ball c r := by
  have hcc : star c = c := Complex.conj_eq_iff_im.mpr hc
  change dist (star z) c < r
  rw [← hcc, dist_star_star]
  exact hz

private theorem extension_continuous {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hc : c.im = 0) (hf : ContinuousOn f (upperClosure c r))
    (hreal : ∀ z ∈ diameter c r, (f z).im = 0) :
    ContinuousOn (extension f) (ball c r) := by
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have hclosed' : IsClosed {z : ℂ | z.im ≤ 0} := isClosed_le continuous_im continuous_const
  have hcl : closure {z : ℂ | ¬ 0 ≤ z.im} ⊆ {z : ℂ | z.im ≤ 0} := by
    apply closure_minimal _ hclosed'
    intro z hz
    exact le_of_lt (not_le.mp hz)
  have hg : ContinuousOn (fun z => star (f (star z)))
      (ball c r ∩ {z : ℂ | z.im ≤ 0}) := by
    have hi : ContinuousOn (fun z => f (star z))
        (ball c r ∩ {z : ℂ | z.im ≤ 0}) := by
      apply hf.comp continuous_star.continuousOn
      intro z hz
      exact ⟨conj_mem_ball hc hz.1, by simpa using hz.2⟩
    exact continuous_star.comp_continuousOn hi
  apply ContinuousOn.if
  · intro z hz
    have hp : 0 ≤ z.im := by
      have := hz.2.1
      rwa [hclosed.closure_eq] at this
    have hn : z.im ≤ 0 := hcl (by change z ∈ closure ({z : ℂ | 0 ≤ z.im}ᶜ);
                                       rw [closure_compl]; exact hz.2.2)
    have hz0 := le_antisymm hn hp
    have hzc : star z = z := Complex.conj_eq_iff_im.mpr hz0
    rw [hzc, show star (f z) = f z from Complex.conj_eq_iff_im.mpr (hreal z ⟨hz.1, hz0⟩)]
  · simpa only [hclosed.closure_eq, upperClosure] using hf
  · exact hg.mono (inter_subset_inter_right _ hcl)

theorem schwarz_reflection : Specs.D12Complex.Ch12.Reflection.schwarz_reflection_type := by
  intro c r f hc _hr hf hcont hreal
  have hFcont := extension_continuous hc hcont hreal
  have hF : HolomorphicOn (ball c r) (extension f) := by
    apply continuous_line_gluing _ _ isOpen_ball hFcont
    intro z hz hzne
    rcases lt_or_gt_of_ne hzne with hneg | hpos
    · have hcz : star z ∈ upper c r :=
        ⟨conj_mem_ball hc hz, by simpa using neg_pos.mpr hneg⟩
      have hd : DifferentiableAt ℂ (fun w => star (f (star w))) z := by
        simpa only [Function.comp_def, starRingEnd_apply, star_star] using
          (hf.2 _ hcz).conj_conj
      apply hd.congr_of_eventuallyEq
      filter_upwards [isOpen_lt continuous_im continuous_const |>.mem_nhds hneg] with w hw
      simp only [extension, ite_eq_right (not_le.mpr hw)]
    · apply (hf.2 z ⟨hz, hpos⟩).congr_of_eventuallyEq
      filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds hpos] with w hw
      simp only [extension, ite_eq_left (le_of_lt hw)]
  refine ⟨hF, ?_, ?_, ?_⟩
  · intro z hz
    simp only [extension, ite_eq_left (show 0 ≤ z.im from hz.2)]
  · intro z _ hz
    simp only [extension, ite_eq_right (not_le.mpr hz)]
  · intro z hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · simp [extension, not_le.mpr h, le_of_lt (neg_pos.mpr h)]
    · have he : star z = z := Complex.conj_eq_iff_im.mpr h
      rw [he]
      simp only [extension, ite_eq_left (le_of_eq h.symm)]
      exact (Complex.conj_eq_iff_im.mpr (hreal z ⟨hz, h⟩)).symm
    · simp [extension, le_of_lt h, not_le.mpr (neg_neg_of_pos h)]

open Mobius CirclesReflections
open private coordinate_open coordinate_inverse_continuous coordinate_continuousAt
  coordinate_exists from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

/-- Composition in the two genuine sphere coordinates. -/
theorem sphereHolomorphicAt_comp {F G : RiemannSphere → RiemannSphere}
    {p : RiemannSphere} (hG : SphereHolomorphicAt G (F p))
    (hF : SphereHolomorphicAt F p) : SphereHolomorphicAt (G ∘ F) p := by
  obtain ⟨c, hc⟩ := coordinate_exists p
  obtain ⟨d, hd⟩ := coordinate_exists (F p)
  obtain ⟨e, he⟩ := coordinate_exists (G (F p))
  have hf := ((sphereHolomorphicAt_iff_charts F p c d hc hd).mp hF).2
  have hg := ((sphereHolomorphicAt_iff_charts G (F p) d e hd he).mp hG).2
  apply (sphereHolomorphicAt_iff_charts (G ∘ F) p c e hc he).mpr
  have hg' : HolomorphicGermAt
      (fun z => sphereCoordinate e (G ((sphereCoordinate d).symm z)))
      (sphereCoordinate d (F ((sphereCoordinate c).symm (sphereCoordinate c p)))) := by
    simpa only [(sphereCoordinate c).left_inv hc] using hg
  refine ⟨hG.1.comp hF.1, (hg'.comp hf).congr ?_⟩
  have ht0 : Tendsto (sphereCoordinate c).symm (𝓝 (sphereCoordinate c p)) (𝓝 p) := by
    have hh := (coordinate_inverse_continuous c).continuousAt (x := sphereCoordinate c p)
    change Tendsto _ _ (𝓝 ((sphereCoordinate c).symm (sphereCoordinate c p))) at hh
    rwa [(sphereCoordinate c).left_inv hc] at hh
  have ht := hF.1.tendsto.comp ht0
  filter_upwards [ht ((coordinate_open d).mem_nhds hd)] with z hz
  change F ((sphereCoordinate c).symm z) ∈ (sphereCoordinate d).source at hz
  rw [(sphereCoordinate d).left_inv hz]
  rfl

/-- A sphere holomorphic map may be composed with a plane-to-sphere map. -/
theorem planeSphereHolomorphicAt_comp {F : ℂ → RiemannSphere}
    {G : RiemannSphere → RiemannSphere} {a : ℂ}
    (hG : SphereHolomorphicAt G (F a)) (hF : PlaneSphereHolomorphicAt F a) :
    PlaneSphereHolomorphicAt (G ∘ F) a := by
  obtain ⟨d, hd⟩ := coordinate_exists (F a)
  obtain ⟨e, he⟩ := coordinate_exists (G (F a))
  have hf := ((planeSphereHolomorphicAt_iff_chart F a d hd).mp hF).2
  have hg := ((sphereHolomorphicAt_iff_charts G (F a) d e hd he).mp hG).2
  apply (planeSphereHolomorphicAt_iff_chart (G ∘ F) a e he).mpr
  refine ⟨hG.1.comp hF.1, (hg.comp hf).congr ?_⟩
  filter_upwards [hF.1 ((coordinate_open d).mem_nhds hd)] with z hz
  simp only [Function.comp_def, (sphereCoordinate d).left_inv hz]

private theorem mobius_continuous (M : Coefficients) (hM : Regular M) :
    Continuous (mobiusMap M) :=
  continuous_iff_continuousAt.mpr (fun p => (mobiusMap_holomorphic M hM).2 p trivial |>.1)

private theorem finiteEmbedding_holomorphic (a : ℂ) :
    PlaneSphereHolomorphicAt sphereFinite a := by
  refine ⟨continuous_sphereFinite.continuousAt, .finite, OnePoint.coe_ne_infty _, ?_⟩
  exact ⟨univ, mem_univ _, isOpen_univ, fun _ _ => differentiableAt_id⟩

theorem chartParam_holomorphic (M : Coefficients) (hM : Regular M) (a : ℂ) :
    PlaneSphereHolomorphicAt (chartParam M) a :=
  planeSphereHolomorphicAt_comp
    ((mobiusMap_holomorphic _ (regular_inverseCoefficients M hM)).2 _ trivial)
    (finiteEmbedding_holomorphic a)

theorem chartProjection_param (M : Coefficients) (hM : Regular M) (z : ℂ) :
    chartProjection M (chartParam M z) = z := by
  unfold chartProjection chartParam
  rw [(mobiusMap_inverse M hM).2, finiteCoordinate_sphereFinite]

theorem chartParam_projection (M : Coefficients) (hM : Regular M)
    (p : RiemannSphere) (hp : mobiusMap M p ≠ sphereInfty) :
    chartParam M (chartProjection M p) = p := by
  unfold chartParam chartProjection
  rw [show sphereFinite (finiteCoordinate (mobiusMap M p)) = mobiusMap M p from
    finiteChart.left_inv hp, (mobiusMap_inverse M hM).1]

theorem chartParam_mem_region (M : Coefficients) (hM : Regular M)
    {s : Set ℂ} {z : ℂ} (hz : z ∈ s) : chartParam M z ∈ chartRegion M s := by
  refine ⟨?_, by rwa [chartProjection_param M hM]⟩
  change mobiusMap M (mobiusMap (inverseCoefficients M) (sphereFinite z)) ≠ sphereInfty
  rw [(mobiusMap_inverse M hM).2]
  exact OnePoint.coe_ne_infty z

theorem chartRegion_open (M : Coefficients) (hM : Regular M)
    {s : Set ℂ} (hs : IsOpen s) : IsOpen (chartRegion M s) := by
  have hfin : IsOpen {p : RiemannSphere | p ≠ sphereInfty} := isClosed_singleton.isOpen_compl
  have ho : IsOpen {p : RiemannSphere | p ≠ sphereInfty ∧ finiteCoordinate p ∈ s} := by
    apply (continuousOn_finiteCoordinate.isOpen_inter_preimage ?_ hs)
    exact hfin
  exact ho.preimage (mobius_continuous M hM)

private theorem finiteLift_holomorphic {u : ℂ → ℂ} {p : RiemannSphere}
    (hp : p ≠ sphereInfty) (hu : HolomorphicGermAt u (finiteCoordinate p)) :
    SphereHolomorphicAt (fun q => sphereFinite (u (finiteCoordinate q))) p := by
  apply (sphereHolomorphicAt_iff_charts _ p .finite .finite hp
    (OnePoint.coe_ne_infty _)).mpr
  refine ⟨continuous_sphereFinite.continuousAt.comp
    (hu.differentiableAt.continuousAt.comp (coordinate_continuousAt .finite p hp)), ?_⟩
  change HolomorphicGermAt (fun z => u z) (finiteCoordinate p)
  exact hu

theorem circle_reflection_in_charts :
    Specs.D12Complex.Ch12.Reflection.circle_reflection_in_charts_type := by
  intro M N D c r f hM hN hND hc hr hf hcont hmap hpole
  have hparamcont : Continuous (chartParam M) :=
    (mobius_continuous _ (regular_inverseCoefficients M hM)).comp continuous_sphereFinite
  have hstraight : HolomorphicOn (upper c r) (straightened M N f) := by
    refine ⟨isOpen_ball.inter (isOpen_lt continuous_const continuous_im), ?_⟩
    intro z hz
    have h1 : PlaneSphereHolomorphicAt (f ∘ chartParam M) z :=
      planeSphereHolomorphicAt_comp (hf.2 _ (chartParam_mem_region M hM hz))
        (chartParam_holomorphic M hM z)
    have h2 := planeSphereHolomorphicAt_comp ((mobiusMap_holomorphic N hN).2 _ trivial) h1
    have hne : mobiusMap N (f (chartParam M z)) ≠ sphereInfty :=
      hpole z ⟨hz.1, show 0 ≤ z.im from le_of_lt (show 0 < z.im from hz.2)⟩
    exact ((planeSphereHolomorphicAt_iff_chart _ z .finite hne).mp h2).2.differentiableAt
  have hstraightcont : ContinuousOn (straightened M N f) (upperClosure c r) := by
    apply continuousOn_finiteCoordinate.comp
      ((mobius_continuous N hN).comp_continuousOn
        (hcont.comp hparamcont.continuousOn (fun z hz => chartParam_mem_region M hM hz)))
    intro z hz
    exact hpole z hz
  have hstraightreal : ∀ z ∈ diameter c r, (straightened M N f z).im = 0 := by
    intro z hz
    have hd := hmap (chartParam_mem_region M hM hz)
    have ht : mobiusMap N (f (chartParam M z)) ∈ extendedRealLine := by
      rw [← hND]
      exact mem_image_of_mem _ hd
    have he := finiteChart.left_inv (hpole z ⟨hz.1, le_of_eq hz.2.symm⟩)
    rw [← he] at ht
    exact ht
  obtain ⟨hext, hagree, hlower, _hsym⟩ :=
    schwarz_reflection c r (straightened M N f) hc hr hstraight hstraightcont hstraightreal
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨chartRegion_open M hM isOpen_ball, ?_⟩
    intro p hp
    have h1 := finiteLift_holomorphic hp.1
      (show HolomorphicGermAt (extension (straightened M N f)) (chartProjection M p) from
        ⟨ball c r, hp.2, hext⟩)
    exact sphereHolomorphicAt_comp
      ((mobiusMap_holomorphic _ (regular_inverseCoefficients N hN)).2 _ trivial)
      (sphereHolomorphicAt_comp h1 ((mobiusMap_holomorphic M hM).2 _ trivial))
  · intro p hp
    have hpp := chartParam_projection M hM p hp.1
    have hne := hpole (chartProjection M p) hp.2
    change mobiusMap (inverseCoefficients N)
      (sphereFinite (extension (straightened M N f) (chartProjection M p))) = f p
    rw [hagree hp.2]
    unfold straightened chartProjection
    rw [show chartParam M (finiteCoordinate (mobiusMap M p)) = p from hpp,
      show sphereFinite (finiteCoordinate (mobiusMap N (f p))) = mobiusMap N (f p) from
        finiteChart.left_inv (by change mobiusMap N (f p) ≠ sphereInfty; simpa only [hpp] using hne),
      (mobiusMap_inverse N hN).1]
  · intro p hp hneg
    have hpp : mobiusMap M p = sphereFinite (chartProjection M p) :=
      (finiteChart.left_inv hp.1).symm
    have hreflect : reflectionVia M p = chartParam M (star (chartProjection M p)) := by
      unfold reflectionVia chartParam
      change mobiusMap (inverseCoefficients M) (sphereConj (mobiusMap M p)) = _
      rw [hpp]
      rfl
    change mobiusMap (inverseCoefficients N)
      (sphereFinite (extension (straightened M N f) (chartProjection M p))) = _
    rw [hlower _ hp.2 hneg]
    have hz : star (chartProjection M p) ∈ upperClosure c r :=
      ⟨conj_mem_ball hc hp.2, by simpa using le_of_lt (neg_pos.mpr hneg)⟩
    have hne := hpole _ hz
    unfold straightened
    change mobiusMap (inverseCoefficients N)
      (sphereFinite (star (finiteCoordinate (mobiusMap N
        (f (chartParam M (star (chartProjection M p)))))))) = _
    rw [← hreflect]
    unfold reflectionVia
    change mobiusMap (inverseCoefficients N)
      (sphereFinite (star (finiteCoordinate (mobiusMap N (f (reflectionVia M p)))))) =
      mobiusMap (inverseCoefficients N) (sphereConj (mobiusMap N (f (reflectionVia M p))))
    have hne' : mobiusMap N (f (reflectionVia M p)) ≠ sphereInfty := by
      rw [hreflect]
      exact hne
    rw [show mobiusMap N (f (reflectionVia M p)) =
        sphereFinite (finiteCoordinate (mobiusMap N (f (reflectionVia M p)))) from
      (finiteChart.left_inv hne').symm]
    rfl

theorem circle_reflection_coordinates :
    Specs.D12Complex.Ch12.Reflection.circle_reflection_coordinates_type := by
  intro M N c r f hF p hp b hb
  constructor
  · intro hfin
    exact ((sphereHolomorphicAt_iff_charts _ p b .finite hb hfin).mp (hF.2 p hp)).2
  · intro hinf
    exact ⟨((sphereHolomorphicAt_iff_charts _ p b .reciprocal hb
      (by rw [hinf]; exact OnePoint.infty_ne_coe 0)).mp (hF.2 p hp)).2,
      by rw [hinf]; rfl⟩

private theorem circle_mem_iff_coordinate {C : Set RiemannSphere} {M : Coefficients}
    (hM : Regular M) (hC : mobiusMap M '' C = extendedRealLine)
    {p : RiemannSphere} (hp : mobiusMap M p ≠ sphereInfty) :
    p ∈ C ↔ (chartProjection M p).im = 0 := by
  have he := finiteChart.left_inv hp
  constructor
  · intro h
    have hm : mobiusMap M p ∈ extendedRealLine := by rw [← hC]; exact mem_image_of_mem _ h
    rw [← he] at hm
    exact hm
  · intro h
    have hm : mobiusMap M p ∈ extendedRealLine := by rw [← he]; exact h
    rw [← hC] at hm
    obtain ⟨q, hq, heq⟩ := hm
    exact (mobiusMap_bijective M hM).1 heq ▸ hq

theorem generalized_circle_charts :
    Specs.D12Complex.Ch12.Reflection.generalized_circle_charts_type := by
  intro C D hC hD
  obtain ⟨M, hM, hm⟩ := generalizedCircle_to_realLine C hC
  obtain ⟨N, hN, hn⟩ := generalizedCircle_to_realLine D hD
  exact ⟨M, N, hM, hN, hm, hn, fun _ hp => circle_mem_iff_coordinate hM hm hp,
    fun _ hp => circle_mem_iff_coordinate hN hn hp⟩

/-- Inverting a real-line coordinate moves its pole to zero and still
straightens the same circle. -/
private theorem targetChart_finite_at (N : Coefficients) (hN : Regular N)
    (D : Set RiemannSphere) (hND : mobiusMap N '' D = extendedRealLine)
    (q : RiemannSphere) :
    ∃ K : Coefficients, Regular K ∧ mobiusMap K '' D = extendedRealLine ∧
      mobiusMap K q ≠ sphereInfty := by
  by_cases hq : mobiusMap N q = sphereInfty
  · let J : Coefficients := !![0, 1; 1, 0]
    have hJ : Regular J := by norm_num [Regular, J, Matrix.det_fin_two]
    have hJR : RealCoefficientsUpToScalar J := by
      refine ⟨1, one_ne_zero, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;> simp [J]
    have hJl := (preserves_realLine_iff_realCoefficients J hJ).mpr hJR
    have hJi : mobiusMap J sphereInfty = sphereFinite 0 := by
      simp [mobiusMap, sphereInfty, sphereFinite, spherePair, J]
    refine ⟨J * N, regular_mul _ _ hJ hN, ?_, ?_⟩
    · rw [mobiusMap_mul _ _ hJ hN]
      calc
        (mobiusMap J ∘ mobiusMap N) '' D = mobiusMap J '' (mobiusMap N '' D) :=
          by simpa only [Function.comp_def] using
            (image_image (mobiusMap J) (mobiusMap N) D).symm
        _ = extendedRealLine := by rw [hND, hJl]
    · rw [mobiusMap_mul _ _ hJ hN]
      change mobiusMap J (mobiusMap N q) ≠ sphereInfty
      rw [hq, hJi]
      exact OnePoint.coe_ne_infty 0
  · exact ⟨N, hN, hND, hq⟩

theorem local_circle_reflection :
    Specs.D12Complex.Ch12.Reflection.local_circle_reflection_type := by
  intro M N D c R f hM hN hD hND hc hR hf hcont hmap
  obtain ⟨K, hK, hKD, hKc⟩ := targetChart_finite_at N hN D hND (f (chartParam M c))
  have hparamcont : Continuous (chartParam M) :=
    (mobius_continuous _ (regular_inverseCoefficients M hM)).comp continuous_sphereFinite
  have htrans : ContinuousOn (fun z => mobiusMap K (f (chartParam M z)))
      (upperClosure c R) :=
    (mobius_continuous K hK).comp_continuousOn
      (hcont.comp hparamcont.continuousOn (fun z hz => chartParam_mem_region M hM hz))
  have hcc : c ∈ upperClosure c R := ⟨mem_ball_self hR, by simp [hc]⟩
  have hn := (htrans c hcc).preimage_mem_nhdsWithin
    (isClosed_singleton.isOpen_compl.mem_nhds hKc)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hn
  let r := min R δ
  have hr : 0 < r := lt_min hR hδ
  have hrR : r ≤ R := min_le_left _ _
  have hsmall : ball c r ⊆ ball c R := ball_subset_ball hrR
  have hpole : ∀ z ∈ upperClosure c r, mobiusMap K (f (chartParam M z)) ≠ sphereInfty := by
    intro z hz
    exact hδsub ⟨(ball_subset_ball (min_le_right R δ)) hz.1, hsmall hz.1, hz.2⟩
  have hfsmall : SphereHolomorphicOn (chartRegion M (upper c r)) f := by
    refine ⟨chartRegion_open M hM (isOpen_ball.inter (isOpen_lt continuous_const continuous_im)), ?_⟩
    intro p hp
    exact hf.2 p ⟨hp.1, hsmall hp.2.1, hp.2.2⟩
  have hcsmall : ContinuousOn f (chartRegion M (upperClosure c r)) :=
    hcont.mono (fun p hp => ⟨hp.1, hsmall hp.2.1, hp.2.2⟩)
  have hmsmall : MapsTo f (chartRegion M (diameter c r)) D :=
    fun p hp => hmap ⟨hp.1, hsmall hp.2.1, hp.2.2⟩
  obtain ⟨hF, hagree, hlower⟩ := circle_reflection_in_charts M K D c r f
    hM hK hKD hc hr hfsmall hcsmall hmsmall hpole
  refine ⟨r, K, hr, hrR, hK, hKD, hKc, hF, hagree, ?_⟩
  intro p hp hneg
  rw [hlower p hp hneg, reflection_independent D K N hD hK hN hKD hND]

theorem finite_lift_holomorphic :
    Specs.D12Complex.Ch12.Reflection.finite_lift_holomorphic_type := by
  intro U f hf
  have hfin : IsOpen {p : RiemannSphere | p ≠ sphereInfty} := isClosed_singleton.isOpen_compl
  refine ⟨continuousOn_finiteCoordinate.isOpen_inter_preimage hfin hf.1, ?_⟩
  intro p hp
  exact finiteLift_holomorphic hp.1 ⟨U, hp.2, hf⟩

theorem finite_lift_continuous :
    Specs.D12Complex.Ch12.Reflection.finite_lift_continuous_type := by
  intro s f hf
  apply continuous_sphereFinite.comp_continuousOn
  apply hf.comp (continuousOn_finiteCoordinate.mono (fun _ hp => hp.1))
  intro p hp
  exact hp.2

private theorem finiteCoordinate_eq_inv_infinityCoordinate (p : RiemannSphere) :
    finiteCoordinate p = (infinityCoordinate p)⁻¹ := by
  induction p using OnePoint.rec with
  | infty => simp [finiteCoordinate, infinityCoordinate]
  | coe z => simp [finiteCoordinate, infinityCoordinate]

private theorem germ_analytic {u : ℂ → ℂ} {a : ℂ} (hu : HolomorphicGermAt u a) :
    AnalyticAt ℂ u a :=
  Complex.analyticAt_iff_eventually_differentiableAt.mpr
    ((holomorphicGermAt_iff_eventually _ _).mp hu)

theorem circle_reflection_meromorphic :
    Specs.D12Complex.Ch12.Reflection.circle_reflection_meromorphic_type := by
  intro M N c r f hF p hp b hb
  obtain ⟨hfin, hinf⟩ := circle_reflection_coordinates M N c r f hF p hp b hb
  by_cases h : circleExtension M N f p = sphereInfty
  · have ha := germ_analytic (hinf h).1
    have hm := ha.meromorphicAt.inv
    apply hm.congr
    exact Filter.Eventually.of_forall (fun z =>
      (finiteCoordinate_eq_inv_infinityCoordinate _).symm)
  · exact (germ_analytic (hfin h)).meromorphicAt

theorem plane_circle_reflection :
    Specs.D12Complex.Ch12.Reflection.plane_circle_reflection_type := by
  intro C D M N c R f _hC hD hM hN _hMC hND hc hR hsource hf hcont hmap
  have hu : IsOpen (upper c R) := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hfinite {s : Set ℂ} (hs : s ⊆ ball c R) {p : RiemannSphere}
      (hp : p ∈ chartRegion M s) :
      p ≠ sphereInfty ∧ finiteCoordinate p ∈ planeChartRegion M s := by
    have hpf := hsource p ⟨hp.1, hs hp.2⟩
    refine ⟨hpf, ?_⟩
    change sphereFinite (finiteCoordinate p) ∈ chartRegion M s
    rwa [show sphereFinite (finiteCoordinate p) = p from finiteChart.left_inv hpf]
  have hfu : SphereHolomorphicOn (chartRegion M (upper c R)) (finiteLift f) := by
    refine ⟨chartRegion_open M hM hu, ?_⟩
    intro p hp
    exact (finite_lift_holomorphic _ f hf).2 p
      (hfinite (fun _ hz => hz.1) hp)
  have hfcl : ContinuousOn (finiteLift f) (chartRegion M (upperClosure c R)) := by
    exact (finite_lift_continuous _ f hcont).mono (fun p hp => hfinite (fun _ hz => hz.1) hp)
  have hfmap : MapsTo (finiteLift f) (chartRegion M (diameter c R)) D := by
    intro p hp
    exact hmap (hfinite (fun _ hz => hz.1) hp).2
  obtain ⟨r, K, hr, hrR, hK, hKD, _hKc, hF, hagree, _hlower⟩ :=
    local_circle_reflection M N D c R (finiteLift f) hM hN hD hND hc hR hfu hfcl hfmap
  refine ⟨r, K, hr, hrR, hK, hKD, hF, ?_, ?_, ?_⟩
  · intro z hz
    have h := circle_reflection_meromorphic M K c r (finiteLift f) hF (sphereFinite z)
      hz .finite (OnePoint.coe_ne_infty z)
    exact h
  · intro z hz
    have h := congrArg finiteCoordinate (hagree hz)
    simpa only [finiteLift, finiteCoordinate_sphereFinite] using h
  · intro z hz
    have hzb : sphereFinite z ∈ chartRegion M (ball c r) := ⟨hz.1, hz.2.1⟩
    have hza : sphereFinite z ∈ chartRegion M (upperClosure c r) :=
      ⟨hz.1, hz.2.1, by
        change 0 ≤ (chartProjection M (sphereFinite z)).im
        exact le_of_eq (show (chartProjection M (sphereFinite z)).im = 0 from hz.2.2).symm⟩
    have hne : circleExtension M K (finiteLift f) (sphereFinite z) ≠ sphereInfty := by
      rw [hagree hza]
      exact OnePoint.coe_ne_infty _
    exact (circle_reflection_coordinates M K c r (finiteLift f) hF (sphereFinite z)
      hzb .finite (OnePoint.coe_ne_infty z)).1 hne

theorem source_chart_locally_finite :
    Specs.D12Complex.Ch12.Reflection.source_chart_locally_finite_type := by
  intro M c R hM hR hc
  have hparamcont : Continuous (chartParam M) :=
    (mobius_continuous _ (regular_inverseCoefficients M hM)).comp continuous_sphereFinite
  have he : {z | chartParam M z ≠ sphereInfty} ∈ 𝓝 c :=
    hparamcont.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hc)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min R δ, lt_min hR hδ, min_le_left _ _, ?_⟩
  intro p hp
  have hne := hsub ((ball_subset_ball (min_le_right R δ)) hp.2)
  change chartParam M (chartProjection M p) ≠ sphereInfty at hne
  rwa [chartParam_projection M hM p hp.1] at hne

end D12Complex.Reflection
