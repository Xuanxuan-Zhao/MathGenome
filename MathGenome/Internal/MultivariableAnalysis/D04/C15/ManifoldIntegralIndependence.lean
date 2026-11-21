import MathGenome.Internal.MultivariableAnalysis.D04.C15.OrientedManifoldAndDensityIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OrientationsAndChartSigns

/-! Independence of the actual proper Riemann chart integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open Set Function Topology
open scoped ContDiff BigOperators
namespace D04.ManifoldIntegralIndependence
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C14.FiniteCompactPartition.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open D04.Darboux D04.JordanRegions D04.DirectedSubstitution

/-- Scalar linearity on relative parameter domains, including their flat faces. -/
lemma coefficientIntegral_smul {k : ℕ} {S : Set (E k)} (a : ℝ) {f : S → ℝ}
    (hf : ProperIntegrable f) :
    coefficientIntegral (fun x => a * f x) = a * coefficientIntegral f := by
  have hs := Orientation.support_smul_subset a f
  obtain ⟨Q, hQ, hi⟩ := hf.2
  have hQa : Encloses (support (zeroExtension (fun x => a * f x))) Q :=
    (closure_mono hs).trans hQ
  have hia : Integrable (zeroExtension (fun x => a * f x)) Q := by
    rw [Orientation.zeroExtension_smul]
    exact Darboux.integrable_smul a hi
  have hfa : ProperIntegrable (fun x => a * f x) :=
    ⟨hf.1.subset hs, Q, hQa, hia⟩
  obtain ⟨hi', hv⟩ := DirectedSubstitution.proper_on_box hf Q hQ
  obtain ⟨hia', hva⟩ := DirectedSubstitution.proper_on_box hfa Q hQa
  rw [hv, hva]
  have h := Darboux.integral_smul a hi' (Darboux.integrable_smul a hi')
  change lowerIntegral _ Q = a * lowerIntegral _ Q at h ⊢
  rw [Orientation.zeroExtension_smul]
  exact h

/-- The absolute-Jacobian comparison in one Euclidean extension neighborhood.
The ambient zero extensions may jump at the genuine flat boundary. -/
lemma local_overlap_unsigned {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (heq : EqOn e (chartTransition c d) (chartOverlap c d ∩ e.source))
    (hd : ∀ x ∈ chartOverlap c d ∩ e.source,
      fderiv ℝ e x = fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x)
    {f : chartOverlap d c → ℝ} (hf : Continuous f) (hk : HasCompactSupport f)
    (hs : ∀ y ∈ tsupport f, chartTransition d c y ∈ e.source) :
    coefficientIntegral (fun x : chartOverlap c d =>
      f (DirectedSubstitution.overlapHomeomorph c d x) *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det|) =
      coefficientIntegral f := by
  let F : e.target → ℝ := fun y => zeroExtension f y
  have ht : tsupport (zeroExtension f) ⊆ e.target := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (Localization.zeroExtension_tsupport hk).le hy
    have hj := EmbeddedChart.transition_mem d c z.property
    have hzx := hs z hz
    have hez : e (chartTransition d c z) = z :=
      (heq ⟨hj, hzx⟩).trans (EmbeddedChart.transition_left_inv d c z.property)
    rw [← hez]
    exact e.map_source hzx
  have hF : zeroExtension F = zeroExtension f := by
    funext y
    by_cases hy : y ∈ e.target
    · exact zeroExtension_apply F ⟨y, hy⟩
    · rw [zeroExtension_of_not_mem F hy]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hy (ht h))).symm
  have hfi := DirectedSubstitution.parameter_integrable d.half
    (DirectedSubstitution.overlap_parameter_domain d c) hf hk
  have hFi : OpenIntegrable F := ⟨e.open_target, (DirectedSubstitution.proper_congr hF).1.mpr hfi⟩
  have hFk : HasCompactSupport F := RiemannSubstitution.compact_restrict
    (Localization.zeroExtension_compact hk) ht
  have hFb : RegionBounded F := DirectedSubstitution.extension_regionBounded
    (DirectedSubstitution.regionBounded_of_continuous_compact hf hk)
  let p : e.source → ℝ := fun x => F ⟨e x, e.map_source x.property⟩ * |(fderiv ℝ e x).det|
  have hsub := RiemannSubstitution.riemann_substitution e.toHomeomorphSourceTarget e e.symm
    e.open_source e.open_target he hei (fun _ => rfl) (fun _ => rfl) F hFb hFk
  have hpval : openIntegral F = openIntegral p := hsub.2.2.2.2.2 (Or.inl hFi)
  let g : chartOverlap c d → ℝ := fun x =>
    f (DirectedSubstitution.overlapHomeomorph c d x) *
      |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det|
  have hxS {x : E k} (hx : x ∈ e.source) (hn : zeroExtension f (e x) ≠ 0) :
      x ∈ chartOverlap c d := by
    have hy : e x ∈ chartOverlap d c := by
      by_contra hy
      exact hn (zeroExtension_of_not_mem f hy)
    let y : chartOverlap d c := ⟨e x, hy⟩
    have hyn : f y ≠ 0 := by
      intro hz
      apply hn
      exact (zeroExtension_apply f y).trans hz
    have hjx := hs y (subset_tsupport f hyn)
    have hjs := EmbeddedChart.transition_mem d c hy
    have hje : e (chartTransition d c y) = e x :=
      (heq ⟨hjs, hjx⟩).trans (EmbeddedChart.transition_left_inv d c hy)
    exact e.injOn hjx hx hje ▸ hjs
  have hext : zeroExtension g = zeroExtension p := by
    funext x
    by_cases hx : x ∈ e.source
    · rw [zeroExtension_apply p ⟨x, hx⟩]
      by_cases hxS' : x ∈ chartOverlap c d
      · rw [zeroExtension_apply g ⟨x, hxS'⟩]
        have hex := heq ⟨hxS', hx⟩
        have hdx := hd x ⟨hxS', hx⟩
        change f _ * |_| = zeroExtension f (e x) * |(fderiv ℝ e x).det|
        rw [hdx, hex]
        exact congrArg (fun z => z * |(fderivWithin ℝ (chartTransition c d)
          (chartOverlap c d) x).det|)
          (zeroExtension_apply f (DirectedSubstitution.overlapHomeomorph c d ⟨x, hxS'⟩)).symm
      · rw [zeroExtension_of_not_mem g hxS']
        have hz : zeroExtension f (e x) = 0 := by
          by_contra hn
          exact hxS' (hxS hx hn)
        change 0 = zeroExtension f (e x) * _
        rw [hz, zero_mul]
    · rw [zeroExtension_of_not_mem p hx]
      by_cases hxS' : x ∈ chartOverlap c d
      · rw [zeroExtension_apply g ⟨x, hxS'⟩]
        have hz : f (DirectedSubstitution.overlapHomeomorph c d ⟨x, hxS'⟩) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro ht'
          have h := hs _ ht'
          change chartTransition d c (chartTransition c d x) ∈ e.source at h
          exact hx ((EmbeddedChart.transition_left_inv c d hxS') ▸ h)
        change f _ * _ = 0
        rw [hz, zero_mul]
      · exact zeroExtension_of_not_mem g hxS'
  exact (DirectedSubstitution.proper_congr hext).2.trans
    (hpval.symm.trans (DirectedSubstitution.proper_congr hF).2)

/-- Unsigned substitution on an arbitrary chart overlap. Its components may
have different determinant signs. Localization uses only compact support. -/
lemma overlap_unsigned {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    {f : chartOverlap d c → ℝ} (hf : Continuous f) (hk : HasCompactSupport f) :
    coefficientIntegral (fun x : chartOverlap c d =>
      f (DirectedSubstitution.overlapHomeomorph c d x) *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) x).det|) =
      coefficientIntegral f := by
  classical
  let S := chartOverlap c d
  let T := chartOverlap d c
  let g : S → ℝ := fun x => f (DirectedSubstitution.overlapHomeomorph c d x) *
    |(fderivWithin ℝ (chartTransition c d) S x).det|
  have hloc (y : T) := DirectedSubstitution.local_transition_diffeomorph c d hr hkn
    (EmbeddedChart.transition_mem d c y.property)
  choose e hae he hei heq hd using hloc
  let U : T → Set T := fun y => {z | chartTransition d c z ∈ (e y).source}
  have hU (y : T) : IsOpen (U y) :=
    (e y).open_source.preimage (EmbeddedChart.transition_continuous d c).domRestrict
  have hcover : tsupport f ⊆ ⋃ y, U y := fun y _ => mem_iUnion.mpr ⟨y, hae y⟩
  letI : LocallyCompactSpace T := DirectedSubstitution.parameter_locallyCompact d.half
    (DirectedSubstitution.overlap_parameter_domain d c)
  obtain ⟨s, F, hF, hsum⟩ := DirectedSubstitution.relative_decomposition U hU f hf hk hcover
  let G : s → S → ℝ := fun i x => F i (DirectedSubstitution.overlapHomeomorph c d x) *
    |(fderivWithin ℝ (chartTransition c d) S x).det|
  have hGi (i : s) : Continuous (G i) ∧ HasCompactSupport (G i) :=
    ⟨((hF i).1.comp (DirectedSubstitution.overlapHomeomorph c d).continuous).mul
      (DirectedSubstitution.chart_determinant_regular c d hr hkn).1.domRestrict.abs,
      (RiemannSubstitution.compact_pullback (DirectedSubstitution.overlapHomeomorph c d)
        (hF i).2.1).mul_right⟩
  have hval (i : s) : coefficientIntegral (G i) = coefficientIntegral (F i) :=
    local_overlap_unsigned c d hr hkn (e i.val) (he i.val) (hei i.val) (heq i.val)
      (hd i.val) (hF i).1 (hF i).2.1 (fun y hy => (hF i).2.2 hy)
  have hg : g = fun x => ∑ i, G i x := by
    funext x
    change f _ * _ = ∑ i, F i _ * _
    rw [congrFun hsum (DirectedSubstitution.overlapHomeomorph c d x), Finset.sum_mul]
  calc
    coefficientIntegral g = coefficientIntegral (fun x => ∑ i, G i x) := congrArg _ hg
    _ = ∑ i, coefficientIntegral (G i) := DirectedSubstitution.parameter_integral_sum c.half
      (DirectedSubstitution.overlap_parameter_domain c d) G (fun i => (hGi i).1) (fun i => (hGi i).2)
    _ = ∑ i, coefficientIntegral (F i) := Finset.sum_congr rfl (fun i _ => hval i)
    _ = coefficientIntegral f :=
      (DirectedSubstitution.parameter_integral_sum d.half
        (DirectedSubstitution.overlap_parameter_domain d c) F (fun i => (hF i).1)
        (fun i => (hF i).2.1)).symm.trans (congrArg _ hsum.symm)

/-- Restricting to a smaller represented domain containing the support leaves
its ambient zero extension and hence its proper Riemann integral unchanged. -/
lemma restrict_coefficient {k : ℕ} {S T : Set (E k)} (hST : S ⊆ T)
    {f : T → ℝ} (hf : Continuous f) (hk : HasCompactSupport f)
    (hs : Subtype.val '' tsupport f ⊆ S) :
    let g : S → ℝ := fun x => f ⟨x, hST x.property⟩
    Continuous g ∧ HasCompactSupport g ∧ coefficientIntegral g = coefficientIntegral f := by
  let g : S → ℝ := fun x => f ⟨x, hST x.property⟩
  have hg : g = fun x : S => zeroExtension f x := by
    funext x
    exact (zeroExtension_apply f ⟨x, hST x.property⟩).symm
  have hext : zeroExtension g = zeroExtension f := by
    funext x
    by_cases hx : x ∈ S
    · rw [zeroExtension_apply g ⟨x, hx⟩, hg]
    · rw [zeroExtension_of_not_mem g hx]
      apply Eq.symm
      apply image_eq_zero_of_notMem_tsupport
      rw [Localization.zeroExtension_tsupport hk]
      exact fun h => hx (hs h)
  refine ⟨hf.comp (continuous_subtype_val.subtype_mk _), ?_,
    (DirectedSubstitution.proper_congr hext).2⟩
  change HasCompactSupport g
  rw [hg]
  exact RiemannSubstitution.compact_restrict (Localization.zeroExtension_compact hk)
    ((Localization.zeroExtension_tsupport hk) ▸ hs)

/-- Chart coefficient families transforming by the absolute Jacobian include
both unsigned densities and orientation-adjusted top forms. -/
abbrev ChartCoefficients (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) :=
  (c : EmbeddedChart r k n M) → c.source → ℝ

def weightedCoefficient {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (A : ChartCoefficients r k M) (c : EmbeddedChart r k n M) (w : E n → ℝ) : c.source → ℝ :=
  fun u => w (c.toFun u) * A c u

/-- The compact support bound needed to pass from a chart to an overlap. -/
lemma weighted_support {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (A : ChartCoefficients r k M) (c : EmbeddedChart r k n M) (w : E n → ℝ) :
    tsupport (weightedCoefficient A c w) ⊆
      chartPoint c ⁻¹' tsupport (fun x : M => w x) :=
  tsupport_mul_subset_left.trans
    (tsupport_comp_subset_preimage (fun x : M => w x) (ManifoldIntegral.chartPoint_continuous c))

lemma weighted_overlap {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (A : ChartCoefficients r k M) (hA : ∀ c, Continuous (A c))
    (hchange : ∀ (c d : EmbeddedChart r k n M) (u : chartOverlap c d),
      A c ⟨u, u.property.1⟩ =
        A d ⟨chartTransition c d u, (EmbeddedChart.transition_mem c d u.property).1⟩ *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det|)
    (c d : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    (w : E n → ℝ) (hwc : Continuous w)
    (hw : IsCompact (tsupport (fun x : M => w x)))
    (hsc : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient)
    (hsd : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' d.ambient) :
    coefficientIntegral (weightedCoefficient A c w) =
      coefficientIntegral (weightedCoefficient A d w) := by
  have hci := ManifoldIntegral.localized_coefficient_integrable c w (A c) hwc (hA c) hw hsc
  have hdi := ManifoldIntegral.localized_coefficient_integrable d w (A d) hwc (hA d) hw hsd
  have hcs : Subtype.val '' tsupport (weightedCoefficient A c w) ⊆ chartOverlap c d := by
    rintro u ⟨v, hv, rfl⟩
    exact ⟨v.property, hsd (weighted_support A c w hv)⟩
  have hds : Subtype.val '' tsupport (weightedCoefficient A d w) ⊆ chartOverlap d c := by
    rintro u ⟨v, hv, rfl⟩
    exact ⟨v.property, hsc (weighted_support A d w hv)⟩
  have hc := restrict_coefficient (S := chartOverlap c d) inter_subset_left hci.1 hci.2.1 hcs
  have hd := restrict_coefficient (S := chartOverlap d c) inter_subset_left hdi.1 hdi.2.1 hds
  let f : chartOverlap d c → ℝ := fun u => weightedCoefficient A d w ⟨u, u.property.1⟩
  have he : (fun u : chartOverlap c d => weightedCoefficient A c w ⟨u, u.property.1⟩) =
      fun u => f (DirectedSubstitution.overlapHomeomorph c d u) *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det| := by
    funext u
    have hp : d.toFun (chartTransition c d u) = c.toFun u :=
      d.right_inv _ ⟨(c.map_source u.property.1).1, u.property.2⟩
    change w (c.toFun u) * A c ⟨u, u.property.1⟩ =
      w (d.toFun (chartTransition c d u)) *
        A d ⟨chartTransition c d u, (EmbeddedChart.transition_mem c d u.property).1⟩ * _
    rw [hchange c d u, hp]
    ring
  exact hc.2.2.symm.trans ((congrArg coefficientIntegral he).trans
    ((overlap_unsigned c d hr hkn hd.1 hd.2.1).trans hd.2.2))

/-- Adding a second partition inserts products of the two weights. -/
lemma weighted_refinement {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (A : ChartCoefficients r k M) (hA : ∀ c, Continuous (A c))
    {K : Set M} (P : ChartPartition r k M K)
    (hK : ∀ (c : EmbeddedChart r k n M) (u : c.source), A c u ≠ 0 → chartPoint c u ∈ K)
    (c : EmbeddedChart r k n M) (w : E n → ℝ) (hwc : Continuous w)
    (hw : IsCompact (tsupport (fun x : M => w x)))
    (hs : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    coefficientIntegral (weightedCoefficient A c w) =
      ∑ j, coefficientIntegral (weightedCoefficient A c (fun x => w x * P.weight j x)) := by
  have hsum : weightedCoefficient A c w = fun u =>
      ∑ j, weightedCoefficient A c (fun x => w x * P.weight j x) u := by
    funext u
    by_cases hn : A c u = 0
    · simp [weightedCoefficient, hn]
    · obtain ⟨V, _, hKV, hV⟩ := P.partition.2.2.2.1
      have hv := hV (chartPoint c u) (hKV (hK c u hn))
      change ∑ j, P.weight j (c.toFun u) = 1 at hv
      simp only [weightedCoefficient]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hv, mul_one]
  have hi (j : Fin P.count) := ManifoldIntegral.localized_coefficient_integrable c
    (fun x => w x * P.weight j x) (A c)
    (hwc.mul (P.partition.1 j).continuous) (hA c)
    (hw.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)
    (tsupport_mul_subset_left.trans hs)
  rw [hsum]
  exact DirectedSubstitution.parameter_integral_sum c.half c.source_open _
    (fun j => (hi j).1) (fun j => (hi j).2.1)

/-- The double-partition argument for actual absolute-Jacobian coefficients.
No orientation, connectedness or absence of boundary is required. -/
lemma partition_independence {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (A : ChartCoefficients r k M) (hA : ∀ c, Continuous (A c))
    (hchange : ∀ (c d : EmbeddedChart r k n M) (u : chartOverlap c d),
      A c ⟨u, u.property.1⟩ =
        A d ⟨chartTransition c d u, (EmbeddedChart.transition_mem c d u.property).1⟩ *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det|)
    (hr : ManifoldRegularity r) (hkn : k ≤ n) {K L : Set M}
    (P : ChartPartition r k M K) (Q : ChartPartition r k M L)
    (hK : ∀ c u, A c u ≠ 0 → chartPoint c u ∈ K)
    (hL : ∀ c u, A c u ≠ 0 → chartPoint c u ∈ L) :
    (∑ i, coefficientIntegral (weightedCoefficient A (P.chart i) (P.weight i))) =
      ∑ j, coefficientIntegral (weightedCoefficient A (Q.chart j) (Q.weight j)) := by
  classical
  have hpair (i : Fin P.count) (j : Fin Q.count) :
      coefficientIntegral (weightedCoefficient A (P.chart i) (fun x => P.weight i x * Q.weight j x)) =
      coefficientIntegral (weightedCoefficient A (Q.chart j) (fun x => Q.weight j x * P.weight i x)) := by
    rw [weighted_overlap A hA hchange (P.chart i) (Q.chart j) hr hkn
      (fun x => P.weight i x * Q.weight j x)
      ((P.partition.1 i).continuous.mul (Q.partition.1 j).continuous)
      ((P.partition.2.2.1 i).1.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)
      (tsupport_mul_subset_left.trans (P.partition.2.2.1 i).2)
      (tsupport_mul_subset_right.trans (Q.partition.2.2.1 j).2)]
    congr 1
    funext u
    dsimp only [weightedCoefficient]
    ring
  calc
    _ = ∑ i, ∑ j, coefficientIntegral
        (weightedCoefficient A (P.chart i) (fun x => P.weight i x * Q.weight j x)) :=
      Finset.sum_congr rfl (fun i _ => weighted_refinement A hA Q hL _ _
        (P.partition.1 i).continuous (P.partition.2.2.1 i).1 (P.partition.2.2.1 i).2)
    _ = ∑ j, ∑ i, coefficientIntegral
        (weightedCoefficient A (Q.chart j) (fun x => Q.weight j x * P.weight i x)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hpair i j))
    _ = _ := Finset.sum_congr rfl (fun j _ => (weighted_refinement A hA P hK _ _
      (Q.partition.1 j).continuous (Q.partition.2.2.1 j).1 (Q.partition.2.2.1 j).2).symm)

/-- Change of a top covector coefficient at a common tangent point. -/
lemma top_coefficient_change_at {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (x y : M)
    (F : E k →ₗ[ℝ] tangentSpace r k M x) (G : E k →ₗ[ℝ] tangentSpace r k M y)
    (hxy : x = y) (B : E k →ₗ[ℝ] E k)
    (h : ∀ w, (F w).val = (G (B w)).val) :
    η x (fun i => F (standardBasis k i)) =
      η y (fun i => G (standardBasis k i)) * B.det := by
  subst y
  have he : F = G.comp B := LinearMap.ext (fun w => Subtype.ext (h w))
  rw [he]
  exact Orientations.alternating_comp (η x) G B

set_option maxHeartbeats 2500000 in
lemma topCoefficient_transition {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (c d : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hkn : k ≤ n) (u : E k) (hu : u ∈ chartOverlap c d) :
    topCoefficient η c ⟨u, hu.1⟩ =
      topCoefficient η d ⟨chartTransition c d u, (EmbeddedChart.transition_mem c d hu).1⟩ *
        (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det := by
  let v := chartTransition c d u
  have hv := (EmbeddedChart.transition_mem c d hu).1
  obtain ⟨B, hB, _⟩ := chart_transition_derivatives c d hr hkn u hu
  have hd : chartDifferential c u = (chartDifferential d v).comp B.toContinuousLinearMap := by
    apply (EmbeddedChart.overlap_uniqueDiff c d u hu).eq
      ((EmbeddedChart.hasDifferential c hr hu.1).mono inter_subset_left)
    exact ((EmbeddedChart.hasDifferential d hr hv).comp u hB
      (fun v hv => (EmbeddedChart.transition_mem c d hv).1)).congr'
      (fun v hv => (d.right_inv _ ⟨(c.map_source hv.1).1, hv.2⟩).symm) hu
  have hp : chartPoint c ⟨u, hu.1⟩ = chartPoint d ⟨v, hv⟩ :=
    Subtype.ext (d.right_inv _ ⟨(c.map_source hu.1).1, hu.2⟩).symm
  rw [hB.fderivWithin (EmbeddedChart.overlap_uniqueDiff c d u hu)]
  exact top_coefficient_change_at η (chartPoint c ⟨u, hu.1⟩) (chartPoint d ⟨v, hv⟩)
    (tangentChartMap c u hu.1)
    (tangentChartMap d v hv) hp B.toLinearEquiv.toLinearMap
    (fun w => DFunLike.congr_fun (congrArg ContinuousLinearMap.toLinearMap hd) w)

lemma sign_mul_value (a : ℝ) : Real.sign a * a = |a| := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h, neg_one_mul]
  · simp
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

def signedCoefficient {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M) :
    ChartCoefficients r k M := fun c u => chartSign o.atPoint c u u.property * topCoefficient η c u

lemma signedCoefficient_continuous {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (c : EmbeddedChart r k n M) :
    Continuous (signedCoefficient o η c) :=
  (o.locally_constant c).continuous.mul (hη c)

lemma signedCoefficient_transition {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (c d : EmbeddedChart r k n M) (u : chartOverlap c d) :
    signedCoefficient o η c ⟨u, u.property.1⟩ =
      signedCoefficient o η d
        ⟨chartTransition c d u, (EmbeddedChart.transition_mem c d u.property).1⟩ *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det| := by
  dsimp only [signedCoefficient]
  rw [Orientations.chartSign_transition o.atPoint c d o.manifold.1 o.manifold.2.1 u
    u.property (EmbeddedChart.transition_mem c d u.property).1,
    topCoefficient_transition η c d o.manifold.1 o.manifold.2.1 u u.property]
  calc
    _ = (chartSign o.atPoint d (chartTransition c d u) _ * topCoefficient η d _) *
      (Real.sign ((fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det) *
        (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det) := by ring
    _ = _ := by rw [sign_mul_value]

lemma signedCoefficient_support {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (c : EmbeddedChart r k n M) (u : c.source) (hu : signedCoefficient o η c u ≠ 0) :
    chartPoint c u ∈ topSupport η := by
  apply subset_closure
  intro hz
  apply hu
  change chartSign o.atPoint c u u.property *
    η (chartPoint c u) (fun i => tangentChartMap c u u.property (standardBasis k i)) = 0
  rw [hz]
  simp


lemma signed_expression {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) {K : Set M} (P : SignedChartPartition o K) :
    (∑ i, (P.sign i).val * coefficientIntegral (localizedTopCoefficient η (P.chart i) (P.weight i))) =
      ∑ i, coefficientIntegral (weightedCoefficient (signedCoefficient o η) (P.chart i) (P.weight i)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [← coefficientIntegral_smul (P.sign i).val
    (ManifoldIntegral.top_coefficients_integrable η hη P.toChartPartition i).2.2]
  congr 1
  funext u
  dsimp only [localizedTopCoefficient, weightedCoefficient, signedCoefficient]
  rw [P.agrees i u]
  ring

/-- Independence for every allowed signed-chart partition, also over larger
compact localization sets. The source's integral is its special case K=L=supp η. -/
theorem oriented_comparison {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) {K L : Set M}
    (P : SignedChartPartition o K) (Q : SignedChartPartition o L)
    (hK : topSupport η ⊆ K) (hL : topSupport η ⊆ L) :
    (∑ i, (P.sign i).val * coefficientIntegral (localizedTopCoefficient η (P.chart i) (P.weight i))) =
      ∑ j, (Q.sign j).val * coefficientIntegral (localizedTopCoefficient η (Q.chart j) (Q.weight j)) := by
  rw [signed_expression o η hη P, signed_expression o η hη Q]
  exact partition_independence (signedCoefficient o η) (signedCoefficient_continuous o η hη)
    (signedCoefficient_transition o η) o.manifold.1 o.manifold.2.1 P.toChartPartition Q.toChartPartition
    (fun c u hu => hK (signedCoefficient_support o η c u hu))
    (fun c u hu => hL (signedCoefficient_support o η c u hu))

theorem oriented_independent {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η)
    (P Q : SignedChartPartition o (topSupport η)) : orientedIntegral η P = orientedIntegral η Q :=
  oriented_comparison o η hη P Q Subset.rfl Subset.rfl

lemma densityCoefficient_continuous {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ)
    (c : EmbeddedChart r k n M) : Continuous (densityCoefficient ρ c) :=
  (hρ.comp (ManifoldIntegral.chartPoint_continuous c)).mul
    ((D04MetricDensity.chartDensity_continuous c hM.1).comp_continuous
      continuous_subtype_val (fun u => u.property))

lemma densityCoefficient_transition {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M)
    (c d : EmbeddedChart r k n M) (u : chartOverlap c d) :
    densityCoefficient ρ c ⟨u, u.property.1⟩ =
      densityCoefficient ρ d
        ⟨chartTransition c d u, (EmbeddedChart.transition_mem c d u.property).1⟩ *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det| :=
  (ManifoldIntegral.density_coefficient_change hM ρ c d u u.property
    (EmbeddedChart.transition_mem c d u.property).1).trans (mul_comm _ _)

/-- No orientation is an input: this applies equally on nonorientable M. -/
theorem density_comparison {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ) {K L : Set M}
    (P : ChartPartition r k M K) (Q : ChartPartition r k M L)
    (hK : tsupport ρ ⊆ K) (hL : tsupport ρ ⊆ L) :
    (∑ i, coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i))) =
      ∑ j, coefficientIntegral (localizedDensityCoefficient ρ (Q.chart j) (Q.weight j)) := by
  apply partition_independence (densityCoefficient ρ) (densityCoefficient_continuous hM ρ hρ)
    (densityCoefficient_transition hM ρ) hM.1 hM.2.1 P Q
  · intro c u hu
    apply hK
    apply subset_tsupport
    exact fun h => hu (by simp [densityCoefficient, h])
  · intro c u hu
    apply hL
    apply subset_tsupport
    exact fun h => hu (by simp [densityCoefficient, h])

theorem density_independent {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ)
    (P Q : ChartPartition r k M (tsupport ρ)) : densityIntegral ρ P = densityIntegral ρ Q :=
  density_comparison hM ρ hρ P Q Subset.rfl Subset.rfl

private def formExpression {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation r k M} {K : Set M}
    (η : TangentTopField r k M) (P : SignedChartPartition o K) : ℝ :=
  ∑ i, (P.sign i).val * coefficientIntegral (localizedTopCoefficient η (P.chart i) (P.weight i))

private def densityExpression {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} {K : Set M}
    (ρ : DensityField M) (P : ChartPartition r k M K) : ℝ :=
  ∑ i, coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i))

lemma topCoefficient_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η ξ : TangentTopField r k M) (c : EmbeddedChart r k n M) (u : c.source) :
    topCoefficient (η + ξ) c u = topCoefficient η c u + topCoefficient ξ c u := rfl

lemma topCoefficient_smul {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (a : ℝ) (η : TangentTopField r k M) (c : EmbeddedChart r k n M) (u : c.source) :
    topCoefficient (a • η) c u = a * topCoefficient η c u := rfl

lemma topCoefficient_weight {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (w : E n → ℝ) (η : TangentTopField r k M) (c : EmbeddedChart r k n M) (u : c.source) :
    topCoefficient (fun x => w x • η x) c u = w (c.toFun u) * topCoefficient η c u := rfl

lemma continuousTopField_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {η ξ : TangentTopField r k M} (hη : ContinuousTopField η) (hξ : ContinuousTopField ξ) :
    ContinuousTopField (η + ξ) := fun c => (hη c).add (hξ c)

lemma continuousTopField_smul {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (a : ℝ) {η : TangentTopField r k M} (hη : ContinuousTopField η) :
    ContinuousTopField (a • η) := fun c => continuous_const.mul (hη c)

lemma continuousTopField_weight {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (w : E n → ℝ) (hw : Continuous w) {η : TangentTopField r k M} (hη : ContinuousTopField η) :
    ContinuousTopField (fun x => w x • η x) := fun c =>
  (hw.comp (c.continuous_toFun.comp_continuous continuous_subtype_val (fun u => u.property))).mul (hη c)

lemma topSupport_add_subset {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η ξ : TangentTopField r k M) : topSupport (η + ξ) ⊆ topSupport η ∪ topSupport ξ := by
  apply closure_minimal _ (isClosed_closure.union isClosed_closure)
  intro x hx
  change η x + ξ x ≠ 0 at hx
  by_cases hη : η x = 0
  · have hξ : ξ x ≠ 0 := by simpa only [hη, zero_add] using hx
    exact Or.inr (subset_closure (s := {x : M | ξ x ≠ 0}) hξ)
  · exact Or.inl (subset_closure hη)

lemma topSupport_weight_subset {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (w : M → ℝ) (η : TangentTopField r k M) :
    topSupport (fun x => w x • η x) ⊆ topSupport η := by
  apply closure_mono
  intro x hx hz
  apply hx
  simp [hz]

lemma parameterIntegral_add {k : ℕ} {S : Set (E k)} (half : Bool)
    (hS : ∃ O : Set (E k), IsOpen O ∧ S = parameterSpace k half ∩ O)
    {f g : S → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hkf : HasCompactSupport f) (hkg : HasCompactSupport g) :
    coefficientIntegral (fun x => f x + g x) = coefficientIntegral f + coefficientIntegral g := by
  classical
  have h := DirectedSubstitution.parameter_integral_sum half hS
    (fun i : Fin 2 => if i = 0 then f else g)
    (fun i => by split_ifs <;> assumption) (fun i => by split_ifs <;> assumption)
  simpa [Fin.sum_univ_two] using h

private lemma formExpression_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation r k M} {K : Set M} (P : SignedChartPartition o K)
    (η ξ : TangentTopField r k M) (hη : ContinuousTopField η) (hξ : ContinuousTopField ξ) :
    formExpression (η + ξ) P = formExpression η P + formExpression ξ P := by
  dsimp only [formExpression]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hcoef : localizedTopCoefficient (η + ξ) (P.chart i) (P.weight i) =
      fun u => localizedTopCoefficient η (P.chart i) (P.weight i) u +
        localizedTopCoefficient ξ (P.chart i) (P.weight i) u := by
    funext u
    simp only [localizedTopCoefficient, topCoefficient_add, mul_add]
  rw [hcoef, parameterIntegral_add (P.chart i).half (P.chart i).source_open
    (ManifoldIntegral.top_coefficients_integrable η hη P.toChartPartition i).1
    (ManifoldIntegral.top_coefficients_integrable ξ hξ P.toChartPartition i).1
    (ManifoldIntegral.top_coefficients_integrable η hη P.toChartPartition i).2.1
    (ManifoldIntegral.top_coefficients_integrable ξ hξ P.toChartPartition i).2.1, mul_add]

private lemma formExpression_smul {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation r k M} {K : Set M} (P : SignedChartPartition o K)
    (a : ℝ) (η : TangentTopField r k M) (hη : ContinuousTopField η) :
    formExpression (a • η) P = a * formExpression η P := by
  dsimp only [formExpression]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcoef : localizedTopCoefficient (a • η) (P.chart i) (P.weight i) =
      fun u => a * localizedTopCoefficient η (P.chart i) (P.weight i) u := by
    funext u
    simp only [localizedTopCoefficient, topCoefficient_smul]
    ring
  rw [hcoef, coefficientIntegral_smul a
    (ManifoldIntegral.top_coefficients_integrable η hη P.toChartPartition i).2.2]
  ring

theorem oriented_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η ξ : TangentTopField r k M)
    (hη : ContinuousTopField η) (hξ : ContinuousTopField ξ)
    (hkη : IsCompact (topSupport η)) (hkξ : IsCompact (topSupport ξ))
    (P : SignedChartPartition o (topSupport η)) (Q : SignedChartPartition o (topSupport ξ))
    (R : SignedChartPartition o (topSupport (η + ξ))) :
    orientedIntegral (η + ξ) R = orientedIntegral η P + orientedIntegral ξ Q := by
  obtain ⟨S⟩ := ManifoldIntegral.signed_partition_exists o _ (hkη.union hkξ)
  have h₀ := oriented_comparison o (η + ξ) (continuousTopField_add hη hξ) R S
    Subset.rfl (topSupport_add_subset η ξ)
  have h₁ := oriented_comparison o η hη P S Subset.rfl subset_union_left
  have h₂ := oriented_comparison o ξ hξ Q S Subset.rfl subset_union_right
  exact h₀.trans ((formExpression_add S η ξ hη hξ).trans (congrArg₂ (· + ·) h₁.symm h₂.symm))

theorem oriented_smul {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (a : ℝ) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (P : SignedChartPartition o (topSupport η))
    (Q : SignedChartPartition o (topSupport (a • η))) :
    orientedIntegral (a • η) Q = a * orientedIntegral η P := by
  exact (oriented_comparison o (a • η) (continuousTopField_smul a hη) Q P
    Subset.rfl (topSupport_weight_subset (fun _ => a) η)).trans (formExpression_smul P a η hη)

/-- Finite localization has no overlap multiplicity: each local form is
integrated using any allowed signed-chart partition of its own support. -/
theorem oriented_finite_localization {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) {m : ℕ} (w : Fin m → E n → ℝ)
    (hw : ∀ j, Continuous (w j)) (hsum : ∀ x : M, η x ≠ 0 → ∑ j, w j x = 1)
    (P : SignedChartPartition o (topSupport η))
    (Q : (j : Fin m) → SignedChartPartition o (topSupport (fun x => w j x • η x))) :
    orientedIntegral η P = ∑ j, orientedIntegral (fun x => w j x • η x) (Q j) := by
  classical
  have hval (j : Fin m) : orientedIntegral (fun x => w j x • η x) (Q j) =
      formExpression (fun x => w j x • η x) P :=
    oriented_comparison o _ (continuousTopField_weight (w j) (hw j) hη) (Q j) P
      Subset.rfl (topSupport_weight_subset _ η)
  rw [Finset.sum_congr rfl (fun j _ => hval j)]
  change formExpression η P = _
  dsimp only [formExpression]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  congr 1
  let F : Fin m → (P.chart i).source → ℝ := fun j =>
    localizedTopCoefficient (fun x => w j x • η x) (P.chart i) (P.weight i)
  have hi j := ManifoldIntegral.top_coefficients_integrable _
    (continuousTopField_weight (w j) (hw j) hη) P.toChartPartition i
  have he : localizedTopCoefficient η (P.chart i) (P.weight i) = fun u => ∑ j, F j u := by
    funext u
    by_cases hz : η (chartPoint (P.chart i) u) = 0
    · have hz' : topCoefficient η (P.chart i) u = 0 := by
        change η (chartPoint (P.chart i) u) _ = 0
        rw [hz]
        rfl
      simp [F, localizedTopCoefficient, topCoefficient_weight, hz']
    · have h := hsum (chartPoint (P.chart i) u) hz
      change ∑ j, w j ((P.chart i).toFun u) = 1 at h
      simp only [F, localizedTopCoefficient, topCoefficient_weight]
      rw [← Finset.mul_sum, ← Finset.sum_mul, h, one_mul]
  rw [he]
  exact DirectedSubstitution.parameter_integral_sum (P.chart i).half (P.chart i).source_open F
    (fun j => (hi j).1) (fun j => (hi j).2.1)

private def reverseSignedPartition {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation r k M} {K : Set M} (P : SignedChartPartition o K) :
    SignedChartPartition (Orientations.reverseOrientation o) K where
  toChartPartition := P.toChartPartition
  sign i := ⟨-(P.sign i).val, by rcases (P.sign i).property with h | h <;> simp [h]⟩
  agrees i u := by
    change chartSign (fun x hx => -o.atPoint x hx) (P.chart i) u u.property = -(P.sign i).val
    rw [Orientations.chartSign_reverse o.atPoint (P.chart i) o.manifold.1 o.manifold.2.1 u u.property,
      P.agrees i u]

theorem oriented_reverse {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (P : SignedChartPartition o (topSupport η)) :
    ∃ p : PositiveManifoldOrientation r k M,
      p.atPoint = (fun x hx => -o.atPoint x hx) ∧
      ∀ Q : SignedChartPartition p (topSupport η), orientedIntegral η Q = -orientedIntegral η P := by
  refine ⟨Orientations.reverseOrientation o, rfl, fun Q => ?_⟩
  rw [oriented_independent _ η hη Q (reverseSignedPartition P)]
  change (∑ i, -(P.sign i).val * _) = -(∑ i, (P.sign i).val * _)
  simp only [reverseSignedPartition, neg_mul, Finset.sum_neg_distrib]

lemma chart_compact_preimage {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) {K : Set M} (hK : IsCompact K)
    (hs : K ⊆ Subtype.val ⁻¹' c.ambient) : IsCompact (chartPoint c ⁻¹' K) := by
  let e := ManifoldIntegral.chartHomeomorph c
  have ht : IsCompact (Subtype.val ⁻¹' K : Set ↥(Subtype.val ⁻¹' c.ambient : Set M)) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff
      (by simpa only [Subtype.range_coe] using hs)).mpr hK
  exact (e.isCompact_preimage).mpr ht

lemma chart_coefficient_compact {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (A : ChartCoefficients r k M) (c : EmbeddedChart r k n M) {K : Set M}
    (hK : IsCompact K) (hs : K ⊆ Subtype.val ⁻¹' c.ambient)
    (hpoints : ∀ u, A c u ≠ 0 → chartPoint c u ∈ K) : HasCompactSupport (A c) := by
  apply (chart_compact_preimage c hK hs).of_isClosed_subset (isClosed_tsupport _) _
  exact closure_minimal (fun u hu => hpoints u hu)
    (hK.isClosed.preimage (ManifoldIntegral.chartPoint_continuous c))

/-- A partition may be chosen entirely in any chart containing the compact set. -/
lemma partition_in_chart {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) {K : Set M} (hK : IsCompact K)
    (c : EmbeddedChart r k n M) (hs : K ⊆ Subtype.val ⁻¹' c.ambient) :
    ∃ P : ChartPartition r k M K, ∀ i, P.chart i = c := by
  classical
  obtain ⟨m, a, p, w, hw, hsub⟩ := FiniteCompactPartition.finite_partition_refined hM K hK
    (fun _ : Unit => (univ : Set M)) (fun _ => isOpen_univ)
    (by intro x hx; exact mem_iUnion.mpr ⟨(), mem_univ x⟩)
    (fun _ => c) (fun x => hs x.property) (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  refine ⟨⟨m, fun _ => c, w, hw.1, hw.2.1, ?_, hw.2.2.2⟩, fun _ => rfl⟩
  intro i
  exact ⟨(hw.2.2.1 i).1, fun x hx => (hsub i hx).2⟩

lemma single_chart_expression {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M)
    (A : ChartCoefficients r k M) (hA : ∀ c, Continuous (A c))
    (hchange : ∀ (c d : EmbeddedChart r k n M) (u : chartOverlap c d),
      A c ⟨u, u.property.1⟩ =
        A d ⟨chartTransition c d u, (EmbeddedChart.transition_mem c d u.property).1⟩ *
        |(fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).det|)
    {K : Set M} (hK : IsCompact K) (P : ChartPartition r k M K)
    (hpoints : ∀ c u, A c u ≠ 0 → chartPoint c u ∈ K)
    (c : EmbeddedChart r k n M) (hs : K ⊆ Subtype.val ⁻¹' c.ambient) :
    ProperIntegrable (A c) ∧
      (∑ i, coefficientIntegral (weightedCoefficient A (P.chart i) (P.weight i))) =
        coefficientIntegral (A c) := by
  refine ⟨DirectedSubstitution.parameter_integrable c.half c.source_open (hA c)
    (chart_coefficient_compact A c hK hs (hpoints c)), ?_⟩
  obtain ⟨Q, hQ⟩ := partition_in_chart hM hK c hs
  rw [partition_independence A hA hchange hM.1 hM.2.1 P Q hpoints hpoints]
  have he : (∑ i, coefficientIntegral (weightedCoefficient A (Q.chart i) (Q.weight i))) =
      ∑ i, coefficientIntegral (weightedCoefficient A c (Q.weight i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hQ i]
  rw [he]
  have hi (i : Fin Q.count) := ManifoldIntegral.localized_coefficient_integrable c
    (Q.weight i) (A c) (Q.partition.1 i).continuous (hA c) (Q.partition.2.2.1 i).1
    (by simpa only [id_eq, hQ i] using (Q.partition.2.2.1 i).2)
  rw [← DirectedSubstitution.parameter_integral_sum c.half c.source_open
    (fun i => weightedCoefficient A c (Q.weight i)) (fun i => (hi i).1) (fun i => (hi i).2.1)]
  congr 1
  funext u
  by_cases hu : A c u = 0
  · simp [weightedCoefficient, hu]
  · obtain ⟨V, _, hKV, hV⟩ := Q.partition.2.2.2.1
    have h := hV (chartPoint c u) (hKV (hpoints c u hu))
    change ∑ i, Q.weight i (c.toFun u) = 1 at h
    simp only [weightedCoefficient]
    rw [← Finset.sum_mul, h, one_mul]

lemma topCoefficient_support {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (c : EmbeddedChart r k n M) (u : c.source)
    (hu : topCoefficient η c u ≠ 0) : chartPoint c u ∈ topSupport η := by
  apply subset_closure
  intro hz
  apply hu
  change η (chartPoint c u) _ = 0
  rw [hz]
  rfl

theorem oriented_single_chart {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (hkη : IsCompact (topSupport η))
    (P : SignedChartPartition o (topSupport η)) (c : EmbeddedChart r k n M)
    (hs : topSupport η ⊆ Subtype.val ⁻¹' c.ambient) (s : PointSign)
    (hsgn : ∀ u : c.source, chartSign o.atPoint c u u.property = s.val) :
    ProperIntegrable (topCoefficient η c) ∧
      orientedIntegral η P = s.val * coefficientIntegral (topCoefficient η c) := by
  have hki := chart_coefficient_compact (topCoefficient η) c hkη hs (topCoefficient_support η c)
  have hi := DirectedSubstitution.parameter_integrable c.half c.source_open (hη c) hki
  refine ⟨hi, ?_⟩
  have h := (single_chart_expression o.manifold (signedCoefficient o η)
    (signedCoefficient_continuous o η hη) (signedCoefficient_transition o η) hkη
    P.toChartPartition (signedCoefficient_support o η) c hs).2
  change formExpression η P = _
  rw [show formExpression η P = ∑ i, coefficientIntegral
    (weightedCoefficient (signedCoefficient o η) (P.chart i) (P.weight i)) from signed_expression o η hη P, h]
  have he : signedCoefficient o η c = fun u => s.val * topCoefficient η c u := by
    funext u
    rw [signedCoefficient, hsgn u]
  rw [he, coefficientIntegral_smul s.val hi]

theorem density_single_chart {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ)
    (hkρ : HasCompactSupport ρ) (P : ChartPartition r k M (tsupport ρ))
    (c : EmbeddedChart r k n M) (hs : tsupport ρ ⊆ Subtype.val ⁻¹' c.ambient) :
    ProperIntegrable (densityCoefficient ρ c) ∧
      densityIntegral ρ P = coefficientIntegral (densityCoefficient ρ c) :=
  single_chart_expression hM (densityCoefficient ρ) (densityCoefficient_continuous hM ρ hρ)
    (densityCoefficient_transition hM ρ) hkρ P
    (fun c u hu => subset_tsupport ρ (fun hz => hu (by simp [densityCoefficient, hz]))) c hs

private lemma densityExpression_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) {K : Set M} (P : ChartPartition r k M K)
    (ρ τ : DensityField M) (hρ : Continuous ρ) (hτ : Continuous τ) :
    densityExpression (ρ + τ) P = densityExpression ρ P + densityExpression τ P := by
  dsimp only [densityExpression]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : localizedDensityCoefficient (ρ + τ) (P.chart i) (P.weight i) =
      fun u => localizedDensityCoefficient ρ (P.chart i) (P.weight i) u +
        localizedDensityCoefficient τ (P.chart i) (P.weight i) u := by
    funext u
    simp only [localizedDensityCoefficient, densityCoefficient, Pi.add_apply, add_mul, mul_add]
  rw [he]
  exact parameterIntegral_add (P.chart i).half (P.chart i).source_open
    (ManifoldIntegral.density_coefficients_integrable hM ρ hρ P i).1
    (ManifoldIntegral.density_coefficients_integrable hM τ hτ P i).1
    (ManifoldIntegral.density_coefficients_integrable hM ρ hρ P i).2.1
    (ManifoldIntegral.density_coefficients_integrable hM τ hτ P i).2.1

private lemma densityExpression_smul {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) {K : Set M} (P : ChartPartition r k M K)
    (a : ℝ) (ρ : DensityField M) (hρ : Continuous ρ) :
    densityExpression (a • ρ) P = a * densityExpression ρ P := by
  dsimp only [densityExpression]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : localizedDensityCoefficient (a • ρ) (P.chart i) (P.weight i) =
      fun u => a * localizedDensityCoefficient ρ (P.chart i) (P.weight i) u := by
    funext u
    simp only [localizedDensityCoefficient, densityCoefficient, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact coefficientIntegral_smul a (ManifoldIntegral.density_coefficients_integrable hM ρ hρ P i).2.2

theorem density_add {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ τ : DensityField M) (hρ : Continuous ρ) (hτ : Continuous τ)
    (hkρ : HasCompactSupport ρ) (hkτ : HasCompactSupport τ)
    (P : ChartPartition r k M (tsupport ρ)) (Q : ChartPartition r k M (tsupport τ))
    (R : ChartPartition r k M (tsupport (ρ + τ))) :
    densityIntegral (ρ + τ) R = densityIntegral ρ P + densityIntegral τ Q := by
  obtain ⟨S⟩ := ManifoldIntegral.chart_partition_exists hM _ (hkρ.union hkτ)
  have h₀ := density_comparison hM (ρ + τ) (hρ.add hτ) R S Subset.rfl (tsupport_add ρ τ)
  have h₁ := density_comparison hM ρ hρ P S Subset.rfl subset_union_left
  have h₂ := density_comparison hM τ hτ Q S Subset.rfl subset_union_right
  exact h₀.trans ((densityExpression_add hM S ρ τ hρ hτ).trans (congrArg₂ (· + ·) h₁.symm h₂.symm))

theorem density_smul {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (a : ℝ) (ρ : DensityField M) (hρ : Continuous ρ)
    (P : ChartPartition r k M (tsupport ρ)) (Q : ChartPartition r k M (tsupport (a • ρ))) :
    densityIntegral (a • ρ) Q = a * densityIntegral ρ P := by
  exact (density_comparison hM (a • ρ) (continuous_const.smul hρ) Q P Subset.rfl
    (tsupport_smul_subset_right (fun _ => a) ρ)).trans (densityExpression_smul hM P a ρ hρ)

theorem density_finite_localization {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (ρ : DensityField M) (hρ : Continuous ρ)
    {m : ℕ} (w : Fin m → E n → ℝ) (hw : ∀ j, Continuous (w j))
    (hsum : ∀ x : M, ρ x ≠ 0 → ∑ j, w j x = 1)
    (P : ChartPartition r k M (tsupport ρ))
    (Q : (j : Fin m) → ChartPartition r k M (tsupport (fun x : M => w j x * ρ x))) :
    densityIntegral ρ P = ∑ j, densityIntegral (fun x : M => w j x * ρ x) (Q j) := by
  classical
  have hcont j : Continuous (fun x : M => w j x * ρ x) :=
    ((hw j).comp continuous_subtype_val).mul hρ
  have hval (j : Fin m) : densityIntegral (fun x : M => w j x * ρ x) (Q j) =
      densityExpression (fun x : M => w j x * ρ x) P :=
    density_comparison hM _ (hcont j) (Q j) P Subset.rfl tsupport_mul_subset_right
  rw [Finset.sum_congr rfl (fun j _ => hval j)]
  change densityExpression ρ P = _
  dsimp only [densityExpression]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let F : Fin m → (P.chart i).source → ℝ := fun j =>
    localizedDensityCoefficient (fun x : M => w j x * ρ x) (P.chart i) (P.weight i)
  have hi j := ManifoldIntegral.density_coefficients_integrable hM _ (hcont j) P i
  have he : localizedDensityCoefficient ρ (P.chart i) (P.weight i) = fun u => ∑ j, F j u := by
    funext u
    by_cases hz : ρ (chartPoint (P.chart i) u) = 0
    · simp [F, localizedDensityCoefficient, densityCoefficient, hz]
    · have h := hsum (chartPoint (P.chart i) u) hz
      change ∑ j, w j ((P.chart i).toFun u) = 1 at h
      simp only [F, localizedDensityCoefficient, densityCoefficient]
      calc
        _ = (P.weight i ((P.chart i).toFun u)) *
            ((∑ j, w j ((P.chart i).toFun u)) * ρ (chartPoint (P.chart i) u) *
              chartDensity (P.chart i) u) := by rw [h, one_mul]
        _ = _ := by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rfl
  rw [he]
  exact DirectedSubstitution.parameter_integral_sum (P.chart i).half (P.chart i).source_open F
    (fun j => (hi j).1) (fun j => (hi j).2.1)

/-- Any finite set containing the support computes the same signed-point integral.
This covers every enumeration, with arbitrary additional zero-valued points. -/
theorem zero_integral_finset {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (f : M → ℝ) (s : Finset M) (hs : support f ⊆ (s : Set M)) :
    zeroIntegral o f = ∑ x ∈ s, (o x).val * f x := by
  apply finsum_eq_finsetSum_of_support_subset
  exact (support_mul_subset_right _ _).trans hs

theorem zero_add {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (o : ZeroManifoldOrientation M)
    (f g : M → ℝ) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    zeroIntegral o (f + g) = zeroIntegral o f + zeroIntegral o g := by
  change (∑ᶠ x, (o x).val * (f x + g x)) = _
  simp_rw [mul_add]
  exact finsum_add_distrib
    ((ManifoldIntegral.zero_support_finite hM f hf).subset (support_mul_subset_right _ _))
    ((ManifoldIntegral.zero_support_finite hM g hg).subset (support_mul_subset_right _ _))

theorem zero_smul {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (a : ℝ) (f : M → ℝ) : zeroIntegral o (a • f) = a * zeroIntegral o f := by
  change (∑ᶠ x, (o x).val * (a * f x)) = a * (∑ᶠ x, (o x).val * f x)
  simp_rw [mul_left_comm ((o _).val) a]
  exact (mul_finsum _ a).symm

theorem zero_reverse {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M) (f : M → ℝ) :
    ∃ p : ZeroManifoldOrientation M, (∀ x, (p x).val = -(o x).val) ∧
      zeroIntegral p f = -zeroIntegral o f := by
  let p : ZeroManifoldOrientation M := fun x =>
    ⟨-(o x).val, by rcases (o x).property with h | h <;> simp [h]⟩
  refine ⟨p, fun _ => rfl, ?_⟩
  change (∑ᶠ x, -(o x).val * f x) = -(∑ᶠ x, (o x).val * f x)
  simp only [neg_mul, finsum_neg_distrib]

theorem zero_single_point {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (f : M → ℝ) (x : M) (hs : support f ⊆ {x}) : zeroIntegral o f = (o x).val * f x := by
  classical
  simpa only [Finset.sum_singleton] using zero_integral_finset o f {x} (by simpa using hs)

theorem zero_finite_localization {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (o : ZeroManifoldOrientation M)
    (f : M → ℝ) (hf : HasCompactSupport f) {m : ℕ} (w : Fin m → M → ℝ)
    (hsum : ∀ x, f x ≠ 0 → ∑ j, w j x = 1) :
    zeroIntegral o f = ∑ j, zeroIntegral o (fun x => w j x * f x) := by
  classical
  have hfin := ManifoldIntegral.zero_support_finite hM f hf
  let s := hfin.toFinset
  have hs : support f ⊆ (s : Set M) := hfin.coe_toFinset.ge
  rw [zero_integral_finset o f s hs]
  simp_rw [zero_integral_finset o _ s ((support_mul_subset_right _ _).trans hs)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f x = 0
  · simp [hx]
  · rw [← Finset.mul_sum, ← Finset.sum_mul, hsum x hx, one_mul]

lemma coefficientIntegral_zero_dimension {S : Set (E 0)} (f : S → ℝ) :
    coefficientIntegral f = zeroExtension f 0 :=
  (Darboux.zero_dimension _ (zeroExtension f)).2.2.1

/-- A zero-dimensional chart contributes exactly the weighted value of its
single point; an empty chart contributes zero. -/
lemma zero_chart_density {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (ρ : DensityField M) (c : EmbeddedChart r 0 n M) (w : E n → ℝ)
    (hs : tsupport (fun x : M => w x) ⊆ Subtype.val ⁻¹' c.ambient) :
    coefficientIntegral (localizedDensityCoefficient ρ c w) = ∑ᶠ x : M, w x * ρ x := by
  classical
  rw [coefficientIntegral_zero_dimension]
  by_cases h0 : (0 : E 0) ∈ c.source
  · let p := chartPoint c ⟨0, h0⟩
    have hoff (x : M) (hx : x ≠ p) : w x = 0 := by
      by_contra hn
      have hxambient := hs (subset_tsupport (fun x : M => w x) hn)
      have he := c.right_inv x ⟨x.property, hxambient⟩
      rw [Subsingleton.elim (c.invFun x) 0] at he
      apply hx
      exact Subtype.ext he.symm
    have hc : chartDensity c 0 = 1 := by
      rw [← D04MetricDensity.density_chart c 0 h0]
      exact D04MetricDensity.density_zero _ _
    rw [zeroExtension_apply _ ⟨0, h0⟩]
    change w (c.toFun 0) * (ρ p * chartDensity c 0) = _
    rw [hc, mul_one, finsum_eq_single _ p (fun x hx => by rw [hoff x hx, zero_mul])]
    rfl
  · have hz (x : M) : w x = 0 := by
      by_contra hn
      have hxambient := hs (subset_tsupport (fun x : M => w x) hn)
      have hxsource := c.map_target ⟨x.property, hxambient⟩
      exact h0 ((Subsingleton.elim (c.invFun x) 0) ▸ hxsource)
    rw [zeroExtension_of_not_mem _ h0]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    rw [hz x, zero_mul]

/-- In every zero-manifold, including a noncompact one, a compactly supported
density is integrated by the finite sum of its point values. -/
theorem density_zero_sum {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (ρ : DensityField M) (hkρ : HasCompactSupport ρ)
    (P : ChartPartition r 0 M (tsupport ρ)) : densityIntegral ρ P = ∑ᶠ x : M, ρ x := by
  classical
  have hf := ManifoldIntegral.zero_support_finite hM ρ hkρ
  let s := hf.toFinset
  have hs : support ρ ⊆ (s : Set M) := hf.coe_toFinset.ge
  have hsum (x : M) (hx : ρ x ≠ 0) : ∑ i, P.weight i x = 1 := by
    obtain ⟨V, _, hV, hsum⟩ := P.partition.2.2.2.1
    exact hsum x (hV (subset_tsupport ρ hx))
  change (∑ i, coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i))) = _
  have hc (i : Fin P.count) := zero_chart_density ρ (P.chart i) (P.weight i)
    (P.partition.2.2.1 i).2
  rw [Finset.sum_congr rfl (fun i _ => hc i)]
  have hi (i : Fin P.count) : (∑ᶠ x : M, P.weight i x * ρ x) = ∑ x ∈ s, P.weight i x * ρ x :=
    finsum_eq_finsetSum_of_support_subset (fun x : M => P.weight i x * ρ x)
      ((support_mul_subset_right _ _).trans hs)
  rw [Finset.sum_congr rfl (fun i _ => hi i), finsum_eq_finsetSum_of_support_subset ρ hs,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_mul, hsum x (hf.mem_toFinset.mp hx), one_mul]

/-- The compact signed-point convention agrees with the same integral on all
compactly supported forms on an arbitrary discrete manifold. -/
theorem zero_compact_agrees {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r 0 M) (hc : IsCompact M)
    (o : ZeroManifoldOrientation M) (f : M → ℝ) :
    ∃ h : M.Finite, zeroIntegral o f = compactZeroIntegral h o f :=
  ManifoldIntegral.compact_zero_agrees hM hc o f

/-- The arbitrary single-chart rule retains the locally constant sign inside
the coefficient integral. In particular the chart need not be connected. -/
theorem oriented_single_chart_variable_sign {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation r k M) (η : TangentTopField r k M)
    (hη : ContinuousTopField η) (hkη : IsCompact (topSupport η))
    (P : SignedChartPartition o (topSupport η)) (c : EmbeddedChart r k n M)
    (hs : topSupport η ⊆ Subtype.val ⁻¹' c.ambient) :
    ProperIntegrable (fun u : c.source => chartSign o.atPoint c u u.property * topCoefficient η c u) ∧
      orientedIntegral η P = coefficientIntegral
        (fun u : c.source => chartSign o.atPoint c u u.property * topCoefficient η c u) := by
  have h := single_chart_expression o.manifold (signedCoefficient o η)
    (signedCoefficient_continuous o η hη) (signedCoefficient_transition o η) hkη
    P.toChartPartition (signedCoefficient_support o η) c hs
  exact ⟨h.1, (signed_expression o η hη P).trans h.2⟩

/-- The reversal law for any presentation of the reversed orientation. -/
theorem oriented_reverse_comparison {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o p : PositiveManifoldOrientation r k M)
    (hp : p.atPoint = fun x hx => -o.atPoint x hx)
    (η : TangentTopField r k M) (hη : ContinuousTopField η)
    (P : SignedChartPartition o (topSupport η)) (Q : SignedChartPartition p (topSupport η)) :
    orientedIntegral η Q = -orientedIntegral η P := by
  obtain ⟨q, hq, hval⟩ := oriented_reverse o η hη P
  have he : p = q := by
    have ha := hp.trans hq.symm
    cases p
    cases q
    cases ha
    rfl
  subst q
  exact hval Q

end D04.ManifoldIntegralIndependence
