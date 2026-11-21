import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Titchmarsh
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ProperSupportConvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionRegularization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardySupportBridge
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions Topology Pointwise
namespace ExpandedFA.PartIV.Titchmarsh
open ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜]

lemma support_nonempty {u : LineDistribution 𝕜} (hu : u ≠ 0) :
    (distributionSupport u).Nonempty := by
  by_contra hn
  exact hu ((ProperSupportConvolution.zero_support 𝕜 1 u).mp
    (not_nonempty_iff_eq_empty.mp hn))

lemma orientedSupport_compact {u : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (s : ℝ) :
    IsCompact (orientedSupport u s) :=
  hu.image (continuous_const.mul (continuous_apply 0))

lemma orientedSupport_nonempty {u : LineDistribution 𝕜} (hu : u ≠ 0) (s : ℝ) :
    (orientedSupport u s).Nonempty := (support_nonempty hu).image _

lemma lowerSupportBound_iff {u : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hn : u ≠ 0) (s c : ℝ) :
    LowerSupportBound u s c ↔ c ≤ orientedEndpoint u s := by
  have hm := (orientedSupport_compact hu s).isLeast_sInf (orientedSupport_nonempty hn s)
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := hm.1
    rw [orientedEndpoint, ← he]
    exact h x hx
  · intro h x hx
    exact h.trans (hm.2 ⟨x, hx, rfl⟩)

lemma orientedEndpoint_one (u : LineDistribution 𝕜) :
    orientedEndpoint u 1 = leftEndpoint u := by
  simp [orientedEndpoint, orientedSupport, leftEndpoint, realSupport]

lemma realSupport_compact {u : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) : IsCompact (realSupport u) :=
  hu.image (continuous_apply 0)

lemma realSupport_nonempty {u : LineDistribution 𝕜} (hu : u ≠ 0) :
    (realSupport u).Nonempty := (support_nonempty hu).image _

lemma orientedEndpoint_neg_one {u : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hn : u ≠ 0) :
    orientedEndpoint u (-1) = -rightEndpoint u := by
  have hmin := (orientedSupport_compact hu (-1)).isLeast_sInf
    (orientedSupport_nonempty hn (-1))
  have hmax := (realSupport_compact hu).isGreatest_sSup (realSupport_nonempty hn)
  obtain ⟨x, hx, he⟩ := hmin.1
  obtain ⟨y, hy, hf⟩ := hmax.1
  have hxy := hmin.2 ⟨y, hy, rfl⟩
  have hyx := hmax.2 ⟨x, hx, rfl⟩
  change -1 * x 0 = orientedEndpoint u (-1) at he
  change y 0 = rightEndpoint u at hf
  change orientedEndpoint u (-1) ≤ -1 * y 0 at hxy
  change x 0 ≤ rightEndpoint u at hyx
  linarith

lemma vanishesBefore_iff (u : LineDistribution 𝕜) (c : ℝ) :
    VanishesBefore u c ↔ LowerSupportBound u 1 c := by
  have hopen : IsOpen {x : Domain 1 | x 0 < c} :=
    isOpen_lt (continuous_apply 0) continuous_const
  constructor
  · intro h x hx
    simp only [one_mul]
    by_contra hn
    apply hx.2
    exact ⟨{x : Domain 1 | x 0 < c}, ⟨hopen, subset_univ _, h⟩, lt_of_not_ge hn⟩
  · intro h φ hφ
    apply (support_vanishing 𝕜 1 ⊤ u).2.2
    intro x hx
    by_contra hn
    have hs : x ∈ distributionSupport u := ⟨mem_univ x, hn⟩
    have hb := h x hs
    simp only [one_mul] at hb
    exact (not_lt_of_ge hb) (hφ hx)

lemma vanishesBefore_iff_le {u : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hn : u ≠ 0) (c : ℝ) :
    VanishesBefore u c ↔ c ≤ leftEndpoint u := by
  rw [vanishesBefore_iff, lowerSupportBound_iff hu hn, orientedEndpoint_one]

lemma convolution_support_compact {u v w : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hv : IsCompact (distributionSupport v))
    (hw : IsProperConvolution u v w) : IsCompact (distributionSupport w) := by
  have hs : IsCompact (distributionSupport u + distributionSupport v) := by
    rw [← add_image_prod]
    exact (hu.prod hv).image (continuous_fst.add continuous_snd)
  exact hs.of_isClosed_subset (ProperSupportConvolution.support_closed 𝕜 1 w)
    (ProperSupportConvolution.convolution_support 𝕜 1 u v w hw)

lemma convolution_lowerSupportBound {u v w : LineDistribution 𝕜} {s a b : ℝ}
    (hw : IsProperConvolution u v w)
    (ha : LowerSupportBound u s a) (hb : LowerSupportBound v s b) :
    LowerSupportBound w s (a + b) := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    ProperSupportConvolution.convolution_support 𝕜 1 u v w hw hx
  have hya := ha y hy
  have hzb := hb z hz
  simpa only [Pi.add_apply, mul_add] using add_le_add hya hzb

/-- The complex-valued smoothing used for either scalar field and either
orientation of the line. `RCLike.map` is real-linear. -/
def smoothDensity (u : LineDistribution 𝕜)
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) (s : ℝ) (t : ℝ) : ℂ :=
  RCLike.map 𝕜 ℂ (distributionConvolution u φ (fun _ => s * t))

/-- The one-distribution approximation property. It asserts that
small smoothings can detect the lower endpoint; it makes no assertion about
the endpoint of a convolution of two distributions. -/
def SmoothingDetection : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u : LineDistribution 𝕜), IsCompact (distributionSupport u) → u ≠ 0 →
    ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ δ : ℝ, 0 < δ →
    ∃ φ : Tests 𝕜 (⊤ : Opens (Domain 1)),
      (∀ x ∈ tsupport φ, |x 0| ≤ δ) ∧
      Integrable (smoothDensity u φ s) ∧ MemLp (smoothDensity u φ s) 2 volume ∧
      ¬ (smoothDensity u φ s =ᵐ[volume] 0) ∧
      ∃ a : ℝ, HardySupportBridge.IsLeftEndpoint (smoothDensity u φ s) a ∧
        a < orientedEndpoint u s + δ

/-- The two-distribution compatibility property. A lower support
bound for the distribution convolution gives the elementary support bound for
the convolution of its smoothings. Equality of endpoints is not an input. -/
def SmoothingConvolutionBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (u v w : LineDistribution 𝕜),
    IsCompact (distributionSupport u) → IsCompact (distributionSupport v) →
    IsProperConvolution u v w →
    ∀ (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) (δ η : ℝ),
      0 < δ → 0 < η →
      (∀ x ∈ tsupport φ, |x 0| ≤ δ) →
      (∀ x ∈ tsupport ψ, |x 0| ≤ η) →
      ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ c : ℝ, LowerSupportBound w s c →
        HardySupportBridge.SupportedAbove
          (HardySupportBridge.convolution (smoothDensity u φ s) (smoothDensity v ψ s))
          (c - δ - η)

/-- The analytic assembly: endpoint detection and convolution compatibility,
together with the accepted Hardy theorem, rule out every extra lower bound. -/
theorem lower_bound_addition_of_smoothing
    (hd : SmoothingDetection) (hc : SmoothingConvolutionBound)
    {u v w : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hv : IsCompact (distributionSupport v))
    (hun : u ≠ 0) (hvn : v ≠ 0) (hw : IsProperConvolution u v w)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (c : ℝ) :
    LowerSupportBound w s c ↔ c ≤ orientedEndpoint u s + orientedEndpoint v s := by
  constructor
  · intro hbound
    by_contra hle
    have hgap : 0 < c - (orientedEndpoint u s + orientedEndpoint v s) := by linarith
    let δ := (c - (orientedEndpoint u s + orientedEndpoint v s)) / 4
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨φ, hφ, hfi, hf2, hfn, a, ha, hax⟩ := hd 𝕜 u hu hun s hs δ hδ
    obtain ⟨ψ, hψ, hgi, hg2, hgn, b, hb, hbx⟩ := hd 𝕜 v hv hvn s hs δ hδ
    obtain ⟨_, _, hab⟩ := HardySupportBridge.endpoint_addition
      (smoothDensity u φ s) (smoothDensity v ψ s) hfi hgi hf2 hg2 hfn hgn a b ha hb
    have hconv := hc 𝕜 u v w hu hv hw φ ψ δ δ hδ hδ hφ hψ s hs c hbound
    have hle := (hab (c - δ - δ)).mp hconv
    dsimp only [δ] at hax hbx hle
    linarith
  · intro hle
    have huBound := (lowerSupportBound_iff hu hun s (orientedEndpoint u s)).mpr le_rfl
    have hvBound := (lowerSupportBound_iff hv hvn s (orientedEndpoint v s)).mpr le_rfl
    intro x hx
    exact hle.trans (convolution_lowerSupportBound hw huBound hvBound x hx)

/-- Assemble the endpoint theorem from endpoint detection and compatibility.
Both analytic properties are proved below from the original distributions. -/
theorem convolution_endpoints_of_smoothing
    (hd : SmoothingDetection) (hc : SmoothingConvolutionBound) : Spec.ConvolutionEndpoints := by
  intro 𝕜 _ u v w hu hv hun hvn hw
  have he := lower_bound_addition_of_smoothing hd hc hu hv hun hvn hw
  have hwn : w ≠ 0 := by
    intro hzero
    have hb : LowerSupportBound w 1
        (orientedEndpoint u 1 + orientedEndpoint v 1 + 1) := by
      intro x hx
      rw [(ProperSupportConvolution.zero_support 𝕜 1 w).mpr hzero] at hx
      exact hx.elim
    have h := (he 1 (Or.inl rfl) _).mp hb
    linarith
  have hwc := convolution_support_compact hu hv hw
  have hlo : orientedEndpoint w 1 = orientedEndpoint u 1 + orientedEndpoint v 1 := by
    apply le_antisymm
    · exact (he 1 (Or.inl rfl) _).mp
        ((lowerSupportBound_iff hwc hwn 1 _).mpr le_rfl)
    · exact (lowerSupportBound_iff hwc hwn 1 _).mp
        ((he 1 (Or.inl rfl) _).mpr le_rfl)
  have hhi : orientedEndpoint w (-1) = orientedEndpoint u (-1) + orientedEndpoint v (-1) := by
    apply le_antisymm
    · exact (he (-1) (Or.inr rfl) _).mp
        ((lowerSupportBound_iff hwc hwn (-1) _).mpr le_rfl)
    · exact (lowerSupportBound_iff hwc hwn (-1) _).mp
        ((he (-1) (Or.inr rfl) _).mpr le_rfl)
  simp only [orientedEndpoint_one] at hlo
  rw [orientedEndpoint_neg_one hwc hwn, orientedEndpoint_neg_one hu hun,
    orientedEndpoint_neg_one hv hvn] at hhi
  exact ⟨hwn, hwc, hlo, by linarith⟩

/-- The noncancellation statement is a consequence of the full endpoint
identity, not of the weaker support inclusion. -/
theorem no_extra_initial_interval_of_endpoints
    (ht : Spec.ConvolutionEndpoints) : Spec.NoExtraInitialInterval := by
  intro 𝕜 _ u v w hu hv hun hvn hw c
  obtain ⟨hwn, hwc, hlo, _⟩ := ht 𝕜 u v w hu hv hun hvn hw
  rw [vanishesBefore_iff_le hwc hwn, hlo]

theorem convolution_existence_of_endpoints
    (ht : Spec.ConvolutionEndpoints) : Spec.ConvolutionExistence := by
  intro 𝕜 _ u v hu hv hun hvn
  have hc := ProperSupportConvolution.compact_distribution_suffices 𝕜 1 u v (Or.inl hu)
  obtain ⟨w, hw, _⟩ := ProperSupportConvolution.convolution_existence 𝕜 1 u v hc
  obtain ⟨hwn, _, hlo, hhi⟩ := ht 𝕜 u v w hu hv hun hvn hw
  exact ⟨w, hw, hwn, hlo, hhi⟩

/-- A compact distribution smoothed by a test has support in the ordinary
sum of the two supports. This follows from locality, without Titchmarsh. -/
lemma distributionConvolution_tsupport_subset
    {u : LineDistribution 𝕜} (hu : IsCompact (distributionSupport u))
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    tsupport (distributionConvolution u φ) ⊆ distributionSupport u + tsupport φ := by
  have hc : IsCompact (distributionSupport u + tsupport φ) := by
    rw [← add_image_prod]
    exact (hu.prod φ.hasCompactSupport).image (continuous_fst.add continuous_snd)
  apply closure_minimal _ hc.isClosed
  intro x hx
  by_contra hn
  let V : Set (Domain 1) := (fun y => x - y) ⁻¹' (tsupport φ)ᶜ
  have hV : IsOpen V := isClosed_closure.isOpen_compl.preimage
    (continuous_const.sub continuous_id)
  have hS : distributionSupport u ⊆ V := by
    intro y hy hxy
    apply hn
    exact ⟨y, hy, x-y, hxy, by abel_nf⟩
  have hz := pairing_locality 𝕜 1 ⊤ u (reflectedTranslate φ x) 0 V hV hS (by
    intro y hy
    change φ (x-y) = 0
    exact image_eq_zero_of_notMem_tsupport hy)
  exact hx (by simpa only [distributionConvolution_apply, map_zero] using hz)

lemma distributionConvolution_hasCompactSupport
    {u : LineDistribution 𝕜} (hu : IsCompact (distributionSupport u))
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    HasCompactSupport (distributionConvolution u φ) := by
  have hc : IsCompact (distributionSupport u + tsupport φ) := by
    rw [← add_image_prod]
    exact (hu.prod φ.hasCompactSupport).image (continuous_fst.add continuous_snd)
  exact hc.of_isClosed_subset isClosed_closure (distributionConvolution_tsupport_subset hu φ)

lemma scalarMap_ne_zero {z : 𝕜} (hz : z ≠ 0) : RCLike.map 𝕜 ℂ z ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  apply hz
  apply RCLike.ext
  · simpa [RCLike.map_apply] using hr
  · simpa [RCLike.map_apply] using hi

lemma smoothDensity_continuous (u : LineDistribution 𝕜)
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) (s : ℝ) :
    Continuous (smoothDensity u φ s) :=
  (RCLike.map 𝕜 ℂ).continuous.comp ((distributionConvolution_smooth u φ).continuous.comp
    (continuous_pi (fun _ => continuous_const.mul continuous_id)))

lemma smoothDensity_hasCompactSupport {u : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u))
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    HasCompactSupport (smoothDensity u φ s) := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  let K := (fun x : Domain 1 => s * x 0) '' tsupport (distributionConvolution u φ)
  have hK : IsCompact K := (distributionConvolution_hasCompactSupport hu φ).image
    (continuous_const.mul (continuous_apply 0))
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro t ht
  refine ⟨fun _ => s*t, ?_, ?_⟩
  · apply subset_tsupport
    intro hz
    apply ht
    change RCLike.map 𝕜 ℂ (distributionConvolution u φ (fun _ => s*t)) = 0
    rw [hz, map_zero]
  · change s * (s*t) = t
    rw [← mul_assoc, hss, one_mul]

/-- Every neighborhood of a point of the actual support contains a test
which the distribution does not annihilate. -/
lemma exists_test_ne_zero_near_support {u : LineDistribution 𝕜}
    {x : Domain 1} (hx : x ∈ distributionSupport u)
    {V : Set (Domain 1)} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ θ : Tests 𝕜 (⊤ : Opens (Domain 1)), tsupport θ ⊆ V ∧ u θ ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hx.2 ⟨V, ⟨hV, subset_univ _, hn⟩, hxV⟩

/-- A continuous compactly supported function nonzero at t has a finite
essential left endpoint no greater than t. -/
lemma continuous_compact_endpoint {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {t : ℝ} (ht : f t ≠ 0) :
    Integrable f ∧ MemLp f 2 volume ∧ ¬ (f =ᵐ[volume] 0) ∧
      ∃ a : ℝ, HardySupportBridge.IsLeftEndpoint f a ∧ a ≤ t := by
  have hne : ¬ (f =ᵐ[volume] 0) := by
    intro heq
    exact ht (congrFun (MeasureTheory.Measure.eq_of_ae_eq heq hf continuous_const) t)
  have h2 : MemLp f 2 volume := hf.memLp_of_hasCompactSupport hfc
  have hm := hfc.isLeast_sInf ⟨t, subset_tsupport f ht⟩
  have hb : HardySupportBridge.SupportedAbove f (sInf (tsupport f)) := by
    filter_upwards with x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hmem => (not_le_of_gt hx) (hm.2 hmem)
  obtain ⟨a, _, _, ha⟩ := HardySupportBridge.endpoint_coefficient f h2 hne _ hb
  refine ⟨hf.integrable_of_hasCompactSupport hfc, h2, hne, _, ha, ?_⟩
  by_contra hn
  have htlt : t < sInf (tsupport f) + a / (2 * Real.pi) := lt_of_not_ge hn
  have heq : f =ᵐ[volume.restrict (Iio (sInf (tsupport f) + a / (2 * Real.pi)))] 0 :=
    (ae_restrict_iff' measurableSet_Iio).mpr ((ha _).mpr le_rfl)
  exact ht ((MeasureTheory.Measure.eqOn_open_of_ae_eq heq isOpen_Iio hf.continuousOn
    continuous_const.continuousOn) htlt)

/-- Arbitrarily small tests detect an actual endpoint of a compact
nonzero distribution. No convolution endpoint theorem enters this proof. -/
theorem smoothing_detection : SmoothingDetection := by
  intro 𝕜 _ u hu hun s hs δ hδ
  have hm := (orientedSupport_compact hu s).isLeast_sInf (orientedSupport_nonempty hun s)
  obtain ⟨x, hx, hxe⟩ := hm.1
  have hV : IsOpen {y : Domain 1 | |x 0 - y 0| < δ} :=
    isOpen_lt ((continuous_const.sub (continuous_apply 0)).abs) continuous_const
  obtain ⟨θ, hθ, hθn⟩ := exists_test_ne_zero_near_support hx hV (by simpa using hδ)
  let φ := reflectedTranslate θ x
  have hφ : ∀ z ∈ tsupport φ, |z 0| ≤ δ := by
    intro z hz
    have hz' : x - z ∈ tsupport θ :=
      tsupport_comp_subset_preimage θ (continuous_const.sub continuous_id) hz
    have hh : |x 0 - (x-z) 0| ≤ δ := (hθ hz').le
    simpa only [Pi.sub_apply, sub_sub_cancel] using hh
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hxx : (fun _ : Fin 1 => s * orientedEndpoint u s) = x := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change s * orientedEndpoint u s = x 0
    change s * (sInf (orientedSupport u s)) = x 0
    rw [← hxe, ← mul_assoc, hss, one_mul]
  have hrt : reflectedTranslate φ x = θ := by
    ext y
    change θ (x - (x-y)) = θ y
    rw [sub_sub_cancel]
  have hn : smoothDensity u φ s (orientedEndpoint u s) ≠ 0 := by
    apply scalarMap_ne_zero
    change u (reflectedTranslate φ (fun _ => s * orientedEndpoint u s)) ≠ 0
    rw [hxx, hrt]
    exact hθn
  obtain ⟨hfi, hf2, hfn, a, ha, hax⟩ := continuous_compact_endpoint
    (smoothDensity_continuous u φ s) (smoothDensity_hasCompactSupport hu φ hs) hn
  exact ⟨φ, hφ, hfi, hf2, hfn, a, ha, lt_of_le_of_lt hax (lt_add_of_pos_right _ hδ)⟩

/-- The distribution represented by a continuous density has no support
outside the closed support of that density. -/
lemma regularDistribution_support_subset {f : Domain 1 → 𝕜} (hf : Continuous f) :
    distributionSupport (regularDistribution volume f : LineDistribution 𝕜) ⊆ tsupport f := by
  intro x hx
  by_contra hn
  apply hx.2
  refine ⟨(tsupport f)ᶜ, ⟨isClosed_closure.isOpen_compl, subset_univ _, ?_⟩, hn⟩
  intro θ hθ
  rw [regularDistribution_apply volume f (hf.locallyIntegrable.locallyIntegrableOn _)]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  change f y * θ y = 0
  by_cases hy : θ y = 0
  · rw [hy, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport (hθ (subset_tsupport θ hy)), zero_mul]

lemma regularDistribution_support_compact {f : Domain 1 → 𝕜}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    IsCompact (distributionSupport (regularDistribution volume f : LineDistribution 𝕜)) :=
  hfc.of_isClosed_subset (ProperSupportConvolution.support_closed 𝕜 1 _)
    (regularDistribution_support_subset hf)

/-- Convolution of two tests as an actual compactly supported smooth test. -/
def convolutionTest (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    Tests 𝕜 (⊤ : Opens (Domain 1)) where
  toFun := distributionConvolution (regularDistribution volume φ) ψ
  contDiff' := distributionConvolution_smooth _ _
  hasCompactSupport' := distributionConvolution_hasCompactSupport
    (regularDistribution_support_compact φ.continuous φ.hasCompactSupport) ψ
  tsupport_subset' := subset_univ _

lemma convolutionTest_apply (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) (x : Domain 1) :
    convolutionTest φ ψ x = ∫ y, φ y * ψ (x-y) := by
  exact regularDistribution_apply volume φ (φ.continuous.locallyIntegrable.locallyIntegrableOn _)
    (reflectedTranslate ψ x)

lemma convolutionTest_tsupport (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    tsupport (convolutionTest φ ψ) ⊆ tsupport φ + tsupport ψ :=
  (distributionConvolution_tsupport_subset
    (regularDistribution_support_compact φ.continuous φ.hasCompactSupport) ψ).trans
      (add_subset_add (regularDistribution_support_subset φ.continuous) Subset.rfl)

/-- The transposed smoothing kernel. Its derivatives fall on the outer test. -/
def transposeConvolutionTest (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    Tests 𝕜 (⊤ : Opens (Domain 1)) := convolutionTest (reflectedTranslate φ 0) ψ

lemma transposeConvolutionTest_partial (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1)))
    (w : List (Fin 1)) (y : Domain 1) :
    partialFunction w (transposeConvolutionTest φ ψ) y =
      ∫ z, φ z * partialFunction w ψ (z+y) := by
  change partialFunction w (distributionConvolution
    (regularDistribution volume (reflectedTranslate φ 0)) ψ) y = _
  rw [partialFunction_distributionConvolution]
  change convolutionTest (reflectedTranslate φ 0) (testPartialCLM w ψ) y = _
  rw [convolutionTest_apply, ← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with z
  simp only [reflectedTranslate_apply, sub_neg_eq_add, zero_add]
  rw [testPartial_formula]
  congr 2
  abel

lemma transposeConvolutionTest_apply (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1)))
    (y : Domain 1) : transposeConvolutionTest φ ψ y = ∫ z, φ z * ψ (z+y) :=
  transposeConvolutionTest_partial φ ψ [] y

/-- Moving a distribution across the scalar parameter integral is justified
by its finite-jet factorization on a common compact support. -/
theorem distributionConvolution_transpose (u : LineDistribution 𝕜)
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    (∫ x, distributionConvolution u φ x * ψ x) = u (transposeConvolutionTest φ ψ) := by
  obtain ⟨K₀, hK₀⟩ := reflectedTranslate_common_support φ (tsupport ψ) ψ.hasCompactSupport
  let K : Compacts (Domain 1) :=
    ⟨(K₀ : Set (Domain 1)) ∪ tsupport (transposeConvolutionTest φ ψ),
      K₀.isCompact.union (transposeConvolutionTest φ ψ).hasCompactSupport⟩
  have hθ : tsupport (transposeConvolutionTest φ ψ) ⊆ K := subset_union_right
  have hK : ∀ x ∈ tsupport ψ, tsupport (reflectedTranslate φ x) ⊆ K :=
    fun x hx => (hK₀ x hx).trans subset_union_left
  obtain ⟨m, L, hL⟩ := distribution_finiteJet_factorization u K
  rw [distributionConvolution_transpose_finiteJet u φ ψ K hK m L hL]
  let θ : Step 𝕜 K := ContDiffMapSupportedIn.of_support_subset
    (transposeConvolutionTest φ ψ).contDiff ((subset_tsupport _).trans hθ)
  have hjet : integratedReflectedJet φ ψ m = finiteJetMap K m θ := by
    ext a y
    rw [integratedReflectedJet_apply_by_parts, finiteJetMap_apply]
    change (∫ z, φ z * iteratedFDeriv ℝ a.1.val ψ (z+y)
      (fun j => coordinateVector (a.2 j))) =
      iteratedFDeriv ℝ a.1.val (transposeConvolutionTest φ ψ) y
        (fun j => coordinateVector (a.2 j))
    simp_rw [← partialFunction_ofFn _ a.2 ψ ψ.contDiff]
    rw [← partialFunction_ofFn _ a.2 (transposeConvolutionTest φ ψ)
      (transposeConvolutionTest φ ψ).contDiff, transposeConvolutionTest_partial]
  rw [hjet, hL θ]
  rfl

/-- For a continuous density, distributional and closed pointwise supports
agree. The reverse inclusion uses test-function detection of local integrals. -/
lemma regularDistribution_support_eq {f : Domain 1 → 𝕜} (hf : Continuous f) :
    distributionSupport (regularDistribution volume f : LineDistribution 𝕜) = tsupport f := by
  apply Subset.antisymm (regularDistribution_support_subset hf)
  apply closure_minimal _ (ProperSupportConvolution.support_closed 𝕜 1 _)
  intro x hx
  by_contra hn
  let u : LineDistribution 𝕜 := regularDistribution volume f
  have hxV : x ∈ vanishingRegion u := by
    simpa only [distributionSupport, Opens.coe_top, Set.mem_sdiff, mem_univ, true_and, not_not] using hn
  have hV := (support_vanishing 𝕜 1 ⊤ u).1
  have hae : ∀ᵐ y ∂(volume : Measure (Domain 1)), y ∈ vanishingRegion u → f y = 0 := by
    apply hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrable.locallyIntegrableOn _)
    intro g hg hgc hgt
    let θ : Tests 𝕜 (⊤ : Opens (Domain 1)) :=
      { toFun := fun y => (g y : 𝕜)
        contDiff' := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hg
        hasCompactSupport' := hgc.comp_left (by simp)
        tsupport_subset' := subset_univ _ }
    have hθ : tsupport θ ⊆ vanishingRegion u :=
      (tsupport_comp_subset (RCLike.ofReal_zero (K := 𝕜)) g).trans hgt
    have hz := (support_vanishing 𝕜 1 ⊤ u).2.2 θ hθ
    rw [regularDistribution_apply volume f (hf.locallyIntegrable.locallyIntegrableOn _)] at hz
    change (∫ y, f y * (g y : 𝕜)) = 0 at hz
    simpa only [RCLike.real_smul_eq_coe_mul, mul_comm] using hz
  have hae' : f =ᵐ[volume.restrict (vanishingRegion u)] 0 :=
    (ae_restrict_iff' hV.measurableSet).mpr hae
  exact hx ((MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hV hf.continuousOn
    continuous_const.continuousOn) hxV)

/-- Smoothing a compact distribution by a test agrees with the tensor/cutoff
convolution of that distribution with the test's regular distribution. -/
theorem regularDistribution_smoothing
    {u : LineDistribution 𝕜} (hu : IsCompact (distributionSupport u))
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    IsProperConvolution u (regularDistribution volume φ)
      (regularDistribution volume (distributionConvolution u φ)) := by
  let v : LineDistribution 𝕜 := regularDistribution volume φ
  have hc : Convolvable u v :=
    ProperSupportConvolution.compact_distribution_suffices 𝕜 1 u v (Or.inl hu)
  obtain ⟨w, hw, _⟩ := ProperSupportConvolution.convolution_existence 𝕜 1 u v hc
  have he : w = regularDistribution volume (distributionConvolution u φ) := by
    ext ψ
    obtain ⟨α, V, hV, hSV, hα⟩ := ExpandedFA.Distributions.cutoff_existence
      1 ⊤ _ hu (subset_univ _)
    obtain ⟨β, W, hW, hTW, hβ⟩ := ExpandedFA.Distributions.cutoff_existence
      1 ⊤ (tsupport φ) φ.hasCompactSupport (subset_univ _)
    let χ : ProductTests ℝ 1 := tensorTest α β
    have had : AdmissibleConvolutionCutoff u v ψ χ := by
      refine ⟨V ×ˢ W, hV.prod hW, ?_, ?_⟩
      · intro p hp
        exact ⟨hSV hp.1.1, hTW (regularDistribution_support_subset φ.continuous hp.1.2)⟩
      · intro p hp
        change α p.1 * β p.2 = 1
        simp [hα hp.1, hβ hp.2]
    rw [hw.2.2 (ProperSupportConvolution.iteratedTensor u v)
      (ProperSupportConvolution.iteratedTensor_isTensorProduct u v) ψ χ had,
      ProperSupportConvolution.iteratedTensor_apply,
      regularDistribution_apply volume (distributionConvolution u φ)
        ((show Continuous (distributionConvolution u φ) from
          (distributionConvolution_smooth u φ).continuous).locallyIntegrable.locallyIntegrableOn _),
      distributionConvolution_transpose]
    apply pairing_locality 𝕜 1 ⊤ u _ _ V hV hSV
    intro y hy
    rw [ProperSupportConvolution.kernelActionTest_apply]
    change regularDistribution volume φ _ = _
    rw [regularDistribution_apply volume φ (φ.continuous.locallyIntegrable.locallyIntegrableOn _),
      transposeConvolutionTest_apply]
    apply integral_congr_ae
    filter_upwards with z
    change φ z * ((α y * β z) • ψ (y+z)) = φ z * ψ (z+y)
    by_cases hz : φ z = 0
    · simp [hz]
    · simp [hα hy, hβ (hTW (subset_tsupport φ hz)), add_comm y z]
  rw [← he]
  exact hw

lemma convolution_associativity_iff
    {a b c ab bc z : LineDistribution 𝕜}
    (ha : IsCompact (distributionSupport a)) (hb : IsCompact (distributionSupport b))
    (hab : IsProperConvolution a b ab) (hbc : IsProperConvolution b c bc) :
    IsProperConvolution ab c z ↔ IsProperConvolution a bc z := by
  have ht := ProperSupportConvolution.triple_compact 1 _ _ _ ha hb
    (ProperSupportConvolution.support_closed 𝕜 1 c)
  obtain ⟨t, ht, _⟩ := ProperSupportConvolution.convolution_associativity
    𝕜 1 a b c ab bc ht hab hbc
  constructor
  · intro hz
    have he := ProperSupportConvolution.convolution_uniqueness 𝕜 1 ab c z t hz ht.1
    exact he ▸ ht.2
  · intro hz
    have he := ProperSupportConvolution.convolution_uniqueness 𝕜 1 a bc z t hz ht.2
    exact he ▸ ht.1

/-- The interchange of four compact factors follows from the actual relational
associativity and commutativity theorems. -/
lemma convolution_interchange
    {u v p q up vq uv pq z : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hv : IsCompact (distributionSupport v))
    (hp : IsCompact (distributionSupport p))
    (hup : IsProperConvolution u p up) (hvq : IsProperConvolution v q vq)
    (huv : IsProperConvolution u v uv) (hpq : IsProperConvolution p q pq)
    (hz : IsProperConvolution up vq z) : IsProperConvolution uv pq z := by
  obtain ⟨pv, hpv, _⟩ := ProperSupportConvolution.convolution_existence 𝕜 1 p v
    (ProperSupportConvolution.compact_distribution_suffices 𝕜 1 p v (Or.inl hp))
  obtain ⟨b, hb, _⟩ := ProperSupportConvolution.convolution_existence 𝕜 1 p vq
    (ProperSupportConvolution.compact_distribution_suffices 𝕜 1 p vq (Or.inl hp))
  have hub := (convolution_associativity_iff hu hp hup hb).mp hz
  have hpvq := (convolution_associativity_iff hp hv hpv hvq).mpr hb
  have hvp := ProperSupportConvolution.convolution_commutativity 𝕜 1 p v pv hpv
  have hvpq := (convolution_associativity_iff hv hp hvp hpq).mp hpvq
  exact (convolution_associativity_iff hu hv huv hvpq).mpr hub

/-- Package the actual smooth density of a compact distribution as a test. -/
def smoothingTest (u : LineDistribution 𝕜) (hu : IsCompact (distributionSupport u))
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) : Tests 𝕜 (⊤ : Opens (Domain 1)) where
  toFun := distributionConvolution u φ
  contDiff' := distributionConvolution_smooth u φ
  hasCompactSupport' := distributionConvolution_hasCompactSupport hu φ
  tsupport_subset' := subset_univ _

lemma smoothed_convolution_relation
    {u v w : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hv : IsCompact (distributionSupport v))
    (hw : IsProperConvolution u v w)
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    IsProperConvolution w (regularDistribution volume (convolutionTest φ ψ))
      (regularDistribution volume (convolutionTest (smoothingTest u hu φ) (smoothingTest v hv ψ))) := by
  apply convolution_interchange hu hv
    (regularDistribution_support_compact φ.continuous φ.hasCompactSupport)
    (regularDistribution_smoothing hu φ) (regularDistribution_smoothing hv ψ) hw
    (regularDistribution_smoothing
      (regularDistribution_support_compact φ.continuous φ.hasCompactSupport) ψ)
    (regularDistribution_smoothing
      (regularDistribution_support_compact (smoothingTest u hu φ).continuous
        (smoothingTest u hu φ).hasCompactSupport) (smoothingTest v hv ψ))

lemma scalarMap_mul (a b : 𝕜) :
    RCLike.map 𝕜 ℂ (a*b) = RCLike.map 𝕜 ℂ a * RCLike.map 𝕜 ℂ b := by
  apply Complex.ext <;> simp [RCLike.map_apply, RCLike.mul_re, RCLike.mul_im]

/-- Both orientations preserve Lebesgue measure on the line. -/
lemma integral_line_orientation {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain 1 → F) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (∫ t : ℝ, f (fun _ => s*t)) = ∫ x : Domain 1, f x := by
  have he : (∫ t : ℝ, f (fun _ => t)) = ∫ x : Domain 1, f x :=
    ((volume_preserving_funUnique (Fin 1) ℝ).symm
      (MeasurableEquiv.funUnique (Fin 1) ℝ)).integral_comp' f
  rcases hs with rfl | rfl
  · simpa only [one_mul] using he
  · simpa only [neg_one_mul] using (integral_neg_eq_self
      (fun t : ℝ => f (fun _ => t)) volume).trans he

lemma convolutionTest_orientation
    (F G : Tests 𝕜 (⊤ : Opens (Domain 1))) {s : ℝ} (hs : s = 1 ∨ s = -1) (t : ℝ) :
    (∫ r : ℝ, RCLike.map 𝕜 ℂ (F (fun _ => s*r)) *
      RCLike.map 𝕜 ℂ (G (fun _ => s*(t-r)))) =
      RCLike.map 𝕜 ℂ (convolutionTest F G (fun _ => s*t)) := by
  have hi : Integrable (fun y : Domain 1 => F y * G ((fun _ => s*t)-y)) :=
    (F.continuous.mul (G.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      F.hasCompactSupport.mul_right
  rw [convolutionTest_apply, ← (RCLike.map 𝕜 ℂ).integral_comp_comm hi]
  rw [← integral_line_orientation (fun y : Domain 1 =>
    RCLike.map 𝕜 ℂ (F y * G ((fun _ => s*t)-y))) hs]
  apply integral_congr_ae
  filter_upwards with r
  rw [scalarMap_mul]
  congr 3
  ext i
  simp only [Pi.sub_apply, mul_sub]

lemma smoothed_convolution_vanishes
    {u v w : LineDistribution 𝕜}
    (hu : IsCompact (distributionSupport u)) (hv : IsCompact (distributionSupport v))
    (hw : IsProperConvolution u v w)
    (φ ψ : Tests 𝕜 (⊤ : Opens (Domain 1))) {δ η s c : ℝ}
    (hφ : ∀ x ∈ tsupport φ, |x 0| ≤ δ)
    (hψ : ∀ x ∈ tsupport ψ, |x 0| ≤ η)
    (hs : s = 1 ∨ s = -1) (hc : LowerSupportBound w s c)
    (x : Domain 1) (hx : s * x 0 < c - δ - η) :
    convolutionTest (smoothingTest u hu φ) (smoothingTest v hv ψ) x = 0 := by
  by_contra hn
  have hts := subset_tsupport _ hn
  rw [← regularDistribution_support_eq
    (convolutionTest (smoothingTest u hu φ) (smoothingTest v hv ψ)).continuous] at hts
  obtain ⟨y, hy, z, hz, he⟩ := ProperSupportConvolution.convolution_support
    𝕜 1 _ _ _ (smoothed_convolution_relation hu hv hw φ ψ) hts
  have hz' := convolutionTest_tsupport φ ψ
    (regularDistribution_support_subset (convolutionTest φ ψ).continuous hz)
  obtain ⟨p, hp, q, hq, hpq⟩ := hz'
  have hpc := hφ p hp
  have hqc := hψ q hq
  have hyc := hc y hy
  have he0 := congrFun he 0
  have hpq0 := congrFun hpq 0
  simp only [Pi.add_apply] at he0 hpq0
  rcases hs with rfl | rfl <;> rw [abs_le] at hpc hqc <;> simp only [one_mul, neg_one_mul] at * <;> linarith

/-- The smoothings of two distributions satisfy the function support bound
obtained from the actual distribution convolution. -/
theorem smoothing_convolution_bound : SmoothingConvolutionBound := by
  intro 𝕜 _ u v w hu hv hw φ ψ δ η _ _ hφ hψ s hs c hc
  filter_upwards with t ht
  change (∫ r : ℝ, RCLike.map 𝕜 ℂ (smoothingTest u hu φ (fun _ => s*r)) *
    RCLike.map 𝕜 ℂ (smoothingTest v hv ψ (fun _ => s*(t-r)))) = 0
  rw [convolutionTest_orientation _ _ hs]
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hxt : s * ((fun _ : Fin 1 => s*t) 0) < c - δ - η := by
    simpa only [← mul_assoc, hss, one_mul] using ht
  rw [smoothed_convolution_vanishes hu hv hw φ ψ hφ hψ hs hc _ hxt, map_zero]

/-- Titchmarsh's theorem for both manuscript scalar fields, applied to the
original tensor/cutoff distribution convolution. -/
theorem convolution_endpoints : Spec.ConvolutionEndpoints :=
  convolution_endpoints_of_smoothing smoothing_detection smoothing_convolution_bound

theorem convolution_existence : Spec.ConvolutionExistence :=
  convolution_existence_of_endpoints convolution_endpoints

theorem no_extra_initial_interval : Spec.NoExtraInitialInterval :=
  no_extra_initial_interval_of_endpoints convolution_endpoints

end ExpandedFA.PartIV.Titchmarsh
