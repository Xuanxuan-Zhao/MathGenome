import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatZeroTrace
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatTrace
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ENNReal

namespace P102.Trace
open P102.U4

/-- Zero extension of a half-space Lp class, including the flat face in the zero side. -/
def flatZeroExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (v : DomainLp 𝕜 (halfSpace m) p) : DomainLp 𝕜 (⊤ : Opens (Space (m + 1))) p :=
  (show MemLp ((halfSpace m : Set (Space (m + 1))).indicator v) p
      (volume.restrict ((⊤ : Opens (Space (m + 1))) : Set (Space (m + 1)))) from by
    simpa using (memLp_indicator_iff_restrict
      (halfSpace m).isOpen.measurableSet.nullMeasurableSet).mpr (Lp.memLp v)).toLp _

/-- This uses actual vertical ACL boundary values, as in the accepted trace theorem. -/
def HasZeroFlatTrace {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) : Prop :=
  HasVerticalBoundaryValues u (0 : BoundaryLp m 𝕜 p)

/-- Membership of the zero-extended Lp function in the ordinary whole-space Sobolev space.
In particular, this predicate does not assume the desired formula for derivatives. -/
def HasFlatZeroExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) : Prop :=
  ∃ w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
    sobolevUnderlying w = flatZeroExtension (sobolevUnderlying u)

/-- Smooth compact approximants have their topological supports contained in H,
as imposed by `TestSpace (halfSpace m)`. All weak derivative coordinates converge
in the existing Sobolev norm, which includes the zeroth coordinate. -/
def IsHalfSpaceTestLimit {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p) : Prop :=
  ∃ (φ : ℕ → TestSpace 𝕜 (halfSpace m)) (v : ℕ → HalfSobolev m 𝕜 p),
    (∀ n (α : SobolevIndex (m + 1) 1),
      (sobolevDerivative (v n) α : Space (m + 1) → 𝕜) =ᵐ[
        volume.restrict (halfSpace m : Set (Space (m + 1)))]
          multiPartial (φ n) α.val) ∧
    Tendsto v atTop (𝓝 u)

/-- The defining representative of the extension really is the indicator. -/
theorem flatZeroExtension_ae {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (v : DomainLp 𝕜 (halfSpace m) p) :
    (flatZeroExtension v : Space (m + 1) → 𝕜) =ᵐ[volume]
      (halfSpace m : Set (Space (m + 1))).indicator v := by
  have h : MemLp ((halfSpace m : Set (Space (m + 1))).indicator v) p
      (volume.restrict ((⊤ : Opens (Space (m + 1))) : Set (Space (m + 1)))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (memLp_indicator_iff_restrict
        (halfSpace m).isOpen.measurableSet.nullMeasurableSet).mpr (Lp.memLp v)
  have hh := h.coeFn_toLp
  change (h.toLp _ : Space (m + 1) → 𝕜) =ᵐ[volume] _
  simpa only [Opens.coe_top, Measure.restrict_univ] using hh

/-- Extension does not alter any Lp norm. -/
theorem flatZeroExtension_norm {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (v : DomainLp 𝕜 (halfSpace m) p) : ‖flatZeroExtension v‖ = ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  simp only [Opens.coe_top, Measure.restrict_univ]
  rw [eLpNorm_congr_ae (flatZeroExtension_ae v),
    eLpNorm_indicator_eq_eLpNorm_restrict
      (halfSpace m).isOpen.measurableSet.nullMeasurableSet]

/-- Vertical ACL limits are independent of the representative. -/
theorem verticalBoundaryValues_unique {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u : HalfSobolev m 𝕜 p} {g h : BoundaryLp m 𝕜 p}
    (hg : HasVerticalBoundaryValues u g) (hh : HasVerticalBoundaryValues u h) : g = h := by
  obtain ⟨f, huf, hf⟩ := hg
  obtain ⟨k, huk, hk⟩ := hh
  have heq := ACL.ae_on_fibers (Fin.last m) (huf.symm.trans huk)
  apply Lp.ext
  filter_upwards [hf, hk, heq] with z hfz hkz hz
  have hfc := ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn
    hfz.1 isOpen_Ioi
  have hkc := ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn
    hkz.1 isOpen_Ioi
  have hz' : (fun t => f (point m z t)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => k (point m z t)) := by
    simpa only [Filter.EventuallyEq, vertical_fiber, point] using hz
  have hon := Measure.eqOn_open_of_ae_eq hz' isOpen_Ioi hfc hkc
  exact tendsto_nhds_unique hfz.2.2 (hkz.2.2.congr'
    (eventually_mem_nhdsWithin.mono fun t ht => (hon ht).symm))

/-- The zero boundary-value predicate agrees with the ordinary flat trace. -/
theorem flat_zero_trace_slice_bridge :
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (u : HalfSobolev m 𝕜 p) (F : ℝ → BoundaryLp m 𝕜 p),
      IsSliceRepresentative u F → (HasZeroFlatTrace u ↔ F 0 = 0) := by
  intro m _hm 𝕜 _ p _ hpt u F hF
  have hboundary := slice_hasVerticalBoundaryValues hpt hF
  constructor
  · intro hzero
    exact verticalBoundaryValues_unique hboundary hzero
  · intro hzero
    change HasVerticalBoundaryValues u 0
    rwa [hzero] at hboundary

/-- A continuous whole-line function vanishing almost everywhere on the negative
half-line has value zero at its endpoint. -/
theorem continuous_zero_of_ae_negative {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : Continuous f) (hz : f =ᵐ[volume.restrict (Iio (0 : ℝ))] 0) : f 0 = 0 := by
  have hon := Measure.eqOn_open_of_ae_eq hz isOpen_Iio hf.continuousOn
    continuous_const.continuousOn
  have ht : Tendsto f (𝓝[<] 0) (𝓝 (0 : 𝕜)) :=
    tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun t ht => (hon ht).symm)
  letI : (𝓝[<] (0 : ℝ)).NeBot := nhdsLT_neBot_of_exists_lt ⟨-1, by norm_num⟩
  have ht' : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 (f 0)) :=
    (hf.tendsto 0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique ht' ht

/-- A whole-space Sobolev zero extension forces the original trace to vanish.
The original half-space representative supplies the prescribed derivative;
the whole-space representative is used only for continuity across zero. -/
theorem flat_zero_extension_implies_zero_trace :
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ u : HalfSobolev m 𝕜 p, HasFlatZeroExtension u → HasZeroFlatTrace u := by
  intro m _hm 𝕜 _ p _ _hpt u hw
  obtain ⟨w, hw⟩ := hw
  obtain ⟨f, huf, hf⟩ := vertical_acl m 𝕜 p u
  obtain ⟨k, hwk, hk⟩ := (acl_characterization (m + 1) (by omega) 𝕜
    (⊤ : Opens (Space (m + 1))) (Fin.last m)
    (sobolevUnderlying w) (sobolevDerivative w (verticalIndex m))
    (domainLp_locallyIntegrable ⊤ p _)
    (domainLp_locallyIntegrable ⊤ p _)).mp
      (sobolev_derivative_distribution ⊤ 1 p w (verticalIndex m))
  have hwk' : (sobolevUnderlying w : Space (m + 1) → 𝕜) =ᵐ[volume] k := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hwk
  have hke : k =ᵐ[volume]
      (halfSpace m : Set (Space (m + 1))).indicator (sobolevUnderlying u) := by
    rw [hw] at hwk'
    exact hwk'.symm.trans (flatZeroExtension_ae _)
  have hline := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space (m + 1))))
    (Fin.last m) (by simpa only [Filter.EventuallyEq, Opens.coe_top, Measure.restrict_univ] using hke)
  have hku : k =ᵐ[volume.restrict (halfSpace m : Set (Space (m + 1)))] f := by
    filter_upwards [hke.filter_mono (ae_mono Measure.restrict_le_self), huf,
      ae_restrict_mem (halfSpace m).isOpen.measurableSet] with x hx hfx hxH
    exact (hx.trans (indicator_of_mem hxH _)).trans hfx
  have hlineH := ACL.ae_on_fibers (Fin.last m) hku
  refine ⟨f, huf, ?_⟩
  filter_upwards [hf, hk, hline, hlineH, Lp.coeFn_zero 𝕜 p volume] with z hfz hkz hez heHz hzero
  refine ⟨hfz.1, hfz.2, ?_⟩
  have hkc : Continuous (fun t => k (point m z t)) := by
    apply continuousOn_univ.mp
    apply ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn _ isOpen_univ
    simpa only [ACL.fiber, Opens.coe_top, preimage_univ, point] using hkz.1
  have hez' : (fun t => k (point m z t)) =ᵐ[volume]
      (fun t => (halfSpace m : Set (Space (m + 1))).indicator
        (sobolevUnderlying u) (point m z t)) := by
    simpa only [Filter.EventuallyEq, ACL.fiber, Opens.coe_top, preimage_univ, Measure.restrict_univ,
      point] using hez
  have hneg : (fun t => k (point m z t)) =ᵐ[volume.restrict (Iio (0 : ℝ))] 0 := by
    filter_upwards [hez'.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Iio] with t ht htneg
    have hnot : point m z t ∉ (halfSpace m : Set (Space (m + 1))) := by
      simpa only [halfSpace, Opens.coe_mk, mem_ofPred_eq, point_height] using
        not_lt.mpr (le_of_lt (show t < 0 from htneg))
    simpa only [Pi.zero_apply, indicator_of_notMem hnot] using ht
  have hkzero : k (point m z 0) = 0 := continuous_zero_of_ae_negative hkc hneg
  have heHz' : (fun t => k (point m z t)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => f (point m z t)) := by
    simpa only [Filter.EventuallyEq, vertical_fiber, point] using heHz
  have hfc := ExpandedFA.Sobolev.Lines.LocallyAbsolutelyContinuousOn.continuousOn
    hfz.1 isOpen_Ioi
  have hon := Measure.eqOn_open_of_ae_eq heHz' isOpen_Ioi hkc.continuousOn hfc
  simp only [Pi.zero_apply] at hzero
  rw [hzero, ← hkzero]
  exact ((hkc.tendsto 0).mono_left inf_le_left).congr'
    (eventually_mem_nhdsWithin.mono fun t ht => hon ht)

/-- A zero right boundary value lets an AC curve pass through the endpoint by
zero. Local integrability of the extended derivative is essential here. -/
theorem locallyAC_zero_extension {𝕜 : Type} [RCLike 𝕜] {f h : ℝ → 𝕜}
    (hf : ACL.LocallyAC f (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), HasDerivAt f (h t) t)
    (hi : LocallyIntegrable ((Ioi (0 : ℝ)).indicator h) volume)
    (hz : Tendsto f (𝓝[>] 0) (𝓝 0)) :
    ACL.LocallyAC ((Ioi (0 : ℝ)).indicator f) univ := by
  let k := (Ioi (0 : ℝ)).indicator h
  have hki (a b : ℝ) : IntervalIntegrable k volume a b :=
    (hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  let g : ℝ → 𝕜 := fun t => f 1 + ∫ s in (1 : ℝ)..t, k s
  have hga (a b : ℝ) : AbsolutelyContinuousOnInterval g a b :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => f 1)).contDiffOn.absolutelyContinuousOnInterval).add
      (ExpandedFA.Sobolev.OneDimensional.integral_primitive_absolutelyContinuous hki a b 1)
  have hgc : Continuous g := continuous_const.add (intervalIntegral.continuous_primitive hki 1)
  have hpos (t : ℝ) (ht : 0 < t) : g t = f t := by
    have hs : uIcc (1 : ℝ) t ⊆ Ioi 0 := by
      intro s hs
      exact lt_of_lt_of_le (lt_min zero_lt_one ht) hs.1
    have hih : IntegrableOn h (uIcc (1 : ℝ) t) := by
      apply (hi.integrableOn_isCompact isCompact_uIcc).congr_fun
      · intro s hs'
        exact indicator_of_mem (hs hs') h
      · exact measurableSet_uIcc
    have he := vertical_integral_eq_sub hf hd zero_lt_one ht hih
    have hek : (∫ s in (1 : ℝ)..t, k s) = ∫ s in (1 : ℝ)..t, h s := by
      apply intervalIntegral.integral_congr
      intro s hs'
      exact indicator_of_mem (hs hs') h
    dsimp only [g]
    rw [hek, he]
    abel
  have hg0 : g 0 = 0 := by
    letI : (𝓝[>] (0 : ℝ)).NeBot := nhdsGT_neBot 0
    have hgL : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hzL : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (0 : 𝕜)) :=
      hz.congr' (eventually_mem_nhdsWithin.mono fun t ht => (hpos t ht).symm)
    exact tendsto_nhds_unique hgL hzL
  have hnonpos (t : ℝ) (ht : t ≤ 0) : g t = 0 := by
    have he : (∫ s in t..(0 : ℝ), k s) = 0 := by
      rw [intervalIntegral.integral_of_le ht]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact indicator_of_notMem (not_lt.mpr hs.2) h
    have hid := intervalIntegral.integral_interval_sub_left (hki 1 0) (hki 1 t)
    dsimp only [g] at hg0 ⊢
    rw [he] at hid
    have heq : (∫ s in (1 : ℝ)..t, k s) = ∫ s in (1 : ℝ)..0, k s := by
      exact (sub_eq_zero.mp hid).symm
    rwa [heq]
  intro a b _
  apply (hga a b).congr
  intro t _
  by_cases ht : 0 < t
  · exact (hpos t ht).trans (indicator_of_mem ht f).symm
  · exact (hnonpos t (not_lt.mp ht)).trans (indicator_of_notMem ht f).symm

/-- The derivative of a zero-extended curve has no boundary contribution away
from the single endpoint. Absolute continuity across it is proved separately. -/
theorem ae_hasDerivAt_zero_extension {𝕜 : Type} [RCLike 𝕜] {f h : ℝ → 𝕜}
    (hd : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), HasDerivAt f (h t) t) :
    ∀ᵐ t ∂volume, HasDerivAt ((Ioi (0 : ℝ)).indicator f)
      ((Ioi (0 : ℝ)).indicator h t) t := by
  have hn : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hd, hn] with t ht hne
  by_cases hp : 0 < t
  · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hp]
    apply (ht hp).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Ioi (0 : ℝ) from hp)] with s hs
    exact indicator_of_mem hs f
  · have hm : t < 0 := lt_of_le_of_ne (not_lt.mp hp) hne
    rw [indicator_of_notMem (s := Ioi (0 : ℝ)) hp]
    apply (hasDerivAt_const t (0 : 𝕜)).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Iio (0 : ℝ) from hm)] with s hs
    exact indicator_of_notMem (not_lt.mpr hs.le) f

/-- Changing a half-space representative changes no zero-extended class. -/
theorem flatZeroExtension_ae_of_ae {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (v : DomainLp 𝕜 (halfSpace m) p) {f : Space (m + 1) → 𝕜}
    (hf : (v : Space (m + 1) → 𝕜) =ᵐ[
      volume.restrict (halfSpace m : Set (Space (m + 1)))] f) :
    (flatZeroExtension v : Space (m + 1) → 𝕜) =ᵐ[volume]
      (halfSpace m : Set (Space (m + 1))).indicator f :=
  (flatZeroExtension_ae v).trans
    ((ae_eq_restrict_iff_indicator_ae_eq (halfSpace m).isOpen.measurableSet).mp hf)

/-- Zero vertical trace supplies a whole-line ACL representative of the
zero extension, with the prescribed extended vertical derivative. -/
theorem zero_extension_vertical_acl {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {u : HalfSobolev m 𝕜 p} (hu : HasZeroFlatTrace u) :
    ACL.HasRepresentative (⊤ : Opens (Space (m + 1))) (Fin.last m)
      (flatZeroExtension (sobolevUnderlying u))
      (flatZeroExtension (sobolevDerivative u (verticalIndex m))) := by
  obtain ⟨f, huf, hf⟩ := hu
  refine ⟨(halfSpace m : Set (Space (m + 1))).indicator f, ?_, ?_⟩
  · simpa only [Opens.coe_top, Measure.restrict_univ] using
      flatZeroExtension_ae_of_ae (sobolevUnderlying u) huf
  have hdext := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space (m + 1)))) (Fin.last m)
    (by simpa only [Filter.EventuallyEq, Opens.coe_top, Measure.restrict_univ] using
      flatZeroExtension_ae (sobolevDerivative u (verticalIndex m)))
  filter_upwards [hf, halfSpace_memLp_vertical_lines
      (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hpt
        (sobolevDerivative u (verticalIndex m)),
      hdext, Lp.coeFn_zero 𝕜 p (volume : Measure (Boundary m))]
    with z hz hiz hez hzero
  have hid : LocallyIntegrable
      ((Ioi (0 : ℝ)).indicator (fun t => sobolevDerivative u (verticalIndex m) (point m z t)))
      volume :=
    ((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hiz).locallyIntegrable Fact.out
  have hefunc : (fun t => (halfSpace m : Set (Space (m + 1))).indicator f (point m z t)) =
      (Ioi (0 : ℝ)).indicator (fun t => f (point m z t)) := by
    funext t
    by_cases ht : 0 < t <;> simp [halfSpace, ht]
  have hederiv : (fun t => (halfSpace m : Set (Space (m + 1))).indicator
      (sobolevDerivative u (verticalIndex m)) (point m z t)) =
      (Ioi (0 : ℝ)).indicator (fun t => sobolevDerivative u (verticalIndex m) (point m z t)) := by
    funext t
    by_cases ht : 0 < t <;> simp [halfSpace, ht]
  have hz0 : Tendsto (fun t => f (point m z t)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : 𝕜)) := by
    simp only [Pi.zero_apply] at hzero
    simpa only [hzero] using hz.2.2
  have hac := locallyAC_zero_extension hz.1 hz.2.1 hid hz0
  have had := ae_hasDerivAt_zero_extension hz.2.1
  constructor
  · simp only [ACL.fiber, Opens.coe_top, preimage_univ]
    change ACL.LocallyAC (fun t => (halfSpace m : Set (Space (m + 1))).indicator f (point m z t)) univ
    rwa [hefunc]
  · have hez' : (fun t => flatZeroExtension (sobolevDerivative u (verticalIndex m))
        (point m z t)) =ᵐ[volume]
        ((Ioi (0 : ℝ)).indicator (fun t => sobolevDerivative u (verticalIndex m) (point m z t))) := by
      simp only [ACL.fiber, Opens.coe_top, preimage_univ, Measure.restrict_univ] at hez
      change (fun t => flatZeroExtension (sobolevDerivative u (verticalIndex m)) (point m z t))
        =ᵐ[volume] (fun t => (halfSpace m : Set (Space (m + 1))).indicator
          (sobolevDerivative u (verticalIndex m)) (point m z t)) at hez
      rwa [hederiv] at hez
    simp only [ACL.fiber, Opens.coe_top, preimage_univ, Measure.restrict_univ]
    change ∀ᵐ t ∂volume, HasDerivAt
      (fun s => (halfSpace m : Set (Space (m + 1))).indicator f (point m z s))
      (flatZeroExtension (sobolevDerivative u (verticalIndex m)) (point m z t)) t
    rw [hefunc]
    filter_upwards [had, hez'] with t ht he
    rwa [he]

/-- A tangential line has constant height. -/
theorem tangential_line_height {m : ℕ} (j : Fin (m + 1)) (hj : j ≠ Fin.last m)
    (z : ACL.Transverse j) (t : ℝ) :
    ACL.line j z t (Fin.last m) = z ⟨Fin.last m, Ne.symm hj⟩ := by
  simp [ACL.line, ExpandedFA.Sobolev.Lines.coordinateLine, Ne.symm hj]

/-- Each tangential fiber lies wholly in the upper half-space or wholly outside
it, so extension requires no endpoint gluing on these lines. -/
theorem zero_extension_tangential_acl {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p)
    (j : Fin (m + 1)) (hj : j ≠ Fin.last m) :
    ACL.HasRepresentative (⊤ : Opens (Space (m + 1))) j
      (flatZeroExtension (sobolevUnderlying u))
      (flatZeroExtension (sobolevDerivative u ⟨{j}, by simp⟩)) := by
  obtain ⟨f, huf, hf⟩ := (acl_characterization (m + 1) (by omega) 𝕜 (halfSpace m) j
    (sobolevUnderlying u) (sobolevDerivative u ⟨{j}, by simp⟩)
    (domainLp_locallyIntegrable (halfSpace m) p _)
    (domainLp_locallyIntegrable (halfSpace m) p _)).mp
      (sobolev_derivative_distribution (halfSpace m) 1 p u ⟨{j}, by simp⟩)
  refine ⟨(halfSpace m : Set (Space (m + 1))).indicator f, ?_, ?_⟩
  · simpa only [Opens.coe_top, Measure.restrict_univ] using
      flatZeroExtension_ae_of_ae (sobolevUnderlying u) huf
  have hdext := ACL.ae_on_fibers (Ω := (⊤ : Opens (Space (m + 1)))) j
    (by simpa only [Filter.EventuallyEq, Opens.coe_top, Measure.restrict_univ] using
      flatZeroExtension_ae (sobolevDerivative u ⟨{j}, by simp⟩))
  filter_upwards [hf, hdext] with z hz hez
  have hez' : (fun t => flatZeroExtension (sobolevDerivative u ⟨{j}, by simp⟩) (ACL.line j z t))
      =ᵐ[volume] (fun t => (halfSpace m : Set (Space (m + 1))).indicator
        (sobolevDerivative u ⟨{j}, by simp⟩) (ACL.line j z t)) := by
    simpa only [Filter.EventuallyEq, ACL.fiber, Opens.coe_top, preimage_univ,
      Measure.restrict_univ] using hez
  simp only [ACL.fiber, Opens.coe_top, preimage_univ, Measure.restrict_univ]
  by_cases hp : 0 < z ⟨Fin.last m, Ne.symm hj⟩
  · have hmem (t : ℝ) : ACL.line j z t ∈ (halfSpace m : Set (Space (m + 1))) := by
      change 0 < ACL.line j z t (Fin.last m)
      rwa [tangential_line_height j hj]
    have hfi : ACL.fiber (halfSpace m) j z = univ := by
      ext t
      simp only [ACL.fiber, mem_preimage, mem_univ, iff_true]
      exact hmem t
    have heq : (fun t => (halfSpace m : Set (Space (m + 1))).indicator f (ACL.line j z t)) =
        (fun t => f (ACL.line j z t)) := by
      funext t
      exact indicator_of_mem (hmem t) f
    rw [heq]
    refine ⟨by simpa only [hfi] using hz.1, ?_⟩
    have hdz := hz.2
    rw [hfi, Measure.restrict_univ] at hdz
    filter_upwards [hdz, hez'] with t ht he
    rwa [he, indicator_of_mem (hmem t)]
  · have hnot (t : ℝ) : ACL.line j z t ∉ (halfSpace m : Set (Space (m + 1))) := by
      change ¬0 < ACL.line j z t (Fin.last m)
      rwa [tangential_line_height j hj]
    have heq : (fun t => (halfSpace m : Set (Space (m + 1))).indicator f (ACL.line j z t)) =
        (fun _ : ℝ => (0 : 𝕜)) := by
      funext t
      exact indicator_of_notMem (hnot t) f
    rw [heq]
    constructor
    · intro a b _
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : 𝕜))).contDiffOn.absolutelyContinuousOnInterval
    · filter_upwards [hez'] with t he
      rw [he, indicator_of_notMem (hnot t)]
      exact hasDerivAt_const t (0 : 𝕜)

/-- For first-order Sobolev functions, zero trace extends every weak
coordinate derivative by zero, including the zeroth coordinate. -/
theorem zero_trace_extension_tuple {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (u : HalfSobolev m 𝕜 p) (hu : HasZeroFlatTrace u) :
    ∃ w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
      ∀ α : SobolevIndex (m + 1) 1,
        sobolevDerivative w α = flatZeroExtension (sobolevDerivative u α) := by
  let v : SobolevTuple 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
    WithLp.toLp 1 (fun α => flatZeroExtension (sobolevDerivative u α))
  have hd (α : SobolevIndex (m + 1) 1) :
      distributionPartial α.val
        (regularDistribution ⊤ (flatZeroExtension (sobolevUnderlying u))) =
        regularDistribution ⊤ (flatZeroExtension (sobolevDerivative u α)) := by
    by_cases hz : α.val = 0
    · have hα : α = zeroSobolevIndex (m + 1) 1 := Subtype.ext hz
      subst α
      exact derivative_zero (m + 1) 𝕜 ⊤ _
    · have hcard : α.val.card = 1 := by
        have hn := Multiset.card_eq_zero.not.mpr hz
        have hle := α.property
        omega
      obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hcard
      have hα : α = ⟨{j}, by simp⟩ := Subtype.ext hj
      subst α
      apply acl_converse (m + 1) (by omega) 𝕜 ⊤ j _ _
        (domainLp_locallyIntegrable ⊤ p _) (domainLp_locallyIntegrable ⊤ p _)
      by_cases hjlast : j = Fin.last m
      · subst j
        exact zero_extension_vertical_acl hpt hu
      · exact zero_extension_tangential_acl u j hjlast
  have hv : v ∈ sobolevSubmodule 𝕜 (⊤ : Opens (Space (m + 1))) 1 p := by
    apply (mem_sobolevSubmodule_iff ⊤ 1 p v).mpr
    intro α φ
    exact (distributionPartial_eq_regularLp_iff ⊤ p α.val _ _).mp (hd α) φ
  exact ⟨⟨v, hv⟩, fun _ => rfl⟩

/-- Both implications of the flat zero-extension criterion. -/
theorem flat_zero_trace_iff_extension :
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ u : HalfSobolev m 𝕜 p, HasZeroFlatTrace u ↔ HasFlatZeroExtension u := by
  intro m hm 𝕜 _ p _ hpt u
  constructor
  · intro hu
    obtain ⟨w, hw⟩ := zero_trace_extension_tuple hpt u hu
    exact ⟨w, hw (zeroSobolevIndex (m + 1) 1)⟩
  · exact flat_zero_extension_implies_zero_trace m hm 𝕜 p hpt u

/-- Every Sobolev realization of the zero extension has exactly the
zero-extended old derivative tuple, by uniqueness of weak derivatives. -/
theorem flat_zero_extension_derivatives :
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (u : HalfSobolev m 𝕜 p) (w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p),
      sobolevUnderlying w = flatZeroExtension (sobolevUnderlying u) →
      ∀ α : SobolevIndex (m + 1) 1,
        sobolevDerivative w α = flatZeroExtension (sobolevDerivative u α) := by
  intro m hm 𝕜 _ p _ hpt u w hw
  have hu := flat_zero_extension_implies_zero_trace m hm 𝕜 p hpt u ⟨w, hw⟩
  obtain ⟨v, hv⟩ := zero_trace_extension_tuple hpt u hu
  have heq : w = v := sobolevUnderlying_injective ⊤ 1 p
    (hw.trans (hv (zeroSobolevIndex (m + 1) 1)).symm)
  subst w
  exact hv

/-- Restriction of a whole-space Lp class to an open set. -/
def restrictWholeLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (Ω : Opens (Space d)) (v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) : DomainLp 𝕜 Ω p :=
  ((Lp.memLp v).mono_measure (Measure.restrict_mono (le_top : Ω ≤ ⊤) le_rfl)).toLp v

theorem restrictWholeLp_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (Ω : Opens (Space d)) (v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    (restrictWholeLp Ω v : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] v :=
  MemLp.coeFn_toLp _

theorem restrictWholeLp_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (Ω : Opens (Space d)) (v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    ‖restrictWholeLp Ω v‖ ≤ ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (restrictWholeLp_ae Ω v)]
  exact ENNReal.toReal_mono (Lp.memLp v).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono (le_top : Ω ≤ ⊤) le_rfl))

theorem restrictWholeLp_sub {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (Ω : Opens (Space d))
    (u v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    restrictWholeLp Ω (u - v) = restrictWholeLp Ω u - restrictWholeLp Ω v := by
  apply Lp.ext
  filter_upwards [restrictWholeLp_ae Ω (u - v), restrictWholeLp_ae Ω u,
    restrictWholeLp_ae Ω v, Lp.coeFn_sub (restrictWholeLp Ω u) (restrictWholeLp Ω v),
    (Lp.coeFn_sub u v).filter_mono
      (ae_mono (Measure.restrict_mono (le_top : Ω ≤ ⊤) le_rfl))] with x h huv hv hsub hsub'
  simp only [h, hsub, hsub', Pi.sub_apply, huv, hv]

/-- Test pairing is unchanged when the whole-space class is restricted and
the interior test is viewed as its ambient zero extension. -/
theorem restrictWholeLp_pairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (Ω : Opens (Space d))
    (v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) (φ : TestSpace 𝕜 Ω) :
    lpTestPairing Ω p φ (restrictWholeLp Ω v) =
      lpTestPairing ⊤ p (zeroExtension 𝕜 (le_top : Ω ≤ ⊤) φ) v := by
  rw [lpTestPairing_eq_integral, lpTestPairing_eq_integral]
  simp only [Opens.coe_top, Measure.restrict_univ]
  calc
    (∫ x in Ω, restrictWholeLp Ω v x * φ x) = ∫ x in Ω, v x * φ x :=
      integral_congr_ae ((restrictWholeLp_ae Ω v).mono fun x hx => congrArg (· * φ x) hx)
    _ = ∫ x, v x * φ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp only [φ.zero_on_compl hx, Pi.zero_apply, mul_zero]
    _ = _ := by simp [zeroExtension, TestFunction.monoCLM_apply]

/-- Restriction carries the entire derivative tuple to the ordinary Sobolev
space; the weak equations are checked using interior tests. -/
def restrictWholeSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {k : ℕ} (Ω : Opens (Space d))
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) k p) : Sobolev 𝕜 Ω k p := by
  let v : SobolevTuple 𝕜 Ω k p := WithLp.toLp 1 (fun α => restrictWholeLp Ω (sobolevDerivative u α))
  refine ⟨v, (mem_sobolevSubmodule_iff Ω k p v).mpr ?_⟩
  intro α φ
  change lpTestPairing Ω p φ (restrictWholeLp Ω (sobolevDerivative u α)) =
    _ * lpTestPairing Ω p _ (restrictWholeLp Ω (sobolevUnderlying u))
  rw [restrictWholeLp_pairing, restrictWholeLp_pairing]
  have he : zeroExtension 𝕜 (le_top : Ω ≤ ⊤) (testPartialWord Ω (α.val.sort (· ≤ ·)) φ) =
      testPartialWord ⊤ (α.val.sort (· ≤ ·)) (zeroExtension 𝕜 (le_top : Ω ≤ ⊤) φ) := by
    ext x
    simp [zeroExtension, TestFunction.monoCLM_apply, testPartialWord_coe]
  rw [he]
  exact (mem_sobolevSubmodule_iff ⊤ k p u.val).mp u.property α _

theorem restrictWholeSobolev_norm_sub_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ} (Ω : Opens (Space d))
    (u v : Sobolev 𝕜 (⊤ : Opens (Space d)) k p) :
    ‖restrictWholeSobolev Ω u - restrictWholeSobolev Ω v‖ ≤ ‖u - v‖ := by
  rw [sobolev_norm, sobolev_norm]
  apply Finset.sum_le_sum
  intro α _
  change ‖restrictWholeLp Ω (sobolevDerivative u α) - restrictWholeLp Ω (sobolevDerivative v α)‖ ≤
    ‖sobolevDerivative u α - sobolevDerivative v α‖
  rw [← restrictWholeLp_sub]
  exact restrictWholeLp_norm_le Ω _

/-- Translate every coordinate of a whole-space derivative tuple. -/
def translateWholeLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (a : Space d) (v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    DomainLp 𝕜 (⊤ : Opens (Space d)) p :=
  Lp.compMeasurePreserving (fun x => x - a)
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using measurePreserving_sub_right volume a) v

theorem translateWholeLp_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (a : Space d) (v : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    (translateWholeLp a v : Space d → 𝕜) =ᵐ[volume] (fun x => v (x - a)) := by
  have h : MeasurePreserving (fun x : Space d => x - a)
      (volume.restrict ((⊤ : Opens (Space d)) : Set (Space d)))
      (volume.restrict ((⊤ : Opens (Space d)) : Set (Space d))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using measurePreserving_sub_right volume a
  have he := Lp.coeFn_compMeasurePreserving v h
  change (translateWholeLp a v : Space d → 𝕜) =ᵐ[
    volume.restrict ((⊤ : Opens (Space d)) : Set (Space d))] (fun x => v (x - a)) at he
  simpa only [Opens.coe_top, Measure.restrict_univ] using he

/-- Translation of tests in the opposite direction is the dual change of variables. -/
def shiftWholeTest {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : Space d) (φ : WholeTests d 𝕜) : WholeTests d 𝕜 where
  toFun x := φ (a + x)
  contDiff' := φ.contDiff.comp (contDiff_const.add contDiff_id)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft a)
  tsupport_subset' := subset_univ _

theorem translateWholeLp_pairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (a : Space d) (v : DomainLp 𝕜 (⊤ : Opens (Space d)) p)
    (φ : WholeTests d 𝕜) :
    lpTestPairing ⊤ p φ (translateWholeLp a v) = lpTestPairing ⊤ p (shiftWholeTest a φ) v := by
  rw [lpTestPairing_eq_integral, lpTestPairing_eq_integral]
  simp only [Opens.coe_top, Measure.restrict_univ]
  calc
    (∫ x, translateWholeLp a v x * φ x) = ∫ x, v (x - a) * φ x :=
      integral_congr_ae ((translateWholeLp_ae a v).mono fun x hx => congrArg (· * φ x) hx)
    _ = ∫ x, v x * φ (a + x) := by
      have he := (measurePreserving_sub_right volume a).integral_comp
        (Homeomorph.subRight a).measurableEmbedding (fun x => v x * φ (a + x))
      simpa only [add_sub_cancel, add_sub_cancel_left] using he
    _ = _ := rfl

def translateWholeSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {k : ℕ} (a : Space d)
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) k p) : Sobolev 𝕜 (⊤ : Opens (Space d)) k p := by
  let v : SobolevTuple 𝕜 (⊤ : Opens (Space d)) k p :=
    WithLp.toLp 1 (fun α => translateWholeLp a (sobolevDerivative u α))
  refine ⟨v, (mem_sobolevSubmodule_iff ⊤ k p v).mpr ?_⟩
  intro α φ
  change lpTestPairing ⊤ p φ (translateWholeLp a (sobolevDerivative u α)) =
    _ * lpTestPairing ⊤ p _ (translateWholeLp a (sobolevUnderlying u))
  rw [translateWholeLp_pairing, translateWholeLp_pairing]
  have he : shiftWholeTest a (testPartialWord ⊤ (α.val.sort (· ≤ ·)) φ) =
      testPartialWord ⊤ (α.val.sort (· ≤ ·)) (shiftWholeTest a φ) := by
    ext x
    change testPartialWord ⊤ (α.val.sort (· ≤ ·)) φ (a + x) = _
    simp only [testPartialWord_coe]
    exact (congrFun (partialWord_const_add φ.contDiff a (α.val.sort (· ≤ ·))) x).symm
  rw [he]
  exact (mem_sobolevSubmodule_iff ⊤ k p u.val).mp u.property α _

theorem translateWholeSobolev_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) k p) : translateWholeSobolev 0 u = u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  apply Lp.ext
  change (translateWholeLp 0 (sobolevDerivative u α) : Space d → 𝕜) =ᵐ[
    volume.restrict ((⊤ : Opens (Space d)) : Set (Space d))] (sobolevDerivative u α)
  simpa only [Opens.coe_top, Measure.restrict_univ, sub_zero] using
    translateWholeLp_ae 0 (sobolevDerivative u α)

theorem continuous_translateWholeSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ} (hpt : p ≠ ∞)
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) k p) : Continuous (fun a => translateWholeSobolev a u) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 1 _).comp
  apply continuous_pi
  intro α
  change Continuous (fun a => translateWholeLp a (sobolevDerivative u α))
  unfold translateWholeLp
  let shifts : C(Space d, C(Space d, Space d)) :=
    (⟨fun q : Space d × Space d => q.2 - q.1, continuous_snd.sub continuous_fst⟩ :
      C(Space d × Space d, Space d)).curry
  exact continuous_const.compMeasurePreservingLp shifts.continuous
    (fun a => by
      change MeasurePreserving (fun x : Space d => x - a)
        (volume.restrict ((⊤ : Opens (Space d)) : Set (Space d)))
        (volume.restrict ((⊤ : Opens (Space d)) : Set (Space d)))
      simpa only [Opens.coe_top, Measure.restrict_univ] using measurePreserving_sub_right volume a) hpt

/-- Regularization cannot cross more than the radius of its kernel below the
lower edge of the essential support. -/
theorem localConvolution_vanishes_below {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space (m + 1) → 𝕜} (hf : LocallyIntegrable f volume)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : ε < δ / 2)
    (hs : ∀ᵐ y ∂volume, y (Fin.last m) < δ → f y = 0)
    (ρ : WholeTests (m + 1) 𝕜) (hρ : tsupport ρ ⊆ Metric.closedBall 0 ε)
    {x : Space (m + 1)} (hx : x (Fin.last m) < δ / 2) :
    localConvolution (regularDistribution ⊤ f) ρ x = 0 := by
  rw [localConvolution_regular_whole hf]
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with y hy
  by_cases hyδ : y (Fin.last m) < δ
  · simp only [P102.U2.Young.integralConvolution, hy hyδ, mul_zero, Pi.zero_apply]
  · have hnot : x - y ∉ tsupport ρ := by
      intro hxy
      have hnorm : ‖x - y‖ ≤ ε := by simpa only [Metric.mem_closedBall, dist_zero_right] using hρ hxy
      have hcoord := PiLp.norm_apply_le (x - y) (Fin.last m)
      have hval : (x - y) (Fin.last m) = x (Fin.last m) - y (Fin.last m) := rfl
      rw [hval, Real.norm_eq_abs] at hcoord
      have hlow := le_abs_self (y (Fin.last m) - x (Fin.last m))
      rw [abs_sub_comm] at hlow
      linarith [not_lt.mp hyδ]
    simp only [P102.U2.Young.integralConvolution, image_eq_zero_of_notMem_tsupport hnot, zero_mul, Pi.zero_apply]

/-- The topological support, not only the pointwise support, stays inside H. -/
theorem localConvolution_tsupport_halfSpace {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space (m + 1) → 𝕜} (hf : LocallyIntegrable f volume)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : ε < δ / 2)
    (hs : ∀ᵐ y ∂volume, y (Fin.last m) < δ → f y = 0)
    (ρ : WholeTests (m + 1) 𝕜) (hρ : tsupport ρ ⊆ Metric.closedBall 0 ε) :
    tsupport (localConvolution (regularDistribution ⊤ f) ρ) ⊆ halfSpace m := by
  have hclosed : IsClosed {x : Space (m + 1) | δ / 2 ≤ x (Fin.last m)} :=
    isClosed_le continuous_const (PiLp.continuous_apply 2 _ _)
  have hsubset : Function.support (localConvolution (regularDistribution ⊤ f) ρ) ⊆
      {x : Space (m + 1) | δ / 2 ≤ x (Fin.last m)} := by
    intro x hx
    exact le_of_not_gt (fun h => hx (localConvolution_vanishes_below hf hδ hε hs ρ hρ h))
  intro x hx
  have h : δ / 2 ≤ x (Fin.last m) := closure_minimal hsubset hclosed hx
  change 0 < x (Fin.last m)
  linarith

/-- Upward translation, cutoff at infinity, and a smaller-radius mollification
approximate whole-space data supported in the closed upper half-space by
smooth compact functions whose topological supports lie in the open half-space. -/
theorem halfSpace_approximation_of_wholeSpace {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    (w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p)
    (hw : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → sobolevUnderlying w x = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ (φ : TestSpace 𝕜 (halfSpace m))
      (v : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p),
      RepresentsSobolev φ v ∧ ‖v - w‖ < η := by
  let a : ℝ → Space (m + 1) := fun δ => δ • coordinateVector (m + 1) (Fin.last m)
  have ha : Continuous a := continuous_id.smul continuous_const
  have ha0 : a 0 = 0 := zero_smul _ _
  have ht : Tendsto (fun δ => ‖translateWholeSobolev (a δ) w - w‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc := ((continuous_translateWholeSobolev hpt w).comp ha).sub (continuous_const (y := w))
    have hc' := (hc.norm.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Function.comp_apply, Pi.sub_apply, ha0, translateWholeSobolev_zero, sub_self, norm_zero] using hc'
  obtain ⟨δ, hδsmall, hδ⟩ :=
    ((tendsto_order.mp ht).2 (η / 3) (by linarith)).and self_mem_nhdsWithin |>.exists
  let z := translateWholeSobolev (a δ) w
  have hz : ∀ᵐ x ∂volume, x (Fin.last m) < δ → sobolevUnderlying z x = 0 := by
    have hwa := (measurePreserving_sub_right volume (a δ)).quasiMeasurePreserving.ae hw
    filter_upwards [hwa, translateWholeLp_ae (a δ) (sobolevUnderlying w)] with x hx he hxδ
    change translateWholeLp (a δ) (sobolevUnderlying w) x = 0
    rw [he]
    apply hx
    have hai : a δ (Fin.last m) = δ := by
      simp [a, coordinateVector, EuclideanSpace.basisFun_apply]
    change x (Fin.last m) - a δ (Fin.last m) < 0
    rw [hai]
    linarith
  obtain ⟨χ, hχ, hχone⟩ := exists_unitSobolevCutoff (m + 1)
  obtain ⟨c, hc, hcompact, hconv⟩ := wholeSpace_cutoff 1 p hpt χ hχ hχone z
  obtain ⟨N, hN⟩ := ((tendsto_order.mp hconv).2 (η / 3) (by linarith)).exists
  have hcN : ‖c N - z‖ < η / 3 := by
    simpa only [sobolevSumError_eq_norm] using hN
  have hcbelow : ∀ᵐ x ∂volume, x (Fin.last m) < δ → sobolevUnderlying (c N) x = 0 := by
    filter_upwards [hc N, hz] with x hx hzx hxδ
    rw [hx, hzx hxδ, mul_zero]
  let ρ := sobolevMollifierKernel (m + 1) 𝕜
  have hρ := sobolevMollifierKernel_conditions (m + 1) 𝕜
  obtain ⟨b, hb, _, hbconv⟩ := wholeSpace_mollification 1 p hpt ρ hρ (c N) (hcompact N)
  have hsmall := (tendsto_order.mp hbconv).2 (η / 3) (by linarith)
  have hradius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ / 2 :=
    (eventually_lt_nhds (show (0 : ℝ) < δ / 2 by linarith)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hεsmall, hε, hεδ⟩ := (hsmall.and (hpos.and hradius)).exists
  have hli : LocallyIntegrable (sobolevUnderlying (c N) : Space (m + 1) → 𝕜) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.memLp (sobolevUnderlying (c N))).locallyIntegrable (Fact.out : 1 ≤ p)
  let φ : TestSpace 𝕜 (halfSpace m) :=
    ⟨localConvolution (regularDistribution ⊤ (sobolevUnderlying (c N))) (ρ ε),
      (hb ε hε).1, (hb ε hε).2.1,
      localConvolution_tsupport_halfSpace hli hδ hεδ hcbelow (ρ ε) (hρ.2 ε hε)⟩
  refine ⟨φ, b ε, (hb ε hε).2.2.1, ?_⟩
  have hbε : ‖b ε - c N‖ < η / 3 := by
    simpa only [sobolevSumError_eq_norm] using hεsmall
  have hzsmall : ‖z - w‖ < η / 3 := hδsmall
  have htri₁ := dist_triangle (b ε) (c N) w
  have htri₂ := dist_triangle (c N) z w
  simp only [dist_eq_norm] at htri₁ htri₂
  linarith

/-- Restricting the zero extension recovers the original Sobolev class. -/
theorem restrict_flatZeroExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : HalfSobolev m 𝕜 p)
    (w : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p)
    (hw : sobolevUnderlying w = flatZeroExtension (sobolevUnderlying u)) :
    restrictWholeSobolev (halfSpace m) w = u := by
  apply sobolevUnderlying_injective (halfSpace m) 1 p
  apply Lp.ext
  have hw' := flatZeroExtension_ae (sobolevUnderlying u)
  rw [← hw] at hw'
  filter_upwards [restrictWholeLp_ae (halfSpace m) (sobolevUnderlying w),
    hw'.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (halfSpace m).isOpen.measurableSet] with x hx hwx hxH
  exact hx.trans (hwx.trans (indicator_of_mem hxH _))

/-- Sequential density by compact smooth functions in the open half-space,
with convergence in the complete Sobolev norm, including all first derivatives. -/
theorem flat_zero_trace_density :
  ∀ (m : ℕ), 1 ≤ m → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ u : HalfSobolev m 𝕜 p, HasZeroFlatTrace u → IsHalfSpaceTestLimit u := by
  intro m _hm 𝕜 _ p _ hpt u hu
  obtain ⟨w, hw⟩ := zero_trace_extension_tuple hpt u hu
  have hw0 : sobolevUnderlying w = flatZeroExtension (sobolevUnderlying u) :=
    hw (zeroSobolevIndex (m + 1) 1)
  have hwneg : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → sobolevUnderlying w x = 0 := by
    have he := flatZeroExtension_ae (sobolevUnderlying u)
    rw [← hw0] at he
    filter_upwards [he] with x hx hxneg
    rw [hx]
    apply indicator_of_notMem
    change ¬0 < x (Fin.last m)
    exact not_lt.mpr hxneg.le
  have hchoice (n : ℕ) : ∃ (φ : TestSpace 𝕜 (halfSpace m))
      (v : Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p),
      RepresentsSobolev φ v ∧ ‖v - w‖ < ((n + 1 : ℕ) : ℝ)⁻¹ :=
    halfSpace_approximation_of_wholeSpace hpt w hwneg (by positivity)
  choose φ v hrep hsmall using hchoice
  refine ⟨φ, fun n => restrictWholeSobolev (halfSpace m) (v n), ?_, ?_⟩
  · intro n α
    exact (restrictWholeLp_ae (halfSpace m) (sobolevDerivative (v n) α)).trans
      ((hrep n α).filter_mono (ae_mono Measure.restrict_le_self))
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hi : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    apply squeeze_zero (fun n => norm_nonneg _) _ hi
    intro n
    rw [← restrict_flatZeroExtension u w hw0]
    exact (restrictWholeSobolev_norm_sub_le (halfSpace m) (v n) w).trans (hsmall n).le

end P102.Trace
