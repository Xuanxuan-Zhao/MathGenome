import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzExtension
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import MathGenome.Internal.FourierSobolev.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace P102.Sobolev.Extension
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry

/-- The source's finite partition supplies the data of the fixed formula. -/
theorem localization_exists {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1)))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m))) :
    Nonempty (Localization e Ω) := by
  obtain ⟨n, C, r, a, hra, _, V, χ, _, hGV, hχ, hsum, hχ0, _, hχi⟩ :=
    finite_localization m (geometricOpen e Ω : Set (Ambient m)) hΩ
  exact ⟨{
    count := n
    chart := C
    cutoff := χ
    smooth := fun i => (hχ i).1
    compact := fun i => (hχ i).2.1
    nonneg := fun i => (hχ i).2.2
    partition := fun z hz => hsum z (hGV (subset_closure hz))
    interior_support := hχ0
    boundary_support := fun i => (hχi i).trans
      (chartImage_mono (C i).frame (C i).graphFunction (C i).center
        (hra i).2.1.le (hra i).2.2.2.le)
  }⟩

/-- Reflected points on the positive side lie on the negative side of the
same chart. This uses only the one-sided set equality in the shared geometry. -/
theorem reflectedPoint_not_mem {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    {z : Ambient m} (hzG : z ∈ G)
    (hzC : z ∈ chartImage C.frame C.graphFunction C.center C.radius C.height) :
    reflectedPoint C z ∉ G := by
  have hz : z ∈ C.frame '' (shear C.graphFunction ''
      upperCylinder C.center C.radius C.height) := by
    rw [← C.side]
    exact ⟨hzG, hzC⟩
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have hr : reflectedPoint C (C.frame (shear C.graphFunction w)) =
      C.frame (shear C.graphFunction (WithLp.toLp 2 (w.ofLp.1, -w.ofLp.2))) := by
    simp [reflectedPoint, (shear_inverse m C.graphFunction).1 w]
  rw [hr]
  intro hneg
  have hwc : WithLp.toLp 2 (w.ofLp.1, -w.ofLp.2) ∈
      cylinder C.center C.radius C.height := by
    refine ⟨hw.1, ?_⟩
    change -C.height < -w.ofLp.2 ∧ -w.ofLp.2 < C.height
    constructor <;> linarith [hw.2.1, hw.2.2, C.height_pos]
  have hnegc : C.frame (shear C.graphFunction (WithLp.toLp 2 (w.ofLp.1, -w.ofLp.2))) ∈
      chartImage C.frame C.graphFunction C.center C.radius C.height :=
    ⟨_, ⟨_, hwc, rfl⟩, rfl⟩
  have hup : C.frame (shear C.graphFunction (WithLp.toLp 2 (w.ofLp.1, -w.ofLp.2))) ∈
      C.frame '' (shear C.graphFunction '' upperCylinder C.center C.radius C.height) := by
    rw [← C.side]
    exact ⟨hneg, hnegc⟩
  obtain ⟨_, ⟨v, hv, rfl⟩, heq⟩ := hup
  have he := (shear_inverse m C.graphFunction).1.injective (C.frame.injective heq)
  have ht := congrArg (fun q : Ambient m => q.ofLp.2) he
  change v.ofLp.2 = -w.ofLp.2 at ht
  linarith [hv.2.1, hw.2.1]

/-- The fixed formula extends every ambient representative pointwise on Ω.
No integrability or exponent assumption is needed for this identity. -/
theorem rawExtension_restrict {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (f : Space (m + 1) → 𝕜) {x : Space (m + 1)} (hx : x ∈ Ω) :
    rawExtension D f x = f x := by
  classical
  have hz : e.symm x ∈ (geometricOpen e Ω : Set (Ambient m)) := by
    change e (e.symm x) ∈ Ω
    rw [e.apply_symm_apply]
    exact hx
  have hi (i : Fin D.count) :
      (chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
        (D.chart i).radius (D.chart i).height).indicator
        (fun z => localizedValue e Ω (D.cutoff i.succ) f z +
          localizedValue e Ω (D.cutoff i.succ) f (reflectedPoint (D.chart i) z)) (e.symm x) =
        D.cutoff i.succ (e.symm x) • f x := by
    by_cases hc : e.symm x ∈ chartImage (D.chart i).frame (D.chart i).graphFunction
        (D.chart i).center (D.chart i).radius (D.chart i).height
    · have hn := reflectedPoint_not_mem (D.chart i) hz hc
      simp [hc, localizedValue, hz, hn]
    · have hzero : D.cutoff i.succ (e.symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hc (D.boundary_support i ht))
      simp [hc, hzero]
  unfold rawExtension
  simp_rw [hi]
  simp only [localizedValue, indicator_of_mem hz, e.apply_symm_apply]
  rw [← Finset.sum_smul, ← add_smul, ← Fin.sum_univ_succ (fun i : Fin (D.count + 1) => D.cutoff i (e.symm x)), D.partition _ hz, one_smul]

/-- A representative-independent support container, fixed by the localization. -/
def supportContainer {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) : Set (Space (m + 1)) :=
  e '' (tsupport (D.cutoff 0) ∪ ⋃ i : Fin D.count,
    chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
      (D.chart i).radius (D.chart i).height)

theorem supportContainer_bounded {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) :
    Bornology.IsBounded (supportContainer D) := by
  apply e.isometry.lipschitzWith.isBounded_image
  exact (D.compact 0).isBounded.union (Bornology.isBounded_iUnion.mpr fun i =>
    chartImage_bounded (D.chart i).frame (D.chart i).graph_lipschitz)

theorem rawExtension_zero_outside {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (f : Space (m + 1) → 𝕜) {x : Space (m + 1)}
    (hx : x ∉ supportContainer D) : rawExtension D f x = 0 := by
  have hz : e.symm x ∉ tsupport (D.cutoff 0) ∪ ⋃ i : Fin D.count,
      chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
        (D.chart i).radius (D.chart i).height := by
    intro h
    exact hx ⟨e.symm x, h, e.apply_symm_apply x⟩
  have hzero : D.cutoff 0 (e.symm x) = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hz (Or.inl h))
  have hi (i : Fin D.count) : e.symm x ∉
      chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
        (D.chart i).radius (D.chart i).height :=
    fun h => hz (Or.inr (mem_iUnion.mpr ⟨i, h⟩))
  simp [rawExtension, localizedValue, hzero, hi]

/-- Restriction of scalar Lp classes to a smaller open set, over the original
scalar field (including complex scalars). -/
def domainLpRestrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DomainLp 𝕜 U p →L[𝕜] DomainLp 𝕜 V p := by
  let F : DomainLp 𝕜 U p →ₗ[𝕜] DomainLp 𝕜 V p := {
    toFun := fun u => ((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)).toLp u
    map_add' := by
      intro u v
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (u + v)).mono_measure
        (Measure.restrict_mono h le_rfl)),
        Lp.coeFn_add (((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)).toLp u)
          (((Lp.memLp v).mono_measure (Measure.restrict_mono h le_rfl)).toLp v),
        MemLp.coeFn_toLp ((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)),
        MemLp.coeFn_toLp ((Lp.memLp v).mono_measure (Measure.restrict_mono h le_rfl)),
        ae_mono (Measure.restrict_mono h le_rfl) (Lp.coeFn_add u v)] with x ha hb hu hv hc
      simp only [Pi.add_apply] at *
      rw [ha, hc, hb, hu, hv]
    map_smul' := by
      intro c u
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • u)).mono_measure
        (Measure.restrict_mono h le_rfl)),
        Lp.coeFn_smul c (((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)).toLp u),
        MemLp.coeFn_toLp ((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)),
        ae_mono (Measure.restrict_mono h le_rfl) (Lp.coeFn_smul c u)] with x ha hb hu hc
      simp only [Pi.smul_apply, RingHom.id_apply] at *
      rw [ha, hc, hb, hu]
  }
  apply F.mkContinuous 1
  intro u
  change ‖((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)).toLp u‖ ≤ 1 * ‖u‖
  rw [Lp.norm_toLp, one_mul, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl))

theorem domainLpRestrict_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 U p) :
    domainLpRestrict h p u =ᵐ[volume.restrict (V : Set (Space d))] u :=
  MemLp.coeFn_toLp ((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl))

theorem domainLpRestrict_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 U p) : ‖domainLpRestrict h p u‖ ≤ ‖u‖ := by
  change ‖((Lp.memLp u).mono_measure (Measure.restrict_mono h le_rfl)).toLp u‖ ≤ ‖u‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp u).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono h le_rfl))

/-- Restriction commutes with the test pairing because the test is zero
outside the smaller domain. This supplies the distributional bridge. -/
theorem lpTestPairing_restrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : TestSpace 𝕜 V) (u : DomainLp 𝕜 U p) :
    lpTestPairing V p φ (domainLpRestrict h p u) =
      lpTestPairing U p (zeroExtension 𝕜 h φ) u := by
  rw [← regularLp_pairing, ← regularLp_pairing]
  rw [regularDistribution, regularDistribution,
    TestFunction.integralAgainstBilinCLM_eq_integral (domainLp_locallyIntegrable V p _),
    TestFunction.integralAgainstBilinCLM_eq_integral (domainLp_locallyIntegrable U p _)]
  have hφ : (zeroExtension 𝕜 h φ : Space d → 𝕜) = φ := by
    simp [zeroExtension, TestFunction.monoCLM_apply, h]
  change (∫ x, φ x * domainLpRestrict h p u x) =
    ∫ x, zeroExtension 𝕜 h φ x * u x
  simp only [hφ]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' V.isOpen.measurableSet).mp (domainLpRestrict_ae h p u)] with x hx
  by_cases hxV : x ∈ V
  · rw [hx hxV]
  · simp [φ.zero_on_compl hxV]

/-- Zero extension of tests preserves each ambient partial derivative. -/
theorem zeroExtension_partialWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (l : List (Fin d)) (φ : TestSpace 𝕜 V) :
    zeroExtension 𝕜 h (testPartialWord V l φ) =
      testPartialWord U l (zeroExtension 𝕜 h φ) := by
  have hφ : (zeroExtension 𝕜 h φ : Space d → 𝕜) = φ := by
    simp [zeroExtension, TestFunction.monoCLM_apply, h]
  ext x
  simp only [zeroExtension, TestFunction.monoCLM_apply, le_refl, h, and_self, ite_true,
    testPartialWord_coe]

/-- Restriction of the complete derivative graph to an arbitrary smaller open.
No positive dimension, boundary regularity or finite-volume hypothesis is used. -/
def sobolevRestrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 U k p →L[𝕜] Sobolev 𝕜 V k p := by
  let F : Sobolev 𝕜 U k p →ₗ[𝕜] Sobolev 𝕜 V k p := {
    toFun := fun u => ⟨WithLp.toLp 1 (fun α => domainLpRestrict h p (sobolevDerivative u α)), by
      rw [mem_sobolevSubmodule_iff]
      intro α φ
      change lpTestPairing V p φ (domainLpRestrict h p (sobolevDerivative u α)) =
        (-1 : 𝕜) ^ α.val.card * lpTestPairing V p (testPartialWord V (α.val.sort (· ≤ ·)) φ)
          (domainLpRestrict h p (sobolevUnderlying u))
      rw [lpTestPairing_restrict, lpTestPairing_restrict, zeroExtension_partialWord]
      exact (mem_sobolevSubmodule_iff U k p u.val).mp u.property α (zeroExtension 𝕜 h φ)⟩
    map_add' := by
      intro u v
      apply Subtype.ext
      apply PiLp.ext
      intro α
      exact (domainLpRestrict h p).map_add _ _
    map_smul' := by
      intro c u
      apply Subtype.ext
      apply PiLp.ext
      intro α
      exact (domainLpRestrict h p).map_smul c _
  }
  apply F.mkContinuous 1
  intro u
  rw [one_mul, sobolev_norm, sobolev_norm]
  exact Finset.sum_le_sum fun α _ => domainLpRestrict_norm_le h p _

theorem sobolevRestrict_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U k p) (α : SobolevIndex d k) :
    sobolevDerivative (sobolevRestrict h k p u) α =
      domainLpRestrict h p (sobolevDerivative u α) := rfl

theorem sobolevRestrict_derivative_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U k p) (α : SobolevIndex d k) :
    sobolevDerivative (sobolevRestrict h k p u) α =ᵐ[volume.restrict (V : Set (Space d))]
      sobolevDerivative u α := domainLpRestrict_ae h p _

theorem sobolevRestrict_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U V : Opens (Space d)} (h : V ≤ U) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U k p) : ‖sobolevRestrict h k p u‖ ≤ ‖u‖ := by
  rw [sobolev_norm, sobolev_norm]
  exact Finset.sum_le_sum fun α _ => domainLpRestrict_norm_le h p _

/-- Ambient smooth representatives remain representatives of every derivative
coordinate after restriction. -/
theorem representsOn_restrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Space d → 𝕜} {u : Sobolev 𝕜 (⊤ : Opens (Space d)) k p}
    (hf : RepresentsSobolev f u) :
    RepresentsOn f (sobolevRestrict (show Ω ≤ ⊤ from le_top) k p u) := by
  intro α
  exact (sobolevRestrict_derivative_ae _ k p u α).trans (ae_restrict_of_ae (hf α))

/-- The density part of the source follows for each function once an actual
whole-space extension has been constructed. The input v here is genuine data,
not an assumed extension operator or a Sobolev membership certificate. -/
theorem ambient_approximation_of_extension {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : Sobolev 𝕜 Ω k p) (v : Sobolev 𝕜 (⊤ : Opens (Space d)) k p)
    (hv : sobolevUnderlying v =ᵐ[volume.restrict (Ω : Set (Space d))] sobolevUnderlying u) :
    ∃ (φ : ℕ → WholeTests d 𝕜) (w : ℕ → Sobolev 𝕜 Ω k p),
      (∀ n, RepresentsOn (φ n) (w n)) ∧ Tendsto w atTop (𝓝 u) := by
  obtain ⟨φ, w, hw, hlim, _⟩ := wholeSpace_density k p hp v
  let R : Sobolev 𝕜 (⊤ : Opens (Space d)) k p →L[𝕜] Sobolev 𝕜 Ω k p :=
    sobolevRestrict le_top k p
  have hRv : R v = u := by
    apply sobolevUnderlying_injective Ω k p
    apply Lp.ext
    exact (sobolevRestrict_derivative_ae le_top k p v (zeroSobolevIndex d k)).trans hv
  refine ⟨φ, fun n => R (w n), fun n => representsOn_restrict Ω k p (hw n), ?_⟩
  simpa only [Function.comp_def, hRv] using (R.continuous.tendsto v).comp hlim

/-- A compact container for all outputs of the fixed formula, independent of
both the input and its integrability exponent. -/
theorem rawExtension_compact_container {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) :
    ∃ K : Compacts (Space (m + 1)), ∀ (𝕜 : Type) [RCLike 𝕜]
      (f : Space (m + 1) → 𝕜) (x : Space (m + 1)),
      x ∉ (K : Set (Space (m + 1))) → rawExtension D f x = 0 := by
  refine ⟨⟨closure (supportContainer D), (supportContainer_bounded D).isCompact_closure⟩,
    fun 𝕜 _ f x hx => rawExtension_zero_outside D f ?_⟩
  exact fun h => hx (subset_closure h)

/-- Normal coordinate reflection in the L² product. -/
def verticalReflection {m : ℕ} (z : Ambient m) : Ambient m :=
  WithLp.toLp 2 (z.ofLp.1, -z.ofLp.2)

theorem verticalReflection_measurePreserving (m : ℕ) :
    MeasurePreserving (@verticalReflection m) volume volume := by
  have hp : MeasurePreserving (fun z : Space m × ℝ => (z.1, -z.2)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id (volume : Measure (Space m))).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact (WithLp.volume_preserving_toLp (Space m) ℝ).comp
    (hp.comp (WithLp.volume_preserving_ofLp (Space m) ℝ))

/-- The rigid frames in the geometric interface preserve Euclidean volume. -/
theorem frame_measurePreserving {m : ℕ} (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) :
    MeasurePreserving F volume volume := by
  have he : (fun z => F.linearIsometryEquiv z + F 0) = (F : Ambient m → Ambient m) := by
    funext z
    simpa only [vadd_eq_add, add_zero] using (F.map_vadd (0 : Ambient m) z).symm
  simpa only [Function.comp_def, he] using
    (measurePreserving_add_right volume (F 0)).comp F.linearIsometryEquiv.measurePreserving

/-- Global reflection associated to a globally Lipschitz graph. The original
chart graph need only agree with this graph on its tangential ball. -/
def globalReflectedPoint {m : ℕ} (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (γ : Space m → ℝ) (z : Ambient m) : Ambient m :=
  F (shear γ (verticalReflection (unshear γ (F.symm z))))

theorem globalReflectedPoint_measurePreserving {m : ℕ}
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ) (hγ : Measurable γ) :
    MeasurePreserving (globalReflectedPoint F γ) volume volume := by
  have hu : MeasurePreserving (unshear γ) volume volume := by
    rw [unshear_eq_shear_neg]
    exact shear_measurePreserving _ hγ.neg
  exact (frame_measurePreserving F).comp ((shear_measurePreserving γ hγ).comp
    ((verticalReflection_measurePreserving m).comp (hu.comp (frame_measurePreserving F.symm))))

/-- Extending the scalar graph to the whole tangential space leaves the
reflection unchanged throughout the original physical chart. -/
theorem reflectedPoint_eq_global {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    (γ : Space m → ℝ) (hγ : EqOn C.graphFunction γ (Metric.ball C.center C.radius))
    {z : Ambient m} (hz : z ∈ chartImage C.frame C.graphFunction C.center C.radius C.height) :
    reflectedPoint C z = globalReflectedPoint C.frame γ z := by
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  simp [reflectedPoint, globalReflectedPoint, verticalReflection, shear, unshear]
  rw [show C.graphFunction (WithLp.fst w) = γ (WithLp.fst w) from hγ hw.1]
  ring

/-- Localized zero extensions respect a.e. equality, before reflection. -/
theorem localizedValue_congr {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (χ : Ambient m → ℝ) {f g : Space (m + 1) → 𝕜}
    (hfg : f =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] g) :
    localizedValue e Ω χ f =ᵐ[volume] localizedValue e Ω χ g := by
  have h := e.measurePreserving.quasiMeasurePreserving.ae
    ((ae_restrict_iff' Ω.isOpen.measurableSet).mp hfg)
  filter_upwards [h] with z hz
  by_cases hze : e z ∈ Ω
  · have hzg : z ∈ (geometricOpen e Ω : Set (Ambient m)) := hze
    simp [localizedValue, hzg, hz hze]
  · have hzg : z ∉ (geometricOpen e Ω : Set (Ambient m)) := hze
    simp [localizedValue, hzg]

/-- The full fixed geometric formula is well-defined on a.e. classes. The
proof uses volume preservation of graph shears, not a smooth-boundary premise. -/
theorem rawExtension_congr {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) {f g : Space (m + 1) → 𝕜}
    (hfg : f =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] g) :
    rawExtension D f =ᵐ[volume] rawExtension D g := by
  have hi (i : Fin D.count) :
      (fun z => (chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
        (D.chart i).radius (D.chart i).height).indicator
        (fun z => localizedValue e Ω (D.cutoff i.succ) f z +
          localizedValue e Ω (D.cutoff i.succ) f (reflectedPoint (D.chart i) z)) z) =ᵐ[volume]
      (fun z => (chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
        (D.chart i).radius (D.chart i).height).indicator
        (fun z => localizedValue e Ω (D.cutoff i.succ) g z +
          localizedValue e Ω (D.cutoff i.succ) g (reflectedPoint (D.chart i) z)) z) := by
    obtain ⟨γ, hγ, heq⟩ := (D.chart i).graph_lipschitz.extend_real
    have hl := localizedValue_congr e Ω (D.cutoff i.succ) hfg
    have hr := (globalReflectedPoint_measurePreserving (D.chart i).frame γ
      hγ.continuous.measurable).quasiMeasurePreserving.ae hl
    filter_upwards [hl, hr] with z hz hzr
    by_cases hzc : z ∈ chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
        (D.chart i).radius (D.chart i).height
    · have he := reflectedPoint_eq_global (D.chart i) γ heq hzc
      simp only [indicator_of_mem hzc, hz, he, hzr]
    · simp only [indicator_of_notMem hzc]
  have hloc : (fun z => rawExtension D f (e z)) =ᵐ[volume]
      (fun z => rawExtension D g (e z)) := by
    filter_upwards [localizedValue_congr e Ω (D.cutoff 0) hfg,
      ae_all_iff.mpr hi] with z hz hzi
    simp only [rawExtension, e.symm_apply_apply]
    rw [hz]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hzi i)
  change ∀ᵐ x ∂volume, rawExtension D f x = rawExtension D g x
  simpa only [e.apply_symm_apply] using e.symm.measurePreserving.quasiMeasurePreserving.ae hloc

/-- The boundary summand of the fixed extension, in graph coordinates. -/
def boundaryValue {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin D.count) (f : Space (m + 1) → 𝕜) : Ambient m → 𝕜 :=
  (chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
    (D.chart i).radius (D.chart i).height).indicator
    (fun z => localizedValue e Ω (D.cutoff i.succ) f z +
      localizedValue e Ω (D.cutoff i.succ) f (reflectedPoint (D.chart i) z))

theorem localizedValue_eq_smul {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (χ : Ambient m → ℝ) (f : Space (m + 1) → 𝕜) :
    localizedValue e Ω χ f = χ • ((Ω : Set (Space (m + 1))).indicator f ∘ e) := by
  ext z
  by_cases hz : e z ∈ Ω
  · have hz' : z ∈ (geometricOpen e Ω : Set (Ambient m)) := hz
    simp [localizedValue, hz, hz']
  · have hz' : z ∉ (geometricOpen e Ω : Set (Ambient m)) := hz
    simp [localizedValue, hz, hz']

/-- Localized pieces have the expected zero-order integrability for every
exponent, including infinity, and either scalar field. -/
theorem localizedValue_memLp {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin (D.count + 1)) (r : ℝ≥0∞)
    {f : Space (m + 1) → 𝕜} (hf : MemLp f r (volume.restrict (Ω : Set (Space (m + 1))))) :
    MemLp (localizedValue e Ω (D.cutoff i) f) r volume := by
  have hz := (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr hf
  rw [localizedValue_eq_smul]
  exact ((D.smooth i).continuous.memLp_of_hasCompactSupport (D.compact i)
    (p := ∞) (μ := volume)).smul (hz.comp_measurePreserving e.measurePreserving)

theorem localizedValue_eLpNorm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin (D.count + 1)) (r : ℝ≥0∞)
    {f : Space (m + 1) → 𝕜} (hf : MemLp f r (volume.restrict (Ω : Set (Space (m + 1))))) :
    eLpNorm (localizedValue e Ω (D.cutoff i) f) r volume ≤
      eLpNorm (D.cutoff i) ∞ volume * eLpNorm f r (volume.restrict (Ω : Set (Space (m + 1)))) := by
  have hz := (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr hf
  rw [localizedValue_eq_smul]
  calc
    _ ≤ eLpNorm (D.cutoff i) ∞ volume *
        eLpNorm ((Ω : Set (Space (m + 1))).indicator f ∘ e) r volume :=
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm r (D.smooth i).continuous.aestronglyMeasurable
    _ = _ := by
      rw [eLpNorm_comp_measurePreserving hz.aestronglyMeasurable e.measurePreserving,
        eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet]

/-- Every local reflection admits a global measure-preserving realization
on its chart. This statement includes only genuine geometric data. -/
theorem boundaryValue_global {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) (i : Fin D.count) :
    ∃ R : Ambient m → Ambient m, MeasurePreserving R volume volume ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (f : Space (m + 1) → 𝕜),
        boundaryValue D i f =
          (chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
            (D.chart i).radius (D.chart i).height).indicator
          (localizedValue e Ω (D.cutoff i.succ) f + localizedValue e Ω (D.cutoff i.succ) f ∘ R) := by
  obtain ⟨γ, hγ, heq⟩ := (D.chart i).graph_lipschitz.extend_real
  refine ⟨globalReflectedPoint (D.chart i).frame γ,
    globalReflectedPoint_measurePreserving _ _ hγ.continuous.measurable, ?_⟩
  intro 𝕜 _ f
  ext z
  by_cases hz : z ∈ chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
      (D.chart i).radius (D.chart i).height
  · simp only [boundaryValue, indicator_of_mem hz, Pi.add_apply, Function.comp_apply,
      reflectedPoint_eq_global (D.chart i) γ heq hz]
  · simp only [boundaryValue, indicator_of_notMem hz]

theorem boundaryValue_memLp {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin D.count) (r : ℝ≥0∞)
    {f : Space (m + 1) → 𝕜} (hf : MemLp f r (volume.restrict (Ω : Set (Space (m + 1))))) :
    MemLp (boundaryValue D i f) r volume := by
  obtain ⟨R, hR, heq⟩ := boundaryValue_global D i
  rw [heq 𝕜 f]
  have hloc := localizedValue_memLp D i.succ r hf
  exact (hloc.add (hloc.comp_measurePreserving hR)).indicator
    (chartImage_open (D.chart i).frame (D.chart i).graph_lipschitz).measurableSet.nullMeasurableSet

theorem boundaryValue_eLpNorm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin D.count) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    {f : Space (m + 1) → 𝕜} (hf : MemLp f r (volume.restrict (Ω : Set (Space (m + 1))))) :
    eLpNorm (boundaryValue D i f) r volume ≤
      (2 * eLpNorm (D.cutoff i.succ) ∞ volume) *
        eLpNorm f r (volume.restrict (Ω : Set (Space (m + 1)))) := by
  obtain ⟨R, hR, heq⟩ := boundaryValue_global D i
  rw [heq 𝕜 f]
  have hloc := localizedValue_memLp D i.succ r hf
  have hbound := localizedValue_eLpNorm_le D i.succ r hf
  calc
    _ ≤ eLpNorm (localizedValue e Ω (D.cutoff i.succ) f +
        localizedValue e Ω (D.cutoff i.succ) f ∘ R) r volume :=
      eLpNorm_indicator_le _
        (chartImage_open (D.chart i).frame (D.chart i).graph_lipschitz).measurableSet.nullMeasurableSet
    _ ≤ eLpNorm (localizedValue e Ω (D.cutoff i.succ) f) r volume +
        eLpNorm (localizedValue e Ω (D.cutoff i.succ) f ∘ R) r volume :=
      eLpNorm_add_le Fact.out
    _ = eLpNorm (localizedValue e Ω (D.cutoff i.succ) f) r volume +
        eLpNorm (localizedValue e Ω (D.cutoff i.succ) f) r volume := by
      rw [eLpNorm_comp_measurePreserving hloc.aestronglyMeasurable hR]
    _ ≤ _ := by
      rw [two_mul, add_mul]
      exact add_le_add hbound hbound

/-- An exponent-independent finite zero-order bound for the fixed formula. -/
def rawLpConstant {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) : ℝ≥0∞ :=
  eLpNorm (D.cutoff 0) ∞ volume + ∑ i : Fin D.count, 2 * eLpNorm (D.cutoff i.succ) ∞ volume

theorem rawLpConstant_ne_top {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) : rawLpConstant D ≠ ⊤ := by
  have h (i : Fin (D.count + 1)) : eLpNorm (D.cutoff i) ∞ volume ≠ ⊤ :=
    ((D.smooth i).continuous.memLp_of_hasCompactSupport (D.compact i)).eLpNorm_ne_top
  simp only [rawLpConstant, ENNReal.add_ne_top, ENNReal.sum_ne_top]
  exact ⟨h 0, fun i _ => ENNReal.mul_ne_top (by norm_num) (h i.succ)⟩

theorem rawExtension_memLp {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (r : ℝ≥0∞)
    {f : Space (m + 1) → 𝕜} (hf : MemLp f r (volume.restrict (Ω : Set (Space (m + 1))))) :
    MemLp (rawExtension D f) r volume := by
  have hsum : MemLp (fun z => ∑ i : Fin D.count, boundaryValue D i f z) r volume :=
    memLp_finsetSum Finset.univ (fun i _ => boundaryValue_memLp D i r hf)
  exact ((localizedValue_memLp D 0 r hf).add hsum).comp_measurePreserving e.symm.measurePreserving

theorem rawExtension_eLpNorm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    {f : Space (m + 1) → 𝕜} (hf : MemLp f r (volume.restrict (Ω : Set (Space (m + 1))))) :
    eLpNorm (rawExtension D f) r volume ≤
      rawLpConstant D * eLpNorm f r (volume.restrict (Ω : Set (Space (m + 1)))) := by
  have hsum : MemLp (fun z => ∑ i : Fin D.count, boundaryValue D i f z) r volume :=
    memLp_finsetSum Finset.univ (fun i _ => boundaryValue_memLp D i r hf)
  have hloc := localizedValue_memLp D 0 r hf
  change eLpNorm ((localizedValue e Ω (D.cutoff 0) f +
    (fun z => ∑ i : Fin D.count, boundaryValue D i f z)) ∘ e.symm) r volume ≤ _
  rw [eLpNorm_comp_measurePreserving (hloc.add hsum).aestronglyMeasurable e.symm.measurePreserving]
  calc
    _ ≤ eLpNorm (localizedValue e Ω (D.cutoff 0) f) r volume +
        eLpNorm (fun z => ∑ i : Fin D.count, boundaryValue D i f z) r volume :=
      eLpNorm_add_le Fact.out
    _ ≤ eLpNorm (D.cutoff 0) ∞ volume *
          eLpNorm f r (volume.restrict (Ω : Set (Space (m + 1)))) +
        ∑ i : Fin D.count, (2 * eLpNorm (D.cutoff i.succ) ∞ volume) *
          eLpNorm f r (volume.restrict (Ω : Set (Space (m + 1)))) := by
      apply add_le_add (localizedValue_eLpNorm_le D 0 r hf)
      rw [show (fun z => ∑ i : Fin D.count, boundaryValue D i f z) =
        ∑ i : Fin D.count, boundaryValue D i f from by ext z; simp]
      exact (eLpNorm_sum_le (μ := volume) (f := fun i => boundaryValue D i f)
        (s := Finset.univ) Fact.out).trans
          (Finset.sum_le_sum fun i _ => boundaryValue_eLpNorm_le D i r hf)
    _ = _ := by rw [rawLpConstant, add_mul, Finset.sum_mul]

theorem localizedValue_add {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (χ : Ambient m → ℝ) (f g : Space (m + 1) → 𝕜) :
    localizedValue e Ω χ (f + g) = localizedValue e Ω χ f + localizedValue e Ω χ g := by
  ext z
  by_cases hz : z ∈ (geometricOpen e Ω : Set (Ambient m)) <;>
    simp [localizedValue, hz, smul_add]

theorem localizedValue_smul {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (χ : Ambient m → ℝ) (c : 𝕜) (f : Space (m + 1) → 𝕜) :
    localizedValue e Ω χ (c • f) = c • localizedValue e Ω χ f := by
  ext z
  by_cases hz : z ∈ (geometricOpen e Ω : Set (Ambient m)) <;>
    simp [localizedValue, hz]

theorem boundaryValue_add {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin D.count) (f g : Space (m + 1) → 𝕜) :
    boundaryValue D i (f + g) = boundaryValue D i f + boundaryValue D i g := by
  ext z
  by_cases hz : z ∈ chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
      (D.chart i).radius (D.chart i).height
  · simp [boundaryValue, hz, localizedValue_add, add_add_add_comm]
  · simp [boundaryValue, hz]

theorem boundaryValue_smul {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin D.count) (c : 𝕜) (f : Space (m + 1) → 𝕜) :
    boundaryValue D i (c • f) = c • boundaryValue D i f := by
  ext z
  by_cases hz : z ∈ chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
      (D.chart i).radius (D.chart i).height <;>
    simp [boundaryValue, hz, localizedValue_smul, mul_add]

theorem rawExtension_add {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (f g : Space (m + 1) → 𝕜) :
    rawExtension D (f + g) = rawExtension D f + rawExtension D g := by
  ext x
  change localizedValue e Ω (D.cutoff 0) (f + g) (e.symm x) +
      ∑ i, boundaryValue D i (f + g) (e.symm x) =
    (localizedValue e Ω (D.cutoff 0) f (e.symm x) + ∑ i, boundaryValue D i f (e.symm x)) +
    (localizedValue e Ω (D.cutoff 0) g (e.symm x) + ∑ i, boundaryValue D i g (e.symm x))
  simp only [localizedValue_add, boundaryValue_add, Pi.add_apply, Finset.sum_add_distrib]
  abel

theorem rawExtension_smul {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (c : 𝕜) (f : Space (m + 1) → 𝕜) :
    rawExtension D (c • f) = c • rawExtension D f := by
  ext x
  change localizedValue e Ω (D.cutoff 0) (c • f) (e.symm x) +
      ∑ i, boundaryValue D i (c • f) (e.symm x) =
    c • (localizedValue e Ω (D.cutoff 0) f (e.symm x) + ∑ i, boundaryValue D i f (e.symm x))
  simp only [localizedValue_smul, boundaryValue_smul, Pi.smul_apply, smul_add, Finset.smul_sum]

/-- The fixed reflection formula already defines a bounded scalar-linear
extension on every Lp space. The Sobolev mapping property is a further obligation. -/
def lpExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DomainLp 𝕜 Ω p →L[𝕜] Lp 𝕜 p (volume : Measure (Space (m + 1))) := by
  let F : DomainLp 𝕜 Ω p →ₗ[𝕜] Lp 𝕜 p (volume : Measure (Space (m + 1))) := {
    toFun := fun u => (rawExtension_memLp D p (Lp.memLp u)).toLp (rawExtension D u)
    map_add' := by
      intro u v
      apply Lp.ext
      have h := rawExtension_congr D (Lp.coeFn_add u v)
      filter_upwards [MemLp.coeFn_toLp (rawExtension_memLp D p (Lp.memLp (u + v))),
        MemLp.coeFn_toLp (rawExtension_memLp D p (Lp.memLp u)),
        MemLp.coeFn_toLp (rawExtension_memLp D p (Lp.memLp v)),
        Lp.coeFn_add ((rawExtension_memLp D p (Lp.memLp u)).toLp (rawExtension D u))
          ((rawExtension_memLp D p (Lp.memLp v)).toLp (rawExtension D v)), h] with x ha hu hv hb hx
      rw [ha, hx, rawExtension_add, Pi.add_apply, hb, Pi.add_apply, hu, hv]
    map_smul' := by
      intro c u
      apply Lp.ext
      have h := rawExtension_congr D (Lp.coeFn_smul c u)
      filter_upwards [MemLp.coeFn_toLp (rawExtension_memLp D p (Lp.memLp (c • u))),
        MemLp.coeFn_toLp (rawExtension_memLp D p (Lp.memLp u)),
        Lp.coeFn_smul c ((rawExtension_memLp D p (Lp.memLp u)).toLp (rawExtension D u)), h]
          with x ha hu hb hx
      simp only [RingHom.id_apply]
      rw [ha, hx, rawExtension_smul, Pi.smul_apply, hb, Pi.smul_apply, hu]
  }
  apply F.mkContinuous (rawLpConstant D).toReal
  intro u
  change ‖(rawExtension_memLp D p (Lp.memLp u)).toLp (rawExtension D u)‖ ≤ _
  rw [Lp.norm_toLp]
  calc
    _ ≤ (rawLpConstant D * eLpNorm u p (volume.restrict (Ω : Set (Space (m + 1))))).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (rawLpConstant_ne_top D) (Lp.memLp u).eLpNorm_ne_top)
        (rawExtension_eLpNorm_le D p (Lp.memLp u))
    _ = _ := by rw [ENNReal.toReal_mul, Lp.norm_def]

theorem lpExtension_ae {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p) :
    lpExtension D p u =ᵐ[volume] rawExtension D u :=
  MemLp.coeFn_toLp (rawExtension_memLp D p (Lp.memLp u))

theorem lpExtension_restrict_ae {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p) :
    lpExtension D p u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] u := by
  filter_upwards [ae_restrict_of_ae (lpExtension_ae D p u),
    ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  exact hx.trans (rawExtension_restrict D u hxΩ)

/-- On intersections of exponent spaces the constructed Lp extensions agree. -/
theorem lpExtension_compatible {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (u : DomainLp 𝕜 Ω p) (v : DomainLp 𝕜 Ω q)
    (huv : u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] v) :
    lpExtension D p u =ᵐ[volume] lpExtension D q v :=
  (lpExtension_ae D p u).trans ((rawExtension_congr D huv).trans (lpExtension_ae D q v).symm)

theorem lpExtension_norm_le {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖(lpExtension D p : DomainLp 𝕜 Ω p →L[𝕜] Lp 𝕜 p volume)‖ ≤ (rawLpConstant D).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  intro u
  rw [Lp.norm_def, eLpNorm_congr_ae (lpExtension_ae D p u)]
  calc
    _ ≤ (rawLpConstant D * eLpNorm u p (volume.restrict (Ω : Set (Space (m + 1))))).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (rawLpConstant_ne_top D) (Lp.memLp u).eLpNorm_ne_top)
        (rawExtension_eLpNorm_le D p (Lp.memLp u))
    _ = _ := by rw [ENNReal.toReal_mul, Lp.norm_def]

/-! Multipliers on arbitrary opens. These lemmas use the distributional product
rule and place no boundedness assumption on the Sobolev input. -/

/-- A scalar test has a finite uniform bound on the whole ambient space. -/
def testBound {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (a : WholeTests d 𝕜) : ℝ≥0 :=
  ⟨max 0 (a.hasCompactSupport.exists_bound_of_continuous a.continuous).choose,
    le_max_left _ _⟩

theorem norm_le_testBound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : WholeTests d 𝕜) (x : Space d) : ‖a x‖ ≤ testBound a :=
  ((a.hasCompactSupport.exists_bound_of_continuous a.continuous).choose_spec x).trans
    (le_max_right _ _)

/-- Multiplication on domain Lp classes by an ambient smooth compact function. -/
def domainTestMul {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d 𝕜) :
    DomainLp 𝕜 Ω p →L[𝕜] DomainLp 𝕜 Ω p := by
  let hm (f : DomainLp 𝕜 Ω p) :
      MemLp (fun x => a x * f x) p (volume.restrict (Ω : Set (Space d))) :=
    (a.continuous.memLp_of_hasCompactSupport (p := ⊤) a.hasCompactSupport).mul
      (Lp.memLp f)
  let F : DomainLp 𝕜 Ω p →ₗ[𝕜] DomainLp 𝕜 Ω p := {
    toFun := fun f => (hm f).toLp _
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hm (f + g)).coeFn_toLp, (hm f).coeFn_toLp,
        (hm g).coeFn_toLp, Lp.coeFn_add f g,
        Lp.coeFn_add ((hm f).toLp _) ((hm g).toLp _)] with x hfg hf hg hs ht
      simp only [Pi.add_apply] at *
      rw [hfg, hs, ht, hf, hg, mul_add]
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(hm (c • f)).coeFn_toLp, (hm f).coeFn_toLp,
        Lp.coeFn_smul c f, Lp.coeFn_smul c ((hm f).toLp _)] with x hcf hf hs ht
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
      rw [hcf, hs, ht, hf]
      ring
  }
  apply F.mkContinuous (testBound a)
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(hm f).coeFn_toLp] with x hx
  change ‖(hm f).toLp _ x‖ ≤ _
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_testBound a x) (norm_nonneg _)

theorem domainTestMul_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d 𝕜)
    (f : DomainLp 𝕜 Ω p) :
    domainTestMul Ω p a f =ᵐ[volume.restrict (Ω : Set (Space d))]
      (fun x => a x * f x) :=
  ((a.continuous.memLp_of_hasCompactSupport (p := ⊤) a.hasCompactSupport).mul
    (Lp.memLp f) : MemLp _ p _).coeFn_toLp

theorem domainTestMul_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d 𝕜) :
    ‖domainTestMul Ω p a‖ ≤ testBound a := by
  apply ContinuousLinearMap.opNorm_le_bound _ (testBound a).coe_nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [domainTestMul_ae Ω p a f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_testBound a x) (norm_nonneg _)

/-- The actual distribution associated with a domain product. -/
theorem regular_domainTestMul {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (f : DomainLp 𝕜 Ω p) :
    regularDistribution Ω (domainTestMul Ω p a f) =
      distributionMultiplier ⟨a, a.contDiff.contDiffOn⟩ (regularDistribution Ω f) := by
  ext φ
  rw [distributionMultiplier_apply, regular_pairing d 𝕜 Ω _
    (domainLp_locallyIntegrable Ω p _), regular_pairing d 𝕜 Ω _
    (domainLp_locallyIntegrable Ω p _)]
  apply integral_congr_ae
  filter_upwards [domainTestMul_ae Ω p a f] with x hx
  change domainTestMul Ω p a f x * φ x = f x * (a x * φ x)
  rw [hx]
  ring

/-- The weak product identity includes unbounded u and the exponent infinity. -/
theorem domainTestMul_weakDerivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) (j : Fin d) :
    distributionPartial {j} (regularDistribution Ω
      (domainTestMul Ω p a (sobolevUnderlying u))) =
      regularDistribution Ω (domainTestMul Ω p (testPartialWord ⊤ [j] a)
        (sobolevUnderlying u) + domainTestMul Ω p a (firstWeakDerivative u j)) := by
  have hc : (⟨testPartialWord ⊤ [j] a, (testPartialWord ⊤ [j] a).contDiff.contDiffOn⟩ :
      SmoothCoefficient 𝕜 Ω) = coefficientPartial j ⟨a, a.contDiff.contDiffOn⟩ := by
    apply Subtype.ext
    exact testPartialWord_coe ⊤ [j] a
  have hadd (f g : DomainLp 𝕜 Ω p) :
      regularDistribution Ω (f + g) = regularDistribution Ω f + regularDistribution Ω g := by
    ext φ
    simp only [regularLp_pairing Ω p, map_add, add_apply]
  have hd := sobolev_derivative_distribution Ω 1 p u (firstSobolevIndex j)
  change distributionPartial {j} (regularDistribution Ω (sobolevUnderlying u)) =
    regularDistribution Ω (firstWeakDerivative u j) at hd
  rw [regular_domainTestMul, distributionMultiplier_productRule, hd, hadd,
    regular_domainTestMul, regular_domainTestMul, hc]

/-- Existence in the canonical graph, with all first derivatives identified. -/
theorem domainTestMul_sobolev_exists {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) :
    ∃ v : Sobolev 𝕜 Ω 1 p,
      sobolevUnderlying v = domainTestMul Ω p a (sobolevUnderlying u) ∧
      ∀ j : Fin d, firstWeakDerivative v j =
        domainTestMul Ω p (testPartialWord ⊤ [j] a) (sobolevUnderlying u) +
          domainTestMul Ω p a (firstWeakDerivative u j) :=
  firstOrder_graph Ω p _ _ (domainTestMul_weakDerivative Ω p a u)

/-- Each coordinate of the canonical Sobolev graph is bounded by its sum norm. -/
theorem sobolevCoordinate_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω k p) (α : SobolevIndex d k) :
    ‖sobolevDerivative u α‖ ≤ ‖u‖ := by
  rw [sobolev_norm]
  exact Finset.single_le_sum (fun β _ => norm_nonneg (sobolevDerivative u β))
    (Finset.mem_univ α)

/-- A convenient finite multiplier bound, independent of the function exponent. -/
def testSobolevBound {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (a : WholeTests d 𝕜) : ℝ≥0 :=
  testBound a + ∑ j : Fin d, (testBound (testPartialWord ⊤ [j] a) + testBound a)

private def domainTestMulSobolevValue {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) : Sobolev 𝕜 Ω 1 p :=
  (domainTestMul_sobolev_exists Ω p a u).choose

private theorem domainTestMulSobolevValue_underlying {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) :
    sobolevUnderlying (domainTestMulSobolevValue Ω p a u) =
      domainTestMul Ω p a (sobolevUnderlying u) :=
  (domainTestMul_sobolev_exists Ω p a u).choose_spec.1

private theorem domainTestMulSobolevValue_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) (j : Fin d) :
    firstWeakDerivative (domainTestMulSobolevValue Ω p a u) j =
      domainTestMul Ω p (testPartialWord ⊤ [j] a) (sobolevUnderlying u) +
        domainTestMul Ω p a (firstWeakDerivative u j) :=
  (domainTestMul_sobolev_exists Ω p a u).choose_spec.2 j

private def domainTestMulSobolevLinear {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) : Sobolev 𝕜 Ω 1 p →ₗ[𝕜] Sobolev 𝕜 Ω 1 p where
  toFun := domainTestMulSobolevValue Ω p a
  map_add' u v := by
    apply sobolevUnderlying_injective Ω 1 p
    change sobolevUnderlying (domainTestMulSobolevValue Ω p a (u + v)) =
      sobolevUnderlying (domainTestMulSobolevValue Ω p a u) +
        sobolevUnderlying (domainTestMulSobolevValue Ω p a v)
    simp only [domainTestMulSobolevValue_underlying]
    exact (domainTestMul Ω p a).map_add _ _
  map_smul' c u := by
    apply sobolevUnderlying_injective Ω 1 p
    change sobolevUnderlying (domainTestMulSobolevValue Ω p a (c • u)) =
      c • sobolevUnderlying (domainTestMulSobolevValue Ω p a u)
    simp only [domainTestMulSobolevValue_underlying]
    exact (domainTestMul Ω p a).map_smul c _

private theorem domainTestMulSobolevLinear_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) :
    ‖domainTestMulSobolevLinear Ω p a u‖ ≤ testSobolevBound a * ‖u‖ := by
  have hmul (b : WholeTests d 𝕜) (α : SobolevIndex d 1) :
      ‖domainTestMul Ω p b (sobolevDerivative u α)‖ ≤ testBound b * ‖u‖ :=
    ((domainTestMul Ω p b).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (domainTestMul_norm_le Ω p b) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (sobolevCoordinate_norm_le u α) (testBound b).coe_nonneg))
  change ‖domainTestMulSobolevValue Ω p a u‖ ≤ _
  rw [BiLipschitzPullback.sobolev_firstOrder_norm,
    domainTestMulSobolevValue_underlying]
  simp only [domainTestMulSobolevValue_derivative]
  calc
    _ ≤ (testBound a : ℝ) * ‖u‖ + ∑ j : Fin d,
        ((testBound (testPartialWord ⊤ [j] a) : ℝ) * ‖u‖ + (testBound a : ℝ) * ‖u‖) :=
      add_le_add (hmul a (zeroSobolevIndex d 1))
        (Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans
          (add_le_add (hmul _ (zeroSobolevIndex d 1)) (hmul a (firstSobolevIndex j))))
    _ = _ := by simp only [testSobolevBound, NNReal.coe_add, NNReal.coe_sum,
        add_mul, Finset.sum_mul]

/-- Bounded scalar-linear cutoff multiplication on W¹ᵖ of any open set. -/
def domainTestMulSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d 𝕜) :
    Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 Ω 1 p :=
  (domainTestMulSobolevLinear Ω p a).mkContinuous (testSobolevBound a)
    (domainTestMulSobolevLinear_bound Ω p a)

theorem domainTestMulSobolev_underlying {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) :
    sobolevUnderlying (domainTestMulSobolev Ω p a u) =
      domainTestMul Ω p a (sobolevUnderlying u) :=
  domainTestMulSobolevValue_underlying Ω p a u

theorem domainTestMulSobolev_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 Ω 1 p) (j : Fin d) :
    firstWeakDerivative (domainTestMulSobolev Ω p a u) j =
      domainTestMul Ω p (testPartialWord ⊤ [j] a) (sobolevUnderlying u) +
        domainTestMul Ω p a (firstWeakDerivative u j) :=
  domainTestMulSobolevValue_derivative Ω p a u j

theorem domainTestMulSobolev_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d 𝕜) :
    ‖domainTestMulSobolev Ω p a‖ ≤ testSobolevBound a :=
  LinearMap.mkContinuous_norm_le _ (testSobolevBound a).coe_nonneg
    (domainTestMulSobolevLinear_bound Ω p a)

/-! Relative zero extension. The compact container may meet the genuine
boundary of V; only its intersection with V must lie inside the source open U.
Thus this lemma crosses artificial chart edges without imposing zero trace on
an actual domain boundary. -/

/-- Zero extension from U followed by restriction to V on Lp classes. -/
def relativeZeroLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DomainLp 𝕜 U p →L[𝕜] DomainLp 𝕜 V p :=
  (domainLpRestrict (show V ≤ ⊤ from le_top) p).comp
    (lpZeroExtensionLI U p).toContinuousLinearMap

theorem relativeZeroLp_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 U p) :
    relativeZeroLp U V p u =ᵐ[volume.restrict (V : Set (Space d))]
      (U : Set (Space d)).indicator u :=
  (domainLpRestrict_ae le_top p _).trans (ae_restrict_of_ae (lpZeroExtension_ae U p u))

theorem relativeZeroLp_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 U p) :
    ‖relativeZeroLp U V p u‖ ≤ ‖u‖ := by
  exact (domainLpRestrict_norm_le le_top p _).trans
    (le_of_eq ((lpZeroExtensionLI U p).norm_map u))

/-- Test integrals can be evaluated back on U, since the test is zero off V. -/
theorem relativeZeroLp_pairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : TestSpace 𝕜 V) (u : DomainLp 𝕜 U p) :
    lpTestPairing V p φ (relativeZeroLp U V p u) = ∫ x in U, u x * φ x := by
  change lpTestPairing V p φ (domainLpRestrict le_top p (lpZeroExtension U p u)) = _
  rw [lpTestPairing_restrict, lpTestPairing_eq_integral]
  simp only [Opens.coe_top, Measure.restrict_univ]
  have hφ : (zeroExtension 𝕜 (show V ≤ ⊤ from le_top) φ : Space d → 𝕜) = φ := by
    simp [zeroExtension, TestFunction.monoCLM_apply]
  rw [hφ]
  exact integral_lpZeroExtension_mul U p u φ

/-- Every weak equation transfers across the artificial boundary, at all p≥1. -/
theorem relativeZero_sobolev_mem {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hu : ∀ᵐ x ∂volume.restrict (U : Set (Space d)), x ∉ K → sobolevUnderlying u x = 0) :
    WithLp.toLp 1 (fun α => relativeZeroLp U V p (sobolevDerivative u α)) ∈
      sobolevSubmodule 𝕜 V k p := by
  apply (mem_sobolevSubmodule_iff V k p _).mpr
  intro α φ
  let Kφ : Compacts (Space d) :=
    ⟨(K : Set (Space d)) ∩ tsupport φ, K.isCompact.inter_right (isClosed_tsupport φ)⟩
  have hKφ : (Kφ : Set (Space d)) ⊆ U :=
    fun x hx => hKV ⟨hx.1, φ.tsupport_subset hx.2⟩
  obtain ⟨χ, _, N, hKN, _, hχ⟩ := cutoff d U Kφ hKφ
  let χk : TestSpace 𝕜 U :=
    TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  let ψ : TestSpace 𝕜 U := ⟨fun x => χk x * φ x,
    χk.contDiff.mul φ.contDiff, χk.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans χk.tsupport_subset⟩
  have hnear (x : Space d) (hx : x ∈ K) : (ψ : Space d → 𝕜) =ᶠ[𝓝 x] φ := by
    by_cases hφ : x ∈ tsupport φ
    · filter_upwards [N.isOpen.mem_nhds (hKN ⟨hx, hφ⟩)] with y hy
      change (RCLike.ofReal (χ y)) * φ y = φ y
      simp only [hχ y hy, RCLike.ofReal_one, one_mul]
    · filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hφ] with y hy
      change χk y * φ y = φ y
      simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  have hder (x : Space d) (hx : x ∈ K) :
      testPartialWord U (α.val.sort (· ≤ ·)) ψ x =
        testPartialWord V (α.val.sort (· ≤ ·)) φ x := by
    simp only [testPartialWord_coe]
    exact (partialWord_eventuallyEq (hnear x hx) _).eq_of_nhds
  have hleft : (∫ x in U, sobolevDerivative u α x * φ x) =
      ∫ x in U, sobolevDerivative u α x * ψ x := by
    apply integral_congr_ae
    filter_upwards [sobolevDerivative_zero_off_compact U k p u K hu α] with x hx
    by_cases hxK : x ∈ K
    · rw [(hnear x hxK).eq_of_nhds]
    · simp only [hx hxK, zero_mul]
  have hright : (∫ x in U, sobolevUnderlying u x *
      testPartialWord V (α.val.sort (· ≤ ·)) φ x) =
      ∫ x in U, sobolevUnderlying u x * testPartialWord U (α.val.sort (· ≤ ·)) ψ x := by
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    by_cases hxK : x ∈ K
    · rw [hder x hxK]
    · simp only [hx hxK, zero_mul]
  change lpTestPairing V p φ (relativeZeroLp U V p (sobolevDerivative u α)) =
    (-1 : 𝕜) ^ α.val.card * lpTestPairing V p
      (testPartialWord V (α.val.sort (· ≤ ·)) φ) (relativeZeroLp U V p (sobolevUnderlying u))
  rw [relativeZeroLp_pairing, relativeZeroLp_pairing, hleft, hright]
  have hw := (mem_sobolevSubmodule_iff U k p u.val).mp u.property α ψ
  change lpTestPairing U p ψ (sobolevDerivative u α) =
    (-1 : 𝕜) ^ α.val.card * lpTestPairing U p
      (testPartialWord U (α.val.sort (· ≤ ·)) ψ) (sobolevUnderlying u) at hw
  simpa only [lpTestPairing_eq_integral] using hw

/-- Relative zero extension in the actual graph, with every derivative retained. -/
def relativeZeroSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hu : ∀ᵐ x ∂volume.restrict (U : Set (Space d)), x ∉ K → sobolevUnderlying u x = 0) :
    Sobolev 𝕜 V k p :=
  ⟨WithLp.toLp 1 (fun α => relativeZeroLp U V p (sobolevDerivative u α)),
    relativeZero_sobolev_mem U V k p u K hKV hu⟩

theorem relativeZeroSobolev_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hu : ∀ᵐ x ∂volume.restrict (U : Set (Space d)), x ∉ K → sobolevUnderlying u x = 0)
    (α : SobolevIndex d k) :
    sobolevDerivative (relativeZeroSobolev U V k p u K hKV hu) α =
      relativeZeroLp U V p (sobolevDerivative u α) := rfl

theorem relativeZeroSobolev_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hu : ∀ᵐ x ∂volume.restrict (U : Set (Space d)), x ∉ K → sobolevUnderlying u x = 0) :
    ‖relativeZeroSobolev U V k p u K hKV hu‖ ≤ ‖u‖ := by
  rw [sobolev_norm, sobolev_norm]
  exact Finset.sum_le_sum fun α _ => relativeZeroLp_norm_le U V p _




/-- Relative zero extension applied to a bounded linear family with common compact support. -/
def relativeZeroOperator {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : X →L[𝕜] Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hT : ∀ u, ∀ᵐ x ∂volume.restrict (U : Set (Space d)),
      x ∉ K → sobolevUnderlying (T u) x = 0) :
    X →L[𝕜] Sobolev 𝕜 V k p := by
  let F : X →ₗ[𝕜] Sobolev 𝕜 V k p := {
    toFun := fun u => relativeZeroSobolev U V k p (T u) K hKV (hT u)
    map_add' := by
      intro u v
      apply sobolevUnderlying_injective V k p
      change relativeZeroLp U V p (sobolevUnderlying (T (u + v))) =
        relativeZeroLp U V p (sobolevUnderlying (T u)) +
          relativeZeroLp U V p (sobolevUnderlying (T v))
      rw [map_add]
      change relativeZeroLp U V p (sobolevUnderlying (T u) + sobolevUnderlying (T v)) = _
      exact (relativeZeroLp U V p).map_add _ _
    map_smul' := by
      intro c u
      apply sobolevUnderlying_injective V k p
      change relativeZeroLp U V p (sobolevUnderlying (T (c • u))) =
        c • relativeZeroLp U V p (sobolevUnderlying (T u))
      rw [map_smul]
      change relativeZeroLp U V p (c • sobolevUnderlying (T u)) = _
      exact (relativeZeroLp U V p).map_smul c _
  }
  exact F.mkContinuous ‖T‖ fun u =>
    (relativeZeroSobolev_norm_le U V k p (T u) K hKV (hT u)).trans (T.le_opNorm u)

theorem relativeZeroOperator_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : X →L[𝕜] Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hT : ∀ u, ∀ᵐ x ∂volume.restrict (U : Set (Space d)),
      x ∉ K → sobolevUnderlying (T u) x = 0)
    (u : X) (α : SobolevIndex d k) :
    sobolevDerivative (relativeZeroOperator U V k p T K hKV hT u) α =
      relativeZeroLp U V p (sobolevDerivative (T u) α) := rfl

theorem relativeZeroOperator_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : X →L[𝕜] Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hT : ∀ u, ∀ᵐ x ∂volume.restrict (U : Set (Space d)),
      x ∉ K → sobolevUnderlying (T u) x = 0) :
    ‖relativeZeroOperator U V k p T K hKV hT‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro u
  exact (relativeZeroSobolev_norm_le U V k p (T u) K hKV (hT u)).trans (T.le_opNorm u)

 theorem relativeZeroOperator_underlying_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (U V : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : X →L[𝕜] Sobolev 𝕜 U k p) (K : Compacts (Space d))
    (hKV : (K : Set (Space d)) ∩ (V : Set (Space d)) ⊆ U)
    (hT : ∀ u, ∀ᵐ x ∂volume.restrict (U : Set (Space d)),
      x ∉ K → sobolevUnderlying (T u) x = 0) (u : X) :
    sobolevUnderlying (relativeZeroOperator U V k p T K hKV hT u) =ᵐ[
      volume.restrict (V : Set (Space d))]
        (U : Set (Space d)).indicator (sobolevUnderlying (T u)) :=
  relativeZeroLp_ae U V p _

/-- Every cutoff product vanishes outside the cutoff's fixed compact support. -/
theorem domainTestMulSobolev_zero_off_support {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (u : Sobolev 𝕜 U 1 p) :
    ∀ᵐ x ∂volume.restrict (U : Set (Space d)),
      x ∉ tsupport a → sobolevUnderlying (domainTestMulSobolev U p a u) x = 0 := by
  rw [domainTestMulSobolev_underlying]
  filter_upwards [domainTestMul_ae U p a (sobolevUnderlying u)] with x hx hxK
  rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul]

/-- A multiplier followed by relative zero extension is bounded on the full source Sobolev space. -/
def relativeCutoffSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜)
    (ha : tsupport a ∩ (V : Set (Space d)) ⊆ U) :
    Sobolev 𝕜 U 1 p →L[𝕜] Sobolev 𝕜 V 1 p :=
  relativeZeroOperator U V 1 p (domainTestMulSobolev U p a)
    ⟨tsupport a, a.hasCompactSupport⟩ ha
    (domainTestMulSobolev_zero_off_support U p a)

/-- Relative zero extension adds no loss to the cutoff multiplier bound. -/
theorem relativeCutoffSobolev_norm_le_operator {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜)
    (ha : tsupport a ∩ (V : Set (Space d)) ⊆ U) :
    ‖relativeCutoffSobolev U V p a ha‖ ≤ ‖domainTestMulSobolev U p a‖ :=
  relativeZeroOperator_norm_le U V 1 p (domainTestMulSobolev U p a)
    ⟨tsupport a, a.hasCompactSupport⟩ ha
    (domainTestMulSobolev_zero_off_support U p a)

theorem relativeCutoffSobolev_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜)
    (ha : tsupport a ∩ (V : Set (Space d)) ⊆ U) :
    ‖relativeCutoffSobolev U V p a ha‖ ≤ testSobolevBound a :=
  (relativeZeroOperator_norm_le U V 1 p (domainTestMulSobolev U p a)
    ⟨tsupport a, a.hasCompactSupport⟩ ha
    (domainTestMulSobolev_zero_off_support U p a)).trans
      (domainTestMulSobolev_norm_le U p a)

/-- On the target open the artificial zero extension has the ordinary product formula. -/
theorem relativeCutoffSobolev_underlying_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜)
    (ha : tsupport a ∩ (V : Set (Space d)) ⊆ U)
    (u : Sobolev 𝕜 U 1 p) :
    sobolevUnderlying (relativeCutoffSobolev U V p a ha u) =ᵐ[
      volume.restrict (V : Set (Space d))] fun x => a x * sobolevUnderlying u x := by
  have hm := (ae_restrict_iff' U.isOpen.measurableSet).mp
    (domainTestMul_ae U p a (sobolevUnderlying u))
  have hz := relativeZeroOperator_underlying_ae U V 1 p (domainTestMulSobolev U p a)
    ⟨tsupport a, a.hasCompactSupport⟩ ha
    (domainTestMulSobolev_zero_off_support U p a) u
  filter_upwards [hz, ae_restrict_of_ae hm, self_mem_ae_restrict V.isOpen.measurableSet]
    with x hx hmul hxV
  change sobolevUnderlying (relativeZeroOperator U V 1 p (domainTestMulSobolev U p a)
    ⟨tsupport a, a.hasCompactSupport⟩ ha
    (domainTestMulSobolev_zero_off_support U p a) u) x = _
  rw [hx]
  by_cases hxU : x ∈ U
  · rw [indicator_of_mem hxU, domainTestMulSobolev_underlying, hmul hxU]
  · rw [indicator_of_notMem hxU]
    have hxa : x ∉ tsupport a := fun h => hxU (ha ⟨h, hxV⟩)
    rw [image_eq_zero_of_notMem_tsupport hxa, zero_mul]




theorem domainTestMul_norm_le_of_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (A : ℝ≥0) (ha : ∀ x, ‖a x‖ ≤ A) :
    ‖domainTestMul Ω p a‖ ≤ A := by
  apply ContinuousLinearMap.opNorm_le_bound _ A.coe_nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [domainTestMul_ae Ω p a f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (ha x) (norm_nonneg _)

theorem domainTestMulSobolev_norm_le_of_bounds {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WholeTests d 𝕜) (A : ℝ≥0) (B : Fin d → ℝ≥0)
    (ha : ∀ x, ‖a x‖ ≤ A)
    (hb : ∀ j x, ‖testPartialWord ⊤ [j] a x‖ ≤ B j) :
    ‖domainTestMulSobolev Ω p a‖ ≤ A + ∑ j, (B j + A) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have hm (b : WholeTests d 𝕜) (C : ℝ≥0) (hc : ∀ x, ‖b x‖ ≤ C)
      (α : SobolevIndex d 1) :
      ‖domainTestMul Ω p b (sobolevDerivative u α)‖ ≤ C * ‖u‖ :=
    ((domainTestMul Ω p b).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (domainTestMul_norm_le_of_bound Ω p b C hc)
        (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (sobolevCoordinate_norm_le u α) C.coe_nonneg))
  rw [BiLipschitzPullback.sobolev_firstOrder_norm, domainTestMulSobolev_underlying]
  simp only [domainTestMulSobolev_derivative]
  calc
    _ ≤ (A : ℝ) * ‖u‖ + ∑ j : Fin d,
        ((B j : ℝ) * ‖u‖ + (A : ℝ) * ‖u‖) :=
      add_le_add (hm a A ha (zeroSobolevIndex d 1))
        (Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans
          (add_le_add (hm _ (B j) (hb j) (zeroSobolevIndex d 1))
            (hm a A ha (firstSobolevIndex j))))
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_sum, add_mul, Finset.sum_mul]

/-- A real cutoff, viewed in either scalar field. -/
def scalarTest {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (a : WholeTests d ℝ) :
    WholeTests d 𝕜 :=
  TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) a

theorem scalarTest_partial {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (a : WholeTests d ℝ) (j : Fin d) (x : Space d) :
    testPartialWord ⊤ [j] (scalarTest 𝕜 a) x =
      RCLike.ofReal (testPartialWord ⊤ [j] a x) := by
  simp only [testPartialWord_coe, partialWord]
  change fderiv ℝ ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ∘ a) x _ = _
  rw [fderiv_comp x (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).differentiableAt
    (a.contDiff.differentiable (by simp)).differentiableAt, ContinuousLinearMap.fderiv]
  rfl

/-- The multiplier bound uses only a real cutoff, uniformly over scalar fields. -/
theorem scalarTest_sobolev_norm_le {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : WholeTests d ℝ) :
    ‖domainTestMulSobolev Ω p (scalarTest 𝕜 a)‖ ≤ testSobolevBound a := by
  apply domainTestMulSobolev_norm_le_of_bounds Ω p _ (testBound a)
    (fun j => testBound (testPartialWord ⊤ [j] a))
  · intro x
    change ‖(RCLike.ofReal (a x) : 𝕜)‖ ≤ _
    rw [RCLike.norm_ofReal, ← Real.norm_eq_abs]
    exact norm_le_testBound a x
  · intro j x
    rw [scalarTest_partial, RCLike.norm_ofReal, ← Real.norm_eq_abs]
    exact norm_le_testBound _ x

/-- Reflection conjugated by a global graph shear is an involution. -/
theorem globalReflectedPoint_involutive {m : ℕ}
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ) :
    Function.Involutive (globalReflectedPoint F γ) := by
  intro z
  simp only [globalReflectedPoint, F.symm_apply_apply,
    unshear_shear]
  have hh : verticalReflection (verticalReflection (unshear γ (F.symm z))) =
      unshear γ (F.symm z) := by
    apply WithLp.ofLp_injective
    simp only [verticalReflection, WithLp.ofLp_toLp, neg_neg]
  rw [hh, shear_unshear, F.apply_symm_apply]

theorem reflectedPoint_mem_chart {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    {z : Ambient m}
    (hz : z ∈ chartImage C.frame C.graphFunction C.center C.radius C.height) :
    reflectedPoint C z ∈ chartImage C.frame C.graphFunction C.center C.radius C.height := by
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have hr : reflectedPoint C (C.frame (shear C.graphFunction w)) =
      C.frame (shear C.graphFunction (verticalReflection w)) := by
    simp [reflectedPoint, verticalReflection]
  rw [hr]
  refine ⟨_, ⟨verticalReflection w, ?_, rfl⟩, rfl⟩
  refine ⟨hw.1, ?_⟩
  change -C.height < -w.ofLp.2 ∧ -w.ofLp.2 < C.height
  constructor <;> linarith [hw.2.1, hw.2.2]

/-- The global reflection preserves the original symmetric physical chart. -/
theorem globalReflectedPoint_mem_chart_iff {m : ℕ} {G : Set (Ambient m)}
    (C : BoundaryChart G) (γ : Space m → ℝ)
    (hγ : EqOn C.graphFunction γ (Metric.ball C.center C.radius)) (z : Ambient m) :
    globalReflectedPoint C.frame γ z ∈
        chartImage C.frame C.graphFunction C.center C.radius C.height ↔
      z ∈ chartImage C.frame C.graphFunction C.center C.radius C.height := by
  have hmaps {w : Ambient m}
      (hw : w ∈ chartImage C.frame C.graphFunction C.center C.radius C.height) :
      globalReflectedPoint C.frame γ w ∈
        chartImage C.frame C.graphFunction C.center C.radius C.height := by
    rw [← reflectedPoint_eq_global C γ hγ hw]
    exact reflectedPoint_mem_chart C hw
  constructor
  · intro h
    simpa only [globalReflectedPoint_involutive C.frame γ z] using hmaps h
  · exact hmaps

/-- Compact cutoff supports make the chart indicator redundant after reflection. -/
theorem boundaryValue_eq_global_sum {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (i : Fin D.count) (γ : Space m → ℝ)
    (hγ : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    (f : Space (m + 1) → 𝕜) :
    boundaryValue D i f = localizedValue e Ω (D.cutoff i.succ) f +
      localizedValue e Ω (D.cutoff i.succ) f ∘ globalReflectedPoint (D.chart i).frame γ := by
  ext z
  by_cases hz : z ∈ chartImage (D.chart i).frame (D.chart i).graphFunction
      (D.chart i).center (D.chart i).radius (D.chart i).height
  · simp only [boundaryValue, indicator_of_mem hz, Pi.add_apply, Function.comp_apply,
      reflectedPoint_eq_global (D.chart i) γ hγ hz]
  · have hr : globalReflectedPoint (D.chart i).frame γ z ∉
        chartImage (D.chart i).frame (D.chart i).graphFunction
          (D.chart i).center (D.chart i).radius (D.chart i).height :=
      fun h => hz ((globalReflectedPoint_mem_chart_iff (D.chart i) γ hγ z).mp h)
    have hχ : D.cutoff i.succ z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (D.boundary_support i h))
    have hχr : D.cutoff i.succ (globalReflectedPoint (D.chart i).frame γ z) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hr (D.boundary_support i h))
    simp only [boundaryValue, indicator_of_notMem hz]
    simp only [Pi.add_apply, Function.comp_apply, localizedValue_eq_smul, Pi.smul_apply',
      hχ, hχr, zero_smul, add_zero]




/-- A real localization cutoff in the canonical Euclidean coordinates. -/
def localizationRealTest {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) (i : Fin (D.count + 1)) :
    WholeTests (m + 1) ℝ :=
  ⟨fun x => D.cutoff i (e.symm x),
    (D.smooth i).comp e.symm.contDiff,
    (D.compact i).comp_homeomorph e.symm.toHomeomorph, subset_univ _⟩

theorem localizationRealTest_tsupport {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω) (i : Fin (D.count + 1)) :
    tsupport (localizationRealTest D i) = e '' tsupport (D.cutoff i) := by
  apply le_antisymm
  · apply closure_minimal
    · intro x hx
      refine ⟨e.symm x, subset_tsupport _ ?_, e.apply_symm_apply x⟩
      exact hx
    · exact e.toHomeomorph.isClosedMap _ (isClosed_tsupport _)
  · rintro x ⟨z, hz, rfl⟩
    have hclosed : IsClosed (e ⁻¹' tsupport (localizationRealTest D i)) :=
      (isClosed_tsupport _).preimage e.continuous
    have hsub : Function.support (D.cutoff i) ⊆ e ⁻¹' tsupport (localizationRealTest D i) := by
      intro y hy
      apply subset_tsupport
      change D.cutoff i (e.symm (e y)) ≠ 0
      simpa using hy
    exact closure_minimal hsub hclosed hz

/-- The interior cutoff has compact support contained in the actual open set. -/
theorem localizationRealTest_interior_support {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) : tsupport (localizationRealTest D 0) ⊆ Ω := by
  rw [localizationRealTest_tsupport]
  rintro x ⟨z, hz, rfl⟩
  exact D.interior_support hz

/-- The same localization cutoff over either scalar field. -/
def localizationScalarTest {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω)
    (𝕜 : Type) [RCLike 𝕜] (i : Fin (D.count + 1)) : WholeTests (m + 1) 𝕜 :=
  scalarTest 𝕜 (localizationRealTest D i)

theorem localizationScalarTest_tsupport_subset {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (𝕜 : Type) [RCLike 𝕜] (i : Fin (D.count + 1)) :
    tsupport (localizationScalarTest D 𝕜 i) ⊆ e '' tsupport (D.cutoff i) := by
  rw [← localizationRealTest_tsupport D i]
  exact tsupport_comp_subset (map_zero (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜)) _

theorem localizationScalarTest_interior_support {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (𝕜 : Type) [RCLike 𝕜] :
    tsupport (localizationScalarTest D 𝕜 0) ⊆ Ω := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := localizationScalarTest_tsupport_subset D 𝕜 0 hx
  exact D.interior_support hz

/-- The interior piece is zero extended across a genuine compact collar. -/
def interiorSobolevExtension {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
  relativeCutoffSobolev Ω ⊤ p (localizationScalarTest D 𝕜 0)
    (fun _ hx => localizationScalarTest_interior_support D 𝕜 hx.1)

/-- The interior bound depends only on the real geometric cutoff. -/
theorem interiorSobolevExtension_norm_le {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖interiorSobolevExtension D 𝕜 p‖ ≤ testSobolevBound (localizationRealTest D 0) :=
  (relativeZeroOperator_norm_le Ω ⊤ 1 p (domainTestMulSobolev Ω p (localizationScalarTest D 𝕜 0))
    ⟨tsupport (localizationScalarTest D 𝕜 0), (localizationScalarTest D 𝕜 0).hasCompactSupport⟩
    (fun _ hx => localizationScalarTest_interior_support D 𝕜 hx.1)
    (domainTestMulSobolev_zero_off_support Ω p (localizationScalarTest D 𝕜 0))).trans
      (scalarTest_sobolev_norm_le 𝕜 Ω p (localizationRealTest D 0))

/-- The interior operator realizes exactly the interior summand of the fixed formula. -/
theorem interiorSobolevExtension_underlying_ae {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) :
    sobolevUnderlying (interiorSobolevExtension D 𝕜 p u) =ᵐ[volume]
      fun x => localizedValue e Ω (D.cutoff 0) (sobolevUnderlying u) (e.symm x) := by
  have hm := relativeCutoffSobolev_underlying_ae Ω ⊤ p (localizationScalarTest D 𝕜 0)
    (fun _ hx => localizationScalarTest_interior_support D 𝕜 hx.1) u
  simp only [Opens.coe_top, Measure.restrict_univ] at hm
  filter_upwards [hm] with x hx
  change sobolevUnderlying (relativeCutoffSobolev Ω ⊤ p (localizationScalarTest D 𝕜 0)
    (fun _ hx => localizationScalarTest_interior_support D 𝕜 hx.1) u) x = _
  rw [hx]
  change RCLike.ofReal (D.cutoff 0 (e.symm x)) * sobolevUnderlying u x = _
  by_cases hxΩ : x ∈ Ω
  · have hxG : e.symm x ∈ (geometricOpen e Ω : Set (Ambient m)) := by
      change e (e.symm x) ∈ Ω
      simpa using hxΩ
    simp only [localizedValue, indicator_of_mem hxG, e.apply_symm_apply,
      RCLike.real_smul_eq_coe_mul]
  · have hxG : e.symm x ∉ (geometricOpen e Ω : Set (Ambient m)) := by
      change e (e.symm x) ∉ Ω
      simpa using hxΩ
    have hz : D.cutoff 0 (e.symm x) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hxG (D.interior_support h)
    simp only [localizedValue, indicator_of_notMem hxG, hz, RCLike.ofReal_zero, zero_mul]




/-- Tangential coordinates followed by the vertical coordinate. -/
def splitCoordinates (m : ℕ) : Ambient m ≃ₗᵢ[ℝ] Space (m+1) where
  toFun z := WithLp.toLp 2 (Fin.snoc (fun i => z.ofLp.1 i) z.ofLp.2)
  invFun x := WithLp.toLp 2 (WithLp.toLp 2 (fun i : Fin m => x i.castSucc), x (Fin.last m))
  left_inv z := by
    apply (WithLp.equiv 2 (Space m × ℝ)).injective
    apply Prod.ext
    · ext i
      simp
    · simp
  right_inv x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_castSucc, Real.norm_eq_abs, sq_abs]

@[simp] theorem splitCoordinates_last (m : ℕ) (z : Ambient m) :
    splitCoordinates m z (Fin.last m) = z.ofLp.2 := by simp [splitCoordinates]
@[simp] theorem splitCoordinates_castSucc (m : ℕ) (z : Ambient m) (i : Fin m) :
    splitCoordinates m z i.castSucc = z.ofLp.1 i := by simp [splitCoordinates]
@[simp] theorem splitCoordinates_symm_vertical (m : ℕ) (x : Space (m+1)) :
    ((splitCoordinates m).symm x).ofLp.2 = x (Fin.last m) := rfl

/-- The globally extended physical flattening, expressed in the shared model. -/
def flattenEquiv {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ) :
    Space (m+1) ≃ Space (m+1) :=
  (((splitCoordinates m).toEquiv.symm.trans (shearEquiv γ)).trans F.toEquiv).trans e.toEquiv

@[simp] theorem flattenEquiv_apply {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ) (x : Space (m+1)) :
    flattenEquiv e F γ x = e (F (shear γ ((splitCoordinates m).symm x))) := rfl

@[simp] theorem flattenEquiv_symm_apply {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ) (x : Space (m+1)) :
    (flattenEquiv e F γ).symm x = splitCoordinates m (unshear γ (F.symm (e.symm x))) := rfl

 theorem flattenEquiv_lipschitz {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {γ : Space m → ℝ} {L : ℝ≥0}
    (hγ : LipschitzWith L γ) :
    LipschitzWith (shearConstant L) (flattenEquiv e F γ) := by
  simpa [flattenEquiv, shearEquiv, Function.comp_def, one_mul, mul_one] using e.isometry.lipschitzWith.comp
    (F.isometry.lipschitzWith.comp ((shear_lipschitzWith hγ).comp (splitCoordinates m).symm.isometry.lipschitzWith))

 theorem flattenEquiv_symm_lipschitz {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {γ : Space m → ℝ} {L : ℝ≥0}
    (hγ : LipschitzWith L γ) :
    LipschitzWith (shearConstant L) (flattenEquiv e F γ).symm := by
  have hu : LipschitzWith (shearConstant L) (unshear γ) := by
    rw [unshear_eq_shear_neg]
    exact shear_lipschitzWith hγ.neg
  simpa [flattenEquiv, shearEquiv, Function.comp_def, one_mul, mul_one] using (splitCoordinates m).isometry.lipschitzWith.comp
    (hu.comp (F.symm.isometry.lipschitzWith.comp e.symm.isometry.lipschitzWith))

 def flattenChart {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {γ : Space m → ℝ} {L : ℝ≥0}
    (hγ : LipschitzWith L γ) :
    BiLipschitzChart (⊤ : Opens (Space (m+1))) ⊤ (shearConstant L) (shearConstant L) where
  toFun := flattenEquiv e F γ
  invFun := (flattenEquiv e F γ).symm
  mapsTo := fun _ _ => Set.mem_univ _
  inv_mapsTo := fun _ _ => Set.mem_univ _
  left_inv := fun x _ => (flattenEquiv e F γ).symm_apply_apply x
  right_inv := fun x _ => (flattenEquiv e F γ).apply_symm_apply x
  lipschitz := (flattenEquiv_lipschitz e F hγ).lipschitzOnWith
  inv_lipschitz := (flattenEquiv_symm_lipschitz e F hγ).lipschitzOnWith


/-- The standard upper half-space for the final coordinate. -/
def flatHalfSpace (m : ℕ) : Opens (Space (m+1)) :=
  ⟨{x | 0 < x (Fin.last m)}, isOpen_lt continuous_const
    ((continuous_apply (Fin.last m)).comp (P102.U4.ACL.coordinates (m+1)).continuous)⟩

/-- The global physical graph epigraph used to extend localized pieces. -/
def globalGraphOpen {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {γ : Space m → ℝ} {L : ℝ≥0}
    (hγ : LipschitzWith L γ) : Opens (Space (m+1)) :=
  ⟨(flattenEquiv e F γ).symm ⁻¹' (flatHalfSpace m : Set (Space (m+1))),
    (flatHalfSpace m).isOpen.preimage (flattenEquiv_symm_lipschitz e F hγ).continuous⟩

@[simp] theorem mem_globalGraphOpen {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {γ : Space m → ℝ} {L : ℝ≥0}
    (hγ : LipschitzWith L γ) (x : Space (m+1)) :
    x ∈ globalGraphOpen e F hγ ↔ 0 < (unshear γ (F.symm (e.symm x))).ofLp.2 := by
  simp [globalGraphOpen, flatHalfSpace, flattenEquiv_symm_apply]

/-- The global flattening restricted to the standard half-space. -/
def graphChart {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {γ : Space m → ℝ} {L : ℝ≥0}
    (hγ : LipschitzWith L γ) :
    BiLipschitzChart (globalGraphOpen e F hγ) (flatHalfSpace m)
      (shearConstant L) (shearConstant L) where
  toFun := flattenEquiv e F γ
  invFun := (flattenEquiv e F γ).symm
  mapsTo := fun x hx => by
    change (flattenEquiv e F γ).symm (flattenEquiv e F γ x) ∈ flatHalfSpace m
    simpa using hx
  inv_mapsTo := fun x hx => hx
  left_inv := fun x _ => (flattenEquiv e F γ).symm_apply_apply x
  right_inv := fun x _ => (flattenEquiv e F γ).apply_symm_apply x
  lipschitz := (flattenEquiv_lipschitz e F hγ).lipschitzOnWith
  inv_lipschitz := (flattenEquiv_symm_lipschitz e F hγ).lipschitzOnWith

/-- Inverse charts, retaining the same global representatives. -/
abbrev inverseChart {d : ℕ} {U V : Opens (Space d)} {L M : ℝ≥0}
    (g : BiLipschitzChart U V L M) : BiLipschitzChart V U M L := g.symm

/-- The cutoff's physical support is a compact set. -/
def physicalSupport {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (χ : Ambient m → ℝ) (hχ : HasCompactSupport χ) : Compacts (Space (m+1)) :=
  ⟨e '' tsupport χ, hχ.isCompact.image e.continuous⟩

/-- The extended global graph has exactly the original positive side in the chart. -/
theorem globalGraphOpen_side {m : ℕ} {G : Set (Ambient m)}
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (C : BoundaryChart G)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn C.graphFunction γ (Metric.ball C.center C.radius))
    {z : Ambient m}
    (hz : z ∈ chartImage C.frame C.graphFunction C.center C.radius C.height) :
    e z ∈ globalGraphOpen e C.frame hγ ↔ z ∈ G := by
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have hcoord : unshear γ (shear C.graphFunction w) = w := by
    rw [show shear C.graphFunction w = shear γ w by simp only [shear, heq hw.1]]
    exact unshear_shear γ w
  simp only [mem_globalGraphOpen, LinearIsometryEquiv.symm_apply_apply,
    AffineIsometryEquiv.symm_apply_apply, hcoord]
  constructor
  · intro ht
    have hs : C.frame (shear C.graphFunction w) ∈
        C.frame '' (shear C.graphFunction '' upperCylinder C.center C.radius C.height) :=
      ⟨_, ⟨w, ⟨hw.1, ht, hw.2.2⟩, rfl⟩, rfl⟩
    rw [← C.side] at hs
    exact hs.1
  · intro hG
    have hs : C.frame (shear C.graphFunction w) ∈
        G ∩ chartImage C.frame C.graphFunction C.center C.radius C.height :=
      ⟨hG, ⟨_, ⟨w, hw, rfl⟩, rfl⟩⟩
    rw [C.side] at hs
    obtain ⟨_, ⟨v, hv, he⟩, he'⟩ := hs
    have hwv : v = w := (shearEquiv C.graphFunction).injective
      (C.frame.injective ((congrArg C.frame he).trans he'))
    simpa only [hwv] using hv.2.1

/-- This is the collar condition needed by relative zero extension to the global epigraph. -/
theorem physicalSupport_inter_graph {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (Ω : Opens (Space (m+1))) (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn C.graphFunction γ (Metric.ball C.center C.radius))
    (χ : Ambient m → ℝ) (hχ : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ chartImage C.frame C.graphFunction C.center C.radius C.height) :
    (physicalSupport e χ hχ : Set (Space (m+1))) ∩
      (globalGraphOpen e C.frame hγ : Set (Space (m+1))) ⊆ Ω := by
  rintro x ⟨⟨z, hz, rfl⟩, hx⟩
  exact (globalGraphOpen_side e C hγ heq (hsupp hz)).mp hx




abbrev coordinateLpIso {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DomainLp 𝕜 Ω p ≃ₗᵢ[𝕜] ExpandedFA.Sobolev.DomainLp 𝕜 (ACL.coordinateDomain Ω) p :=
  ExpandedFA.Sobolev.HalfSpace.LpTransport.restrictPullIso
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)) (PiLp.volume_preserving_toLp (Fin d))
    (Ω : Set (Space d)) Ω.isOpen.measurableSet

theorem coordinateLpIso_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p) :
    coordinateLpIso Ω p u =ᵐ[volume.restrict (ACL.coordinateDomain Ω : Set (Fin d → ℝ))]
      u ∘ (ACL.coordinates d).symm :=
  ExpandedFA.Sobolev.HalfSpace.LpTransport.restrictPullIso_coe _ _ _ _ _

theorem coordinateLpIso_symm_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : ExpandedFA.Sobolev.DomainLp 𝕜 (ACL.coordinateDomain Ω) p) :
    (coordinateLpIso Ω p).symm u =ᵐ[volume.restrict (Ω : Set (Space d))]
      u ∘ ACL.coordinates d :=
  ExpandedFA.Sobolev.HalfSpace.LpTransport.restrictPullIso_symm_coe _ _ _ _ _

theorem coordinateLp_test_pairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p)
    (φ : TestFunction (ACL.coordinateDomain Ω) 𝕜 ⊤) :
    ExpandedFA.Sobolev.lpDistribution (coordinateLpIso Ω p u) φ =
      regularDistribution Ω u (ACL.testFromCoordinates φ) := by
  rw [ExpandedFA.Sobolev.lpDistribution_apply,
    regular_pairing d 𝕜 Ω u (domainLp_locallyIntegrable Ω p u)]
  rw [integral_congr_ae ((coordinateLpIso_ae Ω p u).mono fun x hx =>
    congrArg (φ x * ·) hx)]
  have hp := (PiLp.volume_preserving_toLp (Fin d)).restrict_preimage Ω.isOpen.measurableSet
  rw [← hp.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
    (fun x => u x * ACL.testFromCoordinates φ x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => mul_comm _ _

theorem testFromCoordinates_partial_eq {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (φ : TestFunction (ACL.coordinateDomain Ω) 𝕜 ⊤) (j : Fin d) :
    ACL.testFromCoordinates (ExpandedFA.Distributions.testPartialCLM [j] φ) =
      testPartialWord Ω [j] (ACL.testFromCoordinates φ) := by
  ext x
  exact (ACL.testFromCoordinates_partial φ j x).symm

def testToCoordinates {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (φ : TestSpace 𝕜 Ω) : TestFunction (ACL.coordinateDomain Ω) 𝕜 ⊤ where
  toFun x := φ ((ACL.coordinates d).symm x)
  contDiff' := φ.contDiff.comp (ACL.coordinates d).symm.contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (ACL.coordinates d).symm.toHomeomorph
  tsupport_subset' := (tsupport_comp_subset_preimage φ (ACL.coordinates d).symm.continuous).trans
    (preimage_mono φ.tsupport_subset)

@[simp] theorem testFromCoordinates_toCoordinates {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (φ : TestSpace 𝕜 Ω) :
    ACL.testFromCoordinates (testToCoordinates φ) = φ := by
  ext x
  exact congrArg φ ((ACL.coordinates d).symm_apply_apply x)

theorem weak_coordinate_iff {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u v : DomainLp 𝕜 Ω p) (j : Fin d) :
    distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v ↔
    ExpandedFA.Sobolev.lpDistribution (coordinateLpIso Ω p v) =
      -(ExpandedFA.Sobolev.lpDistribution (coordinateLpIso Ω p u)).comp
        (ExpandedFA.Distributions.testPartialCLM [j]) := by
  constructor
  · intro h
    ext φ
    have he := congrArg (fun T : DistributionSpace 𝕜 Ω => T (ACL.testFromCoordinates φ)) h
    simp only [coordinateLp_test_pairing, neg_apply, ContinuousLinearMap.comp_apply,
      testFromCoordinates_partial_eq] at *
    simpa [distributionPartial] using he.symm
  · intro h
    ext φ
    have he := congrArg (fun T => T (testToCoordinates φ)) h
    simpa only [coordinateLp_test_pairing, neg_apply, ContinuousLinearMap.comp_apply,
      testFromCoordinates_partial_eq, testFromCoordinates_toCoordinates,
      distributionPartial, Multiset.sort_singleton, Multiset.card_singleton,
      pow_one, neg_smul, one_smul, smul_apply] using he.symm


/-- The canonical upper half-space in the Euclidean coordinate norm. -/
def coordinateUpper {d : ℕ} (j : Fin d) : Opens (Space d) :=
  ⟨{x | 0 < x j}, isOpen_lt continuous_const
    ((continuous_apply j).comp (ACL.coordinates d).continuous)⟩

@[simp] theorem coordinateDomain_upper {d : ℕ} (j : Fin d) :
    ACL.coordinateDomain (coordinateUpper j) = ExpandedFA.Sobolev.HalfSpace.upper j := rfl

@[simp] theorem coordinateDomain_top (d : ℕ) :
    ACL.coordinateDomain (⊤ : Opens (Space d)) = ⊤ := rfl

/-- The parity reflection of an ambient representative; boundary values are zero. -/
def coordinateReflectionValue {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (odd : Bool) (f : Space d → 𝕜) (x : Space d) : 𝕜 :=
  ExpandedFA.Sobolev.HalfSpace.reflection j odd (f ∘ (ACL.coordinates d).symm)
    (ACL.coordinates d x)

def coordinateReflect {d : ℕ} (j : Fin d) (x : Space d) : Space d :=
  (ACL.coordinates d).symm (ExpandedFA.Sobolev.HalfSpace.reflect j (ACL.coordinates d x))

@[simp] theorem coordinateReflectionValue_pos {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (odd : Bool) (f : Space d → 𝕜) {x : Space d} (hx : 0 < x j) :
    coordinateReflectionValue j odd f x = f x := by
  unfold coordinateReflectionValue
  rw [ExpandedFA.Sobolev.HalfSpace.reflection_of_pos j odd _ (x := ACL.coordinates d x) hx]
  exact congrArg f ((ACL.coordinates d).symm_apply_apply x)

@[simp] theorem coordinateReflectionValue_neg {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (odd : Bool) (f : Space d → 𝕜) {x : Space d} (hx : x j < 0) :
    coordinateReflectionValue j odd f x =
      if odd then -f (coordinateReflect j x) else f (coordinateReflect j x) := by
  exact ExpandedFA.Sobolev.HalfSpace.reflection_of_neg j odd _ hx

@[simp] theorem coordinateReflectionValue_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (odd : Bool) (f : Space d → 𝕜) {x : Space d} (hx : x j = 0) :
    coordinateReflectionValue j odd f x = 0 :=
  ExpandedFA.Sobolev.HalfSpace.reflection_of_zero j odd _ hx

/-- Bounded linear reflection on zeroth-order classes, including p=infinity. -/
def upperReflectionLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (odd : Bool) :
    DomainLp 𝕜 (coordinateUpper j) p →L[𝕜] DomainLp 𝕜 (⊤ : Opens (Space d)) p :=
  (coordinateLpIso (⊤ : Opens (Space d)) p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ExpandedFA.Sobolev.HalfSpace.reflectionCLM j odd).comp
      (coordinateLpIso (coordinateUpper j) p).toContinuousLinearEquiv.toContinuousLinearMap)

theorem upperReflectionLp_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (odd : Bool)
    (u : DomainLp 𝕜 (coordinateUpper j) p) :
    upperReflectionLp j p odd u =
      (coordinateLpIso (⊤ : Opens (Space d)) p).symm
        (ExpandedFA.Sobolev.HalfSpace.reflectLp j odd
          (coordinateLpIso (coordinateUpper j) p u)) := rfl

theorem upperReflectionLp_norm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (odd : Bool)
    (u : DomainLp 𝕜 (coordinateUpper j) p) :
    ‖upperReflectionLp j p odd u‖ =
      ExpandedFA.Sobolev.HalfSpace.reflectionFactor p * ‖u‖ := by
  change ‖(coordinateLpIso (⊤ : Opens (Space d)) p).symm
    (ExpandedFA.Sobolev.HalfSpace.reflectLp j odd (coordinateLpIso (coordinateUpper j) p u))‖ = _
  exact ((coordinateLpIso (⊤ : Opens (Space d)) p).symm.norm_map _).trans
    ((ExpandedFA.Sobolev.HalfSpace.reflectLp_norm j odd _).trans
      (congrArg (ExpandedFA.Sobolev.HalfSpace.reflectionFactor p * ·)
        ((coordinateLpIso (coordinateUpper j) p).norm_map u)))

theorem upperReflectionLp_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (odd : Bool)
    (u : DomainLp 𝕜 (coordinateUpper j) p) :
    upperReflectionLp j p odd u =ᵐ[volume] coordinateReflectionValue j odd u := by
  have hp := (PiLp.volume_preserving_toLp (Fin d)).symm
    (MeasurableEquiv.toLp 2 (Fin d → ℝ))
  have h₁ := coordinateLpIso_symm_ae (⊤ : Opens (Space d)) p
    (ExpandedFA.Sobolev.HalfSpace.reflectLp j odd (coordinateLpIso (coordinateUpper j) p u))
  have h₂ := hp.quasiMeasurePreserving.ae
    (ExpandedFA.Sobolev.HalfSpace.reflectLp_coe j odd (coordinateLpIso (coordinateUpper j) p u))
  have h₃ := hp.quasiMeasurePreserving.ae
    (ExpandedFA.Sobolev.HalfSpace.reflection_congr j odd
      (coordinateLpIso_ae (coordinateUpper j) p u))
  simp only [Opens.coe_top, Measure.restrict_univ] at h₁
  filter_upwards [h₁, h₂, h₃] with x hx₁ hx₂ hx₃
  exact hx₁.trans (hx₂.trans hx₃)

theorem upperReflection_weakDerivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (coordinateUpper j) 1 p) (k : Fin d) :
    distributionPartial {k} (regularDistribution ⊤
      (upperReflectionLp j p false (sobolevUnderlying u))) =
      regularDistribution ⊤ (upperReflectionLp j p (decide (k = j)) (firstWeakDerivative u k)) := by
  apply (weak_coordinate_iff ⊤ p _ _ k).mpr
  have hw : ExpandedFA.Sobolev.Lines.HasWeakCoordinateDerivatives
      (coordinateLpIso (coordinateUpper j) p (sobolevUnderlying u))
      (fun k => coordinateLpIso (coordinateUpper j) p (firstWeakDerivative u k)) := by
    intro k
    apply (weak_coordinate_iff (coordinateUpper j) p _ _ k).mp
    exact sobolev_derivative_distribution _ 1 p u (firstSobolevIndex k)
  have he := ExpandedFA.Sobolev.HalfSpace.weak_reflection 𝕜 d j p
    (coordinateLpIso (coordinateUpper j) p (sobolevUnderlying u))
    (fun k => coordinateLpIso (coordinateUpper j) p (firstWeakDerivative u k)) hw
    (ExpandedFA.Sobolev.HalfSpace.reflectLp j false
      (coordinateLpIso (coordinateUpper j) p (sobolevUnderlying u)))
    (fun k => ExpandedFA.Sobolev.HalfSpace.reflectLp j (decide (k = j))
      (coordinateLpIso (coordinateUpper j) p (firstWeakDerivative u k)))
    (ExpandedFA.Sobolev.HalfSpace.reflectLp_coe j false _)
    (fun k => ExpandedFA.Sobolev.HalfSpace.reflectLp_coe j (decide (k = j)) _)
  rw [upperReflectionLp_apply, upperReflectionLp_apply]
  have hc (v : ExpandedFA.Sobolev.DomainLp 𝕜 (⊤ : Opens (Fin d → ℝ)) p) :
      coordinateLpIso (⊤ : Opens (Space d)) p
        ((coordinateLpIso (⊤ : Opens (Space d)) p).symm v) = v :=
    (coordinateLpIso (⊤ : Opens (Space d)) p).apply_symm_apply v
  rw [hc, hc]
  exact he k


private theorem upperReflection_sobolev_exists {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (coordinateUpper j) 1 p) :
    ∃ v : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
      sobolevUnderlying v = upperReflectionLp j p false (sobolevUnderlying u) ∧
      ∀ k, firstWeakDerivative v k =
        upperReflectionLp j p (decide (k = j)) (firstWeakDerivative u k) :=
  firstOrder_graph ⊤ p _ _ (upperReflection_weakDerivative j p u)

private def upperReflectionSobolevValue {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (coordinateUpper j) 1 p) : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p :=
  (upperReflection_sobolev_exists j p u).choose

private theorem upperReflectionSobolevValue_underlying {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 (coordinateUpper j) 1 p) :
    sobolevUnderlying (upperReflectionSobolevValue j p u) =
      upperReflectionLp j p false (sobolevUnderlying u) :=
  (upperReflection_sobolev_exists j p u).choose_spec.1

private theorem upperReflectionSobolevValue_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (coordinateUpper j) 1 p) (k : Fin d) :
    firstWeakDerivative (upperReflectionSobolevValue j p u) k =
      upperReflectionLp j p (decide (k = j)) (firstWeakDerivative u k) :=
  (upperReflection_sobolev_exists j p u).choose_spec.2 k

private def upperReflectionSobolevLinear {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 (coordinateUpper j) 1 p →ₗ[𝕜] Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p where
  toFun := upperReflectionSobolevValue j p
  map_add' u v := by
    apply sobolevUnderlying_injective ⊤ 1 p
    simp only [upperReflectionSobolevValue_underlying]
    change upperReflectionLp j p false (sobolevUnderlyingCLM _ 1 p (u + v)) =
      sobolevUnderlyingCLM _ 1 p (upperReflectionSobolevValue j p u + upperReflectionSobolevValue j p v)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (upperReflectionSobolevValue_underlying j p u).symm
      (upperReflectionSobolevValue_underlying j p v).symm
  map_smul' c u := by
    apply sobolevUnderlying_injective ⊤ 1 p
    simp only [upperReflectionSobolevValue_underlying]
    change upperReflectionLp j p false (sobolevUnderlyingCLM _ 1 p (c • u)) =
      sobolevUnderlyingCLM _ 1 p (c • upperReflectionSobolevValue j p u)
    rw [map_smul, map_smul]
    exact congrArg (c • ·) (upperReflectionSobolevValue_underlying j p u).symm

private theorem upperReflectionSobolevValue_norm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 (coordinateUpper j) 1 p) :
    ‖upperReflectionSobolevValue j p u‖ =
      ExpandedFA.Sobolev.HalfSpace.reflectionFactor p * ‖u‖ := by
  rw [BiLipschitzPullback.sobolev_firstOrder_norm ⊤ p,
    upperReflectionSobolevValue_underlying, upperReflectionLp_norm]
  simp_rw [upperReflectionSobolevValue_derivative, upperReflectionLp_norm]
  rw [← Finset.mul_sum, ← mul_add, BiLipschitzPullback.sobolev_firstOrder_norm (coordinateUpper j) p]

/-- Even reflection in the canonical first-order weak-derivative graph.
One scalar-linear formula works for real/complex scalars and every p≥1. -/
def upperReflectionSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 (coordinateUpper j) 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p :=
  (upperReflectionSobolevLinear j p).mkContinuous
    (ExpandedFA.Sobolev.HalfSpace.reflectionFactor p)
    (fun u => (upperReflectionSobolevValue_norm j p u).le)

theorem upperReflectionSobolev_underlying {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 (coordinateUpper j) 1 p) :
    sobolevUnderlying (upperReflectionSobolev j p u) =
      upperReflectionLp j p false (sobolevUnderlying u) :=
  upperReflectionSobolevValue_underlying j p u

theorem upperReflectionSobolev_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (coordinateUpper j) 1 p) (k : Fin d) :
    firstWeakDerivative (upperReflectionSobolev j p u) k =
      upperReflectionLp j p (decide (k = j)) (firstWeakDerivative u k) :=
  upperReflectionSobolevValue_derivative j p u k

theorem upperReflectionSobolev_norm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 (coordinateUpper j) 1 p) :
    ‖upperReflectionSobolev j p u‖ =
      ExpandedFA.Sobolev.HalfSpace.reflectionFactor p * ‖u‖ :=
  upperReflectionSobolevValue_norm j p u

theorem upperReflectionSobolev_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 (coordinateUpper j) 1 p) :
    sobolevUnderlying (upperReflectionSobolev j p u) =ᵐ[volume]
      coordinateReflectionValue j false (sobolevUnderlying u) := by
  rw [upperReflectionSobolev_underlying]
  exact upperReflectionLp_ae j p false _

theorem upperReflectionSobolev_restrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 (coordinateUpper j) 1 p) :
    sobolevUnderlying (upperReflectionSobolev j p u) =ᵐ[
      volume.restrict (coordinateUpper j : Set (Space d))] sobolevUnderlying u := by
  filter_upwards [ae_restrict_of_ae (upperReflectionSobolev_ae j p u),
    ae_restrict_mem (coordinateUpper j).isOpen.measurableSet] with x hx hxH
  exact hx.trans (coordinateReflectionValue_pos j false _ hxH)


theorem coordinateReflectionValue_congr {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (odd : Bool) {f g : Space d → 𝕜}
    (h : f =ᵐ[volume.restrict (coordinateUpper j : Set (Space d))] g) :
    coordinateReflectionValue j odd f =ᵐ[volume] coordinateReflectionValue j odd g := by
  have hp := (PiLp.volume_preserving_toLp (Fin d)).restrict_preimage
    (coordinateUpper j).isOpen.measurableSet
  have he := ExpandedFA.Sobolev.HalfSpace.reflection_congr j odd
    (hp.quasiMeasurePreserving.ae_eq_comp h)
  exact ((PiLp.volume_preserving_toLp (Fin d)).symm
    (MeasurableEquiv.toLp 2 (Fin d → ℝ))).quasiMeasurePreserving.ae he

theorem coordinateReflectionValue_even {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (f : Space d → 𝕜) (x : Space d) :
    coordinateReflectionValue j false f x =
      (coordinateUpper j : Set (Space d)).indicator f x +
      (coordinateUpper j : Set (Space d)).indicator f (coordinateReflect j x) := rfl

theorem upperReflectionSobolev_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : Fin d) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖upperReflectionSobolev (𝕜 := 𝕜) j p‖ ≤
      ExpandedFA.Sobolev.HalfSpace.reflectionFactor p := by
  apply (upperReflectionSobolev (𝕜 := 𝕜) j p).opNorm_le_bound
  · exact Real.rpow_nonneg (by norm_num) _
  · intro u
    exact (upperReflectionSobolev_norm j p u).le




set_option maxHeartbeats 1500000 in
/-- Once the first-order bound is available, the fixed formula supplies every
support, representative, compatibility, and additional Lr clause. -/
theorem extension_clauses_of_sobolev {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (C : ℝ≥0∞ → ℝ≥0)
    (hE : ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
      ∃ E : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
        (∀ u, sobolevUnderlying (E u) =ᵐ[volume] rawExtension D (sobolevUnderlying u)) ∧
        ‖E‖ ≤ C p) :
    ∃ (K : Compacts (Space (m + 1))) (B : ℝ≥0∞ → ℝ≥0),
      (∀ (𝕜 : Type) [RCLike 𝕜] (f g : Space (m + 1) → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] g →
        rawExtension D f =ᵐ[volume] rawExtension D g) ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
        ∃ E : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
          (∀ u, sobolevUnderlying (E u) =ᵐ[volume] rawExtension D (sobolevUnderlying u)) ∧
          (∀ u, sobolevUnderlying (E u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
            sobolevUnderlying u) ∧
          (∀ u, ∀ᵐ x ∂volume, x ∉ (K : Set (Space (m + 1))) → sobolevUnderlying (E u) x = 0) ∧
          ‖E‖ ≤ C p ∧
          ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (u : Sobolev 𝕜 Ω 1 p),
            MemLp (sobolevUnderlying u) r (volume.restrict (Ω : Set (Space (m + 1)))) →
            MemLp (sobolevUnderlying (E u)) r volume ∧
            eLpNorm (sobolevUnderlying (E u)) r volume ≤
              (B r : ℝ≥0∞) * eLpNorm (sobolevUnderlying u) r
                (volume.restrict (Ω : Set (Space (m + 1)))) := by
  obtain ⟨K, hK⟩ := rawExtension_compact_container D
  refine ⟨K, fun _ => (rawLpConstant D).toNNReal,
    fun 𝕜 _ f g hfg => rawExtension_congr D hfg, ?_⟩
  intro 𝕜 _ p _
  obtain ⟨E, hformula, hnorm⟩ := hE 𝕜 p
  refine ⟨E, hformula, ?_, ?_, hnorm, ?_⟩
  · intro u
    filter_upwards [ae_restrict_of_ae (hformula u),
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    exact hx.trans (rawExtension_restrict D _ hxΩ)
  · intro u
    filter_upwards [hformula u] with x hx hxK
    exact hx.trans (hK 𝕜 _ x hxK)
  · intro r _ u hu
    refine ⟨(memLp_congr_ae (hformula u)).mpr (rawExtension_memLp D r hu), ?_⟩
    rw [eLpNorm_congr_ae (hformula u), ENNReal.coe_toNNReal (rawLpConstant_ne_top D)]
    exact rawExtension_eLpNorm_le D r hu

/-- Ambient density follows from the complete extension theorem and the
already established whole-space density in the full derivative norm. -/
theorem ambient_density_of_extension (hExtension : Expected.Extension) : Expected.Density := by
  intro m e Ω hΩ 𝕜 _ p _ hp u
  obtain ⟨D, K, C, B, _, hE⟩ := hExtension m e Ω hΩ
  obtain ⟨E, _, hrestrict, _⟩ := hE 𝕜 p
  exact ambient_approximation_of_extension Ω 1 p hp u (E u) (hrestrict u)





/-- Finite sums of Lp classes admit the sum of the chosen representatives a.e. -/
theorem domainLp_sum_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {ι : Type*} [Fintype ι] (f : ι → DomainLp 𝕜 U p) :
    (∑ i, f i : DomainLp 𝕜 U p) =ᵐ[volume.restrict (U : Set (Space d))]
      fun x => ∑ i, f i x := by
  classical
  have hs (s : Finset ι) :
      (∑ i ∈ s, f i : DomainLp 𝕜 U p) =ᵐ[volume.restrict (U : Set (Space d))]
        fun x => ∑ i ∈ s, f i x := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        filter_upwards [Lp.coeFn_zero 𝕜 p (volume.restrict (U : Set (Space d)))] with x hx
        exact hx
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (Lp.coeFn_add _ _).trans ((Filter.EventuallyEq.refl _ _).add ih)
  exact hs Finset.univ

/-- The finite Sobolev graph sum realizes the interior and boundary local extensions. -/
def localizedSobolevSum {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)}
    {Ω : Opens (Space (m + 1))} (D : Localization e Ω)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Fin D.count → Sobolev 𝕜 Ω 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p) :
    Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
  interiorSobolevExtension D 𝕜 p + ∑ i, T i

theorem localizedSobolevSum_underlying_ae {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Fin D.count → Sobolev 𝕜 Ω 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p)
    (hT : ∀ i u, sobolevUnderlying (T i u) =ᵐ[volume]
      fun x => boundaryValue D i (sobolevUnderlying u) (e.symm x))
    (u : Sobolev 𝕜 Ω 1 p) :
    sobolevUnderlying (localizedSobolevSum D 𝕜 p T u) =ᵐ[volume]
      rawExtension D (sobolevUnderlying u) := by
  classical
  have hzero : sobolevUnderlying (interiorSobolevExtension D 𝕜 p u) =ᵐ[volume]
      fun x => localizedValue e Ω (D.cutoff 0) (sobolevUnderlying u) (e.symm x) :=
    interiorSobolevExtension_underlying_ae D 𝕜 p u
  have hsum := domainLp_sum_ae (⊤ : Opens (Space (m + 1))) p
    (fun i => sobolevUnderlying (T i u))
  simp only [Opens.coe_top, Measure.restrict_univ] at hsum
  have hpoint : ∀ᵐ x ∂volume, ∀ i, sobolevUnderlying (T i u) x =
      boundaryValue D i (sobolevUnderlying u) (e.symm x) :=
    ae_all_iff.mpr fun i => hT i u
  have heq : sobolevUnderlying (localizedSobolevSum D 𝕜 p T u) =
      sobolevUnderlying (interiorSobolevExtension D 𝕜 p u) +
        ∑ i, sobolevUnderlying (T i u) := by
    change sobolevUnderlyingCLM ⊤ 1 p
      ((interiorSobolevExtension D 𝕜 p + ∑ i, T i) u) = _
    simp only [add_apply, sum_apply,
      map_add, map_sum]
    rfl
  rw [heq]
  have hadd := Lp.coeFn_add (sobolevUnderlying (interiorSobolevExtension D 𝕜 p u))
    (∑ i, sobolevUnderlying (T i u))
  simp only [Opens.coe_top, Measure.restrict_univ] at hadd
  filter_upwards [hadd, hzero, hsum, hpoint] with x hx hz hs hxs
  simp only [Pi.add_apply] at hx
  rw [hx, hz, hs]
  change _ + ∑ i, sobolevUnderlying (T i u) x = _
  simp only [rawExtension, boundaryValue, hxs]

theorem localizedSobolevSum_norm_le {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Fin D.count → Sobolev 𝕜 Ω 1 p →L[𝕜]
      Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p)
    (b : Fin D.count → ℝ≥0) (hT : ∀ i, ‖T i‖ ≤ b i) :
    ‖localizedSobolevSum D 𝕜 p T‖ ≤ testSobolevBound (localizationRealTest D 0) + ∑ i, b i := by
  rw [localizedSobolevSum]
  simp only [NNReal.coe_sum]
  apply (norm_add_le (interiorSobolevExtension D 𝕜 p) (∑ i, T i)).trans
  apply add_le_add (interiorSobolevExtension_norm_le D 𝕜 p)
  exact (norm_sum_le Finset.univ T).trans (Finset.sum_le_sum fun i _ => hT i)





/-- The actual upstream pullback operator, with its quantitative estimate. -/
def sobolevChartPullback {d : ℕ} (hd : 0 < d) {U V : Opens (Space d)}
    {L M : ℝ≥0} (g : BiLipschitzChart U V L M)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 U 1 p →L[𝕜] Sobolev 𝕜 V 1 p :=
  (bilipschitz_sobolevPullback d hd 𝕜 U V L M g p).choose

theorem sobolevChartPullback_ae {d : ℕ} (hd : 0 < d) {U V : Opens (Space d)}
    {L M : ℝ≥0} (g : BiLipschitzChart U V L M)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U 1 p) :
    sobolevUnderlying (sobolevChartPullback hd g 𝕜 p u) =ᵐ[
      volume.restrict (V : Set (Space d))] sobolevUnderlying u ∘ g.toFun :=
  (bilipschitz_sobolevPullback d hd 𝕜 U V L M g p).choose_spec.1 u

theorem sobolevChartPullback_norm_le {d : ℕ} (hd : 0 < d) {U V : Opens (Space d)}
    {L M : ℝ≥0} (g : BiLipschitzChart U V L M)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖sobolevChartPullback hd g 𝕜 p‖ ≤ pullbackSobolevBound d p L M :=
  (bilipschitz_sobolevPullback d hd 𝕜 U V L M g p).choose_spec.2.2

/-- The local side identity supplies the support condition for the relative zero extension. -/
theorem boundaryScalarTest_support {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    (𝕜 : Type) [RCLike 𝕜] :
    tsupport (localizationScalarTest D 𝕜 i.succ) ∩
      (globalGraphOpen e (D.chart i).frame hγ : Set (Space (m+1))) ⊆ Ω := by
  intro x hx
  exact physicalSupport_inter_graph e Ω (D.chart i) hγ heq (D.cutoff i.succ)
    (D.compact i.succ) (D.boundary_support i)
      ⟨localizationScalarTest_tsupport_subset D 𝕜 i.succ hx.1, hx.2⟩

def boundaryCutoffSobolev {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (globalGraphOpen e (D.chart i).frame hγ) 1 p :=
  relativeCutoffSobolev Ω _ p (localizationScalarTest D 𝕜 i.succ)
    (boundaryScalarTest_support D i hγ heq 𝕜)

theorem boundaryCutoffSobolev_norm_le {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖boundaryCutoffSobolev D i hγ heq 𝕜 p‖ ≤
      testSobolevBound (localizationRealTest D i.succ) :=
  (relativeZeroOperator_norm_le Ω _ 1 p
    (domainTestMulSobolev Ω p (localizationScalarTest D 𝕜 i.succ)) _
    (boundaryScalarTest_support D i hγ heq 𝕜)
    (domainTestMulSobolev_zero_off_support Ω p (localizationScalarTest D 𝕜 i.succ))).trans
      (scalarTest_sobolev_norm_le 𝕜 Ω p (localizationRealTest D i.succ))

/-- The complete local extension uses the graph condition only. -/
def boundarySobolevExtension {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p :=
  (sobolevChartPullback (Nat.succ_pos m) (inverseChart (flattenChart e (D.chart i).frame hγ)) 𝕜 p).comp
    ((upperReflectionSobolev (Fin.last m) p).comp
      ((sobolevChartPullback (Nat.succ_pos m) (graphChart e (D.chart i).frame hγ) 𝕜 p).comp
        (boundaryCutoffSobolev D i hγ heq 𝕜 p)))


@[simp] theorem splitCoordinates_verticalReflection (m : ℕ) (z : Ambient m) :
    splitCoordinates m (verticalReflection z) =
      coordinateReflect (Fin.last m) (splitCoordinates m z) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [verticalReflection, coordinateReflect, P102.U4.ACL.coordinates,
      ExpandedFA.Sobolev.HalfSpace.reflect]
  · simp [verticalReflection, coordinateReflect, P102.U4.ACL.coordinates,
      ExpandedFA.Sobolev.HalfSpace.reflect, Fin.castSucc_ne_last]

/-- Standard reflection conjugates to the graph reflection of the fixed formula. -/
theorem flattenEquiv_reflect {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1))
    (F : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ) (x : Space (m+1)) :
    flattenEquiv e F γ
      (coordinateReflect (Fin.last m) ((flattenEquiv e F γ).symm x)) =
        e (globalReflectedPoint F γ (e.symm x)) := by
  have h := splitCoordinates_verticalReflection m (unshear γ (F.symm (e.symm x)))
  rw [flattenEquiv_symm_apply, ← h, flattenEquiv_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply, globalReflectedPoint]

/-- The physical cutoff and epigraph indicators coincide on the entire ambient space. -/
theorem graphIndicator_localizedValue {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    {𝕜 : Type} [RCLike 𝕜] (f : Space (m+1) → 𝕜) (x : Space (m+1)) :
    (globalGraphOpen e (D.chart i).frame hγ : Set (Space (m+1))).indicator
      (fun x => localizationScalarTest D 𝕜 i.succ x * f x) x =
        localizedValue e Ω (D.cutoff i.succ) f (e.symm x) := by
  by_cases hχ : D.cutoff i.succ (e.symm x) = 0
  · have hv : localizationScalarTest D 𝕜 i.succ x * f x = 0 := by
      change RCLike.ofReal (D.cutoff i.succ (e.symm x)) * f x = 0
      simp only [hχ, RCLike.ofReal_zero, zero_mul]
    have hv' : (globalGraphOpen e (D.chart i).frame hγ : Set (Space (m+1))).indicator
        (fun x => localizationScalarTest D 𝕜 i.succ x * f x) x = 0 := by
      by_cases hx : x ∈ globalGraphOpen e (D.chart i).frame hγ
      · simpa only [indicator_of_mem hx] using hv
      · exact indicator_of_notMem hx _
    rw [hv']
    simp only [localizedValue_eq_smul, Pi.smul_apply', hχ, zero_smul]
  · have hchart := D.boundary_support i (subset_tsupport _ hχ)
    have hside := globalGraphOpen_side e (D.chart i) hγ heq hchart
    have hside' : x ∈ globalGraphOpen e (D.chart i).frame hγ ↔
        e.symm x ∈ (geometricOpen e Ω : Set (Ambient m)) := by
      simpa only [e.apply_symm_apply] using hside
    by_cases hx : x ∈ globalGraphOpen e (D.chart i).frame hγ
    · rw [indicator_of_mem hx]
      rw [localizedValue, indicator_of_mem (hside'.mp hx)]
      change RCLike.ofReal (D.cutoff i.succ (e.symm x)) * f x = _
      simp only [e.apply_symm_apply, RCLike.real_smul_eq_coe_mul]
    · rw [indicator_of_notMem hx]
      simp only [localizedValue, indicator_of_notMem (fun h => hx (hside'.mpr h))]

/-- Even reflection of a cutoff pullback is precisely the source boundary summand. -/
theorem reflection_cutoff_formula {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    {𝕜 : Type} [RCLike 𝕜] (f : Space (m+1) → 𝕜) (x : Space (m+1)) :
    coordinateReflectionValue (Fin.last m) false
      (fun y => localizationScalarTest D 𝕜 i.succ (flattenEquiv e (D.chart i).frame γ y) *
        f (flattenEquiv e (D.chart i).frame γ y))
      ((flattenEquiv e (D.chart i).frame γ).symm x) =
        boundaryValue D i f (e.symm x) := by
  rw [coordinateReflectionValue_even]
  have hi (y : Space (m+1)) :
      (coordinateUpper (Fin.last m) : Set (Space (m+1))).indicator
        (fun y => localizationScalarTest D 𝕜 i.succ (flattenEquiv e (D.chart i).frame γ y) *
          f (flattenEquiv e (D.chart i).frame γ y)) y =
      (globalGraphOpen e (D.chart i).frame hγ : Set (Space (m+1))).indicator
        (fun x => localizationScalarTest D 𝕜 i.succ x * f x)
        (flattenEquiv e (D.chart i).frame γ y) := by
    have hm : flattenEquiv e (D.chart i).frame γ y ∈ globalGraphOpen e (D.chart i).frame hγ ↔
        y ∈ coordinateUpper (Fin.last m) := by
      change (flattenEquiv e (D.chart i).frame γ).symm
        (flattenEquiv e (D.chart i).frame γ y) ∈ flatHalfSpace m ↔ _
      simp only [Equiv.symm_apply_apply]
      rfl
    by_cases hy : y ∈ coordinateUpper (Fin.last m)
    · rw [indicator_of_mem hy, indicator_of_mem (hm.mpr hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (hm.mp h))]
  rw [hi, hi, Equiv.apply_symm_apply, flattenEquiv_reflect,
    graphIndicator_localizedValue D i hγ heq,
    graphIndicator_localizedValue D i hγ heq,
    e.symm_apply_apply]
  rw [boundaryValue_eq_global_sum D i γ heq]
  rfl


/-- The local norm constant depends only on the geometric chart and real cutoff. -/
def boundarySobolevBound {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    (p : ℝ≥0∞) (L : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (pullbackSobolevBound (m+1) p (shearConstant L) (shearConstant L)) *
    Real.toNNReal (ExpandedFA.Sobolev.HalfSpace.reflectionFactor p) *
    Real.toNNReal (pullbackSobolevBound (m+1) p (shearConstant L) (shearConstant L)) *
    testSobolevBound (localizationRealTest D i.succ)

theorem pullbackSobolevBound_nonneg (d : ℕ) (p : ℝ≥0∞) (L M : ℝ≥0) :
    0 ≤ pullbackSobolevBound d p L M := by
  unfold pullbackSobolevBound pullbackLpBound
  positivity

set_option maxHeartbeats 1000000 in
theorem boundarySobolevExtension_norm_le {m : ℕ} {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)}
    {Ω : Opens (Space (m+1))} (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖boundarySobolevExtension D i hγ heq 𝕜 p‖ ≤ boundarySobolevBound D i p L := by
  let P : Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p := sobolevChartPullback (Nat.succ_pos m)
    (inverseChart (flattenChart e (D.chart i).frame hγ)) 𝕜 p
  let Q : Sobolev 𝕜 (globalGraphOpen e (D.chart i).frame hγ) 1 p →L[𝕜] Sobolev 𝕜 (flatHalfSpace m) 1 p := sobolevChartPullback (Nat.succ_pos m) (graphChart e (D.chart i).frame hγ) 𝕜 p
  let R : Sobolev 𝕜 (flatHalfSpace m) 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m+1))) 1 p := @upperReflectionSobolev (m+1) 𝕜 _ (Fin.last m) p _
  let A : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (globalGraphOpen e (D.chart i).frame hγ) 1 p := boundaryCutoffSobolev D i hγ heq 𝕜 p
  have hP : ‖P‖ ≤ pullbackSobolevBound (m+1) p (shearConstant L) (shearConstant L) :=
    sobolevChartPullback_norm_le (Nat.succ_pos m) (inverseChart (flattenChart e (D.chart i).frame hγ)) 𝕜 p
  have hQ : ‖Q‖ ≤ pullbackSobolevBound (m+1) p (shearConstant L) (shearConstant L) :=
    sobolevChartPullback_norm_le (Nat.succ_pos m) (graphChart e (D.chart i).frame hγ) 𝕜 p
  have hR : ‖R‖ ≤ ExpandedFA.Sobolev.HalfSpace.reflectionFactor p :=
    upperReflectionSobolev_norm_le (𝕜 := 𝕜) (Fin.last m) p
  have hA : ‖A‖ ≤ testSobolevBound (localizationRealTest D i.succ) :=
    boundaryCutoffSobolev_norm_le D i hγ heq 𝕜 p
  change ‖P.comp (R.comp (Q.comp A))‖ ≤ _
  calc
    _ ≤ ‖P‖ * (‖R‖ * (‖Q‖ * ‖A‖)) :=
      (ContinuousLinearMap.opNorm_comp_le P (R.comp (Q.comp A))).trans
        (mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.opNorm_comp_le R (Q.comp A)).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le Q A) (norm_nonneg R)))
          (norm_nonneg P))
    _ ≤ pullbackSobolevBound (m+1) p (shearConstant L) (shearConstant L) *
        (ExpandedFA.Sobolev.HalfSpace.reflectionFactor p *
          (pullbackSobolevBound (m+1) p (shearConstant L) (shearConstant L) *
            (testSobolevBound (localizationRealTest D i.succ) : ℝ))) :=
      mul_le_mul hP
        (mul_le_mul hR (mul_le_mul hQ hA (norm_nonneg A)
          (pullbackSobolevBound_nonneg _ _ _ _))
          (mul_nonneg (norm_nonneg Q) (norm_nonneg A))
          (by unfold ExpandedFA.Sobolev.HalfSpace.reflectionFactor; positivity))
        (mul_nonneg (norm_nonneg R) (mul_nonneg (norm_nonneg Q) (norm_nonneg A)))
        (pullbackSobolevBound_nonneg _ _ _ _)
    _ = _ := by
      simp only [boundarySobolevBound, NNReal.coe_mul,
        Real.coe_toNNReal _ (pullbackSobolevBound_nonneg _ _ _ _),
        Real.coe_toNNReal _ (show 0 ≤ ExpandedFA.Sobolev.HalfSpace.reflectionFactor p from by
          unfold ExpandedFA.Sobolev.HalfSpace.reflectionFactor; positivity)]
      ring



/-- The reflected graph piece has exactly the fixed, exponent-independent representative. -/
theorem boundarySobolevExtension_underlying_ae {m : ℕ}
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)} {Ω : Opens (Space (m+1))}
    (D : Localization e Ω) (i : Fin D.count)
    {γ : Space m → ℝ} {L : ℝ≥0} (hγ : LipschitzWith L γ)
    (heq : EqOn (D.chart i).graphFunction γ
      (Metric.ball (D.chart i).center (D.chart i).radius))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) :
    sobolevUnderlying (boundarySobolevExtension D i hγ heq 𝕜 p u) =ᵐ[volume]
      fun x => boundaryValue D i (sobolevUnderlying u) (e.symm x) := by
  let A := boundaryCutoffSobolev D i hγ heq 𝕜 p u
  let Q := sobolevChartPullback (Nat.succ_pos m) (graphChart e (D.chart i).frame hγ) 𝕜 p A
  let R := upperReflectionSobolev (Fin.last m) p Q
  have hA : sobolevUnderlying A =ᵐ[
      volume.restrict (globalGraphOpen e (D.chart i).frame hγ : Set (Space (m+1)))]
      fun x => localizationScalarTest D 𝕜 i.succ x * sobolevUnderlying u x :=
    relativeCutoffSobolev_underlying_ae Ω _ p (localizationScalarTest D 𝕜 i.succ)
      (boundaryScalarTest_support D i hγ heq 𝕜) u
  have hQ : sobolevUnderlying Q =ᵐ[volume.restrict
      (coordinateUpper (Fin.last m) : Set (Space (m+1)))]
      fun y => localizationScalarTest D 𝕜 i.succ (flattenEquiv e (D.chart i).frame γ y) *
        sobolevUnderlying u (flattenEquiv e (D.chart i).frame γ y) :=
    (sobolevChartPullback_ae (Nat.succ_pos m) (graphChart e (D.chart i).frame hγ) 𝕜 p A).trans
      ((graphChart e (D.chart i).frame hγ).ae_comp hA)
  have hR : sobolevUnderlying R =ᵐ[volume]
      coordinateReflectionValue (Fin.last m) false
        (fun y => localizationScalarTest D 𝕜 i.succ (flattenEquiv e (D.chart i).frame γ y) *
          sobolevUnderlying u (flattenEquiv e (D.chart i).frame γ y)) :=
    (upperReflectionSobolev_ae (Fin.last m) p Q).trans
      (coordinateReflectionValue_congr (Fin.last m) false hQ)
  have hP := sobolevChartPullback_ae (Nat.succ_pos m)
    (inverseChart (flattenChart e (D.chart i).frame hγ)) 𝕜 p R
  have hR' := (inverseChart (flattenChart e (D.chart i).frame hγ)).ae_comp
    (ae_restrict_of_ae hR)
  simp only [Opens.coe_top, Measure.restrict_univ] at hP hR'
  filter_upwards [hP, hR'] with x hx hxR
  exact hx.trans (hxR.trans (reflection_cutoff_formula D i hγ heq (sobolevUnderlying u) x))




/-- Bounded Lipschitz opens admit one fixed compactly supported extension
formula, uniformly compatible with every scalar field and integrability exponent. -/
theorem lipschitz_extension : Expected.Extension := by
  classical
  intro m e Ω hΩ
  let D : Localization e Ω := (localization_exists e Ω hΩ).some
  have hgraph (i : Fin D.count) : ∃ γ : Space m → ℝ,
      LipschitzWith (D.chart i).constant γ ∧
        EqOn (D.chart i).graphFunction γ (Metric.ball (D.chart i).center (D.chart i).radius) :=
    (D.chart i).graph_lipschitz.extend_real
  choose γ hγ heq using hgraph
  let C : ℝ≥0∞ → ℝ≥0 := fun p =>
    testSobolevBound (localizationRealTest D 0) +
      ∑ i : Fin D.count, boundarySobolevBound D i p (D.chart i).constant
  have hE (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
      ∃ E : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
        (∀ u, sobolevUnderlying (E u) =ᵐ[volume] rawExtension D (sobolevUnderlying u)) ∧
        ‖E‖ ≤ C p := by
    let T : Fin D.count → Sobolev 𝕜 Ω 1 p →L[𝕜]
        Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p :=
      fun i => boundarySobolevExtension D i (hγ i) (heq i) 𝕜 p
    refine ⟨localizedSobolevSum D 𝕜 p T, ?_, ?_⟩
    · exact localizedSobolevSum_underlying_ae D 𝕜 p T
        (fun i u => boundarySobolevExtension_underlying_ae D i (hγ i) (heq i) 𝕜 p u)
    · exact localizedSobolevSum_norm_le D 𝕜 p T
        (fun i => boundarySobolevBound D i p (D.chart i).constant)
        (fun i => boundarySobolevExtension_norm_le D i (hγ i) (heq i) 𝕜 p)
  obtain ⟨K, B, hcongr, hfull⟩ := extension_clauses_of_sobolev D C hE
  exact ⟨D, K, C, B, hcongr, hfull⟩

/-- Restrictions of ambient compactly supported smooth functions are dense in
W¹ᵖ of every bounded Lipschitz open set when p is finite. -/
theorem lipschitz_ambient_density : Expected.Density :=
  ambient_density_of_extension lipschitz_extension


end P102.Sobolev.Extension
