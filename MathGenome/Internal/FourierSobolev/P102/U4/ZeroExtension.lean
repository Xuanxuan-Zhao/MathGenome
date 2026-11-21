import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions ENNReal Topology
namespace P102.U4

abbrev sobolevZero : ZeroExtensionExpected.SpaceType := @SobolevZero
abbrev zeroExtendLp : ZeroExtensionExpected.LpExtensionType := @lpZeroExtension

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞)

theorem testToDomainLp_ae [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) :
    (testToDomainLp Ω p φ : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] φ :=
  MemLp.coeFn_toLp (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

theorem lpZeroExtension_ae (u : DomainLp 𝕜 Ω p) :
    (lpZeroExtension Ω p u : Space d → 𝕜) =ᵐ[volume] (Ω : Set (Space d)).indicator u := by
  have h : (lpZeroExtension Ω p u : Space d → 𝕜) =ᵐ[
      volume.restrict (↑(⊤ : Opens (Space d)) : Set (Space d))]
      (Ω : Set (Space d)).indicator u :=
    MemLp.coeFn_toLp (by simpa using
      (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr (Lp.memLp u))
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

/-- A.e. equality on Ω becomes ambient a.e. equality after zero extension. -/
theorem indicator_ae_eq {f g : Space d → 𝕜}
    (h : f =ᵐ[volume.restrict (Ω : Set (Space d))] g) :
    (Ω : Set (Space d)).indicator f =ᵐ[volume] (Ω : Set (Space d)).indicator g := by
  have h' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp h
  filter_upwards [h'] with x hx
  by_cases hΩ : x ∈ Ω
  · simp [hΩ, hx hΩ]
  · simp [hΩ]

theorem lpZeroExtension_norm (u : DomainLp 𝕜 Ω p) :
    ‖lpZeroExtension Ω p u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  rw [eLpNorm_congr_ae (lpZeroExtension_ae Ω p u),
    eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet]

def lpZeroExtensionLI [Fact (1 ≤ p)] :
    DomainLp 𝕜 Ω p →ₗᵢ[𝕜] DomainLp (d := d) 𝕜 ⊤ p where
  toFun := lpZeroExtension Ω p
  map_add' u v := by
    apply Lp.ext
    simp only [Opens.coe_top, Measure.restrict_univ]
    have h := indicator_ae_eq Ω (Lp.coeFn_add u v)
    have hadd := Lp.coeFn_add (lpZeroExtension Ω p u) (lpZeroExtension Ω p v)
    simp only [Opens.coe_top, Measure.restrict_univ] at hadd
    filter_upwards [lpZeroExtension_ae Ω p (u + v), lpZeroExtension_ae Ω p u,
      lpZeroExtension_ae Ω p v, h,
      hadd] with x huv hu hv hsum hadd
    rw [huv, hsum, hadd]
    simp only [Pi.add_apply, hu, hv]
    by_cases hx : x ∈ Ω <;> simp [hx]
  map_smul' c u := by
    apply Lp.ext
    simp only [Opens.coe_top, Measure.restrict_univ]
    have h := indicator_ae_eq Ω (Lp.coeFn_smul c u)
    have hcoe := Lp.coeFn_smul c (lpZeroExtension Ω p u)
    simp only [Opens.coe_top, Measure.restrict_univ] at hcoe
    simp only [RingHom.id_apply]
    filter_upwards [lpZeroExtension_ae Ω p (c • u), lpZeroExtension_ae Ω p u, h,
      hcoe] with x hcu hu hsmul hcoe
    rw [hcu, hsmul, hcoe]
    simp only [Pi.smul_apply, hu]
    by_cases hx : x ∈ Ω <;> simp [hx]
  norm_map' := lpZeroExtension_norm Ω p

theorem zeroExtension_lpIsometry : ZeroExtensionExpected.LpIsometry := by
  intro d 𝕜 _ Ω p _
  exact ⟨lpZeroExtensionLI Ω p, fun _ => rfl⟩

theorem zeroExtension_lpRepresentative : ZeroExtensionExpected.LpRepresentative :=
  @lpZeroExtension_ae

theorem zeroExtension_closure : ZeroExtensionExpected.Closure := by
  intro d 𝕜 _ Ω m p _
  change closure (smoothSobolevSubmodule 𝕜 Ω m p : Set (Sobolev 𝕜 Ω m p)) = _
  congr 1
  ext u
  change (∃ φ, testToDomainLp Ω p φ = sobolevUnderlying u) ↔ _
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ, hφ.symm⟩, fun ⟨φ, hφ⟩ => ⟨φ, hφ.symm⟩⟩

variable [Fact (1 ≤ p)]

/-- The regular distribution depends only on the restricted a.e. class. -/
theorem regular_testToDomainLp (φ : TestSpace 𝕜 Ω) :
    regularDistribution Ω (testToDomainLp Ω p φ) = regularDistribution Ω φ := by
  apply (regular_injectivity d 𝕜 Ω _ _ (domainLp_locallyIntegrable Ω p _)
    (φ.continuous.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)).mpr
  exact testToDomainLp_ae Ω p φ

/-- Every smooth compactly supported test belongs to every integer Sobolev space. -/
theorem zeroExtension_smoothInclusion : ZeroExtensionExpected.SmoothInclusion := by
  intro d 𝕜 _ Ω m p _ φ
  apply (Set.ext_iff.mp (sobolev_range Ω m p) (testToDomainLp Ω p φ)).mpr
  intro α hα
  refine ⟨testToDomainLp Ω p (testPartialWord Ω (α.sort (· ≤ ·)) φ), ?_⟩
  rw [regular_testToDomainLp Ω p, regular_testToDomainLp Ω p]
  rw [derivative_classicalCompatibility d 𝕜 Ω α φ
    (φ.contDiff.of_le (by simp)).contDiffOn]
  congr 1
  exact (testPartialWord_coe Ω _ φ).symm


/-- Coordinate derivatives are local, for arbitrary ambient functions. -/
theorem partialWord_eventuallyEq {f g : Space d → 𝕜} {x : Space d}
    (h : f =ᶠ[𝓝 x] g) (l : List (Fin d)) :
    partialWord f l =ᶠ[𝓝 x] partialWord g l := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg
      (fun A : Space d →L[ℝ] 𝕜 => A (coordinateVector d i)) hy

/-- Integrating a test product over its domain is the ambient integral. -/
theorem setIntegral_mul_test (f : Space d → 𝕜) (φ : TestSpace 𝕜 Ω) :
    (∫ x in Ω, f x * φ x) = ∫ x, f x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp only [φ.zero_on_compl hx, Pi.zero_apply, mul_zero]

/-- A weak derivative cannot create support inside Ω. -/
theorem sobolevDerivative_zero_off_compact (u : Sobolev 𝕜 Ω m p)
    (K : Compacts (Space d))
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      x ∉ K → sobolevUnderlying u x = 0) (α : SobolevIndex d m) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      x ∉ K → sobolevDerivative u α x = 0 := by
  let V : Opens (Space d) := ⟨(Ω : Set (Space d)) \ K, Ω.isOpen.sdiff K.isCompact.isClosed⟩
  have hVΩ : V ≤ Ω := fun _ hx => hx.1
  have hvloc : LocallyIntegrableOn (sobolevDerivative u α : Space d → 𝕜) V volume :=
    (domainLp_locallyIntegrable Ω p _).mono_set hVΩ
  have heq : regularDistribution V (sobolevDerivative u α) = regularDistribution V (0 : Space d → 𝕜) := by
    ext η
    let η' : TestSpace 𝕜 Ω := ⟨η, η.contDiff, η.hasCompactSupport, η.tsupport_subset.trans hVΩ⟩
    rw [regular_pairing d 𝕜 V _ hvloc,
      regular_pairing d 𝕜 V (0 : Space d → 𝕜) (show LocallyIntegrableOn (0 : Space d → 𝕜) V volume from locallyIntegrableOn_zero)]
    simp only [Pi.zero_apply, zero_mul, integral_zero]
    rw [setIntegral_mul_test V]
    change (∫ x, sobolevDerivative u α x * η' x) = 0
    rw [← setIntegral_mul_test Ω]
    have hw := (mem_sobolevSubmodule_iff Ω m p u.val).mp u.property α η'
    change lpTestPairing Ω p η' (sobolevDerivative u α) =
      (-1 : 𝕜) ^ α.val.card * lpTestPairing Ω p
        (testPartialWord Ω (α.val.sort (· ≤ ·)) η') (sobolevUnderlying u) at hw
    rw [lpTestPairing_eq_integral, lpTestPairing_eq_integral] at hw
    rw [hw]
    suffices (∫ x in Ω, sobolevUnderlying u x *
      testPartialWord Ω (α.val.sort (· ≤ ·)) η' x) = 0 by rw [this, mul_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [hu] with x hx
    by_cases hxK : x ∈ K
    · have hder : testPartialWord Ω (α.val.sort (· ≤ ·)) η' x = 0 := by
        have hcoe : ⇑(testPartialWord Ω (α.val.sort (· ≤ ·)) η') =
            ⇑(testPartialWord V (α.val.sort (· ≤ ·)) η) := by
          rw [testPartialWord_coe, testPartialWord_coe]
          rfl
        rw [hcoe]
        exact (testPartialWord V _ η).zero_on_compl (fun h => h.2 hxK)
      simp only [hder, mul_zero, Pi.zero_apply]
    · simp only [hx hxK, zero_mul, Pi.zero_apply]
  have hz := (regular_injectivity d 𝕜 V _ _ hvloc locallyIntegrableOn_zero).mp heq
  have hz' := (ae_restrict_iff' V.isOpen.measurableSet).mp hz
  apply (ae_restrict_iff' Ω.isOpen.measurableSet).mpr
  filter_upwards [hz'] with x hx hxΩ hxK
  exact hx ⟨hxΩ, hxK⟩

/-- Pairing with the zero-extended Lp class gives the original domain integral. -/
theorem integral_lpZeroExtension_mul (u : DomainLp 𝕜 Ω p) (f : Space d → 𝕜) :
    (∫ x, lpZeroExtension Ω p u x * f x) = ∫ x in Ω, u x * f x := by
  calc
    _ = ∫ x, ((Ω : Set (Space d)).indicator u) x * f x :=
      integral_congr_ae ((lpZeroExtension_ae Ω p u).mul EventuallyEq.rfl)
    _ = ∫ x, (Ω : Set (Space d)).indicator (fun x => u x * f x) x := by
      congr 1
      ext x
      by_cases hx : x ∈ Ω <;> simp [hx]
    _ = _ := integral_indicator Ω.isOpen.measurableSet


/-- Coordinatewise zero extension preserves the L¹ norm on the derivative tuple. -/
def sobolevTupleZeroExtensionLI : SobolevTuple 𝕜 Ω m p →ₗᵢ[𝕜]
    SobolevTuple (d := d) 𝕜 ⊤ m p where
  toFun v := WithLp.toLp 1 (fun α => lpZeroExtension Ω p (v α))
  map_add' v w := by
    apply PiLp.ext
    intro α
    exact (lpZeroExtensionLI Ω p).map_add (v α) (w α)
  map_smul' c v := by
    apply PiLp.ext
    intro α
    exact (lpZeroExtensionLI Ω p).map_smul c (v α)
  norm_map' v := by
    rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
    exact Finset.sum_congr rfl (fun α _ => lpZeroExtension_norm Ω p (v α))

/-- A cutoff transfers every weak equation across the artificial boundary. -/
theorem compact_zeroExtension_mem (u : Sobolev 𝕜 Ω m p)
    (hu : HasCompactSupportIn (sobolevUnderlying u)) :
    sobolevTupleZeroExtensionLI Ω m p u.val ∈ sobolevSubmodule 𝕜 ⊤ m p := by
  obtain ⟨K, hK, hu⟩ := hu
  obtain ⟨χ, _, U, hKU, _, hχ⟩ := cutoff d Ω K hK
  apply (mem_sobolevSubmodule_iff (⊤ : Opens (Space d)) m p _).mpr
  intro α φ
  let χk : TestSpace 𝕜 Ω :=
    TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  let ψ : TestSpace 𝕜 Ω := ⟨fun x => χk x * φ x,
    χk.contDiff.mul φ.contDiff, χk.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans χk.tsupport_subset⟩
  have hψ (x : Space d) (hx : x ∈ U) : ψ x = φ x := by
    change (RCLike.ofReal (χ x)) * φ x = φ x
    simp only [hχ x hx, RCLike.ofReal_one, one_mul]
  have hder (x : Space d) (hx : x ∈ K) :
      testPartialWord Ω (α.val.sort (· ≤ ·)) ψ x =
        testPartialWord (⊤ : Opens (Space d)) (α.val.sort (· ≤ ·)) φ x := by
    rw [testPartialWord_coe, testPartialWord_coe]
    have he : (ψ : Space d → 𝕜) =ᶠ[𝓝 x] φ := by
      filter_upwards [U.isOpen.mem_nhds (hKU hx)] with y hy
      exact hψ y hy
    exact (partialWord_eventuallyEq he _).eq_of_nhds
  have hleft : (∫ x in Ω, sobolevDerivative u α x * φ x) =
      ∫ x in Ω, sobolevDerivative u α x * ψ x := by
    apply integral_congr_ae
    filter_upwards [sobolevDerivative_zero_off_compact Ω m p u K hu α] with x hx
    by_cases hxK : x ∈ K
    · rw [hψ x (hKU hxK)]
    · simp only [hx hxK, zero_mul]
  have hright : (∫ x in Ω, sobolevUnderlying u x *
      testPartialWord (⊤ : Opens (Space d)) (α.val.sort (· ≤ ·)) φ x) =
      ∫ x in Ω, sobolevUnderlying u x * testPartialWord Ω (α.val.sort (· ≤ ·)) ψ x := by
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    by_cases hxK : x ∈ K
    · rw [hder x hxK]
    · simp only [hx hxK, zero_mul]
  have hw := (mem_sobolevSubmodule_iff Ω m p u.val).mp u.property α ψ
  simp only [lpTestPairing_eq_integral] at hw ⊢
  simp only [Opens.coe_top, Measure.restrict_univ]
  change (∫ x, lpZeroExtension Ω p (sobolevDerivative u α) x * φ x) =
    (-1 : 𝕜) ^ α.val.card * ∫ x, lpZeroExtension Ω p (sobolevUnderlying u) x *
      testPartialWord (⊤ : Opens (Space d)) (α.val.sort (· ≤ ·)) φ x
  rw [integral_lpZeroExtension_mul, integral_lpZeroExtension_mul, hleft, hright]
  exact hw

theorem zeroExtension_compact : ZeroExtensionExpected.CompactExtension := by
  intro d 𝕜 _ Ω m p _ _ u hu
  refine ⟨⟨sobolevTupleZeroExtensionLI Ω m p u.val, compact_zeroExtension_mem Ω m p u hu⟩,
    rfl, (fun _ => rfl), ?_⟩
  exact (sobolevTupleZeroExtensionLI Ω m p).norm_map u.val


/-- Zero extension satisfies the closed weak equations on the norm closure. -/
theorem sobolevZero_zeroExtension_mem (u : SobolevZero 𝕜 Ω m p) :
    sobolevTupleZeroExtensionLI Ω m p u.val.val ∈ sobolevSubmodule 𝕜 ⊤ m p := by
  let F : Sobolev 𝕜 Ω m p →L[𝕜] SobolevTuple (d := d) 𝕜 ⊤ m p :=
    (sobolevTupleZeroExtensionLI Ω m p).toContinuousLinearMap.comp
      (sobolevSubmodule 𝕜 Ω m p).subtypeL
  have hc : IsClosed {v : Sobolev 𝕜 Ω m p | F v ∈ sobolevSubmodule 𝕜 ⊤ m p} :=
    (sobolevSubmodule_isClosed (⊤ : Opens (Space d)) m p).preimage F.continuous
  have hs : (smoothSobolevSubmodule 𝕜 Ω m p : Set (Sobolev 𝕜 Ω m p)) ⊆
      {v | F v ∈ sobolevSubmodule 𝕜 ⊤ m p} := by
    intro v hv
    change ∃ φ, testToDomainLp Ω p φ = sobolevUnderlying v at hv
    obtain ⟨φ, hφ⟩ := hv
    apply compact_zeroExtension_mem Ω m p v
    refine ⟨⟨tsupport φ, φ.hasCompactSupport⟩, φ.tsupport_subset, ?_⟩
    have hrep : (sobolevUnderlying v : Space d → 𝕜) =ᵐ[
        volume.restrict (Ω : Set (Space d))] φ := by
      rw [← hφ]
      exact testToDomainLp_ae Ω p φ
    filter_upwards [hrep] with x hx hxK
    exact hx.trans (image_eq_zero_of_notMem_tsupport hxK)
  exact (closure_minimal hs hc) u.property

/-- Canonical linear isometric zero extension from the norm closure of tests.
The same argument also works for p = ∞; the source only requires finite p. -/
def sobolevZeroExtensionLI : SobolevZero 𝕜 Ω m p →ₗᵢ[𝕜]
    Sobolev (d := d) 𝕜 ⊤ m p where
  toFun u := ⟨sobolevTupleZeroExtensionLI Ω m p u.val.val,
    sobolevZero_zeroExtension_mem Ω m p u⟩
  map_add' u v := by
    apply Subtype.ext
    exact (sobolevTupleZeroExtensionLI Ω m p).map_add u.val.val v.val.val
  map_smul' c u := by
    apply Subtype.ext
    exact (sobolevTupleZeroExtensionLI Ω m p).map_smul c u.val.val
  norm_map' u := (sobolevTupleZeroExtensionLI Ω m p).norm_map u.val.val

theorem zeroExtension_operator : ZeroExtensionExpected.Extension := by
  intro d 𝕜 _ Ω m p _ _
  refine ⟨sobolevZeroExtensionLI Ω m p, (fun _ => rfl), (fun _ _ => rfl), ?_⟩
  intro u
  rw [(sobolevZeroExtensionLI Ω m p).norm_map]
  exact sobolev_norm Ω m p u.val

end P102.U4
