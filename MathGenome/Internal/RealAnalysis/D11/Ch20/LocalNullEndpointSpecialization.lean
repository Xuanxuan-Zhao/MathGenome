import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullEndpointSpecialization
import MathGenome.Internal.RealAnalysis.D11.Ch20.LocalNullVariant
import MathGenome.Internal.RealAnalysis.D11.Ch20.LocalNullEndpointRepresentative
import MathGenome.Internal.RealAnalysis.D11.Ch20.IntegralPairing

open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
universe u
namespace D11.Ch20.LocalNullEndpointSpecialization
open D11.Ch20.LocalNullVariant

variable {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]

/-- A pointwise bounded representative also defines an ordinary L-infinity
class, used here to construct its integral functional. -/
def boundedToLp (ν : Measure X) (g : BoundedMeasurable X 𝕜) : Lp 𝕜 ∞ ν :=
  (memLp_top_of_bound g.property.1.aestronglyMeasurable
    g.property.2.choose (ae_of_all ν g.property.2.choose_spec.2)).toLp g.val

lemma boundedToLp_coe (ν : Measure X) (g : BoundedMeasurable X 𝕜) :
    boundedToLp ν g =ᵐ[ν] g.val := MemLp.coeFn_toLp _

/-- The ordinary integral functional of an actual bounded measurable function. -/
def rawPairing (ν : Measure X) (g : BoundedMeasurable X 𝕜) : Lp 𝕜 1 ν →L[𝕜] 𝕜 :=
  IntegralPairing.pairing ν 1 ∞ (boundedToLp ν g)

lemma rawPairing_apply (ν : Measure X) (g : BoundedMeasurable X 𝕜) (f : Lp 𝕜 1 ν) :
    Integrable (fun x => f x * g.val x) ν ∧
    rawPairing ν g f = ∫ x, f x * g.val x ∂ν := by
  obtain ⟨hi, he⟩ := IntegralPairing.pairing_eq_integral ν 1 ∞ (boundedToLp ν g) f
  have hae : (fun x => f x * boundedToLp ν g x) =ᵐ[ν] fun x => f x * g.val x := by
    filter_upwards [boundedToLp_coe ν g] with x hx
    rw [hx]
  exact ⟨hi.congr hae, he.trans (integral_congr_ae hae)⟩

/-- The nonzero support of an L¹ function is a countable union of finite
strict level sets, so a locally-null set meets it in an ordinary null set. -/
lemma local_null_mul_ae (ν : Measure X) (g h : BoundedMeasurable X 𝕜)
    (hgh : LocallyNull ν {x | g.val x ≠ h.val x}) (f : Lp 𝕜 1 ν) :
    (fun x => f x * g.val x) =ᵐ[ν] fun x => f x * h.val x := by
  let A (n : ℕ) : Set X := {x | 1 / (n + 1 : ℝ) < ‖f x‖}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).measurable.norm
  have hAf (n : ℕ) : ν (A n) < ∞ :=
    (L1.integrable_coeFn f).measure_norm_gt_lt_top (by positivity)
  have hz : ν (⋃ n, {x | g.val x ≠ h.val x} ∩ A n) = 0 :=
    measure_iUnion_null fun n => hgh.2 (A n) (hA n) (hAf n)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
  by_cases hf : f x = 0
  · simp [hf]
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hf)
    have he : g.val x = h.val x := by
      by_contra he
      exact hx (mem_iUnion.mpr ⟨n, he, hn⟩)
    rw [he]

theorem local_null_pairing_invariant :
    Specs.D11.Ch20.LocalNullEndpointSpecialization.local_null_pairing_invariant := by
  intro X _ 𝕜 _ ν g h hgh f
  exact ⟨(rawPairing_apply ν g f).1, (rawPairing_apply ν h f).1,
    integral_congr_ae (local_null_mul_ae ν g h hgh f)⟩

lemma rawPairing_congr (ν : Measure X) (g h : BoundedMeasurable X 𝕜)
    (hgh : ClassOf ν g = ClassOf ν h) : rawPairing ν g = rawPairing ν h := by
  ext f
  rw [(rawPairing_apply ν g f).2, (rawPairing_apply ν h f).2]
  exact integral_congr_ae (local_null_mul_ae ν g h ((classOf_eq_iff ν g h).mp hgh) f)

lemma rawPairing_add (ν : Measure X) (g h : BoundedMeasurable X 𝕜) :
    rawPairing ν (g + h) = rawPairing ν g + rawPairing ν h := by
  ext f
  rw [(rawPairing_apply ν (g + h) f).2]
  change (∫ x, f x * (g.val x + h.val x) ∂ν) = _
  simp_rw [mul_add]
  rw [integral_add (rawPairing_apply ν g f).1 (rawPairing_apply ν h f).1]
  exact congrArg₂ (· + ·) (rawPairing_apply ν g f).2.symm (rawPairing_apply ν h f).2.symm

lemma rawPairing_smul (ν : Measure X) (c : 𝕜) (g : BoundedMeasurable X 𝕜) :
    rawPairing ν (c • g) = c • rawPairing ν g := by
  ext f
  rw [(rawPairing_apply ν (c • g) f).2]
  change (∫ x, f x * (c * g.val x) ∂ν) = c * rawPairing ν g f
  simp_rw [mul_left_comm (f _) c]
  rw [integral_const_mul, (rawPairing_apply ν g f).2]

/-- Choose a bounded representative solely to construct the descended map;
`localPairing_classOf` proves that the choice has no effect. -/
def localPairing (ν : Measure X) (q : LocalLInfinity 𝕜 ν) : Lp 𝕜 1 ν →L[𝕜] 𝕜 :=
  rawPairing ν (bounded_representative ν q).choose

lemma localPairing_classOf (ν : Measure X) (g : BoundedMeasurable X 𝕜) :
    localPairing ν (ClassOf ν g) = rawPairing ν g := by
  exact rawPairing_congr ν _ g (bounded_representative ν (ClassOf ν g)).choose_spec.1

lemma localPairing_add (ν : Measure X) (q r : LocalLInfinity 𝕜 ν) :
    localPairing ν (q + r) = localPairing ν q + localPairing ν r := by
  obtain ⟨g, rfl, _⟩ := bounded_representative ν q
  obtain ⟨h, rfl, _⟩ := bounded_representative ν r
  rw [← classOf_add, localPairing_classOf, localPairing_classOf, localPairing_classOf]
  exact rawPairing_add ν g h

lemma localPairing_smul (ν : Measure X) (c : 𝕜) (q : LocalLInfinity 𝕜 ν) :
    localPairing ν (c • q) = c • localPairing ν q := by
  obtain ⟨g, rfl, _⟩ := bounded_representative ν q
  rw [← classOf_smul, localPairing_classOf, localPairing_classOf]
  exact rawPairing_smul ν c g

lemma localPairing_norm_le (ν : Measure X) (q : LocalLInfinity 𝕜 ν) :
    ‖localPairing ν q‖ ≤ ‖q‖ := by
  obtain ⟨g, hg, hbound⟩ := bounded_representative ν q
  rw [← hg, localPairing_classOf]
  apply (IntegralPairing.pairing_norm_bound ν 1 ∞ (boundedToLp ν g)).trans
  apply PairingNormEndpoint.norm_le_of_ae_bound_top _ (norm_nonneg _)
  filter_upwards [boundedToLp_coe ν g] with x hx
  rw [hx]
  simpa only [hg] using hbound x

/-- Testing on each finite measurable set controls the local norm. On such a
restriction the endpoint norm theorem is proved by finite positive level-set
tests. Zero extension preserves the L¹ norm, so every restricted test
is also a test for the original functional. -/
lemma local_norm_le_rawPairing (ν : Measure X) (g : BoundedMeasurable X 𝕜) :
    ‖ClassOf ν g‖ ≤ ‖rawPairing ν g‖ := by
  apply (classOf_norm_le_iff ν g _ (norm_nonneg _)).mpr
  have hlevel : MeasurableSet {x | ‖rawPairing ν g‖ < ‖g.val x‖} :=
    measurableSet_lt measurable_const g.property.1.norm
  refine ⟨hlevel, fun E hE hfin => ?_⟩
  letI : IsFiniteMeasure (ν.restrict E) := isFiniteMeasure_restrict.mpr hfin.ne
  let k := boundedToLp (ν.restrict E) g
  have heq : rawPairing (ν.restrict E) g =
      (rawPairing ν g).comp
        (LocalNullEndpointRepresentative.extendZero (𝕜 := 𝕜) ν E hE).toContinuousLinearMap := by
    ext f
    rw [(rawPairing_apply (ν.restrict E) g f).2]
    change _ = rawPairing ν g (LocalNullEndpointRepresentative.extendZero ν E hE f)
    rw [(rawPairing_apply ν g _).2,
      LocalNullEndpointRepresentative.integral_extendZero_mul ν E hE f g.val]
  have hn : ‖k‖ ≤ ‖rawPairing ν g‖ := by
    rw [← PairingNormEndpoint.pairing_norm_endpoint (ν.restrict E)
      (PairingNormEndpoint.sigmaFinite_semifinite (ν.restrict E) inferInstance)]
    change ‖rawPairing (ν.restrict E) g‖ ≤ _
    rw [heq]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] using
      (rawPairing ν g).le_opNorm (LocalNullEndpointRepresentative.extendZero ν E hE f)
  have hb : ∀ᵐ x ∂ν.restrict E, ‖g.val x‖ ≤ ‖rawPairing ν g‖ := by
    filter_upwards [PairingNormEndpoint.ae_norm_le k,
      boundedToLp_coe (ν.restrict E) g] with x hx he
    exact he ▸ hx.trans hn
  have hz : ν.restrict E {x | ‖rawPairing ν g‖ < ‖g.val x‖} = 0 := by
    simpa only [ae_iff, not_le] using hb
  rwa [Measure.restrict_apply hlevel] at hz

lemma localPairing_norm (ν : Measure X) (q : LocalLInfinity 𝕜 ν) :
    ‖localPairing ν q‖ = ‖q‖ := by
  apply le_antisymm (localPairing_norm_le ν q)
  obtain ⟨g, rfl, _⟩ := bounded_representative ν q
  rw [localPairing_classOf]
  exact local_norm_le_rawPairing ν g

/-- The canonical descended map, scalar-linear and norm preserving. -/
def localPairingIsometry (ν : Measure X) :
    LocalLInfinity 𝕜 ν →ₗᵢ[𝕜] (Lp 𝕜 1 ν →L[𝕜] 𝕜) where
  toFun := localPairing ν
  map_add' := localPairing_add ν
  map_smul' := localPairing_smul ν
  norm_map' := localPairing_norm ν

theorem local_pairing_isometry :
    Specs.D11.Ch20.LocalNullEndpointSpecialization.local_pairing_isometry := by
  intro X _ 𝕜 _ ν
  refine ⟨localPairingIsometry ν, ?_, ?_⟩
  · intro g f
    exact ⟨(rawPairing_apply ν g f).1,
      congrArg (fun L : Lp 𝕜 1 ν →L[𝕜] 𝕜 => L f) (localPairing_classOf ν g) |>.trans
        (rawPairing_apply ν g f).2⟩
  · intro g
    exact (localPairing_norm ν (ClassOf ν g)).trans (norm_formula ν g)

/-- The representative theorem supplies surjectivity on precisely Σ* and μ₁;
the local isometry above supplies the exact quotient and its uniqueness. -/
theorem endpoint_specialization :
    Specs.D11.Ch20.LocalNullEndpointSpecialization.endpoint_specialization := by
  intro X _ _ _ 𝕜 _ _ _ μ hμ
  letI : MeasurableSpace X := Specs.D11.Ch20.RadonDisjointCompactLocalization.M μ
  let ν := Specs.D11.Ch20.RadonDisjointCompactLocalization.m μ
  obtain ⟨J, hJ, hnorm⟩ := local_pairing_isometry (𝕜 := 𝕜) ν
  have hsurj : Function.Surjective J := by
    intro ℓ
    obtain ⟨g, hg, hb, hr⟩ :=
      LocalNullEndpointRepresentative.endpoint_representative μ hμ ℓ
    have hgB : @Measurable X 𝕜 _ RCLike.measurableSpace g := by
      rw [@BorelSpace.measurable_eq 𝕜 _ _ _] at hg
      exact hg
    let b : BoundedMeasurable X 𝕜 := ⟨g, hgB, ‖ℓ‖, norm_nonneg _, hb⟩
    refine ⟨ClassOf ν b, ?_⟩
    ext f
    exact (hJ b f).2.trans (hr f).2.symm
  refine ⟨LinearIsometryEquiv.ofSurjective J hsurj, ?_, ?_⟩
  · exact hJ
  · exact hnorm

end D11.Ch20.LocalNullEndpointSpecialization
