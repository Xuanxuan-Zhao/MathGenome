import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.HalfSpaceExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
import Mathlib.LinearAlgebra.Transvection.Basic

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal

namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

@[simp] theorem reflect_self (i : Fin d) (x : Domain d) : reflect i x i = -x i := by
  simp [reflect]

@[simp] theorem reflect_other (i j : Fin d) (h : j ≠ i) (x : Domain d) :
    reflect i x j = x j := by simp [reflect, h]

@[simp] theorem reflect_reflect (i : Fin d) (x : Domain d) :
    reflect i (reflect i x) = x := by
  ext j
  by_cases h : j = i <;> simp [reflect, h]

/-- Reflection has no volume scaling in the manuscript's Euclidean coordinates. -/
theorem reflect_measurePreserving (i : Fin d) :
    MeasurePreserving (reflect i) volume volume := by
  classical
  unfold reflect
  apply volume_preserving_pi (f := fun j t => if j = i then -t else t)
  intro j
  by_cases hj : j = i
  · simpa [reflect, hj] using (Measure.measurePreserving_neg (volume : Measure ℝ))
  · simp only [hj, ite_false]
    exact ⟨measurable_id, Measure.map_id⟩

@[simp] theorem reflection_of_pos (i : Fin d) (odd : Bool) (f : Domain d → 𝕜)
    {x : Domain d} (hx : 0 < x i) : reflection i odd f x = f x := by
  have hn : ¬ 0 < (reflect i x) i := by simp; linarith
  cases odd <;> simp [reflection, upper, hx, not_lt.mpr hx.le]

@[simp] theorem reflection_of_neg (i : Fin d) (odd : Bool) (f : Domain d → 𝕜)
    {x : Domain d} (hx : x i < 0) :
    reflection i odd f x = if odd then -f (reflect i x) else f (reflect i x) := by
  have hn : ¬ 0 < x i := by linarith
  have hp : 0 < (reflect i x) i := by simp; linarith
  cases odd <;> simp [reflection, upper, hx, hn]

@[simp] theorem reflection_of_zero (i : Fin d) (odd : Bool) (f : Domain d → 𝕜)
    {x : Domain d} (hx : x i = 0) : reflection i odd f x = 0 := by
  cases odd <;> simp [reflection, upper, hx]

/-- Away from the null boundary, this is the stated even-reflection formula. -/
theorem even_reflection_eq_abs (i : Fin d) (f : Domain d → 𝕜)
    {x : Domain d} (hx : x i ≠ 0) :
    reflection i false f x = f (Function.update x i |x i|) := by
  classical
  rcases lt_or_gt_of_ne hx with hn | hp
  · have he : reflect i x = Function.update x i |x i| := by
      ext j
      by_cases hj : j = i <;> simp [reflect, hj, abs_of_neg hn]
    simpa only [Bool.false_eq_true, ite_false, he] using reflection_of_neg i false f hn
  · have he : Function.update x i |x i| = x := by simp [abs_of_pos hp]
    rw [he, reflection_of_pos i false f hp]

theorem reflection_restrict (i : Fin d) (odd : Bool) (f : Domain d → 𝕜) :
    reflection i odd f =ᵐ[volume.restrict (upper i : Set (Domain d))] f :=
  (ae_restrict_mem (upper i).isOpen.measurableSet).mono fun _ hx =>
    reflection_of_pos i odd f hx

theorem reflection_memLp : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.ReflectionMemLp := by
  intro 𝕜 _ d i p _ odd u
  have hz := Smoothing.zeroExtend_memLp u
  have hr := hz.comp_measurePreserving (reflect_measurePreserving i)
  cases odd
  · exact hz.add hr
  · exact hz.add hr.neg

/-- A measurable involution, useful also for nonmeasurable nonnegative integrands. -/
def reflectEquiv (i : Fin d) : Domain d ≃ᵐ Domain d where
  toFun := reflect i
  invFun := reflect i
  left_inv := reflect_reflect i
  right_inv := reflect_reflect i
  measurable_toFun := (reflect_measurePreserving i).measurable
  measurable_invFun := (reflect_measurePreserving i).measurable

/-- The two reflected pieces have disjoint supports; their norms add pointwise. -/
theorem reflection_enorm_rpow (i : Fin d) (odd : Bool) (f : Domain d → 𝕜)
    (q : ℝ) (hq : 0 < q) (x : Domain d) :
    ‖reflection i odd f x‖ₑ ^ q =
      ‖(upper i : Set (Domain d)).indicator f x‖ₑ ^ q +
      ‖(upper i : Set (Domain d)).indicator f (reflect i x)‖ₑ ^ q := by
  rcases lt_trichotomy (x i) 0 with hn | hz | hp
  · rw [reflection_of_neg i odd f hn]
    have hn' : ¬ 0 < x i := not_lt.mpr hn.le
    have hp' : 0 < (reflect i x) i := by simp; linarith
    cases odd <;> simp [upper, reflect, hn, hn', ENNReal.zero_rpow_of_pos hq]
  · rw [reflection_of_zero i odd f hz]
    simp [upper, hz, ENNReal.zero_rpow_of_pos hq]
  · rw [reflection_of_pos i odd f hp]
    have hn' : ¬ 0 < (reflect i x) i := by simp; linarith
    simp [upper, reflect, hp, not_lt.mpr hp.le, ENNReal.zero_rpow_of_pos hq]

/-- Reflection exactly doubles all positive power integrals. This statement
uses lower integrals, so it is valid without an extra integrability assumption. -/
theorem reflection_integral : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.ReflectionIntegral := by
  intro 𝕜 _ d i p _ odd u q hq
  let z : Domain d → 𝕜 := (upper i : Set (Domain d)).indicator u
  have hz : MemLp z p volume := Smoothing.zeroExtend_memLp u
  have hsplit : (fun x => ‖reflection i odd u x‖ₑ ^ q) =
      (fun x => ‖z x‖ₑ ^ q + ‖z (reflect i x)‖ₑ ^ q) :=
    funext (reflection_enorm_rpow i odd u q hq)
  rw [hsplit, lintegral_add_left' (hz.aestronglyMeasurable.enorm.pow_const q)]
  rw [(reflect_measurePreserving i).lintegral_comp_emb
    (reflectEquiv i).measurableEmbedding (f := fun x => ‖z x‖ₑ ^ q)]
  have hzint : (∫⁻ x, ‖z x‖ₑ ^ q) =
      ∫⁻ x in (upper i : Set (Domain d)), ‖u x‖ₑ ^ q := by
    rw [← lintegral_indicator (upper i).isOpen.measurableSet]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ (upper i : Set (Domain d)) <;>
      simp [z, hx, ENNReal.zero_rpow_of_pos hq]
  rw [hzint, two_mul]

/-- Even and odd reflection have the same pointwise magnitude, namely the
maximum of the magnitudes of the two disjoint pieces. -/
theorem reflection_enorm (i : Fin d) (odd : Bool) (f : Domain d → 𝕜) (x : Domain d) :
    ‖reflection i odd f x‖ₑ =
      max ‖(upper i : Set (Domain d)).indicator f x‖ₑ
        ‖(upper i : Set (Domain d)).indicator f (reflect i x)‖ₑ := by
  rcases lt_trichotomy (x i) 0 with hn | hz | hp
  · rw [reflection_of_neg i odd f hn]
    cases odd <;> simp [upper, reflect, hn, not_lt.mpr hn.le]
  · rw [reflection_of_zero i odd f hz]
    simp [upper, reflect, hz]
  · rw [reflection_of_pos i odd f hp]
    simp [upper, reflect, hp, not_lt.mpr hp.le]

/-- The infinity estimate is a direct essential-supremum computation. -/
theorem reflection_top_norm (i : Fin d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (odd : Bool) (u : DomainLp 𝕜 (upper i) p) :
    eLpNorm (reflection i odd u) ∞ volume =
      eLpNorm u ∞ (volume.restrict (upper i : Set (Domain d))) := by
  let z : Domain d → 𝕜 := (upper i : Set (Domain d)).indicator u
  have hz : MemLp z p volume := Smoothing.zeroExtend_memLp u
  have he := reflection_memLp 𝕜 d i p odd u
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (upper i).isOpen.measurableSet.nullMeasurableSet]
  change eLpNorm (reflection i odd u) ∞ volume = eLpNorm z ∞ volume
  rw [eLpNorm_exponent_top he.aestronglyMeasurable,
    eLpNorm_exponent_top hz.aestronglyMeasurable]
  apply le_antisymm
  · apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [enorm_ae_le_eLpNormEssSup z volume,
      (reflect_measurePreserving i).quasiMeasurePreserving.ae
        (enorm_ae_le_eLpNormEssSup z volume)] with x hx hxr
    rw [reflection_enorm]
    exact max_le hx hxr
  · apply eLpNormEssSup_mono_enorm_ae
    exact Eventually.of_forall fun x => by
      rw [reflection_enorm]
      exact le_max_left _ _

theorem reflection_norm : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.ReflectionNorm := by
  intro 𝕜 _ d i p _ odd u
  by_cases hp : p = ∞
  · subst p
    simpa using reflection_top_norm i odd u
  · have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
    have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
        (reflection_memLp 𝕜 d i p odd u).aestronglyMeasurable,
      reflection_integral 𝕜 d i p odd u p.toReal hpr,
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.memLp u).aestronglyMeasurable]

/-- Reflection respects a.e. equality on the half-space. -/
theorem reflection_congr (i : Fin d) (odd : Bool) {f g : Domain d → 𝕜}
    (h : f =ᵐ[volume.restrict (upper i : Set (Domain d))] g) :
    reflection i odd f =ᵐ[volume] reflection i odd g := by
  have hz := (ae_eq_restrict_iff_indicator_ae_eq (upper i).isOpen.measurableSet).mp h
  have hr := (reflect_measurePreserving i).quasiMeasurePreserving.ae_eq_comp hz
  cases odd
  · exact hz.add hr
  · exact hz.add hr.neg

theorem reflection_add (i : Fin d) (odd : Bool) (f g : Domain d → 𝕜) :
    reflection i odd (f + g) = reflection i odd f + reflection i odd g := by
  funext x
  by_cases hx : 0 < x i <;> by_cases hr : 0 < -x i <;>
    cases odd <;> simp [reflection, upper, reflect, hx, hr, Pi.add_apply] <;> abel

theorem reflection_smul (i : Fin d) (odd : Bool) (c : 𝕜) (f : Domain d → 𝕜) :
    reflection i odd (c • f) = c • reflection i odd f := by
  funext x
  by_cases hx : 0 < x i <;> by_cases hr : 0 < -x i <;>
    cases odd <;> simp [reflection, upper, reflect, hx, hr, Pi.smul_apply,
      smul_add, smul_neg, mul_add, mul_neg]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reflected a.e. class on the full space. -/
def reflectLp (i : Fin d) (odd : Bool) (u : DomainLp 𝕜 (upper i) p) :
    DomainLp 𝕜 (⊤ : Opens (Domain d)) p :=
  (show MemLp (reflection i odd u) p
    (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))) by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        reflection_memLp 𝕜 d i p odd u).toLp (reflection i odd u)

theorem reflectLp_coe (i : Fin d) (odd : Bool) (u : DomainLp 𝕜 (upper i) p) :
    reflectLp i odd u =ᵐ[volume] reflection i odd u := by
  have h : reflectLp i odd u =ᵐ[volume.restrict
      ((⊤ : Opens (Domain d)) : Set (Domain d))] reflection i odd u :=
    MemLp.coeFn_toLp _
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

theorem reflectLp_norm (i : Fin d) (odd : Bool) (u : DomainLp 𝕜 (upper i) p) :
    ‖reflectLp i odd u‖ = reflectionFactor p * ‖u‖ := by
  rw [Lp.norm_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  rw [eLpNorm_congr_ae (reflectLp_coe i odd u), reflection_norm 𝕜 d i p odd u,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def]
  rfl

theorem reflectLp_add (i : Fin d) (odd : Bool) (u v : DomainLp 𝕜 (upper i) p) :
    reflectLp i odd (u + v) = reflectLp i odd u + reflectLp i odd v := by
  apply Lp.ext
  simp only [Opens.coe_top, Measure.restrict_univ]
  exact ((reflectLp_coe i odd (u + v)).trans
    ((reflection_congr i odd (Lp.coeFn_add u v)).trans
      (EventuallyEq.of_eq (reflection_add i odd u v)))).trans
    (((reflectLp_coe i odd u).add (reflectLp_coe i odd v)).symm.trans
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using
        (Lp.coeFn_add (reflectLp i odd u) (reflectLp i odd v)).symm))

theorem reflectLp_smul (i : Fin d) (odd : Bool) (c : 𝕜) (u : DomainLp 𝕜 (upper i) p) :
    reflectLp i odd (c • u) = c • reflectLp i odd u := by
  have h₁ := reflectLp_coe i odd (c • u)
  have h₂ := reflection_congr i odd (Lp.coeFn_smul c u)
  have h₃ : reflection i odd (c • (u : Domain d → 𝕜)) =ᵐ[volume]
      c • reflection i odd u := EventuallyEq.of_eq (reflection_smul i odd c (u : Domain d → 𝕜))
  have h₄ := (reflectLp_coe i odd u).symm.const_smul c
  have h₅ : (c • reflectLp i odd u : DomainLp 𝕜 ⊤ p) =ᵐ[volume]
      c • (reflectLp i odd u : Domain d → 𝕜) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.coeFn_smul c (reflectLp i odd u)
  apply Lp.ext
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅.symm)))

/-- One continuous scalar-linear reflection map for each parity. Its defining
pointwise formula is independent of p. -/
def reflectionCLM (i : Fin d) (odd : Bool) :
    DomainLp 𝕜 (upper i) p →L[𝕜] DomainLp 𝕜 (⊤ : Opens (Domain d)) p :=
  LinearMap.mkContinuous
    { toFun := reflectLp i odd
      map_add' := reflectLp_add i odd
      map_smul' := reflectLp_smul i odd }
    (reflectionFactor p) (fun u => (reflectLp_norm i odd u).le)

/-- The bounded reflection map on derivative tuples. Graph compatibility is a
separate analytic obligation; the construction itself uses no such assumption. -/
def reflectJet (i : Fin d) (u : DerivativeTuple 𝕜 (upper i) 1 p) :
    DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p :=
  WithLp.toLp 1 (fun α => reflectLp i (normalParity i α) (u α))

theorem reflectJet_norm (i : Fin d) (u : DerivativeTuple 𝕜 (upper i) 1 p) :
    ‖reflectJet i u‖ = reflectionFactor p * ‖u‖ := by
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  simp only [reflectJet, PiLp.toLp_apply, reflectLp_norm, Finset.mul_sum]

/-- Continuous linearity of the full derivative-tuple map. -/
def reflectionJetCLM (i : Fin d) :
    DerivativeTuple 𝕜 (upper i) 1 p →L[𝕜] DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p :=
  LinearMap.mkContinuous
    { toFun := reflectJet i
      map_add' := fun u v => by
        apply PiLp.ext
        intro α
        exact reflectLp_add i (normalParity i α) (u α) (v α)
      map_smul' := fun c u => by
        apply PiLp.ext
        intro α
        exact reflectLp_smul i (normalParity i α) c (u α) }
    (reflectionFactor p) (fun u => (reflectJet_norm i u).le)

/-- The canonical first derivative index in the upstream derivative graph. -/
def coordinateIndex (j : Fin d) : DerivativeIndex d 1 :=
  boundedIndex (Pi.single j 1) (by classical simp)

@[simp] theorem normalParity_zero (i : Fin d) : normalParity i (zeroIndex d 1) = false := by
  simp [normalParity, natIndex, zeroIndex]

@[simp] theorem normalParity_coordinate (i j : Fin d) :
    normalParity i (coordinateIndex j) = decide (j = i) := by
  classical
  by_cases h : j = i
  · subst j
    simp [normalParity, coordinateIndex]
  · simp [normalParity, coordinateIndex, Pi.single_apply, h, Ne.symm h]

theorem derivativeIndex_ext {α β : DerivativeIndex d 1} (h : natIndex α = natIndex β) :
    α = β := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrFun h j

theorem coordinate_weak_derivatives (i : Fin d)
    (u : SobolevSpace 𝕜 d (upper i) 1 p) :
    Lines.HasWeakCoordinateDerivatives (underlyingLp u)
      (fun j => u.val (coordinateIndex j)) := by
  intro j
  have h := u.property (coordinateIndex j)
  change lpDistribution (u.val (coordinateIndex j)) =
    distributionDerivative 𝕜 d (upper i) (multiIndexWord (natIndex (coordinateIndex j)))
      (lpDistribution (underlyingLp u)) at h
  simpa only [coordinateIndex, natIndex_boundedIndex, Lines.multiIndexWord_single,
    distributionDerivative_cons, distributionDerivative_nil] using h

/-- Algebraic assembly of the derivative graph, conditional on the explicitly
separated boundary-compatibility lemma. No such lemma is assumed globally. -/
theorem reflectJet_mem (hreflection : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.WeakReflection)
    (i : Fin d) (u : SobolevSpace 𝕜 d (upper i) 1 p) :
    reflectJet i u.val ∈ derivativeGraph 𝕜 (⊤ : Opens (Domain d)) 1 p := by
  have hw := hreflection 𝕜 d i p (underlyingLp u)
    (fun j => u.val (coordinateIndex j)) (coordinate_weak_derivatives i u)
    (reflectLp i false (underlyingLp u))
    (fun j => reflectLp i (decide (j = i)) (u.val (coordinateIndex j)))
    (reflectLp_coe i false _) (fun j => reflectLp_coe i (decide (j = i)) _)
  intro α
  rcases Lines.multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
  · have hα : α = zeroIndex d 1 := derivativeIndex_ext hz
    subst α
    change lpDistribution (reflectLp i (normalParity i (zeroIndex d 1)) _) = _
    rw [normalParity_zero]
    exact (derivative_zero _).symm
  · have hα : α = coordinateIndex j := derivativeIndex_ext (by simpa [coordinateIndex] using hj)
    subst α
    change lpDistribution (reflectLp i (normalParity i (coordinateIndex j)) _) =
      distributionDerivative 𝕜 d ⊤ (multiIndexWord (natIndex (coordinateIndex j)))
        (lpDistribution (reflectLp i (normalParity i (zeroIndex d 1)) _))
    rw [normalParity_coordinate, normalParity_zero]
    simpa only [coordinateIndex, natIndex_boundedIndex, Lines.multiIndexWord_single,
      distributionDerivative_cons, distributionDerivative_nil] using hw j

/-- Once boundary compatibility is proved, restriction of the already bounded
linear tuple map supplies the Sobolev extension. -/
def sobolevReflection (hreflection : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.WeakReflection)
    (i : Fin d) : SobolevSpace 𝕜 d (upper i) 1 p →L[𝕜] SobolevSpace 𝕜 d ⊤ 1 p :=
  (reflectionJetCLM (𝕜 := 𝕜) (p := p) i).restrict
    (fun u hu => reflectJet_mem hreflection i ⟨u, hu⟩)

@[simp] theorem sobolevReflection_val
    (hreflection : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.WeakReflection)
    (i : Fin d) (u : SobolevSpace 𝕜 d (upper i) 1 p) :
    (sobolevReflection hreflection i u).val = reflectJet i u.val := rfl

theorem extension_of_weakReflection
    (hreflection : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.WeakReflection) :
    Specs.ExpandedFA.Sobolev.HalfSpaceExtension.ExtensionExists := by
  intro 𝕜 _ d i p _
  let E := sobolevReflection (𝕜 := 𝕜) (p := p) hreflection i
  have hcoe (u : SobolevSpace 𝕜 d (upper i) 1 p) (α : DerivativeIndex d 1) :
      (E u).val α =ᵐ[volume] reflection i (normalParity i α) (u.val α) :=
    reflectLp_coe i (normalParity i α) (u.val α)
  have hn (u : SobolevSpace 𝕜 d (upper i) 1 p) :
      ‖E u‖ = reflectionFactor p * ‖u‖ := reflectJet_norm i u.val
  refine ⟨E, ?_, ?_, hcoe, hn, ?_, ?_, ?_⟩
  · intro u
    simpa only [normalParity_zero] using hcoe u (zeroIndex d 1)
  · intro u
    exact ((hcoe u (zeroIndex d 1)).filter_mono (ae_mono Measure.restrict_le_self)).trans
      (by simpa only [normalParity_zero] using reflection_restrict i false (u.val (zeroIndex d 1)))
  · exact E.opNorm_le_bound (Real.rpow_nonneg (by norm_num) _) (fun u => (hn u).le)
  · intro hp u α
    calc
      (∫⁻ x, ‖(E u).val α x‖ₑ ^ p.toReal) =
          ∫⁻ x, ‖reflection i (normalParity i α) (u.val α) x‖ₑ ^ p.toReal :=
        lintegral_congr_ae ((hcoe u α).mono fun x hx =>
          congrArg (fun z : 𝕜 => ‖z‖ₑ ^ p.toReal) hx)
      _ = _ := reflection_integral 𝕜 d i p (normalParity i α) (u.val α) p.toReal
        (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)
  · intro hp u α
    rw [eLpNorm_congr_ae (hcoe u α)]
    exact reflection_top_norm i (normalParity i α) (u.val α)

/-- The primitive of an a.e. odd density, based at the boundary, is even. -/
theorem primitive_even {G : ℝ → 𝕜}
    (hodd : (fun t => G (-t)) =ᵐ[volume] -G) (t : ℝ) :
    (∫ s in (0 : ℝ)..-t, G s) = ∫ s in (0 : ℝ)..t, G s := by
  calc
    (∫ s in (0 : ℝ)..-t, G s) = -(∫ s in -t..0, G s) :=
      intervalIntegral.integral_symm _ _
    _ = -(∫ s in (0 : ℝ)..t, G (-s)) := by
      rw [intervalIntegral.integral_comp_neg]
      simp only [neg_zero]
    _ = -(∫ s in (0 : ℝ)..t, -G s) := by
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hodd] with s hs _
      exact hs
    _ = _ := by rw [intervalIntegral.integral_neg, neg_neg]

/-- A one-dimensional boundary gluing lemma. A positive-half-line AC
representative, an even function class, and an odd locally integrable derivative
class have a global AC representative. No norm approximation is involved. -/
theorem exists_even_AC_representative {H G f : ℝ → 𝕜}
    (hg : LocallyIntegrable G volume)
    (hf : Lines.LocallyAbsolutelyContinuousOn f (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Ioi 0), HasDerivAt f (G t) t)
    (hrep : H =ᵐ[volume.restrict (Ioi 0)] f)
    (heven : (fun t => H (-t)) =ᵐ[volume] H)
    (hodd : (fun t => G (-t)) =ᵐ[volume] -G) :
    ∃ F : ℝ → 𝕜, Continuous F ∧
      (∀ a b, AbsolutelyContinuousOnInterval F a b) ∧ H =ᵐ[volume] F ∧
      ∀ᵐ t ∂volume, HasDerivAt F (G t) t := by
  let P : ℝ → 𝕜 := fun t => ∫ s in (0 : ℝ)..t, G s
  let C : 𝕜 := f 1 - P 1
  let F : ℝ → 𝕜 := fun t => P t + C
  have hi (a b : ℝ) : IntervalIntegrable G volume a b :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hmatch (t : ℝ) (ht : 0 < t) : f t = F t := by
    have hs : uIcc 1 t ⊆ Ioi (0 : ℝ) := by
      intro s hs
      have hmin : 0 < min (1 : ℝ) t := lt_min (by norm_num) ht
      exact hmin.trans_le hs.1
    have hdt : ∀ᵐ s ∂volume, s ∈ uIcc 1 t → HasDerivAt f (G s) s := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hd] with s hds hst
      exact hds (hs hst)
    have he := OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
      (hf 1 t hs) hg hdt
    have hp := intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 1)
    change P t - P 1 = _ at hp
    change f t = P t + (f 1 - P 1)
    linear_combination -he - hp
  have hpos : ∀ᵐ t ∂volume, 0 < t → H t = F t := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hrep] with t ht htp
    exact (ht htp).trans (hmatch t htp)
  have hnegeven := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hpos
  have hFeven (t : ℝ) : F (-t) = F t := by
    change P (-t) + C = P t + C
    rw [show P (-t) = P t from primitive_even hodd t]
  have hFrep : H =ᵐ[volume] F := by
    filter_upwards [hpos, hnegeven, heven, volume.ae_ne (0 : ℝ)] with t ht hnt het htz
    rcases lt_or_gt_of_ne htz with hn | hp
    · exact het.symm.trans ((hnt (neg_pos.mpr hn)).trans (hFeven t))
    · exact ht hp
  refine ⟨F, (intervalIntegral.continuous_primitive hi 0).add continuous_const,
    ?_, hFrep, ?_⟩
  · intro a b
    exact (OneDimensional.integral_primitive_absolutelyContinuous hi a b 0).add
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  · filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht
    exact (ht 0).add_const C

@[simp] theorem fiber_normal (i : Fin d) (y : Lines.Transverse i) :
    (Lines.fiber (upper i) i y : Set ℝ) = Ioi 0 := by
  ext t
  simp [Lines.fiber, upper]

@[simp] theorem fiber_top (j : Fin d) (y : Lines.Transverse j) :
    (Lines.fiber (⊤ : Opens (Domain d)) j y : Set ℝ) = univ := rfl

@[simp] theorem reflect_normal_line (i : Fin d) (y : Lines.Transverse i) (t : ℝ) :
    reflect i (Lines.coordinateLine i y t) = Lines.coordinateLine i y (-t) := by
  ext j
  by_cases hj : j = i <;> simp [reflect, Lines.coordinateLine, hj]

/-- Parity holds pointwise, including the arbitrary zero boundary convention. -/
theorem reflection_parity (i : Fin d) (odd : Bool) (f : Domain d → 𝕜) (x : Domain d) :
    reflection i odd f (reflect i x) =
      if odd then -reflection i odd f x else reflection i odd f x := by
  cases odd <;> simp [reflection, reflect_reflect] <;> abel

/-- Convenient full-space Fubini, with the redundant restricted-top measure removed. -/
theorem ae_full_lines (j : Fin d) {f g : Domain d → 𝕜} (h : f =ᵐ[volume] g) :
    ∀ᵐ y : Lines.Transverse j ∂volume,
      (fun t => f (Lines.coordinateLine j y t)) =ᵐ[volume]
        (fun t => g (Lines.coordinateLine j y t)) := by
  have h' : f =ᵐ[volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))] g := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using h
  filter_upwards [Lines.ae_on_fibers j h'] with y hy
  change ∀ᵐ t ∂volume, f (Lines.coordinateLine j y t) = g (Lines.coordinateLine j y t)
  simpa only [fiber_top, Measure.restrict_univ] using hy

theorem locallyIntegrable_full_lines (j : Fin d)
    (v : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    ∀ᵐ y : Lines.Transverse j ∂volume,
      LocallyIntegrable (fun t => v (Lines.coordinateLine j y t)) volume := by
  simpa only [Opens.coe_top, indicator_univ] using
    Lines.domainLp_zeroExtension_locallyIntegrable_on_lines v j

/-- Coordinate weak differentiation can be checked using individual AC line
representatives. No common choice of representatives on different lines is
needed for the compact test integrals in this implication. -/
theorem coordinate_weak_of_line_representatives
    (v h : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) (j : Fin d)
    (hslice : ∀ᵐ y : Lines.Transverse j ∂volume, ∃ F : ℝ → 𝕜,
      Continuous F ∧ (∀ a b, AbsolutelyContinuousOnInterval F a b) ∧
      (fun t => v (Lines.coordinateLine j y t)) =ᵐ[volume] F ∧
      ∀ᵐ t ∂volume, HasDerivAt F (h (Lines.coordinateLine j y t)) t) :
    lpDistribution h = -(lpDistribution v).comp (testPartialCLM [j]) := by
  ext φ
  simp only [lpDistribution_apply, neg_apply, ContinuousLinearMap.comp_apply,
    Opens.coe_top, Measure.restrict_univ]
  have hv := Lines.integrable_test_mul_lp (testPartialCLM [j] φ) v
  have hh := Lines.integrable_test_mul_lp φ h
  have hpair : ∀ᵐ y : Lines.Transverse j ∂volume,
      (∫ t, φ (Lines.coordinateLine j y t) * h (Lines.coordinateLine j y t)) =
        -(∫ t, testPartialCLM [j] φ (Lines.coordinateLine j y t) *
          v (Lines.coordinateLine j y t)) := by
    filter_upwards [hslice, locallyIntegrable_full_lines j h] with y hy hgy
    obtain ⟨F, hFc, hFac, hFrep, hFd⟩ := hy
    let ψ : ℝ → 𝕜 := fun t => φ (Lines.coordinateLine j y t)
    have hψ := φ.contDiff.comp (Lines.coordinateLine_contDiff j y)
    have hcψ := φ.hasCompactSupport.comp_isClosedEmbedding
      (Lines.coordinateLine_isClosedEmbedding j y)
    have he := OneDimensional.integral_test_mul_density hFc hFac hgy hFd hψ hcψ
    calc
      (∫ t, φ (Lines.coordinateLine j y t) * h (Lines.coordinateLine j y t)) =
          -(∫ t, deriv ψ t * F t) := he
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hFrep] with t ht
        rw [Lines.testPartial_on_coordinateLine, ht]
  rw [Lines.integral_coordinateLines j hh, Lines.integral_coordinateLines j hv]
  exact (integral_congr_ae hpair).trans (integral_neg _)

/-- The normal derivative acquires the odd sign. The proof extends a primitive
on each normal line, so it applies to p=infinity without any norm density. -/
theorem normal_weak_reflection (i : Fin d) (u : DomainLp 𝕜 (upper i) p)
    (g : Fin d → DomainLp 𝕜 (upper i) p) (hw : Lines.HasWeakCoordinateDerivatives u g)
    (v h : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (hv : v =ᵐ[volume] reflection i false u)
    (hh : h =ᵐ[volume] reflection i true (g i)) :
    lpDistribution h = -(lpDistribution v).comp (testPartialCLM [i]) := by
  apply coordinate_weak_of_line_representatives v h i
  filter_upwards [Lines.ae_coordinate_line_representative u g hw i,
    ae_full_lines i hv, ae_full_lines i hh, locallyIntegrable_full_lines i h]
    with y hy hvy hhy hgy
  obtain ⟨f, hfrep, hfac, hfder⟩ := hy
  simp only [fiber_normal] at hfrep hfac hfder
  have hposv : (fun t => v (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [hvy.filter_mono (ae_mono Measure.restrict_le_self), hfrep,
      ae_restrict_mem measurableSet_Ioi] with t hvt hft ht
    exact hvt.trans ((reflection_of_pos i false u (by simpa using ht)).trans hft)
  have hposd : ∀ᵐ t ∂volume.restrict (Ioi 0),
      HasDerivAt f (h (Lines.coordinateLine i y t)) t := by
    filter_upwards [hhy.filter_mono (ae_mono Measure.restrict_le_self), hfder,
      ae_restrict_mem measurableSet_Ioi] with t hht hdt ht
    have he : h (Lines.coordinateLine i y t) = g i (Lines.coordinateLine i y t) :=
      hht.trans (reflection_of_pos i true (g i) (by simpa using ht))
    rw [he]
    exact hdt
  have heven : (fun t => v (Lines.coordinateLine i y (-t))) =ᵐ[volume]
      (fun t => v (Lines.coordinateLine i y t)) := by
    filter_upwards [hvy,
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hvy]
      with t ht hnt
    rw [hnt, ← reflect_normal_line, reflection_parity]
    simpa using ht.symm
  have hodd : (fun t => h (Lines.coordinateLine i y (-t))) =ᵐ[volume]
      -(fun t => h (Lines.coordinateLine i y t)) := by
    filter_upwards [hhy,
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hhy]
      with t ht hnt
    rw [hnt, ← reflect_normal_line, reflection_parity]
    simpa using congrArg Neg.neg ht.symm
  exact exists_even_AC_representative hgy hfac hposd hposv heven hodd

/-- Reflection of the normal component among the coordinates transverse to j. -/
def reflectTransverse (i j : Fin d) (y : Lines.Transverse j) : Lines.Transverse j :=
  fun k => if k.val = i then -y k else y k

theorem reflectTransverse_measurePreserving (i j : Fin d) :
    MeasurePreserving (reflectTransverse i j) volume volume := by
  classical
  unfold reflectTransverse
  apply volume_preserving_pi (f := fun (k : {k : Fin d // k ≠ j}) (t : ℝ) =>
    if k.val = i then -t else t)
  intro k
  by_cases hk : k.val = i
  · simpa [hk] using (Measure.measurePreserving_neg (volume : Measure ℝ))
  · simp only [hk, ite_false]
    exact ⟨measurable_id, Measure.map_id⟩

@[simp] theorem reflect_tangent_line (i j : Fin d) (hij : i ≠ j)
    (y : Lines.Transverse j) (t : ℝ) :
    reflect i (Lines.coordinateLine j y t) =
      Lines.coordinateLine j (reflectTransverse i j y) t := by
  ext k
  by_cases hkj : k = j
  · subst k
    simp [reflect, Lines.coordinateLine, Ne.symm hij]
  · simp [reflect, Lines.coordinateLine, hkj, reflectTransverse]

theorem fiber_tangent_pos (i j : Fin d) (hij : i ≠ j)
    (y : Lines.Transverse j) (hy : 0 < y ⟨i, hij⟩) :
    (Lines.fiber (upper i) j y : Set ℝ) = univ := by
  ext t
  simp [Lines.fiber, upper, Lines.coordinateLine, hij, hy]

/-- Tangential derivatives are reflected evenly. Exceptional transverse
hyperplanes have measure zero, also when the original dimension is one. -/
theorem tangent_weak_reflection (i j : Fin d) (hij : i ≠ j)
    (u : DomainLp 𝕜 (upper i) p) (g : Fin d → DomainLp 𝕜 (upper i) p)
    (hw : Lines.HasWeakCoordinateDerivatives u g)
    (v h : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (hv : v =ᵐ[volume] reflection i false u)
    (hh : h =ᵐ[volume] reflection i false (g j)) :
    lpDistribution h = -(lpDistribution v).comp (testPartialCLM [j]) := by
  classical
  apply coordinate_weak_of_line_representatives v h j
  have hs := Lines.ae_coordinate_line_representative u g hw j
  have hsR := (reflectTransverse_measurePreserving i j).quasiMeasurePreserving.ae hs
  filter_upwards [hs, hsR, ae_full_lines j hv, ae_full_lines j hh,
    Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) ⟨i, hij⟩ 0]
    with y hy hyR hvy hhy hyne
  let y' : Lines.Transverse j := if 0 < y ⟨i, hij⟩ then y else reflectTransverse i j y
  have hy' : ∃ f : ℝ → 𝕜,
      (fun t => u (Lines.coordinateLine j y' t)) =ᵐ[volume.restrict
        (Lines.fiber (upper i) j y' : Set ℝ)] f ∧
      Lines.LocallyAbsolutelyContinuousOn f (Lines.fiber (upper i) j y') ∧
      ∀ᵐ t ∂volume.restrict (Lines.fiber (upper i) j y' : Set ℝ),
        HasDerivAt f (g j (Lines.coordinateLine j y' t)) t := by
    dsimp only [y']
    split_ifs with hpos
    · exact hy
    · exact hyR
  have hpos' : 0 < y' ⟨i, hij⟩ := by
    dsimp [y']
    split_ifs with hpos
    · exact hpos
    · simp only [reflectTransverse, ite_true]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hyne)
  have heq (f : Domain d → 𝕜) (t : ℝ) :
      reflection i false f (Lines.coordinateLine j y t) = f (Lines.coordinateLine j y' t) := by
    by_cases hpos : 0 < y ⟨i, hij⟩
    · dsimp only [y']
      rw [ite_eq_left hpos]
      exact reflection_of_pos i false f (by simpa [Lines.coordinateLine, hij] using hpos)
    · have hneg : y ⟨i, hij⟩ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hyne
      dsimp only [y']
      rw [ite_eq_right hpos, reflection_of_neg i false f
        (by simpa [Lines.coordinateLine, hij] using hneg)]
      simp only [Bool.false_eq_true, ite_false, reflect_tangent_line i j hij]
  obtain ⟨f, hfrep, hfac, hfder⟩ := hy'
  have hfib := fiber_tangent_pos i j hij y' hpos'
  rw [hfib, Measure.restrict_univ] at hfrep hfder
  rw [hfib] at hfac
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_univ.mp (hfac.continuousOn isOpen_univ)
  · exact fun a b => hfac a b (subset_univ _)
  · filter_upwards [hvy, hfrep] with t hvt hft
    exact hvt.trans ((heq u t).trans hft)
  · filter_upwards [hhy, hfder] with t hht hdt
    rw [hht, heq (g j) t]
    exact hdt

/-- Weak reflection on the entire half-space, uniformly for all exponents. -/
theorem weak_reflection : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.WeakReflection := by
  intro 𝕜 _ d i p _ u g hw v h hv hh j
  by_cases hj : j = i
  · subst j
    exact normal_weak_reflection i u g hw v (h i) hv (by simpa using hh i)
  · exact tangent_weak_reflection i j (Ne.symm hj) u g hw v (h j) hv
      (by simpa only [hj, decide_false] using hh j)

/-- Even reflection gives the required bounded linear Sobolev extension. -/
theorem halfSpace_extension : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.ExtensionExists :=
  extension_of_weakReflection weak_reflection

end ExpandedFA.Sobolev.HalfSpace

namespace ExpandedFA.Sobolev.HalfSpace.Geometry
abbrev V (d : ℕ) := Fin d → ℝ

def normalLinear {d : ℕ} (a : V d) : V d →ₗ[ℝ] ℝ where
  toFun x := ∑ j, a j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def chartForm {d : ℕ} (a : V d) (i : Fin d) : V d →ₗ[ℝ] ℝ :=
  (|a i|)⁻¹ • normalLinear a - LinearMap.proj i

@[simp] theorem normalLinear_single {d : ℕ} (a : V d) (i : Fin d) :
    normalLinear a (Pi.single i 1) = a i := by
  simp [normalLinear, Pi.single_apply]

@[simp] theorem chartForm_single {d : ℕ} (a : V d) (i : Fin d) :
    chartForm a i (Pi.single i 1) = a i / |a i| - 1 := by
  simp [chartForm, div_eq_mul_inv, mul_comm]

def chartLinearEquiv {d : ℕ} (a : V d) (i : Fin d) (ha : a i ≠ 0) :
    V d ≃ₗ[ℝ] V d :=
  LinearEquiv.dilatransvection (f := chartForm a i) (v := Pi.single i 1)
    (by simpa using (isUnit_iff_ne_zero.mpr (div_ne_zero ha (abs_ne_zero.mpr ha))))

def chartLinear {d : ℕ} (a : V d) (i : Fin d) (ha : a i ≠ 0) :
    V d ≃L[ℝ] V d :=
  (chartLinearEquiv a i ha).toContinuousLinearEquiv

@[simp] theorem chartLinear_apply_normal {d : ℕ} (a : V d) (i : Fin d)
    (ha : a i ≠ 0) (x : V d) :
    chartLinear a i ha x i = (∑ j, a j * x j) / |a i| := by
  simp [chartLinear, chartLinearEquiv, LinearEquiv.dilatransvection.apply,
    chartForm, normalLinear, div_eq_mul_inv, mul_comm]

@[simp] theorem chartLinear_apply_other {d : ℕ} (a : V d) (i : Fin d)
    (ha : a i ≠ 0) (x : V d) (j : Fin d) (hj : j ≠ i) :
    chartLinear a i ha x j = x j := by
  simp [chartLinear, chartLinearEquiv, LinearEquiv.dilatransvection.apply,
    hj]

@[simp] theorem chartLinear_det {d : ℕ} (a : V d) (i : Fin d)
    (ha : a i ≠ 0) :
    LinearMap.det (chartLinear a i ha : V d →ₗ[ℝ] V d) = a i / |a i| := by
  simp [chartLinear, chartLinearEquiv]

@[simp] theorem chartLinear_abs_det {d : ℕ} (a : V d) (i : Fin d)
    (ha : a i ≠ 0) :
    |LinearMap.det (chartLinear a i ha : V d →ₗ[ℝ] V d)| = 1 := by
  simp [abs_div, ha]

theorem chartLinear_measurePreserving {d : ℕ} (a : V d) (i : Fin d)
    (ha : a i ≠ 0) : MeasurePreserving (chartLinear a i ha) volume volume := by
  refine ⟨(chartLinear a i ha).continuous.measurable, ?_⟩
  change Measure.map (chartLinear a i ha : V d →ₗ[ℝ] V d) volume = volume
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · simp [abs_div, ha]
  · exact (LinearEquiv.isUnit_det' (chartLinear a i ha).toLinearEquiv).ne_zero


def chart {d : ℕ} (a : V d) (b : ℝ) (i : Fin d) (ha : a i ≠ 0) :
    V d ≃ₜ V d :=
  (chartLinear a i ha).toHomeomorph.trans
    (Homeomorph.addRight (-Pi.single i (b / |a i|)))

theorem chart_apply {d : ℕ} (a : V d) (b : ℝ) (i : Fin d)
    (ha : a i ≠ 0) (x : V d) :
    chart a b i ha x = chartLinear a i ha x + -Pi.single i (b / |a i|) := rfl

theorem chart_symm_apply {d : ℕ} (a : V d) (b : ℝ) (i : Fin d)
    (ha : a i ≠ 0) (x : V d) :
    (chart a b i ha).symm x =
      (chartLinear a i ha).symm (x + Pi.single i (b / |a i|)) := by
  change (chartLinear a i ha).symm (x + - -Pi.single i (b / |a i|)) = _
  rw [neg_neg]

@[simp] theorem chart_apply_normal {d : ℕ} (a : V d) (b : ℝ) (i : Fin d)
    (ha : a i ≠ 0) (x : V d) :
    chart a b i ha x i = ((∑ j, a j * x j) - b) / |a i| := by
  simp [chart]
  ring

@[simp] theorem chart_apply_other {d : ℕ} (a : V d) (b : ℝ) (i : Fin d)
    (ha : a i ≠ 0) (x : V d) (j : Fin d) (hj : j ≠ i) :
    chart a b i ha x j = x j := by
  simp [chart, hj]

theorem chart_measurePreserving {d : ℕ} (a : V d) (b : ℝ) (i : Fin d)
    (ha : a i ≠ 0) : MeasurePreserving (chart a b i ha) volume volume := by
  change MeasurePreserving ((fun x : V d => x + -Pi.single i (b / |a i|)) ∘
    chartLinear a i ha) volume volume
  exact (measurePreserving_add_right (volume : Measure (V d))
    (-Pi.single i (b / |a i|))).comp (chartLinear_measurePreserving a i ha)

theorem chart_symm_measurePreserving {d : ℕ} (a : V d) (b : ℝ) (i : Fin d)
    (ha : a i ≠ 0) : MeasurePreserving (chart a b i ha).symm volume volume :=
  (chart_measurePreserving a b i ha).symm (chart a b i ha).toMeasurableEquiv

theorem chart_preimage_upper {d : ℕ} (a : V d) (b : ℝ) (i : Fin d)
    (ha : a i ≠ 0) :
    (chart a b i ha) ⁻¹' {x : V d | 0 < x i} =
      {x : V d | b < ∑ j, a j * x j} := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq, chart_apply_normal,
    div_pos_iff_of_pos_right (abs_pos.mpr ha), sub_pos]

theorem exists_pivot {d : ℕ} (a : V d) (ha : a ≠ 0) : ∃ i, a i ≠ 0 := by
  by_contra! h
  apply ha
  ext i
  exact h i

end ExpandedFA.Sobolev.HalfSpace.Geometry

namespace ExpandedFA.Sobolev.HalfSpace.LpTransport
variable {α β 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [RCLike 𝕜] {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]

def pullIso (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp 𝕜 p ν ≃ₗᵢ[𝕜] Lp 𝕜 p μ :=
  { Lp.compMeasurePreservingₗᵢ 𝕜 e he with
    invFun := Lp.compMeasurePreserving e.symm (MeasurePreserving.symm e he)
    left_inv := fun u => by
      apply Lp.ext
      exact ((Lp.coeFn_compMeasurePreserving _ (MeasurePreserving.symm e he)).trans
        ((MeasurePreserving.symm e he).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_compMeasurePreserving u he))).trans
        (Eventually.of_forall fun x => by simp [Function.comp_def])
    right_inv := fun u => by
      apply Lp.ext
      exact ((Lp.coeFn_compMeasurePreserving _ he).trans
        (he.quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_compMeasurePreserving u (MeasurePreserving.symm e he)))).trans
        (Eventually.of_forall fun x => by simp [Function.comp_def]) }

theorem pullIso_coe (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (u : Lp 𝕜 p ν) :
    pullIso e he u =ᵐ[μ] u ∘ e := Lp.coeFn_compMeasurePreserving _ he

def restrictPullIso (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (s : Set β) (hs : MeasurableSet s) :
    Lp 𝕜 p (ν.restrict s) ≃ₗᵢ[𝕜] Lp 𝕜 p (μ.restrict (e ⁻¹' s)) :=
  pullIso e (he.restrict_preimage hs)

theorem restrictPullIso_coe (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (s : Set β) (hs : MeasurableSet s) (u : Lp 𝕜 p (ν.restrict s)) :
    restrictPullIso e he s hs u =ᵐ[μ.restrict (e ⁻¹' s)] u ∘ e :=
  pullIso_coe e (he.restrict_preimage hs) u

theorem restrictPullIso_symm_coe (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (s : Set β) (hs : MeasurableSet s) (u : Lp 𝕜 p (μ.restrict (e ⁻¹' s))) :
    (restrictPullIso e he s hs).symm u =ᵐ[ν.restrict s] u ∘ e.symm :=
  Lp.coeFn_compMeasurePreserving _ (MeasurePreserving.symm e (he.restrict_preimage hs))

end ExpandedFA.Sobolev.HalfSpace.LpTransport


namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def affineMeasEquiv (A : Domain d ≃L[ℝ] Domain d) (b : Domain d) :
    Domain d ≃ᵐ Domain d where
  toFun := affineMap A b
  invFun y := A.symm (y - b)
  left_inv x := by simp [affineMap]
  right_inv y := by simp [affineMap]
  measurable_toFun := (A.continuous.add continuous_const).measurable
  measurable_invFun := (A.symm.continuous.comp (continuous_id.sub continuous_const)).measurable

def affineLpPull (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d)) :
    DomainLp 𝕜 Ω p ≃ₗᵢ[𝕜] DomainLp 𝕜 (affinePreimage A b Ω) p :=
  LpTransport.restrictPullIso (affineMeasEquiv A b) hA Ω Ω.isOpen.measurableSet

theorem affineLpPull_coe (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : DomainLp 𝕜 Ω p) :
    affineLpPull A b hA Ω u =ᵐ[volume.restrict (affinePreimage A b Ω : Set (Domain d))]
      u ∘ affineMap A b :=
  LpTransport.restrictPullIso_coe (affineMeasEquiv A b) hA Ω Ω.isOpen.measurableSet u

theorem affineLpPull_symm_coe (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : DomainLp 𝕜 (affinePreimage A b Ω) p) :
    (affineLpPull A b hA Ω).symm u =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun y => u (A.symm (y - b)) :=
  LpTransport.restrictPullIso_symm_coe (affineMeasEquiv A b) hA Ω Ω.isOpen.measurableSet u

theorem affineMap_inverse (A : Domain d ≃L[ℝ] Domain d) (b : Domain d) :
    (fun y => A.symm (y - b)) = affineMap A.symm (-A.symm b) := by
  funext y
  simp [affineMap, map_sub, sub_eq_add_neg]

theorem affine_inverse_measurePreserving (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) :
    MeasurePreserving (affineMap A.symm (-A.symm b)) volume volume := by
  have h := MeasurePreserving.symm (affineMeasEquiv A b) hA
  change MeasurePreserving (fun y => A.symm (y - b)) volume volume at h
  rwa [affineMap_inverse] at h

@[simp] theorem affinePreimage_top (A : Domain d ≃L[ℝ] Domain d) (b : Domain d) :
    affinePreimage A b (⊤ : Opens (Domain d)) = ⊤ := by
  ext x
  simp [affinePreimage]

@[simp] theorem affinePreimage_inverse (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (Ω : Opens (Domain d)) :
    affinePreimage A.symm (-A.symm b) (affinePreimage A b Ω) = Ω := by
  ext x
  change (A (A.symm x + -A.symm b) + b ∈ Ω) ↔ x ∈ Ω
  simp

end ExpandedFA.Sobolev.HalfSpace

namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions ExpandedFA.Sobolev.Lines
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

def affineHomeomorph (A : Domain d ≃L[ℝ] Domain d) (b : Domain d) : Domain d ≃ₜ Domain d :=
  A.toHomeomorph.trans (Homeomorph.addRight b)

@[simp] theorem affineHomeomorph_apply (A : Domain d ≃L[ℝ] Domain d) (b x : Domain d) :
  affineHomeomorph A b x = affineMap A b x := rfl

@[simp] theorem affineHomeomorph_symm_apply (A : Domain d ≃L[ℝ] Domain d) (b x : Domain d) :
  (affineHomeomorph A b).symm x = A.symm (x-b) := rfl

def pushTest (A : Domain d ≃L[ℝ] Domain d) (b : Domain d) (Ω : Opens (Domain d))
    (φ : Tests 𝕜 (affinePreimage A b Ω)) : Tests 𝕜 Ω where
  toFun := φ ∘ (affineHomeomorph A b).symm
  contDiff' := φ.contDiff.comp (A.symm.contDiff.comp (contDiff_id.sub contDiff_const))
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (affineHomeomorph A b).symm
  tsupport_subset' := by
    rw [tsupport_comp_eq_preimage]
    intro x hx
    have h := φ.tsupport_subset hx
    change affineMap A b ((affineHomeomorph A b).symm x) ∈ (Ω : Set (Domain d)) at h
    simpa only [← affineHomeomorph_apply, Homeomorph.apply_symm_apply] using h

@[simp] theorem pushTest_apply (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (Ω : Opens (Domain d)) (φ : Tests 𝕜 (affinePreimage A b Ω)) (x : Domain d) :
    pushTest A b Ω φ x = φ (A.symm (x-b)) := rfl

@[simp] theorem pushTest_affineMap (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (Ω : Opens (Domain d)) (φ : Tests 𝕜 (affinePreimage A b Ω)) (x : Domain d) :
    pushTest A b Ω φ (affineMap A b x) = φ x := by simp [affineMap]

theorem pushTest_partial (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (Ω : Opens (Domain d)) (φ : Tests 𝕜 (affinePreimage A b Ω)) (j : Fin d)
    (x : Domain d) :
    testPartialCLM [j] φ x = ∑ k, A (coordinateVector j) k •
      testPartialCLM [k] (pushTest A b Ω φ) (affineMap A b x) := by
  classical
  let ψ := pushTest A b Ω φ
  have hcomp : (fun y => ψ (affineMap A b y)) = φ := by
    funext y
    exact pushTest_affineMap A b Ω φ y
  have hf := ((ψ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
    (A.hasFDerivAt.add_const b)
  have hh : fderiv ℝ φ x = (fderiv ℝ ψ (affineMap A b x)).comp A.toContinuousLinearMap := by
    change HasFDerivAt (fun y => ψ (affineMap A b y)) _ x at hf
    rw [hcomp] at hf
    exact hf.fderiv
  rw [testPartial_single_apply, hh]
  change (fderiv ℝ ψ (affineMap A b x)) (A (coordinateVector j)) = _
  calc
    _ = (fderiv ℝ ψ (affineMap A b x))
        (∑ k, A (coordinateVector j) k • coordinateVector k) :=
      congrArg _ (pi_eq_sum_univ' (A (coordinateVector j)))
    _ = _ := by simp only [map_sum, map_smul, testPartial_single_apply, ψ]

theorem weak_affine_pullback (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (Ω : Opens (Domain d))
    (hf : MeasurePreserving (affineMap A b) volume volume)
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hw : HasWeakCoordinateDerivatives u g)
    (v : DomainLp 𝕜 (affinePreimage A b Ω) p)
    (h : Fin d → DomainLp 𝕜 (affinePreimage A b Ω) p)
    (hv : v =ᵐ[volume.restrict (affinePreimage A b Ω : Set (Domain d))]
      fun x => u (affineMap A b x))
    (hh : ∀ j, h j =ᵐ[volume.restrict (affinePreimage A b Ω : Set (Domain d))]
      fun x => ∑ k, A (coordinateVector j) k • g k (affineMap A b x)) :
    HasWeakCoordinateDerivatives v h := by
  classical
  intro j
  ext φ
  simp only [lpDistribution_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
  let ψ := pushTest A b Ω φ
  let Δ := affinePreimage A b Ω
  let a : Fin d → ℝ := fun k => A (coordinateVector j) k
  have hp : MeasurePreserving (affineMap A b)
      (volume.restrict (Δ : Set (Domain d))) (volume.restrict (Ω : Set (Domain d))) :=
    hf.restrict_preimage Ω.isOpen.measurableSet
  have he : MeasurableEmbedding (affineMap A b) :=
    (affineHomeomorph A b).toMeasurableEquiv.measurableEmbedding
  have hi₁ (k : Fin d) : Integrable (fun y => ψ y * g k y)
      (volume.restrict (Ω : Set (Domain d))) :=
    ψ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) (domainLp_locallyIntegrable (g k))
  have hi₂ (k : Fin d) : Integrable (fun y => testPartialCLM [k] ψ y * u y)
      (volume.restrict (Ω : Set (Domain d))) :=
    (testPartialCLM [k] ψ).integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (domainLp_locallyIntegrable u)
  have hk (k : Fin d) :
      (∫ y in (Ω : Set (Domain d)), ψ y * g k y) =
        -(∫ y in (Ω : Set (Domain d)), testPartialCLM [k] ψ y * u y) := by
    have hkw := congrArg (fun T : ScalarDistribution 𝕜 Ω => T ψ) (hw k)
    simpa only [lpDistribution_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply] using hkw
  calc
    (∫ x in (Δ : Set (Domain d)), φ x * h j x) =
        ∫ x in (Δ : Set (Domain d)), ∑ k,
          a k • (ψ (affineMap A b x) * g k (affineMap A b x)) := by
      apply integral_congr_ae
      filter_upwards [hh j] with x hx
      rw [hx]
      simp only [Finset.mul_sum, mul_smul_comm, ψ, pushTest_affineMap, a]
    _ = ∫ y in (Ω : Set (Domain d)), ∑ k, a k • (ψ y * g k y) :=
      hp.integral_comp he (fun y => ∑ k, a k • (ψ y * g k y))
    _ = ∑ k, a k • (∫ y in (Ω : Set (Domain d)), ψ y * g k y) := by
      rw [integral_finsetSum Finset.univ (f := fun k y => a k • (ψ y * g k y)) (fun k _ => (hi₁ k).smul (a k))]
      simp only [integral_smul]
    _ = -(∑ k, a k • (∫ y in (Ω : Set (Domain d)), testPartialCLM [k] ψ y * u y)) := by
      simp only [hk, smul_neg, Finset.sum_neg_distrib]
    _ = -(∫ y in (Ω : Set (Domain d)), ∑ k, a k • (testPartialCLM [k] ψ y * u y)) := by
      rw [integral_finsetSum Finset.univ (f := fun k y => a k • (testPartialCLM [k] ψ y * u y)) (fun k _ => (hi₂ k).smul (a k))]
      simp only [integral_smul]
    _ = -(∫ x in (Δ : Set (Domain d)), ∑ k,
        a k • (testPartialCLM [k] ψ (affineMap A b x) * u (affineMap A b x))) :=
      congrArg Neg.neg (hp.integral_comp he _).symm
    _ = -(∫ x in (Δ : Set (Domain d)), testPartialCLM [j] φ x * v x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx, pushTest_partial A b Ω φ j x]
      simp only [Finset.sum_mul, smul_mul_assoc, ψ, a]

end ExpandedFA.Sobolev.HalfSpace

open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal
namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_coordinate_of_ne_zero (α : DerivativeIndex d 1)
    (hα : α ≠ zeroIndex d 1) : ∃ j, α = coordinateIndex j := by
  rcases Lines.multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
  · exact (hα (derivativeIndex_ext hz)).elim
  · exact ⟨j, derivativeIndex_ext (by simpa [coordinateIndex] using hj)⟩

private def firstJetCoordinate (α : DerivativeIndex d 1) (hα : α ≠ zeroIndex d 1) : Fin d :=
  Classical.choose (exists_coordinate_of_ne_zero α hα)

private theorem firstJetCoordinate_spec (α : DerivativeIndex d 1) (hα : α ≠ zeroIndex d 1) :
    α = coordinateIndex (firstJetCoordinate α hα) :=
  Classical.choose_spec (exists_coordinate_of_ne_zero α hα)

@[simp] theorem coordinateIndex_ne_zero (j : Fin d) : coordinateIndex j ≠ zeroIndex d 1 := by
  intro h
  have he := congrFun (congrArg natIndex h) j
  simp only [coordinateIndex, natIndex_boundedIndex] at he
  simpa [natIndex, zeroIndex] using he

private theorem coordinateIndex_injective : Function.Injective (@coordinateIndex d) := by
  intro j k h
  by_contra hne
  have he := congrFun (congrArg natIndex h) j
  simpa [coordinateIndex, natIndex_boundedIndex, Pi.single_apply, hne, Ne.symm hne] using he

@[simp] private theorem firstJetCoordinate_coordinate (j : Fin d)
    (h : coordinateIndex j ≠ zeroIndex d 1) :
    firstJetCoordinate (coordinateIndex j) h = j :=
  coordinateIndex_injective (firstJetCoordinate_spec _ h).symm

def affinePullJet (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : DerivativeTuple 𝕜 Ω 1 p) : DerivativeTuple 𝕜 (affinePreimage A b Ω) 1 p :=
  WithLp.toLp 1 (fun α => if hα : α = zeroIndex d 1 then
    affineLpPull A b hA Ω (u (zeroIndex d 1)) else
    ∑ k, A (coordinateVector (firstJetCoordinate α hα)) k •
      affineLpPull A b hA Ω (u (coordinateIndex k)))

@[simp] theorem affinePullJet_zero (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : DerivativeTuple 𝕜 Ω 1 p) :
    affinePullJet A b hA Ω u (zeroIndex d 1) = affineLpPull A b hA Ω (u (zeroIndex d 1)) := by
  simp [affinePullJet]

@[simp] theorem affinePullJet_coordinate (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : DerivativeTuple 𝕜 Ω 1 p) (j : Fin d) :
    affinePullJet A b hA Ω u (coordinateIndex j) =
      ∑ k, A (coordinateVector j) k • affineLpPull A b hA Ω (u (coordinateIndex k)) := by
  simp [affinePullJet]

theorem affinePullJet_coordinate_coe (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : DerivativeTuple 𝕜 Ω 1 p) (j : Fin d) :
    affinePullJet A b hA Ω u (coordinateIndex j) =ᵐ[volume.restrict
      (affinePreimage A b Ω : Set (Domain d))]
      fun x => ∑ k, A (coordinateVector j) k • u (coordinateIndex k) (affineMap A b x) := by
  classical
  rw [affinePullJet_coordinate]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h := eventuallyEq_sum (s := Finset.univ) (fun k (_hk : k ∈ Finset.univ) =>
    (Lp.coeFn_smul (A (coordinateVector j) k)
      (affineLpPull A b hA Ω (u (coordinateIndex k)))).trans
      ((affineLpPull_coe A b hA Ω (u (coordinateIndex k))).const_smul
        (A (coordinateVector j) k)))
  exact h.trans (Eventually.of_forall fun x => by
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply])

theorem affinePullJet_add (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u v : DerivativeTuple 𝕜 Ω 1 p) :
    affinePullJet A b hA Ω (u + v) = affinePullJet A b hA Ω u + affinePullJet A b hA Ω v := by
  classical
  apply PiLp.ext
  intro α
  simp only [affinePullJet, PiLp.toLp_apply, PiLp.add_apply]
  split_ifs <;> simp [map_add, smul_add, Finset.sum_add_distrib]

theorem affinePullJet_smul (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (c : 𝕜) (u : DerivativeTuple 𝕜 Ω 1 p) :
    affinePullJet A b hA Ω (c • u) = c • affinePullJet A b hA Ω u := by
  classical
  apply PiLp.ext
  intro α
  simp only [affinePullJet, PiLp.toLp_apply, PiLp.smul_apply]
  split_ifs
  · exact map_smul (affineLpPull A b hA Ω) c _
  · simp only [PiLp.smul_apply, map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact smul_comm _ _ _

theorem affinePullJet_norm_le (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : DerivativeTuple 𝕜 Ω 1 p) :
    ‖affinePullJet A b hA Ω u‖ ≤ affineJetBound A * ‖u‖ := by
  classical
  let S := ∑ j, ∑ k, |A (coordinateVector j) k|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hcomp (α : DerivativeIndex d 1) :
      ‖affinePullJet A b hA Ω u α‖ ≤ (1 + S) * ‖u‖ := by
    simp only [affinePullJet, PiLp.toLp_apply]
    split_ifs with hα
    · rw [(affineLpPull A b hA Ω).norm_map]
      exact (PiLp.norm_apply_le u _).trans (by nlinarith [norm_nonneg u])
    · calc
        ‖∑ k, A (coordinateVector (firstJetCoordinate α hα)) k •
            affineLpPull A b hA Ω (u (coordinateIndex k))‖ ≤
            ∑ k, |A (coordinateVector (firstJetCoordinate α hα)) k| * ‖u‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          rw [norm_smul, Real.norm_eq_abs, (affineLpPull A b hA Ω).norm_map]
          exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u _) (abs_nonneg _)
        _ = (∑ k, |A (coordinateVector (firstJetCoordinate α hα)) k|) * ‖u‖ :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ S * ‖u‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact Finset.single_le_sum
            (f := fun j : Fin d => ∑ k : Fin d, |A (coordinateVector j) k|)
            (fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _)
            (Finset.mem_univ (firstJetCoordinate α hα))
        _ ≤ (1 + S) * ‖u‖ := by nlinarith [norm_nonneg u]
  rw [PiLp.norm_eq_of_L1]
  calc
    ∑ α, ‖affinePullJet A b hA Ω u α‖ ≤ ∑ _α : DerivativeIndex d 1, (1 + S) * ‖u‖ :=
      Finset.sum_le_sum fun α _ => hcomp α
    _ = affineJetBound A * ‖u‖ := by simp [affineJetBound, S, mul_assoc]

def affinePullJetCLM (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d)) :
    DerivativeTuple 𝕜 Ω 1 p →L[𝕜] DerivativeTuple 𝕜 (affinePreimage A b Ω) 1 p :=
  LinearMap.mkContinuous
    { toFun := affinePullJet A b hA Ω
      map_add' := affinePullJet_add A b hA Ω
      map_smul' := affinePullJet_smul A b hA Ω }
    (affineJetBound A) (affinePullJet_norm_le A b hA Ω)

theorem norm_affinePullJetCLM_le (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d)) :
    ‖affinePullJetCLM (𝕜 := 𝕜) (p := p) A b hA Ω‖ ≤ affineJetBound A := by
  apply LinearMap.mkContinuous_norm_le
  unfold affineJetBound
  positivity

end ExpandedFA.Sobolev.HalfSpace

open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem affineCoordinateIndex_eq (j : Fin d) :
    affineCoordinateIndex j = coordinateIndex j := by
  apply derivativeIndex_ext
  simp only [coordinateIndex, natIndex_boundedIndex]
  funext k
  by_cases hk : k = j <;>
    simp [natIndex, affineCoordinateIndex, Pi.single_apply, hk]

theorem coordinate_weak_derivatives_on (u : SobolevSpace 𝕜 d Ω 1 p) :
    Lines.HasWeakCoordinateDerivatives (underlyingLp u)
      (fun j => u.val (coordinateIndex j)) := by
  intro j
  have h := u.property (coordinateIndex j)
  change lpDistribution (u.val (coordinateIndex j)) =
    distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex (coordinateIndex j)))
      (lpDistribution (underlyingLp u)) at h
  simpa only [coordinateIndex, natIndex_boundedIndex, Lines.multiIndexWord_single,
    distributionDerivative_cons, distributionDerivative_nil] using h

theorem firstJet_mem_of_coordinateWeak (v : DerivativeTuple 𝕜 Ω 1 p)
    (hw : Lines.HasWeakCoordinateDerivatives (v (zeroIndex d 1))
      (fun j => v (coordinateIndex j))) :
    v ∈ derivativeGraph 𝕜 Ω 1 p := by
  intro α
  rcases Lines.multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
  · have hα : α = zeroIndex d 1 := derivativeIndex_ext hz
    subst α
    exact (derivative_zero _).symm
  · have hα : α = coordinateIndex j := derivativeIndex_ext (by simpa [coordinateIndex] using hj)
    subst α
    change lpDistribution (v (coordinateIndex j)) =
      distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex (coordinateIndex j)))
        (lpDistribution (v (zeroIndex d 1)))
    simpa only [coordinateIndex, natIndex_boundedIndex, Lines.multiIndexWord_single,
      distributionDerivative_cons, distributionDerivative_nil] using hw j

theorem affineLpPull_sum_smul_coe (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (c : Fin d → ℝ) (g : Fin d → DomainLp 𝕜 Ω p) :
    (∑ k, c k • affineLpPull A b hA Ω (g k) : DomainLp 𝕜 (affinePreimage A b Ω) p)
      =ᵐ[volume.restrict (affinePreimage A b Ω : Set (Domain d))]
      fun x => ∑ k, c k • g k (affineMap A b x) := by
  have hc : ∀ k, (c k • affineLpPull A b hA Ω (g k) : DomainLp 𝕜 (affinePreimage A b Ω) p)
      =ᵐ[volume.restrict (affinePreimage A b Ω : Set (Domain d))]
      fun x => c k • g k (affineMap A b x) := fun k =>
    (Lp.coeFn_smul (c k) _).trans ((affineLpPull_coe A b hA Ω (g k)).const_smul (c k))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun k => c k • affineLpPull A b hA Ω (g k)), ae_all_iff.mpr hc] with x hx hcx
  rw [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl fun k _ => hcx k)


end ExpandedFA.Sobolev.HalfSpace

open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal
namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem affinePullJet_mem (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d))
    (u : SobolevSpace 𝕜 d Ω 1 p) :
    affinePullJet A b hA Ω u.val ∈ derivativeGraph 𝕜 (affinePreimage A b Ω) 1 p := by
  apply firstJet_mem_of_coordinateWeak
  apply weak_affine_pullback A b Ω hA (underlyingLp u)
    (fun j => u.val (coordinateIndex j)) (coordinate_weak_derivatives_on u)
  · simpa only [affinePullJet_zero, underlyingLp, Function.comp_def] using affineLpPull_coe A b hA Ω (underlyingLp u)
  · intro j
    rw [affinePullJet_coordinate]
    exact affineLpPull_sum_smul_coe A b hA Ω (fun k => A (coordinateVector j) k)
      (fun k => u.val (coordinateIndex k))

/-- Pullback on the canonical Sobolev graph, with all coefficients obtained
from the actual derivative matrix of the affine map. -/
def affineSobolevPull (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (Ω : Opens (Domain d)) :
    SobolevSpace 𝕜 d Ω 1 p →L[𝕜] SobolevSpace 𝕜 d (affinePreimage A b Ω) 1 p :=
  (affinePullJetCLM A b hA Ω).restrict (fun u hu => affinePullJet_mem A b hA Ω ⟨u, hu⟩)

theorem affine_pullback : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.AffinePullback := by
  intro 𝕜 _ d A b hA Ω p _
  let P := affineSobolevPull (𝕜 := 𝕜) (p := p) A b hA Ω
  refine ⟨P, ?_, ?_, ?_⟩
  · intro u
    change affinePullJet A b hA Ω u.val (zeroIndex d 1) =ᵐ[_] _
    simpa only [affinePullJet_zero, underlyingLp, Function.comp_def] using affineLpPull_coe A b hA Ω (underlyingLp u)
  · intro u j
    simp only [affineCoordinateIndex_eq]
    change affinePullJet A b hA Ω u.val (coordinateIndex j) =ᵐ[_] _
    rw [affinePullJet_coordinate]
    exact affineLpPull_sum_smul_coe A b hA Ω (fun k => A (coordinateVector j) k)
      (fun k => u.val (coordinateIndex k))
  · apply P.opNorm_le_bound
    · unfold affineJetBound
      positivity
    · intro u
      exact affinePullJet_norm_le A b hA Ω u.val

end ExpandedFA.Sobolev.HalfSpace

open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal
namespace ExpandedFA.Sobolev.HalfSpace
open ExpandedFA.Distributions

private theorem jetBound_nonneg {d : ℕ} (A : Domain d ≃L[ℝ] Domain d) :
    0 ≤ affineJetBound A := by
  unfold affineJetBound
  positivity

private def sobolevDomainCongr {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω Δ : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (h : Ω = Δ) :
    Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p ≃ₗᵢ[𝕜]
      Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Δ 1 p := by
  subst Δ
  exact LinearIsometryEquiv.refl _ _

private theorem sobolevDomainCongr_coe {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω Δ : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (h : Ω = Δ)
    (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p)
    (α : DerivativeIndex d 1) (x : Domain d) :
    (sobolevDomainCongr h u).val α x = u.val α x := by
  subst Δ
  rfl

private theorem ae_domain_congr {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω Δ : Opens (Domain d)} (h : Ω = Δ) {f g : Domain d → 𝕜}
    (hf : f =ᵐ[volume.restrict (Ω : Set (Domain d))] g) :
    f =ᵐ[volume.restrict (Δ : Set (Domain d))] g := by
  subst Δ
  exact hf

private theorem extension_on_affinePreimage
    (hP : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.AffinePullback)
    (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (A : Domain d ≃L[ℝ] Domain d) (b : Domain d)
    (hA : MeasurePreserving (affineMap A b) volume volume) (i : Fin d)
    (H : Opens (Domain d)) (hH : affinePreimage A b (upper i) = H)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ E : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d H 1 p →L[𝕜]
        Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d ⊤ 1 p,
      (∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume]
        fun x => reflection i false
          (fun y => u.val (zeroIndex d 1) (A.symm (y - b))) (affineMap A b x)) ∧
      (∀ u, (E u).val (zeroIndex d 1) =ᵐ[volume.restrict
        (H : Set (Domain d))] u.val (zeroIndex d 1)) ∧
      ‖E‖ ≤ affineJetBound A * reflectionFactor p * affineJetBound A.symm := by
  have hB := affine_inverse_measurePreserving A b hA
  have hInv : affinePreimage A.symm (-A.symm b) H = upper i := by
    rw [← hH, affinePreimage_inverse]
  obtain ⟨P₀, hPzero₀, hPder, hPnorm₀⟩ := hP 𝕜 d A.symm (-A.symm b) hB H p
  let P := (sobolevDomainCongr (𝕜 := 𝕜) (p := p) hInv).toContinuousLinearEquiv.toContinuousLinearMap.comp P₀
  have hPzero (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d H 1 p) :
      (P u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun x => u.val (zeroIndex d 1) (affineMap A.symm (-A.symm b) x) := by
    have hc : (P u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        (P₀ u).val (zeroIndex d 1) :=
      Eventually.of_forall (sobolevDomainCongr_coe hInv (P₀ u) _)
    exact hc.trans (ae_domain_congr hInv (hPzero₀ u))
  have hPnorm : ‖P‖ ≤ affineJetBound A.symm := by
    apply P.opNorm_le_bound (jetBound_nonneg A.symm)
    intro u
    change ‖sobolevDomainCongr hInv (P₀ u)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (P₀.le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hPnorm₀ (norm_nonneg u))
  obtain ⟨Q₀, hQzero₀, hQder, hQnorm₀⟩ := hP 𝕜 d A b hA ⊤ p
  let Q := (sobolevDomainCongr (𝕜 := 𝕜) (p := p) (affinePreimage_top A b)).toContinuousLinearEquiv.toContinuousLinearMap.comp Q₀
  have hQzero (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d ⊤ 1 p) :
      (Q u).val (zeroIndex d 1) =ᵐ[volume]
        fun x => u.val (zeroIndex d 1) (affineMap A b x) := by
    have hc : (Q u).val (zeroIndex d 1) =ᵐ[volume.restrict (⊤ : Opens (Domain d))]
        (Q₀ u).val (zeroIndex d 1) :=
      Eventually.of_forall (sobolevDomainCongr_coe (affinePreimage_top A b) (Q₀ u) _)
    have hz := hc.trans (ae_domain_congr (affinePreimage_top A b) (hQzero₀ u))
    simpa only [Opens.coe_top, Measure.restrict_univ] using hz
  have hQnorm : ‖Q‖ ≤ affineJetBound A := by
    apply Q.opNorm_le_bound (jetBound_nonneg A)
    intro u
    change ‖sobolevDomainCongr (affinePreimage_top A b) (Q₀ u)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (Q₀.le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hQnorm₀ (norm_nonneg u))
  obtain ⟨R, hRzero, hRrestrict, hRder, hRnorm, hRbound, hRint, hRtop⟩ :=
    halfSpace_extension 𝕜 d i p
  let E := Q.comp (R.comp P)
  have hformula (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d H 1 p) :
      (E u).val (zeroIndex d 1) =ᵐ[volume]
        fun x => reflection i false
          (fun y => u.val (zeroIndex d 1) (A.symm (y - b))) (affineMap A b x) := by
    have hp := hPzero u
    rw [← affineMap_inverse A b] at hp
    have hRefl := reflection_congr i false hp
    have h1 := hA.quasiMeasurePreserving.ae (hRzero (P u))
    have h2 := hA.quasiMeasurePreserving.ae hRefl
    filter_upwards [hQzero (R (P u)), h1, h2] with x hx hx1 hx2
    exact hx.trans (hx1.trans hx2)
  refine ⟨E, hformula, ?_, ?_⟩
  · intro u
    filter_upwards [ae_restrict_of_ae (hformula u),
      ae_restrict_mem H.isOpen.measurableSet] with x hx hxH
    rw [hx]
    have hpos : 0 < affineMap A b x i := by
      rw [← hH] at hxH
      exact hxH
    rw [reflection_of_pos i false _ hpos]
    simp [affineMap]
  · calc
      ‖E‖ ≤ ‖Q‖ * ‖R.comp P‖ := Q.opNorm_comp_le _
      _ ≤ ‖Q‖ * (‖R‖ * ‖P‖) := mul_le_mul_of_nonneg_left (R.opNorm_comp_le P) (norm_nonneg Q)
      _ ≤ affineJetBound A * (reflectionFactor p * affineJetBound A.symm) := by
        exact mul_le_mul hQnorm
          (mul_le_mul hRbound hPnorm (norm_nonneg P)
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
          (mul_nonneg (norm_nonneg R) (norm_nonneg P)) (jetBound_nonneg A)
      _ = _ := by ring

theorem affineExtension_of_pullback
    (hP : Specs.ExpandedFA.Sobolev.HalfSpaceExtension.AffinePullback) :
    Specs.ExpandedFA.Sobolev.HalfSpaceExtension.AffineExtensionExists := by
  intro d a ha c
  obtain ⟨i, hi⟩ := Geometry.exists_pivot a ha
  let A := Geometry.chartLinear a i hi
  let b : Domain d := -Pi.single i (c / |a i|)
  have hA : MeasurePreserving (affineMap A b) volume volume :=
    Geometry.chart_measurePreserving a c i hi
  have hH : affinePreimage A b (upper i) = affineHalfSpace a c := by
    apply Opens.ext
    exact Geometry.chart_preimage_upper a c i hi
  refine ⟨i, A, b, hA, hH, ?_⟩
  intro 𝕜 _ p _
  exact extension_on_affinePreimage hP 𝕜 d A b hA i (affineHalfSpace a c) hH p

end ExpandedFA.Sobolev.HalfSpace

namespace ExpandedFA.Sobolev.HalfSpace

/-- Bounded extension on every affine half-space, over both scalar fields and
for every 1 ≤ p ≤ infinity, using one exponent-independent reflection formula. -/
theorem affineHalfSpace_extension :
    Specs.ExpandedFA.Sobolev.HalfSpaceExtension.AffineExtensionExists :=
  affineExtension_of_pullback affine_pullback

end ExpandedFA.Sobolev.HalfSpace
