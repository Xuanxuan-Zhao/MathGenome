import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceTransport
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SecondTraceFlat
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.C1DomainExtension

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace ExpandedFA.PartIV.SecondTraceTransport
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.C1Extension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SecondTraceFlat

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω Λ : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reassemble the actual order-two graph from an order-one function and
order-one representatives of each of its first weak derivatives. Coordinate
words determine the second components, including mixed derivatives. -/
def twoJet (v : SpaceValue 𝕜 d Ω 1 p) (w : Fin d → SpaceValue 𝕜 d Ω 1 p) :
    DerivativeTuple 𝕜 Ω 2 p :=
  WithLp.toLp 1 (fun α => match multiIndexWord (natIndex α) with
    | [] => v.val (zeroIndex d 1)
    | [i] => v.val (coordinateIndex i)
    | i :: j :: _ => (w i).val (coordinateIndex j))

@[simp] lemma twoJet_zero (v : SpaceValue 𝕜 d Ω 1 p)
    (w : Fin d → SpaceValue 𝕜 d Ω 1 p) :
    twoJet v w (zeroIndex d 2) = v.val (zeroIndex d 1) := by
  simp [twoJet]

lemma twoJet_mem (v : SpaceValue 𝕜 d Ω 1 p)
    (w : Fin d → SpaceValue 𝕜 d Ω 1 p)
    (hw : ∀ i, (w i).val (zeroIndex d 1) = v.val (coordinateIndex i)) :
    twoJet v w ∈ derivativeGraph 𝕜 Ω 2 p := by
  intro α
  change lpDistribution (twoJet v w α) =
    distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex α))
      (lpDistribution (twoJet v w (zeroIndex d 2)))
  rw [twoJet_zero]
  have hlen : (multiIndexWord (natIndex α)).length ≤ 2 := by
    simpa [natIndex] using α.property
  unfold twoJet
  simp only [PiLp.toLp_apply]
  generalize he : multiIndexWord (natIndex α) = z at *
  cases z with
  | nil => simp [distributionDerivative_nil]
  | cons i z =>
    cases z with
    | nil =>
      simpa [distributionDerivative_cons, distributionDerivative_nil] using
        coordinate_weak_derivatives_on v i
    | cons j z =>
      have hz : z = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst z
      simp only [distributionDerivative_cons, distributionDerivative_nil]
      rw [← coordinate_weak_derivatives_on v i]
      change lpDistribution ((w i).val (coordinateIndex j)) =
        -(lpDistribution (v.val (coordinateIndex i))).comp (testPartialCLM [j])
      rw [← hw i]
      exact coordinate_weak_derivatives_on (w i) j

lemma twoJet_norm_le (v : SpaceValue 𝕜 d Ω 1 p)
    (w : Fin d → SpaceValue 𝕜 d Ω 1 p) :
    ‖twoJet v w‖ ≤ Fintype.card (DerivativeIndex d 2) * (‖v‖ + ∑ i, ‖w i‖) := by
  classical
  rw [PiLp.norm_eq_of_L1]
  calc
    ∑ α, ‖twoJet v w α‖ ≤
        ∑ _ : DerivativeIndex d 2, (‖v‖ + ∑ i, ‖w i‖) := by
      apply Finset.sum_le_sum
      intro α _
      simp only [twoJet, PiLp.toLp_apply]
      split
      · exact (PiLp.norm_apply_le v.val _).trans (le_add_of_nonneg_right (by positivity))
      · exact (PiLp.norm_apply_le v.val _).trans (le_add_of_nonneg_right (by positivity))
      · rename_i i j z he
        exact (PiLp.norm_apply_le (w i).val _).trans
          ((Finset.single_le_sum (fun k _ => norm_nonneg (w k)) (Finset.mem_univ i)).trans
            (le_add_of_nonneg_left (norm_nonneg v)))
    _ = _ := by simp [mul_add]

section Assembly
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (V : X →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
  (W : Fin d → X →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
  (hW : ∀ x i, (W i x).val (zeroIndex d 1) = (V x).val (coordinateIndex i))

/-- Bounded reconstruction into the original sum-norm derivative graph. -/
def assembleTwo : X →L[𝕜] SpaceValue 𝕜 d Ω 2 p :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨twoJet (V x) (fun i => W i x), twoJet_mem _ _ (hW x)⟩
      map_add' := by
        intro x y
        apply sobolev_underlying_injective 𝕜 d Ω 2 p
        change twoJet (V (x+y)) (fun i => W i (x+y)) (zeroIndex d 2) =
          twoJet (V x) (fun i => W i x) (zeroIndex d 2) +
            twoJet (V y) (fun i => W i y) (zeroIndex d 2)
        simp only [twoJet_zero, map_add, Submodule.coe_add, PiLp.add_apply]
      map_smul' := by
        intro c x
        apply sobolev_underlying_injective 𝕜 d Ω 2 p
        change twoJet (V (c • x)) (fun i => W i (c • x)) (zeroIndex d 2) =
          c • twoJet (V x) (fun i => W i x) (zeroIndex d 2)
        simp only [twoJet_zero, map_smul, Submodule.coe_smul, PiLp.smul_apply] }
    (Fintype.card (DerivativeIndex d 2) * (‖V‖ + ∑ i, ‖W i‖)) (fun x => by
      refine (twoJet_norm_le (V x) (fun i => W i x)).trans ?_
      rw [mul_assoc, add_mul, Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (V.le_opNorm x) (Finset.sum_le_sum (fun i _ => (W i).le_opNorm x)))
        (Nat.cast_nonneg _))

@[simp] lemma assembleTwo_zero (x : X) :
    (assembleTwo V W hW x).val (zeroIndex d 2) = (V x).val (zeroIndex d 1) :=
  twoJet_zero _ _
end Assembly


section Multiplication
variable (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
  (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
  (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
  (hDD : ∀ j k x, ‖partialFunction [k] (partialFunction [j] a) x‖ ≤ C)

/-- The order-one part of the product, before reconstruction. -/
def multiplyValue : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  (ambientMultiply a ha C hC0 hC hD).comp (orderOnePartCLM 𝕜 d Ω p)

/-- First product derivatives, themselves genuine order-one graph elements. -/
def multiplyDerivative (j : Fin d) :
    SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  (ambientMultiply a ha C hC0 hC hD).comp (derivativePartCLM 𝕜 d Ω p j) +
    (ambientMultiply (partialFunction [j] a) (Smoothing.partialFunction_contDiff _ a ha)
      C hC0 (hD j) (fun k => hDD j k)).comp (orderOnePartCLM 𝕜 d Ω p)

lemma multiplyDerivative_zero (u : SpaceValue 𝕜 d Ω 2 p) (j : Fin d) :
    (multiplyDerivative a ha C hC0 hC hD hDD j u).val (zeroIndex d 1) =
      (multiplyValue a ha C hC0 hC hD u).val (coordinateIndex j) := by
  change ambientMultiplyJet a ha C hC hD (derivativePart j u).val (zeroIndex d 1) +
    ambientMultiplyJet (partialFunction [j] a) (Smoothing.partialFunction_contDiff _ a ha)
      C (hD j) (fun k => hDD j k) (orderOnePart u).val (zeroIndex d 1) =
    ambientMultiplyJet a ha C hC hD (orderOnePart u).val (coordinateIndex j)
  simp only [ambientMultiplyJet_zero, ambientMultiplyJet_coordinate]
  congr 2
  simp only [derivativePart_apply, derivativePartIndex_zero, orderOnePart_apply]
  change u.val (normalIndex j) = u.val (orderOneToTwo (coordinateIndex j))
  have hi : normalIndex j = orderOneToTwo (coordinateIndex j) := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp [natIndex, normalIndex, coordinateIndex, orderOneToTwo, boundedIndex, Pi.single_apply, apply_ite]
  rw [hi]

/-- Smooth ambient multiplication on the existing full order-two graph.
The only quantitative inputs here are ordinary bounds on the coefficient's
classical derivatives, not assumptions about weak product rules. -/
def multiplyTwo : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Ω 2 p :=
  assembleTwo (multiplyValue a ha C hC0 hC hD)
    (multiplyDerivative a ha C hC0 hC hD hDD)
    (multiplyDerivative_zero a ha C hC0 hC hD hDD)

lemma multiplyTwo_coe (u : SpaceValue 𝕜 d Ω 2 p) :
    (multiplyTwo a ha C hC0 hC hD hDD u).val (zeroIndex d 2) =ᵐ[
      volume.restrict (Ω : Set (Domain d))] fun x => a x * u.val (zeroIndex d 2) x := by
  rw [multiplyTwo, assembleTwo_zero]
  exact ambientMultiply_coe a ha C hC0 hC hD (orderOnePart u)

lemma multiplyTwo_supported (K : Set (Domain d))
    (hK : (Ω : Set (Domain d)) ∩ tsupport a ⊆ K)
    (u : SpaceValue 𝕜 d Ω 2 p) :
    multiplyTwo a ha C hC0 hC hD hDD u ∈ supportedSobolev 𝕜 Ω K 2 p := by
  classical
  have hv := ambientMultiply_supported a ha C hC0 hC hD K hK (orderOnePart u)
  have hw (i : Fin d) : multiplyDerivative a ha C hC0 hC hD hDD i u ∈
      supportedSobolev 𝕜 Ω K 1 p := by
    apply (supportedSobolev 𝕜 Ω K 1 p).add_mem
    · exact ambientMultiply_supported a ha C hC0 hC hD K hK (derivativePart i u)
    · apply ambientMultiply_supported (partialFunction [i] a)
        (Smoothing.partialFunction_contDiff _ a ha) C hC0 (hD i) (fun j => hDD i j) K
      exact fun x hx => hK ⟨hx.1, (tsupport_fderiv_apply_subset ℝ (coordinateVector i)) hx.2⟩
  intro α
  change ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)), x ∉ K →
    twoJet (multiplyValue a ha C hC0 hC hD u)
      (fun i => multiplyDerivative a ha C hC0 hC hD hDD i u) α x = 0
  simp only [twoJet, PiLp.toLp_apply]
  split
  · exact hv _
  · exact hv _
  · exact hw _ _
end Multiplication

/-- Compact support supplies a finite bound on the coefficient and all
classical derivatives through order two, before choosing p or Ω. -/
lemma compact_second_bounds (a : Domain d → 𝕜)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖a x‖ ≤ C) ∧
      (∀ j x, ‖partialFunction [j] a x‖ ≤ C) ∧
      (∀ j k x, ‖partialFunction [k] (partialFunction [j] a) x‖ ≤ C) := by
  classical
  let η : Tests 𝕜 (⊤ : Opens (Domain d)) := ⟨a, ha, hc, subset_univ _⟩
  obtain ⟨C₀, hC₀, ha₀, ha₁⟩ := ambient_test_bounds η
  choose D hD hD₀ hD₁ using fun j : Fin d => ambient_test_bounds (testPartialCLM [j] η)
  refine ⟨C₀ + ∑ j, D j, add_nonneg hC₀ (Finset.sum_nonneg (fun j _ => hD j)), ?_, ?_, ?_⟩
  · intro x
    exact (ha₀ x).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hD j)))
  · intro j x
    exact (ha₁ j x).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hD j)))
  · intro j k x
    have hb := hD₁ j k x
    have he : partialFunction [k] (partialFunction [j] a) x =
        partialFunction [k] (testPartialCLM [j] η) x := by
      rw [testPartial_formula]
      rfl
    rw [he]
    exact hb.trans ((Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left hC₀))

/-- Compact smooth multiplication, with no boundary vanishing condition on
its coefficient. In fact this holds also at p=1 and p=infinity. -/
theorem smooth_multiplication : Spec.SmoothMultiplication := by
  intro 𝕜 _ d Ω p _ a ha hc
  obtain ⟨C, hC0, hC, hD, hDD⟩ := compact_second_bounds a ha hc
  refine ⟨multiplyTwo a ha C hC0 hC hD hDD, fun u f hf => ?_⟩
  exact (multiplyTwo_coe a ha C hC0 hC hD hDD u).trans
    (hf.symm.mono (fun x hx => congrArg (a x * ·) hx))

/-- Localized zero extension of order-two patches is a bounded linear map. -/
theorem localized_zero_extension : Spec.LocalizedZeroExtension := by
  intro 𝕜 _ d Ω Λ h K hK hKΩ a ha hc hcoeff p _
  obtain ⟨C, hC0, hC, hD, hDD⟩ := compact_second_bounds a ha hc
  let M : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Ω 2 p :=
    multiplyTwo a ha C hC0 hC hD hDD
  let E := (relativeZeroExtensionCLM h K hK hKΩ).comp
    (M.codRestrict (supportedSobolev 𝕜 Ω K 2 p)
      (multiplyTwo_supported a ha C hC0 hC hD hDD K hcoeff))
  refine ⟨E, fun u f hf => ?_⟩
  have hm := (multiplyTwo_coe a ha C hC0 hC hD hDD u).trans
    (hf.symm.mono (fun x hx => congrArg (a x * ·) hx))
  have hm' := ((ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp hm).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (Λ : Set (Domain d)))))
  exact (zeroLp_coe (Λ := Λ) ((M u).val (zeroIndex d 2))).trans hm'

/-- Existing all-order relative zero extension supplies exact order-two
recovery as well, including dimension zero and the empty open set. -/
theorem supported_recovery : Spec.SupportedRecovery := by
  intro 𝕜 _ d Ω Λ h K hK hKΩ p _ u hu
  refine ⟨relativeZeroExtend h K hK hKΩ u hu, fun α => zeroLp_coe (u.val α),
    ?_, relativeZeroExtend_norm h K hK hKΩ u hu⟩
  intro α
  have hz := (zeroLp_coe (Λ := Λ) (u.val α)).filter_mono
    (ae_mono (Measure.restrict_mono h le_rfl))
  filter_upwards [hz, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  exact hx.trans (Set.indicator_of_mem hxΩ _)


/-! A C¹ real coefficient on an arbitrary open set suffices for the iterated
weak chain rule. Smoothness of a coordinate map beyond C² is never assumed. -/
open private firstJetCoordinate firstJetCoordinate_coordinate
  from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension

section FirstTuple
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (F : X →L[𝕜] DomainLp 𝕜 Ω p) (G : Fin d → X →L[𝕜] DomainLp 𝕜 Ω p)

def firstTuple : X →L[𝕜] DerivativeTuple 𝕜 Ω 1 p where
  toFun x := WithLp.toLp 1 (fun α => if hα : α = zeroIndex d 1 then F x
    else G (firstJetCoordinate α hα) x)
  map_add' x y := by
    apply PiLp.ext
    intro α
    simp only [PiLp.toLp_apply, PiLp.add_apply]
    split_ifs <;> exact map_add _ x y
  map_smul' c x := by
    apply PiLp.ext
    intro α
    simp only [PiLp.toLp_apply, PiLp.smul_apply]
    split_ifs <;> exact map_smul _ c x
  cont := (PiLp.continuous_toLp 1 _).comp (continuous_pi (fun α => by
    dsimp
    split_ifs
    · exact F.continuous
    · exact (G _).continuous))

@[simp] lemma firstTuple_zero (x : X) :
    firstTuple F G x (zeroIndex d 1) = F x := by simp [firstTuple]

@[simp] lemma firstTuple_coordinate (x : X) (j : Fin d) :
    firstTuple F G x (coordinateIndex j) = G j x := by simp [firstTuple]
end FirstTuple

def evalOne (α : DerivativeIndex d 1) :
    SpaceValue 𝕜 d Ω 1 p →L[𝕜] DomainLp 𝕜 Ω p :=
  (PiLp.proj _ _ α).comp (derivativeGraph 𝕜 Ω 1 p).subtypeL

section LocalC1
variable (a : Domain d → ℝ) (ha : ContDiffOn ℝ 1 a Ω)
  (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x ∈ Ω, ‖a x‖ ≤ B)
  (hDa : ∀ j x, x ∈ Ω → ‖fderiv ℝ a x (coordinateVector j)‖ ≤ B)

/-- Real multiplication on Lp uses only a.e. coefficients on Ω. -/
def localRealMul : DomainLp 𝕜 Ω p →L[𝕜] DomainLp 𝕜 Ω p :=
  Transport.aeSmulLpCLM a
    (ha.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet) B
    (by filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx; exact hB x hx)

lemma localRealMul_coe (u : DomainLp 𝕜 Ω p) :
    localRealMul a ha B hB u =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => a x • u x := by
  unfold localRealMul
  exact Transport.aeSmulLp_coe a
    (ha.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet) B
    (by filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx; exact hB x hx) u

/-- The raw first product jet is continuous before asserting its weak rules. -/
def localProductJet : SpaceValue 𝕜 d Ω 1 p →L[𝕜] DerivativeTuple 𝕜 Ω 1 p :=
  firstTuple ((localRealMul a ha B hB).comp (evalOne (zeroIndex d 1)))
    (fun j => (localRealMul a ha B hB).comp (evalOne (coordinateIndex j)) +
      (Transport.aeSmulLpCLM (𝕜 := 𝕜) (p := p) (fun x => fderiv ℝ a x (coordinateVector j))
        ((Classical.c1_partial_continuousOn a ha j).aestronglyMeasurable Ω.isOpen.measurableSet)
        B (by filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx; exact hDa j x hx)).comp (evalOne (zeroIndex d 1)))

lemma localProductJet_zero_coe (u : SpaceValue 𝕜 d Ω 1 p) :
    localProductJet a ha B hB hDa u (zeroIndex d 1) =ᵐ[
      volume.restrict (Ω : Set (Domain d))] fun x => a x • u.val (zeroIndex d 1) x := by
  simp only [localProductJet, firstTuple_zero, ContinuousLinearMap.comp_apply]
  exact localRealMul_coe a ha B hB _

lemma localProductJet_coordinate_coe (u : SpaceValue 𝕜 d Ω 1 p) (j : Fin d) :
    localProductJet a ha B hB hDa u (coordinateIndex j) =ᵐ[
      volume.restrict (Ω : Set (Domain d))]
      fun x => a x • u.val (coordinateIndex j) x +
        fderiv ℝ a x (coordinateVector j) • u.val (zeroIndex d 1) x := by
  simp only [localProductJet, firstTuple_coordinate, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply]
  exact (Lp.coeFn_add _ _).trans ((localRealMul_coe a ha B hB _).add
    (Transport.aeSmulLp_coe (fun x => fderiv ℝ a x (coordinateVector j))
      ((Classical.c1_partial_continuousOn a ha j).aestronglyMeasurable Ω.isOpen.measurableSet)
      B (by filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx; exact hDa j x hx)
      (u.val (zeroIndex d 1))))

lemma localProductJet_mem_smooth (u : SpaceValue 𝕜 d Ω 1 p)
    (f : Domain d → 𝕜) (hf : ContDiffOn ℝ 1 f Ω)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f) :
    localProductJet a ha B hB hDa u ∈ derivativeGraph 𝕜 Ω 1 p := by
  apply Classical.c1_firstJet_mem (fun x => a x • f x) (ha.smul hf)
  · exact (localProductJet_zero_coe a ha B hB hDa u).trans (hu.mono (fun x hx => congrArg (a x • ·) hx))
  · intro j
    apply (localProductJet_coordinate_coe a ha B hB hDa u j).trans
    filter_upwards [hu, Classical.c1_representative_derivative u f hf hu j,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hdx hxΩ
    have hda := (ha.contDiffAt (Ω.isOpen.mem_nhds hxΩ)).differentiableAt (by simp)
    have hdf := (hf.contDiffAt (Ω.isOpen.mem_nhds hxΩ)).differentiableAt (by simp)
    rw [hx, hdx]
    change _ = fderiv ℝ (a • f) x (coordinateVector j)
    rw [fderiv_smul hda hdf]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply]

/-- Density and closedness pass the genuine product rule to arbitrary W1p
inputs. No derivative formula is assumed of a nonsmooth representative. -/
lemma localProductJet_mem (hp : p ≠ ∞) (u : SpaceValue 𝕜 d Ω 1 p) :
    localProductJet a ha B hB hDa u ∈ derivativeGraph 𝕜 Ω 1 p := by
  have hc : IsClosed {u : SpaceValue 𝕜 d Ω 1 p |
      localProductJet a ha B hB hDa u ∈ derivativeGraph 𝕜 Ω 1 p} :=
    Smoothing.derivativeGraph_isClosed.preimage (localProductJet a ha B hB hDa).continuous
  have hsub : Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothMembers
      𝕜 d Ω 1 p ⊆ {u : SpaceValue 𝕜 d Ω 1 p |
        localProductJet a ha B hB hDa u ∈ derivativeGraph 𝕜 Ω 1 p} := by
    rintro v ⟨f, hf, hv⟩
    exact localProductJet_mem_smooth a ha B hB hDa v f (hf.of_le (by simp)) hv
  exact (hc.closure_subset_iff.mpr hsub) (Smoothing.smooth_density 𝕜 d Ω 1 p hp u)

def localC1Multiply (hp : p ≠ ∞) :
    SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  (localProductJet a ha B hB hDa).codRestrict (derivativeGraph 𝕜 Ω 1 p)
    (localProductJet_mem a ha B hB hDa hp)

lemma localC1Multiply_coe (hp : p ≠ ∞) (u : SpaceValue 𝕜 d Ω 1 p) :
    (localC1Multiply a ha B hB hDa hp u).val (zeroIndex d 1) =ᵐ[
      volume.restrict (Ω : Set (Domain d))] fun x => a x • u.val (zeroIndex d 1) x :=
  localProductJet_zero_coe a ha B hB hDa u
end LocalC1


open C1Extension.Transport

lemma chartCoefficient_c1 (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (j k : Fin d) :
    ContDiffOn ℝ 1 (chartCoefficient Φ j k) Φ.source := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ Φ) Φ.source :=
    hΦ.fderiv_of_isOpen Φ.open_source (by norm_num)
  exact (contDiff_apply ℝ (fun _ : Fin d => ℝ) k).comp_contDiffOn
    (hd.clm_apply contDiffOn_const)

section BoundedChart
variable (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
  (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
  (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
  (hDD : ∀ j k l x, x ∈ Φ.source →
    ‖fderiv ℝ (chartCoefficient Φ j k) x (coordinateVector l)‖ ≤ B)
  (J : ℝ) (hJ : ∀ y ∈ Φ.target, |(fderiv ℝ Φ.symm y).det| ≤ J) (hJ1 : 1 ≤ J)
  (Λ : Opens (Domain d)) (hTarget : Bornology.IsBounded Φ.target) (hp : p ≠ ∞)

/-- The available first-order pullback with the chart's actual derivatives. -/
def chartOne : SpaceValue 𝕜 d (chartTarget Φ Λ) 1 p →L[𝕜]
    SpaceValue 𝕜 d (chartPreimage Φ Λ) 1 p :=
  chartSobolevPull Φ (hΦ.of_le (by norm_num)) hInv B hB hB0 J hJ hJ1 Λ hTarget

def chartTwoValue : SpaceValue 𝕜 d (chartTarget Φ Λ) 2 p →L[𝕜]
    SpaceValue 𝕜 d (chartPreimage Φ Λ) 1 p :=
  (chartOne Φ hΦ hInv B hB0 hB J hJ hJ1 Λ hTarget).comp
    (orderOnePartCLM 𝕜 d (chartTarget Φ Λ) p)

/-- Multipliers by the chart's C¹ Jacobian entries. The second classical
coordinate derivatives provide their bounds. -/
def chartEntryMultiply (j k : Fin d) :
    SpaceValue 𝕜 d (chartPreimage Φ Λ) 1 p →L[𝕜]
      SpaceValue 𝕜 d (chartPreimage Φ Λ) 1 p :=
  localC1Multiply (chartCoefficient Φ j k) ((chartCoefficient_c1 Φ hΦ j k).mono inter_subset_left)
    B (fun x hx => by
      exact (norm_le_pi_norm (fderiv ℝ Φ x (coordinateVector j)) k).trans
        ((ContinuousLinearMap.le_opNorm _ _).trans (by
          simpa only [coordinateVector, Pi.norm_single, norm_one, mul_one] using hB x hx.1)))
    (fun l x hx => hDD j k l x hx.1) hp

def chartTwoDerivative (j : Fin d) :
    SpaceValue 𝕜 d (chartTarget Φ Λ) 2 p →L[𝕜]
      SpaceValue 𝕜 d (chartPreimage Φ Λ) 1 p :=
  ∑ k, (chartEntryMultiply Φ hΦ B hB hDD Λ hp j k).comp
    ((chartOne Φ hΦ hInv B hB0 hB J hJ hJ1 Λ hTarget).comp
      (derivativePartCLM 𝕜 d (chartTarget Φ Λ) p k))

lemma chartTwoDerivative_zero (u : SpaceValue 𝕜 d (chartTarget Φ Λ) 2 p) (j : Fin d) :
    (chartTwoDerivative Φ hΦ hInv B hB0 hB hDD J hJ hJ1 Λ hTarget hp j u).val (zeroIndex d 1) =
      (chartTwoValue Φ hΦ hInv B hB0 hB J hJ hJ1 Λ hTarget u).val (coordinateIndex j) := by
  classical
  let P := chartOne (𝕜 := 𝕜) (p := p) Φ hΦ hInv B hB0 hB J hJ hJ1 Λ hTarget
  let M := chartEntryMultiply (𝕜 := 𝕜) (p := p) Φ hΦ B hB hDD Λ hp j
  have hs : (chartTwoDerivative Φ hΦ hInv B hB0 hB hDD J hJ hJ1 Λ hTarget hp j u).val
      (zeroIndex d 1) = ∑ k, (M k (P (derivativePart k u))).val (zeroIndex d 1) := by
    simp only [chartTwoDerivative, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
    exact map_sum (evalOne (zeroIndex d 1)) _ _
  rw [hs]
  apply Lp.ext
  have hc (k : Fin d) : (M k (P (derivativePart k u))).val (zeroIndex d 1) =ᵐ[
      volume.restrict (chartPreimage Φ Λ : Set (Domain d))]
      fun x => chartCoefficient Φ j k x • (orderOnePart u).val (coordinateIndex k) (Φ x) := by
    apply (localC1Multiply_coe _ _ _ _ _ hp (P (derivativePart k u))).trans
    have hPull := chartSobolevPull_coe Φ (hΦ.of_le (by norm_num)) hInv B hB hB0 J hJ hJ1 Λ hTarget
      (derivativePart k u) ((derivativePart k u).val (zeroIndex d 1)) Filter.EventuallyEq.rfl
    have hi : derivativePartIndex k (zeroIndex d 1) = orderOneToTwo (coordinateIndex k) := by
      rw [derivativePartIndex_zero]
      apply Subtype.ext
      funext l
      apply Fin.ext
      simp [normalIndex, orderOneToTwo, coordinateIndex, boundedIndex, natIndex, Pi.single_apply, apply_ite]
    filter_upwards [hPull] with x hx
    change (P (derivativePart k u)).val (zeroIndex d 1) x =
      (derivativePart k u).val (zeroIndex d 1) (Φ x) at hx
    rw [hx]
    change chartCoefficient Φ j k x • u.val (derivativePartIndex k (zeroIndex d 1)) (Φ x) =
      chartCoefficient Φ j k x • u.val (orderOneToTwo (coordinateIndex k)) (Φ x)
    rw [hi]
  have hR := chartSobolevPull_coordinate_coe Φ (hΦ.of_le (by norm_num)) hInv B hB hB0 J hJ hJ1 Λ hTarget
    (orderOnePart u) j
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun k => (M k (P (derivativePart k u))).val (zeroIndex d 1)), ae_all_iff.mpr hc, hR]
    with x hsum hcx hr
  rw [hsum]
  exact (Finset.sum_congr rfl (fun k _ => hcx k)).trans hr.symm

/-- Iterating the proved first weak chain rule gives a bounded pullback
on the complete order-two graph; these are real/complex scalar-linear maps. -/
def boundedChartPullTwo : SpaceValue 𝕜 d (chartTarget Φ Λ) 2 p →L[𝕜]
    SpaceValue 𝕜 d (chartPreimage Φ Λ) 2 p :=
  assembleTwo (chartTwoValue Φ hΦ hInv B hB0 hB J hJ hJ1 Λ hTarget)
    (chartTwoDerivative Φ hΦ hInv B hB0 hB hDD J hJ hJ1 Λ hTarget hp)
    (chartTwoDerivative_zero Φ hΦ hInv B hB0 hB hDD J hJ hJ1 Λ hTarget hp)

lemma boundedChartPullTwo_coe (u : SpaceValue 𝕜 d (chartTarget Φ Λ) 2 p)
    (f : Domain d → 𝕜)
    (hf : f =ᵐ[volume.restrict (chartTarget Φ Λ : Set (Domain d))] u.val (zeroIndex d 2)) :
    (boundedChartPullTwo Φ hΦ hInv B hB0 hB hDD J hJ hJ1 Λ hTarget hp u).val (zeroIndex d 2) =ᵐ[
      volume.restrict (chartPreimage Φ Λ : Set (Domain d))] f ∘ Φ := by
  rw [boundedChartPullTwo, assembleTwo_zero]
  exact chartSobolevPull_coe Φ (hΦ.of_le (by norm_num)) hInv B hB hB0 J hJ hJ1 Λ hTarget
    (orderOnePart u) f hf
end BoundedChart


/-- Every compact set inside a C² chart fits in a subchart on which the
first and second coordinate coefficients and inverse Jacobian determinant
have finite bounds. No connectedness or nonempty-set hypothesis is used. -/
lemma exists_bounded_c2_subchart
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (K : Set (Domain d)) (hK : IsCompact K) (hKs : K ⊆ Φ.source) :
    ∃ (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (B J : ℝ),
      (Ψ : Domain d → Domain d) = Φ ∧
      (Ψ.symm : Domain d → Domain d) = Φ.symm ∧
      K ⊆ Ψ.source ∧ Ψ.source ⊆ Φ.source ∧
      ContDiffOn ℝ 2 Ψ Ψ.source ∧ ContDiffOn ℝ 2 Ψ.symm Ψ.target ∧
      0 ≤ B ∧ (∀ x ∈ Ψ.source, ‖fderiv ℝ Ψ x‖ ≤ B) ∧
      (∀ j k l x, x ∈ Ψ.source →
        ‖fderiv ℝ (chartCoefficient Ψ j k) x (coordinateVector l)‖ ≤ B) ∧
      1 ≤ J ∧ (∀ y ∈ Ψ.target, |(fderiv ℝ Ψ.symm y).det| ≤ J) ∧
      Bornology.IsBounded Ψ.target := by
  classical
  obtain ⟨U, hUo, hKU, hUs, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK Φ.open_source hKs
  let Ψ := Φ.restrOpen U hUo
  have hsrc : Ψ.source ⊆ Φ.source := inter_subset_left
  have htgt : Ψ.target ⊆ Φ.target := inter_subset_left
  have himg : IsCompact (Φ '' closure U) :=
    hUc.image_of_continuousOn (hΦ.continuousOn.mono hUs)
  have himgtgt : Φ '' closure U ⊆ Φ.target := by
    rintro y ⟨x, hx, rfl⟩
    exact Φ.map_source (hUs hx)
  have htimg : Ψ.target ⊆ Φ '' closure U := by
    intro y hy
    exact ⟨Ψ.symm y, subset_closure (Ψ.map_target hy).2, Ψ.right_inv hy⟩
  obtain ⟨A, hA⟩ := hUc.exists_bound_of_continuousOn
    ((hΦ.continuousOn_fderiv_of_isOpen Φ.open_source (by norm_num)).mono hUs)
  have hd (q : Fin d × Fin d × Fin d) : ∃ D : ℝ, ∀ x ∈ closure U,
      ‖fderiv ℝ (chartCoefficient Φ q.1 q.2.1) x (coordinateVector q.2.2)‖ ≤ D :=
    hUc.exists_bound_of_continuousOn
      ((Classical.c1_partial_continuousOn (Ω := ⟨Φ.source, Φ.open_source⟩)
        _ (chartCoefficient_c1 Φ hΦ q.1 q.2.1) q.2.2).mono hUs)
  choose D hD using hd
  let B := max 0 A + ∑ q : Fin d × Fin d × Fin d, max 0 (D q)
  have hsum : 0 ≤ ∑ q : Fin d × Fin d × Fin d, max 0 (D q) := by positivity
  have hdet : ContinuousOn (fun y => (fderiv ℝ Φ.symm y).det) Φ.target :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hInv.continuousOn_fderiv_of_isOpen Φ.open_target (by norm_num))
  obtain ⟨J, hJ⟩ := himg.exists_bound_of_continuousOn (hdet.mono himgtgt)
  refine ⟨Ψ, B, max 1 J, rfl, rfl, (fun x hx => ⟨hKs hx, hKU hx⟩), hsrc,
    hΦ.mono hsrc, hInv.mono htgt, add_nonneg (le_max_left _ _) hsum, ?_, ?_,
    le_max_left _ _, ?_, himg.isBounded.subset htimg⟩
  · intro x hx
    exact (hA x (subset_closure hx.2)).trans
      ((le_max_right 0 A).trans (le_add_of_nonneg_right hsum))
  · intro j k l x hx
    have hsingle : max 0 (D (j,k,l)) ≤ ∑ q : Fin d × Fin d × Fin d, max 0 (D q) :=
      Finset.single_le_sum (fun q _ => le_max_left _ _) (Finset.mem_univ _)
    exact (hD (j,k,l) x (subset_closure hx.2)).trans
      ((le_max_right _ _).trans (hsingle.trans (le_add_of_nonneg_left (le_max_left _ _))))
  · intro y hy
    exact (hJ y (htimg hy)).trans (le_max_right _ _)


/-- Localized C² transport for the unchanged distributional W2p graph.
The compact cutoff determines a bounded subchart. After transport there,
multiplication and relative zero extension recover the patch on the entire
original chart preimage. -/
theorem localized_transport : Spec.LocalizedTransport := by
  intro 𝕜 _ d Λ p _ hp1 hp Φ hΦ hInv θ hθ hc hs
  obtain ⟨Ψ, B, J, hfun, hinv, hθΨ, hΨΦ, hΨ, hΨinv, hB0, hB, hDD, hJ1, hJ, hTarget⟩ :=
    exists_bounded_c2_subchart Φ hΦ hInv (tsupport θ) hc hs
  let S := chartPreimage Ψ Λ
  let A := chartPreimage Φ Λ
  let K : Set (Domain d) := (A : Set (Domain d)) ∩ tsupport θ
  have hSA : S ≤ A := by
    intro x hx
    exact ⟨hΨΦ hx.1, by simpa only [← hfun] using hx.2⟩
  have hKc : IsClosed (K ∪ (A : Set (Domain d))ᶜ) := by
    convert (isClosed_tsupport θ).union A.isOpen.isClosed_compl using 1
    ext x
    simp only [K, mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  have hKS : K ⊆ S := by
    intro x hx
    exact ⟨hθΨ hx.2, by simpa only [hfun] using hx.1.2⟩
  have hcoeff : (S : Set (Domain d)) ∩ tsupport θ ⊆ K :=
    fun x hx => ⟨hSA hx.1, hx.2⟩
  obtain ⟨E, hE⟩ := localized_zero_extension 𝕜 d S A hSA K hKc hKS θ hθ hc hcoeff p
  let R : SpaceValue 𝕜 d Λ 2 p →L[𝕜] SpaceValue 𝕜 d (chartTarget Ψ Λ) 2 p :=
    restrictSobolev (show chartTarget Ψ Λ ≤ Λ from inter_subset_left)
  let P : SpaceValue 𝕜 d (chartTarget Ψ Λ) 2 p →L[𝕜] SpaceValue 𝕜 d S 2 p :=
    boundedChartPullTwo Ψ hΨ (hΨinv.of_le (by norm_num)) B hB0 hB hDD J hJ hJ1 Λ hTarget hp
  refine ⟨E.comp (P.comp R), fun u f hf => ?_⟩
  have hfR : f =ᵐ[volume.restrict (chartTarget Ψ Λ : Set (Domain d))]
      (R u).val (zeroIndex d 2) :=
    (hf.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))).trans
      (restrictSobolev_coe inter_subset_left u (zeroIndex d 2)).symm
  have hP : (P (R u)).val (zeroIndex d 2) =ᵐ[volume.restrict (S : Set (Domain d))] f ∘ Ψ :=
    boundedChartPullTwo_coe Ψ hΨ (hΨinv.of_le (by norm_num)) B hB0 hB hDD J hJ hJ1 Λ hTarget hp
      (R u) f hfR
  apply (hE (P (R u)) (f ∘ Ψ) hP.symm).trans
  filter_upwards [ae_restrict_mem A.isOpen.measurableSet] with x hx
  change (S : Set (Domain d)).indicator (fun x => θ x * f (Ψ x)) x = θ x * f (Φ x)
  by_cases hxS : x ∈ S
  · simp only [Set.indicator_of_mem hxS, hfun]
  · have hz : θ x = 0 := by
      by_contra hn
      exact hxS (hKS ⟨hx, subset_tsupport θ hn⟩)
    simp only [Set.indicator_of_notMem hxS, hz, zero_mul]

end ExpandedFA.PartIV.SecondTraceTransport
