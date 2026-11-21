import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BanachStone
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.UniversalContinuousEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.MeasureBallExtremes
import Mathlib.Topology.Separation.CompletelyRegular

noncomputable section
namespace ExpandedFA.Supplements.BanachStone

universe u v
open Set MeasureTheory

variable {𝕜 : Type} [RCLike 𝕜]
variable {K : Type u} {L : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

/-- The operator defined by a continuous unimodular weighted composition. -/
def weightedComposition (φ : L ≃ₜ K) (h : C(L, 𝕜))
    (hh : ∀ t, ‖h t‖ = 1) : C(K, 𝕜) ≃ₗᵢ[𝕜] C(L, 𝕜) where
  toFun f := h * f.comp (⟨φ, φ.continuous⟩ : C(L, K))
  invFun g := ⟨fun s => (h (φ.symm s))⁻¹ * g (φ.symm s),
    ((h.continuous.comp φ.symm.continuous).inv₀ (fun s => by
      have := hh (φ.symm s)
      exact norm_ne_zero_iff.mp (by change ‖h (φ.symm s)‖ ≠ 0; rw [this]; exact one_ne_zero))).mul
        (g.continuous.comp φ.symm.continuous)⟩
  left_inv f := by
    ext s
    simp only [ContinuousMap.coe_mk, ContinuousMap.mul_apply, ContinuousMap.comp_apply, Homeomorph.apply_symm_apply]
    have hn : h (φ.symm s) ≠ 0 := norm_ne_zero_iff.mp (by rw [hh]; exact one_ne_zero)
    exact inv_mul_cancel_left₀ hn _
  right_inv g := by
    ext t
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, Homeomorph.symm_apply_apply,
      ContinuousMap.coe_mk]
    have hn : h t ≠ 0 := norm_ne_zero_iff.mp (by rw [hh]; exact one_ne_zero)
    exact mul_inv_cancel_left₀ hn _
  map_add' f g := by ext t; simp [mul_add]
  map_smul' a f := by ext t; simp
  norm_map' f := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro t
      simpa [norm_mul, hh] using f.norm_coe_le_norm (φ t)
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro s
      have hb := (h * f.comp (⟨φ, φ.continuous⟩ : C(L, K))).norm_coe_le_norm (φ.symm s)
      simpa [norm_mul, hh] using hb

@[simp] theorem weightedComposition_apply (φ : L ≃ₜ K) (h : C(L, 𝕜))
    (hh : ∀ t, ‖h t‖ = 1) (f : C(K, 𝕜)) (t : L) :
    weightedComposition φ h hh f t = h t * f (φ t) := rfl

theorem converse : Spec.Converse.{u,v} := by
  intro 𝕜 _ K L _ _ _ _ _ _ φ h hh
  exact ⟨weightedComposition φ h hh, fun _ _ => rfl⟩

theorem real_signs : Spec.RealSigns.{v} := by
  intro L _ h hh t
  exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (hh t)

theorem universal_embedding : Spec.UniversalEmbedding.{u} :=
  UniversalContinuousEmbedding.universal_evaluation_embedding

/-- Continuous scalar functions separate points, over either scalar field. -/
lemma eq_of_continuousMap_values {x y : K}
    (h : ∀ f : C(K, 𝕜), f x = f y) : x = y := by
  by_contra hn
  obtain ⟨f, hf, hne⟩ := separatesPoints_continuous_of_t35Space hn
  let g : C(K, 𝕜) := ⟨fun s => (f s : 𝕜), RCLike.continuous_ofReal.comp hf⟩
  exact hne (RCLike.ofReal_injective (h g))

/-- On a compact Hausdorff space, scalar continuous tests determine continuity. -/
lemma continuous_of_continuousMap_comp (φ : L → K)
    (hφ : ∀ f : C(K, 𝕜), Continuous (fun t => f (φ t))) : Continuous φ := by
  let j : K → (C(K, 𝕜) → 𝕜) := fun s f => f s
  have hj : Continuous j := continuous_pi (fun f => f.continuous)
  have hemb : Topology.IsEmbedding j :=
    (hj.isClosedEmbedding (fun x y h => eq_of_continuousMap_values
      (fun f => congrFun h f))).isEmbedding
  exact hemb.continuous_iff.mpr (continuous_pi hφ)

/-- Pointwise weighted evaluations for an isometry and its inverse give the
homeomorphism. This argument also works for empty compact spaces. -/
lemma classification_of_pointwise
    (U : C(K, 𝕜) ≃ₗᵢ[𝕜] C(L, 𝕜))
    (hU : ∀ t : L, ∃ s : K, ∃ c : 𝕜, ‖c‖ = 1 ∧
      ∀ f : C(K, 𝕜), U f t = c * f s)
    (hV : ∀ s : K, ∃ t : L, ∃ c : 𝕜, ‖c‖ = 1 ∧
      ∀ g : C(L, 𝕜), U.symm g s = c * g t) :
    ∃ (φ : L ≃ₜ K) (h : C(L, 𝕜)),
      (∀ t, ‖h t‖ = 1) ∧ ∀ f t, U f t = h t * f (φ t) := by
  classical
  choose φ c hc hform using hU
  choose ψ d hd hinv using hV
  have hcU (t : L) : c t = U 1 t := by simpa using (hform t 1).symm
  have hdV (s : K) : d s = U.symm 1 s := by simpa using (hinv s 1).symm
  have hleft (t : L) : ψ (φ t) = t := by
    apply eq_of_continuousMap_values (𝕜 := 𝕜)
    intro g
    have hcd : c t * d (φ t) = 1 := by
      have := hform t (U.symm 1)
      rw [U.apply_symm_apply] at this
      simpa [← hdV] using this.symm
    have heq := hform t (U.symm g)
    rw [U.apply_symm_apply, hinv] at heq
    simpa [← mul_assoc, hcd] using heq.symm
  have hright (s : K) : φ (ψ s) = s := by
    apply eq_of_continuousMap_values (𝕜 := 𝕜)
    intro f
    have hdc : d s * c (ψ s) = 1 := by
      have := hinv s (U 1)
      rw [U.symm_apply_apply] at this
      simpa [← hcU] using this.symm
    have heq := hinv s (U f)
    rw [U.symm_apply_apply, hform] at heq
    simpa [← mul_assoc, hdc] using heq.symm
  have hcont : Continuous φ := by
    apply continuous_of_continuousMap_comp (𝕜 := 𝕜)
    intro f
    have hne (t : L) : U 1 t ≠ 0 := by
      rw [← hcU]
      exact norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero)
    have heq : (fun t => f (φ t)) = (fun t => U f t / U 1 t) := by
      funext t
      rw [hform, ← hcU]
      have hn : c t ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero)
      exact (mul_div_cancel_left₀ (f (φ t)) hn).symm
    rw [heq]
    exact (U f).continuous.div (U 1).continuous hne
  let e : L ≃ K := ⟨φ, ψ, hleft, hright⟩
  let homeo : L ≃ₜ K := e.toHomeomorphOfContinuousClosed hcont hcont.isClosedMap
  refine ⟨homeo, U 1, ?_, ?_⟩
  · intro t
    rw [← hcU]
    exact hc t
  · intro f t
    exact (hform t f).trans (by rw [hcU]; rfl)

open FunctionSpaces.ScalarRieszMarkovSpec
open FunctionSpaces.ScalarRieszMarkov
open scoped ZeroAtInfty

/-- The accepted compact C/C₀ identification, preserving each function value. -/
def compactEquiv : C(K, 𝕜) ≃ₗᵢ[𝕜] C₀(K, 𝕜) :=
  (compact_identification K 𝕜).choose

@[simp] lemma compactEquiv_apply (f : C(K, 𝕜)) (s : K) :
    compactEquiv f s = f s := (compact_identification K 𝕜).choose_spec.1 f s

@[simp] lemma compactEquiv_symm_apply (f : C₀(K, 𝕜)) (s : K) :
    compactEquiv.symm f s = f s := (compact_identification K 𝕜).choose_spec.2 f s

section Measures
variable [MeasurableSpace K] [BorelSpace K]

/-- Integration on C(K), using the accepted scalar Riesz--Markov operator. -/
def measureFunctional (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν) :
    C(K, 𝕜) →L[𝕜] 𝕜 := by
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  exact (scalarMeasureFunctional ν).comp
    (compactEquiv (K := K) (𝕜 := 𝕜)).toContinuousLinearEquiv.toContinuousLinearMap

lemma measureFunctional_apply (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν)
    (f : C(K, 𝕜)) : measureFunctional ν hν f = scalarIntegral ν f := by
  change scalarIntegral ν (compactEquiv f) = _
  congr 1
  funext s
  exact compactEquiv_apply f s

lemma norm_measureFunctional (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν) :
    ‖measureFunctional ν hν‖ = ν.variation.real univ := by
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  letI : ν.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  change ‖(scalarMeasureFunctional ν).comp
    (compactEquiv (K := K) (𝕜 := 𝕜)).toContinuousLinearEquiv.toContinuousLinearMap‖ = _
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, scalarMeasureFunctional_norm_eq]

lemma measureFunctional_injective (ν η : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η)
    (heq : measureFunctional ν hν = measureFunctional η hη) : ν = η := by
  apply scalarIntegral_injective ν η hν hη
  intro f
  have hh := congrArg (fun l : C(K, 𝕜) →L[𝕜] 𝕜 => l (compactEquiv.symm f)) heq
  simp only [measureFunctional_apply] at hh
  have hfun : (⇑(compactEquiv.symm f) : K → 𝕜) = f := by
    funext s
    exact compactEquiv_symm_apply f s
  simpa only [hfun] using hh

lemma finiteRadon_add (ν η : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η) : FiniteScalarRadon (ν + η) := by
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  letI : IsFiniteMeasure η.variation := ⟨hη.1⟩
  letI : ν.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  letI : η.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hη.2
  letI : (ν.variation + η.variation).Regular := regular_add _ _
  have hle := VectorMeasure.variation_add_le (μ := ν) (ν := η)
  exact ⟨(hle univ).trans_lt (measure_lt_top _ _),
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
      (regular_of_le hle)⟩

lemma measureFunctional_combination (ν η : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η) (r : ℝ)
    (hcomb : FiniteScalarRadon (r • ν + (1-r) • η)) :
    measureFunctional (r • ν + (1-r) • η) hcomb =
      r • measureFunctional ν hν + (1-r) • measureFunctional η hη := by
  letI : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  letI : IsFiniteMeasure η.variation := ⟨hη.1⟩
  ext f
  simp only [add_apply, smul_apply,
    measureFunctional_apply, scalarIntegral]
  rw [VectorMeasure.integral_add_vectorMeasure
    (VectorMeasure.Integrable.smul_vectorMeasure
      (show Integrable (f : K → 𝕜) ν.variation from by
        have heq : (⇑(compactEquiv f) : K → 𝕜) = f := by ext s; simp
        simpa only [heq] using (scalarIntegral_bound ν (compactEquiv f)).1) r)
    (VectorMeasure.Integrable.smul_vectorMeasure
      (show Integrable (f : K → 𝕜) η.variation from by
        have heq : (⇑(compactEquiv f) : K → 𝕜) = f := by ext s; simp
        simpa only [heq] using (scalarIntegral_bound η (compactEquiv f)).1) (1-r))]
  simp only [VectorMeasure.integral_smul_vectorMeasure]

/-- The scalar Riesz--Markov representation transported to C(K). -/
lemma exists_measureFunctional
    (hrep : FunctionSpaces.ScalarRieszMarkovSpec.ScalarRepresentation.{u} 𝕜)
    (l : C(K, 𝕜) →L[𝕜] 𝕜) :
    ∃ ν : VectorMeasure K 𝕜, ∃ hν : FiniteScalarRadon ν,
      measureFunctional ν hν = l := by
  let e := compactEquiv (K := K) (𝕜 := 𝕜)
  obtain ⟨ν, hν, hf, _, _⟩ := hrep K
    (l.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨ν, hν, ?_⟩
  ext f
  rw [measureFunctional_apply]
  have hh := (hf (e f)).2
  change l (e.symm (e f)) = _ at hh
  rw [e.symm_apply_apply] at hh
  rw [hh]
  congr 1
  funext s
  exact (compactEquiv_apply f s).symm

end Measures

/-- The dual unit ball, with real convex combinations also for complex scalars. -/
def dualBall : Set (C(K, 𝕜) →L[𝕜] 𝕜) := {l | ‖l‖ ≤ 1}

section MeasuresExtreme
variable [MeasurableSpace K] [BorelSpace K]

lemma finiteRadon_combination (ν η : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hη : FiniteScalarRadon η) (r : ℝ) :
    FiniteScalarRadon (r • ν + (1-r) • η) :=
  finiteRadon_add _ _ (MeasureBallExtremes.finiteRadon_smul ν hν r)
    (MeasureBallExtremes.finiteRadon_smul η hη (1-r))

/-- Riesz--Markov is an affine isometric bijection on the two closed unit balls. -/
lemma extreme_measureFunctional_iff
    (hrep : FunctionSpaces.ScalarRieszMarkovSpec.ScalarRepresentation.{u} 𝕜)
    (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν) :
    measureFunctional ν hν ∈ P1.C24FacesSpec.extremePoints (dualBall (K := K)) ↔
      ν ∈ P1.C24FacesSpec.extremePoints (MeasureBallExtremesSpec.UnitBall K 𝕜) := by
  constructor
  · rintro ⟨hnorm, hext⟩
    refine ⟨⟨hν, ?_⟩, ?_⟩
    · simpa only [dualBall, mem_setOf_eq, norm_measureFunctional] using hnorm
    · intro η hη ξ hξ r hr0 hr1 heq
      have hcomb := finiteRadon_combination η ξ hη.1 hξ.1 r
      have hfunc : measureFunctional ν hν =
          r • measureFunctional η hη.1 + (1-r) • measureFunctional ξ hξ.1 := by
        rw [← measureFunctional_combination η ξ hη.1 hξ.1 r hcomb]
        congr 1
      have hηnorm : measureFunctional η hη.1 ∈ dualBall := by
        simpa only [dualBall, mem_setOf_eq, norm_measureFunctional] using hη.2
      have hξnorm : measureFunctional ξ hξ.1 ∈ dualBall := by
        simpa only [dualBall, mem_setOf_eq, norm_measureFunctional] using hξ.2
      obtain ⟨hηeq, hξeq⟩ := hext _ hηnorm _ hξnorm r hr0 hr1 hfunc
      exact ⟨measureFunctional_injective _ _ _ _ hηeq,
        measureFunctional_injective _ _ _ _ hξeq⟩
  · rintro ⟨hball, hext⟩
    refine ⟨?_, ?_⟩
    · simpa only [dualBall, mem_setOf_eq, norm_measureFunctional] using hball.2
    · intro l hl m hm r hr0 hr1 heq
      obtain ⟨η, hη, hηeq⟩ := exists_measureFunctional hrep l
      obtain ⟨ξ, hξ, hξeq⟩ := exists_measureFunctional hrep m
      have hηball : η ∈ MeasureBallExtremesSpec.UnitBall K 𝕜 := by
        refine ⟨hη, ?_⟩
        rw [← norm_measureFunctional η hη, hηeq]
        exact hl
      have hξball : ξ ∈ MeasureBallExtremesSpec.UnitBall K 𝕜 := by
        refine ⟨hξ, ?_⟩
        rw [← norm_measureFunctional ξ hξ, hξeq]
        exact hm
      have hcomb := finiteRadon_combination η ξ hη hξ r
      have heq' : ν = r • η + (1-r) • ξ := by
        apply measureFunctional_injective ν _ hν hcomb
        rw [measureFunctional_combination η ξ hη hξ r hcomb, hηeq, hξeq]
        exact heq
      obtain ⟨hηeq', hξeq'⟩ := hext η hηball ξ hξball r hr0 hr1 heq'
      subst η
      subst ξ
      exact ⟨hηeq.symm, hξeq.symm⟩

lemma measureFunctional_dirac (s : K) (c : 𝕜) :
    measureFunctional (VectorMeasure.dirac s c) (MeasureBallExtremes.finiteRadon_dirac s c) =
      c • (ContinuousMap.evalCLM 𝕜 s : C(K, 𝕜) →L[𝕜] 𝕜) := by
  ext f
  rw [measureFunctional_apply]
  simp [scalarIntegral, mul_comm]

/-- Every extreme dual functional is a unimodular scalar multiple of an evaluation. -/
lemma dual_extreme_classification [Nonempty K]
    (hrep : FunctionSpaces.ScalarRieszMarkovSpec.ScalarRepresentation.{u} 𝕜)
    (l : C(K, 𝕜) →L[𝕜] 𝕜) :
    l ∈ P1.C24FacesSpec.extremePoints (dualBall (K := K)) ↔
      ∃ s : K, ∃ c : 𝕜, ‖c‖ = 1 ∧ l = c • ContinuousMap.evalCLM 𝕜 s := by
  obtain ⟨ν, hν, rfl⟩ := exists_measureFunctional hrep l
  rw [extreme_measureFunctional_iff hrep, MeasureBallExtremes.classification K 𝕜 ν]
  constructor
  · rintro ⟨s, c, hc, rfl⟩
    exact ⟨s, c, hc, measureFunctional_dirac s c⟩
  · rintro ⟨s, c, hc, heq⟩
    refine ⟨s, c, hc, ?_⟩
    apply measureFunctional_injective ν (VectorMeasure.dirac s c) hν
      (MeasureBallExtremes.finiteRadon_dirac s c)
    rw [measureFunctional_dirac]
    exact heq

end MeasuresExtreme

/-- Precomposition with an onto linear isometry is an isometric linear
bijection on the scalar-linear duals; its linearity includes real combinations. -/
def dualIsometry (U : C(K, 𝕜) ≃ₗᵢ[𝕜] C(L, 𝕜)) :
    (C(L, 𝕜) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] (C(K, 𝕜) →L[𝕜] 𝕜) where
  toFun l := l.comp U.toContinuousLinearEquiv.toContinuousLinearMap
  invFun l := l.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  left_inv l := by ext f; simp
  right_inv l := by ext f; simp
  map_add' l m := by ext f; rfl
  map_smul' c l := by ext f; rfl
  norm_map' l := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv l U

/-- The dual isometry takes real extreme points of the closed ball to extremes. -/
lemma dualIsometry_extreme (U : C(K, 𝕜) ≃ₗᵢ[𝕜] C(L, 𝕜))
    (l : C(L, 𝕜) →L[𝕜] 𝕜)
    (hl : l ∈ P1.C24FacesSpec.extremePoints (dualBall (K := L))) :
    dualIsometry U l ∈ P1.C24FacesSpec.extremePoints (dualBall (K := K)) := by
  let e := dualIsometry U
  refine ⟨?_, ?_⟩
  · change ‖e l‖ ≤ 1
    rw [e.norm_map]
    exact hl.1
  · intro a ha b hb r hr0 hr1 heq
    have ha' : e.symm a ∈ dualBall := by
      change ‖e.symm a‖ ≤ 1
      rw [e.symm.norm_map]
      exact ha
    have hb' : e.symm b ∈ dualBall := by
      change ‖e.symm b‖ ≤ 1
      rw [e.symm.norm_map]
      exact hb
    have heq' : l = r • e.symm a + (1-r) • e.symm b := by
      apply e.injective
      have hreal (a : C(L, 𝕜) →L[𝕜] 𝕜) (c : ℝ) : e (c • a) = c • e a := by
        ext f
        rfl
      rw [map_add, hreal, hreal, e.apply_symm_apply, e.apply_symm_apply]
      exact heq
    obtain ⟨haeq, hbeq⟩ := hl.2 _ ha' _ hb' r hr0 hr1 heq'
    exact ⟨by simpa using congrArg e haeq, by simpa using congrArg e hbeq⟩

/-- Point evaluations after an onto isometry are weighted point evaluations. -/
lemma pointwise_weighted_evaluation [Nonempty K] [Nonempty L]
    (hrepK : FunctionSpaces.ScalarRieszMarkovSpec.ScalarRepresentation.{u} 𝕜)
    (hrepL : FunctionSpaces.ScalarRieszMarkovSpec.ScalarRepresentation.{v} 𝕜)
    (U : C(K, 𝕜) ≃ₗᵢ[𝕜] C(L, 𝕜)) (t : L) :
    ∃ s : K, ∃ c : 𝕜, ‖c‖ = 1 ∧ ∀ f : C(K, 𝕜), U f t = c * f s := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  letI : MeasurableSpace L := borel L
  letI : BorelSpace L := ⟨rfl⟩
  have hext : (ContinuousMap.evalCLM 𝕜 t : C(L, 𝕜) →L[𝕜] 𝕜) ∈
      P1.C24FacesSpec.extremePoints dualBall := by
    apply (dual_extreme_classification hrepL _).mpr
    exact ⟨t, 1, by simp, by simp⟩
  obtain ⟨s, c, hc, heq⟩ := (dual_extreme_classification hrepK _).mp
    (dualIsometry_extreme U _ hext)
  refine ⟨s, c, hc, ?_⟩
  intro f
  exact congrArg (fun l : C(K, 𝕜) →L[𝕜] 𝕜 => l f) heq

/-- Full classification from the accepted real/complex scalar representation.
The separate universe arguments allow K and L to have different universe levels. -/
lemma classification_for_of_representation
    (hrepK : FunctionSpaces.ScalarRieszMarkovSpec.ScalarRepresentation.{u} 𝕜)
    (hrepL : FunctionSpaces.ScalarRieszMarkovSpec.ScalarRepresentation.{v} 𝕜) :
    Spec.ClassificationFor.{u,v} 𝕜 := by
  intro K L _ _ _ _ _ _ U hU
  let e := LinearIsometryEquiv.ofSurjective U hU
  classical
  cases isEmpty_or_nonempty K with
  | inl hK =>
    letI := hK
    have hL : IsEmpty L := by
      refine ⟨fun t => ?_⟩
      obtain ⟨f, hf⟩ := hU 1
      have hfzero : f = 0 := by ext s; exact isEmptyElim s
      have hone : (1 : C(L, 𝕜)) = 0 := by rw [← hf, hfzero, map_zero]
      have hfalse := congrArg (fun g : C(L, 𝕜) => g t) hone
      exact one_ne_zero hfalse
    letI := hL
    let φ : L ≃ₜ K :=
      { toFun := isEmptyElim
        invFun := isEmptyElim
        left_inv := fun t => isEmptyElim t
        right_inv := fun s => isEmptyElim s
        continuous_toFun := continuous_iff_continuousAt.mpr (fun t => isEmptyElim t)
        continuous_invFun := continuous_iff_continuousAt.mpr (fun t => isEmptyElim t) }
    exact ⟨φ, 1, fun t => isEmptyElim t, fun f t => isEmptyElim t⟩
  | inr hK =>
    letI := hK
    have hL : Nonempty L := by
      by_contra hnone
      haveI : IsEmpty L := not_nonempty_iff.mp hnone
      have hh : U 1 = U 0 := by ext t; exact isEmptyElim t
      obtain ⟨s⟩ := hK
      have hfalse := congrArg (fun f : C(K, 𝕜) => f s) (U.injective hh)
      exact one_ne_zero hfalse
    letI := hL
    obtain ⟨φ, h, hh, hform⟩ := classification_of_pointwise e
      (pointwise_weighted_evaluation hrepK hrepL e)
      (pointwise_weighted_evaluation hrepL hrepK e.symm)
    exact ⟨φ, h, hh, hform⟩

/-- Real Banach--Stone, for all compact Hausdorff K and L, including empty spaces. -/
theorem real_classification : Spec.RealClassification.{u,v} :=
  classification_for_of_representation
    FunctionSpaces.ScalarRieszMarkov.real_representation
    FunctionSpaces.ScalarRieszMarkov.real_representation

/-- Complex Banach--Stone for complex-linear, rather than conjugate-linear, maps. -/
theorem complex_classification : Spec.ComplexClassification.{u,v} :=
  classification_for_of_representation
    FunctionSpaces.ScalarRieszMarkov.complex_representation
    FunctionSpaces.ScalarRieszMarkov.complex_representation

end ExpandedFA.Supplements.BanachStone
