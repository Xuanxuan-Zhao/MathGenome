import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open Set TopologicalSpace MeasureTheory Metric
open scoped ENNReal ContDiff InnerProductSpace FourierTransform Pointwise
namespace P201
abbrev Space : P201Specs.SpaceType := @P201Specs.Space
abbrev Domain : P201Specs.DomainType := @P201Specs.Domain
abbrev spatialMeasure : P201Specs.spatialMeasureType := @P201Specs.spatialMeasure
abbrev domainMeasure : P201Specs.domainMeasureType := @P201Specs.domainMeasure
abbrev Test : P201Specs.TestType := @P201Specs.Test
abbrev Distribution : P201Specs.DistributionType := @P201Specs.Distribution
abbrev MultiIndex : P201Specs.MultiIndexType := @P201Specs.MultiIndex
abbrev coordinate : P201Specs.coordinateType := @P201Specs.coordinate
abbrev multiPartial : P201Specs.multiPartialType := @P201Specs.multiPartial
abbrev distributionDerivative : P201Specs.distributionDerivativeType := @P201Specs.distributionDerivative
abbrev regularDistribution : P201Specs.regularDistributionType := @P201Specs.regularDistribution
abbrev Lp : P201Specs.LpType := @P201Specs.Lp
abbrev W : P201Specs.WType := @P201Specs.W
abbrev H : P201Specs.HType := @P201Specs.H
abbrev H10 : P201Specs.H10Type := @P201Specs.H10
abbrev Hminus1 : P201Specs.Hminus1Type := @P201Specs.Hminus1
abbrev pivot : P201Specs.pivotType := @P201Specs.pivot
abbrev laplacian : P201Specs.laplacianType := @P201Specs.laplacian
abbrev distributionLaplacian : P201Specs.distributionLaplacianType := @P201Specs.distributionLaplacian
abbrev gradient : P201Specs.gradientType := @P201Specs.gradient
abbrev divergence : P201Specs.divergenceType := @P201Specs.divergence
abbrev positiveDivergence : P201Specs.positiveDivergenceType := @P201Specs.positiveDivergence
abbrev weakNegativeDivergence : P201Specs.weakNegativeDivergenceType := @P201Specs.weakNegativeDivergence
abbrev fourierPhase : P201Specs.fourierPhaseType := @P201Specs.fourierPhase
abbrev fourierIntegral : P201Specs.fourierIntegralType := @P201Specs.fourierIntegral
abbrev hFirstDerivative : P201Specs.hFirstDerivativeType := @P201Specs.hFirstDerivative
abbrev hGradient : P201Specs.hGradientType := @P201Specs.hGradient
abbrev ellipticEnergyForm : P201Specs.ellipticEnergyFormType := @P201Specs.ellipticEnergyForm
abbrev negativeDivergenceDistribution : P201Specs.negativeDivergenceDistributionType := @P201Specs.negativeDivergenceDistribution
abbrev graphFrame : P201Specs.graphFrameType := @P201Specs.graphFrame
abbrev IsBoundedLipschitzOpen : P201Specs.IsBoundedLipschitzOpenType := @P201Specs.IsBoundedLipschitzOpen
abbrev HasCkBoundary : P201Specs.HasCkBoundaryType := @P201Specs.HasCkBoundary
abbrev HasC11Boundary : P201Specs.HasC11BoundaryType := @P201Specs.HasC11Boundary
abbrev boundaryMeasure : P201Specs.boundaryMeasureType := @P201Specs.boundaryMeasure
abbrev unitSurface : P201Specs.unitSurfaceType := @P201Specs.unitSurface
abbrev omega : P201Specs.omegaType := @P201Specs.omega
abbrev sphereSurface : P201Specs.sphereSurfaceType := @P201Specs.sphereSurface
abbrev ballAverage : P201Specs.ballAverageType := @P201Specs.ballAverage
abbrev sphereAverage : P201Specs.sphereAverageType := @P201Specs.sphereAverage
abbrev IsClassicalEllipticSolution : P201Specs.IsClassicalEllipticSolutionType := @P201Specs.IsClassicalEllipticSolution
abbrev IsDistributionalEllipticSolution : P201Specs.IsDistributionalEllipticSolutionType := @P201Specs.IsDistributionalEllipticSolution
abbrev IsWeakDirichletSolution : P201Specs.IsWeakDirichletSolutionType := @P201Specs.IsWeakDirichletSolution
abbrev IsMildSolution : P201Specs.IsMildSolutionType := @P201Specs.IsMildSolution
abbrev HasEnergyTimeDerivative : P201Specs.HasEnergyTimeDerivativeType := @P201Specs.HasEnergyTimeDerivative
abbrev IsDirichletEnergySolution : P201Specs.IsDirichletEnergySolutionType := @P201Specs.IsDirichletEnergySolution

abbrev hToW : P201Specs.hToWExportType := @P201Specs.hToW

abbrev hUnderlying : P201Specs.hUnderlyingExportType := @P201Specs.hUnderlying

abbrev hZeroUnderlying : P201Specs.hZeroUnderlyingExportType := @P201Specs.hZeroUnderlying

theorem fullHilbertNorm : P201Specs.fullHilbertNormStatement := by
  unfold P201Specs.fullHilbertNormStatement
  intro n 𝕜 _ Ω k u
  exact PiLp.norm_sq_eq_of_L2 _ u.val

theorem hilbertDerivativeDistribution : P201Specs.hilbertDerivativeDistributionStatement := by
  unfold P201Specs.hilbertDerivativeDistributionStatement
  intro n 𝕜 _ Ω k u α
  exact P102.U4.sobolev_derivative_distribution Ω k 2 (P201Specs.hToW 𝕜 Ω k u) α

theorem hilbertUnderlyingInjective : P201Specs.hilbertUnderlyingInjectiveStatement := by
  unfold P201Specs.hilbertUnderlyingInjectiveStatement
  intro n 𝕜 _ Ω k u v h
  apply (P201Specs.hToW 𝕜 Ω k).injective
  apply P102.U4.sobolevUnderlying_injective Ω k 2
  exact h

theorem hZeroClosureBridge : P201Specs.hZeroClosureBridgeStatement := by
  unfold P201Specs.hZeroClosureBridgeStatement
  intro n 𝕜 _ Ω
  apply SetLike.coe_injective
  change closure ((P201Specs.hToW 𝕜 Ω 1) ⁻¹'
      (P102.U4.smoothSobolevSubmodule 𝕜 Ω 1 2 : Set _)) =
    (P201Specs.hToW 𝕜 Ω 1) ⁻¹' closure (P102.U4.smoothSobolevSubmodule 𝕜 Ω 1 2 : Set _)
  exact ((P201Specs.hToW 𝕜 Ω 1).toHomeomorph.preimage_closure _).symm

theorem pivotPairing : P201Specs.pivotPairingStatement := by
  unfold P201Specs.pivotPairingStatement
  intro n Ω f v
  change inner ℝ f (P201Specs.hZeroUnderlying Ω v) = _
  rw [L2.inner_def]
  congr 1
  funext x
  simp [RCLike.inner_apply, mul_comm]

theorem boundaryCountingMeasure : P201Specs.boundaryCountingMeasureStatement := by
  unfold P201Specs.boundaryCountingMeasureStatement
  exact P102.Trace.Ordinary.boundaryMeasure_one_dimension

theorem fourierNormalization : P201Specs.fourierNormalizationStatement := by
  unfold P201Specs.fourierNormalizationStatement
  intro n f ξ
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  change Complex.exp _ * f x = Complex.exp _ * f x
  congr 2
  push_cast
  ring

theorem unitSurfaceDimensionOne : P201Specs.unitSurfaceDimensionOneStatement := by
  unfold P201Specs.unitSurfaceDimensionOneStatement
  simp [P201Specs.unitSurface, P102.Trace.Ordinary.linePoint]

theorem endpointPositiveMass : P201Specs.endpointPositiveMassStatement := by
  unfold P201Specs.endpointPositiveMassStatement
  rw [unitSurfaceDimensionOne]
  have hne : P102.Trace.Ordinary.linePoint (1 : ℝ) ≠ P102.Trace.Ordinary.linePoint (-1) := by
    intro h
    have hc := congrArg (fun x : Space 1 => x 0) h
    norm_num [P102.Trace.Ordinary.linePoint] at hc
  simp [Pi.single_apply, hne, hne.symm]

theorem endpointNegativeMass : P201Specs.endpointNegativeMassStatement := by
  unfold P201Specs.endpointNegativeMassStatement
  rw [unitSurfaceDimensionOne]
  have hne : P102.Trace.Ordinary.linePoint (1 : ℝ) ≠ P102.Trace.Ordinary.linePoint (-1) := by
    intro h
    have hc := congrArg (fun x : Space 1 => x 0) h
    norm_num [P102.Trace.Ordinary.linePoint] at hc
  simp [Pi.single_apply, hne, hne.symm]

theorem oneDimensionalBallVolume : P201Specs.oneDimensionalBallVolumeStatement := by
  unfold P201Specs.oneDimensionalBallVolumeStatement
  have h := P102.Trace.Ordinary.lineIsometry.measurePreserving.measure_preimage
    (s := ball (0 : Space 1) 1) measurableSet_ball.nullMeasurableSet
  have he : P102.Trace.Ordinary.lineIsometry ⁻¹' ball (0 : Space 1) 1 = ball (0 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_ball, dist_zero_right]
    rw [P102.Trace.Ordinary.lineIsometry.norm_map]
  rw [he] at h
  simp only [Measure.real, ← h, Real.volume_ball, mul_one]
  norm_num

theorem unitSurfaceMass : P201Specs.unitSurfaceMassStatement := by
  unfold P201Specs.unitSurfaceMassStatement
  intro n
  by_cases hn : n = 1
  · subst n
    rw [unitSurfaceDimensionOne]
    simp only [Nat.cast_one, one_mul]
    rw [oneDimensionalBallVolume]
    norm_num [Measure.real]
  · simp only [P201Specs.unitSurface, ite_eq_right hn]
    change ((Measure.map (fun θ : sphere (0 : Space n) 1 => (θ : Space n)) (volume : Measure (Space n)).toSphere) univ).toReal = _
    rw [Measure.map_apply_of_aemeasurable (by fun_prop) MeasurableSet.univ]
    simp only [preimage_univ]
    change (volume : Measure (Space n)).toSphere.real univ = _
    rw [Measure.toSphere_real_apply_univ]
    simp [Space, P201Specs.Space]

theorem ballVolumeNormalization : P201Specs.ballVolumeNormalizationStatement := by
  unfold P201Specs.ballVolumeNormalizationStatement
  intro n hn a r hr
  have : NeZero n := ⟨by omega⟩
  have hv := Measure.addHaar_ball (volume : Measure (Space n)) a hr
  have hm : P201Specs.omega n = (n : ℝ) * (volume : Measure (Space n)).real (ball 0 1) := unitSurfaceMass n
  change (volume (ball a r)).toReal = _
  rw [hv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [hm]
  simp only [Measure.real]
  field_simp

theorem sphereSurfaceMass : P201Specs.sphereSurfaceMassStatement := by
  unfold P201Specs.sphereSurfaceMassStatement
  intro n a r hr
  simp only [P201Specs.sphereSurface, Measure.real, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) MeasurableSet.univ]
  change r ^ (n - 1) * P201Specs.omega n = P201Specs.omega n * r ^ (n - 1)
  ring

theorem unitSurfaceCone : P201Specs.unitSurfaceConeStatement := by
  unfold P201Specs.unitSurfaceConeStatement
  intro n hn s hs
  have he : MeasurableEmbedding (Subtype.val : sphere (0 : Space n) 1 → Space n) :=
    MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet
  simp only [P201Specs.unitSurface, ite_eq_right hn]
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) (he.measurableSet_image.mpr hs)]
  rw [Set.preimage_image_eq _ Subtype.val_injective]
  simpa [Space, P201Specs.Space] using (volume : Measure (Space n)).toSphere_apply' hs

end P201
