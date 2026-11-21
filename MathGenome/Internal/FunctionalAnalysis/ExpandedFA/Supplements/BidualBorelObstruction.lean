import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BidualBorelObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.BoundedBorelBidual
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

namespace ExpandedFA.Supplements.BidualBorelObstruction

open MeasureTheory Set
open scoped ENNReal unitInterval
open FunctionSpaces.ScalarRieszMarkovSpec
open FunctionSpaces.ScalarRieszMarkov
open FunctionSpaces.PositiveRadonRepresentation
open BoundedBorelBidualSpec BoundedBorelBidual BidualBorelObstructionSpec

universe u

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
variable {𝕜 : Type} [RCLike 𝕜]

/-- Finite partial sums of the absolute point masses are bounded by variation. -/
theorem sum_norm_atoms_le (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation]
    (s : Finset X) : (∑ x ∈ s, ‖ν {x}‖) ≤ ν.variation.real univ := by
  have hn (x : X) : ‖ν {x}‖ = ν.variation.real {x} := by
    simp [measureReal_def, VectorMeasure.variation_apply_singleton]
  simp_rw [hn]
  rw [sum_measureReal_singleton]
  exact measureReal_mono (subset_univ _)

/-- Absolute summability is unconditional and does not require an enumeration. -/
theorem summable_norm_atoms (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] :
    Summable (fun x : X => ‖ν {x}‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (sum_norm_atoms_le ν)

theorem summable_atoms (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] :
    Summable (fun x : X => ν {x}) := (summable_norm_atoms ν).of_norm

theorem countable_atoms (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] :
    {x : X | ν {x} ≠ 0}.Countable :=
  (summable_atoms ν).countable_support

theorem tsum_norm_atoms_le (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] :
    (∑' x : X, ‖ν {x}‖) ≤ ν.variation.real univ :=
  Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (sum_norm_atoms_le ν)

/-- Absolute convergence permits addition even when the atomic supports differ. -/
theorem diffuseMass_add (ν η : VectorMeasure X 𝕜)
    [IsFiniteMeasure ν.variation] [IsFiniteMeasure η.variation] :
    diffuseMass (ν + η) = diffuseMass ν + diffuseMass η := by
  simp only [diffuseMass, _root_.add_apply]
  rw [Summable.tsum_add (summable_atoms ν) (summable_atoms η)]
  ring

omit [MeasurableSingletonClass X] in
theorem diffuseMass_smul (c : 𝕜) (ν : VectorMeasure X 𝕜) :
    diffuseMass (c • ν) = c • diffuseMass ν := by
  simp only [diffuseMass, _root_.smul_apply, tsum_const_smul'', smul_sub]

theorem norm_diffuseMass_le (ν : VectorMeasure X 𝕜) [IsFiniteMeasure ν.variation] :
    ‖diffuseMass ν‖ ≤ 2 * ν.variation.real univ := by
  calc
    _ ≤ ‖ν univ‖ + ‖∑' x : X, ν {x}‖ := norm_sub_le _ _
    _ ≤ ν.variation.real univ + ∑' x : X, ‖ν {x}‖ :=
      add_le_add (VectorMeasure.norm_measure_le_variation) (norm_tsum_le_tsum_norm (summable_norm_atoms ν))
    _ ≤ 2 * ν.variation.real univ := by linarith [tsum_norm_atoms_le ν]

@[simp] theorem diffuseMass_dirac (x : X) (c : 𝕜) :
    diffuseMass (VectorMeasure.dirac x c) = 0 := by
  classical
  have hsum : (∑' y : X, (VectorMeasure.dirac x c) {y}) = c := by
    rw [tsum_eq_single x]
    · simp
    · intro y hy
      simp [Ne.symm hy]
  simp [diffuseMass, hsum]

section Compact

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

/-- The atomic-complement functional transported to the continuous bidual
using the unique representing scalar Radon measure. -/
def diffuseFunctional (hr : ScalarRepresentation 𝕜) :
    StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜)) :=
  LinearMap.mkContinuous
    { toFun := fun L => diffuseMass (representingMeasure hr L)
      map_add' := by
        intro L M
        have hL := representingMeasure_properties hr L
        have hM := representingMeasure_properties hr M
        have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
        have : IsFiniteMeasure (representingMeasure hr M).variation := ⟨hM.1.1⟩
        rw [representingMeasure_add, diffuseMass_add]
      map_smul' := by
        intro c L
        rw [representingMeasure_smul, diffuseMass_smul]
        rfl }
    2 (by
      intro L
      have hL := representingMeasure_properties hr L
      have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
      change ‖diffuseMass (representingMeasure hr L)‖ ≤ 2 * ‖L‖
      rw [hL.2.2]
      exact norm_diffuseMass_le (representingMeasure hr L))

theorem diffuseFunctional_norm_le (hr : ScalarRepresentation 𝕜) :
    ‖(diffuseFunctional hr : StrongDual 𝕜 (StrongDual 𝕜 C(K, 𝕜)))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro L
  have hL := representingMeasure_properties hr L
  have : IsFiniteMeasure (representingMeasure hr L).variation := ⟨hL.1.1⟩
  change ‖diffuseMass (representingMeasure hr L)‖ ≤ 2 * ‖L‖
  rw [hL.2.2]
  exact norm_diffuseMass_le (representingMeasure hr L)

theorem diffuseFunctional_measure (hr : ScalarRepresentation 𝕜)
    (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν)
    (L : StrongDual 𝕜 C(K, 𝕜)) (hL : ∀ f : C(K, 𝕜), L f = scalarIntegral ν f) :
    diffuseFunctional hr L = diffuseMass ν := by
  change diffuseMass (representingMeasure hr L) = _
  rw [representingMeasure_eq hr L ν hν hL]

theorem diffuseFunctional_dirac (hr : ScalarRepresentation 𝕜) (x : K) :
    diffuseFunctional hr (ContinuousMap.evalCLM 𝕜 x) = 0 := by
  rw [diffuseFunctional_measure hr _ (finiteScalarRadon_dirac x) _
    (fun f => by simp [scalarIntegral]), diffuseMass_dirac]

end Compact

/-- Embed an ordinary finite measure as a scalar measure by real inclusion. -/
def scalarMeasure (μ : Measure X) [IsFiniteMeasure μ] : VectorMeasure X 𝕜 :=
  VectorMeasure.mapRangeL RCLike.ofRealCLM μ.toSignedMeasure

omit [MeasurableSingletonClass X] in
/-- Real inclusion is isometric, so this scalar conversion preserves variation. -/
theorem scalarMeasure_variation (μ : Measure X) [IsFiniteMeasure μ] :
    (scalarMeasure μ : VectorMeasure X 𝕜).variation = μ := by
  have hn (s : Set X) : ‖(scalarMeasure μ : VectorMeasure X 𝕜) s‖ₑ = ‖μ.toSignedMeasure s‖ₑ := by
    change ‖(μ.toSignedMeasure s : 𝕜)‖ₑ = ‖μ.toSignedMeasure s‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_ofReal, Real.norm_eq_abs]
  calc
    _ = μ.toSignedMeasure.variation := by
      apply le_antisymm
      · apply VectorMeasure.variation_le_of_forall_enorm_le
        intro s hs
        rw [hn]
        exact VectorMeasure.enorm_measure_le_variation _ _
      · apply VectorMeasure.variation_le_of_forall_enorm_le
        intro s hs
        rw [← hn]
        exact VectorMeasure.enorm_measure_le_variation _ _
    _ = μ := Measure.variation_toSignedMeasure

omit [MeasurableSingletonClass X] in
/-- The scalar pairing against a positive measure is the ordinary Bochner
integral, over either scalar field and without conjugation. -/
theorem scalarIntegral_scalarMeasure (μ : Measure X) [IsFiniteMeasure μ] (f : X → 𝕜) :
    scalarIntegral (scalarMeasure μ) f = ∫ x, f x ∂μ := by
  have h : scalarIntegral (scalarMeasure μ) f =
      μ.toSignedMeasure.integral f (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    simp only [scalarIntegral, VectorMeasure.integral, scalarMeasure_variation,
      Measure.variation_toSignedMeasure]
    apply setToFun_congr_left'
    intro s hs hsf
    ext z
    change z * (μ.toSignedMeasure s : 𝕜) = (μ.toSignedMeasure s) • z
    simp only [RCLike.real_smul_eq_coe_mul, mul_comm]
  rw [h, VectorMeasure.integral_toSignedMeasure]

local instance : NormedAddCommGroup C(I, 𝕜) := inferInstance
local instance : NormedSpace 𝕜 C(I, 𝕜) := inferInstance

/-- Lebesgue integration on continuous functions on the actual unit interval. -/
def lebesgueFunctional : StrongDual 𝕜 C(I, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x : I, f x ∂volume
      map_add' := fun f g => integral_add
        ((BoundedContinuousFunction.mkOfCompact f).integrable volume)
        ((BoundedContinuousFunction.mkOfCompact g).integrable volume)
      map_smul' := fun c f => integral_smul c f }
    1 (by
      intro f
      simpa using (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm volume)

theorem scalarMeasure_lebesgue_radon :
    FiniteScalarRadon (scalarMeasure (volume : Measure I) : VectorMeasure I 𝕜) := by
  rw [FiniteScalarRadon, scalarMeasure_variation]
  exact ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr inferInstance⟩

theorem diffuseMass_lebesgue :
    diffuseMass (scalarMeasure (volume : Measure I) : VectorMeasure I 𝕜) = 1 := by
  have hs (s : Set I) (hm : MeasurableSet s) :
      (scalarMeasure (volume : Measure I) : VectorMeasure I 𝕜) s =
        ((volume.real s : ℝ) : 𝕜) := by
    change (volume.toSignedMeasure s : 𝕜) = _
    rw [Measure.toSignedMeasure_apply_measurable hm]
  simp [diffuseMass, hs univ MeasurableSet.univ,
    fun x => hs {x} (measurableSet_singleton x), measureReal_def]

theorem diffuseFunctional_lebesgue (hr : ScalarRepresentation 𝕜) :
    diffuseFunctional hr (lebesgueFunctional : StrongDual 𝕜 C(I, 𝕜)) = 1 := by
  rw [diffuseFunctional_measure hr _ scalarMeasure_lebesgue_radon _
    (fun f => (scalarIntegral_scalarMeasure volume f).symm), diffuseMass_lebesgue]

/-- Any inclusion with the integration pairing misses the diffuse-mass
functional: Dirac tests force a representing Borel function to be zero. -/
theorem integral_embedding_not_surjective (hr : ScalarRepresentation.{0} 𝕜)
    (e : BoundedBorel I 𝕜 →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 C(I, 𝕜)))
    (he : ∀ (h : BoundedBorel I 𝕜) (ν : VectorMeasure I 𝕜), FiniteScalarRadon ν →
      ∀ L : StrongDual 𝕜 C(I, 𝕜),
      (∀ f : C(I, 𝕜), L f = scalarIntegral ν f) → e h L = scalarIntegral ν h) :
    ¬ Function.Surjective e := by
  intro hsurj
  obtain ⟨h, hh⟩ := hsurj (diffuseFunctional hr)
  have hz (x : I) : h x = 0 := by
    have htest := he h (VectorMeasure.dirac x 1) (finiteScalarRadon_dirac x)
      (ContinuousMap.evalCLM 𝕜 x) (fun f => by simp [scalarIntegral])
    have hx : e h (ContinuousMap.evalCLM 𝕜 x) = h x := by
      simpa [scalarIntegral] using htest
    rw [hh, diffuseFunctional_dirac] at hx
    exact hx.symm
  have hzero : (h : I → 𝕜) = fun _ => 0 := funext hz
  have htest := he h (scalarMeasure volume) scalarMeasure_lebesgue_radon
    lebesgueFunctional (fun f => (scalarIntegral_scalarMeasure volume f).symm)
  rw [hh, diffuseFunctional_lebesgue] at htest
  have hi : scalarIntegral (scalarMeasure volume) h = 0 := by
    rw [scalarIntegral_scalarMeasure, hzero]
    simp
  exact one_ne_zero (htest.trans hi)

/-- The complete interval construction, uniform over real-like scalar fields
whenever the accepted representation theorem is supplied. -/
theorem atomic_obstruction_of_representation (hr : ScalarRepresentation.{0} 𝕜) :
    AtomicObstruction 𝕜 := by
  refine ⟨?_, diffuseFunctional hr, diffuseFunctional_norm_le hr,
    diffuseFunctional_measure hr, diffuseFunctional_dirac hr, ?_,
    integral_embedding_not_surjective hr⟩
  · intro ν hν
    have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
    exact ⟨countable_atoms ν, summable_norm_atoms ν, tsum_norm_atoms_le ν⟩
  · exact ⟨lebesgueFunctional, fun _ => rfl, diffuseFunctional_lebesgue hr⟩

/-- Bounded Borel functions embed isometrically for arbitrary compact
Hausdorff spaces, but the inclusion is not onto already on `[0,1]`, over `ℝ`. -/
theorem real_conclusion : RealConclusion.{u} :=
  ⟨real_borel_embedding, atomic_obstruction_of_representation real_representation⟩

/-- The same construction is complex-linear, with no conjugation in the pairing. -/
theorem complex_conclusion : ComplexConclusion.{u} :=
  ⟨complex_borel_embedding, atomic_obstruction_of_representation complex_representation⟩

end ExpandedFA.Supplements.BidualBorelObstruction
