import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.DistributionPaleyWiener
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SmoothPaleyWiener
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TemperedExamples
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Set TopologicalSpace MeasureTheory
open scoped ContDiff Pointwise FourierTransform

noncomputable section
namespace ExpandedFA.Fourier.DistributionPaleyWiener
open ExpandedFA.Distributions ExpandedFA.Fourier.PaleyWiener

lemma norm_iteratedFDeriv_cexp_comp_clm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℂ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun x => Complex.exp (L x)) x‖ ≤
      ‖Complex.exp (L x)‖ * ‖L‖ ^ n := by
  rw [show (fun x => Complex.exp (L x)) = Complex.exp ∘ L from rfl,
    L.iteratedFDeriv_comp_right (Complex.contDiff_exp (𝕜 := ℝ)) x (by simp : (n : WithTop ℕ∞) ≤ ⊤)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have heq : ‖iteratedFDeriv ℝ n Complex.exp (L x)‖ = ‖Complex.exp (L x)‖ := by
    rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt (x := L x)).restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
    simp only [Function.comp_apply]
    rw [ContinuousMultilinearMap.norm_restrictScalars,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]
  simp [heq]

lemma iteratedFDeriv_cexp_comp_clm_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℂ) (n : ℕ) (x : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun x => Complex.exp (L x)) x v =
      (∏ j, L (v j)) * Complex.exp (L x) := by
  rw [show (fun x => Complex.exp (L x)) = Complex.exp ∘ L from rfl,
    L.iteratedFDeriv_comp_right (Complex.contDiff_exp (𝕜 := ℝ)) x (by simp : (n : WithTop ℕ∞) ≤ ⊤)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt (x := L x)).restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_eq_iterate,
    Complex.iter_deriv_exp, smul_eq_mul]

def coordinateSpatialExponent {d : ℕ} (z : ComplexEuclidean d) : Domain d →L[ℝ] ℂ :=
  (spatialExponentCLM z).comp (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap

lemma coordinateSpatialExponent_apply {d : ℕ} (z : ComplexEuclidean d) (x : Domain d) :
    coordinateSpatialExponent z x = -2 * (Real.pi : ℂ) * Complex.I *
      ∑ j, Complex.ofRealCLM (x j) * z j := by
  simp [coordinateSpatialExponent, spatialExponentCLM_apply, complexPairing]

def coordinateSpatialExponentLM (d : ℕ) :
    ComplexEuclidean d →ₗ[ℂ] (Domain d →L[ℝ] ℂ) where
  toFun := coordinateSpatialExponent
  map_add' z w := by
    ext x
    simp [coordinateSpatialExponent_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c z := by
    ext x
    simp [coordinateSpatialExponent_apply, ← Finset.mul_sum, mul_left_comm, mul_assoc]

def coordinateSpatialExponentCLM (d : ℕ) :
    ComplexEuclidean d →L[ℂ] (Domain d →L[ℝ] ℂ) :=
  (coordinateSpatialExponentLM d).toContinuousLinearMap

lemma coordinateSpatialExponent_norm_bound {d : ℕ} (z : ComplexEuclidean d) :
    ‖coordinateSpatialExponent z‖ ≤ ‖coordinateSpatialExponentCLM d‖ * ‖z‖ :=
  (coordinateSpatialExponentCLM d).le_opNorm z

lemma laplaceKernel_iteratedFDeriv_apply {d : ℕ} (z : ComplexEuclidean d)
    (n : ℕ) (x : Domain d) (v : Fin n → Domain d) :
    iteratedFDeriv ℝ n (laplaceKernel z).val x v =
      (∏ j, coordinateSpatialExponent z (v j)) * (laplaceKernel z).val x := by
  have heq : (laplaceKernel z).val = fun x => Complex.exp (coordinateSpatialExponent z x) := by
    funext x
    simp [laplaceKernel, coordinateSpatialExponent_apply]
  rw [heq]
  exact iteratedFDeriv_cexp_comp_clm_apply _ _ _ _

lemma laplaceKernel_coordinate_derivative {d : ℕ} (z : ComplexEuclidean d)
    (n : ℕ) (x : Domain d) (a : Fin n → Fin d) :
    iteratedFDeriv ℝ n (laplaceKernel z).val x (fun j => coordinateVector (a j)) =
      (∏ j, (-2 * (Real.pi : ℂ) * Complex.I * z (a j))) * (laplaceKernel z).val x := by
  rw [laplaceKernel_iteratedFDeriv_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [coordinateSpatialExponent_apply, coordinateVector, Pi.single_apply,
    Complex.ofRealCLM_apply, apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
  simp

lemma laplaceKernel_derivative_bound {d : ℕ} (z : ComplexEuclidean d)
    (n : ℕ) (x : Domain d) :
    ‖iteratedFDeriv ℝ n (laplaceKernel z).val x‖ ≤
      Real.exp (2 * Real.pi * inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x)
        (imaginaryPart z)) * ‖coordinateSpatialExponent z‖ ^ n := by
  have heq : (laplaceKernel z).val = fun x => Complex.exp (coordinateSpatialExponent z x) := by
    funext x
    simp [laplaceKernel, coordinateSpatialExponent_apply]
  rw [heq]
  convert norm_iteratedFDeriv_cexp_comp_clm (coordinateSpatialExponent z) n x using 1
  rw [coordinateSpatialExponent, ContinuousLinearMap.comp_apply,
    spatialExponentCLM_apply, kernel_norm]
  rfl

lemma laplaceKernel_seminorm_bound {d : ℕ} (z : ComplexEuclidean d)
    (q : SmoothJetIndex (⊤ : Opens (Domain d))) :
    smoothSeminorm ℂ ⊤ q (laplaceKernel z) ≤
      Real.exp (2 * Real.pi * supportFunction
        ((EuclideanSpace.equiv (Fin d) ℝ).symm '' (q.1.val : Set (Domain d)))
        (imaginaryPart z)) * ‖coordinateSpatialExponent z‖ ^ q.2 := by
  change ‖smoothJetLM ℂ ⊤ q (laplaceKernel z)‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (laplaceKernel_derivative_bound z q.2 x).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact inner_le_supportFunction
    (q.1.val.isCompact.image (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous)
    (mem_image_of_mem _ x.property) _

lemma laplaceKernel_seminorm_bound_of_subset {d : ℕ} (z : ComplexEuclidean d)
    (q : SmoothJetIndex (⊤ : Opens (Domain d))) (Q : Compacts (Domain d))
    (hq : q.1.val ≤ Q) :
    smoothSeminorm ℂ ⊤ q (laplaceKernel z) ≤
      Real.exp (2 * Real.pi * supportFunction
        ((EuclideanSpace.equiv (Fin d) ℝ).symm '' (Q : Set (Domain d)))
        (imaginaryPart z)) * ‖coordinateSpatialExponent z‖ ^ q.2 := by
  change ‖smoothJetLM ℂ ⊤ q (laplaceKernel z)‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (laplaceKernel_derivative_bound z q.2 x).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact inner_le_supportFunction
    (Q.isCompact.image (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous)
    (mem_image_of_mem _ (hq x.property)) _

lemma coordinateSpatialExponent_pow_bound {d : ℕ} (z : ComplexEuclidean d)
    {n N : ℕ} (hn : n ≤ N) :
    ‖coordinateSpatialExponent z‖ ^ n ≤
      (1 + ‖coordinateSpatialExponentCLM d‖) ^ N * (1 + ‖z‖) ^ N := by
  calc
    _ ≤ (1 + ‖coordinateSpatialExponent z‖) ^ n := by gcongr; exact le_add_of_nonneg_left zero_le_one
    _ ≤ (1 + ‖coordinateSpatialExponent z‖) ^ N := by
      exact pow_le_pow_right₀ (by linarith [norm_nonneg (coordinateSpatialExponent z)]) hn
    _ ≤ (1 + ‖coordinateSpatialExponentCLM d‖ * ‖z‖) ^ N := by
      gcongr
      exact coordinateSpatialExponent_norm_bound z
    _ ≤ ((1 + ‖coordinateSpatialExponentCLM d‖) * (1 + ‖z‖)) ^ N := by
      gcongr
      nlinarith [norm_nonneg (coordinateSpatialExponentCLM d), norm_nonneg z]
    _ = _ := mul_pow _ _ _

lemma smooth_functional_laplace_growth {d : ℕ} (L : Smooth d →L[ℂ] ℂ) :
    ∃ (Q : Compacts (Domain d)) (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ z : ComplexEuclidean d, ‖L (laplaceKernel z)‖ ≤
        C * (1 + ‖z‖) ^ N * Real.exp (2 * Real.pi * supportFunction
          ((EuclideanSpace.equiv (Fin d) ℝ).symm '' (Q : Set (Domain d)))
          (imaginaryPart z)) := by
  classical
  obtain ⟨s, A, _, hA⟩ := Seminorm.bound_of_continuous
    (smooth_withSeminorms (𝕜 := ℂ) (Ω := (⊤ : Opens (Domain d))))
    ((normSeminorm ℂ ℂ).comp L.toLinearMap) L.continuous.norm
  let Q : Compacts (Domain d) := s.sup fun q => q.1.val
  let N : ℕ := s.sup fun q => q.2
  let B : ℝ := (1 + ‖coordinateSpatialExponentCLM d‖) ^ N
  refine ⟨Q, N, (A : ℝ) * B, by positivity, fun z => ?_⟩
  have hb : (s.sup (smoothSeminorm ℂ (⊤ : Opens (Domain d)))) (laplaceKernel z) ≤
      Real.exp (2 * Real.pi * supportFunction
        ((EuclideanSpace.equiv (Fin d) ℝ).symm '' (Q : Set (Domain d)))
        (imaginaryPart z)) * (B * (1 + ‖z‖) ^ N) := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro q hq
    apply (laplaceKernel_seminorm_bound_of_subset z q Q
      (Finset.le_sup (f := fun q : SmoothJetIndex (⊤ : Opens (Domain d)) => q.1.val) hq)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact coordinateSpatialExponent_pow_bound z
      (Finset.le_sup (f := fun q : SmoothJetIndex (⊤ : Opens (Domain d)) => q.2) hq)
  calc
    _ ≤ (A : ℝ) * (s.sup (smoothSeminorm ℂ (⊤ : Opens (Domain d))))
      (laplaceKernel z) := hA _
    _ ≤ (A : ℝ) * (Real.exp (2 * Real.pi * supportFunction
        ((EuclideanSpace.equiv (Fin d) ℝ).symm '' (Q : Set (Domain d)))
        (imaginaryPart z)) * (B * (1 + ‖z‖) ^ N)) :=
      mul_le_mul_of_nonneg_left hb A.coe_nonneg
    _ = _ := by ring

lemma functional_factorization_of_bound {E B : Type*}
    [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (J : E →ₗ[ℂ] B) (l : E →ₗ[ℂ] ℂ) (C : ℝ)
    (hl : ∀ x, ‖l x‖ ≤ C * ‖J x‖) :
    ∃ L : B →L[ℂ] ℂ, ∀ x, L (J x) = l x := by
  have hker : J.ker ≤ l.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    have hh := hl x
    rw [LinearMap.mem_ker.mp hx, norm_zero, mul_zero] at hh
    exact norm_le_zero_iff.mp hh
  let v : J.range →ₗ[ℂ] ℂ :=
    (J.ker.liftQ l hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hv_apply (x : E) (h : J x ∈ J.range) : v ⟨J x, h⟩ = l x := by
    simp [v, LinearMap.quotKerEquivRange_symm_apply_image]
  have hv : ∀ z : J.range, ‖v z‖ ≤ C * ‖z‖ := by
    intro z
    obtain ⟨x, hx⟩ := z.property
    have hz : z = ⟨J x, LinearMap.mem_range_self J x⟩ := Subtype.ext hx.symm
    rw [hz, hv_apply]
    exact hl x
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq J.range (v.mkContinuous C hv)
  refine ⟨L, fun x => ?_⟩
  exact (hL ⟨J x, LinearMap.mem_range_self J x⟩).trans (hv_apply x _)

abbrev CompactJetSpace {d : ℕ} (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d)))) :=
  (a : s) → C(a.val.1.1.val, ℂ)

def compactJetMap {d : ℕ} (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d)))) :
    Smooth d →ₗ[ℂ] CompactJetSpace s :=
  LinearMap.pi fun a => (((coordinateEvaluation ℂ a.val.2).compLeftContinuous ℂ a.val.1.1.val).toLinearMap.comp
    (smoothJetLM ℂ ⊤ a.val.1))

lemma norm_compactJetMap {d : ℕ} (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d))))
    (f : Smooth d) : ‖compactJetMap s f‖ = (s.sup (smoothCoordinateSeminorm ℂ ⊤)) f := by
  classical
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
    intro a
    change smoothCoordinateSeminorm ℂ ⊤ a.val f ≤ _
    exact Seminorm.le_finset_sup_apply a.property
  · apply Seminorm.finset_sup_apply_le (norm_nonneg _)
    intro a ha
    exact norm_le_pi_norm (compactJetMap s f) ⟨a, ha⟩

lemma smooth_functional_compactJet_factorization {d : ℕ} (l : Smooth d →L[ℂ] ℂ) :
    ∃ s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d))),
      ∃ L : CompactJetSpace s →L[ℂ] ℂ, ∀ f, L (compactJetMap s f) = l f := by
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
    (smooth_coordinate_topology ℂ d ⊤)
    ((normSeminorm ℂ ℂ).comp l.toLinearMap) l.continuous.norm
  refine ⟨s, ?_⟩
  apply functional_factorization_of_bound (compactJetMap s) l.toLinearMap C
  intro f
  rw [norm_compactJetMap]
  exact hC f



def compactExponentLM {d : ℕ} (K : Compacts (Domain d)) :
    ComplexEuclidean d →ₗ[ℂ] C(K, ℂ) where
  toFun z := ⟨fun x => coordinateSpatialExponent z x,
    (coordinateSpatialExponent z).continuous.comp continuous_subtype_val⟩
  map_add' z w := by
    ext x
    exact congrArg (fun L : Domain d →L[ℝ] ℂ => L x)
      ((coordinateSpatialExponentLM d).map_add z w)
  map_smul' c z := by
    ext x
    exact congrArg (fun L : Domain d →L[ℝ] ℂ => L x)
      ((coordinateSpatialExponentLM d).map_smul c z)

def compactExponentCLM {d : ℕ} (K : Compacts (Domain d)) :
    ComplexEuclidean d →L[ℂ] C(K, ℂ) := (compactExponentLM K).toContinuousLinearMap

def compactKernel {d : ℕ} (K : Compacts (Domain d)) (z : ComplexEuclidean d) : C(K, ℂ) :=
  NormedSpace.exp (compactExponentCLM K z)

lemma compactKernel_apply {d : ℕ} (K : Compacts (Domain d)) (z : ComplexEuclidean d)
    (x : K) : compactKernel K z x = (laplaceKernel z).val x := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
    (ContinuousMap.evalCLM ℂ x).continuous (compactExponentCLM K z)
  rw [show (laplaceKernel z).val x = Complex.exp (coordinateSpatialExponent z x) by
    simp [laplaceKernel, coordinateSpatialExponent_apply]]
  simpa [compactKernel, compactExponentCLM, compactExponentLM, ← Complex.exp_eq_exp_ℂ] using h

lemma differentiable_compactKernel {d : ℕ} (K : Compacts (Domain d)) :
    Differentiable ℂ (compactKernel K) := by
  have h : Differentiable ℂ (NormedSpace.exp : C(K, ℂ) → C(K, ℂ)) :=
    fun x => (hasFDerivAt_exp (𝕂 := ℂ) (x := x)).differentiableAt
  exact h.comp (compactExponentCLM K).differentiable

lemma differentiable_compactJetMap_kernel {d : ℕ}
    (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d)))) :
    Differentiable ℂ (fun z : ComplexEuclidean d => compactJetMap s (laplaceKernel z)) := by
  classical
  have heq : (fun z : ComplexEuclidean d => compactJetMap s (laplaceKernel z)) =
      fun z (a : s) => (∏ j, (-2 * (Real.pi : ℂ) * Complex.I * z (a.val.2 j))) •
        compactKernel a.val.1.1.val z := by
    funext z a
    apply ContinuousMap.ext
    intro x
    change iteratedFDeriv ℝ a.val.1.2 (laplaceKernel z).val x
      (fun j => coordinateVector (a.val.2 j)) = _
    rw [laplaceKernel_coordinate_derivative]
    simp [compactKernel_apply]
  rw [heq]
  apply differentiable_pi.mpr
  intro a
  have hpoly : Differentiable ℂ (fun z : ComplexEuclidean d =>
      ∏ j, (-2 * (Real.pi : ℂ) * Complex.I * z (a.val.2 j))) := by fun_prop
  exact hpoly.smul (differentiable_compactKernel a.val.1.1.val)

lemma differentiable_smooth_functional_laplace {d : ℕ} (l : Smooth d →L[ℂ] ℂ) :
    Differentiable ℂ (fun z => l (laplaceKernel z)) := by
  obtain ⟨s, L, hL⟩ := smooth_functional_compactJet_factorization l
  have heq : (fun z => l (laplaceKernel z)) = L ∘ (fun z => compactJetMap s (laplaceKernel z)) := by
    funext z
    exact (hL _).symm
  rw [heq]
  exact L.differentiable.comp (differentiable_compactJetMap_kernel s)


lemma isCompact_distributionSupport {d : ℕ} {u : Distribution d}
    (hu : IsCompact (euclideanSupport u)) : IsCompact (distributionSupport u) := by
  have heq : distributionSupport u =
      (EuclideanSpace.equiv (Fin d) ℝ) '' euclideanSupport u := by
    change distributionSupport u = (EuclideanSpace.equiv (Fin d) ℝ) ''
      ((EuclideanSpace.equiv (Fin d) ℝ).symm '' distributionSupport u)
    rw [Set.image_image]
    simp only [ContinuousLinearEquiv.apply_symm_apply, Set.image_id']
  rw [heq]
  exact hu.image (EuclideanSpace.equiv (Fin d) ℝ).continuous

lemma isClosed_euclideanSupport {d : ℕ} (u : Distribution d) :
    IsClosed (euclideanSupport u) := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph.isClosedMap
  have h := (support_vanishing ℂ d ⊤ u).1.isClosed_compl
  convert h using 1
  ext x
  simp [distributionSupport]

lemma isCompact_euclideanSupport_of_supportedIn {d : ℕ}
    {K : Set (Euclidean d)} (hK : IsCompact K) {u : Distribution d}
    (hu : SupportedIn K u) : IsCompact (euclideanSupport u) :=
  hK.of_isClosed_subset (isClosed_euclideanSupport u) hu

/-- The choice in the definition really agrees with the original LF distribution. -/
theorem extension : Specs.ExpandedFA.Fourier.DistributionPaleyWiener.extensionType := by
  intro d u hu
  obtain ⟨L, hL, _⟩ := compact_dual_extension ℂ d ⊤ u
    (isCompact_distributionSupport hu)
  exact Classical.epsilon_spec (show ∃ L : Smooth d →L[ℂ] ℂ,
    ∀ φ : Tests ℂ (⊤ : Opens (Domain d)), L (testToSmoothLM ℂ ⊤ φ) = u φ from ⟨L, hL⟩)

lemma smoothExtension_eq {d : ℕ} {u : Distribution d}
    (hu : IsCompact (euclideanSupport u)) (L : Smooth d →L[ℂ] ℂ)
    (hL : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)), L (testToSmoothLM ℂ ⊤ φ) = u φ) :
    smoothExtension u = L := by
  obtain ⟨M, _, hM⟩ := compact_dual_extension ℂ d ⊤ u
    (isCompact_distributionSupport hu)
  exact (hM _ (extension d u hu)).trans (hM _ hL).symm

/-- The canonical transform of a compactly supported distribution is entire. -/
theorem entire : Specs.ExpandedFA.Fourier.DistributionPaleyWiener.entireType := by
  intro d u _
  exact differentiable_smooth_functional_laplace (smoothExtension u)

/-- Transform evaluation is independent of any choice of extension or cutoff. -/
theorem cutoff : Specs.ExpandedFA.Fourier.DistributionPaleyWiener.cutoffType := by
  intro d u hu χ V hV hs hχ z
  obtain ⟨L, hL, hf⟩ := compact_dual_cutoff_formula ℂ d ⊤ u
    (isCompact_distributionSupport hu)
  rw [fourierLaplace, smoothExtension_eq hu L hL]
  exact hf χ V hV hs hχ (laplaceKernel z)

lemma inner_le_supportFunction_convexHull {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsCompact K) (η : Euclidean d) {x : Euclidean d}
    (hx : x ∈ convexHull ℝ K) : inner ℝ x η ≤ supportFunction K η := by
  have hlin : IsLinearMap ℝ (fun x : Euclidean d => inner ℝ x η) :=
    ⟨fun x y => inner_add_left x y η, fun a x => real_inner_smul_left x η a⟩
  exact (convexHull_min (fun y hy => inner_le_supportFunction hK hy η)
    (convex_halfSpace_le hlin (supportFunction K η))) hx

/-- Taking convex hulls leaves the support function unchanged, so exponential
bounds alone cannot detect holes in a compact support. -/
theorem convex_hull : Specs.ExpandedFA.Fourier.DistributionPaleyWiener.convexHullType := by
  intro d K hne hK η
  have hne' : (convexHull ℝ K).Nonempty := hne.mono (subset_convexHull ℝ K)
  have hb : BddAbove ((fun x => inner ℝ x η) '' convexHull ℝ K) :=
    ⟨supportFunction K η, by
      rintro _ ⟨x, hx, rfl⟩
      exact inner_le_supportFunction_convexHull hK η hx⟩
  apply le_antisymm
  · exact csSup_le (hne'.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      exact inner_le_supportFunction_convexHull hK η hx)
  · exact csSup_le (hne.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      exact le_csSup hb (mem_image_of_mem _ (subset_convexHull ℝ K hx)))

lemma polynomial_real_axis_bound {d : ℕ} {K : Set (Euclidean d)} (hne : K.Nonempty)
    {F : ComplexEuclidean d → ℂ} (hF : PolynomialExponentialType K F) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ ξ : Euclidean d,
      ‖F (realFrequency ξ)‖ ≤ C * (1 + ‖ξ‖) ^ M := by
  obtain ⟨M, C, hC, hb⟩ := hF
  refine ⟨M, C, hC, fun ξ => ?_⟩
  simpa [supportFunction_zero hne] using hb (realFrequency ξ)

/-- A polynomially bounded real restriction has integrable weighted norm.
This supplies the actual hypothesis of `integral_growth_tempered`. -/
lemma polynomial_real_axis_weighted_integrable {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) {F : ComplexEuclidean d → ℂ}
    (hc : Continuous F) (hF : PolynomialExponentialType K F) :
    ∃ N : ℕ, Integrable (fun ξ : Euclidean d =>
      (1 + ‖ξ‖)⁻¹ ^ N * ‖F (realFrequency ξ)‖) := by
  obtain ⟨M, C, hC, hb⟩ := polynomial_real_axis_bound hne hF
  let Q := Module.finrank ℝ (Euclidean d) + 1
  refine ⟨M + Q, ?_⟩
  have hi : Integrable (fun ξ : Euclidean d => (1 + ‖ξ‖) ^ (-(Q : ℤ))) := by
    simp_rw [← Real.rpow_neg_natCast]
    apply integrable_one_add_norm
    dsimp [Q]
    norm_num
  apply (hi.const_mul C).mono' (by
    have hfc := hc.comp (continuous_realFrequency d)
    apply Continuous.aestronglyMeasurable
    have hn : Continuous (fun ξ : Euclidean d => 1 + ‖ξ‖) :=
      continuous_const.add continuous_norm
    have hw : Continuous (fun ξ : Euclidean d => (1 + ‖ξ‖)⁻¹) :=
      hn.inv₀ (fun ξ => by positivity)
    exact (hw.pow _).mul hfc.norm)
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 + ‖ξ‖)⁻¹ ^ (M + Q) * (C * (1 + ‖ξ‖) ^ M) := by
      exact mul_le_mul_of_nonneg_left (hb ξ) (by positivity)
    _ = C * (1 + ‖ξ‖) ^ (-(Q : ℤ)) := by
      have hp : (1 + ‖ξ‖) ≠ 0 := by positivity
      rw [← zpow_neg_one, ← zpow_natCast, ← zpow_mul, ← zpow_natCast]
      rw [mul_left_comm, ← zpow_add₀ hp]
      congr 2
      push_cast
      ring

/-- Construction of the tempered distribution on the real frequency axes.
No compact-support conclusion for its inverse is asserted at this stage. -/
theorem real_axis_tempered :
    Specs.ExpandedFA.Fourier.DistributionPaleyWiener.realAxisTemperedType := by
  intro d K hne F hF hb
  obtain ⟨N, hN⟩ := polynomial_real_axis_weighted_integrable hne hF.continuous hb
  have hc : Continuous (fun ξ : Euclidean d => F (realFrequency ξ)) :=
    hF.continuous.comp (continuous_realFrequency d)
  exact Examples.integral_growth_tempered ℂ d _ hc.locallyIntegrable N hN

/-- Support functions add under Minkowski addition. -/
lemma supportFunction_add {d : ℕ} {K L : Set (Euclidean d)}
    (hneK : K.Nonempty) (hK : IsCompact K) (hneL : L.Nonempty) (hL : IsCompact L)
    (η : Euclidean d) :
    supportFunction (K + L) η = supportFunction K η + supportFunction L η := by
  obtain ⟨x, hx, hmaxK⟩ := hK.exists_isMaxOn hneK
    (show ContinuousOn (fun x => inner ℝ x η) K by fun_prop)
  obtain ⟨y, hy, hmaxL⟩ := hL.exists_isMaxOn hneL
    (show ContinuousOn (fun y => inner ℝ y η) L by fun_prop)
  have hsupK : supportFunction K η = inner ℝ x η := by
    apply le_antisymm
    · exact csSup_le (hneK.image _) (by rintro _ ⟨a, ha, rfl⟩; exact hmaxK ha)
    · exact inner_le_supportFunction hK hx η
  have hsupL : supportFunction L η = inner ℝ y η := by
    apply le_antisymm
    · exact csSup_le (hneL.image _) (by rintro _ ⟨b, hb, rfl⟩; exact hmaxL hb)
    · exact inner_le_supportFunction hL hy η
  rw [hsupK, hsupL]
  apply le_antisymm
  · apply csSup_le ((hneK.add hneL).image _)
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    simpa only [inner_add_left] using add_le_add (hmaxK ha) (hmaxL hb)
  · simpa only [inner_add_left] using
      inner_le_supportFunction (hK.add hL) (Set.add_mem_add hx hy) η

/-- Multiplication by a rapidly decreasing entire function absorbs every
polynomial power, without enlarging the sum of exponential support types. -/
lemma polynomial_mul_rapid {d : ℕ} {K L : Set (Euclidean d)}
    (hneK : K.Nonempty) (hK : IsCompact K) (hneL : L.Nonempty) (hL : IsCompact L)
    {F G : ComplexEuclidean d → ℂ} (hF : PolynomialExponentialType K F)
    (hG : RapidExponentialType L G) :
    RapidExponentialType (K + L) (fun z => F z * G z) := by
  obtain ⟨M, C, hC, hb⟩ := hF
  intro N
  obtain ⟨D, hD, hd⟩ := hG (M + N)
  refine ⟨C * D, mul_nonneg hC hD, fun z => ?_⟩
  rw [norm_mul]
  calc
    _ ≤ (C * (1 + ‖z‖) ^ M * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z))) *
        (D * (1 + ‖z‖) ^ (-((M + N : ℕ) : ℤ)) *
          Real.exp (2 * Real.pi * supportFunction L (imaginaryPart z))) :=
      mul_le_mul (hb z) (hd z) (norm_nonneg _) (by positivity)
    _ = C * D * (1 + ‖z‖) ^ (-(N : ℤ)) *
        Real.exp (2 * Real.pi * supportFunction (K + L) (imaginaryPart z)) := by
      rw [supportFunction_add hneK hK hneL hL, mul_add, Real.exp_add]
      have hp : (1 + ‖z‖) ^ M * (1 + ‖z‖) ^ (-((M + N : ℕ) : ℤ)) =
          (1 + ‖z‖) ^ (-(N : ℤ)) := by
        rw [← zpow_natCast (1 + ‖z‖) M, ← zpow_add₀ (by positivity : 1 + ‖z‖ ≠ 0)]
        congr 1
        omega
      calc
        _ = (C * D) * ((1 + ‖z‖) ^ M * (1 + ‖z‖) ^ (-((M + N : ℕ) : ℤ))) *
            (Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) *
              Real.exp (2 * Real.pi * supportFunction L (imaginaryPart z))) := by ring
        _ = _ := by rw [hp]

/-- The smooth theorem now produces actual regularized inverses. -/
theorem regularized_inverse :
    Specs.ExpandedFA.Fourier.DistributionPaleyWiener.regularizedInverseType := by
  intro d K L hneK hK hcK hneL hL hcL F ρ hF hb hρ
  obtain ⟨hρdiff, hρbound⟩ := PaleyWiener.forward d L hneL hL hcL ρ hρ
  exact PaleyWiener.inverse d (K + L) (hneK.add hneL) (hK.add hL) (hcK.add hcL)
    _ (hF.mul hρdiff) (polynomial_mul_rapid hneK hK hneL hL hb hρbound)

/-- An exact test-function criterion for support in a closed set. -/
lemma support_subset_iff_vanishes {d : ℕ} (u : Distribution d) {K : Set (Domain d)}
    (hK : IsClosed K) :
    distributionSupport u ⊆ K ↔
      ∀ φ : Tests ℂ (⊤ : Opens (Domain d)), tsupport φ ⊆ Kᶜ → u φ = 0 := by
  constructor
  · intro hu φ hφ
    apply (support_vanishing ℂ d ⊤ u).2.2
    intro x hx
    by_contra hn
    exact hφ hx (hu ⟨Set.mem_univ x, hn⟩)
  · intro hv x hx
    by_contra hxK
    apply hx.2
    exact Set.mem_sUnion.mpr ⟨Kᶜ, ⟨hK.isOpen_compl, subset_univ _, hv⟩, hxK⟩

/-- Support survives a weak distributional limit when the approximating supports
lie in shrinking closed neighborhoods. The metric here is the native coordinate
metric of the LF tests; the assertion is independent of a choice of equivalent norm. -/
lemma support_subset_of_testwise_limit {d : ℕ} {K : Set (Domain d)}
    (hK : IsClosed K) (u : Distribution d) (v : ℝ → Distribution d)
    (hv : ∀ ε > 0, distributionSupport (v ε) ⊆ Metric.cthickening ε K)
    (hlim : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      Filter.Tendsto (fun ε => v ε φ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (u φ))) :
    distributionSupport u ⊆ K := by
  apply (support_subset_iff_vanishes u hK).mpr
  intro φ hφ
  have hdis : Disjoint (tsupport φ) K := Set.disjoint_left.mpr (fun x hx hxK => hφ hx hxK)
  obtain ⟨δ, hδ, hd⟩ := hdis.exists_cthickenings φ.hasCompactSupport hK
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  have hzero : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), v ε φ = 0 := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεδ hε
    apply (support_vanishing ℂ d ⊤ (v ε)).2.2
    intro x hx
    by_contra hn
    have hxv : x ∈ distributionSupport (v ε) := ⟨Set.mem_univ x, hn⟩
    have hxt : x ∈ Metric.cthickening δ (tsupport φ) := Metric.self_subset_cthickening _ hx
    have hxK : x ∈ Metric.cthickening δ K :=
      Metric.cthickening_mono hεδ.le K (hv ε hε hxv)
    exact Set.disjoint_left.mp hd hxt hxK
  exact tendsto_nhds_unique (hlim φ) (tendsto_const_nhds.congr' (hzero.mono (fun _ h => h.symm)))

/-- The inclusion of LF tests in Schwartz space, before changing coordinates. -/
def coordinateTestSchwartzLM (d : ℕ) :
    Tests ℂ (⊤ : Opens (Domain d)) →ₗ[ℂ] SchwartzMap (Domain d) ℂ where
  toFun φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

lemma coordinateTestSchwartz_continuous (d : ℕ) : Continuous (coordinateTestSchwartzLM d) := by
  rw [TestFunction.continuous_iff_continuous_comp]
  intro K hK
  obtain ⟨R, hR, hRK⟩ := K.isCompact.isBounded.exists_pos_norm_le
  let T : Step ℂ K →ₗ[ℂ] SchwartzMap (Domain d) ℂ :=
    (coordinateTestSchwartzLM d).comp (TestFunction.ofSupportedInCLM ℂ hK).toLinearMap
  change Continuous T
  refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
    (schwartz_withSeminorms ℂ (Domain d) ℂ) T (.of_real fun q => ?_)
  refine ⟨{q.2}, R ^ q.1, fun φ => ?_⟩
  simp only [Finset.sup_singleton]
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity)
  intro x
  change ‖x‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 φ x‖ ≤ _
  by_cases hx : x ∈ K
  · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (hRK x hx) q.1)
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ (f := φ) (x := x))
      (norm_nonneg _) (by positivity)
  · rw [φ.iteratedFDeriv_zero_on_compl hx]
    simp only [Pi.zero_apply, norm_zero, mul_zero]
    positivity

/-- LF continuity, obtained from a fixed support bound on each compact step. -/
theorem test_schwartz_continuous (d : ℕ) :
    Continuous (Examples.testSchwartz ℂ (d := d)) := by
  let P : SchwartzMap (Domain d) ℂ →L[ℂ] Schwartz ℂ d :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin d) ℝ)
  exact P.continuous.comp (coordinateTestSchwartz_continuous d)

/-- Any tempered distribution restricts to the original complex-linear LF dual. -/
def testSchwartzCLM (d : ℕ) : Tests ℂ (⊤ : Opens (Domain d)) →L[ℂ] Schwartz ℂ d where
  toLinearMap := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (EuclideanSpace.equiv (Fin d) ℝ)).toLinearMap.comp (coordinateTestSchwartzLM d)
  cont := test_schwartz_continuous d

def temperedRestriction {d : ℕ} (U : Tempered ℂ d) : Distribution d :=
  U.comp (testSchwartzCLM d)

@[simp] lemma temperedRestriction_apply {d : ℕ} (U : Tempered ℂ d)
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    temperedRestriction U φ = U (Examples.testSchwartz ℂ φ) := rfl

lemma temperedFourier_injective (d : ℕ) : Function.Injective (@temperedFourier d) := by
  obtain ⟨e, he, _⟩ := Inversion.tempered_automorphism d
  intro U V h
  apply e.injective
  simpa only [he] using h

/-- Construct the distribution specified by taking the inverse of the real
restriction. The remaining converse proof must establish its support and
identify its entire transform. -/
theorem inverse_tempered :
    Specs.ExpandedFA.Fourier.DistributionPaleyWiener.inverseTemperedType := by
  intro d K hne F hF hb
  obtain ⟨V, hV⟩ := real_axis_tempered d K hne F hF hb
  obtain ⟨e, he, _⟩ := Inversion.tempered_automorphism d
  refine ⟨temperedRestriction (e.symm V), e.symm V, fun _ => rfl, ?_⟩
  intro ψ
  have heq : temperedFourier (e.symm V) = V := by
    rw [← he, e.apply_symm_apply]
  rw [heq]
  exact hV ψ

/-- A normalized nonnegative smooth bump in the Euclidean realization. -/
def bumpKernel {d : ℕ} (b : ContDiffBump (0 : Euclidean d)) : Euclidean d → ℂ :=
  fun x => (b.normed volume x : ℂ)

lemma bumpKernel_smoothSupportedIn {d : ℕ} (b : ContDiffBump (0 : Euclidean d)) :
    SmoothSupportedIn (Metric.closedBall 0 b.rOut) (bumpKernel b) := by
  constructor
  · exact Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  · apply subset_trans (tsupport_comp_subset (g := Complex.ofReal) (by simp) _)
    rw [b.tsupport_normed_eq]

lemma bumpKernel_integral_norm {d : ℕ} (b : ContDiffBump (0 : Euclidean d)) :
    ∫ x, ‖bumpKernel b x‖ = 1 := by
  simpa only [bumpKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (b.nonneg_normed _)] using b.integral_normed (μ := volume)

lemma bumpKernel_transform_bound {d : ℕ} (b : ContDiffBump (0 : Euclidean d))
    (ξ : Euclidean d) :
    ‖PaleyWiener.fourierLaplace (bumpKernel b) (realFrequency ξ)‖ ≤ 1 := by
  rw [PaleyWiener.real_restriction, PaleyWiener.integralFourier_eq_fourier]
  exact (Real.norm_fourier_le_integral_norm _ ξ).trans_eq (bumpKernel_integral_norm b)

/-- The Fourier transforms of shrinking probability bumps tend pointwise to one. -/
lemma bumpKernel_transform_tendsto {d : ℕ} {b : ℕ → ContDiffBump (0 : Euclidean d)}
    (hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0))
    (ξ : Euclidean d) :
    Filter.Tendsto (fun n => PaleyWiener.fourierLaplace (bumpKernel (b n))
      (realFrequency ξ)) Filter.atTop (nhds 1) := by
  let g : Euclidean d → ℂ := fun x =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) hb hg 0
  have heq (n : ℕ) :
      MeasureTheory.convolution ((b n).normed volume) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 =
      PaleyWiener.fourierLaplace (bumpKernel (b n)) (realFrequency ξ) := by
    rw [MeasureTheory.convolution, PaleyWiener.real_restriction, integralFourier]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, bumpKernel, ContinuousLinearMap.lsmul_apply, zero_sub,
      inner_neg_left, Complex.ofReal_neg, RCLike.real_smul_eq_coe_mul]
    conv_lhs => rw [mul_comm]
    congr 2; ring
  simp only [heq] at h
  simpa [g] using h

/-- Restricting a regular Schwartz distribution cannot enlarge its support. -/
lemma euclideanSupport_regular {d : ℕ} (f : Schwartz ℂ d) :
    euclideanSupport (temperedRestriction (schwartzRegularDistribution f)) ⊆ tsupport f := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hs : distributionSupport (temperedRestriction (schwartzRegularDistribution f)) ⊆
      e.symm ⁻¹' tsupport f := by
    apply (support_subset_iff_vanishes _
      (isClosed_tsupport f |>.preimage e.symm.continuous)).mpr
    intro φ hφ
    rw [temperedRestriction_apply, Inversion.regular_distribution_pairing]
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport f
    · have hp : φ (e x) = 0 := by
        by_contra hn
        have ht := hφ (subset_tsupport φ hn)
        exact ht (by simpa only [Set.mem_preimage, e.symm_apply_apply] using hx)
      simp [Examples.testSchwartz, hp, e]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rintro _ ⟨x, hx, rfl⟩
  exact hs hx

/-- Inverse Fourier pairings for smooth compactly supported inverses, using
Schwartz duality rather than an interchange with a distribution. -/
lemma inverse_smooth_pairing {d : ℕ} {K : Set (Euclidean d)} (hK : IsCompact K)
    {f : Euclidean d → ℂ} (hf : SmoothSupportedIn K f)
    {G : ComplexEuclidean d → ℂ} (hG : PaleyWiener.fourierLaplace f = G)
    (φ : Schwartz ℂ d) :
    ∫ x, f x * φ x = ∫ ξ, G (realFrequency ξ) * (𝓕⁻ φ : Schwartz ℂ d) ξ := by
  let fS : Schwartz ℂ d := hf.hasCompactSupport hK |>.toSchwartzMap hf.1
  have heq (ξ : Euclidean d) : (𝓕 fS : Schwartz ℂ d) ξ = G (realFrequency ξ) := by
    rw [show (𝓕 fS : Schwartz ℂ d) ξ = integralFourier f ξ from
      schwartz_integral d fS ξ]
    rw [← PaleyWiener.real_restriction, hG]
  have h := SchwartzMap.integral_fourier_mul_eq fS (𝓕⁻ φ)
  change (∫ x, fS x * φ x) = _
  simpa only [heq, FourierTransform.fourier_fourierInv_eq] using h.symm

/-- A dominated-convergence bridge for the regularized inverses. -/
lemma regularized_pairing_tendsto {d : ℕ} {K : Set (Euclidean d)}
    (hne : K.Nonempty) (hK : IsCompact K) (hcK : Convex ℝ K)
    {F : ComplexEuclidean d → ℂ} (hF : Differentiable ℂ F)
    (hbound : PolynomialExponentialType K F)
    {b : ℕ → ContDiffBump (0 : Euclidean d)}
    (hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0))
    (φ : Schwartz ℂ d) :
    Filter.Tendsto (fun n => ∫ x,
      inverseRealIntegral (fun z => F z * PaleyWiener.fourierLaplace (bumpKernel (b n)) z) x * φ x)
      Filter.atTop (nhds (∫ ξ, F (realFrequency ξ) * (𝓕⁻ φ : Schwartz ℂ d) ξ)) := by
  obtain ⟨V, hV⟩ := real_axis_tempered d K hne F hF hbound
  have hi := (hV (𝓕⁻ φ)).1
  have hpoint n := regularized_inverse d K (Metric.closedBall 0 (b n).rOut)
    hne hK hcK ⟨0, Metric.mem_closedBall_self (b n).rOut_pos.le⟩
    (isCompact_closedBall ..) (convex_closedBall ..) F (bumpKernel (b n))
    hF hbound (bumpKernel_smoothSupportedIn (b n))
  have heq n := inverse_smooth_pairing (hK.add (isCompact_closedBall 0 (b n).rOut))
    (hpoint n).1 (hpoint n).2 φ
  simp_rw [heq]
  apply tendsto_integral_of_dominated_convergence
    (fun ξ => ‖F (realFrequency ξ) * (𝓕⁻ φ : Schwartz ℂ d) ξ‖)
  · intro n
    exact ((hF.continuous.comp (continuous_realFrequency d)).mul
      ((PaleyWiener.differentiable_fourierLaplace (isCompact_closedBall 0 (b n).rOut)
        (bumpKernel_smoothSupportedIn (b n))).continuous.comp (continuous_realFrequency d))).mul
        (𝓕⁻ φ : Schwartz ℂ d).continuous |>.aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [] with ξ
    simp only [norm_mul]
    calc
      _ ≤ (‖F (realFrequency ξ)‖ * 1) * ‖(𝓕⁻ φ : Schwartz ℂ d) ξ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (bumpKernel_transform_bound (b n) ξ) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  · filter_upwards [] with ξ
    simpa only [mul_one] using
      (tendsto_const_nhds.mul (bumpKernel_transform_tendsto hb ξ)).mul tendsto_const_nhds

/-- The support limit criterion in the Euclidean norm used by the type bounds. -/
lemma supportedIn_of_testwise_limit {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsClosed K) (u : Distribution d) (v : ℕ → Distribution d) (r : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hv : ∀ n, euclideanSupport (v n) ⊆ Metric.cthickening (r n) K)
    (hlim : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      Filter.Tendsto (fun n => v n φ) Filter.atTop (nhds (u φ))) :
    SupportedIn K u := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  change e.symm '' distributionSupport u ⊆ K
  rw [Set.image_subset_iff]
  apply (support_subset_iff_vanishes u (hK.preimage e.symm.continuous)).mpr
  intro φ hφ
  have hs : IsCompact (e.symm '' tsupport φ) :=
    φ.hasCompactSupport.image e.symm.continuous
  have hd : Disjoint (e.symm '' tsupport φ) K := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxK
    exact hφ hx hxK
  obtain ⟨δ, hδ, hdδ⟩ := hd.exists_cthickenings hs hK
  have hsmall : ∀ᶠ n in Filter.atTop, r n < δ := hr.eventually (gt_mem_nhds hδ)
  have hzero : ∀ᶠ n in Filter.atTop, v n φ = 0 := by
    filter_upwards [hsmall] with n hn
    apply (support_vanishing ℂ d ⊤ (v n)).2.2
    intro x hx
    by_contra hxn
    have hxs : e.symm x ∈ Metric.cthickening δ (e.symm '' tsupport φ) :=
      Metric.self_subset_cthickening _ (mem_image_of_mem _ hx)
    have hxK : e.symm x ∈ Metric.cthickening δ K :=
      Metric.cthickening_mono hn.le K (hv n
        (mem_image_of_mem e.symm ⟨Set.mem_univ x, hxn⟩))
    exact Set.disjoint_left.mp hdδ hxs hxK
  exact tendsto_nhds_unique (hlim φ)
    (tendsto_const_nhds.congr' (hzero.mono (fun _ h => h.symm)))

/-- A concrete sequence of probability bumps, valid also in dimension zero. -/
def shrinkingBump (d n : ℕ) : ContDiffBump (0 : Euclidean d) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

lemma shrinkingBump_rOut_tendsto (d : ℕ) :
    Filter.Tendsto (fun n => (shrinkingBump d n).rOut) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The inverse tempered distribution has support in the exact prescribed K.
This proves the support part of the polynomial-growth converse without presuming
any Fourier--Laplace representation for compact distributions. -/
theorem inverse_supported_tempered :
    Specs.ExpandedFA.Fourier.DistributionPaleyWiener.inverseSupportedTemperedType := by
  intro d K hne hK hcK F hF hb
  obtain ⟨V, hV⟩ := real_axis_tempered d K hne F hF hb
  obtain ⟨e, he, hei⟩ := Inversion.tempered_automorphism d
  let U := e.symm V
  let u := temperedRestriction U
  let b := shrinkingBump d
  let G (n : ℕ) := fun z => F z * PaleyWiener.fourierLaplace (bumpKernel (b n)) z
  let f (n : ℕ) := inverseRealIntegral (G n)
  have hf (n : ℕ) : SmoothSupportedIn (K + Metric.closedBall 0 (b n).rOut) (f n) ∧
      PaleyWiener.fourierLaplace (f n) = G n :=
    regularized_inverse d K (Metric.closedBall 0 (b n).rOut) hne hK hcK
      ⟨0, Metric.mem_closedBall_self (b n).rOut_pos.le⟩
      (isCompact_closedBall ..) (convex_closedBall ..) F (bumpKernel (b n)) hF hb
      (bumpKernel_smoothSupportedIn (b n))
  let fs (n : ℕ) : Schwartz ℂ d :=
    ((hf n).1.hasCompactSupport (hK.add (isCompact_closedBall ..))).toSchwartzMap (hf n).1.1
  let v (n : ℕ) := temperedRestriction (schwartzRegularDistribution (fs n))
  have hu : SupportedIn K u := by
    apply supportedIn_of_testwise_limit hK.isClosed u v (fun n => (b n).rOut)
      (shrinkingBump_rOut_tendsto d)
    · intro n
      apply subset_trans (euclideanSupport_regular (fs n))
      apply subset_trans (hf n).1.2
      rintro _ ⟨a, ha, y, hy, rfl⟩
      apply Metric.mem_cthickening_of_dist_le (a + y) a _ K ha
      simpa [dist_eq_norm, Metric.mem_closedBall, sub_eq_add_neg, add_assoc] using hy
    · intro φ
      have h := regularized_pairing_tendsto hne hK hcK hF hb
        (shrinkingBump_rOut_tendsto d) (Examples.testSchwartz ℂ φ)
      have huφ : u φ = ∫ ξ, F (realFrequency ξ) *
          (𝓕⁻ (Examples.testSchwartz ℂ φ) : Schwartz ℂ d) ξ := by
        change e.symm V (Examples.testSchwartz ℂ φ) = _
        rw [hei, (hV _).2]
      rw [huφ]
      exact h
  refine ⟨u, U, hu, fun _ => rfl, ?_⟩
  intro ψ
  have hUV : temperedFourier U = V := by
    change temperedFourier (e.symm V) = V
    rw [← he, e.apply_symm_apply]
  rw [hUV]
  exact hV ψ

/-- For a regular compactly supported Schwartz distribution, the canonical LF
transform equals the ordinary Fourier--Laplace integral. -/
lemma regular_fourierLaplace {d : ℕ} (f : Schwartz ℂ d) (hf : HasCompactSupport f) :
    DistributionPaleyWiener.fourierLaplace
      (temperedRestriction (schwartzRegularDistribution f)) = PaleyWiener.fourierLaplace f := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let u := temperedRestriction (schwartzRegularDistribution f)
  have hu : IsCompact (euclideanSupport u) :=
    hf.of_isClosed_subset (isClosed_euclideanSupport u) (euclideanSupport_regular f)
  have hS : IsCompact (e '' tsupport f) := hf.image e.continuous
  obtain ⟨χ, V, hV, hSV, hχ⟩ := cutoff_existence d (⊤ : Opens (Domain d))
    (e '' tsupport f) hS (subset_univ _)
  have hsV : distributionSupport u ⊆ V := by
    intro x hx
    apply hSV
    refine ⟨e.symm x, euclideanSupport_regular f (mem_image_of_mem e.symm hx), ?_⟩
    exact e.apply_symm_apply x
  have hcV : EqOn (scalarCutoff ℂ χ) 1 V := by
    intro x hx
    simp [scalarCutoff_apply, hχ hx]
  funext z
  obtain ⟨ψ, hψ, hval⟩ := cutoff d u hu (scalarCutoff ℂ χ) V hV hsV hcV z
  rw [hval]
  change schwartzRegularDistribution f (Examples.testSchwartz ℂ ψ) = _
  rw [Inversion.regular_distribution_pairing]
  apply integral_congr_ae
  filter_upwards [] with x
  change f x * ψ (e x) =
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * complexPairing x z) * f x
  by_cases hx : f x = 0
  · simp [hx]
  · have hχx : χ (e x) = 1 := hχ (hSV (mem_image_of_mem e (subset_tsupport f hx)))
    rw [hψ, scalarCutoff_apply, hχx]
    simp only [RCLike.ofReal_one, one_mul]
    change f x * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * complexPairing x z) = _
    exact mul_comm _ _

/-- The smooth inverses supplied by regularization also give genuine LF
distribution inverses, with the same exact complex transform. -/
theorem regularized_distribution_inverse :
    Specs.ExpandedFA.Fourier.DistributionPaleyWiener.regularizedDistributionInverseType := by
  intro d K L hneK hK hcK hneL hL hcL F ρ hF hb hρ
  let G := fun z => F z * PaleyWiener.fourierLaplace ρ z
  obtain ⟨hf, hG⟩ := regularized_inverse d K L hneK hK hcK hneL hL hcL F ρ hF hb hρ
  let f : Schwartz ℂ d := (hf.hasCompactSupport (hK.add hL)).toSchwartzMap hf.1
  refine ⟨temperedRestriction (schwartzRegularDistribution f), ?_, ?_, ?_⟩
  · exact (euclideanSupport_regular f).trans hf.2
  · exact (regular_fourierLaplace f (hf.hasCompactSupport (hK.add hL))).trans hG
  · intro φ
    exact Inversion.regular_distribution_pairing d f (Examples.testSchwartz ℂ φ)

lemma fourierLaplace_cutoff {d : ℕ} {u : Distribution d}
    (hu : IsCompact (euclideanSupport u))
    (χ : Tests ℂ (⊤ : Opens (Domain d))) (V : Set (Domain d))
    (hV : IsOpen V) (hs : distributionSupport u ⊆ V) (hχ : EqOn χ 1 V)
    (z : ComplexEuclidean d) :
    DistributionPaleyWiener.fourierLaplace u z = u (smoothCutoffCLM χ (laplaceKernel z)) := by
  obtain ⟨ψ, hψ, hv⟩ := cutoff d u hu χ V hV hs hχ z
  rw [hv]
  congr 1
  ext x
  exact (hψ x).trans (mul_comm _ _)

/-- On distributions with one common compact support, weak convergence implies
pointwise convergence of their complex Fourier--Laplace transforms. -/
lemma fourierLaplace_tendsto_of_common_support {d : ℕ}
    {K : Set (Euclidean d)} (hK : IsCompact K)
    {u : Distribution d} {v : ℕ → Distribution d}
    (hu : SupportedIn K u) (hv : ∀ n, SupportedIn K (v n))
    (hlim : ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      Filter.Tendsto (fun n => v n φ) Filter.atTop (nhds (u φ)))
    (z : ComplexEuclidean d) :
    Filter.Tendsto (fun n => DistributionPaleyWiener.fourierLaplace (v n) z)
      Filter.atTop (nhds (DistributionPaleyWiener.fourierLaplace u z)) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  obtain ⟨χ, V, hV, hKV, hχ⟩ := cutoff_existence d (⊤ : Opens (Domain d))
    (e '' K) (hK.image e.continuous) (subset_univ _)
  have hs (w : Distribution d) (hw : SupportedIn K w) : distributionSupport w ⊆ V := by
    intro x hx
    apply hKV
    exact ⟨e.symm x, hw (mem_image_of_mem e.symm hx), e.apply_symm_apply x⟩
  have hc : EqOn (scalarCutoff ℂ χ) 1 V := by
    intro x hx
    simp [scalarCutoff_apply, hχ hx]
  have heq (w : Distribution d) (hw : SupportedIn K w) :=
    fourierLaplace_cutoff (isCompact_euclideanSupport_of_supportedIn hK hw)
      (scalarCutoff ℂ χ) V hV (hs w hw) hc z
  simp_rw [heq u hu, fun n => heq (v n) (hv n)]
  exact hlim _

lemma bumpKernel_transform_tendsto_complex {d : ℕ} {b : ℕ → ContDiffBump (0 : Euclidean d)}
    (hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0))
    (z : ComplexEuclidean d) :
    Filter.Tendsto (fun n => PaleyWiener.fourierLaplace (bumpKernel (b n)) z)
      Filter.atTop (nhds 1) := by
  let g : Euclidean d → ℂ := fun x => Complex.exp (-spatialExponentCLM z x)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) hb hg 0
  have heq (n : ℕ) :
      MeasureTheory.convolution ((b n).normed volume) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 =
      PaleyWiener.fourierLaplace (bumpKernel (b n)) z := by
    rw [MeasureTheory.convolution, PaleyWiener.fourierLaplace]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [g, bumpKernel, ContinuousLinearMap.lsmul_apply, zero_sub,
      map_neg, neg_neg, RCLike.real_smul_eq_coe_mul]
    rw [spatialExponentCLM_apply]
    exact mul_comm _ _
  simp only [heq] at h
  simpa [g] using h

lemma shrinkingBump_rOut_le_one (d n : ℕ) : (shrinkingBump d n).rOut ≤ 1 := by
  change 1 / ((n : ℝ) + 1) ≤ 1
  apply (div_le_one (by positivity)).mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

/-- Existence with the exact complex transform. Uniqueness is independent. -/
theorem inverse_exists :
    Specs.ExpandedFA.Fourier.DistributionPaleyWiener.inverseExistenceType := by
  intro d K hne hK hcK F hF hb
  obtain ⟨u, U, hu, hU, hpair⟩ := inverse_supported_tempered d K hne hK hcK F hF hb
  let b := shrinkingBump d
  let G (n : ℕ) := fun z => F z * PaleyWiener.fourierLaplace (bumpKernel (b n)) z
  have hv (n : ℕ) := regularized_distribution_inverse d K (Metric.closedBall 0 (b n).rOut)
    hne hK hcK ⟨0, Metric.mem_closedBall_self (b n).rOut_pos.le⟩
    (isCompact_closedBall ..) (convex_closedBall ..) F (bumpKernel (b n)) hF hb
    (bumpKernel_smoothSupportedIn (b n))
  choose v hvs hvF hvpair using hv
  have hlim (φ : Tests ℂ (⊤ : Opens (Domain d))) :
      Filter.Tendsto (fun n => v n φ) Filter.atTop (nhds (u φ)) := by
    have huφ : u φ = ∫ ξ, F (realFrequency ξ) *
        (𝓕⁻ (Examples.testSchwartz ℂ φ) : Schwartz ℂ d) ξ := by
      rw [hU]
      have h := (hpair (𝓕⁻ (Examples.testSchwartz ℂ φ))).2
      change U (𝓕 (𝓕⁻ (Examples.testSchwartz ℂ φ) : Schwartz ℂ d)) = _ at h
      simpa only [FourierTransform.fourier_fourierInv_eq] using h
    simp_rw [hvpair, huφ]
    exact regularized_pairing_tendsto hne hK hcK hF hb
      (shrinkingBump_rOut_tendsto d) (Examples.testSchwartz ℂ φ)
  have huA : SupportedIn (K + Metric.closedBall 0 1) u := by
    intro x hx
    exact ⟨x, hu hx, 0, Metric.mem_closedBall_self zero_le_one, by simp⟩
  have hvA (n : ℕ) : SupportedIn (K + Metric.closedBall 0 1) (v n) := by
    intro x hx
    rcases hvs n hx with ⟨a, ha, y, hy, rfl⟩
    exact ⟨a, ha, y, Metric.closedBall_subset_closedBall (shrinkingBump_rOut_le_one d n) hy, rfl⟩
  refine ⟨u, hu, ?_⟩
  funext z
  have hleft := fourierLaplace_tendsto_of_common_support
    (hK.add (isCompact_closedBall 0 1)) huA hvA hlim z
  have hright : Filter.Tendsto
      (fun n => DistributionPaleyWiener.fourierLaplace (v n) z)
      Filter.atTop (nhds (F z)) := by
    simp_rw [hvF]
    simpa only [mul_one] using tendsto_const_nhds.mul
      (bumpKernel_transform_tendsto_complex (shrinkingBump_rOut_tendsto d) z)
  exact tendsto_nhds_unique hleft hright


@[simp] lemma compactJetMap_apply {d : ℕ}
    (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d)))) (f : Smooth d)
    (a : s) (x : a.val.1.1.val) :
    compactJetMap s f a x = iteratedFDeriv ℝ a.val.1.2 f.val x
      (fun j => coordinateVector (a.val.2 j)) := rfl

lemma laplaceKernel_real_norm {d : ℕ} (ξ : Euclidean d) (x : Domain d) :
    ‖(laplaceKernel (realFrequency ξ)).val x‖ = 1 := by
  change ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
    complexPairing ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (realFrequency ξ))‖ = 1
  rw [kernel_norm, imaginaryPart_realFrequency]
  simp

lemma coordinate_kernel_coefficient_bound {d n : ℕ} (a : Fin n → Fin d) (ξ : Euclidean d) :
    ‖∏ j, (-2 * (Real.pi : ℂ) * Complex.I * realFrequency ξ (a j))‖ ≤
      (2 * Real.pi) ^ n * ‖ξ‖ ^ n := by
  calc
    _ = ∏ j, 2 * Real.pi * ‖ξ (a j)‖ := by
      simp [norm_prod, norm_neg, realFrequency]
    _ ≤ ∏ _j : Fin n, 2 * Real.pi * ‖ξ‖ := by
      apply Finset.prod_le_prod₀
      · intro j _; positivity
      · intro j _; exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ (a j)) (by positivity)
    _ = _ := by simp [mul_pow]

lemma compactJetKernel_continuous {d : ℕ}
    (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d)))) :
    Continuous (fun ξ : Euclidean d => compactJetMap s (laplaceKernel (realFrequency ξ))) := by
  apply continuous_pi
  intro a
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Euclidean d × a.val.1.1.val =>
    iteratedFDeriv ℝ a.val.1.2 (laplaceKernel (realFrequency p.1)).val p.2
      (fun j => coordinateVector (a.val.2 j)))
  simp_rw [laplaceKernel_coordinate_derivative]
  simp only [laplaceKernel, realFrequency, Complex.ofRealCLM_apply]
  have hξ (i : Fin d) : Continuous (fun p : Euclidean d × a.val.1.1.val => p.1 i) :=
    (PiLp.continuous_apply 2 _ i).comp continuous_fst
  have hy (i : Fin d) : Continuous (fun p : Euclidean d × a.val.1.1.val => (p.2 : Domain d) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  apply Continuous.mul
  · exact continuous_finsetProd _ fun j _ => continuous_const.mul
      (Complex.continuous_ofReal.comp (hξ _))
  · apply Complex.continuous_exp.comp
    apply continuous_const.mul
    exact continuous_finsetSum _ fun j _ =>
      (Complex.continuous_ofReal.comp (hy j)).mul (Complex.continuous_ofReal.comp (hξ j))

lemma compactJetKernel_integrable {d : ℕ}
    (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d)))) (φ : Schwartz ℂ d) :
    Integrable (fun ξ : Euclidean d => φ ξ • compactJetMap s (laplaceKernel (realFrequency ξ))) := by
  apply integrable_pi_iff.mpr
  intro a
  apply ((φ.integrable_pow_mul volume a.val.1.2).const_mul ((2 * Real.pi) ^ a.val.1.2)).mono'
    ((φ.continuous.smul ((continuous_apply a).comp (compactJetKernel_continuous s))).aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖φ ξ • compactJetMap s (laplaceKernel (realFrequency ξ)) a‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖φ ξ‖ * ((2 * Real.pi) ^ a.val.1.2 * ‖ξ‖ ^ a.val.1.2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro x
      rw [compactJetMap_apply, laplaceKernel_coordinate_derivative, norm_mul, laplaceKernel_real_norm, mul_one]
      exact coordinate_kernel_coefficient_bound a.val.2 ξ
    _ = _ := by ring


def euclideanSchwartzToSmooth {d : ℕ} (φ : Schwartz ℂ d) : Smooth d :=
  Examples.schwartzToSmooth ℂ d
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin d) ℝ).symm φ)

set_option maxHeartbeats 1000000 in
lemma fourier_coordinate_derivative_integral {d n : ℕ} (φ : Schwartz ℂ d)
    (x : Domain d) (a : Fin n → Fin d) :
    iteratedFDeriv ℝ n (euclideanSchwartzToSmooth (𝓕 φ)).val x
        (fun j => coordinateVector (a j)) =
      ∫ ξ, φ ξ * (∏ j, (-2 * (Real.pi : ℂ) * Complex.I * realFrequency ξ (a j))) *
        (laplaceKernel (realFrequency ξ)).val x := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  change iteratedFDeriv ℝ n (((𝓕 φ : Schwartz ℂ d) : Euclidean d → ℂ) ∘ e.toContinuousLinearMap) x
    (fun j => coordinateVector (a j)) = _
  rw [e.toContinuousLinearMap.iteratedFDeriv_comp_right ((𝓕 φ : Schwartz ℂ d).smooth ⊤) x (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ n (𝓕 (φ : Euclidean d → ℂ)) (e x)
    (fun j => e (coordinateVector (a j))) = _
  rw [Real.iteratedFDeriv_fourier
    (N := ⊤) (fun k _ => φ.integrable_pow_mul volume k)
    φ.continuous.aestronglyMeasurable (by simp)]
  rw [Real.fourier_continuousMultilinearMap_apply
    (VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ)
      (φ.integrable_pow_mul volume n) φ.continuous.aestronglyMeasurable)]
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [VectorFourier.fourierPowSMulRight_apply, smul_eq_mul]
  have hinner (j : Fin n) : inner ℝ ξ (e (coordinateVector (a j))) = ξ (a j) := by
    change inner ℝ ξ (EuclideanSpace.single (a j) 1) = _
    simp [EuclideanSpace.inner_single_right]
  have hexp : Complex.exp ((↑(-2 * Real.pi * inner ℝ ξ (e x)) * Complex.I)) =
      (laplaceKernel (realFrequency ξ)).val x := by
    change _ = Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * complexPairing (e x) (realFrequency ξ))
    rw [complexPairing_realFrequency, real_inner_comm ξ (e x)]
    congr 1
    push_cast
    ring
  rw [hexp]
  have hinner' (j : Fin n) : ((innerSL ℝ) ξ) (e (coordinateVector (a j))) = ξ (a j) := hinner j
  simp_rw [hinner']
  simp only [RCLike.real_smul_eq_coe_mul]
  simp only [realFrequency, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring_nf
  ac_rfl

lemma compactJetMap_fourier_integral {d : ℕ}
    (s : Finset (SmoothCoordinateIndex (⊤ : Opens (Domain d)))) (φ : Schwartz ℂ d) :
    compactJetMap s (euclideanSchwartzToSmooth (𝓕 φ)) =
      ∫ ξ, φ ξ • compactJetMap s (laplaceKernel (realFrequency ξ)) := by
  ext a x
  let ev : CompactJetSpace s →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ x).comp (ContinuousLinearMap.proj a)
  have h := ev.integral_comp_comm (compactJetKernel_integrable s φ)
  change _ = ev (∫ ξ, φ ξ • compactJetMap s (laplaceKernel (realFrequency ξ)))
  rw [← h]
  simp only [ev, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousMap.evalCLM_apply, Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul,
    compactJetMap_apply, laplaceKernel_coordinate_derivative]
  simpa only [mul_assoc] using fourier_coordinate_derivative_integral φ x a.val.2


lemma smooth_functional_fourier_integral {d : ℕ} (l : Smooth d →L[ℂ] ℂ)
    (φ : Schwartz ℂ d) :
    Integrable (fun ξ => l (laplaceKernel (realFrequency ξ)) * φ ξ) ∧
      l (euclideanSchwartzToSmooth (𝓕 φ)) =
        ∫ ξ, l (laplaceKernel (realFrequency ξ)) * φ ξ := by
  obtain ⟨s, L, hL⟩ := smooth_functional_compactJet_factorization l
  have heq (ξ : Euclidean d) : L (φ ξ • compactJetMap s (laplaceKernel (realFrequency ξ))) =
      l (laplaceKernel (realFrequency ξ)) * φ ξ := by
    rw [map_smul, hL, smul_eq_mul, mul_comm]
  constructor
  · exact (L.integrable_comp (compactJetKernel_integrable s φ)).congr
      (Filter.Eventually.of_forall heq)
  · rw [← hL, compactJetMap_fourier_integral,
      ← L.integral_comp_comm (compactJetKernel_integrable s φ)]
    exact integral_congr_ae (Filter.Eventually.of_forall heq)

@[simp] lemma euclideanSchwartzToSmooth_testSchwartz {d : ℕ}
    (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    euclideanSchwartzToSmooth (Examples.testSchwartz ℂ φ) = testToSmoothLM ℂ ⊤ φ := by
  apply Subtype.ext
  funext x
  change φ ((EuclideanSpace.equiv (Fin d) ℝ) ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) = φ x
  rw [ContinuousLinearEquiv.apply_symm_apply]

lemma distribution_fourier_pairing {d : ℕ} (u : Distribution d)
    (hu : IsCompact (euclideanSupport u)) (φ : Tests ℂ (⊤ : Opens (Domain d))) :
    u φ = ∫ ξ, DistributionPaleyWiener.fourierLaplace u (realFrequency ξ) *
      (𝓕⁻ (Examples.testSchwartz ℂ φ) : Schwartz ℂ d) ξ := by
  have h := (smooth_functional_fourier_integral (smoothExtension u)
    (𝓕⁻ (Examples.testSchwartz ℂ φ))).2
  rw [FourierTransform.fourier_fourierInv_eq, euclideanSchwartzToSmooth_testSchwartz,
    extension d u hu φ] at h
  exact h

theorem injectivity : Specs.ExpandedFA.Fourier.DistributionPaleyWiener.injectivityType := by
  intro d u v hu hv h
  ext φ
  rw [distribution_fourier_pairing u hu φ, distribution_fourier_pairing v hv φ, h]



/-- Full converse, including uniqueness of the supported inverse distribution. -/
theorem inverse : Specs.ExpandedFA.Fourier.DistributionPaleyWiener.inverseType := by
  intro d K hne hK hcK F hF hb
  obtain ⟨u, hu, htransform⟩ := inverse_exists d K hne hK hcK F hF hb
  refine ⟨u, ⟨hu, htransform⟩, ?_⟩
  intro v hv
  exact injectivity d v u (isCompact_euclideanSupport_of_supportedIn hK hv.1)
    (isCompact_euclideanSupport_of_supportedIn hK hu) (hv.2.trans htransform.symm)

/-- The real restriction of a compact distribution transform represents the
Fourier transform of its actual tempered extension. -/
lemma compact_distribution_tempered_representation {d : ℕ} (u : Distribution d)
    (hu : IsCompact (euclideanSupport u)) :
    ∃ U : Tempered ℂ d,
      (∀ φ : Tests ℂ (⊤ : Opens (Domain d)), u φ = U (Examples.testSchwartz ℂ φ)) ∧
      ∀ φ : Schwartz ℂ d,
        Integrable (fun ξ => DistributionPaleyWiener.fourierLaplace u (realFrequency ξ) * φ ξ) ∧
        temperedFourier U φ = ∫ ξ,
          DistributionPaleyWiener.fourierLaplace u (realFrequency ξ) * φ ξ := by
  let P : Schwartz ℂ d →L[ℂ] SchwartzMap (Domain d) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin d) ℝ).symm
  let U : Tempered ℂ d := (smoothExtension u).comp ((Examples.schwartzToSmooth ℂ d).comp P)
  refine ⟨U, ?_, ?_⟩
  · intro φ
    change u φ = smoothExtension u (euclideanSchwartzToSmooth (Examples.testSchwartz ℂ φ))
    rw [euclideanSchwartzToSmooth_testSchwartz, extension d u hu φ]
  · intro φ
    exact smooth_functional_fourier_integral (smoothExtension u) φ


lemma smoothTransition_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ n Real.smoothTransition t‖ ≤ C := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, by positivity, fun t => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact Real.smoothTransition.le_one t
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 2)).exists_bound_of_continuousOn
      ((Real.smoothTransition.contDiff (n := ⊤)).continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
    refine ⟨max 0 C, le_max_left _ _, fun t => ?_⟩
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 2
    · exact (hC t ht).trans (le_max_right _ _)
    · have hz : iteratedFDeriv ℝ n Real.smoothTransition t = 0 := by
        have ht' : t < -1 ∨ 2 < t := by simpa only [Set.mem_Icc, not_and_or, not_le] using ht
        rcases ht' with ht | ht
        · have heq : Real.smoothTransition =ᶠ[nhds t] fun _ => (0 : ℝ) := by
            filter_upwards [eventually_lt_nhds (show t < 0 by linarith)] with y hy
            exact Real.smoothTransition.zero_of_nonpos hy.le
          rw [(heq.iteratedFDeriv ℝ n).self_of_nhds,
            iteratedFDeriv_const_of_ne hn (0 : ℝ)]
          rfl
        · have heq : Real.smoothTransition =ᶠ[nhds t] fun _ => (1 : ℝ) := by
            filter_upwards [eventually_gt_nhds (show (1 : ℝ) < t by linarith)] with y hy
            exact Real.smoothTransition.one_of_one_le hy.le
          rw [(heq.iteratedFDeriv ℝ n).self_of_nhds,
            iteratedFDeriv_const_of_ne hn (1 : ℝ)]
          rfl
      rw [hz, norm_zero]
      exact le_max_left _ _


lemma norm_smoothTransition_affine_derivative_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) {B : ℝ}
    (hB : ∀ t : ℝ, ‖iteratedFDeriv ℝ n Real.smoothTransition t‖ ≤ B)
    (a : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => Real.smoothTransition (a + L y)) x‖ ≤ B * ‖L‖ ^ n := by
  let f : ℝ → ℝ := fun t => Real.smoothTransition (a + t)
  have hf : ContDiff ℝ ∞ f := by
    exact Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf x (mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
    _ ≤ B * ‖L‖ ^ n := by
      gcongr
      simpa only [f, iteratedFDeriv_comp_add_left] using hB (a + L x)

lemma norm_imaginaryPart_le {d : ℕ} (z : ComplexEuclidean d) :
    ‖imaginaryPart z‖ ≤ ‖z‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  rw [← pow_two, ← pow_two]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  change ‖(z j).im‖ ^ 2 ≤ ‖z j‖ ^ 2
  exact pow_le_pow_left₀ (by positivity) (Complex.abs_im_le_norm _) _


lemma cutoff_kernel_derivative_bound_general {d : ℕ} (χ : Domain d → ℂ)
    (hχ : ContDiff ℝ ∞ χ)
    (E : ℝ) (hE : 0 ≤ E) (z : ComplexEuclidean d)
    (hs : ∀ x ∈ tsupport χ, ‖(laplaceKernel z).val x‖ ≤ E)
    (n : ℕ) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i)
    (hb : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ A i)
    (x : Domain d) :
    ‖iteratedFDeriv ℝ n (fun x => χ x * (laplaceKernel z).val x) x‖ ≤
      E *
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i *
        ‖coordinateSpatialExponent z‖ ^ (n - i) := by
  have hk : ContDiff ℝ ∞ (laplaceKernel z).val := by
    change ContDiff ℝ ∞ (fun x : Domain d => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ∑ j, Complex.ofRealCLM (x j) * z j))
    fun_prop
  apply (norm_iteratedFDeriv_mul_le hχ hk x (by simp)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  by_cases hz : iteratedFDeriv ℝ i χ x = 0
  · simp only [hz, norm_zero, mul_zero, zero_mul]
    have hai := hA i
    positivity
  · have hxs : x ∈ tsupport χ := support_iteratedFDeriv_subset i hz
    have hkn := (laplaceKernel_derivative_bound z (n - i) x)
    have hke := hs x hxs
    have hkn' : ‖iteratedFDeriv ℝ (n - i) (laplaceKernel z).val x‖ ≤
        E *
          ‖coordinateSpatialExponent z‖ ^ (n - i) := by
      apply hkn.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      convert hke using 1
      change Real.exp _ = ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        complexPairing ((EuclideanSpace.equiv (Fin d) ℝ).symm x) z)‖
      rw [kernel_norm]
    calc
      _ ≤ (n.choose i : ℝ) * A i *
        (E *
          ‖coordinateSpatialExponent z‖ ^ (n - i)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i hin x) (by positivity))
          hkn' (norm_nonneg _) (mul_nonneg (by positivity) (hA i))
      _ = _ := by ring



lemma cutoff_kernel_derivative_uniform_polynomial {d : ℕ}
    (χ : Domain d → ℂ) (hχ : ContDiff ℝ ∞ χ) (z : ComplexEuclidean d)
    (N : ℕ) (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hb : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ A * (1 + ‖z‖) ^ N)
    (hs : ∀ x ∈ tsupport χ, ‖(laplaceKernel z).val x‖ ≤ E)
    {n : ℕ} (hn : n ≤ N) (x : Domain d) :
    ‖iteratedFDeriv ℝ n (fun x => χ x * (laplaceKernel z).val x) x‖ ≤
      ((2 : ℝ) ^ N * A * (1 + ‖coordinateSpatialExponentCLM d‖) ^ N) *
        (1 + ‖z‖) ^ (2 * N) * E := by
  let T := 1 + ‖z‖
  let B := (1 + ‖coordinateSpatialExponentCLM d‖) ^ N
  have hsumb : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (A * T ^ N) * ‖coordinateSpatialExponent z‖ ^ (n - i)) ≤
      (2 : ℝ) ^ N * (A * T ^ N) * (B * T ^ N) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (A * T ^ N) * (B * T ^ N) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact coordinateSpatialExponent_pow_bound z ((Nat.sub_le n i).trans hn)
      _ = (2 : ℝ) ^ n * (A * T ^ N) * (B * T ^ N) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose n
      _ ≤ _ := by gcongr; norm_num
  have hmain := cutoff_kernel_derivative_bound_general χ hχ E hE z hs n
    (fun _ => A * T ^ N) (fun _ => by positivity) (fun i hi => hb i (hi.trans hn)) x
  calc
    _ ≤ E * ((2 : ℝ) ^ N * (A * T ^ N) * (B * T ^ N)) :=
      hmain.trans (mul_le_mul_of_nonneg_left hsumb hE)
    _ = _ := by dsimp [T, B]; rw [two_mul, pow_add]; ring

lemma polynomialExponentialType_of_cutoff_family {d : ℕ} {K : Set (Euclidean d)}
    (L : Smooth d →L[ℂ] ℂ) (χ : ComplexEuclidean d → Domain d → ℂ)
    (G : ComplexEuclidean d → Smooth d)
    (hχ : ∀ z, ContDiff ℝ ∞ (χ z))
    (hG : ∀ z x, (G z).val x = χ z x * (laplaceKernel z).val x)
    (hLG : ∀ z, L (G z) = L (laplaceKernel z))
    (E : ℝ) (hE : 0 ≤ E)
    (hs : ∀ z x, x ∈ tsupport (χ z) → ‖(laplaceKernel z).val x‖ ≤
      E * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)))
    (hb : ∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z i, i ≤ N → ∀ x,
      ‖iteratedFDeriv ℝ i (χ z) x‖ ≤ A * (1 + ‖z‖) ^ N) :
    PolynomialExponentialType K (fun z => L (laplaceKernel z)) := by
  classical
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
    (smooth_withSeminorms (𝕜 := ℂ) (Ω := (⊤ : Opens (Domain d))))
    ((normSeminorm ℂ ℂ).comp L.toLinearMap) L.continuous.norm
  let N : ℕ := s.sup fun q => q.2
  obtain ⟨A, hA, hb⟩ := hb N
  let B : ℝ := (2 : ℝ) ^ N * A * (1 + ‖coordinateSpatialExponentCLM d‖) ^ N
  refine ⟨2 * N, (C : ℝ) * B * E, by positivity, fun z => ?_⟩
  have hjet (q : SmoothJetIndex (⊤ : Opens (Domain d))) (hq : q ∈ s) :
      smoothSeminorm ℂ ⊤ q (G z) ≤ B * (1 + ‖z‖) ^ (2 * N) *
        (E * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z))) := by
    change ‖smoothJetLM ℂ ⊤ q (G z)‖ ≤ _
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    change ‖iteratedFDeriv ℝ q.2 (G z).val x‖ ≤ _
    have heq : (G z).val = fun x => χ z x * (laplaceKernel z).val x := funext (hG z)
    rw [heq]
    exact cutoff_kernel_derivative_uniform_polynomial (χ z) (hχ z) z N A
      (E * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z))) hA
      (by positivity) (hb z) (hs z)
      (Finset.le_sup (f := fun q : SmoothJetIndex (⊤ : Opens (Domain d)) => q.2) hq) x
  dsimp only
  rw [← hLG]
  calc
    _ ≤ (C : ℝ) * (s.sup (smoothSeminorm ℂ (⊤ : Opens (Domain d)))) (G z) := hC _
    _ ≤ (C : ℝ) * (B * (1 + ‖z‖) ^ (2 * N) *
        (E * Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)))) := by
      apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
      exact Seminorm.finset_sup_apply_le (by positivity) hjet
    _ = _ := by ring

def coordinateInner {d : ℕ} (η : Euclidean d) : Domain d →L[ℝ] ℝ :=
  (innerSL ℝ η).comp (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap

lemma coordinateInner_apply {d : ℕ} (η : Euclidean d) (x : Domain d) :
    coordinateInner η x = inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) η := by
  change inner ℝ η ((EuclideanSpace.equiv (Fin d) ℝ).symm x) = _
  exact real_inner_comm _ _

def halfspaceCutoff {d : ℕ} (K : Set (Euclidean d))
    (χ : Tests ℂ (⊤ : Opens (Domain d))) (z : ComplexEuclidean d) :
    Tests ℂ (⊤ : Opens (Domain d)) where
  toFun x := χ x * Complex.ofRealCLM (Real.smoothTransition
    (supportFunction K (imaginaryPart z) + 2 -
      inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z)))
  contDiff' := by
    apply χ.contDiff.mul
    apply Complex.ofRealCLM.contDiff.comp
    have hi : ContDiff ℝ ∞ (fun x => Real.smoothTransition
        (supportFunction K (imaginaryPart z) + 2 - coordinateInner (imaginaryPart z) x)) :=
      Real.smoothTransition.contDiff.comp
        (contDiff_const.sub (coordinateInner (imaginaryPart z)).contDiff)
    simpa only [coordinateInner_apply] using hi
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := subset_univ _

lemma halfspaceCutoff_eq_one {d : ℕ} {K : Set (Euclidean d)}
    (χ : Tests ℂ (⊤ : Opens (Domain d))) (z : ComplexEuclidean d)
    {V : Set (Domain d)} (hχ : EqOn χ 1 V) :
    EqOn (halfspaceCutoff K χ z) 1
      (V ∩ {x | inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z) <
        supportFunction K (imaginaryPart z) + 1}) := by
  intro x hx
  change χ x * Complex.ofRealCLM _ = 1
  have hx' := hx.2
  change inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z) <
    supportFunction K (imaginaryPart z) + 1 at hx'
  rw [hχ hx.1, Real.smoothTransition.one_of_one_le (by linarith)]
  simp

lemma halfspaceCutoff_tsupport {d : ℕ} (K : Set (Euclidean d))
    (χ : Tests ℂ (⊤ : Opens (Domain d))) (z : ComplexEuclidean d) :
    tsupport (halfspaceCutoff K χ z) ⊆
      {x | inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z) ≤
        supportFunction K (imaginaryPart z) + 2} := by
  apply closure_minimal _ (isClosed_le (by fun_prop) continuous_const)
  intro x hx
  by_contra h
  change ¬ inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z) ≤
    supportFunction K (imaginaryPart z) + 2 at h
  have hz : Real.smoothTransition (supportFunction K (imaginaryPart z) + 2 -
      inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith [lt_of_not_ge h])
  apply hx
  change χ x * Complex.ofRealCLM _ = 0
  rw [hz]
  simp

lemma halfspaceCutoff_formula {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsCompact K) {u : Distribution d} (hu : SupportedIn K u)
    (χ : Tests ℂ (⊤ : Opens (Domain d))) (V : Set (Domain d))
    (hV : IsOpen V) (hsV : distributionSupport u ⊆ V) (hχ : EqOn χ 1 V)
    (z : ComplexEuclidean d) :
    DistributionPaleyWiener.fourierLaplace u z =
      u (smoothCutoffCLM (halfspaceCutoff K χ z) (laplaceKernel z)) := by
  let W := V ∩ {x : Domain d |
    inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z) <
      supportFunction K (imaginaryPart z) + 1}
  have hW : IsOpen W := hV.inter (isOpen_lt (by fun_prop) continuous_const)
  have huW : distributionSupport u ⊆ W := by
    intro x hx
    refine ⟨hsV hx, ?_⟩
    have h := inner_le_supportFunction hK
      (hu (mem_image_of_mem (EuclideanSpace.equiv (Fin d) ℝ).symm hx)) (imaginaryPart z)
    change inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm x) (imaginaryPart z) <
      supportFunction K (imaginaryPart z) + 1
    linarith
  exact fourierLaplace_cutoff (isCompact_euclideanSupport_of_supportedIn hK hu)
    (halfspaceCutoff K χ z) W hW huW (halfspaceCutoff_eq_one χ z hχ) z


lemma halfspaceCutoff_kernel_bound {d : ℕ} (K : Set (Euclidean d))
    (χ : Tests ℂ (⊤ : Opens (Domain d))) (z : ComplexEuclidean d)
    (x : Domain d) (hx : x ∈ tsupport (halfspaceCutoff K χ z)) :
    ‖(laplaceKernel z).val x‖ ≤ Real.exp (4 * Real.pi) *
      Real.exp (2 * Real.pi * supportFunction K (imaginaryPart z)) := by
  have hi := halfspaceCutoff_tsupport K χ z hx
  change ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
    complexPairing ((EuclideanSpace.equiv (Fin d) ℝ).symm x) z)‖ ≤ _
  rw [kernel_norm]
  calc
    _ ≤ Real.exp (2 * Real.pi * (supportFunction K (imaginaryPart z) + 2)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


lemma coordinateInner_norm_le {d : ℕ} (η : Euclidean d) :
    ‖coordinateInner η‖ ≤ ‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖ * ‖η‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [coordinateInner_apply, Real.norm_eq_abs]
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin d) ℝ).symm x‖ * ‖η‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖ * ‖x‖) * ‖η‖ := by
      gcongr
      exact (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.le_opNorm x
    _ = _ := by ring

lemma affine_transition_cutoff_derivative_family {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z]
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : Z → ℝ) (L : Z → E →L[ℝ] ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hL : ∀ z, ‖L z‖ ≤ D * ‖z‖) :
    ∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z i, i ≤ N → ∀ x,
      ‖iteratedFDeriv ℝ i
        (fun y => χ y * (Real.smoothTransition (a z + L z y) : ℂ)) x‖ ≤
          A * (1 + ‖z‖) ^ N := by
  classical
  have hχb (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hχ.continuous_iteratedFDeriv (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
      ((hcχ.iteratedFDeriv (𝕜 := ℝ) i).comp_left norm_zero)
    exact ⟨max C 0, le_max_right _ _, fun x => (hC (mem_range_self _)).trans (le_max_left _ _)⟩
  choose C hC hCb using hχb
  choose B hB hBb using smoothTransition_derivative_bound
  intro N
  let C0 := ∑ i ∈ Finset.range (N + 1), C i
  let B0 := ∑ i ∈ Finset.range (N + 1), B i
  have hC0 : 0 ≤ C0 := Finset.sum_nonneg (fun i _ => hC i)
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg (fun i _ => hB i)
  have hCN (i : ℕ) (hi : i ≤ N) (x : E) : ‖iteratedFDeriv ℝ i χ x‖ ≤ C0 := by
    exact (hCb i x).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega)))
  have hBN (i : ℕ) (hi : i ≤ N) (t : ℝ) : ‖iteratedFDeriv ℝ i Real.smoothTransition t‖ ≤ B0 := by
    exact (hBb i t).trans (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega)))
  refine ⟨(2 : ℝ)^N * C0 * (B0 * (1 + D)^N), by positivity, fun z n hn x => ?_⟩
  have hg : ContDiff ℝ ∞ (fun y : E => (Real.smoothTransition (a z + L z y) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.smoothTransition.contDiff.comp (contDiff_const.add (L z).contDiff))
  have hgb (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun y : E => (Real.smoothTransition (a z + L z y) : ℂ)) x‖ ≤
        B0 * (1 + D)^N * (1 + ‖z‖)^N := by
    have hs : ContDiff ℝ ∞ (fun y : E => Real.smoothTransition (a z + L z y)) :=
      Real.smoothTransition.contDiff.comp (contDiff_const.add (L z).contDiff)
    change ‖iteratedFDeriv ℝ i (Complex.ofRealLI ∘ (fun y : E => Real.smoothTransition (a z + L z y))) x‖ ≤ _
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hs.contDiffAt (mod_cast le_top)]
    apply (norm_smoothTransition_affine_derivative_le i (hBN i hi) (a z) (L z) x).trans
    have hp : ‖L z‖ ^ i ≤ (1 + D)^N * (1 + ‖z‖)^N := by
      calc
        _ ≤ ((1 + D) * (1 + ‖z‖)) ^ i := by
          gcongr
          exact (hL z).trans (by nlinarith [norm_nonneg z])
        _ ≤ ((1 + D) * (1 + ‖z‖)) ^ N :=
          pow_le_pow_right₀ (by nlinarith [norm_nonneg z]) hi
        _ = _ := mul_pow _ _ _
    exact (mul_le_mul_of_nonneg_left hp hB0).trans_eq (by ring)
  apply (norm_iteratedFDeriv_mul_le hχ hg x (mod_cast le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C0 *
        (B0 * (1 + D)^N * (1 + ‖z‖)^N) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hCN i (hin.trans hn) x) (by positivity))
        (hgb (n-i) ((Nat.sub_le n i).trans hn)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^n * C0 * (B0 * (1 + D)^N) * (1 + ‖z‖)^N := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hc : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = (2 : ℝ)^n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hc]
      ring
    _ ≤ _ := by
      have hpow : (2 : ℝ)^n ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hn
      gcongr

lemma halfspaceCutoff_derivative_family {d : ℕ} (K : Set (Euclidean d))
    (χ : Tests ℂ (⊤ : Opens (Domain d))) :
    ∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z i, i ≤ N → ∀ x,
      ‖iteratedFDeriv ℝ i (halfspaceCutoff K χ z) x‖ ≤ A * (1 + ‖z‖) ^ N := by
  let D := ‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖
  have hL (z : ComplexEuclidean d) : ‖-coordinateInner (imaginaryPart z)‖ ≤ D * ‖z‖ := by
    rw [norm_neg]
    exact (coordinateInner_norm_le (imaginaryPart z)).trans
      (mul_le_mul_of_nonneg_left (norm_imaginaryPart_le z) (norm_nonneg _))
  have h := affine_transition_cutoff_derivative_family χ χ.contDiff χ.hasCompactSupport
    (fun z : ComplexEuclidean d => supportFunction K (imaginaryPart z) + 2)
    (fun z => -coordinateInner (imaginaryPart z)) D (norm_nonneg _) hL
  change ∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z i, i ≤ N → ∀ x,
    ‖iteratedFDeriv ℝ i (fun y => χ y * Complex.ofRealCLM
      (Real.smoothTransition (supportFunction K (imaginaryPart z) + 2 -
        inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm y) (imaginaryPart z)))) x‖ ≤
          A * (1 + ‖z‖)^N
  simpa only [coordinateInner_apply, neg_apply,
    sub_eq_add_neg, Complex.ofRealCLM_apply] using h

/-- The entire transform has the sharp support function of K, with one finite
polynomial degree. A directional transition gives a uniform exponential surplus. -/
theorem forward : Specs.ExpandedFA.Fourier.DistributionPaleyWiener.forwardType := by
  intro d K hne hK hcK u hu
  have huc := isCompact_euclideanSupport_of_supportedIn hK hu
  refine ⟨entire d u huc, ?_⟩
  obtain ⟨χ, V, hV, huV, hχ⟩ := cutoff_existence d (⊤ : Opens (Domain d))
    (distributionSupport u) (isCompact_distributionSupport huc) (subset_univ _)
  let χ0 := scalarCutoff ℂ χ
  have hχ0 : EqOn χ0 1 V := by
    intro x hx
    simp [χ0, scalarCutoff_apply, hχ hx]
  let cuts (z : ComplexEuclidean d) := halfspaceCutoff K χ0 z
  let G (z : ComplexEuclidean d) : Smooth d :=
    testToSmoothLM ℂ ⊤ (smoothCutoffCLM (cuts z) (laplaceKernel z))
  change PolynomialExponentialType K (fun z => smoothExtension u (laplaceKernel z))
  refine polynomialExponentialType_of_cutoff_family (smoothExtension u)
    (fun z => cuts z) G (fun z => (cuts z).contDiff) ?_ ?_
      (Real.exp (4 * Real.pi)) (by positivity) ?_ ?_
  · intro z x
    change (laplaceKernel z).val x * cuts z x = cuts z x * (laplaceKernel z).val x
    exact mul_comm _ _
  · intro z
    change smoothExtension u (testToSmoothLM ℂ ⊤ _) = smoothExtension u (laplaceKernel z)
    rw [extension d u huc]
    exact (halfspaceCutoff_formula hK hu χ0 V hV huV hχ0 z).symm
  · intro z x hx
    exact halfspaceCutoff_kernel_bound K χ0 z x hx
  · exact halfspaceCutoff_derivative_family K χ0

/-- Complete characterization with the original compact convex support type. -/
theorem characterization :
    Specs.ExpandedFA.Fourier.DistributionPaleyWiener.characterizationType := by
  intro d K hne hK hcK F
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact forward d K hne hK hcK u hu
  · rintro ⟨hF, hb⟩
    exact inverse_exists d K hne hK hcK F hF hb


end ExpandedFA.Fourier.DistributionPaleyWiener
