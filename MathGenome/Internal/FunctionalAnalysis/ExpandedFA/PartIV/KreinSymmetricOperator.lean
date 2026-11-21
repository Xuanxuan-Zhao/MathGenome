import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinSymmetricOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinSolutions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ReproducingKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosedSymmetricExtensions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosabilityAndDoubleAdjoint
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators Topology ContDiff
open MeasureTheory
open TopologicalSpace

namespace ExpandedFA.PartIV.KreinSymmetricOperator
open Spec
open ExpandedFA.PartV

/-- Real symmetric positive kernels remain positive for complex coefficients.
The mixed real-imaginary terms cancel by swapping the two finite indices. -/
lemma complex_positive_of_real (K : ℝ → ℝ → ℝ)
    (hK : KreinSolutions.Specs.PositiveDefiniteValue K) :
    ReproducingKernels.Spec.PositiveKernel (fun s t => (K s t : ℂ)) := by
  apply (ReproducingKernels.finite_kernel_characterization ℂ ℝ _).mpr
  refine ⟨?_, ?_⟩
  · intro s t
    simp [hK.1 t s]
  · intro n x c
    let a : Fin n → ℝ := fun i => (c i).re
    let b : Fin n → ℝ := fun i => (c i).im
    let r := ∑ i, ∑ j, a i * a j * K (x i) (x j)
    let q := ∑ i, ∑ j, b i * b j * K (x i) (x j)
    refine ⟨r + q, add_nonneg (hK.2 n x a) (hK.2 n x b), ?_⟩
    apply Complex.ext
    · simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      dsimp [r, q, a, b]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · have hcross :
          (∑ i, ∑ j, a i * b j * K (x i) (x j)) =
          (∑ i, ∑ j, b i * a j * K (x i) (x j)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hK.1 (x j) (x i)]
        ring
      simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
      change (∑ i, ∑ j, (a i * b j + -b i * a j) * K (x i) (x j)) = 0
      simp_rw [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [hcross]
      exact add_neg_cancel _

lemma kernel_continuous (p : Bool) (F : ℝ → ℝ) (hF : Continuous F)
    (he : Function.Even F) : Continuous (fun x : ℝ × ℝ => kernel p F x.1 x.2) := by
  cases p
  · exact (KreinSolutions.kernelRegularity F hF he).2.1
  · exact (KreinSolutions.kernelRegularity F hF he).1.1

/-- Reflection in either variable acts by the selected parity. -/
lemma kernel_reflect (p : Bool) (F : ℝ → ℝ) (he : Function.Even F) (s t : ℝ) :
    (kernel p F (-s) t : ℂ) = paritySign p * (kernel p F s t : ℂ) := by
  have h₁ : F (-s - t) = F (s + t) := by
    rw [show -s - t = -(s + t) by ring, he]
  have h₂ : F (-s + t) = F (s - t) := by
    rw [show -s + t = -(s - t) by ring, he]
  cases p <;> simp [kernel, paritySign, KreinSolutions.Specs.KernelMinusValue,
    KreinSolutions.Specs.KernelPlusValue, h₁, h₂] <;> ring

section GramHelpers
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous total family indexed by ℝ generates a separable Hilbert space.
No nonzero-space assumption is needed. -/
lemma separable_of_total_continuous (v : ℝ → H) (hv : Continuous v)
    (ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) : SeparableSpace H := by
  have hs := (isSeparable_range hv).span (R := ℂ) |>.closure
  have he : closure (Submodule.span ℂ (Set.range v) : Set H) = Set.univ := by
    exact congrArg (fun S : Submodule ℂ H => (S : Set H)) ht
  rw [he] at hs
  exact isSeparable_univ_iff.mp hs

/-- Coefficientwise conjugation on finite formal linear combinations. -/
def conjugateCoefficients : (ℝ →₀ ℂ) →ₗ⋆[ℂ] (ℝ →₀ ℂ) :=
  Finsupp.mapRange.linearMap (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ).toLinearMap

@[simp] lemma conjugateCoefficients_apply (c : ℝ →₀ ℂ) (t : ℝ) :
    conjugateCoefficients c t = conj (c t) := rfl

@[simp] lemma conjugateCoefficients_involutive (c : ℝ →₀ ℂ) :
    conjugateCoefficients (conjugateCoefficients c) = c := by
  ext t
  simp

/-- Conjugate the coefficients before synthesizing a vector. -/
def conjugateSynthesis (v : ℝ → H) : (ℝ →₀ ℂ) →ₗ⋆[ℂ] H :=
  (Finsupp.linearCombination ℂ v).comp conjugateCoefficients

lemma conjugateSynthesis_apply (v : ℝ → H) (c : ℝ →₀ ℂ) :
    conjugateSynthesis v c = c.sum (fun t z => conj z • v t) := by
  simp [conjugateSynthesis, conjugateCoefficients, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index]

/-- Reality of the Gram matrix makes coefficient conjugation preserve norms,
including all finite linear relations and all null vectors. -/
lemma conjugateSynthesis_norm (v : ℝ → H) (K : ℝ → ℝ → ℝ)
    (hgram : ∀ s t, ⟪v s, v t⟫_ℂ = (K s t : ℂ)) (c : ℝ →₀ ℂ) :
    ‖conjugateSynthesis v c‖ = ‖Finsupp.linearCombination ℂ v c‖ := by
  have he : ⟪conjugateSynthesis v c, conjugateSynthesis v c⟫_ℂ =
      conj ⟪Finsupp.linearCombination ℂ v c, Finsupp.linearCombination ℂ v c⟫_ℂ := by
    simp only [conjugateSynthesis_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left, inner_smul_right, hgram]
    simp only [Finsupp.sum, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), he,
    RCLike.conj_re]

lemma dense_synthesis (v : ℝ → H)
    (ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    DenseRange (Finsupp.linearCombination ℂ v) := by
  change Dense (Set.range (Finsupp.linearCombination ℂ v))
  rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr ht

/-- A total family separates vectors by their inner products. -/
lemma eq_of_inner_vectors (v : ℝ → H)
    (ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    {x y : H} (h : ∀ t, ⟪x, v t⟫_ℂ = ⟪y, v t⟫_ℂ) : x = y := by
  apply (dense_synthesis v ht).eq_of_inner_left ℂ
  intro c
  simp only [Finsupp.linearCombination_apply, Finsupp.inner_sum, inner_smul_right, h]

/-- Extend coefficient conjugation from the dense Gram span to the completion. -/
def gramConjugation (v : ℝ → H) (K : ℝ → ℝ → ℝ)
    (hgram : ∀ s t, ⟪v s, v t⟫_ℂ = (K s t : ℂ))
    (ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) : H →ₗᵢ⋆[ℂ] H :=
  (conjugateSynthesis v).extendOfIsometry (dense_synthesis v ht)
    (conjugateSynthesis_norm v K hgram)

lemma gramConjugation_synthesis (v : ℝ → H) (K : ℝ → ℝ → ℝ)
    (hg : ∀ s t, ⟪v s, v t⟫_ℂ = (K s t : ℂ))
    (ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) (c : ℝ →₀ ℂ) :
    gramConjugation v K hg ht (Finsupp.linearCombination ℂ v c) =
      Finsupp.linearCombination ℂ v (conjugateCoefficients c) := by
  exact LinearMap.extendOfIsometry_eq _ (dense_synthesis v ht)
    (conjugateSynthesis_norm v K hg) c

lemma gramConjugation_vectors (v : ℝ → H) (K : ℝ → ℝ → ℝ)
    (hg : ∀ s t, ⟪v s, v t⟫_ℂ = (K s t : ℂ))
    (ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) (t : ℝ) :
    gramConjugation v K hg ht (v t) = v t := by
  have h := gramConjugation_synthesis v K hg ht (Finsupp.single t 1)
  have hc : conjugateCoefficients (Finsupp.single t 1) = Finsupp.single t 1 := by
    ext u
    simp [Finsupp.single_apply]
  simpa [hc, Finsupp.linearCombination_single] using h

lemma gramConjugation_involutive (v : ℝ → H) (K : ℝ → ℝ → ℝ)
    (hg : ∀ s t, ⟪v s, v t⟫_ℂ = (K s t : ℂ))
    (ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    Function.Involutive (gramConjugation v K hg ht) := by
  have he : (fun x => gramConjugation v K hg ht (gramConjugation v K hg ht x)) =
      (id : H → H) := by
    apply (dense_synthesis v ht).equalizer
    · fun_prop
    · exact continuous_id
    · funext c
      simp only [Function.comp_apply, id_eq, gramConjugation_synthesis,
        conjugateCoefficients_involutive]
  intro x
  exact congrFun he x

end GramHelpers
/-- The canonical complex Gram Hilbert space, with all its required geometric
properties, is constructed from the original real positivity hypothesis. -/
theorem gram_space_exists : Spec.GramExists := by
  intro p F hF he hK
  let K : ℝ → ℝ → ℂ := fun s t => (kernel p F s t : ℂ)
  let L := ReproducingKernels.scalarOperators K
  let : Fact L.PosSemidef :=
    ⟨ReproducingKernels.scalarOperators_posSemidef K (complex_positive_of_real _ hK)⟩
  let H := RKHS.OfKernel L
  have hk : RKHS.kernel H = L := RKHS.OfKernel.kernel_ofKernel
  let v : ℝ → H := fun t => RKHS.kerFun H t 1
  have hg : ∀ s t, ⟪v s, v t⟫_ℂ = (kernel p F s t : ℂ) := by
    intro s t
    rw [← ReproducingKernels.native_kernel_apply_one]
    rw [hk]
    simp [L, ReproducingKernels.scalarOperators, K]
  have hspan : Submodule.span ℂ {RKHS.kerFun H x z | (x : ℝ) (z : ℂ)} =
      Submodule.span ℂ (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, z, rfl⟩
      have hz : RKHS.kerFun H x z = z • v x := by
        rw [← map_smul]
        simp
      rw [hz]
      exact Submodule.smul_mem _ z (Submodule.subset_span (Set.mem_range_self x))
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x, 1, rfl⟩
  have ht : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
    rw [← hspan]
    exact RKHS.kerFun_dense H
  have hc : Continuous (fun x : ℝ × ℝ => RKHS.kernel H x.1 x.2) := by
    simp only [hk]
    exact (Complex.continuous_ofReal.comp (kernel_continuous p F hF he)).smul continuous_const
  have hv : Continuous v :=
    ((RKHS.continuous_kernel_iff_continuous_kerFun H).mp hc).clm_apply continuous_const
  have hp : ∀ t, v (-t) = paritySign p • v t := by
    intro t
    have hs : conj (paritySign p) = paritySign p := by cases p <;> simp [paritySign]
    have hgen : ∀ s, ⟪v (-t), v s⟫_ℂ = ⟪paritySign p • v t, v s⟫_ℂ := by
      intro s
      rw [inner_smul_left, hg, hg, kernel_reflect p F he, hs]
    exact eq_of_inner_vectors v ht hgen
  refine ⟨H, inferInstance, inferInstance, inferInstance,
    separable_of_total_continuous v hv ht, ⟨?_⟩⟩
  exact
    { vectors := v
      gram := hg
      total := ht
      continuous_vectors := hv
      parity := hp
      conjugation := gramConjugation v (kernel p F) hg ht
      conjugation_involutive := gramConjugation_involutive v (kernel p F) hg ht
      conjugation_vectors := gramConjugation_vectors v (kernel p F) hg ht }

/-- A symmetric formula on a dense family descends to an actual densely
defined partial linear map. The null-vector argument proves well-definedness. -/
theorem symmetric_descent : Spec.SymmetricDescent := by
  intro T H _ _ _ _ _ J L hJ hsym
  have hker : J.ker ≤ L.ker := by
    intro f hf
    change L f = 0
    apply hJ.eq_zero_of_inner_left ℂ
    intro g
    rw [hsym f g, show J f = 0 from hf, inner_zero_left]
  let B : J.range →ₗ[ℂ] H :=
    (J.ker.liftQ L hker).comp J.quotKerEquivRange.symm.toLinearMap
  let A : ExpandedFA.Unbounded.Operator ℂ H H := ⟨J.range, B⟩
  have hA (f : T) : A ⟨J f, LinearMap.mem_range_self J f⟩ = L f := by
    simp [A, B]
  have hd : Dense (A.domain : Set H) := hJ
  have hformal : A.IsFormalAdjoint A := by
    intro x y
    obtain ⟨f, hf⟩ := x.2
    obtain ⟨g, hg⟩ := y.2
    have hx : x = ⟨J f, LinearMap.mem_range_self J f⟩ := Subtype.ext hf.symm
    have hy : y = ⟨J g, LinearMap.mem_range_self J g⟩ := Subtype.ext hg.symm
    subst x
    subst y
    simpa only [hA] using hsym f g
  have hs : ExpandedFA.Unbounded.IsSymmetric A := ⟨hd, LinearPMap.IsFormalAdjoint.le_adjoint hd hformal⟩
  exact ⟨A, rfl, fun f => ⟨LinearMap.mem_range_self J f, hA f⟩, hs, hs.isClosable⟩

open ExpandedFA.Unbounded
section
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma antiisometry_inner (C : H →ₗᵢ⋆[ℂ] K) (x y : H) :
    ⟪C x, C y⟫_ℂ = conj ⟪x, y⟫_ℂ := by
  have hm : C (x - Complex.I • y) = C x + Complex.I • C y := by
    simp [C.map_smulₛₗ, sub_eq_add_neg]
  have hp : C (x + Complex.I • y) = C x - Complex.I • C y := by
    simp [C.map_smulₛₗ, sub_eq_add_neg]
  have hplus : ‖C x + C y‖ = ‖x + y‖ := by rw [← map_add, C.norm_map]
  have hminus : ‖C x - C y‖ = ‖x - y‖ := by rw [← map_sub, C.norm_map]
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  change ((‖C x + C y‖ : ℂ)^2 - (‖C x - C y‖ : ℂ)^2 +
    ((‖C x - Complex.I • C y‖ : ℂ)^2 - (‖C x + Complex.I • C y‖ : ℂ)^2) * Complex.I) / 4 =
    conj (((‖x + y‖ : ℂ)^2 - (‖x - y‖ : ℂ)^2 +
    ((‖x - Complex.I • y‖ : ℂ)^2 - (‖x + Complex.I • y‖ : ℂ)^2) * Complex.I) / 4)
  rw [hplus, hminus, ← hp, ← hm, C.norm_map, C.norm_map]
  simp only [map_div₀, map_add, map_sub, map_pow, map_mul, Complex.conj_ofReal,
    map_ofNat, Complex.conj_I]
  ring

/-- An antiunitary equivalence also supplies a complex-linear unitary, by
transporting a Hilbert basis and then identifying the two coordinate spaces. -/
lemma unitary_of_surjective_antiisometry [CompleteSpace H] [CompleteSpace K]
    (C : H →ₗᵢ⋆[ℂ] K) (hC : Function.Surjective C) : Nonempty (H ≃ₗᵢ[ℂ] K) := by
  classical
  let b := (exists_hilbertBasis ℂ H).choose_spec.choose
  let v := fun i => C (b i)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v, antiisometry_inner C, orthonormal_iff_ite.mp b.orthonormal i j]
    split_ifs <;> simp
  have ht : (Submodule.span ℂ (Set.range v)).orthogonal = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    obtain ⟨x, rfl⟩ := hC y
    have hx : x = 0 := by
      apply b.repr.injective
      ext i
      simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, b.repr_apply_apply]
      have hh := (Submodule.mem_orthogonal _ _).mp hy (v i)
        (Submodule.subset_span (Set.mem_range_self i))
      rw [show v i = C (b i) from rfl, antiisometry_inner C] at hh
      exact (map_eq_zero_iff _ (starRingEnd ℂ).injective).mp hh
    rw [hx, map_zero]
  let d := HilbertBasis.mkOfOrthogonalEqBot hv ht
  exact ⟨b.repr.trans d.repr.symm⟩

end
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma commutes_adjoint (A : Operator ℂ H H) (hA : DenselyDefined A)
    (C : H →ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C) (hr : Spec.CommutesWith A C) :
    Spec.CommutesWith (hilbertAdjoint A) C := by
  intro y
  have hw : ∀ x : A.domain,
      ⟪A x, C y⟫_ℂ = ⟪(x : H), C (hilbertAdjoint A y)⟫_ℂ := by
    intro x
    obtain ⟨hx, he⟩ := hr x
    have hh := hilbertAdjoint_inner A hA y ⟨C x, hx⟩
    rw [he] at hh
    have ha : ⟪A x, C y⟫_ℂ = conj ⟪C (A x), y⟫_ℂ := by
      rw [← antiisometry_inner C, hC]
    rw [ha, hh, ← antiisometry_inner C, hC]
  have hy := (mem_hilbertAdjoint_domain_iff A hA (C y)).mpr ⟨_, hw⟩
  exact ⟨hy, hilbertAdjoint_apply_eq A hA ⟨C y, hy⟩ _ hw⟩

lemma conjugation_mem_deficiency (A : Operator ℂ H H) (hA : DenselyDefined A)
    (C : H →ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C) (hr : Spec.CommutesWith A C)
    (z : ℂ) {y : H} (hy : y ∈ deficiencySpace A z) :
    C y ∈ deficiencySpace A (conj z) := by
  obtain ⟨hy, he⟩ := (mem_deficiencySpace_iff A z y).mp hy
  obtain ⟨hCy, hCe⟩ := commutes_adjoint A hA C hC hr ⟨y, hy⟩
  refine (mem_deficiencySpace_iff A (conj z) (C y)).mpr ⟨hCy, ?_⟩
  rw [hCe, he, C.map_smulₛₗ]

lemma real_symmetric_deficiency_unitary (A : Operator ℂ H H) (hA : IsSymmetric A)
    (C : H →ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C) (hr : Spec.CommutesWith A C) :
    Nonempty (deficiencyPlus A ≃ₗᵢ[ℂ] deficiencyMinus A) := by
  let : CompleteSpace (deficiencyPlus A) :=
    (deficiencySpace_isClosed A hA.1 Complex.I).isComplete.completeSpace_coe
  let : CompleteSpace (deficiencyMinus A) :=
    (deficiencySpace_isClosed A hA.1 (-Complex.I)).isComplete.completeSpace_coe
  let D : deficiencyPlus A →ₗᵢ⋆[ℂ] deficiencyMinus A :=
    { toLinearMap :=
        { toFun := fun y => ⟨C y, by
            have hm := conjugation_mem_deficiency A hA.1 C hC hr Complex.I y.2
            simpa only [Complex.conj_I, deficiencyMinus, deficiencySpace,
              SymmetryAndDeficienciesSpec.deficiencyMinusValue,
              SymmetryAndDeficienciesSpec.deficiencySpaceValue] using hm⟩
          map_add' := fun x y => Subtype.ext (C.map_add _ _)
          map_smul' := fun z y => Subtype.ext (C.map_smulₛₗ _ _) }
      norm_map' := fun y => C.norm_map y }
  apply unitary_of_surjective_antiisometry D
  intro y
  have hm := conjugation_mem_deficiency A hA.1 C hC hr (-Complex.I) y.2
  have hm' : C y ∈ deficiencyPlus A := by
    simpa only [map_neg, Complex.conj_I, neg_neg, deficiencyPlus, deficiencySpace,
      SymmetryAndDeficienciesSpec.deficiencyPlusValue,
      SymmetryAndDeficienciesSpec.deficiencySpaceValue] using hm
  exact ⟨⟨C y, hm'⟩, Subtype.ext (hC y)⟩

lemma commutes_closure (A : Operator ℂ H H) (hc : A.IsClosable)
    (C : H →ₗᵢ⋆[ℂ] H) (hr : Spec.CommutesWith A C) :
    Spec.CommutesWith A.closure C := by
  have hm : Set.MapsTo (fun z : H × H => (C z.1, C z.2))
      (A.graph : Set (H × H)) (A.graph : Set (H × H)) := by
    rintro ⟨x,y⟩ hz
    obtain ⟨x, rfl, rfl⟩ := A.mem_graph_iff.mp hz
    obtain ⟨hx, he⟩ := hr x
    exact A.mem_graph_iff.mpr ⟨⟨C x, hx⟩, rfl, he⟩
  have hm' := hm.closure (C.continuous.prodMap C.continuous)
  intro x
  have hx : ((x : H), A.closure x) ∈ A.graph.topologicalClosure := by
    rw [hc.graph_closure_eq_closure_graph]
    exact A.closure.mem_graph_iff.mpr ⟨x, rfl, rfl⟩
  have hy := hm' hx
  change (C (x : H), C (A.closure x)) ∈ A.graph.topologicalClosure at hy
  rw [hc.graph_closure_eq_closure_graph] at hy
  obtain ⟨u, hu, he⟩ := A.closure.mem_graph_iff.mp hy
  change (u : H) = C (x : H) at hu
  exact ⟨by rw [← hu]; exact u.2, by simpa only [← hu] using he⟩

lemma symmetric_closure (A : Operator ℂ H H) (hA : IsSymmetric A) :
    IsSymmetric A.closure := by
  have hd : DenselyDefined A.closure := hA.1.mono A.le_closure.1
  have had : DenselyDefined (hilbertAdjoint A) :=
    (isClosable_iff_dense_hilbertAdjoint A hA.1).mp hA.isClosable
  have hle : A.closure ≤ hilbertAdjoint A :=
    by
      apply LinearPMap.le_of_le_graph
      rw [← hA.isClosable.graph_closure_eq_closure_graph]
      exact A.graph.topologicalClosure_minimal
        (LinearPMap.le_graph_of_le hA.2) (hilbertAdjoint_isClosed A hA.1)
  have he : A.closure = hilbertAdjoint (hilbertAdjoint A) :=
    closure_eq_hilbertAdjoint_hilbertAdjoint A hA.1 hA.isClosable
  have hf : A.closure.IsFormalAdjoint A.closure := by
    intro x y
    have h := hilbertAdjoint_inner (hilbertAdjoint A) had
      ⟨y, by rw [← he]; exact y.2⟩ ⟨x, hle.1 x.2⟩
    have hx : hilbertAdjoint A ⟨x, hle.1 x.2⟩ = A.closure x := (hle.2 rfl).symm
    rw [hx] at h
    have hy : hilbertAdjoint (hilbertAdjoint A) ⟨y, by rw [← he]; exact y.2⟩ =
        A.closure y := by
      have ht : A.closure ≤ hilbertAdjoint (hilbertAdjoint A) := he.le
      exact (ht.2 rfl).symm
    rw [hy] at h
    exact h
  exact ⟨hd, hf.le_adjoint hd⟩
/-- A real symmetric operator has a self-adjoint extension of its closure;
no essential self-adjointness or uniqueness is asserted. -/
lemma real_symmetric_extension (A : Operator ℂ H H) (hA : IsSymmetric A)
    (C : H →ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C) (hr : Spec.CommutesWith A C) :
    ∃ B : Operator ℂ H H, A.closure ≤ B ∧ Unbounded.IsSelfAdjoint B := by
  have hs := symmetric_closure A hA
  have hr' := commutes_closure A hA.isClosable C hr
  obtain ⟨U⟩ := real_symmetric_deficiency_unitary A.closure hs C hC hr'
  apply (exists_selfAdjoint_extension_iff_deficiencyIndices_eq A.closure
    hA.isClosable.closure_isClosed hs).mpr
  let : CompleteSpace (SymmetryAndDeficienciesSpec.deficiencySpaceValue A.closure Complex.I) :=
    (deficiencySpace_isClosed A.closure hs.1 Complex.I).isComplete.completeSpace_coe
  let : CompleteSpace (SymmetryAndDeficienciesSpec.deficiencySpaceValue A.closure (-Complex.I)) :=
    (deficiencySpace_isClosed A.closure hs.1 (-Complex.I)).isComplete.completeSpace_coe
  exact hilbertDimension_eq_of_linearIsometryEquiv U

end

theorem real_symmetric_extension_exists : Spec.RealSymmetricExtension := by
  intro H _ _ _ A hA C hC hr
  exact real_symmetric_extension A hA C hC hr

/-- The test space has its ordinary pointwise complex vector-space operations. -/
def smoothTestSubmodule (p : Bool) : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    ∀ t, f (-t) = paritySign p * f t}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfs, hfp⟩ ⟨hg, hgs, hgp⟩
    exact ⟨hf.add hg, hfs.add hgs, by intro t; simp [hfp, hgp, mul_add]⟩
  smul_mem' := by
    rintro z f ⟨hf, hfs, hfp⟩
    refine ⟨contDiff_const.mul hf, hfs.mul_left, ?_⟩
    intro t
    change z * f (-t) = paritySign p * (z * f t)
    rw [hfp]
    ring

instance (p : Bool) : AddCommGroup (SmoothTest p) :=
  inferInstanceAs (AddCommGroup (smoothTestSubmodule p))
instance (p : Bool) : Module ℂ (SmoothTest p) :=
  inferInstanceAs (Module ℂ (smoothTestSubmodule p))

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma test_integrable (v : ℝ → H) (hv : Continuous v) (f : ℝ → ℂ)
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun t => f t • v t) :=
  (hf.smul hv).integrable_of_hasCompactSupport hs.smul_right

/-- The actual synthesis map; its linearity uses Bochner integrability. -/
def smoothTestIntegral (p : Bool) (v : ℝ → H) (hv : Continuous v) :
    SmoothTest p →ₗ[ℂ] H where
  toFun f := testIntegral v f.val
  map_add' f g := by
    change (∫ t, (f.val t + g.val t) • v t) = _
    simp_rw [add_smul]
    exact integral_add (test_integrable v hv _ f.2.1.continuous f.2.2.1)
      (test_integrable v hv _ g.2.1.continuous g.2.2.1)
  map_smul' z f := by
    change (∫ t, (z * f.val t) • v t) = z • _
    simp_rw [mul_smul]
    exact integral_smul z _

/-- Project any compact smooth scalar test to the matching parity. -/
def projectTest (p : Bool) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : SmoothTest p :=
  ⟨fun t => f t + paritySign p * f (-t),
    hf.add (contDiff_const.mul (hf.comp contDiff_neg)),
    hs.add ((hs.comp_homeomorph (Homeomorph.neg ℝ)).mul_left), by
      intro t
      cases p <;> simp [paritySign] <;> ring⟩

lemma integral_projectTest {p : Bool} (v : ℝ → H) (hv : Continuous v)
    (hp : ∀ t, v (-t) = paritySign p • v t)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    testIntegral v (projectTest p f hf hs).val =
      testIntegral v f + testIntegral v f := by
  have hi := test_integrable v hv f hf.continuous hs
  have he : (fun t => (f t + paritySign p * f (-t)) • v t) =
      fun t => f t • v t + f (-t) • v (-t) := by
    funext t
    rw [add_smul, hp, smul_smul, mul_comm (f (-t))]
  dsimp only [testIntegral, projectTest]
  rw [he, integral_add hi (by simpa only [neg_neg] using hi.comp_neg)]
  exact congrArg ((∫ t : ℝ, f t • v t) + ·)
    (integral_neg_eq_self (fun t : ℝ => f t • v t) volume)

lemma smoothTestIntegral_dense {p : Bool} {F : ℝ → ℝ} (G : GramData p F H) :
    DenseRange (smoothTestIntegral p G.vectors G.continuous_vectors) := by
  let J := smoothTestIntegral p G.vectors G.continuous_vectors
  change Dense (J.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have ht : ∀ f : SmoothTest p, ⟪x, testIntegral G.vectors f.val⟫_ℂ = 0 := by
    intro f
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hx (J f) ⟨f, rfl⟩)
  have hall : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ t, f t • ⟪x, G.vectors t⟫_ℂ = 0 := by
    intro f hf hs
    let g : ℝ → ℂ := fun t => (f t : ℂ)
    have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hf
    have hgs : HasCompactSupport g := hs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have hh := ht (projectTest p g hg hgs)
    rw [integral_projectTest _ G.continuous_vectors G.parity] at hh
    rw [inner_add_right] at hh
    have hz : ⟪x, testIntegral G.vectors g⟫_ℂ = 0 := by
      exact (add_self_eq_zero.mp hh)
    dsimp only [testIntegral] at hz
    rw [← integral_inner (𝕜 := ℂ) (test_integrable G.vectors G.continuous_vectors g
      hg.continuous hgs) x] at hz
    simpa only [inner_smul_right, g, Complex.real_smul] using hz
  have hc : Continuous (fun t => ⟪x, G.vectors t⟫_ℂ) :=
    continuous_const.inner G.continuous_vectors
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable hall
  have he := MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_const
  apply eq_of_inner_vectors G.vectors G.total
  intro t
  simpa only [inner_zero_left] using congrFun he t
end

lemma second_deriv_comp_neg (f : ℝ → ℂ) :
    deriv (deriv (fun t => f (-t))) = fun t => deriv (deriv f) (-t) := by
  have h : deriv (fun t => f (-t)) = fun t => -deriv f (-t) :=
    funext (deriv_comp_neg f)
  rw [h]
  funext t
  change deriv (-(fun t => deriv f (-t))) t = _
  rw [deriv.neg, deriv_comp_neg, neg_neg]

lemma second_deriv_const_mul (c : ℂ) (f : ℝ → ℂ) :
    deriv (deriv (fun t => c * f t)) = fun t => c * deriv (deriv f) t := by
  have h (g : ℝ → ℂ) : deriv (fun t => c * g t) = fun t => c * deriv g t := by
    funext t
    exact deriv_fun_const_smul_field c g
  rw [h, h]

def secondDerivativeTest {p : Bool} (f : SmoothTest p) : SmoothTest p := by
  refine ⟨deriv (deriv f.val), (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp f.2.1).2).2, f.2.2.1.deriv.deriv, ?_⟩
  have he : (fun t => f.val (-t)) = fun t => paritySign p * f.val t :=
    funext f.2.2.2
  have hh := congrArg (fun g : ℝ → ℂ => deriv (deriv g)) he
  rw [second_deriv_comp_neg, second_deriv_const_mul] at hh
  exact congrFun hh

/-- Complex conjugation preserves the original scalar test class. -/
def conjugateTest {p : Bool} (f : SmoothTest p) : SmoothTest p :=
  ⟨fun t => conj (f.val t), Complex.conjCLE.contDiff.comp f.2.1,
    f.2.2.1.comp_left (g := conj) (by simp), by
      intro t
      change conj (f.val (-t)) = paritySign p * conj (f.val t)
      rw [f.2.2.2, map_mul]
      have hs : conj (paritySign p) = paritySign p := by cases p <;> simp [paritySign]
      rw [hs]⟩

lemma second_deriv_conjugate (f : ℝ → ℂ) :
    deriv (deriv (fun t => conj (f t))) = fun t => conj (deriv (deriv f) t) := by
  simp only [show (fun t => conj (f t)) = (fun t => star (f t)) from rfl,
    deriv.star']
  rfl

/-- Second differentiation is a linear endomorphism of the original test space. -/
def smoothTestSecondDerivative (p : Bool) : SmoothTest p →ₗ[ℂ] SmoothTest p where
  toFun := secondDerivativeTest
  map_add' f g := by
    apply Subtype.ext
    change deriv (deriv (f.val + g.val)) = deriv (deriv f.val) + deriv (deriv g.val)
    have h : deriv (f.val + g.val) = deriv f.val + deriv g.val := by
      funext t
      exact deriv_add (f.2.1.differentiable (by simp) t)
        (g.2.1.differentiable (by simp) t)
    rw [h]
    funext t
    exact deriv_add ((contDiff_infty_iff_deriv.mp f.2.1).2.differentiable (by simp) t)
      ((contDiff_infty_iff_deriv.mp g.2.1).2.differentiable (by simp) t)
  map_smul' c f := by
    apply Subtype.ext
    exact second_deriv_const_mul c f.val

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma conjugation_testIntegral (C : H →ₗᵢ⋆[ℂ] H) (v : ℝ → H) (hv : Continuous v)
    (hCv : ∀ t, C (v t) = v t) (f : ℝ → ℂ)
    (hf : Continuous f) (hs : HasCompactSupport f) :
    C (testIntegral v f) = testIntegral v (fun t => conj (f t)) := by
  let D : H →L[ℝ] H :=
    { toLinearMap :=
        { toFun := C
          map_add' := C.map_add
          map_smul' := by
            intro r x
            change C ((r : ℂ) • x) = (r : ℂ) • C x
            rw [C.map_smulₛₗ, Complex.conj_ofReal] }
      cont := C.continuous }
  change D (∫ t, f t • v t) = ∫ t, conj (f t) • v t
  rw [← D.integral_comp_comm (test_integrable v hv f hf hs)]
  apply integral_congr_ae
  filter_upwards [] with t
  change C (f t • v t) = conj (f t) • v t
  rw [C.map_smulₛₗ, hCv]
end


section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma inner_testIntegral_eq_double (v : ℝ → H) (hv : Continuous v)
    (K : ℝ → ℝ → ℂ) (hg : ∀ s t, ⟪v s, v t⟫_ℂ = K s t)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg' : Continuous g) (hgs : HasCompactSupport g) :
    ⟪testIntegral v f, testIntegral v g⟫_ℂ =
      ∫ s, ∫ t, conj (f s) * g t * K s t := by
  have hi := test_integrable v hv f hf hfs
  have hj := test_integrable v hv g hg' hgs
  dsimp only [testIntegral]
  calc
    ⟪∫ s, f s • v s, ∫ t, g t • v t⟫_ℂ =
        conj ⟪∫ t, g t • v t, ∫ s, f s • v s⟫_ℂ :=
      (inner_conj_symm _ _).symm
    _ = ∫ s, conj ⟪∫ t, g t • v t, f s • v s⟫_ℂ := by
      rw [← integral_inner hi, integral_conj]
    _ = ∫ s, ⟪f s • v s, ∫ t, g t • v t⟫_ℂ := by
      simp only [inner_conj_symm]
    _ = ∫ s, ∫ t, conj (f s) * g t * K s t := by
      congr 1
      funext s
      rw [← integral_inner hj]
      congr 1
      funext t
      rw [inner_smul_left, inner_smul_right, hg]
      ring
end

lemma weighted_kernel_hasCompactSupport (K : ℝ → ℝ → ℂ)
    (f g : ℝ → ℂ) (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasCompactSupport (fun x : ℝ × ℝ => conj (f x.1) * g x.2 * K x.1 x.2) := by
  apply HasCompactSupport.intro (hfs.isCompact.prod hgs.isCompact)
  rintro ⟨s,t⟩ hx
  by_cases hs : s ∈ tsupport f
  · have ht : t ∉ tsupport g := by simpa only [Set.mem_prod, hs, true_and] using hx
    rw [image_eq_zero_of_notMem_tsupport ht]
    simp
  · rw [image_eq_zero_of_notMem_tsupport hs]
    simp

lemma weighted_kernel_integrable (K : ℝ → ℝ → ℂ)
    (hK : Continuous (fun x : ℝ × ℝ => K x.1 x.2))
    (f g : ℝ → ℂ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun x : ℝ × ℝ => conj (f x.1) * g x.2 * K x.1 x.2) :=
  (((Complex.continuous_conj.comp (hf.comp continuous_fst)).mul
    (hg.comp continuous_snd)).mul hK).integrable_of_hasCompactSupport
    (weighted_kernel_hasCompactSupport K f g hfs hgs)

/-- For a matching-parity test, both summands of the selected kernel contribute
one half of the same integral. No regularity of F beyond continuity is needed. -/
lemma integral_kernel_parity (p : Bool) (F : ℝ → ℝ) (hF : Continuous F)
    (g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgp : ∀ t, g (-t) = paritySign p * g t) (s : ℝ) :
    (∫ t, g t * (kernel p F s t : ℂ)) = ∫ t, g t * (F (s-t) : ℂ) := by
  have ha : Integrable (fun t => g t * (F (s-t) : ℂ)) :=
    (hg.mul (Complex.continuous_ofReal.comp (hF.comp
      (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport hgs.mul_right
  have hb : Integrable (fun t => g t * (F (s+t) : ℂ)) :=
    (hg.mul (Complex.continuous_ofReal.comp (hF.comp
      (continuous_const.add continuous_id)))).integrable_of_hasCompactSupport hgs.mul_right
  have he : (∫ t, g t * (F (s+t) : ℂ)) =
      paritySign p * ∫ t, g t * (F (s-t) : ℂ) := by
    rw [← integral_neg_eq_self (fun t => g t * (F (s+t) : ℂ)) volume,
      ← integral_const_mul]
    congr 1
    funext t
    rw [hgp]
    simp only [sub_eq_add_neg]
    ring
  cases p
  · simp only [Spec.kernel, Bool.false_eq_true, ↓reduceIte,
      KreinSolutions.Specs.KernelMinusValue, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_ofNat]
    simp_rw [← mul_div_assoc, mul_sub]
    rw [integral_div, integral_sub ha hb, he]
    simp [paritySign]
  · simp only [Spec.kernel, ↓reduceIte, KreinSolutions.Specs.KernelPlusValue,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat]
    simp_rw [← mul_div_assoc, mul_add]
    rw [integral_div, integral_add ha hb, he]
    simp [paritySign]

lemma double_integral_kernel_parity (p : Bool) (F : ℝ → ℝ) (hF : Continuous F)
    (f g : ℝ → ℂ) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgp : ∀ t, g (-t) = paritySign p * g t) :
    (∫ s, ∫ t, conj (f s) * g t * (kernel p F s t : ℂ)) =
      ∫ s, ∫ t, conj (f s) * g t * (F (s-t) : ℂ) := by
  simp_rw [mul_assoc, integral_const_mul,
    integral_kernel_parity p F hF g hg hgs hgp]

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma inner_testIntegral_kernel_parity {p : Bool} {F : ℝ → ℝ}
    (G : GramData p F H) (hF : Continuous F)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgp : ∀ t, g (-t) = paritySign p * g t) :
    ⟪testIntegral G.vectors f, testIntegral G.vectors g⟫_ℂ =
      ∫ s, ∫ t, conj (f s) * g t * (F (s-t) : ℂ) := by
  rw [inner_testIntegral_eq_double G.vectors G.continuous_vectors
    (fun s t => (kernel p F s t : ℂ)) G.gram f g hf hfs hg hgs,
    double_integral_kernel_parity p F hF f g hg hgs hgp]
end


open Function
namespace WaveSupport
lemma compact_support_shear {f g : ℝ → ℂ} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (k : ℝ → ℂ) (x₀ : ℝ) :
    HasCompactSupport (fun z : ℝ × ℝ => f z.2 * (g (z.1 - z.2) * k (x₀ - z.1))) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((hf.prod hg).image (show Continuous (fun z : ℝ × ℝ => (z.1 + z.2, z.1)) by fun_prop))
  intro z hz
  change f z.2 * (g (z.1 - z.2) * k (x₀ - z.1)) ≠ 0 at hz
  have hfz : f z.2 ≠ 0 := (mul_ne_zero_iff.mp hz).1
  have hgz : g (z.1 - z.2) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).2).1
  refine ⟨(z.2, z.1 - z.2), ⟨subset_tsupport f hfz, subset_tsupport g hgz⟩, ?_⟩
  ext <;> simp

lemma integrable_shear {f g k : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hk : Continuous k) (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) (x₀ : ℝ) :
    Integrable (fun z : ℝ × ℝ => f z.2 * (g (z.1 - z.2) * k (x₀ - z.1)))
      (volume.prod volume) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact compact_support_shear hsf hsg k x₀
lemma compact_support_product {f g : ℝ → ℂ} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (k : ℝ × ℝ → ℂ) :
    HasCompactSupport (fun z : ℝ × ℝ => f z.1 * (g z.2 * k z)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hf.prod hg)
  intro z hz
  change f z.1 * (g z.2 * k z) ≠ 0 at hz
  exact ⟨subset_tsupport f (mul_ne_zero_iff.mp hz).1,
    subset_tsupport g (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).2).1⟩

lemma integrable_product {f g : ℝ → ℂ} {k : ℝ × ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hk : Continuous k)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    Integrable (fun z : ℝ × ℝ => f z.1 * (g z.2 * k z)) (volume.prod volume) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact compact_support_product hsf hsg k

open scoped Convolution
lemma convolution_assoc_compact {f g k : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hk : Continuous k) (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℂ] g) ⋆[ContinuousLinearMap.mul ℝ ℂ] k =
      f ⋆[ContinuousLinearMap.mul ℝ ℂ] (g ⋆[ContinuousLinearMap.mul ℝ ℂ] k) := by
  funext x₀
  exact convolution_assoc' (ContinuousLinearMap.mul ℝ ℂ) (ContinuousLinearMap.mul ℝ ℂ)
    (ContinuousLinearMap.mul ℝ ℂ) (ContinuousLinearMap.mul ℝ ℂ)
    (fun x y z => mul_assoc x y z)
    (Filter.Eventually.of_forall (hsf.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.mul ℝ ℂ) hf.locallyIntegrable hg))
    (Filter.Eventually.of_forall (hsg.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.mul ℝ ℂ) hg.locallyIntegrable hk))
    (integrable_shear hf hg hk hsf hsg x₀)
end WaveSupport

open scoped Convolution
open ContinuousLinearMap
local notation "M" => (ContinuousLinearMap.mul ℝ ℂ)

lemma convolution_deriv_move {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) :
    deriv f ⋆[M] g = f ⋆[M] deriv g := by
  funext x
  exact (hcf.hasDerivAt_convolution_left M hf hg.continuous.locallyIntegrable x).unique
    (hcg.hasDerivAt_convolution_right M hf.continuous.locallyIntegrable hg x)

lemma convolution_second_deriv_move {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    deriv (deriv f) ⋆[M] g = f ⋆[M] deriv (deriv g) := by
  calc
    deriv (deriv f) ⋆[M] g = deriv f ⋆[M] deriv g :=
      convolution_deriv_move ((contDiff_infty_iff_deriv.mp hf).2.of_le (by simp)) hcf.deriv
        (hg.of_le (by simp)) hcg
    _ = f ⋆[M] deriv (deriv g) :=
      convolution_deriv_move (hf.of_le (by simp)) hcf
        ((contDiff_infty_iff_deriv.mp hg).2.of_le (by simp)) hcg.deriv

lemma convolution_second_deriv_transfer {f g k : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (hk : Continuous k) :
    deriv (deriv f) ⋆[M] (g ⋆[M] k) =
      f ⋆[M] (deriv (deriv g) ⋆[M] k) := by
  have hf'' : Continuous (deriv (deriv f)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2.continuous
  have hg'' : Continuous (deriv (deriv g)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hg).2).2.continuous
  rw [← WaveSupport.convolution_assoc_compact hf'' hg.continuous hk hcf.deriv.deriv hcg,
    convolution_second_deriv_move hf hcf hg hcg,
    WaveSupport.convolution_assoc_compact hf.continuous hg'' hk hcf hcg.deriv.deriv]

lemma reflect_convolution_eq_double (f g k : ℝ → ℂ) :
    ((fun s => f (-s)) ⋆[M] (g ⋆[M] k)) 0 =
      ∫ s : ℝ, ∫ t : ℝ, f s * (g t * k (s - t)) := by
  change (∫ s : ℝ, f (-s) * ∫ t : ℝ, g t * k (0 - s - t)) = _
  rw [← integral_neg_eq_self (fun s : ℝ => f (-s) * ∫ t : ℝ, g t * k (0 - s - t))]
  simp only [neg_neg, zero_sub, integral_const_mul]

lemma double_integral_second_deriv_transfer {f g k : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (hk : Continuous k) :
    (∫ s : ℝ, ∫ t : ℝ, deriv (deriv f) s * (g t * k (s - t))) =
      ∫ s : ℝ, ∫ t : ℝ, f s * (deriv (deriv g) t * k (s - t)) := by
  have h := congrFun (convolution_second_deriv_transfer
    (hf.comp contDiff_neg) (hcf.comp_homeomorph (Homeomorph.neg ℝ)) hg hcg hk) 0
  dsimp only [Function.comp_def] at h
  rw [second_deriv_comp_neg] at h
  simpa only [reflect_convolution_eq_double] using h

open scoped InnerProductSpace ComplexConjugate
open Spec
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma testIntegral_second_deriv_symmetric {p : Bool} {F : ℝ → ℝ}
    (G : GramData p F H) (hF : Continuous F) (f g : SmoothTest p) :
    ⟪testIntegral G.vectors (deriv (deriv f.val)), testIntegral G.vectors g.val⟫_ℂ =
      ⟪testIntegral G.vectors f.val, testIntegral G.vectors (deriv (deriv g.val))⟫_ℂ := by
  calc
    ⟪testIntegral G.vectors (deriv (deriv f.val)), testIntegral G.vectors g.val⟫_ℂ =
        ∫ s, ∫ t, conj (deriv (deriv f.val) s) * g.val t * (F (s-t) : ℂ) :=
      inner_testIntegral_kernel_parity G hF _ _ (secondDerivativeTest f).2.1.continuous
        (secondDerivativeTest f).2.2.1 g.2.1.continuous g.2.2.1 g.2.2.2
    _ = ∫ s, ∫ t, conj (f.val s) * deriv (deriv g.val) t * (F (s-t) : ℂ) := by
      have h := double_integral_second_deriv_transfer
        (Complex.conjCLE.contDiff.comp f.2.1)
        (f.2.2.1.comp_left (g := conj) (by simp)) g.2.1 g.2.2.1
        (Complex.continuous_ofReal.comp hF)
      dsimp only [Function.comp_def] at h
      change (∫ s : ℝ, ∫ t : ℝ, deriv (deriv (fun s => conj (f.val s))) s *
        (g.val t * (F (s-t) : ℂ))) =
          ∫ s : ℝ, ∫ t : ℝ, conj (f.val s) *
            (deriv (deriv g.val) t * (F (s-t) : ℂ)) at h
      rw [second_deriv_conjugate] at h
      simpa only [mul_assoc] using h
    _ = ⟪testIntegral G.vectors f.val, testIntegral G.vectors (deriv (deriv g.val))⟫_ℂ :=
      (inner_testIntegral_kernel_parity G hF _ _ f.2.1.continuous f.2.2.1
        (secondDerivativeTest g).2.1.continuous (secondDerivativeTest g).2.2.1
        (secondDerivativeTest g).2.2.2).symm
end


section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operatorConclusion_of_test_symmetry {p : Bool} {F : ℝ → ℝ}
    (G : GramData p F H)
    (hidentity : ∀ f g : SmoothTest p,
      ⟪testIntegral G.vectors (deriv (deriv f.val)), testIntegral G.vectors g.val⟫_ℂ =
      ⟪testIntegral G.vectors f.val, testIntegral G.vectors (deriv (deriv g.val))⟫_ℂ) :
    OperatorConclusion G := by
  let J := smoothTestIntegral p G.vectors G.continuous_vectors
  let L := J.comp (smoothTestSecondDerivative p)
  obtain ⟨A, hd, ha, hs, hc⟩ := symmetric_descent (SmoothTest p) H J L
    (smoothTestIntegral_dense G) hidentity
  have hr : CommutesWith A G.conjugation := by
    intro x
    have hx : (x : H) ∈ J.range := by rw [← hd]; exact x.2
    obtain ⟨f, hf⟩ := hx
    have hCx : G.conjugation (x : H) = J (conjugateTest f) := by
      rw [← hf]
      exact conjugation_testIntegral G.conjugation G.vectors G.continuous_vectors
        G.conjugation_vectors f.val f.2.1.continuous f.2.2.1
    have hm : G.conjugation (x : H) ∈ A.domain := by
      rw [hCx, hd]
      exact LinearMap.mem_range_self J (conjugateTest f)
    refine ⟨hm, ?_⟩
    have hAx : A x = L f := by
      have hx' : x = ⟨J f, (ha f).1⟩ := Subtype.ext hf.symm
      rw [hx']
      exact (ha f).2
    rw [hAx]
    calc
      A ⟨G.conjugation (x : H), hm⟩ = L (conjugateTest f) := by
        have hx' : (⟨G.conjugation (x : H), hm⟩ : A.domain) =
            ⟨J (conjugateTest f), (ha (conjugateTest f)).1⟩ := Subtype.ext hCx
        rw [hx']
        exact (ha (conjugateTest f)).2
      _ = G.conjugation (L f) := by
        change testIntegral G.vectors (deriv (deriv (fun t => conj (f.val t)))) =
          G.conjugation (testIntegral G.vectors (deriv (deriv f.val)))
        rw [second_deriv_conjugate]
        exact (conjugation_testIntegral G.conjugation G.vectors G.continuous_vectors
          G.conjugation_vectors _ (secondDerivativeTest f).2.1.continuous
          (secondDerivativeTest f).2.2.1).symm
  refine ⟨A, ?_, ha, hs, hr, hc,
    real_symmetric_extension A hs G.conjugation G.conjugation_involutive hr⟩
  rw [hd]
  rfl
end

/-- The full original construction: the second derivative on the exact range
of smooth tests of matching parity is symmetric, real and closable, and its
closure has a self-adjoint extension. -/
theorem krein_symmetric_operator : Spec.Main := by
  intro p F hF he hpos
  obtain ⟨H, hnorm, hinner, hcomplete, hsep, ⟨G⟩⟩ := gram_space_exists p F hF he hpos
  exact ⟨H, hnorm, hinner, hcomplete, hsep, G,
    operatorConclusion_of_test_symmetry G (testIntegral_second_deriv_symmetric G hF)⟩

end ExpandedFA.PartIV.KreinSymmetricOperator
