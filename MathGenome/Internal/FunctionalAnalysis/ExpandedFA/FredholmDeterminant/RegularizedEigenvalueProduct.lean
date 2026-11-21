import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RegularizedEigenvalueProduct
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.KernelSpectralBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalLogDerivative
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.HilbertSchmidtPowerTraces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.CanonicalProductExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.Lidskii
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2HilbertSchmidt
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

noncomputable section
set_option maxHeartbeats 600000
universe u v
open MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.FredholmDeterminant.RegularizedEigenvalueProduct
open Spec.Data
open TraceIdeals.Lidskii.Spec
open TraceIdeals.HilbertSchmidtDefinitions.Spec
open IntegralOperators.ContinuousTraceDiagonal.Spec

/-- The spectral comparison retains full generalized spaces even when the
natural C(Q) to L² quotient map is not globally injective. -/
theorem spectral_comparison : Spec.SpectralComparison.{u} :=
  KernelSpectralBridge.spectral_comparison

section SquareSum
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Weyl's square bound for an unordered finite selection of algebraic
occurrences. Sorting and padding are used only inside this proof. -/
lemma finite_eigenvalue_square_sum_le (T : H →L[ℂ] H) (hT : IsHilbertSchmidtValue T)
    (s : Finset (EigenvalueIndex T)) :
    (∑ i ∈ s, ‖eigenvalue T i‖ ^ 2) ≤
      ∑' n : ℕ, TraceIdeals.TraceClassDefinitions.Spec.singularSequence T n ^ 2 := by
  classical
  let e : Fin s.card ≃ s := s.equivFin.symm
  let f : Fin s.card → EigenvalueIndex T := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hselect := TraceIdeals.Lidskii.selection_of_injective T f hf
  obtain ⟨σ, hσ⟩ := TraceIdeals.QuasinilpotentTraceZero.exists_sorted_selection T
    (fun i => eigenvalue T (f i)) hselect
  let ev : ℕ → ℂ := fun j => if h : j < s.card then eigenvalue T (f (σ ⟨j,h⟩)) else 0
  have hsum : (∑ j ∈ Finset.range s.card, ‖ev j‖ ^ 2) =
      ∑ i ∈ s, ‖eigenvalue T i‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ i : Fin s.card, ‖eigenvalue T (f (σ i))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [ev, dite_eq_left i.isLt]
      _ = ∑ i : Fin s.card, ‖eigenvalue T (f i)‖ ^ 2 := Equiv.sum_comp σ (fun i => ‖eigenvalue T (f i)‖ ^ 2)
      _ = ∑ i : s, ‖eigenvalue T i.val‖ ^ 2 := by
        simpa only [f] using e.sum_comp (fun i : s => ‖eigenvalue T i.val‖ ^ 2)
      _ = _ := Finset.sum_coe_sort s (fun i => ‖eigenvalue T i‖ ^ 2)
  have hb := TraceIdeals.WeylSumsProducts.weyl_power_sums H T
    (TraceIdeals.HilbertSchmidtBasis.compactness T hT) ev hσ 2 (by omega) s.card
  rw [hsum] at hb
  exact hb.trans ((TraceIdeals.HilbertSchmidtBasis.singular_norm_identity ⟨T,hT⟩).1.sum_le_tsum
    (Finset.range s.card) (fun _ _ => sq_nonneg _))

/-- Square summability of the complete algebraic spectrum, without any
normality or choice of a sorted exhaustive enumeration. -/
lemma hilbertSchmidt_eigenvalues_square_summable (T : H →L[ℂ] H)
    (hT : IsHilbertSchmidtValue T) :
    Summable (fun i : EigenvalueIndex T => ‖eigenvalue T i‖ ^ 2) := by
  exact summable_of_sum_le (fun i => sq_nonneg _) (finite_eigenvalue_square_sum_le T hT)
end SquareSum

theorem square_summability : Spec.SquareSummability.{u} := by
  intro Q _ _ _ _ μ _ k
  exact hilbertSchmidt_eigenvalues_square_summable _
    (PartV.L2HilbertSchmidt.kernel_hilbertSchmidt μ μ (KernelSpectralBridge.Spec.kernelClass μ k))

section CanonicalProduct
variable {I : Type v}

/-- Quadratic cancellation in the genus-one factor. -/
lemma norm_factor_sub_one_le (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖factor w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have he : factor w - 1 = (Complex.exp w - 1 - w) - w * (Complex.exp w - 1) := by
    unfold factor
    ring
  rw [he]
  calc
    _ ≤ ‖Complex.exp w - 1 - w‖ + ‖w * (Complex.exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
      rw [norm_mul]
      gcongr
      · exact Complex.norm_exp_sub_one_sub_id_le hw
      · exact Complex.norm_exp_sub_one_le hw
    _ = _ := by ring

lemma differentiable_factor (a : ℂ) : Differentiable ℂ (fun z => factor (z * a)) := by
  unfold factor
  fun_prop

/-- A square-summable family has uniformly small scaled tails on every disk. -/
lemma eventually_scaled_norm_le_one (a : I → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ i in cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖z * a i‖ ≤ 1 := by
  have hr : 0 < R + 1 := by positivity
  have ht := ha.tendsto_cofinite_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < ((R + 1)⁻¹) ^ 2 by positivity))
  filter_upwards [ht] with i hi z hz
  have hai : ‖a i‖ ≤ (R + 1)⁻¹ := by
    have := inv_pos.mpr hr
    nlinarith [norm_nonneg (a i)]
  calc
    ‖z * a i‖ = ‖z‖ * ‖a i‖ := norm_mul _ _
    _ ≤ (R + 1) * (R + 1)⁻¹ :=
      mul_le_mul (hz.trans (by linarith)) hai (norm_nonneg _) hr.le
    _ = 1 := mul_inv_cancel₀ hr.ne'

/-- Normal convergence of genus-one products on compact disks for every
square-summable family, with no enumeration hypothesis. -/
lemma uniform_canonical_product (a : I → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun s : Finset I => fun z : ℂ => ∏ i ∈ s, factor (z * a i))
      (fun z => ∏' i, factor (z * a i)) atTop (Metric.closedBall 0 R) := by
  have hs := ha.mul_left (3 * R ^ 2)
  have ht := eventually_scaled_norm_le_one a ha R hR
  have hb : ∀ᶠ i in cofinite, ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖factor (z * a i) - 1‖ ≤ (3 * R ^ 2) * ‖a i‖ ^ 2 := by
    filter_upwards [ht] with i hi z hz
    have hz' := mem_closedBall_zero_iff.mp hz
    calc
      _ ≤ 3 * ‖z * a i‖ ^ 2 := norm_factor_sub_one_le _ (hi z hz')
      _ ≤ (3 * R ^ 2) * ‖a i‖ ^ 2 := by
        rw [norm_mul, mul_pow]
        calc
          _ = 3 * ‖z‖ ^ 2 * ‖a i‖ ^ 2 := by ring
          _ ≤ (3 * R ^ 2) * ‖a i‖ ^ 2 := by gcongr
  have hu := Summable.hasProdUniformlyOn_one_add (R := ℂ)
    (f := fun i z => factor (z * a i) - 1) (isCompact_closedBall 0 R) hs hb
    (fun i => ((differentiable_factor (a i)).continuous.sub continuous_const).continuousOn)
  simpa only [add_sub_cancel] using hu.tendstoUniformlyOn

lemma canonical_product_multipliable (a : I → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (z : ℂ) :
    Multipliable (fun i => factor (z * a i)) := by
  have hu := uniform_canonical_product a ha ‖z‖ (norm_nonneg _)
  exact ⟨_, hu.tendsto_at (mem_closedBall_zero_iff.mpr le_rfl)⟩

lemma entire_canonical_product (a : I → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) :
    Differentiable ℂ (fun z => ∏' i, factor (z * a i)) := by
  have hu := TraceDeterminantContinuity.locallyUniform_of_disks
    (uniform_canonical_product a ha)
  have hd := hu.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall (fun s =>
      (Differentiable.fun_finsetProd (fun i _ => differentiable_factor (a i))).differentiableOn))
    isOpen_univ
  exact differentiableOn_univ.mp hd

lemma summable_factor_deviations (a : I → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (z : ℂ) :
    Summable (fun i => ‖factor (z * a i) - 1‖) := by
  have ht := eventually_scaled_norm_le_one a ha ‖z‖ (norm_nonneg _)
  apply (ha.mul_left (3 * ‖z‖ ^ 2)).of_norm_bounded_eventually
  filter_upwards [ht] with i hi
  simp only [norm_norm]
  calc
    _ ≤ 3 * ‖z * a i‖ ^ 2 := norm_factor_sub_one_le _ (hi z le_rfl)
    _ = _ := by rw [norm_mul, mul_pow]; ring

lemma canonical_product_ne_zero (a : I → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (z : ℂ)
    (hz : ∀ i, z * a i ≠ 1) : (∏' i, factor (z * a i)) ≠ 0 := by
  have hf (i : I) : 1 + (factor (z * a i) - 1) ≠ 0 := by
    rw [add_sub_cancel, factor]
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm (hz i))) (Complex.exp_ne_zero _)
  simpa only [add_sub_cancel] using
    tprod_one_add_ne_zero_of_summable hf (summable_factor_deviations a ha z)

/-- One scalar factor has a simple zero at the reciprocal parameter. -/
lemma factor_order (b : ℂ) (hb : b ≠ 0) :
    analyticOrderAt (fun z => factor (z * b)) b⁻¹ = 1 := by
  have hd : HasDerivAt (fun z : ℂ => factor (z * b)) (-b * Complex.exp 1) b⁻¹ := by
    convert (((hasDerivAt_id b⁻¹).mul_const b).const_sub 1).mul
      (((hasDerivAt_id b⁻¹).mul_const b).cexp) using 1
    · funext z
      simp [factor, Pi.mul_apply, mul_comm]
    · simp [hb]
  have hf := (differentiable_factor b).analyticAt b⁻¹
  exact hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (by simp [factor, hb]) (hd.deriv.symm ▸ mul_ne_zero (neg_ne_zero.mpr hb) (Complex.exp_ne_zero _))

/-- Isolate the complete finite fiber at b; the complementary product is
entire and nonvanishing at b⁻¹. Thus the order equals the number of occurrences. -/
lemma canonical_product_order (a : I → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (b : ℂ) (hb : b ≠ 0)
    [Fintype {i : I // a i = b}] :
    analyticOrderAt (fun z => ∏' i, factor (z * a i)) b⁻¹ =
      (Fintype.card {i : I // a i = b} : ℕ∞) := by
  have hs : Summable (fun i : {i : I // a i = b} => ‖a i.val‖ ^ 2) := ha.subtype {i | a i = b}
  have hc : Summable (fun i : {i : I // a i ≠ b} => ‖a i.val‖ ^ 2) := ha.subtype {i | a i ≠ b}
  have heq : (fun z => ∏' i, factor (z * a i)) =
      (fun z => factor (z * b) ^ Fintype.card {i : I // a i = b}) *
      (fun z => ∏' i : {i : I // a i ≠ b}, factor (z * a i.val)) := by
    funext z
    have hsplit := Multipliable.tprod_mul_tprod_compl (s := {i | a i = b})
      (f := fun i => factor (z * a i))
      (canonical_product_multipliable (fun i : {i : I // a i = b} => a i.val) hs z)
      (canonical_product_multipliable (fun i : {i : I // a i ≠ b} => a i.val) hc z)
    rw [← hsplit]
    change _ = factor (z * b) ^ Fintype.card {i : I // a i = b} * _
    congr 1
    change (∏' i : {i : I // a i = b}, factor (z * a i.val)) = _
    rw [tprod_fintype]
    simp only [show ∀ i : {i : I // a i = b}, a i.val = b from fun i => i.property,
      Finset.prod_const, Finset.card_univ]
  have htail : (∏' i : {i : I // a i ≠ b}, factor (b⁻¹ * a i.val)) ≠ 0 := by
    apply canonical_product_ne_zero _ hc
    intro i hi
    have hai : a i.val = b := by
      calc
        a i.val = b * (b⁻¹ * a i.val) := by field_simp
        _ = b := by rw [hi, mul_one]
    exact i.property hai
  rw [heq]
  change analyticOrderAt (((fun z => factor (z * b)) ^ Fintype.card {i : I // a i = b}) *
    (fun z => ∏' i : {i : I // a i ≠ b}, factor (z * a i.val))) b⁻¹ = _
  rw [analyticOrderAt_mul
    (((differentiable_factor b).analyticAt b⁻¹).pow _)
    ((entire_canonical_product _ hc).analyticAt b⁻¹),
    analyticOrderAt_pow ((differentiable_factor b).analyticAt b⁻¹), factor_order b hb,
    ((entire_canonical_product _ hc).analyticAt b⁻¹).analyticOrderAt_eq_zero.mpr htail]
  simp

end CanonicalProduct

theorem uniform_product : Spec.UniformProduct.{u} := by
  intro Q _ _ _ _ μ _ k R hR
  exact uniform_canonical_product _ (square_summability μ k) R hR

theorem entire_product : Spec.EntireProduct.{u} := by
  intro Q _ _ _ _ μ _ k
  exact entire_canonical_product _ (square_summability μ k)


/-- The fiber of the scalar map contains exactly its algebraic occurrences. -/
def eigenvalueFiberEquiv {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (a : NonzeroEigenvalues T) :
    {i : EigenvalueIndex T // eigenvalue T i = a.val} ≃
      Fin (TraceIdeals.WeylProducts.Spec.algebraicMultiplicity T a.val) where
  toFun i := by
    rcases i with ⟨⟨b,j⟩,hb⟩
    have he : b = a := Subtype.ext hb
    subst b
    exact j
  invFun j := ⟨⟨a,j⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨b,j⟩,hb⟩
    have he : b = a := Subtype.ext hb
    subst b
    rfl
  right_inv j := rfl

lemma hilbertSchmidt_product_order {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : IsHilbertSchmidtValue T) (a : NonzeroEigenvalues T) :
    analyticOrderAt (product T) a.val⁻¹ =
      (TraceIdeals.WeylProducts.Spec.algebraicMultiplicity T a.val : ℕ∞) := by
  let e := eigenvalueFiberEquiv T a
  letI : Fintype {i : EigenvalueIndex T // eigenvalue T i = a.val} :=
    Fintype.ofEquiv _ e.symm
  have hc := canonical_product_order (eigenvalue T)
    (hilbertSchmidt_eigenvalues_square_summable T hT) a.val a.property.1
  have hcard : Fintype.card {i : EigenvalueIndex T // eigenvalue T i = a.val} =
      TraceIdeals.WeylProducts.Spec.algebraicMultiplicity T a.val :=
    (Fintype.card_congr e).trans (Fintype.card_fin _)
  unfold Spec.Data.product
  simpa only [hcard] using hc

/-- Algebraic conversion of the convergent-product statement to the source's
normalization. This helper does not assume any trace-class property. -/
lemma determinant_formula_of_product_formula (h : Spec.ProductFormula.{u}) :
    Spec.DeterminantFormula.{u} := by
  intro Q _ _ _ _ μ _ k z
  have hp := (h μ k z).tprod_eq
  change product (continuousKernelOperator μ k) z = _ at hp
  rw [hp, ← mul_assoc, ← Complex.exp_add]
  have he : -z * (∫ t, k (t,t) ∂μ) + z * (∫ t, k (t,t) ∂μ) = 0 := by ring
  simp [he]

/-- Once the determinant identity is established, its nonvanishing exponential
prefactor transfers the product's exact analytic zero orders. -/
lemma zero_multiplicities_of_determinant_formula (h : Spec.DeterminantFormula.{u}) :
    Spec.ZeroMultiplicities.{u} := by
  intro Q _ _ _ _ μ _ k a ha hea
  have heq : ClassicalDefinitions.Spec.FredholmDeterminantValue μ k =
      (fun z : ℂ => Complex.exp (-z * ∫ t, k (t,t) ∂μ)) *
        product (continuousKernelOperator μ k) := funext (h μ k)
  rw [heq, analyticOrderAt_mul (by fun_prop) ((entire_product μ k).analyticAt a⁻¹),
    (show analyticOrderAt (fun z : ℂ => Complex.exp (-z * ∫ t, k (t,t) ∂μ)) a⁻¹ = 0 from
      (show AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z * ∫ t, k (t,t) ∂μ)) a⁻¹ by
        fun_prop).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)), zero_add]
  exact hilbertSchmidt_product_order _
    (PartV.L2HilbertSchmidt.kernel_hilbertSchmidt μ μ (KernelSpectralBridge.Spec.kernelClass μ k))
    ⟨a,ha,hea⟩


lemma hasEigenvalue_iff_exists_vector {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : E →L[ℂ] E) (a : ℂ) :
    Module.End.HasEigenvalue T.toLinearMap a ↔ ∃ x : E, x ≠ 0 ∧ T x = a • x := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := h.exists_hasEigenvector
    exact ⟨x,hx.2,hx.apply_eq_smul⟩
  · rintro ⟨x,hx,he⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he,hx⟩

/-- The complete nonzero eigenvalue characterization in the Hilbert model. -/
theorem zeros_exactly : Spec.ZerosExactly.{u} := by
  intro Q _ _ _ _ μ _ k z
  let T := continuousKernelOperator μ k
  let C := KernelSpectralBridge.Spec.continuousOperator μ k
  have hT : IsHilbertSchmidtValue T := PartV.L2HilbertSchmidt.kernel_hilbertSchmidt μ μ
    (KernelSpectralBridge.Spec.kernelClass μ k)
  have hTC := TraceIdeals.HilbertSchmidtBasis.compactness T hT
  have hCC : Compactness.DefinitionsSpec.IsCompactLinearMapValue C.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr
      (IntegralOperators.ContinuousKernelCompactness.canonical_properties ℂ Q μ k).2.2.1
  have hcompare (a : ℂ) (ha : a ≠ 0) :
      Module.End.HasEigenvalue C.toLinearMap a ↔ Module.End.HasEigenvalue T.toLinearMap a := by
    rw [hasEigenvalue_iff_exists_vector, hasEigenvalue_iff_exists_vector,
      ← Fredholm.compact_nonzero_spectrum_iff_eigenvalue C hCC a ha,
      ← Fredholm.compact_nonzero_spectrum_iff_eigenvalue T hTC a ha]
    exact (KernelSpectralBridge.spectral_comparison μ k a ha).1
  rw [ClassicalFredholm.exceptional_eigenvalues μ k z]
  constructor
  · rintro ⟨hz,x,hx,he⟩
    refine ⟨z⁻¹,inv_ne_zero hz,?_,mul_inv_cancel₀ hz⟩
    exact (hcompare _ (inv_ne_zero hz)).mp
      ((hasEigenvalue_iff_exists_vector C _).mpr ⟨x,hx,he⟩)
  · rintro ⟨a,ha,hea,hza⟩
    have hz : z ≠ 0 := by intro hz; simp [hz] at hza
    have hae : a = z⁻¹ := by apply (mul_left_cancel₀ hz); simpa [hz] using hza
    subst a
    exact ⟨hz,(hasEigenvalue_iff_exists_vector C _).mp
      ((hcompare _ (inv_ne_zero hz)).mpr hea)⟩

theorem product_zero_multiplicities : Spec.ProductZeroMultiplicities.{u} := by
  intro Q _ _ _ _ μ _ k a ha hea
  exact hilbertSchmidt_product_order _
    (PartV.L2HilbertSchmidt.kernel_hilbertSchmidt μ μ (KernelSpectralBridge.Spec.kernelClass μ k))
    ⟨a,ha,hea⟩

section DeterminantIdentity
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
  (k : C(Q × Q, ℂ))
open ClassicalLogDerivative.Spec.Data
open ClassicalDefinitions.Spec

/-- Only powers starting at two need to be trace class. Their actual continuous
kernels identify the spectral moments with the diagonal coefficients. -/
lemma spectral_moment (n : ℕ) :
    HasSum (fun i : EigenvalueIndex (continuousKernelOperator μ k) =>
      eigenvalue (continuousKernelOperator μ k) i ^ (n + 2))
      (diagonalCoefficient μ k (n + 1)) := by
  have hT := PartV.L2HilbertSchmidt.kernel_hilbertSchmidt μ μ
    (KernelSpectralBridge.Spec.kernelClass μ k)
  have hpower := HilbertSchmidtPowerTraces.traceClass_powers _ _ hT n
  have htrace := IntegralOperators.ContinuousTraceDiagonal.diagonal_trace Q μ
    (iteratedKernel μ k (n + 1))
  rw [ClassicalLogDerivative.iterated_operator μ k (n + 1)] at htrace
  have hcoeff : TraceIdeals.TraceClassDefinitions.Spec.TraceValue
      (continuousKernelOperator μ k ^ (n + 2)) = diagonalCoefficient μ k (n + 1) :=
    htrace hpower
  have hsum := (HilbertSchmidtPowerTraces.power_traces _ _ hT n).2
  change HasSum (fun i : EigenvalueIndex (continuousKernelOperator μ k) =>
    eigenvalue (continuousKernelOperator μ k) i ^ (n + 2))
    (TraceIdeals.TraceClassDefinitions.Spec.TraceValue
      (continuousKernelOperator μ k ^ (n + 2))) at hsum
  rw [hcoeff] at hsum
  exact hsum

/-- The two absolutely convergent logarithmic series agree after restoring
the linear diagonal term; no trace of the original Hilbert–Schmidt operator
is used. -/
lemma product_formula_near_zero :
    product (continuousKernelOperator μ k) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => Complex.exp (z * ∫ t, k (t,t) ∂μ) *
        FredholmDeterminantValue μ k z) := by
  obtain ⟨_, r, hr, hcanonical⟩ := CanonicalProductExpansion.canonical_expansion
    (eigenvalue (continuousKernelOperator μ k)) (square_summability μ k)
  obtain ⟨s, hs, hlog⟩ := ClassicalLogDerivative.logarithmic_series μ k
  have hnonzero : ∀ᶠ z in 𝓝 (0 : ℂ), FredholmDeterminantValue μ k z ≠ 0 :=
    ((ClassicalEntireSeries.entire_functions μ k).1.continuous.tendsto 0).eventually
      (isOpen_ne.mem_nhds (by
        change FredholmDeterminantValue μ k 0 ≠ 0
        rw [(ClassicalEntireSeries.values_at_zero μ k).1]
        exact one_ne_zero))
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr,
    Metric.ball_mem_nhds (0 : ℂ) hs, hnonzero] with z hzr hzs hz0
  obtain ⟨habs, _, hprod⟩ := hcanonical z (mem_ball_zero_iff.mp hzr)
  let S : ℂ := ∑' n : ℕ, -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)) *
    (∑' i : EigenvalueIndex (continuousKernelOperator μ k),
      eigenvalue (continuousKernelOperator μ k) i ^ (n + 2))
  have htail : HasSum (fun n : ℕ =>
      -(z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * diagonalCoefficient μ k (n + 1))) S := by
    dsimp only [S]
    simpa only [(spectral_moment μ k _).tsum_eq, neg_mul] using habs.of_norm.hasSum
  have hfull : HasSum (fun n : ℕ =>
      -(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * diagonalCoefficient μ k n))
      (-z * (∫ t, k (t,t) ∂μ) + S) := by
    simpa only [Nat.zero_add, pow_one, Nat.cast_one, div_one,
      diagonalCoefficient, iteratedKernel, neg_mul, Nat.add_assoc] using
      (HasSum.zero_add (f := fun n : ℕ =>
        -(z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * diagonalCoefficient μ k n)) htail)
  have heq := (hlog z (mem_ball_zero_iff.mp hzs)).unique hfull
  calc
    product (continuousKernelOperator μ k) z = Complex.exp S := hprod
    _ = Complex.exp (z * (∫ t, k (t,t) ∂μ) +
        Complex.log (FredholmDeterminantValue μ k z)) := by rw [heq]; congr 1; ring
    _ = _ := by rw [Complex.exp_add, Complex.exp_log hz0]

/-- Global identification by the identity theorem for entire functions. -/
theorem product_formula : Spec.ProductFormula.{u} := by
  intro Q _ _ _ _ μ _ k z
  have hD : Differentiable ℂ (fun z => Complex.exp (z * ∫ t, k (t,t) ∂μ) *
      FredholmDeterminantValue μ k z) := by
    apply Differentiable.mul
    · fun_prop
    · exact (ClassicalEntireSeries.entire_functions μ k).1
  have heq := (Complex.analyticOnNhd_univ_iff_differentiable.mpr (entire_product μ k)).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hD) (product_formula_near_zero μ k)
  have hp := (canonical_product_multipliable _ (square_summability μ k) z).hasProd
  change HasProd _ (product (continuousKernelOperator μ k) z) at hp
  rw [congrFun heq z] at hp
  exact hp

theorem determinant_formula : Spec.DeterminantFormula.{u} :=
  determinant_formula_of_product_formula product_formula

theorem zero_multiplicities : Spec.ZeroMultiplicities.{u} :=
  zero_multiplicities_of_determinant_formula determinant_formula

theorem full_conclusion : Spec.FullConclusion.{u} :=
  ⟨product_formula, determinant_formula, uniform_product, entire_product,
    zeros_exactly, zero_multiplicities, spectral_comparison⟩

end DeterminantIdentity

end ExpandedFA.FredholmDeterminant.RegularizedEigenvalueProduct
