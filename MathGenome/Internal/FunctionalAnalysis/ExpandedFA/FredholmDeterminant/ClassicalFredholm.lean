import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.ClassicalFredholm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalResolventIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.ContinuousKernelCompactness
import Mathlib.Analysis.Analytic.Order

open MeasureTheory Filter
open scoped Topology
universe u
namespace ExpandedFA.FredholmDeterminant.ClassicalFredholm
open ClassicalDefinitions.Spec ClassicalEntireSeries.Spec.Data

/-- A holomorphic solution of f' = f h cannot have a zero unless it vanishes locally.
The proof compares orders of vanishing, avoiding any choice of a primitive. -/
lemma locally_zero_of_deriv_eq_mul {f h : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hh : AnalyticAt ℂ h z) (hz : f z = 0)
    (heq : deriv f =ᶠ[𝓝 z] f * h) : f =ᶠ[𝓝 z] 0 := by
  apply analyticOrderAt_eq_top.mp
  have hd : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa [hz] using hf.analyticOrderAt_deriv_add_one
  have hm : analyticOrderAt (deriv f) z = analyticOrderAt f z + analyticOrderAt h z := by
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul hf hh]
  have hle : analyticOrderAt f z ≤ analyticOrderAt (deriv f) z := by
    rw [hm]
    exact le_add_right le_rfl
  have hs : analyticOrderAt f z + 1 ≤ analyticOrderAt f z := by
    calc
      _ ≤ analyticOrderAt (deriv f) z + 1 := add_le_add hle le_rfl
      _ = _ := hd
  by_contra hn
  exact (lt_irrefl _ ((ENat.add_one_le_iff hn).mp hs))

section
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q]
  [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ] (k : C(Q × Q, ℂ))

/-- The norm-continuous family of columns of a continuous kernel. -/
noncomputable def columns (b : C(Q × Q, ℂ)) : C(Q, C(Q, ℂ)) :=
  (b.comp ⟨Prod.swap, continuous_swap⟩).curry

omit [MeasurableSpace Q] [BorelSpace Q] in
lemma norm_columns_le (b : C(Q × Q, ℂ)) (y : Q) : ‖columns b y‖ ≤ ‖b‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact b.norm_coe_le_norm (x, y)

omit [MeasurableSpace Q] [BorelSpace Q] in
lemma continuous_operator_diagonal (S : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) :
    Continuous (fun t : Q => S (columns k t) t) := by
  exact (S.continuous.comp (columns k).continuous).eval continuous_id

/-- Integrate the diagonal after applying an arbitrary bounded operator to each
column. This is a bounded linear functional on the operator algebra, even when
μ is zero or Q is empty. -/
noncomputable def operatorDiagonal : (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) →L[ℂ] ℂ :=
  ({ toFun := fun S => ∫ t, S (columns k t) t ∂μ
     map_add' := fun S T => by
       simp only [add_apply, ContinuousMap.add_apply]
       exact integral_add
         ((continuous_operator_diagonal k S).integrable_of_hasCompactSupport
           (HasCompactSupport.of_compactSpace _))
         ((continuous_operator_diagonal k T).integrable_of_hasCompactSupport
           (HasCompactSupport.of_compactSpace _))
     map_smul' := fun a S => by
       simp only [smul_apply, ContinuousMap.smul_apply,
         smul_eq_mul, RingHom.id_apply]
       exact integral_const_mul a _ } : (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) →ₗ[ℂ] ℂ).mkContinuous
    (μ.real Set.univ * ‖k‖) (fun S => by
      change ‖∫ t, S (columns k t) t ∂μ‖ ≤ _
      have hb (t : Q) : ‖S (columns k t) t‖ ≤ ‖S‖ * ‖k‖ :=
        ((S (columns k t)).norm_coe_le_norm t).trans
          ((S.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_columns_le k t)
            (norm_nonneg S)))
      have hi := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)
      calc
        _ ≤ μ.real Set.univ * (‖S‖ * ‖k‖) := by simpa [mul_comm] using hi
        _ = _ := by ring)

lemma column_identity (z : ℂ) (y : Q) :
    (1 - z • KernelOperatorValue μ k) (columns (minorKernel μ k z) y) =
      FredholmDeterminantValue μ k z • columns k y := by
  ext x
  have hi := (ClassicalResolventIdentities.kernel_identities μ k z x y).1
  change minorKernel μ k z (x, y) - z *
    (KernelOperatorValue μ k (columns (minorKernel μ k z) y)) x =
      FredholmDeterminantValue μ k z * k (x, y)
  rw [(ClassicalDefinitions.data_identification μ k).1]
  simp only [columns, ContinuousMap.curry_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Prod.swap_prod_mk]
  simp_rw [ClassicalEntireSeries.minor_kernel_identification μ k z]
  linear_combination hi

lemma derivative_eq_mul_inverse (z : ℂ) (hz : IsUnit (1 - z • KernelOperatorValue μ k)) :
    deriv (FredholmDeterminantValue μ k) z = FredholmDeterminantValue μ k z *
      (-operatorDiagonal μ k (Ring.inverse (1 - z • KernelOperatorValue μ k))) := by
  have hc (y : Q) : columns (minorKernel μ k z) y =
      FredholmDeterminantValue μ k z •
        (Ring.inverse (1 - z • KernelOperatorValue μ k)) (columns k y) := by
    have he := congrArg (fun S : C(Q, ℂ) →L[ℂ] C(Q, ℂ) =>
      S (columns (minorKernel μ k z) y)) (Ring.inverse_mul_cancel _ hz)
    change Ring.inverse (1 - z • KernelOperatorValue μ k)
      ((1 - z • KernelOperatorValue μ k) (columns (minorKernel μ k z) y)) =
      columns (minorKernel μ k z) y at he
    rw [column_identity μ k, map_smul] at he
    exact he.symm
  rw [ClassicalResolventIdentities.diagonal_derivative μ k z]
  have hpoint (t : Q) : FredholmMinorValue μ k t t z =
      FredholmDeterminantValue μ k z *
        (Ring.inverse (1 - z • KernelOperatorValue μ k)) (columns k t) t := by
    rw [← ClassicalEntireSeries.minor_kernel_identification μ k z]
    exact congrArg (fun f : C(Q, ℂ) => f t) (hc t)
  simp_rw [hpoint]
  rw [integral_const_mul]
  change -(FredholmDeterminantValue μ k z *
    (∫ t, (Ring.inverse (1 - z • KernelOperatorValue μ k)) (columns k t) t ∂μ)) =
    FredholmDeterminantValue μ k z *
      (-(∫ t, (Ring.inverse (1 - z • KernelOperatorValue μ k)) (columns k t) t ∂μ))
  ring

lemma determinant_ne_zero_of_isUnit (z : ℂ)
    (hz : IsUnit (1 - z • KernelOperatorValue μ k)) : FredholmDeterminantValue μ k z ≠ 0 := by
  intro hzero
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 - w • KernelOperatorValue μ k) z := by
    fun_prop
  have hinv : AnalyticAt ℂ
      (@Ring.inverse (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) _)
      (1 - z • KernelOperatorValue μ k) := by
    simpa only [hz.unit_spec] using
      (analyticAt_inverse (𝕜 := ℂ) (A := C(Q, ℂ) →L[ℂ] C(Q, ℂ)) hz.unit)
  have hi : AnalyticAt ℂ (fun w : ℂ => Ring.inverse (1 - w • KernelOperatorValue μ k)) z :=
    hinv.comp (f := fun w : ℂ => 1 - w • KernelOperatorValue μ k) ha
  have hh : AnalyticAt ℂ (fun w : ℂ =>
      -operatorDiagonal μ k (Ring.inverse (1 - w • KernelOperatorValue μ k))) z :=
    ((operatorDiagonal μ k).analyticAt _ |>.comp hi).neg
  have hu : ∀ᶠ w in 𝓝 z, IsUnit (1 - w • KernelOperatorValue μ k) :=
    ha.continuousAt.eventually ((Units.isOpen (R := C(Q, ℂ) →L[ℂ] C(Q, ℂ))).mem_nhds hz)
  have hf := (ClassicalEntireSeries.entire_functions μ k).1.analyticAt z
  have heq : deriv (FredholmDeterminantValue μ k) =ᶠ[𝓝 z]
      (FredholmDeterminantValue μ k) * (fun w =>
        -operatorDiagonal μ k (Ring.inverse (1 - w • KernelOperatorValue μ k))) :=
    hu.mono fun w hw => derivative_eq_mul_inverse μ k w hw
  have hlocal := locally_zero_of_deriv_eq_mul hf hh hzero heq
  have hfa : AnalyticOnNhd ℂ (FredholmDeterminantValue μ k) Set.univ :=
    fun w _ => (ClassicalEntireSeries.entire_functions μ k).1.analyticAt w
  have hglobal := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hlocal
  have h0 := hglobal (Set.mem_univ (0 : ℂ))
  rw [(ClassicalEntireSeries.values_at_zero μ k).1] at h0
  exact one_ne_zero h0

end

theorem invertibility : Spec.Invertibility.{u} := by
  intro Q _ _ _ _ μ _ k z
  constructor
  · exact determinant_ne_zero_of_isUnit μ k z
  · intro hz
    obtain ⟨hleft, hright⟩ := ClassicalResolventIdentities.two_sided_inverse μ k z hz
    exact isUnit_iff_exists.mpr
      ⟨ClassicalResolventIdentities.Spec.ResolventOperatorValue μ k z, hleft, hright⟩

theorem inverse_formula : Spec.InverseFormula.{u} := by
  intro Q _ _ _ _ μ _ k z hz f x
  have hu := (invertibility μ k z).mpr hz
  obtain ⟨hleft, _⟩ := ClassicalResolventIdentities.two_sided_inverse μ k z hz
  have he : Ring.inverse (1 - z • KernelOperatorValue μ k) =
      ClassicalResolventIdentities.Spec.ResolventOperatorValue μ k z := by
    apply hu.mul_left_cancel
    calc
      _ = 1 := Ring.mul_inverse_cancel _ hu
      _ = _ := hleft.symm
  rw [he]
  exact ClassicalResolventIdentities.resolvent_formula μ k z f x

theorem exceptional_discrete : Spec.ExceptionalDiscrete.{u} := by
  intro Q _ _ _ _ μ _ k z
  have hfa : AnalyticOnNhd ℂ (FredholmDeterminantValue μ k) Set.univ :=
    fun w _ => (ClassicalEntireSeries.entire_functions μ k).1.analyticAt w
  rcases (hfa z (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · have hglobal := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hzero
    have h0 := hglobal (Set.mem_univ (0 : ℂ))
    rw [(ClassicalEntireSeries.values_at_zero μ k).1] at h0
    exact (one_ne_zero h0).elim
  · exact hne

theorem exceptional_eigenvalues : Spec.ExceptionalEigenvalues.{u} := by
  intro Q _ _ _ _ μ _ k z
  by_cases hz : z = 0
  · subst z
    simp [(ClassicalEntireSeries.values_at_zero μ k).1]
  · have hcompact : ExpandedFA.Compactness.IsCompactLinearMap
        (KernelOperatorValue μ k).toLinearMap :=
      (ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr
        (ExpandedFA.IntegralOperators.ContinuousKernelCompactness.canonical_properties
          ℂ Q μ k).2.2.1
    have hspec := ExpandedFA.Fredholm.compact_nonzero_spectrum_iff_eigenvalue
      (KernelOperatorValue μ k) hcompact z⁻¹ (inv_ne_zero hz)
    have hfactor : algebraMap ℂ (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) z⁻¹ - KernelOperatorValue μ k =
        z⁻¹ • (1 - z • KernelOperatorValue μ k) := by
      rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, inv_mul_cancel₀ hz, one_smul]
    have hunit : IsUnit (algebraMap ℂ (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) z⁻¹ - KernelOperatorValue μ k) ↔
        IsUnit (1 - z • KernelOperatorValue μ k) := by
      rw [hfactor]
      exact isUnit_smul_iff (Units.mk0 z⁻¹ (inv_ne_zero hz)) _
    rw [and_iff_right hz, ← hspec, spectrum.mem_iff, hunit, invertibility μ k z]
    simp only [not_not]

/-- The entire functions, identities, actual inverse formula, and the complete
exceptional-parameter characterization for the original Fredholm series. -/
theorem classical_fredholm : Spec.FullTheorem.{u} :=
  ⟨ClassicalEntireSeries.entire_functions, ClassicalEntireSeries.values_at_zero,
    ClassicalEntireSeries.minor_kernel_identification,
    ClassicalResolventIdentities.kernel_identities,
    ClassicalResolventIdentities.diagonal_derivative,
    invertibility, inverse_formula, exceptional_discrete, exceptional_eigenvalues⟩

end ExpandedFA.FredholmDeterminant.ClassicalFredholm
