import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidt
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceClassFactorization

/-! The trace identification completes the existing matrix Hilbert realization.
Absolute summability on the product of arbitrary basis index sets justifies
Parseval and the exchange of sums, including nonseparable and zero spaces. -/
noncomputable section
universe u v w z t a b
namespace ExpandedFA.TraceIdeals.HilbertSchmidt
open HilbertSchmidtDefinitions HilbertSchmidtBasis TraceClassDefinitions

section
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

lemma adjoint_comp_traceClass
    (S T : HilbertSchmidtMap (𝕜 := 𝕜) (H := H) (K := K)) :
    IsTraceClass (S.val.adjoint.comp T.val) :=
  (TraceClassFactorization.product_bound 𝕜 H H K
    ⟨S.val.adjoint, (adjoint_finiteness S.val).mpr S.property⟩ T).1

theorem trace_inner_product : Spec.TraceInnerProduct.{u,v,w,a,b} := by
  intro 𝕜 _ H K _ _ _ _ _ _ S T ι κ e f he hf
  let cS : lp (fun _ : ι × κ => 𝕜) 2 :=
    ⟨_, matrix_memℓp S.val S.property e f he hf⟩
  let cT : lp (fun _ : ι × κ => 𝕜) 2 :=
    ⟨_, matrix_memℓp T.val T.property e f he hf⟩
  have hs : Summable (fun p : ι × κ =>
      star (inner 𝕜 (f p.2) (S.val (e p.1))) * inner 𝕜 (f p.2) (T.val (e p.1))) := by
    simpa only [cS, cT, RCLike.inner_apply', ← RCLike.star_def] using
      (lp.summable_inner (𝕜 := 𝕜) cS cT)
  have htc := adjoint_comp_traceClass S T
  refine ⟨htc, hs, ?_⟩
  have het := (ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 H ι e he.1).mp he
  have hft := (ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 K κ f hf.1).mp hf
  let E : HilbertBasis ι 𝕜 H := HilbertBasis.mk he.1 het.ge
  let F : HilbertBasis κ 𝕜 K := HilbertBasis.mk hf.1 hft.ge
  have hE : ∀ i, E i = e i := fun i => congrFun (HilbertBasis.coe_mk he.1 het.ge) i
  have hF : ∀ j, F j = f j := fun j => congrFun (HilbertBasis.coe_mk hf.1 hft.ge) j
  have hd := (TraceBasisCyclicity.diagonal_trace 𝕜 H (S.val.adjoint.comp T.val) htc ι E).2.tsum_eq
  calc
    trace (S.val.adjoint.comp T.val) = ∑' i, inner 𝕜 (S.val (e i)) (T.val (e i)) := by
      change TraceClassDefinitions.Spec.TraceValue (S.val.adjoint.comp T.val) = _
      rw [← hd]
      apply tsum_congr
      intro i
      rw [hE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    _ = ∑' i, ∑' j, star (inner 𝕜 (f j) (S.val (e i))) *
        inner 𝕜 (f j) (T.val (e i)) := by
      apply tsum_congr
      intro i
      rw [← F.tsum_inner_mul_inner (S.val (e i)) (T.val (e i))]
      apply tsum_congr
      intro j
      rw [hF, ← inner_conj_symm]
      rfl
    _ = _ := hs.tsum_prod.symm

end

theorem complete_trace_hilbert_realization : Spec.CompleteTraceHilbertRealization.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _
  obtain ⟨E, nE, iE, cE, j, hj, hr, hn, hi⟩ :=
    complete_hilbert_realization (𝕜 := 𝕜) (H := H) (K := K)
  letI := nE
  letI := iE
  letI := cE
  refine ⟨E, nE, iE, cE, j, hj, hr, hn, ?_⟩
  intro x y
  have hx : IsHilbertSchmidt (j x) := (hr (j x)).mp ⟨x, rfl⟩
  have hy : IsHilbertSchmidt (j y) := (hr (j y)).mp ⟨y, rfl⟩
  obtain ⟨ι, e, _⟩ := exists_hilbertBasis 𝕜 H
  obtain ⟨κ, f, _⟩ := exists_hilbertBasis 𝕜 K
  have he := hilbertBasis_isBasis e
  have hf := hilbertBasis_isBasis f
  have ht := trace_inner_product ⟨j x, hx⟩ ⟨j y, hy⟩ e f he hf
  exact ⟨ht.1, (hi e f he hf x y).2.trans ht.2.2.symm⟩

/- The remaining assertions retain the exact shared objects and hypotheses. -/
theorem basis_independence : Spec.BasisIndependence.{u,v,w,a,b} :=
  HilbertSchmidtDefinitions.basis_independence
theorem finiteness_in_basis : Spec.FinitenessInBasis.{u,v,w,a} :=
  HilbertSchmidtDefinitions.finiteness_in_basis
theorem normSquare_in_basis : Spec.NormSquareInBasis.{u,v,w,a} :=
  HilbertSchmidtDefinitions.normSquare_in_basis
theorem adjoint_norm : Spec.AdjointNorm.{u,v,w} := HilbertSchmidtBasis.adjoint_norm
theorem linear_subspace : Spec.LinearSubspace.{u,v,w} := HilbertSchmidtBasis.linear_subspace
theorem ideal_finiteness : Spec.IdealFiniteness.{u,v,w,z,t} := HilbertSchmidtBasis.ideal_finiteness
theorem ideal_norm_bound : Spec.IdealNormBound.{u,v,w,z,t} := HilbertSchmidtBasis.ideal_norm_bound
theorem compactness : Spec.Compactness.{u,v,w} := HilbertSchmidtBasis.compactness
theorem singular_norm_identity : Spec.SingularNormIdentity.{u,v,w} :=
  HilbertSchmidtBasis.singular_norm_identity
theorem kernel_isometry : Spec.KernelIsometry.{v,w} := HilbertSchmidtKernels.kernel_isometry
theorem unique_kernel : Spec.UniqueKernel.{v,w} := HilbertSchmidtKernels.unique_kernel
theorem kernel_ae_uniqueness : Spec.KernelAEUniqueness.{v,w} :=
  HilbertSchmidtKernels.kernel_ae_uniqueness
theorem integral_representation : Spec.IntegralRepresentation.{v,w} :=
  HilbertSchmidtKernels.integral_representation

end ExpandedFA.TraceIdeals.HilbertSchmidt
