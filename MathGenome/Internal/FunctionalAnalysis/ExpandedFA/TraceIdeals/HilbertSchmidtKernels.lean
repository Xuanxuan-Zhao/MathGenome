import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2HilbertSchmidt

/-! Surjectivity of the original kernel assignment. Matrix coefficients belong
to ℓ² on arbitrary basis index sets. Synthesis in the product Hilbert basis
therefore constructs an ordinary product L² class; no pointwise uncountable
sum or separability assumption is used. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal
universe u v a b
namespace ExpandedFA.TraceIdeals.HilbertSchmidtKernels
open HilbertSchmidtDefinitions
open ExpandedFA.PartV.L2Kernel (kernelOperator)
open ExpandedFA.PartV.L2HilbertSchmidt

variable {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- Synthesize the matrix of a Hilbert–Schmidt map in the product basis. -/
lemma exists_kernel (T : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ) (hT : IsHilbertSchmidt T) :
    ∃ k : Lp 𝕜 2 (μ.prod ν), kernelOperator μ ν k = T := by
  obtain ⟨ι, e, _⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 ν)
  obtain ⟨κ, f, _⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 μ)
  have he := HilbertSchmidtBasis.hilbertBasis_isBasis e
  have hf := HilbertSchmidtBasis.hilbertBasis_isBasis f
  let p : ι × κ → Lp 𝕜 2 (μ.prod ν) := fun ij => productVector μ ν (f ij.2) (e ij.1)
  have hp : HilbertSchmidtDefinitions.Spec.IsBasis (𝕜 := 𝕜) p := product_basis μ ν e f he hf
  have htotal := (ExpandedFA.Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 _ _ p hp.1).mp hp
  let B : HilbertBasis (ι × κ) 𝕜 (Lp 𝕜 2 (μ.prod ν)) := HilbertBasis.mk hp.1 htotal.ge
  have hB : ∀ ij, B ij = p ij := fun ij => congrFun (HilbertBasis.coe_mk hp.1 htotal.ge) ij
  let c : lp (fun _ : ι × κ => 𝕜) 2 :=
    ⟨fun ij => ⟪f ij.2, T (e ij.1)⟫_𝕜, HilbertSchmidtBasis.matrix_memℓp T hT e f he hf⟩
  let k := B.repr.symm c
  have hcoef (i : ι) (j : κ) :
      ⟪f j, kernelOperator μ ν k (e i)⟫_𝕜 = ⟪f j, T (e i)⟫_𝕜 := by
    rw [← productVector_coefficient]
    change ⟪p (i,j), k⟫_𝕜 = _
    rw [← hB (i,j), ← B.repr_apply_apply]
    change (B.repr (B.repr.symm c)) (i,j) = _
    rw [B.repr.apply_symm_apply]
  have hcolumn (i : ι) : kernelOperator μ ν k (e i) = T (e i) := by
    apply sub_eq_zero.mp
    apply eq_zero_of_basis_coefficients f hf
    intro j
    rw [inner_sub_right, hcoef, sub_self]
  refine ⟨k, ?_⟩
  ext1 x
  have hK := (kernelOperator μ ν k).hasSum (e.hasSum_repr x)
  have hTx := T.hasSum (e.hasSum_repr x)
  simp only [map_smul, hcolumn] at hK hTx
  exact hK.unique hTx

/-- Equal canonical operators have the same ordinary a.e. kernel class. -/
lemma kernel_injective : Function.Injective (kernelOperator (𝕜 := 𝕜) μ ν) := by
  intro k l h
  apply sub_eq_zero.mp
  apply kernel_eq_zero μ ν (k - l)
  change ExpandedFA.PartV.L2KernelCompact.kernelAssignment μ ν (k - l) = 0
  rw [map_sub]
  change kernelOperator μ ν k - kernelOperator μ ν l = 0
  exact sub_eq_zero.mpr h

theorem kernel_isometry : Spec.KernelIsometry.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k
  refine ⟨kernel_hilbertSchmidt μ ν k, ?_⟩
  intro h
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg k)).mp
  exact (kernel_norm_identity μ ν k h).trans (kernel_integral_square μ ν k)

theorem unique_kernel : Spec.UniqueKernel.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ T hT
  obtain ⟨k, hk⟩ := exists_kernel μ ν T hT
  refine ⟨k, hk, ?_⟩
  intro l hl
  exact kernel_injective μ ν (hl.trans hk.symm)

theorem kernel_ae_uniqueness : Spec.KernelAEUniqueness.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ k l
  constructor
  · intro h
    exact (kernel_injective μ ν h) ▸ Filter.EventuallyEq.rfl
  · intro h
    exact congrArg (kernelOperator μ ν) (Lp.ext h)

theorem integral_representation : Spec.IntegralRepresentation.{u,v} := by
  intro X Y 𝕜 _ _ _ μ ν _ _ T hT
  obtain ⟨k, hk⟩ := exists_kernel μ ν T hT
  refine ⟨k, hk, ?_, ?_⟩
  · intro f
    rw [← hk]
    exact ExpandedFA.PartV.L2KernelCompact.kernelOperator_coe μ ν k f
  · subst T
    exact (kernel_isometry μ ν k).2 hT

end ExpandedFA.TraceIdeals.HilbertSchmidtKernels
