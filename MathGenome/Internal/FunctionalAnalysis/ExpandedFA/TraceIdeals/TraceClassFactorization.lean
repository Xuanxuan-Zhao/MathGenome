import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassFactorization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceBasisCyclicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import Mathlib.Analysis.Real.Sqrt

noncomputable section
set_option maxHeartbeats 800000
universe u v w z a b
namespace ExpandedFA.TraceIdeals.TraceClassFactorization
open TraceClassDefinitions HilbertSchmidtDefinitions HilbertSchmidtBasis
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

/-- A finite orthonormal family contributes at most the full S₂ square norm. -/
lemma orthonormal_column_bound {ι : Type a} [Fintype ι]
    (T : HilbertSchmidtMap (𝕜 := 𝕜) (H := H) (K := K))
    (e : ι → H) (he : Orthonormal 𝕜 e) :
    ∑ i, ‖T.val (e i)‖ ^ 2 ≤ hilbertSchmidtNorm T ^ 2 := by
  classical
  obtain ⟨s, b, hs, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let f : ι → s := fun i => ⟨e i, hs (Set.mem_range_self i)⟩
  have hf : Function.Injective f := fun i j hij =>
    he.linearIndependent.injective (congrArg Subtype.val hij)
  have hbf (i : ι) : b (f i) = e i := by rw [hb]
  have hsum := (finiteness_in_basis T.val b (hilbertBasis_isBasis b)).mp T.property
  rw [(normSquare_in_basis T b (hilbertBasis_isBasis b)).2]
  have h : (∑' i : ι, ‖T.val (e i)‖ ^ 2) ≤ ∑' j : s, ‖T.val (b j)‖ ^ 2 := by
    apply Summable.tsum_le_tsum_of_inj (f := fun i : ι => ‖T.val (e i)‖ ^ 2)
      (g := fun j : s => ‖T.val (b j)‖ ^ 2) f hf
    · intro j _
      exact sq_nonneg _
    · intro i
      rw [hbf i]
    · exact (hasSum_fintype _).summable
    · exact hsum
  simpa only [tsum_fintype] using h


/-- Finite-family characterization plus Cauchy–Schwarz proves the product
bound directly, without a countability hypothesis on any basis. -/
theorem product_bound : Spec.ProductBound.{u,v,w,z} := by
  intro 𝕜 _ H K G _ _ _ _ _ _ _ _ _ A B
  have hAc := compactness A.val A.property
  have hc := Compactness.compact_precomp A.val.toLinearMap B.val hAc
  apply TraceNormIdeal.traceClass_of_finite_family_bound (A.val.comp B.val) hc
    (hilbertSchmidtNorm A * hilbertSchmidtNorm B)
  intro n a b ha hb
  let A' : HilbertSchmidtMap (𝕜 := 𝕜) (H := K) (K := G) :=
    ⟨A.val.adjoint, (adjoint_finiteness A.val).mpr A.property⟩
  have hA := orthonormal_column_bound A' a ha
  have hB := orthonormal_column_bound B b hb
  have hAN : hilbertSchmidtNorm A' = hilbertSchmidtNorm A := adjoint_norm A _
  rw [hAN] at hA
  calc
    _ ≤ ∑ i, ‖A.val.adjoint (a i)‖ * ‖B.val (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
      exact norm_inner_le_norm _ _
    _ ≤ Real.sqrt (∑ i, ‖A.val.adjoint (a i)‖ ^ 2) *
        Real.sqrt (∑ i, ‖B.val (b i)‖ ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i => ‖A.val.adjoint (a i)‖) (fun i => ‖B.val (b i)‖)
    _ ≤ hilbertSchmidtNorm A * hilbertSchmidtNorm B := by
      apply mul_le_mul
      · exact (Real.sqrt_le_sqrt hA).trans_eq (Real.sqrt_sq (Real.sqrt_nonneg _))
      · exact (Real.sqrt_le_sqrt hB).trans_eq (Real.sqrt_sq (Real.sqrt_nonneg _))
      · positivity
      · exact Real.sqrt_nonneg _

/-- Square-summable singular half-weights give both synthesis maps. Their
composition with the adjoint reproduces the full singular expansion. -/
theorem factorization : Spec.Factorization.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T
  constructor
  · intro hT
    obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system 𝕜 H K T hT.1
    have hσ := (singularSystem_sum 𝕜 H K T hT S).1
    let b : HilbertBasis S.Index 𝕜 (lp (fun _ : S.Index => 𝕜) 2) :=
      HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)
    have hl (i : S.Index) : ‖(Real.sqrt (S.sigma i) : 𝕜) • S.leftVector i‖ ^ 2 =
        S.sigma i := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
        S.left_orthonormal.norm_eq_one i, mul_one, Real.sq_sqrt (S.positive i).le]
    have hr (i : S.Index) : ‖(Real.sqrt (S.sigma i) : 𝕜) • S.rightVector i‖ ^ 2 =
        S.sigma i := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
        S.right_orthonormal.norm_eq_one i, mul_one, Real.sq_sqrt (S.positive i).le]
    let cL : lp (fun _ : S.Index => K) 2 :=
      ⟨fun i => (Real.sqrt (S.sigma i) : 𝕜) • S.leftVector i,
        memℓp_gen (by simpa [hl] using hσ)⟩
    let cR : lp (fun _ : S.Index => H) 2 :=
      ⟨fun i => (Real.sqrt (S.sigma i) : 𝕜) • S.rightVector i,
        memℓp_gen (by simpa [hr] using hσ)⟩
    let A := columnOperator b cL
    let C := columnOperator b cR
    have hA : IsHilbertSchmidt A := columnOperator_finiteness b cL
    have hC : IsHilbertSchmidt C := columnOperator_finiteness b cR
    refine ⟨S.Index, S.countable, A, C.adjoint, hA, (adjoint_finiteness C).mpr hC, ?_⟩
    ext x
    change A (C.adjoint x) = T x
    rw [show A = columnOperator b cL from rfl, columnOperator_apply]
    have hcoord (i : S.Index) : b.repr (C.adjoint x) i =
        (Real.sqrt (S.sigma i) : 𝕜) * inner 𝕜 (S.rightVector i) x := by
      rw [b.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right]
      change inner 𝕜 (columnOperator b cR (b i)) x = _
      rw [columnOperator_basis]
      change inner 𝕜 ((Real.sqrt (S.sigma i) : 𝕜) • S.rightVector i) x = _
      simp only [inner_smul_left, RCLike.conj_ofReal]
    convert (S.expansion x).tsum_eq using 1
    apply tsum_congr
    intro i
    rw [hcoord]
    change ((Real.sqrt (S.sigma i) : 𝕜) * inner 𝕜 (S.rightVector i) x) •
      ((Real.sqrt (S.sigma i) : 𝕜) • S.leftVector i) = _
    rw [smul_smul]
    congr 1
    have hsqrt : (Real.sqrt (S.sigma i) : 𝕜) * (Real.sqrt (S.sigma i) : 𝕜) =
        (S.sigma i : 𝕜) := by
      rw [← RCLike.ofReal_mul, ← pow_two, Real.sq_sqrt (S.positive i).le]
    calc
      _ = ((Real.sqrt (S.sigma i) : 𝕜) * (Real.sqrt (S.sigma i) : 𝕜)) *
        inner 𝕜 (S.rightVector i) x := by ring
      _ = _ := by rw [hsqrt]
  · rintro ⟨ι, _, A, B, hA, hB, rfl⟩
    exact (product_bound 𝕜 H K (lp (fun _ : ι => 𝕜) 2) ⟨A, hA⟩ ⟨B, hB⟩).1

/-- The already established trace-norm and trace conclusions are retained
with the same canonical singular-value and diagonal-sum definitions. -/
theorem normed_ideal_axioms : Spec.NormedIdealAxioms.{u,v,w} :=
  TraceNormIdeal.normed_ideal_axioms

theorem trace_norm_complete : Spec.TraceNormComplete.{u,v,w} :=
  TraceNormIdeal.trace_norm_complete

theorem two_sided_ideal : Spec.TwoSidedIdeal.{u,v,w,a,b} :=
  TraceNormIdeal.two_sided_ideal

theorem diagonal_trace : Spec.DiagonalTrace.{u,v,z} :=
  TraceBasisCyclicity.diagonal_trace

theorem trace_bound : Spec.TraceBound.{u,v} := TraceBasisCyclicity.trace_bound

theorem rectangular_cyclicity : Spec.RectangularCyclicity.{u,v,w} :=
  TraceBasisCyclicity.rectangular_cyclicity

end ExpandedFA.TraceIdeals.TraceClassFactorization
