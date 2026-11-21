import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15CoordinateContinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BasisNormCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08BoundedInverse

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.C15CoordinateContinuity

open ExpandedFA.P1.C15Basis ExpandedFA.P1.BasisNormCompleteness

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

namespace CoordinateContinuityProof

/-- The closed sequence model is Banach. Evaluation at its limit is a bounded
bijection onto the original E, so bounded inverse bounds its algebraic inverse.
This avoids assigning a second normed-space instance to E. -/
theorem supNorm_bound_of_closed_range (P : ℕ → E →ₗ[𝕜] E)
    (hP : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x))
    (hc : IsClosed (Set.range (BasisNormProof.extension P hP))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ExpandedFA.P1.BasisNormCompleteness.Spec.partialSumSupNorm (fun N x => P N x) x ≤ C * ‖x‖ := by
  let A := BasisNormProof.extension P hP
  let S := A.range
  have : CompleteSpace S := hc.completeSpace_coe
  let T : S →L[𝕜] E := (ContinuousMap.evalCLM 𝕜 OnePoint.infty).comp S.subtypeL
  have hT : Function.Bijective T := by
    constructor
    · intro q r he
      obtain ⟨x, hx⟩ := q.property
      obtain ⟨y, hy⟩ := r.property
      have hxy : x = y := by
        change q.val OnePoint.infty = r.val OnePoint.infty at he
        rw [← hx, ← hy] at he
        exact he
      apply Subtype.ext
      rw [← hx, ← hy, hxy]
    · intro x
      exact ⟨⟨A x, LinearMap.mem_range_self A x⟩, rfl⟩
  obtain ⟨U, hUT, _, _⟩ := ExpandedFA.P1.C08BoundedInverse.bounded_inverse 𝕜 S E T hT
  refine ⟨‖U‖, norm_nonneg _, fun x => ?_⟩
  have hu : U x = (⟨A x, LinearMap.mem_range_self A x⟩ : S) := hUT ⟨A x, LinearMap.mem_range_self A x⟩
  have hb := U.le_opNorm x
  rw [hu] at hb
  change ‖A x‖ ≤ ‖U‖ * ‖x‖ at hb
  simpa only [A, BasisNormProof.extension_norm] using hb

omit [CompleteSpace E] in
/-- Every individual term is bounded by the finite supremum. -/
theorem norm_le_sup (P : ℕ → E → E)
    (hb : ∀ x, ∃ M : ℝ, ∀ N, ‖P N x‖ ≤ M) (N : ℕ) (x : E) :
    ‖P N x‖ ≤ ExpandedFA.P1.BasisNormCompleteness.Spec.partialSumSupNorm P x := by
  obtain ⟨M, hM⟩ := hb x
  exact le_ciSup (show BddAbove (Set.range fun n => ‖P n x‖) from
    ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩) N

end CoordinateContinuityProof

/-- Norm equivalence follows before any coordinate is assumed continuous. -/
theorem raw_basis_norm_equivalent {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      partialSumSupNorm (rawPartialSum h) x ≤ C * ‖x‖ := by
  apply CoordinateContinuityProof.supNorm_bound_of_closed_range
    (rawPartialSumLinearMap h) (rawPartialSum_tendsto h)
  rw [BasisNormProof.raw_extension_range h]
  exact BasisNormProof.admissible_closed e

/-- The bound on an increment bounds the algebraic coordinate functional. -/
theorem raw_coordinate_bound {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    {C : ℝ} (hC : ∀ x, partialSumSupNorm (rawPartialSum h) x ≤ C * ‖x‖)
    (i : ℕ) (x : E) : ‖rawCoordinates h x i‖ ≤ (2 * C / ‖e i‖) * ‖x‖ := by
  have hp (N : ℕ) : ‖rawPartialSum h N x‖ ≤ C * ‖x‖ :=
    (CoordinateContinuityProof.norm_le_sup _ (raw_basis_complete h).bounded N x).trans (hC x)
  have hi : 0 < ‖e i‖ := norm_pos_iff.mpr (h.1 i)
  have hh : ‖rawCoordinates h x i‖ * ‖e i‖ ≤ 2 * C * ‖x‖ := by
    rw [← norm_smul, ← BasisNormProof.raw_increment h x i]
    exact (norm_sub_le _ _).trans (by linarith [hp (i + 1), hp i])
  calc
    ‖rawCoordinates h x i‖ ≤ (2 * C * ‖x‖) / ‖e i‖ := (le_div_iff₀ hi).mpr hh
    _ = (2 * C / ‖e i‖) * ‖x‖ := by ring

/-- Boundedness of both algebraic maps, together with completeness and equivalence
of the actual supremum norm from the source. -/
theorem raw_coordinate_continuity : Spec.RawCoordinateContinuity := by
  intro 𝕜 E _ _ _ _ e h
  have hcomplete := raw_basis_complete h
  obtain ⟨C, hCpos, hC⟩ := raw_basis_norm_equivalent h
  refine ⟨hcomplete, ⟨C, hCpos, fun x => ⟨hcomplete.dominates x, hC x⟩⟩, ?_, ?_⟩
  · intro i
    exact ⟨(rawCoordinateLinearMap h i).mkContinuous (2 * C / ‖e i‖)
      (raw_coordinate_bound h hC i), fun x => rfl⟩
  · intro N
    refine ⟨(rawPartialSumLinearMap h N).mkContinuous C (fun x => ?_), fun x => rfl⟩
    exact (CoordinateContinuityProof.norm_le_sup _ hcomplete.bounded N x).trans (hC x)

omit [CompleteSpace E] in
/-- A raw finite expansion identifies E as a finite-dimensional space. -/
theorem finiteBasis_finiteDimensional {d : ℕ} {e : Fin d → E}
    (h : IsRawFiniteBasis (𝕜 := 𝕜) e) : FiniteDimensional 𝕜 E := by
  let A : (Fin d → 𝕜) →ₗ[𝕜] E :=
    { toFun := finiteSynthesis e
      map_add' := by
        intro a b
        simp [finiteSynthesis, ExpandedFA.P1.C15Basis.Spec.finiteSynthesis, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [finiteSynthesis, ExpandedFA.P1.C15Basis.Spec.finiteSynthesis, mul_smul, Finset.smul_sum] }
  exact FiniteDimensional.of_surjective A (fun x =>
    ⟨finiteCoordinates h x, finiteCoordinates_expansion h x⟩)

/-- The finite supremum norm comparison, including the zero-length list. -/
theorem finite_basis_norm_equivalent {d : ℕ} {e : Fin d → E}
    (h : IsRawFiniteBasis (𝕜 := 𝕜) e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      partialSumSupNorm (finitePartialSum h) x ≤ C * ‖x‖ := by
  let := finiteBasis_finiteDimensional h
  have hP (x : E) : Tendsto (fun N => finitePartialSumLinearMap h N x) atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    exact (finitePartialSum_of_le h N hN x).symm
  apply CoordinateContinuityProof.supNorm_bound_of_closed_range
    (finitePartialSumLinearMap h) hP
  exact (BasisNormProof.extension (finitePartialSumLinearMap h) hP).range.closed_of_finiteDimensional

/-- The complete norm and both bounded map families are retained in the finite
case; no positive-dimension assumption occurs. -/
theorem finite_coordinate_continuity : Spec.FiniteCoordinateContinuity := by
  intro 𝕜 E _ _ _ _ d e h
  let := finiteBasis_finiteDimensional h
  have hc := finite_basis_complete h
  obtain ⟨C, hCpos, hC⟩ := finite_basis_norm_equivalent h
  exact ⟨hc, ⟨C, hCpos, fun x => ⟨hc.dominates x, hC x⟩⟩,
    (fun i => ⟨(finiteCoordinateLinearMap h i).toContinuousLinearMap, fun x => rfl⟩),
    (fun N => ⟨(finitePartialSumLinearMap h N).toContinuousLinearMap, fun x => rfl⟩)⟩

omit [CompleteSpace E] in
/-- Uniqueness identifies the coefficients of a single basis vector. -/
theorem rawCoordinates_basis {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    (j : ℕ) : rawCoordinates h (e j) = Pi.single j 1 := by
  classical
  symm
  apply rawCoordinates_unique h
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  simp [orderedPartialSum, ExpandedFA.P1.C15Basis.Spec.orderedPartialSum, Pi.single_apply, hN]

omit [CompleteSpace E] in
/-- Finite biorthogonality also follows solely from algebraic uniqueness. -/
theorem finiteCoordinates_basis {d : ℕ} {e : Fin d → E}
    (h : IsRawFiniteBasis (𝕜 := 𝕜) e) (j : Fin d) :
    finiteCoordinates h (e j) = Pi.single j 1 := by
  classical
  symm
  apply finiteCoordinates_unique h
  simp [finiteSynthesis, ExpandedFA.P1.C15Basis.Spec.finiteSynthesis, Pi.single_apply]

/-- Construction of the conditional native basis, after continuity is proved. -/
theorem raw_native_basis : Spec.RawNativeBasis := by
  intro 𝕜 E _ _ _ _ e h
  classical
  choose f hf using (raw_coordinate_continuity h).2.2.1
  let b : SchauderBasis 𝕜 E :=
    { basis := e
      coord := f
      ortho := by
        intro i j
        rw [hf]
        by_cases hij : i = j <;>
          simpa [Pi.single_apply, hij] using congrFun (rawCoordinates_basis h j) i
      expansion := by
        intro x
        simp only [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
        have hx := rawCoordinates_tendsto h x
        change Tendsto (fun N => ∑ i ∈ Finset.range N,
          ExpandedFA.P1.C15Basis.Spec.rawCoordinates h x i • e i) atTop (𝓝 x) at hx
        simpa only [Function.comp_def, hf] using hx }
  refine ⟨b, rfl, hf, fun N x => ?_⟩
  simp only [SchauderBasis.proj_apply, b, hf]
  rfl

/-- A finite native basis preserves the list, coordinates and every truncation. -/
theorem finite_native_basis : Spec.FiniteNativeBasis := by
  intro 𝕜 E _ _ _ _ d e h
  classical
  choose f hf using (finite_coordinate_continuity h).2.2.1
  let b : UnconditionalSchauderBasis (Fin d) 𝕜 E :=
    { basis := e
      coord := f
      ortho := by
        intro i j
        rw [hf]
        by_cases hij : i = j <;>
          simpa [Pi.single_apply, hij] using congrFun (finiteCoordinates_basis h j) i
      expansion := by
        intro x
        simpa only [hf,
          show (∑ i, finiteCoordinates h x i • e i) = x from finiteCoordinates_expansion h x]
          using hasSum_fintype (fun i => finiteCoordinates h x i • e i) }
  refine ⟨b, rfl, hf, fun N x => ?_⟩
  simp only [GeneralSchauderBasis.proj_apply, b, hf]
  rfl

end ExpandedFA.P1.C15CoordinateContinuity
