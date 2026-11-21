import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceBasisCyclicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceNormIdeal
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
universe u v w z
namespace ExpandedFA.TraceIdeals.TraceBasisCyclicity
open TraceClassDefinitions
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

theorem diagonal_trace : Spec.DiagonalTrace.{u,v,z} := TraceClassDefinitions.diagonal_trace

theorem trace_bound : Spec.TraceBound.{u,v} := TraceClassDefinitions.trace_bound

theorem rankOne_trace : Spec.RankOneTrace.{u,v} := TraceClassDefinitions.rankOne_trace

omit [CompleteSpace H] in
/-- The two Bessel inequalities control an arbitrary rank-one diagonal,
without requiring either vector to be a unit vector. -/
lemma sum_norm_inner_mul_inner_le {ι : Type z} (b : HilbertBasis ι 𝕜 H)
    (x y : H) (s : Finset ι) :
    ∑ i ∈ s, ‖inner 𝕜 y (b i) * inner 𝕜 (b i) x‖ ≤
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have hp (i : ι) : ‖inner 𝕜 y (b i) * inner 𝕜 (b i) x‖ ≤
      (‖inner 𝕜 (b i) y‖ ^ 2 + ‖inner 𝕜 (b i) x‖ ^ 2) / 2 := by
    rw [norm_mul, norm_inner_symm y]
    nlinarith [sq_nonneg (‖inner 𝕜 (b i) y‖ - ‖inner 𝕜 (b i) x‖)]
  calc
    _ ≤ ∑ i ∈ s, (‖inner 𝕜 (b i) y‖ ^ 2 + ‖inner 𝕜 (b i) x‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = ((∑ i ∈ s, ‖inner 𝕜 (b i) y‖ ^ 2) +
        ∑ i ∈ s, ‖inner 𝕜 (b i) x‖ ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by
      have h₁ := b.orthonormal.sum_inner_products_le (s := s) y
      have h₂ := b.orthonormal.sum_inner_products_le (s := s) x
      linarith

/-- Absolute summation of a bounded-vector nuclear expansion computes the
shared trace. Both the expansion index and basis index may be uncountable. -/
lemma trace_of_expansion {J : Type*} (T : H →L[𝕜] H)
    (c : J → ℝ) (x y : J → H) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (M : ℝ) (hM : ∀ j, (‖x j‖ ^ 2 + ‖y j‖ ^ 2) / 2 ≤ M)
    (hexp : ∀ v, HasSum (fun j => ((c j : 𝕜) * inner 𝕜 (y j) v) • x j) (T v)) :
    trace T = ∑' j, (c j : 𝕜) * inner 𝕜 (y j) (x j) := by
  let b := TraceClassDefinitions.Spec.chosenBasis (𝕜 := 𝕜) (H := H)
  let d : J → _ → 𝕜 := fun j i => (c j : 𝕜) *
    (inner 𝕜 (y j) (b i) * inner 𝕜 (b i) (x j))
  have hrow (j : J) : Summable (fun i => ‖d j i‖) :=
    (((b.summable_inner_mul_inner (y j) (x j)).mul_left (c j : 𝕜)).norm)
  have hrow_bound (j : J) : (∑' i, ‖d j i‖) ≤ c j * M := by
    simp only [d, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hc j), tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (hc j)
    simpa only [norm_mul] using (tsum_le_of_sum_le' (by positivity)
      (sum_norm_inner_mul_inner_le b (x j) (y j))).trans (hM j)
  have habs : Summable (fun p : J × _ => ‖d p.1 p.2‖) :=
    (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
      ⟨hrow, (hs.mul_right M).of_nonneg_of_le
        (fun j => tsum_nonneg (fun i => norm_nonneg _)) hrow_bound⟩
  have hab : Summable (Function.uncurry d) := habs.of_norm
  have hdiag (i) : (∑' j, d j i) = inner 𝕜 (b i) (T (b i)) := by
    have hh := (hexp (b i)).mapL (innerSL 𝕜 (b i))
    simp only [innerSL_apply_apply, inner_smul_right] at hh
    convert hh.tsum_eq using 1
    congr 1
    funext j
    dsimp [d]
    ring
  change (∑' i, inner 𝕜 (b i) (T (b i))) = _
  calc
    _ = ∑' i, ∑' j, d j i := tsum_congr (fun i => (hdiag i).symm)
    _ = ∑' j, ∑' i, d j i := hab.tsum_comm
    _ = _ := tsum_congr (fun j =>
      ((b.hasSum_inner_mul_inner (y j) (x j)).mul_left (c j : 𝕜)).tsum_eq)

/-- Rectangular cyclicity with the trace-class factor in the first slot. -/
lemma trace_comp_comm (T : H →L[𝕜] K) (A : K →L[𝕜] H) (hT : IsTraceClass T) :
    trace (A.comp T) = trace (T.comp A) := by
  obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system 𝕜 H K T hT.1
  have hs := (singularSystem_sum 𝕜 H K T hT S).1
  have hleft : trace (A.comp T) =
      ∑' j, (S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) (A (S.leftVector j)) := by
    apply trace_of_expansion (A.comp T) S.sigma (fun j => A (S.leftVector j))
      S.rightVector (fun j => (S.positive j).le) hs ((‖A‖ ^ 2 + 1) / 2)
    · intro j
      have hb := A.le_opNorm (S.leftVector j)
      rw [S.left_orthonormal.norm_eq_one j, mul_one] at hb
      rw [S.right_orthonormal.norm_eq_one j]
      nlinarith [sq_le_sq₀ (norm_nonneg (A (S.leftVector j))) (norm_nonneg A) |>.mpr hb]
    · intro x
      simpa only [ContinuousLinearMap.comp_apply, map_smul] using (S.expansion x).mapL A
  have hright : trace (T.comp A) =
      ∑' j, (S.sigma j : 𝕜) * inner 𝕜 (A.adjoint (S.rightVector j)) (S.leftVector j) := by
    apply trace_of_expansion (T.comp A) S.sigma S.leftVector
      (fun j => A.adjoint (S.rightVector j)) (fun j => (S.positive j).le) hs
      ((1 + ‖A.adjoint‖ ^ 2) / 2)
    · intro j
      have hb := A.adjoint.le_opNorm (S.rightVector j)
      rw [S.right_orthonormal.norm_eq_one j, mul_one] at hb
      rw [S.left_orthonormal.norm_eq_one j]
      nlinarith [sq_le_sq₀ (norm_nonneg (A.adjoint (S.rightVector j))) (norm_nonneg A.adjoint) |>.mpr hb]
    · intro x
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left] using
        S.expansion (A x)
  rw [hleft, hright]
  exact tsum_congr (fun j => by rw [ContinuousLinearMap.adjoint_inner_left])

theorem rectangular_cyclicity : Spec.RectangularCyclicity.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T A h
  rcases h with hT | hA
  · have hl := (TraceNormIdeal.two_sided_ideal 𝕜 H K H H T A
      (ContinuousLinearMap.id 𝕜 H) hT).1
    have hr := (TraceNormIdeal.two_sided_ideal 𝕜 H K K K T
      (ContinuousLinearMap.id 𝕜 K) A hT).1
    simpa only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] using
      And.intro hl (And.intro hr (trace_comp_comm T A hT))
  · have hl := (TraceNormIdeal.two_sided_ideal 𝕜 K H H H A
      (ContinuousLinearMap.id 𝕜 H) T hA).1
    have hr := (TraceNormIdeal.two_sided_ideal 𝕜 K H K K A T
      (ContinuousLinearMap.id 𝕜 K) hA).1
    simpa only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] using
      And.intro hl (And.intro hr (trace_comp_comm A T hA).symm)

end ExpandedFA.TraceIdeals.TraceBasisCyclicity
