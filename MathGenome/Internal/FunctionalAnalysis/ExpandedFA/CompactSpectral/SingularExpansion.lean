import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.CompactNormalClassification
import Mathlib.Tactic.FieldSimp

/-!
Apply the compact self-adjoint spectral theorem to the Gram operator T†T.
For a unit eigenvector e with eigenvalue a, a = ‖T e‖²; hence the nonzero
eigenvalues are positive. Normalize T e to obtain the left singular vectors.
The orthogonal complements are identified with the entire kernels, including
nonseparable kernels. All vector expansions use norm `HasSum`.
-/

noncomputable section
universe u v w z
namespace ExpandedFA.CompactSpectral.SingularExpansion
open scoped InnerProductSpace

variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

/-- The real Gram eigenvalue of a unit vector is the squared image norm. -/
lemma gram_eigenvalue_eq_norm_sq (T : H →L[𝕜] G) {e : H} {a : ℝ}
    (he : ‖e‖ = 1) (ha : (ContinuousLinearMap.adjoint T) (T e) = (a : 𝕜) • e) :
    a = ‖T e‖ ^ 2 := by
  have h := congrArg (fun y => RCLike.re (inner 𝕜 e y)) ha
  simpa [ContinuousLinearMap.adjoint_inner_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, he] using h.symm

/-- Normalizing the images of Gram eigenvectors produces an orthonormal family. -/
lemma gram_normalized_images_orthonormal {J : Type z} (T : H →L[𝕜] G)
    (e : J → H) (a : J → ℝ) (he : Orthonormal 𝕜 e)
    (ha : ∀ j, (ContinuousLinearMap.adjoint T) (T (e j)) = (a j : 𝕜) • e j)
    (hne : ∀ j, ‖T (e j)‖ ≠ 0) :
    Orthonormal 𝕜 (fun j => ((‖T (e j)‖ : ℝ) : 𝕜)⁻¹ • T (e j)) := by
  constructor
  · intro j
    simp only [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (hne j)
  · intro i j hij
    have hinner : inner 𝕜 (T (e i)) (T (e j)) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, ha j, inner_smul_right,
        he.inner_eq_zero hij, mul_zero]
    simp only [inner_smul_left, inner_smul_right, hinner, mul_zero]

/-- Complete existence of a compact singular system. -/
theorem compact_singular_system : Spec.Existence.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ T hT
  let S := (ContinuousLinearMap.adjoint T).comp T
  have hTc : IsCompactOperator T :=
    (ExpandedFA.Compactness.compact_iff_isCompactOperator T.toLinearMap).mp hT
  have hc : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue S.toLinearMap :=
    (ExpandedFA.Compactness.compact_iff_isCompactOperator S.toLinearMap).mpr
      (hTc.clm_comp T.adjoint)
  have hs : IsSelfAdjoint S := by
    apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    simp [S, ContinuousLinearMap.adjoint_comp]
  obtain ⟨J, hJ, e, a, he, ha, hM, hcompl, hexp, hmult, hfin⟩ :=
    CompactNormalClassification.selfAdjoint_expansion 𝕜 H S hs hc
  letI : Countable J := hJ
  have hker : S.ker = T.ker := T.ker_adjoint_comp_self
  have ha' (j : J) : (ContinuousLinearMap.adjoint T) (T (e j)) = (a j : 𝕜) • e j :=
    (ha j).2
  have haeq (j : J) : a j = ‖T (e j)‖ ^ 2 :=
    gram_eigenvalue_eq_norm_sq T (he.norm_eq_one j) (ha' j)
  have hn (j : J) : ‖T (e j)‖ ≠ 0 := by
    intro hz
    exact (ha j).1 (by rw [haeq j, hz, zero_pow (by decide)])
  let σ : J → ℝ := fun j => ‖T (e j)‖
  let f : J → G := fun j => ((σ j : 𝕜)⁻¹) • T (e j)
  have hσ (j : J) : 0 < σ j := lt_of_le_of_ne (norm_nonneg _) (hn j).symm
  have hσK (j : J) : (σ j : 𝕜) ≠ 0 := by exact_mod_cast (ne_of_gt (hσ j))
  have hf : Orthonormal 𝕜 f := gram_normalized_images_orthonormal T e a he ha' hn
  have hTf (j : J) : T (e j) = (σ j : 𝕜) • f j := by
    simp [f, smul_smul, hσK j]
  have hAf (j : J) : ContinuousLinearMap.adjoint T (f j) = (σ j : 𝕜) • e j := by
    rw [show f j = (σ j : 𝕜)⁻¹ • T (e j) from rfl, map_smul, ha' j, smul_smul]
    congr 1
    rw [haeq j]
    change (σ j : 𝕜)⁻¹ * ((σ j ^ 2 : ℝ) : 𝕜) = (σ j : 𝕜)
    push_cast
    field_simp
  have hright : (Submodule.span 𝕜 (Set.range e)).topologicalClosure = T.ker.orthogonal := by
    rw [hM, hker]
  have hperpe : (Submodule.span 𝕜 (Set.range e)).orthogonal = T.ker := by
    rw [← Submodule.orthogonal_closure, hright, Submodule.orthogonal_orthogonal]
  have hperpf : (Submodule.span 𝕜 (Set.range f)).orthogonal =
      (ContinuousLinearMap.adjoint T).ker := by
    ext y
    constructor
    · intro hy
      have hy' := (CompactNormalClassification.orthogonal_span_range_iff f y).mp hy
      have hAy : ContinuousLinearMap.adjoint T y ∈ T.ker := by
        rw [← hperpe]
        apply (CompactNormalClassification.orthogonal_span_range_iff e _).mpr
        intro j
        rw [ContinuousLinearMap.adjoint_inner_right, hTf j, inner_smul_left,
          hy' j, mul_zero]
      have hz : inner 𝕜 (ContinuousLinearMap.adjoint T y) (ContinuousLinearMap.adjoint T y) = 0 := by
        rw [ContinuousLinearMap.adjoint_inner_left, show T (ContinuousLinearMap.adjoint T y) = 0 from hAy,
          inner_zero_right]
      exact inner_self_eq_zero.mp hz
    · intro hy
      apply (CompactNormalClassification.orthogonal_span_range_iff f y).mpr
      intro j
      change ContinuousLinearMap.adjoint T y = 0 at hy
      simp only [f, inner_smul_left, ← ContinuousLinearMap.adjoint_inner_right, hy,
        inner_zero_right, mul_zero]
  have hleft : (Submodule.span 𝕜 (Set.range f)).topologicalClosure =
      (ContinuousLinearMap.adjoint T).ker.orthogonal := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperpf]
  letI : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  letI : CompleteSpace (ContinuousLinearMap.adjoint T).ker :=
    (ContinuousLinearMap.adjoint T).isClosed_ker.completeSpace_coe
  refine ⟨{
    Index := J
    countable := hJ
    sigma := σ
    rightVector := e
    leftVector := f
    positive := hσ
    right_orthonormal := he
    left_orthonormal := hf
    map_right := hTf
    adjoint_left := hAf
    right_closedSpan := hright
    right_complement := ?_
    left_closedSpan := hleft
    left_complement := ?_
    expansion := ?_
    adjoint_expansion := ?_
    finite_multiplicity := ?_
    finite_away := ?_
    finite_rank := ?_
    zero_empty := ?_ }⟩
  · rw [hright]
    exact T.ker.isCompl_orthogonal
  · rw [hleft]
    exact (ContinuousLinearMap.adjoint T).ker.isCompl_orthogonal
  · intro x
    have hh := (hexp x).1
    change HasSum (fun j => inner 𝕜 (e j) x • e j) (x - S.ker.starProjection x) at hh
    have hp : T (S.ker.starProjection x) = 0 := by
      exact hker.le (S.ker.starProjection_apply_mem x)
    have hm := hh.map T T.continuous
    simpa only [Function.comp_def, map_smul, hTf, smul_smul, mul_comm,
      map_sub, hp, sub_zero] using hm
  · intro y
    have hh := (hexp (ContinuousLinearMap.adjoint T y)).1
    change HasSum (fun j => inner 𝕜 (e j) (ContinuousLinearMap.adjoint T y) • e j)
      (ContinuousLinearMap.adjoint T y - S.ker.starProjection (ContinuousLinearMap.adjoint T y)) at hh
    have hp : S.ker.starProjection (ContinuousLinearMap.adjoint T y) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff S.ker).mpr
      rw [hker]
      intro x hx
      rw [ContinuousLinearMap.adjoint_inner_right, show T x = 0 from hx, inner_zero_left]
    simpa only [hp, sub_zero, ContinuousLinearMap.adjoint_inner_right, hTf,
      inner_smul_left, RCLike.conj_ofReal] using hh
  · intro s hs
    apply (hfin (s ^ 2) (sq_pos_of_pos hs)).subset
    intro j hj
    change s ^ 2 ≤ |a j|
    rw [haeq j]
    change σ j = s at hj
    rw [show ‖T (e j)‖ = s from hj, abs_of_nonneg (sq_nonneg _)]
  · intro ε hε
    apply (hfin (ε ^ 2) (sq_pos_of_pos hε)).subset
    intro j hj
    change ε ^ 2 ≤ |a j|
    rw [haeq j, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_of_lt hε) hj 2
  · intro hfinite
    letI := hfinite
    let g : J → T.range := fun j =>
      ⟨f j, T.range.smul_mem _ (show T (e j) ∈ T.range from ⟨e j, rfl⟩)⟩
    have hli : LinearIndependent 𝕜 (T.range.subtype ∘ g) := hf.linearIndependent
    exact (hli.of_comp T.range.subtype).finite
  · intro hz
    exact ⟨fun j => (hn j) (by simp [hz])⟩

end ExpandedFA.CompactSpectral.SingularExpansion
