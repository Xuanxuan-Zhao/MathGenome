import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.GramDistance
import Mathlib.Tactic.Ring

/-!
Gram positivity, exact least-squares formulas, and degenerate cases in an
arbitrary real or complex inner-product space (paper.tex 8009–8047).
The normal equations give an orthogonal residual directly; no completeness
assumption or certificate is introduced. Expanding its squared norm gives
the quadratic formula, and the scalar Schur complement gives the determinant
ratio. Independent spanning sublists transfer both conclusions to the same
target subspace.
-/

noncomputable section
open scoped InnerProductSpace ComplexOrder
open Matrix

namespace ExpandedFA.Hilbert.GramDistance
universe u v w

theorem gram_positivity : Spec.GramPositivity.{u, v, w} := by
  intro 𝕜 E ι _ _ _ _ y
  exact ⟨Matrix.posSemidef_gram 𝕜 y, Matrix.posDef_gram_iff_linearIndependent⟩

theorem dependent_determinant : Spec.DependentDeterminant.{u, v, w} := by
  intro 𝕜 E ι _ _ _ _ _ y h
  exact not_ne_iff.mp (h ∘ Matrix.linearIndependent_of_det_gram_ne_zero)

section NormalEquations
variable {𝕜 : Type u} {E : Type v} {ι : Type w} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]

lemma normal_equations (y : ι → E) (hy : LinearIndependent 𝕜 y) (x : E) :
    gram 𝕜 y *ᵥ ((gram 𝕜 y)⁻¹ *ᵥ Spec.rhs 𝕜 y x) = Spec.rhs 𝕜 y x := by
  rw [mulVec_mulVec, mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (det_gram_ne_zero_iff_linearIndependent.mpr hy)), one_mulVec]

lemma leastSquaresPoint_mem (y : ι → E) (x : E) :
    Spec.leastSquaresPoint 𝕜 y x ∈ Submodule.span 𝕜 (Set.range y) := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma residual_mem_orthogonal (y : ι → E) (hy : LinearIndependent 𝕜 y) (x : E) :
    x - Spec.leastSquaresPoint 𝕜 y x ∈ (Submodule.span 𝕜 (Set.range y)).orthogonal := by
  have heq : ∀ i, ⟪y i, x - Spec.leastSquaresPoint 𝕜 y x⟫_𝕜 = 0 := by
    intro i
    have h := congrFun (normal_equations y hy x) i
    simpa only [Spec.leastSquaresPoint, inner_sub_right, inner_sum, inner_smul_right,
      Matrix.mulVec, dotProduct, gram_apply, Spec.rhs, mul_comm, sub_eq_zero] using h.symm
  rw [Submodule.mem_orthogonal]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact heq i
  | zero => exact inner_zero_left _
  | add z w _ _ hz hw => rw [inner_add_left, hz, hw, add_zero]
  | smul a z _ hz => rw [inner_smul_left, hz, mul_zero]

lemma infDist_eq_residual (y : ι → E) (hy : LinearIndependent 𝕜 y) (x : E) :
    Metric.infDist x (Submodule.span 𝕜 (Set.range y) : Set E) =
      ‖x - Spec.leastSquaresPoint 𝕜 y x‖ := by
  let Y := Submodule.span 𝕜 (Set.range y)
  let : Y.HasOrthogonalProjection :=
    ⟨fun z => ⟨Spec.leastSquaresPoint 𝕜 y z, leastSquaresPoint_mem y z,
      residual_mem_orthogonal y hy z⟩⟩
  have hproj : Y.starProjection x = Spec.leastSquaresPoint 𝕜 y x :=
    Submodule.eq_starProjection_of_mem_orthogonal
    (leastSquaresPoint_mem (𝕜 := 𝕜) y x) (residual_mem_orthogonal y hy x)
  simpa only [hproj, dist_eq_norm] using (Y.dist_starProjection_eq_infDist x).symm

lemma distance_schur (y : ι → E) (hy : LinearIndependent 𝕜 y) (x : E) :
    (Metric.infDist x (Submodule.span 𝕜 (Set.range y) : Set E) : 𝕜) ^ 2 =
      (‖x‖ : 𝕜) ^ 2 - star (Spec.rhs 𝕜 y x) ⬝ᵥ (gram 𝕜 y)⁻¹ *ᵥ Spec.rhs 𝕜 y x := by
  let p := Spec.leastSquaresPoint 𝕜 y x
  have hp := leastSquaresPoint_mem (𝕜 := 𝕜) y x
  have ho := residual_mem_orthogonal y hy x
  have hpx : ⟪p, x⟫_𝕜 = ⟪p, p⟫_𝕜 := by
    apply sub_eq_zero.mp
    rw [← inner_sub_right]
    exact Submodule.inner_right_of_mem_orthogonal hp ho
  have hxp : ⟪x, p⟫_𝕜 = ⟪p, p⟫_𝕜 := by
    apply sub_eq_zero.mp
    rw [← inner_sub_left]
    exact Submodule.inner_left_of_mem_orthogonal hp ho
  have hdot : star (Spec.rhs 𝕜 y x) ⬝ᵥ (gram 𝕜 y)⁻¹ *ᵥ Spec.rhs 𝕜 y x =
      ⟪x, p⟫_𝕜 := by
    simp [p, Spec.leastSquaresPoint, dotProduct, inner_sum, inner_smul_right,
      Spec.rhs, RCLike.star_def, inner_conj_symm, mul_comm]
  rw [infDist_eq_residual y hy x]
  change (‖x - p‖ : 𝕜) ^ 2 = _
  rw [← inner_self_eq_norm_sq_to_K, inner_sub_sub_self, hpx, hxp,
    inner_self_eq_norm_sq_to_K x, hdot, hxp]
  ring

end NormalEquations

/-- Schur's determinant identity for a scalar-bordered matrix. -/
lemma bordered_determinant {𝕜 : Type u} {ι : Type w} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι 𝕜) (hG : G.det ≠ 0)
    (b : ι → 𝕜) (d : 𝕜) :
    (fromBlocks G (of fun i (_ : Unit) => b i)
      (of fun (_ : Unit) i => star (b i))
      (of fun (_ : Unit) (_ : Unit) => d)).det =
        G.det * (d - star b ⬝ᵥ G⁻¹ *ᵥ b) := by
  let : Invertible G := G.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hG)
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, Matrix.mul_assoc, Matrix.det_unique (n := Unit)]
  rfl

theorem independent_distance_formula : Spec.IndependentDistanceFormula.{u, v, w} := by
  intro 𝕜 E ι _ _ _ _ _ y hy x
  have hd := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hy
  refine ⟨hd, distance_schur y hy x, ?_⟩
  rw [distance_schur y hy x]
  apply (eq_div_iff hd).mpr
  rw [Spec.augmentedGram, bordered_determinant _ hd]
  exact mul_comm _ _

theorem independent_nearestPoint : Spec.IndependentNearestPoint.{u, v, w} := by
  intro 𝕜 E ι _ _ _ _ _ y hy x
  let Y := Submodule.span 𝕜 (Set.range y)
  let : Y.HasOrthogonalProjection :=
    ⟨fun z => ⟨Spec.leastSquaresPoint 𝕜 y z, leastSquaresPoint_mem y z,
      residual_mem_orthogonal y hy z⟩⟩
  have hp := leastSquaresPoint_mem (𝕜 := 𝕜) y x
  have hproj := Submodule.eq_starProjection_of_mem_orthogonal hp
    (residual_mem_orthogonal y hy x)
  have hmin : ∀ z ∈ Y, ‖x - Spec.leastSquaresPoint 𝕜 y x‖ ≤ ‖x - z‖ := by
    intro z hz
    rw [← hproj, Y.starProjection_minimal]
    exact ciInf_le (f := fun w : Y => ‖x - w‖)
      ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ ⟨z, hz⟩
  refine ⟨hp, hmin, ?_⟩
  intro q hq hqmin
  have hnorm : ‖x - q‖ = ⨅ z : Y, ‖x - z‖ := by
    rw [← Y.starProjection_minimal, hproj]
    exact le_antisymm (hqmin _ hp) (hmin _ hq)
  have hinner := (Y.norm_eq_iInf_iff_inner_eq_zero hq).mp hnorm
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hq hinner).symm.trans hproj

theorem independent_spanningSublist : Spec.IndependentSpanningSublist.{u, v, w} := by
  intro 𝕜 E ι _ _ _ _ y
  classical
  obtain ⟨s, _, _, hs, hli⟩ := exists_linearIndepOn_extension
    (K := 𝕜) (v := y) (s := ∅) (t := Set.univ) (by simp) (Set.empty_subset _)
  have hr : Set.range (fun i : s => y i) = y '' s := by
    ext z
    simp
  refine ⟨s, hli, ?_⟩
  rw [hr]
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    simpa only [Set.image_univ] using hs

theorem spanning_sublist_formulas : Spec.SpanningSublistFormulas.{u, v, w} := by
  intro 𝕜 E ι _ _ _ _ y s
  let : Fintype s := Fintype.ofFinite s
  let : DecidableEq s := Classical.decEq s
  dsimp only
  intro hs hspan x
  have hn := independent_nearestPoint 𝕜 E s (fun i : s => y i) hs x
  have hd := independent_distance_formula 𝕜 E s (fun i : s => y i) hs x
  dsimp only at hn hd ⊢
  rw [hspan] at hn hd
  exact ⟨hn, hd⟩

theorem empty_list : Spec.EmptyList.{u, v, w} := by
  intro 𝕜 E ι _ _ _ _ _ _ y x
  have hr : Set.range y = ∅ := by ext z; simp
  simp [hr, Spec.leastSquaresPoint, Matrix.det_isEmpty, Submodule.bot_coe,
    Metric.infDist_singleton]

end ExpandedFA.Hilbert.GramDistance
