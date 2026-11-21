import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Complementation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02Projections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08BoundedInverse
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection

/-!
Bounded projections and closed complements, Proposition
`fa2:p1:c15:complementation`, paper.tex 4057–4084.

For closed algebraic complements, addition from their Banach product is a
bounded bijection. The accepted bounded-inverse theorem makes its inverse,
and hence both coordinate maps, bounded. The converse and the elementary
finite (co)dimensional cases use the accepted Chapter 2 projection results.
The Hilbert case uses the accepted orthogonal decomposition.
-/
namespace ExpandedFA.P1.C15Complementation

universe u v

theorem algebraic_split_iff_unique_decomposition :
    Spec.AlgebraicSplitMeaning.{u, v} := by
  intro 𝕜 E _ _ _ M N
  constructor
  · exact fun h x => Submodule.existsUnique_add_of_isCompl_prod h x
  · intro h
    constructor
    · rw [disjoint_iff_inf_le]
      intro x hx
      have he : (⟨x, hx.1⟩, (0 : N)) = ((0 : M), ⟨x, hx.2⟩) :=
        (h x).unique (by simp) (by simp)
      have hz := congrArg (fun z : M × N => (z.1 : E)) he
      simpa using hz
    · rw [codisjoint_iff_le_sup]
      intro x _
      obtain ⟨⟨m, n⟩, he, _⟩ := h x
      exact Submodule.mem_sup.mpr ⟨m, m.property, n, n.property, he⟩

/-- The analytic step: the inverse of addition is bounded in the given norms. -/
theorem closed_split_isTopCompl : Spec.ClosedSplitTopological.{u, v} := by
  intro 𝕜 E _ _ _ _ M N hM hN h
  let : CompleteSpace M := hM.completeSpace_coe
  let : CompleteSpace N := hN.completeSpace_coe
  let A : (M × N) →L[𝕜] E := M.subtypeL.coprod N.subtypeL
  let e : (M × N) ≃ₗ[𝕜] E := M.prodEquivOfIsCompl N h
  have hA : Function.Bijective A := e.bijective
  obtain ⟨S, hSA, _, _⟩ := C08BoundedInverse.bounded_inverse 𝕜 (M × N) E A hA
  have hS (x : E) : S x = e.symm x := by
    have hx : A (e.symm x) = x := e.apply_symm_apply x
    calc
      S x = S (A (e.symm x)) := congrArg S hx.symm
      _ = e.symm x := hSA (e.symm x)
  apply (Submodule.IsCompl.isTopCompl_iff_continuous_symm_prodEquivOfIsCompl h).mpr
  exact S.continuous.congr hS

theorem closed_split_projection : Spec.ClosedSplitProjection.{u, v} := by
  intro 𝕜 E _ _ _ _ M N hM hN h
  let ht := closed_split_isTopCompl 𝕜 E M N hM hN h
  let P := M.projectionL N ht
  refine ⟨P, Submodule.isIdempotentElem_projectionL ht,
    Submodule.range_projectionL ht, Submodule.ker_projectionL ht, ?_⟩
  intro m n
  change (M.projectionL N ht) ((m : E) + (n : E)) = (m : E)
  rw [map_add, Submodule.projectionL_apply_left ht m,
    Submodule.projectionL_apply_right ht n, add_zero]

theorem bounded_idempotent_closed_split : Spec.IdempotentClosedSplit.{u, v} := by
  intro 𝕜 E _ _ _ P hP
  have hp : IsIdempotentElem P := hP
  have hpl := ContinuousLinearMap.IsIdempotentElem.toLinearMap hp
  obtain ⟨ht, hclosed, hkclosed, _, _⟩ :=
    C02Projections.bounded_projection_direct_sum 𝕜 E P hP
  refine ⟨LinearMap.IsIdempotentElem.range_eq_ker hpl,
    hclosed, hkclosed, ht.isCompl,
    fun x => Submodule.existsUnique_add_of_isCompl_prod ht.isCompl x, ?_, ?_⟩
  · intro x
    refine ⟨?_, by abel⟩
    change P (x - P x) = 0
    have hx : P (P x) = P x := congrArg (fun Q : E →L[𝕜] E => Q x) hP
    simp [hx]
  · intro m n
    have hm : P (m : E) = (m : E) :=
      (LinearMap.IsIdempotentElem.mem_range_iff hpl).mp m.property
    have hn : P (n : E) = 0 := n.property
    rw [map_add, hm, hn, add_zero]

theorem bounded_projection_iff_closed_complement :
    Spec.ProjectionClosedComplementIff.{u, v} := by
  intro 𝕜 E _ _ _ _ M hM
  constructor
  · rintro ⟨P, hP, hr⟩
    obtain ⟨ht, _, hker, _, _⟩ := C02Projections.bounded_projection_direct_sum 𝕜 E P hP
    exact ⟨P.ker, hker, hr ▸ ht.isCompl⟩
  · rintro ⟨N, hN, h⟩
    obtain ⟨P, hP, hr, _, _⟩ := closed_split_projection 𝕜 E M N hM hN h
    exact ⟨P, hP, hr⟩

theorem closed_hilbert_subspace_bounded_projection :
    Spec.HilbertSubspaceProjection.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM
  obtain ⟨ht, _⟩ := Hilbert.Projection.closed_subspace_decomposition 𝕜 H M hM
  obtain ⟨P, _, hP, _, hr, _, _, _, _, _⟩ :=
    C02Projections.topological_direct_sum_projections 𝕜 H M M.orthogonal ht
  exact ⟨⟨M.orthogonal, ht⟩, P, hP, hr⟩

theorem finite_dimensional_subspace_bounded_projection :
    Spec.FiniteDimensionalSubspaceProjection.{u, v} := by
  intro 𝕜 E _ _ _ M _
  obtain ⟨hcomp, N, _, _, ht⟩ := C02Projections.finite_dimensional_complemented 𝕜 E M
  obtain ⟨P, _, hP, _, hr, _, _, _, _, _⟩ :=
    C02Projections.topological_direct_sum_projections 𝕜 E M N ht
  exact ⟨hcomp, P, hP, hr⟩

theorem closed_finite_codimensional_subspace_bounded_projection :
    Spec.FiniteCodimensionalSubspaceProjection.{u, v} := by
  intro 𝕜 E _ _ _ M hM _
  obtain ⟨hcomp, N, _, _, ht⟩ := C02Projections.finite_codimensional_complemented 𝕜 E M hM
  obtain ⟨P, _, hP, _, hr, _, _, _, _, _⟩ :=
    C02Projections.topological_direct_sum_projections 𝕜 E M N ht
  exact ⟨hcomp, P, hP, hr⟩

end ExpandedFA.P1.C15Complementation
