import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.OrthonormalExpansion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.PreHilbertBesselParseval
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Arbitrary orthonormal bases, paper.tex 7465–7486. Zorn gives a maximal
orthonormal subset. The maximality/orthogonal-complement criterion and the
Hilbert double-complement theorem make its span dense. The accepted
pre-Hilbert net criterion then gives expansion and Parseval. No enumeration,
separability, nonzero-space or nonempty-index assumption is used.
-/

noncomputable section
open scoped InnerProductSpace
open Filter Topology

namespace ExpandedFA.Hilbert.OrthonormalExpansion
universe u v w

/-- Maximality is under inclusion of ranges of orthonormal families. -/
abbrev IsMaximalOrthonormal : Spec.IsMaximalOrthonormalType.{u, v, w} :=
  Spec.IsMaximalOrthonormalValue

theorem exists_maximal_orthonormal_subset : Spec.ExistsMaximalOrthonormalSubset.{u, v} := by
  intro 𝕜 H _ _ _ _
  obtain ⟨S, _, hS, hmax⟩ := exists_maximal_orthonormal (orthonormal_empty 𝕜 H)
  refine ⟨S, hS, ?_⟩
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hmax

theorem exists_maximal_orthonormal_family : Spec.ExistsMaximalOrthonormalFamily.{u, v} := by
  intro 𝕜 H _ _ _ _
  obtain ⟨S, hS⟩ := exists_maximal_orthonormal_subset 𝕜 H
  exact ⟨S, Subtype.val, hS⟩

theorem maximal_iff_total : Spec.MaximalIffTotal.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ e he
  change (Orthonormal 𝕜 e ∧ _) ↔ _
  rw [and_iff_right he]
  exact (maximal_orthonormal_iff_orthogonalComplement_eq_bot he.toSubtypeRange).trans
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure_eq_top_iff.symm

theorem finiteSubsetNet_expansion : Spec.FiniteSubsetNetExpansion.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ e he x
  apply (PreHilbertBesselParseval.closedSpan_iff_net_convergence 𝕜 H ι e he.1 x).mp
  rw [(maximal_iff_total 𝕜 H ι e he.1).mp he]
  exact Submodule.mem_top

theorem expansion : Spec.Expansion.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ e he x
  have hs : HasSum (fun i => ⟪e i, x⟫_𝕜 • e i) x :=
    finiteSubsetNet_expansion 𝕜 H ι e he x
  exact ⟨hs, hs.tsum_eq.symm⟩

theorem parseval : Spec.Parseval.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ e he x
  have hp := (PreHilbertBesselParseval.net_convergence_iff_parseval 𝕜 H ι e he.1 x).mp
    (finiteSubsetNet_expansion 𝕜 H ι e he x)
  have hs := (PreHilbertBesselParseval.coefficient_squares_summable 𝕜 H ι e he.1 x).hasSum
  rw [hp] at hs
  exact ⟨hs, hp.symm⟩

theorem countable_coefficient_support : Spec.CountableCoefficientSupport.{u, v, w} :=
  PreHilbertBesselParseval.countable_coefficient_support

theorem empty_basis_iff_zero : Spec.EmptyBasisIffZero.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ _ e
  rw [maximal_iff_total 𝕜 H ι e (Orthonormal.of_isEmpty e)]
  have hr : Set.range e = ∅ := by
    ext x
    simp
  rw [hr, Submodule.span_empty]
  have hc : IsClosed ((⊥ : Submodule 𝕜 H) : Set H) := by simp
  rw [hc.submodule_topologicalClosure_eq]
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    have hz (z : H) : z = 0 := by
      have : z ∈ (⊥ : Submodule 𝕜 H) := h ▸ Submodule.mem_top
      simpa using this
    rw [hz x, hz y]
  · intro h
    let := h
    ext x
    simp [Subsingleton.elim x 0]

theorem finite_index_in_finite_dimension : Spec.FiniteIndexInFiniteDimension.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ e he
  exact he.linearIndependent.finite

theorem exists_finite_basis : Spec.ExistsFiniteBasis.{u, v} := by
  intro 𝕜 H _ _ _ _ _
  obtain ⟨S, hS⟩ := exists_maximal_orthonormal_subset 𝕜 H
  exact ⟨S, hS.1.linearIndependent.setFinite, hS⟩

theorem finite_expansion_and_parseval : Spec.FiniteExpansionAndParseval.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ _ e he x
  simpa only [tsum_fintype] using
    And.intro (expansion 𝕜 H ι e he x).2 (parseval 𝕜 H ι e he x).2

end ExpandedFA.Hilbert.OrthonormalExpansion
