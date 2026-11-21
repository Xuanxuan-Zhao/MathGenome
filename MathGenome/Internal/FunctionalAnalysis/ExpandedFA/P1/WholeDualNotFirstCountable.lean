import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WholeDualNotFirstCountable
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.Normed.Group.Quotient

/-!
The whole continuous dual of an infinite-dimensional Banach space is not
first countable in its weak-star topology (fa2:p1:c13:whole-dual).

A countable neighborhood base would cover E by the finite-dimensional spans
of its finite sets of tests. A separating functional, rescaled to have value
one at x, shows that every x belongs to one of these spans. Baire forces one
span to have nonempty interior and hence to equal E, a contradiction.
The incomplete c₀₀ contrast is established by the separate upstream module
`ExpandedFA.P1.IncompleteWholeDualMetric`.
-/

namespace ExpandedFA.P1.WholeDualNotFirstCountable

open Set Filter
open scoped Topology
noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A closed subspace can be separated from any point outside it by a
norm-continuous scalar-linear functional. -/
private theorem separate_subspace (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E))
    {x : E} (hx : x ∉ S) :
    ∃ f : E →L[𝕜] 𝕜, (∀ y ∈ S, f y = 0) ∧ f x ≠ 0 := by
  let : IsClosed (S : Set E) := hS
  have hxq : S.mkQ x ≠ 0 := by simpa using hx
  obtain ⟨f, _, hf⟩ := exists_dual_vector 𝕜 (S.mkQ x) (norm_ne_zero_iff.mpr hxq)
  refine ⟨f.comp S.mkQL, ?_, ?_⟩
  · intro y hy
    simp [(Submodule.Quotient.mk_eq_zero S).mpr hy]
  · change f (S.mkQ x) ≠ 0
    rw [hf]
    exact_mod_cast (norm_ne_zero_iff.mpr hxq)

/-- If a finite-test neighborhood controls evaluation at x, then x lies in
its finite-dimensional test span. Scaling a separating functional proves this. -/
private theorem mem_span_of_neighborhood_subset (s : Finset E) {ε : ℝ} (hε : 0 < ε)
    (x : E)
    (hsub : C12WeakStar.Spec.NeighborhoodValue 𝕜 E 0 s ε ⊆
      C12WeakStar.Spec.NeighborhoodValue 𝕜 E 0 {x} 1) :
    x ∈ Submodule.span 𝕜 (s : Set E) := by
  classical
  by_contra hx
  let S := Submodule.span 𝕜 (s : Set E)
  obtain ⟨f, hf, hfx⟩ := separate_subspace S S.closed_of_finiteDimensional hx
  have hmem : (f x)⁻¹ • f ∈
      C12WeakStar.Spec.NeighborhoodValue 𝕜 E 0 s ε := by
    intro y hy
    have hfy := hf y (Submodule.subset_span hy)
    simpa [hfy] using hε
  have h := hsub hmem x (by simp)
  simp [hfx] at h

/-- The neighborhood filter at zero on the entire weak-star dual cannot have
a countable generating family. Completeness is used only by Baire on E. -/
theorem whole_dual_not_first_countable_at_zero :
    Spec.NotFirstCountableAtZero := by
  intro 𝕜 E _ _ _ _ hInfinite hcount
  classical
  let := hcount
  obtain ⟨p, hp, hb⟩ :=
    (C12WeakStar.weakStarTopology_nhds_basis 𝕜 E 0).exists_antitone_subbasis
  let S : ℕ → Submodule 𝕜 E := fun n => Submodule.span 𝕜 (p n).1
  have hcover : (⋃ n, (S n : Set E)) = univ := by
    apply eq_univ_of_forall
    intro x
    have hmem := (C12WeakStar.weakStarTopology_nhds_basis 𝕜 E 0).mem_of_mem
      (i := (⟨{x}, 1⟩ : Finset E × ℝ)) (by norm_num)
    obtain ⟨n, hn⟩ := hb.mem_iff.mp hmem
    exact mem_iUnion.mpr ⟨n, mem_span_of_neighborhood_subset (p n).1 (hp n) x hn⟩
  obtain ⟨n, hn⟩ := C07Baire.exists_nonempty_interior_of_closed_cover
    (fun n => (S n : Set E)) (fun n => (S n).closed_of_finiteDimensional) hcover
  have htop := (S n).eq_top_of_nonempty_interior' hn
  have : FiniteDimensional 𝕜 E := by
    have : FiniteDimensional 𝕜 (S n) := inferInstance
    exact FiniteDimensional.of_surjective (S n).subtype (by
      intro x
      exact ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩)
  exact hInfinite this

/-- Every metrizable topology has a countably generated neighborhood filter. -/
theorem whole_dual_not_metrizable : Spec.NotMetrizable := by
  intro 𝕜 E _ _ _ _ hInfinite hmetr
  let : TopologicalSpace (E →L[𝕜] 𝕜) :=
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  let := hmetr
  exact whole_dual_not_first_countable_at_zero 𝕜 E hInfinite inferInstance

end
end ExpandedFA.P1.WholeDualNotFirstCountable
