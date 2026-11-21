import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.JonesCounting
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions

/-!
Jones's counting lemma (paper.tex, d10:08:jones). Disjoint open separation
encodes every subset of a closed discrete subspace by its trace on a dense
subset. Cantor's theorem then gives the stated obstruction to normality.
-/

open Set
universe u

namespace D10Topology.Ch08

variable {X : Type u} [TopologicalSpace X]

theorem normal_closed_discrete_powerset_embedding [NormalSpace X]
    (D E : Set X) [DiscreteTopology E] (hD : Dense D) (hE : IsClosed E) :
    Nonempty (Set E ↪ Set D) := by
  classical
  -- Every subset of E is closed in X, since E is closed and discrete.
  have hclosed (T : Set E) : IsClosed ((Subtype.val : E → X) '' T) :=
    hE.isClosedMap_subtype_val T (isClosed_discrete T)
  have hsep (T : Set E) : ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ (Subtype.val '' T) ⊆ U ∧
        (Subtype.val '' Tᶜ) ⊆ V ∧ Disjoint U V := by
    exact normal_separation (hclosed T) (hclosed Tᶜ)
      ((disjoint_image_iff Subtype.val_injective).mpr disjoint_compl_right)
  choose U V hU hV hTU hCV hdisj using hsep
  let trace : Set E → Set D := fun T => (Subtype.val : D → X) ⁻¹' U T
  -- Equal traces force inclusion: a point in T \ T' would yield a nonempty
  -- open U(T) ∩ V(T'), hence a point of D distinguishing the two traces.
  have hreflect (T T' : Set E) (heq : trace T = trace T') : T ⊆ T' := by
    intro e he
    by_contra he'
    have heU : (e : X) ∈ U T := hTU T ⟨e, he, rfl⟩
    have heV : (e : X) ∈ V T' := hCV T' ⟨e, he', rfl⟩
    obtain ⟨d, hdD, hdU, hdV⟩ :=
      hD.exists_mem_open ((hU T).inter (hV T')) ⟨e, heU, heV⟩
    have hdtrace : (⟨d, hdD⟩ : D) ∈ trace T := hdU
    have hdtrace' : (⟨d, hdD⟩ : D) ∈ trace T' := heq ▸ hdtrace
    have hdU' : d ∈ U T' := hdtrace'
    exact Set.disjoint_left.mp (hdisj T') hdU' hdV
  exact ⟨⟨trace, fun T T' heq =>
    Set.Subset.antisymm (hreflect T T' heq) (hreflect T' T heq.symm)⟩⟩

theorem normal_closed_discrete_cardinal_bound [NormalSpace X]
    (D E : Set X) [DiscreteTopology E] (hD : Dense D) (hE : IsClosed E) :
    (2 : Cardinal) ^ Cardinal.mk E ≤ (2 : Cardinal) ^ Cardinal.mk D := by
  obtain ⟨f⟩ := normal_closed_discrete_powerset_embedding D E hD hE
  simpa only [Cardinal.mk_set] using Cardinal.mk_le_of_injective f.injective

theorem jones_counting (D E : Set X) [DiscreteTopology E]
    (hD : Dense D) (hE : IsClosed E)
    (hcard : (2 : Cardinal) ^ Cardinal.mk D ≤ Cardinal.mk E) :
    ¬ Ch07.Normal X := by
  intro hN
  let : NormalSpace X := hN
  have hbound := normal_closed_discrete_cardinal_bound D E hD hE
  exact (not_lt_of_ge (hbound.trans hcard)) (Cardinal.cantor (Cardinal.mk E))

end D10Topology.Ch08
