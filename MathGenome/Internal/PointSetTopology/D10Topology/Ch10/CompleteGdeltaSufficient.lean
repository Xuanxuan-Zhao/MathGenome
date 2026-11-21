import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.CompleteGdeltaSufficient
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.MetricSpace.Polish

/-!
The sufficiency direction of d10:10:complete-gdelta.

We use the library's complete metric on each open factor, without its Polish
space (separability) hypothesis. The intersection embeds as the closed diagonal
in X times the countable product of these factors. Thus it has a compatible
complete metric, which need not be the restriction of the original metric.
The library's `Opens.CompleteCopy` construction uses reciprocal distances; its
completeness proof handles an empty complement separately by observing that a
limit outside the open set would itself belong to the complement.
-/

open Set Topology TopologicalSpace
universe u

namespace D10Topology.Ch10
open D10Topology.Ch09

private theorem open_completelyMetrizable {X : Type u} [MetricSpace X]
    [CompleteSpace X] {G : Set X} (hG : IsOpen G) :
    IsCompletelyMetrizableSpace G := by
  exact inferInstanceAs
    (IsCompletelyMetrizableSpace (TopologicalSpace.Opens.CompleteCopy ⟨G, hG⟩))

private theorem intersection_completelyMetrizable {X : Type u} [MetricSpace X]
    [CompleteSpace X] (A : Set X) (G : ℕ → Set X) (hG : ∀ n, IsOpen (G n))
    (hA : A = ⋂ n, G n) : IsCompletelyMetrizableSpace A := by
  let : ∀ n, IsCompletelyMetrizableSpace (G n) :=
    fun n => open_completelyMetrizable (hG n)
  have haG (a : A) (n : ℕ) : (a : X) ∈ G n :=
    mem_iInter.mp (hA ▸ a.property) n
  let e : A → X × (∀ n, G n) := fun a => (a.val, fun n => ⟨a.val, haG a n⟩)
  have he_cont : Continuous e :=
    continuous_subtype_val.prodMk
      (continuous_pi fun n => continuous_subtype_val.subtype_mk (fun a => haG a n))
  have he : IsEmbedding e :=
    IsEmbedding.of_comp he_cont continuous_fst IsEmbedding.subtypeVal
  have hrange : range e = ⋂ n : ℕ, {z : X × (∀ n, G n) | (z.2 n).val = z.1} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact mem_iInter.mpr fun _ => rfl
    · intro hz
      have hp : z.1 ∈ A := by
        rw [hA]
        exact mem_iInter.mpr fun n => (mem_iInter.mp hz n) ▸ (z.2 n).property
      refine ⟨⟨z.1, hp⟩, ?_⟩
      apply Prod.ext
      · rfl
      · funext n
        apply Subtype.ext
        exact (mem_iInter.mp hz n).symm
  have he_closed : IsClosedEmbedding e := ⟨he, by
    rw [hrange]
    exact isClosed_iInter fun n => isClosed_eq
      (continuous_subtype_val.comp ((continuous_apply n).comp continuous_snd))
      continuous_fst⟩
  exact he_closed.IsCompletelyMetrizableSpace

/-- A G_delta subset of any complete metric space admits a complete metric
compatible with its subspace topology, including the empty subset. -/
theorem complete_gdelta_sufficient {X : Type u} (d : MetricSpace X) (A : Set X)
    (hd : SequentiallyComplete d.toPseudoMetricSpace)
    (hA : @IsGδ X (metricTopology d.toPseudoMetricSpace) A) :
    CompletelyMetrizable
      ((metricTopology d.toPseudoMetricSpace).induced (Subtype.val : A → X)) := by
  let := d
  let : CompleteSpace X := (sequentiallyComplete_iff_mathlib _).mp hd
  obtain ⟨G, hG, hAG⟩ := hA.eq_iInter_nat
  exact (completelyMetrizable_iff_mathlib _).mpr
    (intersection_completelyMetrizable A G hG hAG)

end D10Topology.Ch10
