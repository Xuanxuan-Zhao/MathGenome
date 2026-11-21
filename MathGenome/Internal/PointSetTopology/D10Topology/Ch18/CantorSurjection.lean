import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.CantorSurjection
import MathGenome.Internal.PointSetTopology.D10Topology.Ch18.CantorModel
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff

/-! The Cantor surjection theorem of paper.tex, d10:18:cantor-surjection.
Mathlib proves Hausdorff–Alexandroff for zero-based binary sequences. We
transport its map along the canonical product homeomorphism from positive
integer coordinates. No perfectness or zero-dimensionality is required of K.
-/

universe u

namespace D10Topology.Ch18

/-- Every nonempty compact metric space is a continuous image of the
paper's canonical Cantor product. -/
theorem cantor_surjection (K : Type u) [MetricSpace K] [CompactSpace K] [Nonempty K] :
    ∃ f : CantorSpace → K, Continuous f ∧ Function.Surjective f := by
  obtain ⟨f, hf, hsurj⟩ := exists_nat_bool_continuous_surjective_of_compact K
  exact ⟨f ∘ positiveReindex, hf.comp positiveReindex.continuous,
    hsurj.comp positiveReindex.surjective⟩

/-- In particular the theorem cannot be extended to the empty target. -/
theorem cantor_surjection_iff_nonempty (K : Type u) [MetricSpace K] [CompactSpace K] :
    (∃ f : CantorSpace → K, Continuous f ∧ Function.Surjective f) ↔ Nonempty K := by
  constructor
  · rintro ⟨f, _, _⟩
    exact ⟨f (fun _ => false)⟩
  · intro hK
    letI : Nonempty K := hK
    exact cantor_surjection K

end D10Topology.Ch18
