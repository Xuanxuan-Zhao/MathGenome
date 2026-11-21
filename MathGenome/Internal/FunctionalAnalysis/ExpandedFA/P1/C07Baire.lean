import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07Baire
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Category
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Baire's complete-metric theorem

Theorem `fa2:p1:c07:baire` and its two stated consequences.
The shared category interface identifies `BaireSpace` with the countable
open-dense-intersection property, and `IsMeagre` with an exact countable
union of nowhere dense sets. All interiors and meagreness below are ambient.
-/

open Set TopologicalSpace

universe u v

namespace ExpandedFA.P1.C07Baire

/-- Every complete metric space is Baire; nonemptiness is not needed. -/
theorem baireSpace_of_completeMetric
    (X : Type u) [MetricSpace X] [CompleteSpace X] : BaireSpace X :=
  BaireSpace.of_completelyPseudoMetrizable

/-- A countable closed cover of a nonempty complete metric space has a
member with nonempty interior. -/
theorem exists_nonempty_interior_of_closed_cover
    {X : Type u} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type v} [Countable ι] (F : ι → Set X)
    (hF : ∀ i, IsClosed (F i)) (hcover : (⋃ i, F i) = univ) :
    ∃ i, (interior (F i)).Nonempty := by
  let : BaireSpace X := baireSpace_of_completeMetric X
  exact nonempty_interior_of_iUnion_of_closed hF hcover

/-- A nonempty open subset is nonmeagre in the ambient complete metric space. -/
theorem not_isMeagre_of_nonempty_open
    {X : Type u} [MetricSpace X] [CompleteSpace X] (O : Set X)
    (hO : IsOpen O) (hne : O.Nonempty) : ¬ IsMeagre O := by
  let : BaireSpace X := baireSpace_of_completeMetric X
  exact not_isMeagre_of_isOpen hO hne

end ExpandedFA.P1.C07Baire
