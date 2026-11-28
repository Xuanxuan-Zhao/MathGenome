import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

set_option autoImplicit false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.ClosedSupportPerversitySpecs.Expected

open Analytic

/-- The derived image from a closed union of strata is middle perverse on the
containing stage. Its composite image in the union is finite-stage perverse. -/
def ClosedExtensionPerverse : Prop :=
  ∀ {Y X : TopCat.{0}} (A : ClosedStages X)
    (P : Stratification Y) (Q : ∀ n, Stratification (A.space n)) (n : ℕ)
    (j : Y ⟶ A.space n) (_ : IsClosedEmbedding j)
    (index : P.Index ≃ {q : (Q n).Index // Set.range ((Q n).stratum q).inclusion ⊆ Set.range j})
    (_ : ∀ p, Set.range ((Q n).stratum (index p).val).inclusion =
      j '' Set.range (P.stratum p).inclusion)
    (_ : ∀ p, ((Q n).stratum (index p).val).complexDimension = (P.stratum p).complexDimension)
    (_ : ∀ q : (Q n).Index, ¬ Set.range ((Q n).stratum q).inclusion ⊆ Set.range j →
      Disjoint (Set.range ((Q n).stratum q).inclusion) (Set.range j))
    (F : BoundedBelow Y),
    IsMiddlePerverse P F.obj →
      IsMiddlePerverse (Q n) ((derivedDirectImage j).obj F).obj ∧
        IsFiniteStagePerverse A Q ((derivedDirectImage (j ≫ A.inclusion n)).obj F).obj

end RepTheorySurvey.Geometric.ClosedSupportPerversitySpecs.Expected
