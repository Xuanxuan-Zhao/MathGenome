import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteStageClosedExtensions

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.SupportIntersectionJetDescentSpecs.Expected

open Analytic
open FiniteStageClosedExtensionSpecs (SupportIntersections)
open EquivariantIntersectionComplexesSpecs (restrictedArrow)

/-- Restrict a support datum to every actual support intersection, including at
jet levels below the support cutoff. The pullback equation determines each
arrow by full faithfulness at `max k S.cutoff` and holds at every higher common
level. The local data use the given intersection restrictions and their
canonical transition comparisons. -/
def SupportIntersectionJetDescent : Prop :=
  ∀ {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
    (I : SupportIntersections B i S),
    (∀ {k l : ℕ} (h : k ≤ l) (U : TopCat.{0}),
      Nonempty ((boundedBelowInverseImage (J.parameterMap h (𝟙 U))).FullyFaithful)) →
    (∀ {k l : ℕ} (h : k ≤ l) (U : TopCat.{0}),
      Nonempty ((boundedBelowInverseImage
        (J.parameterMap h (J.parameterMap h (𝟙 U)))).FullyFaithful)) →
    ∃ L : ∀ (F : BoundedBelow Y) (α : S.Equivariance F.obj), I.LocalEquivariance F α,
      (∀ (F : BoundedBelow Y) (α : S.Equivariance F.obj) (n k : ℕ)
          (hk : (I.action n).cutoff ≤ k) (hs : S.cutoff ≤ k),
        (((L F α).datum n).datum k hk).iso.hom =
          restrictedArrow (I.supportActionSquare n) α k hk hs) ∧
      (∀ (F : BoundedBelow Y) (α : S.Equivariance F.obj) (n : ℕ) {k l : ℕ}
          (hk : (I.action n).cutoff ≤ k) (h : k ≤ l) (hs : S.cutoff ≤ l),
        pullbackMorphism (J.parameterMap h (𝟙 (I.space n))) ((I.action n).factors hk h)
          (TopCat.ext (fun _ => rfl)) (((L F α).datum n).datum k hk).iso.hom =
          restrictedArrow (I.supportActionSquare n) α l (hk.trans h) hs) ∧
      ∀ {F G : BoundedBelow Y} {α : S.Equivariance F.obj} {γ : S.Equivariance G.obj}
        (f : F ⟶ G),
        (∀ (k : ℕ) (hk : S.cutoff ≤ k),
          (derivedInverseImage (S.action k hk).act).map f.hom ≫ (γ.datum k hk).iso.hom =
            (α.datum k hk).iso.hom ≫
              (derivedInverseImage (AnalyticAction.projection (J.group k) Y)).map f.hom) →
        ∀ (n k : ℕ) (hk : (I.action n).cutoff ≤ k),
          let qf := ((boundedBelowInverseImage (I.intoSupport n)).map f).hom
          (derivedInverseImage ((I.action n).action k hk).act).map qf ≫
              (((L G γ).datum n).datum k hk).iso.hom =
            (((L F α).datum n).datum k hk).iso.hom ≫
              (derivedInverseImage (AnalyticAction.projection (J.group k) (I.space n))).map qf

end RepTheorySurvey.Geometric.SupportIntersectionJetDescentSpecs.Expected
