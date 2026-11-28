import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteStageClosedExtensions

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace RepTheorySurvey.Geometric.SupportIntersectionEquivarianceSpecs.Expected

open Analytic
open EquivariantIntersectionComplexesSpecs (restrictedArrow)
open FiniteStageClosedExtensionSpecs (SupportIntersections)

/-- Restrict the normalized jet data to the actual support intersections.
At common levels the arrow is the pullback through the action and projection
squares. Below the support cutoff its source and target are zero objects.
The chosen family is natural for restricted equivariant morphisms. -/
def SupportIntersectionEquivariance : Prop :=
  ∀ {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
    (D : SupportIntersections B i S),
    (∀ n k : ℕ, (D.action n).cutoff ≤ k → S.cutoff ≤ k ∨ IsEmpty (D.space n)) →
    ∃ L : ∀ (F : BoundedBelow Y) (α : S.Equivariance F.obj), D.LocalEquivariance F α,
      (∀ (F : BoundedBelow Y) (α : S.Equivariance F.obj) (n k : ℕ)
          (hn : (D.action n).cutoff ≤ k) (hs : S.cutoff ≤ k),
        (((L F α).datum n).datum k hn).iso.hom =
          restrictedArrow (D.supportActionSquare n) α k hn hs) ∧
      (∀ (F : BoundedBelow Y) (n k : ℕ) (hn : (D.action n).cutoff ≤ k),
        k < S.cutoff →
        IsZero ((derivedInverseImage ((D.action n).action k hn).act).obj
          (D.intersectionRestriction F n).obj) ∧
        IsZero ((derivedInverseImage (AnalyticAction.projection (J.group k) (D.space n))).obj
          (D.intersectionRestriction F n).obj)) ∧
      ∀ {F G : BoundedBelow Y} {α : S.Equivariance F.obj} {γ : S.Equivariance G.obj}
        (f : F ⟶ G),
        (∀ (k : ℕ) (hk : S.cutoff ≤ k),
          (derivedInverseImage (S.action k hk).act).map f.hom ≫ (γ.datum k hk).iso.hom =
            (α.datum k hk).iso.hom ≫
              (derivedInverseImage (AnalyticAction.projection (J.group k) Y)).map f.hom) →
        ∀ (n k : ℕ) (hk : (D.action n).cutoff ≤ k),
          let qf := ((boundedBelowInverseImage (D.intoSupport n)).map f).hom
          (derivedInverseImage ((D.action n).action k hk).act).map qf ≫
              (((L G γ).datum n).datum k hk).iso.hom =
            (((L F α).datum n).datum k hk).iso.hom ≫
              (derivedInverseImage (AnalyticAction.projection (J.group k) (D.space n))).map qf

end RepTheorySurvey.Geometric.SupportIntersectionEquivarianceSpecs.Expected
