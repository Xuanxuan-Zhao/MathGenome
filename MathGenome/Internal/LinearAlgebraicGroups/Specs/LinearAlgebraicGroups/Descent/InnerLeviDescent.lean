import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.InnerLeviDescent

open CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open GeometricRadicals (IsReductive IsSplitReductive IsSplitTorus)
open QuasiSplitInnerForms (AreInnerForms)
open RankOneFlag (IsGeometricallyMaximal)
open RelativeFormComparison (IsInduced fieldTest transportedAut)
open SchemeDerivedGroup (IsDerivedSubgroup)
open Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

variable (F : Type u) [Field F]

abbrev MultiplicativeGroup : GroupScheme F :=
  specGroup (groupAlgebra F IntegerCharacters)

/-- Innerness of the derived group of the centralizer of a rational cocharacter.
The rational reference and both comparison squares use the centralizers and
derived subgroups of the displayed cocharacters. -/
def Statement : Prop :=
  ∀ {F : Type u} [Field F],
    let E := groupBaseChange F (SeparableClosure F)
    ∀ (G₀ G : AffineAlgebraicGroup F),
    IsSplitReductive G₀ → IsReductive G → AreInnerForms (S := SeparableClosure F) G₀ G →
    ∀ (c : Cocharacter G.val) (L : LimitDecomposition c),
      IsReductive (closedSubgroupAlgebraicGroup L.centralizer) →
      ∀ (H : ClosedSubgroup L.centralizer.group), IsDerivedSubgroup H →
      ∀ (T : ClosedSubgroup (E.obj G.val)),
        IsSplitTorus T.group → IsGeometricallyMaximal T →
        (∃ t : E.obj (MultiplicativeGroup F) ⟶ T.group, t ≫ T.inclusion = E.map c) →
        ∃ (c₀ : Cocharacter G₀.val) (L₀ : LimitDecomposition c₀)
          (H₀ : ClosedSubgroup L₀.centralizer.group),
          IsReductive (closedSubgroupAlgebraicGroup L₀.centralizer) ∧
          IsDerivedSubgroup H₀ ∧
          IsSplitReductive
            (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup L₀.centralizer) H₀) ∧
          ∃ (a : E.obj G₀.val ≅ E.obj G.val)
            (b : E.obj L₀.centralizer.group ≅ E.obj L.centralizer.group)
            (d : E.obj H₀.group ≅ E.obj H.group),
            E.map c₀ ≫ a.hom = E.map c ∧
            E.map L₀.centralizer.inclusion ≫ a.hom =
              b.hom ≫ E.map L.centralizer.inclusion ∧
            E.map H₀.inclusion ≫ b.hom = d.hom ≫ E.map H.inclusion ∧
            ∃ (Q : AutomorphismSequence.AdjointQuotient
                (closedSubgroupAlgebraicGroup
                  (G := closedSubgroupAlgebraicGroup L₀.centralizer) H₀))
              (inn : AutomorphismSequence.groupSections Q.quotient.val ⟶
                AutomorphismSequence.automorphisms H₀.group),
              (∀ (U : SchemeOver F) (g : U ⟶ H₀.group.X),
                inn.app (Opposite.op U) ⟨g ≫ Q.projection.hom.hom⟩ =
                  AutomorphismSequence.innerAut g) ∧
              (∀ U, Function.Injective (inn.app U)) ∧
              ∃ i : AutomorphismSequence.relativePoints H₀.group (fieldTest F (SeparableClosure F)) ≅
                  AutomorphismSequence.relativePoints H.group (fieldTest F (SeparableClosure F)),
                IsInduced F (SeparableClosure F) d i ∧
                ∀ σ, transportedAut F (SeparableClosure F) i σ ∈
                  (inn.app (Opposite.op (fieldTest F (SeparableClosure F)))).hom.range

end

end LinearAlgebraicGroups.Specs.InnerLeviDescent
