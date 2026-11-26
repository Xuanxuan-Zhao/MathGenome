import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.LeviConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RationalFlagLifting
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.SplitContractingRadical

open CategoryTheory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Relative.Parabolics

open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open Fppf (fieldBase)
open GeometricRadicals (IsReductive IsUnipotentRadical)
open LeviConjugacy (Transports)
open QuotientEmbedding (Presentation)
open StandardParabolicLevi (IsContractingRadical)
open Unipotent (IsSplitUnipotent closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

/-- The ground-field cocharacter defining a parabolic exhibits its Levi
decomposition. The contracting subgroup and centralizer give the radical
and Levi inside the original parabolic. -/
def CocharacterLeviDecomposition : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P →
    ∃ (c : Cocharacter G.val) (D : LimitDecomposition c)
      (e : P.group ≅ D.parabolic.group) (U : ClosedSubgroup P.group)
      (i : U.group ≅ D.contracting.group) (L : ClosedSubgroup P.group)
      (j : L.group ≅ D.centralizer.group),
      e.hom ≫ D.parabolic.inclusion = P.inclusion ∧
        i.hom ≫ D.contractingToParabolic = U.inclusion ≫ e.hom ∧
        j.hom ≫ D.sectionMap = L.inclusion ≫ e.hom ∧
        IsSchemeKernel (e.hom ≫ D.limit) U ∧
        IsIso (L.inclusion ≫ (e.hom ≫ D.limit)) ∧
        IsReductive (closedSubgroupAlgebraicGroup D.centralizer) ∧
        IsContractingRadical D ∧
        IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U ∧
        IsSplitUnipotent (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup P) U)

/-- Two Levi complements of the radical are conjugate as closed subgroup
schemes by a unique rational point of the radical. -/
def RationalLeviConjugacy : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P →
    ∀ (U : ClosedSubgroup P.group), IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U →
    ∀ (Q : AffineAlgebraicGroup k) (q : P.group ⟶ Q.val), IsSchemeKernel q U →
    ∀ (L L' : ClosedSubgroup P.group), IsIso (L.inclusion ≫ q) → IsIso (L'.inclusion ≫ q) →
      ∃! a : 𝟙_ (SchemeOver k) ⟶ U.group.X,
        Transports L L' (a ≫ U.inclusion.hom.hom)

/-- The canonical bijection with the rational points of a representing flag
scheme sends the coset of a rational group point to its quotient projection. -/
def RationalFlagCosets : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P → ∀ D : Presentation P,
      ∃ e : RightCosets P (fieldBase k) ≃ (fieldBase k ⟶ D.scheme),
        ∀ g : fieldBase k ⟶ G.val.X, e (QuotientGroup.mk g) = g ≫ D.projection

/-- D08, rational parabolics, Levis and flags, including the conjugation
description of parabolic families and its compatibility with base change. -/
def Statement : Prop :=
  CocharacterLeviDecomposition.{u} ∧
    RationalLeviConjugacy.{u} ∧
    RationalFlagCosets.{u} ∧
    MaximalSplitTori.MinimalParabolicsConjugate.{u} ∧
    MaximalSplitTori.MaximalSplitToriConjugate.{u} ∧
    ParabolicFamilyTransporter.ParabolicFamilyRepresentability.{u} ∧
    ParabolicFamilyTransporter.ClassifiesBaseChange.{u}

end LinearAlgebraicGroups.Specs.Relative.Parabolics
