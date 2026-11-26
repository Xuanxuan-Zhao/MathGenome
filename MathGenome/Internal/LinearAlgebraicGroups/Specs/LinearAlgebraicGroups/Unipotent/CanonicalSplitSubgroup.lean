import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralAdditiveSubgroup
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.WoundExample
import Mathlib.FieldTheory.PurelyInseparable.Basic

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

noncomputable section

variable {k : Type u} [Field k]

/-- Every scheme morphism from the affine line factors through the ground field. -/
def IsWound (G : GroupScheme k) : Prop :=
  ∀ x : AffineLineCurve G, ¬ IsNonconstantCurve x

def IsWoundType := ∀ {k : Type u} [Field k], GroupScheme k → Prop

/-- Inclusion of closed subgroup schemes, as a factorization of their inclusions. -/
def ClosedSubgroupContained {G : GroupScheme k} (H N : ClosedSubgroup G) : Prop :=
  ∃ j : H.group ⟶ N.group, j ≫ N.inclusion = H.inclusion

/-- The largest smooth connected split subgroup, with maximality among split subgroups. -/
def IsLargestSplitSubgroup {U : AffineAlgebraicGroup k} (H : ClosedSubgroup U.val) : Prop :=
  Smooth H.group.X.hom ∧ ConnectedSpace H.group.X.left ∧
    IsSplitUnipotent (closedSubgroupAlgebraicGroup H) ∧
    ∀ N : ClosedSubgroup U.val, IsSplitUnipotent (closedSubgroupAlgebraicGroup N) →
      ClosedSubgroupContained N H

/-- Woundness is equivalent to the absence of a closed copy of the additive group. -/
def WoundIffNoAdditiveSubgroup : Prop :=
  ∀ {k : Type u} [Field k] (U : AffineAlgebraicGroup k),
    Smooth U.val.X.hom → ConnectedSpace U.val.X.left → IsUnipotent U →
    (IsWound U.val ↔
      ∀ H : ClosedSubgroup U.val,
        ¬ Nonempty ((groupPointsFunctor k).obj H.group ≅ StandardGroups.additivePoints k))

def WoundSeparableExtension : Prop :=
  ∀ {k : Type u} [Field k] (U : AffineAlgebraicGroup k),
    Smooth U.val.X.hom → ConnectedSpace U.val.X.left → IsUnipotent U →
    IsWound U.val →
    ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K],
      IsWound ((groupBaseChange k K).obj U.val)

/-- Triviality here is an equality of scheme morphisms, including on nonreduced test algebras. -/
def SplitToWoundTrivial : Prop :=
  ∀ {k : Type u} [Field k] (S U : AffineAlgebraicGroup k),
    IsSplitUnipotent S → IsWound U.val → ∀ f : S.val ⟶ U.val, f.hom.hom = 1

/-- Existence of the largest split subgroup and its represented wound fppf quotient. -/
def CanonicalSplitSubgroup : Prop :=
  ∀ {k : Type u} [Field k] (U : AffineAlgebraicGroup k),
    Smooth U.val.X.hom → ConnectedSpace U.val.X.left → IsUnipotent U →
    ∃ (H : ClosedSubgroup U.val) (Q : AffineAlgebraicGroup k) (q : U.val ⟶ Q.val),
      IsLargestSplitSubgroup (U := U) H ∧ IsNormalSubgroup H.inclusion ∧
      IsFppfGroupQuotient H q ∧ Smooth Q.val.X.hom ∧ ConnectedSpace Q.val.X.left ∧
      IsUnipotent Q ∧ IsWound Q.val

def CanonicalSplitSubgroupUniqueness : Prop :=
  ∀ {k : Type u} [Field k] {U : AffineAlgebraicGroup k}
    (H N : ClosedSubgroup U.val),
    IsLargestSplitSubgroup (U := U) H → IsLargestSplitSubgroup (U := U) N →
    ∃! e : H.group ≅ N.group, e.hom ≫ N.inclusion = H.inclusion

/-- The same subgroup inclusion after extension of scalars gives the new largest split subgroup. -/
def CanonicalSplitSubgroupBaseChange : Prop :=
  ∀ {k : Type u} [Field k] (U : AffineAlgebraicGroup k)
    (H : ClosedSubgroup U.val) (Q : AffineAlgebraicGroup k) (q : U.val ⟶ Q.val),
    IsLargestSplitSubgroup (U := U) H → IsFppfGroupQuotient H q →
    Smooth Q.val.X.hom → ConnectedSpace Q.val.X.left → IsUnipotent Q → IsWound Q.val →
    ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K],
      ∃ h : IsClosedImmersion ((groupBaseChange k K).map H.inclusion).hom.hom.left,
        IsLargestSplitSubgroup (U := baseChangedAlgebraicGroup K U)
          ⟨_, (groupBaseChange k K).map H.inclusion, h⟩

/-- The example (y^p=x-cx^p) has trivial split part over (k) and full nontrivial
split part after adjoining a (p)-th root of (c). -/
def WoundExampleSplitEnlargement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (c : k),
    (∀ d : k, d ^ p ≠ c) →
    ∃ (h : StandardGroups.HopfOperations k (WoundExample.Plane k)),
      (∀ i : WoundExample.PlaneIndex.{u},
        WoundExample.Primitive k h (MvPolynomial.X i)) ∧
      letI := h.hopf
      ∃ hI : (WoundExample.equationIdeal k p c).IsHopfIdeal k,
        letI := hI
        let W := StandardGroups.spectrum k (WoundExample.Coordinates k p c)
        ∃ (H : ClosedSubgroup W.val)
          (d : AlgebraicClosure k) (_hd : d ^ p = algebraMap k (AlgebraicClosure k) c),
          let K := IntermediateField.adjoin k ({d} : Set (AlgebraicClosure k))
          IsPurelyInseparable k K ∧
          ∃ N : ClosedSubgroup (baseChangedAlgebraicGroup K W).val,
            IsLargestSplitSubgroup (U := W) H ∧
            Nonempty (H.group ≅ Grp.trivial (SchemeOver k)) ∧
            IsLargestSplitSubgroup (U := baseChangedAlgebraicGroup K W) N ∧
            IsIso N.inclusion ∧
            ¬ Nonempty (N.group ≅ Grp.trivial (SchemeOver K)) ∧
            ¬ IsIso ((groupBaseChange k K).map H.inclusion)

end

end LinearAlgebraicGroups.Specs.Unipotent
