import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
import Mathlib.GroupTheory.QuotientGroup.Basic

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Relative.RelativeWeylScheme

open GeometricBorelConjugacy (ConjugatesSubgroups)
open GeometricRadicals (IsReductive)
open MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open NormalizerLatticeAction (SplitImage)
open RankOneFlag (SameSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)
open UnipotentRadicalIntersection (IsSchemeIntersection)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The scheme normalizer, centralizer and right fppf quotient of the indicated split torus. -/
structure QuotientData (S : ClosedSubgroup G.val) where
  normalizer : ClosedSubgroup G.val
  centralizer : ClosedSubgroup G.val
  inclusion : centralizer.group ⟶ normalizer.group
  inclusionClosed : IsClosedImmersion inclusion.hom.hom.left
  group : AffineAlgebraicGroup k
  projection : normalizer.group ⟶ group.val
  normalizerProperty : RepresentsSubgroup normalizer (fun _ g ↦ Normalizes S.inclusion g)
  centralizerProperty : RepresentsSubgroup centralizer (fun _ g ↦ Centralizes S.inclusion g)
  inclusionProperty : inclusion ≫ normalizer.inclusion = centralizer.inclusion
  quotientProperty : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup normalizer)
    ⟨_, inclusion, inclusionClosed⟩ projection
  finite : IsFinite group.val.X.hom
  etale : Etale group.val.X.hom
  splitImage : SplitImage S.inclusion normalizer.inclusion projection

/-- Minimal rational parabolic subgroups containing S, with equality as closed subgroup schemes. -/
def ParabolicsThrough (G : AffineAlgebraicGroup k) (S : ClosedSubgroup G.val) :=
  Quotient (show Setoid {P : ClosedSubgroup G.val // IsMinimalParabolic G P ∧ IsSubgroupOf S P} from
    { r := fun P Q ↦ SameSubgroup P.val Q.val
      iseqv :=
        let refl (P : ClosedSubgroup G.val) : IsSubgroupOf P P :=
          ⟨𝟙 _, Category.id_comp _⟩
        let trans {P Q R : ClosedSubgroup G.val} (h : IsSubgroupOf P Q)
            (j : IsSubgroupOf Q R) : IsSubgroupOf P R := by
          obtain ⟨a, ha⟩ := h
          obtain ⟨b, hb⟩ := j
          exact ⟨a ≫ b, by rw [Category.assoc, hb, ha]⟩
        ⟨fun P ↦ ⟨refl P.val, refl P.val⟩, fun h ↦ ⟨h.2, h.1⟩,
          fun h j ↦ ⟨trans h.1 j.1, trans j.2 h.2⟩⟩ })

abbrev markedParabolic (P : ClosedSubgroup G.val) (hP : IsMinimalParabolic G P)
    {S : ClosedSubgroup G.val} (hSP : IsSubgroupOf S P) : ParabolicsThrough G S :=
  Quotient.mk _ ⟨P, hP, hSP⟩

/-- The quotient is finite constant, and the indicated intersection is schematic. -/
def FiniteConstantQuotient : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (S : ClosedSubgroup G.val), IsMaximalSplitTorus S →
      ∃ D : QuotientData S, ∀ (P : ClosedSubgroup G.val),
        IsMinimalParabolic G P → IsSubgroupOf S P →
          IsSchemeIntersection {D.normalizer, P} D.centralizer

/-- The homomorphism on rational points induced by the quotient projection. -/
noncomputable abbrev rationalProjection {S : ClosedSubgroup G.val} (D : QuotientData S) :
    (𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) →*
      (𝟙_ (SchemeOver k) ⟶ D.group.val.X) :=
  IsMonHom.monoidHom D.projection.hom.hom _

/-- The action is induced by conjugation, is simply transitive, and the projection
identifies the label group with the quotient of rational normalizer points by rational
centralizer points. -/
def RelativeWeylAction : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (S P : ClosedSubgroup G.val), IsMaximalSplitTorus S →
      IsMinimalParabolic G P → IsSubgroupOf S P →
      ∀ D : QuotientData S,
      let W := D.splitImage.labels
      let Z := MonoidHom.range (IsMonHom.monoidHom D.inclusion.hom.hom (𝟙_ (SchemeOver k)))
      ∃ (_hZ : Z.Normal) (e : (𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) ⧸ Z ≃* W)
        (a : MulAction W (ParabolicsThrough G S)),
        (∀ n, rationalProjection D n = D.splitImage.constantGroup.sectionPoint
          (e (QuotientGroup.mk n))) ∧
        (∀ (w : W), ∃ n, rationalProjection D n = D.splitImage.constantGroup.sectionPoint w) ∧
        (∀ (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) (A B : ClosedSubgroup G.val)
          (hA : IsMinimalParabolic G A) (hB : IsMinimalParabolic G B)
          (hSA : IsSubgroupOf S A) (hSB : IsSubgroupOf S B),
          ConjugatesSubgroups (n ≫ D.normalizer.inclusion.hom.hom) A B ↔
            @SMul.smul W (ParabolicsThrough G S) a.toSMul (e (QuotientGroup.mk n))
              (markedParabolic A hA hSA) = markedParabolic B hB hSB) ∧
        ∀ x y : ParabolicsThrough G S,
          ∃! w : W, @SMul.smul W (ParabolicsThrough G S) a.toSMul w x = y

/-- Two minimal rational parabolics share a split torus maximal in the whole group. -/
def CommonMaximalSplitTorus : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (P Q : ClosedSubgroup G.val),
      IsMinimalParabolic G P → IsMinimalParabolic G Q →
        ∃ S : ClosedSubgroup G.val, IsMaximalSplitTorus S ∧ IsSubgroupOf S P ∧ IsSubgroupOf S Q

end LinearAlgebraicGroups.Specs.Relative.RelativeWeylScheme
