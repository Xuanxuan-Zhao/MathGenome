import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.IsogenyFlagComparison

open CentralIsogenies (IsCentralIsogeny characterPullback)
open FlagLineBundle (OppositeBorelPair BorelProjection AssociatedBundle)
open NormalizerLatticeAction (SplitImage)
open QuotientEmbedding (Presentation)

variable {k : Type u} [Field k]
variable {G' G : AffineAlgebraicGroup k}
variable {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}

/-- Restrictions of the isogeny to the corresponding split maximal tori and
opposite Borels. Correspondence here means that the source subgroups map
onto the indicated target subgroups on underlying schemes. -/
structure Restrictions (f : G'.val ⟶ G.val) (P' : OppositeBorelPair G')
    (P : OppositeBorelPair G) where
  torus : P'.torus.group ⟶ P.torus.group
  borel : P'.negative.group ⟶ P.negative.group
  torus_comm : torus ≫ P.torus.inclusion = P'.torus.inclusion ≫ f
  borel_comm : borel ≫ P.negative.inclusion = P'.negative.inclusion ≫ f
  torus_surjective : Surjective torus.hom.hom.left
  borel_surjective : Surjective borel.hom.hom.left

/-- The full scheme inverse image of the opposite Borel is the corresponding
opposite Borel, even when the kernel is non-smooth. -/
def OppositeBorelInverseImage : Prop :=
  ∀ {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val), IsCentralIsogeny f → ∀ r : Restrictions f P' P,
    IsPullback P'.negative.inclusion.hom.hom r.borel.hom.hom f.hom.hom
      P.negative.inclusion.hom.hom

/-- The induced map of right fppf quotients is an isomorphism. The equality
on projections identifies the lift of a coset as the image under the isogeny. -/
def FlagQuotientComparison : Prop :=
  ∀ {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val), IsCentralIsogeny f → ∀ r : Restrictions f P' P,
    ∀ (Q' : Presentation P'.negative) (Q : Presentation P.negative),
      ∃ e : Q'.scheme ≅ Q.scheme,
        Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection ∧
        Q'.quotientIso.inv ≫ rightQuotientMap f r.borel r.borel_comm.symm ≫ Q.quotientIso.hom =
          (fppfOver k).uliftYoneda.map e.hom

/-- The canonical comparison is a pullback over the equivariant isomorphism
of flags. It is linear in the torsor trivializations, acting by the identity
on the affine-line coordinate. -/
def FlagBundleComparison : Prop :=
  ∀ {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val), IsCentralIsogeny f → ∀ r : Restrictions f P' P,
    ∀ (p' : BorelProjection P') (p : BorelProjection P)
      (χ : CharacterDescent.Character P.torus.group)
      (Q' : Presentation P'.negative) (Q : Presentation P.negative)
      (a' : ModObj G'.val.X Q'.scheme) (a : ModObj G.val.X Q.scheme),
      μ[G'.val.X] ≫ Q'.projection = (𝟙 G'.val.X ⊗ₘ Q'.projection) ≫ a'.smul →
      μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
      ∀ (L' : AssociatedBundle Q' a' p' (characterPullback r.torus χ))
        (L : AssociatedBundle Q a p χ),
        ∃ (e : Q'.scheme ≅ Q.scheme) (m : L'.total ⟶ L.total),
          Q'.projection ≫ e.hom = f.hom.hom ≫ Q.projection ∧
          a'.smul ≫ e.hom = (f.hom.hom ⊗ₘ e.hom) ≫ a.smul ∧
          IsPullback m L'.projection L.projection e.hom ∧
          L'.trivialization ≫ m =
            prod.map f.hom.hom (𝟙 (FlagLineBundle.affineLine k)) ≫ L.trivialization ∧
          L'.action.smul ≫ m = (f.hom.hom ⊗ₘ m) ≫ L.action.smul

/-- A presentation of the scheme Weyl group as the right quotient of the
scheme normalizer by the split maximal torus. -/
structure WeylQuotient {H : AffineAlgebraicGroup k} (T : ClosedSubgroup H.val) where
  normalizer : ClosedSubgroup H.val
  represents : RepresentsSubgroup normalizer (fun _ g ↦ Normalizes T.inclusion g)
  torusInclusion : T.group ⟶ normalizer.group
  torusClosed : IsClosedImmersion torusInclusion.hom.hom.left
  torus_comm : torusInclusion ≫ normalizer.inclusion = T.inclusion
  scheme : AffineAlgebraicGroup k
  projection : normalizer.group ⟶ scheme.val
  quotient : Unipotent.IsFppfGroupQuotient (G := Unipotent.closedSubgroupAlgebraicGroup normalizer)
    ⟨T.group, torusInclusion, torusClosed⟩ projection

/-- Character pullback identifies the roots. The induced isomorphism of
normalizer quotients intertwines the Weyl actions on pulled-back characters. -/
def RootAndWeylComparison : Prop :=
  ∀ {k : Type u} [Field k] {G' G : AffineAlgebraicGroup k}
    {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val), IsCentralIsogeny f → ∀ r : Restrictions f P' P,
    Function.Injective (characterPullback r.torus) ∧
    Set.BijOn (characterPullback r.torus) (CharacterPairing.absoluteRoots P.torus)
      (CharacterPairing.absoluteRoots P'.torus) ∧
    ∀ (W' : WeylQuotient P'.torus) (W : WeylQuotient P.torus),
      ∃ (n : W'.normalizer.group ⟶ W.normalizer.group) (e : W'.scheme.val ≅ W.scheme.val),
        n ≫ W.normalizer.inclusion = W'.normalizer.inclusion ≫ f ∧
        W'.torusInclusion ≫ n = r.torus ≫ W.torusInclusion ∧
        W'.projection ≫ e.hom = n ≫ W.projection ∧
        ∀ (D' : SplitImage P'.torus.inclusion W'.normalizer.inclusion W'.projection)
          (D : SplitImage P.torus.inclusion W.normalizer.inclusion W.projection)
          (w' : D'.labels) (w : D.labels),
          D'.constantGroup.sectionPoint w' ≫ e.hom.hom.hom = D.constantGroup.sectionPoint w →
          ∀ χ : CharacterDescent.Character P.torus.group,
            characterPullback r.torus (w.val χ) = w'.val (characterPullback r.torus χ)

end LinearAlgebraicGroups.Specs.IsogenyFlagComparison
