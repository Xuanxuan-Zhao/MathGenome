import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.InducedSocle

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.InducedNonvanishing

open AbstractPairing (IsAttachedCoroot)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open FlagLineBundle
open QuotientEmbedding (Presentation)
open RootWeightAction (SimpleRoot)

/-- Dominance on the actual character lattice of the marked split torus,
tested on the coroots attached to the positive Borel's simple roots. -/
def Dominant {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (χ : Character P.torus.group) : Prop :=
  ∀ (α : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group),
    IsAttachedCoroot P.torus α.val c → 0 ≤ pairing P.torus.group χ c

/-- Nonvanishing of the actual E04 induced module, together with its socle
and longest-element weight bounds. The bundle and the character covariance
refer to the same split Borel pair and the same weight. -/
def Statement : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (χ : Character P.torus.group),
    ∃ (p : BorelProjection P) (Q : Presentation P.negative)
      (a : ModObj G.val.X Q.scheme) (A D : HopfAlgebraCategory k)
      (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
      (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k
        DiagonalizableGroups.IntegerCharacters ⟶ D)
      (c : GroupLike k D) (L : AssociatedBundle Q a p χ)
      (E : BundleSection L ≃ covariantFunctions q c)
      (ρ : RightComodule k A (covariantFunctions q c)),
      μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul ∧
      specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion ∧
      specGroupMap φ = d.hom ≫ p.projection ≫ χ ∧
      (c : D) = characterCoordinate φ ∧
      FiniteDimensional k (covariantFunctions q c) ∧
      (∀ s : BundleSection L,
        Q.projection ≫ s.val =
          CategoryTheory.Limits.prod.lift (𝟙 G.val.X)
            (e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) (E s : A)) ≫ L.trivialization) ∧
      ((covariantFunctions q c).subtype.rTensor A).comp ρ.coaction =
        (leftRegularCoaction A).comp (covariantFunctions q c).subtype ∧
      InducedSocle.SocleProperties P χ A e q c ρ ∧
      (Nontrivial (covariantFunctions q c) ↔ Dominant P χ)

end LinearAlgebraicGroups.Specs.InducedNonvanishing
