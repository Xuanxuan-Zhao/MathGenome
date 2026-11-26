import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveFlags
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.TensorAndDual
import Mathlib.RingTheory.HopfAlgebra.GroupLike

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Coalgebra WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.FlagLineBundle

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open CharacterDescent (Character)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open QuotientEmbedding (Presentation)

variable {k : Type u} [Field k]

/-- The split Borel pair and the opposite Borel used for induction. -/
structure OppositeBorelPair (G : AffineAlgebraicGroup k) where
  torus : ClosedSubgroup G.val
  positive : ClosedSubgroup G.val
  negative : ClosedSubgroup G.val
  reductive : IsReductive G
  split : IsSplitTorus torus.group
  maximal : IsGeometricallyMaximal torus
  positiveBorel : IsKBorel positive
  negativeBorel : IsKBorel negative
  inPositive : IsSubgroupOf torus positive
  inNegative : IsSubgroupOf torus negative
  opposite : OpenCell.AreOpposite torus positive negative

/-- The projection of the opposite Borel onto the split maximal torus, with
its kernel identified as the unipotent radical. -/
structure BorelProjection {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G) where
  inclusion : P.torus.group ⟶ P.negative.group
  inclusion_comp : inclusion ≫ P.negative.inclusion = P.torus.inclusion
  projection : P.negative.group ⟶ P.torus.group
  section_projection : inclusion ≫ projection = 𝟙 _
  radical : ClosedSubgroup P.negative.group
  isRadical : IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.negative) radical
  isKernel : IsSchemeKernel projection radical

/-- Existence of the split projection and of the smooth projective right quotient
by the opposite Borel, with its quotient torsor. -/
def OppositeFlagGeometry : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G),
    Nonempty (BorelProjection P) ∧ Nonempty (Presentation P.negative) ∧
      ∀ Q : Presentation P.negative,
        Smooth Q.scheme.hom ∧ IsProper Q.scheme.hom ∧
        HomogeneousQuotient.IsQuotientTorsor Q ∧
        ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
          (a : ModObj G.val.X Q.scheme) (j : Q.scheme ⟶ ProjectiveSpaces.projectiveSpace k V),
          IsClosedImmersion j.left ∧
          μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul

variable {A D : HopfAlgebraCategory k}

/-- The function on the subgroup obtained by pulling back the standard coordinate
on the multiplicative group along the character. -/
def characterCoordinate
    (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D) :
    D :=
  φ.hom (MonoidAlgebra.of k _ DiagonalizableGroups.integerGenerator)

/-- The restriction of the torus character along the Borel projection acts
on the line by the pulled-back group-like function. -/
def BorelCharacterLine : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group),
    ∃ (D : HopfAlgebraCategory k) (d : specGroup D ≅ P.negative.group)
      (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D)
      (c : GroupLike k D) (ρ : RightComodule k D k),
      specGroupMap φ = d.hom ≫ p.projection ≫ χ ∧
      (c : D) = characterCoordinate φ ∧
      ∀ z, ρ.coaction z = z ⊗ₜ[k] (c : D)

/-- The one-dimensional module for a group-like character coordinate. -/
def CharacterLine : Prop :=
  ∀ {k : Type u} [Field k] (D : HopfAlgebraCategory k) (c : GroupLike k D),
    ∃ ρ : RightComodule k D k, ∀ z, ρ.coaction z = z ⊗ₜ[k] (c : D)

/-- Scheme covariance in the coordinate algebras of the group and subgroup.
The character coordinate is inverted in the covariance equation. -/
def covariantFunctions (q : A ⟶ D) (c : GroupLike k D) : Submodule k A :=
  LinearMap.eqLocus
    (q.hom.toAlgHom.toLinearMap.lTensor A ∘ₗ comul)
    (TensorProduct.mk k A D |>.flip (↑(c⁻¹) : D))

/-- The two-variable formula is tested on all test algebras, including
the tensor algebra carrying the universal pair of points. -/
def CovarianceOnPoints : Prop :=
  ∀ {k : Type u} [Field k] {A D : HopfAlgebraCategory k} (q : A ⟶ D)
    (c : GroupLike k D) (f : A),
    f ∈ covariantFunctions q c ↔
      ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (b : D →ₐ[k] R),
        (g * toConv (b.comp q.hom.toAlgHom)) f = b (↑(c⁻¹) : D) * g f

/-- Right coaction for the left regular action. Inversion is applied to the
first variable of multiplication, which goes into the coefficient factor. -/
def leftRegularCoaction (A : HopfAlgebraCategory k) : A →ₗ[k] A ⊗[k] A :=
  (HopfAlgebra.antipode k).lTensor A ∘ₗ
    (TensorProduct.comm k A A).toLinearMap ∘ₗ comul

/-- Left translation restricts to a rational coaction on the covariant functions. -/
def CovariantCoaction : Prop :=
  ∀ {k : Type u} [Field k] {A D : HopfAlgebraCategory k} (q : A ⟶ D)
    (c : GroupLike k D),
    let W := covariantFunctions q c
    ∃ ρ : RightComodule k A W,
      (W.subtype.rTensor A).comp ρ.coaction = (leftRegularCoaction A).comp W.subtype ∧
      ∀ (R : TestAlgebra k) (h g : WithConv (A →ₐ[k] R)) (f : W),
        letI := convolutionGroup A R
        (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ Commute.all _ _))
          ((W.subtype.rTensor A) (ρ.coaction f)) = (h⁻¹ * g) (f : A)

/-- The trivial one-dimensional affine space over the ground field. -/
abbrev affineLine (k : Type u) [Field k] : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (Polynomial k)))

/-- The test-algebra point of the line with coordinate z. -/
def linePoint (R : TestAlgebra k) (z : R) : Points (affineLine k) R :=
  (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval z)).op

/-- The total space with its descent trivialization. The transition formula
uses the inverse character, and changes to Zariski charts are linear in
the fiber coordinate. -/
structure AssociatedBundle {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (p : BorelProjection P) (χ : Character P.torus.group) where
  total : SchemeOver k
  projection : total ⟶ Q.scheme
  action : ModObj G.val.X total
  trivialization : G.val.X ⨯ affineLine k ⟶ total
  trivializes : IsPullback (prod.fst : G.val.X ⨯ affineLine k ⟶ G.val.X)
    trivialization Q.projection projection
  equivariant : action.smul ≫ projection = (𝟙 G.val.X ⊗ₘ projection) ≫ a.smul
  transition : ∀ (R : TestAlgebra k) (g : Points G.val.X R)
    (b : Points P.negative.group.X R) (z : R),
    prod.lift (g * (b ≫ P.negative.inclusion.hom.hom))
      (linePoint R (CharacterPairing.characterValue (p.projection ≫ χ) R (b⁻¹) * z)) ≫ trivialization =
    prod.lift g (linePoint R z) ≫ trivialization
  leftTranslation : ∀ (R : TestAlgebra k) (h g : Points G.val.X R) (z : R),
    lift h (prod.lift g (linePoint R z) ≫ trivialization) ≫ action.smul =
      prod.lift (h * g) (linePoint R z) ≫ trivialization
  charts : ∀ y : Q.scheme.left, ∃ (U : SchemeOver k) (j : U ⟶ Q.scheme)
    (t : U ⨯ affineLine k ⟶ total),
    IsOpenImmersion j.left ∧ y ∈ Set.range j.left ∧
    IsPullback (prod.fst : U ⨯ affineLine k ⟶ U) t j projection ∧
    ∀ (R : TestAlgebra k) (u : Points U R) (g : Points G.val.X R),
      u ≫ j = g ≫ Q.projection →
      ∃ e : Rˣ, ∀ z : R,
        prod.lift u (linePoint R z) ≫ t =
          prod.lift g (linePoint R ((e : R) * z)) ≫ trivialization

abbrev BundleSection {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : Character P.torus.group}
    (L : AssociatedBundle Q a p χ) :=
  {s : Q.scheme ⟶ L.total // s ≫ L.projection = 𝟙 _}

/-- A regular function satisfies covariance for the right action of B⁻ if
its values as morphisms to the affine line satisfy the displayed identity
on every test algebra. -/
def SchemeCovariant {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group)
    (f : G.val.X ⟶ affineLine k) : Prop :=
  ∀ (R : TestAlgebra k) (g : Points G.val.X R) (b : Points P.negative.group.X R) (z : R),
    g ≫ f = linePoint R z →
    (g * (b ≫ P.negative.inclusion.hom.hom)) ≫ f =
      linePoint R (CharacterPairing.characterValue (p.projection ≫ χ) R (b⁻¹) * z)

/-- The coordinate-algebra equalizer expresses the covariance of the regular
function as a scheme morphism, using the same inclusion and character. -/
def SchemeCovarianceComparison : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ : Character P.torus.group) {A D : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k
      DiagonalizableGroups.IntegerCharacters ⟶ D),
    specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion →
    specGroupMap φ = d.hom ≫ p.projection ≫ χ →
    ∀ (c : GroupLike k D), (c : D) = characterCoordinate φ →
      ∃ F : A ≃ (G.val.X ⟶ affineLine k),
        (∀ f : A, F f = e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) f) ∧
        ∀ f : A, f ∈ covariantFunctions q c ↔ SchemeCovariant p χ (F f)

/-- Descent identifies the sections of a bundle with the covariant functions
via the specified trivialization over G. -/
def SectionsAreCovariant : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : Character P.torus.group}
    (L : AssociatedBundle Q a p χ),
    ∃ E : BundleSection L ≃ {f : G.val.X ⟶ affineLine k // SchemeCovariant p χ f},
      ∀ s : BundleSection L,
        Q.projection ≫ s.val =
          prod.lift (𝟙 G.val.X) (E s).val ≫ L.trivialization

/-- Construct the line bundle for every character in any choice of quotient
presentation and coordinate algebras. Its sections identify by pullback with
the finite-dimensional space carrying the coaction of left translation. -/
def FlagLineBundleAndSections : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (p : BorelProjection P) (χ : Character P.torus.group) (Q : Presentation P.negative)
    (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∀ (A D : HopfAlgebraCategory k) (e : specGroup A ≅ G.val)
      (d : specGroup D ≅ P.negative.group)
      (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k
        DiagonalizableGroups.IntegerCharacters ⟶ D),
      specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion →
      specGroupMap φ = d.hom ≫ p.projection ≫ χ →
      ∃ (c : GroupLike k D), (c : D) = characterCoordinate φ ∧
        ∃ (L : AssociatedBundle Q a p χ) (E : BundleSection L ≃ covariantFunctions q c)
          (ρ : RightComodule k A (covariantFunctions q c)),
          FiniteDimensional k (covariantFunctions q c) ∧
          (∀ (s : BundleSection L),
            Q.projection ≫ s.val =
              prod.lift (𝟙 G.val.X)
                (e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) (E s : A)) ≫ L.trivialization) ∧
          ((covariantFunctions q c).subtype.rTensor A).comp ρ.coaction =
            (leftRegularCoaction A).comp (covariantFunctions q c).subtype ∧
          ∀ (R : TestAlgebra k) (h g : WithConv (A →ₐ[k] R)) (f : covariantFunctions q c),
            letI := convolutionGroup A R
            (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ Commute.all _ _))
              (((covariantFunctions q c).subtype.rTensor A) (ρ.coaction f)) =
                (h⁻¹ * g) (f : A)

/-- Existence with the original split reductive hypotheses. The character
line, quotient, linearized bundle and finite-dimensional module use the same
projection and the same character coordinate. -/
def FlagInduction : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (χ : Character P.torus.group),
    ∃ (p : BorelProjection P) (Q : Presentation P.negative)
      (a : ModObj G.val.X Q.scheme) (A D : HopfAlgebraCategory k)
      (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
      (q : A ⟶ D) (φ : DiagonalizableGroups.groupAlgebra k
        DiagonalizableGroups.IntegerCharacters ⟶ D)
      (c : GroupLike k D) (ρ₁ : RightComodule k D k)
      (L : AssociatedBundle Q a p χ) (E : BundleSection L ≃ covariantFunctions q c)
      (ρ : RightComodule k A (covariantFunctions q c)),
      Smooth Q.scheme.hom ∧ IsProper Q.scheme.hom ∧ HomogeneousQuotient.IsQuotientTorsor Q ∧
      (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
        (j : Q.scheme ⟶ ProjectiveSpaces.projectiveSpace k V), IsClosedImmersion j.left) ∧
      μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul ∧
      specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion ∧
      specGroupMap φ = d.hom ≫ p.projection ≫ χ ∧
      (c : D) = characterCoordinate φ ∧ (∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D)) ∧
      FiniteDimensional k (covariantFunctions q c) ∧
      (∀ s : BundleSection L,
        Q.projection ≫ s.val =
          prod.lift (𝟙 G.val.X)
            (e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) (E s : A)) ≫ L.trivialization) ∧
      ((covariantFunctions q c).subtype.rTensor A).comp ρ.coaction =
        (leftRegularCoaction A).comp (covariantFunctions q c).subtype ∧
      ∀ (R : TestAlgebra k) (h g : WithConv (A →ₐ[k] R)) (f : covariantFunctions q c),
        letI := convolutionGroup A R
        (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ Commute.all _ _))
          (((covariantFunctions q c).subtype.rTensor A) (ρ.coaction f)) = (h⁻¹ * g) (f : A)

end LinearAlgebraicGroups.Specs.FlagLineBundle
