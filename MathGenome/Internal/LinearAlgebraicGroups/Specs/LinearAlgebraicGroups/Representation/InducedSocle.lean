import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.PrimitiveLine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Coalgebra WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.InducedSocle

open FlagLineBundle
open CharacterDescent (Character)
open LinearAlgebraicGroups.RationalRepresentations (tensorCoordinate evaluate)
open QuotientEmbedding (Presentation)
open AbstractPairing (Datum)
open GeometricRadicals (IsUnipotentRadical)
open RootWeightAction (Representation act extendVector weightSpace fixedSpace DominanceLE IsDominant)
open PrimitiveLine (IsStable)
open CyclicHighestWeight (orbitSpan)

/-- A nonzero rational submodule with no nonzero proper rational submodule. -/
def IsSimpleSubmodule {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    {G : AffineAlgebraicGroup k} (σ : Representation G.val I) (M : Submodule k (I → k)) : Prop :=
  IsStable σ M ∧ M ≠ ⊥ ∧ ∀ N : Submodule k (I → k),
    IsStable σ N → N ≤ M → N = ⊥ ∨ N = M

/-- The socle and the weight bounds for the covariance model of the sections.
The finite-basis representation is the one obtained from the section coaction. -/
def SocleProperties {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (χ : Character P.torus.group)
    (A : HopfAlgebraCategory k) (e : specGroup A ≅ G.val)
    {D : HopfAlgebraCategory k} (q : A ⟶ D)
    (c : GroupLike k D) (ρ : RightComodule k A (covariantFunctions q c)) : Prop :=
  ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
    (b : Module.Basis I k (covariantFunctions q c))
    (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U ∧
    ∃ comm : IsCommMonObj P.torus.group.X, letI := comm
    ∃ (R : Datum P.torus) (ey : DatumAndWeyl.Identification R) (base : R.rootDatum.Base),
      (∀ α : AbstractPairing.Root P.torus,
        base.IsPos α ↔ α ∈ BorelsAndChambers.subgroupRoots P.torus P.positive) ∧
      ∃ σ : Representation G.val I,
      (∀ (S : TestAlgebra k) (g : A →ₐ[k] S) (v : I → k) (i : I),
        act σ S ((testSpec k).map (CommAlgCat.ofHom g).op ≫ e.hom.hom.hom)
          (extendVector S v) i = tensorCoordinate b i (evaluate A ρ g (b.equivFun.symm v))) ∧
      let F := fixedSpace σ (U.inclusion ≫ P.positive.inclusion)
      Function.Injective (fun f : F ↦ counit (R := k) ((b.equivFun.symm f.val : covariantFunctions q c) : A)) ∧
      (Nontrivial (covariantFunctions q c) →
        ∃ v : I → k, v ≠ 0 ∧ F = Submodule.span k {v} ∧
          v ∈ weightSpace σ P.torus χ ∧ IsDominant R P.positive χ ∧
          (∃! M : Submodule k (I → k), IsSimpleSubmodule σ M) ∧
          F ≤ orbitSpan σ (𝟙 G.val.X) v ∧
          IsSimpleSubmodule σ (orbitSpan σ (𝟙 G.val.X) v) ∧
          ∀ mu : Character P.torus.group, weightSpace σ P.torus mu ≠ ⊥ →
            DominanceLE P.torus P.positive mu χ ∧
            ∀ w₀ : R.rootDatum.weylGroup,
              (∀ w, SimpleRoots.wordLength R.rootDatum base w ≤
                SimpleRoots.wordLength R.rootDatum base w₀) →
              DominanceLE P.torus P.positive ((ey.labelEquiv w₀).val χ) mu)

/-- The necessary dominance, invariant line, simple socle and weight bounds
from E05 for the induced module of E04. -/
def Statement : Prop :=
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
      (∀ (R : TestAlgebra k) (h g : WithConv (A →ₐ[k] R)) (f : covariantFunctions q c),
        letI := convolutionGroup A R
        (Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ Commute.all _ _))
          (((covariantFunctions q c).subtype.rTensor A) (ρ.coaction f)) = (h⁻¹ * g) (f : A)) ∧
      SocleProperties P χ A e q c ρ


end LinearAlgebraicGroups.Specs.InducedSocle
