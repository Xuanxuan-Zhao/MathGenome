import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Mathlib.LinearAlgebra.TensorProduct.Basis

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct MonoidAlgebra

universe u

namespace LinearAlgebraicGroups.Specs.InnerTypeATorusWeightProjections

noncomputable section

variable {k M A : Type u} [Field k] [CommGroup M] [Ring A] [Algebra k A]

/-- A pointwise representation of the diagonalizable group in the underlying
multiplicative monoid of the scalar extension. Its values are units because
the source of each homomorphism is a group. -/
abbrev PointRepresentation (k M A : Type u) [Field k] [CommGroup M] [Ring A]
    [Algebra k A] :=
  ∀ R : TestAlgebra k, (M →* Rˣ) →* (R ⊗[k] A)

/-- Change of test algebra for a character-valued point. -/
abbrev mapCharacter {R S : TestAlgebra k} (f : R ⟶ S) (t : M →* Rˣ) :
    M →* Sˣ :=
  (Units.map f.hom.toMonoidHom).comp t

/-- The expansion at the universal point of `D(M)` and its evaluation on
every test algebra. The support of the finitely supported coefficient family
is exactly the set of nonzero projections. Cocharacters are expressed as
lattice homomorphisms to `Multiplicative ℤ` via the diagonalizable-group
comparison. -/
def WeightExpansion (ρ : PointRepresentation k M A) : Prop := by
  classical
  exact
    let R₀ : TestAlgebra k := CommAlgCat.of k (MonoidAlgebra k M)
    let e₀ : M →* R₀ˣ := (MonoidAlgebra.of k M).toHomUnits
    ∃ P : M →₀ A,
      P = TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis M k) (ρ R₀ e₀) ∧
      (∀ a b, P a * P b = if a = b then P a else 0) ∧
      (∑ a ∈ P.support, P a) = 1 ∧
      (∀ (R : TestAlgebra k) (t : M →* Rˣ),
        ρ R t = ∑ a ∈ P.support, ((t a : R) ⊗ₜ[k] P a)) ∧
      Subgroup.closure (↑P.support : Set M) = ⊤ ∧
      (∀ l μ : M →* Multiplicative ℤ, (∀ a ∈ P.support, l a = μ a) → l = μ)

/-- The faithful weight decomposition holds for any group algebra and any
target algebra. In particular it applies to a split torus and to
`A = Matrix (Fin m) (Fin m) B`, including `m = 1`. -/
def FaithfulPointWeights : Prop :=
  ∀ {k M A : Type u} [Field k] [CommGroup M] [Ring A] [Algebra k A]
    (ρ : PointRepresentation k M A),
    (∀ {R S : TestAlgebra k} (f : R ⟶ S) (t : M →* Rˣ),
      ρ S (mapCharacter f t) =
        Algebra.TensorProduct.map f.hom (AlgHom.id k A) (ρ R t)) →
    (∀ R, Function.Injective (ρ R)) →
    WeightExpansion ρ

/-- For a closed morphism out of `D(M)` the point representation is obtained
by transporting the character-valued points through the natural group
comparison for `D(M)` and postcomposing with the given scheme morphism. -/
def ClosedTorusWeights : Prop :=
  ∀ {k M A : Type u} [Field k] [CommGroup M] [Group.FG M] [Ring A] [Algebra k A]
    (G : GroupScheme k)
    (e : (groupPointsFunctor k).obj (DiagonalizableGroups.diagonalGroup k M).val ≅
      DiagonalizableGroups.characterValuedPoints k M)
    (i : (DiagonalizableGroups.diagonalGroup k M).val ⟶ G),
    IsClosedImmersion i.hom.hom.left →
    ∀ (p : ∀ R : TestAlgebra k, ((groupPointsFunctor k).obj G).obj R →* (R ⊗[k] A)),
    (∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : ((groupPointsFunctor k).obj G).obj R),
      p S (((groupPointsFunctor k).obj G).map f x) =
        Algebra.TensorProduct.map f.hom (AlgHom.id k A) (p R x)) →
    (∀ R, Function.Injective (p R)) →
    WeightExpansion (fun R => (p R).comp
      ((((groupPointsFunctor k).map i).app R).hom.comp (e.inv.app R).hom))

open _root_.Specs.RM03.CSA (isCentralDivision isCentralSimple)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open LinearAlgebraicGroups.Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)
open StandardGroups (HopfOperations spectrum)

/-- The F05 norm-one spectrum has its stated coordinate evaluation and point
identification. Every closed embedding of a split torus into that same
spectrum has the faithful weight expansion in the original tensor algebra. -/
def NormOneWeightModel {k A : Type u} [Field k] [Ring A] [Algebra k A]
    {ι : Type u} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A) : Prop :=
  ∃ H : HopfOperations k (NormOneCoordinates hA b),
    letI := H.hopf
    let G := spectrum k (NormOneCoordinates hA b)
    ∃ (p : ∀ R : TestAlgebra k, ((groupPointsFunctor k).obj G.val).obj R →* (R ⊗[k] A)),
      (∀ R, Function.Injective (p R)) ∧
      (∀ R, Set.range (p R) = {x | normAt hA b x = 1}) ∧
      (∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : ((groupPointsFunctor k).obj G.val).obj R),
        p S (((groupPointsFunctor k).obj G.val).map f x) =
          Algebra.TensorProduct.map f.hom (AlgHom.id k A) (p R x)) ∧
      (∀ (R : TestAlgebra k) (f : NormOneCoordinates hA b →ₐ[k] R)
        (x : Points G.val.X R), x.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
        ∀ j, (b.baseChange R).repr (p R x) j =
          f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X j))) ∧
      ∀ (M : Type u) [CommGroup M] [Group.FG M],
        let D := (DiagonalizableGroups.diagonalGroup k M).val
        ∃ e : (groupPointsFunctor k).obj D ≅ DiagonalizableGroups.characterValuedPoints k M,
          (∀ (R : TestAlgebra k) (f : MonoidAlgebra k M →ₐ[k] R) (x : Points D.X R),
            x.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
            ∀ a, ((show M →* Rˣ from e.hom.app R x) a : R) = f (MonoidAlgebra.of k M a)) ∧
          ∀ (i : D ⟶ G.val), IsClosedImmersion i.hom.hom.left →
            WeightExpansion (fun R => (p R).comp
              ((((groupPointsFunctor k).map i).app R).hom.comp (e.inv.app R).hom))

def NormOneTorusWeights : Prop :=
  ∀ {k A : Type u} [Field k] [Ring A] [Algebra k A]
    {ι : Type u} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A),
    NormOneWeightModel hA b

/-- The weight expansion for the division-block model of inner type A, in
the original matrix algebra and for every choice of norm coordinates. -/
def MatrixNormOneTorusWeights : Prop :=
  ∀ {k B : Type u} [Field k] [DivisionRing B] [Algebra k B]
    {m : ℕ}, isCentralDivision k B → 0 < m →
    ∃ hA : isCentralSimple k (Matrix (Fin m) (Fin m) B),
      ∀ {ι : Type u} [Fintype ι] (b : Module.Basis ι k (Matrix (Fin m) (Fin m) B)),
        NormOneWeightModel hA b

end

end LinearAlgebraicGroups.Specs.InnerTypeATorusWeightProjections
