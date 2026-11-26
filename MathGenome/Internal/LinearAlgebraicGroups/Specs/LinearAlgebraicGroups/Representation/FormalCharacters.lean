import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RootWeightAction
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions

open CategoryTheory
open scoped CategoryTheory.MonObj Kronecker

universe u

namespace LinearAlgebraicGroups.Specs.FormalCharacters

open AbstractPairing (Datum)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open RootWeightAction (Representation act weightSpace)
open SchemeDerivedGroup (IsSubgroupOf)

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k I J L : Type u} [Field k]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
  {G : AffineAlgebraicGroup k}

/-- The multiplicity of a torus weight, regarded as an integer independently
of the characteristic of the ground field. -/
def multiplicity (T : ClosedSubgroup G.val) (ρ : Representation G.val I)
    (χ : Character T.group) : ℤ :=
  Module.finrank k (weightSpace ρ T χ)

/-- The integral formal character. The coefficient theorem establishes finite
support and recovers every coefficient for the split torus in the theorem. -/
def formalCharacter (T : ClosedSubgroup G.val) (ρ : Representation G.val I) :
    MonoidAlgebra ℤ (Character T.group) := by
  classical
  exact MonoidAlgebra.ofCoeff (if h : (Function.support (multiplicity T ρ)).Finite
    then Finsupp.ofSupportFinite (multiplicity T ρ) h else 0)

/-- Equivariance of a linear map after extending its matrix to each test algebra. -/
def Equivariant (ρ : Representation G.val I) (σ : Representation G.val J)
    (f : (I → k) →ₗ[k] (J → k)) : Prop :=
  ∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (v : I → R),
    let F := ((LinearMap.toMatrix' f).map (algebraMap k R)).mulVec
    F (act ρ R g v) = act σ R g (F v)

/-- The tensor representation on the product basis acts by the Kronecker
product over every commutative test algebra. -/
def tensorRepresentation (ρ : Representation G.val I) (σ : Representation G.val J) :
    Representation G.val (I × J) where
  app R := GrpCat.ofHom
    { toFun := fun g => Matrix.GeneralLinearGroup.kronecker (ρ.app R g) (σ.app R g)
      map_one' := by
        apply Units.ext
        change (ρ.app R 1).val ⊗ₖ (σ.app R 1).val = 1
        rw [map_one, map_one, Units.val_one, Units.val_one, Matrix.one_kronecker_one]
      map_mul' g h := by
        apply Units.ext
        change (ρ.app R (g * h)).val ⊗ₖ (σ.app R (g * h)).val =
          ((ρ.app R g).val ⊗ₖ (σ.app R g).val) * ((ρ.app R h).val ⊗ₖ (σ.app R h).val)
        rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_kronecker_mul] }
  naturality R S a := by
    apply GrpCat.ext
    intro g
    apply Units.ext
    have hρ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality a)) g
    have hσ := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (σ.naturality a)) g
    change (ρ.app S (((groupPointsFunctor k).obj G.val).map a g)).val ⊗ₖ
      (σ.app S (((groupPointsFunctor k).obj G.val).map a g)).val =
        ((ρ.app R g).val ⊗ₖ (σ.app R g).val).map a.hom
    rw [show ρ.app S (((groupPointsFunctor k).obj G.val).map a g) =
      (StandardGroups.generalLinearPoints k I).map a (ρ.app R g) from hρ,
      show σ.app S (((groupPointsFunctor k).obj G.val).map a g) =
      (StandardGroups.generalLinearPoints k J).map a (σ.app R g) from hσ]
    ext p q
    exact (map_mul a.hom _ _).symm

/-- The coefficients in the character lattice are the weight multiplicities. -/
def CoefficientFormula (T : ClosedSubgroup G.val) : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I),
    (Function.support (multiplicity T ρ)).Finite ∧
    ∀ χ, (formalCharacter T ρ).coeff χ = multiplicity T ρ χ

/-- Additivity holds for all short exact sequences of rational representations. -/
def ExactAdditivity (T : ClosedSubgroup G.val) : Prop :=
  ∀ {I J L : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype L] [DecidableEq L] (ρ : Representation G.val I) (σ : Representation G.val J)
    (τ : Representation G.val L) (f : (I → k) →ₗ[k] (J → k))
    (g : (J → k) →ₗ[k] (L → k)),
    Equivariant ρ σ f → Equivariant σ τ g → Function.Injective f →
    Function.Exact f g → Function.Surjective g →
    formalCharacter T σ = formalCharacter T ρ + formalCharacter T τ

/-- Tensor products multiply in the integral group algebra of characters. -/
def TensorMultiplicativity (T : ClosedSubgroup G.val) : Prop :=
  ∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ : Representation G.val I) (σ : Representation G.val J),
    formalCharacter T (tensorRepresentation ρ σ) = formalCharacter T ρ * formalCharacter T σ

/-- The coefficients are constant under the actual Weyl action on the character lattice. -/
def WeylInvariance {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (e : DatumAndWeyl.Identification D) : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I)
    (w : D.rootDatum.weylGroup) (χ : Character T.group),
    (formalCharacter T ρ).coeff ((e.labelEquiv w).val χ) = (formalCharacter T ρ).coeff χ

/-- Integral formal characters of finite-dimensional rational modules for a
connected split reductive group with a chosen split Borel pair. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsSubgroupOf T B →
      CoefficientFormula T ∧ ExactAdditivity T ∧ TensorMultiplicativity T ∧
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ (D : Datum T) (e : DatumAndWeyl.Identification D), WeylInvariance e

end

end LinearAlgebraicGroups.Specs.FormalCharacters
