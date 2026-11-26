import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite Coalgebra HopfAlgebra WithConv
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable (k : Type u) [Field k]

/-- Commutative Hopf algebras over the same base field as the group schemes. -/
abbrev HopfAlgebraCategory := CommHopfAlgCat.{u} k

/-- The full category on the affine group schemes of A01. -/
abbrev AffineGroupCategory :=
  InducedCategory (Specs.GroupScheme k) (Subtype.val : Specs.AffineGroupScheme k → _)

/-- The full category on the affine algebraic groups of A01. -/
abbrev AffineAlgebraicGroupCategory :=
  InducedCategory (Specs.GroupScheme k) (Subtype.val : Specs.AffineAlgebraicGroup k → _)

/-- Finitely generated as an algebra over the field. -/
abbrev FiniteTypeHopfAlgebraCategory :=
  InducedCategory (HopfAlgebraCategory k)
    (Subtype.val : { A : HopfAlgebraCategory k // Algebra.FiniteType k A } → _)

abbrev affineGroupInclusion : AffineGroupCategory k ⥤ Specs.GroupScheme k :=
  inducedFunctor Subtype.val

abbrev schemeOfAffineGroup : AffineGroupCategory k ⥤ SchemeOver k :=
  affineGroupInclusion k ⋙ Grp.forget _

abbrev forgetHopfAlgebra : HopfAlgebraCategory k ⥤ TestAlgebra k :=
  forget₂ (HopfAlgebraCategory k) (CommBialgCat k) ⋙
    forget₂ (CommBialgCat k) (TestAlgebra k)

/-- Spectrum with its Hopf-induced group law, regarded as an affine group scheme. -/
def affineHopfSpec : (HopfAlgebraCategory k)ᵒᵖ ⥤ AffineGroupCategory k where
  obj A := ⟨(hopfSpec (CommRingCat.of k)).obj A,
    essImage_hopfSpec.mp ⟨A, ⟨Iso.refl _⟩⟩⟩
  map f := InducedCategory.homMk ((hopfSpec (CommRingCat.of k)).map f)
  map_id A := by apply InducedCategory.hom_ext; exact (hopfSpec (CommRingCat.of k)).map_id _
  map_comp f g := by apply InducedCategory.hom_ext; exact (hopfSpec (CommRingCat.of k)).map_comp _ _

lemma hopfSpec_locallyOfFiniteType_iff (A : HopfAlgebraCategory k) :
    LocallyOfFiniteType ((hopfSpec (CommRingCat.of k)).obj (op A)).X.hom ↔
      Algebra.FiniteType k A := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap

/-- Spectrum restricted to finitely generated commutative Hopf algebras. -/
def finiteTypeHopfSpec :
    (FiniteTypeHopfAlgebraCategory k)ᵒᵖ ⥤ AffineAlgebraicGroupCategory k where
  obj A :=
    let B := A.unop.val
    let G := (affineHopfSpec k).obj (op B)
    ⟨G.val, G.property, (hopfSpec_locallyOfFiniteType_iff k B).mpr A.unop.property, by
      change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      infer_instance⟩
  map f := InducedCategory.homMk ((hopfSpec (CommRingCat.of k)).map f.unop.hom.op)
  map_id A := by
    apply InducedCategory.hom_ext
    exact (hopfSpec (CommRingCat.of k)).map_id (op A.unop.val)
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (hopfSpec (CommRingCat.of k)).map_comp f.unop.hom.op g.unop.hom.op

variable {k}

/-- Convolution of algebra maps to an arbitrary test algebra, with inverse induced by
the antipode of the source. -/
@[instance_reducible]
def convolutionGroup (A : HopfAlgebraCategory k) (R : TestAlgebra k) :
    Group (WithConv (A →ₐ[k] R)) where
  toMonoid := inferInstance
  inv f := toConv (f.ofConv.comp (antipodeAlgHom k A))
  inv_mul_cancel f := by
    let s : WithConv (A →ₐ[k] A) := toConv (antipodeAlgHom k A)
    let i : WithConv (A →ₐ[k] A) := toConv (AlgHom.id k A)
    have hs : s * i = 1 := AlgHom.antipode_id_cancel
    have h := AlgHom.comp_convMul_distrib f.ofConv s i
    rw [hs] at h
    have h₁ : f.ofConv.comp (1 : WithConv (A →ₐ[k] A)).ofConv =
        (1 : WithConv (A →ₐ[k] R)).ofConv := by
      ext x
      exact f.ofConv.commutes (counit x)
    apply WithConv.ofConv_injective
    change (toConv (f.ofConv.comp s.ofConv) * f).ofConv = _
    simpa [i, h₁] using h.symm

/-- The functor of algebra maps out of a Hopf algebra, with convolution on each test algebra. -/
@[implicit_reducible]
def convolutionPoints (A : HopfAlgebraCategory k) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := letI := convolutionGroup A R; GrpCat.of (WithConv (A →ₐ[k] R))
  map {R S} a :=
    letI := convolutionGroup A R
    letI := convolutionGroup A S
    GrpCat.ofHom
      { toFun := fun f ↦ toConv (a.hom.comp f.ofConv)
        map_one' := by
          apply WithConv.ofConv_injective
          ext x
          exact a.hom.commutes (counit x)
        map_mul' := fun f g ↦
          WithConv.ofConv_injective (AlgHom.comp_convMul_distrib a.hom f g) }
  map_id R := by
    apply GrpCat.ext
    intro f
    exact WithConv.ofConv_injective (AlgHom.id_comp _)
  map_comp a b := by
    apply GrpCat.ext
    intro f
    exact WithConv.ofConv_injective (AlgHom.comp_assoc _ _ _)

namespace Specs

def AffineHopfSpecEquivalence : Prop :=
  ∀ (k : Type u) [Field k], (affineHopfSpec k).IsEquivalence

def FiniteTypeHopfSpecEquivalence : Prop :=
  ∀ (k : Type u) [Field k], (finiteTypeHopfSpec k).IsEquivalence

/-- The underlying algebra functor of the inverse equivalence is global sections,
including its action on morphisms. -/
def CoordinateHopfComparison : Prop :=
  ∀ (k : Type u) [Field k] [_h : (affineHopfSpec k).IsEquivalence],
    ∃ e : (affineHopfSpec k).inv ⋙ (forgetHopfAlgebra k).op ≅
        schemeOfAffineGroup k ⋙ algΓ (CommRingCat.of k),
      ∀ G : AffineGroupCategory k,
        (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app G.val.X ≫
            (testSpec k).map (e.inv.app G) =
          ((affineHopfSpec k).asEquivalence.counitIso.inv.app G).hom.hom.hom

/-- The three group operations under the affine product identification. -/
def HopfSpecOperations : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k),
    let G := (hopfSpec (CommRingCat.of k)).obj (op A)
    μ[G.X].left = (pullbackSpecIso (CommRingCat.of k) (CommRingCat.of A) (CommRingCat.of A)).hom ≫
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k A).toRingHom) ∧
    η[G.X].left = Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k A).toRingHom) ∧
    ι[G.X].left = Spec.map (CommRingCat.ofHom (antipodeAlgHom k A).toRingHom)

/-- Morphisms act by spectrum in the opposite direction and preserve the antipode. -/
def HopfSpecMorphism : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k} (a : A ⟶ B),
    ((hopfSpec (CommRingCat.of k)).map a.op).hom.hom.left =
        Spec.map (CommRingCat.ofHom a.hom.toAlgHom.toRingHom) ∧
      a.hom.toAlgHom.comp (antipodeAlgHom k A) =
        (antipodeAlgHom k B).comp a.hom.toAlgHom

def HopfSpecCommutativity : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k),
    IsCommMonObj ((hopfSpec (CommRingCat.of k)).obj (op A)).X ↔ IsCocomm k A

def CoordinateHopfCommutativity : Prop :=
  ∀ (k : Type u) [Field k] [_h : (affineHopfSpec k).IsEquivalence] (G : AffineGroupCategory k),
    IsCommMonObj G.val.X ↔ IsCocomm k ((affineHopfSpec k).inv.obj G).unop

/-- Convolution gives the point groups of the spectrum naturally in the test algebra
and in the Hopf algebra. The comparison sends an algebra map to its spectrum. -/
def HopfSpecPoints : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ e : ∀ A : HopfAlgebraCategory k, convolutionPoints A ≅
        (groupPointsFunctor k).obj ((hopfSpec (CommRingCat.of k)).obj (op A)),
      (∀ (A : HopfAlgebraCategory k) (R : TestAlgebra k) (f : WithConv (A →ₐ[k] R)),
        ((e A).hom.app R f : Points ((hopfSpec (CommRingCat.of k)).obj (op A)).X R).left =
          Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)) ∧
      (∀ {A B : HopfAlgebraCategory k} (a : A ⟶ B) (R : TestAlgebra k)
        (f : WithConv (B →ₐ[k] R)),
        (e A).hom.app R (toConv (f.ofConv.comp a.hom.toAlgHom)) =
          ((groupPointsFunctor k).map ((hopfSpec (CommRingCat.of k)).map a.op)).app R
            ((e B).hom.app R f))

/-- The point description for any affine group scheme, via its coordinate Hopf algebra. -/
def CoordinateHopfPoints : Prop :=
  ∀ (k : Type u) [Field k] [_h : (affineHopfSpec k).IsEquivalence] (G : AffineGroupCategory k),
    ∃ e : (convolutionPoints ((affineHopfSpec k).inv.obj G).unop) ≅
        (groupPointsFunctor k).obj G.val,
      ∀ (R : TestAlgebra k) (f : WithConv (((affineHopfSpec k).inv.obj G).unop →ₐ[k] R)),
        (e.hom.app R f : Points G.val.X R).left =
          Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
            ((affineHopfSpec k).asEquivalence.counitIso.hom.app G).hom.hom.hom.left

end Specs
end
end LinearAlgebraicGroups
