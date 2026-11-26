import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.IntegralRankOneExtension

open IntegralRootRelations (upper lower diagonal)

noncomputable section

abbrev Integers := ULift.{u} ℤ
abbrev IntegralAlgebra := CommAlgCat.{u} Integers.{u}
abbrev IntegralScheme := Over (Spec (CommRingCat.of Integers.{u}))
abbrev IntegralGroup := Grp IntegralScheme.{u}

abbrev integralSpec : IntegralAlgebra.{u}ᵒᵖ ⥤ IntegralScheme.{u} :=
  algSpec (CommRingCat.of Integers.{u})

abbrev integralPointFunctor (G : IntegralGroup.{u}) : IntegralAlgebra.{u} ⥤ GrpCat.{u} :=
  integralSpec.rightOp ⋙ yonedaGrp.obj G

abbrev IntegralPoints (G : IntegralGroup.{u}) (R : IntegralAlgebra.{u}) :=
  (integralPointFunctor G).obj R

/-- The functor of determinant-one matrices of size two over the integers. -/
def rankOnePoints : IntegralAlgebra.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro x; ext i j; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext i j; rfl

/-- Natural root and coroot homomorphisms satisfying the rank-one relations. -/
structure RootHomomorphisms (G : IntegralGroup.{u}) where
  positive : ∀ R : IntegralAlgebra.{u}, Multiplicative R →* IntegralPoints G R
  negative : ∀ R : IntegralAlgebra.{u}, Multiplicative R →* IntegralPoints G R
  coroot : ∀ R : IntegralAlgebra.{u}, Rˣ →* IntegralPoints G R
  map_positive : ∀ {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (x : R),
    (integralPointFunctor G).map f (positive R (.ofAdd x)) =
      positive S (.ofAdd (f.hom x))
  map_negative : ∀ {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (x : R),
    (integralPointFunctor G).map f (negative R (.ofAdd x)) =
      negative S (.ofAdd (f.hom x))
  map_coroot : ∀ {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (a : Rˣ),
    (integralPointFunctor G).map f (coroot R a) =
      coroot S (Units.map f.hom.toMonoidHom a)
  positive_conjugation : ∀ (R : IntegralAlgebra.{u}) (a : Rˣ) (x : R),
    coroot R a * positive R (.ofAdd x) * (coroot R a)⁻¹ =
      positive R (.ofAdd ((a : R) ^ 2 * x))
  negative_conjugation : ∀ (R : IntegralAlgebra.{u}) (a : Rˣ) (x : R),
    coroot R a * negative R (.ofAdd x) * (coroot R a)⁻¹ =
      negative R (.ofAdd ((↑a⁻¹ : R) ^ 2 * x))
  opposite : ∀ (R : IntegralAlgebra.{u}) (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
    positive R (.ofAdd x) * negative R (.ofAdd y) =
      negative R (.ofAdd (y * (↑s⁻¹ : R))) * coroot R s *
        positive R (.ofAdd (x * (↑s⁻¹ : R)))

def Extension : Prop :=
  ∀ (G : IntegralGroup.{u}), IsAffine G.X.left → ∀ h : RootHomomorphisms G,
    ∃ F : rankOnePoints.{u} ⟶ integralPointFunctor G,
      (∀ (R : IntegralAlgebra.{u}) (x : R), F.app R (upper x) = h.positive R (.ofAdd x)) ∧
      (∀ (R : IntegralAlgebra.{u}) (y : R), F.app R (lower y) = h.negative R (.ofAdd y)) ∧
      (∀ (R : IntegralAlgebra.{u}) (a : Rˣ), F.app R (diagonal a) = h.coroot R a)

end

end LinearAlgebraicGroups.Specs.IntegralRankOneExtension
