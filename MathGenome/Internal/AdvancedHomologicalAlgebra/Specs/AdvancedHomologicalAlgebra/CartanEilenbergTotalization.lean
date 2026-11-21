import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! HA-G02, notes/002/advanced-homological-algebra.tex:2499–2570.
The totalization is the signed diagonal sum, with finite nonzero support.
No infinite coproduct preservation or exactness is imposed on the additive functor.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u v' u'
universe w w'
namespace AdvancedHomologicalAlgebra.CartanEilenbergTotalization
open CartanEilenbergData DoubleTotalization FiniteDiagonalFiltrations

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Apply the functor to the objects and both commuting differentials. -/
abbrev mapDouble (U : C ⥤ D) [U.Additive] : DoubleComplex C ⥤ DoubleComplex D :=
  (U.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The summand identity uniquely specifies the canonical comparison. -/
def SummandFormula (U : C ⥤ D) [U.Additive] (I : DoubleComplex C)
    [I.HasTotal (ComplexShape.up ℤ)]
    [((mapDouble U).obj I).HasTotal (ComplexShape.up ℤ)]
    (e : (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal I) ≅
      sumTotal ((mapDouble U).obj I)) : Prop :=
  ∀ p q n (h : p + q = n),
    U.map (sumInjection I p q n h) ≫ e.hom.f n =
      sumInjection ((mapDouble U).obj I) p q n h

/-- Every split filtration step is carried to the corresponding split diagonal
step. The mapped bicone is a bilimit, and its inclusion is still monic and
has precisely the prescribed summand legs. Taking the first and second axes
recovers both decreasing filtrations, including empty diagonal steps. -/
def SplitFiltrationFormula (U : C ⥤ D) [U.Additive] (I : DoubleComplex C)
    [I.HasTotal (ComplexShape.up ℤ)]
    [((mapDouble U).obj I).HasTotal (ComplexShape.up ℤ)]
    (e : (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal I) ≅
      sumTotal ((mapDouble U).obj I)) : Prop :=
  ∀ (axis : ℤ × ℤ → ℤ), axis = Prod.fst ∨ axis = Prod.snd → ∀ a n : ℤ,
    ∀ (b : Bicone (fun i : {i : Diagonal n // a ≤ axis i.val} =>
        diagonalFamily I n i.val)), b.IsBilimit →
    ∀ (j : b.pt ⟶ (sumTotal I).X n), Mono j →
    (∀ i, b.ι i ≫ j = sumInjection I i.val.val.1 i.val.val.2 n i.val.property) →
    Nonempty (U.mapBicone b).IsBilimit ∧
      Mono (U.map j ≫ e.hom.f n) ∧
      ∀ i, U.map (b.ι i) ≫ U.map j ≫ e.hom.f n =
        sumInjection ((mapDouble U).obj I) i.val.val.1 i.val.val.2 n i.val.property

section Derived
variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C]

/-- The termwise derived computation determined by the given replacement.
The comparison on the injective model is the actual right-derived unit. -/
structure ReplacementComparison (U : C ⥤ D) [U.Additive]
    (K I : CochainComplex.Plus C) (a : K ⟶ I) where
  quasiIso : QuasiIso a.hom
  injective : ∀ n, Injective (I.obj.X n)
  iso : U.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
    DerivedCategory.Plus.Q.obj (U.mapCochainComplexPlus.obj I)
  unit_eq :
    iso.hom ≫ U.rightDerivedFunctorPlusUnit.app I =
      U.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map a)

def ReplacementComparison.homologyIso {U : C ⥤ D} [U.Additive]
    {K I : CochainComplex.Plus C} {a : K ⟶ I}
    (M : ReplacementComparison U K I a) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
      (U.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      ((U.mapCochainComplexPlus.obj I).obj).homology n :=
  (DerivedCategory.Plus.homologyFunctor D n).mapIso M.iso ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app (U.mapCochainComplexPlus.obj I).obj

/-- The same augmented total replacement and signed biproduct isomorphism
determine both filtered targets, for every Cartan–Eilenberg resolution. -/
structure DerivedTotalComparison (U : C ⥤ D) [U.Additive] (K : CochainComplex.Plus C)
    (R : ResolutionData K.obj) [R.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble U).obj R.bicomplex).HasTotal (.up ℤ)] where
  totalBound : (CochainComplex.plus C) (sumTotal R.bicomplex)
  augmentation : K ⟶ (⟨sumTotal R.bicomplex, totalBound⟩ : CochainComplex.Plus C)
  augmentation_eq : ∀ n, augmentation.hom.f n =
    R.augmentation.f n ≫ sumInjection R.bicomplex n 0 n (add_zero n)
  model : ReplacementComparison U _ _ augmentation
  additivity : (U.mapHomologicalComplex (.up ℤ)).obj (sumTotal R.bicomplex) ≅
    sumTotal ((mapDouble U).obj R.bicomplex)
  summands : SummandFormula U R.bicomplex additivity

def DerivedTotalComparison.homologyIso {U : C ⥤ D} [U.Additive]
    {K : CochainComplex.Plus C} {R : ResolutionData K.obj} [R.bicomplex.HasTotal (.up ℤ)]
    [((mapDouble U).obj R.bicomplex).HasTotal (.up ℤ)]
    (M : DerivedTotalComparison U K R) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
      (U.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      (sumTotal ((mapDouble U).obj R.bicomplex)).homology n :=
  M.model.homologyIso n ≪≫ (HomologicalComplex.homologyFunctor D (.up ℤ) n).mapIso M.additivity

end Derived

namespace Specs

def FiniteSupport : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K), FiniteDiagonals R.bicomplex ∧
      R.bicomplex.HasTotal (ComplexShape.up ℤ)

def Augmentation : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K) [R.bicomplex.HasTotal (ComplexShape.up ℤ)],
    ∃ f : K ⟶ sumTotal R.bicomplex, QuasiIso f ∧
      ∀ n, f.f n = R.augmentation.f n ≫ sumInjection R.bicomplex n 0 n (add_zero n)

def BoundedInjective : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K) [R.bicomplex.HasTotal (ComplexShape.up ℤ)],
    (∃ L : ℤ, ∀ n : ℤ, n < L → IsZero ((sumTotal R.bicomplex).X n)) ∧
      ∀ n, Injective ((sumTotal R.bicomplex).X n)

/-- Comparison for the actual total augmentations, rather than only their
component expressions. Existence and uniqueness up to homotopy are supplied
by HA-G02-Comparison. -/
def AugmentationComparison : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K L : CochainComplex C ℤ}
    (R : ResolutionData K) (S : ResolutionData L)
    [R.bicomplex.HasTotal (ComplexShape.up ℤ)] [S.bicomplex.HasTotal (ComplexShape.up ℤ)]
    (f : K ⟶ L) (a : R.bicomplex ⟶ S.bicomplex),
    CartanEilenbergComparison.IsLift R S f a →
    ∀ (r : K ⟶ sumTotal R.bicomplex) (s : L ⟶ sumTotal S.bicomplex),
    (∀ n, r.f n = R.augmentation.f n ≫ sumInjection R.bicomplex n 0 n (add_zero n)) →
    (∀ n, s.f n = S.augmentation.f n ≫ sumInjection S.bicomplex n 0 n (add_zero n)) →
    r ≫ HomologicalComplex₂.total.map a (ComplexShape.up ℤ) = f ≫ s

def AdditiveSupport : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (U : C ⥤ D) [U.Additive] {K : CochainComplex C ℤ} (R : ResolutionData K),
    FiniteDiagonals ((mapDouble U).obj R.bicomplex) ∧
      ((mapDouble U).obj R.bicomplex).HasTotal (ComplexShape.up ℤ)

def AdditiveComparison : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (U : C ⥤ D) [U.Additive] {K : CochainComplex C ℤ} (R : ResolutionData K)
    [R.bicomplex.HasTotal (ComplexShape.up ℤ)]
    [((mapDouble U).obj R.bicomplex).HasTotal (ComplexShape.up ℤ)],
    ∃ e : (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal R.bicomplex) ≅
      sumTotal ((mapDouble U).obj R.bicomplex),
      SummandFormula U R.bicomplex e ∧ SplitFiltrationFormula U R.bicomplex e

def AdditiveNaturality : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (U : C ⥤ D) [U.Additive] {K L : CochainComplex C ℤ}
    (R : ResolutionData K) (S : ResolutionData L)
    [R.bicomplex.HasTotal (ComplexShape.up ℤ)] [S.bicomplex.HasTotal (ComplexShape.up ℤ)]
    [((mapDouble U).obj R.bicomplex).HasTotal (ComplexShape.up ℤ)]
    [((mapDouble U).obj S.bicomplex).HasTotal (ComplexShape.up ℤ)]
    (e : (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal R.bicomplex) ≅
      sumTotal ((mapDouble U).obj R.bicomplex))
    (e' : (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj (sumTotal S.bicomplex) ≅
      sumTotal ((mapDouble U).obj S.bicomplex)),
    SummandFormula U R.bicomplex e → SummandFormula U S.bicomplex e' →
    ∀ a : R.bicomplex ⟶ S.bicomplex,
      (U.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex₂.total.map a (ComplexShape.up ℤ)) ≫ e'.hom =
        e.hom ≫ HomologicalComplex₂.total.map ((mapDouble U).map a) (ComplexShape.up ℤ)

end Specs
end AdvancedHomologicalAlgebra.CartanEilenbergTotalization
