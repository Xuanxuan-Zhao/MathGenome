import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Shrink
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-! The Ext colimit over the positive powers of an ideal and its normalization
on injective resolutions. -/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Specs.CommutativeAlgebraNotes.DerivedTorsionExtComparison

universe v u

variable {R : Type u} [CommRing R] [Small.{v} R]

noncomputable section

set_option linter.checkUnivs false

/-- A copy of `R / I^(n+1)` in the module universe of the injective resolutions. -/
abbrev powerQuotient (I : Ideal R) (n : ℕ) : ModuleCat.{v} R :=
  ModuleCat.of R (Shrink.{v} (R ⧸ I ^ (n + 1)))

abbrev quotientLinearEquiv (I : Ideal R) (n : ℕ) :
    powerQuotient.{v} I n ≃ₗ[R] R ⧸ I ^ (n + 1) :=
  Shrink.linearEquiv R _

def quotientOne (I : Ideal R) (n : ℕ) : powerQuotient.{v} I n :=
  (quotientLinearEquiv I n).symm 1

/-- The canonical quotient map from the larger power to the smaller power. -/
def powerQuotientMap (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    powerQuotient.{v} I n ⟶ powerQuotient.{v} I m :=
  ModuleCat.ofHom ((quotientLinearEquiv I m).symm.toLinearMap.comp
    ((Submodule.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h) :
      I ^ (n + 1) ≤ I ^ (m + 1))).comp (quotientLinearEquiv I n).toLinearMap))

/-- The inverse system of quotient modules, viewed in the opposite category. -/
abbrev powerQuotientDiagram (I : Ideal R) : ℕ ⥤ (ModuleCat.{v} R)ᵒᵖ where
  obj n := Opposite.op (powerQuotient I n)
  map f := (powerQuotientMap I (leOfHom f)).op
  map_id n := by
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (powerQuotientMap I (le_refl n)) x = x
    apply (quotientLinearEquiv I n).injective
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (I ^ (n + 1) : Ideal R)
      (quotientLinearEquiv I n x)
    simp [powerQuotientMap, ← hr]
  map_comp {m n k} f g := by
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change powerQuotientMap I ((leOfHom f).trans (leOfHom g)) x =
      powerQuotientMap I (leOfHom f) (powerQuotientMap I (leOfHom g) x)
    apply (quotientLinearEquiv I m).injective
    simp [powerQuotientMap]

/-- The directed system of Ext functors, with transition maps given by pullback. -/
abbrev extPowerDiagram (I : Ideal R) (q : ℕ) : ℕ ⥤ ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  powerQuotientDiagram I ⋙ linearExtFunctor R (ModuleCat.{v} R) q

/-- The colimit of the directed system, as an R-linear comparison target in every module. -/
def extPowerColimit (I : Ideal R) (q : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  colimit (extPowerDiagram I q)

abbrev extStage (I : Ideal R) (q : ℕ) (M : ModuleCat.{v} R) (n : ℕ) :=
  ((extPowerDiagram I q).flip.obj M).obj n

/-- The map from the n-th Ext functor to the colimit. -/
def extPowerι (I : Ideal R) (q n : ℕ) :
    (extPowerDiagram.{v} I q).obj n ⟶ extPowerColimit I q :=
  colimit.ι _ n

/-- Degree-zero evaluation at the residue class of 1. -/
def extZeroEvaluation (I : Ideal R) (n : ℕ) (M : ModuleCat.{v} R) :
    extStage I 0 M n ⟶ M :=
  ModuleCat.ofHom
    { toFun := fun x => (Ext.linearEquiv₀ (R := R) x) (quotientOne I n)
      map_add' := by intro x y; rw [map_add]; rfl
      map_smul' := by intro r x; rw [map_smul]; rfl }

abbrev torsionComplex (I : Ideal R) {M : ModuleCat.{v} R} (Q : InjectiveResolution M) :=
  ((IdealTorsion.idealTorsionFunctor I).mapHomologicalComplex (.up ℕ)).obj Q.cocomplex

/-- The cohomology class of an element of a module complex killed by the next differential. -/
def cycleClass (K : CochainComplex (ModuleCat.{v} R) ℕ) (q : ℕ)
    (x : K.X q) (hx : K.d q (q + 1) x = 0) : K.homology q :=
  K.homologyπ q ((K.sc q).moduleCatCyclesIso.inv ⟨x, by
    change K.d q ((ComplexShape.up ℕ).next q) x = 0
    rwa [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)]⟩)

def extPowerComparisonType :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (q : ℕ),
    (IdealTorsion.idealTorsionFunctor.{v} I).rightDerived q ≅ extPowerColimit I q

/-- The isomorphism sends the evaluated cocycle to the corresponding Ext class,
with the normalization of Mathlib's injective `extMk`. -/
def extPowerComparisonOnCocycles (α : extPowerComparisonType.{v,u}) : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (q n : ℕ)
    {M : ModuleCat.{v} R} (Q : InjectiveResolution M)
    (f : powerQuotient I n ⟶ Q.cocomplex.X q) (hf : f ≫ Q.cocomplex.d q (q + 1) = 0)
    (x : (torsionComplex I Q).X q) (hx : (torsionComplex I Q).d q (q + 1) x = 0),
    x.val = f (quotientOne I n) →
      (α I q).inv.app M ((extPowerι I q n).app M (Q.extMk f (q + 1) rfl hf)) =
        (Q.isoRightDerivedObj (IdealTorsion.idealTorsionFunctor I) q).inv
          (cycleClass (torsionComplex I Q) q x hx)

/-- The edge map to the original module, normalized on every degree-zero Ext stage. -/
def extPowerZeroEdge (α : extPowerComparisonType.{v,u}) : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R),
    ∃ β : extPowerColimit.{v} I 0 ≅ IdealTorsion.idealTorsionFunctor I,
      β.hom ≫ (IdealTorsion.idealTorsionFunctor I).toRightDerivedZero = (α I 0).inv ∧
      ∀ n (M : ModuleCat.{v} R),
        (extPowerι I 0 n).app M ≫ β.hom.app M ≫ (IdealTorsion.idealTorsionInclusion I).app M =
          extZeroEvaluation I n M

/-- Existence of a natural comparison with its cochain and edge normalizations. -/
def extPowerComparison : Prop :=
  ∃ α : extPowerComparisonType.{v,u},
    extPowerComparisonOnCocycles α ∧ extPowerZeroEdge α

end

end Specs.CommutativeAlgebraNotes.DerivedTorsionExtComparison
