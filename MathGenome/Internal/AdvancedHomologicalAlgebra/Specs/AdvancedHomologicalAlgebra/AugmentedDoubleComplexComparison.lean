import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import Mathlib.Algebra.Homology.SingleHomology

/-! HA-B04 assembly, source lines 899–909, 931–956.
The cochain augmentations go INTO totalization. The chain augmentations go
FROM totalization. Degree-zero hypotheses concern the actual maps on homology
of the single-object column maps, using the canonical H₀(single X) ≅ X.
All complexes are integer indexed; the chain hypotheses are first-quadrant.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
open DoubleTotalization FiniteDiagonalFiltrations

namespace Specs

def CochainColumn : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : Bicomplex A), FiniteDiagonals K →
  (∀ p q : ℤ, q < 0 → IsZero ((K.X p).X q)) →
  ∀ [K.HasTotal (ComplexShape.up ℤ)] (L : CochainComplex A ℤ)
  (a : L ⟶ K.flip.X 0)
  (z : ∀ p q, (ComplexShape.up ℤ).Rel 0 q → a.f p ≫ (K.X p).d 0 q = 0),
  (∀ p, IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex.mkHomFromSingle (K := K.X p) (j := 0) (a.f p) (z p)) 0)) →
  (∀ p q : ℤ, q ≠ 0 → IsZero ((K.X p).homology q)) →
  ∃ f : L ⟶ sumTotal K, QuasiIso f ∧
    ∀ n, f.f n = a.f n ≫ sumInjection K n 0 n (add_zero n)

def CochainRow : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : Bicomplex A), FiniteDiagonals K →
  (∀ p q : ℤ, p < 0 → IsZero ((K.X p).X q)) →
  ∀ [K.HasTotal (ComplexShape.up ℤ)] (L : CochainComplex A ℤ)
  (a : L ⟶ K.X 0)
  (z : ∀ q p, (ComplexShape.up ℤ).Rel 0 p → a.f q ≫ (K.d 0 p).f q = 0),
  (∀ q, IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex.mkHomFromSingle (K := K.flip.X q) (j := 0) (a.f q) (z q)) 0)) →
  (∀ q p : ℤ, p ≠ 0 → IsZero ((K.flip.X q).homology p)) →
  ∃ f : L ⟶ sumTotal K, QuasiIso f ∧
    ∀ n, f.f n = a.f n ≫ sumInjection K 0 n n (zero_add n)

def ChainColumn : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)),
  (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) →
  ∀ [K.HasTotal (ComplexShape.down ℤ)] (L : ChainComplex A ℤ)
  (a : K.flip.X 0 ⟶ L)
  (z : ∀ p q, (ComplexShape.down ℤ).Rel q 0 → (K.X p).d q 0 ≫ a.f p = 0),
  (∀ p, IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex.mkHomToSingle (K := K.X p) (j := 0) (a.f p) (z p)) 0)) →
  (∀ p q : ℤ, 0 < q → IsZero ((K.X p).homology q)) →
  ∃ f : sumTotal K ⟶ L, QuasiIso f ∧
    ∀ p q n (h : p + q = n),
      sumInjection K p q n h ≫ f.f n =
        if hq : q = 0 then
          (HomologicalComplex.XIsoOfEq (K.X p) hq).hom ≫ a.f p ≫ (L.XIsoOfEq (by omega : p = n)).hom
        else 0

def ChainRow : Prop := ∀ {A : Type u} [Category.{v} A] [Abelian A]
  (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)),
  (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) →
  ∀ [K.HasTotal (ComplexShape.down ℤ)] (L : ChainComplex A ℤ)
  (a : K.X 0 ⟶ L)
  (z : ∀ q p, (ComplexShape.down ℤ).Rel p 0 → (K.d p 0).f q ≫ a.f q = 0),
  (∀ q, IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex.mkHomToSingle (K := K.flip.X q) (j := 0) (a.f q) (z q)) 0)) →
  (∀ q p : ℤ, 0 < p → IsZero ((K.flip.X q).homology p)) →
  ∃ f : sumTotal K ⟶ L, QuasiIso f ∧
    ∀ p q n (h : p + q = n),
      sumInjection K p q n h ≫ f.f n =
        if hp : p = 0 then
          (HomologicalComplex.XIsoOfEq (K.flip.X q) hp).hom ≫ a.f q ≫ (L.XIsoOfEq (by omega : q = n)).hom
        else 0

end Specs
end AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
