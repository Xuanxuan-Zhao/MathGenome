import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleTotalization
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Cartan–Eilenberg injective double resolutions (HA-G00)

Source: notes/002/advanced-homological-algebra.tex, chapter 5 introduction
and "Simultaneous resolutions", especially lines 2337–2359. Both axes are
integer cochain degrees. Objects with negative vertical degree are zero.
The bicomplex uses commuting, unsigned differentials. This definition has
no relation to the Lie algebra Chevalley–Eilenberg complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace AdvancedHomologicalAlgebra.CartanEilenbergData

variable {C : Type u} [Category.{v} C] [Abelian C]

abbrev DoubleComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- Horizontal boundaries: the actual image of the incoming differential.
The map on images is induced by the commuting square of a cochain map. -/
noncomputable def boundariesFunctor (p : ℤ) : CochainComplex C ℤ ⥤ C where
  obj K := image (K.d (p - 1) p)
  map f := image.map (Arrow.homMk' _ _ (f.comm (p - 1) p))
  map_id K := by
    apply (cancel_mono (image.ι (K.d (p - 1) p))).1
    simp [image.map_homMk'_ι]
  map_comp f g := by
    exact image.map_comp (Arrow.homMk' _ _ (f.comm (p - 1) p))
      (Arrow.homMk' _ _ (g.comm (p - 1) p))


instance (p : ℤ) : (boundariesFunctor (C := C) p).PreservesZeroMorphisms where
  map_zero K L := by
    apply (cancel_mono (image.ι (L.d (p - 1) p))).1
    simp [boundariesFunctor, image.map_homMk'_ι]

/-- Apply a horizontal invariant functor row by row. Its differentials are
induced by the vertical chain maps, rather than independently chosen maps. -/
noncomputable def invariantColumn (I : DoubleComplex C)
    (F : CochainComplex C ℤ ⥤ C) [F.PreservesZeroMorphisms] : CochainComplex C ℤ :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.flip

/-- An augmented integer cochain complex is an injective resolution precisely
when it is zero below zero, is injective in nonnegative degrees, and the
augmented sequence 0 → A → J⁰ → J¹ → … is exact. These are conditions on the
specified augmentation, not on an independently chosen resolution of A. -/
structure IsInjectiveResolution (A : C) (J : CochainComplex C ℤ)
    (ι : A ⟶ J.X 0) : Prop where
  zero_neg : ∀ q : ℤ, q < 0 → IsZero (J.X q)
  injective : ∀ q : ℤ, 0 ≤ q → Injective (J.X q)
  mono : Mono ι
  augmentation_d : ι ≫ J.d 0 1 = 0
  exact_zero : (ShortComplex.mk ι (J.d 0 1) augmentation_d).Exact
  exact_pos : ∀ q : ℤ, 0 < q → J.ExactAt q

/-- Canonical data for a Cartan–Eilenberg resolution. A single augmentation
induces all four families of augmented columns. No existence or enough
injectives hypothesis is part of this definition. -/
structure ResolutionData (K : CochainComplex C ℤ) where
  bicomplex : DoubleComplex C
  boundedBelow : ∃ L : ℤ, ∀ p q : ℤ, p < L → IsZero ((bicomplex.X p).X q)
  nonnegative : ∀ p q : ℤ, q < 0 → IsZero ((bicomplex.X p).X q)
  augmentation : K ⟶ bicomplex.flip.X 0
  augmentation_d : ∀ p : ℤ, augmentation.f p ≫ (bicomplex.X p).d 0 1 = 0
  terms : ∀ p : ℤ, IsInjectiveResolution (K.X p) (bicomplex.X p) (augmentation.f p)
  boundaries : ∀ p : ℤ,
    IsInjectiveResolution ((boundariesFunctor p).obj K)
      (invariantColumn bicomplex (boundariesFunctor p))
      ((boundariesFunctor p).map augmentation)
  cycles : ∀ p : ℤ,
    IsInjectiveResolution (K.cycles p)
      (invariantColumn bicomplex (HomologicalComplex.cyclesFunctor C (ComplexShape.up ℤ) p))
      (HomologicalComplex.cyclesMap augmentation p)
  cohomology : ∀ p : ℤ,
    IsInjectiveResolution (K.homology p)
      (invariantColumn bicomplex (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p))
      (HomologicalComplex.homologyMap augmentation p)

namespace Specs

/-- The input complex is necessarily bounded below as well. -/
def SourceBoundedBelow : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (_R : ResolutionData K), ∃ L : ℤ, ∀ p : ℤ, p < L → IsZero (K.X p)

/-- The full category and universe parameters of the definition are retained. -/
def ExpectedResolutionType :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C], CochainComplex C ℤ → Type (max u v)

def resolutionValue : ExpectedResolutionType.{v, u} := fun K => ResolutionData K

/-- The sum totalization is the one already fixed by HA-B01. -/
def ExpectedTotalType :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K) [R.bicomplex.HasTotal (ComplexShape.up ℤ)], CochainComplex C ℤ

noncomputable def totalValue : ExpectedTotalType.{v, u} :=
  fun R => DoubleTotalization.sumTotal R.bicomplex

/-- On the summand I^(p,q), the total differential is d_h + (-1)^p d_v. -/
def TotalDifferential : Prop :=
  ∀ {C : Type u} [Category.{v} C] [Abelian C] {K : CochainComplex C ℤ}
    (R : ResolutionData K) [R.bicomplex.HasTotal (ComplexShape.up ℤ)] (p q : ℤ),
  R.bicomplex.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
      (totalValue R).d (p + q) (p + q + 1) =
    (R.bicomplex.d p (p + 1)).f q ≫
        R.bicomplex.ιTotal (ComplexShape.up ℤ) (p + 1) q (p + q + 1) (by change (p + 1) + q = p + q + 1; omega) +
    p.negOnePow • ((R.bicomplex.X p).d q (q + 1) ≫
        R.bicomplex.ιTotal (ComplexShape.up ℤ) p (q + 1) (p + q + 1) (by change p + (q + 1) = p + q + 1; omega))

end Specs
end AdvancedHomologicalAlgebra.CartanEilenbergData
