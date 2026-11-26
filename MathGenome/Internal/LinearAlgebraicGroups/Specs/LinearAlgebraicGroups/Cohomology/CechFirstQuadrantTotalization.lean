import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u v' u'

namespace LinearAlgebraicGroups.CechFirstQuadrantTotalization

abbrev CohomologicalBicomplex (A : Type u) [Category.{v} A] [Preadditive A] :=
  HomologicalComplex₂ A (.up ℤ) (.up ℤ)

namespace Specs

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type u'} [Category.{v'} B] [Preadditive B]

/-- Both coordinates of a possibly nonzero term are nonnegative. -/
def FirstQuadrant (K : CohomologicalBicomplex A) : Prop :=
  ∀ p q : ℤ, (p < 0 ∨ q < 0) → IsZero ((K.X p).X q)

def RowClosed (K : CohomologicalBicomplex A) {G : CochainComplex A ℤ}
    (a₀ : G ⟶ K.X 0) : Prop :=
  ∀ q p : ℤ, (ComplexShape.up ℤ).Rel 0 p → a₀.f q ≫ (K.d 0 p).f q = 0

def ColumnClosed (K : CohomologicalBicomplex A) {C : CochainComplex A ℤ}
    (b₀ : C ⟶ K.flip.X 0) : Prop :=
  ∀ p q : ℤ, (ComplexShape.up ℤ).Rel 0 q → b₀.f p ≫ (K.X p).d 0 q = 0

def RowComponents (K : CohomologicalBicomplex A) [K.HasTotal (.up ℤ)]
    {G : CochainComplex A ℤ} (a₀ : G ⟶ K.X 0) (a : G ⟶ K.total (.up ℤ)) : Prop :=
  ∀ n : ℤ, a.f n = a₀.f n ≫ K.ιTotal (.up ℤ) 0 n n (zero_add n)

def ColumnComponents (K : CohomologicalBicomplex A) [K.HasTotal (.up ℤ)]
    {C : CochainComplex A ℤ} (b₀ : C ⟶ K.flip.X 0) (b : C ⟶ K.total (.up ℤ)) : Prop :=
  ∀ n : ℤ, b.f n = b₀.f n ≫ K.ιTotal (.up ℤ) n 0 n (add_zero n)

/-- Horizontal quasi-isomorphisms from single objects give a quasi-isomorphism
from the vertical axis into the sum totalization. -/
def RowAssembly : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A]
    (K : CohomologicalBicomplex A) [K.HasTotal (.up ℤ)], FirstQuadrant K →
    ∀ (G : CochainComplex A ℤ) (a₀ : G ⟶ K.X 0) (z : RowClosed K a₀),
      (∀ q : ℤ, QuasiIso
        (mkHomFromSingle (K := K.flip.X q) (j := 0) (a₀.f q) (z q))) →
      ∃ a : G ⟶ K.total (.up ℤ), QuasiIso a ∧ RowComponents K a₀ a

/-- Vertical quasi-isomorphisms from single objects give a quasi-isomorphism
from the horizontal axis into the sum totalization. -/
def ColumnAssembly : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A]
    (K : CohomologicalBicomplex A) [K.HasTotal (.up ℤ)], FirstQuadrant K →
    ∀ (C : CochainComplex A ℤ) (b₀ : C ⟶ K.flip.X 0) (z : ColumnClosed K b₀),
      (∀ p : ℤ, QuasiIso
        (mkHomFromSingle (K := K.X p) (j := 0) (b₀.f p) (z p))) →
      ∃ b : C ⟶ K.total (.up ℤ), QuasiIso b ∧ ColumnComponents K b₀ b

/-- Apply an additive functor to the two directions of the bicomplex. -/
abbrev mapBicomplex (R : B ⥤ A) [R.Additive] :
    CohomologicalBicomplex B ⥤ CohomologicalBicomplex A :=
  (R.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)

variable (R : B ⥤ A) [R.Additive]
  (K : CohomologicalBicomplex A) (L : CohomologicalBicomplex B)
  [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]
  (φ : K ⟶ (mapBicomplex R).obj L)

def TotalMapComponents
    (t : K.total (.up ℤ) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (L.total (.up ℤ))) : Prop :=
  ∀ (p q n : ℤ) (h : p + q = n),
    K.ιTotal (.up ℤ) p q n h ≫ t.f n =
      (φ.f p).f q ≫ R.map (L.ιTotal (.up ℤ) p q n h)

/-- Descend from the source coproduct with the given map on each summand. -/
def TotalMap : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Preadditive A]
    {B : Type u'} [Category.{v'} B] [Preadditive B] (R : B ⥤ A) [R.Additive]
    (K : CohomologicalBicomplex A) (L : CohomologicalBicomplex B)
    [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)] (φ : K ⟶ (mapBicomplex R).obj L),
    ∃! t : K.total (.up ℤ) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (L.total (.up ℤ)),
      TotalMapComponents R K L φ t

def RowNaturality : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Preadditive A]
    {B : Type u'} [Category.{v'} B] [Preadditive B] (R : B ⥤ A) [R.Additive]
    (K : CohomologicalBicomplex A) (L : CohomologicalBicomplex B)
    [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)] (φ : K ⟶ (mapBicomplex R).obj L)
    {G : CochainComplex A ℤ} {G' : CochainComplex B ℤ}
    (g : G ⟶ (R.mapHomologicalComplex (.up ℤ)).obj G')
    (a₀ : G ⟶ K.X 0) (a₀' : G' ⟶ L.X 0)
    (a : G ⟶ K.total (.up ℤ)) (a' : G' ⟶ L.total (.up ℤ))
    (t : K.total (.up ℤ) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (L.total (.up ℤ))),
    RowComponents K a₀ a → RowComponents L a₀' a' → TotalMapComponents R K L φ t →
    a₀ ≫ φ.f 0 = g ≫ (R.mapHomologicalComplex (.up ℤ)).map a₀' →
    a ≫ t = g ≫ (R.mapHomologicalComplex (.up ℤ)).map a'

def ColumnNaturality : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Preadditive A]
    {B : Type u'} [Category.{v'} B] [Preadditive B] (R : B ⥤ A) [R.Additive]
    (K : CohomologicalBicomplex A) (L : CohomologicalBicomplex B)
    [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)] (φ : K ⟶ (mapBicomplex R).obj L)
    {C : CochainComplex A ℤ} {C' : CochainComplex B ℤ}
    (g : C ⟶ (R.mapHomologicalComplex (.up ℤ)).obj C')
    (b₀ : C ⟶ K.flip.X 0) (b₀' : C' ⟶ L.flip.X 0)
    (b : C ⟶ K.total (.up ℤ)) (b' : C' ⟶ L.total (.up ℤ))
    (t : K.total (.up ℤ) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (L.total (.up ℤ))),
    ColumnComponents K b₀ b → ColumnComponents L b₀' b' → TotalMapComponents R K L φ t →
    b₀ ≫ ((HomologicalComplex₂.flipFunctor A (.up ℤ) (.up ℤ)).map φ).f 0 =
      g ≫ (R.mapHomologicalComplex (.up ℤ)).map b₀' →
    b ≫ t = g ≫ (R.mapHomologicalComplex (.up ℤ)).map b'

end Specs
end LinearAlgebraicGroups.CechFirstQuadrantTotalization
