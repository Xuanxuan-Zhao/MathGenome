import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FilteredComplexes
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Int.Interval

/-! HA-B02, notes/002/advanced-homological-algebra.tex:772–810.
The support condition uses categorical zero objects and does not require
countable products or coproducts in the ambient abelian category. -/
noncomputable section
open scoped Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations

abbrev Bicomplex (A : Type u) [Category.{v} A] [Preadditive A] :=
  HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ)

abbrev Diagonal (n : ℤ) := {i : ℤ × ℤ // i.1 + i.2 = n}

variable {A : Type u} [Category.{v} A] [Abelian A]

abbrev diagonalFamily (K : Bicomplex A) (n : ℤ) : Diagonal n → A :=
  fun i => (K.X i.val.1).X i.val.2

/-- Exactly the finite-diagonal hypothesis, with the empty support allowed. -/
def FiniteDiagonals (K : Bicomplex A) : Prop :=
  ∀ n : ℤ, {i : Diagonal n | ¬ IsZero (diagonalFamily K n i)}.Finite

/-- A translated first quadrant, with unrestricted integer lower bounds. -/
def InQuadrant (K : Bicomplex A) (p₀ q₀ : ℤ) : Prop :=
  ∀ p q : ℤ, ¬ (p₀ ≤ p ∧ q₀ ≤ q) → IsZero ((K.X p).X q)

open DoubleTotalization

/-- A filtration step is the indicated sub-biproduct: its injection identifies
its underlying subobject and agrees with every diagonal summand injection. -/
def HasFiltrationFormula (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
    (axis : ℤ × ℤ → ℤ) (F : Filtration (sumTotal K)) : Prop :=
  ∀ a n : ℤ,
    ∃ (b : Bicone (fun i : {i : Diagonal n // a ≤ axis i.val} =>
        diagonalFamily K n i.val))
      (_hb : b.IsBilimit) (ι : b.pt ⟶ (sumTotal K).X n) (_hi : Mono ι),
      Subobject.mk ι = F.piece a n ∧
      ∀ i, b.ι i ≫ ι = sumInjection K i.val.val.1 i.val.val.2 n i.val.property

/-- Bounds are allowed to depend on the degree. No nonzero-diagonal assumption
is imposed. -/
def DegreewiseFinite {K : CochainComplex A ℤ} (F : Filtration K) : Prop :=
  ∀ n : ℤ, ∃ l u : ℤ, ∀ a : ℤ,
    (a ≤ l → F.piece a n = ⊤) ∧ (u ≤ a → F.piece a n = ⊥)

namespace Specs

def DiagonalBiproducts : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A] (K : Bicomplex A),
    FiniteDiagonals K → ∀ n, HasBiproduct (diagonalFamily K n)

def QuadrantFinite : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A] (K : Bicomplex A) (p₀ q₀ : ℤ),
    InQuadrant K p₀ q₀ → FiniteDiagonals K

def TotalizationsExist : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A] (K : Bicomplex A),
    FiniteDiagonals K → K.HasTotal (ComplexShape.up ℤ) ∧ HasProductTotal K

/-- The identity/zero matrix characterizes the canonical comparison. -/
def Comparison : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A] (K : Bicomplex A),
    FiniteDiagonals K → ∀ [K.HasTotal (ComplexShape.up ℤ)] [HasProductTotal K],
    ∃ e : sumTotal K ≅ productTotal K,
      ∀ n (i j : Diagonal n),
        sumInjection K i.val.1 i.val.2 n i.property ≫ e.hom.f n ≫
          productProjection K j.val.1 j.val.2 n j.property =
        if h : i = j then eqToHom (congrArg (diagonalFamily K n) h) else 0

def Filtrations : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A] (K : Bicomplex A),
    FiniteDiagonals K → ∀ [K.HasTotal (ComplexShape.up ℤ)],
    ∃ Fc Fr : Filtration (sumTotal K),
      HasFiltrationFormula K Prod.fst Fc ∧ HasFiltrationFormula K Prod.snd Fr ∧
      DegreewiseFinite Fc ∧ DegreewiseFinite Fr

/-- Naturality for any realizations of the two prescribed subobject filtrations.
It gives actual filtered cochain maps, not merely a relation between supports. -/
def Naturality : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A] (K L : Bicomplex A)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (Fc Fr : Filtration (sumTotal K)) (Gc Gr : Filtration (sumTotal L)),
    HasFiltrationFormula K Prod.fst Fc → HasFiltrationFormula K Prod.snd Fr →
    HasFiltrationFormula L Prod.fst Gc → HasFiltrationFormula L Prod.snd Gr →
    ∀ f : K ⟶ L,
      (∃ g : FilteredMap ⟨sumTotal K, Fc⟩ ⟨sumTotal L, Gc⟩,
        g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) ∧
      (∃ g : FilteredMap ⟨sumTotal K, Fr⟩ ⟨sumTotal L, Gr⟩,
        g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ))

end Specs
end AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations
