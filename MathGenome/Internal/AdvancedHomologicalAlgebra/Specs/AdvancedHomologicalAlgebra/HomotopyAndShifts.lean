import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
Independent specifications for HA-K01, notes/002/advanced-homological-algebra.tex,
lines 1214–1237; global cochain and sign conventions at lines 107–109.

All constructions below use the library quotient by cochain homotopy. An additive
category is covered by the weaker hypothesis `Preadditive`: no finite biproducts
are needed here. The additional cohomology conclusions assume `Abelian`.
Expected theorem types are definitions of propositions, never axioms.
-/

-- Universally quantified specification types combine the object and Hom universes.
set_option linter.checkUnivs false
universe v u
open CategoryTheory

namespace Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts

abbrev K (A : Type u) [Category.{v} A] [Preadditive A] :=
  HomotopyCategory A (ComplexShape.up ℤ)

abbrev Q (A : Type u) [Category.{v} A] [Preadditive A] :=
  HomotopyCategory.quotient A (ComplexShape.up ℤ)

abbrev S (A : Type u) [Category.{v} A] [Preadditive A] (m : ℤ) :=
  CategoryTheory.shiftFunctor (CochainComplex A ℤ) m

noncomputable abbrev T (A : Type u) [Category.{v} A] [Preadditive A] (m : ℤ) :=
  CategoryTheory.shiftFunctor (K A) m

noncomputable abbrev H (A : Type u) [Category.{v} A] [Abelian A] (n : ℤ) :=
  HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n

/-- The cochain homotopy category: the categorical quotient by existence of a cochain homotopy. -/
def homotopyCategoryType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], Type (max u v)

noncomputable def homotopyCategoryValue : homotopyCategoryType :=
  fun A _ _ => HomotopyCategory A (ComplexShape.up ℤ)

/-- The quotient functor sends a cochain map to its homotopy class. -/
def quotientType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], CochainComplex A ℤ ⥤ K A

noncomputable def quotientValue : quotientType :=
  fun A _ _ => HomotopyCategory.quotient A (ComplexShape.up ℤ)

/-- Two cochain maps have the same quotient class exactly when they are cochain homotopic. -/
def quotient_eq_iffType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ (X Y : CochainComplex A ℤ) (f g : X ⟶ Y),
  (Q A).map f = (Q A).map g ↔ Nonempty (Homotopy f g)

/-- Addition descends to homotopy classes. -/
def quotient_addType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ (X Y : CochainComplex A ℤ) (f g : X ⟶ Y),
  (Q A).map (f + g) = (Q A).map f + (Q A).map g

/-- The signed cochain shift functor, including its action on cochain maps. -/
def complexShiftType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ℤ → (CochainComplex A ℤ ⥤ CochainComplex A ℤ)

noncomputable def complexShiftValue : complexShiftType :=
  fun A _ _ m => CategoryTheory.shiftFunctor (CochainComplex A ℤ) m

/-- The shifted object in degree n is the original object in degree n + m. -/
def shift_objectType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ (X : CochainComplex A ℤ) (m n : ℤ),
  ((S A m).obj X).X n = X.X (n + m)

/-- The shifted differential is multiplied by (-1)^m. Int.negOnePow is (-1 : ℤˣ)^m, acting on each Hom group. -/
def shift_differentialType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ (X : CochainComplex A ℤ) (m i j : ℤ),
  ((S A m).obj X).d i j = m.negOnePow • X.d (i + m) (j + m)

/-- Shifting cochain maps reindexes their components without a sign. -/
def shift_mapType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y) (m n : ℤ),
  ((S A m).map f).f n = f.f (n + m)

/-- A homotopy shifts with the same (-1)^m sign as the differentials. -/
def shiftHomotopyType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ (X Y : CochainComplex A ℤ) (f g : X ⟶ Y),
  Homotopy f g → ∀ m : ℤ, Homotopy ((S A m).map f) ((S A m).map g)

noncomputable def shiftHomotopyValue : shiftHomotopyType :=
  fun _A _ _ _X _Y _f _g h m => h.shift m

/-- In particular the degree -1 homotopy component is (-1)^m times the original reindexed component. -/
def shift_homotopy_componentType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ (X Y : CochainComplex A ℤ) (f g : X ⟶ Y)
  (h : Homotopy f g) (m i j : ℤ),
  (h.shift m).hom i j = m.negOnePow • h.hom (i + m) (j + m)

/-- The shift functor on the homotopy category. -/
def homotopyShiftType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ℤ → (K A ⥤ K A)

noncomputable def homotopyShiftValue : homotopyShiftType :=
  fun A _ _ m => CategoryTheory.shiftFunctor (K A) m

/-- The quotient functor commutes naturally with shifts; hence the signed shifts descend. -/
def shiftDescendsType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ m : ℤ,
  S A m ⋙ Q A ≅ Q A ⋙ T A m

noncomputable def shiftDescendsValue : shiftDescendsType :=
  fun A _ _ m => (Q A).commShiftIso m

/-- The zero shift on cochain complexes is naturally the identity. -/
def complexShiftZeroType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], S A 0 ≅ 𝟭 (CochainComplex A ℤ)

noncomputable def complexShiftZeroValue : complexShiftZeroType :=
  fun A _ _ => CategoryTheory.shiftFunctorZero (CochainComplex A ℤ) ℤ

/-- Shifts of cochain complexes compose by addition, naturally in the complex. -/
def complexShiftAddType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ m l : ℤ,
  S A (m + l) ≅ S A m ⋙ S A l

noncomputable def complexShiftAddValue : complexShiftAddType :=
  fun A _ _ m l => CategoryTheory.shiftFunctorAdd (CochainComplex A ℤ) m l

/-- The zero shift on the homotopy category is naturally the identity. -/
def homotopyShiftZeroType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], T A 0 ≅ 𝟭 (K A)

noncomputable def homotopyShiftZeroValue : homotopyShiftZeroType :=
  fun A _ _ => CategoryTheory.shiftFunctorZero (K A) ℤ

/-- Shifts on the homotopy category compose by addition. -/
def homotopyShiftAddType :=
  ∀ (A : Type u) [Category.{v} A] [Preadditive A], ∀ m l : ℤ,
  T A (m + l) ≅ T A m ⋙ T A l

noncomputable def homotopyShiftAddValue : homotopyShiftAddType :=
  fun A _ _ m l => CategoryTheory.shiftFunctorAdd (K A) m l

/-- Cohomology in cochain degree n, as a functor on the homotopy category. -/
def cohomologyType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], ℤ → (K A ⥤ A)

noncomputable def cohomologyValue : cohomologyType :=
  fun A _ _ n => HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n

/-- The ordinary cohomology functor factors naturally through the homotopy quotient. -/
def cohomologyFactorsType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], ∀ n : ℤ,
  Q A ⋙ H A n ≅ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n

noncomputable def cohomologyFactorsValue : cohomologyFactorsType :=
  fun A _ _ n => HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n

/-- Homotopic maps induce equal cohomology maps in every degree. -/
def homotopic_cohomology_mapType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], ∀ (X Y : CochainComplex A ℤ) (f g : X ⟶ Y)
  (_h : Homotopy f g) (n : ℤ),
  HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n

/-- The natural cohomology identification H^n(X[m]) ≅ H^(n+m)(X). -/
def cohomologyShiftComplexType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], ∀ m n : ℤ,
  S A m ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n ≅
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (n + m)

noncomputable def cohomologyShiftComplexValue : cohomologyShiftComplexType :=
  fun A _ _ m n => CochainComplex.ShiftSequence.shiftIso A m n (n + m) (add_comm m n)

/-- The same cohomology identification is natural on the homotopy category. -/
def cohomologyShiftHomotopyType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], ∀ m n : ℤ,
  T A m ⋙ H A n ≅ H A (n + m)

noncomputable def cohomologyShiftHomotopyValue : cohomologyShiftHomotopyType :=
  fun A _ _ m n =>
  (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso
    m n (n + m) (add_comm m n)

/-- The cohomology shift comparison commutes with every cochain map. -/
def cohomology_shift_naturalityType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A], ∀ (X Y : CochainComplex A ℤ) (f : X ⟶ Y) (m n : ℤ),
  HomologicalComplex.homologyMap ((S A m).map f) n ≫
      (CochainComplex.ShiftSequence.shiftIso A m n (n + m) (add_comm m n)).hom.app Y =
    (CochainComplex.ShiftSequence.shiftIso A m n (n + m) (add_comm m n)).hom.app X ≫
      HomologicalComplex.homologyMap f (n + m)

end Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
