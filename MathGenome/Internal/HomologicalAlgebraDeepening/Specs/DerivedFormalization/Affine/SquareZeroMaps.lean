import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.RelativePathComparison

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.SquareZeroMaps

open _root_.DerivedFormalization
open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Kahler (IsDerivation)
open CochainComplex.HomComplex (Cochain)
open Tensor (ModuleTensor act regular term)
open DG.Basic (cyclesZero)
open DG.HomComplex (component homComplex)
open PolynomialPath (ModulePathModel)
open RelativePathComparison (baseChangedSymbol)
open CotangentComplex (Model)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}

/-- The square-zero product, with the left action written using the right action. -/
structure Extension (M : B.Module) where
  algebra : CommDGAlgebra.{u,v} k
  coord : ∀ i, algebra.complex.X i ≃ₗ[k] (B.complex.X i × term M i)
  projection : algebra ⟶ B.toCommDGAlgebra
  zeroSection : B.toCommDGAlgebra ⟶ algebra
  section_projection : zeroSection ≫ projection = 𝟙 _
  projection_coord (i : ℤ) (x : algebra.complex.X i) :
    projection.chainMap.f i x = (coord i x).1
  section_coord (i : ℤ) (x : B.complex.X i) :
    coord i (zeroSection.chainMap.f i x) = (x, 0)
  unit_coord : coord 0 algebra.one = (B.one, 0)
  differential (i j : ℤ) (x : algebra.complex.X i) :
    coord j (algebra.complex.d i j x) =
      (B.complex.d i j (coord i x).1, (M.complex ()).d i j (coord i x).2)
  multiplication (i j n : ℤ) (h : i+j=n) (x : algebra.complex.X i) (y : algebra.complex.X j) :
    coord n (algebra.mul i j n h x y) =
      (B.mul i j n h (coord i x).1 (coord j y).1,
        act M i j n h (coord i x).2 (coord j y).1 +
          (i*j).negOnePow • act M j i n (by omega) (coord j y).2 (coord i x).1)

abbrev IsNonpositive (M : B.Module) : Prop :=
  ∀ i : ℤ, 0 < i → Subsingleton (term M i)

def Extension.nonpositiveAlgebra {M : B.Module} (S : Extension M)
    (h : S.algebra.IsNonpositive) : NonpositiveCDGA.{u,v} k := ⟨S.algebra, h⟩

def ExtensionConstruction : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {B : NonpositiveCDGA.{u,v} k},
    ∃ S : ∀ M : B.Module, Extension M,
      ∀ M : B.Module, IsNonpositive M → (S M).algebra.IsNonpositive

abbrev underlying {P Q : NonpositiveCDGA.{u,v} k} (f : P ⟶ Q) :
    P.toCommDGAlgebra ⟶ Q.toCommDGAlgebra := f

/-- Maps of augmented algebras under the base and over the fixed target. -/
abbrev Maps (R : Model b) {E : CommDGAlgebra.{u,v} k}
    (p : E ⟶ B.toCommDGAlgebra) (s : B.toCommDGAlgebra ⟶ E) :=
  {f : R.algebra.toCommDGAlgebra ⟶ E //
    f ≫ p = underlying R.augmentation ∧
      underlying R.base ≫ f = underlying b ≫ s}

abbrev Cycles (R : Model b) (T : ModuleTensor.{u,v} k) (M : B.Module) :=
  cyclesZero (homComplex (R.module T) M)

abbrev symbol (R : Model b) (T : ModuleTensor.{u,v} k) (i : ℤ) :=
  baseChangedSymbol T R.augmentation R.differentials i

/-- Read a cycle on the base-changed universal differential. -/
abbrev read {R : Model b} {T : ModuleTensor.{u,v} k} {M : B.Module}
    (z : Cycles R T M) (i : ℤ) (x : R.algebra.complex.X i) : term M i :=
  component z.val () i i (add_zero i) (symbol R T i x)

structure CycleComparison (R : Model b) (T : ModuleTensor.{u,v} k)
    {M : B.Module} (S : Extension M) where
  equiv : Maps R S.projection S.zeroSection ≃ Cycles R T M
  read_equiv (f : Maps R S.projection S.zeroSection) (i : ℤ) (x : R.algebra.complex.X i) :
    read (equiv f) i x = (S.coord i (f.val.chainMap.f i x)).2
  component_derivation (f : Maps R S.projection S.zeroSection) :
    ∃ D : R.algebra.complex ⟶ M.complex (),
      (∀ (i : ℤ) (x : R.algebra.complex.X i), D.f i x = (S.coord i (f.val.chainMap.f i x)).2) ∧
      IsDerivation (underlying R.base)
        (M := Tensor.restrict (underlying R.augmentation) M) (Cochain.ofHom D)
  cycle_ext {z z' : Cycles R T M} :
    (∀ (i : ℤ) (x : R.algebra.complex.X i), read z i x = read z' i x) → z = z'

def MapsAreCycles : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    {b : A ⟶ B} (R : Model b) (T : ModuleTensor.{u,v} k)
    (_ : T.Formulas (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra))
    {M : B.Module} (S : Extension M), Nonempty (CycleComparison R T S)

/-- The map of extensions induced by a strict map of coefficient modules. -/
structure CoefficientMap {M N : B.Module} (S : Extension M) (U : Extension N)
    (g : M ⟶ N) where
  hom : S.algebra ⟶ U.algebra
  projection_comm : hom ≫ U.projection = S.projection
  section_comm : S.zeroSection ≫ hom = U.zeroSection
  coefficients (i : ℤ) (x : S.algebra.complex.X i) :
    (U.coord i (hom.chainMap.f i x)).2 = (g.app ()).f i (S.coord i x).2

def CoefficientMap.postcompose {M N : B.Module} {S : Extension M} {U : Extension N}
    {g : M ⟶ N} (G : CoefficientMap S U g) {R : Model b}
    (f : Maps R S.projection S.zeroSection) : Maps R U.projection U.zeroSection :=
  ⟨f.val ≫ G.hom, by rw [Category.assoc, G.projection_comm, f.property.1],
    by rw [← Category.assoc, f.property.2, Category.assoc, G.section_comm]⟩

def CoefficientNaturality : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    {b : A ⟶ B} (R : Model b) (T : ModuleTensor.{u,v} k)
    {M N : B.Module} (S : Extension M) (U : Extension N)
    (E : CycleComparison R T S) (E' : CycleComparison R T U) (g : M ⟶ N),
    ∃ G : CoefficientMap S U g, ∀ (f : Maps R S.projection S.zeroSection)
      (i : ℤ) (x : R.algebra.complex.X i),
      read (E'.equiv (G.postcompose f)) i x = (g.app ()).f i (read (E.equiv f) i x)

/-- The polynomial path target over the constant augmentation, truncated at zero. -/
structure PathTarget {M : B.Module} (S : Extension M)
    (W : ModulePathModel M) (U : Extension W.obj) where
  algebra : NonpositiveCDGA.{u,v} k
  inclusion : algebra.toCommDGAlgebra ⟶ U.algebra
  inclusion_injective (i : ℤ) : Function.Injective (inclusion.chainMap.f i)
  inclusion_range (i : ℤ) (x : U.algebra.complex.X i) :
    (∃ y : algebra.complex.X i, inclusion.chainMap.f i y = x) ↔
      (0 < i → x = 0) ∧ (i = 0 → U.algebra.complex.d i (i+1) x = 0)
  zeroSection : B.toCommDGAlgebra ⟶ algebra.toCommDGAlgebra
  section_inclusion : zeroSection ≫ inclusion = U.zeroSection
  evaluation : k → (algebra.toCommDGAlgebra ⟶ S.algebra)
  evaluation_projection (c : k) : evaluation c ≫ S.projection = inclusion ≫ U.projection
  section_evaluation (c : k) : zeroSection ≫ evaluation c = S.zeroSection
  evaluation_coefficients (c : k) (i : ℤ) (x : algebra.complex.X i) :
    (S.coord i ((evaluation c).chainMap.f i x)).2 =
      ((W.evaluation c).app ()).f i (U.coord i (inclusion.chainMap.f i x)).2

abbrev PathTarget.augmentation {M : B.Module} {S : Extension M}
    {W : ModulePathModel M} {U : Extension W.obj} (H : PathTarget S W U) :=
  H.inclusion ≫ U.projection

def PathTarget.evalMap {M : B.Module} {S : Extension M} {W : ModulePathModel M}
    {U : Extension W.obj} (H : PathTarget S W U) {R : Model b}
    (f : Maps R H.augmentation H.zeroSection) (c : k) : Maps R S.projection S.zeroSection :=
  ⟨f.val ≫ H.evaluation c, by rw [Category.assoc, H.evaluation_projection]; exact f.property.1,
    by rw [← Category.assoc, f.property.2, Category.assoc, H.section_evaluation]⟩

def PolynomialPathsAreCycles : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    {b : A ⟶ B} (R : Model b) (T : ModuleTensor.{u,v} k)
    (_ : T.Formulas (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra))
    {M : B.Module} (_ : IsNonpositive M) (S : Extension M) (W : ModulePathModel M)
    (U : Extension W.obj),
    ∃ (H : PathTarget S W U) (E : CycleComparison R T S)
      (e : Maps R H.augmentation H.zeroSection ≃ Cycles R T W.obj),
      (∀ (f : Maps R H.augmentation H.zeroSection) (i : ℤ) (x : R.algebra.complex.X i),
        read (e f) i x = (U.coord i ((f.val ≫ H.inclusion).chainMap.f i x)).2) ∧
      ∀ (f : Maps R H.augmentation H.zeroSection) (c : k)
        (i : ℤ) (x : R.algebra.complex.X i),
        read (E.equiv (H.evalMap f c)) i x = ((W.evaluation c).app ()).f i (read (e f) i x)

end
end Specs.DerivedFormalization.Affine.SquareZeroMaps
