import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.KoszulZeroLocus
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.OrdinaryComplex
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! The conormal model of a polynomial complete intersection over a field of characteristic zero. -/

open CategoryTheory

universe u

namespace Specs.DerivedFormalization.Affine.CompleteIntersectionConormal

open _root_.DerivedFormalization.Affine
open NonpositiveCDGA (ordinary ordinaryMap DegreewiseSurjective IsQuasiIso)
open Kahler (DifferentialModel value)
open Semifree (Variables StagedPresentation variableTerm)
open KoszulZeroLocus (KoszulAlgebra quotientAlg quotientMap)
open CotangentComplex (Model ComparisonSystem oneObject)
open Tensor (ModuleTensor term act regular)
open DG.HomComplex (homComplex component)

noncomputable section

variable {k : Type u} [Field k] [CharZero k] {s r : ℕ}

abbrev Polynomial (k : Type u) [Field k] (s : ℕ) := MvPolynomial (Fin s) k

abbrev PolynomialAlgebra (k : Type u) [Field k] (s : ℕ) :=
  CommAlgCat.of k (Polynomial k s)

abbrev Quotient (f : Fin r → Polynomial k s) :=
  KoszulZeroLocus.quotientRing f

abbrev coefficientMap (k : Type u) [Field k] [CharZero k] (s : ℕ) :
    ordinary (CommAlgCat.of k k) ⟶ ordinary (PolynomialAlgebra k s) :=
  ordinaryMap (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k s)))

abbrev quotientClass (f : Fin r → Polynomial k s) :
    Polynomial k s →ₐ[k] Quotient f :=
  Ideal.Quotient.mkₐ k _

abbrev quotientCDGA (f : Fin r → Polynomial k s) : NonpositiveCDGA.{u,u} k :=
  ordinary (quotientAlg (PolynomialAlgebra k s) f)

abbrev groundMap (f : Fin r → Polynomial k s) :
    ordinary (CommAlgCat.of k k) ⟶ quotientCDGA f :=
  coefficientMap k s ≫ quotientMap (PolynomialAlgebra k s) f

variable (f : Fin r → Polynomial k s)

/-- Row `j`, column `i` of the conormal differential. -/
def jacobianEntry (j : Fin s) (i : Fin r) : Quotient f :=
  quotientClass f (MvPolynomial.pderiv j (f i))

/-- The differential in degrees `-1,0`. -/
def jacobian : (Fin r → Quotient f) →ₗ[Quotient f] (Fin s → Quotient f) where
  toFun a j := ∑ i, jacobianEntry f j i * a i
  map_add' a b := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' b a := by
    ext j
    change (∑ i, jacobianEntry f j i * (b * a i)) = b * ∑ i, jacobianEntry f j i * a i
    simp [Finset.mul_sum, mul_left_comm]

/-- The transpose acts on the coordinates of a homogeneous map into the quotient. -/
def transposeJacobian : (Fin s → Quotient f) →ₗ[Quotient f] (Fin r → Quotient f) where
  toFun a i := ∑ j, jacobianEntry f j i * a j
  map_add' a b := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' b a := by
    ext i
    change (∑ j, jacobianEntry f j i * (b * a j)) = b * ∑ j, jacobianEntry f j i * a j
    simp [Finset.mul_sum, mul_left_comm]

abbrev JacobianCokernel := (Fin r → Quotient f) ⧸ (transposeJacobian f).range

private abbrev up := ComplexShape.up ℤ
private abbrev conormalStep : up.Rel (-1) 0 := by decide

/-- The actual two-term complex of modules over the quotient ring. -/
def conormal : CochainComplex (ModuleCat.{u} (Quotient f)) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom (jacobian f)) conormalStep

abbrev equationCoordinates :
    (conormal f).X (-1) ≅ ModuleCat.of (Quotient f) (Fin r → Quotient f) :=
  HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (jacobian f)) conormalStep

abbrev polynomialCoordinates :
    (conormal f).X 0 ≅ ModuleCat.of (Quotient f) (Fin s → Quotient f) :=
  HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (jacobian f)) conormalStep (by decide)

abbrev quotientStalk : CochainComplex (ModuleCat.{u} (Quotient f)) ℤ :=
  (Cochains.stalkValue (Quotient f)).obj (ModuleCat.of (Quotient f) (Quotient f))

abbrev conormalHom : CochainComplex (ModuleCat.{u} (Quotient f)) ℤ :=
  CochainModels.internalHomValue (conormal f) (quotientStalk f)

abbrev restriction :=
  DG.OrdinaryComplex.restrictComplex k (Quotient f)

variable {f}

/-- Both blocks of generators of the Koszul resolution viewed over the field. -/
def resolutionVariables (s r : ℕ) : Variables.{u} where
  Index := ULift.{u} (Fin s ⊕ Fin r)
  degree x := x.down.elim (fun _ => 0) (fun _ => -1)
  nonpositive x := by
    rcases x with ⟨x | x⟩
    · exact le_refl 0
    · exact (by decide : (-1 : ℤ) ≤ 0)

abbrev polynomialIndex (j : Fin s) : (resolutionVariables.{u} s r).Index := ⟨Sum.inl j⟩
abbrev equationIndex (i : Fin r) : (resolutionVariables.{u} s r).Index := ⟨Sum.inr i⟩

/-- The resolution over the field is the Koszul algebra itself with the
polynomial variables adjoined before the degree `-1` variables. -/
structure KoszulPresentation (f : Fin r → Polynomial k s) where
  koszul : KoszulAlgebra (PolynomialAlgebra k s) f
  overField : StagedPresentation _ (resolutionVariables s r) (coefficientMap k s ≫ koszul.base)
  polynomial_generator (j : Fin s) :
    overField.component 0 (variableTerm _ _ (polynomialIndex j)) =
      koszul.base.chainMap.f 0 (MvPolynomial.X j)
  equation_generator (i : Fin r) :
    overField.component (-1) (variableTerm _ _ (equationIndex i)) = koszul.generator i
  stage_order (j : Fin s) (i : Fin r) :
    overField.stages.stage (polynomialIndex j) < overField.stages.stage (equationIndex i)
  surjective : DegreewiseSurjective koszul.augmentation
  quasiIso : IsQuasiIso koszul.augmentation

variable (P : KoszulPresentation f)

abbrev KoszulPresentation.relativeDifferentials :=
  DifferentialModel (show (ordinary (CommAlgCat.of k k)).toCommDGAlgebra ⟶
    P.koszul.obj.toCommDGAlgebra from coefficientMap k s ≫ P.koszul.base)

def KoszulPresentation.model (O : P.relativeDifferentials) : Model (groundMap f) where
  algebra := P.koszul.obj
  base := coefficientMap k s ≫ P.koszul.base
  augmentation := P.koszul.augmentation
  triangle := by rw [Category.assoc, P.koszul.augmentation_base]
  semifree := ⟨resolutionVariables s r, ⟨P.overField⟩⟩
  surjective := P.surjective
  quasiIso := P.quasiIso
  differentials := O

variable (O : P.relativeDifferentials)

/-- The differential on the two sets of Kähler symbols before extension of scalars. -/
def SymbolDifferentials : Prop :=
  (∀ j : Fin s, (O.module.complex ()).d 0 1
    (value O.symbol 0 0 rfl (P.koszul.base.chainMap.f 0 (MvPolynomial.X j))) = 0) ∧
  (∀ i : Fin r, (O.module.complex ()).d (-1) 0
    (value O.symbol (-1) (-1) rfl (P.koszul.generator i)) =
      value O.symbol 0 0 rfl (P.koszul.base.chainMap.f 0 (f i)))

variable (T : ModuleTensor.{u,u} k)

abbrev extendedSymbol (n : ℤ) (p : P.koszul.obj.complex.X n) :
    term ((P.model O).module T) n :=
  T.tmul P.koszul.augmentation (N := regular (quotientCDGA f).toCommDGAlgebra)
    n 0 n (add_zero n) (value O.symbol n n (add_zero n) p) (quotientCDGA f).one

open scoped Classical

/-- The cotangent representative is compared by a quotient-linear cochain
isomorphism taking the extended symbols to their coordinate vectors. -/
structure ConormalComparison where
  iso : ((P.model O).module T).complex () ≅ (restriction f).obj (conormal f)
  scalar (n : ℤ) (a : Quotient f) (x : term ((P.model O).module T) n) :
    (show (conormal f).X n from iso.hom.f n
      (act ((P.model O).module T) n 0 n (add_zero n) x
        (show (quotientCDGA f).complex.X 0 from a))) =
      a • (show (conormal f).X n from iso.hom.f n x)
  polynomial_symbol (j : Fin s) :
    (polynomialCoordinates f).hom (iso.hom.f 0
      (extendedSymbol P O T 0 (P.koszul.base.chainMap.f 0 (MvPolynomial.X j)))) =
        Pi.single j 1
  equation_symbol (i : Fin r) :
    (equationCoordinates f).hom (iso.hom.f (-1)
      (extendedSymbol P O T (-1) (P.koszul.generator i))) = Pi.single i 1

/-- The quotient of degree-one cochains by boundaries, in coordinates given
by evaluation on the equation symbols. -/
structure CokernelComparison (f : Fin r → Polynomial k s) where
  iso : (conormalHom f).homology 1 ≃ₗ[Quotient f] JacobianCokernel f
  on_class (z : (conormalHom f).cycles 1) :
    iso ((conormalHom f).homologyπ 1 z) =
      (transposeJacobian f).range.mkQ (fun i =>
        (((conormalHom f).iCycles 1 z :
          CochainComplex.HomComplex.Cochain (conormal f) (quotientStalk f) 1).v
            (-1) 0 rfl) ((equationCoordinates f).inv (Pi.single i 1)))

/-- The Koszul cotangent representative, the strict two-term comparison, and
the degree-one internal Hom calculation. -/
def ConormalModel : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {s r : ℕ}
    (f : Fin r → Polynomial k s),
    RingTheory.Sequence.IsRegular (Polynomial k s) (List.ofFn f) →
    ∃ (P : KoszulPresentation f) (O : P.relativeDifferentials)
      (T : ModuleTensor.{u,u} k)
      (h : DG.Derived.HomotopyCategoryLaws (oneObject (quotientCDGA f)))
      (_ : ComparisonSystem T (groundMap f) h) (E : ConormalComparison P O T),
      SymbolDifferentials P O ∧
      (∃ H : (restriction f).obj (conormalHom f) ≅
          homComplex ((P.model O).module T) (regular (quotientCDGA f).toCommDGAlgebra),
        ∀ (m n : ℤ) (hmn : m + n = 0)
          (a : CochainComplex.HomComplex.Cochain (conormal f) (quotientStalk f) n)
          (x : term ((P.model O).module T) m),
          component (H.hom.f n a) () m 0 hmn x =
            (show (quotientCDGA f).complex.X 0 from
              a.v m 0 hmn (E.iso.hom.f m x))) ∧
      Nonempty (CokernelComparison f)

end

end Specs.DerivedFormalization.Affine.CompleteIntersectionConormal
