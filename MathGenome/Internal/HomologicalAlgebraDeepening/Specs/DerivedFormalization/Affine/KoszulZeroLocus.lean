import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedAffineBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KoszulCochainResolution
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.PolynomialExample
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! The Koszul cdga and the algebra maps in the derived zero locus calculation. -/

open CategoryTheory HomologicalComplex
open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Semifree (Variables)
open _root_.DerivedFormalization.Affine.NonpositiveCDGA (ordinary ordinaryMap)
open _root_.AdvCommAlg.Koszul (listIdeal listForm)

universe u v

namespace Specs.DerivedFormalization.Affine.KoszulZeroLocus

open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor)
open Specs.DerivedFormalization.Affine.TensorResolutionComparison
open Specs.DerivedFormalization.KoszulCochainResolution (cochainValue termIsoValue augmentationValue)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]

/-- The variable over equation `i` is in degree `-1`. -/
abbrev exteriorVariables (r : ℕ) : Variables.{v} where
  Index := ULift.{v} (Fin r)
  degree _ := -1
  nonpositive _ := by decide

abbrev quotientRing {R : Type v} [CommRing R] {r : ℕ} (f : Fin r → R) :=
  R ⧸ listIdeal (List.ofFn f)

abbrev quotientAlg {r : ℕ} (R : CommAlgCat.{v} k) (f : Fin r → R) : CommAlgCat.{v} k :=
  CommAlgCat.of k (quotientRing f)

abbrev quotientMap {r : ℕ} (R : CommAlgCat.{v} k) (f : Fin r → R) :
    ordinary R ⟶ ordinary (quotientAlg R f) :=
  ordinaryMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k (listIdeal (List.ofFn f))))

/-- The ordinary Koszul cochain complex with scalars restricted to the field. -/
abbrev restrictCochains (R : CommAlgCat.{v} k) :
    CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} k) ℤ :=
  (ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of the quotient stalk, using the original field action on
the quotient on the cdga side. -/
def quotientStalkIso (R : CommAlgCat.{v} k) {r : ℕ} (f : Fin r → R) :
    (restrictCochains R).obj ((Cochains.stalkValue R).obj (ModuleCat.of R (quotientRing f))) ≅
      (ordinary (quotientAlg R f)).complex :=
  (singleMapHomologicalComplex (ModuleCat.restrictScalars (algebraMap k R)) (.up ℤ) 0).app
      (ModuleCat.of R (quotientRing f)) ≪≫
    (HomologicalComplex.single (ModuleCat.{v} k) (.up ℤ) 0).mapIso
      ({ toFun := id
         invFun := id
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl
         map_add' := fun _ _ => rfl
         map_smul' := fun a x => by
           let y : quotientRing f := x
           change algebraMap k R a • y = a • y
           exact IsScalarTower.algebraMap_smul R a y } :
        (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R (quotientRing f))
          ≃ₗ[k] quotientRing f).toModuleIso

/-- The wedge of the coordinate vectors indexed by the given ordered tuple. -/
def coordinateWedge {R : Type v} [CommRing R] {r : ℕ} (f : Fin r → R)
    (n : ℕ) (s : Fin n → Fin r) : ⋀[R]^n (Fin (List.ofFn f).length → R) :=
  exteriorPower.ιMulti R n (fun j =>
    Pi.basisFun R (Fin (List.ofFn f).length) (Fin.cast List.length_ofFn.symm (s j)))

/-- Multiply the degree `-1` elements in tuple order. -/
def orderedProduct {r : ℕ} (P : NonpositiveCDGA.{u,v} k)
    (e : Fin r → P.complex.X (-1)) :
    (n : ℕ) → (Fin n → Fin r) → P.complex.X (-(n : ℤ))
  | 0, _ => P.one
  | n + 1, s =>
      P.mul (-1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
        (e (s 0)) (orderedProduct P e n (Fin.tail s))

variable {r : ℕ} {R : CommAlgCat.{v} k} {f : Fin r → R}

/-- A Koszul cdga over the ordinary algebra, with its comparisons to the
ordinary Koszul complex and to the canonical quotient augmentation. -/
structure KoszulAlgebra (R : CommAlgCat.{v} k) {r : ℕ} (f : Fin r → R) where
  obj : NonpositiveCDGA.{u,v} k
  base : ordinary R ⟶ obj
  exterior : Semifree.StagedPresentation (ordinary R) (exteriorVariables r) base
  d_generator (i : Fin r) :
    obj.complex.d (-1) 0
      (exterior.component (-1) (Semifree.variableTerm (ordinary R) (exteriorVariables r) (ULift.up i))) =
        base.chainMap.f 0 (f i)
  cochain : obj.complex ≅ (restrictCochains R).obj (cochainValue (List.ofFn f))
  cochain_scalar (i : ℤ) (a : R) (x : obj.complex.X i) :
    (show (cochainValue (List.ofFn f)).X i from
      cochain.hom.f i (obj.mul 0 i i (zero_add i) (base.chainMap.f 0 a) x)) =
      a • (show (cochainValue (List.ofFn f)).X i from cochain.hom.f i x)
  monomial (n : ℕ) (s : Fin n → Fin r) (a : R) :
    (termIsoValue (List.ofFn f) n).hom
      (cochain.hom.f (-(n : ℤ))
        (obj.mul 0 (-(n : ℤ)) (-(n : ℤ)) (zero_add _)
          (base.chainMap.f 0 a) (orderedProduct obj
            (fun i => exterior.component (-1)
              (Semifree.variableTerm (ordinary R) (exteriorVariables r) (ULift.up i))) n s))) =
      a • coordinateWedge f n s
  augmentation : obj ⟶ ordinary (quotientAlg R f)
  augmentation_base : base ≫ augmentation = quotientMap R f
  augmentation_cochain :
    augmentation.chainMap =
      cochain.hom ≫ (restrictCochains R).map (augmentationValue (List.ofFn f)) ≫
        (quotientStalkIso R f).hom

namespace KoszulAlgebra

variable (P : KoszulAlgebra R f)

abbrev generator (i : Fin r) : P.obj.complex.X (-1) :=
  P.exterior.component (-1) (Semifree.variableTerm (ordinary R) (exteriorVariables r) (ULift.up i))

theorem semifree : Semifree.IsSemifree (ordinary R) P.base :=
  ⟨exteriorVariables r, ⟨P.exterior⟩⟩

/-- The underlying ordered exterior wedges have the alternating deletion differential. -/
def WedgeDifferential : Prop :=
  ∀ (n : ℕ) (x : Fin (n + 1) → (Fin (List.ofFn f).length → R)),
    (termIsoValue (List.ofFn f) n).hom
      (P.cochain.hom.f (-(n : ℤ))
        (P.obj.complex.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
          (P.cochain.inv.f (-((n + 1 : ℕ) : ℤ))
            ((termIsoValue (List.ofFn f) (n + 1)).inv
              (exteriorPower.ιMulti R (n + 1) x))))) =
      ∑ i : Fin (n + 1), (-1 : R)^i.val •
        (listForm (List.ofFn f) (x i) • exteriorPower.ιMulti R n (x ∘ i.succAbove))

/-- Package the same Koszul augmentation as a resolution, once its two
resolution conditions have been proved. -/
def resolution (hs : NonpositiveCDGA.DegreewiseSurjective P.augmentation)
    (hq : NonpositiveCDGA.IsQuasiIso P.augmentation) : Resolution (quotientMap R f) :=
  ⟨P.obj, P.base, P.augmentation, P.augmentation_base, P.semifree, hs, hq⟩

end KoszulAlgebra

/-- Any representative `K` of the ground field at the coefficient universe
can be used in the polynomial and zero-section diagrams. The ground field
itself can be used at its native universe, or lifted to a common universe. -/
abbrev fieldRepresentative (k : Type u) [Field k] : CommAlgCat.{max u v} k :=
  CommAlgCat.of k (ULift.{v} k)

abbrev fieldRepresentativeEquiv (k : Type u) [Field k] :
    fieldRepresentative.{u,v} k ≃ₐ[k] k :=
  ULift.algEquiv

abbrev polynomial (K : CommAlgCat.{v} k) (r : ℕ) : CommAlgCat.{v} k :=
  CommAlgCat.of k (MvPolynomial (Fin r) K)

def polynomialMap (K : CommAlgCat.{v} k) (e : K ≃ₐ[k] k) (R : CommAlgCat.{v} k)
    {r : ℕ} (f : Fin r → R) : ordinary (polynomial K r) ⟶ ordinary R :=
  ordinaryMap (CommAlgCat.ofHom (MvPolynomial.aevalTower
    ((Algebra.ofId k R).comp e.toAlgHom) f))

def zeroSection (K : CommAlgCat.{v} k) (r : ℕ) : ordinary (polynomial K r) ⟶ ordinary K :=
  ordinaryMap (CommAlgCat.ofHom ((MvPolynomial.aeval (fun _ : Fin r => (0 : K))).restrictScalars k))

abbrev polynomialKoszul (K : CommAlgCat.{v} k) (r : ℕ) :=
  KoszulAlgebra (polynomial K r) (r := r) MvPolynomial.X

/-- The polynomial resolution uses the very same exterior generators as the
universal Koszul algebra, and its augmentation is evaluation at zero. -/
structure PolynomialResolution (K : CommAlgCat.{v} k) (r : ℕ) where
  koszul : polynomialKoszul K r
  coefficients : quotientRing (R := MvPolynomial (Fin r) K) MvPolynomial.X ≃ₐ[k] K
  coefficients_eval (p : MvPolynomial (Fin r) K) :
    coefficients (Ideal.Quotient.mk _ p) = MvPolynomial.eval (fun _ => 0) p
  commutes : koszul.base ≫
      (koszul.augmentation ≫ ordinaryMap (CommAlgCat.ofHom coefficients.toAlgHom)) =
        zeroSection K r
  surjective : NonpositiveCDGA.DegreewiseSurjective
    (koszul.augmentation ≫ ordinaryMap (CommAlgCat.ofHom coefficients.toAlgHom))
  quasiIso : NonpositiveCDGA.IsQuasiIso
    (koszul.augmentation ≫ ordinaryMap (CommAlgCat.ofHom coefficients.toAlgHom))

def PolynomialResolution.resolution {K : CommAlgCat.{v} k} {r : ℕ}
    (Q : PolynomialResolution K r) : Resolution (zeroSection K r) :=
  ⟨Q.koszul.obj, Q.koszul.base,
    Q.koszul.augmentation ≫ ordinaryMap (CommAlgCat.ofHom Q.coefficients.toAlgHom),
    Q.commutes, Q.koszul.semifree, Q.surjective, Q.quasiIso⟩

variable {T : ModuleTensor.{u,v} k} (S : CoproductModel T)

/-- Identify the formal tensor with the Koszul algebra over the second
factor, including its coefficient algebra and the left-factor generators. -/
def TensorComparison {B : CommAlgCat.{v} k} {a : Fin r → B}
    (P : KoszulAlgebra B a) (g : ordinary B ⟶ ordinary R) (Q : KoszulAlgebra R f) : Prop :=
  ∃ e : S.tensor P.base g ≅ Q.obj,
    S.inr P.base g ≫ e.hom = Q.base ∧
    ∀ i : Fin r, e.hom.chainMap.f (-1) ((S.inl P.base g).chainMap.f (-1) (P.generator i)) =
      Q.generator i

/-- The polynomial Koszul resolution, the arbitrary derived fibre, and the
regular-sequence self-intersection. -/
def KoszulCalculations : Prop :=
  (∀ (R : CommAlgCat.{v} k) (r : ℕ) (f : Fin r → R),
    ∃ P : KoszulAlgebra R f, P.WedgeDifferential) ∧
  (∀ (K : CommAlgCat.{v} k) (e : K ≃ₐ[k] k) (r : ℕ),
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin r) K)
      (_root_.AdvCommAlg.Koszul.PolynomialExample.variableList K r) ∧
    ∃ P : PolynomialResolution K r,
      ∀ (R : CommAlgCat.{v} k) (f : Fin r → R)
        (Q : KoszulAlgebra R f), TensorComparison S P.koszul (polynomialMap K e R f) Q) ∧
  (∀ (R : CommAlgCat.{v} k) (r : ℕ) (f : Fin r → R) (P : KoszulAlgebra R f),
    RingTheory.Sequence.IsRegular R (List.ofFn f) →
    NonpositiveCDGA.DegreewiseSurjective P.augmentation ∧
    NonpositiveCDGA.IsQuasiIso P.augmentation ∧
    ∃ Q : KoszulAlgebra (quotientAlg R f) (fun _ : Fin r => 0),
      TensorComparison S P (quotientMap R f) Q ∧
      ∀ i j : ℤ, Q.obj.complex.d i j = 0)

/-- The origin of the affine line over the represented field. The degree
`-1` isomorphism takes the actual exterior generator class to `1`. -/
def OriginCohomology : Prop :=
  ∀ (K : CommAlgCat.{v} k) (eK : K ≃ₐ[k] k),
    ∀ P : PolynomialResolution K 1,
    let X := S.tensor P.resolution.base (zeroSection K 1)
    let e₁ := (S.inl P.resolution.base (zeroSection K 1)).chainMap.f (-1) (P.koszul.generator 0)
    (∃ e : X.H0 ≃ₐ[k] k,
      ∀ a : K, e (X.h0Class ((S.inr P.resolution.base (zeroSection K 1)).chainMap.f 0 a)) =
        eK a) ∧
    (∃ (e : X.complex.homology (-1) ≃ₗ[k] k) (z : X.complex.cycles (-1)),
      X.complex.iCycles (-1) z = e₁ ∧ e (X.complex.homologyπ (-1) z) = 1) ∧
    ∀ i : ℤ, i ≠ 0 → i ≠ -1 → Limits.IsZero (X.complex.homology i)

/-- The full A05 calculation over the signed tensor models for derived affine
base change. Both the field and the coefficient universe are arbitrary. -/
def ZeroLocus : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k],
    ∃ (T : ModuleTensor.{u,v} k) (S : CoproductModel T),
      KoszulCalculations S ∧ OriginCohomology S

end

end Specs.DerivedFormalization.Affine.KoszulZeroLocus
