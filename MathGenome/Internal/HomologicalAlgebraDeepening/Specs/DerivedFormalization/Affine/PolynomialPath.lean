import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.Tensor
import Mathlib.LinearAlgebra.Finsupp.LSum

open CategoryTheory

universe u v

noncomputable section

set_option linter.checkUnivs false

namespace Specs.DerivedFormalization.Affine.PolynomialPath

open _root_.DerivedFormalization

variable {k : Type u} [Field k] [CharZero k]

abbrev Coefficients (V : Type v) [AddCommGroup V] := ℕ →₀ V

section Coefficients

variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type*} [AddCommGroup W] [Module k W]

/-- The linear map on coefficients induced by a map of coefficient modules. -/
def mapCoefficients (f : V →ₗ[k] W) : Coefficients V →ₗ[k] Coefficients W :=
  Finsupp.lsum k fun n => (Finsupp.lsingle n).comp f

def derivative : Coefficients V →ₗ[k] Coefficients V :=
  Finsupp.lsum k fun
    | 0 => 0
    | n+1 => ((n+1 : ℕ) : k) • Finsupp.lsingle n

/-- The polynomial primitive with zero constant coefficient. -/
def primitive : Coefficients V →ₗ[k] Coefficients V :=
  Finsupp.lsum k fun n => (((n+1 : ℕ) : k)⁻¹) • Finsupp.lsingle (n+1)

def evaluate (c : k) : Coefficients V →ₗ[k] V :=
  Finsupp.lsum k fun n => (c ^ n) • LinearMap.id

def DerivativeType :=
  ∀ {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V],
    Coefficients V →ₗ[k] Coefficients V

def PrimitiveType := DerivativeType.{u,v}

def EvaluateType :=
  ∀ {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V],
    k → Coefficients V →ₗ[k] V

def FundamentalIdentities : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {V : Type v} [AddCommGroup V] [Module k V],
    let D : Coefficients V →ₗ[k] Coefficients V := derivative
    let J : Coefficients V →ₗ[k] Coefficients V := primitive
    let c : V →ₗ[k] Coefficients V := Finsupp.lsingle 0
    D.comp J = LinearMap.id ∧
      J.comp D = LinearMap.id - c.comp (evaluate (0 : k)) ∧
      (evaluate (0 : k)).comp J = 0 ∧
      (evaluate (1 : k)).comp (J.comp D) = evaluate 1 - evaluate 0

end Coefficients

section Complex

variable (X : ModuleCochain.{u,v} k)

abbrev term (n : ℤ) := ModuleCat.of k (Coefficients (X.X n) × Coefficients (X.X (n-1)))

abbrev polynomial (n : ℤ) : Coefficients (X.X n) →ₗ[k] term X n := LinearMap.inl k _ _
abbrev form (n : ℤ) : Coefficients (X.X (n-1)) →ₗ[k] term X n := LinearMap.inr k _ _

def transport (i j : ℤ) (e : i = j) : X.X i →ₗ[k] X.X j :=
  (eqToHom (congrArg X.X e)).hom

/-- In total degree n the two components are (X^n[t]) and (X^{n-1}[t],dt). -/
def differential (i j : ℤ) (e : i+1=j) : term X i →ₗ[k] term X j :=
  (((mapCoefficients (X.d i j).hom).comp (LinearMap.fst k _ _)).prod
    ((mapCoefficients (X.d (i-1) (j-1)).hom).comp (LinearMap.snd k _ _) +
      i.negOnePow • (((mapCoefficients (transport X i (j-1) (by omega))).comp derivative).comp
        (LinearMap.fst k _ _))))

def constant (n : ℤ) : X.X n →ₗ[k] term X n :=
  (polynomial X n).comp (Finsupp.lsingle 0)

def endpoint (c : k) (n : ℤ) : term X n →ₗ[k] X.X n :=
  (evaluate c).comp (LinearMap.fst k _ _)

/-- Integration from zero to (t), with the sign of the coefficient degree. -/
def contraction (i j : ℤ) (e : i-1=j) : term X i →ₗ[k] term X j :=
  j.negOnePow • ((polynomial X j).comp
    ((mapCoefficients (transport X (i-1) j e)).comp
      (primitive.comp (LinearMap.snd k _ _))))

/-- Integration from zero to one. -/
def integral (i j : ℤ) (e : i-1=j) : term X i →ₗ[k] X.X j :=
  (endpoint X 1 j).comp (contraction X i j e)

def DifferentialSquare : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (X : ModuleCochain.{u,v} k)
    (i j l : ℤ) (e : i+1=j) (f : j+1=l),
    (differential X j l f).comp (differential X i j e) = 0

def ContractionEquation : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (X : ModuleCochain.{u,v} k)
    (i j l : ℤ) (e : j+1=i) (f : i+1=l),
    (differential X j i e).comp (contraction X i j (by omega)) +
      (contraction X l i (by omega)).comp (differential X i l f) =
      LinearMap.id - (constant X i).comp (endpoint X 0 i)

def IntegralEquation : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (X : ModuleCochain.{u,v} k)
    (i j l : ℤ) (e : j+1=i) (f : i+1=l),
    (X.d j i).hom.comp (integral X i j (by omega)) +
      (integral X l i (by omega)).comp (differential X i l f) =
      endpoint X 1 i - endpoint X 0 i

end Complex

section Models

open _root_.DerivedFormalization.Affine
open Specs.DerivedFormalization.Affine.Tensor (act)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component HomotopyEquation)

/-- The coefficient of the product of two monomials occurs at the sum of their powers. -/
def convolution {V W Y : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup Y] [Module k Y]
    (m : V →ₗ[k] W →ₗ[k] Y) :
    Coefficients V →ₗ[k] Coefficients W →ₗ[k] Coefficients Y :=
  Finsupp.lsum k fun a =>
    (Finsupp.lsum (α := ℕ) (M := W) (N := Coefficients Y) k).toLinearMap.comp
      (LinearMap.pi fun b => m.compr₂ (Finsupp.lsingle (a+b)))

structure ModulePathModel {A : CommDGAlgebra.{u,v} k} (M : A.Module) where
  obj : A.Module
  coordinates : ∀ n : ℤ, (obj.complex ()).X n ≃ₗ[k] term (M.complex ()) n
  constantMap : M ⟶ obj
  evaluation : k → (obj ⟶ M)
  homotopy : gradedHom obj M (-1)
  primitiveHomotopy : gradedHom obj obj (-1)
  d_coordinates (i j : ℤ) (e : i+1=j) (x : (obj.complex ()).X i) :
    coordinates j ((obj.complex ()).d i j x) =
      differential (M.complex ()) i j e (coordinates i x)
  action_coordinates (i j n : ℤ) (h : i+j=n) (x : (obj.complex ()).X i) (a : A.complex.X j) :
    coordinates n (act obj i j n h x a) =
      (mapCoefficients ((act M i j n h).flip a) (coordinates i x).1,
        j.negOnePow • mapCoefficients ((act M (i-1) j (n-1) (by omega)).flip a)
          (coordinates i x).2)
  constant_coordinates (i : ℤ) (x : (M.complex ()).X i) :
    coordinates i ((constantMap.app ()).f i x) = constant (M.complex ()) i x
  evaluation_coordinates (c : k) (i : ℤ) (x : (obj.complex ()).X i) :
    ((evaluation c).app ()).f i x = endpoint (M.complex ()) c i (coordinates i x)
  integral_coordinates (i j : ℤ) (e : i-1=j) (x : (obj.complex ()).X i) :
    component homotopy () i j (by omega) x = integral (M.complex ()) i j e (coordinates i x)
  primitive_coordinates (i j : ℤ) (e : i-1=j) (x : (obj.complex ()).X i) :
    coordinates j (component primitiveHomotopy () i j (by omega) x) =
      contraction (M.complex ()) i j e (coordinates i x)
  endpoints_homotopic : HomotopyEquation (evaluation 1) (evaluation 0) homotopy
  contraction_at_zero : HomotopyEquation (𝟙 obj) (evaluation 0 ≫ constantMap) primitiveHomotopy

def ModulePathConstruction : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A : CommDGAlgebra.{u,v} k} (M : A.Module),
    Nonempty (ModulePathModel M)

structure AlgebraPathModel (A : CommDGAlgebra.{u,v} k) where
  obj : CommDGAlgebra.{u,v} k
  coordinates : ∀ i : ℤ, obj.complex.X i ≃ₗ[k] term A.complex i
  constantMap : A ⟶ obj
  evaluation : k → (obj ⟶ A)
  d_coordinates (i j : ℤ) (e : i+1=j) (x : obj.complex.X i) :
    coordinates j (obj.complex.d i j x) = differential A.complex i j e (coordinates i x)
  multiplication (i j n : ℤ) (h : i+j=n) (x : obj.complex.X i) (y : obj.complex.X j) :
    coordinates n (obj.mul i j n h x y) =
      (convolution (A.mul i j n h) (coordinates i x).1 (coordinates j y).1,
        convolution (A.mul i (j-1) (n-1) (by omega)) (coordinates i x).1 (coordinates j y).2 +
          j.negOnePow • convolution (A.mul (i-1) j (n-1) (by omega))
            (coordinates i x).2 (coordinates j y).1)
  constant_coordinates (i : ℤ) (x : A.complex.X i) :
    coordinates i (constantMap.chainMap.f i x) = constant A.complex i x
  evaluation_coordinates (c : k) (i : ℤ) (x : obj.complex.X i) :
    (evaluation c).chainMap.f i x = endpoint A.complex c i (coordinates i x)
  constant_evaluation (c : k) : constantMap ≫ evaluation c = 𝟙 A

def AlgebraPathConstruction : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : CommDGAlgebra.{u,v} k),
    Nonempty (AlgebraPathModel A)

def ground (k : Type u) [Field k] [CharZero k] : NonpositiveCDGA.{u,u} k :=
  NonpositiveCDGA.ordinary (CommAlgCat.of k k)

def DeRhamAlgebra : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ (P : AlgebraPathModel (ground k).toCommDGAlgebra)
      (t : P.obj.complex.X 0) (dt : P.obj.complex.X 1),
      P.coordinates 0 t = (Finsupp.single 1 (ground k).one, 0) ∧
      P.coordinates 1 dt = (0, Finsupp.single 0 (ground k).one) ∧
      P.obj.complex.d 0 1 t = dt ∧ P.obj.complex.d 1 2 dt = 0 ∧
      P.obj.mul 1 1 2 rfl dt dt = 0 ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (P.obj.complex.X i)) ∧
      (∀ c : k, (P.evaluation c).chainMap.f 0 t = c • (ground k).one ∧
        (P.evaluation c).chainMap.f 1 dt = 0)

def TensorCoordinates : Prop :=
  ∀ {k : Type u} [Field k] (V : Type v) [AddCommGroup V] [Module k V],
    ∃ e : TensorProduct k V (Coefficients k) ≃ₗ[k] Coefficients V,
      ∀ (x : V) (p : Coefficients k) (n : ℕ), e (TensorProduct.tmul k x p) n = p n • x

/-- The coordinate model is the total tensor with the actual de Rham forms.
The only form degrees are zero and one, so their direct sum is a binary product. -/
def DeRhamTensorCoordinates : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ P : AlgebraPathModel (ground k).toCommDGAlgebra,
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (P.obj.complex.X i)) ∧
      ∀ (X : ModuleCochain.{u,v} k) (n : ℤ),
        ∃ e : (TensorProduct k (X.X n) (P.obj.complex.X 0) ×
            TensorProduct k (X.X (n-1)) (P.obj.complex.X 1)) ≃ₗ[k] term X n,
          (∀ (x : X.X n) (p : P.obj.complex.X 0) (a : ℕ),
            (e (TensorProduct.tmul k x p,0)).1 a = (show k from (P.coordinates 0 p).1 a) • x) ∧
          (∀ (x : X.X (n-1)) (q : P.obj.complex.X 1) (a : ℕ),
            (e (0,TensorProduct.tmul k x q)).2 a = (show k from (P.coordinates 1 q).2 a) • x)

variable {Q B : NonpositiveCDGA.{u,v} k} (f : Q ⟶ B)
  (P : AlgebraPathModel Q.toCommDGAlgebra) (R : AlgebraPathModel B.toCommDGAlgebra)

/-- The relative path and its good truncation, including both universal properties
and the endpoint comparison. -/
structure RelativePathModel where
  coefficientMap : P.obj ⟶ R.obj
  map_coordinates (n : ℤ) (x : P.obj.complex.X n) :
    R.coordinates n (coefficientMap.chainMap.f n x) =
      (mapCoefficients (f.chainMap.f n).hom (P.coordinates n x).1,
        mapCoefficients (f.chainMap.f (n-1)).hom (P.coordinates n x).2)
  relative : CommDGAlgebra.{u,v} k
  includeRelative : relative ⟶ P.obj
  augmentRelative : relative ⟶ B.toCommDGAlgebra
  relative_square : includeRelative ≫ coefficientMap = augmentRelative ≫ R.constantMap
  relative_pullback (D : CommDGAlgebra.{u,v} k) (a : D ⟶ P.obj) (b : D ⟶ B.toCommDGAlgebra)
      (h : a ≫ coefficientMap = b ≫ R.constantMap) :
    ∃! g : D ⟶ relative, g ≫ includeRelative = a ∧ g ≫ augmentRelative = b
  relativeConstant : Q.toCommDGAlgebra ⟶ relative
  relative_constant : relativeConstant ≫ includeRelative = P.constantMap
  relative_section : relativeConstant ≫ includeRelative ≫ P.evaluation 0 = 𝟙 Q.toCommDGAlgebra
  contractingHomotopy : ∀ i j : ℤ, i-1=j → relative.complex.X i →ₗ[k] relative.complex.X j
  contraction_coordinates (i j : ℤ) (e : i-1=j) (x : relative.complex.X i) :
    P.coordinates j (includeRelative.chainMap.f j (contractingHomotopy i j e x)) =
      contraction Q.complex i j e (P.coordinates i (includeRelative.chainMap.f i x))
  contraction_in_kernel (i j : ℤ) (e : i-1=j) (x : relative.complex.X i) :
    ((includeRelative ≫ P.evaluation 0).chainMap.f j).hom (contractingHomotopy i j e x) = 0
  contraction_equation (i : ℤ) (x : relative.complex.X i) :
    relative.complex.d (i-1) i (contractingHomotopy i (i-1) rfl x) +
      contractingHomotopy (i+1) i (by omega) (relative.complex.d i (i+1) x) =
      x - (((includeRelative ≫ P.evaluation 0) ≫ relativeConstant).chainMap.f i) x
  truncated : NonpositiveCDGA.{u,v} k
  includeTruncation : truncated.toCommDGAlgebra ⟶ relative
  truncation_injective (i : ℤ) : Function.Injective (includeTruncation.chainMap.f i)
  truncation_range (i : ℤ) (x : relative.complex.X i) :
    (∃ y : truncated.complex.X i, includeTruncation.chainMap.f i y = x) ↔
      (0 < i → x = 0) ∧ (i = 0 → relative.complex.d i (i+1) x = 0)
  constants : Q ⟶ truncated
  constants_truncate :
    ((constants : Q.toCommDGAlgebra ⟶ truncated.toCommDGAlgebra) ≫ includeTruncation :
      Q.toCommDGAlgebra ⟶ relative) = relativeConstant
  inclusion_comparison : QuasiIso includeTruncation.chainMap
  truncated_comparison : QuasiIso ((includeTruncation ≫ includeRelative ≫ P.evaluation 0).chainMap)
  target : NonpositiveCDGA.{u,v} k
  first : target ⟶ Q
  second : target ⟶ Q
  same_augmentation : first ≫ f = second ≫ f
  target_pullback (D : NonpositiveCDGA.{u,v} k) (a b : D ⟶ Q) (h : a ≫ f = b ≫ f) :
    ∃! g : D ⟶ target, g ≫ first = a ∧ g ≫ second = b
  endpoints : truncated ⟶ target
  first_eval :
    (endpoints ≫ first).chainMap = (includeTruncation ≫ includeRelative ≫ P.evaluation 0).chainMap
  second_eval :
    (endpoints ≫ second).chainMap = (includeTruncation ≫ includeRelative ≫ P.evaluation 1).chainMap
  constant_first : constants ≫ endpoints ≫ first = 𝟙 Q
  constant_second : constants ≫ endpoints ≫ second = 𝟙 Q
  trivial_fibration : NonpositiveCDGA.DegreewiseSurjective f → NonpositiveCDGA.IsQuasiIso f →
    NonpositiveCDGA.DegreewiseSurjective endpoints ∧ NonpositiveCDGA.IsQuasiIso endpoints

def RelativePathConstruction : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {Q B : NonpositiveCDGA.{u,v} k} (f : Q ⟶ B),
    ∃ (P : AlgebraPathModel Q.toCommDGAlgebra) (R : AlgebraPathModel B.toCommDGAlgebra),
      Nonempty (RelativePathModel f P R)

end Models

end Specs.DerivedFormalization.Affine.PolynomialPath
