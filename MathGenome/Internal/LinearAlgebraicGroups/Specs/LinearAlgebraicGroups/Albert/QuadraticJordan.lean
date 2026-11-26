import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Data.ZMod.Basic

/-! The scalar-extension definitions for NA13-C02.09. -/

namespace Specs.LinearAlgebraicGroups.Albert

universe u v w

open TensorProduct

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Compatibility is stated on the values of the operators. This avoids identifying
the scalar extension of an endomorphism module with the endomorphisms of the
scalar-extended module, which need not hold for arbitrary modules. -/
structure QuadraticOperatorLaw (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] where
  op (S : Type u) [CommRing S] [Algebra R S] :
    QuadraticMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M))
  natural {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (x y : S ⊗[R] M) :
    f.toLinearMap.rTensor M (op S x y) =
      op T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y)

namespace QuadraticOperatorLaw

variable (Q : QuadraticOperatorLaw R M)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The two outer slots polarize the quadratic variable, and the middle slot is
the input to the resulting endomorphism. -/
def triple (x y z : S ⊗[R] M) : S ⊗[R] M :=
  QuadraticMap.polarBilin (R := S) (N := Module.End S (S ⊗[R] M)) (Q.op S) x z y

end QuadraticOperatorLaw

/-- Unital quadratic Jordan structure on the specified module. -/
structure QuadraticJordan (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] extends QuadraticOperatorLaw R M where
  unit : M
  op_unit (S : Type u) [CommRing S] [Algebra R S] :
    op S (1 ⊗ₜ[R] unit) = 1
  fundamental (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] M) :
    op S (op S x y) = op S x * op S y * op S x
  commuting (S : Type u) [CommRing S] [Algebra R S] (x y z : S ⊗[R] M) :
    op S x (toQuadraticOperatorLaw.triple S y x z) =
      toQuadraticOperatorLaw.triple S (op S x y) z x

namespace QuadraticJordan

variable (J : QuadraticJordan R M)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The symmetric bilinear map obtained by polarizing the operator law. -/
def polar : LinearMap.BilinMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M)) :=
  QuadraticMap.polarBilin (R := S) (N := Module.End S (S ⊗[R] M)) (J.op S)

/-- The square at a test algebra. -/
def square (x : S ⊗[R] M) : S ⊗[R] M :=
  J.op S x (1 ⊗ₜ[R] J.unit)

/-- Jordan homomorphisms preserve the unit and intertwine the law after every extension. -/
structure Hom (J : QuadraticJordan R M) (K : QuadraticJordan R N) where
  toLinearMap : M →ₗ[R] N
  map_unit : toLinearMap J.unit = K.unit
  map_op (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] M) :
    toLinearMap.baseChange S (J.op S x y) =
      K.op S (toLinearMap.baseChange S x) (toLinearMap.baseChange S y)

/-- Recover the ground-ring operator using the tensor product unitor. -/
def groundOp (x : M) : Module.End R M :=
  (TensorProduct.lid R M).conj (J.op R (1 ⊗ₜ[R] x))

/-- The square over the original base ring. -/
def groundSquare (x : M) : M := J.groundOp x J.unit

/-- The candidate linear multiplication at each scalar algebra, with the
inverse of two specified by a unit of the base. -/
def linearProduct (d : Rˣ) : LinearMap.BilinMap S (S ⊗[R] M) (S ⊗[R] M) :=
  (algebraMap R S (↑d⁻¹ : R)) •
    (QuadraticMap.polarBilin (R := S) (N := Module.End S (S ⊗[R] M)) (J.op S)).compr₂
      (LinearMap.applyₗ (R := S) (M := S ⊗[R] M) (1 ⊗ₜ[R] J.unit))

/-- The same multiplication on the original module. -/
def groundProduct (d : Rˣ) : LinearMap.BilinMap R M M :=
  ((J.linearProduct R d).compl₁₂ (TensorProduct.lid R M).symm.toLinearMap
    (TensorProduct.lid R M).symm.toLinearMap).compr₂ (TensorProduct.lid R M).toLinearMap

end QuadraticJordan

/-- The unital linear presentation, with the Jordan identity tested on the
ordinary scalar extensions of its bilinear multiplication. -/
structure LinearJordan (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] where
  unit : M
  product : LinearMap.BilinMap R M M
  comm (x y : M) : product x y = product y x
  unit_mul (x : M) : product unit x = x
  jordan (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] M) :
    let p := product.baseChange S
    p (p x y) (p x x) = p x (p y (p x x))

/-- Thus the linear presentation determines the operators by the multiplication. -/
def operatorOfProduct {S : Type*} [CommRing S]
    {P : Type*} [AddCommGroup P] [Module S P]
    (p : LinearMap.BilinMap S P P) (x : P) : Module.End S P :=
  (2 : S) • (p x * p x) - p (p x x)

section BaseChange
set_option linter.style.haveILetI false

variable {S : Type u} [CommRing S] [Algebra R S]

abbrev towerAlgebra (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] : Algebra R T :=
  ((algebraMap S T).comp (algebraMap R S)).toAlgebra

private theorem towerScalars (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] :
    letI := towerAlgebra R S T
    IsScalarTower R S T := by
  letI := towerAlgebra R S T
  exact IsScalarTower.of_algebraMap_eq' rfl

abbrev iteratedTensorEquiv (T : Type u) [CommRing T] [Algebra S T] :
    letI := towerAlgebra R S T
    T ⊗[S] (S ⊗[R] M) ≃ₗ[T] T ⊗[R] M :=
  letI := towerAlgebra R S T
  letI := towerScalars R S T
  AlgebraTensorModule.cancelBaseChange R S T T M

private theorem iteratedTensorEquiv_natural {T W : Type u} [CommRing T] [CommRing W]
    [Algebra S T] [Algebra S W] (f : T →ₐ[S] W) (x : T ⊗[S] (S ⊗[R] M)) :
    letI := towerAlgebra R S T
    letI := towerAlgebra R S W
    letI := towerScalars R S T
    letI := towerScalars R S W
    iteratedTensorEquiv (R := R) (S := S) W (f.toLinearMap.rTensor (S ⊗[R] M) x) =
      (f.restrictScalars R).toLinearMap.rTensor M (iteratedTensorEquiv (R := R) (S := S) T x) := by
  letI := towerAlgebra R S T
  letI := towerAlgebra R S W
  letI := towerScalars R S T
  letI := towerScalars R S W
  induction x using TensorProduct.inductionOn with
  | tmul t y =>
    induction y using TensorProduct.inductionOn with
    | tmul s m =>
      simp only [LinearMap.rTensor_tmul, AlgebraTensorModule.cancelBaseChange_tmul,
        AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, Algebra.smul_def,
        map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace QuadraticJordan

variable (J : QuadraticJordan R M)

private noncomputable def baseChangeOp (T : Type u) [CommRing T] [Algebra S T] :
    QuadraticMap T (T ⊗[S] (S ⊗[R] M)) (Module.End T (T ⊗[S] (S ⊗[R] M))) :=
  letI := towerAlgebra R S T
  let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
  e.symm.conj.toLinearMap.compQuadraticMap ((J.op T).comp e.toLinearMap)

private theorem baseChangeOp_apply (T : Type u) [CommRing T] [Algebra S T]
    (x y : T ⊗[S] (S ⊗[R] M)) :
    letI := towerAlgebra R S T
    let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
    e (J.baseChangeOp T x y) = J.op T (e x) (e y) := by
  letI := towerAlgebra R S T
  let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
  change e (e.symm (J.op T (e x) (e y))) = _
  exact e.apply_symm_apply _

private noncomputable def baseChangeLaw (S : Type u) [CommRing S] [Algebra R S] :
    QuadraticOperatorLaw S (S ⊗[R] M) where
  op T := J.baseChangeOp T
  natural {T W} _ _ _ _ f x y := by
    letI := towerAlgebra R S T
    letI := towerAlgebra R S W
    letI := towerScalars R S T
    letI := towerScalars R S W
    apply (iteratedTensorEquiv (R := R) (S := S) W).injective
    rw [iteratedTensorEquiv_natural, J.baseChangeOp_apply, J.baseChangeOp_apply,
      iteratedTensorEquiv_natural, iteratedTensorEquiv_natural, J.natural]

private theorem baseChange_triple (T : Type u) [CommRing T] [Algebra S T]
    (x y z : T ⊗[S] (S ⊗[R] M)) :
    letI := towerAlgebra R S T
    let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
    e ((J.baseChangeLaw S).triple T x y z) =
      J.toQuadraticOperatorLaw.triple T (e x) (e y) (e z) := by
  letI := towerAlgebra R S T
  change iteratedTensorEquiv (R := R) (S := S) T (J.baseChangeOp T (x + z) y -
      J.baseChangeOp T x y - J.baseChangeOp T z y) = _
  rw [map_sub, map_sub, J.baseChangeOp_apply, J.baseChangeOp_apply,
    J.baseChangeOp_apply, map_add]
  rfl

/-- Base change transports the given law across the iterated tensor product. -/
noncomputable def baseChange (S : Type u) [CommRing S] [Algebra R S] :
    QuadraticJordan S (S ⊗[R] M) where
  toQuadraticOperatorLaw := J.baseChangeLaw S
  unit := 1 ⊗ₜ[R] J.unit
  op_unit T _ _ := by
    letI := towerAlgebra R S T
    apply LinearMap.ext
    intro y
    apply (iteratedTensorEquiv (R := R) (S := S) T).injective
    change iteratedTensorEquiv (R := R) (S := S) T (J.baseChangeOp T (1 ⊗ₜ[S] (1 ⊗ₜ[R] J.unit)) y) = _
    rw [J.baseChangeOp_apply, AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      J.op_unit, Module.End.one_apply, Module.End.one_apply]
  fundamental T _ _ x y := by
    letI := towerAlgebra R S T
    apply LinearMap.ext
    intro z
    apply (iteratedTensorEquiv (R := R) (S := S) T).injective
    change iteratedTensorEquiv (R := R) (S := S) T
        (J.baseChangeOp T (J.baseChangeOp T x y) z) =
      iteratedTensorEquiv (R := R) (S := S) T
        (J.baseChangeOp T x (J.baseChangeOp T y (J.baseChangeOp T x z)))
    simp only [baseChangeOp_apply, J.fundamental, Module.End.mul_apply]
  commuting T _ _ x y z := by
    letI := towerAlgebra R S T
    apply (iteratedTensorEquiv (R := R) (S := S) T).injective
    change iteratedTensorEquiv (R := R) (S := S) T
        (J.baseChangeOp T x ((J.baseChangeLaw S).triple T y x z)) =
      iteratedTensorEquiv (R := R) (S := S) T
        ((J.baseChangeLaw S).triple T (J.baseChangeOp T x y) z x)
    rw [J.baseChangeOp_apply, J.baseChange_triple, J.baseChange_triple,
      J.baseChangeOp_apply, J.commuting]

end QuadraticJordan
end BaseChange

section AssociativeExample

variable {A : Type*} [CommRing A] {C : Type*} [Ring C] [Algebra A C]

private def sandwichBilinear : LinearMap.BilinMap A C (Module.End A C) :=
  LinearMap.mk₂ A (fun x z => LinearMap.mulRight A z * LinearMap.mulLeft A x)
    (fun _ _ _ => LinearMap.ext fun _ => by
      simp [Module.End.mul_apply, add_mul])
    (fun _ _ _ => LinearMap.ext fun _ => by
      simp [Module.End.mul_apply, Algebra.smul_mul_assoc])
    (fun _ _ _ => LinearMap.ext fun _ => by
      simp [Module.End.mul_apply, mul_add])
    (fun _ _ _ => LinearMap.ext fun _ => by
      simp [Module.End.mul_apply, Algebra.mul_smul_comm])

private def sandwich : QuadraticMap A C (Module.End A C) :=
  (sandwichBilinear (A := A) (C := C)).toQuadraticMap

private theorem sandwich_apply (x y : C) : sandwich (A := A) x y = x * y * x := rfl

private theorem sandwich_polar (x y z : C) :
    QuadraticMap.polar (sandwich (A := A) (C := C)) x z y = x * y * z + z * y * x := by
  simp only [QuadraticMap.polar, LinearMap.sub_apply, sandwich_apply, add_mul, mul_add]
  abel

variable (R) (C : Type w) [Ring C] [Algebra R C]

private def associativeLaw : QuadraticOperatorLaw R C where
  op S := sandwich (A := S)
  natural {S T} _ _ _ _ f x y := by
    have hmap : f.toLinearMap.rTensor C =
        (Algebra.TensorProduct.map f (AlgHom.id R C)).toLinearMap := by
      apply TensorProduct.ext'
      intro s c
      rfl
    change f.toLinearMap.rTensor C (sandwich (A := S) x y) =
      sandwich (A := T) (f.toLinearMap.rTensor C x) (f.toLinearMap.rTensor C y)
    rw [hmap]
    simp only [sandwich_apply, AlgHom.toLinearMap_apply, map_mul]

/-- The unital quadratic Jordan structure of an associative algebra, in every
characteristic, with the sandwich operator. -/
def associativeJordan : QuadraticJordan R C where
  toQuadraticOperatorLaw := associativeLaw R C
  unit := 1
  op_unit S _ _ := by
    apply LinearMap.ext
    intro y
    change sandwich (A := S) (1 : S ⊗[R] C) y = (1 : Module.End S (S ⊗[R] C)) y
    simp only [sandwich_apply, one_mul, mul_one, Module.End.one_apply]
  fundamental S _ _ x y := by
    apply LinearMap.ext
    intro z
    change sandwich (A := S) (sandwich (A := S) x y) z =
      sandwich (A := S) x (sandwich (A := S) y (sandwich (A := S) x z))
    simp only [sandwich_apply, mul_assoc]
  commuting S _ _ x y z := by
    change sandwich (A := S) x (QuadraticMap.polar (sandwich (A := S)) y z x) =
      QuadraticMap.polar (sandwich (A := S)) (sandwich (A := S) x y) x z
    simp only [sandwich_apply, sandwich_polar, mul_add, add_mul, mul_assoc]

end AssociativeExample

/-- The two presentations match precisely when they have the same unit and
the linear product gives the prescribed quadratic operator on every test algebra. -/
def Presents (L : LinearJordan R M) (J : QuadraticJordan R M) : Prop :=
  J.unit = L.unit ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] (x : S ⊗[R] M),
      J.op S x = operatorOfProduct (L.product.baseChange S) x

namespace Types
set_option linter.checkUnivs false

def QuadraticOperatorLawType :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], Type (max (u + 1) v)

def QuadraticJordanType := QuadraticOperatorLawType.{u, v}

def LinearJordanType :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M], Type v

abbrev QuadraticOperatorLawValue := QuadraticOperatorLaw
abbrev QuadraticJordanValue := QuadraticJordan
abbrev LinearJordanValue := LinearJordan

abbrev HomValue (J : QuadraticJordan R M) (K : QuadraticJordan R N) :=
  QuadraticJordan.Hom J K

def TripleType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticOperatorLaw R M → ∀ (S : Type u) [CommRing S] [Algebra R S],
      (S ⊗[R] M) → (S ⊗[R] M) → (S ⊗[R] M) → S ⊗[R] M

def HomType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N],
    QuadraticJordan R M → QuadraticJordan R N → Type (max v w)

def SquareType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticJordan R M → ∀ (S : Type u) [CommRing S] [Algebra R S],
      (S ⊗[R] M) → S ⊗[R] M

def GroundOpType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticJordan R M → M → Module.End R M

def GroundSquareType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticJordan R M → M → M

def LinearProductType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticJordan R M → ∀ (S : Type u) [CommRing S] [Algebra R S],
      Rˣ → LinearMap.BilinMap S (S ⊗[R] M) (S ⊗[R] M)

def GroundProductType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticJordan R M → Rˣ → LinearMap.BilinMap R M M

def BaseChangeType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticJordan R M → ∀ (S : Type u) [CommRing S] [Algebra R S],
      QuadraticJordan S (S ⊗[R] M)

def AssociativeJordanType :=
  ∀ (R : Type u) [CommRing R] (C : Type w) [Ring C] [Algebra R C], QuadraticJordan R C

def PolarType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M],
    QuadraticJordan R M → ∀ (S : Type u) [CommRing S] [Algebra R S],
      LinearMap.BilinMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M))

def OperatorOfProductType :=
  ∀ {S : Type u} [CommRing S] {P : Type v} [AddCommGroup P] [Module S P],
    LinearMap.BilinMap S P P → P → Module.End S P

def PolarSymmetricType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S] (x z : S ⊗[R] M),
    QuadraticMap.polar (fun a => J.op S a) x z =
      QuadraticMap.polar (fun a => J.op S a) z x

def ProductFormulaType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (d : Rˣ) (x y : S ⊗[R] M),
    J.linearProduct S d x y =
      algebraMap R S (↑d⁻¹ : R) • J.toQuadraticOperatorLaw.triple S x (1 ⊗ₜ[R] J.unit) y

def ProductCommutativeType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (d : Rˣ) (x y : S ⊗[R] M),
    J.linearProduct S d x y = J.linearProduct S d y x

def ProductUnitType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (d : Rˣ) (_ : (↑d : R) = 2) (x : S ⊗[R] M),
    J.linearProduct S d (1 ⊗ₜ[R] J.unit) x = x

def ProductJordanType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (d : Rˣ) (_ : (↑d : R) = 2) (x y : S ⊗[R] M),
    let p := J.linearProduct S d
    p (p x y) (p x x) = p x (p y (p x x))

def GroundProductBaseChangeType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S] (d : Rˣ),
    (J.groundProduct d).baseChange S = J.linearProduct S d

def SquareFormulaType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (d : Rˣ) (_ : (↑d : R) = 2) (x : S ⊗[R] M),
    J.linearProduct S d x x = J.square S x

def OperatorFormulaType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (d : Rˣ) (_ : (↑d : R) = 2) (x : S ⊗[R] M),
    J.op S x = operatorOfProduct (J.linearProduct S d) x

def BaseChangeOpType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra S T] (x y : T ⊗[S] (S ⊗[R] M)),
    letI := towerAlgebra R S T
    let e := iteratedTensorEquiv (R := R) (S := S) (M := M) T
    e ((J.baseChange S).op T x y) = J.op T (e x) (e y)

def ScalarExtensionIdentityType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : LinearMap.BilinMap R M M)
    (_ : ∀ x y, p x y = p y x)
    (_ : ∀ x y, p (p x y) (p x x) = p x (p y (p x x)))
    (d : Rˣ) (_ : (↑d : R) = 2)
    (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] M),
    let q := p.baseChange S
    q (q x y) (q x x) = q x (q y (q x x))

def PresentationEquivalenceType :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (d : Rˣ) (_ : (↑d : R) = 2),
    (∀ J : QuadraticJordan R M, ∃! L : LinearJordan R M, Presents L J) ∧
    (∀ L : LinearJordan R M, ∃! J : QuadraticJordan R M, Presents L J)

def AssociativeFormulaType :=
  ∀ (R : Type u) [CommRing R] (C : Type w) [Ring C] [Algebra R C]
    (S : Type u) [CommRing S] [Algebra R S] (x y z : S ⊗[R] C),
    let J := associativeJordan R C
    J.op S x y = x * y * x ∧ J.toQuadraticOperatorLaw.triple S x y z = x * y * z + z * y * x

def CharacteristicTwoType : Prop :=
  let F := ZMod 2
  let J := associativeJordan F F
  let e : F ⊗[F] F := 1 ⊗ₜ[F] 1
  J.toQuadraticOperatorLaw.triple F e e e = 0 ∧ J.op F e e = e ∧ e ≠ 0

end Types

end Specs.LinearAlgebraicGroups.Albert
