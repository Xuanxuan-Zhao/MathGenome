import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.AutomorphismScheme

/-! Intrinsic cubic laws of an Albert algebra, over arbitrary commutative base rings. -/

namespace LinearAlgebraicGroups.Albert.IntrinsicCubicSpecification

open TensorProduct
open SplitSpecification CubicSpecification LowerRankSpecification
open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open scoped DualNumber

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A scalar-valued polynomial law on the module, in its functorial formulation. -/
structure ScalarLaw (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] where
  eval (S : Type u) [CommRing S] [Algebra R S] : S ⊗[R] M → S
  natural {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (x : S ⊗[R] M) :
    eval T (f.toLinearMap.rTensor M x) = f (eval S x)

/-- The three coefficients of the characteristic identity. -/
structure Coefficients (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] where
  trace : ScalarLaw R M
  quadraticTrace : ScalarLaw R M
  norm : ScalarLaw R M

variable (J : ParaQuadratic R M) (F : Coefficients R M)
variable (S : Type u) [CommRing S] [Algebra R S]

def IsCharacteristic : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] (x : S ⊗[R] M),
    J.op S x x = F.trace.eval S x • J.op S x (1 ⊗ₜ[R] J.unit) -
      F.quadraticTrace.eval S x • x + F.norm.eval S x • (1 ⊗ₜ[R] J.unit)

def adjoint (x : S ⊗[R] M) : S ⊗[R] M :=
  J.op S x (1 ⊗ₜ[R] J.unit) - F.trace.eval S x • x +
    F.quadraticTrace.eval S x • (1 ⊗ₜ[R] J.unit)

def pairing (x y : S ⊗[R] M) : S :=
  F.trace.eval S x * F.trace.eval S y -
    (F.quadraticTrace.eval S (x + y) - F.quadraticTrace.eval S x - F.quadraticTrace.eval S y)

/-- A split coordinate chart for the operator on a test ring. -/
structure SplitChart where
  coordinates : S ⊗[R] M ≃ₗ[S] SplitRank.octonion.Model S
  unit : coordinates (1 ⊗ₜ[R] J.unit) = cubicUnit
  op (x y : S ⊗[R] M) :
    coordinates (J.op S x y) = QuadraticOperatorSpecification.applyOperator
      (SplitRank.norm S .octonion) (untwisted S) (coordinates x) (coordinates y)

def AgreesOnCharts : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] (c : SplitChart J S) (x : S ⊗[R] M),
    F.trace.eval S x = linearTrace (SplitRank.norm S .octonion) (untwisted S) (c.coordinates x) ∧
    F.quadraticTrace.eval S x = quadraticTrace (SplitRank.norm S .octonion) (untwisted S) (c.coordinates x) ∧
    F.norm.eval S x = cubicNorm (SplitRank.norm S .octonion) (untwisted S) (c.coordinates x)

/-- Coefficient laws exist uniquely and recover the split laws in every chart. -/
def IntrinsicCoefficientsType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M), IsAlbert J →
      (∃! F : Coefficients R M, IsCharacteristic J F) ∧
      ∀ F : Coefficients R M, IsCharacteristic J F → AgreesOnCharts J F

/-- The polar coefficients and the recovered operator, on every test algebra. -/
def CubicRecoveryType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M) (F : Coefficients R M), IsAlbert J → IsCharacteristic J F →
    ∀ (S : Type u) [CommRing S] [Algebra R S],
      (∃ T : LinearMap.BilinForm S (S ⊗[R] M), T.IsPerfPair ∧ ∀ x y, T x y = pairing F S x y) ∧
      F.norm.eval S (1 ⊗ₜ[R] J.unit) = 1 ∧
      adjoint J F S (1 ⊗ₜ[R] J.unit) = (1 ⊗ₜ[R] J.unit) ∧
      (∀ x, F.trace.eval S x = pairing F S x (1 ⊗ₜ[R] J.unit)) ∧
      (∀ x, F.quadraticTrace.eval S x = F.trace.eval S (adjoint J F S x)) ∧
      (∀ x y r, F.norm.eval S (x + r • y) = F.norm.eval S x +
        r * pairing F S (adjoint J F S x) y +
        r ^ 2 * pairing F S (adjoint J F S y) x + r ^ 3 * F.norm.eval S y) ∧
      (∀ x y, J.op S x y = pairing F S x y • x -
        (adjoint J F S (adjoint J F S x + y) - adjoint J F S (adjoint J F S x) - adjoint J F S y))

/-- Preservation of the distinguished unit and the norm as a polynomial law. -/
def PreservesNorm (g : Module.End R M) : Prop :=
  g J.unit = J.unit ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] (x : S ⊗[R] M),
      F.norm.eval S (g.baseChange S x) = F.norm.eval S x

def AutomorphismType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : ParaQuadratic R M) (F : Coefficients R M), IsAlbert J → IsCharacteristic J F →
    ∀ g : M ≃ₗ[R] M, J.IsIso J g ↔ PreservesNorm J F g.toLinearMap

open private towerScalars iteratedTensorEquiv_natural from
  MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan

/-- The same scalar law on test algebras over a new base ring. -/
noncomputable def ScalarLaw.changeScalars (L : ScalarLaw R M) (S : Type u) [CommRing S] [Algebra R S] :
    ScalarLaw S (S ⊗[R] M) where
  eval T _ _ x :=
    letI := towerAlgebra R S T
    L.eval T (iteratedTensorEquiv (R := R) (S := S) (M := M) T x)
  natural {B C} _ _ _ _ f x := by
    let := towerAlgebra R S B
    let := towerAlgebra R S C
    let := towerScalars R S B
    let := towerScalars R S C
    change L.eval C (iteratedTensorEquiv (R := R) (S := S) (M := M) C
      (f.toLinearMap.rTensor (S ⊗[R] M) x)) = _
    rw [iteratedTensorEquiv_natural, L.natural]
    rfl

/-- Transport of all three scalar laws along scalar extension. -/
noncomputable def Coefficients.changeScalars (F : Coefficients R M)
    (S : Type u) [CommRing S] [Algebra R S] : Coefficients S (S ⊗[R] M) :=
  ⟨F.trace.changeScalars S, F.quadraticTrace.changeScalars S, F.norm.changeScalars S⟩

/-- Equality of the two stabilizers on every scalar algebra. -/
def NormStabilizerType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (F : Coefficients R M),
    IsAlbert (ParaQuadratic.ofJordan J) → IsCharacteristic (ParaQuadratic.ofJordan J) F →
    ∀ (S : Type u) [CommRing S] [Algebra R S] (g : (Module.End S (S ⊗[R] M))ˣ),
      g ∈ quadraticStabilizer J S ↔ PreservesNorm ((ParaQuadratic.ofJordan J).baseChange S)
        (F.changeScalars S) g.val

/-- The unit equation and the vanishing of the linear coefficient of the norm,
expressed on every test algebra so it is a coefficientwise condition. -/
def NormTangentEquations (D : Module.End R M) : Prop :=
  D J.unit = 0 ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] (x : S ⊗[R] M),
      pairing F S (adjoint J F S x) (D.baseChange S x) = 0

def TangentEquationsType : Prop :=
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (J : QuadraticJordan R M) (F : Coefficients R M),
    IsAlbert (ParaQuadratic.ofJordan J) → IsCharacteristic (ParaQuadratic.ofJordan J) F →
    ∀ D : Module.End R M,
      IsQuadraticDerivation J D ↔ NormTangentEquations (ParaQuadratic.ofJordan J) F D

end LinearAlgebraicGroups.Albert.IntrinsicCubicSpecification
