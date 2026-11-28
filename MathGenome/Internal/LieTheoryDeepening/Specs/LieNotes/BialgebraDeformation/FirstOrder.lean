import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

namespace LieNotes.BialgebraDeformation

open TensorProduct
open scoped TensorProduct

universe u v

abbrev D (k : Type u) := DualNumber k

abbrev Extended (k : Type u) (X : Type v) [Field k] [AddCommGroup X] [Module k X] :=
  D k ⊗[k] X

noncomputable section

variable {k : Type u} [Field k]

/-- The map with constant coefficient `p` and infinitesimal coefficient `q`. -/
def jet {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (p q : X →ₗ[k] Y) : Extended k X →ₗ[D k] Extended k Y :=
  p.baseChange (D k) + (DualNumber.eps : D k) • q.baseChange (D k)

/-- Transport a linear map through two specified linear equivalences. -/
def transport {R X Y X' Y' : Type*} [CommSemiring R]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid X'] [Module R X'] [AddCommMonoid Y'] [Module R Y']
    (e : X ≃ₗ[R] X') (f : Y ≃ₗ[R] Y') (p : X →ₗ[R] Y) : X' →ₗ[R] Y' :=
  f.toLinearMap ∘ₗ (p ∘ₗ e.symm.toLinearMap)

abbrev tensorComparison {X Y : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] :=
  AlgebraTensorModule.distribBaseChange k (D k) X Y

/-- Tensor comparison with specified coordinates on the two factors. -/
def tensorCoordinates {X Y X' Y' : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommMonoid X'] [Module (D k) X']
    [AddCommMonoid Y'] [Module (D k) Y']
    (e : Extended k X ≃ₗ[D k] X') (f : Extended k Y ≃ₗ[D k] Y') :
    Extended k (X ⊗[k] Y) ≃ₗ[D k] X' ⊗[D k] Y' :=
  tensorComparison.trans (TensorProduct.congr e f)

abbrev scalarCoordinates (k : Type u) [Field k] :=
  AlgebraTensorModule.rid k (D k) (D k)

/-- Constant and infinitesimal coefficient projections on a scalar extension. -/
def coeff₀ {X : Type*} [AddCommGroup X] [Module k X] : Extended k X →ₗ[k] X :=
  (TensorProduct.lid k X).toLinearMap ∘ₗ
    TensorProduct.map (TrivSqZeroExt.fstHom k k k).toLinearMap LinearMap.id

def coeff₁ {X : Type*} [AddCommGroup X] [Module k X] : Extended k X →ₗ[k] X :=
  (TensorProduct.lid k X).toLinearMap ∘ₗ
    TensorProduct.map (TrivSqZeroExt.sndHom k k) LinearMap.id

section Laws

variable {R : Type*} [CommSemiring R] {V : Type*} [AddCommMonoid V] [Module R V]

abbrev middleFlip (R : Type*) (V : Type*) [CommSemiring R] [AddCommMonoid V] [Module R V] :=
  (TensorProduct.tensorTensorTensorComm R V V V V).toLinearMap

/-- Bialgebra identities on a fixed module with the given multiplication, comultiplication,
unit and counit. The left and right unitors identify scalar tensor factors. -/
structure Laws (m : V ⊗[R] V →ₗ[R] V) (d : V →ₗ[R] V ⊗[R] V)
    (e : R →ₗ[R] V) (c : V →ₗ[R] R) : Prop where
  unit_left : m.comp (TensorProduct.map e LinearMap.id) = (TensorProduct.lid R V).toLinearMap
  unit_right : m.comp (TensorProduct.map LinearMap.id e) = (TensorProduct.rid R V).toLinearMap
  assoc : m.comp (TensorProduct.map m LinearMap.id) =
    m.comp ((TensorProduct.map LinearMap.id m).comp (TensorProduct.assoc R V V V).toLinearMap)
  counit_left : (TensorProduct.lid R V).toLinearMap.comp
      ((TensorProduct.map c LinearMap.id).comp d) = LinearMap.id
  counit_right : (TensorProduct.rid R V).toLinearMap.comp
      ((TensorProduct.map LinearMap.id c).comp d) = LinearMap.id
  coassoc : (TensorProduct.assoc R V V V).toLinearMap.comp
      ((TensorProduct.map d LinearMap.id).comp d) = (TensorProduct.map LinearMap.id d).comp d
  counit_unit : c.comp e = LinearMap.id
  counit_mul : c.comp m = (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map c c)
  comul_unit : d.comp e = (TensorProduct.map e e).comp (TensorProduct.lid R R).symm.toLinearMap
  compatibility : d.comp m = (TensorProduct.map m m).comp
    ((middleFlip R V).comp (TensorProduct.map d d))

end Laws

variable {B : Type v} [Ring B] [Bialgebra k B]

abbrev mulTensor (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :=
  TensorProduct.lift (LinearMap.mul k B)

abbrev comul (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :=
  (Coalgebra.comul : B →ₗ[k] B ⊗[k] B)

abbrev counit (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :=
  (Coalgebra.counit : B →ₗ[k] k)

abbrev unit (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :=
  (Algebra.linearMap k B)

abbrev carrierCoordinates (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :=
  LinearEquiv.refl (D k) (Extended k B)

abbrev squareCoordinates (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :=
  tensorCoordinates (k := k) (X := B) (Y := B) (carrierCoordinates k B) (carrierCoordinates k B)

def deformedMul (f : B ⊗[k] B →ₗ[k] B) :
    Extended k B ⊗[D k] Extended k B →ₗ[D k] Extended k B :=
  transport (squareCoordinates k B) (carrierCoordinates k B) (jet (mulTensor k B) f)

def deformedComul (g : B →ₗ[k] B ⊗[k] B) :
    Extended k B →ₗ[D k] Extended k B ⊗[D k] Extended k B :=
  transport (carrierCoordinates k B) (squareCoordinates k B) (jet (comul k B) g)

def fixedUnit (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :
    D k →ₗ[D k] Extended k B :=
  transport (scalarCoordinates k) (carrierCoordinates k B) (jet (unit k B) 0)

def fixedCounit (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :
    Extended k B →ₗ[D k] D k :=
  transport (carrierCoordinates k B) (scalarCoordinates k) (jet (counit k B) 0)

local notation "m" => mulTensor k B
local notation "d" => comul k B
local notation "c" => counit k B
local notation "ι" => (LinearMap.id : B →ₗ[k] B)
local notation "α" => LinearEquiv.toLinearMap (TensorProduct.assoc k B B B)

/-- The equations in the source on the two first-order cochains. -/
structure Linearized (f : B ⊗[k] B →ₗ[k] B) (g : B →ₗ[k] B ⊗[k] B) : Prop where
  left_unit : ∀ b : B, f (1 ⊗ₜ[k] b) = 0
  right_unit : ∀ b : B, f (b ⊗ₜ[k] 1) = 0
  counit_mul : (c).comp f = 0
  comul_unit : g 1 = 0
  left_counit : (TensorProduct.map c ι).comp g = 0
  right_counit : (TensorProduct.map ι c).comp g = 0
  assoc : ∀ a b z : B, a * f (b ⊗ₜ[k] z) - f ((a * b) ⊗ₜ[k] z) +
    f (a ⊗ₜ[k] (b * z)) - f (a ⊗ₜ[k] b) * z = 0
  coassoc : (α).comp ((TensorProduct.map d ι).comp g + (TensorProduct.map g ι).comp d) -
    (TensorProduct.map ι d).comp g - (TensorProduct.map ι g).comp d = 0
  compatibility : (d).comp f + g.comp m =
    (TensorProduct.map f m + TensorProduct.map m f).comp
      ((middleFlip k B).comp (TensorProduct.map d d)) +
    (TensorProduct.map m m).comp ((middleFlip k B).comp
      (TensorProduct.map g d + TensorProduct.map d g))

structure Deformation (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] where
  f : B ⊗[k] B →ₗ[k] B
  g : B →ₗ[k] B ⊗[k] B
  laws : Laws (deformedMul f) (deformedComul g) (fixedUnit k B) (fixedCounit k B)

abbrev Change (k : Type u) (B : Type v) [Field k] [Ring B] [Bialgebra k B] :=
  Extended k B ≃ₗ[D k] Extended k B

def Allowed (T : Change k B) : Prop :=
  (∀ x : Extended k B, coeff₀ (T x) = coeff₀ x) ∧
  T.toLinearMap.comp (fixedUnit k B) = fixedUnit k B ∧
  (fixedCounit k B).comp T.toLinearMap = fixedCounit k B

def pullMul (T : Change k B) (f : B ⊗[k] B →ₗ[k] B) :=
  T.symm.toLinearMap.comp ((deformedMul f).comp (TensorProduct.map T.toLinearMap T.toLinearMap))

def pullComul (T : Change k B) (g : B →ₗ[k] B ⊗[k] B) :=
  (TensorProduct.map T.symm.toLinearMap T.symm.toLinearMap).comp
    ((deformedComul g).comp T.toLinearMap)

def Equivalent (x y : Deformation k B) : Prop :=
  ∃ T : Change k B, Allowed T ∧
    pullMul T x.f = deformedMul y.f ∧ pullComul T x.g = deformedComul y.g

def NormalizedChange (u : B →ₗ[k] B) : Prop :=
  u 1 = 0 ∧ (c).comp u = 0

def tensorDerivative (u : B →ₗ[k] B) : B ⊗[k] B →ₗ[k] B ⊗[k] B :=
  TensorProduct.map u ι + TensorProduct.map ι u

def changedMul (u : B →ₗ[k] B) (f : B ⊗[k] B →ₗ[k] B) :=
  f + (m).comp (tensorDerivative u) - u.comp m

def changedComul (u : B →ₗ[k] B) (g : B →ₗ[k] B ⊗[k] B) :=
  g + (d).comp u - (tensorDerivative u).comp d

namespace Expected

def laws_iff := ∀ {k : Type u} {B : Type v} [Field k] [CharZero k] [Ring B] [Bialgebra k B]
    (f : B ⊗[k] B →ₗ[k] B) (g : B →ₗ[k] B ⊗[k] B),
  Laws (deformedMul f) (deformedComul g) (fixedUnit k B) (fixedCounit k B) ↔ Linearized f g

def allowed_iff := ∀ {k : Type u} {B : Type v} [Field k] [CharZero k] [Ring B] [Bialgebra k B]
    (T : Change k B),
  Allowed T ↔ ∃! u : B →ₗ[k] B, NormalizedChange u ∧ T.toLinearMap = jet LinearMap.id u

def coordinate_change := ∀ {k : Type u} {B : Type v} [Field k] [CharZero k]
    [Ring B] [Bialgebra k B] (u : B →ₗ[k] B),
  ∃ T : Change k B, T.toLinearMap = jet LinearMap.id u ∧
    T.symm.toLinearMap = jet LinearMap.id (-u) ∧ (Allowed T ↔ NormalizedChange u)

def coefficient_decomposition := ∀ {k : Type u} {X : Type v} [Field k] [AddCommGroup X]
    [Module k X] (x : Extended k X),
  x = (1 : D k) ⊗ₜ[k] coeff₀ x + (DualNumber.eps : D k) ⊗ₜ[k] coeff₁ x

def pullback := ∀ {k : Type u} {B : Type v} [Field k] [CharZero k] [Ring B] [Bialgebra k B]
    (T : Change k B) (u : B →ₗ[k] B), T.toLinearMap = jet LinearMap.id u →
    ∀ (f : B ⊗[k] B →ₗ[k] B) (g : B →ₗ[k] B ⊗[k] B),
    pullMul T f = deformedMul (changedMul u f) ∧
    pullComul T g = deformedComul (changedComul u g)

def equivalent_iff := ∀ {k : Type u} {B : Type v} [Field k] [CharZero k] [Ring B] [Bialgebra k B]
    (x y : Deformation k B),
    Equivalent x y ↔ ∃ u : B →ₗ[k] B, NormalizedChange u ∧
      y.f = changedMul u x.f ∧ y.g = changedComul u x.g

end Expected

end

end LieNotes.BialgebraDeformation
