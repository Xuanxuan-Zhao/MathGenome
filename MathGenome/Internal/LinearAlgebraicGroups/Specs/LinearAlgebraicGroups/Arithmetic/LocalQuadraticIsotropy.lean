import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Quaternion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Norm.Defs

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy

open LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSpinGeneration (IsIsotropic reflection)
open LinearAlgebraicGroups.Albert.SpinSpecification (ScalarClifford spinUnits IsVectorAction)
open scoped TensorProduct

universe u v

/-- The pure norm of the quaternion algebra with generator squares `a` and `b`. -/
def pureNorm {F : Type u} [Field F] (a b x y z : F) : F :=
  -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2

/-- An anisotropic pure quaternion norm over a local field omits exactly the
class of minus one. Scaling gives the corresponding assertion for every
anisotropic ternary form. -/
def PureNormValues : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ a b : F, (∀ x y z, pureNorm a b x y z = 0 → x = 0 ∧ y = 0 ∧ z = 0) →
      ∀ t : F, t ≠ 0 → ((∃ x y z, pureNorm a b x y z = t) ↔ ¬ IsSquare (-t))

/-- Exact nonzero value set of a diagonal anisotropic ternary form. -/
def TernaryValues : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ a b c : F, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      (∀ x y z : F, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 →
        x = 0 ∧ y = 0 ∧ z = 0) →
      ∀ t : F, t ≠ 0 →
        ((∃ x y z : F, a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = t) ↔
          ¬ IsSquare (-(t / (a * b / c))))

/-- An anisotropic ternary form is a scaled pure division quaternion norm and
represents every nonzero square class except the class of the negative scale. -/
def TernaryFormValues : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (q : QuadraticForm F V), Module.finrank F V = 3 → ¬ IsIsotropic q →
      ∃ (s a b : F), s ≠ 0 ∧
        let D := QuaternionAlgebra F a 0 b
        ∃ hD : _root_.Specs.RM03.CSA.isCentralSimple F D,
          (∀ p : D, p ≠ 0 → IsUnit p) ∧
          (∃ e : V ≃ₗ[F] (QuaternionAlgebra.reₗ a 0 b).ker, ∀ x : V,
            q x = s * _root_.Specs.RM03.CSA.reducedNorm hD (e x).val) ∧
          ∀ t : F, t ≠ 0 → ((∃ x : V, q x = t) ↔ ¬ IsSquare (-(t / s)))

/-- A diagonal anisotropic binary form in characteristic different from two is
a scalar multiple of the norm of a separable quadratic field extension. -/
def BinaryExtensionNorm : Prop :=
  ∀ {F : Type u} [Field F], (2 : F) ≠ 0 →
    ∀ a b : F, a ≠ 0 →
      (∀ x y : F, a * x ^ 2 + b * y ^ 2 = 0 → x = 0 ∧ y = 0) →
      ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : Algebra.IsSeparable F E),
        Module.finrank F E = 2 ∧
          ∃ e : (F × F) ≃ₗ[F] E, ∀ x y : F,
            a * x ^ 2 + b * y ^ 2 = a * Algebra.norm F (e (x, y))

/-- The quadratic norm `x² - d y²` represents one and a nonsquare. This
also computes two different square classes for its nonzero scalar multiples. -/
def BinaryNormClasses : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ d : F, ¬ IsSquare d → ∃ x y : F, ¬ IsSquare (x ^ 2 - d * y ^ 2)

/-- An anisotropic binary form is a scaled quadratic field norm and has two
nonzero represented values belonging to different square classes. -/
def BinaryFormNormClasses : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (q : QuadraticForm F V), Module.finrank F V = 2 → ¬ IsIsotropic q →
      (∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : Algebra.IsSeparable F E),
        Module.finrank F E = 2 ∧ ∃ a : F, a ≠ 0 ∧
          ∃ e : V ≃ₗ[F] E, ∀ x : V, q x = a * Algebra.norm F (e x)) ∧
      ∃ x y : V, q x ≠ 0 ∧ q y ≠ 0 ∧ ¬ IsSquare (q y / q x)

/-- The local isotropy bound, including dyadic local fields. -/
def LocalIsotropy : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
    ∀ {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (q : QuadraticForm F V), LinearMap.ker q.polarBilin = ⊥ →
      5 ≤ Module.finrank F V → IsIsotropic q

section Spin

variable {F : Type u} {V : Type v} [AddCommGroup V]

/-- Determinant-one linear isometries of the given quadratic form. -/
def specialOrthogonal [CommRing F] [Module F V] (q : QuadraticForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := { g | (∀ x, q (g x) = q x) ∧ LinearEquiv.det g = 1 }
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change (∀ x, q (g (h x)) = q x) ∧ LinearEquiv.det (g * h) = 1
    exact ⟨fun x => (hg.1 (h x)).trans (hh.1 x), by
      rw [map_mul, hg.2, hh.2, mul_one]⟩
  inv_mem' {g} hg := by
    change (∀ x, q (g.symm x) = q x) ∧ LinearEquiv.det g⁻¹ = 1
    exact ⟨fun x => by simpa using (hg.1 (g.symm x)).symm, by
      rw [map_inv, hg.2, inv_one]⟩

variable [Field F] [Module F V]
abbrev SquareClasses (F : Type u) [Field F] := Fˣ ⧸ Subgroup.square Fˣ

abbrev ReflectionVector (q : QuadraticForm F V) := {w : V // q w ≠ 0}

def reflectionWord (q : QuadraticForm F V) (l : List (ReflectionVector q)) (x : V) : V :=
  l.foldr (fun w z => reflection q w.val z) x

def reflectionNorm (q : QuadraticForm F V) (l : List (ReflectionVector q)) : Fˣ :=
  (l.map fun w => Units.mk0 (q w.val) w.prop).prod

/-- A rational point of the Clifford spin functor inducing the given isometry. -/
def HasSpinLift (q : QuadraticForm F V) (g : specialOrthogonal q) : Prop :=
  ∃ a : (ScalarClifford q F)ˣ,
    a ∈ spinUnits q F ∧ IsVectorAction q F a (g.val.baseChange F F V V)

/-- Reflection words define the spinor norm and its kernel is the image of spin. -/
def IsSpinorNorm (q : QuadraticForm F V)
    (ν : specialOrthogonal q →* SquareClasses F) : Prop :=
  (∀ g : specialOrthogonal q, ∃ l : List (ReflectionVector q), Even l.length ∧
    ∀ x, g.val x = reflectionWord q l x) ∧
  (∀ (g : specialOrthogonal q) (l : List (ReflectionVector q)),
    Even l.length → (∀ x, g.val x = reflectionWord q l x) →
    ν g = QuotientGroup.mk' (Subgroup.square Fˣ) (reflectionNorm q l)) ∧
  ∀ g, ν g = 1 ↔ HasSpinLift q g

def SpinorNorm : Prop :=
  ∀ {F : Type u} [Field F] [CharZero F]
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticForm F V), LinearMap.ker q.polarBilin = ⊥ →
    ∃ ν : specialOrthogonal q →* SquareClasses F, IsSpinorNorm q ν

end Spin

/-- At a characteristic-zero finite place of odd residue characteristic,
the scalar extension of a determinant-one isometry of a unimodular lattice
has spinor norm represented by a unit of the valuation ring. -/
def IntegralUnitClass : Prop :=
  ∀ {F : Type u} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    let R := LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification.Integers F
    ∀ h₂ : IsUnit (2 : R), letI : Invertible (2 : R) := h₂.invertible
    ∀ {L : Type v} [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]
      (q : QuadraticForm R L), Function.Bijective q.polarBilin →
      ∀ g : specialOrthogonal q, ∃ gF : specialOrthogonal (q.baseChange F),
        (∀ x : L, gF.val (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] g.val x) ∧
        (∃ ν, IsSpinorNorm (q.baseChange F) ν) ∧
        ∀ ν : specialOrthogonal (q.baseChange F) →* SquareClasses F,
          IsSpinorNorm (q.baseChange F) ν →
            ∃ u : Rˣ, ν gF =
              QuotientGroup.mk' (Subgroup.square Fˣ) (Units.map (algebraMap R F).toMonoidHom u)

end LinearAlgebraicGroups.Specs.Arithmetic.LocalQuadraticIsotropy
