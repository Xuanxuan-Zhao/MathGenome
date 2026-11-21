import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Enveloping
import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! The restricted-power axioms and restricted enveloping algebra from LA-J09. -/

open scoped BigOperators

namespace Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary

universe u v

variable {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]

/-- Coefficient of `t^j` in `(ad (t x + y))^n x`. The recurrence applies
one additional adjoint and separates its constant and linear terms. -/
def jacobsonCoeffValue (x y : G) : ℕ → ℕ → G
  | 0, 0 => x
  | 0, _ + 1 => 0
  | n + 1, 0 => ⁅y, jacobsonCoeffValue x y n 0⁆
  | n + 1, j + 1 => ⁅x, jacobsonCoeffValue x y n j⁆ + ⁅y, jacobsonCoeffValue x y n (j + 1)⁆

def jacobsonCoeffType :=
  ∀ {G : Type v} [LieRing G], G → G → ℕ → ℕ → G

/-- The sum of the Jacobson terms `s_i(x,y)` for `1 ≤ i < p`.
The coefficient of `t^(i-1)` is `i s_i(x,y)`. -/
def jacobsonCorrectionValue (k : Type u) [Field k]
    {G : Type v} [LieRing G] [LieAlgebra k G] (p : ℕ) (x y : G) : G :=
  ∑ j ∈ Finset.range (p - 1), (((j + 1 : ℕ) : k)⁻¹) • jacobsonCoeffValue x y (p - 1) j

def jacobsonCorrectionType :=
  ∀ (k : Type u) [Field k] {G : Type v} [LieRing G] [LieAlgebra k G], ℕ → G → G → G

/-- The three restricted Lie algebra axioms for the specified operation in
positive characteristic. The adjoint powers are powers under composition. -/
def isRestrictedPowerValue (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] (power : G → G) : Prop :=
  (∀ x, LieAlgebra.ad k G (power x) = (LieAlgebra.ad k G x) ^ p) ∧
  (∀ (a : k) x, power (a • x) = a ^ p • power x) ∧
  (∀ x y, power (x + y) = power x + power y + jacobsonCorrectionValue k p x y)

def isRestrictedPowerType :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G], (G → G) → Prop

def restrictedPowerType :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    (G : Type v) [LieRing G] [LieAlgebra k G], Type v

/-- A Lie algebra's additional operation, with the three axioms. -/
def restrictedPowerValue (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    (G : Type v) [LieRing G] [LieAlgebra k G] : Type v :=
  {power : G → G // isRestrictedPowerValue k p power}

def derivationPowerType :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G],
    ℕ → LieDerivation k G G → Module.End k G

def derivationPowerValue (n : ℕ) (D : LieDerivation k G G) : Module.End k G :=
  (D : Module.End k G) ^ n

def derivationPower_isDerivationType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] (D : LieDerivation k G G) (x y : G),
    derivationPowerValue p D ⁅x, y⁆ =
      ⁅derivationPowerValue p D x, y⁆ + ⁅x, derivationPowerValue p D y⁆

def derivations_admit_restrictedPowerType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G],
    ∃ power : restrictedPowerValue k p (LieDerivation k G G),
      ∀ D, ((power.val D : LieDerivation k G G) : Module.End k G) = derivationPowerValue p D

/-- The composition power of an associative-algebra derivation satisfies the
Leibniz rule for multiplication. This covers the truncated polynomial algebra
used to define the Witt algebra in LA-J09. -/
def associativeDerivationPower_isDerivationType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {A : Type v} [CommRing A] [Algebra k A] (D : Derivation k A A) (a b : A),
    ((D : Module.End k A) ^ p) (a * b) =
      a * ((D : Module.End k A) ^ p) b + b * ((D : Module.End k A) ^ p) a

/-- On the actual associative-algebra derivations with their commutator Lie
bracket, the restricted power acts as p-fold composition. -/
def associativeDerivations_admit_restrictedPowerType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {A : Type v} [CommRing A] [Algebra k A],
    ∃ power : restrictedPowerValue k p (Derivation k A A),
      ∀ D, ((power.val D : Derivation k A A) : Module.End k A) = (D : Module.End k A) ^ p

section Enveloping

open _root_.Shared.Lie

variable (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
  {G : Type v} [LieRing G] [LieAlgebra k G]

/-- The additional relations are imposed in the already constructed ordinary enveloping algebra. -/
def restrictedRelationsValue (power : restrictedPowerValue k p G) : Ideal (U k G) :=
  (TwoSidedIdeal.span (Set.range fun x : G =>
    (inclusion k G x) ^ p - inclusion k G (power.val x))).asIdeal

instance (power : restrictedPowerValue k p G) :
    (restrictedRelationsValue k p power).IsTwoSided := by
  unfold restrictedRelationsValue
  infer_instance

def restrictedRelationsType :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G], restrictedPowerValue k p G → Ideal (U k G)

abbrev restrictedEnvelopingValue (power : restrictedPowerValue k p G) :=
  U k G ⧸ restrictedRelationsValue k p power

def restrictedEnvelopingType :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G], restrictedPowerValue k p G → Type (max u v)

def quotientMapValue (power : restrictedPowerValue k p G) :
    U k G →ₐ[k] restrictedEnvelopingValue k p power :=
  Ideal.Quotient.mkₐ k (restrictedRelationsValue k p power)

def quotientMapType :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] (power : restrictedPowerValue k p G),
    U k G →ₐ[k] restrictedEnvelopingValue k p power

def quotientMap_specType : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] (power : restrictedPowerValue k p G),
    Function.Surjective (quotientMapValue k p power) ∧
    (∀ a, quotientMapValue k p power a = 0 ↔ a ∈ restrictedRelationsValue k p power) ∧
    (∀ x : G, (quotientMapValue k p power (inclusion k G x)) ^ p =
      quotientMapValue k p power (inclusion k G (power.val x)))

end Enveloping
end Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
