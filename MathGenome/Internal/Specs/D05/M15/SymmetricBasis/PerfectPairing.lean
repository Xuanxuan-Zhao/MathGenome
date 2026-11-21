import MathGenome.Internal.Specs.D05.M15.SymmetricBasis
import MathGenome.Internal.Specs.D05.M07.DualBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The permanent pairing on the actual adjacent-swap quotients, with ordinary
monomial normalization. No factorial assumption is used for its existence or
its values. Perfectness requires precisely invertibility of the degree factorial.
The statements include nullary products and the positive-characteristic failure. -/
noncomputable section
open scoped Classical
namespace Specs.D05.M15.SymmetricBasis.PerfectPairing
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis
open D05.Foundations
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Row functionals and column vectors; the permanent has no signs. -/
def permanent {p : ℕ} (φ : Fin p → Module.Dual K V) (x : Fin p → V) : K :=
  ∑ σ : Equiv.Perm (Fin p), ∏ i, φ i (x (σ i))

/-- This fixes the pairing on a spanning family on each side. -/
def IsPermanentPairing (p : ℕ)
    (P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K) : Prop :=
  ∀ φ x, P (elementary K (Module.Dual K V) p φ) (elementary K V p x) = permanent φ x

/-- Both induced maps to algebraic duals are isomorphisms. -/
def IsPerfect {A B : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (P : A →ₗ[K] B →ₗ[K] K) : Prop :=
  Function.Bijective P ∧ Function.Bijective P.flip

def exists_unique_pairing : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ),
  ∃! P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K,
    IsPermanentPairing p P

/-- Multilinearity and symmetry in the two lists before descent. -/
def permanent_multilinear_symmetric : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ),
  (∀ x : Fin p → V, ∃ F : MultilinearMap K (fun _ : Fin p => Module.Dual K V) K,
    ∀ φ, F φ = permanent φ x) ∧
  (∀ φ : Fin p → Module.Dual K V, ∃ F : MultilinearMap K (fun _ : Fin p => V) K,
    ∀ x, F x = permanent φ x) ∧
  (∀ (φ : Fin p → Module.Dual K V) (x : Fin p → V) (σ τ : Equiv.Perm (Fin p)), permanent (φ ∘ σ) (x ∘ τ) = permanent φ x)

/-- The inclusion conditions identify the ordinary quotient monomials, without
assuming a pairing certificate or any coordinate decomposition. -/
def monomial_values : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
  (b : Module.Basis (Fin n) K V) (p : ℕ)
  (P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K),
  IsPermanentPairing p P → ∀ (a c : NonnegativeTuples n p)
    (α : symmetricPower K (Module.Dual K V) p) (x : symmetricPower K V p),
    powerInclusion (K := K) (V := Module.Dual K V) p α = ∏ i, (_root_.SymmetricAlgebra.ι K (Module.Dual K V) (b.dualBasis i)) ^ a.val i →
    powerInclusion (K := K) (V := V) p x = ∏ i, (_root_.SymmetricAlgebra.ι K V (b i)) ^ c.val i →
    P α x = if a = c then ((∏ i, (a.val i).factorial : ℕ) : K) else 0

def diagonal_isUnit : Prop := ∀ {K : Type u} [Field K] (n p : ℕ),
  IsUnit (p.factorial : K) → ∀ a : NonnegativeTuples n p,
    IsUnit ((∏ i, (a.val i).factorial : ℕ) : K)

def perfect : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (p : ℕ),
  IsUnit (p.factorial : K) → ∀ P, IsPermanentPairing (K := K) (V := V) p P → IsPerfect P

/-- Under any scalar identifications sending the nullary elementary tensor to 1,
the nullary pairing is scalar multiplication. -/
def degree_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V]
  (P : symmetricPower K (Module.Dual K V) 0 →ₗ[K] symmetricPower K V 0 →ₗ[K] K),
  IsPermanentPairing 0 P →
  ∀ (E : symmetricPower K (Module.Dual K V) 0 ≃ₗ[K] K)
    (F : symmetricPower K V 0 ≃ₗ[K] K),
    (∀ φ, E (elementary K (Module.Dual K V) 0 φ) = 1) →
    (∀ x, F (elementary K V 0 x) = 1) → ∀ α x, P α x = E α * F x

/-- Actual scalar identifications in degree zero, including the zero space. -/
def degree_zero_scalar : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V]
  (P : symmetricPower K (Module.Dual K V) 0 →ₗ[K] symmetricPower K V 0 →ₗ[K] K),
  IsPermanentPairing 0 P →
  ∃ (E : symmetricPower K (Module.Dual K V) 0 ≃ₗ[K] K)
    (F : symmetricPower K V 0 ≃ₗ[K] K),
    (∀ φ, E (elementary K (Module.Dual K V) 0 φ) = 1) ∧
    (∀ x, F (elementary K V 0 x) = 1) ∧ ∀ α x, P α x = E α * F x

def characteristic_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (p : ℕ) (P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K),
  IsPermanentPairing p P → IsPerfect P

/-- In dimension one and degree equal to positive characteristic, the permanent
pairing is zero on the two unit monomials and is not injective. -/
def characteristic_failure : Prop := ∀ {K : Type u} [Field K] (ℓ : ℕ) [CharP K ℓ],
  0 < ℓ → ∀ (P : symmetricPower K (Module.Dual K K) ℓ →ₗ[K] symmetricPower K K ℓ →ₗ[K] K),
    IsPermanentPairing ℓ P →
    P (elementary K (Module.Dual K K) ℓ (fun _ => LinearMap.id))
      (elementary K K ℓ (fun _ => 1)) = 0 ∧ ¬Function.Injective P

end Specs.D05.M15.SymmetricBasis.PerfectPairing
