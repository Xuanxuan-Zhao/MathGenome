import MathGenome.Internal.Specs.D05.M15.SymmetricBasis.PerfectPairing
import MathGenome.Internal.Specs.D05.M15.SymmetricDerivation
import MathGenome.Internal.Specs.D05.M15.Symmetrizers
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-! Permanent normalization and contraction bridges, paper.tex:3024–3030.
All operator assertions are on the accepted adjacent-swap quotients. Existence
and uniqueness are obligations, not premises. The algebra bridges specify the
operators without a choice of basis. Averaging alone needs the degree factorial
invertible. The other statements hold in every characteristic and dimension. -/
noncomputable section
namespace Specs.D05.M15.SymmetricBasis.PairingContractions
open Specs.D05.M15.Symmetric Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.SymmetricBasis.PerfectPairing
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Evaluation at v, as a functional on the algebraic dual. -/
abbrev evaluation (v : V) : Module.Dual K (Module.Dual K V) := Module.Dual.eval K V v

/-- Agreement with the previously constructed algebra contraction. -/
def IsContraction (v : V) (p : ℕ)
    (C : symmetricPower K (Module.Dual K V) (p+1) →ₗ[K] symmetricPower K (Module.Dual K V) p) : Prop :=
  ∀ α, powerInclusion (K := K) (V := Module.Dual K V) p (C α) =
    Specs.D05.M15.SymmetricDerivation.contraction (evaluation (K := K) v) (powerInclusion (K := K) (V := Module.Dual K V) (p+1) α)

/-- Agreement with ordinary multiplication by the generator v. -/
def IsMultiplication (v : V) (p : ℕ)
    (M : symmetricPower K V p →ₗ[K] symmetricPower K V (p+1)) : Prop :=
  ∀ x, powerInclusion (K := K) (V := V) (p+1) (M x) = _root_.SymmetricAlgebra.ι K V v * powerInclusion (K := K) (V := V) p x

/-- Ordered contraction D_last ... D_first, including the empty identity. -/
def iterated (vs : List V) :
    _root_.SymmetricAlgebra K (Module.Dual K V) →ₗ[K] _root_.SymmetricAlgebra K (Module.Dual K V) :=
  match vs with
  | [] => LinearMap.id
  | v :: vs => (iterated vs).comp (Specs.D05.M15.SymmetricDerivation.contraction (evaluation (K := K) v))

def operators_exist : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (v : V) (p : ℕ),
  (∃! C, IsContraction (K := K) v p C) ∧ (∃! M, IsMultiplication (K := K) v p M)

/-- The omitted slot is enumerated by swapping it to the front and taking the tail.
This retains every remaining occurrence once, even when values repeat. -/
def contraction_formula : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (v : V) (p : ℕ) (C),
  IsContraction (K := K) v p C → ∀ φ : Fin (p+1) → Module.Dual K V,
  C (elementary K (Module.Dual K V) (p+1) φ) =
    ∑ j, φ j v • elementary K (Module.Dual K V) p
      (fun i => φ (Equiv.swap 0 j i.succ))

def multiplication_formula : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (v : V) (p : ℕ) (M),
  IsMultiplication (K := K) v p M → ∀ x : Fin p → V,
  M (elementary K V p x) = elementary K V (p+1) (Fin.cons v x)

def degree_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (v : V) (α : symmetricPower K (Module.Dual K V) 0),
  Specs.D05.M15.SymmetricDerivation.contraction (evaluation (K := K) v) (powerInclusion (K := K) (V := Module.Dual K V) 0 α) = 0

/-- Ordinary tensor evaluation of two averages is the permanent divided by p!.
The equation is for arbitrary representatives, rather than only elementary ones. -/
def averaged_pairing : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ) (hp : (p.factorial : K) ≠ 0)
  (P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K),
  IsPermanentPairing p P → ∀ (α : TensorPower K p (Module.Dual K V)) (x : TensorPower K p V),
  PiTensorProduct.dualDistrib (R := K) (M := fun _ : Fin p => V)
      (Specs.D05.M15.Symmetrizers.symmetricProjector (K := K) (V := Module.Dual K V) p hp α)
      (Specs.D05.M15.Symmetrizers.symmetricProjector (K := K) (V := V) p hp x) =
    (p.factorial : K)⁻¹ * P (Submodule.Quotient.mk α : symmetricPower K (Module.Dual K V) p)
      ((adjacentRelations K V p).mkQ x)

def adjoint : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (v : V) (p : ℕ) (C) (M),
  IsContraction (K := K) v p C → IsMultiplication (K := K) v p M →
  ∀ (P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K)
    (Q : symmetricPower K (Module.Dual K V) (p+1) →ₗ[K] symmetricPower K V (p+1) →ₗ[K] K),
    IsPermanentPairing p P → IsPermanentPairing (p+1) Q → ∀ α x, P (C α) x = Q α (M x)

/-- The list has the paper's order: its first vector contracts first. -/
def iterated_adjoint : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (vs : List V) (p : ℕ)
  (P : ∀ q, symmetricPower K (Module.Dual K V) q →ₗ[K] symmetricPower K V q →ₗ[K] K),
  (∀ q, IsPermanentPairing q (P q)) →
  ∃ (C : symmetricPower K (Module.Dual K V) (p+vs.length) →ₗ[K] symmetricPower K (Module.Dual K V) p)
    (M : symmetricPower K V p →ₗ[K] symmetricPower K V (p+vs.length)),
    (∀ α, powerInclusion (K := K) (V := Module.Dual K V) p (C α) = iterated (K := K) vs (powerInclusion (K := K) (V := Module.Dual K V) (p+vs.length) α)) ∧
    (∀ x, powerInclusion (K := K) (V := V) (p+vs.length) (M x) =
      (vs.map (_root_.SymmetricAlgebra.ι K V)).prod * powerInclusion (K := K) (V := V) p x) ∧
    ∀ α x, P p (C α) x = P (p+vs.length) α (M x)

def contractions_commute : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (v w : V)
  (α : _root_.SymmetricAlgebra K (Module.Dual K V)),
  Specs.D05.M15.SymmetricDerivation.contraction (evaluation (K := K) v)
      (Specs.D05.M15.SymmetricDerivation.contraction (evaluation w) α) =
  Specs.D05.M15.SymmetricDerivation.contraction (evaluation w)
      (Specs.D05.M15.SymmetricDerivation.contraction (evaluation (K := K) v) α)

/-- Commutation on the actual symmetric powers, in every characteristic. -/
def degree_contractions_commute : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (v w : V) (p : ℕ)
  (Cv Cw : symmetricPower K (Module.Dual K V) (p+1) →ₗ[K] symmetricPower K (Module.Dual K V) p)
  (Cv' Cw' : symmetricPower K (Module.Dual K V) (p+1+1) →ₗ[K] symmetricPower K (Module.Dual K V) (p+1)),
  IsContraction (K := K) v p Cv → IsContraction (K := K) w p Cw →
  IsContraction (K := K) v (p+1) Cv' → IsContraction (K := K) w (p+1) Cw' →
  Cv.comp Cw' = Cw.comp Cv'

end Specs.D05.M15.SymmetricBasis.PairingContractions
