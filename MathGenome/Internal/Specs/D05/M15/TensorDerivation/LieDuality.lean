import MathGenome.Internal.Specs.D05.M15.TensorDerivation
import MathGenome.Internal.Specs.D05.M15.ExteriorDerivation
import MathGenome.Internal.Specs.D05.M15.SymmetricDerivation
import MathGenome.Internal.Specs.D05.M15.TensorPairing
import MathGenome.Internal.Specs.D05.M15.ExteriorPairing
import MathGenome.Internal.Specs.D05.M15.SymmetricBasis.PerfectPairing

/-! The induced Lie action and its algebraic duality, paper.tex:3075–3079.
No finiteness or characteristic assumption is needed. We use the actual
homogeneous exterior submodules and adjacent-swap symmetric quotients.
The degree operators in the two duality statements are constructed, with their
inclusion formulas, rather than assumed. Permanent pairing existence and its
separate perfection theorem retain their upstream meanings and hypotheses. -/
namespace Specs.D05.M15.TensorDerivation.LieDuality
universe u v

open Specs.D05.M15

def tensor_add : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A B : V →ₗ[K] V),
  TensorDerivation.induced (A + B) = TensorDerivation.induced A + TensorDerivation.induced B

def tensor_smul : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (a : K) (A : V →ₗ[K] V),
  TensorDerivation.induced (a • A) = a • TensorDerivation.induced A

def tensor_commutator : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A B : V →ₗ[K] V),
  (TensorDerivation.induced A).comp (TensorDerivation.induced B) -
    (TensorDerivation.induced B).comp (TensorDerivation.induced A) =
      TensorDerivation.induced (A.comp B - B.comp A)

def tensor_power_commutator : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A B : V →ₗ[K] V) (p : ℕ)
  (x : TensorPower K p V),
  TensorDerivation.onPower A p (TensorDerivation.onPower B p x) -
    TensorDerivation.onPower B p (TensorDerivation.onPower A p x) =
      TensorDerivation.onPower (A.comp B - B.comp A) p x

/-- Canonical finite tensor evaluation, with arbitrary-dimensional V, including p=0. -/
def tensor_duality : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A : V →ₗ[K] V) (p : ℕ)
  (α : TensorPower K p (Module.Dual K V)) (x : TensorPower K p V),
  TensorPairing.finite_evaluation_value K (Fin p) (fun _ => V)
    (TensorDerivation.onPower A.dualMap p α) x =
  TensorPairing.finite_evaluation_value K (Fin p) (fun _ => V)
    α (TensorDerivation.onPower A p x)

def tensor_degree_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A : V →ₗ[K] V),
  TensorDerivation.onPower A 0 = 0

def exterior_add : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A B : V →ₗ[K] V),
  ExteriorDerivation.induced (A + B) = ExteriorDerivation.induced A + ExteriorDerivation.induced B

def exterior_smul : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (a : K) (A : V →ₗ[K] V),
  ExteriorDerivation.induced (a • A) = a • ExteriorDerivation.induced A

def exterior_commutator : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A B : V →ₗ[K] V),
  (ExteriorDerivation.induced A).comp (ExteriorDerivation.induced B) -
    (ExteriorDerivation.induced B).comp (ExteriorDerivation.induced A) =
      ExteriorDerivation.induced (A.comp B - B.comp A)

/-- Both actual degree restrictions, together with determinant-pairing duality. -/
def exterior_duality : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A : V →ₗ[K] V) (p : ℕ),
  ∃ (D : (⋀[K]^p V) →ₗ[K] (⋀[K]^p V))
    (E : (⋀[K]^p (Module.Dual K V)) →ₗ[K] (⋀[K]^p (Module.Dual K V))),
    (∀ x, (D x : _root_.ExteriorAlgebra K V) = ExteriorDerivation.induced A x) ∧
    (∀ α, (E α : _root_.ExteriorAlgebra K (Module.Dual K V)) =
      ExteriorDerivation.induced A.dualMap α) ∧
    ∀ α x, ExteriorPairing.pairing_value K V p (E α) x =
      ExteriorPairing.pairing_value K V p α (D x)

def symmetric_add : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A B : V →ₗ[K] V),
  SymmetricDerivation.induced (A + B) = SymmetricDerivation.induced A + SymmetricDerivation.induced B

def symmetric_smul : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (a : K) (A : V →ₗ[K] V),
  SymmetricDerivation.induced (a • A) = a • SymmetricDerivation.induced A

def symmetric_commutator : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A B : V →ₗ[K] V),
  (SymmetricDerivation.induced A).comp (SymmetricDerivation.induced B) -
    (SymmetricDerivation.induced B).comp (SymmetricDerivation.induced A) =
      SymmetricDerivation.induced (A.comp B - B.comp A)

/-- The actual quotient degree operators are dual under every established
permanent pairing. The formula needs neither perfection nor division by p!. -/
def symmetric_duality : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (A : V →ₗ[K] V) (p : ℕ),
  ∃ (D : Symmetric.symmetricPower K V p →ₗ[K] Symmetric.symmetricPower K V p)
    (E : Symmetric.symmetricPower K (Module.Dual K V) p →ₗ[K]
      Symmetric.symmetricPower K (Module.Dual K V) p),
    (∀ x, SymmetricBasis.powerInclusion (K := K) (V := V) p (D x) =
      SymmetricDerivation.induced A (SymmetricBasis.powerInclusion (K := K) (V := V) p x)) ∧
    (∀ α, SymmetricBasis.powerInclusion (K := K) (V := Module.Dual K V) p (E α) =
      SymmetricDerivation.induced A.dualMap (SymmetricBasis.powerInclusion (K := K) (V := Module.Dual K V) p α)) ∧
    ∀ P, SymmetricBasis.PerfectPairing.IsPermanentPairing p P →
      ∀ α x, P (E α) x = P α (D x)

end Specs.D05.M15.TensorDerivation.LieDuality
