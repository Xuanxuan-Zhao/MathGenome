import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization.ShuffleProduct
import MathGenome.Internal.Specs.D05.M15.PolynomialBridge
import MathGenome.Internal.Specs.D05.M15.PolynomialPolarization.SubsetIdentity
import MathGenome.Internal.Specs.D05.M15.SymmetricBasis.PairingContractions

/-! The two products and their diagonal/insertion conventions, paper.tex:3228–3240.
All powers, inclusions, contractions and shuffle sums are the upstream objects.
`normalizedDiagonal` divides the raw diagonal by the degree factorial. -/
noncomputable section
open scoped Classical DirectSum
namespace Specs.D05.M15.PolynomialPolarization.FormProducts
open Specs.D05.M15.Symmetric Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.SymmetricBasis.PerfectPairing
open Specs.D05.M15.SymmetricBasis.PairingContractions
open Specs.D05.M15.PolynomialPolarization.ShuffleProduct
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Evaluation of an actual symmetric multilinear form. -/
def formEvaluation {p : ℕ} (x : Fin p → V) : symmetricForms K V p →ₗ[K] K where
  toFun B := B.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw diagonal with the usual pointwise linear structure on functions. -/
def diagonalMap (p : ℕ) : symmetricForms K V p →ₗ[K] (V → K) where
  toFun B v := _root_.D05.M15.PolynomialPolarization.rawDiagonal B.val v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def normalizedDiagonal {p : ℕ} (B : MultilinearMap K (fun _ : Fin p => V) K)
    (v : V) : K := (p.factorial : K)⁻¹ * _root_.D05.M15.PolynomialPolarization.rawDiagonal B v

/-- All finite homogeneous sums, evaluated by the normalized diagonal. -/
def normalizedEvaluation : formAlgebra K V →ₗ[K] (V → K) :=
  DirectSum.toModule K ℕ (V → K)
    (fun p => (p.factorial : K)⁻¹ • diagonalMap p)

def permanent_isomorphism : Prop := ShuffleProduct.permanent_isomorphism.{u,v}
def graded_algebra_isomorphism : Prop := ShuffleProduct.graded_algebra_isomorphism.{u,v}
def normalization : Prop := ShuffleProduct.normalization.{u,v}

def averaged_symmetric : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q),
  ShuffleProduct.averagedProduct B C ∈ symmetricForms K V (p+q)

def averaged_diagonal : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q) (v : V),
  ShuffleProduct.averagedProduct B C (fun _ => v) =
    B.val (fun _ => v) * C.val (fun _ => v)

def shuffle_diagonal : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q) (v : V),
  shuffle B C (fun _ => v) = ((p+q).choose p : K) *
    B.val (fun _ => v) * C.val (fun _ => v)

def normalized_diagonal_mul : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q) (v : V),
  normalizedDiagonal (shuffle B C) v =
    normalizedDiagonal B.val v * normalizedDiagonal C.val v

/-- Both conventions are isomorphisms, on the same actual symmetric powers.
The multiplication is pinned to the canonical inclusions in the symmetric algebra. -/
def product_correspondence : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∃ (R N : ∀ p, symmetricPower K (Module.Dual K V) p ≃ₗ[K] symmetricForms K V p)
    (m : ∀ p q, symmetricPower K (Module.Dual K V) p →ₗ[K]
      symmetricPower K (Module.Dual K V) q →ₗ[K] symmetricPower K (Module.Dual K V) (p+q)),
    (∀ p, IsPermanentMap p (R p).toLinearMap) ∧
    (∀ p a, N p a = (p.factorial : K)⁻¹ • R p a) ∧
    ∀ p q a b,
      powerInclusion (K := K) (V := Module.Dual K V) (p+q) (m p q a b) =
        powerInclusion (K := K) (V := Module.Dual K V) p a *
          powerInclusion (K := K) (V := Module.Dual K V) q b ∧
      (R (p+q) (m p q a b)).val = shuffle (R p a) (R q b) ∧
      (N (p+q) (m p q a b)).val = ShuffleProduct.averagedProduct (N p a) (N q b)

/-- The normalized diagonal of the permanent map is ordinary polynomial evaluation.
This identifies its target as polynomial functions on the original space. -/
def polynomial_evaluation : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] (p : ℕ)
  (R : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricForms K V p),
  IsPermanentMap p R → ∀ a v,
    normalizedDiagonal (R a).val v = PolynomialBridge.evaluation K V
      (powerInclusion (K := K) (V := Module.Dual K V) p a) v

/-- A genuine injective algebra map on finite sums of all degrees, with the
standard addition/scalar action and the shuffle product on homogeneous forms. -/
def diagonal_algebra_map : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∃ (A : CommRing (formAlgebra K V))
    (AK : @Algebra K (formAlgebra K V) _ A.toSemiring),
  letI := A
  letI := AK
  ∃ F : formAlgebra K V →ₐ[K] (V → K),
    (∀ x y : formAlgebra K V, x + y = formAdd x y) ∧
    (∀ (c : K) (x : formAlgebra K V),
      @SMul.smul K (formAlgebra K V) AK.toSMul c x = formSmul c x) ∧
    (∀ p q (B : symmetricForms K V p) (C : symmetricForms K V q),
      ∃ D : symmetricForms K V (p+q), D.val = shuffle B C ∧
        formSingle p B * formSingle q C = formSingle (p+q) D) ∧
    (∀ x, F x = normalizedEvaluation x) ∧ Function.Injective F ∧
    (∀ f : V → K, (∃ x, F x = f) ↔ ∃ a : symmetricAlgebra K (Module.Dual K V),
      PolynomialBridge.evaluation K V a = f)

/-- Insertion has no extra degree factor for the unnormalized permanent. -/
def insertion : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] (p : ℕ) (v : V)
  (C : symmetricPower K (Module.Dual K V) (p+1) →ₗ[K]
    symmetricPower K (Module.Dual K V) p), IsContraction v p C →
  ∀ (R : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricForms K V p)
    (S : symmetricPower K (Module.Dual K V) (p+1) →ₗ[K] symmetricForms K V (p+1)),
    IsPermanentMap p R → IsPermanentMap (p+1) S → ∀ a x,
      (R (C a)).val x = (S a).val (Fin.cons v x)

/-- Under R/p!, insertion acquires the factor p+1 on degree p+1. -/
def normalized_insertion : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] (p : ℕ) (v : V)
  (C : symmetricPower K (Module.Dual K V) (p+1) →ₗ[K]
    symmetricPower K (Module.Dual K V) p), IsContraction v p C →
  ∀ (R : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricForms K V p)
    (S : symmetricPower K (Module.Dual K V) (p+1) →ₗ[K] symmetricForms K V (p+1)),
    IsPermanentMap p R → IsPermanentMap (p+1) S → ∀ a x,
      ((p.factorial : K)⁻¹ • R (C a)).val x =
        (p+1 : ℕ) • ((((p+1).factorial : K)⁻¹ • S a).val (Fin.cons v x))

/-- Every scalar, not just the unit, is preserved in degree zero. -/
def degree_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V]
  (R : symmetricPower K (Module.Dual K V) 0 →ₗ[K] symmetricForms K V 0),
  IsPermanentMap 0 R → ∀ (c : K) (v : V),
    (R (c • elementary K (Module.Dual K V) 0 (fun i => Fin.elim0 i))).val
      (fun i => Fin.elim0 i) = c ∧
    normalizedDiagonal (R (c • elementary K (Module.Dual K V) 0
      (fun i => Fin.elim0 i))).val v = c

/-- The conflicting raw-diagonal homomorphism convention already fails on K. -/
def linear_form_correction : Prop := ∀ (K : Type u) [Field K] [CharZero K],
  (∀ {V : Type v} [AddCommGroup V] [Module K V]
    (B C : symmetricForms K V 1) (v : V),
    shuffle B C (fun _ => v) = 2 * B.val (fun _ => v) * C.val (fun _ => v)) ∧
  ∃ (B C : symmetricForms K K 1) (v : K),
    shuffle B C (fun _ => v) ≠ B.val (fun _ => v) * C.val (fun _ => v)

end Specs.D05.M15.PolynomialPolarization.FormProducts
