import MathGenome.Internal.Specs.D05.M15.SymmetricBasis.PerfectPairing
import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-! Symmetric scalar forms and the unsigned shuffle convention of
paper.tex:3228–3240. The degreewise spaces are actual symmetric multilinear
maps, and the covector powers are the accepted adjacent-swap quotients.
A shuffle is a permutation modulo the permutations within its two blocks.
Each coset is counted once; the choice of representative will be proved
irrelevant. No diagonal map is used to define multiplication. -/
noncomputable section
open scoped Classical DirectSum
namespace Specs.D05.M15.PolynomialPolarization.ShuffleProduct
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis
open Specs.D05.M15.SymmetricBasis.PerfectPairing
universe u v
variable (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V]

/-- The subspace of forms invariant under every permutation of the slots. -/
def symmetricForms (p : ℕ) : Submodule K (MultilinearMap K (fun _ : Fin p => V) K) where
  carrier := {B | ∀ (x : Fin p → V) (σ : Equiv.Perm (Fin p)), B (x ∘ σ) = B x}
  zero_mem' := by simp
  add_mem' := by intro B C hB hC x σ; exact congrArg₂ (· + ·) (hB x σ) (hC x σ)
  smul_mem' := by intro c B hB x σ; exact congrArg (c • ·) (hB x σ)

variable {K V}

/-- The ordinary product of a p-form and a q-form on consecutive blocks. -/
def blockProduct {p q : ℕ}
    (B : MultilinearMap K (fun _ : Fin p => V) K)
    (C : MultilinearMap K (fun _ : Fin q => V) K) :
    MultilinearMap K (fun _ : Fin p ⊕ Fin q => V) K :=
  (LinearMap.mul' K K).compMultilinearMap (B.domCoprod C)

/-- One representative of a shuffle coset; symmetry of the two forms makes
the summand independent of the representative. -/
def shuffleSummand {p q : ℕ} (B : symmetricForms K V p) (C : symmetricForms K V q)
    (s : Equiv.Perm.ModSumCongr (Fin p) (Fin q)) :
    MultilinearMap K (fun _ : Fin p ⊕ Fin q => V) K :=
  (blockProduct B.val C.val).domDomCongr s.out

/-- The unsigned shuffle sum, reindexed from the disjoint union to Fin(p+q). -/
def shuffle {p q : ℕ} (B : symmetricForms K V p) (C : symmetricForms K V q) :
    MultilinearMap K (fun _ : Fin (p+q) => V) K :=
  (∑ s : Equiv.Perm.ModSumCongr (Fin p) (Fin q), shuffleSummand B C s).domDomCongr
    finSumFinEquiv

/-- Normalized averaging over all (p+q)! permutations. -/
def averagedProduct {p q : ℕ} (B : symmetricForms K V p) (C : symmetricForms K V q) :
    MultilinearMap K (fun _ : Fin (p+q) => V) K :=
  ((p+q).factorial : K)⁻¹ •
    ∑ σ : Equiv.Perm (Fin (p+q)),
      ((blockProduct B.val C.val).domDomCongr finSumFinEquiv).domDomCongr σ

/-- The defining unnormalized permanent formula, on the spanning monomials. -/
def IsPermanentMap (p : ℕ)
    (R : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricForms K V p) : Prop :=
  ∀ φ x, (R (elementary K (Module.Dual K V) p φ)).val x = permanent φ x

def permanent_isomorphism : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (p : ℕ), ∃ R : symmetricPower K (Module.Dual K V) p ≃ₗ[K] symmetricForms K V p,
    IsPermanentMap p R.toLinearMap

def representative_independent : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q)
  (σ : Equiv.Perm (Fin p ⊕ Fin q)),
  shuffleSummand B C (Quotient.mk'' σ) = (blockProduct B.val C.val).domDomCongr σ

/-- This identity counts every full permutation once, without division. -/
def permutation_partition : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q),
  ∑ σ : Equiv.Perm (Fin p ⊕ Fin q), (blockProduct B.val C.val).domDomCongr σ =
    (p.factorial * q.factorial) •
      ∑ s : Equiv.Perm.ModSumCongr (Fin p) (Fin q), shuffleSummand B C s

def shuffle_symmetric : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q),
  shuffle B C ∈ symmetricForms K V (p+q)

/-- Greub's product: (p+q)!/(p!q!) times normalized symmetrization. -/
def normalization : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] {p q : ℕ}
  (B : symmetricForms K V p) (C : symmetricForms K V q),
  shuffle B C = (((p+q).factorial : K) / ((p.factorial : K) * (q.factorial : K))) •
    averagedProduct B C

/-- Quotient multiplication is fixed by its inclusion into the original
symmetric algebra. Compatibility is asserted for all covectors, not only
monomials or decomposable powers. -/
def multiplication : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∃ (R : ∀ p, symmetricPower K (Module.Dual K V) p ≃ₗ[K] symmetricForms K V p)
    (m : ∀ p q, symmetricPower K (Module.Dual K V) p →ₗ[K]
      symmetricPower K (Module.Dual K V) q →ₗ[K] symmetricPower K (Module.Dual K V) (p+q)),
    (∀ p, IsPermanentMap p (R p).toLinearMap) ∧
    ∀ p q a b,
      powerInclusion (K := K) (V := Module.Dual K V) (p+q) (m p q a b) = powerInclusion (K := K) (V := Module.Dual K V) p a * powerInclusion (K := K) (V := Module.Dual K V) q b ∧
      (R (p+q) (m p q a b)).val = shuffle (R p a) (R q b)

/-- Degree zero consists of scalars, and shuffle multiplication of nullary
forms is ordinary scalar multiplication. -/
def degree_zero : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [AddCommGroup V] [Module K V]
  (B C : symmetricForms K V 0) (x : Fin (0+0) → V),
    shuffle B C x = B.val (fun i => Fin.elim0 i) * C.val (fun i => Fin.elim0 i)

/-- Finitely supported sums of symmetric scalar forms of all degrees. -/
abbrev formAlgebra (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] :=
  ⨁ p : ℕ, symmetricForms K V p

/-- Freeze the standard linear operations before supplying a ring structure. -/
def formAdd (x y : formAlgebra K V) : formAlgebra K V := x + y
def formSmul (c : K) (x : formAlgebra K V) : formAlgebra K V := c • x
def formSingle (p : ℕ) : symmetricForms K V p →ₗ[K] formAlgebra K V :=
  DirectSum.lof K ℕ (fun p => symmetricForms K V p) p

/-- The full graded algebra statement, including its multiplication, unit,
standard linear structure, and its degreewise permanent formula. The map from
the original symmetric algebra is onto the finitely supported sum, not a
completion or an infinite product of form spaces. -/
def graded_algebra_isomorphism : Prop := ∀ {K : Type u} {V : Type v}
  [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∃ (A : CommRing (formAlgebra K V))
    (AK : @Algebra K (formAlgebra K V) _ A.toSemiring),
  letI := A
  letI := AK
  ∃ (E : symmetricAlgebra K (Module.Dual K V) ≃ₐ[K] formAlgebra K V)
    (R : ∀ p, symmetricPower K (Module.Dual K V) p ≃ₗ[K] symmetricForms K V p),
    (∀ x y : formAlgebra K V, x + y = formAdd x y) ∧
    (∀ (c : K) (x : formAlgebra K V),
      @SMul.smul K (formAlgebra K V) AK.toSMul c x = formSmul c x) ∧
    (∀ p, IsPermanentMap p (R p).toLinearMap) ∧
    (∀ p a, E (powerInclusion (K := K) (V := Module.Dual K V) p a) = formSingle p (R p a)) ∧
    (∀ p q (B : symmetricForms K V p) (C : symmetricForms K V q),
      ∃ D : symmetricForms K V (p+q), D.val = shuffle B C ∧
        formSingle p B * formSingle q C = formSingle (p+q) D) ∧
    (∃ B : symmetricForms K V 0, (∀ x, B.val x = 1) ∧
      (1 : formAlgebra K V) = formSingle 0 B)

end Specs.D05.M15.PolynomialPolarization.ShuffleProduct
