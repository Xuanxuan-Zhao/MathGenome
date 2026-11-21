import MathGenome.Internal.Specs.D05.M15.Multilinear
import Mathlib.Data.Fintype.Perm

/-! Independent statements for the subset-identity stage of
K05.15.polynomial_polarization (paper.tex:3212–3226).
`Fin p` indexes occurrences, so equal vectors in distinct slots stay distinct.
The identities below actually hold without finite dimension; characteristic zero
is used only for division by the factorial and diagonal injectivity. -/

namespace D05.M15.PolynomialPolarization

open scoped BigOperators

/-- Invariance under all permutations of the slots of the canonical multilinear map. -/
def IsSymmetric {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {p : ℕ}
    (B : MultilinearMap K (fun _ : Fin p => V) K) : Prop :=
  ∀ (σ : Equiv.Perm (Fin p)) (v : Fin p → V), B (v ∘ σ) = B v

/-- The raw, unnormalized diagonal, also for nullary forms. -/
def rawDiagonal {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {p : ℕ}
    (B : MultilinearMap K (fun _ : Fin p => V) K) (v : V) : K :=
  B (fun _ => v)

end D05.M15.PolynomialPolarization

namespace Specs.D05.M15.PolynomialPolarization.SubsetIdentity

open scoped BigOperators
open _root_.D05.M15.PolynomialPolarization

/-- The coefficient of an expanded tuple missing a specified index vanishes. -/
def missing_index_cancellation : Prop :=
  ∀ {K : Type*} [Field K] (p : ℕ) (f : Fin p → Fin p) (a : Fin p),
    (∀ i, f i ≠ a) →
    (∑ S : Finset (Fin p), if ∀ i, f i ∈ S then (-1 : K) ^ (p - S.card) else 0) = 0

/-- A tuple using every index is a permutation, and there are exactly `p!` such tuples. -/
def survivor_count : Prop := by
  classical
  exact ∀ p : ℕ,
    (∀ f : Fin p → Fin p, Function.Surjective f ↔ Function.Bijective f) ∧
    (Finset.univ.filter (fun f : Fin p → Fin p => Function.Surjective f)).card = p.factorial

/-- Every surviving term is the same symmetric value, including nullary forms. -/
def survivor_sum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (p : ℕ)
    (B : MultilinearMap K (fun _ : Fin p => V) K), IsSymmetric B →
    ∀ v : Fin p → V,
      (∑ f : Fin p → Fin p, if Function.Surjective f then B (v ∘ f) else 0) =
        (p.factorial : K) * B v

/-- The undivided subset-sum identity; valid even in positive characteristic. -/
def subset_identity : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (p : ℕ)
    (B : MultilinearMap K (fun _ : Fin p => V) K), IsSymmetric B →
    ∀ v : Fin p → V,
      (p.factorial : K) * B v =
        ∑ S : Finset (Fin p), (-1 : K) ^ (p - S.card) * rawDiagonal B (∑ i ∈ S, v i)

/-- The inverse polarization formula for every symmetric form. -/
def polarization_formula : Prop :=
  ∀ {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] (p : ℕ)
    (B : MultilinearMap K (fun _ : Fin p => V) K), IsSymmetric B →
    ∀ v : Fin p → V,
      B v = (p.factorial : K)⁻¹ *
        ∑ S : Finset (Fin p), (-1 : K) ^ (p - S.card) * rawDiagonal B (∑ i ∈ S, v i)

/-- Equality of the raw diagonals determines the symmetric multilinear forms. -/
def raw_diagonal_injective : Prop :=
  ∀ {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] (p : ℕ)
    (B C : MultilinearMap K (fun _ : Fin p => V) K),
    IsSymmetric B → IsSymmetric C → rawDiagonal B = rawDiagonal C → B = C

/-- There is just one empty subset, and the zero-degree identity recovers the
chosen scalar value of the nullary form. -/
def degree_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : MultilinearMap K (fun _ : Fin 0 => V) K) (v : Fin 0 → V),
      (Finset.univ : Finset (Finset (Fin 0))).card = 1 ∧
      (∑ S : Finset (Fin 0), (-1 : K) ^ (0 - S.card) * rawDiagonal B (∑ i ∈ S, v i)) = B v

end Specs.D05.M15.PolynomialPolarization.SubsetIdentity
