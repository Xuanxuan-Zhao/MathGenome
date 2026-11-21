import MathGenome.Internal.Specs.D05.Foundations.PermutationSign
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Algebra.CharP.Two

/-!
Independent statements for K05.05.alternating, paper.tex:790–796.
Slots are indexed by `Fin n`, including `n = 0`. The scalar-valued maps are
multilinear over the given commutative ring, with no dimension or characteristic
restriction until the explicitly stated converse and counterexample.
-/

namespace D05.Specs.Alternating

/-- Alternation means vanishing on every tuple with two equal, distinct slots. -/
def IsAlternating {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M) R) : Prop :=
  ∀ (v : Fin n → M) (i j : Fin n), v i = v j → i ≠ j → f v = 0

/-- The sign is the integer inversion-parity sign of the shared foundation,
cast into the scalar ring. Permutations act by precomposition on tuples. -/
def HasSignRule {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M) R) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → M),
    f (v ∘ σ) = (D05.Foundations.permutationSign σ : R) * f v

/-- The unbundled vanishing definition is precisely Mathlib's bundled structure. -/
def alternating_iff_bundled : Prop :=
  ∀ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n => M) R),
    IsAlternating f ↔ ∃ a : AlternatingMap R M R (Fin n), a.toMultilinearMap = f

/-- Expansion in distinct slots containing `u + w` leaves these two cross terms. -/
def cross_terms : Prop :=
  ∀ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n => M) R), IsAlternating f →
    ∀ (v : Fin n → M) (i j : Fin n), i ≠ j → ∀ (u w : M),
      0 = f (Function.update (Function.update v i u) j w) +
        f (Function.update (Function.update v i w) j u)

/-- An interchange of distinct input positions negates an alternating form. -/
def swap_neg : Prop :=
  ∀ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n => M) R), IsAlternating f →
    ∀ (v : Fin n → M) (i j : Fin n), i ≠ j →
      f (v ∘ Equiv.swap i j) = -f v

/-- Alternation implies the full permutation-sign rule over every scalar ring. -/
def permutation_rule : Prop :=
  ∀ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n => M) R),
    IsAlternating f → HasSignRule f

/-- Over a field of characteristic other than two, the sign rule implies
alternation. `(2 : K) ≠ 0` expresses exactly this characteristic restriction. -/
def converse_char_ne_two : Prop :=
  ∀ {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n : ℕ}
    (f : MultilinearMap K (fun _ : Fin n => M) K), (2 : K) ≠ 0 →
    HasSignRule f → IsAlternating f

/-- Multiplication on the one-dimensional module `R` in two input slots. -/
def multiplicationForm (R : Type*) [CommRing R] :
    MultilinearMap R (fun _ : Fin 2 => R) R :=
  MultilinearMap.mkPiAlgebra R (Fin 2) R

def multiplication_form_type := ∀ (R : Type*) [CommRing R],
  MultilinearMap R (fun _ : Fin 2 => R) R

def multiplication_form_value : multiplication_form_type := multiplicationForm

/-- The example is exactly the bilinear map `(x,y) ↦ x*y`. -/
def multiplication_formula : Prop := ∀ (R : Type*) [CommRing R] (v : Fin 2 → R),
  multiplicationForm R v = v 0 * v 1

/-- In every field of characteristic two the displayed multiplication form
obeys the sign rule and is symmetric, but has value one at `(1,1)`, so is
not alternating. The module `K` is one-dimensional over itself. -/
def characteristic_two_counterexample : Prop :=
  ∀ (K : Type*) [Field K] [CharP K 2],
    HasSignRule (multiplicationForm K) ∧
    (∀ v : Fin 2 → K, multiplicationForm K (v ∘ Equiv.swap 0 1) =
      multiplicationForm K v) ∧
    multiplicationForm K (fun _ => 1) = 1 ∧
    ¬ IsAlternating (multiplicationForm K)

end D05.Specs.Alternating
