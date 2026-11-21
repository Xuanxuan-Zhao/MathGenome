import MathGenome.Internal.Specs.D07.Ch20.SeparablePartUniformInseparableExponent
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Minpoly.Finite

/-!
The uniform inseparability exponent in K07.20.separable_part.

We bound the exponent of every element by the dimension of the purely
inseparable extension. Its minimal polynomial is X^(p^n) - c, so p^n is
at most the dimension and hence n is at most that dimension. Raising its
base-valued p^n-th power further gives the same exponent for all elements.
Apply this to L over the internal separable subfield of L/K.
-/

universe u v

namespace D07.Ch20.SeparablePartUniformInseparableExponent

open Polynomial

/-- A dimension bound gives a uniform exponent for any finite purely
inseparable extension in positive characteristic. -/
theorem pow_finrank_mem_range
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsPurelyInseparable F E]
    (p : ℕ) [CharP F p] (hp : p.Prime) (x : E) :
    x ^ (p ^ Module.finrank F E) ∈ (algebraMap F E).range := by
  let : ExpChar F p := ExpChar.prime hp
  obtain ⟨n, c, hpoly⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hdegree : p ^ n ≤ Module.finrank F E := by
    simpa only [hpoly, natDegree_X_pow_sub_C] using minpoly.natDegree_le (A := F) x
  have hn : n ≤ Module.finrank F E :=
    (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt)).trans hdegree
  have hx : x ^ (p ^ n) = algebraMap F E c := by
    have hz := minpoly.aeval F x
    rw [hpoly] at hz
    exact sub_eq_zero.mp (by simpa only [map_sub, map_pow, aeval_X, aeval_C] using hz)
  refine ⟨c ^ (p ^ (Module.finrank F E - n)), ?_⟩
  rw [map_pow, ← hx, ← pow_mul, ← pow_add, Nat.add_sub_of_le hn]

theorem uniform_inseparable_exponent :
    Specs.D07.Ch20.SeparablePartUniformInseparableExponent.UniformInseparableExponent.{u, v} := by
  intro K L _ _ _ _ p _ hp
  let S := separableClosure K L
  let : CharP S p := charP_of_injective_algebraMap' K p
  let : FiniteDimensional S L := FiniteDimensional.right K S L
  refine ⟨Module.finrank S L, fun x => ?_⟩
  obtain ⟨y, hy⟩ := pow_finrank_mem_range S L p hp x
  exact hy ▸ y.property

end D07.Ch20.SeparablePartUniformInseparableExponent
