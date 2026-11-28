import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedMatrices
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.AssociativePrimePowers
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedLie
import Mathlib.Algebra.CharP.Lemmas

/-! The restricted operation on the special linear Lie algebra. -/

namespace LieNotes.SuperRestricted.RestrictedMatrices

open LieAlgebra.SpecialLinear (sl)
open _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary (jacobsonCoeffValue)
open _root_.Specs.LieNotes.SuperRestricted.JacobsonPolynomials (jacobsonTermValue)
open RestrictedLie (RestrictedPower)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p] {n : ℕ}

private theorem trace_jacobsonCoeff_succ (A B : Matrix (Fin n) (Fin n) k) (m j : ℕ) :
    (jacobsonCoeffValue A B (m + 1) j).trace = 0 := by
  cases j <;> simp [jacobsonCoeffValue, Matrix.trace_add]

private theorem trace_pow_add (A B : Matrix (Fin n) (Fin n) k) :
    ((A + B) ^ p).trace = (A ^ p).trace + (B ^ p).trace := by
  have hp : 1 < p := (CharP.char_is_prime_of_pos k p).out.one_lt
  have hterm (i : ℕ) : (jacobsonTermValue k p i A B).trace = 0 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hp)
    simp [jacobsonTermValue, hm, Matrix.trace_smul, trace_jacobsonCoeff_succ]
  rw [AssociativePrimePowers.pow_add (k := k)]
  simp [Matrix.trace_add, Matrix.trace_sum, hterm]

private theorem trace_single_pow (i j : Fin n) (a : k) :
    ((Matrix.single i j a) ^ p).trace = (Matrix.single i j a).trace ^ p := by
  by_cases hij : i = j
  · subst j
    have h (m : ℕ) : (Matrix.single i i a) ^ (m + 1) = Matrix.single i i (a ^ (m + 1)) := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, ih, Matrix.single_mul_single_same, ← pow_succ]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
    rw [h, Matrix.trace_single_eq_same, Matrix.trace_single_eq_same]
  · have hsq : (Matrix.single i j a) ^ 2 = 0 := by
      rw [pow_two, Matrix.single_mul_single_of_ne a i j i (Ne.symm hij)]
    have hp : 2 ≤ p := (CharP.char_is_prime_of_pos k p).out.two_le
    simp [pow_eq_zero_of_le hp hsq, hij, zero_pow (NeZero.ne p)]

private theorem trace_pow (A : Matrix (Fin n) (Fin n) k) :
    (A ^ p).trace = A.trace ^ p := by
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  let left : Matrix (Fin n) (Fin n) k →+ k :=
    { toFun := fun M => (M ^ p).trace
      map_zero' := by rw [zero_pow (NeZero.ne p), Matrix.trace_zero]
      map_add' := trace_pow_add (p := p) }
  let right : Matrix (Fin n) (Fin n) k →+ k :=
    (frobenius k p).toAddMonoidHom.comp (Matrix.traceLinearMap (Fin n) k k).toAddMonoidHom
  change left A = right A
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => trace_single_pow (p := p) i j (A i j)

/-- The special linear Lie subalgebra is stable under associative powers in characteristic `p`. -/
theorem pow_mem_sl (A : sl (Fin n) k) : (A.val ^ p) ∈ sl (Fin n) k := by
  have hA : A.val.trace = 0 := A.property
  change (A.val ^ p).trace = 0
  rw [trace_pow, hA, zero_pow (NeZero.ne p)]

/-- The matrix power and its three restricted axioms on the full matrix algebra. -/
private def ambientPower (n : ℕ) : RestrictedPower k p (Matrix (Fin n) (Fin n) k) :=
  ⟨fun A => A ^ p, (RestrictedLie.isRestrictedPower_iff _).2
    ⟨fun A => (AssociativePrimePowers.ad_pow (k := k) (p := p) A).symm,
      fun a A => smul_pow a A p,
      AssociativePrimePowers.pow_add (k := k) (p := p)⟩⟩

/-- The restricted operation on `sl` obtained from the full matrix algebra. -/
def restrictedPower (n : ℕ) : RestrictedPower k p (sl (Fin n) k) :=
  RestrictedLie.restrict (ambientPower n) (sl (Fin n) k) (pow_mem_sl (p := p))

@[simp]
theorem coe_restrictedPower_apply (A : sl (Fin n) k) :
    ((restrictedPower (p := p) n).val A).val = A.val ^ p :=
  rfl

/-- The special linear Lie algebra admits the restricted structure induced by matrix powers. -/
theorem sl_admits_restrictedPower (n : ℕ) :
    ∃ power : RestrictedPower k p (sl (Fin n) k),
      ∀ A : sl (Fin n) k, (power.val A).val = A.val ^ p :=
  ⟨restrictedPower n, coe_restrictedPower_apply⟩

end LieNotes.SuperRestricted.RestrictedMatrices
