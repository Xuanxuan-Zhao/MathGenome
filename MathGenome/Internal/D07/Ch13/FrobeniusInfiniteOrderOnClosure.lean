import MathGenome.Internal.Specs.D07.Ch13.FrobeniusInfiniteOrderOnClosure
import MathGenome.Internal.D07.Ch11.RootBound
import MathGenome.Internal.D07.Ch13.Existence

/-! The infinite-order assertion concerns the closure, not a finite field.
The proof uses the constructed q^(j+1)-element intermediate field and the
degree-q^j root bound, without using any finite-field Galois-group theorem. -/

universe u v

namespace D07.Ch13.FrobeniusInfiniteOrderOnClosure

open Polynomial Specs.D07.Ch13.FrobeniusInfiniteOrderOnClosure

theorem iterated_frobenius_apply (K : Type u) (Ω : Type v)
    [Field K] [Field Ω] [Algebra K Ω] (q : ℕ)
    (Φ : Ω ≃ₐ[K] Ω) (hΦ : ∀ x : Ω, Φ x = x ^ q) (j : ℕ) (x : Ω) :
    (Φ ^ j) x = x ^ (q ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, hΦ, ih, ← pow_mul, Nat.pow_succ]

theorem embedded_moved_element : EmbeddedMovedElement.{u, v} := by
  intro K Ω _ _ _ _ _ _ q hq Φ hΦ j hj
  classical
  let E := Existence.rootField K Ω q (j + 1)
  obtain ⟨hfinite, hcard, _⟩ :=
    Existence.embedded_existence K Ω q (j + 1) hq (Nat.le_add_left 1 j)
  let : Finite E := hfinite
  let := Fintype.ofFinite K
  have hq1 : 1 < q := hq ▸ Finite.one_lt_card
  by_contra h
  have hfixed : ∀ x : E, (Φ ^ j) (x : Ω) = (x : Ω) := by
    simpa only [not_exists, not_not] using h
  let f : Polynomial E := X ^ (q ^ j) - X
  have hf : f ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero E (Nat.ne_of_gt hj) hq1
  have hdegree : f.degree = (q ^ j : ℕ) := by
    rw [degree_eq_natDegree hf]
    exact congrArg (fun n : ℕ => (n : WithBot ℕ))
      (FiniteField.X_pow_card_pow_sub_X_natDegree_eq E (Nat.ne_of_gt hj) hq1)
  have hall : {a : E | f.eval a = 0} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    have ha : a ^ (q ^ j) = a := by
      apply Subtype.ext
      exact (iterated_frobenius_apply K Ω q Φ hΦ j a).symm.trans (hfixed a)
    simp [f, ha]
  have hbound := (D07.Ch11.RootBound.distinct_root_bound E f (q ^ j) hf hdegree).2
  rw [hall, Set.ncard_univ, hcard] at hbound
  exact (Nat.not_le_of_gt (Nat.pow_lt_pow_right hq1 (Nat.lt_succ_self j))) hbound

theorem infinite_order_on_closure : InfiniteOrderOnClosure.{u, v} := by
  intro K Ω _ _ _ _ _ _ q hq
  obtain ⟨Φ, hΦ⟩ := Frobenius.relative_automorphism K Ω q hq
  have hmoved : ∀ j : ℕ, 0 < j → ∃ x : Ω, (Φ ^ j) x ≠ x := by
    intro j hj
    obtain ⟨x, hx⟩ := embedded_moved_element K Ω q hq Φ hΦ j hj
    exact ⟨x, hx⟩
  refine ⟨Φ, hΦ, orderOf_eq_zero_iff'.mpr ?_, hmoved⟩
  intro j hj hidentity
  obtain ⟨x, hx⟩ := hmoved j hj
  exact hx (by rw [hidentity]; rfl)

end D07.Ch13.FrobeniusInfiniteOrderOnClosure
