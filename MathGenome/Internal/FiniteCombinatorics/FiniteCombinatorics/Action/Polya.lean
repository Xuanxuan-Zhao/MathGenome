import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.Polya
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.FixedColorings
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.Burnside
import Lean.Elab.Tactic.Omega

/-! Unweighted Pólya enumeration (paper.tex W32). -/
namespace FiniteCombinatorics.Action

open scoped BigOperators
universe u v w
variable (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X]

private theorem sum_countCycles_fin (g : G) :
    (∑ i : Fin (Fintype.card X), countCycles G X g (i.val + 1)) =
      ∑ k ∈ Finset.Icc 1 (Fintype.card X), countCycles G X g k := by
  classical
  apply Finset.sum_bij (fun i _ => i.val + 1)
  · intro i _
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ h
    apply Fin.ext
    omega
  · intro k hk
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    change k - 1 + 1 = k
    omega
  · intro i _
    rfl

/-- Constant substitution turns the complete cycle monomial into a power
whose exponent is the number of complete cycles. -/
theorem eval_elementMonomial (g : G) (q : ℚ) :
    MvPolynomial.eval (fun _ => q) (elementMonomial G X g) =
      q ^ (∑ k ∈ Finset.Icc 1 (Fintype.card X), countCycles G X g k) := by
  classical
  simp only [elementMonomial, permutationMonomial, MvPolynomial.eval_prod,
    map_pow, MvPolynomial.eval_X]
  rw [Finset.prod_pow_eq_pow_sum]
  exact congrArg (fun n => q ^ n) (sum_countCycles_fin G X g)

/-- The actual number of coloring orbits is the rational evaluation of the
cycle index. This includes zero colors, empty positions, and nonfaithful actions. -/
theorem polya (G : Type u) (X : Type v) (C : Type w)
    [Group G] [MulAction G X] [Fintype G] [Fintype X] [Fintype C] :
    letI := coloringAction G X C
    (Nat.card (Quotient (MulAction.orbitRel G (X → C))) : ℚ) =
      MvPolynomial.eval (fun _ => (Fintype.card C : ℚ)) (cycleIndex G X) := by
  classical
  let := coloringAction G X C
  have hb : Nat.card G * Nat.card (Quotient (MulAction.orbitRel G (X → C))) =
      ∑ g : G, Nat.card (fixedBy G (X → C) g) := by
    have hUniv : @Finset.univ G (Fintype.ofFinite G) = @Finset.univ G ‹Fintype G› :=
      congrArg (fun ft => @Finset.univ G ft) (Subsingleton.elim _ _)
    simpa only [hUniv] using burnside G (X → C)
  have hfixed (g : G) : Nat.card (fixedBy G (X → C) g) =
      Fintype.card C ^ (∑ k ∈ Finset.Icc 1 (Fintype.card X), countCycles G X g k) :=
    card_fixedColorings G X C g
  simp_rw [hfixed] at hb
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) hb
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
    show Nat.card G = Fintype.card G from Nat.card_eq_fintype_card] at hcast
  have hG : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [cycleIndex, MvPolynomial.smul_eval, map_sum]
  simp_rw [eval_elementMonomial]
  rw [← hcast]
  exact (inv_mul_cancel_left₀ hG _).symm

end FiniteCombinatorics.Action
