import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.AsymptoticScale
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OAlgebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.CoefficientUnique

/-!
# Uniqueness of asymptotic coefficients

K03.17.coefficient_unique, paper.tex:4321–4334. Truncating an expansion
preserves its remainder estimate at the preceding order. Induction then
identifies the earlier coefficients. Subtracting the two order-m remainders
leaves the last coefficient difference times φ m. Division by the eventually
nonzero φ m gives a constant tending to zero on a nontrivial filter.

No assertion about convergence of an infinite sum, or uniqueness of functions
with prescribed all-orders coefficients, is used or concluded.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology BigOperators
universe u v

variable {X : Type u} {K : Type v} [NormedField K]

private theorem mul_self_littleO_constant_zero (l : Filter X) (g : X → K) (c : K)
    (hl : l.NeBot) (hg : ∀ᶠ x in l, g x ≠ 0)
    (h : ScalarLittleO l (fun x => c * g x) g) : c = 0 := by
  let : l.NeBot := hl
  have ht := (scalarLittleO_iff_ratio_tendsto l (fun x => c * g x) g hg).mp h
  have hc : Tendsto (fun _ : X => c) l (𝓝 0) := by
    apply ht.congr'
    filter_upwards [hg] with x hx
    simp [hx]
  exact tendsto_nhds_unique tendsto_const_nhds hc

/-- An expansion through the successor order is also an expansion through
its predecessor, with the same coefficients. -/
private theorem expansionThrough_predecessor (l : Filter X) (φ : ℕ → X → K)
    (a : ℕ → K) (f : X → K) (m : ℕ) (hφ : IsScalarAsymptoticScale l φ)
    (ha : HasScalarExpansionThrough l φ a f (m + 1)) :
    HasScalarExpansionThrough l φ a f m := by
  have hr := scalarLittleO_trans_bigO l
    (fun x => f x - AsymptoticPartialSum φ a (m + 1) x) (φ (m + 1)) (φ m)
    ha (scalarLittleO_isBigO l _ _ (hφ.2.2 m))
  have ht := scalarLittleO_const_mul l (φ (m + 1)) (φ m) (a (m + 1)) (hφ.2.2 m)
  have hs := scalarLittleO_add l _ _ _ hr ht
  change ScalarLittleO l (fun x => f x - AsymptoticPartialSum φ a m x) (φ m)
  convert hs using 1
  funext x
  rw [asymptoticPartialSum_succ]
  ring

private theorem expansionThrough_partialSum_sub (l : Filter X) (φ : ℕ → X → K)
    (a b : ℕ → K) (f : X → K) (m : ℕ)
    (ha : HasScalarExpansionThrough l φ a f m)
    (hb : HasScalarExpansionThrough l φ b f m) :
    ScalarLittleO l (fun x => AsymptoticPartialSum φ a m x -
      AsymptoticPartialSum φ b m x) (φ m) := by
  apply (scalarLittleO_iff_isLittleO l _ _).mpr
  have h := ((scalarLittleO_iff_isLittleO l _ _).mp hb).sub
    ((scalarLittleO_iff_isLittleO l _ _).mp ha)
  exact h.congr_left (fun x => by ring)

/-- Two finite expansions of the same function in a fixed scale have equal
coefficients at every index in the expansion. -/
theorem expansionThrough_coefficients_unique (l : Filter X) (φ : ℕ → X → K)
    (a b : ℕ → K) (f : X → K) (m : ℕ)
    (hφ : IsScalarAsymptoticScale l φ)
    (ha : HasScalarExpansionThrough l φ a f m)
    (hb : HasScalarExpansionThrough l φ b f m) :
    ∀ j, j ≤ m → a j = b j := by
  induction m with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    apply sub_eq_zero.mp
    apply mul_self_littleO_constant_zero l (φ 0) (a 0 - b 0) hφ.1 (hφ.2.1 0)
    have h := expansionThrough_partialSum_sub l φ a b f 0 ha hb
    simpa only [asymptoticPartialSum_zero, sub_mul] using h
  | succ m ih =>
    have hprev := ih (expansionThrough_predecessor l φ a f m hφ ha)
      (expansionThrough_predecessor l φ b f m hφ hb)
    have hp : ∀ x, AsymptoticPartialSum φ a m x = AsymptoticPartialSum φ b m x := by
      intro x
      apply Finset.sum_congr rfl
      intro j hj
      rw [hprev j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    have hlast : a (m + 1) = b (m + 1) := by
      apply sub_eq_zero.mp
      apply mul_self_littleO_constant_zero l (φ (m + 1)) (a (m + 1) - b (m + 1))
        hφ.1 (hφ.2.1 (m + 1))
      have h := expansionThrough_partialSum_sub l φ a b f (m + 1) ha hb
      convert h using 1
      funext x
      rw [asymptoticPartialSum_succ, asymptoticPartialSum_succ, hp x]
      ring
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | heq
    · exact hprev j (Nat.le_of_lt_succ hlt)
    · simpa only [heq] using hlast

/-- All finite orders use the same coefficient sequence, so finite uniqueness
implies equality of the entire sequences. -/
theorem asymptoticExpansion_coefficients_unique (l : Filter X) (φ : ℕ → X → K)
    (a b : ℕ → K) (f : X → K) (hφ : IsScalarAsymptoticScale l φ)
    (ha : HasScalarAsymptoticExpansion l φ a f)
    (hb : HasScalarAsymptoticExpansion l φ b f) : a = b := by
  funext j
  exact expansionThrough_coefficients_unique l φ a b f j hφ (ha j) (hb j) j le_rfl

end SingleVariableAnalysis
