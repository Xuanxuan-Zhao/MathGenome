import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.AsymptoticScale

/-!
# Asymptotic scales and finite expansions

K03.17.asymptotic_scale, paper.tex:4306–4319. The common filter specifies
both the domain and the direction of the limit. Its nontriviality is retained
in the scale predicate. The normed-field formulation specializes to ℝ and ℂ.

Expansions through index `m` contain exactly the terms `0, …, m`. An
all-orders expansion fixes one coefficient sequence and asserts each finite
remainder bound. These definitions introduce no infinite sum or convergence
claim. They are remainder predicates for a family; the hypothesis that the
family is an asymptotic scale is stated separately when required.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology BigOperators
universe u v

/-- An eventually nonzero scale on a fixed nontrivial approach, in decreasing
asymptotic order. -/
def IsScalarAsymptoticScale {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) : Prop :=
  l.NeBot ∧ (∀ j, ∀ᶠ x in l, φ j x ≠ 0) ∧
    ∀ j, ScalarLittleO l (φ (j + 1)) (φ j)

/-- A finite sum including the zeroth and the `m`th terms. -/
def AsymptoticPartialSum {X : Type u} {K : Type v} [NormedField K]
    (φ : ℕ → X → K) (a : ℕ → K) (m : ℕ) (x : X) : K :=
  ∑ j ∈ Finset.range (m + 1), a j * φ j x

/-- The remainder after a finite expansion through index `m` is `o(φ m)`.
The scale condition on `φ` is a separate hypothesis. -/
def HasScalarExpansionThrough {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) (a : ℕ → K) (f : X → K) (m : ℕ) : Prop :=
  ScalarLittleO l (fun x => f x - AsymptoticPartialSum φ a m x) (φ m)

/-- Every finite-order remainder bound, with the same coefficients at all orders. -/
def HasScalarAsymptoticExpansion {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) (a : ℕ → K) (f : X → K) : Prop :=
  ∀ m, HasScalarExpansionThrough l φ a f m

section Scalar

variable {X : Type u} {K : Type v} [NormedField K]

theorem isScalarAsymptoticScale_iff (l : Filter X) (φ : ℕ → X → K) :
    IsScalarAsymptoticScale l φ ↔
      l.NeBot ∧ (∀ j, ∀ᶠ x in l, φ j x ≠ 0) ∧
        ∀ j, ScalarLittleO l (φ (j + 1)) (φ j) := Iff.rfl

theorem isScalarAsymptoticScale_neBot (l : Filter X) (φ : ℕ → X → K)
    (hφ : IsScalarAsymptoticScale l φ) : l.NeBot := hφ.1

theorem isScalarAsymptoticScale_eventually_ne_zero (l : Filter X) (φ : ℕ → X → K)
    (hφ : IsScalarAsymptoticScale l φ) (j : ℕ) : ∀ᶠ x in l, φ j x ≠ 0 := hφ.2.1 j

/-- Iterating adjacent little-o comparisons gives every strictly later term.
Each induction step uses transitivity of the norm inequalities; no infinite
product is formed. -/
theorem isScalarAsymptoticScale_littleO (l : Filter X) (φ : ℕ → X → K)
    (hφ : IsScalarAsymptoticScale l φ) {j k : ℕ} (hjk : j < k) :
    ScalarLittleO l (φ k) (φ j) := by
  apply (scalarLittleO_iff_isLittleO l (φ k) (φ j)).mpr
  have hchain : ∀ n, j < n → Asymptotics.IsLittleO l (φ n) (φ j) := by
    intro n
    induction n with
    | zero => exact fun h => (Nat.not_lt_zero j h).elim
    | succ n ih =>
      intro hjn
      have hstep := (scalarLittleO_iff_isLittleO l (φ (n + 1)) (φ n)).mp (hφ.2.2 n)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hlt | heq
      · exact hstep.trans (ih hlt)
      · simpa only [heq] using hstep
  exact hchain k hjk

/-- The denominator is nonzero on a tail, so the little-o comparison has
precisely the manuscript's quotient-limit meaning. -/
theorem isScalarAsymptoticScale_ratio_tendsto (l : Filter X) (φ : ℕ → X → K)
    (hφ : IsScalarAsymptoticScale l φ) {j k : ℕ} (hjk : j < k) :
    Tendsto (fun x => φ k x / φ j x) l (𝓝 0) := by
  exact (scalarLittleO_iff_ratio_tendsto l (φ k) (φ j) (hφ.2.1 j)).mp
    (isScalarAsymptoticScale_littleO l φ hφ hjk)

theorem asymptoticPartialSum_zero (φ : ℕ → X → K) (a : ℕ → K) (x : X) :
    AsymptoticPartialSum φ a 0 x = a 0 * φ 0 x := by
  simp [AsymptoticPartialSum]

theorem asymptoticPartialSum_succ (φ : ℕ → X → K) (a : ℕ → K) (m : ℕ) (x : X) :
    AsymptoticPartialSum φ a (m + 1) x =
      AsymptoticPartialSum φ a m x + a (m + 1) * φ (m + 1) x := by
  exact Finset.sum_range_succ (fun j => a j * φ j x) (m + 1)

theorem hasScalarExpansionThrough_iff (l : Filter X) (φ : ℕ → X → K)
    (a : ℕ → K) (f : X → K) (m : ℕ) :
    HasScalarExpansionThrough l φ a f m ↔
      ScalarLittleO l
        (fun x => f x - ∑ j ∈ Finset.range (m + 1), a j * φ j x) (φ m) := Iff.rfl

theorem hasScalarAsymptoticExpansion_iff (l : Filter X) (φ : ℕ → X → K)
    (a : ℕ → K) (f : X → K) :
    HasScalarAsymptoticExpansion l φ a f ↔
      ∀ m, HasScalarExpansionThrough l φ a f m := Iff.rfl

theorem hasScalarAsymptoticExpansion_through (l : Filter X) (φ : ℕ → X → K)
    (a : ℕ → K) (f : X → K) (h : HasScalarAsymptoticExpansion l φ a f) (m : ℕ) :
    HasScalarExpansionThrough l φ a f m := h m

end Scalar

end SingleVariableAnalysis
