import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SequenceLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Subsequence

/-!
# Subsequences and subsequential limits

This implements `K03.01.subsequence` (paper.tex:260–269). The indexing convention
is inherited from `SequenceLimit`: the value `a n` denotes the positive-indexed
term `a_{n+1}`. Thus `a ∘ φ` at position `j + 1` selects term `φ j + 1`.
Every strictly increasing map between positive indices corresponds to such a
`φ` by subtracting one from its input and output indices, and conversely.

The proof uses the manuscript's induction `j ≤ φ j`. Consequently an estimate
on the original tail starting at `N` applies to the selected terms for every
`j ≥ N`. No boundedness or convergence assumption on any other sequence is used.
-/

namespace SingleVariableAnalysis

universe u

/-- `b` is a subsequence of `a`, selected by a strictly increasing index map. -/
def IsSubsequence {α : Type u} (b a : ℕ → α) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ b = a ∘ φ

/-- A finite real value is a subsequential limit when some selected sequence
converges to that value. -/
def RealSubsequentialLimit (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ RealSequenceConverges (a ∘ φ) L

/-- A finite complex subsequential limit, using the canonical complex modulus. -/
def ComplexSubsequentialLimit (a : ℕ → ℂ) (L : ℂ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ComplexSequenceConverges (a ∘ φ) L

theorem subsequenceIndex_ge (φ : ℕ → ℕ) (hφ : StrictMono φ) (j : ℕ) :
    j ≤ φ j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j hj =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hj (hφ (Nat.lt_succ_self j)))

/-- Any original tail estimate holds on the same tail of the subsequence. -/
theorem sequenceEventually_comp (P : ℕ → Prop) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (h : SequenceEventually P) : SequenceEventually (P ∘ φ) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun j hj => hN (φ j) (hj.trans (subsequenceIndex_ge φ hφ j))⟩

theorem realSequenceConverges_comp (a : ℕ → ℝ) (L : ℝ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (h : RealSequenceConverges a L) :
    RealSequenceConverges (a ∘ φ) L := by
  intro ε hε
  exact sequenceEventually_comp (fun n => |a n - L| < ε) φ hφ (h ε hε)

theorem complexSequenceConverges_comp (a : ℕ → ℂ) (L : ℂ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (h : ComplexSequenceConverges a L) :
    ComplexSequenceConverges (a ∘ φ) L := by
  intro ε hε
  exact sequenceEventually_comp (fun n => ‖a n - L‖ < ε) φ hφ (h ε hε)

theorem realSequenceConverges_of_isSubsequence (a b : ℕ → ℝ) (L : ℝ)
    (hb : IsSubsequence b a) (h : RealSequenceConverges a L) :
    RealSequenceConverges b L := by
  obtain ⟨φ, hφ, rfl⟩ := hb
  exact realSequenceConverges_comp a L φ hφ h

theorem complexSequenceConverges_of_isSubsequence (a b : ℕ → ℂ) (L : ℂ)
    (hb : IsSubsequence b a) (h : ComplexSequenceConverges a L) :
    ComplexSequenceConverges b L := by
  obtain ⟨φ, hφ, rfl⟩ := hb
  exact complexSequenceConverges_comp a L φ hφ h

end SingleVariableAnalysis
