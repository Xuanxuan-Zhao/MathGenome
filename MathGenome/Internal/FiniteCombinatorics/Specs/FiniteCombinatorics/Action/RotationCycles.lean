import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.CycleIndex
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient

/-! Independent specification of the rotation classification in paper.tex W34.
The index `i : Fin |ZMod n|` denotes s_(i+1), as in the shared cycle index.
`NeZero n` expresses precisely the source assumption n ≥ 1. -/
namespace FiniteCombinatorics.RotationCyclesSpec

/-- Rotation through the residue a, acting on every position by x ↦ x+a. -/
def rotation {n : ℕ} (a : ZMod n) : Equiv.Perm (ZMod n) := Equiv.addRight a

/-- The gcd uses the canonical least nonnegative representative. -/
def returnTime {n : ℕ} (a : ZMod n) : ℕ := n / n.gcd a.val

/-- The source variable s_d in the shared polynomial ring. The fallback is
irrelevant for the positive lengths at most n occurring in the theorems. -/
noncomputable def lengthVariable (n : ℕ) [NeZero n] (d : ℕ) :
    MvPolynomial (Fin (Fintype.card (ZMod n))) ℚ :=
  if h : 0 < d ∧ d ≤ n then
    MvPolynomial.X ⟨d - 1, by rw [ZMod.card]; omega⟩
  else 1

def rotationType := {n : ℕ} → ZMod n → Equiv.Perm (ZMod n)
def returnTimeType := {n : ℕ} → ZMod n → ℕ
def lengthVariableType := ∀ (n : ℕ) [NeZero n], ℕ →
  MvPolynomial (Fin (Fintype.card (ZMod n))) ℚ

def Representative : Prop := ∀ {n : ℕ} [NeZero n] (k : ℕ),
  returnTime (k : ZMod n) = n / n.gcd k

def ReturnCriterion : Prop := ∀ {n : ℕ} [NeZero n] (a x : ZMod n) (m : ℕ),
  (rotation a ^ m) x = x ↔ returnTime a ∣ m

def Bounds : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n),
  0 < returnTime a ∧ returnTime a ≤ n ∧ returnTime a ∣ n

def CycleLength : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n) (C : Finset (ZMod n)),
  C ∈ PermutationCyclesSpec.cycles (rotation a) → C.card = returnTime a

def CycleCount : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n),
  (PermutationCyclesSpec.cycles (rotation a)).card = n / returnTime a

def LengthCount : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ),
  PermutationCyclesSpec.countCyclesOfLength (rotation a) k =
    if k = returnTime a then n / returnTime a else 0

def Monomial : Prop := ∀ {n : ℕ} [NeZero n] (a : ZMod n),
  CycleIndexSpec.permutationMonomial (ZMod n) (rotation a) =
    lengthVariable n (returnTime a) ^ (n / returnTime a)

def TotientCount : Prop := by
  classical
  exact ∀ {n : ℕ} [NeZero n] (d : ℕ), 0 < d → d ∣ n →
    (Finset.univ.filter (fun a : ZMod n => returnTime a = d)).card = Nat.totient d

/-- The identity is included as a length-one rotation, also when n=1. -/
def Identity : Prop := ∀ {n : ℕ} [NeZero n], returnTime (0 : ZMod n) = 1

end FiniteCombinatorics.RotationCyclesSpec
