import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.ENNReal.Real

/-!
Independent specification of paper.tex:4499–4511 (`fa2:p1:james-space-definition`).

A natural coordinate `n` denotes manuscript coordinate `n+1`. Every length at
least two is uniquely of the form `k+2`; thus the supremum below includes exactly
all the manuscript's increasing finite lists. The sum has `k+1` adjacent edges
and, separately, the closing edge from the last entry to the first.

The supremum is taken in `ℝ≥0∞` so that infinite variation is recorded faithfully.
Only null sequences with finite variation enter the space. The real norm is
obtained by `toReal` on that subtype; `norm_finite` specifies the recovery of its
extended value. The norm axioms and Banach/basis structure are subsequent goals.
-/

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal

namespace ExpandedFA.P1.JamesSpec

def CyclicEnergyType := (ℕ → ℝ) → (k : ℕ) → (Fin (k + 2) → ℕ) → ℝ

def cyclicEnergyValue : CyclicEnergyType := fun a k p =>
  (∑ j : Fin (k + 1), (a (p j.castSucc) - a (p j.succ)) ^ 2) +
    (a (p (Fin.last (k + 1))) - a (p 0)) ^ 2

def ExtendedNormType := (ℕ → ℝ) → ℝ≥0∞

def extendedNormValue : ExtendedNormType := fun a =>
  ENNReal.ofReal (1 / Real.sqrt 2) *
    ⨆ (k : ℕ) (p : Fin (k + 2) → ℕ) (_hp : StrictMono p),
      ENNReal.ofReal (Real.sqrt (cyclicEnergyValue a k p))

def MembershipType := (ℕ → ℝ) → Prop

def membershipValue : MembershipType := fun a =>
  Tendsto a atTop (𝓝 0) ∧ extendedNormValue a ≠ ⊤

def SpaceType := Type

def spaceValue : SpaceType := {a : ℕ → ℝ // membershipValue a}

def NormType := spaceValue → ℝ

def normValue : NormType := fun a => (extendedNormValue a.val).toReal

def NormInstanceType := Norm spaceValue

def normInstanceValue : NormInstanceType := ⟨normValue⟩

/-- Taking the real norm does not discard an infinite value. -/
def NormFinite : Prop :=
  ∀ a : spaceValue, ENNReal.ofReal (normValue a) = extendedNormValue a.val

/-- Exact description of the underlying set, including the null condition. -/
def SpaceCharacterization : Prop :=
  ∀ a : ℕ → ℝ, (∃ x : spaceValue, x.val = a) ↔
    Tendsto a atTop (𝓝 0) ∧ extendedNormValue a < ⊤

/-- In particular the zero sequence is retained. -/
def ZeroMember : Prop := membershipValue (fun _ => 0)

end ExpandedFA.P1.JamesSpec
