import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.PivotedLU
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.GammaProducts

/-! W22. A row is indexed by its original identity in `state` and `ell`.
`order t` maps current positions to those identities. Thus a row exchange moves
both the trailing data and every previously stored multiplier. This is the
multiplier-preserving convention of W20, represented without physically copying
rows. There are n stages; the last stage is a harmless identity exchange, with
no division or trailing update. In particular its diagonal may be zero.
-/
noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LinearAlgebra.Doolittle
open NumAnalysis206.MatrixDefinitions

/-- The actual sequential arithmetic execution. No error estimate or
factorization is a field of this structure. `state` retains unused eliminated
entries; the output U explicitly clears them and L stores the divisions. -/
structure Run {n : ℕ} (round : ℝ → ℝ) (D : Set ℝ) (A : Mat ℝ n n) where
  order : ℕ → Equiv.Perm (Fin n)
  state : ℕ → Mat ℝ n n
  choice : Fin n → Fin n
  ell : Fin n → Fin n → ℝ
  order_zero : order 0 = Equiv.refl _
  state_zero : state 0 = A
  choice_ge : ∀ t, t ≤ choice t
  exchange : ∀ t : Fin n,
    order (t.val + 1) = (Equiv.swap t (choice t)).trans (order t.val)
  division : ∀ (t : Fin n) (a : Fin n),
    t.val < ((order (t.val + 1)).symm a).val →
    state t.val (order (t.val + 1) t) t ≠ 0 ∧
    state t.val a t / state t.val (order (t.val + 1) t) t ∈ D ∧
    ell t a = round (state t.val a t / state t.val (order (t.val + 1) t) t)
  safety : ∀ (t : Fin n) (a j : Fin n),
    t.val < ((order (t.val + 1)).symm a).val → t < j →
    ell t a * state t.val (order (t.val + 1) t) j ∈ D ∧
    state t.val a j - round (ell t a * state t.val (order (t.val + 1) t) j) ∈ D
  update : ∀ (t : Fin n) (a j : Fin n),
    state (t.val + 1) a j =
      if t.val < ((order (t.val + 1)).symm a).val ∧ t < j then
        round (state t.val a j - round (ell t a * state t.val (order (t.val + 1) t) j))
      else state t.val a j

namespace Run
variable {n : ℕ} {round : ℝ → ℝ} {D : Set ℝ} {A : Mat ℝ n n}

def permutation (R : Run round D A) : Equiv.Perm (Fin n) := R.order n

def lower (R : Run round D A) : Mat ℝ n n := fun i j =>
  if j < i then R.ell j (R.permutation i) else if i = j then 1 else 0

def upper (R : Run round D A) : Mat ℝ n n := fun i j =>
  if i ≤ j then R.state i.val (R.permutation i) j else 0
end Run
end NumAnalysis206.LinearAlgebra.Doolittle

namespace Specs.NumAnalysis206.LinearAlgebra.Doolittle
open _root_.NumAnalysis206.MatrixDefinitions
open _root_.NumAnalysis206.LinearAlgebra.Doolittle
open _root_.NumAnalysis206.PivotedLU

/-- W22, with the actual stored factors and the final row permutation.
The safe-domain relative model includes 0 ≤ u < 1. -/
def backward_error : Prop :=
  ∀ {n : ℕ} (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ) (A : Mat ℝ n n),
    _root_.NumAnalysis206.Rounding.Specs.RelativeModelValue round u D →
    (R : Run round D A) → (3 * (n : ℝ)) * u < 1 →
    ∃ Δ : Mat ℝ n n,
      permutationMatrix R.permutation * A + Δ = R.lower * R.upper ∧
      EntrywiseLE (entrywiseAbs Δ)
        ((Specs.NumAnalysis206.Rounding.gammaValue (3 * n) u) •
          (entrywiseAbs R.lower * entrywiseAbs R.upper))
end Specs.NumAnalysis206.LinearAlgebra.Doolittle
