import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SequenceLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Pointwise

/-!
# Pointwise convergence

Implements `K03.12.pointwise` (paper.tex:1190–1197). `E` is the domain
itself; for functions on a subset use the corresponding subtype. The domain
is arbitrary and may be empty. Indices follow the upstream shifted convention:
`F n` represents the manuscript's term numbered `n + 1`.

Each point has its own scalar sequence limit, so the tail index may depend on
that point. Uniqueness follows point by point from Hausdorff uniqueness of the
canonical real and complex metric limits, through the upstream equivalences.
-/

namespace SingleVariableAnalysis

universe u

/-- Pointwise real convergence; the tail threshold may depend on the point. -/
def RealPointwiseConverges {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) : Prop :=
  ∀ x, RealSequenceConverges (fun n => F n x) (f x)

/-- Pointwise complex convergence, using the usual complex modulus. -/
def ComplexPointwiseConverges {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) : Prop :=
  ∀ x, ComplexSequenceConverges (fun n => F n x) (f x)

theorem realPointwiseConverges_epsilon_iff {E : Type u}
    (F : ℕ → E → ℝ) (f : E → ℝ) :
    RealPointwiseConverges F f ↔
      ∀ x, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |F n x - f x| < ε := Iff.rfl

theorem complexPointwiseConverges_epsilon_iff {E : Type u}
    (F : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexPointwiseConverges F f ↔
      ∀ x, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖F n x - f x‖ < ε := Iff.rfl

theorem realPointwiseConverges_sequence_iff {E : Type u}
    (F : ℕ → E → ℝ) (f : E → ℝ) :
    RealPointwiseConverges F f ↔
      ∀ x, RealSequenceConverges (fun n => F n x) (f x) := Iff.rfl

theorem complexPointwiseConverges_sequence_iff {E : Type u}
    (F : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexPointwiseConverges F f ↔
      ∀ x, ComplexSequenceConverges (fun n => F n x) (f x) := Iff.rfl

theorem realPointwiseLimit_unique {E : Type u}
    (F : ℕ → E → ℝ) (f g : E → ℝ)
    (hf : RealPointwiseConverges F f) (hg : RealPointwiseConverges F g) : f = g := by
  funext x
  exact tendsto_nhds_unique
    ((realSequenceConverges_iff _ _).mp (hf x))
    ((realSequenceConverges_iff _ _).mp (hg x))

theorem complexPointwiseLimit_unique {E : Type u}
    (F : ℕ → E → ℂ) (f g : E → ℂ)
    (hf : ComplexPointwiseConverges F f) (hg : ComplexPointwiseConverges F g) : f = g := by
  funext x
  exact tendsto_nhds_unique
    ((complexSequenceConverges_iff _ _).mp (hf x))
    ((complexSequenceConverges_iff _ _).mp (hg x))

/-- The empty function to either of the manuscript's scalar types. -/
def emptyScalarFunction (k : ScalarKind) (E : Type u) [IsEmpty E] : E → Scalar k :=
  fun x => isEmptyElim x

theorem emptyScalarFunction_unique (k : ScalarKind) (E : Type u) [IsEmpty E]
    (f : E → Scalar k) : f = emptyScalarFunction k E := by
  funext x
  exact isEmptyElim x

theorem realPointwiseConverges_empty {E : Type u} [IsEmpty E]
    (F : ℕ → E → ℝ) (f : E → ℝ) : RealPointwiseConverges F f := by
  intro x
  exact isEmptyElim x

theorem complexPointwiseConverges_empty {E : Type u} [IsEmpty E]
    (F : ℕ → E → ℂ) (f : E → ℂ) : ComplexPointwiseConverges F f := by
  intro x
  exact isEmptyElim x

end SingleVariableAnalysis
