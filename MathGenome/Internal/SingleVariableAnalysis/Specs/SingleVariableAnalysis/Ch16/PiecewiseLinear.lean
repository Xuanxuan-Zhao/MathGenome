import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Partitions
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.SupSpace
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent specification for K03.16.piecewise_linear (paper.tex:3864–3873).
The domain is the closed real interval, including a singleton. Functions are
canonical continuous maps; partitions are the upstream strict finite partitions.
The modulus is the real supremum over pairs in this interval at distance ≤ δ.
The interpolant selects a closed cell containing x and uses the affine formula.
Agreement on overlapping cells, node values and continuity are proof obligations.
Outside the interval its value is immaterial. On zero-cell partitions it is
constant. The norm is the canonical sup norm, with no extra regularity of f.
-/
namespace Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear
open _root_.SingleVariableAnalysis.Riemann
open scoped Topology

/-- A partition node, regarded as a point of the closed interval. -/
def node {a b : ℝ} (P : PartitionData a b) (i : Fin (P.n + 1)) : Set.Icc a b :=
  ⟨P.point i,
    by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i),
    by simpa only [P.last] using P.strictMono.monotone (Fin.le_last i)⟩

noncomputable def cellValue {a b : ℝ} (P : PartitionData a b)
    (f : C(Set.Icc a b, ℝ)) (i : Fin P.n) (x : ℝ) : ℝ :=
  let t := (x - P.point i.castSucc) / (P.point i.succ - P.point i.castSucc)
  (1-t) * f (node P i.castSucc) + t * f (node P i.succ)

abbrev interpolantType := {a b : ℝ} → (P : PartitionData a b) →
  C(Set.Icc a b, ℝ) → ℝ → ℝ
noncomputable def interpolantValue : interpolantType := fun P f x =>
  if h : ∃ i : Fin P.n, x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ)
  then cellValue P f h.choose x else f (node P 0)

abbrev modulusType := {a b : ℝ} → C(Set.Icc a b, ℝ) → ℝ → ℝ
noncomputable def modulusValue : modulusType := fun {a b} f δ =>
  sSup {r : ℝ | ∃ x y : Set.Icc a b, |(x : ℝ) - (y : ℝ)| ≤ δ ∧ r = |f x - f y|}

def cellFormula : Prop := ∀ {a b : ℝ} (P : PartitionData a b)
  (f : C(Set.Icc a b, ℝ)) (i : Fin P.n) (x : ℝ),
  x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ) →
    interpolantValue P f x = cellValue P f i x

def nodeValues : Prop := ∀ {a b : ℝ} (P : PartitionData a b)
  (f : C(Set.Icc a b, ℝ)) (i : Fin (P.n+1)),
  interpolantValue P f (P.point i) = f (node P i)

def interpolantContinuous : Prop := ∀ {a b : ℝ} (P : PartitionData a b)
  (f : C(Set.Icc a b, ℝ)), ContinuousOn (interpolantValue P f) (Set.Icc a b)

def degenerate : Prop := ∀ (a : ℝ) (P : PartitionData a a)
  (f : C(Set.Icc a a, ℝ)) (x : ℝ), interpolantValue P f x = f (node P 0)

def modulusLimit : Prop := ∀ {a b : ℝ}, a ≤ b → ∀ f : C(Set.Icc a b, ℝ),
  Filter.Tendsto (modulusValue f) (𝓝[Set.Ici 0] 0) (𝓝 0)

/-- In particular the interpolant belongs to C([a,b]) and satisfies the exact
modulus bound in the canonical sup norm. -/
def normBound : Prop := ∀ {a b : ℝ} (P : PartitionData a b)
  (f : C(Set.Icc a b, ℝ)), ∃ L : C(Set.Icc a b, ℝ),
  (∀ x, L x = interpolantValue P f x) ∧
    ‖f - L‖ ≤ modulusValue f (Ch08.Partitions.meshValue P)

/-- This epsilon formulation is uniform over all partitions of small mesh. -/
def approximation : Prop := ∀ {a b : ℝ}, a ≤ b → ∀ f : C(Set.Icc a b, ℝ),
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ P : PartitionData a b, Ch08.Partitions.meshValue P < δ →
      ∃ L : C(Set.Icc a b, ℝ), (∀ x, L x = interpolantValue P f x) ∧ ‖f-L‖ < ε

def convergence : Prop := ∀ {a b : ℝ} (f : C(Set.Icc a b, ℝ))
  (P : ℕ → PartitionData a b),
  Filter.Tendsto (fun n => Ch08.Partitions.meshValue (P n)) Filter.atTop (𝓝 0) →
  ∃ L : ℕ → C(Set.Icc a b, ℝ),
    (∀ n x, L n x = interpolantValue (P n) f x) ∧
    Filter.Tendsto (fun n => ‖f - L n‖) Filter.atTop (𝓝 0) ∧
    Ch12.Uniform.realUniformConvergesValue (fun n x => L n x) f

end Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear
