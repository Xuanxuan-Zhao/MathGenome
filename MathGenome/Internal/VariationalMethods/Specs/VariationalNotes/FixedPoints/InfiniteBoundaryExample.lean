import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Sequences

/-! The coordinates are indexed by ℕ: coordinate 0 here is coordinate 1 in the notes. -/
namespace VariationalNotes.InfiniteBoundary

abbrev H := lp (fun _ : ℕ => ℝ) 2

def ball : Set H := Metric.closedBall 0 1
abbrev B := {x : H // x ∈ ball}

/-- Prepend a real coordinate to a square-summable sequence. -/
noncomputable def prepend (a : ℝ) (x : H) : H :=
  ⟨fun n => Nat.casesOn n a x, memℓp_gen <| (summable_nat_add_iff 1).mp <| by
    simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)⟩

noncomputable def map (x : B) : H := prepend (Real.sqrt (1 - ‖(x : H)‖ ^ 2)) x

noncomputable def basis (n : ℕ) : H := lp.single 2 n 1

noncomputable def basisInBall (n : ℕ) : B := ⟨basis n, by
  change dist (basis n) 0 ≤ 1
  simp [dist_zero_right, basis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]⟩

noncomputable def origin : B := ⟨0, by change dist (0 : H) 0 ≤ 1; simp⟩

namespace Spec

def domain : Prop :=
  (0 : H) ∈ ball ∧ IsClosed ball ∧ Bornology.IsBounded ball ∧ Convex ℝ ball

def infiniteDimensional : Prop := ¬ FiniteDimensional ℝ H

def fixedPointFreeSelfMap : Prop :=
  ∃ F : B → B, Continuous F ∧ (∀ x : B, (F x : H) = map x) ∧ ∀ x : B, F x ≠ x

def continuousMap : Prop := Continuous map

def sphere : Prop := ∀ x : B, ‖map x‖ = 1

def noFixedPoint : Prop := ∀ x : B, map x ≠ (x : H)

def atOrigin : Prop := map origin ≠ 0

def onBasis : Prop := ∀ n : ℕ, map (basisInBall n) = basis (n + 1)

def noConvergentSubsequence : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∀ y : H,
    ¬ Filter.Tendsto (fun n => basis (φ n + 1)) Filter.atTop (nhds y)

def imageNotRelativelyCompact : Prop := ¬ IsCompact (closure (Set.range map))

end Spec
end VariationalNotes.InfiniteBoundary
