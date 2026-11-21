import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.NonclosedPSDImage
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
Independent statements for paper.tex, Proposition `prop:sdp-weak-infeasibility`
(lines 2547–2574), using exactly the cone and projection of §1.7.
Weak infeasibility here means absence of a PSD lift together with membership
in the closure of the image. The explicit matrices use positive natural indices.
-/

noncomputable section
open Set Filter
open VariationalNotes.ConvexGeometry.Specs.PSDImage

namespace VariationalNotes.Ch05.SemidefiniteWeakInfeasibility.Specs

def projectedCone_description : Prop :=
  projectedCone = {p : ℝ × ℝ | 0 < p.1} ∪ {(0, 0)}

def approximating_matrices : Prop :=
  ∀ n : ℕ, 0 < n →
    symmetricMatrix (1 / (n : ℝ)) 1 (n : ℝ) ∈ psdCone ∧
    projection (symmetricMatrix (1 / (n : ℝ)) 1 (n : ℝ)) = (1 / (n : ℝ), 1)

def projected_matrices_tendsto : Prop :=
  Tendsto (fun n : ℕ => projection (symmetricMatrix (1 / (n : ℝ)) 1 (n : ℝ)))
    atTop (nhds (0, 1))

def target_not_mem : Prop := (0, 1) ∉ projectedCone

def target_mem_closure : Prop := (0, 1) ∈ closure projectedCone

def target_weakly_infeasible : Prop :=
  (¬ ∃ M ∈ psdCone, projection M = (0, 1)) ∧ (0, 1) ∈ closure projectedCone

def nonnegative_at_target : Prop :=
  ∀ l : (ℝ × ℝ) →L[ℝ] ℝ,
    (∀ p ∈ projectedCone, 0 ≤ l p) → 0 ≤ l (0, 1)

def no_strict_farkas_certificate : Prop :=
  ¬ ∃ l : (ℝ × ℝ) →L[ℝ] ℝ,
    (∀ p ∈ projectedCone, 0 ≤ l p) ∧ l (0, 1) < 0

end VariationalNotes.Ch05.SemidefiniteWeakInfeasibility.Specs
