import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums
import Mathlib.Tactic.NormNum

/-! K03.15.rs_mesh_counterexample, paper.tex:3786–3793.
Closed-cell tags and the original refinement integral are used unchanged.
The mesh predicate quantifies over all partitions, without mandatory nodes. -/
namespace SingleVariableAnalysis.Stieltjes.MeshCounterexample
open Riemann

noncomputable def integrator (x : ℝ) : ℝ := if x ≤ 0 then 0 else 1
noncomputable def integrand (x : ℝ) : ℝ := if x < 0 then 0 else 1

/-- The partition (-1,0,1). -/
def base : PartitionData (-1) 1 where
  n := 2
  point i := (i.val : ℝ) - 1
  strictMono := fun _ _ hij => sub_lt_sub_right (Nat.cast_lt.mpr hij) 1
  first := by norm_num
  last := by norm_num

/-- Unrestricted convergence as the mesh tends to zero. -/
def MeshLimit (I : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ P : PartitionData (-1) 1,
      Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue P < δ →
      ∀ t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
        ‖Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue P t integrand integrator - I‖ < ε

end SingleVariableAnalysis.Stieltjes.MeshCounterexample

namespace Specs.SingleVariableAnalysis.Ch15.RsMeshCounterexample
open _root_.SingleVariableAnalysis.Riemann
open _root_.SingleVariableAnalysis.Stieltjes.MeshCounterexample
open Specs.SingleVariableAnalysis.Ch08.Partitions
open Specs.SingleVariableAnalysis.Ch15.RsSums

/-- The sole nonzero increment is on the first cell to the right of zero;
all closed-cell tags there give integrand value one. -/
def uniqueIncrement : Prop := ∀ P : PartitionData (-1) 1,
  refinesValue P base → ∃ i : Fin P.n,
    P.point i.castSucc = 0 ∧ 0 < P.point i.succ ∧
    (∀ j : Fin P.n, integrator (P.point j.succ) - integrator (P.point j.castSucc) =
      if j = i then 1 else 0) ∧
    ∀ t : taggingValue P, integrand (t i) = 1

def refinementSums : Prop := ∀ P : PartitionData (-1) 1,
  refinesValue P base → ∀ t : taggingValue P, sumValue P t integrand integrator = 1

def refinementIntegral : Prop := integralValue (-1) 1 integrand integrator 1

/-- On any crossing cell the entire sum is determined by its tag. This includes
negative tags (zero sum), zero, and all positive tags (sum one). -/
def crossingSums : Prop := ∀ (P : PartitionData (-1) 1) (i : Fin P.n),
  P.point i.castSucc < 0 → 0 < P.point i.succ →
    (∀ j : Fin P.n, integrator (P.point j.succ) - integrator (P.point j.castSucc) =
      if j = i then 1 else 0) ∧
    ∀ t : taggingValue P, sumValue P t integrand integrator = integrand (t i)

/-- At any prescribed mesh scale there is a symmetric crossing cell, no node
at zero, and negative, positive, and zero tags giving the stated sums. -/
def fineCrossingSums : Prop := ∀ δ : ℝ, 0 < δ →
  ∃ P : PartitionData (-1) 1,
    0 < meshValue P ∧ meshValue P < δ ∧ 0 ∉ pointsValue P ∧
    ∃ (h : ℝ) (i : Fin P.n), 0 < h ∧ h < δ / 2 ∧
      P.point i.castSucc = -h ∧ P.point i.succ = h ∧
      (∃ t : taggingValue P, (t i : ℝ) < 0 ∧ sumValue P t integrand integrator = 0) ∧
      (∃ t : taggingValue P, (t i : ℝ) > 0 ∧ sumValue P t integrand integrator = 1) ∧
      (∃ t : taggingValue P, (t i : ℝ) = 0 ∧ sumValue P t integrand integrator = 1)

def noMeshLimit : Prop := ¬ ∃ I : ℝ, MeshLimit I

end Specs.SingleVariableAnalysis.Ch15.RsMeshCounterexample
