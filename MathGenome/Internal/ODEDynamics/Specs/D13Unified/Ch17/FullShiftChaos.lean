import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ChaosDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces
import Mathlib.SetTheory.Cardinal.Finite

/-! Full independent statements for paper.tex, Theorem `d13:17:full-shift-chaos`.
All topological assertions use the native product topology. Sensitivity uses
exactly the two distances specified in the paper. The final chaos assertions
also exhibit compatible metric structures, making the metric predicate apply
to precisely those distances. Fixed-point counts count all n-fixed points. -/
namespace Specs.D13Unified.Ch17.FullShiftChaos
open Set
open scoped Topology
open ShiftSpaces ChaosDefinitions

def shiftPlus_transitiveStatement : Prop := TopologicallyTransitive shiftPlus
def shift_transitiveStatement : Prop := TopologicallyTransitive shift
def shiftPlus_dense_periodicStatement : Prop := DensePeriodicPoints shiftPlus
def shift_dense_periodicStatement : Prop := DensePeriodicPoints shift
def shiftPlus_sensitiveStatement : Prop :=
   ∀ s : OneSided, ∀ U ∈ 𝓝 s, ∃ t ∈ U, ∃ n : ℕ,
     (1 / 2 : ℝ) < distancePlus (shiftPlus^[n] s) (shiftPlus^[n] t)
def shift_sensitiveStatement : Prop :=
   ∀ s : TwoSided, ∀ U ∈ 𝓝 s, ∃ t ∈ U, ∃ n : ℕ,
     (1 / 8 : ℝ) < distance (shift^[n] s) (shift^[n] t)
def shiftPlus_fixed_cardStatement : Prop :=
   ∀ n : ℕ, 0 < n → Nat.card {s : OneSided // shiftPlus^[n] s = s} = 2 ^ n
def shift_fixed_cardStatement : Prop :=
   ∀ n : ℕ, 0 < n → Nat.card {s : TwoSided // shift^[n] s = s} = 2 ^ n
def shiftPlus_dense_orbitStatement : Prop :=
   ∃ s : OneSided, Dense (range (fun n : ℕ => shiftPlus^[n] s))
def shift_dense_orbitStatement : Prop :=
   ∃ s : TwoSided, Dense (range (fun n : ℕ => shift^[n] s))
def shiftPlus_chaoticStatement : Prop :=
   ∃ m : MetricSpace OneSided,
     m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
       (inferInstance : TopologicalSpace OneSided) ∧
     (∀ s t, @dist _ m.toDist s t = distancePlus s t) ∧
     @Chaotic OneSided m shiftPlus
def shift_chaoticStatement : Prop :=
   ∃ m : MetricSpace TwoSided,
     m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
       (inferInstance : TopologicalSpace TwoSided) ∧
     (∀ s t, @dist _ m.toDist s t = distance s t) ∧
     @Chaotic TwoSided m shift
end Specs.D13Unified.Ch17.FullShiftChaos
