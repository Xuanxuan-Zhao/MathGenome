import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.BarrierSqueeze

/-! The punctured-disk counterexample in paper.tex:2643–2651. The total
representative of the boundary datum matters only on the frontier. -/
noncomputable section
open Set Metric Filter
open scoped Topology

namespace Specs.D12Complex.Ch14.PunctureIrregularity
open _root_.D12Complex

def puncturedDisk_type := Set ℂ
def puncturedDisk_value : Set ℂ := ball 0 1 \ {0}
def punctureDatum_type := ℂ → ℝ
def punctureDatum_value : ℂ → ℝ := fun z => if z = 0 then 1 else 0

local notation "puncturedDisk" => puncturedDisk_value
local notation "punctureDatum" => punctureDatum_value

def punctured_disk_geometry_type : Prop :=
  IsDomain puncturedDisk ∧ Bornology.IsBounded puncturedDisk ∧
    closure puncturedDisk = closedBall 0 1 ∧
    frontier puncturedDisk = {0} ∪ sphere 0 1

def puncture_datum_continuous_type : Prop :=
  ContinuousOn punctureDatum (frontier puncturedDisk) ∧ punctureDatum 0 = 1 ∧
    ∀ z ∈ sphere (0 : ℂ) 1, punctureDatum z = 0

def no_dirichlet_solution_type : Prop :=
  ¬ ∃ u : ℂ → ℝ, ContinuousOn u (closure puncturedDisk) ∧
    HarmonicOn puncturedDisk u ∧ EqOn u punctureDatum (frontier puncturedDisk)

def puncture_perron_zero_type : Prop :=
  ∀ z ∈ puncturedDisk, perronEnvelope puncturedDisk punctureDatum z = 0

def puncture_boundary_failure_type : Prop :=
  ¬ Tendsto (perronEnvelope puncturedDisk punctureDatum)
    (𝓝[puncturedDisk] 0) (𝓝 (punctureDatum 0))

def puncture_no_barrier_type : Prop :=
  (¬ ∃ r : ℝ, ∃ b : ℂ → ℝ,
    Specs.D12Complex.Ch14.BarrierSqueeze.PositiveLocalBarrier_value puncturedDisk 0 r b) ∧
  ¬ Specs.D12Complex.Ch14.BarrierSqueeze.RegularBoundaryPoint_value puncturedDisk 0

end Specs.D12Complex.Ch14.PunctureIrregularity
