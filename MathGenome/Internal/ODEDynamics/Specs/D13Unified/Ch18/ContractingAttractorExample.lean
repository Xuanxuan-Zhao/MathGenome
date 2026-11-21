import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.TrappingAttractor
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.GrowthDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ChaosDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Independent statements for the example “Attraction need not mean chaos”,
paper.tex, Chapter 18. The map acts on the whole real line. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch18.ContractingAttractorExample

/-- The actual map in the example. -/
def F (x : ℝ) : ℝ := x / 2

/-- Its compact trapping interval. -/
def K : Set ℝ := Icc (-1) 1

/-- The same map as a C¹ self-map of its actual open domain ℝ. -/
def smoothMap : GrowthDefinitions.C1SelfMap ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  value := F
  mapsTo := fun _ _ => mem_univ _
  contDiffOn := (contDiff_id.div_const (2 : ℝ)).contDiffOn

end D13Unified.Ch18.ContractingAttractorExample

namespace Specs.D13Unified.Ch18.ContractingAttractorExample
open _root_.D13Unified.Ch18.ContractingAttractorExample

def iterate_formulaStatement : Prop :=
  ∀ (n : ℕ) (x : ℝ), F^[n] x = (1 / 2 : ℝ)^n * x

def trappingStatement : Prop :=
  IsCompact K ∧ K.Nonempty ∧ F '' K ⊆ interior K

def trapping_limitStatement : Prop :=
  TrappingLimit.trappingLimit F K = {0}

def stable_attractorStatement : Prop :=
  AttractorDefinition.StableAttractor F {0}

def basin_univStatement : Prop :=
  AttractorDefinition.basin F {0} = univ

def directional_rateStatement : Prop :=
  ∀ (x : smoothMap.domain) (v : ℝ) (hv : v ≠ 0) (n : ℕ) (hn : 0 < n),
    GrowthDefinitions.discreteDirectionalRate smoothMap x v hv n hn =
      ((-Real.log 2 : ℝ) : EReal)

def directional_exponentStatement : Prop :=
  ∀ (x : smoothMap.domain) (v : ℝ) (hv : v ≠ 0),
    GrowthDefinitions.HasDiscreteDirectionalExponent smoothMap x v hv
      ((-Real.log 2 : ℝ) : EReal) ∧
    GrowthDefinitions.discreteDirectionalExponent smoothMap x v hv =
      some ((-Real.log 2 : ℝ) : EReal)

def not_sensitiveStatement : Prop :=
  ¬ Ch17.ChaosDefinitions.SensitiveDependence F

def not_chaoticStatement : Prop :=
  ¬ Ch17.ChaosDefinitions.Chaotic F

end Specs.D13Unified.Ch18.ContractingAttractorExample
