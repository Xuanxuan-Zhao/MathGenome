import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Real.Lemmas

/-! The actual countable-deletion refinement of the ordinary real line in
paper.tex, Example d10:13:ascoli-nonlch. Positive paper indices are n+1.
The domain is a type synonym, so its topology cannot be confused with the
ordinary topology of the scalar target ℝ. All assertions below are Prop
values, with no assumed certificates. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D10Topology.Ch13.AscoliNonLCH

def Domain := ℝ

def toReal (x : Domain) : ℝ := x
def ofReal (x : ℝ) : Domain := x

def generators : Set (Set Domain) :=
  {B | ∃ O : Set ℝ, IsOpen O ∧ ∃ C : Set ℝ, C.Countable ∧
    B = toReal ⁻¹' (O \ C)}

instance domainTopology : TopologicalSpace Domain :=
  TopologicalSpace.generateFrom generators

def tent (n : ℕ) (x : Domain) : ℝ :=
  max 0 (1 - |(n + 1 : ℝ) * toReal x - 1|)

def family : Set (ContinuousMap Domain ℝ) :=
  {f | (∀ x, f x = 0) ∨ ∃ n : ℕ, ∀ x, f x = tent n x}

def domainType := Type
def domainValue : domainType := Domain
def toRealType := Domain → ℝ
def ofRealType := ℝ → Domain
def generatorsType := Set (Set Domain)
def topologyType := TopologicalSpace Domain
def tentType := ℕ → Domain → ℝ
def familyType := Set (ContinuousMap Domain ℝ)

def topology_basis : Prop := TopologicalSpace.IsTopologicalBasis generators
def hausdorff : Prop := T2Space Domain

def compact_iff_finite : Prop := ∀ K : Set Domain, IsCompact K ↔ K.Finite

/-- Local compactness in the paper means existence of compact neighborhoods. -/
def not_locally_compact : Prop := ¬ WeaklyLocallyCompactSpace Domain

def compactOpen_eq_pointwise : Prop :=
  FunctionTopologies.compactOpenContinuousTopology (X := Domain) (Y := ℝ) =
    FunctionTopologies.pointwiseContinuousTopology

def tents_continuous : Prop := ∀ n, Continuous (tent n)

def tents_pointwise : Prop :=
  ∀ x : Domain, Tendsto (fun n => tent n x) atTop (𝓝 (0 : ℝ))

def family_compact : Prop :=
  @IsCompact (ContinuousMap Domain ℝ)
    FunctionTopologies.compactOpenContinuousTopology family

def family_not_equicontinuousAt_zero : Prop :=
  ¬ FunctionTopologies.EquicontinuousAt family (ofReal 0)

/-- Compact closure is the precise antecedent in the failed converse of Ascoli. -/
def counterexample : Prop :=
  T2Space Domain ∧ ¬ WeaklyLocallyCompactSpace Domain ∧
  @IsCompact (ContinuousMap Domain ℝ)
    FunctionTopologies.compactOpenContinuousTopology
    (@closure (ContinuousMap Domain ℝ)
      FunctionTopologies.compactOpenContinuousTopology family) ∧
  ¬ FunctionTopologies.Equicontinuous family

end Specs.D10Topology.Ch13.AscoliNonLCH
