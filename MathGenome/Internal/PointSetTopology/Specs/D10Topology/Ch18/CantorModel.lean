import Mathlib.Topology.Instances.CantorSet
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Bases

/-! Independent specification of paper.tex, d10:18:cantor-model.
The coordinates really are positive integers. `Bool.toNat` identifies the
discrete factor with {0,1}; thus the series has exactly the paper's weights.
The finite-stage interval description below fixes the middle-thirds model
independently of its library name. -/

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology

namespace Specs.D10Topology.Ch18.CantorModel

abbrev CantorSpace := ℕ+ → Bool

def cantorSpaceType := Type
def cantorSpaceValue : cantorSpaceType := CantorSpace

def cylinder (s : Finset ℕ+) (a : CantorSpace) : Set CantorSpace :=
  {b | ∀ n ∈ s, b n = a n}

def cylinders : Set (Set CantorSpace) :=
  {U | ∃ (s : Finset ℕ+) (a : CantorSpace), U = cylinder s a}

def digitTerm (a : CantorSpace) (n : ℕ+) : ℝ :=
  2 * (a n).toNat / (3 : ℝ) ^ (n : ℕ)

def series (a : CantorSpace) : ℝ := ∑' n : ℕ+, digitTerm a n

def prefixSum (r : ℕ) (a : CantorSpace) : ℝ :=
  ∑ n ∈ Finset.range r, digitTerm a n.succPNat

def retainedStage (r : ℕ) : Set ℝ :=
  ⋃ a : CantorSpace, Icc (prefixSum r a) (prefixSum r a + 1 / (3 : ℝ) ^ r)

def cylinderType := Finset ℕ+ → CantorSpace → Set CantorSpace
def seriesType := CantorSpace → ℝ
def prefixSumType := ℕ → CantorSpace → ℝ
def retainedStageType := ℕ → Set ℝ
def positiveReindexType := CantorSpace ≃ₜ (ℕ → Bool)
def positiveReindexValue : positiveReindexType :=
  Homeomorph.piCongrLeft (Y := fun _ => Bool) Equiv.pnatEquivNat

def cantor_nonempty : Prop := Nonempty CantorSpace
def cantor_compact : Prop := IsCompact (univ : Set CantorSpace)
def cantor_metrizable : Prop := MetrizableSpace CantorSpace
def cylinder_clopen : Prop := ∀ s a, IsClopen (cylinder s a)
def cylinder_basis : Prop := TopologicalSpace.IsTopologicalBasis cylinders
def cantor_no_isolated : Prop := ∀ a : CantorSpace, ¬ IsOpen ({a} : Set CantorSpace)

def positive_reindex : Prop :=
  ∃ h : CantorSpace ≃ₜ (ℕ → Bool), ∀ a n, h a n = a n.succPNat

def digit_series_bridge : Prop :=
  ∀ a : CantorSpace,
    series a = Real.ofDigits (fun n => cond (a n.succPNat) (2 : Fin 3) 0)

def series_hasSum : Prop := ∀ a : CantorSpace, HasSum (digitTerm a) (series a)
def series_uniform : Prop := TendstoUniformly prefixSum series atTop
def series_continuous : Prop := Continuous series
def series_injective : Prop := Function.Injective series
def series_image : Prop := range series = cantorSet
def series_unitInterval : Prop := ∀ a : CantorSpace, series a ∈ Icc (0 : ℝ) 1

/-- This is the finite union of the retained closed intervals of length 3⁻ʳ,
with endpoints given by the finite ternary prefixes in the source. -/
def middle_thirds_stages : Prop := ∀ r, retainedStage r = preCantorSet r
def middle_thirds_intersection : Prop := (⋂ r, retainedStage r) = cantorSet

def cantor_homeomorph : Prop :=
  ∃ h : CantorSpace ≃ₜ cantorSet, ∀ a, (h a : ℝ) = series a

end Specs.D10Topology.Ch18.CantorModel
