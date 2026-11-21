import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent specification of the real-target construction in the proof of
`thm:kernel-randomization`, paper.tex lines 1243–1250. The source space has its
arbitrary specified sigma algebra. Uniform input on the closed unit interval is
represented by `volume.restrict (Icc 0 1)` on ℝ. The map is extended by zero off
(0,1), so its values at both endpoints are the same fixed real number. -/

open MeasureTheory ProbabilityTheory Set

namespace Specs.ProbabilityFoundations.Ch04.RealKernelQuantile

universe u

/-- The rational upper level set, viewed as a subset of ℝ for its infimum. -/
def rationalQuantileSetValue {S : Type u} [MeasurableSpace S]
    (K : Kernel S ℝ) (s : S) (u : ℝ) : Set ℝ :=
  (fun q : ℚ => (q : ℝ)) '' {q : ℚ | u ≤ (K s (Iic (q : ℝ))).toReal}

/-- The source's infimum, with the agreed endpoint assignment. -/
noncomputable def realKernelQuantileValue {S : Type u} [MeasurableSpace S]
    (K : Kernel S ℝ) (s : S) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then sInf (rationalQuantileSetValue K s u) else 0

def rationalQuantileSetType : Type _ :=
  ∀ {S : Type u} [MeasurableSpace S], Kernel S ℝ → S → ℝ → Set ℝ

def realKernelQuantileType : Type _ :=
  ∀ {S : Type u} [MeasurableSpace S], Kernel S ℝ → S → ℝ → ℝ

/-- Both conditions are necessary to interpret the conditional real infimum as
an actual finite infimum, rather than the default for an empty or unbounded set. -/
def finiteInfimumType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (K : Kernel S ℝ) [IsMarkovKernel K]
    (s : S) (u : ℝ), 0 < u → u < 1 →
    (rationalQuantileSetValue K s u).Nonempty ∧ BddBelow (rationalQuantileSetValue K s u)

def infimumFormulaType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (K : Kernel S ℝ)
    (s : S) (u : ℝ), 0 < u → u < 1 →
    realKernelQuantileValue K s u = sInf (rationalQuantileSetValue K s u)

def inverseCDFType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (K : Kernel S ℝ) [IsMarkovKernel K]
    (s : S) (u t : ℝ), 0 < u → u < 1 →
    (realKernelQuantileValue K s u ≤ t ↔ u ≤ (K s (Iic t)).toReal)

def endpointType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (K : Kernel S ℝ) (s : S) (u : ℝ),
    u ∉ Ioo (0 : ℝ) 1 → realKernelQuantileValue K s u = 0

def jointMeasurabilityType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (K : Kernel S ℝ) [IsMarkovKernel K],
    Measurable (fun p : S × ℝ => realKernelQuantileValue K p.1 p.2)

def unitIntervalMeasurabilityType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (K : Kernel S ℝ) [IsMarkovKernel K],
    Measurable (fun p : S × Icc (0 : ℝ) 1 => realKernelQuantileValue K p.1 p.2)

def uniformProbabilityType : Prop :=
  IsProbabilityMeasure ((volume : Measure ℝ).restrict (Icc 0 1))

/-- Equality of Borel measures on every measurable set, for every s, including atomic laws. -/
def fiberLawType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (K : Kernel S ℝ) [IsMarkovKernel K] (s : S),
    Measure.map (realKernelQuantileValue K s) ((volume : Measure ℝ).restrict (Icc 0 1)) = K s

end Specs.ProbabilityFoundations.Ch04.RealKernelQuantile
