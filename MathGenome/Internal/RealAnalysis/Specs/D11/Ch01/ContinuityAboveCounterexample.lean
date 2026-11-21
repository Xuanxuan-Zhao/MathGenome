import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import Mathlib.MeasureTheory.Measure.Continuity

/-!
Independent statements for paper.tex:484–491.

The upstream Euclidean construction uses `Point 1` for the real line. Its
sole coordinate is a bijection to ℝ (recorded below), and the sequence here
is precisely the inverse image of the real intervals `(n, ∞)` under that
coordinate. Masses use the full Chapter 3 Carathéodory measure, including
its specified measurable space, rather than an unspecified measure.
Indexing starts at zero; deleting that initial term gives the same example.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.D11.Ch01.ContinuityAboveCounterexample

open _root_.D11.Ch03

/-- The explicit real-line identification for the upstream one-dimensional space. -/
def coordinate_bijective : Prop :=
  Function.Bijective (fun x : Point 1 => x (0 : Fin 1))

def ray_type := ℕ → Set (Point 1)
def ray_value : ray_type := fun n =>
  (fun x : Point 1 => x (0 : Fin 1)) ⁻¹' Ioi (n : ℝ)

def rays_measurable : Prop := ∀ n,
  MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1] (ray_value n)

def rays_antitone : Prop := Antitone ray_value

def rays_intersection : Prop := (⋂ n, ray_value n) = ∅

def rays_infinite : Prop := ∀ n,
  Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 (ray_value n) = ∞

def intersection_mass : Prop :=
  Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 (⋂ n, ray_value n) = 0

def masses_tendsto_top : Prop :=
  Tendsto (fun n => Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 (ray_value n))
    atTop (𝓝 ∞)

def continuity_above_failure : Prop :=
  ¬ Tendsto (fun n => Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 (ray_value n))
    atTop (𝓝 (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 (⋂ n, ray_value n)))

end Specs.D11.Ch01.ContinuityAboveCounterexample
