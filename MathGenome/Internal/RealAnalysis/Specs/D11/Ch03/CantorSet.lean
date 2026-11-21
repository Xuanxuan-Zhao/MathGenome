import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.Perfect
import Mathlib.SetTheory.Cardinal.Continuum

/-! Independent statements for the middle-thirds part of paper.tex:1025–1050.
The positive-mass construction is allocated separately. The recursive retained
stages are Mathlib's middle-thirds stages, not an arbitrary perfect null set. -/
noncomputable section
open Set MeasureTheory
open scoped Cardinal ENNReal

namespace D11.Ch03.CantorConstruction

/-- The left endpoint of the interval prescribed by a finite binary word. -/
def leftEndpoint : (n : ℕ) → (Fin n → Bool) → ℝ
  | 0, _ => 0
  | n + 1, w => ((if w 0 then 2 else 0) + leftEndpoint n (fun i => w i.succ)) / 3

def interval (n : ℕ) (w : Fin n → Bool) : Set ℝ :=
  Icc (leftEndpoint n w) (leftEndpoint n w + (1 / 3 : ℝ) ^ n)

/-- The canonical coordinate identification of the real line with Euclidean R¹. -/
def linePoint (x : ℝ) : Point 1 := WithLp.toLp 2 (fun _ => x)

end D11.Ch03.CantorConstruction

namespace Specs.D11.Ch03.CantorSet
open _root_.D11.Ch03 _root_.D11.Ch03.CantorConstruction

abbrev C_type := Set ℝ
def C_value : C_type := _root_.cantorSet

abbrev stage_type := ℕ → Set ℝ
def stage_value : stage_type := _root_.preCantorSet

def stage_zero : Prop := stage_value 0 = Icc 0 1

def stage_succ : Prop := ∀ n, stage_value (n + 1) =
  (fun x : ℝ => x / 3) '' stage_value n ∪
  (fun x : ℝ => (2 + x) / 3) '' stage_value n

def stage_antitone : Prop := Antitone stage_value

def C_eq_inter : Prop := C_value = ⋂ n, stage_value n

def C_subset : Prop := C_value ⊆ Icc 0 1

def stage_intervals : Prop := ∀ n, stage_value n = ⋃ w : Fin n → Bool, interval n w

def stage_interval_count : Prop := ∀ n, Fintype.card (Fin n → Bool) = 2 ^ n

def stage_interval_length : Prop := ∀ n (w : Fin n → Bool),
  (leftEndpoint n w + (1 / 3 : ℝ) ^ n) - leftEndpoint n w = (1 / 3 : ℝ) ^ n

def stage_disjoint : Prop := ∀ n, Pairwise (fun a b => Disjoint (interval n a) (interval n b))

def stage_volume_bound : Prop := ∀ n,
  volume (stage_value n) ≤ ENNReal.ofReal (2 / 3 : ℝ) ^ n

def C_compact : Prop := IsCompact C_value

def C_perfect : Prop := Perfect C_value

def C_cardinality : Prop := Cardinal.mk ↥C_value = 𝔠

def C_volume_zero : Prop := volume C_value = 0

def C_nowhere_dense : Prop := IsNowhereDense C_value

/-- Borel measurability is kept distinct from completed measurability. -/
def C_borel : Prop := MeasurableSet C_value

def C_lebesgue_null : Prop :=
  MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1] (linePoint '' C_value) ∧
  LebesgueMeasures.lebesgue_value 1 (linePoint '' C_value) = 0

end Specs.D11.Ch03.CantorSet
