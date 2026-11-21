import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import Mathlib.Topology.Instances.Real.Lemmas

/-! The two examples of paper.tex, d10:11:proper-boundary. The two finite
spaces have exactly the same underlying set `Fin 2`, with the displayed
(discrete/indiscrete) topologies. The interval has its usual subspace topology.
The countable cover is indexed starting at zero, so its denominator is `n+1`. -/

open Set

noncomputable section

namespace Specs.D10Topology.Ch11.ProperBoundary

abbrev Interval := Icc (0 : ℝ) 1

/-- Zero maps to zero and every positive point of the interval maps to one. -/
def intervalMap (x : Interval) : Fin 2 := if (x : ℝ) = 0 then 0 else 1

def positivePart : Set Interval := {x | 0 < (x : ℝ)}

/-- The restriction of `(1/(n+1),2)` to `(0,1]`, viewed inside `[0,1]`.
The lower bound already implies positivity. -/
def cover (n : ℕ) : Set Interval :=
  {x | 1 / ((n : ℝ) + 1) < (x : ℝ) ∧ (x : ℝ) < 2}

def intervalMapType := Interval → Fin 2
def intervalMapValue : intervalMapType := intervalMap

def positivePartType := Set Interval
def positivePartValue : positivePartType := positivePart

def coverType := ℕ → Set Interval
def coverValue : coverType := cover

def discrete_identity_continuous : Prop :=
  @Continuous (Fin 2) (Fin 2) ⊥ ⊤ id

def discrete_identity_proper : Prop :=
  @Specs.D10Topology.Ch11.LocalCompactConventions.Proper (Fin 2) (Fin 2) ⊥ ⊤ id

def discrete_identity_not_closed : Prop :=
  ¬ @IsClosedMap (Fin 2) (Fin 2) ⊥ ⊤ id

def interval_map_values : Prop :=
  ∀ x : Interval, (intervalMap x = 0 ↔ (x : ℝ) = 0) ∧
    (intervalMap x = 1 ↔ 0 < (x : ℝ))

def interval_domain_compact : Prop := CompactSpace Interval

def interval_map_continuous : Prop :=
  @Continuous Interval (Fin 2) inferInstance ⊤ intervalMap

def target_singleton_compact : Prop :=
  @IsCompact (Fin 2) ⊤ {1}

def interval_map_preimage : Prop := intervalMap ⁻¹' {1} = positivePart

/-- Explicit bridge to the real interval in the source. -/
def positivePart_image : Prop :=
  Subtype.val '' positivePart = Ioc (0 : ℝ) 1

def cover_eq_restricted_intervals : Prop :=
  ∀ n : ℕ, cover n = (Subtype.val ⁻¹' Ioo (1 / ((n : ℝ) + 1)) 2) ∩ positivePart

def cover_open : Prop := ∀ n : ℕ, IsOpen (cover n)
def cover_union : Prop := ⋃ n : ℕ, cover n = positivePart

def cover_no_finite_subcover : Prop :=
  ∀ s : Finset ℕ, ¬ positivePart ⊆ ⋃ n ∈ s, cover n

def positivePart_not_compact : Prop := ¬ IsCompact positivePart

def interval_map_not_proper : Prop :=
  ¬ @Specs.D10Topology.Ch11.LocalCompactConventions.Proper
    Interval (Fin 2) inferInstance ⊤ intervalMap

end Specs.D10Topology.Ch11.ProperBoundary
