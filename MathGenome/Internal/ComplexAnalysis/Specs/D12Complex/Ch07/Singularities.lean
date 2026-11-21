import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-!
Canonical isolated-singularity predicates for paper.tex, definition d12:07-02.
Functions are total representatives, as in the shared Basic interface. Their
value at the puncture and their values outside the witnessing disk are ignored.
Every singularity predicate requires a whole punctured neighborhood, so a general
boundary point of an open set does not qualify merely by being a boundary point.

The public definitions live here so later independent Specs can reuse them.
No classification theorem, Laurent expansion, or analytic certificate is assumed.
-/

namespace D12Complex

/-- The entire punctured disk `0 < ‖z - a‖ < R`. -/
def puncturedDisk (a : ℂ) (R : ℝ) : Set ℂ :=
  {z | 0 < ‖z - a‖ ∧ ‖z - a‖ < R}

/-- Holomorphy on some whole punctured disk of positive radius about `a`.
This includes the removable case, even when the representative is already
holomorphic at `a`, in accordance with the source terminology. -/
def IsolatedSingularityAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ HolomorphicOn (puncturedDisk a R) f

/-- An isolated singularity admitting a holomorphic extension to a full disk.
The extension need only agree with the representative away from `a`. -/
def RemovableSingularityAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  IsolatedSingularityAt f a ∧
    ∃ R : ℝ, 0 < R ∧ ∃ g : ℂ → ℂ,
      HolomorphicOn (Metric.ball a R) g ∧
        ∀ z ∈ puncturedDisk a R, f z = g z

/-- A pole of exact positive order `m`.
The reciprocal power is `(z-a)^(-m)`; writing it as an inverse of a natural
power avoids natural-number subtraction in the exponent. The nonzero value
`g a` makes the order exact. -/
def PoleOfOrderAt (f : ℂ → ℂ) (a : ℂ) (m : ℕ) : Prop :=
  1 ≤ m ∧ IsolatedSingularityAt f a ∧
    ∃ R : ℝ, 0 < R ∧ ∃ g : ℂ → ℂ,
      HolomorphicOn (Metric.ball a R) g ∧ g a ≠ 0 ∧
        ∀ z ∈ puncturedDisk a R, f z = ((z - a) ^ m)⁻¹ * g z

/-- A pole of some finite positive order. -/
def PoleAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ m : ℕ, PoleOfOrderAt f a m

/-- An isolated singularity which is neither removable nor a finite-order pole. -/
def EssentialSingularityAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  IsolatedSingularityAt f a ∧ ¬RemovableSingularityAt f a ∧ ¬PoleAt f a

end D12Complex

namespace Specs.D12Complex.Ch07.Singularities

open _root_.D12Complex

def puncturedDisk_type := ℂ → ℝ → Set ℂ
def puncturedDisk_value : puncturedDisk_type :=
  fun a R => {z | 0 < ‖z - a‖ ∧ ‖z - a‖ < R}

def IsolatedSingularityAt_type := (ℂ → ℂ) → ℂ → Prop
def IsolatedSingularityAt_value : IsolatedSingularityAt_type :=
  fun f a => ∃ R : ℝ, 0 < R ∧ HolomorphicOn (puncturedDisk a R) f

def RemovableSingularityAt_type := (ℂ → ℂ) → ℂ → Prop
def RemovableSingularityAt_value : RemovableSingularityAt_type :=
  fun f a => IsolatedSingularityAt f a ∧
    ∃ R : ℝ, 0 < R ∧ ∃ g : ℂ → ℂ,
      HolomorphicOn (Metric.ball a R) g ∧
        ∀ z ∈ puncturedDisk a R, f z = g z

def PoleOfOrderAt_type := (ℂ → ℂ) → ℂ → ℕ → Prop
def PoleOfOrderAt_value : PoleOfOrderAt_type :=
  fun f a m => 1 ≤ m ∧ IsolatedSingularityAt f a ∧
    ∃ R : ℝ, 0 < R ∧ ∃ g : ℂ → ℂ,
      HolomorphicOn (Metric.ball a R) g ∧ g a ≠ 0 ∧
        ∀ z ∈ puncturedDisk a R, f z = ((z - a) ^ m)⁻¹ * g z

def PoleAt_type := (ℂ → ℂ) → ℂ → Prop
def PoleAt_value : PoleAt_type :=
  fun f a => ∃ m : ℕ, PoleOfOrderAt f a m

def EssentialSingularityAt_type := (ℂ → ℂ) → ℂ → Prop
def EssentialSingularityAt_value : EssentialSingularityAt_type :=
  fun f a => IsolatedSingularityAt f a ∧ ¬RemovableSingularityAt f a ∧ ¬PoleAt f a

def removableSingularityAt_isolated_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), RemovableSingularityAt f a → IsolatedSingularityAt f a

def poleOfOrderAt_isolated_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (m : ℕ), PoleOfOrderAt f a m → IsolatedSingularityAt f a

def poleOfOrderAt_positive_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (m : ℕ), PoleOfOrderAt f a m → 1 ≤ m

def essentialSingularityAt_isolated_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), EssentialSingularityAt f a → IsolatedSingularityAt f a

end Specs.D12Complex.Ch07.Singularities
