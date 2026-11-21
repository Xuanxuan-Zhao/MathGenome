import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Connected.Basic

/-!
Canonical foundations for the D12 project (paper.tex, families D12.01.01 and D12.01.04,
and unified conventions 1--3). Later Specs import this module, so they use these
same objects without importing any candidate proof module.

Functions on open sets are represented by total complex functions; all on-set
conditions are restricted to the stated set. Open sets may be empty or disconnected.
The three regularity predicates are separate definitions. Their later analytic
equivalence is not an assumption in this interface.
-/

open scoped Topology

namespace D12Complex

/-- A plane domain is nonempty, open, and connected. Nonemptiness is explicit. -/
def IsDomain : Set ℂ → Prop :=
  fun Ω => Ω.Nonempty ∧ IsOpen Ω ∧ IsPreconnected Ω

/-- The source epsilon-delta limit, with points restricted to the function domain s. -/
def PuncturedLimitWithin : Set ℂ → (ℂ → ℂ) → ℂ → ℂ → Prop :=
  fun s f a L => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ s, 0 < ‖z - a‖ → ‖z - a‖ < δ → ‖f z - L‖ < ε

/-- The unrestricted punctured limit. No value at the center is tested. -/
def PuncturedLimit : (ℂ → ℂ) → ℂ → ℂ → Prop :=
  fun f a L => PuncturedLimitWithin Set.univ f a L

/-- Continuity relative to s, with the actual value f(a) and no puncture. -/
def ContinuousWithinAtPoint : Set ℂ → (ℂ → ℂ) → ℂ → Prop :=
  fun s f a => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ s, ‖z - a‖ < δ → ‖f z - f a‖ < ε

/-- Ordinary pointwise continuity, including the value at the center. -/
def ContinuousAtPoint : (ℂ → ℂ) → ℂ → Prop :=
  fun f a => ContinuousWithinAtPoint Set.univ f a

/-- Complex derivative A at a, defined using exactly the punctured increment quotient. -/
def HasComplexDerivativeAt : (ℂ → ℂ) → ℂ → ℂ → Prop :=
  fun f A a => PuncturedLimit (fun h => (f (a + h) - f a) / h) 0 A

/-- Existence of a complex derivative, before its bridge to Mathlib differentiation. -/
def ComplexDifferentiableAt : (ℂ → ℂ) → ℂ → Prop :=
  fun f a => ∃ A : ℂ, HasComplexDerivativeAt f A a

/-- Weak holomorphy on an open set. The derivative is not assumed continuous. -/
def HolomorphicOn : Set ℂ → (ℂ → ℂ) → Prop :=
  fun Ω f => IsOpen Ω ∧ ∀ a ∈ Ω, DifferentiableAt ℂ f a

/-- The separate C1-holomorphic predicate: holomorphic with continuous complex derivative. -/
def C1HolomorphicOn : Set ℂ → (ℂ → ℂ) → Prop :=
  fun Ω f => HolomorphicOn Ω f ∧ ContinuousOn (deriv f) Ω

/-- An actual convergent complex scalar series represents f on a neighborhood of a. -/
def PowerSeriesAnalyticAt : (ℂ → ℂ) → ℂ → Prop :=
  fun f a => ∃ r : ℝ, 0 < r ∧ ∃ c : ℕ → ℂ,
    ∀ z : ℂ, ‖z - a‖ < r → HasSum (fun n => c n * (z - a) ^ n) (f z)

/-- Local scalar power-series representations at all points of the open set. -/
def PowerSeriesAnalyticOn : Set ℂ → (ℂ → ℂ) → Prop :=
  fun Ω f => IsOpen Ω ∧ ∀ a ∈ Ω, PowerSeriesAnalyticAt f a

/-- Two holomorphic maps between open sets which are mutual inverses on those sets. -/
def BiholomorphicPair : Set ℂ → Set ℂ → (ℂ → ℂ) → (ℂ → ℂ) → Prop :=
  fun Ω V f g => HolomorphicOn Ω f ∧ HolomorphicOn V g ∧
    Set.MapsTo f Ω V ∧ Set.MapsTo g V Ω ∧
    Set.LeftInvOn g f Ω ∧ Set.RightInvOn g f V

/-- A map between open sets with a holomorphic inverse. Bijectivity follows from the inverse laws. -/
def IsBiholomorphism : Set ℂ → Set ℂ → (ℂ → ℂ) → Prop :=
  fun Ω V f => ∃ g : ℂ → ℂ, BiholomorphicPair Ω V f g

/-- Holomorphy with nonzero derivative on the open set; no injectivity is stipulated. -/
def ConformalOn : Set ℂ → (ℂ → ℂ) → Prop :=
  fun Ω f => HolomorphicOn Ω f ∧ ∀ a ∈ Ω, deriv f a ≠ 0

/-- Conformality locally: some open neighborhood has holomorphy and nonzero derivative. -/
def ConformalAt : (ℂ → ℂ) → ℂ → Prop :=
  fun f a => ∃ U : Set ℂ, a ∈ U ∧ ConformalOn U f

end D12Complex

namespace Specs.D12Complex.Ch01.Basic

open _root_.D12Complex

def IsDomain_type := Set ℂ → Prop

def IsDomain_value : IsDomain_type :=
  fun Ω => Ω.Nonempty ∧ IsOpen Ω ∧ IsPreconnected Ω

def PuncturedLimitWithin_type := Set ℂ → (ℂ → ℂ) → ℂ → ℂ → Prop

def PuncturedLimitWithin_value : PuncturedLimitWithin_type :=
  fun s f a L => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ s, 0 < ‖z - a‖ → ‖z - a‖ < δ → ‖f z - L‖ < ε

def PuncturedLimit_type := (ℂ → ℂ) → ℂ → ℂ → Prop

def PuncturedLimit_value : PuncturedLimit_type :=
  fun f a L => PuncturedLimitWithin Set.univ f a L

def ContinuousWithinAtPoint_type := Set ℂ → (ℂ → ℂ) → ℂ → Prop

def ContinuousWithinAtPoint_value : ContinuousWithinAtPoint_type :=
  fun s f a => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ s, ‖z - a‖ < δ → ‖f z - f a‖ < ε

def ContinuousAtPoint_type := (ℂ → ℂ) → ℂ → Prop

def ContinuousAtPoint_value : ContinuousAtPoint_type :=
  fun f a => ContinuousWithinAtPoint Set.univ f a

def HasComplexDerivativeAt_type := (ℂ → ℂ) → ℂ → ℂ → Prop

def HasComplexDerivativeAt_value : HasComplexDerivativeAt_type :=
  fun f A a => PuncturedLimit (fun h => (f (a + h) - f a) / h) 0 A

def ComplexDifferentiableAt_type := (ℂ → ℂ) → ℂ → Prop

def ComplexDifferentiableAt_value : ComplexDifferentiableAt_type :=
  fun f a => ∃ A : ℂ, HasComplexDerivativeAt f A a

def HolomorphicOn_type := Set ℂ → (ℂ → ℂ) → Prop

def HolomorphicOn_value : HolomorphicOn_type :=
  fun Ω f => IsOpen Ω ∧ ∀ a ∈ Ω, DifferentiableAt ℂ f a

def C1HolomorphicOn_type := Set ℂ → (ℂ → ℂ) → Prop

def C1HolomorphicOn_value : C1HolomorphicOn_type :=
  fun Ω f => HolomorphicOn Ω f ∧ ContinuousOn (deriv f) Ω

def PowerSeriesAnalyticAt_type := (ℂ → ℂ) → ℂ → Prop

def PowerSeriesAnalyticAt_value : PowerSeriesAnalyticAt_type :=
  fun f a => ∃ r : ℝ, 0 < r ∧ ∃ c : ℕ → ℂ,
    ∀ z : ℂ, ‖z - a‖ < r → HasSum (fun n => c n * (z - a) ^ n) (f z)

def PowerSeriesAnalyticOn_type := Set ℂ → (ℂ → ℂ) → Prop

def PowerSeriesAnalyticOn_value : PowerSeriesAnalyticOn_type :=
  fun Ω f => IsOpen Ω ∧ ∀ a ∈ Ω, PowerSeriesAnalyticAt f a

def BiholomorphicPair_type := Set ℂ → Set ℂ → (ℂ → ℂ) → (ℂ → ℂ) → Prop

def BiholomorphicPair_value : BiholomorphicPair_type :=
  fun Ω V f g => HolomorphicOn Ω f ∧ HolomorphicOn V g ∧
    Set.MapsTo f Ω V ∧ Set.MapsTo g V Ω ∧
    Set.LeftInvOn g f Ω ∧ Set.RightInvOn g f V

def IsBiholomorphism_type := Set ℂ → Set ℂ → (ℂ → ℂ) → Prop

def IsBiholomorphism_value : IsBiholomorphism_type :=
  fun Ω V f => ∃ g : ℂ → ℂ, BiholomorphicPair Ω V f g

def ConformalOn_type := Set ℂ → (ℂ → ℂ) → Prop

def ConformalOn_value : ConformalOn_type :=
  fun Ω f => HolomorphicOn Ω f ∧ ∀ a ∈ Ω, deriv f a ≠ 0

def ConformalAt_type := (ℂ → ℂ) → ℂ → Prop

def ConformalAt_value : ConformalAt_type :=
  fun f a => ∃ U : Set ℂ, a ∈ U ∧ ConformalOn U f


def isDomain_iff_type : Prop :=
  ∀ Ω : Set ℂ, D12Complex.IsDomain Ω ↔ IsOpen Ω ∧ IsConnected Ω

def puncturedLimitWithin_iff_tendsto_type : Prop :=
  ∀ (s : Set ℂ) (f : ℂ → ℂ) (a L : ℂ),
    PuncturedLimitWithin s f a L ↔ Filter.Tendsto f (𝓝[s \ {a}] a) (𝓝 L)

def continuousWithinAtPoint_iff_type : Prop :=
  ∀ (s : Set ℂ) (f : ℂ → ℂ) (a : ℂ),
    ContinuousWithinAtPoint s f a ↔ ContinuousWithinAt f s a

def continuousAtPoint_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), ContinuousAtPoint f a ↔ ContinuousAt f a

def hasComplexDerivativeAt_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (A a : ℂ),
    HasComplexDerivativeAt f A a ↔ HasDerivAt f A a

def complexDifferentiableAt_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ),
    ComplexDifferentiableAt f a ↔ DifferentiableAt ℂ f a

def holomorphicOn_iff_incrementLimit_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    HolomorphicOn Ω f ↔ IsOpen Ω ∧ ∀ a ∈ Ω, ComplexDifferentiableAt f a

def holomorphicOn_iff_differentiableOn_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    HolomorphicOn Ω f ↔ IsOpen Ω ∧ DifferentiableOn ℂ f Ω

def biholomorphicPair_bijOn_type : Prop :=
  ∀ (Ω V : Set ℂ) (f g : ℂ → ℂ),
    BiholomorphicPair Ω V f g → Set.BijOn f Ω V ∧ Set.BijOn g V Ω

def isBiholomorphism_iff_type : Prop :=
  ∀ (Ω V : Set ℂ) (f : ℂ → ℂ),
    IsBiholomorphism Ω V f ↔
      HolomorphicOn Ω f ∧ Set.BijOn f Ω V ∧ ∃ g : ℂ → ℂ,
        HolomorphicOn V g ∧ Set.MapsTo g V Ω ∧
        Set.LeftInvOn g f Ω ∧ Set.RightInvOn g f V

end Specs.D12Complex.Ch01.Basic
