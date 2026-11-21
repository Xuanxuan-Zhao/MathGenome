import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! Independent statements for `d04:01:sequential-continuity`.
Maps have their actual relative domain as a subtype. Coordinates are real-valued,
so their limit and continuity assertions are written explicitly in epsilon-delta
form. No positive-dimensional or non-isolation hypothesis is imposed on continuity.
The accumulation hypothesis for limits is retained even for an empty target index. -/

open Set Filter Topology
namespace Specs.D04.C01.SequentialContinuity
open Specs.D04.C01.EuclideanInterfaces.Model

def relativeLimit_iff_sequenceType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : E n) (b : E m),
    AccumulationPoint A a →
    (RelativeLimit A f a b ↔
      ∀ s : ℕ → A, (∀ k, (s k : E n) ≠ a) →
        Tendsto (fun k => (s k : E n)) atTop (𝓝 a) →
        Tendsto (fun k => f (s k)) atTop (𝓝 b))

def relativeContinuousAt_iff_sequenceType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A),
    RelativeContinuousAt A f a ↔
      ∀ s : ℕ → A, Tendsto (fun k => (s k : E n)) atTop (𝓝 (a : E n)) →
        Tendsto (fun k => f (s k)) atTop (𝓝 (f a))

def relativeLimit_uniqueType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : E n) (b c : E m),
    AccumulationPoint A a → RelativeLimit A f a b → RelativeLimit A f a c → b = c

def relativeLimit_iff_coordinatesType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : E n) (b : E m),
    AccumulationPoint A a →
    (RelativeLimit A f a b ↔
      ∀ i : Fin m, ∀ ε > 0, ∃ δ > 0, ∀ x : A,
        0 < ‖(x : E n) - a‖ → ‖(x : E n) - a‖ < δ → |f x i - b i| < ε)

def relativeContinuousAt_iff_coordinatesType : Prop :=
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (a : A),
    RelativeContinuousAt A f a ↔
      ∀ i : Fin m, ∀ ε > 0, ∃ δ > 0, ∀ x : A,
        ‖(x : E n) - (a : E n)‖ < δ → |f x i - f a i| < ε

end Specs.D04.C01.SequentialContinuity
