import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions

/-! Independent statements for paper.tex, Proposition `d13:15:conjugacy-transport`.
The topology is arbitrary for orbit correspondences. Stability statements retain
continuous self-maps and a fixed point in metric spaces, exactly as in the paper.
All orbit sets and stability predicates use the canonical upstream definitions.
-/
namespace Specs.D13Unified.Ch15.ConjugacyTransport
universe u v
open Function Set Filter
open scoped Topology
open Specs.D13Unified.Ch15.DiscreteDefinitions

def iterate_transportStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} (F : X → X) (G : Y → Y) (h : X → Y),
    h ∘ F = G ∘ h → ∀ n : ℕ, h ∘ F^[n] = G^[n] ∘ h

def periodicPt_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    ∀ (x : X) (n : ℕ), IsPeriodicPt F n x ↔ IsPeriodicPt G n (h x)

def leastPeriod_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    ∀ (x : X) (n : ℕ), HasLeastPeriod F x n ↔ HasLeastPeriod G (h x) n

def periodic_points_bijOnStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    Set.BijOn h {x | ∃ n : ℕ, 0 < n ∧ IsPeriodicPt F n x}
      {y | ∃ n : ℕ, 0 < n ∧ IsPeriodicPt G n y}

def invariant_image_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    ∀ A : Set X, Invariant F A ↔ Invariant G (h '' A)

def invariant_sets_bijOnStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    Set.BijOn (fun A : Set X => h '' A) {A | Invariant F A} {B | Invariant G B}

def orbitSet_imageStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    ∀ x : X, h '' orbitSet F x = orbitSet G (h x)

def dense_orbit_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    ∀ x : X, Dense (orbitSet F x) ↔ Dense (orbitSet G (h x))

def dense_orbit_points_bijOnStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    Set.BijOn h {x | Dense (orbitSet F x)} {y | Dense (orbitSet G y)}

def fixed_pointStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    ∀ p : X, F p = p → G (h p) = h p

def lyapunovStable_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    Continuous F → Continuous G → ∀ p : X, F p = p →
    (LyapunovStable F p ↔ LyapunovStable G (h p))

def asymptoticallyStable_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y), IsConjugacy F G h →
    Continuous F → Continuous G → ∀ p : X, F p = p →
    (AsymptoticallyStable F p ↔ AsymptoticallyStable G (h p))

end Specs.D13Unified.Ch15.ConjugacyTransport
