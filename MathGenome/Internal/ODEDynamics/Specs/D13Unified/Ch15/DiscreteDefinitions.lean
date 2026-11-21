import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Normed.Group.Basic

/-!
Independent specification of paper.tex, Chapter 15, Definitions
`d13:15:discrete-system`, `d13:15:conjugacy-definition`, and
`d13:15:stability-definition`.

The orbit predicates are defined for arbitrary maps. In the paper the three
stability predicates are applied to fixed points of continuous maps; continuity
and fixedness are hypotheses of that setting, not consequences asserted by the
predicates. This allows the same quantitative predicates for maps continuous
only on a neighborhood, as in the subsequent local linearization theorems.
-/

namespace Specs.D13Unified.Ch15.DiscreteDefinitions

universe u v
open Filter Set Function
open scoped Topology

def DiscreteSystemType := Type u → Type u

/-- A discrete system is a self-map, with no topology required. -/
def DiscreteSystem : DiscreteSystemType :=
  fun X => X → X

def iterateType := {X : Type u} → (X → X) → ℕ → X → X

/-- Use the native natural-number iterate throughout. -/
def iterate : iterateType :=
  fun F n => F^[n]

def forwardOrbitType := {X : Type u} → (X → X) → X → ℕ → X

/-- The forward orbit as a sequence, including time zero. -/
def forwardOrbit : forwardOrbitType :=
  fun F x n => F^[n] x

def orbitSetType := {X : Type u} → (X → X) → X → Set X

/-- The set of values of the forward orbit. -/
def orbitSet : orbitSetType :=
  fun F x => Set.range (forwardOrbit F x)

def PositivelyInvariantType := {X : Type u} → (X → X) → Set X → Prop

/-- Positive invariance is image inclusion. -/
def PositivelyInvariant : PositivelyInvariantType :=
  fun F A => F '' A ⊆ A

def InvariantType := {X : Type u} → (X → X) → Set X → Prop

/-- Invariance requires equality of the image and the set. -/
def Invariant : InvariantType :=
  fun F A => F '' A = A

def HasLeastPeriodType := {X : Type u} → (X → X) → X → ℕ → Prop

/-- Least period is positive and excludes every smaller positive return. -/
def HasLeastPeriod : HasLeastPeriodType :=
  fun F x p => 0 < p ∧ Function.IsPeriodicPt F p x ∧
  ∀ m : ℕ, 0 < m → m < p → ¬Function.IsPeriodicPt F m x

def integerIterateType := {X : Type u} → (X ≃ X) → ℤ → X → X

/-- Signed iterates require a specified invertible map, never an arbitrary self-map. -/
def integerIterate : integerIterateType :=
  fun F n => match n with
  | Int.ofNat k => (F : _ → _)^[k]
  | Int.negSucc k => (F.symm : _ → _)^[k + 1]

def IsConjugacyType := {X : Type u} → {Y : Type v} → [TopologicalSpace X] →
  [TopologicalSpace Y] → (X → X) → (Y → Y) → (X ≃ₜ Y) → Prop

/-- A specified homeomorphism conjugates F to G. -/
def IsConjugacy : IsConjugacyType :=
  fun F G h => Function.Semiconj (h : _ → _) F G

def TopologicallyConjugateType := {X : Type u} → {Y : Type v} → [TopologicalSpace X] →
  [TopologicalSpace Y] → (X → X) → (Y → Y) → Prop

/-- Existence of a topological conjugacy. -/
def TopologicallyConjugate : TopologicallyConjugateType :=
  fun F G => ∃ h : _ ≃ₜ _, IsConjugacy F G h

def IsSemiconjugacyType := {X : Type u} → {Y : Type v} → [TopologicalSpace X] →
  [TopologicalSpace Y] → (X → X) → (Y → Y) → (X → Y) → Prop

/-- A semiconjugacy is continuous and surjective; injectivity is not required. -/
def IsSemiconjugacy : IsSemiconjugacyType :=
  fun F G h => Continuous h ∧ Function.Surjective h ∧ Function.Semiconj h F G

def LyapunovStableType := {X : Type u} → [MetricSpace X] → (X → X) → X → Prop

/-- The epsilon-delta orbit condition used for fixed points of continuous maps. -/
def LyapunovStable : LyapunovStableType :=
  fun F p => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x, dist x p < δ → ∀ n : ℕ, dist (F^[n] x) p < ε

def AttractsNeighborhoodType := {X : Type u} → [MetricSpace X] → (X → X) → X → Prop

/-- Every point of some ball converges to p; convergence is pointwise in x. -/
def AttractsNeighborhood : AttractsNeighborhoodType :=
  fun F p => ∃ δ : ℝ, 0 < δ ∧
  ∀ x, dist x p < δ → Tendsto (fun n : ℕ => F^[n] x) atTop (𝓝 p)

def AsymptoticallyStableType := {X : Type u} → [MetricSpace X] → (X → X) → X → Prop

/-- Asymptotic stability includes Lyapunov stability and local attraction. -/
def AsymptoticallyStable : AsymptoticallyStableType :=
  fun F p => LyapunovStable F p ∧ AttractsNeighborhood F p

def LocallyExponentiallyStableType := {E : Type u} → [NormedAddCommGroup E] → (E → E) → E → Prop

/-- The original quantitative bound on a neighborhood, for every natural n. -/
def LocallyExponentiallyStable : LocallyExponentiallyStableType :=
  fun F p => ∃ C : ℝ, 0 < C ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖x - p‖ < δ → ∀ n : ℕ,
    ‖F^[n] x - p‖ ≤ C * q ^ n * ‖x - p‖

def iterate_zeroStatement : Prop :=
  ∀ {X : Type u} (F : X → X), iterate F 0 = id

def iterate_succStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (n : ℕ),
  iterate F (n + 1) = F ∘ iterate F n

def forwardOrbit_zeroStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (x : X), forwardOrbit F x 0 = x

def forwardOrbit_succStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (x : X) (n : ℕ),
  forwardOrbit F x (n + 1) = F (forwardOrbit F x n)

def mem_orbitSetStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (x y : X),
  y ∈ orbitSet F x ↔ ∃ n : ℕ, F^[n] x = y

def positivelyInvariant_iff_mapsToStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (A : Set X),
  PositivelyInvariant F A ↔ Set.MapsTo F A A

def hasLeastPeriod_iffStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (x : X) (p : ℕ),
  HasLeastPeriod F x p ↔ 0 < p ∧ F^[p] x = x ∧
    ∀ m : ℕ, 0 < m → m < p → F^[m] x ≠ x

def hasLeastPeriod_iff_minimalPeriodStatement : Prop :=
  ∀ {X : Type u} (F : X → X) (x : X) (p : ℕ),
  HasLeastPeriod F x p ↔ 0 < p ∧ Function.minimalPeriod F x = p

def integerIterate_ofNatStatement : Prop :=
  ∀ {X : Type u} (F : X ≃ X) (n : ℕ),
  integerIterate F (n : ℤ) = (F : X → X)^[n]

def integerIterate_negSuccStatement : Prop :=
  ∀ {X : Type u} (F : X ≃ X) (n : ℕ),
  integerIterate F (Int.negSucc n) = (F.symm : X → X)^[n + 1]

def inverse_iterate_cancelStatement : Prop :=
  ∀ {X : Type u} (F : X ≃ X) (n : ℕ) (x : X),
  (F.symm : X → X)^[n] ((F : X → X)^[n] x) = x ∧
    (F : X → X)^[n] ((F.symm : X → X)^[n] x) = x

def isConjugacy_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (F : X → X) (G : Y → Y) (h : X ≃ₜ Y),
  IsConjugacy F G h ↔ (h : X → Y) ∘ F = G ∘ (h : X → Y)

def isSemiconjugacy_iffStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (F : X → X) (G : Y → Y) (h : X → Y),
  IsSemiconjugacy F G h ↔ Continuous h ∧ Function.Surjective h ∧ h ∘ F = G ∘ h

def lyapunovStable_iff_neighborhoodsStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (p : X),
  LyapunovStable F p ↔ ∀ V ∈ 𝓝 p, ∃ U ∈ 𝓝 p,
    ∀ x ∈ U, ∀ n : ℕ, F^[n] x ∈ V

def attractsNeighborhood_iffStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (p : X),
  AttractsNeighborhood F p ↔ ∃ U ∈ 𝓝 p,
    ∀ x ∈ U, Tendsto (fun n : ℕ => F^[n] x) atTop (𝓝 p)

def asymptoticallyStable_iff_neighborhoodsStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (F : X → X) (p : X),
  AsymptoticallyStable F p ↔ LyapunovStable F p ∧ ∃ U ∈ 𝓝 p,
    ∀ x ∈ U, Tendsto (fun n : ℕ => F^[n] x) atTop (𝓝 p)

def locallyExponentiallyStable_iff_neighborhoodsStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] (F : E → E) (p : E),
  LocallyExponentiallyStable F p ↔
    ∃ C : ℝ, 0 < C ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ U ∈ 𝓝 p,
      ∀ x ∈ U, ∀ n : ℕ, ‖F^[n] x - p‖ ≤ C * q ^ n * ‖x - p‖

end Specs.D13Unified.Ch15.DiscreteDefinitions
