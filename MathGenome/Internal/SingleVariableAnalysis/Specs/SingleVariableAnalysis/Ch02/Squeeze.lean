import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided

/-!
Independent specifications for K03.02.squeeze, paper.tex:401–409.
All inequalities hold eventually on the same domain and approach. The five
constructors of RealApproach include each side and both input infinities.
Limits are finite; an error majorant has no extra global sign hypothesis.
The metric finite-point formulation also covers complex input domains.
Punctured squeeze and error estimates permit vacuity, as does the upstream
punctured-limit predicate. Order of limits requires accumulation. The common
approach wrapper already contains nontriviality (side accumulation or
unboundedness in the selected direction).
-/
namespace Specs.SingleVariableAnalysis.Ch02.Squeeze

open _root_.SingleVariableAnalysis
open RelativeLimit OneSided
universe u v

/-- Real squeeze at a finite point, for real or complex metric input domains. -/
def relativePuncturedLimitSqueeze : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f g h : X → ℝ) (E : Set X) (a : X) (L : ℝ),
    (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      f x ≤ g x ∧ g x ≤ h x) →
    relativePuncturedLimitValue f E a L → relativePuncturedLimitValue h E a L →
    relativePuncturedLimitValue g E a L

/-- The metric error estimate specializes to scalar modulus via the usual metric. -/
def relativePuncturedLimitOfDistLe : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L : Y) (v : X → ℝ),
    (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      dist (f x) L ≤ v x) →
    relativePuncturedLimitValue v E a 0 → relativePuncturedLimitValue f E a L

/-- Explicit real scalar error estimate. -/
def relativePuncturedLimitOfAbsLe : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : X)
    (L : ℝ) (v : X → ℝ),
    (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      |f x - L| ≤ v x) →
    relativePuncturedLimitValue v E a 0 → relativePuncturedLimitValue f E a L

/-- Explicit complex scalar error estimate. -/
def relativePuncturedLimitOfNormLe : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : X)
    (L : ℂ) (v : X → ℝ),
    (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ →
      ‖f x - L‖ ≤ v x) →
    relativePuncturedLimitValue v E a 0 → relativePuncturedLimitValue f E a L

def relativePuncturedLimitLeOfEventuallyLe : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f g : X → ℝ) (E : Set X)
    (a : X) (A B : ℝ), domainAccumulationValue E a →
    (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, 0 < dist x a → dist x a < δ → f x ≤ g x) →
    relativePuncturedLimitValue f E a A → relativePuncturedLimitValue g E a B → A ≤ B

/-- One theorem for punctured, right, left, +∞ and -∞ input approaches. -/
def finiteApproachLimitSqueeze : Prop :=
  ∀ (f g h : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (L : ℝ),
    approachEventuallyValue E q (fun x => f x ≤ g x ∧ g x ≤ h x) →
    finiteApproachLimitValue f E q L → finiteApproachLimitValue h E q L →
    finiteApproachLimitValue g E q L

def finiteApproachLimitOfDistLe : Prop :=
  ∀ {Y : Type u} [MetricSpace Y] (f : ℝ → Y) (E : Set ℝ)
    (q : RealApproach) (L : Y) (v : ℝ → ℝ),
    approachEventuallyValue E q (fun x => dist (f x) L ≤ v x) →
    finiteApproachLimitValue v E q 0 → finiteApproachLimitValue f E q L

def finiteApproachLimitOfAbsLe : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (L : ℝ) (v : ℝ → ℝ),
    approachEventuallyValue E q (fun x => |f x - L| ≤ v x) →
    finiteApproachLimitValue v E q 0 → finiteApproachLimitValue f E q L

def finiteApproachLimitOfNormLe : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (q : RealApproach) (L : ℂ) (v : ℝ → ℝ),
    approachEventuallyValue E q (fun x => ‖f x - L‖ ≤ v x) →
    finiteApproachLimitValue v E q 0 → finiteApproachLimitValue f E q L

def finiteApproachLimitLeOfEventuallyLe : Prop :=
  ∀ (f g : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (A B : ℝ),
    approachEventuallyValue E q (fun x => f x ≤ g x) →
    finiteApproachLimitValue f E q A → finiteApproachLimitValue g E q B → A ≤ B

end Specs.SingleVariableAnalysis.Ch02.Squeeze
