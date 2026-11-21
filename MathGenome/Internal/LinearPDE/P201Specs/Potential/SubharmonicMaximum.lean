import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Semicontinuity.Basic

/-! Independent statements for the definition and maximum/smooth-criterion portions
of paper.tex:769–824 and 840–846. Comparison and its reverse belong to L04_subharmonic_comparison.
Functions are total, and all hypotheses concern their restrictions to the domain.
`EReal` together with the no-top condition represents [-∞,∞).
The signed extended integral uses the positive and negative Lebesgue integrals;
the compact-upper-bound assertions ensure its positive part is finite at every use.
-/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace P201Specs.SubharmonicMaximum

abbrev ExtendedIntegralType := {n : ℕ} → Measure (Space n) → (Space n → EReal) → EReal

def extendedIntegral : ExtendedIntegralType := fun μ u =>
  ((∫⁻ x, (u x).toENNReal ∂μ) : EReal) -
    ((∫⁻ x, (-u x).toENNReal ∂μ) : EReal)

abbrev ExtendedAverageType := ExtendedIntegralType

def extendedAverage : ExtendedAverageType := fun μ u =>
  ((μ.real univ)⁻¹ : EReal) * extendedIntegral μ u

abbrev SubmeanType := {n : ℕ} → Domain n → (Space n → EReal) → Prop

def HasSphereSubmean : SubmeanType := fun Ω u =>
  ∀ (a : Space _) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    u a ≤ extendedAverage (sphereSurface a r) u

def HasBallSubmean : SubmeanType := fun Ω u =>
  ∀ (a : Space _) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    u a ≤ extendedAverage (volume.restrict (ball a r)) u

/-- Nontrivial on each connected component, with no positive infinite values. -/
def IsAdmissible : SubmeanType := fun Ω u =>
  UpperSemicontinuousOn u (Ω : Set _) ∧ (∀ x ∈ Ω, u x ≠ ⊤) ∧
    ∀ a ∈ Ω, ∃ x ∈ connectedComponentIn (Ω : Set _) a, u x ≠ ⊥

def IsSubharmonic : SubmeanType := fun Ω u =>
  IsAdmissible Ω u ∧ HasSphereSubmean Ω u

abbrev RealSubmeanType := {n : ℕ} → Domain n → (Space n → ℝ) → Prop

def HasRealSphereSubmean : RealSubmeanType := fun Ω u =>
  ∀ (a : Space _) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    u a ≤ sphereAverage u a r

def HasRealBallSubmean : RealSubmeanType := fun Ω u =>
  ∀ (a : Space _) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    u a ≤ ballAverage u a r

/-- Upper semicontinuity and exclusion of +∞ give a real compact upper bound,
including when every value on the compact set is -∞. -/
def CompactUpperBoundStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (u : Space n → EReal),
    UpperSemicontinuousOn u (Ω : Set _) → (∀ x ∈ Ω, u x ≠ ⊤) →
    ∀ K : Set (Space n), IsCompact K → K ⊆ (Ω : Set _) →
      ∃ C : ℝ, ∀ x ∈ K, u x ≤ (C : EReal)

/-- The positive part is integrable for every tested sphere and ball. -/
def PositivePartFiniteStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal),
    UpperSemicontinuousOn u (Ω : Set _) → (∀ x ∈ Ω, u x ≠ ⊤) →
    ∀ (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
      (∫⁻ x, (u x).toENNReal ∂sphereSurface a r) < ⊤ ∧
      (∫⁻ x in ball a r, (u x).toENNReal) < ⊤

/-- Agreement with the ordinary real mean when the integrand is integrable. -/
def RealAverageBridgeStatement : Prop :=
  ∀ {n : ℕ} (μ : Measure (Space n)) (u : Space n → ℝ), Integrable u μ →
    extendedAverage μ (fun x => (u x : EReal)) =
      (((μ.real univ)⁻¹ * ∫ x, u x ∂μ : ℝ) : EReal)

/-- In particular the extended predicates specialize to the usual real ones. -/
def ContinuousSubmeanBridgeStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ), ContinuousOn u Ω →
    (HasSphereSubmean Ω (fun x => (u x : EReal)) ↔ HasRealSphereSubmean Ω u) ∧
    (HasBallSubmean Ω (fun x => (u x : EReal)) ↔ HasRealBallSubmean Ω u)

def SphereImpliesBallStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal),
    UpperSemicontinuousOn u (Ω : Set _) → (∀ x ∈ Ω, u x ≠ ⊤) →
    HasSphereSubmean Ω u → HasBallSubmean Ω u

/-- The maximum is on the full component, rather than merely locally attained. -/
def StrongMaximumStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal),
    UpperSemicontinuousOn u (Ω : Set _) → (∀ x ∈ Ω, u x ≠ ⊤) →
    HasBallSubmean Ω u → ∀ (a : Space n), a ∈ Ω → ∀ m : ℝ, u a = (m : EReal) →
    (∀ x ∈ connectedComponentIn (Ω : Set _) a, u x ≤ (m : EReal)) →
      ∀ x ∈ connectedComponentIn (Ω : Set _) a, u x = (m : EReal)

/-- The approach filter is from the domain at each boundary point; boundary
values and boundary regularity are not assumed. -/
def BoundaryMaximumStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal) (M : ℝ),
    Bornology.IsBounded (Ω : Set (Space n)) → UpperSemicontinuousOn u (Ω : Set _) →
    (∀ x ∈ Ω, u x ≠ ⊤) → HasBallSubmean Ω u →
    (∀ ζ ∈ frontier (Ω : Set _), limsup u (𝓝[Ω] ζ) ≤ (M : EReal)) →
      ∀ x ∈ Ω, u x ≤ (M : EReal)

def SmoothSphereCriterionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ), ContDiffOn ℝ 2 u Ω →
    (HasRealSphereSubmean Ω u ↔ ∀ x ∈ Ω, 0 ≤ laplacian u x)

def SmoothBallCriterionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ), ContDiffOn ℝ 2 u Ω →
    (HasRealBallSubmean Ω u ↔ ∀ x ∈ Ω, 0 ≤ laplacian u x)

/-- The original subharmonicity definition, specialized to real C² functions. -/
def SmoothSubharmonicCriterionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ), ContDiffOn ℝ 2 u Ω →
    (IsSubharmonic Ω (fun x => (u x : EReal)) ↔ ∀ x ∈ Ω, 0 ≤ laplacian u x)

def SmoothExtendedBallCriterionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ), ContDiffOn ℝ 2 u Ω →
    (HasBallSubmean Ω (fun x => (u x : EReal)) ↔ ∀ x ∈ Ω, 0 ≤ laplacian u x)

end P201Specs.SubharmonicMaximum
