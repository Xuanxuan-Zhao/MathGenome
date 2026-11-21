import MathGenome.Internal.FourierSobolev.Specs.P102.U4.GraphAreaPieces
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Normed.Affine.Isometry

/-! Independent specifications for the area theorem, paper.tex:1548–1575,
1638–1672. Null measurability is measurability for the completed measure;
the Hausdorff measure is Euclidean normalized, including counting in dimension 0.
The gradient is any Borel representative of the a.e. classical derivative. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace P102.U4.GraphArea
open GraphPieces
def surfaceMeasure {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ) :
    Measure (Ambient m) := (μHE[m] : Measure (Ambient m)).restrict (graph γ '' (U : Set (Space m)))

def density {m : ℕ} (a : Space m → Space m) (x : Space m) : ℝ≥0∞ :=
  ENNReal.ofReal (jacobian (a x))

def conormal {m : ℕ} (a : Space m) : Ambient m := WithLp.toLp 2 (a, (-1 : ℝ))

def unitNormal {m : ℕ} (a : Space m) : Ambient m := (jacobian a)⁻¹ • conormal a

def normalField {m : ℕ} (a : Space m → Space m) (z : Ambient m) : Ambient m :=
  unitNormal (a z.ofLp.1)

def epigraphSide {m : ℕ} (U : Opens (Space m)) (γ : Space m → ℝ) : Set (Ambient m) :=
  {z | z.ofLp.1 ∈ U ∧ γ z.ofLp.1 < z.ofLp.2}

/-- A unit vector perpendicular to the intrinsic tangent cone, pointing outward:
the positive normal ray is exterior and the negative ray is interior near zero. -/
def OutwardUnitNormal {m : ℕ} (Ω S : Set (Ambient m)) (p n : Ambient m) : Prop :=
  ‖n‖ = 1 ∧ (∀ v ∈ tangentConeAt ℝ S p, inner ℝ n v = 0) ∧
    ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), p + r • n ∉ Ω ∧ p - r • n ∈ Ω

namespace Expected

def BorelArea : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ B : Set (Space m), MeasurableSet B → B ⊆ U →
      (μHE[m] : Measure (Ambient m)) (graph γ '' B) =
        ∫⁻ x in B, ENNReal.ofReal (jacobian (a x))

def CompletedArea : Prop :=
  ∀ (m : ℕ), ∀ (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ B : Set (Space m), NullMeasurableSet B volume → B ⊆ U →
      NullMeasurableSet (graph γ '' B) (μHE[m] : Measure (Ambient m)) ∧
      (μHE[m] : Measure (Ambient m)) (graph γ '' B) =
        ∫⁻ x in B, ENNReal.ofReal (jacobian (a x))

/-- The statement also asserts completed-measure measurability of the pullback. -/
def NonnegativeIntegral : Prop :=
  ∀ (m : ℕ), ∀ (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ w : Ambient m → ℝ≥0∞, NullMeasurable w (surfaceMeasure U γ) →
      NullMeasurable (fun x => w (graph γ x)) (volume.restrict (U : Set (Space m))) ∧
      (∫⁻ z, w z ∂surfaceMeasure U γ) =
        ∫⁻ x in (U : Set (Space m)), w (graph γ x) * density a x

/-- Real and complex integration are covered by this stronger real-Banach formulation. -/
def Integral : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (m : ℕ), ∀ (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ w : Ambient m → E,
      (Integrable w (surfaceMeasure U γ) ↔
        IntegrableOn (fun x => jacobian (a x) • w (graph γ x)) U volume) ∧
      (∫ z, w z ∂surfaceMeasure U γ) =
        ∫ x in (U : Set (Space m)), jacobian (a x) • w (graph γ x)

def ZeroDimension : Prop :=
  (volume : Measure (Space 0)) = Measure.dirac 0 ∧
  (∀ a : Space 0, jacobian a = 1) ∧
  ∀ (γ : Space 0 → ℝ) (B : Set (Space 0)),
    B = ∅ ∨ B = {0} ∧
      (μHE[0] : Measure (Ambient 0)) (graph γ '' B) = 1

def Flux : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ F : Ambient m → Ambient m,
      (Integrable (fun z => inner ℝ (F z) (normalField a z)) (surfaceMeasure U γ) ↔
        IntegrableOn (fun x => inner ℝ (F (graph γ x)) (conormal (a x))) U volume) ∧
      (∫ z, inner ℝ (F z) (normalField a z) ∂surfaceMeasure U γ) =
        ∫ x in (U : Set (Space m)), inner ℝ (F (graph γ x)) (conormal (a x))

def Tangent : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ) (x a : Space m),
    x ∈ U → HasFDerivAt γ (innerSL ℝ a) x →
      tangentConeAt ℝ (graph γ '' (U : Set (Space m))) (graph γ x) =
        (affineGraph a).range

def Outward : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ) (x a : Space m),
    x ∈ U → HasFDerivAt γ (innerSL ℝ a) x →
      OutwardUnitNormal (epigraphSide U γ) (graph γ '' (U : Set (Space m)))
        (graph γ x) (unitNormal a)

def AENormal : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
      ∀ᵐ z ∂surfaceMeasure U γ,
        OutwardUnitNormal (epigraphSide U γ) (graph γ '' (U : Set (Space m)))
          z (normalField a z)

/-- Arbitrary rigid coordinate frames, and local agreement of graph and side.
The chart points need only be differentiability points of their Lipschitz graphs. -/
def ChartAgreement : Prop :=
  ∀ (m : ℕ) (U V : Opens (Space m)) (γ δ : Space m → ℝ)
    (x y a b : Space m) (e f : Ambient m ≃ᵃⁱ[ℝ] Ambient m),
    x ∈ U → y ∈ V → HasFDerivAt γ (innerSL ℝ a) x →
    HasFDerivAt δ (innerSL ℝ b) y → e (graph γ x) = f (graph δ y) →
    (e '' (graph γ '' (U : Set (Space m)))) =ᶠ[nhds (e (graph γ x))]
      (f '' (graph δ '' (V : Set (Space m)))) →
    (e '' epigraphSide U γ) =ᶠ[nhds (e (graph γ x))] (f '' epigraphSide V δ) →
      (e.linearIsometryEquiv '' ((affineGraph a).range : Set (Ambient m))) =
        (f.linearIsometryEquiv '' ((affineGraph b).range : Set (Ambient m))) ∧
      e.linearIsometryEquiv (unitNormal a) = f.linearIsometryEquiv (unitNormal b)

/-- There is a gradient representative under just the original Lipschitz
hypothesis. In dimension zero its value is the unique zero vector. -/
def GradientExistence : Prop :=
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
      ∃ a : Space m → Space m, GradientRepresentative U γ a

def ZeroNormal : Prop :=
  ∀ a : Space 0, unitNormal a = WithLp.toLp 2 (0, (-1 : ℝ))

/-- A.e. measurability expresses measurability for the completed measures.
This equivalence applies in particular to real and complex weights and fields. -/
def AEPullbackMeasurability : Prop :=
  ∀ (E : Type*) [MeasurableSpace E],
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ w : Ambient m → E, AEMeasurable w (surfaceMeasure U γ) ↔
      AEMeasurable (fun x => w (graph γ x)) (volume.restrict (U : Set (Space m)))

def PullbackMeasurability : Prop :=
  ∀ (E : Type*) [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E],
  ∀ (m : ℕ) (U : Opens (Space m)) (γ : Space m → ℝ)
    (L : ℝ≥0), LipschitzOnWith L γ U →
    ∀ a : Space m → Space m, GradientRepresentative U γ a →
    ∀ w : Ambient m → E, NullMeasurable w (surfaceMeasure U γ) ↔
      NullMeasurable (fun x => w (graph γ x)) (volume.restrict (U : Set (Space m)))

end Expected
end P102.U4.GraphArea
