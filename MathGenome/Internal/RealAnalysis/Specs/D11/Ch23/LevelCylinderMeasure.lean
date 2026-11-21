import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.UndergraphOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.GeneratedRingAlgebra

/-! Cylinder stage of paper.tex:6252–6260. All functions have actual finite
real values. No constant unit or finite total mass is assumed. -/
noncomputable section
universe u
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace D11.Ch23.Specs

def LevelTruncation {X : Type u} (f : X → ℝ) (b : ℝ) (n : ℕ) : X → ℝ :=
  fun x => min 1 ((n : ℝ) * (f x - min (f x) b))

def CylinderMass {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) (c : ℝ) (A : Set X) : ℝ≥0∞ :=
  UndergraphMeasure V L (A ×ˢ Ico 0 c)

/-- The exact infinity-outside-ring extension prescription, on A_V only. -/
def CylinderExtensionFormula {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) (μ : @Measure X (positiveLevelMeasurableSpace V)) : Prop := by
  classical
  exact ∀ A, MeasurableSet[positiveLevelMeasurableSpace V] A →
    μ A = if A ∈ positiveLevelSigmaRing V then CylinderMass V L 1 A else ∞

/-- Choose the measure with the prescribed measurable-set values if it exists.
The zero fallback makes the definition total outside the construction hypotheses.
Existence and the formula under those hypotheses are separate proof obligations. -/
def LevelCylinderMeasure {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) : @Measure X (positiveLevelMeasurableSpace V) := by
  classical
  exact if h : ∃ μ, CylinderExtensionFormula V L μ then h.choose else 0

def LevelTruncationType := ∀ {X : Type u}, (X → ℝ) → ℝ → ℕ → X → ℝ
def CylinderMassType := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  (V →ₗ[ℝ] ℝ) → ℝ → Set X → ℝ≥0∞
def LevelCylinderMeasureType := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  (V →ₗ[ℝ] ℝ) → @Measure X (positiveLevelMeasurableSpace V)

def LevelTruncationMem : Prop := ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
  IsStone V → ∀ f ∈ V, ∀ b : ℝ, 0 < b → ∀ n, LevelTruncation f b n ∈ V

def LevelTruncationConvergence : Prop := ∀ {X : Type u} (f : X → ℝ) (b : ℝ),
  (∀ n x, 0 ≤ LevelTruncation f b n x ∧ LevelTruncation f b n x ≤ 1) ∧
  (∀ x, Monotone (fun n => LevelTruncation f b n x)) ∧
  (∀ x, Tendsto (fun n => LevelTruncation f b n x) atTop
    (𝓝 (({x | b < f x} : Set X).indicator (fun _ => (1 : ℝ)) x)))

def PositiveLevelCylinderMeasurable : Prop := ∀ {X : Type u}
  (V : Submodule ℝ (X → ℝ)), IsStone V → ∀ f ∈ V, ∀ b : ℝ, 0 < b →
  ∀ c : ℝ, 0 < c →
    MeasurableSet[UndergraphMeasurableSpace V] ({x | b < f x} ×ˢ Ico 0 c)

def RingCylinderMeasurable : Prop := ∀ {X : Type u}
  (V : Submodule ℝ (X → ℝ)), IsStone V → ∀ A ∈ positiveLevelSigmaRing V,
  ∀ c : ℝ, 0 < c → MeasurableSet[UndergraphMeasurableSpace V] (A ×ˢ Ico 0 c)

def CylinderRingMeasureExists : Prop := ∀ {X : Type u}
  (V : Submodule ℝ (X → ℝ)), IsStone V → ∀ L : V →ₗ[ℝ] ℝ,
  ∃ μ₀ : SigmaRingMeasure (positiveLevelSigmaRing V),
    ∀ A (hA : A ∈ positiveLevelSigmaRing V), μ₀ ⟨A, hA⟩ = CylinderMass V L 1 A

def LevelCylinderMeasureApply : Prop := ∀ {X : Type u}
  (V : Submodule ℝ (X → ℝ)), IsStone V → ∀ L : V →ₗ[ℝ] ℝ,
  CylinderExtensionFormula V L (LevelCylinderMeasure V L)

/-- The right side is a finite ENNReal value; L is evaluated on f⁺ in V. -/
def PositiveLevelMassBound : Prop := ∀ {X : Type u}
  (V : Submodule ℝ (X → ℝ)) (_hV : IsVectorLattice V), IsStone V →
  ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L → ∀ f : V, ∀ b : ℝ, 0 < b →
  ∀ (hp : (fun x => max ((f : X → ℝ) x) 0) ∈ V),
    CylinderMass V L 1 {x | b < (f : X → ℝ) x} ≤
      ENNReal.ofReal (L ⟨_, hp⟩ / b) ∧ ENNReal.ofReal (L ⟨_, hp⟩ / b) < ∞

def PositiveLevelCylinderScaling : Prop := ∀ {X : Type u}
  (V : Submodule ℝ (X → ℝ)), IsVectorLattice V → IsStone V →
  ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L → ∀ f ∈ V, ∀ b : ℝ, 0 < b →
  ∀ c : ℝ, 0 < c → CylinderMass V L c {x | b < f x} =
    ENNReal.ofReal c * CylinderMass V L 1 {x | b < f x}

/-- Allows nested levels of different functions, hence also successive levels
of the same function. Both thresholds are strictly positive. -/
def NestedLevelCylinderScaling : Prop := ∀ {X : Type u}
  (V : Submodule ℝ (X → ℝ)), IsVectorLattice V → IsStone V →
  ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L →
  ∀ f ∈ V, ∀ g ∈ V, ∀ b d : ℝ, 0 < b → 0 < d →
  {x | d < g x} ⊆ {x | b < f x} → ∀ c : ℝ, 0 < c →
    CylinderMass V L c ({x | b < f x} \ {x | d < g x}) =
      ENNReal.ofReal c * CylinderMass V L 1 ({x | b < f x} \ {x | d < g x})

end D11.Ch23.Specs
