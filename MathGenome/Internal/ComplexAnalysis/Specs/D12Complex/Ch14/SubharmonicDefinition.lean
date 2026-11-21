import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.DiskDirichlet

/-! Continuous subharmonicity in paper.tex:2611–2616. All functions are total;
only their restrictions to the indicated open sets and closed disks are used.
The Poisson extension is the translated, closed-disk extension from Ch13. -/
noncomputable section
open Set Metric

namespace D12Complex

/-- The harmonic Poisson extension on a disk, with the given values on its circle. -/
def diskPoissonExtension (a : ℂ) (R : ℝ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  Specs.D12Complex.Ch13.DiskDirichlet.closedPoissonIntegral_value
    R (fun w => φ (a + w)) (z - a)

/-- The chosen continuous subharmonic class, defined by Poisson comparison. -/
def SubharmonicOn (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ (a : ℂ) (R : ℝ), 0 < R → closedBall a R ⊆ U →
      ∀ z ∈ closedBall a R, u z ≤ diskPoissonExtension a R u z

/-- The center submean characterization, retaining continuity and openness. -/
def CircleSubmeanOn (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ (a : ℂ) (R : ℝ), 0 < R → closedBall a R ⊆ U →
      u a ≤ Real.circleAverage u a R

/-- Comparison with every real harmonic function continuous on a test closed disk. -/
def HarmonicComparisonOn (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ (a : ℂ) (R : ℝ), 0 < R → closedBall a R ⊆ U →
      ∀ h : ℂ → ℝ, ContinuousOn h (closedBall a R) → HarmonicOn (ball a R) h →
        (∀ ζ ∈ sphere a R, u ζ ≤ h ζ) → ∀ z ∈ closedBall a R, u z ≤ h z

/-- Superharmonicity is subharmonicity after sign reversal. -/
def SuperharmonicOn (U : Set ℂ) (b : ℂ → ℝ) : Prop :=
  SubharmonicOn U (fun z => -b z)

end D12Complex

namespace Specs.D12Complex.Ch14.SubharmonicDefinition
open _root_.D12Complex

def diskPoissonExtension_type := ℂ → ℝ → (ℂ → ℝ) → ℂ → ℝ
def diskPoissonExtension_value : diskPoissonExtension_type := fun a R φ z =>
  Specs.D12Complex.Ch13.DiskDirichlet.closedPoissonIntegral_value
    R (fun w => φ (a + w)) (z - a)

def SubharmonicOn_type := Set ℂ → (ℂ → ℝ) → Prop
def SubharmonicOn_value : SubharmonicOn_type := fun U u =>
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ (a : ℂ) (R : ℝ), 0 < R → closedBall a R ⊆ U →
      ∀ z ∈ closedBall a R, u z ≤ diskPoissonExtension a R u z

def CircleSubmeanOn_type := Set ℂ → (ℂ → ℝ) → Prop
def CircleSubmeanOn_value : CircleSubmeanOn_type := fun U u =>
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ (a : ℂ) (R : ℝ), 0 < R → closedBall a R ⊆ U →
      u a ≤ Real.circleAverage u a R

def HarmonicComparisonOn_type := Set ℂ → (ℂ → ℝ) → Prop
def HarmonicComparisonOn_value : HarmonicComparisonOn_type := fun U u =>
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ (a : ℂ) (R : ℝ), 0 < R → closedBall a R ⊆ U →
      ∀ h : ℂ → ℝ, ContinuousOn h (closedBall a R) → HarmonicOn (ball a R) h →
        (∀ ζ ∈ sphere a R, u ζ ≤ h ζ) → ∀ z ∈ closedBall a R, u z ≤ h z

def SuperharmonicOn_type := Set ℂ → (ℂ → ℝ) → Prop
def SuperharmonicOn_value : SuperharmonicOn_type := fun U b =>
  SubharmonicOn U (fun z => -b z)

def diskPoissonExtension_solution_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere a R) →
    ContinuousOn (diskPoissonExtension a R φ) (closedBall a R) ∧
    HarmonicOn (ball a R) (diskPoissonExtension a R φ) ∧
    EqOn (diskPoissonExtension a R φ) φ (sphere a R)

def diskPoissonExtension_center_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (φ : ℂ → ℝ), 0 < R → ContinuousOn φ (sphere a R) →
    diskPoissonExtension a R φ a = Real.circleAverage φ a R

def subharmonicOn_iff_circleSubmeanOn_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), SubharmonicOn U u ↔ CircleSubmeanOn U u

def subharmonicOn_iff_harmonicComparisonOn_type : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), SubharmonicOn U u ↔ HarmonicComparisonOn U u

end Specs.D12Complex.Ch14.SubharmonicDefinition
