import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.CkDependence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Scalar angular evolution used in paper.tex:3673–3693.
All radii are signed. The hypotheses concern only the vector field, not its
solutions. The normalized amplitude uses the shared canonical maximal IVP.
Its totalization has no meaning outside the explicit solution domain below. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace D13Unified.Ch16.HopfAngularScalarEstimates

structure AngularData where
  T : ℝ
  ρ : ℝ
  ε : ℝ
  M : ℝ
  A : ℝ → ℝ
  B : ℝ → ℝ
  domain : Set ((ℝ × ℝ) × ℝ)
  G : ((ℝ × ℝ) × ℝ) → ℝ

def angularField (d : AngularData) (θ r μ : ℝ) : ℝ := r * d.G ((θ,r),μ)

def remainder (d : AngularData) (θ r μ : ℝ) : ℝ :=
  angularField d θ r μ - d.A μ * r - d.B μ * r ^ 3

def cylinder (d : AngularData) : Set ((ℝ × ℝ) × ℝ) :=
  {q | q.1.1 ∈ Icc 0 d.T ∧ |q.1.2| < d.ρ ∧ |q.2| < d.ε}

/-- No crossing, nondegeneracy, return map, or solution certificate is assumed. -/
structure Hypotheses (d : AngularData) : Prop where
  T_pos : 0 < d.T
  radius_pos : 0 < d.ρ
  parameter_pos : 0 < d.ε
  bound_nonneg : 0 ≤ d.M
  open_domain : IsOpen d.domain
  contains_cylinder : cylinder d ⊆ d.domain
  smooth_G : ContDiffOn ℝ 2 d.G d.domain
  smooth_A : ContDiffOn ℝ 2 d.A (Ioo (-d.ε) d.ε)
  smooth_B : ContDiffOn ℝ 2 d.B (Ioo (-d.ε) d.ε)
  value_at_zero : ∀ θ ∈ Icc 0 d.T, ∀ μ, |μ| < d.ε →
    d.G ((θ,0),μ) = d.A μ
  remainder_differentiable : ∀ q ∈ cylinder d,
    DifferentiableAt ℝ (fun r => remainder d q.1.1 r q.2) q.1.2 ∧
    DifferentiableAt ℝ (fun μ => remainder d q.1.1 q.1.2 μ) q.2
  remainder_bounds : ∀ q ∈ cylinder d,
    |remainder d q.1.1 q.1.2 q.2| ≤ d.M * |q.1.2| ^ 4 ∧
    |deriv (fun r => remainder d q.1.1 r q.2) q.1.2| ≤ d.M * |q.1.2| ^ 3 ∧
    |deriv (fun μ => remainder d q.1.1 q.1.2 μ) q.2| ≤ d.M * |q.1.2| ^ 4

/-- Variables are `((θ,Y),(r₀,μ))`. The condition is on `r₀ Y`, not Y. -/
def normalizedDomain (d : AngularData) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {q | ((q.1.1,q.2.1 * q.1.2),q.2.2) ∈ d.domain}

def normalizedField (d : AngularData) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  q.1.2 * d.G ((q.1.1,q.2.1 * q.1.2),q.2.2)

/-- A construction from the vector-field hypotheses only. -/
def normalizedODE (d : AngularData) (h : Hypotheses d) : ParameterODE ℝ (ℝ × ℝ) where
  domain := normalizedDomain d
  isOpen_domain := h.open_domain.preimage
    ((continuous_fst.fst.prodMk (continuous_snd.fst.mul continuous_fst.snd)).prodMk
      continuous_snd.snd)
  field := fun q => normalizedField d q.val
  continuous_field := by
    have hc : ContinuousOn (normalizedField d) (normalizedDomain d) :=
      continuousOn_fst.snd.mul (h.smooth_G.continuousOn.comp
        ((continuousOn_fst.fst.prodMk (continuousOn_snd.fst.mul
          continuousOn_fst.snd)).prodMk continuousOn_snd.snd) (fun _ hq => hq))
    exact continuousOn_iff_continuous_domRestrict.mp hc

/-- Parameter coordinates are `(r₀,μ)` and the initial Y-value is always one. -/
def amplitude (d : AngularData) (h : Hypotheses d) (θ r μ : ℝ) : ℝ :=
  Specs.D13Unified.Ch04.MaximalSolutionMap.parameterSolutionValueValue
    (normalizedODE d h) θ 0 1 (r,μ)

def amplitudeDomain (d : AngularData) (h : Hypotheses d) : Set (ℝ × (ℝ × ℝ)) :=
  {q | (q.1,((0,1),q.2)) ∈
    Specs.D13Unified.Ch04.MaximalSolutionMap.parameterSolutionDomainValue (normalizedODE d h)}

def radialSolution (d : AngularData) (h : Hypotheses d) (θ r μ : ℝ) : ℝ :=
  r * amplitude d h θ r μ

def endpoint (d : AngularData) (h : Hypotheses d) (r μ : ℝ) : ℝ :=
  radialSolution d h d.T r μ

/-- This expression has no division by A and includes A=0. -/
def cubicCoefficient (d : AngularData) (μ : ℝ) : ℝ :=
  d.B μ * Real.exp (d.T * d.A μ) * ∫ s in 0..d.T, Real.exp (2 * d.A μ * s)

def endpointError (d : AngularData) (h : Hypotheses d) (r μ : ℝ) : ℝ :=
  endpoint d h r μ - Real.exp (d.T * d.A μ) * r - cubicCoefficient d μ * r ^ 3

def dividedDisplacement (d : AngularData) (h : Hypotheses d) (r μ : ℝ) : ℝ :=
  amplitude d h d.T r μ - 1

def parameterBox (δ η : ℝ) : Set (ℝ × ℝ) :=
  Ioo (-δ) δ ×ˢ Ioo (-η) η

end D13Unified.Ch16.HopfAngularScalarEstimates

namespace Specs.D13Unified.Ch16.HopfAngularScalarEstimates
open _root_.D13Unified.Ch16.HopfAngularScalarEstimates

/-- Common normalized evolution, including its actual open domain and the
C² extension at zero. This is a conclusion to be proved, never an assumption. -/
def EvolutionOnBox (d : AngularData) (h : Hypotheses d) (δ η L a b : ℝ) : Prop :=
  0 < δ ∧ δ < d.ρ ∧ 0 < η ∧ η < d.ε ∧ 0 < L ∧
  a < 0 ∧ d.T < b ∧ L * δ < d.ρ ∧
  (Ioo a b ×ˢ parameterBox δ η) ⊆ amplitudeDomain d h ∧
  ContDiffOn ℝ 2 (fun q : ℝ × (ℝ × ℝ) => amplitude d h q.1 q.2.1 q.2.2)
    (Ioo a b ×ˢ parameterBox δ η) ∧
  (∀ r μ, (r,μ) ∈ parameterBox δ η →
    amplitude d h 0 r μ = 1 ∧
    (∀ θ ∈ Ioo a b,
      ((θ,radialSolution d h θ r μ),μ) ∈ d.domain ∧
      HasDerivAt (fun s => amplitude d h s r μ)
        (amplitude d h θ r μ * d.G ((θ,radialSolution d h θ r μ),μ)) θ ∧
      HasDerivAt (fun s => radialSolution d h s r μ)
        (angularField d θ (radialSolution d h θ r μ) μ) θ) ∧
    radialSolution d h 0 r μ = r ∧
    (∀ θ ∈ Icc 0 d.T,
      |radialSolution d h θ r μ| ≤ L * |r| ∧
      |radialSolution d h θ r μ| < d.ρ ∧
      (0 < r → 0 < radialSolution d h θ r μ))) ∧
  (∀ μ, |μ| < η → ∀ θ ∈ Icc 0 d.T,
    amplitude d h θ 0 μ = Real.exp (d.A μ * θ)) ∧
  ContDiffOn ℝ 2 (fun q : ℝ × ℝ => dividedDisplacement d h q.1 q.2)
    (parameterBox δ η) ∧
  (∀ r μ, endpoint d h r μ = r * (1 + dividedDisplacement d h r μ))

def NormalizedEvolution : Prop :=
  ∀ (d : AngularData) (h : Hypotheses d), ∃ δ η L a b : ℝ,
    EvolutionOnBox d h δ η L a b

/-- Full generic scalar theorem, with all three uniform estimates also at
zero radius. The separately stated evolution result supplies only the first
part of the conclusion; the estimates remain genuine proof obligations. -/
def AngularEstimates : Prop :=
  ∀ (d : AngularData) (h : Hypotheses d),
    ∃ δ η L C a b : ℝ,
      0 ≤ C ∧ EvolutionOnBox d h δ η L a b ∧
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => endpointError d h q.1 q.2)
        (parameterBox δ η) ∧
      (∀ r μ, (r,μ) ∈ parameterBox δ η →
        endpoint d h r μ = Real.exp (d.T * d.A μ) * r +
          cubicCoefficient d μ * r ^ 3 + endpointError d h r μ ∧
        |endpointError d h r μ| ≤ C * |r| ^ 4 ∧
        |deriv (fun s => endpointError d h s μ) r| ≤ C * |r| ^ 3 ∧
        |deriv (fun ν => endpointError d h r ν) μ| ≤ C * |r| ^ 4)

end Specs.D13Unified.Ch16.HopfAngularScalarEstimates
