import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Algebra.Spectrum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions

/-! Independent statements for paper.tex, `fa2:p5:cordial`.
The scalar field is real or complex. The original singular kernel and its
nonzero endpoint prescription are both retained. The angular integral below
is a canonical construction; agreement with the singular kernel is a separate
obligation, not a hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ExpandedFA.PartV.CordialSpec

abbrev Interval (T : ℝ) := Set.Icc (0 : ℝ) T
abbrev Space (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) := C(Interval T, 𝕂)

variable {𝕂 : Type*} [RCLike 𝕂] {T : ℝ}

def sample (hT : 0 < T) (f : Space 𝕂 T) (t : Interval T) (θ : ℝ) : 𝕂 :=
  f (Set.projIcc 0 T hT.le (t.1 * Real.sin θ))

lemma continuous_sample (hT : 0 < T) (f : Space 𝕂 T) :
    Continuous (Function.uncurry (sample hT f)) := by
  exact f.continuous.comp (continuous_projIcc.comp
    ((continuous_subtype_val.comp continuous_fst).mul
      (Real.continuous_sin.comp continuous_snd)))

lemma sample_integrable (hT : 0 < T) (f : Space 𝕂 T) (t : Interval T) :
    IntervalIntegrable (sample hT f t) volume 0 (Real.pi / 2) :=
  ((continuous_sample hT f).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

/-- Canonical angular construction, before packaging its boundedness. -/
def angularMap (hT : 0 < T) (f : Space 𝕂 T) : Space 𝕂 T :=
  ⟨fun t => ∫ θ in 0..Real.pi / 2, sample hT f t θ,
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_sample hT f) _ _⟩

lemma angularMap_bound (hT : 0 < T) (f : Space 𝕂 T) :
    ‖angularMap hT f‖ ≤ (Real.pi / 2) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (by positivity) (norm_nonneg _))).mpr
  intro t
  change ‖∫ θ in 0..Real.pi / 2, sample hT f t θ‖ ≤ _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := sample hT f t)
    (fun θ _ => f.norm_coe_le_norm _)
  simpa only [sub_zero, abs_of_nonneg (le_of_lt (by positivity : 0 < Real.pi / 2)),
    mul_comm] using h

/-- The bounded angular operator. Its defining proof obligations are proved,
without assuming any spectral or singular-integral claim. -/
def operatorValue (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (hT : 0 < T) :
    Space 𝕂 T →L[𝕂] Space 𝕂 T :=
  LinearMap.mkContinuous
    { toFun := angularMap hT
      map_add' := by
        intro f g
        ext t
        exact intervalIntegral.integral_add (sample_integrable hT f t)
          (sample_integrable hT g t)
      map_smul' := by
        intro a f
        ext t
        exact intervalIntegral.integral_smul a (sample hT f t) }
    (Real.pi / 2) (angularMap_bound hT)

def OperatorType := ∀ (𝕂 : Type*) [RCLike 𝕂] (T : ℝ), 0 < T →
  Space 𝕂 T →L[𝕂] Space 𝕂 T

def eigenvalueValue (r : ℝ) : ℝ := ∫ θ in 0..Real.pi / 2, (Real.sin θ) ^ r
abbrev EigenvalueType := ℝ → ℝ

/-- The power function, including `t^0 = 1` at zero. -/
def power (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (r : ℝ) (hr : 0 ≤ r) : Space 𝕂 T :=
  ⟨fun t => ((t.1 ^ r : ℝ) : 𝕂), RCLike.continuous_ofReal.comp
    (continuous_subtype_val.rpow_const (fun _ => Or.inr hr))⟩

/-- Extension outside the interval only supplies a total integrand. On [0,t]
with t in [0,T] it is exactly f(s). -/
def singularValue (hT : 0 < T) (f : Space 𝕂 T) (t : ℝ) : 𝕂 :=
  ∫ s in 0..t, ((t ^ 2 - s ^ 2) ^ (-(1 / 2 : ℝ))) •
    f (Set.projIcc 0 T hT.le s)

def SingularIdentity : Prop :=
  ∀ (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (hT : 0 < T) (f : Space 𝕂 T)
    (t : Interval T), 0 < t.1 →
    IntervalIntegrable (fun s => ((t.1 ^ 2 - s ^ 2) ^ (-(1 / 2 : ℝ))) •
      f (Set.projIcc 0 T hT.le s)) volume 0 t.1 ∧
    operatorValue 𝕂 T hT f t = singularValue hT f t.1

def EndpointIdentity : Prop :=
  ∀ (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (hT : 0 < T) (f : Space 𝕂 T),
    operatorValue 𝕂 T hT f ⟨0, le_rfl, hT.le⟩ =
      (Real.pi / 2) • f ⟨0, le_rfl, hT.le⟩

def ExactNorm : Prop :=
  ∀ (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (hT : 0 < T),
    ‖operatorValue 𝕂 T hT‖ = Real.pi / 2

def PowerEigenfunctions : Prop :=
  ∀ (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (hT : 0 < T) (r : ℝ) (hr : 0 ≤ r),
    power 𝕂 T r hr ≠ 0 ∧
    operatorValue 𝕂 T hT (power 𝕂 T r hr) =
      (eigenvalueValue r : 𝕂) • power 𝕂 T r hr

/-- The real Euler beta integral. Keeping its integral definition makes the
normalization and the exponent at each endpoint explicit. -/
def beta (a b : ℝ) : ℝ := ∫ u in 0..1, u ^ (a - 1) * (1 - u) ^ (b - 1)

def BetaFormula : Prop :=
  ∀ r : ℝ, 0 ≤ r → eigenvalueValue r = (1 / 2 : ℝ) * beta ((r + 1) / 2) (1 / 2)

def EigenvalueProperties : Prop :=
  eigenvalueValue 0 = Real.pi / 2 ∧
  (∀ r : ℝ, 0 ≤ r → 0 < eigenvalueValue r) ∧
  ContinuousOn eigenvalueValue (Set.Ici 0) ∧
  StrictAntiOn eigenvalueValue (Set.Ici 0) ∧
  Filter.Tendsto eigenvalueValue Filter.atTop (nhds 0)

def Noncompact : Prop :=
  ∀ (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (hT : 0 < T),
    ¬ ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (operatorValue 𝕂 T hT).toLinearMap

/-- Quasinilpotence is vanishing spectral radius. -/
def NotQuasinilpotent : Prop :=
  ∀ (𝕂 : Type*) [RCLike 𝕂] (T : ℝ) (hT : 0 < T),
    spectralRadius 𝕂 (operatorValue 𝕂 T hT) ≠ 0

end ExpandedFA.PartV.CordialSpec
