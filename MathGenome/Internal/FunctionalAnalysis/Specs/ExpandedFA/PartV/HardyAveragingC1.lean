import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingContinuous
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The complex C¹ space is realized as pairs (f,v) of continuous functions
satisfying the fundamental theorem of calculus. Its norm is max(‖f‖∞,‖v‖∞),
the usual C¹ norm. The characterization target identifies v with the continuous
one-sided derivative at both endpoints, so no differentiability is assumed away.
This specification uses only libraries and upstream specifications. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set
open scoped unitInterval Topology
namespace ExpandedFA.PartV.HardyAveragingC1.Spec

abbrev CSpace := HardyAveragingContinuous.Spec.Space
open HardyAveragingContinuous.Spec (extension)

/-- Multiplication by the independent variable on [0,1]. -/
def position : CSpace := ⟨fun x => (x : ℂ), by fun_prop⟩

/-- The primitive of v, written as x Qv(x); the scalar integral identity is
an explicit proof target below. -/
def primitive : CSpace →L[ℂ] CSpace :=
  (ContinuousLinearMap.mul ℂ CSpace position).comp
    HardyAveragingContinuous.Spec.operatorValue

def constant : ℂ →L[ℂ] CSpace :=
  ({ toFun := ContinuousMap.const I
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : ℂ →ₗ[ℂ] CSpace).mkContinuous 1
    (by intro c; change ‖ContinuousMap.const I c‖ ≤ 1 * ‖c‖; simpa using (ContinuousMap.norm_le _ (norm_nonneg c)).mpr (by intro x; rfl))

def graphMap : (CSpace × CSpace) →L[ℂ] CSpace :=
  ContinuousLinearMap.fst ℂ CSpace CSpace -
    constant.comp ((ContinuousMap.evalCLM ℂ 0).comp (ContinuousLinearMap.fst ℂ CSpace CSpace)) -
    primitive.comp (ContinuousLinearMap.snd ℂ CSpace CSpace)

/-- C¹([0,1];ℂ) with its standard maximum norm, in FTC graph form. -/
abbrev c1Subspace : Submodule ℂ (CSpace × CSpace) := graphMap.ker
abbrev Space := ↥c1Subspace

def value (f : Space) : CSpace := f.val.1
def derivative (f : Space) : CSpace := f.val.2

def coordinates : Space →L[ℂ] (ℂ × CSpace) :=
  ((ContinuousMap.evalCLM ℂ 0).comp
    ((ContinuousLinearMap.fst ℂ CSpace CSpace).comp c1Subspace.subtypeL)).prod
    ((ContinuousLinearMap.snd ℂ CSpace CSpace).comp c1Subspace.subtypeL)

/-- r-weighted averaging, constructed from the actual Bochner integral. -/
def weightedDilation (v : CSpace) : C(I, CSpace) :=
  ⟨fun r => (r : ℂ) • HardyAveragingContinuous.Spec.dilation v r, by fun_prop⟩
def weightedAverage (v : CSpace) : CSpace := ∫ r : I, weightedDilation v r

private lemma weighted_integrable (v : CSpace) : Integrable (weightedDilation v) :=
  (weightedDilation v).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private lemma weighted_bound (v : CSpace) : ‖weightedAverage v‖ ≤ ‖v‖ := by
  have h : ∀ r : I, ‖weightedDilation v r‖ ≤ ‖v‖ := by
    intro r
    change ‖(r : ℂ) • HardyAveragingContinuous.Spec.dilation v r‖ ≤ ‖v‖
    rw [norm_smul]
    calc
      _ ≤ ‖(r : ℂ)‖ * ‖v‖ := mul_le_mul_of_nonneg_left
        ((ContinuousMap.norm_le _ (norm_nonneg v)).mpr
          (fun x => ContinuousMap.norm_coe_le_norm v (r * x))) (norm_nonneg _)
      _ ≤ ‖v‖ := by
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r.property.1,
          one_mul] using mul_le_mul_of_nonneg_right r.property.2 (norm_nonneg v)
  simpa [weightedAverage] using
    norm_integral_le_of_norm_le_const (μ := volume) (Filter.Eventually.of_forall h)

def weightedOperator : CSpace →L[ℂ] CSpace :=
  ({ toFun := weightedAverage
     map_add' := by
       intro v w
       have h : weightedDilation (v + w) = weightedDilation v + weightedDilation w := by
         ext r x; simp [weightedDilation, HardyAveragingContinuous.Spec.dilation, mul_add]
       simp only [weightedAverage, h, ContinuousMap.add_apply]
       exact integral_add (weighted_integrable v) (weighted_integrable w)
     map_smul' := by
       intro c v
       have h : weightedDilation (c • v) = c • weightedDilation v := by
         ext r x; simp [weightedDilation, HardyAveragingContinuous.Spec.dilation]; ring
       simp only [weightedAverage, h, ContinuousMap.smul_apply]
       exact integral_smul c _ } : CSpace →ₗ[ℂ] CSpace).mkContinuous 1
       (by intro v; simpa using weighted_bound v)

def blockOperator : (ℂ × CSpace) →L[ℂ] (ℂ × CSpace) :=
  (ContinuousLinearMap.id ℂ ℂ).prodMap weightedOperator

/-- The C¹ Hardy operator is specified by its actual continuous-function
average, not by an assumed spectral certificate. -/
def OperatorFormula (T : Space →L[ℂ] Space) : Prop :=
  ∀ f, value (T f) = HardyAveragingContinuous.Spec.operatorValue (value f)

def PrimitiveFormula : Prop :=
  ∀ (v : CSpace) (x : I), primitive v x = ∫ t in (0 : ℝ)..(x : ℝ), extension v t

def C1Characterization : Prop :=
  ∀ f v : CSpace, (f, v) ∈ c1Subspace ↔
    ∀ x : I, HasDerivWithinAt (extension f) (v x) (Icc (0 : ℝ) 1) (x : ℝ)

def C1Complete : Prop := CompleteSpace Space

def CoordinateIsomorphism : Prop :=
  ∃ e : Space ≃L[ℂ] (ℂ × CSpace), e.toContinuousLinearMap = coordinates

def CoordinateFormula (T : Space →L[ℂ] Space) : Prop :=
  ∀ f, coordinates (T f) = blockOperator (coordinates f)

/-- The source's substitution w(y)=v(√y), including both endpoints. -/
def SquareSubstitution : Prop :=
  ∃ S : CSpace ≃L[ℂ] CSpace,
    (∀ (v : CSpace) (y : I), S v y = v ⟨Real.sqrt y,
      Real.sqrt_nonneg _, Real.sqrt_le_one.mpr y.property.2⟩) ∧
    (∀ (v : CSpace) (x : I), S.symm v x = v (x * x)) ∧
    ∀ v, S (weightedOperator v) =
      (1 / 2 : ℂ) • HardyAveragingContinuous.Spec.operatorValue (S v)

instance : Ring (Space →L[ℂ] Space) := ContinuousLinearMap.ring (R := ℂ) (M := Space)
instance : Algebra ℂ (Space →L[ℂ] Space) := ContinuousLinearMap.algebra (R := ℂ) (S := ℂ) (M := Space)

def SpectrumDisk (T : Space →L[ℂ] Space) : Prop :=
  spectrum ℂ T = {z : ℂ | z = 1 ∨ ‖z - (1 / 4 : ℂ)‖ ≤ (1 / 4 : ℝ)}

def EigenvalueDisk (T : Space →L[ℂ] Space) : Prop :=
  {z : ℂ | ∃ f : Space, f ≠ 0 ∧ T f = z • f} =
    {z : ℂ | z = 1 ∨ z = 1 / 2 ∨ ‖z - (1 / 4 : ℂ)‖ < (1 / 4 : ℝ)}

def Noncompact (T : Space →L[ℂ] Space) : Prop := ¬ IsCompactOperator T

def NormFormula : Prop :=
  ∀ f : Space, ‖f‖ = max ‖value f‖ ‖derivative f‖

def FunctionFaithfulness : Prop := Function.Injective value

def RealSpectrumSection (T : Space →L[ℂ] Space) : Prop :=
  ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ T ↔ t = 1 ∨ t ∈ Icc (0 : ℝ) (1 / 2)

/-- The actual averaging operator exists on the full standard C¹ space.
All conclusions concern that same operator, and the function formula uniquely
determines it. No spectral or compactness hypothesis is assumed. -/
def HardyTheorem : Prop :=
  ∃ T : Space →L[ℂ] Space,
    OperatorFormula T ∧ CoordinateFormula T ∧ SpectrumDisk T ∧
    EigenvalueDisk T ∧ Noncompact T ∧ RealSpectrumSection T ∧
    ∀ U : Space →L[ℂ] Space, OperatorFormula U → U = T

/-! The real C¹ space is the fixed-real part of the same FTC graph. Its
pointwise function and derivative are real-valued, with the inherited C¹ norm.
`RealC1Model` below verifies that this realizes all ordinary real C¹ functions. -/
def realSubspace : Submodule ℝ Space where
  carrier := {f | ∀ x : I, (value f x).im = 0 ∧ (derivative f x).im = 0}
  zero_mem' := by intro x; constructor <;> rfl
  add_mem' := by
    intro f g hf hg x
    constructor
    · change (value f x + value g x).im = 0
      simp [hf x, hg x]
    · change (derivative f x + derivative g x).im = 0
      simp [hf x, hg x]
  smul_mem' := by
    intro c f hf x
    constructor
    · change (c • value f x).im = 0
      simp [hf x]
    · change (c • derivative f x).im = 0
      simp [hf x]

abbrev RealSpace := ↥realSubspace
instance : NormedAddCommGroup RealSpace := by
  unfold RealSpace
  exact Submodule.normedAddCommGroup (𝕜 := ℝ) (E := Space) realSubspace
instance : NormedSpace ℝ RealSpace := by
  unfold RealSpace
  exact Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := Space) realSubspace
instance : Ring (RealSpace →L[ℝ] RealSpace) :=
  ContinuousLinearMap.ring (R := ℝ) (M := RealSpace)
instance : Algebra ℝ (RealSpace →L[ℝ] RealSpace) :=
  ContinuousLinearMap.algebra (R := ℝ) (S := ℝ) (M := RealSpace)
abbrev RealCSpace := HardyAveragingContinuous.Spec.RealSpace

def realValue (f : RealSpace) : RealCSpace :=
  ⟨fun x => (value f.val x).re, Complex.continuous_re.comp (value f.val).continuous⟩

def realDerivative (f : RealSpace) : RealCSpace :=
  ⟨fun x => (derivative f.val x).re,
    Complex.continuous_re.comp (derivative f.val).continuous⟩

/-- Both directions of the actual real C¹ realization, including endpoint
one-sided derivatives, the full C¹ norm, faithfulness and completeness. -/
def RealC1Model : Prop :=
  (∀ f v : RealCSpace,
    (∀ x : I, HasDerivWithinAt (ContinuousMap.IccExtendCM f) (v x)
      (Icc (0 : ℝ) 1) (x : ℝ)) ↔
    ∃ F : RealSpace, realValue F = f ∧ realDerivative F = v) ∧
  (∀ F : RealSpace, ‖F‖ = max ‖realValue F‖ ‖realDerivative F‖) ∧
  Function.Injective realValue ∧ CompleteSpace RealSpace

def RealOperatorFormula (Q : RealSpace →L[ℝ] RealSpace) : Prop :=
  (∀ f : RealSpace, realValue (Q f) 0 = realValue f 0) ∧
  ∀ (f : RealSpace) (x : I), 0 < (x : ℝ) →
    realValue (Q f) x = (x : ℝ)⁻¹ *
      ∫ t in (0 : ℝ)..(x : ℝ), ContinuousMap.IccExtendCM (realValue f) t

/-- Intrinsic real spectrum and eigenvalues of the original real C¹
averaging operator. No spectral certificate is a hypothesis. -/
def RealHardyTheorem : Prop :=
  ∃ Q : RealSpace →L[ℝ] RealSpace,
    RealOperatorFormula Q ∧
    spectrum ℝ Q = {z : ℝ | z = 1 ∨ z ∈ Icc (0 : ℝ) (1 / 2)} ∧
    {z : ℝ | ∃ f : RealSpace, f ≠ 0 ∧ Q f = z • f} =
      {z : ℝ | z = 1 ∨ z ∈ Ioc (0 : ℝ) (1 / 2)} ∧
    Function.Injective Q ∧ ¬ IsCompactOperator Q ∧
    ∀ U : RealSpace →L[ℝ] RealSpace, RealOperatorFormula U → U = Q


end ExpandedFA.PartV.HardyAveragingC1.Spec
