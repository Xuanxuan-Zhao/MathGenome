import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Basic.NNReal.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Data.EReal.Basic

/-! Shared definitions for paper.tex 14435–14441, 14443–14446 and
14627–14637. Time is nonnegative real time. Continuity in the definition
is strong continuity at zero only. In particular no generator, density,
closedness, or growth estimate is included as assumed data.

The generator is a partial linear map on exactly the vectors with a right
norm difference-quotient limit. Bounds take values in the extended reals:
the infimum defining the growth bound and the supremum defining the spectral
bound can be −∞. The spectral bound uses the spectrum over the given scalar
field; its complex specialization is the spectral bound used in the paper's
spectral statements. No complexification of real operators is implicit. -/

noncomputable section
open Filter Topology
open scoped NNReal

namespace ExpandedFA.Semigroups

/-- A semigroup of bounded scalar-linear maps with strong continuity at zero,
on an arbitrary real or complex Banach space. -/
structure C0Semigroup (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] where
  operators : ℝ≥0 → X →L[𝕜] X
  at_zero : operators 0 = ContinuousLinearMap.id 𝕜 X
  add_time : ∀ t s, operators (t + s) = (operators t).comp (operators s)
  strong_zero : ∀ x, Tendsto (fun h : ℝ => operators h.toNNReal x) (𝓝[>] 0) (𝓝 x)

namespace C0SemigroupSpec
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

def MakeType := (T : ℝ≥0 → X →L[𝕜] X) →
  (T 0 = ContinuousLinearMap.id 𝕜 X) →
  (∀ t s, T (t + s) = (T t).comp (T s)) →
  (∀ x, Tendsto (fun h : ℝ => T h.toNNReal x) (𝓝[>] 0) (𝓝 x)) → C0Semigroup 𝕜 X

def makeValue : MakeType (𝕜 := 𝕜) (X := X) := fun T h0 hadd hlim =>
  ⟨T, h0, hadd, hlim⟩

/-- A real parameter is used for the right-hand filter. Only positive values
are tested, so `toNNReal` does not alter the time in the quotient. -/
def DifferenceQuotientType := C0Semigroup 𝕜 X → ℝ → X →L[𝕜] X
def differenceQuotientValue : DifferenceQuotientType (𝕜 := 𝕜) (X := X) :=
  fun T h => (algebraMap ℝ 𝕜 h)⁻¹ • (T.operators h.toNNReal - ContinuousLinearMap.id 𝕜 X)

def HasGeneratorLimitType := C0Semigroup 𝕜 X → X → X → Prop
def hasGeneratorLimitValue : HasGeneratorLimitType (𝕜 := 𝕜) (X := X) :=
  fun T x y => Tendsto (fun h => differenceQuotientValue T h x) (𝓝[>] (0 : ℝ)) (𝓝 y)

/-- Existence of a norm limit, with no a priori restriction on the domain. -/
def GeneratorDomainType := C0Semigroup 𝕜 X → Submodule 𝕜 X
def generatorDomainValue : GeneratorDomainType (𝕜 := 𝕜) (X := X) := fun T =>
  { carrier := {x | ∃ y, hasGeneratorLimitValue T x y}
    zero_mem' := ⟨0, by
      simpa only [hasGeneratorLimitValue, map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : X)) (𝓝[>] 0) (𝓝 0))⟩
    add_mem' := by
      rintro x z ⟨y, hy⟩ ⟨w, hw⟩
      refine ⟨y + w, ?_⟩
      simpa only [hasGeneratorLimitValue, map_add] using hy.add hw
    smul_mem' := by
      rintro c x ⟨y, hy⟩
      refine ⟨c • y, ?_⟩
      simpa only [hasGeneratorLimitValue, map_smul] using hy.const_smul c }

def GeneratorType := C0Semigroup 𝕜 X → Unbounded.Operator 𝕜 X X
def generatorValue : GeneratorType (𝕜 := 𝕜) (X := X) := fun T =>
  { domain := generatorDomainValue T
    toFun :=
      { toFun := fun x => x.2.choose
        map_add' := by
          intro x z
          apply tendsto_nhds_unique ((x + z).2.choose_spec)
          simpa only [hasGeneratorLimitValue, Submodule.coe_add, map_add] using
            x.2.choose_spec.add z.2.choose_spec
        map_smul' := by
          intro c x
          apply tendsto_nhds_unique ((c • x).2.choose_spec)
          simpa only [hasGeneratorLimitValue, Submodule.coe_smul, map_smul, RingHom.id_apply] using
            x.2.choose_spec.const_smul c } }

/-- Equality of generators includes equality of the full derivative domain. -/
def GeneratesType := Unbounded.Operator 𝕜 X X → C0Semigroup 𝕜 X → Prop
def generatesValue : GeneratesType (𝕜 := 𝕜) (X := X) := fun A T => A = generatorValue T

/-- The same constants M ≥ 1 and ω control every nonnegative time. -/
def ExponentialBoundType := C0Semigroup 𝕜 X → ℝ → ℝ → Prop
def exponentialBoundValue : ExponentialBoundType (𝕜 := 𝕜) (X := X) :=
  fun T M ω => 1 ≤ M ∧ ∀ t : ℝ≥0, ‖T.operators t‖ ≤ M * Real.exp (ω * (t : ℝ))

/-- A common bound for a family, with M and ω independent of the index. -/
def CommonExponentialBoundType (ι : Type*) := (ι → C0Semigroup 𝕜 X) → ℝ → ℝ → Prop
def commonExponentialBoundValue {ι : Type*} :
    CommonExponentialBoundType (𝕜 := 𝕜) (X := X) ι :=
  fun T M ω => 1 ≤ M ∧ ∀ i (t : ℝ≥0), ‖(T i).operators t‖ ≤ M * Real.exp (ω * (t : ℝ))

def GrowthBoundType := C0Semigroup 𝕜 X → EReal
def growthBoundValue : GrowthBoundType (𝕜 := 𝕜) (X := X) :=
  fun T => sInf {a : EReal | ∃ ω : ℝ, (ω : EReal) = a ∧ ∃ M, exponentialBoundValue T M ω}

/-- Scalar spectrum is the complement of the canonical bounded two-sided
resolvent set, retaining the exact domain of the unbounded operator. -/
def SpectrumType := Unbounded.Operator 𝕜 X X → Set 𝕜
def spectrumValue : SpectrumType (𝕜 := 𝕜) (X := X) :=
  fun A => {ζ | ¬ Nonempty (Unbounded.ResolventInverse A ζ)}

def SpectralBoundType := Unbounded.Operator 𝕜 X X → EReal
def spectralBoundValue : SpectralBoundType (𝕜 := 𝕜) (X := X) :=
  fun A => sSup {a : EReal | ∃ ζ ∈ spectrumValue A, (RCLike.re ζ : EReal) = a}

/-- All defining semigroup axioms, without any additional regularity assumption. -/
def SemigroupLaws : Prop := ∀ T : C0Semigroup 𝕜 X,
  T.operators 0 = ContinuousLinearMap.id 𝕜 X ∧
  (∀ t s, T.operators (t + s) = (T.operators t).comp (T.operators s)) ∧
  ∀ x, Tendsto (fun h : ℝ => T.operators h.toNNReal x) (𝓝[>] 0) (𝓝 x)

def DifferenceQuotientLaw : Prop := ∀ (T : C0Semigroup 𝕜 X) (h : ℝ) (x : X),
  differenceQuotientValue T h x = (algebraMap ℝ 𝕜 h)⁻¹ • (T.operators h.toNNReal x - x)

def GeneratorDomainLaw : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : X),
  x ∈ (generatorValue T).domain ↔ ∃ y, hasGeneratorLimitValue T x y

def GeneratorLimitLaw : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : (generatorValue T).domain),
  hasGeneratorLimitValue T x (generatorValue T x)

def GeneratorLimitUniqueLaw : Prop := ∀ (T : C0Semigroup 𝕜 X) (x y z : X),
  hasGeneratorLimitValue T x y → hasGeneratorLimitValue T x z → y = z

/-- Graph equality characterizes the generator, including its exact domain. -/
def GeneratorGraphLaw : Prop := ∀ (T : C0Semigroup 𝕜 X) (x y : X),
  (x, y) ∈ (generatorValue T).graph ↔ hasGeneratorLimitValue T x y

/-- Resolvent convention is precisely the one supplied by the upstream Specs. -/
def SpectrumLaw : Prop := ∀ (A : Unbounded.Operator 𝕜 X X) (ζ : 𝕜),
  ζ ∈ spectrumValue A ↔ ζ ∉ Unbounded.OperatorDomainsSpec.resolventSetValue A

/-! Fully quantified independent expected types. -/
set_option linter.checkUnivs false

def MakeTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    MakeType (𝕜 := 𝕜) (X := X)

def DifferenceQuotientTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    DifferenceQuotientType (𝕜 := 𝕜) (X := X)

def HasGeneratorLimitTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    HasGeneratorLimitType (𝕜 := 𝕜) (X := X)

def GeneratorDomainTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorDomainType (𝕜 := 𝕜) (X := X)

def GeneratorTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorType (𝕜 := 𝕜) (X := X)

def GeneratesTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratesType (𝕜 := 𝕜) (X := X)

def ExponentialBoundTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    ExponentialBoundType (𝕜 := 𝕜) (X := X)

def GrowthBoundTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GrowthBoundType (𝕜 := 𝕜) (X := X)

def SpectrumTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    SpectrumType (𝕜 := 𝕜) (X := X)

def SpectralBoundTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    SpectralBoundType (𝕜 := 𝕜) (X := X)

def CommonExponentialBoundTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] {ι : Type*},
    CommonExponentialBoundType (𝕜 := 𝕜) (X := X) ι

def SemigroupLawsExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    SemigroupLaws (𝕜 := 𝕜) (X := X)

def DifferenceQuotientLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    DifferenceQuotientLaw (𝕜 := 𝕜) (X := X)

def GeneratorDomainLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorDomainLaw (𝕜 := 𝕜) (X := X)

def GeneratorLimitLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorLimitLaw (𝕜 := 𝕜) (X := X)

def GeneratorLimitUniqueLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorLimitUniqueLaw (𝕜 := 𝕜) (X := X)

def GeneratorGraphLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorGraphLaw (𝕜 := 𝕜) (X := X)

def SpectrumLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    SpectrumLaw (𝕜 := 𝕜) (X := X)

end C0SemigroupSpec
end ExpandedFA.Semigroups
