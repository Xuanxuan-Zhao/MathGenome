import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.OperatorDomains

/-! C₀ semigroups and exact-domain generators for Part III.
The independent Specs contain the canonical semigroup structure. Here the
public definitions and laws expose the right norm derivative and its exact
domain, together with common exponential, growth, and spectral bounds. -/

noncomputable section
open Filter Topology
open scoped NNReal

namespace ExpandedFA.Semigroups
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

def mkC0Semigroup : C0SemigroupSpec.MakeType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.makeValue

def differenceQuotient : C0SemigroupSpec.DifferenceQuotientType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.differenceQuotientValue

def HasGeneratorLimit : C0SemigroupSpec.HasGeneratorLimitType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.hasGeneratorLimitValue

def generatorDomain : C0SemigroupSpec.GeneratorDomainType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.generatorDomainValue

def generator : C0SemigroupSpec.GeneratorType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.generatorValue

def Generates : C0SemigroupSpec.GeneratesType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.generatesValue

def HasExponentialBound : C0SemigroupSpec.ExponentialBoundType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.exponentialBoundValue

def HasCommonExponentialBound {ι : Type*} :
    C0SemigroupSpec.CommonExponentialBoundType (𝕜 := 𝕜) (X := X) ι :=
  C0SemigroupSpec.commonExponentialBoundValue

def growthBound : C0SemigroupSpec.GrowthBoundType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.growthBoundValue

def spectrum : C0SemigroupSpec.SpectrumType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.spectrumValue

def spectralBound : C0SemigroupSpec.SpectralBoundType (𝕜 := 𝕜) (X := X) :=
  C0SemigroupSpec.spectralBoundValue

theorem semigroup_laws : C0SemigroupSpec.SemigroupLaws (𝕜 := 𝕜) (X := X) := by
  intro T
  exact ⟨T.at_zero, T.add_time, T.strong_zero⟩

theorem differenceQuotient_apply :
    C0SemigroupSpec.DifferenceQuotientLaw (𝕜 := 𝕜) (X := X) := by
  intro T h x
  rfl

theorem mem_generator_domain_iff :
    C0SemigroupSpec.GeneratorDomainLaw (𝕜 := 𝕜) (X := X) := by
  intro T x
  rfl

theorem generator_has_limit :
    C0SemigroupSpec.GeneratorLimitLaw (𝕜 := 𝕜) (X := X) := by
  intro T x
  exact x.2.choose_spec

theorem generator_limit_unique :
    C0SemigroupSpec.GeneratorLimitUniqueLaw (𝕜 := 𝕜) (X := X) := by
  intro T x y z hy hz
  exact tendsto_nhds_unique hy hz

theorem mem_generator_graph_iff :
    C0SemigroupSpec.GeneratorGraphLaw (𝕜 := 𝕜) (X := X) := by
  intro T x y
  constructor
  · intro h
    rcases (Unbounded.mem_graph_iff (C0SemigroupSpec.generatorValue T) (x, y)).mp h with ⟨hx, hxy⟩
    have heq : C0SemigroupSpec.generatorValue T ⟨x, hx⟩ = y := hxy
    exact heq ▸ generator_has_limit T ⟨x, hx⟩
  · intro h
    let hx : x ∈ (C0SemigroupSpec.generatorValue T).domain := ⟨y, h⟩
    apply (Unbounded.mem_graph_iff (C0SemigroupSpec.generatorValue T) (x, y)).mpr
    exact ⟨hx, tendsto_nhds_unique (generator_has_limit T ⟨x, hx⟩) h⟩

omit [CompleteSpace X] in
theorem mem_spectrum_iff : C0SemigroupSpec.SpectrumLaw (𝕜 := 𝕜) (X := X) := by
  intro A ζ
  rfl

end ExpandedFA.Semigroups
