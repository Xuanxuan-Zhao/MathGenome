import MathGenome.Internal.Specs.D05.M03.RankNullity
import MathGenome.Internal.Specs.D05.M02.SubspaceDimension
import MathGenome.Internal.Specs.D05.M08.Evaluation

/-!
Independent statements for K05.10.kernel_stabilization, paper.tex:1419–1425.
Powers use the canonical endomorphism multiplication (composition), and images
are `LinearMap.range`. No splitting or characteristic hypothesis is imposed.
The inclusions and persistence hold even without finite dimension. The dimension
parameter in the stabilization statements may be zero.
-/

namespace Specs.D05.M10.KernelStabilization

def initial_terms : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V),
    LinearMap.ker (T ^ 0) = ⊥ ∧ LinearMap.range (T ^ 0) = ⊤

def kernel_inclusion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (k : ℕ),
    LinearMap.ker (T ^ k) ≤ LinearMap.ker (T ^ (k + 1))

def image_inclusion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (k : ℕ),
    LinearMap.range (T ^ (k + 1)) ≤ LinearMap.range (T ^ k)

def kernel_eq_of_consecutive : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (k : ℕ),
    LinearMap.ker (T ^ k) = LinearMap.ker (T ^ (k + 1)) →
      ∀ j : ℕ, LinearMap.ker (T ^ k) = LinearMap.ker (T ^ (k + j))

def kernel_stabilization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (n : ℕ),
    Module.finrank K V = n →
      ∀ j : ℕ, LinearMap.ker (T ^ n) = LinearMap.ker (T ^ (n + j))

def image_stabilization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (n : ℕ),
    Module.finrank K V = n →
      ∀ j : ℕ, LinearMap.range (T ^ n) = LinearMap.range (T ^ (n + j))

end Specs.D05.M10.KernelStabilization
