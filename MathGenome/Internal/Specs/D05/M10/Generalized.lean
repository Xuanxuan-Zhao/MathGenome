import MathGenome.Internal.Specs.D05.M09.Eigenspace
import MathGenome.Internal.Specs.D05.M10.KernelStabilization
import MathGenome.Internal.Specs.D05.M10.Nilpotent
import MathGenome.Internal.Specs.D05.M06.Invariant

/-!
Independent statements for K05.10.generalized, paper.tex:1440–1443.
The field is unchanged, no splitting assumption is made, and the ambient
finite dimension may be zero. The canonical natural-exponent generalized
eigenspace is related explicitly to the paper's kernel at the ambient dimension.
-/

noncomputable section

namespace Specs.D05.M10.Generalized

universe u v

def generalizedEigenspace_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → Module.End K V → K → Submodule K V

def generalizedEigenspace_value : generalizedEigenspace_type.{u, v} :=
  fun K V _ _ _ _ T μ => T.genEigenspace μ (Module.finrank K V)

def isGeneralizedEigenvector_type :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Module.End K V → K → V → Prop

/-- The nonzero and positive-exponent requirements are part of the predicate. -/
def isGeneralizedEigenvector_value : isGeneralizedEigenvector_type.{u, v} :=
  fun K V _ _ _ T μ x =>
    x ≠ 0 ∧ ∃ r : ℕ, 0 < r ∧ ((T - μ • (1 : Module.End K V)) ^ r) x = 0

def eq_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K) (n : ℕ),
    Module.finrank K V = n →
      generalizedEigenspace_value K V T μ = LinearMap.ker ((T - μ • 1) ^ n)

def mem_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K) (x : V),
    x ∈ generalizedEigenspace_value K V T μ ↔
      ((T - μ • 1) ^ Module.finrank K V) x = 0

def stabilization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K) (n m : ℕ),
    Module.finrank K V = n → n ≤ m →
      LinearMap.ker ((T - μ • 1) ^ m) = generalizedEigenspace_value K V T μ

/-- Equality with the actual set union, including the zeroth power kernel. -/
def eq_union : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    (generalizedEigenspace_value K V T μ : Set V) =
      ⋃ r : ℕ, (LinearMap.ker ((T - μ • 1) ^ r) : Set V)

def eigenvector_iff_mem : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K) (x : V),
    isGeneralizedEigenvector_value K V T μ x ↔
      x ≠ 0 ∧ x ∈ generalizedEigenspace_value K V T μ

def commutes_shift : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (μ : K), Commute T (T - μ • 1)

def invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    Specs.D05.M06.Invariant.invariant_value K V
      (generalizedEigenspace_value K V T μ) T

def shift_invariant : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    Specs.D05.M06.Invariant.invariant_value K V
      (generalizedEigenspace_value K V T μ) (T - μ • 1)

/-- Restrictions use the original endomorphism formulas on the subspace subtype.
The two invariance proofs are data for `restrict`, and are established separately. -/
def restriction_decomposition : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K)
    (hT : Specs.D05.M06.Invariant.invariant_value K V
      (generalizedEigenspace_value K V T μ) T)
    (hN : Specs.D05.M06.Invariant.invariant_value K V
      (generalizedEigenspace_value K V T μ) (T - μ • 1)),
    T.restrict hT = μ • LinearMap.id + (T - μ • 1).restrict hN

def restriction_pow_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K)
    (hN : Specs.D05.M06.Invariant.invariant_value K V
      (generalizedEigenspace_value K V T μ) (T - μ • 1)),
    ((T - μ • 1).restrict hN) ^ Module.finrank K V = 0

def restriction_nilpotent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K)
    (hN : Specs.D05.M06.Invariant.invariant_value K V
      (generalizedEigenspace_value K V T μ) (T - μ • 1)),
    IsNilpotent ((T - μ • 1).restrict hN)

/-- The restriction conclusions assembled without any invariance premise.
Nilpotence here is witnessed by a positive exponent, even in dimension zero. -/
def restriction_structure : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (μ : K),
    ∃ (hT : Specs.D05.M06.Invariant.invariant_value K V
        (generalizedEigenspace_value K V T μ) T)
      (hN : Specs.D05.M06.Invariant.invariant_value K V
        (generalizedEigenspace_value K V T μ) (T - μ • 1)),
      T.restrict hT = μ • LinearMap.id + (T - μ • 1).restrict hN ∧
        ∃ r : ℕ, 0 < r ∧ ((T - μ • 1).restrict hN) ^ r = 0

end Specs.D05.M10.Generalized
