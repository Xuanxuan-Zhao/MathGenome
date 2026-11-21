import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Symmetric operators, exact-domain self-adjointness and normality,
semiboundedness, deficiency subspaces, and Hilbert cardinal indices. -/
noncomputable section
universe u
namespace ExpandedFA.Unbounded
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A densely defined operator included in its Hilbert adjoint. -/
def IsSymmetric (S : Operator ℂ H H) : Prop :=
  SymmetryAndDeficienciesSpec.symmetricValue S

/-- Self-adjointness includes equality of domains. -/
def IsSelfAdjoint (S : Operator ℂ H H) : Prop :=
  SymmetryAndDeficienciesSpec.selfAdjointValue S

/-- The operator is closable and its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint (S : Operator ℂ H H) : Prop :=
  SymmetryAndDeficienciesSpec.essentiallySelfAdjointValue S

/-- Normality includes equality of the domains of N*N and NN*. -/
def IsNormal (N : Operator ℂ H H) : Prop :=
  SymmetryAndDeficienciesSpec.normalValue N

def IsBoundedBelow (S : Operator ℂ H H) (c : ℝ) : Prop :=
  SymmetryAndDeficienciesSpec.boundedBelowValue S c

def IsBoundedAbove (S : Operator ℂ H H) (c : ℝ) : Prop :=
  SymmetryAndDeficienciesSpec.boundedAboveValue S c

def IsSemibounded (S : Operator ℂ H H) : Prop :=
  SymmetryAndDeficienciesSpec.semiboundedValue S

/-- The z-eigenspace of S*, equivalently ker(S* − z). -/
def deficiencySpace (S : Operator ℂ H H) (z : ℂ) : Submodule ℂ H :=
  SymmetryAndDeficienciesSpec.deficiencySpaceValue S z

def deficiencyPlus (S : Operator ℂ H H) : Submodule ℂ H :=
  SymmetryAndDeficienciesSpec.deficiencyPlusValue S

def deficiencyMinus (S : Operator ℂ H H) : Submodule ℂ H :=
  SymmetryAndDeficienciesSpec.deficiencyMinusValue S

/-- Cardinality of a Hilbert basis, including infinite cardinalities. -/
def hilbertDimension (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : Cardinal.{u} :=
  SymmetryAndDeficienciesSpec.hilbertDimensionValue E

/-- The Hilbert cardinal dimension of ker(S* − z). -/
def deficiencyIndex (S : Operator ℂ H H) (hS : DenselyDefined S) (z : ℂ) : Cardinal.{u} :=
  SymmetryAndDeficienciesSpec.deficiencyIndexValue S hS z

def deficiencyIndexPlus (S : Operator ℂ H H) (hS : DenselyDefined S) : Cardinal.{u} :=
  SymmetryAndDeficienciesSpec.deficiencyIndexPlusValue S hS

def deficiencyIndexMinus (S : Operator ℂ H H) (hS : DenselyDefined S) : Cardinal.{u} :=
  SymmetryAndDeficienciesSpec.deficiencyIndexMinusValue S hS

theorem isSymmetric_iff (S : Operator ℂ H H) :
    IsSymmetric S ↔ DenselyDefined S ∧ IsIncluded S (hilbertAdjoint S) := Iff.rfl

theorem isSelfAdjoint_iff (S : Operator ℂ H H) :
    IsSelfAdjoint S ↔ DenselyDefined S ∧ SameOperator S (hilbertAdjoint S) := Iff.rfl

theorem isEssentiallySelfAdjoint_iff (S : Operator ℂ H H) :
    IsEssentiallySelfAdjoint S ↔ DenselyDefined S ∧
      ∃ h : IsClosable S, IsSelfAdjoint (closure S h) := by
  constructor
  · rintro ⟨hd, hc, he⟩
    exact ⟨hd, hc, he⟩
  · rintro ⟨hd, hc, he⟩
    exact ⟨hd, hc, he⟩

theorem isNormal_iff (N : Operator ℂ H H) :
    IsNormal N ↔ DenselyDefined N ∧
      SameOperator (product (hilbertAdjoint N) N) (product N (hilbertAdjoint N)) := Iff.rfl

theorem isBoundedBelow_iff (S : Operator ℂ H H) (c : ℝ) :
    IsBoundedBelow S c ↔ IsSymmetric S ∧
      ∀ x : S.domain, c * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (x : H) (S x)).re := Iff.rfl

theorem isBoundedAbove_iff (S : Operator ℂ H H) (c : ℝ) :
    IsBoundedAbove S c ↔ IsSymmetric S ∧
      ∀ x : S.domain, (inner ℂ (x : H) (S x)).re ≤ c * ‖(x : H)‖ ^ 2 := Iff.rfl

theorem isSemibounded_iff (S : Operator ℂ H H) :
    IsSemibounded S ↔ (∃ c : ℝ, IsBoundedBelow S c) ∨
      (∃ c : ℝ, IsBoundedAbove S c) := Iff.rfl

theorem IsSymmetric.inner_map {S : Operator ℂ H H} (hS : IsSymmetric S)
    (x y : S.domain) : inner ℂ (S x) (y : H) = inner ℂ (x : H) (S y) := by
  change Dense (S.domain : Set H) ∧ S ≤ hilbertAdjoint S at hS
  have hy : S y = hilbertAdjoint S ⟨y, hS.2.1 y.2⟩ := hS.2.2 rfl
  rw [hy]
  exact hilbertAdjoint_inner S hS.1 ⟨y, hS.2.1 y.2⟩ x

theorem IsSymmetric.isClosable {S : Operator ℂ H H} (hS : IsSymmetric S) :
    IsClosable S := by
  change Dense (S.domain : Set H) ∧ S ≤ hilbertAdjoint S at hS
  exact (hilbertAdjoint_isClosed S hS.1).isClosable.leIsClosable hS.2

theorem IsSymmetric.inner_self_im {S : Operator ℂ H H} (hS : IsSymmetric S)
    (x : S.domain) : (inner ℂ (S x) (x : H)).im = 0 := by
  have heq := congrArg Complex.im (hS.inner_map x x)
  rw [← inner_conj_symm (x : H) (S x), Complex.conj_im] at heq
  linarith

theorem mem_deficiencySpace_iff (S : Operator ℂ H H) (z : ℂ) (y : H) :
    y ∈ deficiencySpace S z ↔ ∃ hy : y ∈ (hilbertAdjoint S).domain,
      hilbertAdjoint S ⟨y, hy⟩ = z • y := by
  change y ∈ (OperatorDomainsSpec.shiftValue z (hilbertAdjoint S)).ker ↔ _
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    change z • (w : H) - hilbertAdjoint S w = 0 at hw
    exact ⟨w.2, (sub_eq_zero.mp hw).symm⟩
  · rintro ⟨hy, he⟩
    refine ⟨⟨y, hy⟩, rfl, ?_⟩
    change z • y - hilbertAdjoint S ⟨y, hy⟩ = 0
    exact sub_eq_zero.mpr he.symm

theorem mem_deficiencyPlus_iff (S : Operator ℂ H H) (y : H) :
    y ∈ deficiencyPlus S ↔ ∃ hy : y ∈ (hilbertAdjoint S).domain,
      hilbertAdjoint S ⟨y, hy⟩ = Complex.I • y :=
  mem_deficiencySpace_iff S Complex.I y

theorem mem_deficiencyMinus_iff (S : Operator ℂ H H) (y : H) :
    y ∈ deficiencyMinus S ↔ ∃ hy : y ∈ (hilbertAdjoint S).domain,
      hilbertAdjoint S ⟨y, hy⟩ = (-Complex.I) • y :=
  mem_deficiencySpace_iff S (-Complex.I) y

theorem deficiencySpace_isClosed (S : Operator ℂ H H) (hS : DenselyDefined S) (z : ℂ) :
    _root_.IsClosed (deficiencySpace S z : Set H) :=
  SymmetryAndDeficienciesSpec.deficiencySpace_closed S hS z

/-- This witness states explicitly that the dimension is that of a Hilbert basis. -/
theorem hilbertDimension_hasBasis (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :
    ∃ (w : Set E) (_b : HilbertBasis w ℂ E), hilbertDimension E = Cardinal.mk w := by
  refine ⟨(exists_hilbertBasis ℂ E).choose,
    (exists_hilbertBasis ℂ E).choose_spec.choose, rfl⟩

theorem deficiencyIndex_hasBasis (S : Operator ℂ H H) (hS : DenselyDefined S) (z : ℂ) :
    ∃ (w : Set (deficiencySpace S z)) (_b : HilbertBasis w ℂ (deficiencySpace S z)),
      deficiencyIndex S hS z = Cardinal.mk w := by
  let : CompleteSpace (deficiencySpace S z) :=
    (deficiencySpace_isClosed S hS z).isComplete.completeSpace_coe
  exact hilbertDimension_hasBasis (deficiencySpace S z)

/-- The identity holds for every symmetric operator, without closedness. -/
theorem IsSymmetric.norm_sub_sq {S : Operator ℂ H H} (hS : IsSymmetric S)
    (z : ℂ) (x : S.domain) :
    ‖S x - z • (x : H)‖ ^ 2 =
      ‖S x - (z.re : ℂ) • (x : H)‖ ^ 2 + |z.im| ^ 2 * ‖(x : H)‖ ^ 2 := by
  rw [_root_.norm_sub_sq (𝕜 := ℂ), _root_.norm_sub_sq (𝕜 := ℂ)]
  change ‖S x‖ ^ 2 - 2 * (inner ℂ (S x) (z • (x : H))).re +
      ‖z • (x : H)‖ ^ 2 =
    (‖S x‖ ^ 2 - 2 * (inner ℂ (S x) ((z.re : ℂ) • (x : H))).re +
      ‖(z.re : ℂ) • (x : H)‖ ^ 2) + |z.im| ^ 2 * ‖(x : H)‖ ^ 2
  simp only [inner_smul_right, Complex.mul_re, hS.inner_self_im,
    mul_zero, sub_zero, Complex.ofReal_re, norm_smul, mul_pow,
    Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_im, sq_abs]
  ring

/-- The precise closed-symmetric statement in the manuscript. -/
theorem closed_symmetric_norm_sub_sq (S : Operator ℂ H H) (_hc : IsClosed S)
    (hS : IsSymmetric S) (z : ℂ) (x : S.domain) :
    ‖S x - z • (x : H)‖ ^ 2 =
      ‖S x - (z.re : ℂ) • (x : H)‖ ^ 2 + |z.im| ^ 2 * ‖(x : H)‖ ^ 2 :=
  hS.norm_sub_sq z x

end ExpandedFA.Unbounded
