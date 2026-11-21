import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Properness and cutoff interfaces for paper.tex:17326–17368.
These are independent of the candidate implementation. A compact inverse-image
condition is used for the restriction of addition to the actual supports; its
bridge to `IsProperMap` is an explicit obligation. No nonzero or positive-
dimension convention is imposed. -/
noncomputable section
open Set TopologicalSpace
open scoped Distributions Topology ContDiff Pointwise

namespace ExpandedFA.Distributions

/-- The portion of S × T seen by a compactly supported outer test. -/
def additionSlice {d : ℕ} (S T K : Set (Domain d)) : Set (Domain d × Domain d) :=
  (S ×ˢ T) ∩ (fun p => p.1 + p.2) ⁻¹' K

/-- Addition is proper on S × T. The equivalence with the usual topological
notion, without additional assumptions on S and T, is proved separately. -/
def AdditionProper {d : ℕ} (S T : Set (Domain d)) : Prop :=
  ∀ K : Set (Domain d), IsCompact K → IsCompact (additionSlice S T K)

/-- The domain of the partial convolution operation. -/
def Convolvable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) : Prop :=
  AdditionProper (distributionSupport u) (distributionSupport v)

/-- The corresponding condition for the simultaneous sum of three supports. -/
def TripleAdditionProper {d : ℕ} (S T U : Set (Domain d)) : Prop :=
  ∀ K : Set (Domain d), IsCompact K →
    IsCompact (((S ×ˢ T) ×ˢ U) ∩ (fun p => (p.1.1 + p.1.2) + p.2) ⁻¹' K)

/-- Scalar tests on the Cartesian product, with its ordinary Euclidean topology. -/
abbrev ProductTests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  TestFunction (⊤ : Opens (Domain d × Domain d)) 𝕜 ⊤

/-- A cutoff must equal one on a neighborhood, rather than just pointwise on
the part of the product support seen by the outer test. -/
def AdmissibleConvolutionCutoff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d) : Prop :=
  ∃ V : Set (Domain d × Domain d), IsOpen V ∧
    additionSlice (distributionSupport u) (distributionSupport v) (tsupport ψ) ⊆ V ∧
    EqOn χ 1 V

/-- The actual compactly supported function used by the cutoff construction. -/
def cutoffAdditionTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (χ : ProductTests ℝ d) (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) : ProductTests 𝕜 d where
  toFun p := χ p • ψ (p.1 + p.2)
  contDiff' := χ.contDiff.smul (ψ.contDiff.comp (contDiff_fst.add contDiff_snd))
  hasCompactSupport' := χ.hasCompactSupport.smul_right
  tsupport_subset' := subset_univ _

/-- An elementary tensor test, with the original scalar-linear convention. -/
def tensorTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a b : Tests 𝕜 (⊤ : Opens (Domain d))) : ProductTests 𝕜 d where
  toFun p := a p.1 * b p.2
  contDiff' := (a.contDiff.comp contDiff_fst).mul (b.contDiff.comp contDiff_snd)
  hasCompactSupport' := by
    apply (a.hasCompactSupport.prod b.hasCompactSupport).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
    intro p hp
    exact ⟨subset_tsupport a (mul_ne_zero_iff.mp hp).1,
      subset_tsupport b (mul_ne_zero_iff.mp hp).2⟩
  tsupport_subset' := subset_univ _

/-- A tensor product is an actual continuous scalar-linear functional on product
 tests, characterized by all elementary tensors. Existence and uniqueness are
 proof obligations, not fields assumed as part of the input distributions. -/
def IsTensorProduct {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (T : ProductTests 𝕜 d →L[𝕜] 𝕜) : Prop :=
  ∀ a b : Tests 𝕜 (⊤ : Opens (Domain d)), T (tensorTest a b) = u a * v b

/-- The tensor/cutoff definition of the convolution, expressed as a relation.
Only proper pairs are in its domain. The same value is required for every
admissible cutoff and every tensor functional, not just a selected witness. -/
def IsProperConvolution {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) : Prop :=
  Convolvable u v ∧
  (∃ T : ProductTests 𝕜 d →L[𝕜] 𝕜, IsTensorProduct u v T) ∧
  ∀ (T : ProductTests 𝕜 d →L[𝕜] 𝕜), IsTensorProduct u v T →
    ∀ (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ : ProductTests ℝ d),
      AdmissibleConvolutionCutoff u v ψ χ → w ψ = T (cutoffAdditionTest χ ψ)

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.ProperSupportConvolution
open _root_.ExpandedFA.Distributions

/-- Relational interface for the partial tensor/cutoff product. The existence
of a value at each proper pair is a separate proof obligation. -/
def convolutionRelationType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) →
  ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) →
  ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) → Prop

def convolutionRelationValue : convolutionRelationType :=
  fun _ _ _ u v w => IsProperConvolution u v w

/-- The compact-slice formulation is exactly properness of the restricted map. -/
def propernessBridgeType : Prop := ∀ (d : ℕ) (S T : Set (Domain d)),
  AdditionProper S T ↔ IsProperMap (fun p : S ×ˢ T => p.val.1 + p.val.2)

def propernessSymmetryType : Prop := ∀ (d : ℕ) (S T : Set (Domain d)),
  AdditionProper S T ↔ AdditionProper T S

def compactSupportSufficesType : Prop := ∀ (d : ℕ) (S T : Set (Domain d)),
  IsClosed S → IsClosed T → (IsCompact S ∨ IsCompact T) → AdditionProper S T

def supportClosedType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))), IsClosed (distributionSupport u)

def compactDistributionSufficesType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  (IsCompact (distributionSupport u) ∨ IsCompact (distributionSupport v)) → Convolvable u v

/-- Properness implies the support sum itself is closed, so the conclusion
about support will not be silently weakened to inclusion in its closure. -/
def closedSumType : Prop := ∀ (d : ℕ) (S T : Set (Domain d)),
  AdditionProper S T → IsClosed (S + T)

/-- Closed subsets of the original supports retain properness. -/
def propernessMonotoneType : Prop := ∀ (d : ℕ) (S T A B : Set (Domain d)),
  AdditionProper S T → IsClosed A → IsClosed B → A ⊆ S → B ⊆ T → AdditionProper A B

def cutoffExistenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))), Convolvable u v →
  ∀ ψ : Tests 𝕜 (⊤ : Opens (Domain d)),
    ∃ χ : ProductTests ℝ d, AdmissibleConvolutionCutoff u v ψ χ

/-- Properness of the triple gives properness after adding the first two sets.
This assertion also covers empty sets without an arbitrary choice of a point. -/
def tripleGroupedType : Prop := ∀ (d : ℕ) (S T U : Set (Domain d)),
  TripleAdditionProper S T U → AdditionProper (S + T) U

/-- With a nonempty third set, fixing a point gives properness for the first
pair. No such assertion is made when the third set is empty. -/
def triplePairType : Prop := ∀ (d : ℕ) (S T U : Set (Domain d)),
  IsClosed S → IsClosed T → U.Nonempty →
  TripleAdditionProper S T U → AdditionProper S T

/-- Two compact factors suffice for the triple in this order; permutations
will give the other two placements. -/
def tripleCompactType : Prop := ∀ (d : ℕ) (S T U : Set (Domain d)),
  IsCompact S → IsCompact T → IsClosed U → TripleAdditionProper S T U

def tripleRotationType : Prop := ∀ (d : ℕ) (S T U : Set (Domain d)),
  TripleAdditionProper S T U → TripleAdditionProper T U S

def twoCompactTripleType : Prop := ∀ (d : ℕ) (S T U : Set (Domain d)),
  IsClosed S → IsClosed T → IsClosed U →
  ((IsCompact S ∧ IsCompact T) ∨ (IsCompact S ∧ IsCompact U) ∨
    (IsCompact T ∧ IsCompact U)) → TripleAdditionProper S T U

def cutoffAgreementType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ χ' : ProductTests ℝ d),
  AdmissibleConvolutionCutoff u v ψ χ → AdmissibleConvolutionCutoff u v ψ χ' →
  ∃ V : Set (Domain d × Domain d), IsOpen V ∧
    (distributionSupport u ×ˢ distributionSupport v) ⊆ V ∧
    EqOn (cutoffAdditionTest χ ψ) (cutoffAdditionTest χ' ψ) V

def derivativeSupportType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (w : List (Fin d)),
  distributionSupport (DistributionCalculus.derivativeValue 𝕜 d ⊤ w u) ⊆ distributionSupport u

/-- A single cutoff works for the entire test-function step supported in K.
This is the geometric input to proving LF continuity of the final pairing. -/
def commonCutoffType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))), Convolvable u v →
  ∀ K : Set (Domain d), IsCompact K → ∃ χ : ProductTests ℝ d,
    ∀ ψ : Tests 𝕜 (⊤ : Opens (Domain d)), tsupport ψ ⊆ K →
      AdmissibleConvolutionCutoff u v ψ χ

def derivativeConvolvableType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (w : List (Fin d)),
  Convolvable u v →
    Convolvable (DistributionCalculus.derivativeValue 𝕜 d ⊤ w u) v ∧
    Convolvable u (DistributionCalculus.derivativeValue 𝕜 d ⊤ w v)

def zeroSupportType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  distributionSupport u = ∅ ↔ u = 0

/-! The following are the principal analytic and algebraic proof obligations. They are
ordinary definitions of full propositions, and are not assumed certificates.
Each proposition remains independent of the candidate implementation. -/

def tensorExistenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  ∃! T : ProductTests 𝕜 d →L[𝕜] 𝕜, IsTensorProduct u v T

/-- The resulting pairing is a distribution, so its LF continuity is included. -/
def convolutionExistenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))), Convolvable u v →
  ∃! w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)), IsProperConvolution u v w

/-- Uniqueness can be established before the tensor existence construction. -/
def convolutionUniquenessType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v w w' : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  IsProperConvolution u v w → IsProperConvolution u v w' → w = w'

def convolutionCommutativityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  IsProperConvolution u v w → IsProperConvolution v u w

/-- All coordinate words, including the empty word and every multi-index word. -/
def convolutionDerivativesType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (α : List (Fin d)),
  IsProperConvolution u v w →
    IsProperConvolution (DistributionCalculus.derivativeValue 𝕜 d ⊤ α u) v
      (DistributionCalculus.derivativeValue 𝕜 d ⊤ α w) ∧
    IsProperConvolution u (DistributionCalculus.derivativeValue 𝕜 d ⊤ α v)
      (DistributionCalculus.derivativeValue 𝕜 d ⊤ α w)

def convolutionSupportType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  IsProperConvolution u v w → distributionSupport w ⊆ distributionSupport u + distributionSupport v

/-- Associativity as a relation between partial products: whenever the two
inner products are given, triple properness gives a unique common outer product.
It does not infer pair properness by fixing a point in an empty support.
The final construction must also handle vanishing factors and prove the
specified compact-support sufficient cases. -/
def convolutionAssociativityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v w a b : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  TripleAdditionProper (distributionSupport u) (distributionSupport v) (distributionSupport w) →
  IsProperConvolution u v a → IsProperConvolution v w b →
  ∃! z : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)),
    IsProperConvolution a w z ∧ IsProperConvolution u b z

/-- The chosen convolution is defined only on proper pairs. Its specification
is a separate theorem, proved from tensor existence and cutoff independence. -/
def convolutionOperationType : Type 1 := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  Convolvable u v → ScalarDistribution 𝕜 (⊤ : Opens (Domain d))

noncomputable def convolutionOperationValue : convolutionOperationType :=
  fun _ _ _ u v _ => Classical.epsilon (IsProperConvolution u v)

def convolutionOperationSpecType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))) (h : Convolvable u v),
  IsProperConvolution u v (convolutionOperationValue 𝕜 d u v h)

/-- Both the tensor witness and the admissible cutoff may be changed. -/
def cutoffIndependenceType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  Convolvable u v → ∀ (T T' : ProductTests 𝕜 d →L[𝕜] 𝕜),
  IsTensorProduct u v T → IsTensorProduct u v T' →
  ∀ (ψ : Tests 𝕜 (⊤ : Opens (Domain d))) (χ χ' : ProductTests ℝ d),
  AdmissibleConvolutionCutoff u v ψ χ → AdmissibleConvolutionCutoff u v ψ χ' →
    T (cutoffAdditionTest χ ψ) = T' (cutoffAdditionTest χ' ψ)

/-- Any two compact supports give both inner products and a unique common
outer product, including the zero-factor cases. -/
def twoCompactAssociativityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u v w : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  ((IsCompact (distributionSupport u) ∧ IsCompact (distributionSupport v)) ∨
    (IsCompact (distributionSupport u) ∧ IsCompact (distributionSupport w)) ∨
    (IsCompact (distributionSupport v) ∧ IsCompact (distributionSupport w))) →
  ∃ a b : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)),
    IsProperConvolution u v a ∧ IsProperConvolution v w b ∧
    ∃! z : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)),
      IsProperConvolution a w z ∧ IsProperConvolution u b z

end Specs.ExpandedFA.Distributions.ProperSupportConvolution
