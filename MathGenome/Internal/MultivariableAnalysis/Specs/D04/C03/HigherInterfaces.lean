import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! Independent objects for d04:03:higher-derivative and d04:03:multi-index.
Ambient functions represent restrictions to open U, as in chapter 2.
Derivative selectors do not assert existence. The pointwise predicate below
asserts existence recursively and places no continuity condition on the top derivative. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C03.HigherInterfaces
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
namespace Model

abbrev Differential (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y

/-- The explicit continuous linear identification puts the new slot first. -/
def differentialSuccEquiv (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) :
    (X →L[ℝ] Differential X Y k) ≃L[ℝ] Differential X Y (k + 1) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => X) Y).symm.toContinuousLinearEquiv

/-- Evaluation on all standard basis tuples, with the finite product norm. -/
def differentialCoefficients {n : ℕ} {Y : Type} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (k : ℕ) :
    Differential (E n) Y k →L[ℝ] ((Fin k → Fin n) → Y) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousMultilinearMap.apply ℝ _ Y (fun r => standardBasis n (j r))

/-- D⁰f is the order-zero tensor with value f; successors differentiate the tensor field. -/
def higherDifferential {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) :
    X → Differential X Y k := iteratedFDeriv ℝ k f

/-- Order zero here asserts only the open domain and membership. Continuity for
order-zero Taylor--Peano is a separate hypothesis, as in the source.
At order k+1, derivatives through k exist near a, and Dᵏf is differentiable at a.
Lower-order existence is asserted recursively at every point of one open neighborhood. -/
def TimesDifferentiableAt {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : ℕ → Set X → (X → Y) → X → Prop
  | 0, U, _, a => IsOpen U ∧ a ∈ U
  | k + 1, U, f, a => ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      (∀ x ∈ V, TimesDifferentiableAt k U f x) ∧
      TotalDifferentiableAt V (higherDifferential k f) a

/-- Diagonal evaluation includes order zero without a special nonempty convention. -/
def differentialDiagonal {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k : ℕ}
    (T : Differential X Y k) (h : X) : Y := T (fun _ => h)

abbrev MultiIndex (n : ℕ) := Fin n → ℕ

def multiIndexDegree {n : ℕ} (α : MultiIndex n) : ℕ := ∑ i, α i

def multiIndexFactorial {n : ℕ} (α : MultiIndex n) : ℕ := ∏ i, (α i).factorial

def multiIndexMonomial {n : ℕ} (α : MultiIndex n) (h : E n) : ℝ :=
  ∏ i, (h i) ^ (α i)

/-- A canonical coordinate word: each coordinate is repeated its multiplicity.
Its order is retained until the separately proved symmetry theorem applies. -/
def multiIndexWord {n : ℕ} (α : MultiIndex n) : List (Fin n) :=
  (List.ofFn fun i : Fin n => List.replicate (α i) i).flatten

/-- Ordered partial selectors, defined with the chapter-2 directional derivative.
No existence or order-independence is inferred from a selector value. -/
def orderedPartial {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    List (Fin n) → (E n → Y) → E n → Y
  | [], f => f
  | i :: is, f => fun a => directionalDerivative (orderedPartial is f) a (standardBasis n i)

/-- The multi-index partial uses the canonical word. Under symmetry this is the
partial with these multiplicities, independently of the chosen ordering. -/
def multiIndexPartial {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (α : MultiIndex n) (f : E n → Y) : E n → Y :=
  orderedPartial (multiIndexWord α) f

def taylorPolynomial {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) (a h : X) : Y :=
  ∑ j ∈ Finset.range (k + 1), ((j.factorial : ℝ)⁻¹) •
    differentialDiagonal (higherDifferential j f a) h

def taylorRemainder {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) (a h : X) : Y :=
  f (a + h) - taylorPolynomial k f a h

end Model

abbrev DifferentialType := (X Y : Type) → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → ℕ → Type
def DifferentialValue : DifferentialType := @Model.Differential

abbrev differentialSuccEquivType := (X Y : Type) → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (k : ℕ) → (X →L[ℝ] Model.Differential X Y k) ≃L[ℝ] Model.Differential X Y (k+1)
def differentialSuccEquivValue : differentialSuccEquivType := @Model.differentialSuccEquiv

abbrev differentialCoefficientsType := {n : ℕ} → {Y : Type} → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (k : ℕ) → Model.Differential (E n) Y k →L[ℝ] ((Fin k → Fin n) → Y)
def differentialCoefficientsValue : differentialCoefficientsType := @Model.differentialCoefficients

abbrev higherDifferentialType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (k : ℕ) → (X → Y) → X → Model.Differential X Y k
def higherDifferentialValue : higherDifferentialType := @Model.higherDifferential

abbrev TimesDifferentiableAtType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → ℕ → Set X → (X → Y) → X → Prop
def TimesDifferentiableAtValue : TimesDifferentiableAtType := @Model.TimesDifferentiableAt

abbrev differentialDiagonalType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → {k : ℕ} → Model.Differential X Y k → X → Y
def differentialDiagonalValue : differentialDiagonalType := @Model.differentialDiagonal

abbrev MultiIndexType := ℕ → Type
def MultiIndexValue : MultiIndexType := @Model.MultiIndex

abbrev multiIndexDegreeType := {n : ℕ} → Model.MultiIndex n → ℕ
def multiIndexDegreeValue : multiIndexDegreeType := @Model.multiIndexDegree

abbrev multiIndexFactorialType := {n : ℕ} → Model.MultiIndex n → ℕ
def multiIndexFactorialValue : multiIndexFactorialType := @Model.multiIndexFactorial

abbrev multiIndexMonomialType := {n : ℕ} → Model.MultiIndex n → E n → ℝ
def multiIndexMonomialValue : multiIndexMonomialType := @Model.multiIndexMonomial

abbrev multiIndexWordType := {n : ℕ} → Model.MultiIndex n → List (Fin n)
def multiIndexWordValue : multiIndexWordType := @Model.multiIndexWord

abbrev orderedPartialType := {n : ℕ} → {Y : Type} → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → List (Fin n) → (E n → Y) → E n → Y
def orderedPartialValue : orderedPartialType := @Model.orderedPartial

abbrev multiIndexPartialType := {n : ℕ} → {Y : Type} → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Model.MultiIndex n → (E n → Y) → E n → Y
def multiIndexPartialValue : multiIndexPartialType := @Model.multiIndexPartial

abbrev taylorPolynomialType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → ℕ → (X → Y) → X → X → Y
def taylorPolynomialValue : taylorPolynomialType := @Model.taylorPolynomial

abbrev taylorRemainderType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → ℕ → (X → Y) → X → X → Y
def taylorRemainderValue : taylorRemainderType := @Model.taylorRemainder

-- Expected propositions: full types, independent of candidate implementations.
open Model

def differentialSuccEquiv_applyType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (A : X →L[ℝ] Differential X Y k)
    (v : Fin (k + 1) → X),
    differentialSuccEquiv X Y k A v = A (v 0) (Fin.tail v)

def differentialSuccEquiv_symm_applyType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (T : Differential X Y (k + 1))
    (v : X) (vs : Fin k → X),
    (differentialSuccEquiv X Y k).symm T v vs = T (Fin.cons v vs)

def higherDifferential_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (a : X) (v : Fin 0 → X),
    higherDifferential 0 f a v = f a

def higherDifferential_succType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) (a : X),
    higherDifferential (k+1) f a =
      differentialSuccEquiv X Y k (totalDerivative (higherDifferential k f) a)

def higherDifferential_succ_applyType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) (a v : X)
    (vs : Fin k → X),
    higherDifferential (k+1) f a (Fin.cons v vs) =
      totalDerivative (higherDifferential k f) a v vs

def differentialDiagonal_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : Differential X Y 0) (h : X),
    differentialDiagonal T h = T (fun i => Fin.elim0 i)

def timesDifferentiableAt_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a : X),
    TimesDifferentiableAt 0 U f a ↔ IsOpen U ∧ a ∈ U

def timesDifferentiableAt_succType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f : X → Y) (a : X),
    TimesDifferentiableAt (k+1) U f a ↔
      ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
        (∀ x ∈ V, TimesDifferentiableAt k U f x) ∧
        TotalDifferentiableAt V (higherDifferential k f) a

def timesDifferentiableAt_domainType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt k U f a),
    IsOpen U ∧ a ∈ U

def timesDifferentiableAt_lowerType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a),
    TimesDifferentiableAt k U f a

def timesDifferentiableAt_hasFDerivAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a),
    HasFDerivAt (higherDifferential k f)
      ((differentialSuccEquiv X Y k).symm (higherDifferential (k+1) f a)) a

def timesDifferentiableAt_oneType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a : X),
    TimesDifferentiableAt 1 U f a ↔ TotalDifferentiableAt U f a

def higherDifferential_congrType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f g : X → Y)
    (hU : IsOpen U) (hfg : EqOn f g U),
    EqOn (higherDifferential k f) (higherDifferential k g) U

def timesDifferentiableAt_congrType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f g : X → Y) (a : X)
    (hU : IsOpen U) (hfg : EqOn f g U),
    TimesDifferentiableAt k U f a ↔ TimesDifferentiableAt k U g a

def taylorPolynomial_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (a h : X),
    taylorPolynomial 0 f a h = f a

def taylorPolynomial_congrType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (U : Set X) (f g : X → Y) (a h : X)
    (hU : IsOpen U) (ha : a ∈ U) (hfg : EqOn f g U),
    taylorPolynomial k f a h = taylorPolynomial k g a h

def taylorPolynomial_zero_incrementType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) (a : X),
    taylorPolynomial k f a 0 = f a

def taylorRemainder_zero_incrementType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) (a : X),
    taylorRemainder k f a 0 = 0

def taylorRemainder_expansionType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (k : ℕ) (f : X → Y) (a h : X),
    f (a+h) = taylorPolynomial k f a h + taylorRemainder k f a h

def differentialCoefficients_applyType : Prop :=
  ∀ {n k : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : Differential (E n) Y k) (j : Fin k → Fin n),
    differentialCoefficients k T j = T (fun r => standardBasis n (j r))

def differential_expansionType : Prop :=
  ∀ {n k : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : Differential (E n) Y k) (v : Fin k → E n),
    T v = ∑ j : Fin k → Fin n, (∏ r, v r (j r)) • differentialCoefficients k T j

def differentialCoefficients_injectiveType : Prop :=
  ∀ {n k : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y],
    Function.Injective (differentialCoefficients (n := n) (Y := Y) k)

def differentialCoefficients_surjectiveType : Prop :=
  ∀ {n k : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y],
    Function.Surjective (differentialCoefficients (n := n) (Y := Y) k)

def differentialCoefficients_continuousLinearEquivType : Prop :=
  ∀ (n m k : ℕ),
    ∃ e : Differential (E n) (E m) k ≃L[ℝ] ((Fin k → Fin n) → E m),
      ∀ T j, e T j = T (fun r => standardBasis n (j r))

def differentialSuccEquiv_basisType : Prop :=
  ∀ {n k : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (A : E n →L[ℝ] Differential (E n) Y k)
    (j : Fin (k+1) → Fin n),
    differentialCoefficients (k+1) (differentialSuccEquiv (E n) Y k A) j =
      differentialCoefficients k (A (standardBasis n (j 0))) (Fin.tail j)

def multiIndexWord_lengthType : Prop :=
  ∀ {n : ℕ} (α : MultiIndex n),
    (multiIndexWord α).length = multiIndexDegree α

def multiIndexWord_countType : Prop :=
  ∀ {n : ℕ} (α : MultiIndex n) (i : Fin n),
    (multiIndexWord α).count i = α i

def orderedPartial_nilType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : E n → Y),
    orderedPartial [] f = f

def orderedPartial_consType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (i : Fin n) (is : List (Fin n)) (f : E n → Y) (a : E n),
    orderedPartial (i :: is) f a = directionalDerivative (orderedPartial is f) a (standardBasis n i)

def multiIndexPartial_eqType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (α : MultiIndex n) (f : E n → Y),
    multiIndexPartial α f = orderedPartial (multiIndexWord α) f

def multiIndex_dimension_zero_uniqueType : Prop :=
  ∀ (α β : MultiIndex 0),
    α = β

def multiIndexDegree_dimension_zeroType : Prop :=
  ∀ (α : MultiIndex 0),
    multiIndexDegree α = 0

def multiIndexFactorial_dimension_zeroType : Prop :=
  ∀ (α : MultiIndex 0),
    multiIndexFactorial α = 1

def multiIndexMonomial_dimension_zeroType : Prop :=
  ∀ (α : MultiIndex 0) (h : E 0),
    multiIndexMonomial α h = 1

def multiIndexPartial_dimension_zeroType : Prop :=
  ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (α : MultiIndex 0) (f : E 0 → Y),
    multiIndexPartial α f = f

def higherDifferential_dimension_zeroType : Prop :=
  ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (hk : 0 < k) (f : E 0 → Y) (a : E 0),
    higherDifferential k f a = 0

def taylorPolynomial_dimension_zeroType : Prop :=
  ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (f : E 0 → Y) (a h : E 0),
    taylorPolynomial k f a h = f a

def taylorRemainder_dimension_zeroType : Prop :=
  ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (f : E 0 → Y) (a h : E 0),
    taylorRemainder k f a h = 0

end Specs.D04.C03.HigherInterfaces
