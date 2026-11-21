import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Chapter 2, definitions d04:02:derivative and d04:02:cr.
Functions on a subset are represented by ambient functions restricted to that subset.
`domainExtension` also admits literally subtype-valued domain functions. All open-domain
bridges require openness and membership explicitly. Relative approximation has neither
requirement and carries no uniqueness assertion. Generic normed targets allow the same
recursive regularity definition to apply to the operator-valued derivative map. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C02.DerivativeInterfaces
namespace Model
open Specs.D04.C01.EuclideanInterfaces.Model
def domainExtension : {n m : ℕ} → (U : Set (E n)) → (U → E m) → E n → E m :=
  by
  classical
  exact fun U f x => if hx : x ∈ U then f ⟨x, hx⟩ else 0

def HasDirectionalDerivative : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → X → X → Y → Prop :=
  fun f a v d => Tendsto (fun t : ℝ => t⁻¹ • (f (a + t • v) - f a)) (𝓝[≠] 0) (𝓝 d)

/-- Total selector: Mathlib returns zero when the line derivative does not exist.
Use HasDirectionalDerivative to assert existence; a zero selector alone does not do so. -/
def directionalDerivative : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → X → X → Y :=
  fun f a v => deriv (fun t : ℝ => f (a + t • v)) 0

def HasPartialDerivative : {n m : ℕ} → (E n → E m) → E n → Fin n → E m → Prop :=
  fun f a j d => HasDirectionalDerivative f a (standardBasis _ j) d

def partialDerivative : {n m : ℕ} → (E n → E m) → E n → Fin n → E m :=
  fun f a j => directionalDerivative f a (standardBasis _ j)

def remainder : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → (X →L[ℝ] Y) → X → X → Y :=
  fun f A a h => f (a + h) - f a - A h

def RelativeApproximation : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → (X →L[ℝ] Y) → X → Prop :=
  fun U f A a => Tendsto (fun x => ‖f x - f a - A (x - a)‖ / ‖x - a‖) (𝓝[U \ {a}] a) (𝓝 0)

def HasTotalDerivative : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → (X →L[ℝ] Y) → X → Prop :=
  fun U f A a => IsOpen U ∧ a ∈ U ∧ RelativeApproximation U f A a

def HasLinearDerivative : {n m : ℕ} → Set (E n) → (E n → E m) → (E n →ₗ[ℝ] E m) → E n → Prop :=
  fun U f A a => HasTotalDerivative U f (LinearMap.toContinuousLinearMap A) a

/-- The standard derivative selector. Existence is asserted separately by HasTotalDerivative. -/
def totalDerivative : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → X → X →L[ℝ] Y :=
  fun f a => fderiv ℝ f a

def TotalDifferentiableOn : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → Prop :=
  fun U f => ∀ a ∈ U, ∃ A, HasTotalDerivative U f A a

/-- Recursive finite regularity, with C⁰ equal to continuity. Intended on open U. -/
def CrOn (r : ℕ) {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) : Prop :=
  match r with
  | 0 => ContinuousOn f U
  | r + 1 => TotalDifferentiableOn U f ∧ CrOn r U (totalDerivative f)

def SmoothOn : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → Prop :=
  fun U f => ∀ r : ℕ, CrOn r U f

def RealAnalyticOn : {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → Prop :=
  fun U f => ∀ a ∈ U, ∃ p : FormalMultilinearSeries ℝ _ _, HasFPowerSeriesAt f p a

end Model
open Specs.D04.C01.EuclideanInterfaces.Model

abbrev domainExtensionType := {n m : ℕ} → (U : Set (E n)) → (U → E m) → E n → E m
def domainExtensionValue : domainExtensionType := @Model.domainExtension

abbrev HasDirectionalDerivativeType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → X → X → Y → Prop
def HasDirectionalDerivativeValue : HasDirectionalDerivativeType := @Model.HasDirectionalDerivative

abbrev directionalDerivativeType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → X → X → Y
def directionalDerivativeValue : directionalDerivativeType := @Model.directionalDerivative

abbrev HasPartialDerivativeType := {n m : ℕ} → (E n → E m) → E n → Fin n → E m → Prop
def HasPartialDerivativeValue : HasPartialDerivativeType := @Model.HasPartialDerivative

abbrev partialDerivativeType := {n m : ℕ} → (E n → E m) → E n → Fin n → E m
def partialDerivativeValue : partialDerivativeType := @Model.partialDerivative

abbrev remainderType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → (X →L[ℝ] Y) → X → X → Y
def remainderValue : remainderType := @Model.remainder

abbrev RelativeApproximationType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → (X →L[ℝ] Y) → X → Prop
def RelativeApproximationValue : RelativeApproximationType := @Model.RelativeApproximation

abbrev HasTotalDerivativeType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → (X →L[ℝ] Y) → X → Prop
def HasTotalDerivativeValue : HasTotalDerivativeType := @Model.HasTotalDerivative

abbrev HasLinearDerivativeType := {n m : ℕ} → Set (E n) → (E n → E m) → (E n →ₗ[ℝ] E m) → E n → Prop
def HasLinearDerivativeValue : HasLinearDerivativeType := @Model.HasLinearDerivative

abbrev totalDerivativeType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → (X → Y) → X → X →L[ℝ] Y
def totalDerivativeValue : totalDerivativeType := @Model.totalDerivative

abbrev TotalDifferentiableOnType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → Prop
def TotalDifferentiableOnValue : TotalDifferentiableOnType := @Model.TotalDifferentiableOn

abbrev SmoothOnType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → Prop
def SmoothOnValue : SmoothOnType := @Model.SmoothOn

abbrev RealAnalyticOnType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → Prop
def RealAnalyticOnValue : RealAnalyticOnType := @Model.RealAnalyticOn

abbrev CrOnType := (r : ℕ) → {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → Prop
def CrOnValue : CrOnType := @Model.CrOn

/-! Expected theorem propositions. These import no candidate implementation and
state the full mathematical limits and equivalences. -/
open Model
open scoped ContDiff

def relativeApproximation_iff_hasFDerivWithinAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X),
    RelativeApproximation U f A a ↔ HasFDerivWithinAt f A U a

def hasTotalDerivative_iff_hasFDerivAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X) (hU : IsOpen U) (ha : a ∈ U),
    HasTotalDerivative U f A a ↔ HasFDerivAt f A a

def totalDerivative_eqType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X) (h : HasTotalDerivative U f A a),
    totalDerivative f a = A

def totalDifferentiableOn_iffType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (hU : IsOpen U),
    TotalDifferentiableOn U f ↔ DifferentiableOn ℝ f U

def remainder_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (A : X →L[ℝ] Y) (a : X),
    remainder f A a 0 = 0

def remainder_expansionType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (A : X →L[ℝ] Y) (a : X) (h : X),
    f (a + h) = f a + A h + remainder f A a h

def relativeApproximation_iff_remainder_limitType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X),
    RelativeApproximation U f A a ↔
      Tendsto (fun h => ‖remainder f A a h‖ / ‖h‖)
        (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0)

def hasDirectionalDerivative_iff_hasDerivAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (a : X) (v : X) (d : Y),
    HasDirectionalDerivative f a v d ↔ HasDerivAt (fun t : ℝ => f (a + t • v)) d 0

def directionalDerivative_eqType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (a : X) (v : X) (d : Y)
    (h : HasDirectionalDerivative f a v d),
    directionalDerivative f a v = d

def relativeApproximation_iff_exists_remainderType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X),
    RelativeApproximation U f A a ↔ ∃ r : X → Y,
      r 0 = 0 ∧ (∀ h, a + h ∈ U → f (a + h) = f a + A h + r h) ∧
      Tendsto (fun h => ‖r h‖ / ‖h‖) (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0)

def hasTotalDerivative_iff_remainderType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X) (hU : IsOpen U) (ha : a ∈ U),
    HasTotalDerivative U f A a ↔ ∃ r : X → Y,
      r 0 = 0 ∧ (∀ h, a + h ∈ U → f (a + h) = f a + A h + r h) ∧
      Tendsto (fun h => ‖r h‖ / ‖h‖) (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0)

def hasTotalDerivative_congrType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X) (g : X → Y) (ha : a ∈ U) (hfg : EqOn f g U),
    HasTotalDerivative U f A a ↔ HasTotalDerivative U g A a

def totalDerivative_congrType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (f : X → Y) (a : X) (g : X → Y) (hU : IsOpen U) (ha : a ∈ U)
    (hfg : EqOn f g U),
    totalDerivative f a = totalDerivative g a

def crOn_iff_contDiffOnType : Prop :=
  ∀ (r : ℕ) {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (hU : IsOpen U),
    CrOn r U f ↔ ContDiffOn ℝ (r : ℕ∞ω) f U

def smoothOn_iff_contDiffOnType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (hU : IsOpen U),
    SmoothOn U f ↔ ContDiffOn ℝ ∞ f U

def realAnalyticOn_iffType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y),
    RealAnalyticOn U f ↔ AnalyticOnNhd ℝ f U

def hasLinearDerivative_iffType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (A : E n →ₗ[ℝ] E m) (a : E n) (hU : IsOpen U) (ha : a ∈ U),
    HasLinearDerivative U f A a ↔ HasFDerivAt f (LinearMap.toContinuousLinearMap A) a

def totalDerivative_operatorNormType : Prop :=
  ∀ {n m : ℕ} (f : E n → E m) (a : E n),
    linearOperatorNorm (totalDerivative f a).toLinearMap = ‖fderiv ℝ f a‖

def domainExtension_applyType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : U → E m) (a : U),
    domainExtension U f a = f a

def domainExtension_eqOnType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : U → E m)
    (g : E n → E m) (hg : ∀ x : U, g x = f x),
    EqOn (domainExtension U f) g U

def domainExtension_hasTotalDerivative_iffType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : U → E m)
    (g : E n → E m) (hg : ∀ x : U, g x = f x) (a : U) (A : E n →L[ℝ] E m),
    HasTotalDerivative U (domainExtension U f) A a ↔ HasTotalDerivative U g A a

def crOn_congrType : Prop :=
  ∀ (r : ℕ) {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f g : X → Y)
    (hU : IsOpen U) (hfg : EqOn f g U),
    CrOn r U f ↔ CrOn r U g

def domainExtension_continuousOn_iffType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : U → E m),
    ContinuousOn (domainExtension U f) U ↔ Continuous f

end Specs.D04.C02.DerivativeInterfaces
