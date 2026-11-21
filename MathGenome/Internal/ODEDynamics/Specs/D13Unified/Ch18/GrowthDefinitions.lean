import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.StateDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Independent specification of paper.tex, Definition d13:18:exponent-definition.
All norms of linear maps are the induced operator norms of the given norm on E.
The definitions also work in normed spaces without a dimension restriction;
the matrix interpretation and canonical ODE bridge retain finite dimension.

A directional exponent is the graph of an actual extended-real limit. The
optional value is `none` precisely when there is no such limit. Operator upper
rates are separate limsups and make no assertion of convergence.

`DifferentiableTimeFamily` records only the data needed to define derivative
growth. Every differentiable partial flow supplies these data; no flow law is
needed for this more general definition. Its total representative is used only
on its actual open domain: finite rates require domain membership, use within
derivatives on the actual time slice, and asymptotic rates require forward
completeness. The canonical ODE bridge below uses the existing flow and domain.
-/
noncomputable section
open Set Filter Module
open scoped Topology

namespace D13Unified.Ch18.GrowthDefinitions

/-- A C¹ self-map of an open set. The representative is arbitrary off `domain`. -/
structure C1SelfMap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  domain : Set E
  isOpen_domain : IsOpen domain
  value : E → E
  mapsTo : MapsTo value domain domain
  contDiffOn : ContDiffOn ℝ 1 value domain

/-- A differentiable time family with its actual open domain. This is sufficient
input for growth definitions, without imposing additional dynamical axioms. -/
structure DifferentiableTimeFamily (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  domain : Set (ℝ × E)
  isOpen_domain : IsOpen domain
  value : ℝ → E → E
  differentiableOn : ∀ t : ℝ, DifferentiableOn ℝ (value t) {x | (t,x) ∈ domain}

end D13Unified.Ch18.GrowthDefinitions

namespace Specs.D13Unified.Ch18.GrowthDefinitions
open _root_.D13Unified.Ch18.GrowthDefinitions
universe u v

abbrev logarithmicRateType :=
  ℝ → ℝ → EReal

/-- For a nonnegative magnitude and positive time, log(r)/t, with log(0) = −∞.
The explicit zero branch avoids the real logarithm’s convention at zero. -/
def logarithmicRate : logarithmicRateType :=
  fun t r => if r = 0 then ⊥ else ((Real.log r / t : ℝ) : EReal)

abbrev directionalRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (E →L[ℝ] E) → E → ℝ → EReal

def directionalRate : directionalRateType :=
  fun L v t => logarithmicRate t (‖L v‖ / ‖v‖)

abbrev operatorRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (E →L[ℝ] E) → ℝ → EReal

def operatorRate : operatorRateType :=
  fun L t => logarithmicRate t ‖L‖

abbrev partialLimitType :=
  {ι : Type u} → Filter ι → (ι → EReal) → Option EReal

/-- A partial value: it selects an actual limit if one exists; it never uses limsup.
The filters used below are nontrivial, so such a limit is unique. -/
def partialLimit : partialLimitType :=
  fun l r => by
    classical
    exact if h : ∃ a : EReal, Tendsto r l (𝓝 a) then some (Classical.choose h) else none

abbrev discreteDirectionalRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (F : C1SelfMap E) → F.domain → (v : E) → v ≠ 0 → (n : ℕ) → 0 < n → EReal

/-- The original λ_n(x,v), with n positive, x in U, and v nonzero. -/
def discreteDirectionalRate : discreteDirectionalRateType :=
  fun F x v _ n _ => directionalRate
    (fderivWithin ℝ (Ch15.DiscreteDefinitions.iterate F.value n) F.domain x) v n

abbrev HasDiscreteDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (F : C1SelfMap E) → F.domain → (v : E) → v ≠ 0 → EReal → Prop

/-- The sequence is indexed as λ₁, λ₂, …; −∞ is an allowed limit.
No existence assertion is included in this predicate. -/
def HasDiscreteDirectionalExponent : HasDiscreteDirectionalExponentType :=
  fun F x v hv a => Tendsto
    (fun n : ℕ => discreteDirectionalRate F x v hv (n+1) (Nat.succ_pos n)) atTop (𝓝 a)

abbrev discreteDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (F : C1SelfMap E) → F.domain → (v : E) → v ≠ 0 → Option EReal

def discreteDirectionalExponent : discreteDirectionalExponentType :=
  fun F x v hv => partialLimit atTop
    (fun n : ℕ => discreteDirectionalRate F x v hv (n+1) (Nat.succ_pos n))

abbrev discreteOperatorUpperRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (F : C1SelfMap E) → F.domain → EReal

/-- Operator-norm limsup, which is defined independently of limit existence. -/
def discreteOperatorUpperRate : discreteOperatorUpperRateType :=
  fun F x => limsup (fun n : ℕ => operatorRate
    (fderivWithin ℝ (Ch15.DiscreteDefinitions.iterate F.value (n+1)) F.domain x) (n+1)) atTop

abbrev ForwardCompleteType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → DifferentiableTimeFamily E → E → Prop

/-- The actual trajectory must be defined for every nonnegative time, including zero. -/
def ForwardComplete : ForwardCompleteType :=
  fun Φ x => ∀ t : ℝ, 0 ≤ t → (t,x) ∈ Φ.domain

abbrev flowDirectionalRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (Φ : DifferentiableTimeFamily E) → (x v : E) → v ≠ 0 → (t : ℝ) → 0 < t → (t,x) ∈ Φ.domain → EReal

/-- A finite flow rate requires a positive allowed time; no value is taken at a forbidden time. -/
def flowDirectionalRate : flowDirectionalRateType :=
  fun Φ x v _ t _ _ => directionalRate
    (fderivWithin ℝ (Φ.value t) {y | (t,y) ∈ Φ.domain} x) v t

abbrev flowOperatorRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (Φ : DifferentiableTimeFamily E) → (x : E) → (t : ℝ) → 0 < t → (t,x) ∈ Φ.domain → EReal

/-- Finite-time operator rate at a positive allowed time. -/
def flowOperatorRate : flowOperatorRateType :=
  fun Φ x t _ _ => operatorRate
    (fderivWithin ℝ (Φ.value t) {y | (t,y) ∈ Φ.domain} x) t

abbrev HasFlowDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (Φ : DifferentiableTimeFamily E) → (x v : E) → v ≠ 0 → ForwardComplete Φ x → EReal → Prop

/-- Limit along all positive real times. Forward completeness is an argument,
so an asymptotic rate cannot be formed for an incomplete forward trajectory. -/
def HasFlowDirectionalExponent : HasFlowDirectionalExponentType :=
  fun Φ x v hv hc a => Tendsto
    (fun t : Ioi (0 : ℝ) => flowDirectionalRate Φ x v hv t t.property
      (hc t (le_of_lt t.property))) atTop (𝓝 a)

abbrev flowDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (Φ : DifferentiableTimeFamily E) → (x v : E) → v ≠ 0 → ForwardComplete Φ x → Option EReal

def flowDirectionalExponent : flowDirectionalExponentType :=
  fun Φ x v hv hc => partialLimit atTop
    (fun t : Ioi (0 : ℝ) => flowDirectionalRate Φ x v hv t t.property
      (hc t (le_of_lt t.property)))

abbrev flowOperatorUpperRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → (Φ : DifferentiableTimeFamily E) → (x : E) → ForwardComplete Φ x → EReal

/-- The upper operator rate is only available at a forward complete initial point.
Every time in this limsup is then an allowed time. -/
def flowOperatorUpperRate : flowOperatorUpperRateType :=
  fun Φ x hc => limsup (fun t : Ioi (0 : ℝ) =>
    flowOperatorRate Φ x t t.property (hc t (le_of_lt t.property))) atTop

abbrev cocycleProductType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → (X → X) → (X → E →L[ℝ] E) → ℕ → X → E →L[ℝ] E

/-- Time-ordered product A(T^(n−1)x) ⋯ A(x), with the identity at time zero. -/
def cocycleProduct : cocycleProductType :=
  fun T A n x => Nat.rec (ContinuousLinearMap.id ℝ _)
    (fun k P => (A (Ch15.DiscreteDefinitions.iterate T k x)).comp P) n

abbrev cocycleDirectionalRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → (X → X) → (X → E →L[ℝ] E) → X → (v : E) → v ≠ 0 → (n : ℕ) → 0 < n → EReal

def cocycleDirectionalRate : cocycleDirectionalRateType :=
  fun T A x v _ n _ => directionalRate (cocycleProduct T A n x) v n

abbrev HasCocycleDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → (X → X) → (X → E →L[ℝ] E) → X → (v : E) → v ≠ 0 → EReal → Prop

def HasCocycleDirectionalExponent : HasCocycleDirectionalExponentType :=
  fun T A x v hv a => Tendsto (fun n : ℕ =>
    cocycleDirectionalRate T A x v hv (n+1) (Nat.succ_pos n)) atTop (𝓝 a)

abbrev cocycleDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → (X → X) → (X → E →L[ℝ] E) → X → (v : E) → v ≠ 0 → Option EReal

def cocycleDirectionalExponent : cocycleDirectionalExponentType :=
  fun T A x v hv => partialLimit atTop (fun n : ℕ =>
    cocycleDirectionalRate T A x v hv (n+1) (Nat.succ_pos n))

abbrev cocycleOperatorUpperRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → (X → X) → (X → E →L[ℝ] E) → X → EReal

def cocycleOperatorUpperRate : cocycleOperatorUpperRateType :=
  fun T A x => limsup (fun n : ℕ => operatorRate (cocycleProduct T A (n+1) x) (n+1)) atTop

abbrev matrixOperatorType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {d : ℕ} → Basis (Fin d) ℝ E → Matrix (Fin d) (Fin d) ℝ → E →L[ℝ] E

/-- A matrix acting on E in the specified basis. Its norm is induced by the
given norm on E, not an entrywise matrix norm. -/
def matrixOperator : matrixOperatorType :=
  fun b M => (Matrix.toLin b b M).toContinuousLinearMap

abbrev matrixCocycleProductType :=
  {X : Type v} → {d : ℕ} → (X → X) → (X → Matrix (Fin d) (Fin d) ℝ) → ℕ → X → Matrix (Fin d) (Fin d) ℝ

/-- Literal matrix product with the newest factor on the left. -/
def matrixCocycleProduct : matrixCocycleProductType :=
  fun T A n x => Nat.rec 1
    (fun k P => A (Ch15.DiscreteDefinitions.iterate T k x) * P) n

abbrev matrixDirectionalRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {X : Type v} → {d : ℕ} → Basis (Fin d) ℝ E → (X → X) → (X → Matrix (Fin d) (Fin d) ℝ) → X → (v : E) → v ≠ 0 → (n : ℕ) → 0 < n → EReal

def matrixDirectionalRate : matrixDirectionalRateType :=
  fun b T A x v _ n _ => directionalRate (matrixOperator b (matrixCocycleProduct T A n x)) v n

abbrev HasMatrixDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {X : Type v} → {d : ℕ} → Basis (Fin d) ℝ E → (X → X) → (X → Matrix (Fin d) (Fin d) ℝ) → X → (v : E) → v ≠ 0 → EReal → Prop

def HasMatrixDirectionalExponent : HasMatrixDirectionalExponentType :=
  fun b T A x v hv a => Tendsto (fun n : ℕ =>
    matrixDirectionalRate b T A x v hv (n+1) (Nat.succ_pos n)) atTop (𝓝 a)

abbrev matrixDirectionalExponentType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {X : Type v} → {d : ℕ} → Basis (Fin d) ℝ E → (X → X) → (X → Matrix (Fin d) (Fin d) ℝ) → X → (v : E) → v ≠ 0 → Option EReal

def matrixDirectionalExponent : matrixDirectionalExponentType :=
  fun b T A x v hv => partialLimit atTop (fun n : ℕ =>
    matrixDirectionalRate b T A x v hv (n+1) (Nat.succ_pos n))

abbrev matrixOperatorUpperRateType :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {X : Type v} → {d : ℕ} → Basis (Fin d) ℝ E → (X → X) → (X → Matrix (Fin d) (Fin d) ℝ) → X → EReal

def matrixOperatorUpperRate : matrixOperatorUpperRateType :=
  fun b T A x => limsup (fun n : ℕ => operatorRate (matrixOperator b (matrixCocycleProduct T A (n+1) x)) (n+1)) atTop

def logarithmicRate_zeroStatement : Prop :=
  ∀ t : ℝ, logarithmicRate t 0 = ⊥

def logarithmicRate_nonzeroStatement : Prop :=
  ∀ t r : ℝ, r ≠ 0 → logarithmicRate t r = ((Real.log r / t : ℝ) : EReal)

def directionalRate_annihilatedStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → ∀ (L : E →L[ℝ] E) (v : E) (t : ℝ), L v = 0 →
    directionalRate L v t = ⊥

def partialLimit_some_iffStatement : Prop :=
  ∀ {ι : Type u} (l : Filter ι) [l.NeBot] (r : ι → EReal) (a : EReal),
    partialLimit l r = some a ↔ Tendsto r l (𝓝 a)

def partialLimit_none_iffStatement : Prop :=
  ∀ {ι : Type u} (l : Filter ι) (r : ι → EReal),
    partialLimit l r = none ↔ ¬ ∃ a : EReal, Tendsto r l (𝓝 a)

def discreteDirectionalExponent_some_iffStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → ∀ (F : C1SelfMap E) (x : F.domain) (v : E) (hv : v ≠ 0) (a : EReal),
    discreteDirectionalExponent F x v hv = some a ↔ HasDiscreteDirectionalExponent F x v hv a

def flowDirectionalExponent_some_iffStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → ∀ (Φ : DifferentiableTimeFamily E) (x v : E) (hv : v ≠ 0)
    (hc : ForwardComplete Φ x) (a : EReal),
    flowDirectionalExponent Φ x v hv hc = some a ↔ HasFlowDirectionalExponent Φ x v hv hc a

def cocycleDirectionalExponent_some_iffStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → ∀ (T : X → X) (A : X → E →L[ℝ] E) (x : X)
    (v : E) (hv : v ≠ 0) (a : EReal),
    cocycleDirectionalExponent T A x v hv = some a ↔ HasCocycleDirectionalExponent T A x v hv a

def matrixDirectionalExponent_some_iffStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {X : Type v} → ∀ {d : ℕ} (b : Basis (Fin d) ℝ E) (T : X → X)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : E) (hv : v ≠ 0) (a : EReal),
    matrixDirectionalExponent b T A x v hv = some a ↔ HasMatrixDirectionalExponent b T A x v hv a

def discreteDirectionalRate_formulaStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → ∀ (F : C1SelfMap E) (x : F.domain) (v : E) (hv : v ≠ 0)
    (n : ℕ) (hn : 0 < n),
    discreteDirectionalRate F x v hv n hn =
      logarithmicRate n (‖fderiv ℝ (F.value^[n]) x v‖ / ‖v‖)

def discrete_iterate_differentiableStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → ∀ (F : C1SelfMap E) (n : ℕ) (x : F.domain),
    DifferentiableAt ℝ (F.value^[n]) x

def flowDirectionalRate_formulaStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → ∀ (Φ : DifferentiableTimeFamily E) (x v : E) (hv : v ≠ 0)
    (t : ℝ) (ht : 0 < t) (hx : (t,x) ∈ Φ.domain),
    flowDirectionalRate Φ x v hv t ht hx =
      logarithmicRate t (‖fderiv ℝ (Φ.value t) x v‖ / ‖v‖)

def flowDirectionalRate_congrStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → ∀ (Φ Ψ : DifferentiableTimeFamily E), Φ.domain = Ψ.domain →
    (∀ t x, (t,x) ∈ Φ.domain → Φ.value t x = Ψ.value t x) →
    ∀ (x v : E) (hv : v ≠ 0) (t : ℝ) (ht : 0 < t)
      (hx : (t,x) ∈ Φ.domain) (hy : (t,x) ∈ Ψ.domain),
      flowDirectionalRate Φ x v hv t ht hx = flowDirectionalRate Ψ x v hv t ht hy

def cocycleProduct_zeroStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → ∀ (T : X → X) (A : X → E →L[ℝ] E) (x : X),
    cocycleProduct T A 0 x = ContinuousLinearMap.id ℝ E

def cocycleProduct_succStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → {X : Type v} → ∀ (T : X → X) (A : X → E →L[ℝ] E) (n : ℕ) (x : X),
    cocycleProduct T A (n+1) x = (A (T^[n] x)).comp (cocycleProduct T A n x)

def matrixOperator_productStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {X : Type v} → ∀ {d : ℕ} (b : Basis (Fin d) ℝ E) (T : X → X)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : X),
    matrixOperator b (matrixCocycleProduct T A n x) =
      cocycleProduct T (fun y => matrixOperator b (A y)) n x

def matrixDirectionalRate_eq_cocycleStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → {X : Type v} → ∀ {d : ℕ} (b : Basis (Fin d) ℝ E) (T : X → X)
    (A : X → Matrix (Fin d) (Fin d) ℝ) (x : X) (v : E) (hv : v ≠ 0)
    (n : ℕ) (hn : 0 < n),
    matrixDirectionalRate b T A x v hv n hn =
      cocycleDirectionalRate T (fun y => matrixOperator b (A y)) x v hv n hn

def canonical_flow_familyStatement : Prop :=
  {E : Type u} → [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E] → ∀ (F : _root_.D13Unified.AutonomousODE E),
    ContDiffOn ℝ 1 (Ch01.AutonomousParameters.autonomousEvalValue F) F.domain →
    ∃ Φ : DifferentiableTimeFamily E,
      Φ.domain = _root_.D13Unified.Ch06.StateDerivative.flowDomain F ∧
      Φ.value = _root_.D13Unified.Ch06.StateDerivative.flow F

end Specs.D13Unified.Ch18.GrowthDefinitions
