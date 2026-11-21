import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.DividedDifferences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Independent definitions for the exact iterations of W73–W78.
Scalar formulas specialize to ℝ; the operator formulas cover real and complex
Banach spaces. Totalization is separated from admissibility. These definitions
assume no convergence, invariance, error bound, or eventual successful stop. -/

noncomputable section
open scoped Classical
universe u v w
namespace Specs.NumAnalysis206.Newton

/-- The exact scalar Newton expression; division is totalized, not a validity certificate. -/
def scalarNewtonType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], (𝕜 → 𝕜) → 𝕜 → 𝕜

def scalarNewtonValue : scalarNewtonType :=
  fun {_𝕜} _ => fun f x => x - f x / deriv f x

/-- The multiplicity-m corrected expression. The multiple-root theorem will supply m ≥ 2. -/
def correctedNewtonType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], ℕ → (𝕜 → 𝕜) → 𝕜 → 𝕜

def correctedNewtonValue : correctedNewtonType :=
  fun {𝕜} _ => fun m f x => x - (m : 𝕜) * f x / deriv f x

/-- The canonical first divided difference on the ordered node-value pairs. -/
def secantSlopeType :=
  ∀ {K : Type u} [Field K], (K → K) → K → K → K

def secantSlopeValue : secantSlopeType :=
  fun {_K} _ => fun f u v => Specs.NumAnalysis206.Approximation.dividedDifferenceValue [(u, f u), (v, f v)]

/-- The raw secant point. Its use away from a root requires distinct nodes and nonzero slope. -/
def secantStepType :=
  ∀ {K : Type u} [Field K], (K → K) → K → K → K

def secantStepValue : secantStepType :=
  fun {_K} _ => fun f u v => v - f v / secantSlopeValue f u v

/-- Absorbing extension of a one-point iteration at a successfully reached root. -/
def stopAtRootType :=
  ∀ {X : Type u} {Y : Type v} [Zero Y], (X → Y) → (X → X) → X → X

def stopAtRootValue : stopAtRootType :=
  fun {_X} {_Y} _ => fun f step x => if f x = 0 then x else step x

/-- Two-point state update, checking either initial point for a root before any secant step. -/
def secantTransitionType :=
  ∀ {K : Type u} [Field K], (K → K) → (K × K) → (K × K)

def secantTransitionValue : secantTransitionType :=
  fun {_K} _ => fun f p => if f p.1 = 0 then (p.1, p.1) else if f p.2 = 0 then (p.2, p.2) else (p.2, secantStepValue f p.1 p.2)

/-- Analytic validity of a scalar non-root step; also applies to corrected Newton. -/
def scalarStepValidType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], (𝕜 → 𝕜) → 𝕜 → Prop

def scalarStepValidValue : scalarStepValidType :=
  fun {𝕜} _ => fun f x => DifferentiableAt 𝕜 f x ∧ deriv f x ≠ 0

/-- Validity of a non-root secant step; repeated nodes are not certified by totalized division. -/
def secantStepValidType :=
  ∀ {K : Type u} [Field K], (K → K) → K → K → Prop

def secantStepValidValue : secantStepValidType :=
  fun {_K} _ => fun f u v => u ≠ v ∧ secantSlopeValue f u v ≠ 0

/-- A secant state either permits a successful stop or has a valid next step. -/
def secantStateValidType :=
  ∀ {K : Type u} [Field K], (K → K) → (K × K) → Prop

def secantStateValidValue : secantStateValidType :=
  fun {_K} _ => fun f p => f p.1 = 0 ∨ f p.2 = 0 ∨ secantStepValidValue f p.1 p.2

/-- An open differentiability domain for a total representative of F : U → Y. No regularity outside U is required. -/
def operatorDomainType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y], (X → Y) → Set X → Prop

def operatorDomainValue : operatorDomainType :=
  fun {𝕜} _ {_X} {_Y} _ _ _ _ _ _ F U => IsOpen U ∧ DifferentiableOn 𝕜 F U

/-- Banach-space Newton over the reals or complexes, using the actual Fréchet derivative and the totalized continuous linear inverse. -/
def operatorNewtonType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y], (X → Y) → X → X

def operatorNewtonValue : operatorNewtonType :=
  fun {𝕜} _ {_X} {_Y} _ _ _ _ _ _ F x => x - (fderiv 𝕜 F x).inverse (F x)

/-- Validity at one used point: domain membership, differentiability and a bounded-isomorphism derivative. This makes no assertion about the next point. -/
def operatorStepValidType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y], (X → Y) → Set X → X → Prop

def operatorStepValidValue : operatorStepValidType :=
  fun {𝕜} _ {_X} {_Y} _ _ _ _ _ _ F U x => x ∈ U ∧ DifferentiableAt 𝕜 F x ∧ (fderiv 𝕜 F x).IsInvertible

/-- Validity for a stopped one-point method: a root requires no further division or inverse. -/
def stoppedStepValidType :=
  ∀ {X : Type u} {Y : Type v} [Zero Y], (X → Y) → (X → Prop) → X → Prop

def stoppedStepValidValue : stoppedStepValidType :=
  fun {_X} {_Y} _ => fun f valid x => f x = 0 ∨ valid x

/-- The exact sequence generated by an update. Domain and denominator validity must be proved separately. -/
def exactIteratesType :=
  ∀ {X : Type u}, (X → X) → X → ℕ → X

def exactIteratesValue : exactIteratesType :=
  fun {_X} => fun step x₀ => Nat.rec x₀ (fun _ x => step x)

/-- Only the initial value and exact recurrence, with no convergence or invariance assumption. -/
def IsExactRunType :=
  ∀ {X : Type u}, (X → X) → X → (ℕ → X) → Prop

def IsExactRunValue : IsExactRunType :=
  fun {_X} => fun step x₀ x => x 0 = x₀ ∧ ∀ n, x (n + 1) = step (x n)

/-- A prefix through x N, including the zero-step run. The sequence after N is unrestricted. -/
def IsExactFiniteRunType :=
  ∀ {X : Type u}, (X → X) → X → ℕ → (ℕ → X) → Prop

def IsExactFiniteRunValue : IsExactFiniteRunType :=
  fun {_X} => fun step x₀ N x => x 0 = x₀ ∧ ∀ n < N, x (n + 1) = step (x n)

/-- Separate per-step validity obligations for an infinite run, not a conclusion about its behavior. -/
def StepsValidType :=
  ∀ {X : Type u}, (X → Prop) → (ℕ → X) → Prop

def StepsValidValue : StepsValidType :=
  fun {_X} => fun valid x => ∀ n, valid (x n)

/-- Only points at which an update is used need a valid step. No derivative at the terminal point is required. -/
def FiniteStepsValidType :=
  ∀ {X : Type u}, (X → Prop) → ℕ → (ℕ → X) → Prop

def FiniteStepsValidValue : FiniteStepsValidType :=
  fun {_X} => fun valid N x => ∀ n < N, valid (x n)

/-- An exact successful stop at the terminal point; this does not assert that any run reaches a root. -/
def SuccessfulRootStopType :=
  ∀ {X : Type u} {Y : Type v} [Zero Y], (X → Y) → ℕ → (ℕ → X) → Prop

def SuccessfulRootStopValue : SuccessfulRootStopType :=
  fun {_X} {_Y} _ => fun f N x => f (x N) = 0

/-- Exact scalar Newton iterates with absorbing root stopping. -/
def scalarNewtonIteratesType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], (𝕜 → 𝕜) → 𝕜 → ℕ → 𝕜

def scalarNewtonIteratesValue : scalarNewtonIteratesType :=
  fun {_𝕜} _ => fun f x₀ => exactIteratesValue (stopAtRootValue f (scalarNewtonValue f)) x₀

/-- Exact multiplicity-corrected iterates with absorbing root stopping. -/
def correctedNewtonIteratesType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], ℕ → (𝕜 → 𝕜) → 𝕜 → ℕ → 𝕜

def correctedNewtonIteratesValue : correctedNewtonIteratesType :=
  fun {_𝕜} _ => fun m f x₀ => exactIteratesValue (stopAtRootValue f (correctedNewtonValue m f)) x₀

/-- Exact secant state sequence from two initial points. A root in either slot is a successful stop. -/
def secantIteratesType :=
  ∀ {K : Type u} [Field K], (K → K) → K → K → ℕ → (K × K)

def secantIteratesValue : secantIteratesType :=
  fun {_K} _ => fun f u v => exactIteratesValue (secantTransitionValue f) (u, v)

/-- Exact Banach Newton sequence with absorbing root stopping. Validity of each used inverse is a separate obligation. -/
def operatorNewtonIteratesType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y], (X → Y) → X → ℕ → X

def operatorNewtonIteratesValue : operatorNewtonIteratesType :=
  fun {𝕜} _ {_X} {_Y} _ _ _ _ _ _ F x₀ => exactIteratesValue (stopAtRootValue F (operatorNewtonValue (𝕜 := 𝕜) F)) x₀

def secantSlopeEqDiv : Prop :=
  ∀ {K : Type u} [Field K], ∀ (f : K → K) (u v : K), secantSlopeValue f u v = (f v - f u) / (v - u)

def stopAtRootOfRoot : Prop :=
  ∀ {X : Type u} {Y : Type v} [Zero Y] (f : X → Y) (step : X → X) (x : X), f x = 0 → stopAtRootValue f step x = x

def stopAtRootOfNonroot : Prop :=
  ∀ {X : Type u} {Y : Type v} [Zero Y] (f : X → Y) (step : X → X) (x : X), f x ≠ 0 → stopAtRootValue f step x = step x

def stoppedStepValidOfNonroot : Prop :=
  ∀ {X : Type u} {Y : Type v} [Zero Y] (f : X → Y) (valid : X → Prop) (x : X), f x ≠ 0 → (stoppedStepValidValue f valid x ↔ valid x)

def secantTransitionOfFirstRoot : Prop :=
  ∀ {K : Type u} [Field K], ∀ (f : K → K) (u v : K), f u = 0 → secantTransitionValue f (u, v) = (u, u)

def secantTransitionOfSecondRoot : Prop :=
  ∀ {K : Type u} [Field K], ∀ (f : K → K) (u v : K), f u ≠ 0 → f v = 0 → secantTransitionValue f (u, v) = (v, v)

def secantTransitionOfNonroots : Prop :=
  ∀ {K : Type u} [Field K], ∀ (f : K → K) (u v : K), f u ≠ 0 → f v ≠ 0 → secantTransitionValue f (u, v) = (v, secantStepValue f u v)

def secantStateValidOfNonroots : Prop :=
  ∀ {K : Type u} [Field K], ∀ (f : K → K) (u v : K), f u ≠ 0 → f v ≠ 0 → (secantStateValidValue f (u, v) ↔ u ≠ v ∧ secantSlopeValue f u v ≠ 0)

def operatorNewtonEqOfHasFDerivAt : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y], ∀ (F : X → Y) (x : X) (e : X ≃L[𝕜] Y), HasFDerivAt F (e : X →L[𝕜] Y) x → operatorNewtonValue (𝕜 := 𝕜) F x = x - e.symm (F x)

def operatorStepValidOfDomain : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y], ∀ (F : X → Y) (U : Set X), operatorDomainValue (𝕜 := 𝕜) F U → ∀ x ∈ U, (fderiv 𝕜 F x).IsInvertible → operatorStepValidValue (𝕜 := 𝕜) F U x

def exactIteratesIsExactRun : Prop :=
  ∀ {X : Type u} (step : X → X) (x₀ : X), IsExactRunValue step x₀ (exactIteratesValue step x₀)

def isExactRunIsExactFiniteRun : Prop :=
  ∀ {X : Type u} (step : X → X) (x₀ : X) (x : ℕ → X), IsExactRunValue step x₀ x → ∀ N, IsExactFiniteRunValue step x₀ N x

def isExactFiniteRunEqIterates : Prop :=
  ∀ {X : Type u} (step : X → X) (x₀ : X) (N : ℕ) (x : ℕ → X), IsExactFiniteRunValue step x₀ N x → ∀ n ≤ N, x n = exactIteratesValue step x₀ n

def exactIteratesAbsorbingAfterRoot : Prop :=
  ∀ {X : Type u} {Y : Type v} [Zero Y] (f : X → Y) (step : X → X) (x₀ : X) (N : ℕ), f (exactIteratesValue (stopAtRootValue f step) x₀ N) = 0 → ∀ k, exactIteratesValue (stopAtRootValue f step) x₀ (N + k) = exactIteratesValue (stopAtRootValue f step) x₀ N

/-- Either slot of a terminal secant state can supply the successful root,
including an initial point before any secant division. -/
def SuccessfulSecantStopType :=
  ∀ {K : Type u} [Field K], (K → K) → ℕ → (ℕ → K × K) → Prop

def SuccessfulSecantStopValue : SuccessfulSecantStopType :=
  fun {_K} _ f N x => f (x N).1 = 0 ∨ f (x N).2 = 0

def scalarNewtonIteratesSucc : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], ∀ (f : 𝕜 → 𝕜) (x₀ : 𝕜) (n : ℕ), scalarNewtonIteratesValue f x₀ (n + 1) = scalarNewtonValue f (scalarNewtonIteratesValue f x₀ n)

def correctedNewtonIteratesSucc : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜], ∀ (m : ℕ) (f : 𝕜 → 𝕜) (x₀ : 𝕜) (n : ℕ), correctedNewtonIteratesValue m f x₀ (n + 1) = correctedNewtonValue m f (correctedNewtonIteratesValue m f x₀ n)

def operatorNewtonIteratesSucc : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y], ∀ (F : X → Y) (x₀ : X) (n : ℕ), operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀ (n + 1) = operatorNewtonValue (𝕜 := 𝕜) F (operatorNewtonIteratesValue (𝕜 := 𝕜) F x₀ n)

end Specs.NumAnalysis206.Newton
