import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Independent operator and jet interfaces for paper.tex:107–135,157–170.
The quadratic classification proposition is allocated separately.
Multiset multiplicities are the usual multi-index components. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace P201Specs.Operators
open P201Specs

abbrev Index (n m : ℕ) := P102.U4.SobolevIndex n m
abbrev multiIndexOrder {n : ℕ} (α : MultiIndex n) : ℕ := α.card
abbrev Coefficients (n m : ℕ) := Index n m → Space n → ℂ

/-- Exact order is witnessed somewhere in the open domain, as in the source.
No regularity of the coefficients is required by these pointwise definitions. -/
structure ScalarOperator {n : ℕ} (Ω : Domain n) (m : ℕ) where
  coefficients : Coefficients n m
  exactOrder : ∃ α : Index n m, α.val.card = m ∧ ∃ x ∈ Ω, coefficients α x ≠ 0

abbrev operatorOrder {n m : ℕ} {Ω : Domain n} (_L : ScalarOperator Ω m) := m

def applyOperator {n m : ℕ} (a : Coefficients n m) (u : Space n → ℂ)
    (x : Space n) : ℂ := ∑ α : Index n m, a α x * multiPartial u α.val x

/-- The prescribed source is separate from the linear operator. -/
def LinearEquation {n m : ℕ} (Ω : Domain n) (a : Coefficients n m)
    (f u : Space n → ℂ) : Prop := ∀ x ∈ Ω, applyOperator a u x = f x

def symbolMonomial {n : ℕ} (α : MultiIndex n) (ξ : Space n) : ℂ :=
  (α.map (fun i => Complex.I * (ξ i : ℂ))).prod

def fullSymbol {n m : ℕ} (a : Coefficients n m) (x ξ : Space n) : ℂ :=
  ∑ α : Index n m, a α x * symbolMonomial α.val ξ

def homogeneousSymbol {n m : ℕ} (a : Coefficients n m) (k : ℕ)
    (x ξ : Space n) : ℂ :=
  ∑ α : Index n m, if α.val.card = k then a α x * symbolMonomial α.val ξ else 0

def principalSymbol {n m : ℕ} (a : Coefficients n m) (x ξ : Space n) : ℂ :=
  homogeneousSymbol a m x ξ

def planeWave {n : ℕ} (ξ x : Space n) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ x ξ : ℝ))

/-- Scalar ellipticity is pointwise on the domain, at every nonzero real covector. -/
def IsElliptic {n m : ℕ} (Ω : Domain n) (a : Coefficients n m) : Prop :=
  ∀ x ∈ Ω, ∀ ξ : Space n, ξ ≠ 0 → principalSymbol a x ξ ≠ 0

def quadraticPrincipal {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Space n) : ℝ :=
  ∑ i, ∑ j, a i j * ξ i * ξ j

def UniformPositiveEllipticity {n : ℕ} (Ω : Domain n)
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ ∀ x ∈ Ω, ∀ ξ : Space n,
    θ * ‖ξ‖ ^ 2 ≤ quadraticPrincipal (a x) ξ

/-- Full constant-coefficient Fourier multiplier in the manuscript's 2π convention. -/
def fourierSymbol {n m : ℕ} (a : Index n m → ℂ) (ξ : Space n) : ℂ :=
  fullSymbol (fun α _ => a α) 0 ((2 * Real.pi) • ξ)

def fourierPrincipalSymbol {n m : ℕ} (a : Index n m → ℂ) (ξ : Space n) : ℂ :=
  principalSymbol (fun α _ => a α) 0 ((2 * Real.pi) • ξ)

/-- Repeated derivatives on Schwartz space, in the same sorted coordinate order
as the shared unbundled multiPartial. -/
def schwartzWord {n : ℕ} : List (Fin n) → SchwartzMap (Space n) ℂ → SchwartzMap (Space n) ℂ
  | [], f => f
  | i :: l, f => LineDeriv.lineDerivOp (coordinate n i) (schwartzWord l f)

def schwartzPartial {n : ℕ} (α : MultiIndex n) (f : SchwartzMap (Space n) ℂ) :=
  schwartzWord (α.sort (· ≤ ·)) f

def constantSchwartzOperator {n m : ℕ} (a : Index n m → ℂ)
    (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  ∑ α : Index n m, a α • schwartzPartial α.val f

/-- Lower and highest jets for an arbitrary order m. -/
abbrev LowerJet (n m : ℕ) := {α : MultiIndex n // α.card < m} → ℝ
abbrev HighestJet (n m : ℕ) := {α : MultiIndex n // α.card = m} → ℝ

def lowerJet {n : ℕ} (m : ℕ) (u : Space n → ℝ) (x : Space n) : LowerJet n m :=
  fun α => multiPartial u α.val x

def highestJet {n : ℕ} (m : ℕ) (u : Space n → ℝ) (x : Space n) : HighestJet n m :=
  fun α => multiPartial u α.val x

/-- An equation on chosen lower and highest jet spaces, with prescribed source. -/
def JetEquation {X W E : Type} (F : X → W → E → ℝ) (f : X → ℝ)
    (w : X → W) (h : X → E) : Prop := ∀ x, F x (w x) (h x) = f x

/-- Dependence predicates work on lower/highest jet spaces W,E. In particular
W=LowerJet n m and E=HighestJet n m gives the general scalar order-m definition.
An equation F(x,w,h)=f(x) has a prescribed source f. -/
def LinearJetDependence {X W E : Type} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup E] [Module ℝ E] (F : X → W → E → ℝ) : Prop :=
  ∃ a : X → (W × E →ₗ[ℝ] ℝ), ∀ x w h, F x w h = a x (w, h)

def SemilinearJetDependence {X W E : Type} [AddCommGroup E] [Module ℝ E]
    (F : X → W → E → ℝ) : Prop :=
  ∃ a : X → (E →ₗ[ℝ] ℝ), ∃ b : X → W → ℝ,
    ∀ x w h, F x w h = a x h + b x w

def QuasilinearJetDependence {X W E : Type} [AddCommGroup E] [Module ℝ E]
    (F : X → W → E → ℝ) : Prop :=
  ∃ a : X → W → (E →ₗ[ℝ] ℝ), ∃ b : X → W → ℝ,
    ∀ x w h, F x w h = a x w h + b x w

/-- A genuinely nonlinear dependence on the highest jet cannot have the
quasilinear representation. The broader allowed fully nonlinear class consists
of arbitrary functions of all jets. -/
def FullyNonlinearJetDependence {X W E : Type} [AddCommGroup E] [Module ℝ E]
    (F : X → W → E → ℝ) : Prop := ¬ QuasilinearJetDependence F

/-- Value and gradient form the lower jet for a second-order scalar equation.
The Hessian matrix gives its highest jet; actual smooth Hessians are symmetric,
while these algebraic formulas extend to all matrices. -/
abbrev SecondLowerJet (n : ℕ) := ℝ × Space n

def hessian {n : ℕ} (u : Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => multiPartial u ({i, j} : MultiIndex n) x

def semilinearExample (n : ℕ) (_x : Space n) (w : SecondLowerJet n)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ := Matrix.trace H + w.1 ^ 3

def quasilinearExample (n : ℕ) (_x : Space n) (w : SecondLowerJet n)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ := (1 + w.1 ^ 2) * Matrix.trace H

def mongeAmpereExample (n : ℕ) (_x : Space n) (_w : SecondLowerJet n)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ := H.det - 1

/-- c>0 is the speed hypothesis in wave model applications. -/
def waveQuadratic {n : ℕ} (c τ : ℝ) (ξ : Space n) : ℝ := τ ^ 2 - c ^ 2 * ‖ξ‖ ^ 2

def waveOperator {n : ℕ} (c : ℝ) (u : ℝ → Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  deriv (fun s => deriv (fun r => u r x) s) t - c ^ 2 * laplacian (u t) x

/-- Positive diffusion κ>0, with the chosen first-order time derivative. -/
def heatOperator {n : ℕ} (κ : ℝ) (u : ℝ → Space n → ℝ) (t : ℝ) (x : Space n) : ℝ :=
  deriv (fun s => u s x) t - κ * laplacian (u t) x

def heatQuadratic {n : ℕ} (κ _τ : ℝ) (ξ : Space n) : ℝ := -κ * ‖ξ‖ ^ 2

/-- A forward heat evolution specifies positive spatial diffusion, in addition
to the first-order time realization above. A null time quadratic direction alone
is not this predicate. -/
def IsForwardHeat (κ : ℝ) : Prop := 0 < κ

-- Independent theorem obligations.
def symbolMonomialCountsStatement : Prop := ∀ {n : ℕ} (α : MultiIndex n) (ξ : Space n),
  symbolMonomial α ξ = ∏ i : Fin n, (Complex.I * (ξ i : ℂ)) ^ α.count i

def linearIsSemilinearStatement : Prop := ∀ {X W E : Type} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup E] [Module ℝ E] (F : X → W → E → ℝ),
  LinearJetDependence F → SemilinearJetDependence F

def heatUniformEllipticityStatement : Prop := ∀ {n : ℕ} (Ω : Domain n) (κ : ℝ),
  IsForwardHeat κ → UniformPositiveEllipticity Ω (fun _ => κ • (1 : Matrix (Fin n) (Fin n) ℝ))

def heatDegeneracyInsufficientStatement : Prop := ∀ n : ℕ,
  heatQuadratic (-1) 1 (0 : Space n) = 0 ∧ ¬ IsForwardHeat (-1)

def multiIndexCountsStatement : Prop := ∀ {n : ℕ} (α : MultiIndex n),
  multiIndexOrder α = ∑ i : Fin n, α.count i

def planeWaveDerivativeStatement : Prop := ∀ {n : ℕ} (α : MultiIndex n) (ξ x : Space n),
  multiPartial (planeWave ξ) α x = symbolMonomial α ξ * planeWave ξ x

def exponentialSubstitutionStatement : Prop := ∀ {n m : ℕ} (a : Coefficients n m) (x ξ : Space n),
  Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * applyOperator a (planeWave ξ) x =
    fullSymbol a x ξ

def homogeneousSymbolStatement : Prop := ∀ {n m : ℕ} (a : Coefficients n m)
    (k : ℕ) (r : ℝ) (x ξ : Space n),
  homogeneousSymbol a k x (r • ξ) = (r : ℂ) ^ k * homogeneousSymbol a k x ξ

def symbolDecompositionStatement : Prop := ∀ {n m : ℕ} (a : Coefficients n m) (x ξ : Space n),
  fullSymbol a x ξ = ∑ k ∈ Finset.range (m + 1), homogeneousSymbol a k x ξ

def principalHomogeneousStatement : Prop := ∀ {n m : ℕ} (a : Coefficients n m)
    (r : ℝ) (x ξ : Space n),
  principalSymbol a x (r • ξ) = (r : ℂ) ^ m * principalSymbol a x ξ

def schwartzPartialStatement : Prop := ∀ {n : ℕ} (α : MultiIndex n)
    (f : SchwartzMap (Space n) ℂ) (x : Space n),
  schwartzPartial α f x = multiPartial f α x

def constantSchwartzOperatorStatement : Prop := ∀ {n m : ℕ} (a : Index n m → ℂ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n),
  constantSchwartzOperator a f x = applyOperator (fun α _ => a α) f x

def fourierMultiplierStatement : Prop := ∀ {n m : ℕ} (a : Index n m → ℂ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n),
  (FourierTransform.fourierCLM ℂ (SchwartzMap (Space n) ℂ)) (constantSchwartzOperator a f) ξ =
    fourierSymbol a ξ * (FourierTransform.fourierCLM ℂ (SchwartzMap (Space n) ℂ)) f ξ

def fourierIntegralMultiplierStatement : Prop := ∀ {n m : ℕ} (a : Index n m → ℂ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n),
  fourierIntegral (constantSchwartzOperator a f) ξ = fourierSymbol a ξ * fourierIntegral f ξ

def fourierPrincipalStatement : Prop := ∀ {n m : ℕ} (a : Index n m → ℂ) (ξ : Space n),
  fourierPrincipalSymbol a ξ = (2 * Real.pi : ℂ) ^ m * principalSymbol (fun α _ => a α) 0 ξ

def semilinearIsQuasilinearStatement : Prop := ∀ {X W E : Type} [AddCommGroup E] [Module ℝ E]
  (F : X → W → E → ℝ), SemilinearJetDependence F → QuasilinearJetDependence F

def semilinearExampleStatement : Prop := ∀ n, SemilinearJetDependence (semilinearExample n)
def quasilinearExampleStatement : Prop := ∀ n, QuasilinearJetDependence (quasilinearExample n)
def mongeAmpereExampleStatement : Prop := ∀ n, 2 ≤ n → FullyNonlinearJetDependence (mongeAmpereExample n)

def exampleRealizationsStatement : Prop := ∀ {n : ℕ} (u : Space n → ℝ) (x : Space n),
  semilinearExample n x (u x, gradient u x) (hessian u x) = laplacian u x + u x ^ 3 ∧
  quasilinearExample n x (u x, gradient u x) (hessian u x) = (1 + u x ^ 2) * laplacian u x ∧
  (mongeAmpereExample n x (u x, gradient u x) (hessian u x) = 0 ↔ (hessian u x).det = 1)

def heatDegenerateStatement : Prop := ∀ {n : ℕ} (κ τ : ℝ), heatQuadratic κ τ (0 : Space n) = 0

def heatDiffusionStatement : Prop := ∀ {n : ℕ} (κ : ℝ), IsForwardHeat κ →
  ∀ ξ : Space n, κ * ‖ξ‖ ^ 2 = -heatQuadratic κ 0 ξ

-- Independent expected types; the canonical values above are also the expected values.
def IndexType := Nat → Nat → Type

def multiIndexOrderType := {n : Nat} → P201Specs.MultiIndex n → Nat

def CoefficientsType := Nat → Nat → Type

def ScalarOperatorType := {n : Nat} → P201Specs.Domain n → Nat → Type

def operatorOrderType := {n m : Nat} → {Ω : P201Specs.Domain n} → P201Specs.Operators.ScalarOperator Ω m → Nat

def applyOperatorType := {n m : Nat} → P201Specs.Operators.Coefficients n m → (P201Specs.Space n → Complex) → P201Specs.Space n → Complex

def LinearEquationType := {n m : Nat} →
  P201Specs.Domain n →
    P201Specs.Operators.Coefficients n m → (P201Specs.Space n → Complex) → (P201Specs.Space n → Complex) → Prop

def symbolMonomialType := {n : Nat} → P201Specs.MultiIndex n → P201Specs.Space n → Complex

def fullSymbolType := {n m : Nat} → P201Specs.Operators.Coefficients n m → P201Specs.Space n → P201Specs.Space n → Complex

def homogeneousSymbolType := {n m : Nat} → P201Specs.Operators.Coefficients n m → Nat → P201Specs.Space n → P201Specs.Space n → Complex

def principalSymbolType := {n m : Nat} → P201Specs.Operators.Coefficients n m → P201Specs.Space n → P201Specs.Space n → Complex

def planeWaveType := {n : Nat} → P201Specs.Space n → P201Specs.Space n → Complex

def IsEllipticType := {n m : Nat} → P201Specs.Domain n → P201Specs.Operators.Coefficients n m → Prop

def quadraticPrincipalType := {n : Nat} → Matrix (Fin n) (Fin n) Real → P201Specs.Space n → Real

def UniformPositiveEllipticityType := {n : Nat} → P201Specs.Domain n → (P201Specs.Space n → Matrix (Fin n) (Fin n) Real) → Prop

def fourierSymbolType := {n m : Nat} → (P201Specs.Operators.Index n m → Complex) → P201Specs.Space n → Complex

def fourierPrincipalSymbolType := {n m : Nat} → (P201Specs.Operators.Index n m → Complex) → P201Specs.Space n → Complex

def schwartzWordType := {n : Nat} → List (Fin n) → SchwartzMap (P201Specs.Space n) Complex → SchwartzMap (P201Specs.Space n) Complex

def schwartzPartialType := {n : Nat} → P201Specs.MultiIndex n → SchwartzMap (P201Specs.Space n) Complex → SchwartzMap (P201Specs.Space n) Complex

def constantSchwartzOperatorType := {n m : Nat} →
  (P201Specs.Operators.Index n m → Complex) →
    SchwartzMap (P201Specs.Space n) Complex → SchwartzMap (P201Specs.Space n) Complex

def LowerJetType := Nat → Nat → Type

def HighestJetType := Nat → Nat → Type

def lowerJetType := {n : Nat} → (m : Nat) → (P201Specs.Space n → Real) → P201Specs.Space n → P201Specs.Operators.LowerJet n m

def highestJetType := {n : Nat} → (m : Nat) → (P201Specs.Space n → Real) → P201Specs.Space n → P201Specs.Operators.HighestJet n m

def JetEquationType := {X W E : Type} → (X → W → E → Real) → (X → Real) → (X → W) → (X → E) → Prop

def LinearJetDependenceType := {X W E : Type} →
  [_inst : AddCommGroup W] → [Module Real W] → [_inst : AddCommGroup E] → [Module Real E] → (X → W → E → Real) → Prop

def SemilinearJetDependenceType := {X W E : Type} → [_inst : AddCommGroup E] → [Module Real E] → (X → W → E → Real) → Prop

def QuasilinearJetDependenceType := {X W E : Type} → [_inst : AddCommGroup E] → [Module Real E] → (X → W → E → Real) → Prop

def FullyNonlinearJetDependenceType := {X W E : Type} → [_inst : AddCommGroup E] → [Module Real E] → (X → W → E → Real) → Prop

def SecondLowerJetType := Nat → Type

def hessianType := {n : Nat} → (P201Specs.Space n → Real) → P201Specs.Space n → Matrix (Fin n) (Fin n) Real

def semilinearExampleType := (n : Nat) → P201Specs.Space n → P201Specs.Operators.SecondLowerJet n → Matrix (Fin n) (Fin n) Real → Real

def quasilinearExampleType := (n : Nat) → P201Specs.Space n → P201Specs.Operators.SecondLowerJet n → Matrix (Fin n) (Fin n) Real → Real

def mongeAmpereExampleType := (n : Nat) → P201Specs.Space n → P201Specs.Operators.SecondLowerJet n → Matrix (Fin n) (Fin n) Real → Real

def waveQuadraticType := {n : Nat} → Real → Real → P201Specs.Space n → Real

def waveOperatorType := {n : Nat} → Real → (Real → P201Specs.Space n → Real) → Real → P201Specs.Space n → Real

def heatOperatorType := {n : Nat} → Real → (Real → P201Specs.Space n → Real) → Real → P201Specs.Space n → Real

def heatQuadraticType := {n : Nat} → Real → Real → P201Specs.Space n → Real

def IsForwardHeatType := Real → Prop

def ScalarOperatorValue : ScalarOperatorType := @ScalarOperator

end P201Specs.Operators
