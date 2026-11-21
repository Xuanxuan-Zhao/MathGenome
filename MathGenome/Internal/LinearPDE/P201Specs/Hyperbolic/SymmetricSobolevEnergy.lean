import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SymmetricEnergy

/-! Independent interfaces for the high-order part of thm:pde-symmetric-hs.
The finite fiber uses the Euclidean norm. Each scalar component uses the
canonical distribution-defined H space, with the full derivative-square norm.
No multiplier estimate, commutator estimate or time continuity is a field of
coefficient data. Bounds on time derivatives are deliberately absent.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff
namespace P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricEnergy

abbrev WholeH (n m : ℕ) (𝕜 : Type) [RCLike 𝕜] (k : ℕ) :=
  PiLp 2 (fun _ : Fin m => H 𝕜 (⊤ : Domain n) k)

/-- A derivative coordinate of the genuine weak-derivative tuple, with the
finite fiber assembled in the Euclidean norm. -/
def derivativeSection {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 k) (α : P102.U4.SobolevIndex n k) : Space n → Fiber 𝕜 m :=
  fun x => WithLp.toLp 2 (fun i =>
    P102.U4.sobolevDerivative (hToW 𝕜 ⊤ k (v i)) α x)

/-- The zero-order a.e. representative; all equalities of sections below are
almost everywhere, so they do not depend on choices of Lp representatives. -/
def underlyingSection {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 k) : Space n → Fiber 𝕜 m :=
  derivativeSection v (P102.U4.zeroSobolevIndex n k)

/-- Coordinate derivatives for arbitrary Banach-valued coefficients. The same
sorted coordinate-word convention is used by the shared scalar derivative. -/
def spatialWord {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Space n → E) : List (Fin n) → Space n → E
  | [] => a
  | j :: l => fun x => fderiv ℝ (spatialWord a l) x (coordinate n j)

def spatialPartial {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Space n → E) (α : MultiIndex n) : Space n → E :=
  spatialWord a (α.sort (· ≤ ·))

/-- One common upper bound for the spatial derivatives, INCLUDING zero, on the
closed time slab. There are no uniform bounds on time derivatives. -/
def BoundedSmoothCoefficient {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (s : ℕ) (K : ℝ) (a : LowerOrder n m 𝕜) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry a) (slab n T) ∧
  ∀ (α : MultiIndex n), α.card ≤ s → ∀ t ∈ Icc 0 T, ∀ x,
    ‖spatialPartial (a t) α x‖ ≤ K

def CoefficientHypotheses {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (s : ℕ) (K : ℝ) (A : Principal n m 𝕜)
    (B : LowerOrder n m 𝕜) : Prop :=
  (∀ j, BoundedSmoothCoefficient T s K (A j)) ∧
  BoundedSmoothCoefficient T s K B ∧
  ∀ j, ∀ t ∈ Icc 0 T, ∀ x, IsSelfAdjoint (A j t x)

/-- The bounded multiplier must be the actual pointwise coefficient action. -/
def RealizesMultiplier {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : Space n → Operator m 𝕜)
    (M : WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k) : Prop :=
  ∀ v, underlyingSection (M v) =ᵐ[volume] fun x => a x (underlyingSection v x)

/-- P=-Σ Aʲ∂ʲ-B. The derivative coordinates on the right are the canonical
weak first derivatives, not extra assumed differentiability certificates. -/
def pSection {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → Space n → Operator m 𝕜) (B : Space n → Operator m 𝕜)
    (v : WholeH n m 𝕜 (k + 1)) : Space n → Fiber 𝕜 m :=
  fun x => -(∑ j, A j x
    (derivativeSection v ⟨{j}, by simp⟩ x)) - B x (underlyingSection v x)

def RealizesP {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Fin n → Space n → Operator m 𝕜) (B : Space n → Operator m 𝕜)
    (Q : WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k) : Prop :=
  ∀ v, underlyingSection (Q v) =ᵐ[volume] pSection A B v

/-- The usual Sobolev inclusion is identified by its underlying a.e. section. -/
def IsLowerOrder {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 (k + 1)) (w : WholeH n m 𝕜 k) : Prop :=
  ∀ i : Fin m, hUnderlying ⊤ (k + 1) (v i) = hUnderlying ⊤ k (w i)

/-- Constants are quantified before the coefficient family, time length,
finite fiber dimension and scalar field, so they depend only on n,s,K. -/
def MultiplierStatement : Prop :=
  ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ a : LowerOrder n m 𝕜,
    BoundedSmoothCoefficient T s K a → ∀ k ≤ s,
    ∃ M : ℝ → WholeH n m 𝕜 k →L[𝕜] WholeH n m 𝕜 k,
      (∀ t ∈ Icc 0 T, RealizesMultiplier (a t) (M t) ∧ ‖M t‖ ≤ C) ∧
      ∀ v, ContinuousOn (fun t => M t v) (Icc 0 T)

def OperatorStatement : Prop :=
  ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T s K A B → ∀ k < s,
    ∃ Q : ℝ → WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k,
      (∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t) ∧ ‖Q t‖ ≤ C) ∧
      ∀ v, ContinuousOn (fun t => Q t v) (Icc 0 T)

/-- k=s uses P:H^(s+1)→H^s, which is also defined by the multiplier
estimate at level s. Only its energy bound is needed at this level. -/
def PairingStatement : Prop :=
  ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T s K A B → ∀ k ≤ s,
    ∃ Q : ℝ → WholeH n m 𝕜 (k + 1) →L[𝕜] WholeH n m 𝕜 k,
      (∀ t ∈ Icc 0 T, RealizesP (fun j => A j t) (B t) (Q t)) ∧
      ∀ t ∈ Icc 0 T, ∀ (v : WholeH n m 𝕜 (k + 1)) (w : WholeH n m 𝕜 k),
        IsLowerOrder v w → |RCLike.re (inner 𝕜 w (Q t v))| ≤ C * ‖w‖ ^ 2


/-- A sufficiently regular solution has a strong H^k derivative and values
which lift to H^(k+1). The equation is an a.e. equality of actual sections.
The high-regularity lift is not assumed to satisfy an energy inequality. -/
def IsRegularSolution {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜)
    (u du f : ℝ → WholeH n m 𝕜 k) (V : ℝ → WholeH n m 𝕜 (k + 1)) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ContinuousOn du (Icc 0 T) ∧
  ContinuousOn f (Icc 0 T) ∧
  (∀ t ∈ Ioo 0 T, HasDerivAt u (du t) t) ∧
  (∀ t ∈ Icc 0 T, IsLowerOrder (V t) (u t)) ∧
  ∀ t ∈ Icc 0 T,
    underlyingSection (du t - f t) =ᵐ[volume] pSection (fun j => A j t) (B t) (V t)

/-- The same quantitative constant works for all sufficiently regular
solutions and differences, for all 0≤k≤s. In particular k=s is the
source estimate. The constants precede m,T,A,B,u,f in the quantifiers. -/
def EvolutionStatement : Prop :=
  ∀ (n s : ℕ), 1 ≤ n → n + 2 < 2 * s → ∀ K : ℝ, 0 ≤ K →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T s K A B → ∀ k ≤ s,
    (∀ (u du f : ℝ → WholeH n m 𝕜 k) (V : ℝ → WholeH n m 𝕜 (k + 1)),
      IsRegularSolution T A B u du f V → ∀ t ∈ Icc 0 T,
        ‖u t‖ ≤ Real.exp (C * t) *
          (‖u 0‖ + ∫ r in (0 : ℝ)..t, ‖f r‖)) ∧
    (∀ (u du f v dv g : ℝ → WholeH n m 𝕜 k)
      (U V : ℝ → WholeH n m 𝕜 (k + 1)),
      IsRegularSolution T A B u du f U → IsRegularSolution T A B v dv g V →
      ∀ t ∈ Icc 0 T,
        ‖u t - v t‖ ≤ Real.exp (C * t) *
          (‖u 0 - v 0‖ + ∫ r in (0 : ℝ)..t, ‖f r - g r‖))

/-- An explicit reduction, with the spatial pairing bound as a separate
premise. Binding this helper does not assert PairingStatement. -/
def EvolutionOfPairingStatement : Prop := PairingStatement → EvolutionStatement

/-- Abstract Hilbert comparison used after the spatial pairing estimate.
This is a consequence, not a substitute for proving the PDE pairing bound.
A complex Hilbert space can be regarded as a real Hilbert space here. -/
def HilbertComparisonStatement : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (T C : ℝ) (u du f : ℝ → X), 0 ≤ T → 0 ≤ C →
    ContinuousOn u (Icc 0 T) → ContinuousOn du (Icc 0 T) →
    ContinuousOn f (Icc 0 T) →
    (∀ t ∈ Ioo 0 T, HasDerivAt u (du t) t) →
    (∀ t ∈ Icc 0 T, inner ℝ (u t) (du t) ≤ C * ‖u t‖ ^ 2 + ‖u t‖ * ‖f t‖) →
    ‖u T‖ ≤ Real.exp (C * T) * (‖u 0‖ + ∫ t in (0 : ℝ)..T, ‖f t‖)

/-- The exact norm of the vector space: every multi-index occurs once and
all finite fiber components are summed with the Euclidean square norm. -/
def FullNormStatement : Prop :=
  ∀ {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (v : WholeH n m 𝕜 k),
    ‖v‖ ^ 2 = ∑ α : P102.U4.SobolevIndex n k, ∑ i : Fin m,
      ‖P102.U4.sobolevDerivative (hToW 𝕜 ⊤ k (v i)) α‖ ^ 2

/-- This is the manuscript's vector L² derivative norm, rather than just a
componentwise equivalent norm. Spatial integrability is part of the conclusion. -/
def SectionNormStatement : Prop :=
  ∀ {n m k : ℕ} {𝕜 : Type} [RCLike 𝕜] (v : WholeH n m 𝕜 k),
    (∀ α : P102.U4.SobolevIndex n k, MemLp (derivativeSection v α) 2 volume) ∧
    ‖v‖ ^ 2 = ∑ α : P102.U4.SobolevIndex n k, lpNorm (derivativeSection v α) 2 volume ^ 2

end P201Specs.Hyperbolic.SymmetricSobolevEnergy
