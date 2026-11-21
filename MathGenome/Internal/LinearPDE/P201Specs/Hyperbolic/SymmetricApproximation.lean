import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SymmetricSobolevEnergy

/-! Independent statements for the intermediate solution in the proof of
`thm:pde-symmetric-hs`, paper.tex:4196–4254. We index the source order by
`q + 2`; the source assumptions imply s ≥ 2, so this loses no case.
The paths below take values in the canonical distribution-defined Sobolev
spaces, with their original full derivative-square norms. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace P201Specs.Hyperbolic.SymmetricApproximation
open P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy

/-- Equality of the underlying L² classes across different Sobolev orders. -/
def SameSection {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : WholeH n m 𝕜 a) (w : WholeH n m 𝕜 b) : Prop :=
  ∀ i, hUnderlying ⊤ a (v i) = hUnderlying ⊤ b (w i)

/-- The intermediate PDE class. `u` is continuous in H^(q+1), `w` is
its H^q realization, and `du` is its continuous strong H^q derivative.
Endpoint derivatives are within the closed time interval. The PDE uses the
actual canonical weak spatial derivatives in `pSection`. No energy estimate,
high-order compactness, or pre-existing solution is assumed. -/
def IsIntermediateSolution {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜)
    (f : ℝ → WholeH n m 𝕜 (q + 2))
    (u : ℝ → WholeH n m 𝕜 (q + 1)) (w du : ℝ → WholeH n m 𝕜 q) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧
  ContinuousOn du (Icc 0 T) ∧
  (∀ t ∈ Icc 0 T, SameSection (u t) (w t)) ∧
  (∀ t ∈ Icc 0 T, HasDerivWithinAt w (du t) (Icc 0 T) t) ∧
  ∀ t ∈ Icc 0 T, underlyingSection (du t) =ᵐ[volume]
    fun x => pSection (fun j => A j t) (B t) (u t) x + underlyingSection (f t) x

/-- The complete existence conclusion allocated to this goal, including the
source quantitative bound and weak H^(q+2) continuity. Constants depend only
on n, the source order q+2, and the common coefficient bound K.
`V` is a high-order realization, not a certificate supplied as a premise. -/
def ExistenceStatement : Prop :=
  ∀ (n q : ℕ), 1 ≤ n → n + 2 < 2 * (q + 2) → ∀ K : ℝ, 0 ≤ K →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T (q + 2) K A B →
    ∀ (g : WholeH n m 𝕜 (q + 2)) (f : ℝ → WholeH n m 𝕜 (q + 2)),
    ContinuousOn f (Icc 0 T) →
    ∃ (V : ℝ → WholeH n m 𝕜 (q + 2))
      (u : ℝ → WholeH n m 𝕜 (q + 1)) (w du : ℝ → WholeH n m 𝕜 q),
      IsIntermediateSolution T A B f u w du ∧
      (∀ t ∈ Icc 0 T, SameSection (V t) (u t)) ∧ V 0 = g ∧
      (∀ L : WholeH n m 𝕜 (q + 2) →L[𝕜] 𝕜,
        ContinuousOn (fun t => L (V t)) (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ‖V t‖ ≤ Real.exp (C * t) *
        (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖)

/-- Uniqueness among every intermediate solution, without an assumed high
Sobolev bound or high Sobolev continuity for competing solutions. -/
def UniquenessStatement : Prop :=
  ∀ (n q : ℕ), 1 ≤ n → n + 2 < 2 * (q + 2) → ∀ (K : ℝ), 0 ≤ K →
  ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜] (T : ℝ), 0 ≤ T →
  ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T (q + 2) K A B →
  ∀ (f : ℝ → WholeH n m 𝕜 (q + 2)), ContinuousOn f (Icc 0 T) →
  ∀ (u v : ℝ → WholeH n m 𝕜 (q + 1))
    (w du z dv : ℝ → WholeH n m 𝕜 q),
    IsIntermediateSolution T A B f u w du →
    IsIntermediateSolution T A B f v z dv → u 0 = v 0 → EqOn u v (Icc 0 T)

/-- The source restriction s>n/2+1 implies the nonnegative lower order s-2. -/
def OrderStatement : Prop := ∀ n s : ℕ, 1 ≤ n → n + 2 < 2 * s →
  2 ≤ s ∧ (s - 2) + 2 = s

/-- The weak-compactness step of the construction. Actual high-order
approximants are bounded by `R`, their lower-order realizations converge
pointwise in the lower norm, and that limit is continuous. The resulting
high-order realization has the same bound and is weakly continuous. This
conditional helper does not assert the existence of PDE approximants. -/
def BoundedLimitStatement : Prop :=
  ∀ {n m a b : ℕ} {𝕜 : Type} [RCLike 𝕜] (T : ℝ), 0 ≤ T →
  ∀ (g : WholeH n m 𝕜 a) (z : ℕ → ℝ → WholeH n m 𝕜 a)
    (w : ℕ → ℝ → WholeH n m 𝕜 b) (u : ℝ → WholeH n m 𝕜 b) (R : ℝ → ℝ),
    ContinuousOn u (Icc 0 T) → ContinuousOn R (Icc 0 T) →
    SameSection g (u 0) →
    (∀ i t, t ∈ Icc 0 T → ‖z i t‖ ≤ R t) →
    (∀ i t, t ∈ Icc 0 T → SameSection (z i t) (w i t)) →
    (∀ t ∈ Icc 0 T, Filter.Tendsto (fun i => w i t) Filter.atTop (nhds (u t))) →
    ∃ V : ℝ → WholeH n m 𝕜 a,
      (∀ t ∈ Icc 0 T, SameSection (V t) (u t)) ∧ V 0 = g ∧
      (∀ t ∈ Icc 0 T, ‖V t‖ ≤ R t) ∧
      ∀ L : WholeH n m 𝕜 a →L[𝕜] 𝕜, ContinuousOn (fun t => L (V t)) (Icc 0 T)

/-- Adjacent-order interpolation for the manuscript's full derivative-square
norm. The constant depends only on dimension and Sobolev order, and the three
realizations are identified by their canonical underlying L² sections. -/
def InterpolationStatement : Prop :=
  ∀ {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH n m 𝕜 (q + 2)) (v : WholeH n m 𝕜 (q + 1))
    (w : WholeH n m 𝕜 q), SameSection u v → SameSection v w →
    ‖v‖ ^ 2 ≤ (Fintype.card (P102.U4.SobolevIndex n (q + 1)) : ℝ) * (‖w‖ * ‖u‖)

end P201Specs.Hyperbolic.SymmetricApproximation
