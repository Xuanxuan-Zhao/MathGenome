import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SymmetricApproximation

/-! Independent statements for `thm:pde-symmetric-hs`, paper.tex:4151–4171
and 4256–4279. As in the intermediate interface, the source integer s is
indexed by q+2. The inequalities n≥1 and n+2<2s imply s≥2, so this indexing
covers every source order. The Hilbert norm is the full derivative-square
norm already fixed by `WholeH`, with a finite Euclidean vector fiber.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace P201Specs.Hyperbolic.SymmetricWellPosed
open P201Specs.Hyperbolic.SymmetricEnergy
open P201Specs.Hyperbolic.SymmetricSobolevEnergy
open P201Specs.Hyperbolic.SymmetricApproximation

/-- A strong solution, expressed using its two canonical Sobolev realizations.
U is strongly continuous in H^s; u and its strong derivative du are strongly
continuous in H^(s-1). The PDE is equality of actual a.e. spatial sections.
Within derivatives include both one-sided endpoints. No energy estimate,
existence certificate, or weak-to-strong implication is assumed here. -/
def IsStrongSolution {n m q : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜)
    (f U : ℝ → WholeH n m 𝕜 (q + 2))
    (u du : ℝ → WholeH n m 𝕜 (q + 1)) : Prop :=
  ContinuousOn U (Icc 0 T) ∧ ContinuousOn u (Icc 0 T) ∧
  ContinuousOn du (Icc 0 T) ∧
  (∀ t ∈ Icc 0 T, SameSection (U t) (u t)) ∧
  (∀ t ∈ Icc 0 T, HasDerivWithinAt u (du t) (Icc 0 T) t) ∧
  ∀ t ∈ Icc 0 T, underlyingSection (du t) =ᵐ[volume]
    fun x => pSection (fun j => A j t) (B t) (U t) x + underlyingSection (f t) x

/-- Existence in the full source class and its quantitative H^s bound.
C depends only on n,s,K; in particular it is independent of T, the fiber
dimension, the scalar field, the coefficient family, and the data. -/
def ExistenceStatement : Prop :=
  ∀ (n q : ℕ), 1 ≤ n → n + 2 < 2 * (q + 2) → ∀ K : ℝ, 0 ≤ K →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T (q + 2) K A B →
    ∀ (g : WholeH n m 𝕜 (q + 2)) (f : ℝ → WholeH n m 𝕜 (q + 2)),
    ContinuousOn f (Icc 0 T) →
    ∃ (U : ℝ → WholeH n m 𝕜 (q + 2))
      (u du : ℝ → WholeH n m 𝕜 (q + 1)),
      IsStrongSolution T A B f U u du ∧ U 0 = g ∧
      ∀ t ∈ Icc 0 T, ‖U t‖ ≤ Real.exp (C * t) *
        (‖g‖ + ∫ r in (0 : ℝ)..t, ‖f r‖)

/-- Uniqueness among all solutions of the full strong class, without an
energy estimate as a premise on competitors. -/
def UniquenessStatement : Prop :=
  ∀ (n q : ℕ), 1 ≤ n → n + 2 < 2 * (q + 2) → ∀ K : ℝ, 0 ≤ K →
  ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜] (T : ℝ), 0 ≤ T →
  ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T (q + 2) K A B →
  ∀ (f : ℝ → WholeH n m 𝕜 (q + 2)), ContinuousOn f (Icc 0 T) →
  ∀ (U V : ℝ → WholeH n m 𝕜 (q + 2))
    (u du v dv : ℝ → WholeH n m 𝕜 (q + 1)),
    IsStrongSolution T A B f U u du →
    IsStrongSolution T A B f V v dv → U 0 = V 0 → EqOn U V (Icc 0 T)

/-- Full H^s difference estimate, giving continuous dependence with the same
coefficient dependence as the source bound. It applies to every strong
solution, and the source term is the norm of the difference of the forcing. -/
def DifferenceStatement : Prop :=
  ∀ (n q : ℕ), 1 ≤ n → n + 2 < 2 * (q + 2) → ∀ K : ℝ, 0 ≤ K →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
    CoefficientHypotheses T (q + 2) K A B →
    ∀ (f g U V : ℝ → WholeH n m 𝕜 (q + 2))
      (u du v dv : ℝ → WholeH n m 𝕜 (q + 1)),
      ContinuousOn f (Icc 0 T) → ContinuousOn g (Icc 0 T) →
      IsStrongSolution T A B f U u du → IsStrongSolution T A B g V v dv →
      ∀ t ∈ Icc 0 T, ‖U t - V t‖ ≤ Real.exp (C * t) *
        (‖U 0 - V 0‖ + ∫ r in (0 : ℝ)..t, ‖f r - g r‖)

end P201Specs.Hyperbolic.SymmetricWellPosed
