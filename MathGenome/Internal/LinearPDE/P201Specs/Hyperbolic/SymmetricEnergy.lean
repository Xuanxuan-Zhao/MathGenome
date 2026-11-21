import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Independent statements for paper.tex, Theorem thm:pde-symmetric-energy,
lines 4090–4141 of the adopted source. Operators on finite-dimensional
Euclidean spaces represent the real/complex matrices with their operator
norms. No boundedness of the principal operators themselves, global energy
bound, or global flux integrability is part of the hypotheses.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff
namespace P201Specs.Hyperbolic.SymmetricEnergy

abbrev Fiber (𝕜 : Type) [RCLike 𝕜] (m : ℕ) := EuclideanSpace 𝕜 (Fin m)
abbrev Field (n m : ℕ) (𝕜 : Type) [RCLike 𝕜] := ℝ → Space n → Fiber 𝕜 m
abbrev Operator (m : ℕ) (𝕜 : Type) [RCLike 𝕜] := Fiber 𝕜 m →L[𝕜] Fiber 𝕜 m
abbrev Principal (n m : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  Fin n → ℝ → Space n → Operator m 𝕜
abbrev LowerOrder (n m : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  ℝ → Space n → Operator m 𝕜

def slab (n : ℕ) (T : ℝ) : Set (ℝ × Space n) := Icc 0 T ×ˢ univ

/-- The scalar norm of an actual section; finiteness is always asserted
separately by `MemLp`, so the totalized real value cannot assert integrability. -/
def l2Norm {n m : ℕ} {𝕜 : Type} [RCLike 𝕜] (v : Space n → Fiber 𝕜 m) : ℝ :=
  lpNorm v 2 volume

/-- Actual Bochner L¹(0,T;L²) forcing, with its spatial a.e. representative.
Exceptional time sections need not themselves belong to L². -/
def HasL1L2Source {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (f : Field n m 𝕜) : Prop :=
  ∃ F : ℝ → MeasureTheory.Lp (Fiber 𝕜 m) 2 (volume : Measure (Space n)),
    IntegrableOn F (Ioo 0 T) ∧
      ∀ᵐ s ∂volume.restrict (Ioo 0 T), f s =ᵐ[volume] (F s : Space n → Fiber 𝕜 m)

/-- C¹ and bounded first derivatives on the closed slab; the derivative is
relative to that slab at the time endpoints. The spatial derivatives in the
PDE are ordinary derivatives on all of Euclidean space. -/
def CoefficientHypotheses {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜) : Prop :=
  (∀ j, ContDiffOn ℝ 1 (Function.uncurry (A j)) (slab n T)) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ j, ∀ z ∈ slab n T,
    ‖fderivWithin ℝ (Function.uncurry (A j)) (slab n T) z‖ ≤ K) ∧
  (∀ j, ∀ s ∈ Icc 0 T, ∀ x, IsSelfAdjoint (A j s x)) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc 0 T, ∀ x, ‖B s x‖ ≤ K)

/-- The coordinate derivative ∂_j A^j in the source constant. -/
def diagonalDerivative {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Principal n m 𝕜) (j : Fin n) (s : ℝ) (x : Space n) : Operator m 𝕜 :=
  fderiv ℝ (A j s) x (coordinate n j)

/-- Hermitian part, with the matrix adjoint and the same operator norm. -/
def hermitianPart {m : ℕ} {𝕜 : Type} [RCLike 𝕜] (B : Operator m 𝕜) : Operator m 𝕜 :=
  (1 / 2 : 𝕜) • (B + B.adjoint)

/-- Uniform operator supremum on the slab (the source's ∞ norm for these
bounded coefficient fields). The index set is nonempty for T ≥ 0. -/
def uniformNorm {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (M : LowerOrder n m 𝕜) : ℝ :=
  sSup ((fun z : ℝ × Space n => ‖M z.1 z.2‖) '' slab n T)

def energyConstant {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, uniformNorm T (diagonalDerivative A j) +
    uniformNorm T (fun s x => hermitianPart (B s x))

/-- Smooth classical solution on the closed slab; the PDE is required in its
interior. No global spatial integrability is assumed here. -/
def IsSmoothSolution {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : ℝ) (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜)
    (f u : Field n m 𝕜) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry u) (slab n T) ∧
    ∀ s ∈ Ioo 0 T, ∀ x,
      deriv (fun r => u r x) s +
        (∑ j, A j s x (fderiv ℝ (u s) x (coordinate n j))) + B s x (u s x) = f s x

/-- Full estimate, including terminal L² finiteness, at every time. -/
def EnergyEstimateStatement : Prop :=
  ∀ {n m : ℕ} {𝕜 : Type} [RCLike 𝕜], 1 ≤ n →
    ∀ (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T A B → ∀ (f u : Field n m 𝕜),
        IsSmoothSolution T A B f u → MemLp (u 0) 2 volume → HasL1L2Source T f →
          ∀ t ∈ Icc 0 T, MemLp (u t) 2 volume ∧
            l2Norm (u t) ≤ Real.exp (energyConstant T A B * t) *
              (l2Norm (u 0) + ∫ s in (0 : ℝ)..t, l2Norm (f s))

/-- The exact estimate for differences, with the L¹ L² norm of f−g. -/
def DifferenceEstimateStatement : Prop :=
  ∀ {n m : ℕ} {𝕜 : Type} [RCLike 𝕜], 1 ≤ n →
    ∀ (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T A B → ∀ (f g u v : Field n m 𝕜),
        IsSmoothSolution T A B f u → IsSmoothSolution T A B g v →
          MemLp (u 0) 2 volume → MemLp (v 0) 2 volume →
            HasL1L2Source T f → HasL1L2Source T g →
              ∀ t ∈ Icc 0 T, MemLp (fun x => u t x - v t x) 2 volume ∧
                l2Norm (fun x => u t x - v t x) ≤
                  Real.exp (energyConstant T A B * t) *
                    (l2Norm (fun x => u 0 x - v 0 x) +
                      ∫ s in (0 : ℝ)..t, l2Norm (fun x => f s x - g s x))

/-- Uniqueness in the complete smooth class, even when the data are equated
only a.e. in space. Equality of continuous representatives is pointwise. -/
def UniquenessStatement : Prop :=
  ∀ {n m : ℕ} {𝕜 : Type} [RCLike 𝕜], 1 ≤ n →
    ∀ (T : ℝ), 0 ≤ T → ∀ (A : Principal n m 𝕜) (B : LowerOrder n m 𝕜),
      CoefficientHypotheses T A B → ∀ (f u v : Field n m 𝕜),
        IsSmoothSolution T A B f u → IsSmoothSolution T A B f v →
          MemLp (u 0) 2 volume → MemLp (v 0) 2 volume →
            HasL1L2Source T f → u 0 =ᵐ[volume] v 0 →
              ∀ t ∈ Icc 0 T, u t = v t

/-- Scalar comparison used for the actual moving-ball energy. Its forcing is
merely L¹. Continuous differentiability of this local energy is a conclusion
of the moving-domain calculation, not a hypothesis on global solution norms. -/
def SqrtEnergyComparisonStatement : Prop :=
  ∀ (T C : ℝ) (E D F : ℝ → ℝ), 0 ≤ T → 0 ≤ C →
    ContinuousOn E (Icc 0 T) → ContinuousOn D (Icc 0 T) →
      (∀ s ∈ Ioo 0 T, HasDerivAt E (D s) s) →
        (∀ s ∈ Icc 0 T, 0 ≤ E s) → IntegrableOn F (Icc 0 T) →
          (∀ᵐ s ∂volume.restrict (Icc 0 T), 0 ≤ F s) →
            (∀ᵐ s ∂volume.restrict (Icc 0 T),
              D s ≤ 2 * C * E s + F s * Real.sqrt (2 * E s)) →
                Real.sqrt (2 * E T) ≤ Real.exp (C * T) *
                  (Real.sqrt (2 * E 0) + ∫ s in (0 : ℝ)..T, F s)

/-- Uniform local bounds prove, rather than presume, global L² membership. -/
def BallExhaustionStatement : Prop :=
  ∀ {n m : ℕ} {𝕜 : Type} [RCLike 𝕜] (f : Space n → Fiber 𝕜 m) (K : ℝ),
    0 ≤ K → AEStronglyMeasurable f volume →
      (∀ R : ℝ, 0 < R → MemLp f 2 (volume.restrict (Metric.ball 0 R)) ∧
        lpNorm f 2 (volume.restrict (Metric.ball 0 R)) ≤ K) →
      MemLp f 2 volume ∧ l2Norm f ≤ K


/-- Explicit reductions; neither assumes the PDE estimate as part of any
coefficient or solution definition. -/
def DifferenceOfEnergyStatement : Prop := EnergyEstimateStatement → DifferenceEstimateStatement

def UniquenessOfDifferenceStatement : Prop := DifferenceEstimateStatement → UniquenessStatement

def HermitianQuadraticStatement : Prop :=
  ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜] (M : Operator m 𝕜) (v : Fiber 𝕜 m),
    RCLike.re (inner 𝕜 v (hermitianPart M v)) = RCLike.re (inner 𝕜 v (M v))

def SymmetricFluxDerivativeStatement : Prop :=
  ∀ {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {A : ℝ → Operator m 𝕜} {u : ℝ → Fiber 𝕜 m}
    {A' : Operator m 𝕜} {u' : Fiber 𝕜 m} {s : ℝ},
      HasDerivAt A A' s → HasDerivAt u u' s → IsSelfAdjoint (A s) →
        HasDerivAt (fun r => RCLike.re (inner 𝕜 (u r) (A r (u r))) / 2)
          (RCLike.re (inner 𝕜 (u s) (A' (u s))) / 2 +
            RCLike.re (inner 𝕜 (u s) (A s u'))) s

def PointwiseEnergyBoundStatement : Prop :=
  ∀ {n m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A D : Fin n → Operator m 𝕜) (B : Operator m 𝕜)
    (u ut f : Fiber 𝕜 m) (dx : Fin n → Fiber 𝕜 m),
      ut + (∑ j, A j (dx j)) + B u = f →
        RCLike.re (inner 𝕜 u ut) +
          (∑ j, (RCLike.re (inner 𝕜 u (D j u)) / 2 +
            RCLike.re (inner 𝕜 u (A j (dx j))))) ≤
          ((1 / 2 : ℝ) * ∑ j, ‖D j‖ + ‖hermitianPart B‖) * ‖u‖ ^ 2 + ‖u‖ * ‖f‖

end P201Specs.Hyperbolic.SymmetricEnergy
