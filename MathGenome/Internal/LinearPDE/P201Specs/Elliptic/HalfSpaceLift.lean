import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.HolderCancellation
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RieszL2Multiplier
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Independent specification of the half-space lift in paper.tex:1940–1989.
The boundary dimension is `m ≥ 1`, so the ambient dimension is `m + 1`.
All integrals below use the canonical Euclidean Lebesgue measure.
No convergence, kernel identity, or regularity certificate is assumed. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

namespace P201Specs.Elliptic.HalfSpaceLift

/-- The unnormalized height-one Poisson profile. -/
def poissonProfile (m : ℕ) (z : Space m) : ℝ :=
  (1 + ‖z‖ ^ 2) ^ (-((m : ℝ) + 1) / 2)

/-- Normalization by the actual Lebesgue integral; positivity and finiteness
are proof obligations, not fields of the definition. -/
def poissonConstant (m : ℕ) : ℝ := (∫ z, poissonProfile m z)⁻¹

/-- The source formula. Its interpretation as a probability density is
asserted only for positive heights. -/
def poissonKernel (m : ℕ) (t : ℝ) (z : Space m) : ℝ :=
  poissonConstant m * t * (t ^ 2 + ‖z‖ ^ 2) ^ (-((m : ℝ) + 1) / 2)

def horizontal {m : ℕ} (p : Space (m + 1)) : Space m :=
  WithLp.toLp 2 (fun i => p i.castSucc)

def height {m : ℕ} (p : Space (m + 1)) : ℝ := p (Fin.last m)

def point {m : ℕ} (x : Space m) (t : ℝ) : Space (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)

def closedHalfSpace (m : ℕ) : Set (Space (m + 1)) := {p | 0 ≤ height p}
def openHalfSpace (m : ℕ) : Set (Space (m + 1)) := {p | 0 < height p}

/-- Convolution, also applicable to bounded noncompact normal traces. -/
def poissonIntegral {m : ℕ} (b : Space m → ℝ) (t : ℝ) (x : Space m) : ℝ :=
  ∫ z, poissonKernel m t z * b (x - z)

/-- The closed half-space representative has the prescribed datum at height
zero. The boundary regularity assertion below must still prove this is a trace. -/
def harmonicLift {m : ℕ} (g : Space m → ℝ) (p : Space (m + 1)) : ℝ :=
  if 0 < height p then poissonIntegral g (height p) (horizontal p)
  else g (horizontal p)

/-- Coordinate derivatives on the boundary. -/
def tangent {m : ℕ} (b : Space m → ℝ) (i : Fin m) (x : Space m) : ℝ :=
  fderiv ℝ b x (coordinate m i)

/-- Standard Riesz normalization: its multiplier is -i ξ_i/|ξ|.
The value at zero is totalized and immaterial for principal values. -/
def rieszKernel (m : ℕ) (i : Fin m) (z : Space m) : ℝ :=
  P102.Specs.U3.Riesz.kernelValue m i z

/-- Required normalization bridge between the probability kernel and the
pinned Riesz operators. Equality is a conclusion, never an input certificate. -/
def rieszNormalizationStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m →
    poissonConstant m = P102.Specs.U3.Riesz.constantValue m ∧
    ∀ (i : Fin m) (z : Space m),
      rieszKernel m i z = poissonConstant m * z i / ‖z‖ ^ (m + 1)

/-- The actual principal-value realization of Λ = Σ R_i D_i. -/
def normalGenerator {m : ℕ} (b : Space m → ℝ) (x : Space m) : ℝ :=
  ∑ i : Fin m, HolderCancellation.principalValue (rieszKernel m i) (tangent b i) x

def poissonProfileType := (m : ℕ) → Space m → ℝ
def poissonConstantType := ℕ → ℝ
def poissonKernelType := (m : ℕ) → ℝ → Space m → ℝ
def poissonIntegralType := {m : ℕ} → (Space m → ℝ) → ℝ → Space m → ℝ
def harmonicLiftType := {m : ℕ} → (Space m → ℝ) → Space (m + 1) → ℝ
def rieszKernelType := (m : ℕ) → Fin m → Space m → ℝ
def normalGeneratorType := {m : ℕ} → (Space m → ℝ) → Space m → ℝ

section HolderNorms
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordinary Hölder seminorm, used with a separate finiteness predicate. -/
def holderSeminormOn (α : ℝ) (f : E → F) (S : Set E) : ℝ :=
  sSup {q : ℝ | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ q = ‖f x - f y‖ / dist x y ^ α}

/-- Full ordinary C^{2,α} norm: all jet suprema, plus the Hessian seminorm.
The derivatives are within the closed half-space when S is that half-space. -/
def c2HolderNormOn (α : ℝ) (f : E → ℝ) (S : Set E) : ℝ :=
  (∑ k ∈ Finset.range 3,
    sSup {q : ℝ | ∃ x ∈ S, q = ‖iteratedFDerivWithin ℝ k f S x‖}) +
  holderSeminormOn α (iteratedFDerivWithin ℝ 2 f S) S

/-- Finiteness is explicit, so the totalized real supremum cannot hide
an unbounded derivative or seminorm. -/
def C2HolderOn (α : ℝ) (f : E → ℝ) (S : Set E) : Prop :=
  ContDiffOn ℝ 2 f S ∧ ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
    (∀ k ≤ 2, ∀ x ∈ S, ‖iteratedFDerivWithin ℝ k f S x‖ ≤ M) ∧
    ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDerivWithin ℝ 2 f S x - iteratedFDerivWithin ℝ 2 f S y‖ ≤
        H * dist x y ^ α
end HolderNorms

/-- Positive mass, normalization, scaling, and spatial integrability. -/
def kernelBasicStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → 0 < poissonConstant m ∧
    ∀ t : ℝ, 0 < t → Integrable (poissonKernel m t) volume ∧
      (∫ z, poissonKernel m t z) = 1 ∧
      (∀ z, 0 < poissonKernel m t z) ∧
      (∀ z, poissonKernel m t z = (t ^ m)⁻¹ * poissonKernel m 1 (t⁻¹ • z))

/-- The moment needed for the uniform approximate-identity estimate. -/
def kernelMomentStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun z => ‖z‖ ^ α * poissonKernel m t z) volume ∧
      (∫ z, ‖z‖ ^ α * poissonKernel m t z) = C * t ^ α

/-- Uniform bounds for bounded Hölder data, without any support restriction.
The last estimate gives the uniform boundary limit as t decreases to zero. -/
def poissonHolderStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Space m → ℝ) (M H : ℝ),
      HolderCancellation.HolderBounds α b M H → ∀ t : ℝ, 0 < t →
        (∀ x, Integrable (fun z => poissonKernel m t z * b (x - z)) volume) ∧
        (∀ x, ‖poissonIntegral b t x‖ ≤ M) ∧
        (∀ x y, ‖poissonIntegral b t x - poissonIntegral b t y‖ ≤ H * dist x y ^ α) ∧
        (∀ x, ‖poissonIntegral b t x - b x‖ ≤ C * H * t ^ α)

/-- The kernel and its Fourier transform, with the shared -2πi phase. -/
def kernelSemigroupStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m →
    (ContDiffOn ℝ (⊤ : ℕ∞) (fun p : Space (m + 1) =>
      poissonKernel m (height p) (horizontal p)) (openHalfSpace m)) ∧
    (∀ p ∈ openHalfSpace m,
      laplacian (fun q : Space (m + 1) =>
        poissonKernel m (height q) (horizontal q)) p = 0) ∧
    (∀ t : ℝ, 0 < t → ∀ ξ : Space m,
      fourierIntegral (fun z => (poissonKernel m t z : ℂ)) ξ =
        (Real.exp (-2 * Real.pi * t * ‖ξ‖) : ℂ)) ∧
    (∀ t s : ℝ, 0 < t → 0 < s → ∀ x : Space m,
      Integrable (fun z => poissonKernel m t z * poissonKernel m s (x - z)) volume ∧
      poissonIntegral (poissonKernel m s) t x = poissonKernel m (t + s) x)

/-- The explicit physical kernel is smooth and harmonic at positive height. -/
def kernelRegularityStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m →
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : Space (m + 1) =>
      poissonKernel m (height p) (horizontal p)) (openHalfSpace m) ∧
    ∀ p ∈ openHalfSpace m,
      laplacian (fun q : Space (m + 1) =>
        poissonKernel m (height q) (horizontal q)) p = 0

/-- Classical derivatives of every positive-height horizontal slice. This
assertion does not replace the ambient derivative identities below. -/
def tangentialConvolutionStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ g : Space m → ℝ,
    HasCompactSupport g → ContDiff ℝ 2 g → ∀ t : ℝ, 0 < t →
      ContDiff ℝ 2 (poissonIntegral g t) ∧
      (∀ (x : Space m) (j : Fin m),
        fderiv ℝ (poissonIntegral g t) x (coordinate m j) =
          poissonIntegral (tangent g j) t x) ∧
      ∀ (x : Space m) (i j : Fin m),
        fderiv ℝ (fun y => fderiv ℝ (poissonIntegral g t) y (coordinate m j))
          x (coordinate m i) = poissonIntegral (tangent (tangent g j) i) t x

/-- Actual ambient differentiability and first tangential derivatives at
positive height, already for compact C¹ boundary data. -/
def tangentialLiftStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ g : Space m → ℝ,
    HasCompactSupport g → ContDiff ℝ 1 g →
      (∀ p ∈ openHalfSpace m, DifferentiableAt ℝ (harmonicLift g) p) ∧
      ∀ t : ℝ, 0 < t → ∀ (x : Space m) (j : Fin m),
        fderiv ℝ (harmonicLift g) (point x t) (coordinate (m + 1) j.castSucc) =
          poissonIntegral (tangent g j) t x

/-- Actual classical derivatives, including their boundary values. Tangential
and normal formulas on the open half-space are supplied with the same traces. -/
def LiftDerivativeIdentities {m : ℕ} (g : Space m → ℝ) : Prop :=
  let h := harmonicLift g
  let S := closedHalfSpace m
  (∀ t : ℝ, 0 < t → ∀ x : Space m,
    (∀ j : Fin m,
      fderiv ℝ h (point x t) (coordinate (m + 1) j.castSucc) =
        poissonIntegral (tangent g j) t x) ∧
    (∀ i j : Fin m,
      fderiv ℝ (fun p => fderiv ℝ h p (coordinate (m + 1) j.castSucc))
        (point x t) (coordinate (m + 1) i.castSucc) =
        poissonIntegral (tangent (tangent g j) i) t x) ∧
    fderiv ℝ h (point x t) (coordinate (m + 1) (Fin.last m)) =
      -poissonIntegral (normalGenerator g) t x ∧
    (∀ j : Fin m,
      fderiv ℝ (fun p => fderiv ℝ h p (coordinate (m + 1) j.castSucc))
        (point x t) (coordinate (m + 1) (Fin.last m)) =
        -poissonIntegral (normalGenerator (tangent g j)) t x) ∧
    fderiv ℝ (fun p => fderiv ℝ h p (coordinate (m + 1) (Fin.last m)))
      (point x t) (coordinate (m + 1) (Fin.last m)) =
        -poissonIntegral (laplacian g) t x) ∧
  (∀ x : Space m,
    (∀ j : Fin m,
      fderivWithin ℝ h S (point x 0) (coordinate (m + 1) j.castSucc) = tangent g j x) ∧
    fderivWithin ℝ h S (point x 0) (coordinate (m + 1) (Fin.last m)) =
      -normalGenerator g x ∧
    (∀ i j : Fin m,
      fderivWithin ℝ (fun p => fderivWithin ℝ h S p (coordinate (m + 1) j.castSucc))
        S (point x 0) (coordinate (m + 1) i.castSucc) = tangent (tangent g j) i x) ∧
    (∀ j : Fin m,
      fderivWithin ℝ (fun p => fderivWithin ℝ h S p (coordinate (m + 1) j.castSucc))
        S (point x 0) (coordinate (m + 1) (Fin.last m)) =
          -normalGenerator (tangent g j) x) ∧
    fderivWithin ℝ (fun p => fderivWithin ℝ h S p (coordinate (m + 1) (Fin.last m)))
      S (point x 0) (coordinate (m + 1) (Fin.last m)) = -laplacian g x)

/-- The boundary values in the chosen representative are genuine joint traces,
including when horizontal coordinates vary as the height tends to zero. -/
def boundaryTraceStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ b : Space m → ℝ, HolderCancellation.IsHolder α b → ∀ x : Space m,
      ContinuousAt (harmonicLift b) (point x 0) ∧ harmonicLift b (point x 0) = b x

/-- The qualitative normal traces asserted in the source follow from the
actual compact C^{2,α} datum; derivative regularity is not an extra hypothesis. -/
def normalTracesHolderStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ g : Space m → ℝ, HasCompactSupport g → C2HolderOn α g univ →
      HolderCancellation.IsHolder α (normalGenerator g) ∧
      ∀ j : Fin m, HolderCancellation.IsHolder α (normalGenerator (tangent g j))

/-- Quantitative cancellation bounds with a constant fixed before the datum. -/
def normalTracesQuantitativeStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : Space m → ℝ, HasCompactSupport g →
        tsupport g ⊆ closedBall 0 R → C2HolderOn α g univ →
        HolderCancellation.holderNorm α (normalGenerator g) ≤ C * c2HolderNormOn α g univ ∧
        ∀ j : Fin m, HolderCancellation.holderNorm α (normalGenerator (tangent g j)) ≤
          C * c2HolderNormOn α g univ

/-- The full source obligation, with C chosen before the datum. Using a support
ball centered at zero loses no compactly supported input. `C2HolderOn` requires
actual derivatives and finite ordinary norms; no conclusion is a hypothesis. -/
def halfSpaceLiftStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : Space m → ℝ, HasCompactSupport g →
        tsupport g ⊆ closedBall 0 R → C2HolderOn α g univ →
        C2HolderOn α (harmonicLift g) (closedHalfSpace m) ∧
        (∀ p ∈ openHalfSpace m, laplacian (harmonicLift g) p = 0) ∧
        (∀ x : Space m, harmonicLift g (point x 0) = g x) ∧
        LiftDerivativeIdentities g ∧
        HolderCancellation.IsHolder α (normalGenerator g) ∧
        (∀ j : Fin m, HolderCancellation.IsHolder α (normalGenerator (tangent g j))) ∧
        c2HolderNormOn α (harmonicLift g) (closedHalfSpace m) ≤
          C * c2HolderNormOn α g univ

end P201Specs.Elliptic.HalfSpaceLift
