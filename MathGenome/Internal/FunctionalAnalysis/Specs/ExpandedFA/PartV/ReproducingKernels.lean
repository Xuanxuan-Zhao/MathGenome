import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
Scalar RKHS statements for paper.tex, fa2:p5:rkhs (23157–23180), with the
conjugate-first convention fixed at 67–69. The integral range clause is the
separately allocated app_rkhs_range obligation.

A function realization is an injective scalar-linear map to actual functions.
Only its individual evaluations are required to be continuous. In particular
there is no topology on X or uniform bound on these evaluations. Finitely
supported coefficients express positivity on all finite subsets; FiniteGram
also states the finite-family version, allowing repeated points.
-/
noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.PartV.ReproducingKernels.Spec
universe u v w w'

structure FunctionSpace (𝕜 : Type u) (X : Type v) (H : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  functions : H →ₗ[𝕜] (X → 𝕜)
  injective : Function.Injective functions
  continuous_eval : ∀ x, Continuous (fun f : H => functions f x)

/-- Type and expected value of the scalar Hilbert function-space interface. -/
def FunctionSpaceType :=
  ∀ (𝕜 : Type u) (X : Type v) (H : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], Type (max u v w)

def FunctionSpaceValue : FunctionSpaceType.{u, v, w} :=
  fun 𝕜 X H _ _ _ => FunctionSpace 𝕜 X H

/-- Positive definite in the manuscript's semidefinite sense. -/
def PositiveKernel {𝕜 : Type u} {X : Type v} [RCLike 𝕜] (K : X → X → 𝕜) : Prop :=
  (∀ x y, K y x = conj (K x y)) ∧
  ∀ c : X →₀ 𝕜, ∃ r : ℝ, 0 ≤ r ∧
    (c.sum fun x a => c.sum fun y b => conj a * b * K x y) = (r : 𝕜)

/-- A chosen family of evaluation vectors, with no extra density assumption. -/
def Reproduces {𝕜 : Type u} {X : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (F : FunctionSpace 𝕜 X H) (k : X → H) : Prop :=
  ∀ f x, F.functions f x = ⟪k x, f⟫_𝕜

def EvaluationRepresentation : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (H : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (F : FunctionSpace 𝕜 X H),
    ∃ k : X → H, Reproduces F k ∧
      (∀ l : X → H, Reproduces F l → l = k) ∧
      PositiveKernel (fun x y => ⟪k x, k y⟫_𝕜)

def KernelExistence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜] (K : X → X → 𝕜),
    PositiveKernel K →
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H)
      (_ : InnerProductSpace 𝕜 H) (_ : CompleteSpace H)
      (F : FunctionSpace 𝕜 X H) (k : X → H),
      Reproduces F k ∧ (∀ x y, ⟪k x, k y⟫_𝕜 = K x y)

def KernelUniqueness : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (H : Type w) (G : Type w') [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (F : FunctionSpace 𝕜 X H) (D : FunctionSpace 𝕜 X G)
    (k : X → H) (l : X → G),
    Reproduces F k → Reproduces D l →
    (∀ x y, ⟪k x, k y⟫_𝕜 = ⟪l x, l y⟫_𝕜) →
    ∃ U : H ≃ₗᵢ[𝕜] G, ∀ f x, D.functions (U f) x = F.functions f x

/-- Explicit Gram positivity, including reality, for every finite family. -/
def FiniteGram : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜] (K : X → X → 𝕜),
    PositiveKernel K → ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → 𝕜),
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ i, ∑ j, conj (c i) * c j * K (x i) (x j)) = (r : 𝕜)

/-- The finitely supported definition is exactly positivity of all finite Gram
families; this also records the hypothesis form for the converse theorem. -/
def FiniteKernelCharacterization : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜] (K : X → X → 𝕜),
    PositiveKernel K ↔ (∀ x y, K y x = conj (K x y)) ∧
      ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → 𝕜),
      ∃ r : ℝ, 0 ≤ r ∧
        (∑ i, ∑ j, conj (c i) * c j * K (x i) (x j)) = (r : 𝕜)

end ExpandedFA.PartV.ReproducingKernels.Spec
