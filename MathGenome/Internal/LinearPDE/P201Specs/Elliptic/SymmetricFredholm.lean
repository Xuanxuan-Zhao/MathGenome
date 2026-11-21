import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ClosedForm
import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces

/-! Symmetric spectral compatibility, paper.tex:2536–2556.
The form is arbitrary: no principal-matrix or zero-lower-order model is imposed.
The Dirichlet hypotheses use the full H¹₀ norm and its canonical L² injection.
Compact resolvent means a compact bounded two-sided inverse at some scalar point.
-/
noncomputable section
open scoped InnerProductSpace ComplexConjugate
universe u v
namespace P201.Elliptic.SymmetricFredholm
open ExpandedFA.Unbounded

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- L−rI on exactly the original operator domain. -/
def shifted (A : Operator 𝕜 H H) (r : ℝ) : A.domain →ₗ[𝕜] H :=
  A.toFun - (r : 𝕜) • A.domain.subtype

/-- No preferred resolvent point, and no inverse is postulated at zero. -/
def HasCompactResolvent (A : Operator 𝕜 H H) : Prop :=
  ∃ ζ : 𝕜, ∃ R : ResolventInverse A ζ, IsCompactOperator R.inverse

/-- Absence of a nonzero vector in ker(L−rI). -/
def NotEigenvalue (A : Operator 𝕜 H H) (r : ℝ) : Prop :=
  ∀ u : A.domain, shifted A r u = 0 → (u : H) = 0

/-- Unique solvability off the eigenvalues, compatibility with the same
real eigenspace, and the full affine space of solutions at any eigenvalue. -/
def Conclusion (A : Operator 𝕜 H H) (r : ℝ) : Prop :=
  (NotEigenvalue A r → ∀ f : H, ∃! u : A.domain, shifted A r u = f) ∧
  (∀ f : H, (∃ u : A.domain, shifted A r u = f) ↔
    ∀ v : A.domain, shifted A r v = 0 → paperInner (𝕜 := 𝕜) f (v : H) = 0) ∧
  (∀ (f : H) (u : A.domain), shifted A r u = f →
    ∀ v : A.domain, shifted A r v = f ↔ shifted A r (v - u) = 0)

namespace Expected

def Abstract : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : Operator 𝕜 H H), Dense (A.domain : Set H) → A = A.adjoint →
    HasCompactResolvent A → ∀ r : ℝ, Conclusion A r

def ClosedForms : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : DenseForm 𝕜 H) (hs : a.IsHermitian) (hn : a.IsNonnegative),
    (a.toNonnegative hs hn).IsClosed → HasCompactResolvent a.associatedOperator →
    ∀ r : ℝ, Conclusion a.associatedOperator r

end Expected

section Dirichlet
open P201Specs
variable {𝕜 : Type} [RCLike 𝕜] {m : ℕ} (Ω : Domain (m + 1))
  (a : DenseForm 𝕜 (Lp 𝕜 Ω 2))

/-- V=H¹₀ as an actual subspace of L²; the norm on V is still the full H¹ norm. -/
def DirichletDomain : Prop :=
  a.domain = (hZeroUnderlying (𝕜 := 𝕜) Ω).toLinearMap.range

/-- The canonical injection, expressed as an element of the form domain. -/
def dirichletLift (hd : DirichletDomain Ω a) (u : H10 𝕜 Ω) : a.domain :=
  ⟨hZeroUnderlying Ω u, hd.symm ▸ LinearMap.mem_range_self _ u⟩

/-- Continuity of the whole sesquilinear form, including all lower-order terms. -/
def DirichletBounded (hd : DirichletDomain Ω a) : Prop :=
  ∃ M : ℝ, ∀ u v : H10 𝕜 Ω,
    ‖a.form (dirichletLift Ω a hd u) (dirichletLift Ω a hd v)‖ ≤ M * ‖u‖ * ‖v‖

def DirichletCoercive (hd : DirichletDomain Ω a) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ u : H10 𝕜 Ω,
    c * ‖u‖ ^ 2 ≤ RCLike.re (a.form (dirichletLift Ω a hd u) (dirichletLift Ω a hd u))

end Dirichlet

namespace Expected
/-- The manuscript's full coercive symmetric Dirichlet realization.
Density belongs to `DenseForm`; boundedness/coercivity are on the actual H¹₀.
Closedness and self-adjointness are conclusions of the proof, not hypotheses. -/
def Dirichlet : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {m : ℕ} (Ω : P201Specs.Domain (m + 1)),
    P201Specs.IsBoundedLipschitzOpen Ω →
    ∀ (a : DenseForm 𝕜 (P201Specs.Lp 𝕜 Ω 2)) (hd : DirichletDomain Ω a),
    a.IsHermitian → DirichletBounded Ω a hd → DirichletCoercive Ω a hd →
    HasCompactResolvent a.associatedOperator →
    ∀ r : ℝ, Conclusion a.associatedOperator r
end Expected
end P201.Elliptic.SymmetricFredholm
