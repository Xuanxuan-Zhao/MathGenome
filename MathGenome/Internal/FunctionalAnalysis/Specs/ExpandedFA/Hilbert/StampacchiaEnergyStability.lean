import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.StampacchiaSolvability

/-!
Independent statements for paper.tex 7578–7605 (`fa2:p2:stampacchia`).
The real energy agrees with a(v,v)/2 - Re F(v) for Hermitian forms,
since their diagonal values are real. The datum is F(v) = ⟪v,f⟫, and
coercivity is the positive real-part condition, over either scalar field.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.StampacchiaEnergyStability.Spec
universe u v

/-- The energy in the original Hilbert space and its original norm. -/
def EnergyType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H],
    Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H → H → H → ℝ

def EnergyValue : EnergyType.{u, v} :=
  fun 𝕜 _ _ _ _ a f x => RCLike.re (a x x) / 2 - RCLike.re ⟪x, f⟫_𝕜

/-- Solvability is retained from the accepted prerequisite. -/
def ExistenceUniqueness : Prop :=
  StampacchiaSolvability.Spec.ExistenceUniqueness.{u, v}

/-- The entire variational predicate, including membership, is equivalent to
constrained minimization; the coercivity is not an absolute-diagonal bound. -/
def HermitianMinimization : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    Conventions.Spec.FormBoundValue 𝕜 H H a M →
    Conventions.Spec.FormCoerciveValue 𝕜 H a α →
    Conventions.Spec.FormHermitianValue 𝕜 H a →
    ∀ (f : H) (C : Set H), C.Nonempty → IsClosed C →
      Conventions.Spec.RealConvexValue 𝕜 H C →
      (∀ u : H,
        (u ∈ C ∧ ∀ v ∈ C,
          RCLike.re ⟪v - u, f⟫_𝕜 ≤ RCLike.re (a (v - u) u)) ↔
        (u ∈ C ∧ ∀ v ∈ C, EnergyValue 𝕜 H a f u ≤ EnergyValue 𝕜 H a f v)) ∧
      ∃! u : H, u ∈ C ∧ ∀ v ∈ C,
        EnergyValue 𝕜 H a f u ≤ EnergyValue 𝕜 H a f v

/-- Stability for two data with the same form, constraint, and coercivity
constant. Hermitian symmetry is not assumed. -/
def Stability : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : Conventions.Spec.BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    Conventions.Spec.FormBoundValue 𝕜 H H a M →
    Conventions.Spec.FormCoerciveValue 𝕜 H a α →
    ∀ (C : Set H), C.Nonempty → IsClosed C →
      Conventions.Spec.RealConvexValue 𝕜 H C →
      ∀ (f g u_f u_g : H),
        (u_f ∈ C ∧ ∀ v ∈ C,
          RCLike.re ⟪v - u_f, f⟫_𝕜 ≤ RCLike.re (a (v - u_f) u_f)) →
        (u_g ∈ C ∧ ∀ v ∈ C,
          RCLike.re ⟪v - u_g, g⟫_𝕜 ≤ RCLike.re (a (v - u_g) u_g)) →
        ‖u_f - u_g‖ ≤ ‖f - g‖ / α

end ExpandedFA.Hilbert.StampacchiaEnergyStability.Spec
