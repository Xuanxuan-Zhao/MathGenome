import MathGenome.Internal.LinearPDE.P201Specs.Potential.ContinuousHarmonicLift

/-! Independent full scope of `lem:pde-harmonic-lift`, paper.tex:1027–1115.
The harmonic function is the continuous-data extension; the smooth-data clause
identifies its bulk class with the unique affine weak solution and an actual
H² class. No Sobolev embedding or boundary-continuity certificate is assumed.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace P201Specs.SmoothHarmonicLift

/-- Smooth up to the closure, represented by a smooth function on an open
neighborhood. Values of the ambient representative away from that neighborhood
are irrelevant. -/
def SmoothOnClosure {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (G₀ : Space n → 𝕜) : Prop :=
  ∃ U : Set (Space n), IsOpen U ∧ closure (Ω : Set _) ⊆ U ∧
    ContDiffOn ℝ (⊤ : ℕ∞) G₀ U

/-- Membership in the actual affine class G₀ + H¹₀, expressed in bulk a.e.
values. The witness is a genuine element of the full-H¹ closure. -/
def InAffineClass {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (G₀ : Space n → 𝕜) (u : H 𝕜 Ω 1) : Prop :=
  ∃ z : H10 𝕜 Ω, (hUnderlying Ω 1 u : Space n → 𝕜) =ᵐ[domainMeasure Ω]
    fun x => G₀ x + hZeroUnderlying Ω z x

/-- The weak harmonic equation, with the source's conjugation in the second
factor for complex scalars. -/
def WeakHarmonic {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (u : H 𝕜 Ω 1) : Prop :=
  ∀ v : H10 𝕜 Ω,
    ellipticEnergyForm Ω (fun _ => (1 : Matrix (Fin n) (Fin n) 𝕜)) u v.val = 0

def IsWeakLift {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n)
    (G₀ : Space n → 𝕜) (u : H 𝕜 Ω 1) : Prop :=
  InAffineClass Ω G₀ u ∧ WeakHarmonic Ω u

/-- The complete original conclusion. The same continuous extension works for
every smooth ambient lift of the data. Uniqueness of ambient harmonic
representatives is on the closure; uniqueness of weak solutions is in H¹.
No connectedness or nonemptiness is imposed. -/
def HarmonicLiftStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasCkBoundary Ω 2 →
    ∀ g : C(frontier (Ω : Set (Space (m + 1))), 𝕜),
      ∃ h : Space (m + 1) → 𝕜,
        ContinuousHarmonicLift.IsExtension Ω g h ∧
        (∀ v : Space (m + 1) → 𝕜, ContinuousHarmonicLift.IsExtension Ω g v →
          EqOn v h (closure (Ω : Set _))) ∧
        ∀ G₀ : Space (m + 1) → 𝕜, SmoothOnClosure Ω G₀ →
          (∀ z : frontier (Ω : Set (Space (m + 1))), G₀ z = g z) →
          ∃ u : H 𝕜 Ω 1, IsWeakLift Ω G₀ u ∧
            (hUnderlying Ω 1 u : Space (m + 1) → 𝕜) =ᵐ[domainMeasure Ω] h ∧
            (∃ w : H 𝕜 Ω 2,
              (hUnderlying Ω 2 w : Space (m + 1) → 𝕜) =ᵐ[domainMeasure Ω] h) ∧
            ∀ v : H 𝕜 Ω 1, IsWeakLift Ω G₀ v → v = u

end P201Specs.SmoothHarmonicLift
