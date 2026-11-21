import MathGenome.Internal.Specs.D07.Ch15.QuadraticTowerIff
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Galois.Basic

/-! The normal-envelope construction in paper.tex:4517--4523.
The ambient algebraic closure need not be real. The real-tower statement
uses the existing tower, including degree-one steps. A specified embedding
of the top is respected, rather than replaced by an abstract isomorphic field.
-/

universe u v

namespace D07.Ch15.QuadraticNormalEnvelope

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- Both square roots of every conjugate radicand are included. -/
def conjugateRoots (N : IntermediateField K Ω) (b : N) : Set Ω :=
  {x | ∃ σ : N ≃ₐ[K] N, x ^ 2 = algebraMap N Ω (σ b)}

/-- One stage of the source's construction, in the chosen overfield. -/
noncomputable def rootEnvelope (N : IntermediateField K Ω) (b : N) :
    IntermediateField K Ω :=
  (IntermediateField.adjoin N (conjugateRoots K Ω N b)).restrictScalars K

end D07.Ch15.QuadraticNormalEnvelope

namespace Specs.D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope

open D07.Ch15.StraightedgeCompass D07.Ch15.QuadraticNormalEnvelope

/-- The actual conjugate-square-root stage is finite Galois, has
2-power degree, and contains the old field and every root of the radicand. -/
def ConjugateRootStage : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (N : IntermediateField K Ω)
    [FiniteDimensional K N] [IsGalois K N] (b : N),
    (∃ n : ℕ, Module.finrank K N = 2 ^ n) →
    N ≤ rootEnvelope K Ω N b ∧
      FiniteDimensional K (rootEnvelope K Ω N b) ∧
      IsGalois K (rootEnvelope K Ω N b) ∧
      (∃ n : ℕ, Module.finrank K (rootEnvelope K Ω N b) = 2 ^ n) ∧
      ∀ x : Ω, x ^ 2 = algebraMap N Ω b → x ∈ rootEnvelope K Ω N b

/-- Every compatible specified embedding of a real tower top has an envelope.
Compatibility is expressed directly on the actual real subfields, so no
unmentioned scalar action on the tower top is being chosen. -/
def TowerNormalEnvelope : Prop :=
  ∀ (K M : IntermediateField ℚ ℝ), QuadraticTower K M →
    K ≤ M ∧
    ∀ (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
      (ι : M →+* Ω),
      (∀ (k : K) (hk : (k : ℝ) ∈ M),
        ι ⟨(k : ℝ), hk⟩ = algebraMap K Ω k) →
      ∃ N : IntermediateField K Ω,
        FiniteDimensional K N ∧ IsGalois K N ∧
        (∃ n : ℕ, Module.finrank K N = 2 ^ n) ∧
        Set.range ι ⊆ (N : Set Ω)

/-- The top can in fact be embedded in any chosen algebraic closure,
and the resulting embedded tower lies in a finite 2-power Galois extension. -/
def ExistsTowerNormalEnvelope : Prop :=
  ∀ (K M : IntermediateField ℚ ℝ), QuadraticTower K M →
    ∀ (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω],
    ∃ (hKM : K ≤ M) (ι : M →+* Ω) (N : IntermediateField K Ω),
      (∀ k : K, ι ⟨(k : ℝ), hKM k.2⟩ = algebraMap K Ω k) ∧
      FiniteDimensional K N ∧ IsGalois K N ∧
      (∃ n : ℕ, Module.finrank K N = 2 ^ n) ∧
      Set.range ι ⊆ (N : Set Ω)

end Specs.D07.Ch15.NormalClosureCriterionQuadraticTowerNormalEnvelope
