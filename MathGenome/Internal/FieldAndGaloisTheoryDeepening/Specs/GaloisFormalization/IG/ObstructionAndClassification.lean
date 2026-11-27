import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.LiftCoordinates
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.WeakLiftTorsor

/-! The obstruction and classification of weak lifts in Theorem IG04. -/

namespace Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.Specification

open _root_.GaloisFormalization.GH.Model
open scoped IsMulCommutative

universe u v w

local notation "A[" P "]" => Additive (FiniteEmbeddingProblem.kernel P)

/-- The obstruction to lifting and the induced torsor on classes of weak lifts
use the same action of the profinite group on the kernel. -/
def WeakLiftObstructionAndClassification : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel],
    letI := P.quotientKernelActionValue
    letI := P.pullbackKernelActionValue
    letI : ContinuousSMul Γ A[P] :=
      ⟨(continuous_smul (M := Q) (X := A[P])).comp
        ((P.rho.continuous.comp continuous_fst).prodMk continuous_snd)⟩
    (Nonempty P.WeakSolution ↔ weakLiftObstruction P = 0) ∧
    (Nonempty P.WeakSolution →
      ∃! torsor : AddTorsor (ContinuousH Γ A[P] 1) (WeakSolutionConjugacyClasses P),
        letI := torsor
        (∀ (c : continuousCocycles Γ A[P] 1) (x : P.WeakSolution),
          ∃ y : P.WeakSolution,
            (∀ g : Γ, y.lift g = (c.val.val ![g]).toMul.val * x.lift g) ∧
            continuousClass Γ A[P] 1 c +ᵥ weakSolutionClass P x = weakSolutionClass P y) ∧
        ∀ x y : WeakSolutionConjugacyClasses P,
          ∃! c : ContinuousH Γ A[P] 1, c +ᵥ x = y)

/-- Centrality gives trivial coefficients for the action through the prescribed quotient. -/
def CentralWeakLiftCoefficientAction : Prop :=
  PullbackKernelActionOfCentral.{u,v,w}

end Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.Specification
