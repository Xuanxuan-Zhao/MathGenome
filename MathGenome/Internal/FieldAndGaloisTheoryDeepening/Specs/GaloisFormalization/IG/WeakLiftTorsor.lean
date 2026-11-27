import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.AbelianKernelAction
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Tactic.Group

/-! The classification of weak solutions in Theorem IG04. -/

namespace Specs.GaloisFormalization.IG.FiniteEmbeddingProblem

open _root_.GaloisFormalization.GH.Model
open scoped IsMulCommutative

universe u v w

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q)

/-- Two weak solutions are related if one kernel element conjugates their lifts
at every point of the domain. -/
def weakSolutionConjugacy : Setoid P.WeakSolution where
  r x y := ∃ a : P.kernel, ∀ g : Γ, y.lift g = a.val * x.lift g * a.val⁻¹
  iseqv :=
    { refl := fun x => ⟨1, fun g => by simp⟩
      symm := by
        intro x y ⟨a, h⟩
        refine ⟨a⁻¹, fun g => ?_⟩
        rw [h g, Subgroup.coe_inv, inv_inv]
        group
      trans := by
        intro x y z ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨b * a, fun g => ?_⟩
        rw [hb g, ha g, Subgroup.coe_mul]
        group }

/-- Continuous weak solutions modulo conjugation by the kernel. -/
abbrev WeakSolutionConjugacyClasses := Quotient (weakSolutionConjugacy P)

/-- The conjugacy class of a continuous weak solution. -/
def weakSolutionClass : P.WeakSolution → WeakSolutionConjugacyClasses P :=
  Quotient.mk (weakSolutionConjugacy P)

namespace Specification

private abbrev declarationType {α : Sort*} (_ : α) : Sort _ := α

set_option linter.checkUnivs false

def ConjugacyType := declarationType (@weakSolutionConjugacy.{u,v,w})
def ConjugacyClassesType := declarationType (@WeakSolutionConjugacyClasses.{u,v,w})
def WeakSolutionClassType := declarationType (@weakSolutionClass.{u,v,w})

local notation "A[" P "]" => Additive (FiniteEmbeddingProblem.kernel P)

/-- Whenever there is a weak solution, the classes have a unique torsor structure
whose action twists a representative pointwise by a representative cocycle. -/
def WeakSolutionClassesTorsor : Prop :=
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
    Nonempty P.WeakSolution →
      ∃! torsor : AddTorsor (ContinuousH Γ A[P] 1) (WeakSolutionConjugacyClasses P),
        letI := torsor
        (∀ (c : continuousCocycles Γ A[P] 1) (x : P.WeakSolution),
          ∃ y : P.WeakSolution,
            (∀ g : Γ, y.lift g = (c.val.val ![g]).toMul.val * x.lift g) ∧
            continuousClass Γ A[P] 1 c +ᵥ weakSolutionClass P x = weakSolutionClass P y) ∧
        ∀ x y : WeakSolutionConjugacyClasses P,
          ∃! c : ContinuousH Γ A[P] 1, c +ᵥ x = y

end Specification
end Specs.GaloisFormalization.IG.FiniteEmbeddingProblem
