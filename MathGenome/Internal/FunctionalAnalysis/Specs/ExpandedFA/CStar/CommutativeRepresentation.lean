import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.GelfandTransform
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions

/-!
The representation assertion of `fa2:p2:commutative-cstar`, paper.tex:12201–12219.
The character carrier and evaluation topology are the accepted algebraic
characters, not a newly chosen spectrum. The transform below is the accepted
Banach-algebra Gelfand transform. `CommCStarAlgebra` keeps the original norm,
scalar action and involution. Nonzeroness is imposed only in statements using
the Banach-algebra transform; the zero algebra has its own empty-space result.
Spectral permanence and the singly generated continuous calculus are separate
obligations in the plan.
-/

noncomputable section
namespace ExpandedFA.CStar.CommutativeRepresentation.Spec

open Specs.ExpandedFA.BanachAlgebra.Characters
open Specs.ExpandedFA.BanachAlgebra.GelfandTransform
universe u

local instance characterTop (A : Type u) [CommCStarAlgebra A] :
    TopologicalSpace (Character A) := CharacterTopologyValue A

-- This transport works also for the empty character space of the zero algebra.
local instance characterCompact (A : Type u) [CommCStarAlgebra A] :
    CompactSpace (Character A) :=
  (_root_.ExpandedFA.BanachAlgebra.Characters.characterHomeomorph A).symm.compactSpace

/-- Real self-adjoint character values, derived from the actual spectrum. -/
def CharacterReal : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Nontrivial A]
    (χ : Character A) (a : A), IsSelfAdjoint a → (χ.val a).im = 0

def CharacterStar : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Nontrivial A]
    (χ : Character A) (a : A), χ.val (star a) = star (χ.val a)

def TransformStar : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Nontrivial A] (a : A),
    TransformValue A (star a) = star (TransformValue A a)

def TransformNorm : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Nontrivial A] (a : A),
    ‖TransformValue A a‖ = ‖a‖

def TransformIsometry : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Nontrivial A], Isometry (TransformValue A)

def TransformSurjective : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Nontrivial A],
    Function.Surjective (TransformValue A)

/-- The equivalence is exactly the original Gelfand transform, with its
unital complex algebra and involution laws bundled and its isometry explicit. -/
def Representation : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Nontrivial A],
    ∃ e : A ≃⋆ₐ[ℂ] C(Character A, ℂ),
      (∀ a, e a = TransformValue A a) ∧ Isometry e

/-- The zero algebra is represented on its actual empty character space. -/
def ZeroRepresentation : Prop :=
  ∀ (A : Type u) [CommCStarAlgebra A] [Subsingleton A],
    IsEmpty (Character A) ∧
      ∃ e : A ≃⋆ₐ[ℂ] C(Character A, ℂ),
        (∀ (a : A) (χ : Character A), e a χ = χ.val a) ∧ Isometry e

end ExpandedFA.CStar.CommutativeRepresentation.Spec
