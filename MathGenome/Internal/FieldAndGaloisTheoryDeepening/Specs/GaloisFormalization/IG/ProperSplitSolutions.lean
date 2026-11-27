import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.EmbeddingProblem
import Mathlib.GroupTheory.SemidirectProduct

/-! Specifications for the properness criterion and split solutions of IG06. -/

namespace Specs.GaloisFormalization.IG.FiniteEmbeddingProblem

universe u v w

-- Keep the three group universes independent in the specification types.
set_option linter.checkUnivs false

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- The left action on the actual kernel by conjugation through `s`. -/
def sectionAction (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B) :
    Q →* MulAut P.kernel :=
  (MulAut.conjNormal : B →* MulAut P.pi.toMonoidHom.ker).comp s

def SectionActionType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q), (Q →* B) → (Q →* MulAut P.kernel)

/-- Continuous maps satisfying the multiplicative crossed-homomorphism law. -/
abbrev ContinuousCrossedHom (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B) :=
  {z : C(Γ, P.kernel) // ∀ γ η : Γ,
    z (γ * η) = z γ * sectionAction P s (P.rho γ) (z η)}

def ContinuousCrossedHomType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
    FiniteEmbeddingProblem Γ B Q → (Q →* B) → Type (max u v)

def ImageSurjectsOntoQuotientType : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {P : FiniteEmbeddingProblem Γ B Q} (sol : P.WeakSolution),
    Function.Surjective (fun h : sol.lift.toMonoidHom.range => P.pi (h : B))

def ImageInfKernelType : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {P : FiniteEmbeddingProblem Γ B Q} (sol : P.WeakSolution),
    sol.lift.toMonoidHom.range ⊓ P.kernel =
      P.rho.toMonoidHom.ker.map sol.lift.toMonoidHom

def ProperIffMapKernelType : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {P : FiniteEmbeddingProblem Γ B Q} (sol : P.WeakSolution),
    isProperValue sol ↔ P.rho.toMonoidHom.ker.map sol.lift.toMonoidHom = P.kernel

def SplitMulEquivExistsType : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B),
    P.pi.toMonoidHom.comp s = MonoidHom.id Q →
    ∃ e : SemidirectProduct P.kernel Q (sectionAction P s) ≃* B,
      (∀ x, e x = (x.left : B) * s x.right) ∧
      (∀ b, (e.symm b).right = P.pi b)

def CrossedHomEquivWeakSolutionExistsType : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B),
    P.pi.toMonoidHom.comp s = MonoidHom.id Q →
    ∃ e : ContinuousCrossedHom P s ≃ P.WeakSolution,
      (∀ z γ, (e z).lift γ = (z.val γ : B) * s (P.rho γ)) ∧
      (∀ sol γ, ((e.symm sol).val γ : B) = sol.lift γ * (s (P.rho γ))⁻¹)

def CrossedHomRestrictionAndPropernessType : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) (s : Q →* B),
    P.pi.toMonoidHom.comp s = MonoidHom.id Q →
    ∀ z : ContinuousCrossedHom P s,
      ∃ f : P.rho.toMonoidHom.ker →* P.kernel,
        (∀ n, f n = z.val (n : Γ)) ∧
        ∀ sol : P.WeakSolution,
          (∀ γ, sol.lift γ = (z.val γ : B) * s (P.rho γ)) →
          (isProperValue sol ↔ Function.Surjective f)

end Specs.GaloisFormalization.IG.FiniteEmbeddingProblem
