import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected

/-! The data and predicates in Definition IG01 of the source. -/

namespace Specs.GaloisFormalization.IG

universe u v w

-- The types below retain independent universes for all three groups.
set_option linter.checkUnivs false

/-- Two continuous group epimorphisms from a profinite group and a finite
discrete group to a common finite discrete quotient. -/
structure FiniteEmbeddingProblem (Γ : Type u) (B : Type v) (Q : Type w)
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q] where
  rho : Γ →ₜ* Q
  pi : B →ₜ* Q
  rho_surjective : Function.Surjective rho
  pi_surjective : Function.Surjective pi

def FiniteEmbeddingProblemType :=
  ∀ (Γ : Type u) (B : Type v) (Q : Type w)
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q], Type (max u v w)

def finiteEmbeddingProblemValue : FiniteEmbeddingProblemType.{u, v, w} :=
  fun Γ B Q => FiniteEmbeddingProblem Γ B Q

namespace FiniteEmbeddingProblem

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- A continuous lift through the prescribed quotient map. -/
structure WeakSolution (P : FiniteEmbeddingProblem Γ B Q) where
  lift : Γ →ₜ* B
  commutes : P.pi.comp lift = P.rho

def KernelType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
    FiniteEmbeddingProblem Γ B Q → Subgroup B

abbrev kernel (P : FiniteEmbeddingProblem Γ B Q) : Subgroup B := P.pi.toMonoidHom.ker

def KernelInclusionType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q), P.kernel →ₜ* B

def kernelInclusion (P : FiniteEmbeddingProblem Γ B Q) : P.kernel →ₜ* B :=
  ⟨(P.pi.toMonoidHom.ker).subtype, continuous_subtype_val⟩

def WeakSolutionType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
    FiniteEmbeddingProblem Γ B Q → Type (max u v)

def weakSolutionValue (P : FiniteEmbeddingProblem Γ B Q) : Type (max u v) :=
  WeakSolution P

def IsProperType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {P : FiniteEmbeddingProblem Γ B Q}, P.WeakSolution → Prop

def isProperValue {P : FiniteEmbeddingProblem Γ B Q} : P.WeakSolution → Prop :=
  fun s => Function.Surjective s.lift

def ProblemPredicateType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
    FiniteEmbeddingProblem Γ B Q → Prop

def isSplitValue : FiniteEmbeddingProblem Γ B Q → Prop :=
  fun P => ∃ s : Q →* B, P.pi.toMonoidHom.comp s = MonoidHom.id Q

def isCentralValue : FiniteEmbeddingProblem Γ B Q → Prop :=
  fun P => P.pi.toMonoidHom.ker ≤ Subgroup.center B

end FiniteEmbeddingProblem
end Specs.GaloisFormalization.IG
