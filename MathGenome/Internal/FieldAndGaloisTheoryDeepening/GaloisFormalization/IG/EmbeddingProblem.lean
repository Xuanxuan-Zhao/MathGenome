import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.EmbeddingProblem

namespace GaloisFormalization.IG

universe u v w

variable (Γ : Type u) (B : Type v) (Q : Type w)
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- The pair of continuous surjections defining a finite embedding problem. -/
abbrev FiniteEmbeddingProblem :=
  Specs.GaloisFormalization.IG.FiniteEmbeddingProblem Γ B Q

namespace FiniteEmbeddingProblem

export Specs.GaloisFormalization.IG.FiniteEmbeddingProblem (mk)

variable {Γ B Q}

/-- The kernel of the finite quotient map as a subgroup of the middle group. -/
abbrev kernel (P : FiniteEmbeddingProblem Γ B Q) : Subgroup B :=
  P.pi.toMonoidHom.ker

/-- The continuous inclusion of the kernel in the middle group. -/
def kernelInclusion (P : FiniteEmbeddingProblem Γ B Q) : P.kernel →ₜ* B :=
  ⟨P.kernel.subtype, continuous_subtype_val⟩

/-- A continuous homomorphism into the middle group lifting the prescribed surjection. -/
abbrev WeakSolution (P : FiniteEmbeddingProblem Γ B Q) :=
  Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.WeakSolution P

namespace WeakSolution

export Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.WeakSolution (mk)

variable {P : FiniteEmbeddingProblem Γ B Q}

/-- A weak solution is proper when its lift is surjective. -/
def IsProper (s : P.WeakSolution) : Prop :=
  Function.Surjective s.lift

@[simp] theorem commutes_apply (s : P.WeakSolution) (γ : Γ) :
    P.pi (s.lift γ) = P.rho γ :=
  DFunLike.congr_fun s.commutes γ

end WeakSolution

/-- A problem is split when the finite quotient map has a homomorphic section. -/
def IsSplit (P : FiniteEmbeddingProblem Γ B Q) : Prop :=
  ∃ s : Q →* B, P.pi.toMonoidHom.comp s = MonoidHom.id Q

/-- A problem is central when its kernel is contained in the centre of the middle group. -/
def IsCentral (P : FiniteEmbeddingProblem Γ B Q) : Prop :=
  P.kernel ≤ Subgroup.center B

end FiniteEmbeddingProblem
end GaloisFormalization.IG
