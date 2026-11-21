import MathGenome.Internal.Specs.D07.Ch17.SchurNonscalar
import MathGenome.Internal.Specs.D07.Ch23.Frobenius

/-! Independent statement of K07.23.real_schur, paper.tex:7539–7557.
The endomorphism algebra is the existing centralizer subalgebra of
`Module.End ℝ V`, with composition and the inherited real algebra structure.
Irreducibility includes nonzero V. The group is arbitrary.
-/

universe u v
namespace Specs.D07.Ch23.RealSchur

/-- The equivariant endomorphism algebra of a finite-dimensional irreducible
real representation is one of the three real division algebras. -/
def EndomorphismAlternative : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ρ : Representation ℝ G V),
    Representation.IsIrreducible ρ →
    Nonempty (ℝ ≃ₐ[ℝ] Specs.D07.Ch17.SchurNonscalar.endomorphismAlgebraValue ℝ G V ρ) ∨
    Nonempty (ℂ ≃ₐ[ℝ] Specs.D07.Ch17.SchurNonscalar.endomorphismAlgebraValue ℝ G V ρ) ∨
    Nonempty (Quaternion ℝ ≃ₐ[ℝ] Specs.D07.Ch17.SchurNonscalar.endomorphismAlgebraValue ℝ G V ρ)

end Specs.D07.Ch23.RealSchur
