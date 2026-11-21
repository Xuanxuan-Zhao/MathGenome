import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootForm

/-! LA-D03, notes/005/lie-algebras-and-representations.tex, theorem
`res:D03` (Root triples and reducedness). The standing hypotheses are finite
dimension and semisimplicity over ℂ, and H is any maximal toral subalgebra.
The form and coroot are precisely those defined from the Killing form in LA-U07.
Root spaces are the ordinary simultaneous eigenspaces of LA-D02. -/

universe u
namespace Specs.LieAlgebrasAndRepresentations.RootTriples

open RootDecomposition RootForm

def rootForm_self_ne_zero_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α : Module.Dual ℂ H, α ∈ rootSet_value H → rootForm_value H α α ≠ 0

def exists_root_triple_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α : Module.Dual ℂ H, α ∈ rootSet_value H →
      ∃ e f : L, e ∈ rootSpace_value H α ∧ f ∈ rootSpace_value H (-α) ∧
        e ≠ 0 ∧ f ≠ 0 ∧
        ⁅e, f⁆ = (coroot_value H α : L) ∧
        ⁅(coroot_value H α : L), e⁆ = (2 : ℂ) • e ∧
        ⁅(coroot_value H α : L), f⁆ = (-2 : ℂ) • f

def finrank_rootSpace_eq_one_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α : Module.Dual ℂ H, α ∈ rootSet_value H →
      Module.finrank ℂ (rootSpace_value H α) = 1

/-- Every complex-proportional root is one of the two opposite roots. -/
def proportional_root_eq_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α β : Module.Dual ℂ H, α ∈ rootSet_value H → β ∈ rootSet_value H →
      ∀ c : ℂ, β = c • α → β = α ∨ β = -α

end Specs.LieAlgebrasAndRepresentations.RootTriples
