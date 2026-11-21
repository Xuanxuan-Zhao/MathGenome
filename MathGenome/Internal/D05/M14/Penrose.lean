import MathGenome.Internal.Specs.D05.M14.Penrose
import MathGenome.Internal.D05.M14.Penrose.Projections
import MathGenome.Internal.D05.M14.Penrose.Uniqueness

/-! K05.14.penrose: the projection identities, four equations, and their
converse, assembled from the two proved prerequisite stages. -/

namespace D05.M14.Penrose

theorem projection_identities : Specs.D05.M14.Penrose.projection_identities := by
  intro F V W _ _ _ _ _ _ _ T
  exact ⟨Projections.map_comp_pseudoinverse T, Projections.pseudoinverse_comp_map T⟩

theorem four_identities : Specs.D05.M14.Penrose.four_identities := by
  intro F V W _ _ _ _ _ _ _ T
  exact ⟨Projections.map_pseudoinverse_map T,
    Projections.pseudoinverse_map_pseudoinverse T,
    Projections.map_comp_pseudoinverse_adjoint T,
    Projections.pseudoinverse_comp_map_adjoint T⟩

theorem characterization : Specs.D05.M14.Penrose.characterization := by
  intro F V W _ _ _ _ _ _ _ T X
  constructor
  · rintro ⟨hTXT, hXTX, hTXsa, hXTsa⟩
    exact Uniqueness.uniqueness T X hTXT hXTX hTXsa hXTsa
  · rintro rfl
    exact four_identities T

end D05.M14.Penrose
