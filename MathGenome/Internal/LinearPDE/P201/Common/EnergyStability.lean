import MathGenome.Internal.LinearPDE.P201Specs.Common.EnergyStability

namespace P201.Common.EnergyStability

universe u v w

/-- Interpret an initial observation (including the prescribed time derivatives)
in the chosen classical or energy solution class. -/
def CauchyData : P201Specs.Common.EnergyStability.CauchyDataType.{u,v} :=
  P201Specs.Common.EnergyStability.CauchyDataValue

/-- Interpret the classical restriction or Sobolev boundary observation. -/
def BoundaryData : P201Specs.Common.EnergyStability.BoundaryDataType.{u,v} :=
  P201Specs.Common.EnergyStability.BoundaryDataValue

/-- Prescribe the initial and boundary observations together. -/
def InitialBoundaryData :
    P201Specs.Common.EnergyStability.InitialBoundaryDataType.{u,v,w} :=
  P201Specs.Common.EnergyStability.InitialBoundaryDataValue

/-- Hadamard's three requirements for the specified spaces and problem relation. -/
def HadamardWellPosed : P201Specs.Common.EnergyStability.HadamardWellPosedType.{u,v} :=
  P201Specs.Common.EnergyStability.HadamardWellPosedValue

theorem hadamard_iff_continuous_graph :
    P201Specs.Common.EnergyStability.HadamardGraphStatement.{u,v} := by
  intro D S _ _ solves
  constructor
  · rintro ⟨_, unique, F, hF, solvesF⟩
    exact ⟨F, hF, fun d s => ⟨fun hs => unique d s (F d) hs (solvesF d),
      fun hs => hs ▸ solvesF d⟩⟩
  · rintro ⟨F, hF, graph⟩
    exact ⟨fun d => ⟨F d, (graph d (F d)).2 rfl⟩,
      fun d s₁ s₂ h₁ h₂ => ((graph d s₁).1 h₁).trans ((graph d s₂).1 h₂).symm,
      F, hF, fun d => (graph d (F d)).2 rfl⟩

theorem energy_vanishes :
    P201Specs.Common.EnergyStability.EnergyVanishesStatement.{u} := by
  intro T t₀ E C hnonneg hbound hzero t
  exact le_antisymm (by simpa [hzero] using hbound t) (hnonneg t)

theorem energy_uniqueness :
    P201Specs.Common.EnergyStability.EnergyUniquenessStatement.{u,v} := by
  intro T X _ t₀ u v E C K hnonneg hcontrol hbound hzero
  have hE := energy_vanishes t₀ E C hnonneg hbound hzero
  funext t
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hsq : ‖u t - v t‖ ^ 2 = 0 :=
    le_antisymm (by simpa [hE t] using hcontrol t) (sq_nonneg _)
  exact sq_eq_zero_iff.mp hsq

theorem same_data_uniqueness :
    P201Specs.Common.EnergyStability.SameDataUniquenessStatement.{u,v,w} := by
  intro T X D _ solves t₀ energy C K h d u v hu hv
  rcases h d u v hu hv with ⟨hnonneg, hcontrol, hbound, hzero⟩
  exact energy_uniqueness t₀ u v (energy u v) C K hnonneg hcontrol hbound hzero

theorem norm_stability :
    P201Specs.Common.EnergyStability.NormStabilityStatement.{u,v} := by
  intro D X _ _ d e x y C hsq
  have h := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_mul' C (sq_nonneg ‖d - e‖)] using h

theorem energy_stability :
    P201Specs.Common.EnergyStability.EnergyStabilityStatement.{u,v,w} := by
  intro T D X _ _ t₀ d e u v E C hinitial hexact hbound t
  apply norm_stability d e (u t) (v t) C
  simpa only [hinitial, hexact] using hbound t

theorem stability_continuity :
    P201Specs.Common.EnergyStability.StabilityContinuityStatement.{u,v} := by
  intro D X _ _ solutionMap C hsq
  have hLip : LipschitzWith ⟨Real.sqrt C, Real.sqrt_nonneg C⟩ solutionMap := by
    apply LipschitzWith.of_dist_le_mul
    intro d e
    rw [dist_eq_norm_sub, dist_eq_norm_sub]
    exact norm_stability d e (solutionMap d) (solutionMap e) C (hsq d e)
  exact ⟨hLip, hLip.continuous⟩

end P201.Common.EnergyStability
