import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeReplacement
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeFiltrationTransport

/-! Both K-tests for the semifree replacements of Result U02. -/

namespace DerivedFormalization.SemifreeReplacement

open Specs.DerivedFormalization.SemifreeReplacement

universe u v t

theorem adequateReplacement : AdequateReplacement.{u,v,t} := by
  intro R _ X
  obtain ⟨F, p, hp, hsurj, ⟨filtration⟩, hproj, horig, hcohom⟩ :=
    SemifreeModels.adequateResolution.{u,v,t} R X
  exact ⟨F, p, hp, hsurj, ⟨filtration⟩, hproj,
    SemifreeFiltrationTransport.filtrationIsKFlat _ filtration, horig, hcohom⟩

theorem nativeReplacement : NativeReplacement.{u,v} := by
  intro R _ _ X
  obtain ⟨F, p, hp, hsurj, ⟨filtration⟩, hproj⟩ :=
    SemifreeModels.nativeResolution.{u,v} R X
  exact ⟨F, p, hp, hsurj, ⟨filtration⟩, hproj,
    SemifreeFiltrationTransport.filtrationIsKFlat _ filtration⟩

theorem diagonalReplacement : DiagonalReplacement.{u} := by
  intro R _ X
  obtain ⟨F, p, hp, hsurj, hfiltration, hproj⟩ := SemifreeModels.diagonalResolution R X
  have comparison := SemifreeFiltrationTransport.diagonal F
  obtain ⟨filtration⟩ := comparison.1.mpr hfiltration
  exact ⟨F, p, hp, hsurj, hfiltration, hproj,
    comparison.2.mp (SemifreeFiltrationTransport.filtrationIsKFlat _ filtration)⟩

end DerivedFormalization.SemifreeReplacement
