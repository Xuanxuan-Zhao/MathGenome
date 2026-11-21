import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperDefinition
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Integral

/-!
# Proper Riemann integrals with a real parameter

K03.14.proper_definition, paper.tex:3248–3255. Both arguments are real; the
scalar selector gives exactly `ℝ` or `ℂ`. An input `f` is defined only on the
closed integration interval and the chosen parameter set. Its section has a
canonical ambient representative for the upstream Riemann API. A family value
requires membership in the set of parameters with integrable sections.
-/

namespace SingleVariableAnalysis.ParameterIntegral

namespace S
export Specs.SingleVariableAnalysis.Ch14.ProperDefinition
  (sectionValue sectionIntegrableValue parametersValue familyValue)
end S

/-- Extend an interval section by zero to use the shared Riemann interface. -/
noncomputable abbrev parameterSection := @S.sectionValue

/-- Explicit integrability of the `x` section at the real parameter `t`. -/
abbrev SectionIntegrable := @S.sectionIntegrableValue

/-- Precisely the parameters in `T` at which a family value is defined. -/
abbrev properParameters := @S.parametersValue

/-- The proper integral family, defined only on its integrable parameters. -/
noncomputable abbrev properFamily := @S.familyValue

theorem section_on_interval :
    Specs.SingleVariableAnalysis.Ch14.ProperDefinition.sectionOnInterval := by
  intro k a b T f t x
  classical
  exact dite_eq_left x.property

theorem proper_domain_exact :
    Specs.SingleVariableAnalysis.Ch14.ProperDefinition.domainExact := by
  intro k a b T f t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.property, hu⟩
  · rintro ⟨ht, h⟩
    exact ⟨⟨t, ht⟩, h, rfl⟩

theorem proper_family_formula :
    Specs.SingleVariableAnalysis.Ch14.ProperDefinition.familyFormula := by
  intro k a b T f t h
  rfl

theorem proper_family_on_all :
    Specs.SingleVariableAnalysis.Ch14.ProperDefinition.familyOnAll := by
  intro k a b T f h
  exact ⟨fun t => properFamily k f ⟨t, h t⟩, fun _ => ⟨rfl, rfl⟩⟩

theorem proper_domain_all_iff :
    Specs.SingleVariableAnalysis.Ch14.ProperDefinition.domainAllIff := by
  intro k a b T f
  constructor
  · intro h t
    have ht : t ∈ Specs.SingleVariableAnalysis.Ch14.ProperDefinition.parametersValue k f :=
      h.symm ▸ Set.mem_univ t
    exact ht
  · intro h
    exact Set.eq_univ_of_forall h

theorem proper_family_degenerate :
    Specs.SingleVariableAnalysis.Ch14.ProperDefinition.degenerateFamily := by
  intro k a T f
  constructor
  · apply (proper_domain_all_iff k f).2
    intro t
    exact Riemann.integrable_degenerate k (parameterSection k f t) a
  · intro t
    cases k with
    | real =>
      exact Riemann.integral_degenerate .real (parameterSection .real f t.val) a t.property
    | complex =>
      exact Riemann.integral_degenerate .complex (parameterSection .complex f t.val) a t.property

end SingleVariableAnalysis.ParameterIntegral
