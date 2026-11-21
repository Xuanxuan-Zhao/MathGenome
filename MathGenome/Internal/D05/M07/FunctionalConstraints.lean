import MathGenome.Internal.Specs.D05.M07.FunctionalConstraints
import MathGenome.Internal.D05.M07.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! K05.07.functional_constraints: finite redundant linear constraints on an
arbitrary vector space. -/

namespace D05.M07.FunctionalConstraints

theorem mem_span_iff_iInf_ker_le :
    Specs.D05.M07.FunctionalConstraints.mem_span_iff_iInf_ker_le := by
  intro K V _ _ _ r f g
  constructor
  · intro hg v hv
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hg
    have hf : ∀ i, f i v = 0 := fun i =>
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv i)
    simp [LinearMap.mem_ker, hf]
  · exact _root_.mem_span_of_iInf_ker_le_ker

theorem mem_span_iff_vanishes :
    Specs.D05.M07.FunctionalConstraints.mem_span_iff_vanishes := by
  intro K V _ _ _ r f g
  rw [mem_span_iff_iInf_ker_le r f g]
  change (∀ v, v ∈ (⨅ i, LinearMap.ker (f i)) → v ∈ LinearMap.ker g) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

theorem exists_coefficients_iff_vanishes :
    Specs.D05.M07.FunctionalConstraints.exists_coefficients_iff_vanishes := by
  intro K V _ _ _ r f g
  rw [← mem_span_iff_vanishes r f g, Submodule.mem_span_range_iff_exists_fun K]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext v
    simpa using (ha v).symm
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro v
    simpa using (congrArg (fun h : Module.Dual K V => h v) ha).symm

theorem empty_constraints :
    Specs.D05.M07.FunctionalConstraints.empty_constraints := by
  intro K V _ _ _ f g
  have hs : Submodule.span K (Set.range f) = ⊥ := by simp
  have hi : (⨅ i, LinearMap.ker (f i)) = ⊤ := by simp
  refine ⟨hs, hi, ?_, ?_⟩
  · simp
  · rw [← mem_span_iff_iInf_ker_le 0 f g]
    simp

end D05.M07.FunctionalConstraints
