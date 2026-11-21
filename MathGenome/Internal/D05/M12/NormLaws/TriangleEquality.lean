import MathGenome.Internal.Specs.D05.M12.NormLaws.TriangleEquality
import MathGenome.Internal.D05.M12.NormLaws

/-! The full triangle-equality corollary and its complex-phase guard. -/

namespace D05.M12.NormLaws.TriangleEquality

theorem triangle_equality :
    Specs.D05.M12.NormLaws.TriangleEquality.triangle_equality :=
  @D05.M12.NormLaws.triangle_equality

theorem triangle_equality_of_ne_zero :
    Specs.D05.M12.NormLaws.TriangleEquality.triangle_equality_of_ne_zero :=
  @D05.M12.NormLaws.triangle_equality_of_ne_zero

theorem firstInner_triangle_equality :
    Specs.D05.M12.NormLaws.TriangleEquality.firstInner_triangle_equality :=
  @D05.M12.NormLaws.firstInner_triangle_equality

theorem firstInner_triangle_equality_of_ne_zero :
    Specs.D05.M12.NormLaws.TriangleEquality.firstInner_triangle_equality_of_ne_zero := by
  intro F V _ _ _ u v hu
  simpa only [Norm.inducedNorm_eq_norm (F := F)] using
    triangle_equality_of_ne_zero (firstInner (F := F)) InnerProduct.firstInner_axioms u v hu

/-- A quarter-turn gives a dependent pair but cannot be a real multiple of a
nonzero vector: scalar cancellation followed by imaginary parts gives `1 = 0`. -/
theorem complex_phase_counterexample :
    Specs.D05.M12.NormLaws.TriangleEquality.complex_phase_counterexample := by
  intro V _ _ h hh u hu
  have hiu : Complex.I • u ≠ 0 := smul_ne_zero Complex.I_ne_zero hu
  refine ⟨hiu, ?_, ?_⟩
  · apply (CauchySchwarz.pair_dependent_iff u (Complex.I • u)).mpr
    right
    refine ⟨-Complex.I, ?_⟩
    simp [smul_smul]
  · intro he
    obtain ⟨t, _, ht⟩ := (triangle_equality_of_ne_zero h hh u (Complex.I • u) hu).mp he
    have hi : Complex.I = (t : ℂ) := (smul_left_injective ℂ hu) ht
    have him := congrArg Complex.im hi
    simp at him

theorem firstInner_complex_phase_counterexample :
    Specs.D05.M12.NormLaws.TriangleEquality.firstInner_complex_phase_counterexample := by
  intro V _ _ u hu
  simpa only [Norm.inducedNorm_eq_norm (F := ℂ)] using
    complex_phase_counterexample (firstInner (F := ℂ)) InnerProduct.firstInner_axioms u hu

end D05.M12.NormLaws.TriangleEquality
