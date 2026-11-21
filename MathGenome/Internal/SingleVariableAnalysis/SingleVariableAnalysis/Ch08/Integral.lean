import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.DarbouxSums

/-!
The proper Darboux integral, with its mathematical domain in the type.
All partition sums are the previously defined closed-cell sums. A fixed
partition bounds the opposite family of sums, so completeness applies to
nonempty bounded sets. The scalar interface selects exactly ℝ and ℂ.
-/
namespace SingleVariableAnalysis.Riemann

namespace I
export Specs.SingleVariableAnalysis.Ch08.Integral
  (lowerIntegralValue upperIntegralValue realIntegrableValue realIntegralValue
   complexIntegrableValue complexIntegralValue scalarIntegrableValue scalarIntegralValue)
end I

noncomputable abbrev lowerIntegral := @I.lowerIntegralValue
noncomputable abbrev upperIntegral := @I.upperIntegralValue
abbrev RealIntegrable := I.realIntegrableValue
noncomputable abbrev realIntegral := @I.realIntegralValue
abbrev ComplexIntegrable := I.complexIntegrableValue
noncomputable abbrev complexIntegral := @I.complexIntegralValue
abbrev Integrable := I.scalarIntegrableValue
noncomputable abbrev integral := @I.scalarIntegralValue

theorem partition_exists : Specs.SingleVariableAnalysis.Ch08.Integral.partitionExists := by
  intro a b hab
  rcases lt_or_eq_of_le hab with hlt | rfl
  · exact ⟨uniformPartition hlt 1 (by decide)⟩
  · exact ⟨emptyPartition a⟩

theorem sum_ranges_finite : Specs.SingleVariableAnalysis.Ch08.Integral.sumRangesFinite := by
  intro f a b hab hf
  obtain ⟨P⟩ := partition_exists hab
  refine ⟨⟨lowerSum f P hf, ⟨P, rfl⟩⟩, ⟨upperSum f P hf, ⟨P, rfl⟩⟩,
    ⟨upperSum f P hf, ?_⟩, ⟨lowerSum f P hf, ?_⟩⟩
  · rintro _ ⟨Q, rfl⟩
    exact lower_le_upper f Q P hf
  · rintro _ ⟨Q, rfl⟩
    exact lower_le_upper f P Q hf

theorem lowerIntegral_isLUB : Specs.SingleVariableAnalysis.Ch08.Integral.lowerIsLUB := by
  intro f a b hab hf
  exact isLUB_csSup (sum_ranges_finite f hab hf).1 (sum_ranges_finite f hab hf).2.2.1

theorem upperIntegral_isGLB : Specs.SingleVariableAnalysis.Ch08.Integral.upperIsGLB := by
  intro f a b hab hf
  exact isGLB_csInf (sum_ranges_finite f hab hf).2.1 (sum_ranges_finite f hab hf).2.2.2

theorem lowerIntegral_le_upperIntegral : Specs.SingleVariableAnalysis.Ch08.Integral.lowerLeUpper := by
  intro f a b hab hf
  apply (lowerIntegral_isLUB f hab hf).2
  rintro _ ⟨P, rfl⟩
  apply (upperIntegral_isGLB f hab hf).2
  rintro _ ⟨Q, rfl⟩
  exact lower_le_upper f P Q hf

/-- The boundedness requirement is part of integrability. -/
theorem RealIntegrable.bounded {f : ℝ → ℝ} {a b : ℝ} (h : RealIntegrable f a b) :
    BoundedOnInterval f a b := h.choose_spec.choose

theorem RealIntegrable.ordered {f : ℝ → ℝ} {a b : ℝ} (h : RealIntegrable f a b) :
    a ≤ b := h.choose

theorem realIntegral_common_value : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralCommonValue := by
  intro f a b h hab hf
  exact ⟨rfl, h.choose_spec.choose_spec⟩

theorem realIntegral_bounds : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralBounds := by
  intro f a b h P
  constructor
  · exact (lowerIntegral_isLUB f (RealIntegrable.ordered h) (RealIntegrable.bounded h)).1 ⟨P, rfl⟩
  · rw [(realIntegral_common_value f h (RealIntegrable.ordered h) (RealIntegrable.bounded h)).2]
    exact (upperIntegral_isGLB f (RealIntegrable.ordered h) (RealIntegrable.bounded h)).1 ⟨P, rfl⟩

theorem complexIntegral_components : Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralComponents := by
  intro f a b h
  simp [I.complexIntegralValue]

/-- Every actual real value gives boundedness on a singleton. -/
theorem boundedOnInterval_degenerate (f : ℝ → ℝ) (a : ℝ) : BoundedOnInterval f a a := by
  have heq : f '' Set.Icc a a = {f a} := by simp
  change BddBelow (f '' Set.Icc a a) ∧ BddAbove (f '' Set.Icc a a)
  rw [heq]
  exact ⟨bddBelow_singleton, bddAbove_singleton⟩

theorem degenerate_integral_bounds : Specs.SingleVariableAnalysis.Ch08.Integral.degenerateBounds := by
  intro f a hf
  have hl : Set.range (fun P : Partition a a => lowerSum f P hf) = {0} := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact (degenerate_sums f a P hf).1
    · intro hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      exact ⟨emptyPartition a, (degenerate_sums f a (emptyPartition a) hf).1.trans hx0.symm⟩
  have hu : Set.range (fun P : Partition a a => upperSum f P hf) = {0} := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact (degenerate_sums f a P hf).2
    · intro hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      exact ⟨emptyPartition a, (degenerate_sums f a (emptyPartition a) hf).2.trans hx0.symm⟩
  change sSup _ = 0 ∧ sInf _ = 0
  rw [hl, hu, csSup_singleton, csInf_singleton]
  exact ⟨rfl, rfl⟩

theorem realIntegrable_degenerate (f : ℝ → ℝ) (a : ℝ) : RealIntegrable f a a := by
  let hf := boundedOnInterval_degenerate f a
  exact ⟨le_rfl, hf, (degenerate_integral_bounds f a hf).1.trans
    (degenerate_integral_bounds f a hf).2.symm⟩

theorem realIntegral_degenerate (f : ℝ → ℝ) (a : ℝ) (h : RealIntegrable f a a) :
    realIntegral f h = 0 :=
  (realIntegral_common_value f h le_rfl (RealIntegrable.bounded h)).1.trans
    (degenerate_integral_bounds f a (RealIntegrable.bounded h)).1

theorem integrable_degenerate : Specs.SingleVariableAnalysis.Ch08.Integral.degenerateIntegrable := by
  intro k f a
  cases k with
  | real => exact realIntegrable_degenerate f a
  | complex => exact ⟨realIntegrable_degenerate _ a, realIntegrable_degenerate _ a⟩

theorem integral_degenerate : Specs.SingleVariableAnalysis.Ch08.Integral.degenerateIntegral := by
  intro k f a h
  cases k with
  | real => exact realIntegral_degenerate f a h
  | complex =>
    change complexIntegral f h = 0
    apply Complex.ext
    · exact (complexIntegral_components f h).1.trans (realIntegral_degenerate _ a h.1)
    · exact (complexIntegral_components f h).2.trans (realIntegral_degenerate _ a h.2)

end SingleVariableAnalysis.Riemann
