import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Equivalence

/-!
# Asymptotic equivalence with eventually nonzero denominators

K03.02.equivalence, paper.tex:438–449. Ambient functions are tested along one
filter, which fixes their common domain and approach. All statements specialize
to ℝ and ℂ. Unlike bare Mathlib `IsEquivalent`, this relation retains eventual
nonvanishing as part of its definition.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology
universe u v

/-- The manuscript's ratio definition, with its denominator condition. -/
def ScalarEquivalent {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (f g : X → K) : Prop :=
  (∀ᶠ x in l, g x ≠ 0) ∧ Tendsto (fun x => f x / g x) l (𝓝 1)

section Scalar

variable {X : Type u} {K : Type v} [NormedField K]

/-- The library relation alone does not include the source's nonvanishing. -/
theorem scalarEquivalent_iff_isEquivalent (l : Filter X) (f g : X → K) :
    ScalarEquivalent l f g ↔
      (∀ᶠ x in l, g x ≠ 0) ∧ Asymptotics.IsEquivalent l f g := by
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, (Asymptotics.isEquivalent_iff_tendsto_one hg).mpr h⟩
  · rintro ⟨hg, h⟩
    exact ⟨hg, (Asymptotics.isEquivalent_iff_tendsto_one hg).mp h⟩

/-- The ratio error equals the relative difference error on the nonzero tail. -/
theorem scalarEquivalent_iff_littleO (l : Filter X) (f g : X → K)
    (hg : ∀ᶠ x in l, g x ≠ 0) :
    ScalarEquivalent l f g ↔ ScalarLittleO l (fun x => f x - g x) g := by
  rw [scalarEquivalent_iff_isEquivalent, scalarLittleO_iff_isLittleO]
  exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

/-- A quotient tending to 1 is eventually nonzero, hence so is its numerator. -/
theorem scalarEquivalent_eventually_ne_zero (l : Filter X) (f g : X → K)
    (h : ScalarEquivalent l f g) : ∀ᶠ x in l, f x ≠ 0 := by
  have hratio := h.2.eventually_ne (one_ne_zero : (1 : K) ≠ 0)
  filter_upwards [hratio] with x hx
  exact (div_ne_zero_iff.mp hx).1

theorem scalarEquivalent_isBigO (l : Filter X) (f g : X → K)
    (h : ScalarEquivalent l f g) : ScalarBigO l f g := by
  exact (scalarBigO_iff_isBigO l f g).mpr
    (((scalarEquivalent_iff_isEquivalent l f g).mp h).2.isBigO)

theorem scalarEquivalent_isBigO_reverse (l : Filter X) (f g : X → K)
    (h : ScalarEquivalent l f g) : ScalarBigO l g f := by
  exact (scalarBigO_iff_isBigO l g f).mpr
    (((scalarEquivalent_iff_isEquivalent l f g).mp h).2.isBigO_symm)

theorem scalarEquivalent_symm (l : Filter X) (f g : X → K)
    (h : ScalarEquivalent l f g) : ScalarEquivalent l g f := by
  apply (scalarEquivalent_iff_isEquivalent l g f).mpr
  exact ⟨scalarEquivalent_eventually_ne_zero l f g h,
    ((scalarEquivalent_iff_isEquivalent l f g).mp h).2.symm⟩

theorem scalarEquivalent_trans (l : Filter X) (f g h : X → K)
    (hfg : ScalarEquivalent l f g) (hgh : ScalarEquivalent l g h) :
    ScalarEquivalent l f h := by
  apply (scalarEquivalent_iff_isEquivalent l f h).mpr
  exact ⟨hgh.1, ((scalarEquivalent_iff_isEquivalent l f g).mp hfg).2.trans
    ((scalarEquivalent_iff_isEquivalent l g h).mp hgh).2⟩

theorem scalarEquivalent_refl (l : Filter X) (f : X → K)
    (hf : ∀ᶠ x in l, f x ≠ 0) : ScalarEquivalent l f f := by
  exact (scalarEquivalent_iff_isEquivalent l f f).mpr
    ⟨hf, Asymptotics.IsEquivalent.refl⟩

end Scalar

/-- The five explicit real approaches use the same nonzero tail and ratio limit.
The nontriviality premise is precisely the upstream finite-limit convention. -/
theorem scalarEquivalent_approach_iff {K : Type v} [NormedField K]
    (E : Set ℝ) (q : RealApproach) (f g : ℝ → K) (ha : ApproachNontrivial E q) :
    ScalarEquivalent (RealApproachFilter E q) f g ↔
      ApproachEventually E q (fun x => g x ≠ 0) ∧
        FiniteApproachLimit (fun x => f x / g x) E q 1 := by
  simp only [ScalarEquivalent, FiniteApproachLimit, ha, true_and,
    Metric.tendsto_nhds, approachEventually_filter_iff]

/-- Metric finite-point approaches include real and complex input domains.
As with the upstream punctured limit, no accumulation is needed for this bridge. -/
theorem scalarEquivalent_punctured_iff {X : Type u} {K : Type v}
    [MetricSpace X] [NormedField K] (E : Set X) (a : X) (f g : X → K) :
    ScalarEquivalent (PuncturedDomainFilter E a) f g ↔
      (∀ᶠ x in PuncturedDomainFilter E a, g x ≠ 0) ∧
        RelativePuncturedLimit (fun x => f x / g x) E a 1 := by
  rw [ScalarEquivalent, relativePuncturedLimit_filter_iff]

end SingleVariableAnalysis
