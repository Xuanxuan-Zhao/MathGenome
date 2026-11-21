import MathGenome.Internal.Specs.D07.Ch10.EuclideanAlgorithm
import MathGenome.Internal.D07.Ch10.EuclideanDefinition
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The extended Euclidean algorithm for the source's well-founded division data.
No `EuclideanDomain` instance, gcd operation, or normalization is assumed. -/

universe u

namespace D07.Ch10.EuclideanAlgorithm

open Specs.D07.Ch10.EuclideanAlgorithm
open Specs.D07.Ch10.EuclideanDefinition Specs.D07.Ch10.GcdLcm

theorem algorithmTerminates : AlgorithmTerminates.{u} := by
  intro R _ _ d a b
  classical
  induction b using d.wellFounded.induction generalizing a with
  | h b ih =>
    by_cases hb : b = 0
    · subst b
      exact ⟨a, 0, .stop a⟩
    · rcases d.decrease a b hb with hr | hr
      · exact ⟨b, 1, .step hb (d.division a b hb) (Or.inl hr)
          (hr ▸ DivisionRun.stop b)⟩
      · obtain ⟨g, n, hn⟩ := ih (d.remainder a b) hr b
        exact ⟨g, n + 1, .step hb (d.division a b hb) (Or.inr hr) hn⟩

theorem noInfiniteDivisions : NoInfiniteDivisions.{u} := by
  intro R _ _ d s hs
  classical
  by_contra h
  have hn : ∀ n, s (n + 1) ≠ 0 := by
    intro n hz
    exact h ⟨n, hz⟩
  have hdesc : ∀ n, d.smaller (s (n + 2)) (s (n + 1)) := by
    intro n
    obtain ⟨q, _, hr⟩ := hs n (hn n)
    exact hr.resolve_left (hn (n + 1))
  exact (wellFounded_iff_isEmpty_descending_chain.mp d.wellFounded).false
    ⟨fun n => s (n + 1), hdesc⟩

theorem commonDivisorsStep : CommonDivisorsStep.{u} := by
  intro R _ _ a b q r c hab
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨hb, ?_⟩
    have hr : r = a - q * b := by rw [hab]; ring
    rw [hr]
    exact dvd_sub ha (dvd_mul_of_dvd_right hb q)
  · rintro ⟨hb, hr⟩
    refine ⟨?_, hb⟩
    rw [hab]
    exact dvd_add (dvd_mul_of_dvd_right hb q) hr

theorem runCorrect : RunCorrect.{u} := by
  intro R _ _ d a b g n hrun
  induction hrun with
  | stop a =>
    exact ⟨⟨dvd_refl a, dvd_zero a, fun _ hc _ => hc⟩,
      1, 0, by simp⟩
  | @step a b q r g n hb hdiv hdecrease tail ih =>
    obtain ⟨hg, x, y, hxy⟩ := ih
    have hcommon := commonDivisorsStep R a b q r
    refine ⟨?_, y, x - y * q, ?_⟩
    · have hgab := (hcommon g hdiv).mpr ⟨hg.1, hg.2.1⟩
      exact ⟨hgab.1, hgab.2, fun c hca hcb =>
        hg.2.2 c ((hcommon c hdiv).mp ⟨hca, hcb⟩).1
          ((hcommon c hdiv).mp ⟨hca, hcb⟩).2⟩
    · calc
        g = x * b + y * r := hxy
        _ = y * (q * b + r) +
              (x - y * q) * b := by ring
        _ = y * a + (x - y * q) * b := by rw [← hdiv]

theorem lastNonzero : LastNonzero.{u} := by
  intro R _ _ d a b g n hrun
  have hg := (runCorrect R d a b g n hrun).1
  constructor
  · intro hgn
    by_cases ha : a = 0
    · right
      intro hb
      have hz : g = 0 := by
        have hzero : IsGcd R (0 : R) 0 g := by simpa [ha, hb] using hg
        exact zero_dvd_iff.mp (hzero.2.2 0 (dvd_refl 0) (dvd_refl 0))
      exact hgn hz
    · exact Or.inl ha
  · intro hab hgz
    have ha : a = 0 := zero_dvd_iff.mp (hgz ▸ hg.1)
    have hb : b = 0 := zero_dvd_iff.mp (hgz ▸ hg.2.1)
    exact hab.elim (fun h => h ha) (fun h => h hb)

theorem extendedGcdExists : ExtendedGcdExists.{u} := by
  intro R _ _ hEuclidean a b
  obtain ⟨d⟩ := (D07.Ch10.EuclideanDefinition.divisionDataCharacterization R).mpr hEuclidean
  obtain ⟨g, n, hn⟩ := algorithmTerminates R d a b
  exact ⟨g, runCorrect R d a b g n hn⟩

theorem zeroInputs : ZeroInputs.{u} := by
  intro R _ _ d a
  exact ⟨.stop a, .stop 0⟩

theorem integerNonuniqueDivision : IntegerNonuniqueDivision := by
  unfold IntegerNonuniqueDivision
  decide

theorem nonnegativeIntegerConvention : NonnegativeIntegerConvention := by
  refine ⟨by decide, by decide, ?_⟩
  intro q r h hr0 hr2
  omega

end D07.Ch10.EuclideanAlgorithm
