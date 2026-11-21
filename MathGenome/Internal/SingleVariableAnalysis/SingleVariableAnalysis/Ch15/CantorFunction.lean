import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.CantorFunction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.CantorStaircaseLimit
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.CantorSet
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.Monotone
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Linarith

/-! The fixed-point construction is the upstream staircase, not an arbitrary
singular function. Induction on the finite deletion stages gives local constancy:
rescale a point in the left/right third and use the preceding stage; points in
the middle third have value 1/2. A connectedness argument then gives constancy
on every complementary interval. All differentiation is elementary local
constancy, with no differentiation-of-measures theorem. -/
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology

/-- The Cantor function, named here as an alias of the prescribed constructed limit. -/
noncomputable def cantorFunction : ℝ → ℝ := cantorStaircase

private theorem staircase_left {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hl : x ≤ 1/3) : cantorStaircase x = cantorStaircase (3*x)/2 := by
  rw [cantorStaircase_fixedPoint x hx]
  unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
  rw [ite_eq_left hl]

private theorem staircase_middle {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hl : 1/3 < x) (hr : x ≤ 2/3) : cantorStaircase x = 1/2 := by
  rw [cantorStaircase_fixedPoint x hx]
  unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
  rw [ite_eq_right (not_le.mpr hl), ite_eq_left hr]

private theorem staircase_right {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hr : 2/3 < x) : cantorStaircase x = 1/2 + cantorStaircase (3*x-2)/2 := by
  rw [cantorStaircase_fixedPoint x hx]
  unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
  rw [ite_eq_right (by linarith), ite_eq_right (not_le.mpr hr)]

/-- Every point excluded by a finite stage has a neighborhood on which the
constructed limit is constant. -/
theorem cantorStaircase_locallyConstant_off_stage (n : ℕ) :
    ∀ x ∈ Icc (0 : ℝ) 1, x ∉ cantorStage n →
      ∀ᶠ y in 𝓝 x, cantorStaircase y = cantorStaircase x := by
  induction n with
  | zero => intro x hx hn; exact (hn hx).elim
  | succ n ih =>
    intro x hx hn
    have h0 : (0 : ℝ) ∈ cantorStage (n+1) := zero_mem_preCantorSet _
    have h1 : (1 : ℝ) ∈ cantorStage (n+1) :=
      mem_iInter.mp one_mem_middleThirdsSet _
    have hx0 : 0 < x := lt_of_le_of_ne hx.1 (fun he => hn (he ▸ h0))
    have hx1 : x < 1 := lt_of_le_of_ne hx.2 (fun he => hn (he.symm ▸ h1))
    by_cases hl : x ≤ 1/3
    · have hpre : 3*x ∉ cantorStage n := by
        intro h
        exact hn (Or.inl ⟨3*x, h, by ring⟩)
      have hlt : x < 1/3 := by
        apply lt_of_le_of_ne hl
        intro he
        apply hpre
        have h1n : (1 : ℝ) ∈ cantorStage n := mem_iInter.mp one_mem_middleThirdsSet _
        have heq : 3*x = (1 : ℝ) := by linarith
        rw [heq]
        exact h1n
      have hlocal := ih (3*x) ⟨by linarith, by linarith⟩ hpre
      have hcomp : ∀ᶠ y in 𝓝 x,
          cantorStaircase (3*y) = cantorStaircase (3*x) :=
        (continuousAt_const.mul continuousAt_id).tendsto.eventually hlocal
      filter_upwards [hcomp, Ioo_mem_nhds hx0 hlt] with y hy hyI
      rw [staircase_left ⟨hyI.1.le, by linarith [hyI.2]⟩ hyI.2.le,
        staircase_left hx hl, hy]
    · by_cases hr : x < 2/3
      · filter_upwards [Ioo_mem_nhds (lt_of_not_ge hl) hr] with y hy
        rw [staircase_middle ⟨by linarith [hy.1], by linarith [hy.2]⟩ hy.1 hy.2.le,
          staircase_middle hx (lt_of_not_ge hl) hr.le]
      · have hpre : 3*x-2 ∉ cantorStage n := by
          intro h
          exact hn (Or.inr ⟨3*x-2, h, by ring⟩)
        have hgt : 2/3 < x := by
          apply lt_of_le_of_ne (le_of_not_gt hr)
          intro he
          apply hpre
          have heq : 3*x-2 = (0 : ℝ) := by linarith
          rw [heq]
          exact zero_mem_preCantorSet n
        have hlocal := ih (3*x-2) ⟨by linarith, by linarith⟩ hpre
        have hcomp : ∀ᶠ y in 𝓝 x,
            cantorStaircase (3*y-2) = cantorStaircase (3*x-2) :=
          ((continuousAt_const.mul continuousAt_id).sub continuousAt_const).tendsto.eventually hlocal
        filter_upwards [hcomp, Ioo_mem_nhds hgt hx1] with y hy hyI
        rw [staircase_right ⟨by linarith [hyI.1], hyI.2.le⟩ hyI.1,
          staircase_right hx hgt, hy]

theorem cantorStaircase_regularity :
    Specs.SingleVariableAnalysis.Ch15.CantorFunction.regularity :=
  cantorStaircase_limitProperties

theorem cantorStaircase_locallyConstantOff :
    Specs.SingleVariableAnalysis.Ch15.CantorFunction.locallyConstantOff := by
  intro x hx
  have hn : ∃ n, x ∉ cantorStage n := by
    have hxD : x ∉ middleThirdsSet := hx.2
    simpa only [middleThirdsSet, mem_iInter, not_forall] using hxD
  obtain ⟨n, hn⟩ := hn
  exact cantorStaircase_locallyConstant_off_stage n x hx.1 hn

theorem cantorStaircase_constantOnComplementaryIntervals :
    Specs.SingleVariableAnalysis.Ch15.CantorFunction.constantOnComplementaryIntervals := by
  intro S hS hsub x hx y hy
  let _ : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hlocal : IsLocallyConstant (fun z : S => cantorStaircase z) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuous_subtype_val.continuousAt.tendsto.eventually
      (cantorStaircase_locallyConstantOff z (hsub z.property))
  exact hlocal.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

theorem cantorStaircase_derivativeZeroOff :
    Specs.SingleVariableAnalysis.Ch15.CantorFunction.derivativeZeroOff := by
  intro x hx
  have hd : HasDerivAt cantorStaircase 0 x :=
    (hasDerivAt_const x (cantorStaircase x)).congr_of_eventuallyEq
      (cantorStaircase_locallyConstantOff x hx)
  exact ⟨hd, (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr hd, hd.deriv⟩

theorem cantorStaircase_exceptionalLengthZero :
    Specs.SingleVariableAnalysis.Ch15.CantorFunction.exceptionalLengthZero :=
  cantor_lengthZero

theorem cantorStaircase_nonconstant :
    Specs.SingleVariableAnalysis.Ch15.CantorFunction.nonconstant := by
  rintro ⟨c, hc⟩
  have h0 := hc 0 (by norm_num)
  have h1 := hc 1 (by norm_num)
  change cantorStaircase 0 = c at h0
  change cantorStaircase 1 = c at h1
  rw [cantorStaircase_limitProperties.2.2.1] at h0
  rw [cantorStaircase_limitProperties.2.2.2.1] at h1
  linarith

theorem cantorStaircase_variationOne :
    Specs.SingleVariableAnalysis.Ch15.CantorFunction.variationOne := by
  have h := BV.hasBoundedVariation_of_monotone cantorStaircase
    (show (0 : ℝ) ≤ 1 by norm_num) (Or.inl cantorStaircase_limitProperties.2.1)
  have hv := BV.totalVariation_of_monotoneOn cantorStaircase
    (show (0 : ℝ) ≤ 1 by norm_num) cantorStaircase_limitProperties.2.1
  change BV.totalVariation cantorStaircase 0 1 = _ at hv
  rw [cantorStaircase_limitProperties.2.2.1,
    cantorStaircase_limitProperties.2.2.2.1] at hv
  norm_num at hv
  refine ⟨h.1, hv, ?_⟩
  change (BV.totalVariation cantorStaircase 0 1).toReal = 1
  rw [hv]
  norm_num

end SingleVariableAnalysis
