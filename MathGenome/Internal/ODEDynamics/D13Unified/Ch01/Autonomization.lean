import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.AutonomousParameters
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.IntegralFormulation
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.Autonomization
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set
namespace D13Unified
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[simp] theorem ParameterODE.autonomize_eval (F : ParameterODE E P)
    (q : (ℝ × E) × P) (hq : q ∈ F.domain) :
    F.autonomize.eval q = ((1, F.eval q.1.1 q.1.2 q.2), 0) := by
  classical
  simp [AutonomousODE.eval, ParameterODE.eval, ParameterODE.autonomize,
    Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,
    Specs.D13Unified.Ch01.AutonomousParameters.parameterEvalValue, hq]

/-- Translation preserves all included endpoint derivative conditions. -/
theorem autonomization_lift_iff (F : ParameterODE E P) (p : P)
    (I : TimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) :
    IsParameterIVPOn F p I x s ξ ↔
      IsAutonomousIVPOn F.autonomize (I.elapsed s)
        (autonomizationLift s p x) 0 ((s, ξ), p) := by
  constructor
  · rintro ⟨⟨hc, hg, hd⟩, hs, hx⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (((continuous_const.add continuous_id).continuousOn).prodMk
        (hc.comp (continuous_const.add continuous_id).continuousOn (fun _ h => h))).prodMk
        continuousOn_const
    · intro h hh
      exact hg (s + h) hh
    · intro h hh
      have hx' := (hd (s + h) hh).scomp h
        (((hasDerivAt_id h).const_add s).hasDerivWithinAt)
        (show MapsTo (fun h => s + h) (I.elapsed s).carrier I.carrier from fun _ ht => ht)
      have hh' := (((hasDerivAt_id h).const_add s).hasDerivWithinAt.prodMk
        hx').prodMk (hasDerivWithinAt_const h (I.elapsed s).carrier p)
      change HasDerivWithinAt (autonomizationLift s p x)
        (F.autonomize.eval ((s + h, x (s + h)), p)) _ _
      rw [ParameterODE.autonomize_eval F _ (hg (s + h) hh)]
      change HasDerivWithinAt (fun h => ((s + h, x (s + h)), p))
        ((1, F.eval (s + h) (x (s + h)) p), 0) (I.elapsed s).carrier h
      simpa only [one_smul, Function.comp_def, id_eq, ParameterODE.eval] using hh'
    · simpa only [TimeInterval.elapsed, mem_preimage, add_zero] using hs
    · simp [autonomizationLift, hx]
  · rintro ⟨⟨hc, hg, hd⟩, hs, hx⟩
    have hmap : MapsTo (fun t => t - s) I.carrier (I.elapsed s).carrier := by
      intro t ht
      change s + (t - s) ∈ I.carrier
      simpa using ht
    have hcont := hc.fst.snd.comp (continuous_id.sub continuous_const).continuousOn hmap
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa [autonomizationLift, Function.comp_def] using hcont
    · intro t ht
      have h := hg (t - s) (hmap ht)
      simpa [autonomizationLift, ParameterODE.autonomize] using h
    · intro t ht
      have ht' := hmap ht
      have hd' := hd (t - s) ht'
      change HasDerivWithinAt _ (F.autonomize.eval _) _ _ at hd'
      rw [ParameterODE.autonomize_eval F _ (hg (t - s) ht')] at hd'
      have hstate := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivWithinAt
        (t - s) ((ContinuousLinearMap.fst ℝ (ℝ × E) P).hasFDerivAt.comp_hasDerivWithinAt
          (t - s) hd')
      have hcomp := hstate.scomp t
        (((hasDerivAt_id t).sub_const s).hasDerivWithinAt) hmap
      simpa [autonomizationLift, Function.comp_def, ParameterODE.eval] using hcomp
    · simpa only [TimeInterval.elapsed, mem_preimage, add_zero] using hs
    · have := congrArg (fun q : (ℝ × E) × P => q.1.2) hx
      simpa [autonomizationLift] using this

/-- Integrating the clock and parameter equations identifies every enlarged
solution, without requiring uniqueness of the original equation. -/
theorem autonomization_recover [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval)
    (y : ℝ → (ℝ × E) × P) (s : ℝ) (ξ : E)
    (hy : IsAutonomousIVPOn F.autonomize (I.elapsed s) y 0 ((s, ξ), p)) :
    IsParameterIVPOn F p I (autonomizationRecover s y) s ξ ∧
      ∀ h ∈ (I.elapsed s).carrier, (y h).1.1 = s + h ∧ (y h).2 = p := by
  have hd (h : ℝ) (hh : h ∈ (I.elapsed s).carrier) :
      HasDerivWithinAt y ((1, F.eval (y h).1.1 (y h).1.2 (y h).2), 0)
        (I.elapsed s).carrier h := by
    have hdy := hy.1.2.2 h hh
    change HasDerivWithinAt _ (F.autonomize.eval _) _ _ at hdy
    rwa [ParameterODE.autonomize_eval F _ (hy.1.2.1 h hh)] at hdy
  have hclock (h : ℝ) (hh : h ∈ (I.elapsed s).carrier) :
      HasDerivWithinAt (fun h => (y h).1.1) 1 (I.elapsed s).carrier h := by
    exact (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivWithinAt h
      ((ContinuousLinearMap.fst ℝ (ℝ × E) P).hasFDerivAt.comp_hasDerivWithinAt h (hd h hh))
  have hparam (h : ℝ) (hh : h ∈ (I.elapsed s).carrier) :
      HasDerivWithinAt (fun h => (y h).2) 0 (I.elapsed s).carrier h := by
    exact (ContinuousLinearMap.snd ℝ (ℝ × E) P).hasFDerivAt.comp_hasDerivWithinAt h (hd h hh)
  have hcoords : ∀ h ∈ (I.elapsed s).carrier, (y h).1.1 = s + h ∧ (y h).2 = p := by
    intro h hh
    have hc := integral_eq_sub_on_interval (I.elapsed s).ordConnected
      hy.1.1.fst.fst (continuousOn_const (c := (1 : ℝ))) hclock hy.2.1 hh
    have hp := integral_eq_sub_on_interval (I.elapsed s).ordConnected
      hy.1.1.snd (continuousOn_const (c := (0 : P))) hparam hy.2.1 hh
    have hc0 : (y 0).1.1 = s := congrArg (fun q : (ℝ × E) × P => q.1.1) hy.2.2
    have hp0 : (y 0).2 = p := congrArg Prod.snd hy.2.2
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, hc0] at hc
    simp only [intervalIntegral.integral_zero, hp0] at hp
    exact ⟨by simpa [add_comm] using (sub_eq_iff_eq_add.mp hc.symm), sub_eq_zero.mp hp.symm⟩
  refine ⟨?_, hcoords⟩
  have hmap : MapsTo (fun t => t - s) I.carrier (I.elapsed s).carrier := by
    intro t ht
    simpa [TimeInterval.elapsed] using ht
  refine ⟨⟨hy.1.1.fst.snd.comp (continuous_id.sub continuous_const).continuousOn hmap,
    ?_, ?_⟩, ?_, ?_⟩
  · intro t ht
    have hmem := hy.1.2.1 (t - s) (hmap ht)
    change y (t - s) ∈ F.domain at hmem
    have heq : y (t - s) = ((t, autonomizationRecover s y t), p) := by
      apply Prod.ext
      · apply Prod.ext
        · simpa using (hcoords (t - s) (hmap ht)).1
        · rfl
      · exact (hcoords (t - s) (hmap ht)).2
    rwa [heq] at hmem
  · intro t ht
    have hx := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivWithinAt
      (t - s) ((ContinuousLinearMap.fst ℝ (ℝ × E) P).hasFDerivAt.comp_hasDerivWithinAt
        (t - s) (hd (t - s) (hmap ht)))
    have hx' := hx.scomp t (((hasDerivAt_id t).sub_const s).hasDerivWithinAt) hmap
    have hc := (hcoords (t - s) (hmap ht)).1
    have hp := (hcoords (t - s) (hmap ht)).2
    change HasDerivWithinAt (fun t => (y (t - s)).1.2)
      (F.eval t (y (t - s)).1.2 p) I.carrier t
    simpa [Function.comp_def, hc, hp] using hx'
  · simpa [TimeInterval.elapsed] using hy.2.1
  · simpa [autonomizationRecover] using congrArg (fun q : (ℝ × E) × P => q.1.2) hy.2.2

private def liftIVPCurve (F : ParameterODE E P) (p : P) (I : TimeInterval)
    (s : ℝ) (ξ : E) (x : ParameterIVPCurves F p I s ξ) :
    EnlargedIVPCurves F (I.elapsed s) s ξ p :=
  ⟨fun h => ((s + h.val, x.val ⟨s + h.val, h.property⟩), p), by
    obtain ⟨X, hX, heq⟩ := x.property
    refine ⟨autonomizationLift s p X, (autonomization_lift_iff F p I X s ξ).mp hX, ?_⟩
    intro h
    change ((s + h.val, X (s + h.val)), p) = _
    rw [heq ⟨s + h.val, h.property⟩]⟩

private def recoverIVPCurve [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval) (s : ℝ) (ξ : E)
    (y : EnlargedIVPCurves F (I.elapsed s) s ξ p) : ParameterIVPCurves F p I s ξ :=
  ⟨fun t => (y.val ⟨t.val - s, by simpa [TimeInterval.elapsed] using t.property⟩).1.2, by
    obtain ⟨Y, hY, heq⟩ := y.property
    refine ⟨autonomizationRecover s Y, (autonomization_recover F p I Y s ξ hY).1, ?_⟩
    intro t
    exact congrArg (fun q : (ℝ × E) × P => q.1.2)
      (heq ⟨t.val - s, by simpa [TimeInterval.elapsed] using t.property⟩)⟩

/-- Autonomization is a bijection of all IVP curves on their actual domains.
The formulas also identify the value of any subsequently constructed unique
solution map at absolute time `s + h`. -/
theorem autonomization_bijection [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval) (s : ℝ) (ξ : E) :
    ∃ e : ParameterIVPCurves F p I s ξ ≃ EnlargedIVPCurves F (I.elapsed s) s ξ p,
      (∀ x h, (e x).val h = ((s + h.val, x.val ⟨s + h.val, h.property⟩), p)) ∧
      (∀ y (t : I.carrier), (e.symm y).val t =
        (y.val ⟨t.val - s, by simpa [TimeInterval.elapsed] using t.property⟩).1.2) := by
  refine ⟨{ toFun := liftIVPCurve F p I s ξ
            invFun := recoverIVPCurve F p I s ξ
            left_inv := ?_
            right_inv := ?_ }, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext t
    change x.val ⟨s + (t.val - s), _⟩ = x.val t
    exact congrArg x.val (Subtype.ext (by simp))
  · intro y
    apply Subtype.ext
    funext h
    change ((s + h.val, (y.val ⟨s + h.val - s, _⟩).1.2), p) = y.val h
    have hi : (⟨s + h.val - s, by simpa [TimeInterval.elapsed] using h.property⟩ :
        (I.elapsed s).carrier) = h := Subtype.ext (by simp)
    rw [hi]
    obtain ⟨Y, hY, heq⟩ := y.property
    have hh := (autonomization_recover F p I Y s ξ hY).2 h.val h.property
    rw [heq h] at hh
    exact Prod.ext (Prod.ext hh.1.symm rfl) hh.2.symm
  · intro x h
    rfl
  · intro y t
    rfl

/-- On open intervals the correspondence retains the full C¹ solution notion. -/
theorem autonomization_classical_lift_iff (F : ParameterODE E P) (p : P)
    (I : OpenTimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) :
    IsClassicalParameterIVPOn F p I x s ξ ↔
      IsClassicalAutonomousIVPOn F.autonomize (I.elapsed s)
        (autonomizationLift s p x) 0 ((s, ξ), p) := by
  have hp : IsClassicalParameterIVPOn F p I x s ξ ↔
      IsParameterIVPOn F p I.toTimeInterval x s ξ :=
    and_congr_left fun _ => classicalParameter_iff_solutionOn F p I x
  have ha : IsClassicalAutonomousIVPOn F.autonomize (I.elapsed s)
      (autonomizationLift s p x) 0 ((s, ξ), p) ↔
      IsAutonomousIVPOn F.autonomize (I.toTimeInterval.elapsed s)
        (autonomizationLift s p x) 0 ((s, ξ), p) :=
    and_congr_left fun _ => classicalAutonomous_iff_solutionOn F.autonomize
      (I.elapsed s) (autonomizationLift s p x)
  exact hp.trans ((autonomization_lift_iff F p I.toTimeInterval x s ξ).trans ha.symm)

/-- Specialization to any original uniquely determined curve, without assuming
uniqueness or defining a solution selector in the general correspondence. -/
theorem autonomization_unique_values [FiniteDimensional ℝ P]
    (F : ParameterODE E P) (p : P) (I : TimeInterval) (s : ℝ) (ξ : E) (x : ℝ → E)
    (hu : ∀ z : ℝ → E, IsParameterIVPOn F p I z s ξ → EqOn z x I.carrier)
    (y : ℝ → (ℝ × E) × P)
    (hy : IsAutonomousIVPOn F.autonomize (I.elapsed s) y 0 ((s, ξ), p)) :
    EqOn y (autonomizationLift s p x) (I.elapsed s).carrier := by
  obtain ⟨hrec, hcoords⟩ := autonomization_recover F p I y s ξ hy
  have heq := hu _ hrec
  intro h hh
  have hs := heq hh
  simp only [autonomizationRecover, add_sub_cancel_left] at hs
  have hc := hcoords h hh
  exact Prod.ext (Prod.ext hc.1 hs) hc.2

end D13Unified
