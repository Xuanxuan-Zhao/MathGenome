import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.PendulumPortrait
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.FirstIntegral
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.Lyapunov
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.LinearizedStability
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped Topology
namespace D13Unified.Ch13.PendulumPortrait
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch12.StabilityDefinitions
open Specs.D13Unified.Ch12.Lyapunov
open Ch06.StateDerivative

@[simp] lemma pendulum_eval (z : Plane) : pendulum.eval z = vectorField z := by
  simp [AutonomousODE.eval, autonomousEvalValue, pendulum]

lemma vectorField_contDiff : ContDiff ℝ 1 vectorField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1
  · exact ((contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).sin).neg

lemma energy_contDiff : ContDiff ℝ 1 energy := by
  exact (((contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1).pow 2).div_const 2).add contDiff_const |>.sub
    ((contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).cos)

theorem regularity : Specs.D13Unified.Ch13.PendulumPortrait.Regularity :=
  ⟨vectorField_contDiff, energy_contDiff⟩

lemma pendulum_regular : ContDiffOn ℝ 1 pendulum.eval pendulum.domain := by
  rw [show pendulum.eval = vectorField from funext pendulum_eval]
  exact vectorField_contDiff.contDiffOn

lemma energy_fderiv (z v : Plane) :
    (fderiv ℝ energy z) v = z 1 * v 1 + Real.sin (z 0) * v 0 := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 1 z).pow 2).mul_const (1/2 : ℝ)).add_const 1).sub
    ((Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z (hasFDerivAt_apply 0 z))
  have he : ((fun x : Plane => x 1 ^ 2 * (1/2 : ℝ) + 1) -
      Real.cos ∘ (fun x : Plane => x 0)) = energy := by
    ext x
    simp [energy, div_eq_mul_inv]
  rw [he] at hd
  rw [hd.fderiv]
  simp
  ring

lemma energy_lie (z : Plane) : (fderiv ℝ energy z) (pendulum.eval z) = 0 := by
  rw [energy_fderiv, pendulum_eval]
  simp [vectorField]
  ring

theorem energy_conserved : Specs.D13Unified.Ch13.PendulumPortrait.Conservation := by
  exact Ch11.FirstIntegral.conservation pendulum pendulum_regular energy
    energy_contDiff.contDiffOn (fun z _ => energy_lie z)

lemma sin_center (k : ℤ) : Real.sin (2 * (k : ℝ) * Real.pi) = 0 := by
  convert Real.sin_int_mul_pi (2*k) using 1 <;> push_cast <;> ring
lemma cos_center (k : ℤ) : Real.cos (2 * (k : ℝ) * Real.pi) = 1 := by
  convert Real.cos_int_mul_two_pi k using 1 <;> ring
lemma sin_saddle (k : ℤ) : Real.sin ((2 * (k : ℝ) + 1) * Real.pi) = 0 := by
  convert Real.sin_int_mul_pi (2*k+1) using 1 <;> push_cast <;> ring
lemma cos_saddle (k : ℤ) : Real.cos ((2 * (k : ℝ) + 1) * Real.pi) = -1 := by
  convert Real.cos_int_mul_two_pi_add_pi k using 1 <;> ring

theorem equilibria : Specs.D13Unified.Ch13.PendulumPortrait.Equilibria := by
  intro k
  constructor <;> ext i <;> fin_cases i <;>
    simp [vectorField, center, saddle, sin_center, sin_saddle]

/-- Coordinates centered at p; the original whole-plane equation is retained. -/
def shifted (p : Plane) : AutonomousODE Plane where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun z => vectorField (z.val + p)
  continuous_field := vectorField_contDiff.continuous.comp
    (continuous_subtype_val.add continuous_const)

@[simp] lemma shifted_eval (p z : Plane) : (shifted p).eval z = vectorField (z + p) := by
  simp [AutonomousODE.eval, autonomousEvalValue, shifted]

lemma shifted_regular (p : Plane) : ContDiffOn ℝ 1 (shifted p).eval (shifted p).domain := by
  rw [show (shifted p).eval = (fun z => vectorField (z+p)) from funext (shifted_eval p)]
  exact (vectorField_contDiff.comp (contDiff_id.add (contDiff_const (c := p)))).contDiffOn

lemma translated_flow (p x : Plane) :
    (flowInterval pendulum (x+p)).carrier = (flowInterval (shifted p) x).carrier ∧
      ∀ t ∈ (flowInterval (shifted p) x).carrier,
        flow pendulum t (x+p) = flow (shifted p) t x + p := by
  have hX := flow_ivp pendulum pendulum_regular (show x+p ∈ pendulum.domain from mem_univ _)
  have hY := flow_ivp (shifted p) (shifted_regular p)
    (show x ∈ (shifted p).domain from mem_univ _)
  have hplus : classicalIVPOnValue pendulum.toODE (flowInterval (shifted p) x)
      (fun t => flow (shifted p) t x + p) 0 (x+p) := by
    refine ⟨⟨hY.1.1.add contDiffOn_const, fun _ _ => mem_univ _, ?_⟩,
      hY.2.1, by simpa only using congrArg (fun z => z+p) hY.2.2⟩
    intro t ht
    simpa only [AutonomousODE.toODE_eval, shifted_eval, pendulum_eval] using
      (hY.1.2.2 t ht).add_const p
  have hminus : classicalIVPOnValue (shifted p).toODE (flowInterval pendulum (x+p))
      (fun t => flow pendulum t (x+p) - p) 0 x := by
    refine ⟨⟨hX.1.1.sub contDiffOn_const, fun _ _ => mem_univ _, ?_⟩,
      hX.2.1, by simpa only [add_sub_cancel_right] using congrArg (fun z => z-p) hX.2.2⟩
    intro t ht
    simpa only [AutonomousODE.toODE_eval, shifted_eval, pendulum_eval, sub_add_cancel] using
      (hX.1.2.2 t ht).sub_const p
  have hp := (ODE.canonical_solution pendulum.toODE
    (pendulum.locallyLipschitzInState_of_contDiffOn pendulum_regular)
    0 (x+p) (mem_univ _)).2.2.2.2.2.1 _ _ hplus
  have hm := (ODE.canonical_solution (shifted p).toODE
    ((shifted p).locallyLipschitzInState_of_contDiffOn (shifted_regular p))
    0 x (mem_univ _)).2.2.2.2.2.1 _ _ hminus
  exact ⟨Subset.antisymm hm.1 hp.1, fun t ht => hp.2 ht⟩

lemma shifted_equilibrium (p : Plane) (heq : vectorField p = 0) :
    (shifted p).eval 0 = 0 := by simpa using heq

/-- Stability transport includes equality of the actual maximal lifespans. -/
lemma stable_iff_shifted (p : Plane) (heq : vectorField p = 0) :
    StableAt p ↔ lyapunovStableValue (shifted p) (shifted_regular p)
      (mem_univ _) (shifted_equilibrium p heq) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x _ hx
    have hs : dist (x+p) p < δ := by simpa [dist_eq_norm] using hx
    obtain ⟨hc, hstay⟩ := hb (x+p) hs
    have htr := translated_flow p x
    refine ⟨fun t ht => ⟨mem_univ _, htr.1 ▸ hc t ht⟩, ?_⟩
    intro t ht
    have hh := hstay t ht
    rw [htr.2 t (htr.1 ▸ hc t ht)] at hh
    simpa [dist_eq_norm] using hh
  · intro h ε hε
    obtain ⟨δ, hδ, hb⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro z hz
    obtain ⟨hc, hstay⟩ := hb (z-p) (mem_univ _) (by simpa [dist_eq_norm] using hz)
    have htr := translated_flow p (z-p)
    simp only [sub_add_cancel] at htr
    have htime (t : ℝ) (ht : 0 ≤ t) := htr.1.symm ▸ (hc t ht).2
    refine ⟨htime, ?_⟩
    intro t ht
    rw [htr.2 t (hc t ht).2]
    simpa [dist_eq_norm] using hstay t ht

lemma energy_positive {z : Plane} (hz : ‖z‖ < Real.pi) (hne : z ≠ 0) : 0 < energy z := by
  have hx : |z 0| < Real.pi := (norm_le_pi_norm z 0).trans_lt hz
  have hp := Real.pi_pos
  by_cases h0 : z 0 = 0
  · have h1 : z 1 ≠ 0 := by
      intro h1
      apply hne
      ext i
      fin_cases i <;> simp_all
    have := sq_pos_of_ne_zero h1
    simp only [energy, h0, Real.cos_zero]
    linarith
  · have hc : Real.cos (z 0) < 1 := lt_of_le_of_ne (Real.cos_le_one _)
      (fun he => h0 ((Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [(abs_lt.mp hx).1]) (by linarith [(abs_lt.mp hx).2])).mp he))
    dsimp [energy]
    nlinarith [sq_nonneg (z 1)]

lemma energy_add_center (z : Plane) (k : ℤ) : energy (z + center k) = energy z := by
  have hc : Real.cos (z 0 + 2 * (k : ℝ) * Real.pi) = Real.cos (z 0) := by
    convert Real.cos_add_int_mul_two_pi (z 0) k using 1 <;> congr 1 <;> ring
  simp [energy, center, hc]

lemma shifted_center_eval (z : Plane) (k : ℤ) :
    (shifted (center k)).eval z = pendulum.eval z := by
  have hs : Real.sin (z 0 + 2 * (k : ℝ) * Real.pi) = Real.sin (z 0) := by
    convert Real.sin_add_int_mul_two_pi (z 0) k using 1 <;> congr 1 <;> ring
  simp [shifted_eval, pendulum_eval, vectorField, center, hs]

theorem strict_energy_minima : Specs.D13Unified.Ch13.PendulumPortrait.StrictMinima := by
  intro k
  refine ⟨Real.pi, Real.pi_pos, ?_⟩
  intro z hz hne
  have hp := energy_positive (z := z - center k) (by simpa [dist_eq_norm] using hz)
    (sub_ne_zero.mpr hne)
  have hh := energy_add_center (z - center k) k
  simp only [sub_add_cancel] at hh
  have hec : energy (center k) = 0 := by simp [energy, center, cos_center]
  rw [hec, hh]
  exact hp

theorem centers_stable : Specs.D13Unified.Ch13.PendulumPortrait.CenterStability := by
  intro k
  apply (stable_iff_shifted (center k) (equilibria k).1).mpr
  apply Ch12.Lyapunov.stability (shifted (center k)) (shifted_regular _) (mem_univ _)
    (shifted_equilibrium _ (equilibria k).1) (ball 0 Real.pi) isOpen_ball
    (mem_ball_self Real.pi_pos) (subset_univ _) energy energy_contDiff.contDiffOn
    (by simp [energy])
    (fun z hz hne => energy_positive (by simpa using hz) hne)
  intro z _
  change (fderiv ℝ energy z) ((shifted (center k)).eval z) ≤ 0
  rw [shifted_center_eval, energy_lie]

/-- The true Fréchet derivative in the standard plane coordinates. -/
def jacobian (z : Plane) : Plane →L[ℝ] Plane :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj (1 : Fin 2),
    (-Real.cos (z 0)) • ContinuousLinearMap.proj (0 : Fin 2)]

lemma vectorField_hasFDerivAt (z : Plane) : HasFDerivAt vectorField (jacobian z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply 1 z
  · have hd := ((Real.hasDerivAt_sin (z 0)).comp_hasFDerivAt z
      (hasFDerivAt_apply (𝕜 := ℝ) 0 z)).neg
    convert hd using 1 <;> ext v <;> simp [vectorField] <;> ring

lemma fderiv_saddle_apply (k : ℤ) (v : Plane) :
    (fderiv ℝ vectorField (saddle k)) v = ![v 1, v 0] := by
  rw [(vectorField_hasFDerivAt _).fderiv]
  ext i
  fin_cases i <;> simp [jacobian, saddle, cos_saddle]

theorem saddle_eigenvalues : Specs.D13Unified.Ch13.PendulumPortrait.SaddleEigenvalues := by
  intro k
  constructor
  · apply Module.End.hasEigenvalue_of_hasEigenvector (x := (![1, 1] : Plane))
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · change (fderiv ℝ vectorField (saddle k)) _ = _
      rw [fderiv_saddle_apply]
      simp
    · intro h
      have := congrFun h 0
      norm_num at this
  · apply Module.End.hasEigenvalue_of_hasEigenvector (x := (![1, -1] : Plane))
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · change (fderiv ℝ vectorField (saddle k)) _ = _
      rw [fderiv_saddle_apply]
      ext i
      fin_cases i <;> norm_num
    · intro h
      have := congrFun h 0
      norm_num at this

lemma shifted_fderiv (p : Plane) : fderiv ℝ (shifted p).eval 0 = fderiv ℝ vectorField p := by
  have hi : HasFDerivAt (fun z : Plane => z+p) (ContinuousLinearMap.id ℝ Plane) 0 :=
    (hasFDerivAt_id (0 : Plane)).add_const p
  have hd := (vectorField_hasFDerivAt ((0 : Plane)+p)).comp 0 hi
  rw [show (shifted p).eval = (fun z => vectorField (z+p)) from funext (shifted_eval p)]
  calc
    _ = jacobian p := by simpa only [zero_add, ContinuousLinearMap.comp_id, Function.comp_def] using! hd.fderiv
    _ = _ := (vectorField_hasFDerivAt p).fderiv.symm

lemma saddle_matrix (k : ℤ) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2))
      (fderiv ℝ (shifted (saddle k)).eval 0).toLinearMap = !![0, 1; 1, 0] := by
  rw [shifted_fderiv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, fderiv_saddle_apply, Pi.basisFun_apply]

theorem saddles_unstable : Specs.D13Unified.Ch13.PendulumPortrait.SaddleInstability := by
  intro k hs
  have hspec : ∃ μ : ℂ, 0 < μ.re ∧ Module.End.HasEigenvalue
      (Matrix.toLinAlgEquiv'
        ((LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2))
          (fderiv ℝ (shifted (saddle k)).eval 0).toLinearMap).map Complex.ofReal)) μ := by
    refine ⟨1, by norm_num, ?_⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (![1, 1] : Fin 2 → ℂ))
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · rw [saddle_matrix]
      ext i
      fin_cases i <;> norm_num [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · intro h
      have := congrFun h 0
      norm_num at this
  have hinst := (Ch12.LinearizedStability.linearized_instability
    (Pi.basisFun ℝ (Fin 2)) (shifted (saddle k)) (shifted_regular _) (mem_univ _)
    (shifted_equilibrium _ (equilibria k).2) hspec).2
  exact hinst ((stable_iff_shifted _ (equilibria k).2).mp hs)

end D13Unified.Ch13.PendulumPortrait
