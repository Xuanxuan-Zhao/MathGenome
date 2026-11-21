import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.LatticeFourier
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.CanonicalPathLaw
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.DeterministicTransitions
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory BigOperators

namespace P207.Walk.LatticeFourier

noncomputable section

 theorem step_injective : LatticeFourierSpec.step_injective := by
  intro d ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := by
    by_contra hij
    have hh := congrFun h i
    cases a <;> cases b <;> simp [step, hij] at hh
  subst j
  have hab : a = b := by
    have hh := congrFun h i
    cases a <;> cases b
    · rfl
    · norm_num [step] at hh
    · norm_num [step] at hh
    · rfl
  subst b
  rfl

 theorem stepLaw_step : LatticeFourierSpec.stepLaw_step := by
  intro d _ a
  rw [stepLaw, PMF.map_apply, tsum_eq_single a]
  · simp [choiceLaw, Fintype.card_prod, Nat.mul_comm]
  · intro b hb
    have hn : step a ≠ step b := fun h => hb ((step_injective d h).symm)
    simp [hn]

 theorem stepLaw_elsewhere : LatticeFourierSpec.stepLaw_elsewhere := by
  intro d _ z hz
  rw [stepLaw, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro a
  have hza : z ≠ step a := fun h => hz ⟨a, h.symm⟩
  simp [hza]

 theorem torus_probability : LatticeFourierSpec.torus_probability := fun _ => inferInstance

 theorem phi_representative : LatticeFourierSpec.phi_representative := by
  intro d t
  simp [phi]

 theorem independent_increments : LatticeFourierSpec.independent_increments := by
  intro d _
  exact iIndepFun_infinitePi (X := fun _ (z : Lattice d) => z) (fun _ => measurable_id)

 theorem increment_law : LatticeFourierSpec.increment_law := by
  intro d _ k
  exact Measure.infinitePi_map_eval _ k

 theorem iidWalk_zero {d : ℕ} (x : Lattice d) (ω : ℕ → Lattice d) :
    iidWalk x ω 0 = x := by simp [iidWalk]

 theorem iidWalk_succ {d : ℕ} (x : Lattice d) (ω : ℕ → Lattice d) (n : ℕ) :
    iidWalk x ω (n + 1) = iidWalk x ω n + ω n := by
  simp [iidWalk, Finset.sum_range_succ, add_assoc]

 theorem iidWalk_increment {d : ℕ} (x : Lattice d) (ω : ℕ → Lattice d) (n : ℕ) :
    iidWalk x ω (n + 1) - iidWalk x ω n = ω n := by
  rw [iidWalk_succ, add_sub_cancel_left]

 theorem measurable_iidWalk {d : ℕ} (x : Lattice d) : Measurable (iidWalk x) := by
  apply measurable_pi_iff.mpr
  intro n
  apply measurable_pi_iff.mpr
  intro j
  simp only [iidWalk, Pi.add_apply, Finset.sum_apply]
  fun_prop

 theorem canonical_marginal : LatticeFourierSpec.canonical_marginal := by
  intro d _ x n
  have h := Markov.marginal_law (latticeKernel d) (PMF.pure x)
    Markov.coordinate Markov.coordinateFiltration (latticePathLaw d x)
    (Markov.coordinate_isMarkovChain (latticeKernel d) (PMF.pure x)) n
  unfold Markov.coordinate Markov.evolve at h
  simpa only [PMF.pure_bind] using h

 theorem latticeKernel_apply {d : ℕ} [NeZero d] (x y : Lattice d) :
    latticeKernel d x y = stepLaw d (y - x) := by
  have heq (z : Lattice d) : y = x + z ↔ z = y - x := by
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      rw [h]
      abel
  simp [latticeKernel, PMF.map_apply, heq]

 theorem prefix_iidWalk_iff {d : ℕ} (x : Lattice d) (ω z : ℕ → Lattice d) (n : ℕ) :
    (∀ k ≤ n, iidWalk x ω k = z k) ↔
      x = z 0 ∧ ∀ k < n, ω k = z (k + 1) - z k := by
  constructor
  · intro h
    refine ⟨by simpa [iidWalk] using h 0 (Nat.zero_le _), ?_⟩
    intro k hk
    rw [← h (k + 1) (by omega), ← h k (by omega), iidWalk_increment]
  · rintro ⟨hx, hω⟩ k hk
    induction k with
    | zero => simpa [iidWalk] using hx
    | succ k ih =>
      rw [iidWalk_succ, ih (by omega), hω k (by omega)]
      abel

 theorem iidWalk_pathLaw : LatticeFourierSpec.iidWalk_pathLaw := by
  intro d _ x
  let ρ := (incrementMeasure d).map (iidWalk x)
  have : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_iidWalk x).aemeasurable).mpr inferInstance
  apply Markov.pathLaw_unique (latticeKernel d) (PMF.pure x) ρ
  intro n z
  rw [Measure.map_apply (measurable_iidWalk x) (Markov.measurableSet_prefixCylinder n z)]
  change incrementMeasure d {ω | ∀ k ≤ n, iidWalk x ω k = z k} = _
  simp_rw [prefix_iidWalk_iff]
  by_cases hx : x = z 0
  · have hset : {ω : ℕ → Lattice d | x = z 0 ∧ ∀ k < n, ω k = z (k + 1) - z k} =
        Set.pi (Finset.range n) (fun k => {z (k + 1) - z k}) := by
      ext ω
      simp [hx, Set.mem_pi]
    rw [hset, incrementMeasure, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rw [PMF.pure_apply, ite_eq_left hx.symm, one_mul]
    exact Finset.prod_congr rfl (fun k _ => (latticeKernel_apply (z k) (z (k + 1))).symm)
  · have hz : z 0 ≠ x := Ne.symm hx
    simp [hx, PMF.pure_apply, hz]

/-- The sum of the coordinates modulo two is the bipartite color of a lattice point. -/
def parity {d : ℕ} (x : Lattice d) : ZMod 2 := ∑ j, (x j : ZMod 2)

 theorem parity_zero {d : ℕ} : parity (0 : Lattice d) = 0 := by simp [parity]

 theorem parity_add {d : ℕ} (x y : Lattice d) :
    parity (x + y) = parity x + parity y := by
  simp [parity, Finset.sum_add_distrib]

 theorem parity_step {d : ℕ} (a : StepChoice d) : parity (step a) = 1 := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [parity, step, Pi.single_apply, Finset.sum_ite_eq']

 theorem parity_of_mem_support_power {d : ℕ} [NeZero d] (n : ℕ) (x y : Lattice d)
    (hy : y ∈ (Markov.power (latticeKernel d) n x).support) :
    parity y = parity x + (n : ZMod 2) := by
  induction n generalizing y with
  | zero =>
    have hyx : y = x := by simpa [Markov.power, Markov.identity] using hy
    subst y
    simp
  | succ n ih =>
    change y ∈ ((Markov.power (latticeKernel d) n x).bind (latticeKernel d)).support at hy
    obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hw
    rw [parity_add, parity_step, ih z hz]
    push_cast
    ring

 theorem odd_return : LatticeFourierSpec.odd_return := by
  intro d _ n hn
  by_contra h
  have hs : (0 : Lattice d) ∈ (Markov.power (latticeKernel d) n 0).support := h
  have hp := parity_of_mem_support_power n 0 0 hs
  rw [parity_zero, zero_add] at hp
  exact (Nat.not_even_iff_odd.mpr hn) ((ZMod.natCast_eq_zero_iff_even).mp hp.symm)

 theorem odd_path_return : LatticeFourierSpec.odd_path_return := by
  intro d _ n hn
  have h := congrArg (fun μ : Measure (Lattice d) => μ {0}) (canonical_marginal d 0 n)
  rw [Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  exact h.trans (odd_return d n hn)

/-- The lattice character at frequency `z` on the angular torus. -/
def character {d : ℕ} (z : Lattice d) (t : Torus d) : ℂ :=
  ∏ j : Fin d, fourier (z j) (t j)

 theorem character_zero {d : ℕ} (t : Torus d) : character (0 : Lattice d) t = 1 := by
  simp [character]

 theorem character_add {d : ℕ} (z w : Lattice d) (t : Torus d) :
    character (z + w) t = character z t * character w t := by
  simp only [character, Pi.add_apply, fourier_add, Finset.prod_mul_distrib]

 theorem character_norm {d : ℕ} (z : Lattice d) (t : Torus d) :
    ‖character z t‖ = 1 := by
  simp [character, norm_prod, fourier_apply, Circle.norm_coe]

 theorem continuous_character {d : ℕ} (z : Lattice d) : Continuous (character z) := by
  unfold character
  fun_prop

 theorem character_sum {d : ℕ} (z : ℕ → Lattice d) (n : ℕ) (t : Torus d) :
    character (∑ k ∈ Finset.range n, z k) t = ∏ k ∈ Finset.range n, character (z k) t := by
  induction n with
  | zero => simp [character_zero]
  | succ n ih => rw [Finset.sum_range_succ, character_add, ih, Finset.prod_range_succ]

 theorem integral_fourier (k : ℤ) :
    (∫ t : AddCircle (2 * Real.pi), fourier k t
      ∂@AddCircle.haarAddCircle (2 * Real.pi) ⟨by positivity⟩) = if k = 0 then 1 else 0 := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 2 * Real.pi))) 0 k
  simpa [ContinuousMap.inner_toLp, fourierLp, fourier_zero, eq_comm] using h

 theorem integral_character {d : ℕ} (z : Lattice d) :
    ∫ t : Torus d, character z t ∂torusMeasure d = if z = 0 then 1 else 0 := by
  unfold character torusMeasure
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_fourier]
  by_cases hz : z = 0
  · simp [hz]
  · rw [ite_eq_right hz]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simpa using hj)

 theorem character_single {d : ℕ} (i : Fin d) (t : Torus d) :
    character (Pi.single i 1) t = fourier 1 (t i) := by
  unfold character
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, fourier_zero]
  · simp

 theorem character_neg {d : ℕ} (z : Lattice d) (t : Torus d) :
    character (-z) t = star (character z t) := by
  simp only [character, Pi.neg_apply, fourier_neg, map_prod, Complex.star_def]

 theorem character_step {d : ℕ} (a : StepChoice d) (t : Torus d) :
    character (step a) t = if a.2 then fourier 1 (t a.1) else star (fourier 1 (t a.1)) := by
  rcases a with ⟨i, b⟩
  cases b <;> simp only [step, Bool.false_eq_true, ite_false, ite_true,
    character_neg, character_single]

 theorem fourier_one_angle (t : AddCircle (2 * Real.pi)) :
    fourier 1 t = (Real.Angle.cos t : ℂ) + (Real.Angle.sin t : ℂ) * Complex.I := by
  induction t using QuotientAddGroup.induction_on
  rename_i r
  change fourier 1 (r : AddCircle (2 * Real.pi)) =
    (Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I
  rw [fourier_one]
  rw [AddCircle.toCircle_apply_mk]
  simp [Circle.coe_exp, Complex.exp_mul_I]

 theorem integral_character_stepLaw {d : ℕ} [NeZero d] (t : Torus d) :
    (∫ z, character z t ∂(stepLaw d).toMeasure) = (phi t : ℂ) := by
  have hm : Measurable (fun a : StepChoice d => step a) := measurable_of_countable _
  rw [stepLaw, ← PMF.toMeasure_map step (choiceLaw d) hm,
    integral_map hm.aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    PMF.integral_eq_sum]
  simp only [choiceLaw, PMF.ofFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, character_step]
  rw [Fintype.sum_prod_type]
  have hpair (j : Fin d) : fourier 1 (t j) + star (fourier 1 (t j)) =
      (2 : ℂ) * Real.Angle.cos (t j) := by
    rw [fourier_one_angle]
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, ← smul_add]
  simp_rw [hpair, RCLike.real_smul_eq_coe_mul, ← mul_assoc]
  rw [← Finset.mul_sum]
  unfold phi
  push_cast
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp

 theorem measurable_character {d : ℕ} :
    Measurable (fun p : Torus d × Lattice d => character p.2 p.1) :=
  measurable_from_prod_countable_left (fun z => (continuous_character z).measurable)

 theorem integral_iid_character {d : ℕ} [NeZero d] (n : ℕ) (t : Torus d) :
    (∫ ω, character (iidWalk (0 : Lattice d) ω n) t ∂incrementMeasure d) = (phi t : ℂ) ^ n := by
  have h := integral_restrict_infinitePi (μ := fun _ : ℕ => (stepLaw d).toMeasure)
    (s := Finset.range n) (f := fun ω => ∏ k, character (ω k) t)
    (measurable_of_countable _).aestronglyMeasurable
  calc
    _ = ∫ ω, ∏ k : Finset.range n, character (ω k) t ∂incrementMeasure d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simp only [iidWalk, zero_add, character_sum]
        exact (Finset.prod_coe_sort (Finset.range n) (fun k => character (ω k) t)).symm
    _ = ∫ ω : (k : Finset.range n) → Lattice d, ∏ k, character (ω k) t
          ∂Measure.pi (fun _ : Finset.range n => (stepLaw d).toMeasure) := h
    _ = ∏ k : Finset.range n, ∫ z, character z t ∂(stepLaw d).toMeasure :=
      integral_fintype_prod_eq_prod (fun _ : Finset.range n => fun z : Lattice d => character z t)
    _ = (phi t : ℂ) ^ n := by simp [integral_character_stepLaw]

 theorem iid_return_mass {d : ℕ} [NeZero d] (n : ℕ) :
    incrementMeasure d {ω | iidWalk (0 : Lattice d) ω n = 0} = returnProbability d n := by
  have h := congrArg (fun μ : Measure (Lattice d) => μ {0}) (canonical_marginal d 0 n)
  rw [← iidWalk_pathLaw d 0,
    Measure.map_map (measurable_pi_apply n) (measurable_iidWalk 0),
    Measure.map_apply ((measurable_pi_apply n).comp (measurable_iidWalk 0))
      (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  exact h

 theorem fourier_return (d : ℕ) [NeZero d] (n : ℕ) :
    (returnProbability d n).toReal = ∫ t : Torus d, phi t ^ n ∂torusMeasure d := by
  have hw : Measurable (fun ω : ℕ → Lattice d => iidWalk (0 : Lattice d) ω n) :=
    (measurable_iidWalk (0 : Lattice d)).eval (a := n)
  have hp : Measurable (fun p : Torus d × (ℕ → Lattice d) =>
      (p.1, iidWalk (0 : Lattice d) p.2 n)) :=
    measurable_fst.prodMk (hw.comp measurable_snd)
  have hm := (measurable_character (d := d)).comp hp
  dsimp only [Function.comp_def] at hm
  have hi : Integrable (fun p : Torus d × (ℕ → Lattice d) =>
      character (iidWalk (0 : Lattice d) p.2 n) p.1)
      ((torusMeasure d).prod (incrementMeasure d)) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p =>
        (character_norm (iidWalk (0 : Lattice d) p.2 n) p.1).le)
  have hswap := integral_integral_swap (μ := torusMeasure d) (ν := incrementMeasure d)
    (f := fun t ω => character (iidWalk (0 : Lattice d) ω n) t) hi
  have hs : MeasurableSet {ω | iidWalk (0 : Lattice d) ω n = 0} :=
    measurableSet_eq_fun ((measurable_pi_apply n).comp (measurable_iidWalk 0)) measurable_const
  have hright : (∫ ω, ∫ t : Torus d,
      character (iidWalk (0 : Lattice d) ω n) t ∂torusMeasure d ∂incrementMeasure d) =
      ((returnProbability d n).toReal : ℂ) := by
    simp_rw [integral_character]
    have he : (fun ω => if iidWalk (0 : Lattice d) ω n = 0 then (1 : ℂ) else 0) =
        Set.indicator {ω | iidWalk (0 : Lattice d) ω n = 0} (fun _ => (1 : ℂ)) := by
      ext ω
      simp [Set.indicator]
    rw [he, integral_indicator_const 1 hs, measureReal_def, iid_return_mass]
    simp
  have hleft : (∫ t : Torus d, ∫ ω,
      character (iidWalk (0 : Lattice d) ω n) t ∂incrementMeasure d ∂torusMeasure d) =
      ((∫ t : Torus d, phi t ^ n ∂torusMeasure d : ℝ) : ℂ) := by
    simp only [integral_iid_character, ← Complex.ofReal_pow]
    exact integral_complex_ofReal (f := fun t : Torus d => phi t ^ n) (μ := torusMeasure d)
  exact Complex.ofReal_injective (hright.symm.trans (hswap.symm.trans hleft))

/- Candidate aliases of the shared canonical definitions. -/
abbrev Lattice : LatticeFourierSpec.LatticeType := @P207.Walk.Lattice
abbrev Torus : LatticeFourierSpec.TorusType := @P207.Walk.Torus
abbrev StepChoice : LatticeFourierSpec.StepChoiceType := @P207.Walk.StepChoice
abbrev step : LatticeFourierSpec.stepType := @P207.Walk.step
abbrev choiceLaw : LatticeFourierSpec.choiceLawType := @P207.Walk.choiceLaw
abbrev stepLaw : LatticeFourierSpec.stepLawType := @P207.Walk.stepLaw
abbrev latticeKernel : LatticeFourierSpec.latticeKernelType := @P207.Walk.latticeKernel
abbrev incrementMeasure : LatticeFourierSpec.incrementMeasureType := @P207.Walk.incrementMeasure
abbrev iidWalk : LatticeFourierSpec.iidWalkType := @P207.Walk.iidWalk
abbrev latticePathLaw : LatticeFourierSpec.latticePathLawType := @P207.Walk.latticePathLaw
abbrev torusMeasure : LatticeFourierSpec.torusMeasureType := @P207.Walk.torusMeasure
abbrev phi : LatticeFourierSpec.phiType := @P207.Walk.phi
abbrev returnProbability : LatticeFourierSpec.returnProbabilityType := @P207.Walk.returnProbability

end
end P207.Walk.LatticeFourier
