import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.SobolevEulerLagrange
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.DominatedEulerLagrange
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

namespace VariationalNotes.Sobolev.EulerLagrange

/-- Substitution of a measurable simple field requires only a.e. measurable
base sections; it does not require choosing a common Borel representative. -/
theorem aemeasurable_simple_field {S E : Type*} [MeasurableSpace S]
    [Nonempty E] {μ : Measure S} {F : S → E → ℝ}
    (hF : ∀ y, AEMeasurable (fun x => F x y) μ) (y : SimpleFunc S E) :
    AEMeasurable (fun x => F x (y x)) μ := by
  classical
  induction y using SimpleFunc.induction' with
  | const c => exact hF c
  | @pcw f g s hs hf hg =>
    have hh : (fun x => F x ((f.piecewise s hs g) x)) =
        s.piecewise (fun x => F x (f x)) (fun x => F x (g x)) := by
      ext x
      by_cases hx : x ∈ s <;> simp [SimpleFunc.coe_piecewise, Set.piecewise, hx]
    rw [hh]
    refine ⟨s.piecewise (hf.mk _) (hg.mk _), ?_, ?_⟩
    · exact hf.measurable_mk.piecewise hs hg.measurable_mk
    · filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hx hy
      by_cases hxs : x ∈ s <;> simp [Set.piecewise, hxs, hx, hy]

/-- The countable-grid limit works directly with Lebesgue measurable sections.
Continuity is required outside one common null set, so the approximations
converge a.e. for every a.e. measurable field. -/
theorem aemeasurable_field_substitution {S E : Type*} [MeasurableSpace S]
    [MeasurableSpace E] [PseudoMetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] [Nonempty E] {μ : Measure S} {F : S → E → ℝ}
    (hF : ∀ y, AEMeasurable (fun x => F x y) μ)
    (hC : ∀ᵐ x ∂μ, Continuous (F x))
    {y : S → E} (hy : AEMeasurable y μ) :
    AEMeasurable (fun x => F x (y x)) μ := by
  let a : E := Classical.ofNonempty
  let yₙ := SimpleFunc.approxOn (hy.mk y) hy.measurable_mk Set.univ a (Set.mem_univ a)
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => aemeasurable_simple_field hF (yₙ n))
  filter_upwards [hC, hy.ae_eq_mk] with x hx hxy
  rw [hxy]
  exact hx.continuousAt.tendsto.comp
    (SimpleFunc.tendsto_approxOn hy.measurable_mk (Set.mem_univ a) (by simp))

/-- Directional derivative along an arbitrary measurable pair of fields. -/
def fieldVariation {d m : ℕ}
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d)
    (u w : Domain d → Vector m) (U W : Domain d → Gradient m d)
    (t : ℝ) (x : Domain d) : ℝ :=
  ⟪Fs x (u x + t • w x) (U x + t • W x), w x⟫_ℝ +
    frobenius (FZ x (u x + t • w x) (U x + t • W x)) (W x)

/-- Domination on a fixed, two-sided interval. This is a proof interface,
not an additional assumption in any of the three source theorems. -/
def SobolevLineDomination {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d) : Prop :=
  ∀ u w : W1p Ω m p, ∃ b : Domain d → ℝ, Integrable b (domainMeasure Ω) ∧
    ∀ᵐ x ∂domainMeasure Ω, ∀ t : ℝ, |t| ≤ 1 →
      |fieldVariation Fs FZ (value Ω m p u) (value Ω m p w)
        (gradient Ω m p u) (gradient Ω m p w) t x| ≤ b x

theorem hasDerivAt_fieldVariation {d m : ℕ}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    {x : Domain d}
    (hF : ∀ y : Vector m × Gradient m d,
      HasFDerivAt (fun y => F x y.1 y.2)
        (fiberDerivative (Fs x y.1 y.2) (FZ x y.1 y.2)) y)
    (u w : Domain d → Vector m) (U W : Domain d → Gradient m d) (t : ℝ) :
    HasDerivAt (fun t => F x (u x + t • w x) (U x + t • W x))
      (fieldVariation Fs FZ u w U W t x) t := by
  have h₁ := (hasDerivAt_const t (u x)).add ((hasDerivAt_id t).smul_const (w x))
  have h₂ := (hasDerivAt_const t (U x)).add ((hasDerivAt_id t).smul_const (W x))
  simpa [Function.comp_def, fiberDerivative, fieldVariation, frobenius] using
    (hF (u x + t • w x, U x + t • W x)).comp_hasDerivAt t (h₁.prodMk h₂)

/-- The representative of a Sobolev line equals the affine line a.e. -/
theorem sobolev_line_representatives {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (u w : W1p Ω m p) (t : ℝ) :
    (value Ω m p (u + t • w) : Domain d → Vector m) =ᵐ[domainMeasure Ω]
      (fun x => value Ω m p u x + t • value Ω m p w x) ∧
    (gradient Ω m p (u + t • w) : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
      (fun x => gradient Ω m p u x + t • gradient Ω m p w x) := by
  constructor
  · simp only [map_add, map_smul]
    filter_upwards [Lp.coeFn_add (value Ω m p u) (t • value Ω m p w),
      Lp.coeFn_smul t (value Ω m p w)] with x ha hs
    simp only [Pi.add_apply, Pi.smul_apply] at ha hs
    exact ha.trans (congrArg (fun y => value Ω m p u x + y) hs)
  · simp only [map_add, map_smul]
    filter_upwards [Lp.coeFn_add (gradient Ω m p u) (t • gradient Ω m p w),
      Lp.coeFn_smul t (gradient Ω m p w)] with x ha hs
    simp only [Pi.add_apply, Pi.smul_apply] at ha hs
    exact ha.trans (congrArg (fun y => gradient Ω m p u x + y) hs)

theorem energy_sobolev_line {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (u w : W1p Ω m p) (t : ℝ) :
    energy Ω m p F (u + t • w) = extendedIntegral (domainMeasure Ω)
      (fun x => F x (value Ω m p u x + t • value Ω m p w x)
        (gradient Ω m p u x + t • gradient Ω m p w x)) := by
  have h := sobolev_line_representatives u w t
  exact energy_congr Ω F h.1 h.2

theorem measurable_sobolev_line {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    (hF : ∀ y : Vector m × Gradient m d,
      AEMeasurable (fun x => F x y.1 y.2) (domainMeasure Ω))
    (hC : ∀ᵐ x ∂domainMeasure Ω,
      Continuous (fun y : Vector m × Gradient m d => F x y.1 y.2))
    (u w : W1p Ω m p) (t : ℝ) :
    AEStronglyMeasurable (fun x => F x
      (value Ω m p u x + t • value Ω m p w x)
      (gradient Ω m p u x + t • gradient Ω m p w x)) (domainMeasure Ω) := by
  apply AEMeasurable.aestronglyMeasurable
  apply aemeasurable_field_substitution (y := fun x =>
    (value Ω m p u x + t • value Ω m p w x,
      gradient Ω m p u x + t • gradient Ω m p w x)) hF hC
  exact ((Lp.aestronglyMeasurable (value Ω m p u)).aemeasurable.add
      ((Lp.aestronglyMeasurable (value Ω m p w)).aemeasurable.const_smul t)).prodMk
    ((Lp.aestronglyMeasurable (gradient Ω m p u)).aemeasurable.add
      ((Lp.aestronglyMeasurable (gradient Ω m p w)).aemeasurable.const_smul t))

/-- A continuous zero-boundary line preserves a minimum relative to an affine submodule. -/
theorem localMinOn_affine_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) {f : E → EReal} {u₀ u : E}
    (hu : u - u₀ ∈ S) (hmin : IsLocalMinOn f {v | v-u₀ ∈ S} u)
    {w : E} (hw : w ∈ S) : IsLocalMin (fun t : ℝ => f (u + t • w)) 0 := by
  have hline : ∀ t : ℝ, u + t • w ∈ {v | v-u₀ ∈ S} := by
    intro t
    change u + t • w - u₀ ∈ S
    rw [add_sub_right_comm]
    exact S.add_mem hu (S.smul_mem t hw)
  have hmin' : IsLocalMinOn f {v | v-u₀ ∈ S} (u + (0 : ℝ) • w) := by simpa using hmin
  have H := hmin'.comp_continuousOn (g := fun t : ℝ => u + t • w)
    (t := {v | v-u₀ ∈ S}) (s := (Set.univ : Set ℝ))
    (fun t _ => hline t) (by fun_prop) (Set.mem_univ (0 : ℝ))
  simpa only [isLocalMinOn_univ_iff, Function.comp_def] using H

/-- The local topology here is the source's Sobolev norm topology. -/
theorem localMin_sobolev_line {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    {F : Domain d → Vector m → Gradient m d → ℝ} {u₀ u : W1p Ω m p}
    (hu : u ∈ affineClass Ω m p u₀)
    (hmin : IsLocalMinOn (energy Ω m p F) (affineClass Ω m p u₀) u)
    (w : W1pZero Ω m p) :
    IsLocalMin (fun t : ℝ => energy Ω m p F (u + t • (w : W1p Ω m p))) 0 :=
  localMinOn_affine_line (zeroSubmodule Ω m p) hu hmin w.property

/-- The analytic core of all-Sobolev-test stationarity, after deriving the
integrable envelope from the source growth hypotheses. -/
theorem stationarity_of_direction_domination {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    (hF : SobolevIntegrandRegularity Ω F Fs FZ)
    {u₀ u : W1p Ω m p} (hu : u ∈ affineClass Ω m p u₀)
    (hf : ∃ r : ℝ, energy Ω m p F u = r)
    (hmin : IsLocalMinOn (energy Ω m p F) (affineClass Ω m p u₀) u)
    (w : W1pZero Ω m p)
    (hdom : ∃ b : Domain d → ℝ, Integrable b (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ t : ℝ, |t| ≤ 1 →
        |fieldVariation Fs FZ (value Ω m p u) (value Ω m p w)
          (gradient Ω m p u) (gradient Ω m p w) t x| ≤ b x) :
    Integrable (sobolevWeakDensity Fs FZ u w) (domainMeasure Ω) ∧
      (∫ x, sobolevWeakDensity Fs FZ u w x ∂domainMeasure Ω) = 0 := by
  obtain ⟨b, hb, hbound⟩ := hdom
  let f : ℝ → Domain d → ℝ := fun t x => F x
    (value Ω m p u x + t • value Ω m p w x)
    (gradient Ω m p u x + t • gradient Ω m p w x)
  let g := fieldVariation Fs FZ (value Ω m p u) (value Ω m p w)
    (gradient Ω m p u) (gradient Ω m p w)
  have hfinite : ∃ r : ℝ, extendedIntegral (domainMeasure Ω) (f 0) = r := by
    simpa [f, energy, energyOnFields, extendedIntegral] using hf
  have hmn : IsLocalMin (fun t => extendedIntegral (domainMeasure Ω) (f t)) 0 := by
    simpa only [energy_sobolev_line] using localMin_sobolev_line hu hmin w
  have hd : ∀ᵐ x ∂domainMeasure Ω, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun t => f t x) (g t x) t := by
    filter_upwards [hF.2] with x hx
    intro t _
    exact hasDerivAt_fieldVariation hx.1 _ _ _ _ t
  have hbd : ∀ᵐ x ∂domainMeasure Ω, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖g t x‖ ≤ b x := by
    filter_upwards [hbound] with x hx
    intro t ht
    exact hx t (by
      have H : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
      exact H.le)
  have H := dominated_line_stationarity (measurable_sobolev_line hF.1 (hF.2.mono fun x hx =>
      continuous_iff_continuousAt.mpr fun y => (hx.1 y).continuousAt) u w)
    hfinite hmn (by norm_num : (0 : ℝ) < 1) hb hd hbd
  have he : g 0 = sobolevWeakDensity Fs FZ u w := by
    funext x
    simp only [g, fieldVariation, sobolevWeakDensity, zero_smul, add_zero]
  rw [he] at H
  exact H

/-- An integrable bound on derivatives on [0,1] makes a finite energy finite
at the other end of the segment. No lower bound on the integrand is used. -/
theorem finite_energy_add_of_line_domination {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    (hF : SobolevIntegrandRegularity Ω F Fs FZ)
    (hdom : SobolevLineDomination (Ω := Ω) (p := p) Fs FZ)
    (u w : W1p Ω m p) (hf : ∃ r : ℝ, energy Ω m p F u = r) :
    ∃ r : ℝ, energy Ω m p F (u + w) = r := by
  let f : ℝ → Domain d → ℝ := fun t x => F x
    (value Ω m p u x + t • value Ω m p w x)
    (gradient Ω m p u x + t • gradient Ω m p w x)
  have hfinite : ∃ r : ℝ, extendedIntegral (domainMeasure Ω) (f 0) = r := by
    simpa [f, energy, energyOnFields, extendedIntegral] using hf
  have hi : Integrable (f 0) (domainMeasure Ω) :=
    integrable_of_extendedIntegral_finite (measurable_sobolev_line hF.1 (hF.2.mono fun x hx =>
      continuous_iff_continuousAt.mpr fun y => (hx.1 y).continuousAt) u w 0).aemeasurable hfinite
  obtain ⟨b, hb, hbound⟩ := hdom u w
  have hdiff : ∀ᵐ x ∂domainMeasure Ω, ‖f 1 x - f 0 x‖ ≤ b x := by
    filter_upwards [hF.2, hbound] with x hx hbx
    apply norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t => f t x)
      (f' := fun t => fieldVariation Fs FZ (value Ω m p u) (value Ω m p w)
        (gradient Ω m p u) (gradient Ω m p w) t x)
    · intro t _
      exact (hasDerivAt_fieldVariation hx.1 _ _ _ _ t).hasDerivWithinAt
    · intro t ht
      exact hbx t (by rw [abs_of_nonneg ht.1]; exact ht.2.le)
  have hnew : Integrable (f 1) (domainMeasure Ω) := by
    apply integrable_of_norm_sub_le (measurable_sobolev_line hF.1 (hF.2.mono fun x hx =>
      continuous_iff_continuousAt.mpr fun y => (hx.1 y).continuousAt) u w 1) hi hb
    filter_upwards [hdiff] with x hx
    exact (norm_sub_rev _ _).trans_le hx
  refine ⟨∫ x, f 1 x ∂domainMeasure Ω, ?_⟩
  have he := energy_sobolev_line F u w 1
  change energy Ω m p F (u + (1 : ℝ) • w) = extendedIntegral (domainMeasure Ω) (f 1) at he
  rw [one_smul] at he
  exact he.trans (extendedIntegral_eq_integral hnew)

/-- Finiteness and stationarity assemble without any density extension or
extra assumption on a minimizer. -/
theorem allTests_of_line_domination {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    (hF : SobolevIntegrandRegularity Ω F Fs FZ)
    (hdom : SobolevLineDomination (Ω := Ω) (p := p) Fs FZ)
    (u₀ : W1p Ω m p) (href : FiniteReference F u₀) : AllTestsConclusion F Fs FZ u₀ := by
  obtain ⟨v, hv, hfinite⟩ := href
  have hall : ∀ u : W1p Ω m p, ∃ r : ℝ, energy Ω m p F u = r := by
    intro u
    have H := finite_energy_add_of_line_domination hF hdom v (u-v) hfinite
    have he : v + (u-v) = u := by abel
    rwa [he] at H
  exact ⟨fun u _ => hall u, fun u hu hm w => stationarity_of_direction_domination hF hu (hall u) hm w (hdom u w)⟩

/-- Cauchy--Schwarz for the state and Frobenius terms, with a single coefficient. -/
theorem abs_pairing_le {d m : ℕ} (a v : Vector m) (A V : Gradient m d) :
    |⟪a,v⟫_ℝ + frobenius A V| ≤ (‖a‖ + ‖A‖) * (‖v‖ + ‖V‖) := by
  calc
    |⟪a,v⟫_ℝ + frobenius A V| ≤ |⟪a,v⟫_ℝ| + |⟪A,V⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖a‖ * ‖v‖ + ‖A‖ * ‖V‖ := add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (‖a‖ + ‖A‖) * (‖v‖ + ‖V‖) := by
      nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg V),
        mul_nonneg (norm_nonneg A) (norm_nonneg v)]

theorem norm_add_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u w : E) {t : ℝ} (ht : |t| ≤ 1) : ‖u + t • w‖ ≤ ‖u‖ + ‖w‖ := by
  calc
    ‖u + t • w‖ ≤ ‖u‖ + ‖t • w‖ := norm_add_le _ _
    _ = ‖u‖ + |t| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖u‖ + ‖w‖ := by nlinarith [norm_nonneg w]

/-- Taking a positive real power changes the Lp exponent by division. -/
theorem memLp_nonneg_rpow {S : Type*} [MeasurableSpace S] {μ : Measure S}
    {a : S → ℝ} {p r : ℝ} (hr : 0 < r)
    (ha : MemLp a (ENNReal.ofReal p) μ) (ha₀ : ∀ x, 0 ≤ a x) :
    MemLp (fun x => a x ^ r) (ENNReal.ofReal (p / r)) μ := by
  have H := ha.norm_rpow_div (ENNReal.ofReal r)
  simpa only [ENNReal.toReal_ofReal hr.le, ← ENNReal.ofReal_div_of_pos hr,
    Real.norm_eq_abs, abs_of_nonneg (ha₀ _)] using H

/-- The pointwise envelope along the full unit line interval. -/
theorem fieldVariation_power_bound {d m : ℕ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    (u w : Domain d → Vector m) (U W : Domain d → Gradient m d)
    {b : Domain d → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) {x : Domain d}
    (hbound : ∀ s Z, ‖Fs x s Z‖ + ‖FZ x s Z‖ ≤ b x + C * (‖s‖ ^ r + ‖Z‖ ^ r))
    {t : ℝ} (ht : |t| ≤ 1) :
    |fieldVariation Fs FZ u w U W t x| ≤
      (|b x| + C * ((‖u x‖ + ‖w x‖) ^ r + (‖U x‖ + ‖W x‖) ^ r)) *
        (‖w x‖ + ‖W x‖) := by
  apply (abs_pairing_le _ _ _ _).trans
  apply mul_le_mul_of_nonneg_right _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  apply (hbound _ _).trans
  apply add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left _ hC)
  exact add_le_add
    (Real.rpow_le_rpow (norm_nonneg _) (norm_add_smul_le _ _ ht) hr)
    (Real.rpow_le_rpow (norm_nonneg _) (norm_add_smul_le _ _ ht) hr)

/-- The p-1 envelope belongs to L1 by Hölder with the exact conjugate exponent. -/
theorem powerGrowth_line_domination {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (hp : 1 < p.real)
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    {b : Domain d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : MemLp b (ENNReal.ofReal (p.real / (p.real - 1))) (domainMeasure Ω))
    (hbound : ∀ᵐ x ∂domainMeasure Ω, ∀ s Z,
      ‖Fs x s Z‖ + ‖FZ x s Z‖ ≤ b x + C * (‖s‖ ^ (p.real-1) + ‖Z‖ ^ (p.real-1))) :
    SobolevLineDomination (Ω := Ω) (p := p) Fs FZ := by
  intro u w
  let a : Domain d → ℝ := fun x => ‖value Ω m p u x‖ + ‖value Ω m p w x‖
  let A : Domain d → ℝ := fun x => ‖gradient Ω m p u x‖ + ‖gradient Ω m p w x‖
  let c : Domain d → ℝ := fun x => ‖value Ω m p w x‖ + ‖gradient Ω m p w x‖
  have ha : MemLp a p.ennreal (domainMeasure Ω) :=
    ((Lp.memLp (value Ω m p u)).norm).add ((Lp.memLp (value Ω m p w)).norm)
  have hA : MemLp A p.ennreal (domainMeasure Ω) :=
    ((Lp.memLp (gradient Ω m p u)).norm).add ((Lp.memLp (gradient Ω m p w)).norm)
  have hc : MemLp c p.ennreal (domainMeasure Ω) :=
    ((Lp.memLp (value Ω m p w)).norm).add ((Lp.memLp (gradient Ω m p w)).norm)
  have har := memLp_nonneg_rpow (sub_pos.mpr hp) ha (fun _ => by dsimp [a]; positivity)
  have hAr := memLp_nonneg_rpow (sub_pos.mpr hp) hA (fun _ => by dsimp [A]; positivity)
  have hd : MemLp (fun x => |b x| + C * (a x ^ (p.real-1) + A x ^ (p.real-1)))
      (ENNReal.ofReal (p.real / (p.real-1))) (domainMeasure Ω) := by
    exact hb.norm.add ((har.add hAr).const_mul C)
  have : ENNReal.HolderConjugate p.ennreal (ENNReal.ofReal (p.real / (p.real-1))) :=
    (Real.HolderConjugate.conjExponent hp).ennrealOfReal
  refine ⟨_, hd.integrable_mul hc, ?_⟩
  filter_upwards [hbound] with x hx
  intro t ht
  exact fieldVariation_power_bound _ _ _ _ hC (sub_nonneg.mpr hp.le) hx ht

/-- At p=1 the same envelope uses L∞ times L1, with no rpow at zero. -/
theorem boundedGrowth_line_domination {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (hp : p.real = 1)
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    {b : Domain d → ℝ} (hb : MemLp b ⊤ (domainMeasure Ω))
    (hbound : ∀ᵐ x ∂domainMeasure Ω, ∀ s Z, ‖Fs x s Z‖ + ‖FZ x s Z‖ ≤ b x) :
    SobolevLineDomination (Ω := Ω) (p := p) Fs FZ := by
  intro u w
  have hc : Integrable (fun x => ‖value Ω m p w x‖ + ‖gradient Ω m p w x‖) (domainMeasure Ω) := by
    apply memLp_one_iff_integrable.mp
    have H := ((Lp.memLp (value Ω m p w)).norm).add ((Lp.memLp (gradient Ω m p w)).norm)
    change MemLp (fun x => ‖value Ω m p w x‖ + ‖gradient Ω m p w x‖) p.ennreal _ at H
    have he : p.ennreal = 1 := by simp only [Exponent.ennreal, hp, ENNReal.ofReal_one]
    exact (congrArg (fun q => MemLp (fun x => ‖value Ω m p w x‖ + ‖gradient Ω m p w x‖)
      q (domainMeasure Ω)) he).mp H
  refine ⟨_, hc.mul_of_top_right hb.norm, ?_⟩
  filter_upwards [hbound] with x hx
  intro t _
  apply (abs_pairing_le _ _ _ _).trans
  exact mul_le_mul_of_nonneg_right ((hx _ _).trans (le_abs_self _)) (by positivity)

/-- Source Theorem 8.14, nonendpoint case. -/
theorem sobolev_euler_lagrange_power : SobolevExpected.PowerGrowth := by
  intro d m hd hm Ω hΩ p hp F Fs FZ hF hgrowth u₀ href
  obtain ⟨b, C, hC, hb, hbound⟩ := hgrowth
  exact allTests_of_line_domination hF (powerGrowth_line_domination hp hC hb hbound) u₀ href

/-- Source Theorem 8.14, endpoint case. -/
theorem sobolev_euler_lagrange_one : SobolevExpected.BoundedGrowth := by
  intro d m hd hm Ω hΩ p hp F Fs FZ hF hgrowth u₀ href
  obtain ⟨b, hb, hbound⟩ := hgrowth
  exact allTests_of_line_domination hF (boundedGrowth_line_domination hp hb hbound) u₀ href

/-- The classical Jacobian of a compactly supported smooth vector test has
compact support as a continuous image, fixing zero, of its Fréchet derivative. -/
theorem hasCompactSupport_testGradient {d m : ℕ} {Ω : Opens (Domain d)}
    (φ : VectorTest Ω m) : HasCompactSupport (testGradient φ) := by
  let G : (Domain d →L[ℝ] Vector m) → Gradient m d := fun L =>
    WithLp.toLp 2 (fun ij => (L (P102.U4.coordinateVector d ij.2)) ij.1)
  have hG : G 0 = 0 := by ext ij; simp [G]
  have h := (φ.hasCompactSupport.fderiv ℝ).comp_left hG
  convert h using 1
  funext x
  simp only [G, testGradient, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply, le_top, ↓reduceIte, Function.comp_apply]

/-- At upper p-growth, the coefficient is integrable and the smooth direction
is essentially bounded. This proof deliberately makes no claim for arbitrary
Sobolev directions. -/
theorem smoothGrowth_domination {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    {b : Domain d → ℝ} {C : ℝ} (hC : 0 ≤ C) (hb : Integrable b (domainMeasure Ω))
    (hbound : ∀ᵐ x ∂domainMeasure Ω, ∀ s Z,
      ‖Fs x s Z‖ + ‖FZ x s Z‖ ≤ b x + C * (‖s‖ ^ p.real + ‖Z‖ ^ p.real))
    (u : W1p Ω m p) (φ : VectorTest Ω m) :
    ∃ B : Domain d → ℝ, Integrable B (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ t : ℝ, |t| ≤ 1 →
        |variationDensity Fs FZ (value Ω m p u) (gradient Ω m p u) φ t x| ≤ B x := by
  let a : Domain d → ℝ := fun x => ‖value Ω m p u x‖ + ‖φ x‖
  let A : Domain d → ℝ := fun x => ‖gradient Ω m p u x‖ + ‖testGradient φ x‖
  have hφ : MemLp φ p.ennreal (domainMeasure Ω) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hDφ : MemLp (testGradient φ) p.ennreal (domainMeasure Ω) :=
    (continuous_testGradient φ).memLp_of_hasCompactSupport (hasCompactSupport_testGradient φ)
  have ha : MemLp a p.ennreal (domainMeasure Ω) := (Lp.memLp (value Ω m p u)).norm.add hφ.norm
  have hA : MemLp A p.ennreal (domainMeasure Ω) := (Lp.memLp (gradient Ω m p u)).norm.add hDφ.norm
  have har : Integrable (fun x => a x ^ p.real) (domainMeasure Ω) := by
    have H := ha.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr p.pos)) (ENNReal.ofReal_ne_top)
    simpa only [Exponent.toReal, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ a _ by dsimp [a]; positivity)] using H
  have hAr : Integrable (fun x => A x ^ p.real) (domainMeasure Ω) := by
    have H := hA.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr p.pos)) (ENNReal.ofReal_ne_top)
    simpa only [Exponent.toReal, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ A _ by dsimp [A]; positivity)] using H
  have hd : Integrable (fun x => |b x| + C * (a x ^ p.real + A x ^ p.real)) (domainMeasure Ω) :=
    hb.norm.add ((har.add hAr).const_mul C)
  have hc : MemLp (fun x => ‖φ x‖ + ‖testGradient φ x‖) ⊤ (domainMeasure Ω) := by
    exact φ.memLp_top.norm.add
      ((continuous_testGradient φ).memLp_top_of_hasCompactSupport (hasCompactSupport_testGradient φ) _).norm
  refine ⟨_, hd.mul_of_top_left hc, ?_⟩
  filter_upwards [hbound] with x hx
  intro t ht
  exact fieldVariation_power_bound _ _ _ _ hC p.pos.le hx ht

/-- Source Theorem 8.14, upper p-growth and smooth tests only. -/
theorem sobolev_euler_lagrange_smooth : SobolevExpected.SmoothTestsGrowth := by
  intro d m hd hm Ω hΩ p F Fs FZ hF hgrowth u₀ u hu hfinite hmin
  obtain ⟨b, C, hC, hb, hbound⟩ := hgrowth
  intro φ
  obtain ⟨w, hw⟩ := smooth_vector_inclusion Ω p φ
  have hz : w ∈ zeroSubmodule Ω m p := by
    change w ∈ (zeroSubmodule Ω m p : Set (W1p Ω m p))
    rw [zero_closure (m := m) Ω p]
    exact subset_closure ⟨φ, hw⟩
  have hv : (value Ω m p w : Domain d → Vector m) =ᵐ[domainMeasure Ω] φ := by
    rw [hw]
    exact MemLp.coeFn_toLp (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
  have hg := gradient_of_smooth_value p φ w hw
  have hdensity : sobolevWeakDensity Fs FZ u w =ᵐ[domainMeasure Ω]
      weakDensity
        (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
        (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ := by
    filter_upwards [hv, hg] with x hx hy
    simp only [sobolevWeakDensity, weakDensity, hx, hy]
  have hdom : ∃ B : Domain d → ℝ, Integrable B (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ t : ℝ, |t| ≤ 1 →
        |fieldVariation Fs FZ (value Ω m p u) (value Ω m p w)
          (gradient Ω m p u) (gradient Ω m p w) t x| ≤ B x := by
    obtain ⟨B, hB, hbd⟩ := smoothGrowth_domination hC hb hbound u φ
    refine ⟨B, hB, ?_⟩
    filter_upwards [hbd, hv, hg] with x hx hy hz
    simpa only [fieldVariation, variationDensity, hy, hz] using hx
  have H := stationarity_of_direction_domination hF hu hfinite hmin ⟨w,hz⟩ hdom
  exact ⟨H.1.congr hdensity, (integral_congr_ae hdensity).symm.trans H.2⟩

end VariationalNotes.Sobolev.EulerLagrange
