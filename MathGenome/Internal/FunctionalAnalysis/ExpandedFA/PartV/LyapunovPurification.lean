import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.LyapunovPurification
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Finite-dimensional Lyapunov purification

This module proves that every extreme point of a moment fiber is an indicator,
by splitting a positive fractional band into n+1 positive pieces and finding a
nonzero relation between their n moment vectors. The perturbation is nonzero
in the ordinary a.e. quotient and is scaled by an explicit positive factor.

The functional-analytic stage represents the dual order interval by bounded
densities using Hilbert-space Riesz representation on L². Banach–Alaoglu and
closed integral tests give compactness of every moment fiber in exactly
σ(L∞, L¹). Krein–Milman's extreme-point lemma and the bang-bang argument
then give unconditional purification, including dimension zero and zero measure.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.PartV.LyapunovPurification

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- Products against an L∞ density are integrable for every integrable test. -/
theorem integrable_density_mul (g : Lp ℝ ∞ μ) {h : X → ℝ} (hh : Integrable h μ) :
    Integrable (fun x => g x * h x) μ :=
  hh.mul_of_top_right (Lp.memLp g)

/-- Moment integrals are linear on the actual L∞ quotient. -/
def momentLinear {n : ℕ} (h : Fin n → X → ℝ) (hh : ∀ j, Integrable (h j) μ) :
    Lp ℝ ∞ μ →ₗ[ℝ] (Fin n → ℝ) where
  toFun g j := ∫ x, g x * h j x ∂μ
  map_add' f g := by
    funext j
    calc
      (∫ x, (f + g) x * h j x ∂μ) =
          ∫ x, f x * h j x + g x * h j x ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [Pi.add_apply] at hx
        rw [hx, add_mul]
      _ = _ := integral_add (integrable_density_mul f (hh j))
        (integrable_density_mul g (hh j))
  map_smul' c g := by
    funext j
    calc
      (∫ x, (c • g) x * h j x ∂μ) = ∫ x, c * (g x * h j x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c g] with x hx
        simp only [Pi.smul_apply, smul_eq_mul] at hx
        rw [hx, mul_assoc]
      _ = _ := integral_const_mul c _

/-- A moment fiber is real-convex. -/
theorem densityFiber_convex {n : ℕ} (h : Fin n → X → ℝ)
    (hh : ∀ j, Integrable (h j) μ) (b : Fin n → ℝ) :
    Convex ℝ (Spec.densityFiber μ h b) := by
  intro f hf g hg a c ha hc hac
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1, Lp.coeFn_add (a • f) (c • g),
      Lp.coeFn_smul a f, Lp.coeFn_smul c g] with x hfx hgx hadd haf hcg
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd haf hcg
    rw [hadd, haf, hcg]
    constructor
    · exact add_nonneg (mul_nonneg ha hfx.1) (mul_nonneg hc hgx.1)
    · calc
        a * f x + c * g x ≤ a * 1 + c * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hfx.2 ha)
            (mul_le_mul_of_nonneg_left hgx.2 hc)
        _ = 1 := by nlinarith
  · intro j
    change momentLinear h hh (a • f + c • g) j = b j
    rw [map_add, map_smul, map_smul]
    change a * momentLinear h hh f j + c * momentLinear h hh g j = b j
    change a * (∫ x, f x * h j x ∂μ) + c * (∫ x, g x * h j x ∂μ) = b j
    rw [hf.2 j, hg.2 j, ← add_mul, hac, one_mul]

/-- The last measure-theoretic bridge: an a.e. indicator representative
turns each moment into an ordinary measurable-set integral. -/
theorem moment_eq_setIntegral {n : ℕ} (h : Fin n → X → ℝ)
    (g : Lp ℝ ∞ μ) {s : Set X} (hs : MeasurableSet s)
    (hg : g =ᵐ[μ] s.indicator (fun _ => (1 : ℝ))) (j : Fin n) :
    (∫ x, g x * h j x ∂μ) = ∫ x in s, h j x ∂μ := by
  calc
    _ = ∫ x, s.indicator (h j) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = _ := integral_indicator hs

/-- Atomlessness gives arbitrarily many disjoint positive measurable
pieces inside every positive measurable set. No prescribed masses are needed. -/
theorem exists_disjoint_positive_pieces [IsFiniteMeasure μ]
    (hatom : Spec.Atomless μ) {s : Set X} (hs : MeasurableSet s)
    (hpos : 0 < μ s) (k : ℕ) :
    ∃ t : Fin (k + 1) → Set X,
      (∀ i, MeasurableSet (t i) ∧ t i ⊆ s ∧ 0 < μ (t i)) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) := by
  induction k generalizing s with
  | zero =>
    refine ⟨fun _ => s, fun _ => ⟨hs, Set.Subset.rfl, hpos⟩, ?_⟩
    intro i j hij
    exact (hij (Fin.ext (by omega))).elim
  | succ k ih =>
    obtain ⟨a, ha, has, hpa, hla⟩ := hatom s hs hpos
    have hpr : 0 < μ (s \ a) := by
      rw [measure_sdiff has ha.nullMeasurableSet (measure_ne_top μ a)]
      exact tsub_pos_iff_lt.mpr hla
    obtain ⟨t, ht, htd⟩ := ih ha hpa
    refine ⟨Fin.cons (s \ a) t, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hs.diff ha, Set.sdiff_subset, hpr⟩
      · exact ⟨(ht j).1, (ht j).2.1.trans has, (ht j).2.2⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          exact Set.disjoint_left.mpr (fun x hx hxt => hx.2 ((ht j).2.1 hxt))
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          exact Set.disjoint_left.mpr (fun x hxt hx => hx.2 ((ht i).2.1 hxt))
        | succ j => exact htd (fun h => hij (congrArg Fin.succ h))

/-- The only dimension argument needed for purification. It also covers
zero-dimensional targets. -/
theorem exists_nonzero_moment_relation {n : ℕ} (v : Fin (n + 1) → (Fin n → ℝ)) :
    ∃ c : Fin (n + 1) → ℝ, (∑ i, c i • v i) = 0 ∧ ∃ i, c i ≠ 0 := by
  apply Fintype.not_linearIndependent_iff.mp
  intro hli
  have hc := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_pi] at hc
  omega

/-- A finite linear combination of measurable indicators in the L∞ quotient. -/
def indicatorCombination [IsFiniteMeasure μ] {m : ℕ}
    (t : Fin m → Set X) (ht : ∀ i, MeasurableSet (t i)) (c : Fin m → ℝ) :
    Lp ℝ ∞ μ :=
  ∑ i, c i • indicatorConstLp ∞ (ht i) (measure_ne_top μ (t i)) (1 : ℝ)

/-- Pointwise formula for the finite combination, outside one common null set. -/
theorem indicatorCombination_coeFn [IsFiniteMeasure μ] {m : ℕ}
    (t : Fin m → Set X) (ht : ∀ i, MeasurableSet (t i)) (c : Fin m → ℝ) :
    indicatorCombination (μ := μ) t ht c =ᵐ[μ]
      fun x => ∑ i, (t i).indicator (fun _ => c i) x := by
  have hc : ∀ i, (c i • indicatorConstLp ∞ (ht i) (measure_ne_top μ (t i)) (1 : ℝ))
      =ᵐ[μ] fun x => (t i).indicator (fun _ => c i) x := by
    intro i
    filter_upwards [Lp.coeFn_smul (c i)
      (indicatorConstLp ∞ (ht i) (measure_ne_top μ (t i)) (1 : ℝ)),
      indicatorConstLp_coeFn (p := ∞) (hs := ht i)
        (hμs := measure_ne_top μ (t i)) (c := (1 : ℝ))] with x hx hi
    simp only [Pi.smul_apply, smul_eq_mul] at hx
    rw [hx, hi]
    by_cases hxt : x ∈ t i <;> simp [hxt]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => c i • indicatorConstLp ∞ (ht i) (measure_ne_top μ (t i)) (1 : ℝ)),
    ae_all_iff.mpr hc] with x hx hxc
  exact hx.trans (Finset.sum_congr rfl fun i _ => hxc i)

omit [MeasurableSpace X] in
/-- On one member of a disjoint family the corresponding coefficient is recovered. -/
theorem sum_indicator_eq_coefficient {m : ℕ} (t : Fin m → Set X)
    (hd : Pairwise (fun i j => Disjoint (t i) (t j))) (c : Fin m → ℝ)
    {x : X} {i : Fin m} (hxi : x ∈ t i) :
    (∑ j, (t j).indicator (fun _ => c j) x) = c i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [hxi]
  · intro j _ hji
    have hxj : x ∉ t j := fun hj => Set.disjoint_left.mp (hd hji) hj hxi
    simp [hxj]
  · simp

/-- A combination with a nonzero coefficient on a positive member is nonzero
as an a.e. equivalence class, not just as a pointwise function. -/
theorem indicatorCombination_ne_zero [IsFiniteMeasure μ] {m : ℕ}
    (t : Fin m → Set X) (ht : ∀ i, MeasurableSet (t i))
    (hd : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hp : ∀ i, 0 < μ (t i)) (c : Fin m → ℝ) (i : Fin m) (hci : c i ≠ 0) :
    indicatorCombination (μ := μ) t ht c ≠ (0 : Lp ℝ ∞ μ) := by
  intro hzero
  have hz : (fun x => ∑ j, (t j).indicator (fun _ => c j) x) =ᵐ[μ] 0 :=
    (indicatorCombination_coeFn t ht c).symm.trans
      (hzero ▸ Lp.coeFn_zero ℝ ∞ μ)
  have hn : ∀ᵐ x ∂μ, x ∉ t i := by
    filter_upwards [hz] with x hx hxi
    exact hci ((sum_indicator_eq_coefficient t hd c hxi).symm.trans hx)
  have hm : μ (t i) = 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hn
  exact (ne_of_gt (hp i)) hm

/-- On an atomless positive set there is a nonzero arbitrarily small
L∞ perturbation, supported on that set and annihilating every moment. -/
theorem exists_small_kernel_perturbation [IsFiniteMeasure μ]
    (hatom : Spec.Atomless μ) {n : ℕ} (h : Fin n → X → ℝ)
    (hh : ∀ j, Integrable (h j) μ) {s : Set X} (hs : MeasurableSet s)
    (hpos : 0 < μ s) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Lp ℝ ∞ μ, v ≠ 0 ∧ momentLinear h hh v = 0 ∧
      ∀ᵐ x ∂μ, |v x| ≤ ε ∧ (x ∉ s → v x = 0) := by
  classical
  obtain ⟨t, ht, htd⟩ := exists_disjoint_positive_pieces hatom hs hpos n
  let I : Fin (n + 1) → Lp ℝ ∞ μ :=
    fun i => indicatorConstLp ∞ (ht i).1 (measure_ne_top μ (t i)) (1 : ℝ)
  obtain ⟨c, hc, i, hci⟩ := exists_nonzero_moment_relation
    (fun i => momentLinear h hh (I i))
  let w : Lp ℝ ∞ μ := indicatorCombination t (fun i => (ht i).1) c
  have hw : w ≠ 0 := indicatorCombination_ne_zero t (fun i => (ht i).1)
    htd (fun i => (ht i).2.2) c i hci
  have hwker : momentLinear h hh w = 0 := by
    simpa only [w, indicatorCombination, map_sum, map_smul, I] using hc
  let C : ℝ := ∑ i, |c i|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδC : δ * C ≤ ε := by
    have heq : δ * (C + 1) = ε := div_mul_cancel₀ ε (by positivity : C + 1 ≠ 0)
    nlinarith
  refine ⟨δ • w, smul_ne_zero hδ.ne' hw, ?_, ?_⟩
  · rw [map_smul, hwker, smul_zero]
  · filter_upwards [Lp.coeFn_smul δ w,
      indicatorCombination_coeFn (μ := μ) t (fun i => (ht i).1) c] with x hx hwx
    simp only [Pi.smul_apply, smul_eq_mul] at hx
    change w x = _ at hwx
    rw [hx, hwx]
    constructor
    · rw [abs_mul, abs_of_pos hδ]
      have hb : |∑ i, (t i).indicator (fun _ => c i) x| ≤ C := by
        calc
          _ ≤ ∑ i, |(t i).indicator (fun _ => c i) x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ C := by
            apply Finset.sum_le_sum
            intro i _
            by_cases hxt : x ∈ t i <;> simp [hxt, abs_nonneg]
      exact (mul_le_mul_of_nonneg_left hb hδ.le).trans hδC
    · intro hxs
      have hz : ∀ i, x ∉ t i := fun i hx => hxs ((ht i).2.1 hx)
      simp [hz]

/-- A nonzero two-sided perturbation in a fiber contradicts extremality.
This is algebraic, so it uses no topology and no atomlessness. -/
theorem not_extreme_of_two_sided_perturbation {n : ℕ}
    (h : Fin n → X → ℝ) (b : Fin n → ℝ) (g v : Lp ℝ ∞ μ)
    (hv : v ≠ 0) (hplus : g + v ∈ Spec.densityFiber μ h b)
    (hminus : g - v ∈ Spec.densityFiber μ h b) :
    g ∉ Set.extremePoints ℝ (Spec.densityFiber μ h b) := by
  intro he
  have heq : g + v = g := he.2 hplus hminus (mem_openSegment_add_sub g v)
  exact hv (add_left_cancel (heq.trans (add_zero g).symm))

/-- A bounded density is either an a.e. indicator, or it has a positive
measurable band uniformly separated from both endpoints. Countably many
reciprocal bands suffice; this avoids uncountable unions of null sets. -/
theorem indicator_or_fractional_band (g : Lp ℝ ∞ μ)
    (hgb : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1) :
    (∃ s : Set X, MeasurableSet s ∧ g =ᵐ[μ] s.indicator (fun _ => (1 : ℝ))) ∨
    ∃ ε : ℝ, 0 < ε ∧ 0 < μ {x | ε ≤ g x ∧ g x ≤ 1 - ε} := by
  by_cases hb : ∃ ε : ℝ, 0 < ε ∧ 0 < μ {x | ε ≤ g x ∧ g x ≤ 1 - ε}
  · exact Or.inr hb
  left
  have hband (k : ℕ) :
      μ {x | 1 / ((k : ℝ) + 1) ≤ g x ∧ g x ≤ 1 - 1 / ((k : ℝ) + 1)} = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hp
    exact hb ⟨1 / ((k : ℝ) + 1), by positivity, hp⟩
  have hnon : ∀ᵐ x ∂μ, ∀ k : ℕ,
      ¬ (1 / ((k : ℝ) + 1) ≤ g x ∧ g x ≤ 1 - 1 / ((k : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_iff.mpr
    simpa only [not_not] using hband k
  let s : Set X := {x | g x = 1}
  have hs : MeasurableSet s :=
    measurableSet_eq_fun g.val.measurable measurable_const
  refine ⟨s, hs, ?_⟩
  filter_upwards [hgb, hnon] with x hx hxn
  have he : g x = 0 ∨ g x = 1 := by
    by_cases h0 : g x = 0
    · exact Or.inl h0
    by_cases h1 : g x = 1
    · exact Or.inr h1
    have h0' : 0 < g x := by rcases hx with ⟨hl, hu⟩; exact lt_of_le_of_ne hl (Ne.symm h0)
    have h1' : 0 < 1 - g x := by rcases hx with ⟨hl, hu⟩; exact sub_pos.mpr (lt_of_le_of_ne hu h1)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min h0' h1')
    have hk0 := (lt_min_iff.mp hk).1
    have hk1 := (lt_min_iff.mp hk).2
    exact (hxn k ⟨hk0.le, by linarith⟩).elim
  rcases he with h0 | h1
  · simp [s, h0]
  · simp [s, h1]

/-- The finite-dimensional atomless bang-bang step, using exactly n+1
positive pieces and a finite-dimensional linear relation. -/
theorem extreme_is_indicator : Spec.ExtremeIsIndicator.{u} := by
  intro X _ μ _ hatom n h hh b g he
  rcases indicator_or_fractional_band g he.1.1 with hind | ⟨ε, hε, hband⟩
  · exact hind
  let s : Set X := {x | ε ≤ g x ∧ g x ≤ 1 - ε}
  have hs : MeasurableSet s :=
    (measurableSet_le measurable_const g.val.measurable).inter
      (measurableSet_le g.val.measurable measurable_const)
  obtain ⟨v, hv, hvker, hvb⟩ := exists_small_kernel_perturbation
    hatom h hh hs hband hε
  have hplus : g + v ∈ Spec.densityFiber μ h b := by
    constructor
    · filter_upwards [he.1.1, hvb, Lp.coeFn_add g v] with x hx hvx hgv
      simp only [Pi.add_apply] at hgv
      rw [hgv]
      by_cases hxs : x ∈ s
      · have hgs : ε ≤ g x ∧ g x ≤ 1 - ε := hxs
        have ha := (abs_le.mp hvx.1)
        constructor <;> linarith
      · rw [hvx.2 hxs, add_zero]
        exact hx
    · intro j
      change momentLinear h hh (g + v) j = b j
      rw [map_add, hvker, add_zero]
      exact he.1.2 j
  have hminus : g - v ∈ Spec.densityFiber μ h b := by
    constructor
    · filter_upwards [he.1.1, hvb, Lp.coeFn_sub g v] with x hx hvx hgv
      simp only [Pi.sub_apply] at hgv
      rw [hgv]
      by_cases hxs : x ∈ s
      · have hgs : ε ≤ g x ∧ g x ≤ 1 - ε := hxs
        have ha := (abs_le.mp hvx.1)
        constructor <;> linarith
      · rw [hvx.2 hxs, sub_zero]
        exact hx
    · intro j
      change momentLinear h hh (g - v) j = b j
      rw [map_sub, hvker, sub_zero]
      exact he.1.2 j
  exact (not_extreme_of_two_sided_perturbation h b g v hv hplus hminus he).elim

/-- Once the two substantive stages are proved, no extra regularity on the
input density or measurable space is required for purification. This is an
assembly lemma, not an assertion that either stage has been proved. -/
theorem purification_of_stages
    (hext : Spec.FiberExtremePoint.{u})
    (hind : Spec.ExtremeIsIndicator.{u}) : Spec.Purification.{u} := by
  intro X _ μ _ hatom n h hh g hgm hgb
  have hmem : MemLp g ∞ μ := memLp_top_of_bound hgm 1 (by
    filter_upwards [hgb] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  let G : Lp ℝ ∞ μ := hmem.toLp g
  let b : Fin n → ℝ := fun j => ∫ x, g x * h j x ∂μ
  have hG : G ∈ Spec.densityFiber μ h b := by
    constructor
    · filter_upwards [hmem.coeFn_toLp, hgb] with x hxe hxb
      simpa only [G, hxe] using hxb
    · intro j
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with x hx
      simp only [G, hx]
  obtain ⟨e, he⟩ := hext μ h hh b ⟨G, hG⟩
  obtain ⟨s, hs, hes⟩ := hind μ hatom h hh b e he
  refine ⟨s, hs, fun j => ?_⟩
  exact (moment_eq_setIntegral h e hs hes j).symm.trans (he.1.2 j)

/-- Assembly of extreme-point existence with the established atomless step. -/
theorem purification_of_extreme_existence
    (hext : Spec.FiberExtremePoint.{u}) : Spec.Purification.{u} :=
  purification_of_stages hext extreme_is_indicator

/-- The natural L∞/L¹ integral pairing, with its norm-continuous dual codomain. -/
def densityDual : Lp ℝ ∞ μ →L[ℝ] (Lp ℝ 1 μ →L[ℝ] ℝ) :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1

@[simp] theorem densityDual_apply (g : Lp ℝ ∞ μ) (f : Lp ℝ 1 μ) :
    densityDual g f = ∫ x, g x * f x ∂μ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing_eq_integral g f

/-- Bounded densities are separated by their L¹ tests on finite measure spaces. -/
theorem densityDual_injective [IsFiniteMeasure μ] :
    Function.Injective (densityDual (μ := μ)) := by
  intro g k heq
  apply Lp.ext
  apply Integrable.ae_eq_of_forall_setIntegral_eq g k
    ((Lp.memLp g).integrable (by simp)) ((Lp.memLp k).integrable (by simp))
  intro s hs _
  let f := indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)
  have htest (a : Lp ℝ ∞ μ) : densityDual a f = ∫ x in s, a x ∂μ := by
    rw [densityDual_apply, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs)
      (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx
    change f x = _ at hx
    rw [hx]
    by_cases hxs : x ∈ s <;> simp [hxs]
  rw [← htest g, ← htest k, heq]

/-- Multiplication by the constant one gives the continuous inclusion L² → L¹.
This construction also works when the finite measure is zero. -/
def l2ToL1 [IsFiniteMeasure μ] : Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (Lp.const 2 μ (1 : ℝ))

theorem l2ToL1_coeFn [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    l2ToL1 f =ᵐ[μ] f := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := 1) (Lp.const 2 μ (1 : ℝ)) f, Lp.coeFn_const 2 μ (1 : ℝ)] with x hx h1
  simpa only [l2ToL1, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', h1, Function.const_apply, one_mul] using hx

theorem l2ToL1_indicator [IsFiniteMeasure μ] {s : Set X} (hs : MeasurableSet s)
    (c : ℝ) :
    l2ToL1 (indicatorConstLp 2 hs (measure_ne_top μ s) c) =
      indicatorConstLp 1 hs (measure_ne_top μ s) c := by
  apply Lp.ext
  exact (l2ToL1_coeFn _).trans
    ((indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := measure_ne_top μ s) (c := c)).trans
      (indicatorConstLp_coeFn (p := 1) (hs := hs)
        (hμs := measure_ne_top μ s) (c := c)).symm)

/-- Positive functionals dominated by integration are exactly the densities
between zero and one. Only this order interval of the dual is needed here.
The representation uses the Hilbert-space Riesz theorem on L². -/
theorem exists_density_of_order_tests [IsFiniteMeasure μ]
    (F : Lp ℝ 1 μ →L[ℝ] ℝ)
    (hF : ∀ f : Lp ℝ 1 μ, (∀ᵐ x ∂μ, 0 ≤ f x) →
      0 ≤ F f ∧ F f ≤ ∫ x, f x ∂μ) :
    ∃ g : Lp ℝ ∞ μ, (∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1) ∧ densityDual g = F := by
  let z : Lp ℝ 2 μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm
    (F.comp l2ToL1)
  have hz (f : Lp ℝ 2 μ) : inner ℝ z f = F (l2ToL1 f) :=
    InnerProductSpace.toDual_symm_apply
  have hzi : Integrable z μ := (Lp.memLp z).integrable (by norm_num)
  have hsets (s : Set X) (hs : MeasurableSet s) :
      (∫ x in s, z x ∂μ) = F (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) := by
    rw [← L2.inner_indicatorConstLp_one hs (measure_ne_top μ s) z,
      real_inner_comm, hz, l2ToL1_indicator]
  have hbounds (s : Set X) (hs : MeasurableSet s) :
      0 ≤ ∫ x in s, z x ∂μ ∧ (∫ x in s, z x ∂μ) ≤ μ.real s := by
    rw [hsets s hs]
    have hi : ∀ᵐ x ∂μ, 0 ≤ indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) x := by
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs)
        (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx
      rw [hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    simpa only [integral_indicatorConstLp, smul_eq_mul, mul_one] using hF _ hi
  have hz0 : ∀ᵐ x ∂μ, 0 ≤ z x :=
    ae_nonneg_of_forall_setIntegral_nonneg hzi (fun s hs _ => (hbounds s hs).1)
  have hz1 : ∀ᵐ x ∂μ, z x ≤ 1 :=
    ae_le_of_forall_setIntegral_le hzi (integrable_const (1 : ℝ)) (fun s hs _ => by
      simpa only [setIntegral_const, smul_eq_mul, mul_one] using (hbounds s hs).2)
  have hm : MemLp z ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable z) 1 (by
    filter_upwards [hz0, hz1] with x h0 h1
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1)
  let g : Lp ℝ ∞ μ := hm.toLp z
  have hg : g =ᵐ[μ] z := hm.coeFn_toLp
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [hg, hz0, hz1] with x hx h0 h1
    exact hx ▸ ⟨h0, h1⟩
  · apply ContinuousLinearMap.ext
    apply Lp.induction (p := 1) (by simp)
      (fun f => densityDual g f = F f)
    · intro c s hs _
      change densityDual g (indicatorConstLp 1 hs (measure_ne_top μ s) c) =
        F (indicatorConstLp 1 hs (measure_ne_top μ s) c)
      have hd : densityDual g (indicatorConstLp 1 hs (measure_ne_top μ s) c) =
          c * ∫ x in s, z x ∂μ := by
        rw [densityDual_apply, ← integral_indicator hs, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hg, indicatorConstLp_coeFn (p := 1) (hs := hs)
          (hμs := measure_ne_top μ s) (c := c)] with x hx hi
        rw [hx, hi]
        by_cases hxs : x ∈ s <;> simp [hxs, mul_comm]
      rw [hd, hsets s hs]
      have hc : indicatorConstLp 1 hs (measure_ne_top μ s) c =
          c • indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) := by
        apply Lp.ext
        filter_upwards [Lp.coeFn_smul c (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)),
          indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top μ s) (c := c),
          indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top μ s)
            (c := (1 : ℝ))] with x hx hi h1
        simp only [Pi.smul_apply, smul_eq_mul] at hx
        rw [hx, hi, h1]
        by_cases hxs : x ∈ s <;> simp [hxs]
      rw [hc, map_smul, smul_eq_mul]
    · intro f k _ _ _ hf hk
      rw [map_add, map_add, hf, hk]
    · exact isClosed_eq (densityDual g).continuous F.continuous

/-- The pairing regarded as a map to the native weak dual. -/
def densityWeakDual : Lp ℝ ∞ μ →ₗ[ℝ] WeakDual ℝ (Lp ℝ 1 μ) :=
  StrongDual.toWeakDual.toLinearMap.comp densityDual.toLinearMap

@[simp] theorem densityWeakDual_apply (g : Lp ℝ ∞ μ) (f : Lp ℝ 1 μ) :
    densityWeakDual g f = ∫ x, g x * f x ∂μ := densityDual_apply g f

/-- The specified topology is exactly the topology induced by the integral
embedding in the native weak dual, not the L∞ norm topology. -/
theorem densityWeakDual_inducing :
    @Topology.IsInducing (Lp ℝ ∞ μ) (WeakDual ℝ (Lp ℝ 1 μ))
      (Spec.densityWeakStarTopology μ) inferInstance densityWeakDual := by
  let : TopologicalSpace (Lp ℝ ∞ μ) := Spec.densityWeakStarTopology μ
  refine ⟨?_⟩
  change Spec.densityWeakStarTopology μ =
    TopologicalSpace.induced densityWeakDual
      (TopologicalSpace.induced (fun F : WeakDual ℝ (Lp ℝ 1 μ) => fun f => F f)
        Pi.topologicalSpace)
  rw [induced_compose, induced_to_pi]
  simp only [Spec.densityWeakStarTopology, Function.comp_apply, densityWeakDual_apply]

theorem densityDual_order_bounds (g : Lp ℝ ∞ μ)
    (hg : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1) (f : Lp ℝ 1 μ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    0 ≤ densityDual g f ∧ densityDual g f ≤ ∫ x, f x ∂μ := by
  rw [densityDual_apply]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hg, hf] with x hx hy
    exact mul_nonneg hx.1 hy
  · apply integral_mono_ae (integrable_density_mul g (memLp_one_iff_integrable.mp (Lp.memLp f)))
      (memLp_one_iff_integrable.mp (Lp.memLp f))
    filter_upwards [hg, hf] with x hx hy
    exact mul_le_of_le_one_left hy hx.2

/-- Every density between zero and one gives a functional in the dual unit ball. -/
theorem densityDual_norm_le_one (g : Lp ℝ ∞ μ)
    (hg : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ 1) : ‖densityDual g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, densityDual_apply, L1.norm_eq_integral_norm]
  calc
    _ ≤ ∫ x, ‖g x * f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono_ae
        (integrable_density_mul g (memLp_one_iff_integrable.mp (Lp.memLp f))).norm
        (memLp_one_iff_integrable.mp (Lp.memLp f)).norm
      filter_upwards [hg] with x hx
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hx.2

/-- Conversion of integrable coordinates into genuine L¹ test classes. -/
theorem densityDual_toLp (g : Lp ℝ ∞ μ) {h : X → ℝ} (hh : Integrable h μ) :
    densityDual g ((memLp_one_iff_integrable.mpr hh).toLp h) = ∫ x, g x * h x ∂μ := by
  rw [densityDual_apply]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr hh).coeFn_toLp] with x hx
  rw [hx]

/-- A dual order interval with the same finite list of prescribed moments.
The ball bound is redundant, but makes the Alaoglu application explicit. -/
def dualDensityFiber {n : ℕ} (h : Fin n → X → ℝ)
    (hh : ∀ j, Integrable (h j) μ) (b : Fin n → ℝ) :
    Set (WeakDual ℝ (Lp ℝ 1 μ)) :=
  {F | ‖F.toStrongDual‖ ≤ 1 ∧
    (∀ f : Lp ℝ 1 μ, (∀ᵐ x ∂μ, 0 ≤ f x) →
      0 ≤ F f ∧ F f ≤ ∫ x, f x ∂μ) ∧
    ∀ j, F ((memLp_one_iff_integrable.mpr (hh j)).toLp (h j)) = b j}

/-- Closed order tests and moment equations cut out a compact subset of the
weak dual unit ball. No atomlessness or countable generation is used. -/
theorem dualDensityFiber_isCompact {n : ℕ} (h : Fin n → X → ℝ)
    (hh : ∀ j, Integrable (h j) μ) (b : Fin n → ℝ) :
    IsCompact (dualDensityFiber h hh b) := by
  have hc : IsCompact {F : WeakDual ℝ (Lp ℝ 1 μ) | ‖F.toStrongDual‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right, Set.preimage_ofPred_eq] using
      WeakDual.isCompact_closedBall (0 : Lp ℝ 1 μ →L[ℝ] ℝ) 1
  have ho : IsClosed {F : WeakDual ℝ (Lp ℝ 1 μ) |
      ∀ f : Lp ℝ 1 μ, (∀ᵐ x ∂μ, 0 ≤ f x) →
        0 ≤ F f ∧ F f ≤ ∫ x, f x ∂μ} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      (isClosed_le continuous_const (WeakDual.eval_continuous f)).inter
        (isClosed_le (WeakDual.eval_continuous f) continuous_const)
  have hm : IsClosed {F : WeakDual ℝ (Lp ℝ 1 μ) |
      ∀ j, F ((memLp_one_iff_integrable.mpr (hh j)).toLp (h j)) = b j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j =>
      isClosed_eq (WeakDual.eval_continuous _) continuous_const
  exact hc.inter_right (ho.inter hm)

/-- The dual compact set is precisely the image of the original L∞ fiber. -/
theorem image_densityFiber [IsFiniteMeasure μ] {n : ℕ}
    (h : Fin n → X → ℝ) (hh : ∀ j, Integrable (h j) μ) (b : Fin n → ℝ) :
    densityWeakDual '' Spec.densityFiber μ h b = dualDensityFiber h hh b := by
  apply Set.Subset.antisymm
  · rintro F ⟨g, hg, rfl⟩
    refine ⟨densityDual_norm_le_one g hg.1, ?_, ?_⟩
    · exact densityDual_order_bounds g hg.1
    · intro j
      change densityDual g ((memLp_one_iff_integrable.mpr (hh j)).toLp (h j)) = b j
      rw [densityDual_toLp g (hh j)]
      exact hg.2 j
  · intro F hF
    obtain ⟨g, hg, heq⟩ := exists_density_of_order_tests F.toStrongDual hF.2.1
    have hw : densityWeakDual g = F := by
      apply WeakDual.toStrongDual.injective
      exact heq
    refine ⟨g, ⟨hg, ?_⟩, hw⟩
    intro j
    rw [← densityDual_toLp g (hh j), heq]
    exact hF.2.2 j

/-- Every moment fiber is compact in exactly σ(L∞, L¹), including empty fibers. -/
theorem compact_fiber : Spec.CompactFiber.{u} := by
  intro X _ μ _ n h hh b
  let : TopologicalSpace (Lp ℝ ∞ μ) := Spec.densityWeakStarTopology μ
  have he := densityWeakDual_inducing (μ := μ)
  have hc : IsCompact (densityWeakDual '' Spec.densityFiber μ h b) := by
    rw [image_densityFiber h hh b]
    exact dualDensityFiber_isCompact h hh b
  exact he.isCompact_iff.mpr hc

/-- Krein–Milman's extreme-point lemma, transported along the injective
integral pairing. There is no atomlessness hypothesis in this stage. -/
theorem fiber_extreme_point : Spec.FiberExtremePoint.{u} := by
  intro X _ μ _ n h hh b hne
  let : LocallyConvexSpace ℝ (WeakDual ℝ (Lp ℝ 1 μ)) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing ℝ (Lp ℝ 1 μ))
  have hc := dualDensityFiber_isCompact h hh b
  have him := image_densityFiber h hh b
  have hD : (dualDensityFiber h hh b).Nonempty := by
    rw [← him]
    exact hne.image _
  obtain ⟨F, hF⟩ := hc.extremePoints_nonempty hD
  obtain ⟨g, hg, hgf⟩ := (Set.ext_iff.mp him F).mpr hF.1
  refine ⟨g, hg, ?_⟩
  intro a ha c hc hseg
  apply densityDual_injective
  have haD : densityWeakDual a ∈ dualDensityFiber h hh b := by
    rw [← him]
    exact Set.mem_image_of_mem _ ha
  have hcD : densityWeakDual c ∈ dualDensityFiber h hh b := by
    rw [← him]
    exact Set.mem_image_of_mem _ hc
  have hs : F ∈ openSegment ℝ (densityWeakDual a) (densityWeakDual c) := by
    rw [← hgf]
    rcases hseg with ⟨α, β, hα, hβ, hαβ, hab⟩
    refine ⟨α, β, hα, hβ, hαβ, ?_⟩
    rw [← map_smul, ← map_smul, ← map_add, hab]
  have he := hF.2 haD hcD hs
  have he' : densityWeakDual a = densityWeakDual g := he.trans hgf.symm
  exact congrArg WeakDual.toStrongDual he'

/-- Finite-dimensional purification for an arbitrary finite atomless measure. -/
theorem purification : Spec.Purification.{u} :=
  purification_of_extreme_existence fiber_extreme_point

end ExpandedFA.PartV.LyapunovPurification
