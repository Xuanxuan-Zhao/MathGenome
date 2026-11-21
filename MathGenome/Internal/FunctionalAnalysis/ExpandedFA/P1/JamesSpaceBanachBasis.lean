import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceBanachBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceDefinition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15BasisCriterion
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal

namespace ExpandedFA.P1.James

/-- All cyclic edges, regarded as one finite Euclidean vector. -/
def cyclicProbe (a : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) :
    EuclideanSpace ℝ (Fin (k + 1) ⊕ Unit) :=
  WithLp.toLp 2 fun j => match j with
    | Sum.inl i => a (p i.castSucc) - a (p i.succ)
    | Sum.inr _ => a (p (Fin.last (k + 1))) - a (p 0)

/-- A single test occurring in the normalized James supremum. -/
def variation (a : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) : ℝ :=
  (1 / Real.sqrt 2) * ‖cyclicProbe a k p‖

theorem probe_norm (a : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) :
    ‖cyclicProbe a k p‖ = Real.sqrt (cyclicEnergy a k p) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [cyclicProbe, cyclicEnergy, Fintype.sum_sum_type, Real.norm_eq_abs, sq_abs]

theorem variation_nonneg (a : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) :
    0 ≤ variation a k p := by unfold variation; positivity

theorem probe_add (a b : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) :
    cyclicProbe (a + b) k p = cyclicProbe a k p + cyclicProbe b k p := by
  ext j
  cases j <;> simp [cyclicProbe] <;> ring

theorem probe_smul (c : ℝ) (a : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) :
    cyclicProbe (c • a) k p = c • cyclicProbe a k p := by
  ext j
  cases j <;> simp [cyclicProbe, mul_sub]

theorem variation_add_le (a b : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) :
    variation (a + b) k p ≤ variation a k p + variation b k p := by
  unfold variation
  rw [probe_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

theorem variation_smul (c : ℝ) (a : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) :
    variation (c • a) k p = |c| * variation a k p := by
  simp only [variation, probe_smul, norm_smul, Real.norm_eq_abs]
  ring

/-- The extended supremum is precisely the supremum of normalized tests. -/
theorem enorm_eq_iSup (a : ℕ → ℝ) :
    enorm a = ⨆ (k : ℕ) (p : Fin (k + 2) → ℕ) (_hp : StrictMono p),
      ENNReal.ofReal (variation a k p) := by
  simp only [enorm, variation, probe_norm, ENNReal.mul_iSup,
    ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt 2)]

theorem variation_le_enorm (a : ℕ → ℝ) (k : ℕ)
    (p : Fin (k + 2) → ℕ) (hp : StrictMono p) :
    ENNReal.ofReal (variation a k p) ≤ enorm a := by
  rw [enorm_eq_iSup]
  exact le_iSup_of_le k (le_iSup_of_le p (le_iSup_of_le hp le_rfl))

theorem enorm_le_of_variation_le {a : ℕ → ℝ} {C : ℝ≥0∞}
    (h : ∀ k p, StrictMono p → ENNReal.ofReal (variation a k p) ≤ C) :
    enorm a ≤ C := by
  rw [enorm_eq_iSup]
  exact iSup_le fun k => iSup_le fun p => iSup_le fun hp => h k p hp

theorem enorm_add_le (a b : ℕ → ℝ) : enorm (a + b) ≤ enorm a + enorm b := by
  apply enorm_le_of_variation_le
  intro k p hp
  calc
    ENNReal.ofReal (variation (a + b) k p) ≤
        ENNReal.ofReal (variation a k p + variation b k p) :=
      ENNReal.ofReal_le_ofReal (variation_add_le a b k p)
    _ = ENNReal.ofReal (variation a k p) + ENNReal.ofReal (variation b k p) :=
      ENNReal.ofReal_add (variation_nonneg ..) (variation_nonneg ..)
    _ ≤ enorm a + enorm b := add_le_add (variation_le_enorm a k p hp)
      (variation_le_enorm b k p hp)

theorem enorm_smul (c : ℝ) (a : ℕ → ℝ) :
    enorm (c • a) = ENNReal.ofReal |c| * enorm a := by
  simp only [enorm_eq_iSup, variation_smul, ENNReal.ofReal_mul (abs_nonneg c),
    ENNReal.mul_iSup]

theorem mem_add {a b : ℕ → ℝ} (ha : Mem a) (hb : Mem b) : Mem (a + b) := by
  refine ⟨?_, ?_⟩
  · change Tendsto (fun n => a n + b n) atTop (𝓝 0)
    simpa only [add_zero] using ha.1.add hb.1
  · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ha.2, hb.2⟩) (enorm_add_le a b)

theorem mem_smul (c : ℝ) {a : ℕ → ℝ} (ha : Mem a) : Mem (c • a) := by
  refine ⟨?_, ?_⟩
  · change Tendsto (fun n => c • a n) atTop (𝓝 0)
    simpa only [smul_zero] using ha.1.const_smul c
  · rw [enorm_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha.2

/-- The source sequences are closed under the pointwise vector operations. -/
def finiteVariation : Submodule ℝ (ℕ → ℝ) where
  carrier := Mem
  zero_mem' := zero_mem
  add_mem' := mem_add
  smul_mem' := mem_smul

instance instAddCommGroup : AddCommGroup Space :=
  inferInstanceAs (AddCommGroup finiteVariation)
instance instModule : Module ℝ Space := inferInstanceAs (Module ℝ finiteVariation)

@[simp] theorem val_zero : (0 : Space).val = 0 := rfl
@[simp] theorem val_add (a b : Space) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_neg (a : Space) : (-a).val = -a.val := rfl
@[simp] theorem val_sub (a b : Space) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_smul (c : ℝ) (a : Space) : (c • a).val = c • a.val := rfl

theorem variation_le_norm (a : Space) (k : ℕ)
    (p : Fin (k + 2) → ℕ) (hp : StrictMono p) : variation a.val k p ≤ ‖a‖ :=
  (ENNReal.ofReal_le_iff_le_toReal a.property.2).mp (variation_le_enorm a.val k p hp)

theorem norm_le_of_variation_le (a : Space) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k p, StrictMono p → variation a.val k p ≤ C) : ‖a‖ ≤ C := by
  apply (ENNReal.le_ofReal_iff_toReal_le a.property.2 hC).mp
  exact enorm_le_of_variation_le fun k p hp => ENNReal.ofReal_le_ofReal (h k p hp)

theorem variation_pair (a : ℕ → ℝ) (n m : ℕ) :
    variation a 0 ![n, m] = |a n - a m| := by
  rw [variation, probe_norm]
  have he : cyclicEnergy a 0 ![n, m] = 2 * (a n - a m)^2 := by
    simp [cyclicEnergy]
    ring
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp

theorem coordinate_le_norm (a : Space) (n : ℕ) : |a.val n| ≤ ‖a‖ := by
  have hh : Tendsto (fun m => |a.val n - a.val m|) atTop (𝓝 |a.val n|) := by
    simpa using (tendsto_const_nhds.sub a.property.1).abs
  apply le_of_tendsto hh
  filter_upwards [eventually_gt_atTop n] with m hm
  rw [← variation_pair]
  apply variation_le_norm
  exact Fin.strictMono_iff_lt_succ.mpr (by simpa using hm)

private theorem jamesCore : NormedSpace.Core ℝ Space where
  norm_nonneg a := ENNReal.toReal_nonneg
  norm_smul c a := by
    change (enorm (c • a.val)).toReal = ‖c‖ * (enorm a.val).toReal
    rw [enorm_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
  norm_triangle a b := by
    change (enorm (a.val + b.val)).toReal ≤ (enorm a.val).toReal + (enorm b.val).toReal
    rw [← ENNReal.toReal_add a.property.2 b.property.2]
    exact (ENNReal.toReal_le_toReal (a + b).property.2
      (ENNReal.add_ne_top.mpr ⟨a.property.2, b.property.2⟩)).mpr (enorm_add_le _ _)
  norm_eq_zero_iff a := by
    constructor
    · intro h
      apply Subtype.ext
      funext n
      exact abs_nonpos_iff.mp (by simpa [h] using coordinate_le_norm a n)
    · rintro rfl
      change (enorm (fun _ => 0)).toReal = 0
      simp

instance instNormedAddCommGroup : NormedAddCommGroup Space := NormedAddCommGroup.ofCore jamesCore
instance instNormedSpace : NormedSpace ℝ Space := NormedSpace.ofCore jamesCore

/-- Each test depends continuously on only finitely many coordinates. -/
theorem variation_continuous (k : ℕ) (p : Fin (k + 2) → ℕ) :
    Continuous (fun a : ℕ → ℝ => variation a k p) := by
  simp only [variation, probe_norm, cyclicEnergy]
  fun_prop

/-- A common bound on cyclic variation survives a pointwise limit. -/
theorem enorm_le_of_pointwise_tendsto {u : ℕ → (ℕ → ℝ)} {a : ℕ → ℝ}
    (hu : ∀ n, Tendsto (fun i => u i n) atTop (𝓝 (a n)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᶠ i in atTop, enorm (u i) ≤ ENNReal.ofReal C) :
    enorm a ≤ ENNReal.ofReal C := by
  apply enorm_le_of_variation_le
  intro k p hp
  apply ENNReal.ofReal_le_ofReal
  apply le_of_tendsto ((variation_continuous k p).tendsto a |>.comp (tendsto_pi_nhds.mpr hu))
  filter_upwards [hb] with i hi
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp ((variation_le_enorm (u i) k p hp).trans hi)

/-- Coordinate evaluation is continuous for the actual James norm. -/
def coordinate (n : ℕ) : Space →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => a.val n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun a => by
      change |a.val n| ≤ 1 * ‖a‖
      simpa only [one_mul] using coordinate_le_norm a n)

/-- Completeness follows by taking coordinate limits and retaining every
finite cyclic bound. No completion or replacement sequence model is used. -/
instance instCompleteSpace : CompleteSpace Space := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc (n : ℕ) : ∃ x : ℝ, Tendsto (fun i => (u i).val n) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_complete ((coordinate n).uniformContinuous.comp_cauchySeq hu)
  choose a ha using hc
  have happrox (ε : ℝ) (hε : 0 < ε) :
      ∃ N, ∀ i ≥ N, enorm ((u i).val - a) ≤ ENNReal.ofReal ε := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi => ?_⟩
    apply enorm_le_of_pointwise_tendsto
      (u := fun j => (u i).val - (u j).val) (C := ε)
    · intro n
      simpa only [Pi.sub_apply] using tendsto_const_nhds.sub (ha n)
    · exact hε.le
    · filter_upwards [eventually_ge_atTop N] with j hj
      have hd : ‖u i - u j‖ ≤ ε := le_of_lt (by simpa only [dist_eq_norm] using hN i hi j hj)
      exact (norm_finite (u i - u j)).symm ▸ ENNReal.ofReal_le_ofReal hd
  have hcoord (ε : ℝ) (hε : 0 < ε) :
      ∃ N, ∀ i ≥ N, ∀ n, |(u i).val n - a n| ≤ ε := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi n => ?_⟩
    apply le_of_tendsto ((tendsto_const_nhds.sub (ha n)).abs)
    filter_upwards [eventually_ge_atTop N] with j hj
    exact (coordinate_le_norm (u i - u j) n).trans
      (le_of_lt (by simpa only [dist_eq_norm] using hN i hi j hj))
  have hnull : Tendsto a atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hcoord (ε / 3) (by positivity)
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (u N).property.1 (ε / 3) (by positivity)
    refine ⟨M, fun n hn => ?_⟩
    have ht := hM n hn
    have hd := hN N le_rfl n
    rw [Real.dist_eq, sub_zero] at ht ⊢
    have hh : |a n| ≤ |(u N).val n - a n| + |(u N).val n| := by
      calc
        |a n| = |(u N).val n - ((u N).val n - a n)| := by congr 1; ring
        _ ≤ |(u N).val n| + |(u N).val n - a n| := by
          simpa only [Real.norm_eq_abs] using norm_sub_le ((u N).val n) ((u N).val n - a n)
        _ = _ := add_comm _ _
    linarith
  have hfinite : enorm a ≠ ⊤ := by
    obtain ⟨N, hN⟩ := happrox 1 zero_lt_one
    have he : a = (u N).val + (-1 : ℝ) • ((u N).val - a) := by ext n; simp
    rw [he]
    apply ne_top_of_le_ne_top _ (enorm_add_le _ _)
    apply ENNReal.add_ne_top.mpr
    refine ⟨(u N).property.2, ?_⟩
    rw [enorm_smul]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN N le_rfl)
  let x : Space := ⟨a, hnull, hfinite⟩
  refine ⟨x, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := happrox (ε / 2) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  have hb : ‖u i - x‖ ≤ ε / 2 :=
    (ENNReal.le_ofReal_iff_toReal_le (u i - x).property.2 (by positivity)).mp (hN i hi)
  linarith

/-- A concrete witness for the independent Banach-space specification. -/
def banachModel : JamesBanachBasisSpec.BanachModel where
  group := instNormedAddCommGroup
  scalars := instNormedSpace
  norm_eq := fun _ => rfl
  zero_eq := rfl
  add_eq := fun _ _ => rfl
  neg_eq := fun _ => rfl
  smul_eq := fun _ _ => rfl
  complete := instCompleteSpace

/-- The finite cyclic-variation space is a real Banach space with exactly its
original pointwise operations and norm. -/
theorem banach_space : JamesBanachBasisSpec.BanachSpaceConclusion := ⟨banachModel⟩

/-- The coordinate unit sequence is null, independently of any norm estimate. -/
theorem unit_null (n : ℕ) : Tendsto (Pi.single n (1 : ℝ) : ℕ → ℝ) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop n] with m hm
  simp [ne_of_gt hm]

/-- Evaluation of a finite sum is its ordinary pointwise sum. -/
@[simp] theorem val_sum {ι : Type*} (s : Finset ι) (f : ι → Space) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  map_sum finiteVariation.subtype f s

/-- A coordinate spike has at most one nonzero value along an increasing list.
Its cyclic energy is therefore twice the sum of its squared values. -/
theorem cyclicEnergy_unit_le (n k : ℕ) (p : Fin (k + 2) → ℕ) (hp : StrictMono p) :
    cyclicEnergy (Pi.single n (1 : ℝ)) k p ≤ 2 := by
  let f : Fin (k + 2) → ℝ := fun i => (Pi.single n (1 : ℝ) : ℕ → ℝ) (p i)
  have hmul (i j : Fin (k + 2)) (hij : i ≠ j) : f i * f j = 0 := by
    dsimp [f]
    by_cases hi : p i = n
    · have hj : p j ≠ n := fun hj => hij (hp.injective (hi.trans hj.symm))
      simp [hi, hj]
    · simp [Pi.single_apply, hi]
  have hs (i j : Fin (k + 2)) (hij : i ≠ j) :
      (f i - f j)^2 = (f i)^2 + (f j)^2 := by
    nlinarith [hmul i j hij]
  have hadj (i : Fin (k + 1)) : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hclose : Fin.last (k + 1) ≠ (0 : Fin (k + 2)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have he : cyclicEnergy (Pi.single n (1 : ℝ)) k p = 2 * ∑ i, (f i)^2 := by
    change (∑ j : Fin (k + 1), (f j.castSucc - f j.succ)^2) +
      (f (Fin.last (k + 1)) - f 0)^2 = _
    simp_rw [hs _ _ (hadj _)]
    rw [hs _ _ hclose, Finset.sum_add_distrib]
    have hleft := Fin.sum_univ_castSucc (fun i => (f i)^2)
    have hright := Fin.sum_univ_succ (fun i => (f i)^2)
    linarith
  have hsum : ∑ i, (f i)^2 ≤ 1 := by
    by_cases hex : ∃ j, p j = n
    · obtain ⟨j, hj⟩ := hex
      have hf (i : Fin (k + 2)) : f i = if i = j then 1 else 0 := by
        by_cases hi : i = j
        · subst i; simp [f, Pi.single_apply, hj]
        · have hne : p i ≠ n := fun h => hi (hp.injective (h.trans hj.symm))
          simp [f, Pi.single_apply, hne, hi]
      simp only [hf]
      simp
    · have hf (i : Fin (k + 2)) : f i = 0 := by
        have hne : p i ≠ n := fun hi => hex ⟨i, hi⟩
        simp [f, Pi.single_apply, hne]
      simp only [hf]
      simp
  rw [he]
  linarith

/-- Exact normalization, for the factor and closing edge in the manuscript. -/
theorem unit_enorm : JamesBanachBasisSpec.UnitNorm := by
  intro n
  change enorm (Pi.single n (1 : ℝ)) = 1
  apply le_antisymm
  · apply enorm_le_of_variation_le
    intro k p hp
    have hs := Real.sqrt_le_sqrt (cyclicEnergy_unit_le n k p hp)
    have htwo : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hv : variation (Pi.single n (1 : ℝ)) k p ≤ 1 := by
      rw [variation, probe_norm]
      calc
        (1 / Real.sqrt 2) * Real.sqrt (cyclicEnergy (Pi.single n (1 : ℝ)) k p) ≤
            (1 / Real.sqrt 2) * Real.sqrt 2 := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 1 := one_div_mul_cancel htwo
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hv
  · have hp : StrictMono (![n, n + 1] : Fin 2 → ℕ) :=
      Fin.strictMono_iff_lt_succ.mpr (by simp)
    have hh := variation_le_enorm (Pi.single n (1 : ℝ)) 0 ![n, n + 1] hp
    simpa [variation_pair] using hh

/-- Sampling an increasing subsequence can only remove tests from the supremum. -/
theorem enorm_comp_strictMono (a : ℕ → ℝ) (f : ℕ → ℕ) (hf : StrictMono f) :
    enorm (a ∘ f) ≤ enorm a := by
  apply enorm_le_of_variation_le
  intro k p hp
  exact variation_le_enorm a k (f ∘ p) (hf.comp hp)

/-- Contractivity of truncation follows by shifting the discarded indices
arbitrarily far out in the null sequence, preserving strict order throughout. -/
theorem truncation_bound : JamesBanachBasisSpec.TruncationBound := by
  intro a ha N
  let x : Space := ⟨a, ha⟩
  let shift (q n : ℕ) := if n < N then n else q + n
  have hs (q : ℕ) : StrictMono (shift q) := by
    intro i j hij
    dsimp [shift]
    split_ifs <;> omega
  have hlim : ∀ n, Tendsto (fun q => (a ∘ shift q) n) atTop
      (𝓝 ((fun n => if n < N then a n else 0) n)) := by
    intro n
    by_cases hn : n < N
    · simpa only [Function.comp_apply, shift, ite_eq_left hn] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => a n) atTop (𝓝 (a n)))
    · simp only [Function.comp_apply, shift, ite_eq_right hn]
      exact ha.1.comp (tendsto_add_atTop_nat n)
  change enorm (fun n => if n < N then a n else 0) ≤ enorm a
  rw [← norm_finite x]
  apply enorm_le_of_pointwise_tendsto hlim (norm_nonneg x)
  exact Filter.Eventually.of_forall fun q =>
    (enorm_comp_strictMono a (shift q) (hs q)).trans_eq (norm_finite x).symm

/-- Assemble normalization, contractivity and tail convergence into unique
coordinate expansions and the complete normalized monotone basis conclusion. -/
theorem basis_of_variation_estimates
    (htrunc : JamesBanachBasisSpec.TruncationBound)
    (hunit : JamesBanachBasisSpec.UnitNorm)
    (htail : JamesBanachBasisSpec.TailConvergence) :
    JamesBanachBasisSpec.BanachBasisConclusion := by
  classical
  have hu (n : ℕ) : Mem (Pi.single n (1 : ℝ)) :=
    ⟨unit_null n, by change JamesSpec.extendedNormValue _ ≠ ⊤; rw [hunit n]; simp⟩
  let e : ℕ → Space := fun n => ⟨Pi.single n (1 : ℝ), hu n⟩
  have he (n : ℕ) : (e n).val = Pi.single n (1 : ℝ) := rfl
  have hnormalized (n : ℕ) : ‖e n‖ = 1 := by
    change (JamesSpec.extendedNormValue (Pi.single n (1 : ℝ))).toReal = 1
    rw [hunit n]
    simp
  have hnonzero (n : ℕ) : e n ≠ 0 := by
    intro hz
    have hh := hnormalized n
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hsum (a : ℕ → ℝ) (N : ℕ) :
      (C15Basis.Spec.orderedPartialSum e a N).val = fun n => if n < N then a n else 0 := by
    funext n
    simp [C15Basis.Spec.orderedPartialSum, val_sum, he, Finset.sum_apply,
      Pi.single_apply]
  have hmono (N : ℕ) (x : Space) : ‖C15Basis.Spec.orderedPartialSum e x.val N‖ ≤ ‖x‖ := by
    apply (ENNReal.toReal_le_toReal (C15Basis.Spec.orderedPartialSum e x.val N).property.2
      x.property.2).mpr
    rw [hsum]
    exact htrunc x.val x.property N
  have hexpansion (x : Space) :
      Tendsto (C15Basis.Spec.orderedPartialSum e x.val) atTop (𝓝 x) := by
    have ht : Tendsto (fun N => enorm (fun n => if n < N then 0 else x.val n))
        atTop (𝓝 0) := htail x.val x.property
    have hnorm : Tendsto (fun N => ‖x - C15Basis.Spec.orderedPartialSum e x.val N‖)
        atTop (𝓝 0) := by
      have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
      simp only [ENNReal.toReal_zero] at hh
      convert hh using 1
      funext N
      change (enorm _).toReal = (enorm _).toReal
      congr 2
      rw [val_sub, hsum]
      funext n
      simp only [Pi.sub_apply]
      split_ifs <;> simp
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm ε hε
    refine ⟨N, fun i hi => ?_⟩
    have hh := hN i hi
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), dist_eq_norm,
      norm_sub_rev, norm_norm] using hh
  have horth (i j : ℕ) : coordinate i (e j) = (Pi.single j (1 : ℝ) : ℕ → ℝ) i := rfl
  have hb : C15Basis.Spec.IsRawSchauderBasis (𝕜 := ℝ) e := by
    refine ⟨hnonzero, fun x => ⟨x.val, hexpansion x, ?_⟩⟩
    intro a ha
    exact C15BasisCriterion.BasisCriterionProof.unique_expansion coordinate horth ha
  have hcoord (x : Space) : C15Basis.Spec.rawCoordinates hb x = x.val :=
    C15BasisCriterion.BasisCriterionProof.unique_expansion coordinate horth
      (Classical.choose_spec (hb.2 x).exists)
  exact ⟨{ toBanachModel := banachModel
           e := e
           unit_eq := he
           normalized := hnormalized
           schauder := hb
           coordinates := hcoord
           monotone := hmono }⟩

/-- Specialize the basis construction to the established unit norms and
contractive truncations. The tail-convergence hypothesis is discharged below. -/
theorem banach_basis_of_tail_convergence
    (htail : JamesBanachBasisSpec.TailConvergence) :
    JamesBanachBasisSpec.BanachBasisConclusion :=
  basis_of_variation_estimates truncation_bound unit_enorm htail

/-- Squared variation along an open finite chain (empty chains are allowed). -/
def chainEnergy (a : ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | [_] => 0
  | i :: j :: l => (a i - a j)^2 + chainEnergy a (j :: l)

private theorem chainEnergy_nonneg (a : ℕ → ℝ) (l : List ℕ) :
    0 ≤ chainEnergy a l := by
  induction l with
  | nil => simp [chainEnergy]
  | cons i l ih =>
    cases l with
    | nil => simp [chainEnergy]
    | cons j l => exact add_nonneg (sq_nonneg _) ih

private theorem chainEnergy_append_le (a : ℕ → ℝ) (l q : List ℕ) :
    chainEnergy a l + chainEnergy a q ≤ chainEnergy a (l ++ q) := by
  induction l with
  | nil => simp [chainEnergy]
  | cons i l ih =>
    cases l with
    | nil =>
      cases q with
      | nil => simp [chainEnergy]
      | cons j q =>
        change 0 + chainEnergy a (j :: q) ≤ (a i - a j)^2 + chainEnergy a (j :: q)
        linarith [sq_nonneg (a i - a j)]
    | cons j l =>
      change ((a i - a j)^2 + chainEnergy a (j :: l)) + chainEnergy a q ≤
        (a i - a j)^2 + chainEnergy a ((j :: l) ++ q)
      linarith

private theorem chainEnergy_ofFn (a : ℕ → ℝ) {n : ℕ} (p : Fin (n + 1) → ℕ) :
    chainEnergy a (List.ofFn p) =
      ∑ j : Fin n, (a (p j.castSucc) - a (p j.succ))^2 := by
  induction n with
  | zero => simp [List.ofFn_succ, chainEnergy]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, chainEnergy, Fin.sum_univ_succ]
    have hh := ih (fun i => p i.succ)
    rw [List.ofFn_succ] at hh
    simpa only [Fin.castSucc_zero, Fin.succ_castSucc] using
      congrArg (fun x => (a (p 0) - a (p (Fin.succ 0)))^2 + x) hh

private theorem cyclicEnergy_le_norm_sq (a : Space) (k : ℕ)
    (p : Fin (k + 2) → ℕ) (hp : StrictMono p) :
    cyclicEnergy a.val k p ≤ 2 * ‖a‖^2 := by
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hv := variation_le_norm a k p hp
  rw [variation, probe_norm, one_div_mul_eq_div] at hv
  have hs := (div_le_iff₀ hpos).mp hv
  have he : 0 ≤ cyclicEnergy a.val k p := by
    unfold cyclicEnergy
    positivity
  have hh := mul_self_le_mul_self (Real.sqrt_nonneg _) hs
  nlinarith [Real.sq_sqrt he, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem chainEnergy_le_norm_sq (a : Space) (l : List ℕ)
    (hl : l.Pairwise (· < ·)) : chainEnergy a.val l ≤ 2 * ‖a‖^2 := by
  cases l with
  | nil => simp [chainEnergy]
  | cons i l =>
    cases l with
    | nil => simp [chainEnergy]
    | cons j l =>
      have hget : StrictMono (List.get (i :: j :: l)) := List.pairwise_iff_get.mp hl
      rw [← List.ofFn_get (i :: j :: l), chainEnergy_ofFn]
      exact (le_add_of_nonneg_right (sq_nonneg _)).trans
        (cyclicEnergy_le_norm_sq a l.length _ hget)

/-- Finite total energy leaves arbitrarily little energy on every late chain. -/
theorem late_chainEnergy (a : Space) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ l : List ℕ, l.Pairwise (· < ·) →
      (∀ n ∈ l, N ≤ n) → chainEnergy a.val l < δ := by
  let S : Set ℝ := {r | ∃ l : List ℕ, l.Pairwise (· < ·) ∧ chainEnergy a.val l = r}
  have hne : S.Nonempty := ⟨0, [], by simp, rfl⟩
  have hb : BddAbove S := ⟨2 * ‖a‖^2, by
    rintro r ⟨l, hl, rfl⟩
    exact chainEnergy_le_norm_sq a l hl⟩
  obtain ⟨r, ⟨l, hl, hr⟩, hnear⟩ :=
    exists_lt_of_lt_csSup hne (show sSup S - δ < sSup S by linarith)
  refine ⟨l.sum + 1, fun q hq hlate => ?_⟩
  have happ : (l ++ q).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    refine ⟨hl, hq, fun i hi j hj => ?_⟩
    have hi' : i ≤ l.sum := List.le_sum_of_mem hi
    have hj' := hlate j hj
    omega
  have htotal : chainEnergy a.val (l ++ q) ≤ sSup S :=
    le_csSup hb ⟨l ++ q, happ, rfl⟩
  have hsplit := chainEnergy_append_le a.val l q
  linarith

private theorem chainEnergy_congr {a b : ℕ → ℝ} {l : List ℕ}
    (h : ∀ n ∈ l, a n = b n) : chainEnergy a l = chainEnergy b l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi := h i (by simp)
    have ht : ∀ n ∈ l, a n = b n := fun n hn => h n (by simp [hn])
    cases l with
    | nil => rfl
    | cons j l =>
      have hj := ht j (by simp)
      simp only [chainEnergy, hi, hj, ih ht]

/-- Cutting a sorted chain introduces at most one edge from zero. -/
private theorem cut_chainEnergy_le (a : ℕ → ℝ) (N : ℕ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (_hη : 0 ≤ η)
    (he : ∀ l : List ℕ, l.Pairwise (· < ·) → (∀ n ∈ l, N ≤ n) →
      chainEnergy a l ≤ δ)
    (hc : ∀ n, N ≤ n → |a n| ≤ η)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) :
    chainEnergy (fun n => if n < N then 0 else a n) l ≤ δ + η^2 := by
  let b : ℕ → ℝ := fun n => if n < N then 0 else a n
  have hsame (q : List ℕ) (hq : ∀ n ∈ q, N ≤ n) :
      chainEnergy b q = chainEnergy a q := by
    apply chainEnergy_congr
    intro n hn
    simp [b, not_lt.mpr (hq n hn)]
  have hsmall (n : ℕ) (hn : N ≤ n) : (a n)^2 ≤ η^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg (a n)) (hc n hn)
    nlinarith [sq_abs (a n)]
  change chainEnergy b l ≤ _
  induction l with
  | nil => simpa [chainEnergy] using add_nonneg hδ (sq_nonneg η)
  | cons i l ih =>
    have hp := List.pairwise_cons.mp hl
    by_cases hi : N ≤ i
    · have hall : ∀ n ∈ i :: l, N ≤ n := by
        intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact hi
        · exact hi.trans (hp.1 n hn).le
      rw [hsame _ hall]
      exact (he _ hl hall).trans (le_add_of_nonneg_right (sq_nonneg η))
    · cases l with
      | nil => simpa [chainEnergy] using add_nonneg hδ (sq_nonneg η)
      | cons j l =>
        by_cases hj : N ≤ j
        · have hall : ∀ n ∈ j :: l, N ≤ n := by
            intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · exact hj
            · exact hj.trans ((List.pairwise_cons.mp hp.2).1 n hn).le
          change (b i - b j)^2 + chainEnergy b (j :: l) ≤ _
          rw [hsame _ hall]
          have he' := he _ hp.2 hall
          have hs := hsmall j hj
          simp only [b, ite_eq_left (lt_of_not_ge hi), ite_eq_right (not_lt.mpr hj), zero_sub, neg_sq]
          linarith
        · have hh := ih hp.2
          simpa only [chainEnergy, b, ite_eq_left (lt_of_not_ge hi),
            ite_eq_left (lt_of_not_ge hj), sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            zero_pow, zero_add] using hh

/-- The closing cyclic edge is controlled by nullness as well. -/
private theorem cut_cyclicEnergy_le (a : ℕ → ℝ) (N : ℕ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (he : ∀ l : List ℕ, l.Pairwise (· < ·) → (∀ n ∈ l, N ≤ n) →
      chainEnergy a l ≤ δ)
    (hc : ∀ n, N ≤ n → |a n| ≤ η)
    (k : ℕ) (p : Fin (k + 2) → ℕ) (hp : StrictMono p) :
    cyclicEnergy (fun n => if n < N then 0 else a n) k p ≤ δ + 5 * η^2 := by
  let b : ℕ → ℝ := fun n => if n < N then 0 else a n
  have hcoord (n : ℕ) : |b n| ≤ η := by
    by_cases hn : n < N
    · simpa [b, hn] using hη
    · simpa [b, hn] using hc n (le_of_not_gt hn)
  have hclose : (b (p (Fin.last (k + 1))) - b (p 0))^2 ≤ 4 * η^2 := by
    have hh := (abs_sub (b (p (Fin.last (k + 1)))) (b (p 0))).trans
      (add_le_add (hcoord _) (hcoord _))
    have hs := mul_self_le_mul_self (abs_nonneg _) hh
    nlinarith [sq_abs (b (p (Fin.last (k + 1))) - b (p 0))]
  have hopen := cut_chainEnergy_le a N hδ hη he hc (List.ofFn p)
    (List.pairwise_ofFn.mpr hp)
  rw [chainEnergy_ofFn] at hopen
  change (∑ j : Fin (k + 1), (b (p j.castSucc) - b (p j.succ))^2) +
    (b (p (Fin.last (k + 1))) - b (p 0))^2 ≤ _
  linarith

/-- Tails of every null sequence of finite cyclic variation converge in that
same variation norm. No density or basis assumption is used. -/
theorem tail_convergence : JamesBanachBasisSpec.TailConvergence := by
  intro a ha
  change Tendsto (fun N => enorm (fun n => if n < N then 0 else a n)) atTop (𝓝 0)
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨0, fun _ _ => htop ▸ le_top⟩
  let r : ℝ := ε.toReal
  have hr : 0 < r := ENNReal.toReal_pos (ne_of_gt hε) htop
  let x : Space := ⟨a, ha⟩
  obtain ⟨L, hL⟩ := late_chainEnergy x (δ := r^2 / 16) (by positivity)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp ha.1 (r / 4) (by positivity)
  refine ⟨max L M, fun N hN => ?_⟩
  have hc (n : ℕ) (hn : N ≤ n) : |a n| ≤ r / 4 := by
    have hh := hM n ((le_max_right L M).trans (hN.trans hn))
    simpa only [Real.dist_eq, sub_zero] using hh.le
  have he (l : List ℕ) (hl : l.Pairwise (· < ·)) (hn : ∀ n ∈ l, N ≤ n) :
      chainEnergy a l ≤ r^2 / 16 :=
    (hL l hl fun n hn' => (le_max_left L M).trans (hN.trans (hn n hn'))).le
  rw [← ENNReal.ofReal_toReal htop]
  apply enorm_le_of_variation_le
  intro k p hp
  have he' := cut_cyclicEnergy_le a N (by positivity : 0 ≤ r^2 / 16)
    (by positivity : 0 ≤ r / 4) he hc k p hp
  have hs : Real.sqrt (cyclicEnergy (fun n => if n < N then 0 else a n) k p) ≤ r := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hr.le, by nlinarith [sq_nonneg r]⟩
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hf : 1 / Real.sqrt 2 ≤ 1 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  rw [variation, probe_norm]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans
    (mul_le_of_le_one_left hr.le hf)

/-- The real cyclic-variation James space is Banach and its coordinate units
are a normalized monotone Schauder basis, with their original coordinates. -/
theorem banach_basis : JamesBanachBasisSpec.BanachBasisConclusion :=
  banach_basis_of_tail_convergence tail_convergence

end ExpandedFA.P1.James
