import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.EntireZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.CanonicalFactors
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.HolomorphicProducts
import Mathlib.Basic.Denumerable
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.Compactness.Lindelof

/-!
D12.16.03 (paper.tex:2790–2796). Multiplicity slots are enumerated bijectively;
local finiteness makes their intersection with every compact disk finite, so
any enumeration escapes to infinity. The geometric bound on canonical factors
then gives a normal product. The upstream product order theorem counts its
simple zeros, and the independent center power supplies the order at zero.
Finite divisors are treated by finite polynomial products, including the empty
product one. No analytic or convergence certificate is part of the input.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace D12Complex.EntireZeros

/-- Each nonzero designated point occurs once for each of its multiplicity slots. -/
abbrev Occurrences (d : ℂ → ℕ) := Σ z : {z : ℂ // z ≠ 0 ∧ d z ≠ 0}, Fin (d z)

/-- Exact finite zero orders, entire weak holomorphy and global nontriviality. -/
def Realizes (d : ℂ → ℕ) (f : ℂ → ℂ) : Prop :=
  HolomorphicOn univ f ∧ (∃ z, f z ≠ 0) ∧
    (∀ z, analyticOrderAt f z = (d z : ℕ∞)) ∧
    ∀ z, f z = 0 ↔ d z ≠ 0

/-- The index starts at zero and is exactly the canonical genus. -/
def canonicalProduct (a : ℕ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  z ^ m * ∏' n, Specs.D12Complex.Ch16.CanonicalFactors.factor_value n (z / a n)

/-- Every rescaled elementary factor is entire. -/
lemma rescaled_factor_entire (a : ℕ → ℂ) (n : ℕ) :
    HolomorphicOn univ (fun z => CanonicalFactors.factor n (z / a n)) := by
  refine ⟨isOpen_univ, fun z _ => ?_⟩
  exact ((CanonicalFactors.factor_entire n).2 _ (mem_univ _)).comp z
    (differentiableAt_id.div_const _)

/-- The source geometric majorant on every compact set. -/
lemma canonical_normal (a : ℕ → ℂ) (ha : Tendsto (fun n => ‖a n‖) atTop atTop) :
    HolomorphicProducts.NormalProductCondition univ
      (fun n z => CanonicalFactors.factor n (z / a n)) := by
  intro K hK hKΩ
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have he : ∀ᶠ n in atTop, 2 * max R 1 ≤ ‖a n‖ := ha.eventually_ge_atTop _
  have hgeom : Summable (fun n : ℕ => 6 * (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).comp_injective
      (fun i j h => Nat.add_right_cancel h) |>.mul_left 6
  apply hgeom.of_norm_bounded_eventually_nat
  filter_upwards [he] with n hn
  have hb : ∀ z ∈ K, ‖CanonicalFactors.factor n (z / a n) - 1‖ ≤
      6 * (1 / 2 : ℝ) ^ (n + 1) := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by simpa using hR hz
    have hapos : 0 < ‖a n‖ := by linarith [le_max_right R 1]
    have hhalf : ‖z / a n‖ ≤ (1 / 2 : ℝ) := by
      rw [norm_div, div_le_iff₀ hapos]
      nlinarith [le_max_left R 1]
    exact (CanonicalFactors.norm_factor_sub_one_le n _ hhalf).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hhalf _) (by norm_num))
  have hsup : 0 ≤ sSup ((fun z => ‖CanonicalFactors.factor n (z / a n) - 1‖) '' K) := by
    obtain ⟨z, hz⟩ := hne
    exact (norm_nonneg _).trans (HolomorphicProducts.norm_sub_one_le_sup
      (rescaled_factor_entire a) hK hKΩ n hz)
  rw [Real.norm_eq_abs, abs_of_nonneg hsup]
  exact csSup_le (hne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact hb z hz)

lemma order_rescaled_factor (p : ℕ) {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    analyticOrderAt (fun w => CanonicalFactors.factor p (w / a)) z =
      (if a = z then 1 else 0 : ℕ∞) := by
  have hd : AnalyticAt ℂ (fun w : ℂ => w / a) z := by fun_prop
  have hder : deriv (fun w : ℂ => w / a) z ≠ 0 := by
    simpa using (inv_ne_zero ha)
  have he := analyticOrderAt_comp_of_deriv_ne_zero (f := CanonicalFactors.factor p) hd hder
  change analyticOrderAt (CanonicalFactors.factor p ∘ (fun w => w / a)) z = _
  rw [he]
  split_ifs with h
  · subst z
    rw [div_self ha]
    exact CanonicalFactors.factor_simple_zero p
  · apply (HolomorphicProducts.analyticAt_of_holomorphic
        (CanonicalFactors.factor_entire p) (mem_univ _)).analyticOrderAt_eq_zero.mpr
    simp only [ne_eq, CanonicalFactors.factor_eq_zero_iff]
    exact fun hz => h ((div_eq_one_iff_eq ha).mp hz).symm

theorem canonical_product : Specs.D12Complex.Ch16.EntireZeros.canonical_product_type := by
  classical
  intro a m ha hlim
  let u : ℕ → ℂ → ℂ := fun n z => CanonicalFactors.factor n (z / a n)
  have hu : ∀ n, HolomorphicOn univ (u n) := rescaled_factor_entire a
  have hn := canonical_normal a hlim
  obtain ⟨hconv, hhol⟩ := HolomorphicProducts.holomorphic_product_limit
    univ u isOpen_univ hu hn
  have han : ∀ z, AnalyticAt ℂ (fun z => ∏' n, u n z) z :=
    fun z => HolomorphicProducts.analyticAt_of_holomorphic hhol (mem_univ z)
  have hpow : HolomorphicOn univ (fun z : ℂ => z ^ m) :=
    ⟨isOpen_univ, fun _ _ => differentiableAt_id.pow m⟩
  have hfull : HolomorphicOn univ (canonicalProduct a m) :=
    ⟨isOpen_univ, fun z hz => (hpow.2 z hz).mul (hhol.2 z hz)⟩
  have horder : ∀ z, analyticOrderAt (canonicalProduct a m) z =
      (if z = 0 then (m : ℕ∞) else 0) +
        ∑' n, (if a n = z then 1 else 0 : ℕ∞) := by
    intro z
    have hc : ∀ n, ∃ w ∈ connectedComponentIn univ z, u n w ≠ 0 := by
      intro n
      refine ⟨0, by rw [isPreconnected_univ.connectedComponentIn (mem_univ z)]; trivial, ?_⟩
      simp [u, CanonicalFactors.factor,
        Specs.D12Complex.Ch16.CanonicalFactors.factor_value]
    obtain ⟨_, hsum, _⟩ := HolomorphicProducts.product_order_sum_on_component
      univ u isOpen_univ hu hn z (mem_univ z) hc
    change analyticOrderAt ((fun z : ℂ => z ^ m) * (fun z => ∏' n, u n z)) z = _
    rw [analyticOrderAt_mul (by fun_prop) (han z), hsum]
    congr 1
    · by_cases hz : z = 0
      · subst z
        have heq : ((· - (0 : ℂ)) ^ m : ℂ → ℂ) = fun w => w ^ m := by
          funext w
          simp
        rw [ite_eq_left rfl, ← heq]
        exact analyticOrderAt_centeredMonomial
      · rw [ite_eq_right hz]
        exact (show AnalyticAt ℂ (fun w : ℂ => w ^ m) z by fun_prop).analyticOrderAt_eq_zero.mpr (pow_ne_zero _ hz)
    · exact tsum_congr (fun n => order_rescaled_factor n (ha n) z)
  have hfin : analyticOrderAt (canonicalProduct a m) 0 ≠ ⊤ := by
    rw [horder]
    simp [ha]
  have hnon : ∃ z, canonicalProduct a m z ≠ 0 := by
    by_contra h
    have heq : canonicalProduct a m = (fun _ => 0) := by
      funext z
      exact not_ne_iff.mp (not_exists.mp h z)
    rw [heq] at hfin
    exact hfin analyticOrderAt_zero
  refine ⟨?_, hfull, hnon, horder, ?_⟩
  · have hconst : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z : ℂ => z ^ m)
        (fun z => z ^ m) atTop univ := by
      intro V hV x hx
      exact ⟨univ, univ_mem, Eventually.of_forall (fun _ y _ => refl_mem_uniformity hV)⟩
    exact (hconst.mul₀ hconv
      (continuous_id.pow m).continuousOn
      (fun z hz => (hhol.2 z hz).continuousAt.continuousWithinAt))
  · intro z
    change z ^ m * (∏' n, u n z) = 0 ↔ _
    rw [mul_eq_zero, HolomorphicProducts.product_eq_zero_iff univ u hn z (mem_univ z)]
    simp only [u, CanonicalFactors.factor_eq_zero_iff, div_eq_one_iff_eq (ha _),
      pow_eq_zero_iff', ne_eq]
    constructor
    · rintro (h | ⟨n, hn⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n, hn.symm⟩
    · rintro (h | ⟨n, hn⟩)
      · exact Or.inl h
      · exact Or.inr ⟨n, hn.symm⟩

/-- Finite analytic orders exclude the identically zero function and detect its zeros. -/
lemma realizes_of_order (d : ℂ → ℕ) (f : ℂ → ℂ)
    (hf : HolomorphicOn univ f) (ho : ∀ z, analyticOrderAt f z = (d z : ℕ∞)) :
    Realizes d f := by
  refine ⟨hf, ?_, ho, ?_⟩
  · by_contra h
    have heq : f = (0 : ℂ → ℂ) := by
      funext z
      exact not_ne_iff.mp (not_exists.mp h z)
    have ht := ho 0
    rw [heq, analyticOrderAt_zero] at ht
    exact (ENat.natCast_ne_top (d 0)) ht.symm
  · intro z
    have han := HolomorphicProducts.analyticAt_of_holomorphic hf (mem_univ z)
    rw [← han.analyticOrderAt_ne_zero, ho z]
    simp

lemma order_finset_product (s : Finset ℂ) (v : ℂ → ℂ → ℂ) (z : ℂ)
    (hv : ∀ c ∈ s, AnalyticAt ℂ (v c) z) :
    analyticOrderAt (fun w => ∏ c ∈ s, v c w) z = ∑ c ∈ s, analyticOrderAt (v c) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
  | @insert c s hc ih =>
      simp only [Finset.prod_insert hc, Finset.sum_insert hc]
      change analyticOrderAt (v c * (fun w => ∏ c ∈ s, v c w)) z = _
      rw [analyticOrderAt_mul (hv c (Finset.mem_insert_self _ _))
        (s.analyticAt_fun_prod (fun c hc => hv c (Finset.mem_insert_of_mem hc))),
        ih (fun c hc => hv c (Finset.mem_insert_of_mem hc))]

theorem finite_divisor : Specs.D12Complex.Ch16.EntireZeros.finite_divisor_type := by
  classical
  intro d s hs
  apply realizes_of_order
  · exact ⟨isOpen_univ, fun z _ => DifferentiableAt.fun_finsetProd (fun c _ => by fun_prop)⟩
  · intro z
    rw [order_finset_product s (fun c w => (w - c) ^ d c) z (fun c _ => by fun_prop)]
    have hord : ∀ c, analyticOrderAt (fun w : ℂ => (w - c) ^ d c) z =
        if c = z then (d c : ℕ∞) else 0 := by
      intro c
      change analyticOrderAt ((fun w : ℂ => w - c) ^ d c) z = _
      rw [analyticOrderAt_pow (by fun_prop)]
      by_cases hc : c = z
      · subst c
        simp
      · rw [analyticOrderAt_id_sub_const_of_ne (Ne.symm hc)]
        simp [hc]
    simp_rw [hord]
    by_cases hz : z ∈ s
    · simp [hz]
    · have hd : d z = 0 := by by_contra h; exact hz (hs z h)
      simp [hz, hd]

theorem empty_divisor : Specs.D12Complex.Ch16.EntireZeros.empty_divisor_type := by
  change Specs.D12Complex.Ch16.EntireZeros.Realizes_value (fun _ => 0) (fun _ => 1)
  simpa using finite_divisor (fun _ => 0) ∅ (by simp)

/-- Compact sets contain only finitely many multiplicity slots. -/
lemma finite_occurrences_on_compact (d : ℂ → ℕ) (hd : LocallyFiniteSupport d)
    (K : Set ℂ) (hK : IsCompact K) : {i : Occurrences d | i.1.1 ∈ K}.Finite := by
  classical
  have hbase : {z : {z : ℂ // z ≠ 0 ∧ d z ≠ 0} | z.1 ∈ K}.Finite := by
    apply ((hd.finite_inter_support_of_isCompact hK).preimage
      Subtype.val_injective.injOn).subset
    intro z hz
    exact ⟨hz, z.2.2⟩
  have h := hbase.sigma (fun z _ => Set.toFinite (univ : Set (Fin (d z))))
  apply h.subset
  intro i hi
  exact ⟨hi, mem_univ _⟩

/-- Reindexing the slots counts each assigned multiplicity exactly. -/
lemma occurrence_count (d : ℂ → ℕ) (e : ℕ ≃ Occurrences d) (z : ℂ) (hz : z ≠ 0) :
    (∑' n, (if (e n).1.1 = z then 1 else 0 : ℕ∞)) = (d z : ℕ∞) := by
  classical
  rw [e.tsum_eq (fun i => (if i.1.1 = z then 1 else 0 : ℕ∞))]
  by_cases hd : d z = 0
  · have hne : ∀ i : Occurrences d, i.1.1 ≠ z := by
      intro i hi
      exact i.1.2.2 (hi ▸ hd)
    simp [hne, hd]
  · let q : ↥{i : Occurrences d | i.1.1 = z} ≃ Fin (d z) :=
      { toFun := fun i => Fin.cast (congrArg d i.2) i.1.2
        invFun := fun k => ⟨⟨⟨z, hz, hd⟩, k⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨⟨w, hw⟩, k⟩, hi⟩
          simp only [Set.mem_ofPred_eq] at hi
          subst w
          rfl
        right_inv := by intro k; rfl }
    calc
      (∑' i : Occurrences d, (if i.1.1 = z then 1 else 0 : ℕ∞)) =
          ∑' i : ↥{i : Occurrences d | i.1.1 = z}, (1 : ℕ∞) := by
        simpa only [Set.indicator, mem_ofPred_eq] using
          (tsum_subtype {i : Occurrences d | i.1.1 = z} (fun _ => (1 : ℕ∞))).symm
      _ = ∑' _ : Fin (d z), (1 : ℕ∞) := q.tsum_eq (fun _ => 1)
      _ = (d z : ℕ∞) := by simp [tsum_fintype]

theorem enumerate_divisor : Specs.D12Complex.Ch16.EntireZeros.enumerate_divisor_type := by
  classical
  intro d hd hinf
  let D : Function.locallyFinsupp ℂ ℕ := ⟨d, subset_univ _, fun z _ => hd z⟩
  have hc : {z : ℂ | z ≠ 0 ∧ d z ≠ 0}.Countable :=
    ((HereditarilyLindelofSpace.isLindelof D.support).countable_of_isDiscrete
      D.discreteSupport).mono (fun z hz => hz.2)
  haveI := hc.to_subtype
  haveI : Countable {z : ℂ // z ≠ 0 ∧ d z ≠ 0} :=
    (show Function.Injective
        (fun z : {z : ℂ // z ≠ 0 ∧ d z ≠ 0} =>
          (⟨z.1, z.2⟩ : ↥{z : ℂ | z ≠ 0 ∧ d z ≠ 0})) from
      fun x y h => Subtype.ext (congrArg Subtype.val h)).countable
  haveI : Countable (Occurrences d) := by unfold Occurrences; infer_instance
  haveI : Infinite {z : ℂ // z ≠ 0 ∧ d z ≠ 0} := hinf.to_subtype
  haveI : Infinite (Occurrences d) := Infinite.of_surjective
    (fun i : Occurrences d => i.1)
    (fun z => ⟨⟨z, ⟨0, Nat.pos_of_ne_zero z.2.2⟩⟩, rfl⟩)
  let e : ℕ ≃ Occurrences d := Classical.choice inferInstance
  refine ⟨e, ?_, occurrence_count d e⟩
  apply Filter.tendsto_atTop.mpr
  intro R
  have hb := finite_occurrences_on_compact d hd (closedBall (0 : ℂ) R)
    (isCompact_closedBall _ _)
  have hpre : {n : ℕ | ‖(e n).1.1‖ ≤ R}.Finite := by
    simpa using hb.preimage e.injective.injOn
  obtain ⟨N, hN⟩ := hpre.bddAbove
  filter_upwards [eventually_gt_atTop N] with n hn
  by_contra h
  exact (not_le_of_gt hn) (hN (le_of_lt (lt_of_not_ge h)))

theorem infinite_divisor_product :
    Specs.D12Complex.Ch16.EntireZeros.infinite_divisor_product_type := by
  intro d hd hinf
  obtain ⟨e, he, hcount⟩ := enumerate_divisor d hd hinf
  have hne : ∀ n, (e n).1.1 ≠ 0 := fun n => (e n).1.2.1
  obtain ⟨_, hhol, _, hord, _⟩ := canonical_product (fun n => (e n).1.1) (d 0) hne he
  refine ⟨e, he, realizes_of_order d _ hhol ?_⟩
  intro z
  rw [hord z]
  by_cases hz : z = 0
  · subst z
    simp [hne]
  · rw [ite_eq_right hz, zero_add, hcount z hz]

theorem entire_prescribed_zeros :
    Specs.D12Complex.Ch16.EntireZeros.entire_prescribed_zeros_type := by
  classical
  intro d hd
  by_cases h : {z : ℂ | z ≠ 0 ∧ d z ≠ 0}.Finite
  · let s : Finset ℂ := insert 0 h.toFinset
    exact ⟨_, finite_divisor d s (fun z hz => by
      by_cases hz0 : z = 0
      · subst z; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (h.mem_toFinset.mpr ⟨hz0, hz⟩))⟩
  · obtain ⟨e, _, hr⟩ := infinite_divisor_product d hd (Set.not_finite.mp h)
    exact ⟨_, hr⟩

end D12Complex.EntireZeros
