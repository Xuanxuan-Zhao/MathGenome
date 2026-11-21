import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Besicovitch
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open Set MeasureTheory

namespace ExpandedFA.PartIV.Besicovitch

lemma weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity

lemma summable_weight : Summable weight := by
  change Summable (fun n => weight n)
  simpa [weight, pow_succ, mul_inv_rev, inv_pow] using
    (summable_geometric_two.mul_left (1 / 2 : ℝ))

lemma tsum_weight : ∑' n, weight n = 1 := by
  simpa [weight, pow_succ, mul_inv_rev, inv_pow] using
    (hasSum_geometric_two.mul_left (1 / 2 : ℝ)).tsum_eq

lemma digit_nonneg (a : BinarySequence) (n : ℕ) : 0 ≤ (a n : ℝ) := by positivity

lemma digit_le_one (a : BinarySequence) (n : ℕ) : (a n : ℝ) ≤ 1 := by
  exact_mod_cast (show (a n : ℕ) ≤ 1 by omega)

lemma abs_sub_centers_le_one {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) : |x - c n| ≤ 1 := by
  simpa using abs_sub_le_of_le_of_le hx.1 hx.2 (hc n).1 (hc n).2

lemma summable_digit_weight (a : BinarySequence) :
    Summable (fun n => (a n : ℝ) * weight n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (digit_nonneg a n) (weight_pos n).le) _ summable_weight
  intro n
  exact mul_le_of_le_one_left (weight_pos n).le (digit_le_one a n)

lemma summable_height {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    (a : BinarySequence) (x : ℝ) :
    Summable (fun n => (a n : ℝ) * weight n * (x - c n)) := by
  apply Summable.of_norm_bounded (summable_weight.mul_right (|x| + 1))
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (digit_nonneg a n), abs_of_nonneg (weight_pos n).le]
  apply mul_le_mul
  · exact mul_le_of_le_one_left (weight_pos n).le (digit_le_one a n)
  · calc
      |x - c n| ≤ |x| + |c n| := abs_sub _ _
      _ ≤ |x| + 1 := by rw [abs_of_nonneg (hc n).1]; linarith [(hc n).2]
  · exact abs_nonneg _
  · exact (weight_pos n).le

lemma continuous_height {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1) :
    Continuous (fun z : Icc (0 : ℝ) 1 × BinarySequence => height c z.2 z.1) := by
  apply continuous_tsum (u := weight)
  · intro n
    unfold weight
    fun_prop
  · exact summable_weight
  · intro n z
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (digit_nonneg z.2 n), abs_of_nonneg (weight_pos n).le]
    calc
      (z.2 n : ℝ) * weight n * |(z.1 : ℝ) - c n|
          ≤ 1 * weight n * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (digit_le_one z.2 n) (weight_pos n).le
        · exact abs_sub_centers_le_one hc z.1.property n
        · exact abs_nonneg _
        · exact mul_nonneg zero_le_one (weight_pos n).le
      _ = weight n := by ring

theorem base_compact : Spec.BaseCompact := by
  intro c hc
  let f : Icc (0 : ℝ) 1 × BinarySequence → ℝ × ℝ :=
    fun z => (z.1, height c z.2 z.1)
  have hf : Continuous f := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_height hc)
  have heq : baseSet c = Set.range f := by
    ext p
    constructor
    · rintro ⟨hx, a, ha⟩
      exact ⟨(⟨p.1, hx⟩, a), Prod.ext rfl ha⟩
    · rintro ⟨⟨x, a⟩, rfl⟩
      exact ⟨x.property, a, rfl⟩
  rw [heq]
  exact isCompact_range hf

lemma height_eq_affine {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    (a : BinarySequence) (x : ℝ) :
    height c a x = Real.ofDigits a * x - ∑' n, (a n : ℝ) * weight n * c n := by
  have hs := summable_digit_weight a
  have hsc : Summable (fun n => (a n : ℝ) * weight n * c n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (mul_nonneg (digit_nonneg a n) (weight_pos n).le) (hc n).1)
      _ hs
    intro n
    exact mul_le_of_le_one_right (mul_nonneg (digit_nonneg a n) (weight_pos n).le) (hc n).2
  unfold height
  simp_rw [mul_sub]
  rw [hs.mul_right x |>.tsum_sub hsc, tsum_mul_right]
  rfl

theorem base_slopes : Spec.BaseSlopes := by
  intro c hc m hm
  obtain ⟨a, _, ha⟩ := Real.ofDigits_SurjOn (b := 2) (by norm_num) hm
  refine ⟨-(∑' n, (a n : ℝ) * weight n * c n), ?_⟩
  intro x hx
  refine ⟨hx, a, ?_⟩
  rw [height_eq_affine hc, ha]
  ring

/-- A dyadic block construction: block j is [2^j, 2^(j+1)), and
its value is selected from a dense sequence using the first unpair coordinate.
The second coordinate ensures arbitrarily long repetitions of each value. -/
theorem approximation_blocks_exist : Spec.ApproximationBlocksExist := by
  let : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by constructor <;> norm_num⟩⟩
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (Icc (0 : ℝ) 1)
  let c : ℕ → ℝ := fun n => q (Nat.unpair (Nat.log 2 n)).1
  refine ⟨c, fun n => (q _).property, ?_⟩
  intro x hx ε hε r
  obtain ⟨i, hi⟩ := hq.exists_dist_lt (⟨x, hx⟩ : Icc (0 : ℝ) 1) hε
  let j := Nat.pair i r
  have hrj : r ≤ j := Nat.right_le_pair i r
  have hrpow : r ≤ 2 ^ j := hrj.trans j.lt_two_pow_self.le
  refine ⟨2 ^ j, ?_⟩
  intro k hk
  have hlog : Nat.log 2 (2 ^ j + k) = j := by
    apply (Nat.log_eq_iff (b := 2) (m := j) (n := 2 ^ j + k) (Or.inr ⟨by norm_num, by omega⟩)).mpr
    constructor
    · omega
    · rw [pow_succ]
      omega
  change |x - (q (Nat.unpair (Nat.log 2 (2 ^ j + k))).1 : ℝ)| ≤ ε
  rw [hlog, Nat.unpair_pair]
  simpa only [Subtype.dist_eq, Real.dist_eq] using hi.le

lemma weight_add (N k : ℕ) : weight (N + k) = ((2 : ℝ) ^ N)⁻¹ * weight k := by
  simp only [weight, show N + k + 1 = N + (k + 1) by omega, pow_add, mul_inv]

def tailRadius (c : ℕ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  ∑' k, weight k * |x - c (N + k)|

lemma summable_tailRadius {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    Summable (fun k => weight k * |x - c (N + k)|) := by
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (weight_pos k).le (abs_nonneg _))
    (fun k => mul_le_of_le_one_right (weight_pos k).le
      (abs_sub_centers_le_one hc hx (N + k))) summable_weight

lemma tailRadius_nonneg (c : ℕ → ℝ) (x : ℝ) (N : ℕ) : 0 ≤ tailRadius c x N :=
  tsum_nonneg fun k => mul_nonneg (weight_pos k).le (abs_nonneg _)

lemma tailRadius_le_one {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (N : ℕ) : tailRadius c x N ≤ 1 := by
  rw [← tsum_weight]
  exact (summable_tailRadius hc hx N).tsum_le_tsum
    (fun k => mul_le_of_le_one_right (weight_pos k).le
      (abs_sub_centers_le_one hc hx (N + k))) summable_weight

lemma tailRadius_le_of_block {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε)
    (N r : ℕ) (hblock : ∀ k < r, |x - c (N + k)| ≤ ε) :
    tailRadius c x N ≤ ε + ((2 : ℝ) ^ r)⁻¹ := by
  have hs := summable_tailRadius hc hx N
  have hearly : ∑ k ∈ Finset.range r, weight k * |x - c (N + k)| ≤ ε := by
    calc
      _ ≤ ∑ k ∈ Finset.range r, weight k * ε := by
        exact Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (hblock k (Finset.mem_range.mp hk)) (weight_pos k).le
      _ = (∑ k ∈ Finset.range r, weight k) * ε := by rw [Finset.sum_mul]
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right
        (by simpa only [tsum_weight] using
          summable_weight.sum_le_tsum (Finset.range r) (fun k _ => (weight_pos k).le)) hε
      _ = ε := one_mul ε
  have hlate : (∑' k, weight (k + r) * |x - c (N + (k + r))|) ≤ ((2 : ℝ) ^ r)⁻¹ := by
    calc
      _ ≤ ∑' k, weight (k + r) := by
        exact (hs.comp_injective (add_left_injective r)).tsum_le_tsum
          (fun k => mul_le_of_le_one_right (weight_pos (k + r)).le
            (abs_sub_centers_le_one hc hx _))
          (summable_weight.comp_injective (add_left_injective r))
      _ = ((2 : ℝ) ^ r)⁻¹ := by
        simp_rw [Nat.add_comm _ r, weight_add, tsum_mul_left, tsum_weight, mul_one]
  unfold tailRadius
  rw [← hs.sum_add_tsum_nat_add r]
  linarith

lemma height_sub_prefix_le {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (a : BinarySequence) (N : ℕ) :
    |height c a x - ∑ n ∈ Finset.range N, (a n : ℝ) * weight n * (x - c n)| ≤
      ((2 : ℝ) ^ N)⁻¹ * tailRadius c x N := by
  have hs := summable_height hc a x
  unfold height
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  calc
    _ ≤ ∑' k, |(a (k + N) : ℝ) * weight (k + N) * (x - c (k + N))| :=
      by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using
          (norm_tsum_le_tsum_norm (hs.comp_injective (add_left_injective N)).norm)
    _ ≤ ∑' k, weight (k + N) * |x - c (k + N)| := by
      apply Summable.tsum_le_tsum
      · intro k
        rw [abs_mul, abs_mul, abs_of_nonneg (digit_nonneg a _),
          abs_of_nonneg (weight_pos _).le]
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_left (weight_pos _).le (digit_le_one a _)) (abs_nonneg _)
      · exact (hs.comp_injective (add_left_injective N)).abs
      · simpa only [Nat.add_comm _ N, weight_add, mul_assoc] using
          (summable_tailRadius hc hx N).mul_left (((2 : ℝ) ^ N)⁻¹)
    _ = ((2 : ℝ) ^ N)⁻¹ * tailRadius c x N := by
      simp_rw [Nat.add_comm _ N, weight_add, mul_assoc, tsum_mul_left]
      rfl

lemma fiber_volume_le {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    volume {y : ℝ | (x, y) ∈ baseSet c} ≤ ENNReal.ofReal (2 * tailRadius c x N) := by
  classical
  let R := ((2 : ℝ) ^ N)⁻¹ * tailRadius c x N
  let P : (Fin N → Fin 2) → ℝ := fun b =>
    ∑ n : Fin N, (b n : ℝ) * weight n * (x - c n)
  have hcover : {y : ℝ | (x, y) ∈ baseSet c} ⊆
      ⋃ b : Fin N → Fin 2, Icc (P b - R) (P b + R) := by
    rintro y ⟨_, a, haeq⟩
    change height c a x = y at haeq
    subst y
    refine mem_iUnion.mpr ⟨fun n => a n, ?_⟩
    have ha := height_sub_prefix_le hc hx a N
    have hp : P (fun n => a n) =
        ∑ n ∈ Finset.range N, (a n : ℝ) * weight n * (x - c n) := by
      exact Fin.sum_univ_eq_sum_range (fun n => (a n : ℝ) * weight n * (x - c n)) N
    rw [← hp, abs_le] at ha
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
  calc
    _ ≤ volume (⋃ b : Fin N → Fin 2, Icc (P b - R) (P b + R)) := measure_mono hcover
    _ ≤ ∑ b : Fin N → Fin 2, volume (Icc (P b - R) (P b + R)) :=
      measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal (2 * tailRadius c x N) := by
      simp_rw [Real.volume_Icc, show ∀ b, P b + R - (P b - R) = 2 * R by intro b; ring]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      dsimp [R]
      field_simp

theorem base_fibers_null : Spec.BaseFibersNull := by
  intro c hc hb x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · apply le_antisymm _ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : 0 < (ε : ℝ) := hε
    have hpow : Filter.Tendsto (fun r : ℕ => ((2 : ℝ) ^ r)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [inv_pow] using
        tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
    obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp
      ((tendsto_order.mp hpow).2 ((ε : ℝ) / 4) (by linarith))
    have hr' := hr r le_rfl
    obtain ⟨N, hN⟩ := hb x hx ((ε : ℝ) / 4) (by linarith) r
    have htail := tailRadius_le_of_block hc hx (show 0 ≤ (ε : ℝ) / 4 by linarith) N r hN
    have hvol := fiber_volume_le hc hx N
    have hbound : 2 * tailRadius c x N ≤ (ε : ℝ) := by linarith
    simpa using hvol.trans (ENNReal.ofReal_le_ofReal hbound)
  · have he : {y : ℝ | (x, y) ∈ baseSet c} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, baseSet, mem_empty_iff_false, iff_false, not_and]
      exact fun h => False.elim (hx h)
    rw [he, measure_empty]

lemma base_null {c : ℕ → ℝ} (hc : ∀ n, c n ∈ Icc (0 : ℝ) 1)
    (hb : HasApproximationBlocks c) : volume (baseSet c) = 0 := by
  exact Measure.measure_prod_null_of_ae_null (base_compact c hc).measurableSet
    (Filter.Eventually.of_forall (base_fibers_null c hc hb))

/-- Coordinate reflection. -/
def changeSign (s : Bool) (x : ℝ) : ℝ := if s then -x else x

def signedCoordinates (s t : Bool) : (ℝ × ℝ) → (ℝ × ℝ) :=
  Prod.map (changeSign s) (changeSign t)

lemma continuous_changeSign (s : Bool) : Continuous (changeSign s) := by
  cases s
  · exact continuous_id
  · exact continuous_neg

lemma continuous_signedCoordinates (s t : Bool) : Continuous (signedCoordinates s t) := by
  exact (continuous_changeSign s).prodMap (continuous_changeSign t)

lemma changeSign_involutive (s : Bool) : Function.Involutive (changeSign s) := by
  cases s <;> intro x <;> simp [changeSign]

lemma signedCoordinates_involutive (s t : Bool) : Function.Involutive (signedCoordinates s t) := by
  intro p
  exact Prod.ext (changeSign_involutive s p.1) (changeSign_involutive t p.2)

lemma measurePreserving_changeSign (s : Bool) : MeasurePreserving (changeSign s) := by
  cases s
  · exact MeasurePreserving.id volume
  · exact Measure.measurePreserving_neg volume

lemma measurePreserving_signedCoordinates (s t : Bool) :
    MeasurePreserving (signedCoordinates s t) :=
  (measurePreserving_changeSign s).prod (measurePreserving_changeSign t)

lemma null_image_of_involutive {f : (ℝ × ℝ) → (ℝ × ℝ)}
    (hf : MeasurePreserving f) (hi : Function.Involutive f)
    {K : Set (ℝ × ℝ)} (hK : volume K = 0) : volume (f '' K) = 0 := by
  apply measure_mono_null _ (hf.quasiMeasurePreserving.preimage_null hK)
  rintro _ ⟨p, hp, rfl⟩
  change f (f p) ∈ K
  rwa [hi p]

/-- Eight orthogonal copies, replacing the four rotations in the source.
Coordinate reflections and interchange cover the same unoriented directions. -/
def directionHull (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  ⋃ s : Bool, ⋃ t : Bool, signedCoordinates s t '' (K ∪ Prod.swap '' K)

lemma directionHull_compact {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    IsCompact (directionHull K) := by
  apply isCompact_iUnion
  intro s
  apply isCompact_iUnion
  intro t
  exact (hK.union (hK.image continuous_swap)).image (continuous_signedCoordinates s t)

lemma directionHull_null {K : Set (ℝ × ℝ)} (hK : volume K = 0) :
    volume (directionHull K) = 0 := by
  have hswap : volume (Prod.swap '' K) = 0 :=
    null_image_of_involutive Measure.measurePreserving_swap Prod.swap_swap hK
  have hu : volume (K ∪ Prod.swap '' K) = 0 := measure_union_null hK hswap
  apply measure_iUnion_null
  intro s
  apply measure_iUnion_null
  intro t
  exact null_image_of_involutive (measurePreserving_signedCoordinates s t)
    (signedCoordinates_involutive s t) hu

lemma signedCoordinates_add_smul (s t : Bool) (p v : ℝ × ℝ) (r : ℝ) :
    signedCoordinates s t (p + r • v) =
      signedCoordinates s t p + r • signedCoordinates s t v := by
  cases s <;> cases t <;> ext <;> simp [signedCoordinates, changeSign] <;> ring

lemma changeSign_abs (x : ℝ) : changeSign (decide (x < 0)) |x| = x := by
  by_cases hx : x < 0
  · simp [changeSign, hx, abs_of_neg hx]
  · simp [changeSign, hx, abs_of_nonneg (le_of_not_gt hx)]

lemma segment_of_slope {K : Set (ℝ × ℝ)}
    (hs : ∀ m ∈ Icc (0 : ℝ) 1, ∃ b : ℝ,
      ∀ x ∈ Icc (0 : ℝ) 1, (x, m * x + b) ∈ K)
    {d e : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (he : 0 ≤ e) (hed : e ≤ d) :
    ∃ p : ℝ × ℝ, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (d, e) ∈ K := by
  obtain ⟨b, hb⟩ := hs (e / d) ⟨div_nonneg he hd.le, (div_le_one hd).mpr hed⟩
  refine ⟨(0, b), ?_⟩
  intro t ht
  have hx : t * d ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg ht.1 hd.le, (mul_le_mul_of_nonneg_right ht.2 hd.le).trans (by simpa using hd1)⟩
  have hh := hb (t * d) hx
  convert hh using 1
  ext <;> simp
  field_simp
  ring

lemma directionHull_segments {K : Set (ℝ × ℝ)}
    (hs : ∀ m ∈ Icc (0 : ℝ) 1, ∃ b : ℝ,
      ∀ x ∈ Icc (0 : ℝ) 1, (x, m * x + b) ∈ K) :
    ContainsUnitSegments (directionHull K) := by
  intro v hv
  let s := decide (v.1 < 0)
  let t := decide (v.2 < 0)
  have hsign : signedCoordinates s t (|v.1|, |v.2|) = v :=
    Prod.ext (changeSign_abs v.1) (changeSign_abs v.2)
  have hx1 : |v.1| ≤ 1 := by
    have h := sq_nonneg v.2
    have ha := abs_nonneg v.1
    nlinarith [sq_abs v.1]
  have hy1 : |v.2| ≤ 1 := by
    have h := sq_nonneg v.1
    have ha := abs_nonneg v.2
    nlinarith [sq_abs v.2]
  rcases le_total |v.2| |v.1| with hdom | hdom
  · have hd : 0 < |v.1| := by
      have hx := abs_nonneg v.1
      have hy := abs_nonneg v.2
      nlinarith [sq_abs v.1, sq_abs v.2]
    obtain ⟨p, hp⟩ := segment_of_slope hs hd hx1 (abs_nonneg v.2) hdom
    refine ⟨signedCoordinates s t p, ?_⟩
    intro r hr
    apply mem_iUnion.mpr
    refine ⟨s, mem_iUnion.mpr ⟨t, ?_⟩⟩
    refine ⟨p + r • (|v.1|, |v.2|), Or.inl (hp r hr), ?_⟩
    rw [signedCoordinates_add_smul, hsign]
  · have hd : 0 < |v.2| := by
      have hx := abs_nonneg v.1
      have hy := abs_nonneg v.2
      nlinarith [sq_abs v.1, sq_abs v.2]
    obtain ⟨p, hp⟩ := segment_of_slope hs hd hy1 (abs_nonneg v.1) hdom
    refine ⟨signedCoordinates s t (Prod.swap p), ?_⟩
    intro r hr
    apply mem_iUnion.mpr
    refine ⟨s, mem_iUnion.mpr ⟨t, ?_⟩⟩
    refine ⟨Prod.swap (p + r • (|v.2|, |v.1|)), Or.inr ⟨_, hp r hr, rfl⟩, ?_⟩
    have heq : Prod.swap (p + r • (|v.2|, |v.1|)) =
        Prod.swap p + r • (|v.1|, |v.2|) := rfl
    rw [heq, signedCoordinates_add_smul, hsign]

theorem compact_null_unit_segments : Spec.CompactNullUnitSegments := by
  obtain ⟨c, hc, hb⟩ := approximation_blocks_exist
  exact ⟨directionHull (baseSet c), directionHull_compact (base_compact c hc),
    directionHull_null (base_null hc hb), directionHull_segments (base_slopes c hc)⟩

end ExpandedFA.PartIV.Besicovitch
