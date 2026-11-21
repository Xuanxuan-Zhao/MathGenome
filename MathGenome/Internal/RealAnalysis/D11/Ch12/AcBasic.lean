import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcBasic
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch12.BvDefinition
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set
open scoped BigOperators NNReal ENNReal

namespace D11.Ch12.AcBasic

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The source modulus works for any finite index type, not only `Fin n`. -/
lemma finite_family {F : ℝ → 𝕂} {s : Set ℝ} {ε δ : ℝ}
    (h : ∀ (n : ℕ) (u v : Fin n → ℝ), (∀ j, u j < v j) →
      (∀ j, u j ∈ s ∧ v j ∈ s) →
      (Pairwise fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j))) →
      (∑ j, (v j - u j)) < δ → (∑ j, ‖F (v j) - F (u j)‖) < ε)
    {ι : Type*} [Fintype ι] (u v : ι → ℝ)
    (huv : ∀ j, u j < v j) (hs : ∀ j, u j ∈ s ∧ v j ∈ s)
    (hd : Pairwise fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j)))
    (hlen : (∑ j : ι, (v j - u j)) < δ) : (∑ j : ι, ‖F (v j) - F (u j)‖) < ε := by
  classical
  let e := Fintype.equivFin ι
  have hl : (∑ j, (v (e.symm j) - u (e.symm j))) < δ := by
    rw [e.symm.sum_comp (fun j => v j - u j)]
    exact hlen
  have hh := h (Fintype.card ι) (u ∘ e.symm) (v ∘ e.symm)
    (fun j => huv _) (fun j => hs _)
    (fun i j hij => hd (e.symm.injective.ne hij)) hl
  change (∑ j, ‖F (v (e.symm j)) - F (u (e.symm j))‖) < ε at hh
  rwa [e.symm.sum_comp (fun j => ‖F (v j) - F (u j)‖)] at hh

/-- Zero-length intervals can be discarded without changing either sum. -/
lemma finite_family_le {F : ℝ → 𝕂} {s : Set ℝ} {ε δ : ℝ}
    (h : ∀ (n : ℕ) (u v : Fin n → ℝ), (∀ j, u j < v j) →
      (∀ j, u j ∈ s ∧ v j ∈ s) →
      (Pairwise fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j))) →
      (∑ j, (v j - u j)) < δ → (∑ j, ‖F (v j) - F (u j)‖) < ε)
    {ι : Type*} [Fintype ι] (u v : ι → ℝ)
    (huv : ∀ j, u j ≤ v j) (hs : ∀ j, u j ∈ s ∧ v j ∈ s)
    (hd : Pairwise fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j)))
    (hlen : (∑ j : ι, (v j - u j)) < δ) : (∑ j : ι, ‖F (v j) - F (u j)‖) < ε := by
  classical
  have sum_restrict (g : ι → ℝ) (hg : ∀ j, ¬u j < v j → g j = 0) :
      (∑ j : {j // u j < v j}, g j) = ∑ j, g j := by
    exact (Finset.sum_congr_set {j | u j < v j} g (fun j => g j)
      (by intros; rfl) hg).symm
  have hl := sum_restrict (fun j => v j - u j) (by
    intro j hj; have := (huv j).antisymm (le_of_not_gt hj); simp [this])
  have hv := sum_restrict (fun j => ‖F (v j) - F (u j)‖) (by
    intro j hj; have := (huv j).antisymm (le_of_not_gt hj); simp [this])
  rw [← hv]
  exact finite_family h (fun j : {j // u j < v j} => u j)
    (fun j => v j) (fun j => j.property) (fun j => hs j)
    (fun i j hij => hd (Subtype.coe_ne_coe.mpr hij)) (by rwa [hl])

/-- Equivalence of the accepted open-interval convention and Mathlib's
unordered half-open convention; degenerate intervals contribute zero. -/
theorem library_iff {F : ℝ → 𝕂} {a b : ℝ} (hab : a ≤ b) :
    D11.Ch12.AbsolutelyContinuousOnInterval F a b ↔
      _root_.AbsolutelyContinuousOnInterval F a b := by
  classical
  rw [_root_.absolutelyContinuousOnInterval_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    rintro ⟨n, I⟩ hI hlen
    let u : Fin n → ℝ := fun i => min (I i).1 (I i).2
    let v : Fin n → ℝ := fun i => max (I i).1 (I i).2
    have hmem (i : Fin n) : u i ∈ Icc a b ∧ v i ∈ Icc a b := by
      have := hI.1 i (Finset.mem_range.mpr i.isLt)
      rw [uIcc_of_le hab] at this
      exact ⟨min_rec' (· ∈ Icc a b) this.1 this.2,
        max_rec' (· ∈ Icc a b) this.1 this.2⟩
    have hdis : Pairwise fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j)) := by
      intro i j hij
      exact (hI.2 (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt)
        (Fin.val_injective.ne hij)).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self
    have hlength : (∑ i : Fin n, (v i - u i)) < δ := by
      change (∑ i ∈ Finset.range n, dist (I i).1 (I i).2) < δ at hlen
      rw [← Fin.sum_univ_eq_sum_range] at hlen
      simpa [u, v, max_sub_min_eq_abs, Real.dist_eq, abs_sub_comm] using hlen
    have hv := finite_family_le hd u v (fun i => min_le_max) hmem hdis hlength
    have heq (i : Fin n) : ‖F (v i) - F (u i)‖ = dist (F (I i).1) (F (I i).2) := by
      dsimp [u, v]
      rcases le_total (I i).1 (I i).2 with h | h
      · simp [min_eq_left h, max_eq_right h, dist_eq_norm, norm_sub_rev]
      · simp [min_eq_right h, max_eq_left h, dist_eq_norm]
    change (∑ i ∈ Finset.range n, dist (F (I i).1) (F (I i).2)) < ε
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [heq] using hv
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro n u v huv hs hdis hlen
    let I : ℕ → ℝ × ℝ := fun i => if hi : i < n then (u ⟨i, hi⟩, v ⟨i, hi⟩) else (a, a)
    have hI : (n, I) ∈ _root_.AbsolutelyContinuousOnInterval.disjWithin a b := by
      constructor
      · intro i hi
        simp only [Finset.mem_range] at hi
        simpa [I, hi, uIcc_of_le hab] using hs ⟨i, hi⟩
      · intro i hi j hj hij
        have hi : i < n := Finset.mem_range.mp hi
        have hj : j < n := Finset.mem_range.mp hj
        change Disjoint (uIoc (I i).1 (I i).2) (uIoc (I j).1 (I j).2)
        simp only [I, hi, hj, dite_eq_left, uIoc_of_le (huv _).le]
        rw [Ioc_disjoint_Ioc, ← Ioo_disjoint_Ioo]
        exact hdis ((fun h => hij (congrArg Fin.val h)))
    have hl : (∑ i ∈ Finset.range n, dist (I i).1 (I i).2) < δ := by
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [I, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (huv _).le)] using hlen
    have hh := hd (n, I) hI hl
    rw [← Fin.sum_univ_eq_sum_range] at hh
    simpa [I, dist_eq_norm, norm_sub_rev] using hh

/-- One source interval suffices for uniform continuity. -/
theorem uniformContinuousOn {F : ℝ → 𝕂} {a b : ℝ} (hab : a ≤ b)
    (hF : D11.Ch12.AbsolutelyContinuousOnInterval F a b) :
    UniformContinuousOn F (Icc a b) := by
  simpa [uIcc_of_le hab] using ((library_iff hab).mp hF).uniformContinuousOn

/-- The conclusion uses the classical strict-partition variation. -/
theorem bv {F : ℝ → 𝕂} {a b : ℝ} (hab : a ≤ b)
    (hF : D11.Ch12.AbsolutelyContinuousOnInterval F a b) : D11.Ch12.BV F a b := by
  apply (D11.Ch12.bv_iff_boundedVariationOn F a b).mpr
  simpa [uIcc_of_le hab] using ((library_iff hab).mp hF).boundedVariationOn

theorem add {F G : ℝ → 𝕂} {a b : ℝ} (hab : a ≤ b)
    (hF : D11.Ch12.AbsolutelyContinuousOnInterval F a b)
    (hG : D11.Ch12.AbsolutelyContinuousOnInterval G a b) :
    D11.Ch12.AbsolutelyContinuousOnInterval (fun x => F x + G x) a b :=
  (library_iff hab).mpr (((library_iff hab).mp hF).fun_add ((library_iff hab).mp hG))

theorem const_mul (c : 𝕂) {F : ℝ → 𝕂} {a b : ℝ} (hab : a ≤ b)
    (hF : D11.Ch12.AbsolutelyContinuousOnInterval F a b) :
    D11.Ch12.AbsolutelyContinuousOnInterval (fun x => c * F x) a b := by
  exact (library_iff hab).mpr (((library_iff hab).mp hF).const_smul c)

theorem mul {F G : ℝ → 𝕂} {a b : ℝ} (hab : a ≤ b)
    (hF : D11.Ch12.AbsolutelyContinuousOnInterval F a b)
    (hG : D11.Ch12.AbsolutelyContinuousOnInterval G a b) :
    D11.Ch12.AbsolutelyContinuousOnInterval (fun x => F x * G x) a b := by
  exact (library_iff hab).mpr (((library_iff hab).mp hF).fun_smul ((library_iff hab).mp hG))

/-- A single modulus works on arbitrary real domains, hence also globally. -/
theorem lipschitzOn {F : ℝ → 𝕂} {s : Set ℝ} {L : ℝ≥0}
    (hF : LipschitzOnWith L F s) : D11.Ch12.AbsolutelyContinuousOn F s := by
  intro ε hε
  refine ⟨ε / (L + 1), by positivity, ?_⟩
  intro n u v huv hs _ hlen
  calc
    (∑ j, ‖F (v j) - F (u j)‖) ≤ ∑ j, L * (v j - u j) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [dist_eq_norm, Real.dist_eq, abs_of_pos (sub_pos.mpr (huv j))] using
        hF.dist_le_mul (v j) (hs j).2 (u j) (hs j).1
    _ = L * ∑ j, (v j - u j) := (Finset.mul_sum ..).symm
    _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hlen.le L.coe_nonneg
    _ < (L + 1) * (ε / (L + 1)) := by gcongr; linarith
    _ = ε := by field_simp

theorem finite_linear_combination {ι : Type*} (t : Finset ι) (c : ι → 𝕂)
    (F : ι → ℝ → 𝕂) {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ i ∈ t, D11.Ch12.AbsolutelyContinuousOnInterval (F i) a b) :
    D11.Ch12.AbsolutelyContinuousOnInterval (fun x => ∑ i ∈ t, c i * F i x) a b := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa [D11.Ch12.AbsolutelyContinuousOnInterval] using (lipschitzOn (F := fun _ : ℝ => (0 : 𝕂)) (s := Icc a b)
      (LipschitzWith.const (α := ℝ) (0 : 𝕂)).lipschitzOnWith)
  | @insert i t hi ih =>
    simp only [Finset.forall_mem_insert] at hF
    simpa [Finset.sum_insert hi] using
      add hab (const_mul (c i) hab hF.1) (ih hF.2)

/-- Elementary power integration, rather than the AC FTC, proves this example. -/
theorem sqrt_ac : D11.Ch12.AbsolutelyContinuousOnInterval Real.sqrt 0 1 := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (- (1 / 2 : ℝ)))
      MeasureTheory.volume 0 1 := intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have ha := hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  apply (library_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  apply (ha.const_smul (1 / 2 : ℝ)).congr
  intro x hx
  dsimp only
  rw [smul_eq_mul, integral_rpow (Or.inl (by norm_num))]
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
  rw [Real.sqrt_eq_rpow]
  ring

/-- The slopes at zero are unbounded, with explicit witnesses for every constant. -/
theorem sqrt_not_lipschitz : ¬ ∃ L : ℝ≥0, LipschitzOnWith L Real.sqrt (Icc (0 : ℝ) 1) := by
  rintro ⟨L, hL⟩
  let t : ℝ := 1 / (L + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_one (by positivity)).mpr; linarith [L.coe_nonneg]
  have hx : t ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith⟩
  have hb := hL.dist_le_mul (t ^ 2) hx 0 (by simp)
  have hbound : t ≤ (L : ℝ) * t ^ 2 := by
    simpa [Real.dist_eq, Real.sqrt_sq ht.le, abs_of_nonneg ht.le,
      abs_of_nonneg (sq_nonneg t)] using hb
  have hid : ((L : ℝ) + 1) * t = 1 := by dsimp [t]; field_simp
  nlinarith [sq_pos_of_pos ht, mul_nonneg (sub_nonneg.mpr hbound) ht.le]

/-- Taking independent suprema commutes with a finite sum, in the form
needed to bound sums of variations by a single AC modulus. -/
lemma sum_iSup_le {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, Nonempty (β i)] (f : ∀ i, β i → ℝ≥0∞) (K : ℝ≥0∞)
    (h : ∀ p : ∀ i, β i, (∑ i, f i (p i)) ≤ K) :
    (∑ i, ⨆ j, f i j) ≤ K := by
  classical
  have hs (s : Finset ι) : ∀ z : ℝ≥0∞,
      (∀ p : ∀ i, β i, z + ∑ i ∈ s, f i (p i) ≤ K) →
        z + ∑ i ∈ s, ⨆ j, f i j ≤ K := by
    induction s using Finset.induction_on with
    | empty =>
      intro z hz
      simpa using hz (fun i => Classical.choice (inferInstance : Nonempty (β i)))
    | @insert a s ha ih =>
      intro z hz
      rw [Finset.sum_insert ha, ← add_assoc, ENNReal.add_iSup, ENNReal.iSup_add]
      apply iSup_le
      intro b
      apply ih
      intro p
      have heq : (∑ i ∈ s, f i (Function.update p a b i)) = ∑ i ∈ s, f i (p i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
      have hh := hz (Function.update p a b)
      simpa [Finset.sum_insert ha, Function.update_self, heq, add_assoc] using hh
  simpa using hs Finset.univ 0 (by simpa using h)

lemma partition_point_mem {a b : ℝ} (p : D11.Ch12.IntervalPartition a b)
    {i : ℕ} (hi : i ≤ p.length) : p.point i ∈ Icc a b := by
  constructor
  · simpa [p.start] using p.strictMono.monotoneOn (by simp) (by simpa using hi) (Nat.zero_le i)
  · simpa [p.finish] using p.strictMono.monotoneOn (by simpa using hi) (by simp) hi

lemma partition_exists {u v : ℝ} (huv : u < v) :
    Nonempty (D11.Ch12.IntervalPartition u v) := by
  refine ⟨⟨1, (fun i => if i = 0 then u else v), ?_, by simp, by simp⟩⟩
  intro i hi j hj hij
  simp only [mem_Iic] at hi hj
  have hi0 : i = 0 := by omega
  have hj1 : j = 1 := by omega
  simpa [hi0, hj1] using huv

/-- Refining finitely many disjoint intervals simultaneously preserves the
length sum and disjointness, so one AC modulus controls their total variations. -/
lemma sum_variation_le {F : ℝ → 𝕂} {s : Set ℝ} {ε δ : ℝ}
    (h : ∀ (n : ℕ) (u v : Fin n → ℝ), (∀ j, u j < v j) →
      (∀ j, u j ∈ s ∧ v j ∈ s) →
      (Pairwise fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j))) →
      (∑ j, (v j - u j)) < δ → (∑ j, ‖F (v j) - F (u j)‖) < ε)
    (hs : OrdConnected s) {n : ℕ} (u v : Fin n → ℝ)
    (huv : ∀ i, u i < v i) (hmem : ∀ i, u i ∈ s ∧ v i ∈ s)
    (hdis : Pairwise fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j)))
    (hlen : (∑ i, (v i - u i)) < δ) :
    (∑ i, D11.Ch12.variation F (u i) (v i)) ≤ ENNReal.ofReal ε := by
  classical
  let (i : Fin n) : Nonempty (D11.Ch12.IntervalPartition (u i) (v i)) := partition_exists (huv i)
  apply sum_iSup_le (fun i p => D11.Ch12.partitionSum F p)
  intro p
  let U : (Σ i : Fin n, Fin (p i).length) → ℝ := fun j => (p j.1).point j.2
  let V : (Σ i : Fin n, Fin (p i).length) → ℝ := fun j => (p j.1).point (j.2 + 1)
  have hmono (i : Fin n) {j k : ℕ} (hj : j ≤ (p i).length)
      (hk : k ≤ (p i).length) (hjk : j ≤ k) : (p i).point j ≤ (p i).point k :=
    (p i).strictMono.monotoneOn hj hk hjk
  have hUV (j : Σ i : Fin n, Fin (p i).length) : U j < V j :=
    (p j.1).strictMono (by simp) (by simp) (Nat.lt_succ_self _)
  have hUVmem (j : Σ i : Fin n, Fin (p i).length) : U j ∈ s ∧ V j ∈ s := by
    constructor
    · exact hs.out (hmem j.1).1 (hmem j.1).2 (partition_point_mem (p j.1) (by omega))
    · exact hs.out (hmem j.1).1 (hmem j.1).2 (partition_point_mem (p j.1) (by omega))
  have hUVsub (j : Σ i : Fin n, Fin (p i).length) : Ioo (U j) (V j) ⊆ Ioo (u j.1) (v j.1) := by
    intro x hx
    exact ⟨lt_of_le_of_lt (partition_point_mem (p j.1) (by omega)).1 hx.1,
      lt_of_lt_of_le hx.2 (partition_point_mem (p j.1) (by omega)).2⟩
  have hUVdis : Pairwise fun i j => Disjoint (Ioo (U i) (V i)) (Ioo (U j) (V j)) := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hij
    by_cases h : i = j
    · subst j
      have hkl : k ≠ l := by intro he; subst l; exact hij rfl
      dsimp only [U, V]
      rcases lt_or_gt_of_ne hkl with hkl | hkl
      · apply Ioo_disjoint_Ioo.mpr
        exact (min_le_left _ _).trans ((hmono i (by omega) (by omega) (by omega)).trans (le_max_right _ _))
      · apply Ioo_disjoint_Ioo.mpr
        exact (min_le_right _ _).trans ((hmono i (by omega) (by omega) (by omega)).trans (le_max_left _ _))
    · exact (hdis h).mono (hUVsub _) (hUVsub _)
  have hUVlen : (∑ j, (V j - U j)) = ∑ i, (v i - u i) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [U, V]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (p i).point (k + 1) - (p i).point k),
      Finset.sum_range_sub]
    rw [(p i).finish, (p i).start]
  have hbound := finite_family h U V hUV hUVmem hUVdis (by rwa [hUVlen])
  have heq : (∑ i, D11.Ch12.partitionSum F (p i)) =
      ENNReal.ofReal (∑ j, ‖F (V j) - F (U j)‖) := by
    rw [Fintype.sum_sigma, ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [U, V]
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => ‖F ((p i).point (k + 1)) - F ((p i).point k)‖),
      ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
    simp only [D11.Ch12.partitionSum, ofReal_norm]
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hbound.le

/-- Classical variation functions of AC functions are AC. The proof refines
all tested intervals at once, without a differentiation or FTC argument. -/
theorem variation_ac {F : ℝ → 𝕂} {a b : ℝ} (hab : a ≤ b)
    (hF : D11.Ch12.AbsolutelyContinuousOnInterval F a b) :
    D11.Ch12.AbsolutelyContinuousOnInterval
      (fun x => (D11.Ch12.variationFunction F a x).toReal) a b := by
  have hBV := bv hab hF
  have hfinite {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
      D11.Ch12.variation F u v ≠ ⊤ := by
    apply ne_top_of_le_ne_top hBV.ne
    rw [D11.Ch12.variation_eq_eVariationOn, D11.Ch12.variation_eq_eVariationOn]
    exact eVariationOn.mono _ (Icc_subset_Icc hu.1 hv.2)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hF (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro n u v huv hmem hdis hlen
  have hvar := sum_variation_le hd (inferInstance : OrdConnected (Icc a b))
    u v huv hmem hdis hlen
  have hincr (i : Fin n) :
      ‖(D11.Ch12.variationFunction F a (v i)).toReal -
        (D11.Ch12.variationFunction F a (u i)).toReal‖ =
        (D11.Ch12.variation F (u i) (v i)).toReal := by
    dsimp only [D11.Ch12.variationFunction]
    rw [D11.Ch12.variation_additive F (hmem i).1.1 (huv i).le,
      ENNReal.toReal_add (hfinite ha (hmem i).1) (hfinite (hmem i).1 (hmem i).2),
      add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hincr]
  rw [← ENNReal.toReal_sum (fun i _ => hfinite (hmem i).1 (hmem i).2)]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh.trans_lt (half_lt_self hε)

end D11.Ch12.AcBasic
