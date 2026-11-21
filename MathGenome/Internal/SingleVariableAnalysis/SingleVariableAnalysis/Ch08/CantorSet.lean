import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.CantorSet
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.ZeroCovers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.StandardLimits
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
K03.08.cantor_set. Mathlib supplies the canonical recursive pre-Cantor sets,
closedness, compactness, and both directions of the 0–2 ternary representation.
The finite component calculation below proves that the recursive self-similar
stages implement deletion of each component's open middle third. Perfection uses
surviving endpoints, and length zero uses countable open interval covers directly,
with positive summable padding. No measure-zero/Riemann bridge is assumed.
-/
namespace SingleVariableAnalysis
open Set
open scoped BigOperators Topology ENNReal

noncomputable def cantorStage : ℕ → Set ℝ := preCantorSet
noncomputable def middleThirdsSet : Set ℝ := ⋂ n, cantorStage n
noncomputable def cantorLeft := Specs.SingleVariableAnalysis.Ch08.CantorSet.left
noncomputable def cantorRight := Specs.SingleVariableAnalysis.Ch08.CantorSet.right

@[simp] theorem cantorLeft_zero (w : Fin 0 → Bool) : cantorLeft 0 w = 0 := rfl
@[simp] theorem cantorLeft_cons (n : ℕ) (b : Bool) (w : Fin n → Bool) :
    cantorLeft (n+1) (Fin.cons b w) = ((if b then 2 else 0) + cantorLeft n w)/3 := by
  simp [cantorLeft, Specs.SingleVariableAnalysis.Ch08.CantorSet.left]

theorem cantorRight_cons (n : ℕ) (b : Bool) (w : Fin n → Bool) :
    cantorRight (n+1) (Fin.cons b w) = ((if b then 2 else 0) + cantorRight n w)/3 := by
  change cantorLeft (n+1) (Fin.cons b w) + (1/3 : ℝ)^(n+1) =
    ((if b then 2 else 0) + (cantorLeft n w + (1/3 : ℝ)^n))/3
  rw [cantorLeft_cons, pow_succ]
  ring

theorem cantor_component_bounds (n : ℕ) (w : Fin n → Bool) :
    0 ≤ cantorLeft n w ∧ cantorRight n w ≤ 1 ∧ cantorLeft n w < cantorRight n w := by
  induction n with
  | zero => norm_num [cantorLeft, cantorRight, Specs.SingleVariableAnalysis.Ch08.CantorSet.left,
      Specs.SingleVariableAnalysis.Ch08.CantorSet.right]
  | succ n ih =>
    obtain ⟨b, v, rfl⟩ := Fin.exists_cons w
    obtain ⟨hl, hr, hlt⟩ := ih v
    rw [cantorLeft_cons, cantorRight_cons]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem cantor_initial_stage : cantorStage 0 = Icc 0 1 := rfl

theorem cantor_intersection : middleThirdsSet = ⋂ n, cantorStage n := rfl

theorem cantor_stage_union (n : ℕ) :
    cantorStage n = ⋃ w : Fin n → Bool, Icc (cantorLeft n w) (cantorRight n w) := by
  induction n with
  | zero => ext x; simp [cantorStage, cantorLeft, cantorRight,
      Specs.SingleVariableAnalysis.Ch08.CantorSet.left,
      Specs.SingleVariableAnalysis.Ch08.CantorSet.right]
  | succ n ih =>
    ext x
    change x ∈ (fun y : ℝ => y/3) '' cantorStage n ∪
      (fun y : ℝ => (2+y)/3) '' cantorStage n ↔ _
    rw [ih]
    simp only [mem_union, mem_image, mem_iUnion, mem_Icc]
    constructor
    · rintro (⟨y, ⟨w, hy⟩, rfl⟩ | ⟨y, ⟨w, hy⟩, rfl⟩)
      · refine ⟨Fin.cons false w, ?_⟩
        rw [cantorLeft_cons, cantorRight_cons]
        simp only [Bool.false_eq_true, ↓reduceIte]
        constructor <;> linarith [hy.1, hy.2]
      · refine ⟨Fin.cons true w, ?_⟩
        rw [cantorLeft_cons, cantorRight_cons]
        simp only [↓reduceIte]
        constructor <;> linarith [hy.1, hy.2]
    · rintro ⟨w, hx⟩
      obtain ⟨b, w, rfl⟩ := Fin.exists_cons w
      rw [cantorLeft_cons, cantorRight_cons] at hx
      cases b
      · left
        refine ⟨3*x, ⟨w, ?_⟩, by ring⟩
        simp only [Bool.false_eq_true, ↓reduceIte] at hx
        constructor <;> linarith [hx.1, hx.2]
      · right
        refine ⟨3*x-2, ⟨w, ?_⟩, by ring⟩
        simp only [↓reduceIte] at hx
        constructor <;> linarith [hx.1, hx.2]

theorem cantor_components_disjoint (n : ℕ) :
    Pairwise (fun v w : Fin n → Bool => Disjoint
      (Icc (cantorLeft n v) (cantorRight n v))
      (Icc (cantorLeft n w) (cantorRight n w))) := by
  induction n with
  | zero => intro v w h; exact (h (Subsingleton.elim _ _)).elim
  | succ n ih =>
    intro v w hvw
    obtain ⟨a, v, rfl⟩ := Fin.exists_cons v
    obtain ⟨b, w, rfl⟩ := Fin.exists_cons w
    apply Set.disjoint_left.mpr
    intro x hx hy
    rw [mem_Icc, cantorLeft_cons, cantorRight_cons] at hx hy
    have hv := cantor_component_bounds n v
    have hw := cantor_component_bounds n w
    cases a <;> cases b
    · have hne : v ≠ w := fun h => hvw (by rw [h])
      simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
      have hvx : 3*x ∈ Icc (cantorLeft n v) (cantorRight n v) :=
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact Set.disjoint_left.mp (ih hne) hvx
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
      linarith [hx.2, hy.1, hv.2.1, hw.1]
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
      linarith [hy.2, hx.1, hw.2.1, hv.1]
    · have hne : v ≠ w := fun h => hvw (by rw [h])
      simp only [↓reduceIte] at hx hy
      have hvx : 3*x-2 ∈ Icc (cantorLeft n v) (cantorRight n v) :=
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
      exact Set.disjoint_left.mp (ih hne) hvx
        ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem cantor_stage_components (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2^n ∧
    cantorStage n = ⋃ w : Fin n → Bool, Icc (cantorLeft n w) (cantorRight n w) ∧
    (∀ w, cantorRight n w - cantorLeft n w = (1/3 : ℝ)^n) ∧
    (∀ w, cantorLeft n w < cantorRight n w) ∧
    Pairwise (fun v w : Fin n → Bool => Disjoint
      (Icc (cantorLeft n v) (cantorRight n v))
      (Icc (cantorLeft n w) (cantorRight n w))) := by
  refine ⟨by simp, cantor_stage_union n, ?_,
    fun w => (cantor_component_bounds n w).2.2, cantor_components_disjoint n⟩
  intro w
  change cantorLeft n w + (1/3 : ℝ)^n - cantorLeft n w = _
  ring

theorem cantor_stage_total_length (n : ℕ) :
    (∑ w : Fin n → Bool, (cantorRight n w - cantorLeft n w)) = (2/3 : ℝ)^n := by
  simp_rw [(cantor_stage_components n).2.2.1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
    ← mul_pow]
  congr 1
  ring

theorem cantor_nested : Antitone cantorStage := preCantorSet_antitone

theorem one_mem_middleThirdsSet : (1 : ℝ) ∈ middleThirdsSet := by
  -- The all-two expansion represents one, including the endpoint.
  have h : Real.ofDigits (fun _ : ℕ => (2 : Fin 3)) = 1 := by
    simpa using Real.ofDigits_const_last_eq_one 2
  rw [← h]
  exact ofDigits_zero_two_sequence_mem_cantorSet (fun _ => by decide)

theorem cantor_nonempty_compact : middleThirdsSet.Nonempty ∧ IsCompact middleThirdsSet ∧
    (0 : ℝ) ∈ middleThirdsSet ∧ (1 : ℝ) ∈ middleThirdsSet :=
  ⟨⟨0, zero_mem_cantorSet⟩, isCompact_cantorSet, zero_mem_cantorSet,
    one_mem_middleThirdsSet⟩

theorem cantor_endpoints_remain (n : ℕ) (w : Fin n → Bool) :
    cantorLeft n w ∈ middleThirdsSet ∧ cantorRight n w ∈ middleThirdsSet := by
  induction n with
  | zero => change (0 : ℝ) ∈ middleThirdsSet ∧ (0 + (1/3 : ℝ)^0) ∈ middleThirdsSet
            simpa using And.intro (show (0 : ℝ) ∈ middleThirdsSet from zero_mem_cantorSet)
              one_mem_middleThirdsSet
  | succ n ih =>
    obtain ⟨b, w, rfl⟩ := Fin.exists_cons w
    obtain ⟨hl, hr⟩ := ih w
    rw [cantorLeft_cons, cantorRight_cons]
    change _ ∈ cantorSet ∧ _ ∈ cantorSet
    rw [cantorSet_eq_union_halves]
    cases b
    · exact ⟨Or.inl ⟨_, hl, by simp⟩, Or.inl ⟨_, hr, by simp⟩⟩
    · exact ⟨Or.inr ⟨_, hl, by simp⟩, Or.inr ⟨_, hr, by simp⟩⟩

theorem cantor_ternary_membership (x : ℝ) : x ∈ middleThirdsSet ↔
    ∃ a : ℕ → Fin 3, (∀ i, a i = 0 ∨ a i = 2) ∧ Real.ofDigits a = x := by
  change x ∈ cantorSet ↔ _
  rw [cantorSet_eq_zero_two_ofDigits]
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, fun i => ?_, hax⟩
    have hi := ha i
    generalize a i = d at *
    fin_cases d <;> simp_all
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, fun i => by rcases ha i with h | h <;> simp [h], hax⟩

theorem cantor_perfect : Perfect middleThirdsSet := by
  refine ⟨isClosed_cantorSet, preperfect_iff_nhds.mpr ?_⟩
  intro x hx U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨N, hN⟩ := real_geometric_decay (1/3 : ℝ) (by norm_num) ε hε
  let n := N+1
  have hn : (1/3 : ℝ)^n < ε := by
    have := hN N le_rfl
    simpa [n, abs_of_nonneg (show (0 : ℝ) ≤ (1/3 : ℝ)^(N+1) by positivity)] using this
  have hstage : x ∈ cantorStage n := mem_iInter.mp hx n
  rw [cantor_stage_union] at hstage
  obtain ⟨w, hw⟩ := mem_iUnion.mp hstage
  obtain ⟨hl, hr⟩ := cantor_endpoints_remain n w
  have hlen := (cantor_stage_components n).2.2.1 w
  by_cases hxl : cantorLeft n w = x
  · refine ⟨cantorRight n w, ⟨hball ?_, hr⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hw.2])]
      linarith
    · have := (cantor_component_bounds n w).2.2
      linarith
  · refine ⟨cantorLeft n w, ⟨hball ?_, hl⟩, hxl⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hw.1])]
    linarith [hw.2]

theorem cantor_endpoint_expansion :
    Real.ofDigits (fun n => if n = 0 then (0 : Fin 3) else 2) = (1/3 : ℝ) ∧
    (1/3 : ℝ) ∈ middleThirdsSet := by
  have heq : Real.ofDigits (fun n => if n = 0 then (0 : Fin 3) else 2) = (1/3 : ℝ) := by
    rw [Real.ofDigits_eq_sum_add_ofDigits _ 1]
    simp only [Finset.range_one, Finset.sum_singleton, Real.ofDigitsTerm,
      Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat, pow_one,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_add]
    have h : Real.ofDigits (fun _ : ℕ => (2 : Fin 3)) = 1 := by
      simpa using Real.ofDigits_const_last_eq_one 2
    rw [h]
    norm_num
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact ofDigits_zero_two_sequence_mem_cantorSet (fun n => by split_ifs <;> decide)

/-- Countable open covers obtained by enlarging a finite equal-length interval cover.
The extra intervals have summable positive lengths, so no empty filler interval is used. -/
theorem lengthZero_of_finite_uniform_covers (E : Set ℝ)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ (M : ℕ) (l : Fin M → ℝ) (r : ℝ),
      0 ≤ r ∧ E ⊆ ⋃ i, Icc (l i) (l i + r) ∧ (M : ℝ)*r < ε) : LengthZero E := by
  classical
  intro ε hε
  obtain ⟨M, l, r, hr, hE, hMr⟩ := hcover (ε/2) (by positivity)
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr (show 0 < ε/2 by positivity)).ne' ℕ
  let L : ℕ → ℝ := fun k => if h : k < M then l ⟨k,h⟩ else 0
  let R : ℕ → ℝ := fun k => if h : k < M then l ⟨k,h⟩ + r else 0
  let g : ℕ → ℝ := fun k => if k < M then r else 0
  have hg (k : ℕ) : 0 ≤ g k := by dsimp [g]; split_ifs <;> positivity
  have hdiff (k : ℕ) : R k - L k = g k := by
    dsimp [R,L,g]
    split_ifs <;> ring
  refine ⟨fun k => L k - (δ k : ℝ)/2, fun k => R k + (δ k : ℝ)/2, ?_, ?_, ?_⟩
  · intro k
    have hd := NNReal.coe_pos.mpr (hδ k)
    have := hg k
    linarith [hdiff k]
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hE hx)
    apply mem_iUnion.mpr
    refine ⟨i.val, ?_⟩
    have hd := NNReal.coe_pos.mpr (hδ i.val)
    simp only [L, R, dite_eq_left i.isLt]
    constructor <;> linarith [hi.1, hi.2]
  · have hlen (k : ℕ) : (R k + (δ k : ℝ)/2) - (L k - (δ k : ℝ)/2) =
        g k + (δ k : ℝ) := by linarith [hdiff k]
    change (∑' k, ENNReal.ofReal ((R k + (δ k : ℝ)/2) - (L k - (δ k : ℝ)/2))) < _
    simp_rw [hlen, ENNReal.ofReal_add (hg _) (δ _).coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.tsum_add]
    have hfinite : (∑' k, ENNReal.ofReal (g k)) = ENNReal.ofReal ((M : ℝ)*r) := by
      rw [tsum_eq_sum (s := Finset.range M) (fun k hk => by
        simp only [Finset.mem_range] at hk
        simp [g, hk])]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hg k)]
      congr 1
      calc
        (∑ k ∈ Finset.range M, g k) = ∑ _k ∈ Finset.range M, r := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [g, Finset.mem_range.mp hk]
        _ = (M : ℝ)*r := by simp
    rw [hfinite]
    calc
      ENNReal.ofReal ((M : ℝ)*r) + ∑' k, (δ k : ℝ≥0∞)
          ≤ ENNReal.ofReal (ε/2) + ∑' k, (δ k : ℝ≥0∞) :=
        add_le_add (ENNReal.ofReal_le_ofReal hMr.le) le_rfl
      _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) :=
        ENNReal.add_lt_add_left (by simp) hsum
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem cantor_lengthZero : LengthZero middleThirdsSet := by
  apply lengthZero_of_finite_uniform_covers
  intro ε hε
  obtain ⟨N, hN⟩ := real_geometric_decay (2/3 : ℝ) (by norm_num) ε hε
  let n := N+1
  let e := (Fintype.equivFin (Fin n → Bool)).symm
  refine ⟨Fintype.card (Fin n → Bool), fun i => cantorLeft n (e i), (1/3 : ℝ)^n,
    by positivity, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ cantorStage n := mem_iInter.mp hx n
    rw [cantor_stage_union] at hx'
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx'
    refine mem_iUnion.mpr ⟨e.symm w, ?_⟩
    change cantorLeft n w ≤ x ∧ x ≤ cantorLeft n w + (1/3 : ℝ)^n at hw
    simpa only [Equiv.apply_symm_apply, mem_Icc] using hw
  · have hpow : ((Fintype.card (Fin n → Bool) : ℕ) : ℝ)*(1/3 : ℝ)^n = (2/3 : ℝ)^n := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
        Nat.cast_ofNat, ← mul_pow]
      congr 1
      ring
    rw [hpow]
    have := hN N le_rfl
    simpa [n, abs_of_nonneg (show (0 : ℝ) ≤ (2/3 : ℝ)^(N+1) by positivity)] using this

theorem cantor_empty_interior : interior middleThirdsSet = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  apply not_lengthZero_of_contains_Icc middleThirdsSet (x-ε/2) (x+ε/2)
    (by linarith) ?_ cantor_lengthZero
  intro y hy
  apply interior_subset (hball ?_)
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

private def survivingThirds (a b : ℝ) : Set ℝ :=
  Icc a b \ Ioo (a+(b-a)/3) (b-(b-a)/3)

private theorem survivingThirds_affine (a b d x : ℝ) :
    x ∈ survivingThirds ((d+a)/3) ((d+b)/3) ↔ 3*x-d ∈ survivingThirds a b := by
  simp only [survivingThirds, mem_sdiff, mem_Icc, mem_Ioo, not_and_or, not_lt]
  constructor
  all_goals
    rintro ⟨⟨h1,h2⟩,h3⟩
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rcases h3 with h3 | h3
    · left; linarith
    · right; linarith

private theorem survivingThirds_unit :
    preCantorSet 1 = survivingThirds 0 1 := by
  ext x
  simp only [preCantorSet_succ, preCantorSet_zero, mem_union, mem_image,
    mem_Icc, survivingThirds, mem_sdiff, mem_Ioo, not_and_or, not_lt]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, Or.inl (by linarith [hy.2])⟩
    · exact ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, Or.inr (by linarith [hy.1])⟩
  · rintro ⟨hx, h | h⟩
    · exact Or.inl ⟨3*x, ⟨by linarith [hx.1], by linarith⟩, by ring⟩
    · exact Or.inr ⟨3*x-2, ⟨by linarith, by linarith [hx.2]⟩, by ring⟩

theorem cantor_delete_middle_thirds (n : ℕ) :
    cantorStage (n+1) = ⋃ w : Fin n → Bool,
      (Icc (cantorLeft n w) (cantorRight n w) \ 
        Ioo (cantorLeft n w + (cantorRight n w - cantorLeft n w)/3)
          (cantorRight n w - (cantorRight n w - cantorLeft n w)/3)) := by
  change cantorStage (n+1) = ⋃ w : Fin n → Bool,
    survivingThirds (cantorLeft n w) (cantorRight n w)
  induction n with
  | zero =>
    have h : (⋃ w : Fin 0 → Bool, survivingThirds (cantorLeft 0 w) (cantorRight 0 w)) =
        survivingThirds 0 1 := by
      simp only [cantorLeft_zero, cantorRight,
        Specs.SingleVariableAnalysis.Ch08.CantorSet.right,
        Specs.SingleVariableAnalysis.Ch08.CantorSet.left, pow_zero, zero_add, iUnion_const]
    rw [h]
    exact survivingThirds_unit
  | succ n ih =>
    ext x
    change x ∈ (fun y : ℝ => y/3) '' cantorStage (n+1) ∪
      (fun y : ℝ => (2+y)/3) '' cantorStage (n+1) ↔ _
    rw [ih]
    simp only [mem_union, mem_image, mem_iUnion]
    constructor
    · rintro (⟨y, ⟨w, hy⟩, rfl⟩ | ⟨y, ⟨w, hy⟩, rfl⟩)
      · refine ⟨Fin.cons false w, ?_⟩
        rw [cantorLeft_cons, cantorRight_cons]
        simp only [Bool.false_eq_true, ↓reduceIte]
        apply (survivingThirds_affine _ _ 0 _).mpr
        convert hy using 1 <;> ring
      · refine ⟨Fin.cons true w, ?_⟩
        rw [cantorLeft_cons, cantorRight_cons]
        simp only [↓reduceIte]
        apply (survivingThirds_affine _ _ 2 _).mpr
        convert hy using 1 <;> ring
    · rintro ⟨w, hx⟩
      obtain ⟨b, w, rfl⟩ := Fin.exists_cons w
      rw [cantorLeft_cons, cantorRight_cons] at hx
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at hx
        left
        refine ⟨3*x, ⟨w, ?_⟩, by ring⟩
        simpa using (survivingThirds_affine _ _ 0 x).mp hx
      · simp only [↓reduceIte] at hx
        right
        exact ⟨3*x-2, ⟨w, (survivingThirds_affine _ _ 2 x).mp hx⟩, by ring⟩

end SingleVariableAnalysis
