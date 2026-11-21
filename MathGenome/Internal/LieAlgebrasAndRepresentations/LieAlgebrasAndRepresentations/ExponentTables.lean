import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExponentTables
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalCoordinateE
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open scoped Classical
open Finset Polynomial

namespace LieAlgebrasAndRepresentations.ExponentTables
open ClassicalCoordinates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem coeff_sum_powers {α : Type*} (s : Finset α) (d : α → ℕ) (k : ℕ) :
    (∑ a ∈ s, (X : ℕ[X]) ^ d a).coeff k = (s.filter fun a => d a = k).card := by
  rw [finsetSum_coeff]
  simp only [coeff_X_pow, ← sum_filter, sum_const, smul_eq_mul, mul_one, eq_comm]

private theorem coeff_height {R : Set V} {v : V} {f : V → ℝ}
    (hf : ∀ a ∈ positiveRoots R v, ∃ k : ℕ, 0 < k ∧ f a = (k : ℝ))
    (hfin : (positiveRoots R v).Finite) (k : ℕ) :
    (heightPolynomial R v f hfin).coeff k = (heightSlice R v f k).ncard := by
  rw [heightPolynomial, coeff_sum_powers]
  have he : (↑(hfin.toFinset.filter (fun a => ⌊f a⌋₊ = k)) : Set V) = heightSlice R v f k := by
    ext a
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, heightSlice]
    refine and_congr_right fun ha => ?_
    obtain ⟨j, _, hj⟩ := hf a ha
    rw [hj, Nat.floor_natCast, Nat.cast_inj]
  rw [← he, Set.ncard_coe_finset]

private theorem coeff_strip (m k : ℕ) :
    (heightStrip m).coeff k = if 0 < k ∧ k ≤ m then 1 else 0 := by
  rw [heightStrip, coeff_sum_powers]
  by_cases h : 0 < k ∧ k ≤ m
  · rw [ite_eq_left h]
    suffices (range m).filter (fun a => a + 1 = k) = {k - 1} by rw [this, card_singleton]
    ext a
    simp only [mem_filter, mem_range, mem_singleton]
    omega
  · rw [ite_eq_right h, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro a
    simp only [mem_filter, mem_range]
    omega

private theorem coeff_exponents (ms : List ℕ) (k : ℕ) :
    (exponentPolynomial ms).coeff k = ms.countP (fun m => decide (0 < k ∧ k ≤ m)) := by
  induction ms with
  | nil => simp [exponentPolynomial]
  | cons m ms ih =>
    simp only [exponentPolynomial, List.map_cons, List.sum_cons, coeff_add] at ih ⊢
    rw [ih, coeff_strip, List.countP_cons, add_comm]
    split <;> simp_all

private theorem coeff_exponents_step (ms : List ℕ) (m : ℕ) (hm : 0 < m) :
    (exponentPolynomial ms).coeff m =
      (exponentPolynomial ms).coeff (m+1) + ms.count m := by
  induction ms with
  | nil => simp [exponentPolynomial]
  | cons a ms ih =>
    simp only [exponentPolynomial, List.map_cons, List.sum_cons, coeff_add] at ih ⊢
    rw [ih, coeff_strip, coeff_strip, List.count_cons]
    by_cases h₁ : m ≤ a <;> by_cases h₂ : m+1 ≤ a <;>
      have hm' : 0 < m+1 := by omega
    · have hne : a ≠ m := by omega
      simp [hm, hm', h₁, h₂, hne]
      omega
    · have he : a = m := by omega
      simp [hm, hm', he]
      omega
    · omega
    · have hne : a ≠ m := by omega
      simp [hm, hm', h₁, h₂, hne]

private theorem row_of_poly {ι : Type*} [Fintype ι] {R : Set V} {simple : ι → V}
    {v : V} {b : Module.Basis ι ℝ V} (hr : RootRegular R v) (hb : IsSimpleBasis R v b)
    (hs : ∀ i, b i = simple i) (f : V →ₗ[ℝ] ℝ) (h1 : ∀ i, f (simple i) = 1)
    (hfin : (positiveRoots R v).Finite)
    (hi : ∀ a ∈ positiveRoots R v, ∃ k : ℕ, 0 < k ∧ f a = (k : ℝ))
    {ms : List ℕ} {k : ℕ} (hk : 0 < k) (hkm : k ∈ ms) (hmax : ∀ m ∈ ms, m ≤ k)
    (hp : heightPolynomial R v f hfin = exponentPolynomial ms) :
    TableRow R simple ms (k+1) := by
  have hcount (m : ℕ) :
      (heightSlice R v f m).ncard = ms.countP (fun j => decide (0 < m ∧ m ≤ j)) := by
    rw [← coeff_height hi hfin, hp, coeff_exponents]
  refine ⟨v, b, f, hfin, hr, hb, hs, h1, hi, hp, ?_, k, rfl, ?_⟩
  · intro m hm
    rw [← coeff_height hi hfin, ← coeff_height hi hfin, hp, coeff_exponents_step ms m hm,
      Nat.add_sub_cancel_left]
  · have hsFinite : ∀ j, (heightSlice R v f j).Finite := fun j =>
      hfin.subset (fun _ h => h.1)
    have hx : 0 < (heightSlice R v f k).ncard := by
      rw [hcount, List.countP_pos_iff]
      exact ⟨k, hkm, by simp [hk]⟩
    obtain ⟨a, ha⟩ := (Set.ncard_pos (hsFinite k)).mp hx
    refine ⟨⟨a, ha.1, ha.2⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨j, hj, hja⟩ := hi a ha
    have hx : 0 < (heightSlice R v f j).ncard :=
      (Set.ncard_pos (hsFinite j)).mpr ⟨a, ha, hja⟩
    rw [hcount, List.countP_pos_iff] at hx
    obtain ⟨m, hm, hmj⟩ := hx
    simp only [decide_eq_true_eq] at hmj
    rw [hja]
    exact_mod_cast hmj.2.trans (hmax m hm)


omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
private theorem enumerate {α : Type*} (s : Finset α) {P : Set V} (hP : P.Finite)
    (f : V → ℝ) (g : ∀ a ∈ s, V) (d : α → ℕ)
    (hg : ∀ a ha, g a ha ∈ P)
    (hinj : ∀ a ha b hb, g a ha = g b hb → a = b)
    (hsurj : ∀ x ∈ P, ∃ a ha, g a ha = x)
    (hd : ∀ a ha, f (g a ha) = (d a : ℝ))
    (hpos : ∀ a ∈ s, 0 < d a) :
    (∀ x ∈ P, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
    (∑ x ∈ hP.toFinset, (X : ℕ[X]) ^ ⌊f x⌋₊) = ∑ a ∈ s, X ^ d a := by
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hsurj x hx
    exact ⟨d a, hpos a ha, hd a ha⟩
  · symm
    apply Finset.sum_bij g
    · simpa only [Set.Finite.mem_toFinset] using hg
    · exact hinj
    · simpa only [Set.Finite.mem_toFinset] using hsurj
    · intro a ha
      rw [hd a ha, Nat.floor_natCast]

private def triangle (n : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (range n).sigma range

private theorem mem_triangle {n : ℕ} {p : Sigma fun _ : ℕ => ℕ} :
    p ∈ triangle n ↔ p.1 < n ∧ p.2 < p.1 := by
  simp [triangle]

private theorem sum_triangle {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → ℕ → M) :
    (∑ p ∈ triangle n, f p.1 p.2) = ∑ j ∈ range n, ∑ i ∈ range j, f j i :=
  Finset.sum_sigma _ _ _

private theorem sum_gap (j : ℕ) :
    (∑ i ∈ range j, (X : ℕ[X]) ^ (j-i)) = heightStrip j := by
  rw [heightStrip]
  apply Finset.sum_bij (fun i _ => j-1-i)
  · intro i hi
    simp only [mem_range] at hi ⊢
    omega
  · intro i hi l hl he
    simp only [mem_range] at hi hl
    omega
  · intro k hk
    simp only [mem_range] at hk
    exact ⟨j-1-k, mem_range.mpr (by omega), by omega⟩
  · intro i hi
    simp only [mem_range] at hi
    congr 1
    omega

private theorem exponentPolynomial_append (l m : List ℕ) :
    exponentPolynomial (l ++ m) = exponentPolynomial l + exponentPolynomial m := by
  simp [exponentPolynomial]

private theorem exponentPolynomial_range_succ (f : ℕ → ℕ) (n : ℕ) :
    exponentPolynomial ((List.range (n+1)).map f) =
    exponentPolynomial ((List.range n).map f) + heightStrip (f n) := by
  rw [List.range_succ, List.map_append, exponentPolynomial_append]
  simp [exponentPolynomial]

private theorem typeA_polynomial (n : ℕ) (f : zeroSum n →ₗ[ℝ] ℝ)
    (hf : ∀ i j, f (difference n (i,j)) = (j.val : ℝ) - i.val)
    (hfin : (positiveRoots (rootsA n) (regularA n)).Finite) :
    (∀ x ∈ positiveRoots (rootsA n) (regularA n), ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
    heightPolynomial (rootsA n) (regularA n) f hfin =
      exponentPolynomial ((List.range n).map (· + 1)) := by
  let pair (p : Sigma fun _ : ℕ => ℕ) (hp : p ∈ triangle (n+1)) :
      Fin (n+1) × Fin (n+1) :=
    (⟨p.2, (mem_triangle.mp hp).2.trans (mem_triangle.mp hp).1⟩, ⟨p.1, (mem_triangle.mp hp).1⟩)
  have hlt (p : Sigma fun _ : ℕ => ℕ) (hp : p ∈ triangle (n+1)) :
      (pair p hp).1 < (pair p hp).2 := (mem_triangle.mp hp).2
  obtain ⟨hi, hsum⟩ := enumerate (triangle (n+1)) hfin f
    (fun p hp => difference n (pair p hp)) (fun p => p.1-p.2)
    (fun p hp => (positiveRootsA_iff _).mpr ⟨_, _, hlt p hp, rfl⟩)
    (by
      intro a ha b hb h
      have h' := difference_injOn n (ne_of_lt (hlt a ha)) (ne_of_lt (hlt b hb)) h
      cases a; cases b
      simp only [Prod.mk.injEq, pair] at h'
      exact Sigma.ext (congrArg Fin.val h'.2) (heq_of_eq (congrArg Fin.val h'.1)))
    (by
      intro x hx
      obtain ⟨i, j, hij, rfl⟩ := (positiveRootsA_iff x).mp hx
      exact ⟨⟨j.val,i.val⟩, mem_triangle.mpr ⟨j.isLt,hij⟩, rfl⟩)
    (by
      intro p hp
      rw [hf]
      exact (Nat.cast_sub (mem_triangle.mp hp).2.le).symm)
    (fun p hp => Nat.sub_pos_of_lt (mem_triangle.mp hp).2)
  refine ⟨hi, ?_⟩
  rw [heightPolynomial, hsum, sum_triangle _ (fun j i => (X : ℕ[X]) ^ (j-i))]
  simp_rw [sum_gap]
  suffices ∀ m : ℕ, (∑ j ∈ range (m+1), heightStrip j) =
      exponentPolynomial ((List.range m).map (· + 1)) from this n
  intro m
  induction m with
  | zero => simp [heightStrip, exponentPolynomial]
  | succ m ih => rw [sum_range_succ, ih, exponentPolynomial_range_succ]

theorem typeA : Specs.typeA := by
  intro n hn
  obtain ⟨b, hb, hs⟩ := simpleA_basis n hn
  let f : zeroSum n →ₗ[ℝ] ℝ := ((n+1 : ℝ)⁻¹) • innerₗ (zeroSum n) (regularA n)
  have hf (i j : Fin (n+1)) : f (difference n (i,j)) = (j.val : ℝ) - i.val := by
    change (n+1 : ℝ)⁻¹ * inner ℝ (regularA n) (difference n (i,j)) = _
    rw [regularA_inner_difference, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have h1 (i : Fin n) : f (simpleA n i) = 1 := by
    change f (difference n (i.castSucc,i.succ)) = 1
    simp [hf, Fin.val_succ, Fin.val_castSucc]
  let hfin : (positiveRoots (rootsA n) (regularA n)).Finite :=
    (rootsA_finite n).subset fun _ h => h.1
  obtain ⟨hi, hp⟩ := typeA_polynomial n f hf hfin
  exact row_of_poly (regularA_regular n) hs hb f h1 hfin hi (by omega)
    (List.mem_map.mpr ⟨n-1, List.mem_range.mpr (by omega), by omega⟩)
    (by intro m hm; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm; simp only [List.mem_range] at hi; omega)
    hp


private def reversedIndex (n i : ℕ) (hi : i < n) : Fin n :=
  ⟨n-1-i, by omega⟩

private theorem reversedIndex_coord (n i : ℕ) (hi : i < n) (q : ℕ) :
    (n : ℝ) - (reversedIndex n i hi).val - (1 - (q : ℝ)/2) = i + (q : ℝ)/2 := by
  have he : (reversedIndex n i hi).val + i + 1 = n := by
    change n-1-i+i+1=n
    omega
  have he' := congrArg (fun k : ℕ => (k : ℝ)) he
  push_cast at he'
  linarith

private def pairSum (n q : ℕ) : ℕ[X] :=
  ∑ j ∈ range n, (heightStrip j + ∑ i ∈ range j, X ^ (j+i+q))

private theorem pair_polynomial (n q : ℕ) :
    let v := regularBCD n (1 - (q : ℝ)/2)
    let f := innerₗ (Space n) v
    ∀ hfin : (positiveRoots (pairRoots n) v).Finite,
      (∀ x ∈ positiveRoots (pairRoots n) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
      heightPolynomial (pairRoots n) v f hfin = pairSum n q := by
  intro v f hfin
  let s := triangle n ×ˢ (univ : Finset Bool)
  let J (p : (Sigma fun _ : ℕ => ℕ) × Bool) (hp : p ∈ s) :=
    reversedIndex n p.1.1 (mem_triangle.mp (mem_product.mp hp).1).1
  let I (p : (Sigma fun _ : ℕ => ℕ) × Bool) (hp : p ∈ s) :=
    reversedIndex n p.1.2
      ((mem_triangle.mp (mem_product.mp hp).1).2.trans (mem_triangle.mp (mem_product.mp hp).1).1)
  let param (p : (Sigma fun _ : ℕ => ℕ) × Bool) (hp : p ∈ s) :=
    ((J p hp, I p hp),(false,p.2))
  let d (p : (Sigma fun _ : ℕ => ℕ) × Bool) :=
    if p.2 then p.1.1-p.1.2 else p.1.1+p.1.2+q
  have hlt (p) (hp : p ∈ s) : J p hp < I p hp := by
    have h := mem_triangle.mp (mem_product.mp hp).1
    change n-1-p.1.1 < n-1-p.1.2
    omega
  have hd (p) (hp : p ∈ s) : f (pairParameter n (param p hp)) = (d p : ℝ) := by
    have h := mem_triangle.mp (mem_product.mp hp).1
    change inner ℝ v (sign false • epsilon (J p hp) + sign p.2 • epsilon (I p hp)) = _
    rw [inner_regular_pair, reversedIndex_coord, reversedIndex_coord]
    cases hp₂ : p.2
    · simp [d, hp₂, sign]
      ring
    · simp [d, hp₂, sign, Nat.cast_sub h.2.le]
      ring
  have hpos (p) (hp : p ∈ s) : 0 < d p := by
    have h := mem_triangle.mp (mem_product.mp hp).1
    unfold d
    split <;> omega
  obtain ⟨hi, hp⟩ := enumerate s hfin f (fun p hp => pairParameter n (param p hp)) d
    (by
      intro p hp
      constructor
      · exact ⟨_, _, ne_of_lt (hlt p hp), false, p.2, rfl⟩
      · change 0 < f (pairParameter n (param p hp))
        rw [hd p hp]
        exact_mod_cast hpos p hp)
    (by
      intro a ha b hb he
      have heq := pairParameter_injOn n (hlt a ha) (hlt b hb) he
      have hAJ := (mem_triangle.mp (mem_product.mp ha).1).1
      have hBJ := (mem_triangle.mp (mem_product.mp hb).1).1
      have hAI := (mem_triangle.mp (mem_product.mp ha).1).2
      have hBI := (mem_triangle.mp (mem_product.mp hb).1).2
      have eJ := congrArg (fun p : (Fin n × Fin n) × (Bool × Bool) => p.1.1.val) heq
      have eI := congrArg (fun p : (Fin n × Fin n) × (Bool × Bool) => p.1.2.val) heq
      have et := congrArg (fun p : (Fin n × Fin n) × (Bool × Bool) => p.2.2) heq
      change n-1-a.1.1 = n-1-b.1.1 at eJ
      change n-1-a.1.2 = n-1-b.1.2 at eI
      exact Prod.ext (Sigma.ext (by omega) (heq_of_eq (by omega : a.1.2 = b.1.2))) et)
    (by
      intro x hx
      have hbase := hx.1
      rw [pairRoots_image] at hbase
      obtain ⟨⟨⟨i,j⟩,⟨s₁,t⟩⟩, hij, rfl⟩ := hbase
      change i.val < j.val at hij
      have hq : (0 : ℝ) ≤ q := by positivity
      have hgap : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast hij
      have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
      have hsign : s₁ = false := by
        have h := hx.2
        change 0 < inner ℝ v (sign s₁ • epsilon i + sign t • epsilon j) at h
        rw [inner_regular_pair] at h
        cases s₁
        · rfl
        · cases t
          · norm_num [sign] at h
            exact (False.elim (not_lt_of_ge hij.le h))
          · norm_num [sign] at h
            linarith
      subst s₁
      let p : (Sigma fun _ : ℕ => ℕ) × Bool := (⟨n-1-i.val,n-1-j.val⟩,t)
      have hp : p ∈ s :=
        mem_product.mpr ⟨mem_triangle.mpr ⟨by dsimp [p]; omega, by dsimp [p]; omega⟩, mem_univ _⟩
      have hJ : J p hp = i := by apply Fin.ext; dsimp [J, p, reversedIndex]; omega
      have hI : I p hp = j := by apply Fin.ext; dsimp [I, p, reversedIndex]; omega
      exact ⟨p, hp, by simp [param, hJ, hI, p]⟩)
    hd hpos
  refine ⟨hi, ?_⟩
  rw [heightPolynomial, hp, pairSum]
  change (∑ a ∈ triangle n ×ˢ (univ : Finset Bool), (X : ℕ[X]) ^ d a) = _
  rw [Finset.sum_product]
  simp only [Fintype.sum_bool, d, Bool.false_eq_true, ↓reduceIte]
  rw [sum_triangle _ (fun j i => (X : ℕ[X]) ^ (j-i) + X ^ (j+i+q))]
  simp only [sum_add_distrib, sum_gap]

private def axisSum (n step offset : ℕ) : ℕ[X] :=
  ∑ i ∈ range n, X ^ (step*i+offset)

private theorem axis_polynomial (n step offset : ℕ) (hstep : 0 < step) (hoff : 0 < offset) :
    let v := regularBCD n (1 - (offset : ℝ)/step)
    let f := innerₗ (Space n) v
    ∀ hfin : (positiveRoots (axisRoots n step) v).Finite,
      (∀ x ∈ positiveRoots (axisRoots n step) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
      heightPolynomial (axisRoots n step) v f hfin = axisSum n step offset := by
  intro v f hfin
  let I (i : ℕ) (hi : i ∈ range n) := reversedIndex n i (mem_range.mp hi)
  have hstep' : (0 : ℝ) < step := by exact_mod_cast hstep
  have hcoord (i : ℕ) (hi : i ∈ range n) :
      (n : ℝ) - (I i hi).val - (1 - (offset : ℝ)/step) = i + (offset : ℝ)/step := by
    have he : (I i hi).val + i + 1 = n := by
      change n-1-i+i+1=n
      have := mem_range.mp hi
      omega
    have he' := congrArg (fun k : ℕ => (k : ℝ)) he
    push_cast at he'
    linarith
  have hval (i : ℕ) (hi : i ∈ range n) (t : Bool) :
      f (axisParameter n step (I i hi,t)) = sign t * ((step*i+offset : ℕ) : ℝ) := by
    change inner ℝ v (((step : ℝ) * sign t) • epsilon (I i hi)) = _
    rw [real_inner_smul_right, inner_epsilon_right]
    change ((step : ℝ) * sign t) * ((n : ℝ) - (I i hi).val - (1 - (offset : ℝ)/step)) = _
    rw [hcoord i hi]
    push_cast
    field_simp
  apply enumerate (range n) hfin f (fun i hi => axisParameter n step (I i hi,false))
    (fun i => step*i+offset)
  · intro i hi
    exact ⟨⟨_, false, rfl⟩, by
      change 0 < f (axisParameter n step (I i hi,false))
      rw [hval i hi false]
      simp only [sign, Bool.false_eq_true, ↓reduceIte, one_mul]
      exact_mod_cast (show 0 < step*i+offset by omega)⟩
  · intro i hi j hj he
    have h := axisParameter_injective n (ne_of_gt hstep') he
    have hh := congrArg (fun a : Fin n × Bool => a.1.val) h
    change n-1-i = n-1-j at hh
    have := mem_range.mp hi
    have := mem_range.mp hj
    omega
  · rintro x ⟨⟨i,t,rfl⟩,hpos⟩
    let a := n-1-i.val
    have ha : a ∈ range n := mem_range.mpr (by dsimp [a]; omega)
    have hI : I a ha = i := by apply Fin.ext; dsimp [I, a, reversedIndex]; omega
    have hv := hval a ha t
    rw [hI] at hv
    change 0 < f (axisParameter n step (i,t)) at hpos
    rw [hv] at hpos
    cases t
    · exact ⟨a, ha, by rw [hI]; rfl⟩
    · exfalso
      have hh : (0 : ℝ) ≤ ((step*a+offset : ℕ) : ℝ) := by positivity
      simp only [sign, ↓reduceIte, neg_mul, one_mul] at hpos
      linarith
  · intro i hi
    rw [hval i hi false]
    simp [sign]
  · intro i hi
    omega

private theorem heightStrip_succ (j : ℕ) :
    heightStrip (j+1) = heightStrip j + (X : ℕ[X]) ^ (j+1) :=
  sum_range_succ _ _

private theorem heightStrip_add_tail (j n : ℕ) :
    heightStrip (j+n) = heightStrip j + ∑ i ∈ range n, (X : ℕ[X]) ^ (j+i+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show j + (n+1) = (j+n)+1 by omega, heightStrip_succ, ih, sum_range_succ]
    ac_rfl

private theorem pairSum_succ (n q : ℕ) :
    pairSum (n+1) q = pairSum n q +
      (heightStrip n + ∑ i ∈ range n, X ^ (n+i+q)) :=
  sum_range_succ _ _

private theorem axisSum_succ (n a b : ℕ) :
    axisSum (n+1) a b = axisSum n a b + (X : ℕ[X]) ^ (a*n+b) :=
  sum_range_succ _ _

private theorem polynomialB (n : ℕ) :
    axisSum n 1 1 + pairSum n 2 = exponentPolynomial ((List.range n).map (fun i => 2*i+1)) := by
  induction n with
  | zero => simp [axisSum, pairSum, exponentPolynomial]
  | succ n ih =>
    rw [axisSum_succ, pairSum_succ, exponentPolynomial_range_succ, ← ih]
    have h := heightStrip_add_tail (n+1) n
    rw [show n+1+n = 2*n+1 by omega, heightStrip_succ n] at h
    rw [h]
    simp only [one_mul, show ∀ i : ℕ, n+1+i+1 = n+i+2 by omega]
    ac_rfl

private theorem polynomialC (n : ℕ) :
    axisSum n 2 1 + pairSum n 1 = exponentPolynomial ((List.range n).map (fun i => 2*i+1)) := by
  induction n with
  | zero => simp [axisSum, pairSum, exponentPolynomial]
  | succ n ih =>
    rw [axisSum_succ, pairSum_succ, exponentPolynomial_range_succ, ← ih]
    have h := heightStrip_add_tail n n
    rw [show n+n = 2*n by omega] at h
    rw [heightStrip_succ, h]
    ac_rfl

private theorem polynomialD (n : ℕ) :
    pairSum (n+1) 0 = exponentPolynomial (((List.range n).map (fun i => 2*i+1)) ++ [n]) := by
  simp only [exponentPolynomial_append]
  have hs (a : ℕ) : exponentPolynomial [a] = heightStrip a := by simp [exponentPolynomial]
  simp only [hs]
  induction n with
  | zero => simp [pairSum, heightStrip, exponentPolynomial]
  | succ n ih =>
    rw [pairSum_succ, ih, exponentPolynomial_range_succ]
    have h := heightStrip_add_tail n (n+1)
    rw [show n+(n+1) = 2*n+1 by omega] at h
    rw [h]
    simp only [show ∀ i : ℕ, n+i+1 = (n+1)+i+0 by omega]
    ac_rfl

private theorem union_polynomial {n : ℕ} (v : Space n) (a : ℝ)
    (f : Space n → ℝ)
    (hfin : (positiveRoots (axisRoots n a ∪ pairRoots n) v).Finite)
    (ha : (positiveRoots (axisRoots n a) v).Finite)
    (hp : (positiveRoots (pairRoots n) v).Finite) :
    heightPolynomial (axisRoots n a ∪ pairRoots n) v f hfin =
      heightPolynomial (axisRoots n a) v f ha + heightPolynomial (pairRoots n) v f hp := by
  have hset : hfin.toFinset = ha.toFinset ∪ hp.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, mem_union, positiveRoots, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  have hdis : Disjoint ha.toFinset hp.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.mp (pair_axis_disjoint n a)
      (ha.mem_toFinset.mp hx).1 (hp.mem_toFinset.mp hx').1
  simp only [heightPolynomial, hset, Finset.sum_union hdis]

private theorem union_height {n : ℕ} {v : Space n} {a : ℝ} {f : Space n → ℝ}
    (ha : ∀ x ∈ positiveRoots (axisRoots n a) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ))
    (hp : ∀ x ∈ positiveRoots (pairRoots n) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) :
    ∀ x ∈ positiveRoots (axisRoots n a ∪ pairRoots n) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ) := by
  rintro x ⟨hx, hpos⟩
  exact hx.elim (fun h => ha x ⟨h,hpos⟩) (fun h => hp x ⟨h,hpos⟩)

private theorem odds_max {n : ℕ} (hn : 0 < n) :
    2*n-1 ∈ (List.range n).map (fun i => 2*i+1) ∧
      ∀ m ∈ (List.range n).map (fun i => 2*i+1), m ≤ 2*n-1 := by
  constructor
  · exact List.mem_map.mpr ⟨n-1, List.mem_range.mpr (by omega), by omega⟩
  · intro m hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    simp only [List.mem_range] at hi
    omega

theorem typeB : Specs.typeB := by
  intro n hn
  obtain ⟨b, hb, hs⟩ := simpleB_basis n hn
  let v := regularBCD n 0
  let f := innerₗ (Space n) v
  have hfin : (positiveRoots (rootsB n) v).Finite := (rootsB_finite n).subset fun _ h => h.1
  have hfa : (positiveRoots (axisRoots n 1) v).Finite := (axisRoots_finite n 1).subset fun _ h => h.1
  have hfp : (positiveRoots (pairRoots n) v).Finite := (pairRoots_finite n).subset fun _ h => h.1
  obtain ⟨hiA, hA⟩ := (by
    simpa [v, f] using axis_polynomial n 1 1 (by decide) (by decide) (by simpa [v] using hfa) :
      (∀ x ∈ positiveRoots (axisRoots n 1) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
      heightPolynomial (axisRoots n 1) v f hfa = axisSum n 1 1)
  obtain ⟨hiP, hP⟩ := (by
    simpa [v, f] using pair_polynomial n 2 (by simpa [v] using hfp) :
      (∀ x ∈ positiveRoots (pairRoots n) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
      heightPolynomial (pairRoots n) v f hfp = pairSum n 2)
  have he : heightPolynomial (rootsB n) v f hfin =
      exponentPolynomial ((List.range n).map (fun i => 2*i+1)) := by
    change heightPolynomial (axisRoots n 1 ∪ pairRoots n) v f hfin = _
    rw [union_polynomial v 1 f hfin hfa hfp, hA, hP, polynomialB]
  have hh : 2*n-1+1 = 2*n := by omega
  rw [← hh]
  exact row_of_poly (regularB_regular n) hs hb f (simpleB_height n) hfin (union_height hiA hiP)
    (by omega) (odds_max (by omega)).1 (odds_max (by omega)).2 he

theorem typeC : Specs.typeC := by
  intro n hn
  obtain ⟨b, hb, hs⟩ := simpleC_basis n hn
  let v := regularBCD n (1/2)
  let f := innerₗ (Space n) v
  have hfin : (positiveRoots (rootsC n) v).Finite := (rootsC_finite n).subset fun _ h => h.1
  have hfa : (positiveRoots (axisRoots n 2) v).Finite := (axisRoots_finite n 2).subset fun _ h => h.1
  have hfp : (positiveRoots (pairRoots n) v).Finite := (pairRoots_finite n).subset fun _ h => h.1
  obtain ⟨hiA, hA⟩ := (by
    simpa [v, f, show (1 - 2⁻¹ : ℝ) = 2⁻¹ by norm_num] using axis_polynomial n 2 1 (by decide) (by decide) (by
      norm_num [v] at hfa ⊢
      exact hfa) :
      (∀ x ∈ positiveRoots (axisRoots n 2) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
      heightPolynomial (axisRoots n 2) v f hfa = axisSum n 2 1)
  obtain ⟨hiP, hP⟩ := (by
    simpa [v, f, show (1 - 2⁻¹ : ℝ) = 2⁻¹ by norm_num] using pair_polynomial n 1 (by
      norm_num [v] at hfp ⊢
      exact hfp) :
      (∀ x ∈ positiveRoots (pairRoots n) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
      heightPolynomial (pairRoots n) v f hfp = pairSum n 1)
  have he : heightPolynomial (rootsC n) v f hfin =
      exponentPolynomial ((List.range n).map (fun i => 2*i+1)) := by
    change heightPolynomial (axisRoots n 2 ∪ pairRoots n) v f hfin = _
    rw [union_polynomial v 2 f hfin hfa hfp, hA, hP, polynomialC]
  have hh : 2*n-1+1 = 2*n := by omega
  rw [← hh]
  exact row_of_poly (regularC_regular n) hs hb f (simpleC_height n) hfin (union_height hiA hiP)
    (by omega) (odds_max (by omega)).1 (odds_max (by omega)).2 he

theorem typeD : Specs.typeD := by
  intro n hn
  obtain ⟨b, hb, hs⟩ := simpleD_basis n hn
  let v := regularBCD n 1
  let f := innerₗ (Space n) v
  have hfin : (positiveRoots (rootsD n) v).Finite := (rootsD_finite n).subset fun _ h => h.1
  obtain ⟨hi, hp⟩ := (by
    simpa [v, f, rootsD] using pair_polynomial n 0 (by simpa [rootsD, v] using hfin) :
      (∀ x ∈ positiveRoots (rootsD n) v, ∃ k : ℕ, 0 < k ∧ f x = (k : ℝ)) ∧
      heightPolynomial (rootsD n) v f hfin = pairSum n 0)
  have e : n-1+1 = n := by omega
  have he := polynomialD (n-1)
  rw [e] at he
  have hh : (2*(n-1)-1)+1 = 2*n-2 := by omega
  rw [← hh]
  obtain ⟨hm, hmax⟩ := odds_max (n := n-1) (by omega)
  refine row_of_poly (regularD_regular n) hs hb f (simpleD_height n hn) hfin hi
    (by omega) (List.mem_append_left _ hm) ?_ (hp.trans he)
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hmax _ hm
  · simp only [List.mem_singleton] at hm
    omega

theorem typeD_forkMultiplicity : Specs.typeD_forkMultiplicity := by
  intro n hn
  let odds := (List.range (n-1)).map (fun i => 2*i+1)
  change (odds ++ [n-1]).count (n-1) = _
  have hodd : n-1 ∈ odds ↔ Even n := by
    simp only [odds, List.mem_map, List.mem_range, Nat.even_iff]
    constructor
    · rintro ⟨i, hi, he⟩
      omega
    · intro he
      exact ⟨(n-2)/2, by omega, by omega⟩
  have hd : odds.Nodup :=
    List.nodup_range.map (fun i j h => by omega)
  rw [List.count_append]
  by_cases he : Even n
  · simp [he, List.count_eq_one_of_mem hd (hodd.mpr he)]
  · simp [he, List.count_eq_zero.mpr (fun h => he (hodd.mp h))]

/-- A linear form normalized on the simple roots sums their basis coefficients. -/
theorem height_eq_sum_repr {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    (f : V →ₗ[ℝ] ℝ) (h : ∀ i, f (b i) = 1) (a : V) :
    f a = ∑ i, b.repr a i := by
  calc
    f a = f (∑ i, b.repr a i • b i) := congrArg f (b.sum_repr a).symm
    _ = ∑ i, b.repr a i := by simp only [map_sum, map_smul, h, smul_eq_mul, mul_one]

/-- The table holds for the positive system of any regular vector with the
given simple basis, with height given by the sum of its basis coefficients. -/
theorem TableRow.at_basis {ι : Type*} [Fintype ι] {R : Set V} {v : V}
    {b : Module.Basis ι ℝ V} {ms : List ℕ} {h : ℕ}
    (row : TableRow R b ms h) (hR : RootAxioms R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) :
    let height := fun a : V => ∑ i, b.repr a i
    ∃ hfin : (positiveRoots R v).Finite,
      (∀ a ∈ positiveRoots R v, ∃ k : ℕ, 0 < k ∧ height a = (k : ℝ)) ∧
      heightPolynomial R v height hfin = exponentPolynomial ms ∧
      (∀ m : ℕ, 0 < m →
        (heightSlice R v height m).ncard - (heightSlice R v height (m + 1)).ncard =
          ms.count m) ∧
      ∃ k : ℕ, h = k + 1 ∧ IsGreatest (height '' positiveRoots R v) (k : ℝ) := by
  dsimp only
  obtain ⟨w, c, f, hf, hw, hc, hcb, h1, hnat, hp, hcount, k, hk, htop⟩ := row
  have hsimple : simpleRoots R w = simpleRoots R v := by
    rw [← hc, ← hb]
    exact congrArg Set.range (funext hcb)
  have subset_of_same_simple {z z' : V} (hz' : RootRegular R z')
      (hs : simpleRoots R z = simpleRoots R z') :
      positiveRoots R z ⊆ positiveRoots R z' := by
    intro a ha
    have hm := positive_mem_closure_simple hR z ha
    rw [hs] at hm
    have nonneg : 0 ≤ inner ℝ z' a := by
      clear ha
      induction hm using AddSubmonoid.closure_induction with
      | mem x hx => exact (simpleRoots_subset_positive R z' hx).2.le
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_right]; exact add_nonneg hx hy
    exact ⟨ha.1, lt_of_le_of_ne nonneg (hz' a ha.1).symm⟩
  have hpos : positiveRoots R v = positiveRoots R w :=
    Set.Subset.antisymm (subset_of_same_simple hw hsimple.symm)
      (subset_of_same_simple hv hsimple)
  let hfin : (positiveRoots R v).Finite := hR.finite.subset fun _ ha => ha.1
  have hfin_eq : hfin.toFinset = hf.toFinset := by
    ext a
    simp only [Set.Finite.mem_toFinset, hpos]
  have hslice (m : ℕ) : heightSlice R v f m = heightSlice R w f m := by
    simp only [heightSlice, hpos]
  simp_rw [← height_eq_sum_repr b f h1]
  refine ⟨hfin, ?_, ?_, ?_, k, hk, ?_⟩
  · rwa [hpos]
  · simpa only [heightPolynomial, hfin_eq] using hp
  · intro m hm
    rw [hslice, hslice]
    exact hcount m hm
  · rwa [hpos]

/-- The highest root, which dominates every root in the simple-root order,
attains the greatest height used in the table. -/
theorem highestRoot_height {ι : Type*} [Fintype ι] {R : Set V} {v : V}
    {b : Module.Basis ι ℝ V} (hb : IsSimpleBasis R v b) (f : V →ₗ[ℝ] ℝ)
    (h : ∀ i, f (b i) = 1) {θ : V} (hθ : θ ∈ positiveRoots R v)
    (hdom : ∀ a ∈ R, θ - a ∈ AddSubmonoid.closure (simpleRoots R v)) :
    IsGreatest (f '' positiveRoots R v) (f θ) := by
  refine ⟨⟨θ, hθ, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have nonneg : ∀ x ∈ AddSubmonoid.closure (simpleRoots R v), 0 ≤ f x := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      rw [← hb] at hx
      obtain ⟨i, rfl⟩ := hx
      rw [h]
      norm_num
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add]
      exact add_nonneg ihx ihy
  have hsum := nonneg (θ-a) (hdom a ha.1)
  rw [map_sub, sub_nonneg] at hsum
  exact hsum

/-- A based linear isomorphism preserves every entry of the height table. -/
theorem TableRow.map {ι : Type*} [Fintype ι] {R : Set V} {simple : ι → V}
    {ms : List ℕ} {h : ℕ} (row : TableRow R simple ms h)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (e : V ≃ₗ[ℝ] W) : TableRow (e '' R) (fun i => e (simple i)) ms h := by
  obtain ⟨v, b, f, hf, hr, hb, hs, h1, hnat, hp, hcounts, k, hk, htop⟩ := row
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b
  have : FiniteDimensional ℝ W := Module.Finite.of_basis (b.map e)
  let w := e.symm.toLinearMap.adjoint v
  let f' := f.comp e.symm.toLinearMap
  have image_mem (S : Set V) (x : V) : e x ∈ e '' S ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact e.injective he ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hin (x : V) : inner ℝ w (e x) = inner ℝ v x := by
    rw [LinearMap.adjoint_inner_left]
    simp
  have hpos (x : V) : e x ∈ positiveRoots (e '' R) w ↔ x ∈ positiveRoots R v := by
    change (e x ∈ e '' R ∧ 0 < inner ℝ w (e x)) ↔ _
    rw [hin]
    simp [positiveRoots, image_mem]
  have hsimp (x : V) : e x ∈ simpleRoots (e '' R) w ↔ x ∈ simpleRoots R v := by
    constructor
    · intro hx
      refine ⟨(hpos x).mp hx.1, ?_⟩
      intro a ha c hc he
      exact hx.2 _ ((hpos a).mpr ha) _ ((hpos c).mpr hc) (by rw [he, map_add])
    · intro hx
      refine ⟨(hpos x).mpr hx.1, ?_⟩
      intro a ha c hc he
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨c, rfl⟩ := e.surjective c
      rw [← map_add] at he
      exact hx.2 _ ((hpos a).mp ha) _ ((hpos c).mp hc) (e.injective he)
  have hposImage : positiveRoots (e '' R) w = e '' positiveRoots R v := by
    ext x
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [hpos, image_mem]
  have hf' : (positiveRoots (e '' R) w).Finite := hposImage ▸ hf.image e
  have hcomp (x : V) : f' (e x) = f x := by simp [f']
  have hslice (m : ℕ) : heightSlice (e '' R) w f' m = e '' heightSlice R v f m := by
    ext x
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [image_mem]
    simp only [heightSlice, Set.mem_ofPred_eq, hpos, hcomp]
  refine ⟨w, b.map e, f', hf', ?_, ?_, ?_, ?_, ?_, ?_, ?_, k, hk, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hin]
    exact hr x hx
  · ext y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hsimp]
    simpa only [Module.Basis.map_apply, Set.mem_range, e.injective.eq_iff] using
      (show y ∈ Set.range b ↔ y ∈ simpleRoots R v by rw [hb])
  · intro i
    rw [Module.Basis.map_apply, hs]
  · intro i
    rw [hcomp, h1]
  · intro x hx
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [hcomp]
    exact hnat x ((hpos x).mp hx)
  · rw [← hp, heightPolynomial, heightPolynomial]
    symm
    apply Finset.sum_bij (fun x _ => e x)
    · intro a ha
      exact hf'.mem_toFinset.mpr ((hpos a).mpr (hf.mem_toFinset.mp ha))
    · intro a _ c _ he
      exact e.injective he
    · intro a ha
      obtain ⟨a, rfl⟩ := e.surjective a
      exact ⟨a, hf.mem_toFinset.mpr ((hpos a).mp (hf'.mem_toFinset.mp ha)), rfl⟩
    · intros
      rw [hcomp]
  · intro m hm
    rw [hslice, hslice, Set.ncard_image_of_injective _ e.injective,
      Set.ncard_image_of_injective _ e.injective]
    exact hcounts m hm
  · rw [hposImage, Set.image_image]
    simpa only [Function.comp_def, hcomp] using htop

section Exceptional
open ExceptionalGF (QVec realize dot)
open ExceptionalGF (g2Roots g2Simple g2Plane g2Regular g2List g2AmbientRoots
  f4Roots f4Simple f4Regular f4List)
open ExceptionalE (e6Roots e6Simple e6Space e6Regular e6List e6AmbientRoots
  e7Roots e7Simple e7Space e7Regular e7List e7AmbientRoots
  e8Roots e8Simple e8Regular e8List)

private def rationalHeights {n : ℕ} (S : Finset (QVec n)) (w : QVec n) : Multiset ℚ :=
  (S.filter (fun q => 0 < dot w q)).val.map (dot w)

private def stripHeights (ms : List ℕ) : List ℚ :=
  ms.flatMap fun m => (List.range m).map fun k => ((k+1 : ℕ) : ℚ)

private theorem stripHeights_polynomial (ms : List ℕ) :
    ((stripHeights ms : Multiset ℚ).map (fun q => (X : ℕ[X]) ^ ⌊q⌋₊)).sum =
      exponentPolynomial ms := by
  let powers (l : List ℚ) : ℕ[X] :=
    ((l : Multiset ℚ).map (fun q => (X : ℕ[X]) ^ ⌊q⌋₊)).sum
  change powers (stripHeights ms) = exponentPolynomial ms
  have hadd (l m : List ℚ) : powers (l ++ m) = powers l + powers m := by
    simp only [powers, ← Multiset.coe_add, Multiset.map_add, Multiset.sum_add]
  have hstrip (m : ℕ) :
      powers ((List.range m).map fun i => ((i+1 : ℕ) : ℚ)) = heightStrip m := by
    induction m with
    | zero => simp [powers, heightStrip]
    | succ m ih =>
      rw [List.range_succ, List.map_append, hadd, ih, heightStrip_succ]
      have hfloor : ⌊(m : ℚ) + 1⌋₊ = m+1 := by
        rw [← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
      simp [powers, hfloor]
  induction ms with
  | nil => simp [powers, stripHeights, exponentPolynomial]
  | cons m ms ih =>
    change powers (((List.range m).map fun i => ((i+1 : ℕ) : ℚ)) ++ stripHeights ms) =
      heightStrip m + exponentPolynomial ms
    rw [hadd, hstrip, ih]

private theorem exceptional_row {ι : Type*} [Fintype ι] {n : ℕ} {R : Set V} {v : V}
    {simple : ι → V} (hr : RootRegular R v) (b : Module.Basis ι ℝ V)
    (hb : ∀ i, b i = simple i) (hs : IsSimpleBasis R v b)
    (f : V →ₗ[ℝ] ℝ) (h1 : ∀ i, f (simple i) = 1)
    (hcut : ∀ a ∈ R, 0 < inner ℝ v a ↔ 0 < f a)
    (j : V → Space n) (hj : Function.Injective j) (S : Finset (QVec n)) (w : QVec n)
    (hR : j '' R = realize '' (S : Set (QVec n)))
    (hw : ∀ a q, j a = realize q → f a = (dot w q : ℝ))
    (ms : List ℕ) (k : ℕ) (hk : 0 < k) (hkm : k ∈ ms) (hmax : ∀ m ∈ ms, m ≤ k)
    (hc : rationalHeights S w = (stripHeights ms : Multiset ℚ)) :
    TableRow R simple ms (k+1) := by
  have hRf : R.Finite := by
    apply Set.Finite.of_finite_image _ hj.injOn
    rw [hR]
    exact S.finite_toSet.image realize
  let hfin : (positiveRoots R v).Finite := hRf.subset (fun _ h => h.1)
  let s := S.filter (fun q => 0 < dot w q)
  have hmem (q) : q ∈ s ↔ realize q ∈ j '' positiveRoots R v := by
    constructor
    · intro hq
      obtain ⟨hq, hpos⟩ := mem_filter.mp hq
      have h : realize q ∈ j '' R := hR.symm ▸ ⟨q, hq, rfl⟩
      obtain ⟨a, ha, he⟩ := h
      refine ⟨a, ⟨ha, (hcut a ha).mpr ?_⟩, he⟩
      rw [hw a q he]
      exact_mod_cast hpos
    · rintro ⟨a, ha, he⟩
      have h : realize q ∈ realize '' (S : Set (QVec n)) := hR ▸ ⟨a, ha.1, he⟩
      obtain ⟨p, hp, he'⟩ := h
      have hpq := ExceptionalGF.realize_injective he'
      subst p
      have hpos := (hcut a ha.1).mp ha.2
      rw [hw a q he] at hpos
      exact mem_filter.mpr ⟨hp, by exact_mod_cast hpos⟩
  let g (q) (hq : q ∈ s) : V := Classical.choose ((hmem q).mp hq)
  have hg (q) (hq : q ∈ s) : g q hq ∈ positiveRoots R v ∧ j (g q hq) = realize q :=
    Classical.choose_spec ((hmem q).mp hq)
  have hnat (q) (hq : q ∈ s) : ∃ i : ℕ, 0 < i ∧ dot w q = (i : ℚ) := by
    have h : dot w q ∈ rationalHeights S w := Multiset.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hc] at h
    change dot w q ∈ stripHeights ms at h
    obtain ⟨m, hm, h⟩ := List.mem_flatMap.mp h
    obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    exact ⟨i+1, by omega, he.symm⟩
  obtain ⟨hi, hp⟩ := enumerate s hfin f g (fun q => ⌊dot w q⌋₊)
    (fun q hq => (hg q hq).1)
    (by
      intro q hq p hp he
      exact ExceptionalGF.realize_injective ((hg q hq).2.symm.trans
        ((congrArg j he).trans (hg p hp).2)))
    (by
      intro a ha
      have h : j a ∈ realize '' (S : Set (QVec n)) := hR ▸ ⟨a, ha.1, rfl⟩
      obtain ⟨q, hq, he⟩ := h
      have hqs := (hmem q).mpr ⟨a, ha, he.symm⟩
      exact ⟨q, hqs, hj ((hg q hqs).2.trans he)⟩)
    (by
      intro q hq
      obtain ⟨i, _, hi⟩ := hnat q hq
      rw [hw _ q (hg q hq).2, hi, Nat.floor_natCast]
      norm_cast)
    (by
      intro q hq
      obtain ⟨i, hi, he⟩ := hnat q hq
      rwa [he, Nat.floor_natCast])
  refine row_of_poly hr hs hb f h1 hfin hi hk hkm hmax ?_
  rw [heightPolynomial, hp, ← stripHeights_polynomial ms, ← hc]
  change (s.val.map (fun q => (X : ℕ[X]) ^ ⌊dot w q⌋₊)).sum =
    ((s.val.map (dot w)).map (fun q => (X : ℕ[X]) ^ ⌊q⌋₊)).sum
  rw [Multiset.map_map]
  rfl

private theorem g2_roots_image :
    (Subtype.val : g2Plane → Space 3) '' g2Roots = g2AmbientRoots := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    exact ⟨⟨a, ExceptionalGF.g2_span ▸ Submodule.subset_span ha⟩, ha, rfl⟩

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem g2_signs :
    ∀ q ∈ g2List, (0 < dot ![-1,-2,3] q) ↔ (0 < dot ![-1/3,-4/3,5/3] q) := by
  decide +kernel

private theorem g2_height_certificate :
    rationalHeights g2List ![-1/3,-4/3,5/3] = (stripHeights [1,5] : Multiset ℚ) := by
  decide +kernel

theorem typeG₂ : Specs.typeG₂ := by
  obtain ⟨hr, b, hb, hs⟩ := ExceptionalGF.g2_basis
  let w : QVec 3 := ![-1/3,-4/3,5/3]
  let f := (innerₗ (Space 3) (realize w)).comp g2Plane.subtype
  refine exceptional_row hr b hb hs f ?_ ?_ (Subtype.val : g2Plane → Space 3)
    Subtype.val_injective g2List w g2_roots_image ?_
    [1,5] 5 (by decide) (by decide) (by decide) g2_height_certificate
  · intro i
    fin_cases i <;> norm_num [f, w, g2Simple, ExceptionalGF.g2SimpleAmbient,
      ExceptionalGF.realize_inner, dot, Fin.sum_univ_succ]
  · intro a ha
    obtain ⟨q, hq, he⟩ := (show (a : Space 3) ∈ g2AmbientRoots from ha)
    rw [Submodule.coe_inner]
    change (0 < inner ℝ (realize ![-1,-2,3]) (a : Space 3)) ↔
      (0 < inner ℝ (realize w) (a : Space 3))
    rw [← he, ExceptionalGF.realize_inner, ExceptionalGF.realize_inner]
    simpa only [w, Rat.cast_pos] using g2_signs q hq
  · intro a q ha
    change inner ℝ (realize w) (a : Space 3) = _
    rw [ha, ExceptionalGF.realize_inner]

private theorem f4_height_certificate :
    rationalHeights f4List ![8,3,2,1] = (stripHeights [1,5,7,11] : Multiset ℚ) := by
  decide +kernel

theorem typeF₄ : Specs.typeF₄ := by
  obtain ⟨hr, b, hb, hs⟩ := ExceptionalGF.f4_basis
  refine exceptional_row hr b hb hs (innerₗ _ f4Regular) ?_ (fun _ _ => Iff.rfl) (id : Space 4 → Space 4)
    Function.injective_id f4List ![8,3,2,1] (by simp [f4Roots]) ?_
    [1,5,7,11] 11 (by decide) (by decide) (by decide) f4_height_certificate
  · intro i
    fin_cases i <;> norm_num [f4Regular, f4Simple, ExceptionalGF.realize_inner, dot, Fin.sum_univ_succ]
  · intro a q ha
    change a = realize q at ha
    rw [ha]
    exact ExceptionalGF.realize_inner ![8,3,2,1] q

private theorem e6_height_certificate :
    rationalHeights e6List ![0,1,2,3,4,-4,-4,4] = (stripHeights [1,4,5,7,8,11] : Multiset ℚ) := by
  decide +kernel

theorem typeE₆ : Specs.typeE₆ := by
  obtain ⟨hr, b, hb, hs⟩ := ExceptionalE.e6_basis
  refine exceptional_row hr b hb hs (innerₗ _ e6Regular) ?_ (fun _ _ => Iff.rfl) (Subtype.val : e6Space → Space 8)
    Subtype.val_injective e6List ![0,1,2,3,4,-4,-4,4] ExceptionalE.e6_roots_image ?_
    [1,4,5,7,8,11] 11 (by decide) (by decide) (by decide) e6_height_certificate
  · intro i
    change inner ℝ e6Regular (e6Simple i) = 1
    rw [ExceptionalE.e6_height]
    exact ExceptionalE.simple_height _
  · intro a q ha
    change inner ℝ e6Regular a = _
    rw [Submodule.coe_inner]
    change inner ℝ (realize ![0,1,2,3,4,-4,-4,4]) (a : Space 8) = _
    rw [ha, ExceptionalGF.realize_inner]

private theorem e7_height_certificate :
    rationalHeights e7List ![0,1,2,3,4,5,-17/2,17/2] = (stripHeights [1,5,7,9,11,13,17] : Multiset ℚ) := by
  decide +kernel

theorem typeE₇ : Specs.typeE₇ := by
  obtain ⟨hr, b, hb, hs⟩ := ExceptionalE.e7_basis
  refine exceptional_row hr b hb hs (innerₗ _ e7Regular) ?_ (fun _ _ => Iff.rfl) (Subtype.val : e7Space → Space 8)
    Subtype.val_injective e7List ![0,1,2,3,4,5,-17/2,17/2] ExceptionalE.e7_roots_image ?_
    [1,5,7,9,11,13,17] 17 (by decide) (by decide) (by decide) e7_height_certificate
  · intro i
    change inner ℝ e7Regular (e7Simple i) = 1
    rw [ExceptionalE.e7_height]
    exact ExceptionalE.simple_height _
  · intro a q ha
    change inner ℝ e7Regular a = _
    rw [Submodule.coe_inner]
    change inner ℝ (realize ![0,1,2,3,4,5,-17/2,17/2]) (a : Space 8) = _
    rw [ha, ExceptionalGF.realize_inner]

private theorem e8_height_certificate :
    rationalHeights e8List ![0,1,2,3,4,5,6,23] = (stripHeights [1,7,11,13,17,19,23,29] : Multiset ℚ) := by
  decide +kernel

theorem typeE₈ : Specs.typeE₈ := by
  obtain ⟨hr, b, hb, hs⟩ := ExceptionalE.e8_basis
  refine exceptional_row hr b hb hs (innerₗ _ e8Regular) ?_ (fun _ _ => Iff.rfl) (id : Space 8 → Space 8)
    Function.injective_id e8List ![0,1,2,3,4,5,6,23] (by simp [e8Roots]) ?_
    [1,7,11,13,17,19,23,29] 29 (by decide) (by decide) (by decide) e8_height_certificate
  · exact ExceptionalE.simple_height
  · intro a q ha
    change a = realize q at ha
    rw [ha]
    exact ExceptionalGF.realize_inner ![0,1,2,3,4,5,6,23] q

end Exceptional
end LieAlgebrasAndRepresentations.ExponentTables
