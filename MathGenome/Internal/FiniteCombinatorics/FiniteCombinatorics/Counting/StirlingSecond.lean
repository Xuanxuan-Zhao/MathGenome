import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingSecond

namespace FiniteCombinatorics.StirlingSecond

open Classical

noncomputable def partitionCount : ℕ → ℕ → ℕ := count

@[simp] theorem mem_roots {n} (p : Partition n) (i : Fin n) :
    i ∈ roots p ↔ p.rep i = i := by simp [roots]

/-- Fibers of the canonical representative map are the unordered blocks. -/
def toSetoid {n} (p : Partition n) : Setoid (Fin n) := Setoid.ker p.rep

private noncomputable def classMin {n} (s : Setoid (Fin n)) (i : Fin n) : Fin n :=
  (Finset.univ.filter (s.r i)).min' ⟨i, by simp⟩

private theorem classMin_rel {n} (s : Setoid (Fin n)) (i : Fin n) :
    s.r i (classMin s i) := by
  have := Finset.min'_mem (Finset.univ.filter (s.r i)) ⟨i, by simp⟩
  simpa [classMin] using this

private theorem classMin_le {n} (s : Setoid (Fin n)) (i j : Fin n)
    (h : s.r i j) : classMin s i ≤ j :=
  Finset.min'_le _ _ (by simp [h])

private theorem classMin_eq {n} (s : Setoid (Fin n)) (i j : Fin n)
    (h : s.r i j) : classMin s i = classMin s j := by
  apply le_antisymm
  · exact classMin_le s i _ (s.trans h (classMin_rel s j))
  · exact classMin_le s j _ (s.trans (s.symm h) (classMin_rel s i))

noncomputable def ofSetoid {n} (s : Setoid (Fin n)) : Partition n where
  rep := classMin s
  idempotent i := (classMin_eq s i _ (classMin_rel s i)).symm
  decreasing i := classMin_le s i i (s.refl i)

@[simp] theorem toSetoid_ofSetoid {n} (s : Setoid (Fin n)) :
    toSetoid (ofSetoid s) = s := by
  ext i j
  change classMin s i = classMin s j ↔ s.r i j
  constructor
  · intro h
    exact s.trans (classMin_rel s i) (h ▸ s.symm (classMin_rel s j))
  · exact classMin_eq s i j

@[simp] theorem ofSetoid_toSetoid {n} (p : Partition n) :
    ofSetoid (toSetoid p) = p := by
  apply Partition.ext
  funext i
  change classMin (toSetoid p) i = p.rep i
  apply le_antisymm
  · apply classMin_le
    exact (p.idempotent i).symm
  · have h := classMin_rel (toSetoid p) i
    change p.rep i = p.rep (classMin (toSetoid p) i) at h
    rw [h]
    exact p.decreasing _

noncomputable def partitionEquivSetoid (n : ℕ) : Partition n ≃ Setoid (Fin n) where
  toFun := toSetoid
  invFun := ofSetoid
  left_inv := ofSetoid_toSetoid
  right_inv := toSetoid_ofSetoid

theorem partition_semantics : Specs.FiniteCombinatorics.StirlingSecond.partitionSemantics := by
  intro n
  exact ⟨partitionEquivSetoid n, fun _ _ _ => Iff.rfl⟩

noncomputable def blockEquiv {n} (p : Partition n) :
    Quotient (Setoid.ker p.rep) ≃ {i // i ∈ roots p} where
  toFun := Quotient.lift (fun i => ⟨p.rep i, by simp [p.idempotent]⟩)
    (fun _ _ h => Subtype.ext h)
  invFun i := Quotient.mk _ i.val
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with | _ i =>
      exact Quotient.sound (p.idempotent i)
  right_inv := by
    intro i
    exact Subtype.ext (mem_roots p i.val |>.mp i.prop)

theorem block_semantics : Specs.FiniteCombinatorics.StirlingSecond.blockSemantics := by
  intro n p
  exact ⟨blockEquiv p, fun _ => rfl⟩

/-- Insert the new greatest element either as a singleton, or in one existing block. -/
def extend {n} (p : Partition n) (r : Option {i // i ∈ roots p}) : Partition (n + 1) where
  rep := Fin.lastCases (r.elim (Fin.last n) (fun i => i.val.castSucc))
    (fun i => (p.rep i).castSucc)
  idempotent := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · cases r with
      | none => simp
      | some r => simp [(mem_roots p r.val).mp r.prop]
    · simp [p.idempotent]
  decreasing := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.le_last _
    · simpa using p.decreasing j

@[simp] theorem extend_rep_castSucc {n} (p : Partition n) (r) (i : Fin n) :
    (extend p r).rep i.castSucc = (p.rep i).castSucc := by simp [extend]

@[simp] theorem extend_rep_last {n} (p : Partition n) (r) :
    (extend p r).rep (Fin.last n) = r.elim (Fin.last n) (fun i => i.val.castSucc) := by
  simp [extend]

def drop {n} (p : Partition (n + 1)) : Partition n where
  rep i := ⟨(p.rep i.castSucc).val,
    lt_of_le_of_lt (p.decreasing i.castSucc) i.isLt⟩
  idempotent i := by
    apply Fin.ext
    change (p.rep _).val = (p.rep i.castSucc).val
    have h : (⟨(p.rep i.castSucc).val,
        lt_of_le_of_lt (p.decreasing i.castSucc) i.isLt⟩ : Fin n).castSucc =
        p.rep i.castSucc := rfl
    rw [h, p.idempotent]
  decreasing i := p.decreasing i.castSucc

@[simp] theorem drop_rep_castSucc {n} (p : Partition (n + 1)) (i : Fin n) :
    ((drop p).rep i).castSucc = p.rep i.castSucc := rfl

@[simp] theorem drop_extend {n} (p : Partition n) (r) : drop (extend p r) = p := by
  apply Partition.ext
  funext i
  apply Fin.ext
  simp [drop]

private theorem last_lt {n} (p : Partition (n + 1))
    (h : p.rep (Fin.last n) ≠ Fin.last n) : (p.rep (Fin.last n)).val < n := by
  have := (p.rep (Fin.last n)).isLt
  have : (p.rep (Fin.last n)).val ≠ n := fun he => h (Fin.ext he)
  omega

def lastChoice {n} (p : Partition (n + 1)) : Option {i // i ∈ roots (drop p)} :=
  if h : p.rep (Fin.last n) = Fin.last n then none else
    some ⟨⟨(p.rep (Fin.last n)).val, last_lt p h⟩, by
      rw [mem_roots]
      apply Fin.ext
      change (p.rep _).val = (p.rep (Fin.last n)).val
      have he : (⟨(p.rep (Fin.last n)).val, last_lt p h⟩ : Fin n).castSucc =
          p.rep (Fin.last n) := rfl
      rw [he, p.idempotent]⟩

@[simp] theorem extend_drop {n} (p : Partition (n + 1)) :
    extend (drop p) (lastChoice p) = p := by
  apply Partition.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [extend_rep_last, lastChoice]
    split_ifs with h
    · exact h.symm
    · rfl
  · simp

private theorem extend_injective {n} : Function.Injective
    (fun pr : (Σ p : Partition n, Option {i // i ∈ roots p}) => extend pr.1 pr.2) := by
  rintro ⟨p, r⟩ ⟨q, s⟩ h
  have hp : p = q := by simpa using congrArg drop h
  subst q
  have hr : r = s := by
    have hl := congrArg (fun t : Partition (n + 1) => t.rep (Fin.last n)) h
    simp only [extend_rep_last] at hl
    cases r with
    | none =>
      cases s with
      | none => rfl
      | some s => exact (Fin.castSucc_ne_last _ hl.symm).elim
    | some r =>
      cases s with
      | none => exact (Fin.castSucc_ne_last _ hl).elim
      | some s =>
        congr 1
        exact Subtype.ext (Fin.castSucc_injective _ hl)
  subst s
  rfl

noncomputable def extensionEquiv (n : ℕ) :
    (Σ p : Partition n, Option {i // i ∈ roots p}) ≃ Partition (n + 1) :=
  Equiv.ofBijective (fun pr => extend pr.1 pr.2)
    ⟨extend_injective, fun p => ⟨⟨drop p, lastChoice p⟩, extend_drop p⟩⟩

@[simp] theorem roots_extend_none {n} (p : Partition n) :
    roots (extend p none) = insert (Fin.last n) ((roots p).map Fin.castSuccEmb) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

@[simp] theorem roots_extend_some {n} (p : Partition n) (r : {i // i ∈ roots p}) :
    roots (extend p (some r)) = (roots p).map Fin.castSuccEmb := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

@[simp] theorem card_roots_extend_none {n} (p : Partition n) :
    (roots (extend p none)).card = (roots p).card + 1 := by simp

@[simp] theorem card_roots_extend_some {n} (p : Partition n) (r : {i // i ∈ roots p}) :
    (roots (extend p (some r))).card = (roots p).card := by simp

def successorMap (n k : ℕ) :
    WithBlocks n k ⊕ (Σ p : WithBlocks n (k + 1), {i // i ∈ roots p.val}) →
      WithBlocks (n + 1) (k + 1)
  | .inl p => ⟨extend p.val none, by simp [p.prop]⟩
  | .inr ⟨p, r⟩ => ⟨extend p.val (some r), by simp [p.prop]⟩

private theorem successorMap_injective (n k : ℕ) :
    Function.Injective (successorMap n k) := by
  rintro (a | ⟨a, r⟩) (b | ⟨b, s⟩) h
  · have hp : a.val = b.val := by
      simpa [successorMap] using congrArg drop (congrArg Subtype.val h)
    exact congrArg Sum.inl (Subtype.ext hp)
  · have hd := @extend_injective n ⟨a.val, none⟩ ⟨b.val, some s⟩ (congrArg Subtype.val h)
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [Sigma.mk.inj_iff] at hd
    rcases hd with ⟨hab, hopt⟩
    subst b
    cases hopt
  · have hd := @extend_injective n ⟨a.val, some r⟩ ⟨b.val, none⟩ (congrArg Subtype.val h)
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [Sigma.mk.inj_iff] at hd
    rcases hd with ⟨hab, hopt⟩
    subst b
    cases hopt
  · have hd := @extend_injective n ⟨a.val, some r⟩ ⟨b.val, some s⟩ (congrArg Subtype.val h)
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [Sigma.mk.inj_iff] at hd
    rcases hd with ⟨hab, hopt⟩
    subst b
    have hrs : r = s := by simpa using eq_of_heq hopt
    subst s
    rfl

private theorem successorMap_surjective (n k : ℕ) :
    Function.Surjective (successorMap n k) := by
  intro p
  obtain ⟨⟨q, r⟩, hqr⟩ := (extensionEquiv n).surjective p.val
  change extend q r = p.val at hqr
  have hc := p.prop
  rw [← hqr] at hc
  cases r with
  | none =>
    have hq : (roots q).card = k := by simpa using hc
    exact ⟨.inl ⟨q, hq⟩, Subtype.ext hqr⟩
  | some r =>
    have hq : (roots q).card = k + 1 := by simpa using hc
    exact ⟨.inr ⟨⟨q, hq⟩, r⟩, Subtype.ext hqr⟩

noncomputable def successorEquiv (n k : ℕ) :
    WithBlocks n k ⊕ (Σ p : WithBlocks n (k + 1), {i // i ∈ roots p.val}) ≃
      WithBlocks (n + 1) (k + 1) :=
  Equiv.ofBijective (successorMap n k)
    ⟨successorMap_injective n k, successorMap_surjective n k⟩

theorem count_successor (n k : ℕ) :
    count (n + 1) (k + 1) = count n k + (k + 1) * count n (k + 1) := by
  classical
  rw [count, ← Fintype.card_congr (successorEquiv n k), Fintype.card_sum,
    Fintype.card_sigma]
  have hs : ∀ p : WithBlocks n (k + 1), Fintype.card {i // i ∈ roots p.val} = k + 1 := by
    intro p
    rw [Fintype.card_coe]
    exact p.prop
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.mul_comm]
  rfl

private def emptyPartition : Partition 0 where
  rep := Fin.elim0
  idempotent i := Fin.elim0 i
  decreasing i := Fin.elim0 i

private instance : Unique (Partition 0) where
  default := emptyPartition
  uniq p := by
    apply Partition.ext
    funext i
    exact Fin.elim0 i

theorem count_zero_zero : count 0 0 = 1 := by
  have h : ∀ p : Partition 0, (roots p).card = 0 := by simp [roots]
  have : Unique (WithBlocks 0 0) :=
    { default := ⟨emptyPartition, h _⟩
      uniq := fun p => Subtype.ext (Subsingleton.elim _ _) }
  exact Fintype.card_unique

theorem count_zero_succ (k : ℕ) : count 0 (k + 1) = 0 := by
  have : IsEmpty (WithBlocks 0 (k + 1)) := ⟨fun p => by
    have h := p.prop
    simp [roots] at h⟩
  exact Fintype.card_eq_zero

theorem count_succ_zero (n : ℕ) : count (n + 1) 0 = 0 := by
  have : IsEmpty (WithBlocks (n + 1) 0) := ⟨fun p => by
    have h : (roots p.val).Nonempty := ⟨p.val.rep 0, by simp [p.val.idempotent]⟩
    have := Finset.card_pos.mpr h
    rw [p.prop] at this
    omega⟩
  exact Fintype.card_eq_zero

theorem count_eq_stirlingSecond : Specs.FiniteCombinatorics.StirlingSecond.counting := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => exact count_zero_zero
    | succ k => exact count_zero_succ k
  | succ n ih =>
    intro k
    cases k with
    | zero => exact count_succ_zero n
    | succ k =>
      rw [count_successor, ih, ih, Nat.stirlingSecond_succ_succ, Nat.add_comm]

/-- Relabeling the ground set transports unordered partitions without adding labels to blocks. -/
def setoidCongr {α β : Type*} (e : α ≃ β) : Setoid α ≃ Setoid β where
  toFun s := s.comap e.symm
  invFun s := s.comap e
  left_inv s := by ext i j; simp [Setoid.comap_rel]
  right_inv s := by ext i j; simp [Setoid.comap_rel]

def quotientCongr {α β : Type*} (e : α ≃ β) (s : Setoid α) :
    Quotient s ≃ Quotient (setoidCongr e s) :=
  Quotient.congr e (fun i j => by
    change s i j ↔ s (e.symm (e i)) (e.symm (e j))
    simp)

theorem quotient_card {n} (p : Partition n) :
    Nat.card (Quotient (toSetoid p)) = (roots p).card := by
  change Nat.card (Quotient (Setoid.ker p.rep)) = _
  rw [Nat.card_congr (blockEquiv p), Nat.card_eq_fintype_card, Fintype.card_coe]

noncomputable def withBlocksEquivSetoid (n k : ℕ) :
    WithBlocks n k ≃ {s : Setoid (Fin n) // Nat.card (Quotient s) = k} :=
  (partitionEquivSetoid n).subtypeEquiv (fun p => by
    change (roots p).card = k ↔ Nat.card (Quotient (toSetoid p)) = k
    rw [quotient_card])

theorem card_setoids (α : Type*) [Fintype α] (k : ℕ) :
    Nat.card {s : Setoid α // Nat.card (Quotient s) = k} =
      Nat.stirlingSecond (Fintype.card α) k := by
  let e := Fintype.equivFin α
  let se := (setoidCongr e).subtypeEquiv (p := fun s => Nat.card (Quotient s) = k)
    (q := fun s => Nat.card (Quotient s) = k) (fun s => by
      rw [← Nat.card_congr (quotientCongr e s)])
  rw [Nat.card_congr se, ← Nat.card_congr (withBlocksEquivSetoid (Fintype.card α) k),
    Nat.card_eq_fintype_card]
  exact count_eq_stirlingSecond _ _

/-- Literal collections of nonempty disjoint blocks, covering any finite ground type. -/
theorem finite_set_counting : Specs.FiniteCombinatorics.StirlingSecond.finiteSetCounting := by
  intro α _ k
  let e := (Setoid.Partition.orderIso (α := α)).toEquiv.subtypeEquiv
    (p := fun s => Nat.card (Quotient s) = k)
    (q := fun P => Nat.card P.val = k) (fun s => by
      change Nat.card (Quotient s) = k ↔ Nat.card s.classes = k
      rw [Nat.card_congr (Setoid.quotientEquivClasses s)])
  rw [← Nat.card_congr e]
  exact card_setoids α k

theorem count_out_of_range : Specs.FiniteCombinatorics.StirlingSecond.outOfRange := by
  intro n k h
  rw [count_eq_stirlingSecond]
  exact Nat.stirlingSecond_eq_zero_of_lt h

theorem integer_boundary : Specs.FiniteCombinatorics.StirlingSecond.integerBoundary := by
  intro n k hk
  simp [secondInt, not_le.mpr hk]

theorem integer_recurrence : Specs.FiniteCombinatorics.StirlingSecond.integerRecurrence := by
  intro n k
  by_cases hk : k < 0
  · rw [integer_boundary _ _ hk, integer_boundary _ _ (by omega),
      integer_boundary _ _ hk]
    simp
  · have hk : 0 ≤ k := by omega
    by_cases hz : k = 0
    · subst k
      simp [secondInt, Nat.stirlingSecond_succ_zero]
    · have hp : 0 ≤ k - 1 := by omega
      have ht : (k - 1).toNat = k.toNat - 1 := by omega
      have ht0 : k.toNat ≠ 0 := by omega
      simp only [secondInt, ite_eq_left hk, ite_eq_left hp, ht]
      rw [Nat.stirlingSecond_succ_left n k.toNat ht0, Nat.add_comm]

end FiniteCombinatorics.StirlingSecond
