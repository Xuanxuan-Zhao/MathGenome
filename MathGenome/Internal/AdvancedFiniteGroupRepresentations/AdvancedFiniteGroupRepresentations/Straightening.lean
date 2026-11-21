import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.GarnirRelations
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Straightening
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev standardPolytabloidSpan := @Specs.AdvancedFiniteGroupRepresentations.standardPolytabloidSpan

variable {n : ℕ} {p : Partition n}

/-- Row and column scores use the original positions of labels. Increasing
these scores is used only on the finite set of tableaux of a fixed shape. -/
def columnScore (t : Tableau p) : ℤ :=
  ∑ a : Fin n, (labelColumn t a : ℤ) * (a.val : ℤ)

def rowScore (t : Tableau p) : ℤ :=
  ∑ a : Fin n, (labelRow t a : ℤ) * (a.val : ℤ)

lemma columnScore_smul (g : SymmetricGroup n) (t : Tableau p) :
    columnScore (g • t) = ∑ a : Fin n, (labelColumn t a : ℤ) * ((g a).val : ℤ) := by
  unfold columnScore
  simpa using (Equiv.sum_comp g (fun a => (labelColumn (g • t) a : ℤ) * (a.val : ℤ))).symm

lemma rowScore_smul (g : SymmetricGroup n) (t : Tableau p) :
    rowScore (g • t) = ∑ a : Fin n, (labelRow t a : ℤ) * ((g a).val : ℤ) := by
  unfold rowScore
  simpa using (Equiv.sum_comp g (fun a => (labelRow (g • t) a : ℤ) * (a.val : ℤ))).symm

lemma columnScore_column (t : Tableau p) (g : columnSubgroup t) :
    columnScore (g.val • t) = columnScore t := by
  unfold columnScore
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun k : ℕ => (k : ℤ) * (a.val : ℤ))
    ((columnSubgroup t).inv_mem g.property a)

lemma sum_swap_mul (f : Fin n → ℤ) (a b : Fin n) (hab : a ≠ b) :
    (∑ x : Fin n, f x * ((Equiv.swap a b x).val : ℤ)) -
      (∑ x : Fin n, f x * (x.val : ℤ)) =
      (f b - f a) * ((a.val : ℤ) - (b.val : ℤ)) := by
  classical
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ x : Fin n,
      f x * ((Equiv.swap a b x).val : ℤ) - f x * (x.val : ℤ) =
        (if x = a then f a * ((b.val : ℤ) - (a.val : ℤ)) else 0) +
        (if x = b then f b * ((a.val : ℤ) - (b.val : ℤ)) else 0) := by
    intro x
    by_cases hxa : x = a
    · subst x; simp [hab]; ring
    by_cases hxb : x = b
    · subst x; simp [hab.symm]; ring
    · simp [Equiv.swap_apply_of_ne_of_ne hxa hxb, hxa, hxb]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- A column inversion can be corrected with its actual sign, preserving the
column score and strictly increasing the row score. -/
lemma column_inversion_step (t : Tableau p) (ht : ¬ ColumnIncreasing t) :
    ∃ g : columnSubgroup t, rowScore t < rowScore (g.val • t) := by
  classical
  simp only [ColumnIncreasing, Specs.AdvancedFiniteGroupRepresentations.ColumnIncreasing,
    not_forall] at ht
  obtain ⟨a, b, h⟩ := ht
  obtain ⟨hc, hr, hlabel⟩ := h
  have hab : a ≠ b := by intro heq; subst b; exact lt_irrefl _ hr
  have hba : t b < t a := lt_of_le_of_ne (le_of_not_gt hlabel) (t.injective.ne hab).symm
  let g : SymmetricGroup n := Equiv.swap (t a) (t b)
  have hg : g ∈ columnSubgroup t := by
    intro x
    by_cases hxa : x = t a
    · subst x; simpa [g] using hc.symm
    by_cases hxb : x = t b
    · subst x; simpa [g] using hc
    · rw [show g x = x from Equiv.swap_apply_of_ne_of_ne hxa hxb]
  refine ⟨⟨g,hg⟩, ?_⟩
  have hs := sum_swap_mul (fun x => (labelRow t x : ℤ)) (t a) (t b) (t.injective.ne hab)
  rw [← rowScore_smul g t] at hs
  change rowScore (g • t) - rowScore t = _ at hs
  have hrow : (labelRow t (t b) : ℤ) - (labelRow t (t a) : ℤ) > 0 := by
    simp only [labelRow_tableau]
    exact sub_pos.mpr (Int.ofNat_lt.mpr hr)
  have hl : ((t a).val : ℤ) - ((t b).val : ℤ) > 0 :=
    sub_pos.mpr (Int.ofNat_lt.mpr hba)
  have hpos := mul_pos hrow hl
  change rowScore t < rowScore (g • t)
  linarith

lemma columnIncreasing_le (t : Tableau p) (ht : ColumnIncreasing t)
    (a b : Cell p) (hc : a.val.2 = b.val.2) (hr : a.val.1 ≤ b.val.1) :
    t a ≤ t b := by
  rcases eq_or_lt_of_le hr with heq | hlt
  · have hab : a = b := Subtype.ext (Prod.ext heq hc)
    simp [hab]
  · exact (ht a b hc hlt).le

lemma garnir_separated (t : Tableau p) (ht : ColumnIncreasing t) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p)
    (hdes : t ⟨(i,j+1),hb⟩ < t ⟨(i,j),ha⟩) :
    (∀ a ∈ garnirA t i j, (t ⟨(i,j),ha⟩).val ≤ a.val) ∧
    (∀ b ∈ garnirB t i j, b.val < (t ⟨(i,j),ha⟩).val) := by
  constructor
  · intro a hA
    obtain ⟨hc,hr⟩ := (mem_garnirA t i j a).mp hA
    have h := columnIncreasing_le t ht ⟨(i,j),ha⟩ (t.symm a) hc.symm hr
    simpa using h
  · intro b hB
    obtain ⟨hc,hr⟩ := (mem_garnirB t i j b).mp hB
    have h := columnIncreasing_le t ht (t.symm b) ⟨(i,j+1),hb⟩ hc hr
    have h' : b ≤ t ⟨(i,j+1),hb⟩ := by simpa using h
    exact lt_of_le_of_lt h' hdes

/-- Every belt permutation either preserves the columns or strictly raises
the column score. The threshold lies strictly between the two belt parts.
This is a weighted-sum version of the source's decreasing column-word argument. -/
lemma garnir_score_step (t : Tableau p) (i j k : ℕ)
    (hA : ∀ a ∈ garnirA t i j, k ≤ a.val)
    (hB : ∀ b ∈ garnirB t i j, b.val < k)
    (g : labelPermutations (garnirA t i j ∪ garnirB t i j)) :
    g.val ∈ columnSubgroup t ∨ columnScore t < columnScore (g.val • t) := by
  classical
  let d : Fin n → ℤ := fun a =>
    (labelColumn (g.val • t) a : ℤ) - (labelColumn t a : ℤ)
  let w : Fin n → ℤ := fun a => 2 * (a.val : ℤ) - 2 * (k : ℤ) + 1
  have hcol : ∀ a ∈ garnirA t i j ∪ garnirB t i j,
      labelColumn t a = j ∨ labelColumn t a = j+1 := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Or.inl ((mem_garnirA t i j a).mp ha).1
    · exact Or.inr ((mem_garnirB t i j a).mp ha).1
  have hp : ∀ a : Fin n, 0 ≤ d a * w a ∧ (d a * w a = 0 → d a = 0) := by
    intro a
    by_cases ha : a ∈ garnirA t i j ∪ garnirB t i j
    · have hg : g.val⁻¹ a ∈ garnirA t i j ∪ garnirB t i j :=
        labelPermutations_mapsTo g⁻¹ ha
      have hc := hcol _ hg
      have hc' : labelColumn (g.val • t) a = j ∨
          labelColumn (g.val • t) a = j+1 := hc
      rcases Finset.mem_union.mp ha with ha | ha
      · have hc0 := ((mem_garnirA t i j a).mp ha).1
        have hd : 0 ≤ d a := by
          dsimp only [d]
          rcases hc' with hc' | hc' <;> rw [hc', hc0] <;> omega
        have hw : 0 < w a := by dsimp [w]; have := hA a ha; omega
        exact ⟨mul_nonneg hd hw.le, fun hz => (mul_eq_zero.mp hz).resolve_right (ne_of_gt hw)⟩
      · have hc0 := ((mem_garnirB t i j a).mp ha).1
        have hd : d a ≤ 0 := by
          dsimp only [d]
          rcases hc' with hc' | hc' <;> rw [hc', hc0] <;> omega
        have hw : w a < 0 := by dsimp [w]; have := hB a ha; omega
        exact ⟨mul_nonneg_of_nonpos_of_nonpos hd hw.le,
          fun hz => (mul_eq_zero.mp hz).resolve_right (ne_of_lt hw)⟩
    · have hfix : g.val⁻¹ a = a := (g⁻¹).property a ha
      have hd : d a = 0 := by dsimp only [d]; rw [labelColumn_smul, hfix]; omega
      simp [hd]
  have hdSum : ∑ a : Fin n, d a = 0 := by
    dsimp only [d]
    rw [Finset.sum_sub_distrib]
    have heq := Equiv.sum_comp g.val⁻¹ (fun a => (labelColumn t a : ℤ))
    change (∑ a, (labelColumn t (g.val⁻¹ a) : ℤ)) - _ = 0
    rw [heq, sub_self]
  have hsum : (∑ a : Fin n, d a * w a) =
      2 * (columnScore (g.val • t) - columnScore t) := by
    calc
      _ = ∑ a : Fin n, (2 * ((labelColumn (g.val • t) a : ℤ) * (a.val : ℤ) -
          (labelColumn t a : ℤ) * (a.val : ℤ)) - (2 * (k : ℤ) - 1) * d a) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp only [d, w]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hdSum,
          Finset.sum_sub_distrib]
        simp [columnScore]
  by_cases hs : columnScore t < columnScore (g.val • t)
  · exact Or.inr hs
  · left
    have hz : ∑ a : Fin n, d a * w a = 0 := by
      have hn := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) => (hp a).1)
      omega
    have hd0 : ∀ a, d a = 0 := by
      intro a
      have hle : d a * w a ≤ ∑ b : Fin n, d b * w b :=
        Finset.single_le_sum (fun b _ => (hp b).1) (Finset.mem_univ a)
      exact (hp a).2 (by rw [hz] at hle; exact le_antisymm hle (hp a).1)
    intro a
    have hh := hd0 (g.val a)
    dsimp only [d] at hh
    change (labelColumn t (g.val.symm (g.val a)) : ℤ) -
      (labelColumn t (g.val a) : ℤ) = 0 at hh
    rw [g.val.symm_apply_apply] at hh
    exact_mod_cast (sub_eq_zero.mp hh).symm

lemma rowIncreasing_of_adjacent (t : Tableau p)
    (h : ∀ (i j : ℕ) (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p),
      t ⟨(i,j),ha⟩ < t ⟨(i,j+1),hb⟩) : RowIncreasing t := by
  intro a b hr hc
  have go : ∀ (k : ℕ) (hk : (a.val.1,k) ∈ cells p),
      a.val.2 < k → t a < t ⟨(a.val.1,k),hk⟩ := by
    intro k
    induction k with
    | zero => intro hk hlt; omega
    | succ k ih =>
      intro hk hlt
      have hk' : (a.val.1,k) ∈ cells p :=
        (diagram p).isLowerSet (show (a.val.1,k) ≤ (a.val.1,k+1) from ⟨le_rfl, by omega⟩) hk
      by_cases heq : a.val.2 = k
      · have haeq : a = ⟨(a.val.1,k),hk'⟩ := Subtype.ext (Prod.ext rfl heq)
        exact lt_of_eq_of_lt (congrArg t haeq) (h a.val.1 k hk' hk)
      · exact (ih hk' (by omega)).trans (h a.val.1 k hk' hk)
  have hbm : (a.val.1,b.val.2) ∈ cells p := by simpa only [hr] using b.property
  have hbeq : (⟨(a.val.1,b.val.2),hbm⟩ : Cell p) = b := Subtype.ext (Prod.ext hr rfl)
  simpa only [hbeq] using go b.val.2 hbm hc

lemma exists_row_descent (t : Tableau p) (ht : ¬ RowIncreasing t) :
    ∃ (i j : ℕ) (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p),
      t ⟨(i,j+1),hb⟩ < t ⟨(i,j),ha⟩ := by
  classical
  by_contra hn
  apply ht
  apply rowIncreasing_of_adjacent t
  intro i j ha hb
  have hnot : ¬ t ⟨(i,j+1),hb⟩ < t ⟨(i,j),ha⟩ := fun hd => hn ⟨i,j,ha,hb,hd⟩
  have hne : t ⟨(i,j),ha⟩ ≠ t ⟨(i,j+1),hb⟩ := by
    intro heq
    have hh := congrArg (fun c : Cell p => c.val.2) (t.injective heq)
    dsimp at hh
    omega
  exact lt_of_le_of_ne (le_of_not_gt hnot) hne

/-- The full belt alternator isolates a nonzero multiple of e_t modulo S.
Column-preserving terms each contribute e_t; every other term has greater
column score. No special transversal is selected. -/
lemma garnir_span_step (S : Submodule ℂ (PermutationModule p)) (t : Tableau p)
    (ht : ColumnIncreasing t) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p)
    (hdes : t ⟨(i,j+1),hb⟩ < t ⟨(i,j),ha⟩)
    (hgreater : ∀ u : Tableau p, columnScore t < columnScore u → polytabloid u ∈ S) :
    polytabloid t ∈ S := by
  classical
  let G := labelPermutations (garnirA t i j ∪ garnirB t i j)
  let : Fintype G := Fintype.ofFinite G
  let Q : Finset G := Finset.univ.filter (fun g => g.val ∈ columnSubgroup t)
  have hQ : 0 < Q.card := by
    apply Finset.card_pos.mpr
    exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (columnSubgroup t).one_mem⟩⟩
  obtain ⟨hA,hB⟩ := garnir_separated t ht i j ha hb hdes
  have hterm : ∀ g : G,
      S.mkQ (permutationSign g.val • permutationRepresentation p g.val (polytabloid t)) =
        if g.val ∈ columnSubgroup t then S.mkQ (polytabloid t) else 0 := by
    intro g
    by_cases hg : g.val ∈ columnSubgroup t
    · rw [ite_eq_left hg, column_action_polytabloid t ⟨g.val,hg⟩,
        smul_smul, permutationSign_sq, one_smul]
    · rw [ite_eq_right hg, map_smul, polytabloid_equivariant]
      have hgt := (garnir_score_step t i j (t ⟨(i,j),ha⟩).val hA hB g).resolve_left hg
      have hmem := hgreater (g.val • t) hgt
      have hz : S.mkQ (polytabloid (g.val • t)) = 0 :=
        (Submodule.Quotient.mk_eq_zero S).mpr hmem
      rw [hz, smul_zero]
  have hzero := congrArg S.mkQ (garnir_full_sum_eq_zero t i j ha hb)
  change S.mkQ (∑ g : G,
    permutationSign g.val • permutationRepresentation p g.val (polytabloid t)) = S.mkQ 0 at hzero
  rw [map_sum, map_zero] at hzero
  simp_rw [hterm] at hzero
  have hscalar : (Q.card : ℂ) • S.mkQ (polytabloid t) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    simpa [Q, Finset.sum_ite] using hzero
  have hz : S.mkQ (polytabloid t) = 0 :=
    (smul_eq_zero.mp hscalar).resolve_left (by exact_mod_cast (Nat.ne_of_gt hQ))
  exact (Submodule.Quotient.mk_eq_zero S).mp hz

/-- FR-B02: every polytabloid is in the complex span of the standard ones.
The induction is over a strict relation on the finite set of all tableaux,
so there is no positivity assumption on n or on the diagram. -/
theorem polytabloid_straightening (t : Tableau p) :
    polytabloid t ∈ standardPolytabloidSpan p := by
  classical
  let r : Tableau p → Tableau p → Prop := fun u v =>
    columnScore v < columnScore u ∨
      columnScore u = columnScore v ∧ rowScore v < rowScore u
  let : IsTrans (Tableau p) r := ⟨by
    intro a b c hab hbc
    dsimp only [r] at *
    omega⟩
  let : Std.Irrefl r := ⟨by
    intro a
    dsimp only [r]
    omega⟩
  have hwf := Finite.wellFounded_of_trans_of_irrefl r
  induction t using hwf.induction with
  | h t ih =>
    by_cases hcol : ColumnIncreasing t
    · by_cases hrow : RowIncreasing t
      · exact Submodule.subset_span ⟨⟨t,hrow,hcol⟩,rfl⟩
      · obtain ⟨i,j,ha,hb,hdes⟩ := exists_row_descent t hrow
        apply garnir_span_step (standardPolytabloidSpan p) t hcol i j ha hb hdes
        intro u hu
        exact ih u (Or.inl hu)
    · obtain ⟨g,hg⟩ := column_inversion_step t hcol
      have hu : polytabloid (g.val • t) ∈ standardPolytabloidSpan p :=
        ih (g.val • t) (Or.inr ⟨columnScore_column t g,hg⟩)
      have hback : permutationSign g.val • polytabloid (g.val • t) = polytabloid t := by
        rw [polytabloid_column t g, smul_smul, permutationSign_sq, one_smul]
      rw [← hback]
      exact (standardPolytabloidSpan p).smul_mem _ hu

/-- Equality of the two spans, using the original Specht module definition. -/
theorem standardPolytabloids_span (p : Partition n) :
    standardPolytabloidSpan p = spechtSpan p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨u,rfl⟩
    exact polytabloid_mem_specht u.val
  · apply Submodule.span_le.mpr
    rintro v ⟨t,rfl⟩
    exact polytabloid_straightening t

/-- The finite linear combination stated in FR-B02, with complex coefficients. -/
theorem polytabloid_linearCombination (t : Tableau p) :
    ∃ (s : Finset (StandardTableau p)) (a : StandardTableau p → ℂ),
      polytabloid t = ∑ u ∈ s, a u • polytabloid u.val := by
  have hm := polytabloid_straightening t
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  exact ⟨c.support, c, hc.symm⟩

/-- The other conclusion of FR-B02 remains available with the full original
left-transversal and descent hypotheses. -/
theorem straightening_garnir_relation :
    Specs.AdvancedFiniteGroupRepresentations.garnir_relationType := @garnir_relation

end AdvancedFiniteGroupRepresentations
