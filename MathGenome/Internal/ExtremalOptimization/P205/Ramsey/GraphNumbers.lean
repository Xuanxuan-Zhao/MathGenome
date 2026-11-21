import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.GraphNumbers
import MathGenome.Internal.ExtremalOptimization.P205.Ramsey.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases

universe u v

namespace P205.Ramsey

noncomputable def ramseyNumber : ℕ → ℕ → ℕ := Specs.ramseyNumberValue

/-- The specified-color predicates recover exactly the canonical homogeneity
predicate when the color is existentially quantified. -/
theorem homogeneous_iff_coloredClique {X : Type*} (c : KSubsets X 2 → Fin 2)
    (t : Finset X) : Homogeneous c (↑t : Set X) ↔ ∃ d, ColoredClique c d t := by
  rfl

theorem ColoredClique.mono {X : Type*} {c : KSubsets X 2 → Fin 2}
    {d : Fin 2} {s t : Finset X} (h : ColoredClique c d t) (hst : s ⊆ t) :
    ColoredClique c d s := fun e he => h e (he.trans hst)

theorem graph_ramsey_exists : Specs.GraphRamseyExists := by
  classical
  intro a b ha hb
  obtain ⟨n, hmn, hn⟩ := finite_ramsey 2 2 (max a b) (by omega) (by omega) (by omega)
  refine ⟨n, by omega, ?_⟩
  intro X S hS c
  obtain ⟨t, htS, htm, d, hd⟩ := hn X S hS c
  have hcl : ColoredClique c d t := hd
  fin_cases d
  · obtain ⟨q, hqt, hqa⟩ := Finset.exists_subset_card_eq (show a ≤ t.card by omega)
    exact Or.inl ⟨q, hqt.trans htS, hqa, hcl.mono hqt⟩
  · obtain ⟨q, hqt, hqb⟩ := Finset.exists_subset_card_eq (show b ≤ t.card by omega)
    exact Or.inr ⟨q, hqt.trans htS, hqb, hcl.mono hqt⟩

theorem graph_ramsey_mono : Specs.GraphRamseyMono := by
  classical
  intro a b n N hn hle X S hS c
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show n ≤ S.card by omega)
  rcases hn X T hT c with ⟨t, ht, hcard, hc⟩ | ⟨t, ht, hcard, hc⟩
  · exact Or.inl ⟨t, ht.trans hTS, hcard, hc⟩
  · exact Or.inr ⟨t, ht.trans hTS, hcard, hc⟩

/-- Transport a clique along an injection of its ground set. -/
theorem ColoredClique.map {X : Type u} {Y : Type v}
    (f : X ↪ Y) (c : KSubsets Y 2 → Fin 2) (d : Fin 2) (t : Finset X)
    (h : ColoredClique (fun s => c ⟨s.val.map f, by simpa using s.property⟩) d t) :
    ColoredClique c d (t.map f) := by
  intro s hs
  obtain ⟨q, hqt, hsq⟩ := Finset.subset_map_iff.mp hs
  have hq : q.card = 2 := by
    simpa only [hsq, Finset.card_map] using s.property
  have heq : (⟨q.map f, by simpa using hq⟩ : KSubsets Y 2) = s :=
    Subtype.ext hsq.symm
  simpa only [heq] using h ⟨q, hq⟩ hqt

/-- A universe-independent interpretation of the finite graph Ramsey property. -/
theorem GraphRamseyProperty.on_finset {a b n : ℕ} (h : GraphRamseyProperty a b n)
    (X : Type u) (S : Finset X) (hS : S.card = n) (c : KSubsets X 2 → Fin 2) :
    (∃ t : Finset X, t ⊆ S ∧ t.card = a ∧ ColoredClique c 0 t) ∨
    (∃ t : Finset X, t ⊆ S ∧ t.card = b ∧ ColoredClique c 1 t) := by
  classical
  let e : Fin n ≃ S := (S.equivFinOfCardEq hS).symm
  let f : Fin n ↪ X := e.toEmbedding.trans (Function.Embedding.subtype _)
  let d : KSubsets (Fin n) 2 → Fin 2 :=
    fun s => c ⟨s.val.map f, by simpa using s.property⟩
  have hmap (t : Finset (Fin n)) : t.map f ⊆ S := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e y).property
  rcases h (Fin n) Finset.univ (by simp) d with
    ⟨t, _, hta, htc⟩ | ⟨t, _, htb, htc⟩
  · exact Or.inl ⟨t.map f, hmap t, by simpa using hta, htc.map f c 0 t⟩
  · exact Or.inr ⟨t.map f, hmap t, by simpa using htb, htc.map f c 1 t⟩

theorem ramsey_number_spec : Specs.RamseyNumberSpec := by
  intro a b ha hb
  exact csInf_mem (graph_ramsey_exists a b ha hb)

theorem ramsey_number_least : Specs.RamseyNumberLeast := by
  intro a b n hn hp
  exact csInf_le' (show n ∈ {n | 0 < n ∧ GraphRamseyProperty a b n} from ⟨hn, hp⟩)

theorem ramsey_number_threshold : Specs.RamseyNumberThreshold := by
  intro a b n ha hb hn
  exact ⟨fun h => ramsey_number_least a b n hn h,
    fun h => graph_ramsey_mono a b _ n (ramsey_number_spec a b ha hb).2 h⟩

theorem ramsey_number_on : Specs.RamseyNumberOn.{u} := by
  intro a b ha hb X S hS c
  have h := graph_ramsey_mono a b _ S.card (ramsey_number_spec a b ha hb).2 hS
  exact h.on_finset X S rfl c

private theorem coloredClique_singleton {X : Type*} (c : KSubsets X 2 → Fin 2)
    (d : Fin 2) (x : X) : ColoredClique c d {x} := by
  intro s hs
  have := Finset.card_le_card hs
  simp only [Finset.card_singleton, s.property] at this
  omega

theorem ramsey_number_one_left : Specs.RamseyNumberOneLeft := by
  classical
  intro b hb
  apply Nat.le_antisymm
  · apply ramsey_number_least 1 b 1 (by omega)
    intro X S hS c
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hS
    exact Or.inl ⟨{x}, by rw [hx], by simp, coloredClique_singleton c 0 x⟩
  · have := (ramsey_number_spec 1 b (by omega) hb).1
    omega

theorem ramsey_number_one_right : Specs.RamseyNumberOneRight := by
  classical
  intro a ha
  apply Nat.le_antisymm
  · apply ramsey_number_least a 1 1 (by omega)
    intro X S hS c
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hS
    exact Or.inr ⟨{x}, by rw [hx], by simp, coloredClique_singleton c 1 x⟩
  · have := (ramsey_number_spec a 1 ha (by omega)).1
    omega

private noncomputable def pairColor {X : Type*} (c : KSubsets X 2 → Fin 2)
    (x y : X) : Fin 2 := by
  classical
  exact if h : x ≠ y then c ⟨{x, y}, by simp [h]⟩ else 0

private theorem pairColor_symm {X : Type*} (c : KSubsets X 2 → Fin 2)
    (x y : X) : pairColor c x y = pairColor c y x := by
  classical
  by_cases h : x = y
  · subst y; rfl
  · simp only [pairColor, dite_eq_left h, dite_eq_left (Ne.symm h)]
    congr 1
    exact Subtype.ext (Finset.pair_comm x y)

private theorem coloredClique_insert {X : Type*} [DecidableEq X] {c : KSubsets X 2 → Fin 2}
    {d : Fin 2} {t : Finset X} {x : X} (ht : ColoredClique c d t)
    (hx : ∀ y ∈ t, pairColor c x y = d) : ColoredClique c d (insert x t) := by
  classical
  intro s hs
  obtain ⟨p, q, hpq, hpqs⟩ := Finset.card_eq_two.mp s.property
  have hp : p ∈ insert x t := hs (by simp [hpqs])
  have hq : q ∈ insert x t := hs (by simp [hpqs])
  have hedge : c s = pairColor c p q := by
    simp only [pairColor, dite_eq_left hpq]
    congr 1
    apply Subtype.ext
    ext z
    simp [hpqs]
  by_cases hpx : p = x
  · subst p
    rw [hedge]
    exact hx q ((Finset.mem_insert.mp hq).resolve_left (Ne.symm hpq))
  by_cases hqx : q = x
  · subst q
    rw [hedge, pairColor_symm]
    exact hx p ((Finset.mem_insert.mp hp).resolve_left hpq)
  · apply ht s
    rw [hpqs]
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro ((Finset.mem_insert.mp hp).resolve_left hpx)
       ((Finset.mem_insert.mp hq).resolve_left hqx)

/-- The two neighbor classes have total size one less than the ground set.
One class therefore meets the corresponding smaller Ramsey threshold. -/
theorem ramsey_number_recursion : Specs.RamseyNumberRecursion := by
  classical
  intro a b ha hb
  let u := ramseyNumber (a - 1) b
  let v := ramseyNumber a (b - 1)
  have hu := ramsey_number_spec (a - 1) b (by omega) (by omega)
  have hv := ramsey_number_spec a (b - 1) (by omega) (by omega)
  change 0 < u ∧ GraphRamseyProperty (a - 1) b u at hu
  change 0 < v ∧ GraphRamseyProperty a (b - 1) v at hv
  apply ramsey_number_least a b (u + v) (by omega)
  intro X S hS c
  obtain ⟨x, hxS⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  let T := S.erase x
  let A := T.filter (fun y => pairColor c x y = 0)
  let B := T.filter (fun y => ¬ pairColor c x y = 0)
  have hAB : A.card + B.card = u + v - 1 := by
    rw [Finset.card_filter_add_card_filter_not]
    exact (Finset.card_erase_of_mem hxS).trans (by omega)
  have hAS : A ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hBS : B ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hxA : x ∉ A := by simp [A, T]
  have hxB : x ∉ B := by simp [B, T]
  by_cases hAu : u ≤ A.card
  · rcases graph_ramsey_mono (a - 1) b u A.card hu.2 hAu X A rfl c with
      ⟨t, htA, hta, htc⟩ | ⟨t, htA, htb, htc⟩
    · refine Or.inl ⟨insert x t, Finset.insert_subset hxS (htA.trans hAS), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun h => hxA (htA h)), hta]
        omega
      · exact coloredClique_insert htc (fun y hy => (Finset.mem_filter.mp (htA hy)).2)
    · exact Or.inr ⟨t, htA.trans hAS, htb, htc⟩
  · have hvB : v ≤ B.card := by omega
    rcases graph_ramsey_mono a (b - 1) v B.card hv.2 hvB X B rfl c with
      ⟨t, htB, hta, htc⟩ | ⟨t, htB, htb, htc⟩
    · exact Or.inl ⟨t, htB.trans hBS, hta, htc⟩
    · refine Or.inr ⟨insert x t, Finset.insert_subset hxS (htB.trans hBS), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun h => hxB (htB h)), htb]
        omega
      · apply coloredClique_insert htc
        intro y hy
        have hn := (Finset.mem_filter.mp (htB hy)).2
        have hc := (pairColor c x y).isLt
        apply Fin.ext
        have hne : (pairColor c x y).val ≠ 0 := by
          intro hz
          exact hn (Fin.ext hz)
        simp only [Fin.val_one]
        omega

/-- Pascal's identity and the boundary values give the classical binomial bound. -/
theorem ramsey_number_binomial : Specs.RamseyNumberBinomial := by
  have bound : ∀ i j : ℕ, Specs.ramseyNumberValue (i + 1) (j + 1) ≤
      Nat.choose (i + j) i := by
    intro i
    induction i with
    | zero =>
      intro j
      rw [Nat.zero_add, ramsey_number_one_left (j + 1) (by omega)]
      simp
    | succ i hi =>
      intro j
      induction j with
      | zero =>
        rw [Nat.zero_add, ramsey_number_one_right (i + 1 + 1) (by omega)]
        simp
      | succ j hj =>
        have hrec := ramsey_number_recursion (i + 1 + 1) (j + 1 + 1) (by omega) (by omega)
        have hia := hi (j + 1)
        have hja := hj
        simp only [Nat.add_sub_cancel] at hrec
        calc
          Specs.ramseyNumberValue (i + 1 + 1) (j + 1 + 1) ≤
              Specs.ramseyNumberValue (i + 1) (j + 1 + 1) +
              Specs.ramseyNumberValue (i + 1 + 1) (j + 1) := hrec
          _ ≤ Nat.choose (i + (j + 1)) i + Nat.choose ((i + 1) + j) (i + 1) :=
            Nat.add_le_add hia hja
          _ = Nat.choose ((i + 1) + (j + 1)) (i + 1) := by
            simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using (Nat.choose_succ_succ (i + j + 1) i).symm
  intro a b ha hb
  have h := bound (a - 1) (b - 1)
  simpa only [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb,
    show a - 1 + (b - 1) = a + b - 2 by omega] using h

end P205.Ramsey
