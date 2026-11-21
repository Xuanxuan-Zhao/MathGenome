import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CharacteristicIsometry
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.MurnaghanNakayama
import Mathlib.GroupTheory.Perm.Fin

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace AdvancedFiniteGroupRepresentations

abbrev skewCells := @Specs.AdvancedFiniteGroupRepresentations.skewCells
abbrev CellAdjacent := Specs.AdvancedFiniteGroupRepresentations.CellAdjacent
abbrev EdgeConnected := Specs.AdvancedFiniteGroupRepresentations.EdgeConnected
abbrev NoSquare := Specs.AdvancedFiniteGroupRepresentations.NoSquare
abbrev IsBorderStrip := @Specs.AdvancedFiniteGroupRepresentations.IsBorderStrip
abbrev borderStripHeight := @Specs.AdvancedFiniteGroupRepresentations.borderStripHeight
abbrev spechtCharacterAtCycle := @Specs.AdvancedFiniteGroupRepresentations.spechtCharacterAtCycle
abbrev adjoinCycle := @Specs.AdvancedFiniteGroupRepresentations.adjoinCycle

/-- The definition in the independent Specs uses the actual inherited action. -/
theorem spechtCharacterAtCycle_eq_spechtCycleCharacter {n : ℕ} (lam nu : Partition n) :
    spechtCharacterAtCycle lam nu = spechtCycleCharacter lam nu := by
  let rho := Classical.epsilon
    (fun rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam) =>
      InheritedSpechtAction lam rho)
  have hrho : InheritedSpechtAction lam rho := Classical.epsilon_spec
    (specht_inheritedAction lam)
  change representationClassFunction rho (cycleClass nu) = _
  rw [representationClassFunction_cycleClass, inheritedSpechtAction_eq lam rho hrho]
  rfl

theorem spechtCharacterAtCycle_trace {n : ℕ} (lam nu : Partition n)
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (hrho : InheritedSpechtAction lam rho) (g : SymmetricGroup n)
    (hg : cyclePartition g = nu) :
    spechtCharacterAtCycle lam nu = rho.character g := by
  rw [spechtCharacterAtCycle_eq_spechtCycleCharacter, inheritedSpechtAction_eq lam rho hrho]
  exact character_eq_of_cyclePartition_eq _ _ _ ((cycleRepresentative_type nu).trans hg.symm)

theorem spechtCharacterAtCycle_empty :
    spechtCharacterAtCycle emptyPartition emptyPartition = 1 := by
  have h := frobenius_character_empty (spechtRepresentation emptyPartition)
    (fun _ _ => rfl) (cycleRepresentative emptyPartition)
  rw [spechtCharacterAtCycle_eq_spechtCycleCharacter]
  exact h.1.trans h.2

@[simp] theorem adjoinCycle_parts {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (tau : Partition (n - m)) :
    (adjoinCycle hm hmn tau).parts = m ::ₘ tau.parts := rfl

@[simp] theorem mem_skewCells {n k : ℕ} (lam : Partition n) (mu : Partition k)
    (i j : ℕ) :
    (i, j) ∈ skewCells lam mu ↔ rowLength mu i ≤ j ∧ j < rowLength lam i := by
  simp only [skewCells, Specs.AdvancedFiniteGroupRepresentations.skewCells,
    Finset.mem_sdiff, cell_iff, not_lt]
  exact and_comm

theorem skewCells_card {n k : ℕ} (lam : Partition n) (mu : Partition k)
    (h : cells mu ⊆ cells lam) : (skewCells lam mu).card = n - k := by
  change (cells lam \ cells mu).card = n - k
  rw [Finset.card_sdiff_of_subset h]
  change (diagram lam).card - (diagram mu).card = n - k
  rw [diagram_card, diagram_card]

theorem cellAdjacent_symm {a b : ℕ × ℕ} (h : CellAdjacent a b) : CellAdjacent b a := by
  rcases h with ⟨he, h | h⟩ | ⟨he, h | h⟩
  · exact Or.inl ⟨he.symm, Or.inr h⟩
  · exact Or.inl ⟨he.symm, Or.inl h⟩
  · exact Or.inr ⟨he.symm, Or.inr h⟩
  · exact Or.inr ⟨he.symm, Or.inl h⟩

theorem noSquare_skewCells_iff {n k : ℕ} (lam : Partition n) (mu : Partition k) :
    NoSquare (skewCells lam mu) ↔
      ∀ i : ℕ, rowLength lam (i + 1) ≤ rowLength mu i + 1 := by
  constructor
  · intro h i
    by_contra hi
    have hli : rowLength lam (i+1) ≤ rowLength lam i :=
      rowLength_antitone lam (Nat.le_succ i)
    have hmi : rowLength mu (i+1) ≤ rowLength mu i :=
      rowLength_antitone mu (Nat.le_succ i)
    exact h i (rowLength mu i) ⟨
      (mem_skewCells lam mu _ _).mpr ⟨le_refl _, by omega⟩,
      (mem_skewCells lam mu _ _).mpr ⟨hmi, by omega⟩,
      (mem_skewCells lam mu _ _).mpr ⟨by omega, by omega⟩,
      (mem_skewCells lam mu _ _).mpr ⟨by omega, by omega⟩⟩
  · intro h i j hs
    have htop := (mem_skewCells lam mu _ _).mp hs.1
    have hbottom := (mem_skewCells lam mu _ _).mp hs.2.2.2
    have hi := h i
    omega

/-- An edge path crossing a horizontal cut must use an edge across that cut. -/
theorem exists_vertical_pair_of_edgeConnected {s : Finset (ℕ × ℕ)}
    (hs : EdgeConnected s) {a b : ℕ × ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (i : ℕ) (hai : a.1 ≤ i) (hib : i < b.1) :
    ∃ j, (i, j) ∈ s ∧ (i + 1, j) ∈ s := by
  by_contra hn
  have hcut : ∀ j, ¬ ((i, j) ∈ s ∧ (i + 1, j) ∈ s) := by
    simpa only [not_exists] using hn
  have hle : ∀ {c}, Relation.ReflTransGen
      (fun a b => a ∈ s ∧ b ∈ s ∧ CellAdjacent a b) a c → c.1 ≤ i := by
    intro c hp
    induction hp with
    | refl => exact hai
    | @tail c d hpath hedge ih =>
      rcases hedge with ⟨hc, hd, he⟩
      rcases he with ⟨hr, _⟩ | ⟨hj, hv | hv⟩
      · omega
      · by_contra hdi
        have hci : c.1 = i := by omega
        have hdi : d.1 = i + 1 := by omega
        apply hcut c.2
        constructor
        · simpa only [← hci, Prod.mk.eta] using hc
        · have heq : (i + 1, c.2) = d := Prod.ext hdi.symm hj
          rwa [heq]
      · omega
  have := hle (hs a ha b hb)
  omega

/-- A nonempty skew row is precisely a strict inequality of row lengths. -/
theorem mem_skewRows {n k : ℕ} (lam : Partition n) (mu : Partition k) (i : ℕ) :
    i ∈ (skewCells lam mu).image Prod.fst ↔ rowLength mu i < rowLength lam i := by
  constructor
  · intro hi
    obtain ⟨⟨a,b⟩, hab, he⟩ := Finset.mem_image.mp hi
    change a = i at he
    subst a
    have h := (mem_skewCells lam mu i b).mp hab
    omega
  · intro h
    exact Finset.mem_image.mpr ⟨(i, rowLength mu i),
      (mem_skewCells lam mu _ _).mpr ⟨le_rfl, h⟩, rfl⟩

theorem rowLength_le_of_cells_subset {n k : ℕ} (lam : Partition n) (mu : Partition k)
    (h : cells mu ⊆ cells lam) (i : ℕ) : rowLength mu i ≤ rowLength lam i := by
  by_contra hi
  have hc : (i, rowLength lam i) ∈ cells mu := (cell_iff mu _ _).mpr (by omega)
  have := (cell_iff lam _ _).mp (h hc)
  omega

/-- Successive occupied rows of a border strip meet in exactly one column. -/
theorem borderStrip_adjacent_rows {n k : ℕ} (lam : Partition n) (mu : Partition k)
    (h : IsBorderStrip lam mu) {a b : ℕ × ℕ}
    (ha : a ∈ skewCells lam mu) (hb : b ∈ skewCells lam mu)
    (i : ℕ) (hai : a.1 ≤ i) (hib : i < b.1) :
    rowLength lam (i+1) = rowLength mu i + 1 := by
  obtain ⟨j, hj, hj'⟩ := exists_vertical_pair_of_edgeConnected h.2.2.1 ha hb i hai hib
  have hm := (mem_skewCells lam mu i j).mp hj
  have hl := (mem_skewCells lam mu (i+1) j).mp hj'
  have hs := (noSquare_skewCells_iff lam mu).mp h.2.2.2 i
  omega

/-- Edge paths with both endpoints constrained to the finite diagram. -/
def CellPath (s : Finset (ℕ × ℕ)) (a b : ℕ × ℕ) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ s ∧ b ∈ s ∧ CellAdjacent a b) a b

theorem CellPath.symm {s : Finset (ℕ × ℕ)} {a b : ℕ × ℕ}
    (h : CellPath s a b) : CellPath s b a := by
  induction h with
  | refl => exact .refl
  | tail _ he ih =>
    exact (Relation.ReflTransGen.single ⟨he.2.1, he.1, cellAdjacent_symm he.2.2⟩).trans ih

/-- Every skew row is an interval of columns, including when it has one cell. -/
theorem skewCells_horizontal_path {n k : ℕ} (lam : Partition n) (mu : Partition k)
    (i a b : ℕ) (ha : (i,a) ∈ skewCells lam mu) (hb : (i,b) ∈ skewCells lam mu) :
    CellPath (skewCells lam mu) (i,a) (i,b) := by
  have hright : ∀ a b : ℕ, a ≤ b →
      (i,a) ∈ skewCells lam mu → (i,b) ∈ skewCells lam mu →
      CellPath (skewCells lam mu) (i,a) (i,b) := by
    intro a b hab hma hmb
    induction b, hab using Nat.le_induction with
    | base => exact .refl
    | succ b hab ih =>
      have hc : (i,b) ∈ skewCells lam mu := by
        have h1 := (mem_skewCells lam mu i a).mp hma
        have h2 := (mem_skewCells lam mu i (b+1)).mp hmb
        exact (mem_skewCells lam mu i b).mpr ⟨by omega, by omega⟩
      exact (ih hc).tail ⟨hc, hmb, Or.inl ⟨rfl, Or.inl rfl⟩⟩
  rcases le_total a b with hab | hba
  · exact hright a b hab ha hb
  · exact (hright b a hba hb ha).symm

/-- The explicit row description of moving a single shifted exponent from row
`j` to row `i`. This is a combinatorial condition, with no character assumed. -/
def BorderStripRows {n k : ℕ} (lam : Partition n) (mu : Partition k) (i j : ℕ) : Prop :=
  i ≤ j ∧ rowLength mu i < rowLength lam i ∧
    (∀ t, t < i ∨ j < t → rowLength lam t = rowLength mu t) ∧
    (∀ t, i < t → t ≤ j → rowLength lam t = rowLength mu (t-1) + 1)

/-- The occupied rows in the row description are exactly the closed interval. -/
theorem BorderStripRows.occupied_iff {n k : ℕ} {lam : Partition n} {mu : Partition k}
    {i j : ℕ} (h : BorderStripRows lam mu i j) (t : ℕ) :
    rowLength mu t < rowLength lam t ↔ i ≤ t ∧ t ≤ j := by
  constructor
  · intro ht
    constructor
    · by_contra hh
      have := h.2.2.1 t (Or.inl (by omega))
      omega
    · by_contra hh
      have := h.2.2.1 t (Or.inr (by omega))
      omega
  · rintro ⟨hit, htj⟩
    rcases hit.eq_or_lt with he | he
    · simpa only [← he] using h.2.1
    · have hm : rowLength mu t ≤ rowLength mu (t-1) :=
        rowLength_antitone mu (by omega)
      rw [h.2.2.2 t he htj]
      omega

theorem BorderStripRows.skewRows {n k : ℕ} {lam : Partition n} {mu : Partition k}
    {i j : ℕ} (h : BorderStripRows lam mu i j) :
    (skewCells lam mu).image Prod.fst = Finset.Icc i j := by
  ext t
  rw [mem_skewRows, Finset.mem_Icc, h.occupied_iff]

theorem BorderStripRows.height {n k : ℕ} {lam : Partition n} {mu : Partition k}
    {i j : ℕ} (h : BorderStripRows lam mu i j) : borderStripHeight lam mu = j-i := by
  change ((skewCells lam mu).image Prod.fst).card - 1 = _
  rw [h.skewRows, Nat.card_Icc]
  omega

/-- Exact one-column overlaps produce paths and exclude every square. -/
theorem BorderStripRows.isBorderStrip {n k : ℕ} {lam : Partition n} {mu : Partition k}
    {i j : ℕ} (h : BorderStripRows lam mu i j) : IsBorderStrip lam mu := by
  have hle (t : ℕ) : rowLength mu t ≤ rowLength lam t := by
    by_cases ht : i ≤ t ∧ t ≤ j
    · exact (h.occupied_iff t |>.mpr ht).le
    · have := h.2.2.1 t (by omega)
      omega
  have hcell : (i, rowLength mu i) ∈ skewCells lam mu :=
    (mem_skewCells lam mu _ _).mpr ⟨le_rfl, h.2.1⟩
  refine ⟨?_, ⟨_, hcell⟩, ?_, ?_⟩
  · rintro ⟨t,q⟩ htq
    exact (cell_iff lam t q).mpr (lt_of_lt_of_le ((cell_iff mu t q).mp htq) (hle t))
  · have paths : ∀ t, i ≤ t → t ≤ j → ∀ q, (t,q) ∈ skewCells lam mu →
        CellPath (skewCells lam mu) (i, rowLength mu i) (t,q) := by
      intro t hit
      induction t, hit using Nat.le_induction with
      | base =>
        intro _ q hq
        exact skewCells_horizontal_path lam mu i _ _ hcell hq
      | succ t hit ih =>
        intro htj q hq
        have hprev : (t, rowLength mu t) ∈ skewCells lam mu :=
          (mem_skewCells lam mu _ _).mpr ⟨le_rfl,
            (h.occupied_iff t).mpr ⟨hit, by omega⟩⟩
        have hnext : (t+1, rowLength mu t) ∈ skewCells lam mu := by
          apply (mem_skewCells lam mu _ _).mpr
          constructor
          · exact rowLength_antitone mu (by omega)
          · rw [h.2.2.2 (t+1) (by omega) htj, Nat.add_sub_cancel]
            omega
        exact ((ih (by omega) _ hprev).tail
          ⟨hprev, hnext, Or.inr ⟨rfl, Or.inl rfl⟩⟩).trans
          (skewCells_horizontal_path lam mu (t+1) _ _ hnext hq)
    rintro ⟨a,p⟩ ha ⟨b,q⟩ hb
    have ha' := (h.occupied_iff a).mp ((mem_skewRows lam mu a).mp
      (Finset.mem_image.mpr ⟨(a,p), ha, rfl⟩))
    have hb' := (h.occupied_iff b).mp ((mem_skewRows lam mu b).mp
      (Finset.mem_image.mpr ⟨(b,q), hb, rfl⟩))
    exact (paths a ha'.1 ha'.2 p ha).symm.trans (paths b hb'.1 hb'.2 q hb)
  · apply (noSquare_skewCells_iff lam mu).mpr
    intro t
    by_cases ht : i ≤ t ∧ t < j
    · rw [h.2.2.2 (t+1) (by omega) (by omega), Nat.add_sub_cancel]
    · by_cases htj : j ≤ t
      · have he := h.2.2.1 (t+1) (Or.inr (by omega))
        have hm : rowLength mu (t+1) ≤ rowLength mu t :=
          rowLength_antitone mu (by omega)
        omega
      · have he := h.2.2.1 t (Or.inl (by omega))
        have hl : rowLength lam (t+1) ≤ rowLength lam t :=
          rowLength_antitone lam (by omega)
        omega

/-- Extract the top and bottom occupied rows from an arbitrary geometric strip. -/
theorem exists_borderStripRows {n k : ℕ} (lam : Partition n) (mu : Partition k)
    (h : IsBorderStrip lam mu) : ∃ i j, BorderStripRows lam mu i j := by
  let rows := (skewCells lam mu).image Prod.fst
  have hrows : rows.Nonempty := h.2.1.image _
  let i := rows.min' hrows
  let j := rows.max' hrows
  have hi : i ∈ rows := Finset.min'_mem rows hrows
  have hj : j ∈ rows := Finset.max'_mem rows hrows
  have hmin : ∀ t ∈ rows, i ≤ t := fun t ht => Finset.min'_le rows t ht
  have hmax : ∀ t ∈ rows, t ≤ j := fun t ht => Finset.le_max' rows t ht
  obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp hi
  obtain ⟨b, hb, hbj⟩ := Finset.mem_image.mp hj
  change a.1 = i at hai
  change b.1 = j at hbj
  refine ⟨i, j, hmin j hj, (mem_skewRows lam mu i).mp hi, ?_, ?_⟩
  · intro t ht
    have hn : t ∉ rows := by
      intro hm
      have := hmin t hm
      have := hmax t hm
      omega
    have hh : ¬ rowLength mu t < rowLength lam t := by
      rwa [← mem_skewRows]
    have := rowLength_le_of_cells_subset lam mu h.1 t
    omega
  · intro t hit htj
    have he := borderStrip_adjacent_rows lam mu h ha hb (t-1) (by omega) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using he

theorem isBorderStrip_iff_exists_rows {n k : ℕ} (lam : Partition n) (mu : Partition k) :
    IsBorderStrip lam mu ↔ ∃ i j, BorderStripRows lam mu i j := by
  exact ⟨exists_borderStripRows lam mu, fun ⟨_, _, h⟩ => h.isBorderStrip⟩

/-- Both endpoints, and consequently the height, are intrinsic to the strip. -/
theorem BorderStripRows.unique {n k : ℕ} {lam : Partition n} {mu : Partition k}
    {i j i' j' : ℕ} (h : BorderStripRows lam mu i j)
    (h' : BorderStripRows lam mu i' j') : i = i' ∧ j = j' := by
  have h1 := (h'.occupied_iff i).mp h.2.1
  have h2 := (h.occupied_iff i').mp h'.2.1
  have h3 := (h'.occupied_iff j).mp ((h.occupied_iff j).mpr ⟨h.1, le_rfl⟩)
  have h4 := (h.occupied_iff j').mp ((h'.occupied_iff j').mpr ⟨h'.1, le_rfl⟩)
  omega

/-- Sorting a list with one changed entry preserves the order of all other
entries. Its restriction to the complement of that entry is canonical. -/
theorem exponentMove_complement {r m : ℕ} (a b : Fin (r+1) → ℕ)
    (ha : StrictAnti a) (hb : StrictAnti b) (j : Fin (r+1))
    (sigma : Equiv.Perm (Fin (r+1)))
    (hmove : Function.update b j (b j + m) = fun t => a (sigma t)) :
    (fun t : Fin r => sigma (j.succAbove t)) = (sigma j).succAbove := by
  have he (t : Fin r) : b (j.succAbove t) = a (sigma (j.succAbove t)) := by
    have := congrFun hmove (j.succAbove t)
    simpa only [Function.update_of_ne (Fin.succAbove_ne j t)] using this
  have hmono : StrictMono (fun t : Fin r => sigma (j.succAbove t)) := by
    intro x y hxy
    have hlt := hb (Fin.strictMono_succAbove j hxy)
    rw [he, he] at hlt
    exact ha.lt_iff_gt.mp hlt
  have hrange : Set.range (fun t : Fin r => sigma (j.succAbove t)) =
      Set.range (sigma j).succAbove := by
    rw [Fin.range_succAbove]
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, rfl⟩
      exact sigma.injective.ne (Fin.succAbove_ne j t)
    · intro hx
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq
        (show sigma.symm x ≠ j from fun hh => hx (by simpa [hh] using sigma.apply_symm_apply x |>.symm))
      exact ⟨t, by rw [ht, sigma.apply_symm_apply]⟩
  exact hmono.range_inj_of_wellFoundedLT (Fin.strictMono_succAbove (sigma j)) |>.mp hrange

/-- Raising an exponent moves it weakly upwards, and its sorting permutation
is the cycle through exactly the crossed positions. -/
theorem exponentMove_sorting {r m : ℕ} (a b : Fin (r+1) → ℕ)
    (ha : StrictAnti a) (hb : StrictAnti b) (hm : 0 < m) (j : Fin (r+1))
    (sigma : Equiv.Perm (Fin (r+1)))
    (hmove : Function.update b j (b j + m) = fun t => a (sigma t)) :
    sigma j ≤ j ∧ sigma = Fin.cycleIcc (sigma j) j := by
  have hc := exponentMove_complement a b ha hb j sigma hmove
  have htop : b j + m = a (sigma j) := by
    simpa only [Function.update_self] using congrFun hmove j
  have hij : sigma j ≤ j := by
    by_contra hh
    have hji : j < sigma j := lt_of_not_ge hh
    have hjr : j.val < r := by have := (sigma j).isLt; change j.val < (sigma j).val at hji; omega
    let t : Fin r := ⟨j.val, hjr⟩
    have hjt : j ≤ t.castSucc := by rfl
    have hit : t.castSucc < sigma j := hji
    have he := congrFun hc t
    rw [Fin.succAbove_of_le_castSucc j t hjt,
      Fin.succAbove_of_castSucc_lt (sigma j) t hit] at he
    have hnext : t.succ ≠ j := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_succ] at hv
      change j.val + 1 = j.val at hv
      omega
    have hbnext := hb (show j < t.succ by change j.val < j.val + 1; omega)
    have hnextval := congrFun hmove t.succ
    rw [Function.update_of_ne hnext, he] at hnextval
    have heq : t.castSucc = j := Fin.ext rfl
    rw [heq] at hnextval
    have halt := ha hji
    omega
  refine ⟨hij, ?_⟩
  apply Equiv.ext
  intro t
  by_cases ht : t = j
  · subst t
    rw [Fin.cycleIcc_of_last hij]
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq ht
    exact (congrFun hc q).trans (congrFun (Fin.cycleIcc_comp_succAbove (sigma j) j hij) q).symm

/-- A matching raised-exponent monomial has precisely the border-strip rows. -/
theorem borderStripRows_of_exponentMove {n k r m : ℕ}
    (lam : Partition n) (mu : Partition k) (hlam : length lam ≤ r+1)
    (hmu : length mu ≤ r+1) (hm : 0 < m) (j : Fin (r+1))
    (sigma : Equiv.Perm (Fin (r+1)))
    (hmove : Function.update (shiftedPartition (r+1) mu) j
      (shiftedPartition (r+1) mu j + m) = fun t => shiftedPartition (r+1) lam (sigma t)) :
    BorderStripRows lam mu (sigma j).val j.val := by
  obtain ⟨hij, hsigma⟩ := exponentMove_sorting _ _
    (shiftedPartition_strictAnti lam) (shiftedPartition_strictAnti mu) hm j sigma hmove
  let i := sigma j
  have hi : i ≤ j := hij
  have hfixed (t : Fin (r+1)) (ht : t < i ∨ j < t) : rowLength lam t.val = rowLength mu t.val := by
    have hst : sigma t = t := by
      rw [hsigma]
      rcases ht with ht | ht
      · exact Fin.cycleIcc_of_lt ht
      · exact Fin.cycleIcc_of_gt ht
    have htj : t ≠ j := by rcases ht with ht | ht <;> omega
    have he := congrFun hmove t
    rw [Function.update_of_ne htj, hst] at he
    exact (Nat.add_right_cancel he).symm
  have hsuccessor (t : Fin (r+1)) (hit : i ≤ t) (htj : t < j) :
      rowLength lam (t.val+1) = rowLength mu t.val + 1 := by
    have htj' : t ≠ j := ne_of_lt htj
    have hst : sigma t = t + 1 := by rw [hsigma]; exact Fin.cycleIcc_of_ge_of_lt hit htj
    have he := congrFun hmove t
    rw [Function.update_of_ne htj', hst] at he
    have hval : (t+1).val = t.val+1 := Fin.val_add_one_of_lt (by
      change t.val < r
      have := j.isLt
      change t.val < j.val at htj
      omega)
    change rowLength mu t.val + ((r+1)-1-t.val) =
      rowLength lam (t+1).val + ((r+1)-1-(t+1).val) at he
    rw [hval] at he
    have := t.isLt
    have := j.isLt
    change t.val < j.val at htj
    omega
  refine ⟨hij, ?_, ?_, ?_⟩
  · change rowLength mu i.val < rowLength lam i.val
    by_cases heq : i = j
    · have he := congrFun hmove j
      rw [Function.update_self] at he
      change shiftedPartition (r+1) mu j + m = shiftedPartition (r+1) lam i at he
      rw [heq] at he
      change rowLength mu j.val + _ + m = rowLength lam j.val + _ at he
      change rowLength mu i.val < rowLength lam i.val
      rw [heq]
      omega
    · have hit : i < j := lt_of_le_of_ne hi heq
      have he := hsuccessor i le_rfl hit
      have hl : rowLength lam (i.val+1) ≤ rowLength lam i.val := rowLength_antitone lam (by omega)
      omega
  · intro t ht
    by_cases htr : t < r+1
    · exact hfixed ⟨t,htr⟩ (by rcases ht with ht | ht <;> [left; right] <;> exact ht)
    · rw [rowLength_zero_of_length_le lam t (by omega), rowLength_zero_of_length_le mu t (by omega)]
  · intro t hit htj
    have htr : t-1 < r+1 := by have := j.isLt; omega
    have he := hsuccessor ⟨t-1,htr⟩ (by change i.val ≤ t-1; omega) (by change t-1 < j.val; omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using he

/-- The bottom occupied row lies within any alphabet containing the shape. -/
theorem BorderStripRows.bottom_lt {n k : ℕ} {lam : Partition n} {mu : Partition k}
    {i j : ℕ} (h : BorderStripRows lam mu i j) : j < length lam := by
  have hpos := (h.occupied_iff j).mpr ⟨h.1, le_rfl⟩
  by_contra hn
  rw [rowLength_zero_of_length_le lam j (by omega)] at hpos
  omega

/-- The total degree recovers the raised top exponent from the remaining rows. -/
theorem exponentMove_of_borderStripRows {n k r m : ℕ}
    (lam : Partition n) (mu : Partition k) (hsize : n = k + m)
    (hlam : length lam ≤ r+1) (hmu : length mu ≤ r+1)
    (i j : Fin (r+1)) (h : BorderStripRows lam mu i.val j.val) :
    Function.update (shiftedPartition (r+1) mu) j
      (shiftedPartition (r+1) mu j + m) =
        fun t => shiftedPartition (r+1) lam (Fin.cycleIcc i j t) := by
  let a := shiftedPartition (r+1) lam
  let b := shiftedPartition (r+1) mu
  let sigma := Fin.cycleIcc i j
  have hnon (t : Fin (r+1)) (htj : t ≠ j) : b t = a (sigma t) := by
    rcases lt_or_ge t i with hti | hit
    · have hs : sigma t = t := Fin.cycleIcc_of_lt hti
      have he := h.2.2.1 t.val (Or.inl hti)
      change rowLength mu t.val + _ = rowLength lam (sigma t).val + _
      rw [hs, he]
    · rcases lt_or_gt_of_ne htj with htj | hjt
      · have hs : sigma t = t+1 := Fin.cycleIcc_of_ge_of_lt hit htj
        have hval : (t+1).val = t.val+1 := Fin.val_add_one_of_lt (by
          change t.val < r
          have := j.isLt
          change t.val < j.val at htj
          omega)
        have he := h.2.2.2 (t.val+1) (by change i.val ≤ t.val at hit; omega)
          (by change t.val < j.val at htj; omega)
        rw [Nat.add_sub_cancel] at he
        change rowLength mu t.val + ((r+1)-1-t.val) =
          rowLength lam (sigma t).val + ((r+1)-1-(sigma t).val)
        rw [hs, hval, he]
        have := j.isLt
        change t.val < j.val at htj
        omega
      · have hs : sigma t = t := Fin.cycleIcc_of_gt hjt
        have he := h.2.2.1 t.val (Or.inr hjt)
        change rowLength mu t.val + _ = rowLength lam (sigma t).val + _
        rw [hs, he]
  have hsum : (∑ t, a (sigma t)) = (∑ t, b t) + m := by
    rw [Equiv.sum_comp sigma a]
    change (∑ t, shiftedPartition (r+1) lam t) =
      (∑ t, shiftedPartition (r+1) mu t) + m
    rw [sum_shiftedPartition lam hlam, sum_shiftedPartition mu hmu, hsize]
    omega
  have hsumoff : (∑ t ∈ Finset.univ.erase j, a (sigma t)) =
      ∑ t ∈ Finset.univ.erase j, b t := by
    apply Finset.sum_congr rfl
    intro t ht
    exact (hnon t (Finset.ne_of_mem_erase ht)).symm
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j), hsumoff] at hsum
  funext t
  by_cases ht : t = j
  · subst t
    rw [Function.update_self]
    change b j + m = a (sigma j)
    omega
  · rw [Function.update_of_ne ht]
    exact hnon t ht

/-- The two orientations of the monomial matching condition are equivalent. -/
theorem exponentMove_iff {r m : ℕ} (a b : Fin r → ℕ)
    (j : Fin r) (sigma : Equiv.Perm (Fin r)) :
    (fun t => Function.update b j (b j+m) (sigma.symm t)) = a ↔
      Function.update b j (b j+m) = fun t => a (sigma t) := by
  constructor
  · intro h
    funext t
    simpa only [Equiv.symm_apply_apply] using congrFun h (sigma t)
  · intro h
    funext t
    simpa only [Equiv.apply_symm_apply] using congrFun h (sigma.symm t)

/-- The sorting permutation is unique whenever the target exponents are distinct. -/
theorem exponentMove_perm_unique {r m : ℕ} (a b : Fin r → ℕ)
    (ha : Function.Injective a) (j : Fin r) (sigma tau : Equiv.Perm (Fin r))
    (hsigma : Function.update b j (b j+m) = fun t => a (sigma t))
    (htau : Function.update b j (b j+m) = fun t => a (tau t)) : sigma = tau := by
  apply Equiv.ext
  intro t
  exact ha ((congrFun hsigma t).symm.trans (congrFun htau t))

private theorem sign_pow_smul_complex (d : ℕ) :
    ((-1 : ℤˣ)^d) • (1 : ℂ) = (-1 : ℂ)^d := by
  induction d with
  | zero => simp
  | succ d ih => simp [pow_succ, ih, Units.neg_smul]

/-- The source product by cycle multiplicities is also the product over parts. -/
theorem partitionPowerSum_eq_multiset_prod {n : ℕ} (r : ℕ) (nu : Partition n) :
    partitionPowerSum r nu = (nu.parts.map (powerSum r)).prod := by
  exact (Finset.prod_multiset_map_count nu.parts (powerSum r)).symm

theorem partitionPowerSum_adjoinCycle {n m : ℕ} (r : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) (tau : Partition (n-m)) :
    partitionPowerSum r (adjoinCycle hm hmn tau) = powerSum r m * partitionPowerSum r tau := by
  simp only [partitionPowerSum_eq_multiset_prod, adjoinCycle_parts,
    Multiset.map_cons, Multiset.prod_cons]

/-- Multiplication by p_m raises precisely one column exponent before alternation. -/
theorem powerSum_mul_alternant {r : ℕ} (m : ℕ) (b : Fin r → ℕ) :
    powerSum r m * alternant b =
      ∑ j : Fin r, alternant (Function.update b j (b j + m)) := by
  classical
  simp only [alternant, Specs.AdvancedFiniteGroupRepresentations.alternant, Matrix.det_apply]
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [← Finset.smul_sum, mul_smul_comm]
  congr 1
  change powerSum r m * (∏ i : Fin r, MvPolynomial.X (sigma i) ^ b i) = _
  have hp : powerSum r m = ∑ j : Fin r, (MvPolynomial.X (sigma j) : Alphabet r) ^ m := by
    exact (Fintype.sum_equiv sigma _ _ (fun _ => rfl)).symm
  rw [hp, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have he : ∏ i : Fin r, (MvPolynomial.X (sigma i) : Alphabet r) ^
      Function.update b j (b j + m) i =
      MvPolynomial.X (sigma j) ^ (b j + m) *
        ∏ i ∈ Finset.univ.erase j, MvPolynomial.X (sigma i) ^ b i := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  change _ = ∏ i : Fin r, (MvPolynomial.X (sigma i) : Alphabet r) ^
    Function.update b j (b j + m) i
  rw [he, pow_add]
  ring

/-- A coefficient form of the raw exponent-raising identity, with every sign
still supplied by the literal determinant permutation. -/
theorem naturalCoefficient_powerSum_mul_alternant {r : ℕ} (m : ℕ)
    (a b : Fin r → ℕ) :
    naturalCoefficient a (powerSum r m * alternant b) =
      ∑ j : Fin r, ∑ sigma : Equiv.Perm (Fin r),
        if (fun i => Function.update b j (b j + m) (sigma.symm i)) = a then
          Equiv.Perm.sign sigma • (1 : ℂ) else 0 := by
  rw [powerSum_mul_alternant]
  change (∑ j : Fin r, alternant (Function.update b j (b j + m))).coeff _ = _
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [alternant_eq_sum_monomial, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
  have he : Finsupp.equivFunOnFinite.symm
      (fun i => Function.update b j (b j + m) (sigma.symm i)) =
      Finsupp.equivFunOnFinite.symm a ↔
      (fun i => Function.update b j (b j + m) (sigma.symm i)) = a :=
    Finsupp.equivFunOnFinite.symm.injective.eq_iff
  simp only [he]
  split_ifs <;> simp

/-- The signed determinant coefficient is exactly the geometric border-strip
indicator. Alphabet bounds are only proof parameters and do not restrict strips. -/
theorem naturalCoefficient_borderStrip {n k r m : ℕ}
    (lam : Partition n) (mu : Partition k) (hsize : n = k+m) (hm : 0 < m)
    (hlam : length lam ≤ r+1) (hmu : length mu ≤ r+1) :
    naturalCoefficient (shiftedPartition (r+1) lam)
      (powerSum (r+1) m * partitionAlternant (r+1) mu) =
      if IsBorderStrip lam mu then (-1 : ℂ)^borderStripHeight lam mu else 0 := by
  change naturalCoefficient (shiftedPartition (r+1) lam)
    (powerSum (r+1) m * alternant (shiftedPartition (r+1) mu)) = _
  rw [naturalCoefficient_powerSum_mul_alternant]
  by_cases hb : IsBorderStrip lam mu
  · rw [ite_eq_left hb]
    obtain ⟨it, jt, hrows⟩ := exists_borderStripRows lam mu hb
    let i : Fin (r+1) := ⟨it, lt_of_le_of_lt hrows.1 (hrows.bottom_lt.trans_le hlam)⟩
    let j : Fin (r+1) := ⟨jt, hrows.bottom_lt.trans_le hlam⟩
    have hrows' : BorderStripRows lam mu i.val j.val := hrows
    let sigma := Fin.cycleIcc i j
    have hmove := exponentMove_of_borderStripRows lam mu hsize hlam hmu i j hrows'
    have hmatch := (exponentMove_iff (shiftedPartition (r+1) lam)
      (shiftedPartition (r+1) mu) j sigma).mpr hmove
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single sigma]
      · rw [ite_eq_left hmatch]
        change Equiv.Perm.sign (Fin.cycleIcc i j) • (1 : ℂ) = _
        have hij : i ≤ j := hrows.1
        rw [Fin.sign_cycleIcc_of_le hij, sign_pow_smul_complex, hrows'.height]
      · intro tau _ htau
        split_ifs with hmatching
        · have hmovetau := (exponentMove_iff (shiftedPartition (r+1) lam)
            (shiftedPartition (r+1) mu) j tau).mp hmatching
          exact (htau (exponentMove_perm_unique _ _ (shiftedPartition_strictAnti lam).injective
            j tau sigma hmovetau hmove)).elim
        · rfl
      · simp
    · intro j' _ hj'
      apply Finset.sum_eq_zero
      intro tau _
      split_ifs with hmatching
      · have hmovetau := (exponentMove_iff (shiftedPartition (r+1) lam)
          (shiftedPartition (r+1) mu) j' tau).mp hmatching
        have hrowstau := borderStripRows_of_exponentMove lam mu hlam hmu hm j' tau hmovetau
        exact (hj' (Fin.ext (hrowstau.unique hrows').2)).elim
      · rfl
    · simp
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro sigma _
    split_ifs with hmatching
    · have hmove := (exponentMove_iff (shiftedPartition (r+1) lam)
        (shiftedPartition (r+1) mu) j sigma).mp hmatching
      exact (hb (borderStripRows_of_exponentMove lam mu hlam hmu hm j sigma hmove).isBorderStrip).elim
    · rfl

/-- Power sums expanded in the Schur basis, obtained using the accepted
coefficient uniqueness theorem, rather than postulating a character expansion. -/
theorem partitionPowerSum_schur_expansion {n r : ℕ} (nu : Partition n) (hr : n ≤ r) :
    partitionPowerSum r nu = ∑ mu : Partition n,
      frobeniusCoefficient r mu nu • schurPolynomial mu r := by
  classical
  let Q : Alphabet r := ∑ mu : Partition n,
    frobeniusCoefficient r mu nu • schurPolynomial mu r
  have hlen (mu : Partition n) : length mu ≤ r := (partition_length_le_size mu).trans hr
  have hQsym : Q.IsSymmetric := by
    apply (MvPolynomial.symmetricSubalgebra (Fin r) ℂ).sum_mem
    intro mu _
    exact (schurPolynomial_isSymmetric mu r).smul _
  have hQhom : Q.IsHomogeneous n := by
    apply MvPolynomial.IsHomogeneous.sum
    intro mu _
    rw [MvPolynomial.smul_eq_C_mul]
    exact (schurPolynomial_isHomogeneous mu r).C_mul _
  have hprod : vandermonde r * Q = ∑ mu : Partition n,
      frobeniusCoefficient r mu nu • partitionAlternant r mu := by
    dsimp only [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mu _
    rw [mul_smul_comm, schurPolynomial_characterization mu r (hlen mu)]
  apply sub_eq_zero.mp
  apply eq_zero_of_alternating_coefficients_zero
    (partitionPowerSum r nu - Q)
    (((partitionPowerSum_mem_stableDegree nu).2 r).1.sub hQsym)
    ((partitionPowerSum_isHomogeneous r nu).sub hQhom)
  intro lam
  have hc : naturalCoefficient (shiftedPartition r lam) (vandermonde r * Q) =
      frobeniusCoefficient r lam nu := by
    rw [hprod]
    change (∑ mu : Partition n,
      frobeniusCoefficient r mu nu • partitionAlternant r mu).coeff _ = _
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul]
    change (∑ mu : Partition n, frobeniusCoefficient r mu nu *
      naturalCoefficient (shiftedPartition r lam) (alternant (shiftedPartition r mu))) = _
    simp_rw [naturalCoefficient_alternant _ _ (shiftedPartition_strictAnti lam)
      (shiftedPartition_strictAnti _)]
    have he (mu : Partition n) : shiftedPartition r lam = shiftedPartition r mu ↔ lam = mu :=
      ⟨fun hh => partition_eq_of_diagram_eq lam mu
        (diagram_eq_of_shiftedPartition_eq lam mu (hlen lam) (hlen mu) hh),
        fun hh => congrArg (shiftedPartition r) hh⟩
    simp [he]
  change (vandermonde r * (partitionPowerSum r nu - Q)).coeff _ = 0
  rw [mul_sub, MvPolynomial.coeff_sub]
  change frobeniusCoefficient r lam nu -
    naturalCoefficient (shiftedPartition r lam) (vandermonde r * Q) = 0
  rw [hc, sub_self]

/-- The corresponding alternating expansion used by the deletion proof. -/
theorem vandermonde_mul_partitionPowerSum_expansion {n r : ℕ}
    (nu : Partition n) (hr : n ≤ r) :
    vandermonde r * partitionPowerSum r nu = ∑ mu : Partition n,
      frobeniusCoefficient r mu nu • partitionAlternant r mu := by
  rw [partitionPowerSum_schur_expansion nu hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [mul_smul_comm, schurPolynomial_characterization mu r
    ((partition_length_le_size mu).trans hr)]

/-- The algebraic character recurrence, whose coefficients are evaluated by
`naturalCoefficient_borderStrip` in the final deletion rule. -/
theorem spechtCharacterAtCycle_adjoinCycle {n m : ℕ} (hm : 0 < m)
    (hmn : m ≤ n) (lam : Partition n) (tau : Partition (n-m))
    (r : ℕ) (hr : 1 ≤ r) (hn : n ≤ r) :
    spechtCharacterAtCycle lam (adjoinCycle hm hmn tau) =
      ∑ mu : Partition (n-m),
        naturalCoefficient (shiftedPartition r lam)
          (powerSum r m * partitionAlternant r mu) * spechtCharacterAtCycle mu tau := by
  have hk : n - m ≤ r := (Nat.sub_le _ _).trans hn
  have hc : frobeniusCoefficient r lam (adjoinCycle hm hmn tau) =
      ∑ mu : Partition (n-m), frobeniusCoefficient r mu tau *
        naturalCoefficient (shiftedPartition r lam)
          (powerSum r m * partitionAlternant r mu) := by
    change naturalCoefficient (shiftedPartition r lam)
      (vandermonde r * partitionPowerSum r (adjoinCycle hm hmn tau)) = _
    rw [partitionPowerSum_adjoinCycle]
    have he : vandermonde r * (powerSum r m * partitionPowerSum r tau) =
        powerSum r m * (vandermonde r * partitionPowerSum r tau) := by ring
    rw [he, vandermonde_mul_partitionPowerSum_expansion tau hk, Finset.mul_sum]
    simp_rw [mul_smul_comm]
    change (∑ mu : Partition (n-m), frobeniusCoefficient r mu tau •
      (powerSum r m * partitionAlternant r mu)).coeff _ = _
    rw [MvPolynomial.coeff_sum]
    rfl
  simp_rw [spechtCharacterAtCycle_eq_spechtCycleCharacter]
  rw [← frobeniusCoefficient_eq_spechtCycleCharacter r hr hn]
  simp_rw [← frobeniusCoefficient_eq_spechtCycleCharacter r hr hk]
  rw [hc]
  apply Finset.sum_congr rfl
  intro mu _
  exact mul_comm _ _

/-- Murnaghan--Nakayama for the actual Specht trace, including deletion to the
empty partition. The sign counts every occupied row of the geometric strip. -/
theorem murnaghan_nakayama {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (lam : Partition n) (tau : Partition (n-m)) :
    spechtCharacterAtCycle lam (adjoinCycle hm hmn tau) =
      ∑ mu : Partition (n-m),
        if IsBorderStrip lam mu ∧ (skewCells lam mu).card = m then
          (-1 : ℂ)^borderStripHeight lam mu * spechtCharacterAtCycle mu tau else 0 := by
  rw [spechtCharacterAtCycle_adjoinCycle hm hmn lam tau (n+1) (by omega) (by omega)]
  apply Finset.sum_congr rfl
  intro mu _
  rw [naturalCoefficient_borderStrip lam mu (by omega) hm
    ((partition_length_le_size lam).trans (by omega))
    ((partition_length_le_size mu).trans (by omega))]
  by_cases hb : IsBorderStrip lam mu
  · have hcard : (skewCells lam mu).card = m := by
      rw [skewCells_card lam mu hb.1]
      omega
    rw [ite_eq_left hb, ite_eq_left ⟨hb, hcard⟩]
  · rw [ite_eq_right hb, ite_eq_right (fun h => hb h.1), zero_mul]

end AdvancedFiniteGroupRepresentations
