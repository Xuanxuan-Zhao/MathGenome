import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtModules
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StandardTableaux
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.GarnirRelations
import Mathlib.Data.Finset.Card

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations
abbrev labelPermutations := @Specs.AdvancedFiniteGroupRepresentations.labelPermutations
abbrev garnirA := @Specs.AdvancedFiniteGroupRepresentations.garnirA
abbrev garnirB := @Specs.AdvancedFiniteGroupRepresentations.garnirB
abbrev garnirSubgroup := @Specs.AdvancedFiniteGroupRepresentations.garnirSubgroup
abbrev IsLeftTransversal := @Specs.AdvancedFiniteGroupRepresentations.IsLeftTransversal

variable {n : ℕ} {p : Partition n}

@[simp] theorem mem_garnirA (t : Tableau p) (i j : ℕ) (a : Fin n) :
    a ∈ garnirA t i j ↔ labelColumn t a = j ∧ i ≤ labelRow t a := by
  simp [garnirA, Specs.AdvancedFiniteGroupRepresentations.garnirA]

@[simp] theorem mem_garnirB (t : Tableau p) (i j : ℕ) (a : Fin n) :
    a ∈ garnirB t i j ↔ labelColumn t a = j+1 ∧ labelRow t a ≤ i := by
  simp [garnirB, Specs.AdvancedFiniteGroupRepresentations.garnirB]

theorem labelPermutations_mono {U V : Finset (Fin n)} (h : U ⊆ V) :
    labelPermutations U ≤ labelPermutations V := by
  intro g hg a ha
  exact hg a (fun hU => ha (h hU))

theorem labelPermutations_mapsTo {U : Finset (Fin n)} (g : labelPermutations U)
    {a : Fin n} (ha : a ∈ U) : g.val a ∈ U := by
  by_contra hn
  have hfix := g.property (g.val a) hn
  have heq := g.val.injective hfix
  exact hn (heq.symm ▸ ha)

theorem labelPermutations_column {U : Finset (Fin n)} (t : Tableau p) (j : ℕ)
    (hU : ∀ a ∈ U, labelColumn t a = j) : labelPermutations U ≤ columnSubgroup t := by
  intro g hg a
  by_cases ha : a ∈ U
  · exact (hU _ (labelPermutations_mapsTo ⟨g,hg⟩ ha)).trans (hU a ha).symm
  · rw [hg a ha]

theorem garnirSubgroup_le_column (t : Tableau p) (i j : ℕ) :
    garnirSubgroup t i j ≤ columnSubgroup t := by
  apply sup_le
  · exact labelPermutations_column t j (fun a ha => (mem_garnirA t i j a).mp ha |>.1)
  · exact labelPermutations_column t (j+1) (fun a ha => (mem_garnirB t i j a).mp ha |>.1)

theorem garnirSubgroup_le_union (t : Tableau p) (i j : ℕ) :
    garnirSubgroup t i j ≤ labelPermutations (garnirA t i j ∪ garnirB t i j) := by
  exact sup_le (labelPermutations_mono Finset.subset_union_left)
    (labelPermutations_mono Finset.subset_union_right)

@[simp] theorem labelRow_tableau (t : Tableau p) (a : Cell p) :
    labelRow t (t a) = a.val.1 := by
  change (t.symm (t a)).val.1 = _
  simp

@[simp] theorem labelColumn_tableau (t : Tableau p) (a : Cell p) :
    labelColumn t (t a) = a.val.2 := by
  change (t.symm (t a)).val.2 = _
  simp

theorem labelRow_lt_columnLength (t : Tableau p) (a : Fin n) :
    labelRow t a < columnLength p (labelColumn t a) :=
  (cell_iff_column p _ _).mp (t.symm a).property

theorem label_coordinates_injective (t : Tableau p) {a b : Fin n}
    (hr : labelRow t a = labelRow t b) (hc : labelColumn t a = labelColumn t b) : a = b := by
  apply t.symm.injective
  exact Subtype.ext (Prod.ext hr hc)

theorem garnirA_card (t : Tableau p) (i j : ℕ) :
    (garnirA t i j).card = columnLength p j - i := by
  classical
  calc
    _ = (Finset.Ico i (columnLength p j)).card := by
      apply Finset.card_bij (fun a _ => labelRow t a)
      · intro a ha
        obtain ⟨hc,hr⟩ := (mem_garnirA t i j a).mp ha
        exact Finset.mem_Ico.mpr ⟨hr, hc ▸ labelRow_lt_columnLength t a⟩
      · intro a ha b hb heq
        exact label_coordinates_injective t heq
          (((mem_garnirA t i j a).mp ha).1.trans ((mem_garnirA t i j b).mp hb).1.symm)
      · intro r hr
        obtain ⟨hri,hrp⟩ := Finset.mem_Ico.mp hr
        let c : Cell p := ⟨(r,j), (cell_iff_column p r j).mpr hrp⟩
        refine ⟨t c, ?_, ?_⟩
        · rw [mem_garnirA, labelColumn_tableau, labelRow_tableau]
          exact ⟨rfl,hri⟩
        · exact labelRow_tableau t c
    _ = _ := Nat.card_Ico _ _

theorem garnirB_card (t : Tableau p) (i j : ℕ) (hb : (i,j+1) ∈ cells p) :
    (garnirB t i j).card = i+1 := by
  classical
  calc
    _ = (Finset.range (i+1)).card := by
      apply Finset.card_bij (fun a _ => labelRow t a)
      · intro a ha
        exact Finset.mem_range.mpr (by have := ((mem_garnirB t i j a).mp ha).2; omega)
      · intro a ha b hb heq
        exact label_coordinates_injective t heq
          (((mem_garnirB t i j a).mp ha).1.trans ((mem_garnirB t i j b).mp hb).1.symm)
      · intro r hr
        have hri : r ≤ i := by have := Finset.mem_range.mp hr; omega
        have hip := (cell_iff_column p i (j+1)).mp hb
        let c : Cell p := ⟨(r,j+1), (cell_iff_column p r (j+1)).mpr (by omega)⟩
        refine ⟨t c, ?_, ?_⟩
        · rw [mem_garnirB, labelColumn_tableau, labelRow_tableau]
          exact ⟨rfl,hri⟩
        · exact labelRow_tableau t c
    _ = _ := Finset.card_range _

theorem garnir_disjoint (t : Tableau p) (i j : ℕ) :
    Disjoint (garnirA t i j) (garnirB t i j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have := ((mem_garnirA t i j a).mp ha).1
  have := ((mem_garnirB t i j a).mp hb).1
  omega

/-- Permutations on disjoint label sets have disjoint supports. -/
theorem labelPermutations_disjoint {A B : Finset (Fin n)} (hd : Disjoint A B)
    (a : labelPermutations A) (b : labelPermutations B) : Equiv.Perm.Disjoint a.val b.val := by
  intro x
  by_cases ha : x ∈ A
  · exact Or.inr (b.property x (fun hb => Finset.disjoint_left.mp hd ha hb))
  · exact Or.inl (a.property x ha)

/-- For disjoint label sets the generated subgroup is their internal direct
product, under the actual multiplication of permutations. -/
theorem labelPermutations_product (A B : Finset (Fin n)) (hd : Disjoint A B) :
    ∃ e : (labelPermutations A × labelPermutations B) ≃*
        ↥(labelPermutations A ⊔ labelPermutations B),
      ∀ x, (e x).val = x.1.val * x.2.val := by
  let f : (labelPermutations A × labelPermutations B) →*
      ↥(labelPermutations A ⊔ labelPermutations B) :=
    { toFun := fun x => ⟨x.1.val * x.2.val, Subgroup.mul_mem_sup x.1.property x.2.property⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact ((labelPermutations_disjoint hd y.1 x.2).symm.commute.mul_mul_mul_comm
          x.1.val y.2.val).symm }
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hmul : x.1.val * x.2.val = 1 := congrArg Subtype.val hx
    obtain ⟨ha,hb⟩ := (labelPermutations_disjoint hd x.1 x.2).mul_eq_one_iff.mp hmul
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  let f' := (labelPermutations A ⊔ labelPermutations B).subtype.comp f
  have hle : labelPermutations A ⊔ labelPermutations B ≤ f'.range := by
    apply sup_le
    · intro a ha
      exact ⟨(⟨a,ha⟩,1), by simp [f',f]⟩
    · intro b hb
      exact ⟨(1,⟨b,hb⟩), by simp [f',f]⟩
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨x,hx⟩ := hle g.property
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj,hsurj⟩, fun _ => rfl⟩

/-- Identification with the source subgroup S_A × S_B. -/
theorem garnirSubgroup_product (t : Tableau p) (i j : ℕ) :
    ∃ e : (labelPermutations (garnirA t i j) × labelPermutations (garnirB t i j)) ≃*
        garnirSubgroup t i j,
      ∀ x, (e x).val = x.1.val * x.2.val :=
  labelPermutations_product _ _ (garnir_disjoint t i j)

theorem garnir_union_card (t : Tableau p) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p) :
    (garnirA t i j ∪ garnirB t i j).card = columnLength p j + 1 := by
  rw [Finset.card_union_of_disjoint (garnir_disjoint t i j), garnirA_card, garnirB_card t i j hb]
  have := (cell_iff_column p i j).mp ha
  omega

theorem garnir_row_collision (t : Tableau p) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p) (c : columnSubgroup t) :
    ∃ a ∈ garnirA t i j ∪ garnirB t i j,
      ∃ b ∈ garnirA t i j ∪ garnirB t i j,
        a ≠ b ∧ labelRow (c.val • t) a = labelRow (c.val • t) b := by
  classical
  have hcard : (Finset.range (columnLength p j)).card <
      (garnirA t i j ∪ garnirB t i j).card := by
    rw [Finset.card_range, garnir_union_card t i j ha hb]
    omega
  apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
  intro a hU
  have hc : labelColumn (c.val • t) a = labelColumn t a := by
    exact (columnSubgroup t).inv_mem c.property a
  have hr := labelRow_lt_columnLength (c.val • t) a
  rw [hc] at hr
  apply Finset.mem_range.mpr
  rcases Finset.mem_union.mp hU with hA | hB
  · rwa [((mem_garnirA t i j a).mp hA).1] at hr
  · rw [((mem_garnirB t i j a).mp hB).1] at hr
    have hh : columnLength p (j+1) ≤ columnLength p j :=
      (diagram p).colLen_anti j (j+1) (by omega)
    omega

attribute [local instance] Fintype.ofFinite

/-- The alternating sum of the action over a finite subgroup. -/
def signedActionSum (G : Subgroup (SymmetricGroup n)) (v : PermutationModule p) :
    PermutationModule p :=
  ∑ g : G, permutationSign g.val • permutationRepresentation p g.val v

theorem swap_mem_labelPermutations {U : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ U) (hb : b ∈ U) : Equiv.swap a b ∈ labelPermutations U := by
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb))

theorem swap_mem_rowSubgroup (t : Tableau p) {a b : Fin n}
    (hr : labelRow t a = labelRow t b) : Equiv.swap a b ∈ rowSubgroup t := by
  intro x
  by_cases hxa : x = a
  · subst x
    simpa using hr.symm
  by_cases hxb : x = b
  · subst x
    simpa using hr
  · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

@[simp] theorem permutationSign_swap {a b : Fin n} (hab : a ≠ b) :
    permutationSign (Equiv.swap a b) = -1 := by
  simp [permutationSign, Specs.AdvancedFiniteGroupRepresentations.permutationSign,
    Equiv.Perm.sign_swap hab]

/-- An odd element fixing a vector forces its full alternating sum to vanish. -/
theorem signedActionSum_eq_zero_of_odd_stabilizer (G : Subgroup (SymmetricGroup n))
    (v : PermutationModule p) (τ : G)
    (hτ : permutationSign τ.val = -1)
    (hfix : permutationRepresentation p τ.val v = v) : signedActionSum G v = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have heq : signedActionSum G v = -signedActionSum G v := by
    unfold signedActionSum
    rw [← Finset.sum_neg_distrib]
    apply Fintype.sum_equiv (Equiv.mulRight τ)
    intro g
    change permutationSign g.val • permutationRepresentation p g.val v =
      -(permutationSign (g.val * τ.val) • permutationRepresentation p (g.val * τ.val) v)
    rw [permutationSign_mul, hτ, map_mul, Module.End.mul_apply, hfix]
    simp
  have htwo : (2 : ℂ) • signedActionSum G v = 0 := by
    rw [two_smul]
    calc
      _ = -signedActionSum G v + signedActionSum G v := congrArg (· + signedActionSum G v) heq
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem signedActionSum_basis_eq_zero (U : Finset (Fin n)) (u : Tableau p)
    {a b : Fin n} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (hr : labelRow u a = labelRow u b) (z : ℂ) :
    signedActionSum (labelPermutations U) (MonoidAlgebra.single (tabloid u) z) = 0 := by
  classical
  apply signedActionSum_eq_zero_of_odd_stabilizer _ _
    ⟨Equiv.swap a b, swap_mem_labelPermutations ha hb⟩
  · exact permutationSign_swap hab
  · rw [permutationRepresentation_basis]
    have hfix : Equiv.swap a b • tabloid u = tabloid u := by
      rw [← MulAction.mem_stabilizer_iff, tabloid_stabilizer]
      exact swap_mem_rowSubgroup u hr
    rw [hfix]

theorem garnir_full_sum_eq_zero (t : Tableau p) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p) :
    signedActionSum (labelPermutations (garnirA t i j ∪ garnirB t i j)) (polytabloid t) = 0 := by
  classical
  rw [polytabloid_sum]
  unfold signedActionSum
  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  obtain ⟨a,hA,b,hB,hab,hr⟩ := garnir_row_collision t i j ha hb c
  exact signedActionSum_basis_eq_zero _ _ hA hB hab hr _

/-- The multiplication map of an arbitrary left transversal is a bijection. -/
def leftFactorizationEquiv (G H : Subgroup (SymmetricGroup n)) (hHG : H ≤ G)
    (P : Finset (SymmetricGroup n)) (hP : IsLeftTransversal G H P) :
    ({π // π ∈ P} × H) ≃ G := by
  let f : ({π // π ∈ P} × H) → G := fun x =>
    ⟨x.1.val * x.2.val, G.mul_mem (hP.1 x.1.val x.1.property) (hHG x.2.property)⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    obtain ⟨z,hz,huniq⟩ := hP.2 (f x)
    exact (huniq x rfl).trans (huniq y (congrArg Subtype.val hxy.symm)).symm
  · intro g
    obtain ⟨x,hx,_⟩ := hP.2 g
    exact ⟨x, Subtype.ext hx⟩

@[simp] theorem leftFactorizationEquiv_apply_val
    (G H : Subgroup (SymmetricGroup n)) (hHG : H ≤ G)
    (P : Finset (SymmetricGroup n)) (hP : IsLeftTransversal G H P)
    (x : {π // π ∈ P} × H) :
    (leftFactorizationEquiv G H hHG P hP x).val = x.1.val * x.2.val := rfl

/-- Factor the full alternating sum with the representatives on the left. -/
theorem signedActionSum_left_factorization (G H : Subgroup (SymmetricGroup n))
    (hHG : H ≤ G) (P : Finset (SymmetricGroup n)) (hP : IsLeftTransversal G H P)
    (v : PermutationModule p) :
    signedActionSum G v = ∑ π ∈ P,
      permutationSign π • permutationRepresentation p π (signedActionSum H v) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let : Fintype {π // π ∈ P} := Fintype.ofFinite _
  let e := leftFactorizationEquiv G H hHG P hP
  calc
    _ = ∑ x : {π // π ∈ P} × H,
        permutationSign (x.1.val * x.2.val) •
          permutationRepresentation p (x.1.val * x.2.val) v := by
      unfold signedActionSum
      exact (Fintype.sum_equiv e _ _ (fun x => rfl)).symm
    _ = ∑ π : {π // π ∈ P},
        permutationSign π.val • permutationRepresentation p π.val (signedActionSum H v) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro π _
      unfold signedActionSum
      rw [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [permutationSign_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]
    _ = _ := (Finset.sum_subtype (F := Fintype.ofFinite {π // π ∈ P}) P (fun _ => Iff.rfl)
      (fun π => permutationSign π • permutationRepresentation p π (signedActionSum H v))).symm

/-- Each signed H-term is the same vector when H lies in the column group. -/
theorem signedActionSum_polytabloid (t : Tableau p) (H : Subgroup (SymmetricGroup n))
    (hH : H ≤ columnSubgroup t) :
    signedActionSum H (polytabloid t) = (Fintype.card H : ℂ) • polytabloid t := by
  classical
  let : Fintype H := Fintype.ofFinite H
  unfold signedActionSum
  have heq : ∀ h : H,
      permutationSign h.val • permutationRepresentation p h.val (polytabloid t) = polytabloid t := by
    intro h
    rw [column_action_polytabloid t ⟨h.val,hH h.property⟩, smul_smul,
      permutationSign_sq, one_smul]
  simp only [heq, Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

/-- The belt relation holds even without the ordering hypotheses. -/
theorem garnir_relation_general (t : Tableau p) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p)
    (P : Finset (SymmetricGroup n))
    (hP : IsLeftTransversal
      (labelPermutations (garnirA t i j ∪ garnirB t i j))
      (garnirSubgroup t i j) P) :
    ∑ π ∈ P, permutationSign π • polytabloid (π • t) = 0 := by
  classical
  let H := garnirSubgroup t i j
  let : Fintype H := Fintype.ofFinite H
  have hfactor := signedActionSum_left_factorization
    (labelPermutations (garnirA t i j ∪ garnirB t i j)) H
    (garnirSubgroup_le_union t i j) P hP (polytabloid t)
  rw [garnir_full_sum_eq_zero t i j ha hb,
    signedActionSum_polytabloid t H (garnirSubgroup_le_column t i j)] at hfactor
  have hscalar : (Fintype.card H : ℂ) •
      (∑ π ∈ P, permutationSign π • polytabloid (π • t)) = 0 := by
    rw [Finset.smul_sum]
    convert hfactor.symm using 1
    apply Finset.sum_congr rfl
    intro π _
    rw [map_smul, polytabloid_equivariant]
    exact smul_comm _ _ _
  exact (smul_eq_zero.mp hscalar).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

/-- FR-B02, with precisely the column-increasing descent and identity
representative conditions in the source statement. -/
theorem garnir_relation (t : Tableau p) (i j : ℕ)
    (ha : (i,j) ∈ cells p) (hb : (i,j+1) ∈ cells p)
    (_ht : ColumnIncreasing t) (_hdescent : t ⟨(i,j+1), hb⟩ < t ⟨(i,j), ha⟩)
    (P : Finset (SymmetricGroup n))
    (hP : IsLeftTransversal
      (labelPermutations (garnirA t i j ∪ garnirB t i j))
      (garnirSubgroup t i j) P) (_h1 : 1 ∈ P) :
    ∑ π ∈ P, permutationSign π • polytabloid (π • t) = 0 :=
  garnir_relation_general t i j ha hb P hP

end AdvancedFiniteGroupRepresentations
