import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CharacteristicInducedCharacter
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.HorizontalPieri
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.VerticalPieri

noncomputable section
open scoped BigOperators DirectSum
open Classical
namespace AdvancedFiniteGroupRepresentations

-- Keep implementation helpers distinct from helpers in other source goals.
namespace VerticalPieri
end VerticalPieri

abbrev VerticalStrip := @Specs.AdvancedFiniteGroupRepresentations.VerticalStrip
abbrev verticalExtensions := @Specs.AdvancedFiniteGroupRepresentations.verticalExtensions
abbrev elementaryFunction := Specs.AdvancedFiniteGroupRepresentations.elementaryFunction
abbrev signLine := Specs.AdvancedFiniteGroupRepresentations.signLine
abbrev verticalPieriInput := @Specs.AdvancedFiniteGroupRepresentations.verticalPieriInput
abbrev verticalPieriSum := @Specs.AdvancedFiniteGroupRepresentations.verticalPieriSum

@[simp] theorem VerticalPieri.mem_verticalExtensions {n k : ℕ} (lam : Partition n)
    (mu : Partition (n+k)) : mu ∈ verticalExtensions lam k ↔ VerticalStrip lam mu := by
  simp [verticalExtensions, Specs.AdvancedFiniteGroupRepresentations.verticalExtensions]

theorem verticalStrip_rows {n m : ℕ} (lam : Partition n) (mu : Partition m) :
    VerticalStrip lam mu ↔
      ∀ i, rowLength lam i ≤ rowLength mu i ∧ rowLength mu i ≤ rowLength lam i + 1 := by
  constructor
  · rintro ⟨hsub, hinj⟩ i
    refine ⟨(cells_subset_iff_rows lam mu).mp hsub i, ?_⟩
    by_contra hi
    have hc (q : ℕ) (hq : rowLength lam i ≤ q) (hqm : q < rowLength mu i) :
        (i,q) ∈ cells mu \ cells lam := by
      simp only [Finset.mem_sdiff, cell_iff]
      exact ⟨hqm, not_lt.mpr hq⟩
    have he := hinj (hc _ le_rfl (by omega)) (hc _ (Nat.le_succ _) (by omega)) rfl
    have := congrArg Prod.snd he
    omega
  · intro h
    refine ⟨(cells_subset_iff_rows lam mu).mpr (fun i => (h i).1), ?_⟩
    rintro ⟨i,q⟩ hi ⟨j,s⟩ hj he
    change i = j at he
    subst j
    have hi' := Finset.mem_sdiff.mp hi
    have hj' := Finset.mem_sdiff.mp hj
    have hqi := (cell_iff mu i q).mp hi'.1
    have hsi := (cell_iff mu i s).mp hj'.1
    have hq := mt (cell_iff lam i q).mpr hi'.2
    have hs := mt (cell_iff lam i s).mpr hj'.2
    have hh := (h i).2
    have : q = s := by omega
    subst s
    rfl

theorem verticalStrip_card {n k : ℕ} (lam : Partition n) (mu : Partition (n+k))
    (hstrip : VerticalStrip lam mu) : (cells mu \ cells lam).card = k := by
  rw [Finset.card_sdiff_of_subset hstrip.1]
  change (diagram mu).card - (diagram lam).card = k
  rw [diagram_card, diagram_card, Nat.add_sub_cancel_left]

theorem verticalStrip_zero {n : ℕ} (lam mu : Partition n) :
    VerticalStrip lam mu ↔ lam = mu := by
  constructor
  · intro h
    have he : cells lam = cells mu := Finset.eq_of_subset_of_card_le h.1 (by
      change (diagram mu).card ≤ (diagram lam).card
      rw [diagram_card, diagram_card])
    apply YoungDiagram.equivPartition.symm.injective
    apply Subtype.ext
    exact YoungDiagram.ext he
  · rintro rfl
    exact ⟨Finset.Subset.refl _, by simp [Set.InjOn]⟩



/-- Increasing words enumerate k-element subsets exactly once. -/
def VerticalPieri.strictWordSubset {r k : ℕ} (w : {w : Word r k // StrictMono w}) :
    {s : Finset (Fin r) // s.card = k} :=
  ⟨Finset.univ.image w.val, by
    rw [Finset.card_image_of_injective _ w.property.injective]
    simp⟩

theorem VerticalPieri.strictWordSubset_bijective (r k : ℕ) :
    Function.Bijective (@VerticalPieri.strictWordSubset r k) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have ha := Finset.orderEmbOfFin_unique
      (VerticalPieri.strictWordSubset a).property (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      a.property
    have hb := Finset.orderEmbOfFin_unique
      (VerticalPieri.strictWordSubset b).property (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      b.property
    exact ha.trans (by rw [hab]; exact hb.symm)
  · intro s
    refine ⟨⟨s.val.orderEmbOfFin s.property, (s.val.orderEmbOfFin s.property).strictMono⟩, ?_⟩
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ _ _

theorem VerticalPieri.e_eq_esymm (r k : ℕ) : e r (k : ℤ) = MvPolynomial.esymm (Fin r) ℂ k := by
  rw [e_nat]
  change (∑ w ∈ Finset.univ.filter StrictMono, wordWeight w) = _
  rw [Finset.sum_subtype (p := fun w : Word r k => StrictMono w) _ (fun w => by simp),
    MvPolynomial.esymm_eq_sum_subtype]
  apply Fintype.sum_bijective VerticalPieri.strictWordSubset (VerticalPieri.strictWordSubset_bijective r k) _ _
  intro w
  change (∏ i : Fin k, MvPolynomial.X (w.val i)) =
    ∏ i ∈ Finset.univ.image w.val, MvPolynomial.X i
  rw [Finset.prod_image (fun i _ j _ he => w.property.injective he)]

/-- A squarefree exponent vector is the indicator of its support. -/
theorem VerticalPieri.squarefree_support_sum {r : ℕ} (d : Fin r →₀ ℕ) (hd : ∀ i, d i ≤ 1) :
    (∑ i ∈ d.support, Finsupp.single i 1) = d := by
  ext i
  by_cases hi : i ∈ d.support
  · have hp : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have he : d i = 1 := by have := hd i; omega
    simp [Finsupp.single_apply, hi, he]
  · have hz := Finsupp.notMem_support_iff.mp hi
    simp [Finsupp.single_apply, hi, hz]

theorem VerticalPieri.e_coefficient (r k : ℕ) (d : Fin r →₀ ℕ) :
    (e r (k : ℤ)).coeff d =
      if (∑ i : Fin r, d i) = k ∧ (∀ i, d i ≤ 1) then 1 else 0 := by
  rw [VerticalPieri.e_eq_esymm, MvPolynomial.esymm]
  have hm (s : Finset (Fin r)) : (∏ i ∈ s, (MvPolynomial.X i : Alphabet r)) =
      MvPolynomial.monomial (∑ i ∈ s, Finsupp.single i 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    rfl
  simp_rw [hm]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : (∑ i : Fin r, d i) = k ∧ (∀ i, d i ≤ 1)
  · rw [ite_eq_left hd]
    have hcard : d.support.card = k := by
      calc
        d.support.card = ∑ _i ∈ d.support, 1 := by simp
        _ = ∑ i ∈ d.support, d i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hp := Finsupp.mem_support_iff.mp hi
          have hh := hd.2 i
          omega
        _ = ∑ i : Fin r, d i := by
          exact Finset.sum_subset (Finset.subset_univ _) (by
            intro i _ hi; exact Finsupp.notMem_support_iff.mp hi)
        _ = k := hd.1
    have hmem : d.support ∈ Finset.univ.powersetCard k := by simp [hcard]
    rw [Finset.sum_eq_single d.support]
    · simp [VerticalPieri.squarefree_support_sum d hd.2]
    · intro s hs hne
      rw [ite_eq_right]
      intro he
      apply hne
      apply Finset.ext
      intro i
      have hh : (if i ∈ s then 1 else 0) = d i := by
        simpa [Finsupp.single_apply] using congrArg (fun f : Fin r →₀ ℕ => f i) he
      rw [Finsupp.mem_support_iff]
      by_cases hi : i ∈ s
      · simp only [ite_eq_left hi] at hh
        exact iff_of_true hi (by omega)
      · simp only [ite_eq_right hi] at hh
        exact iff_of_false hi (by omega)
    · exact fun h => False.elim (h hmem)
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro s hs
    rw [ite_eq_right]
    intro he
    apply hd
    have heval (i : Fin r) : d i = if i ∈ s then 1 else 0 := by
      rw [← he]
      simp [Finsupp.single_apply]
    constructor
    · simp only [heval, Finset.sum_boole]
      simpa using (Finset.mem_powersetCard.mp hs).2
    · intro i
      rw [heval]
      split_ifs <;> omega


@[simp] theorem VerticalPieri.mem_cells_transpose {n : ℕ} (p : Partition n) (i j : ℕ) :
    (i,j) ∈ cells (transpose p) ↔ (j,i) ∈ cells p := by
  rw [cell_iff, transpose_rowLength, cell_iff_column]

theorem VerticalPieri.verticalStrip_transpose {n m : ℕ} (lam : Partition n) (mu : Partition m) :
    VerticalStrip lam mu ↔ HorizontalStrip (transpose lam) (transpose mu) := by
  constructor
  · rintro ⟨hsub, hinj⟩
    constructor
    · rintro ⟨i,j⟩ hc
      exact (VerticalPieri.mem_cells_transpose mu i j).mpr (hsub ((VerticalPieri.mem_cells_transpose lam i j).mp hc))
    · rintro ⟨i,j⟩ hi ⟨q,s⟩ hq he
      change j = s at he
      have hmem (a b : ℕ) : (a,b) ∈ cells (transpose mu) \ cells (transpose lam) ↔
          (b,a) ∈ cells mu \ cells lam := by simp only [Finset.mem_sdiff, VerticalPieri.mem_cells_transpose]
      have hh := hinj ((hmem i j).mp hi) ((hmem q s).mp hq) he
      have he' := congrArg Prod.snd hh
      exact Prod.ext he' he
  · rintro ⟨hsub, hinj⟩
    constructor
    · rintro ⟨i,j⟩ hc
      exact (VerticalPieri.mem_cells_transpose mu j i).mp (hsub ((VerticalPieri.mem_cells_transpose lam j i).mpr hc))
    · rintro ⟨i,j⟩ hi ⟨q,s⟩ hq he
      change i = q at he
      have hmem (a b : ℕ) : (a,b) ∈ cells mu \ cells lam ↔
          (b,a) ∈ cells (transpose mu) \ cells (transpose lam) := by
        simp only [Finset.mem_sdiff, VerticalPieri.mem_cells_transpose]
      have hh := hinj ((hmem i j).mp hi) ((hmem q s).mp hq) he
      have he' := congrArg Prod.fst hh
      exact Prod.ext he he'

theorem verticalStrip_empty {k : ℕ} (mu : Partition k) :
    VerticalStrip emptyPartition mu ↔ mu = transpose (Nat.Partition.indiscrete k) := by
  rw [VerticalPieri.verticalStrip_transpose, empty_transpose, horizontalStrip_empty]
  constructor
  · intro he
    have hh := congrArg transpose he
    simpa only [transpose_involutive] using hh
  · rintro rfl
    exact transpose_involutive _

@[simp] theorem VerticalPieri.verticalExtensions_zero {n : ℕ} (lam : Partition n) :
    verticalExtensions lam 0 = {lam} := by
  ext mu
  simp only [VerticalPieri.mem_verticalExtensions, verticalStrip_zero, Finset.mem_singleton]
  exact eq_comm

@[simp] theorem VerticalPieri.verticalExtensions_empty (k : ℕ) :
    verticalExtensions emptyPartition k = {transpose (Nat.Partition.indiscrete (0+k))} := by
  ext mu
  simp [VerticalPieri.mem_verticalExtensions, verticalStrip_empty]

/-- A nontrivial permutation cannot move between two decreasing lists
while increasing each matched exponent by at most one. -/
theorem VerticalPieri.perm_eq_one_of_unit_increments {r : ℕ} (a b : Fin r → ℕ)
    (ha : StrictAnti a) (hb : StrictAnti b) (s : Equiv.Perm (Fin r))
    (h : ∀ i, b i ≤ a (s i) ∧ a (s i) ≤ b i + 1) : s = 1 := by
  have hmono : StrictMono s := by
    intro i j hij
    have hbij := hb hij
    have hne : s i ≠ s j := s.injective.ne hij.ne
    apply lt_of_le_of_ne _ hne
    by_contra hnot
    have hh := ha (lt_of_not_ge hnot)
    have hi := h i
    have hj := h j
    omega
  apply Equiv.ext
  intro i
  exact hmono.apply_eq (x := i)

theorem VerticalPieri.monomial_mul_e_coefficient {r : ℕ} (a b : Fin r → ℕ) (k : ℕ)
    (hs : (∑ i, a i) = (∑ i, b i) + k) :
    naturalCoefficient a
      (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm b) 1 * e r (k : ℤ)) =
      if ∀ i, b i ≤ a i ∧ a i ≤ b i + 1 then 1 else 0 := by
  change (MvPolynomial.monomial _ 1 * e r (k : ℤ)).coeff _ = _
  rw [MvPolynomial.coeff_monomial_mul']
  have he : Finsupp.equivFunOnFinite.symm b ≤ Finsupp.equivFunOnFinite.symm a ↔
      ∀ i, b i ≤ a i := Iff.rfl
  simp only [he]
  by_cases h : ∀ i, b i ≤ a i
  · rw [ite_eq_left h, one_mul, VerticalPieri.e_coefficient]
    have hsum : (∑ i : Fin r,
        (Finsupp.equivFunOnFinite.symm a - Finsupp.equivFunOnFinite.symm b) i) = k := by
      change (∑ i : Fin r, (a i - b i)) = k
      rw [Finset.sum_tsub_distrib _ (fun i _ => h i), hs, Nat.add_sub_cancel_left]
    rw [hsum]
    simp only [true_and]
    congr 1
    apply propext
    apply forall_congr'
    intro i
    change a i - b i ≤ 1 ↔ b i ≤ a i ∧ a i ≤ b i + 1
    have := h i
    omega
  · rw [ite_eq_right h, ite_eq_right (by intro hh; exact h (fun i => (hh i).1))]

theorem VerticalPieri.alternant_mul_e_coefficient {r : ℕ} (a b : Fin r → ℕ) (k : ℕ)
    (ha : StrictAnti a) (hb : StrictAnti b)
    (hs : (∑ i, a i) = (∑ i, b i) + k) :
    naturalCoefficient a (alternant b * e r (k : ℤ)) =
      if ∀ i, b i ≤ a i ∧ a i ≤ b i + 1 then 1 else 0 := by
  rw [alternant_eq_sum_monomial, Finset.sum_mul]
  change (∑ s : Equiv.Perm (Fin r),
    (Equiv.Perm.sign s • MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i => b (s.symm i))) 1) * e r (k : ℤ)).coeff _ = _
  rw [MvPolynomial.coeff_sum]
  simp only [smul_mul_assoc, MvPolynomial.coeff_smul]
  change (∑ s : Equiv.Perm (Fin r), Equiv.Perm.sign s • naturalCoefficient a
    (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => b (s.symm i))) 1 *
      e r (k : ℤ))) = _
  have hm (s : Equiv.Perm (Fin r)) := VerticalPieri.monomial_mul_e_coefficient a (fun i => b (s.symm i)) k
    (by simpa only [Equiv.sum_comp s.symm b] using hs)
  simp_rw [hm]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin r))]
  · simp only [map_one, one_smul]
    rfl
  · intro s _ hs
    rw [ite_eq_right, smul_zero]
    intro h
    apply hs
    apply VerticalPieri.perm_eq_one_of_unit_increments a b ha hb s
    intro i
    simpa using h (s i)
  · simp

theorem VerticalPieri.verticalStrip_shifted_iff {n m r : ℕ} (lam : Partition n) (mu : Partition m)
    (hlam : length lam ≤ r) (hmu : length mu ≤ r) :
    VerticalStrip lam mu ↔ ∀ i : Fin r,
      shiftedPartition r lam i ≤ shiftedPartition r mu i ∧
        shiftedPartition r mu i ≤ shiftedPartition r lam i + 1 := by
  rw [verticalStrip_rows]
  constructor
  · intro h i
    have hh := h i.val
    change rowLength lam i.val + _ ≤ rowLength mu i.val + _ ∧
      rowLength mu i.val + _ ≤ rowLength lam i.val + _ + 1
    omega
  · intro h i
    by_cases hi : i < r
    · have hh := h ⟨i,hi⟩
      change rowLength lam i + (r-1-i) ≤ rowLength mu i + (r-1-i) ∧
        rowLength mu i + (r-1-i) ≤ rowLength lam i + (r-1-i) + 1 at hh
      omega
    · rw [rowLength_zero_of_length_le lam i (by omega),
        rowLength_zero_of_length_le mu i (by omega)]
      omega

theorem VerticalPieri.partitionAlternant_mul_e_coefficient {n k r : ℕ} (lam : Partition n)
    (mu : Partition (n+k)) (hlam : length lam ≤ r) (hmu : length mu ≤ r) :
    naturalCoefficient (shiftedPartition r mu) (partitionAlternant r lam * e r (k : ℤ)) =
      if VerticalStrip lam mu then 1 else 0 := by
  change naturalCoefficient (shiftedPartition r mu) (alternant (shiftedPartition r lam) * _) = _
  rw [VerticalPieri.alternant_mul_e_coefficient _ _ k (shiftedPartition_strictAnti mu)
    (shiftedPartition_strictAnti lam) (by
      rw [sum_shiftedPartition mu hmu, sum_shiftedPartition lam hlam]
      omega)]
  simp only [← VerticalPieri.verticalStrip_shifted_iff lam mu hlam hmu]


theorem VerticalPieri.e_isHomogeneous (r k : ℕ) : (e r (k : ℤ)).IsHomogeneous k := by
  rw [e_nat]
  apply MvPolynomial.IsHomogeneous.sum
  intro w _
  change (∏ i : Fin k, (MvPolynomial.X (w i) : Alphabet r)).IsHomogeneous k
  convert MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin k))
    (fun i => (MvPolynomial.X (w i) : Alphabet r)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X ℂ (w i)) using 1 <;> simp

/-- The identity is first proved in a finite alphabet containing every shape
of the total degree, by testing the ordered coefficients after alternation. -/
theorem VerticalPieri.vertical_pieri_finite_enough {n : ℕ} (lam : Partition n) (k r : ℕ)
    (hr : n+k ≤ r) :
    schurPolynomial lam r * e r (k : ℤ) =
      ∑ mu ∈ verticalExtensions lam k, schurPolynomial mu r := by
  have hlam : length lam ≤ r := (partition_length_le_size lam).trans (by omega)
  have hmu (mu : Partition (n+k)) : length mu ≤ r := (partition_length_le_size mu).trans hr
  have hsum_sym : (∑ mu ∈ verticalExtensions lam k, schurPolynomial mu r).IsSymmetric := by
    apply (MvPolynomial.symmetricSubalgebra (Fin r) ℂ).sum_mem
    intro mu _
    exact schurPolynomial_isSymmetric mu r
  have hsum_hom : (∑ mu ∈ verticalExtensions lam k, schurPolynomial mu r).IsHomogeneous (n+k) := by
    apply MvPolynomial.IsHomogeneous.sum
    intro mu _
    exact schurPolynomial_isHomogeneous mu r
  have he_sym : (e r (k : ℤ)).IsSymmetric := by
    rw [VerticalPieri.e_eq_esymm]
    exact MvPolynomial.esymm_isSymmetric _ _ _
  apply sub_eq_zero.mp
  apply eq_zero_of_alternating_coefficients_zero _
    (((schurPolynomial_isSymmetric lam r).mul he_sym).sub hsum_sym)
    (((schurPolynomial_isHomogeneous lam r).mul (VerticalPieri.e_isHomogeneous r k)).sub hsum_hom)
  intro nu
  have hc (mu : Partition (n+k)) :
      naturalCoefficient (shiftedPartition r nu) (vandermonde r * schurPolynomial mu r) =
        if nu = mu then 1 else 0 := by
    rw [schurPolynomial_characterization mu r (hmu mu)]
    change naturalCoefficient (shiftedPartition r nu) (alternant (shiftedPartition r mu)) = _
    rw [naturalCoefficient_alternant _ _ (shiftedPartition_strictAnti nu) (shiftedPartition_strictAnti mu)]
    have he : shiftedPartition r nu = shiftedPartition r mu ↔ nu = mu := by
      constructor
      · intro h
        exact partition_eq_of_diagram_eq nu mu
          (diagram_eq_of_shiftedPartition_eq nu mu (hmu nu) (hmu mu) h)
      · rintro rfl; rfl
    simp only [he]
  have hc_sum : naturalCoefficient (shiftedPartition r nu)
      (vandermonde r * ∑ mu ∈ verticalExtensions lam k, schurPolynomial mu r) =
        if VerticalStrip lam nu then 1 else 0 := by
    rw [Finset.mul_sum]
    change (∑ mu ∈ verticalExtensions lam k, vandermonde r * schurPolynomial mu r).coeff _ = _
    rw [MvPolynomial.coeff_sum]
    change (∑ mu ∈ verticalExtensions lam k,
      naturalCoefficient (shiftedPartition r nu) (vandermonde r * schurPolynomial mu r)) = _
    simp only [hc]
    simp
  rw [mul_sub]
  change naturalCoefficient (shiftedPartition r nu)
    (vandermonde r * (schurPolynomial lam r * e r (k : ℤ))) -
      naturalCoefficient (shiftedPartition r nu)
        (vandermonde r * ∑ mu ∈ verticalExtensions lam k, schurPolynomial mu r) = 0
  rw [← mul_assoc, schurPolynomial_characterization lam r hlam,
    VerticalPieri.partitionAlternant_mul_e_coefficient lam nu hlam (hmu nu), hc_sum, sub_self]

/-- A column of height k has k rows, also at k=0. -/
theorem VerticalPieri.length_column (k : ℕ) : length (transpose (Nat.Partition.indiscrete k)) = k := by
  rw [length_eq_columnLength_zero, transpose_columnLength, rowLength_indiscrete_zero]

/-- The empty-shape case identifies the elementary polynomial in large
alphabets; both sides vanish in smaller alphabets. -/
theorem VerticalPieri.schurPolynomial_column (k r : ℕ) :
    schurPolynomial (transpose (Nat.Partition.indiscrete k)) r = e r (k : ℤ) := by
  by_cases hk : k ≤ r
  · have hp := VerticalPieri.vertical_pieri_finite_enough emptyPartition k r (by omega)
    calc
      schurPolynomial (transpose (Nat.Partition.indiscrete k)) r =
          schurPolynomial (transpose (Nat.Partition.indiscrete (0+k))) r :=
        congrArg (fun t => schurPolynomial (transpose (Nat.Partition.indiscrete t)) r)
          (Nat.zero_add k).symm
      _ = e r (k : ℤ) := by
        simpa only [empty_schurPolynomial, one_mul, VerticalPieri.verticalExtensions_empty,
          Finset.sum_singleton] using hp.symm
  · rw [schurPolynomial_eq_zero_of_length_gt _ (by rw [VerticalPieri.length_column]; omega),
      e_eq_zero_of_lt_degree r (k : ℤ) (by omega)]

theorem elementaryFunction_specialization (k r : ℕ) :
    stableSpecialization r (elementaryFunction k) = e r (k : ℤ) := by
  exact (schurFunction_specialization (transpose (Nat.Partition.indiscrete k)) r).trans
    (VerticalPieri.schurPolynomial_column k r)

/-- Lift at total degree, where specialization is injective. -/
theorem vertical_pieri_stable : Specs.AdvancedFiniteGroupRepresentations.vertical_pieri_stableType := by
  intro n lam k
  change DirectSum.of (fun n => stableDegree n) n (stableSchur lam) *
    DirectSum.of (fun n => stableDegree n) k (stableSchur (transpose (Nat.Partition.indiscrete k))) =
      ∑ mu ∈ verticalExtensions lam k, DirectSum.of (fun n => stableDegree n) (n+k) (stableSchur mu)
  rw [DirectSum.of_mul_of, ← map_sum]
  apply congrArg (DirectSum.of (fun n => stableDegree n) (n+k))
  apply degreeSpecialization_injective (n+k) (n+k) le_rfl
  change (stableSchur lam).val (n+k) * (stableSchur (transpose (Nat.Partition.indiscrete k))).val (n+k) =
    (∑ mu ∈ verticalExtensions lam k, stableSchur mu).val (n+k)
  simp only [stableSchur_specialization, Submodule.coe_sum, Finset.sum_apply]
  rw [VerticalPieri.schurPolynomial_column]
  exact VerticalPieri.vertical_pieri_finite_enough lam k (n+k) le_rfl

/-- Specialization gives every alphabet, including zero variables. -/
theorem vertical_pieri_finite : Specs.AdvancedFiniteGroupRepresentations.vertical_pieri_finiteType := by
  intro n lam k r
  have he := congrArg (stableSpecialization r) (vertical_pieri_stable lam k)
  rw [map_mul, schurFunction_specialization, elementaryFunction_specialization, map_sum] at he
  simpa only [map_sum, schurFunction_specialization] using he

open private canonicalSpecht canonicalSpecht_inherited
  from MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification

/-- The classification identifies the column with the actual sign line.
Its empty case supplies degree zero. -/
theorem VerticalPieri.columnSpecht_sign (k : ℕ)
    (rho : Representation ℂ (SymmetricGroup k)
      (SpechtModule (transpose (Nat.Partition.indiscrete k))))
    (hrho : InheritedSpechtAction _ rho) : Nonempty (rho.Equiv (signLine k)) := by
  have hline : ∃ f : SpechtModule (transpose (Nat.Partition.indiscrete k)) ≃ₗ[ℂ] ℂ,
      ∀ g v, f (rho g v) = permutationSign g * f v := by
    cases k with
    | zero =>
      have he : transpose (Nat.Partition.indiscrete 0) = emptyPartition := zero_partition_unique _
      revert hrho rho
      rw [he]
      intro rho hrho
      obtain ⟨f, hf⟩ := classification_empty rho hrho
      refine ⟨f, fun g v => ?_⟩
      have hg : g = 1 := Subsingleton.elim _ _
      simpa only [hg, permutationSign_one, one_mul] using hf g v
    | succ k => exact classification_column (k+1) (Nat.succ_pos _) rho hrho
  obtain ⟨f, hf⟩ := hline
  refine ⟨{ toLinearEquiv := f, isIntertwining' := ?_ }⟩
  intro g
  ext v
  exact hf g v

theorem VerticalPieri.characteristic_sign (k : ℕ) :
    characteristic (representationClassFunction (signLine k)) =
      stableSchur (transpose (Nat.Partition.indiscrete k)) := by
  let rho := canonicalSpecht (transpose (Nat.Partition.indiscrete k))
  obtain ⟨f⟩ := VerticalPieri.columnSpecht_sign k rho (canonicalSpecht_inherited _)
  have hc : representationClassFunction rho = representationClassFunction (signLine k) := by
    funext c
    refine Quotient.inductionOn c ?_
    intro g
    exact congrFun (Representation.char_iso f) g
  rw [← hc]
  exact characteristic_specht _ rho (canonicalSpecht_inherited _)

/-- The induced class function has one copy of each allowed Specht character. -/
theorem vertical_pieri_character : Specs.AdvancedFiniteGroupRepresentations.vertical_pieri_characterType := by
  intro n lam k rho sigma hrho hsigma
  apply characteristic_injective (n+k)
  apply DirectSum.of_injective (β := fun n => stableDegree n) (n+k)
  rw [characteristic_induction_product, characteristic_specht lam rho hrho, VerticalPieri.characteristic_sign]
  change schurFunction lam * elementaryFunction k = _
  rw [vertical_pieri_stable lam k]
  obtain ⟨f, hf⟩ := characteristic_linearEquiv (n+k)
  rw [← hf, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [hf, characteristic_specht mu (sigma mu) (hsigma mu)]
  rfl

/-- Ordinary induction of the actual external tensor product is the direct
sum with exactly one summand for every vertical-strip extension. -/
theorem vertical_pieri_module : Specs.AdvancedFiniteGroupRepresentations.vertical_pieri_moduleType := by
  intro n lam k rho sigma hrho hsigma
  let tau := Representation.ind (A := TensorProduct ℂ (SpechtModule lam) ℂ)
    (blockEmbedding n k) (verticalPieriInput rho k)
  change Nonempty (tau.Equiv (Representation.directSum
    (fun mu : {mu : Partition (n+k) // VerticalStrip lam mu} => sigma mu.val)))
  apply equiv_directSum_of_character
    (fun mu : {mu : Partition (n+k) // VerticalStrip lam mu} => sigma mu.val) tau
  · intro mu
    exact classification_irreducible mu.val (sigma mu.val) (hsigma mu.val)
  · intro mu nu he
    apply Subtype.ext
    exact classification_distinct mu.val nu.val (sigma mu.val) (sigma nu.val)
      (hsigma mu.val) (hsigma nu.val) he
  · intro g
    have hind : tau.character g =
        inducedExternal (representationClassFunction rho) (representationClassFunction (signLine k))
          (ConjClasses.mk g) := by
      exact congrFun (blockInduced_character rho (signLine k)) (ConjClasses.mk g)
    rw [hind]
    have hc := congrFun (vertical_pieri_character lam k rho sigma hrho hsigma) (ConjClasses.mk g)
    simp only [Finset.sum_apply] at hc
    change inducedExternal (representationClassFunction rho) (representationClassFunction (signLine k))
      (ConjClasses.mk g) = ∑ mu ∈ verticalExtensions lam k, (sigma mu).character g at hc
    rw [hc]
    exact Finset.sum_subtype (verticalExtensions lam k)
      (fun mu => VerticalPieri.mem_verticalExtensions lam mu) (fun mu => (sigma mu).character g)

end AdvancedFiniteGroupRepresentations
