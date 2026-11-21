import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CharacteristicInducedCharacter
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurTableauFormula
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.HorizontalPieri
import Batteries.Tactic.OpenPrivate
import Mathlib.RepresentationTheory.Maschke

noncomputable section
open scoped BigOperators DirectSum
open Classical
namespace AdvancedFiniteGroupRepresentations

abbrev HorizontalStrip := @Specs.AdvancedFiniteGroupRepresentations.HorizontalStrip
abbrev horizontalExtensions := @Specs.AdvancedFiniteGroupRepresentations.horizontalExtensions
abbrev schurFunction := @Specs.AdvancedFiniteGroupRepresentations.schurFunction
abbrev completeFunction := Specs.AdvancedFiniteGroupRepresentations.completeFunction
abbrev horizontalPieriInput := @Specs.AdvancedFiniteGroupRepresentations.horizontalPieriInput
abbrev horizontalPieriSum := @Specs.AdvancedFiniteGroupRepresentations.horizontalPieriSum

@[simp] theorem mem_horizontalExtensions {n k : ℕ} (lam : Partition n)
    (mu : Partition (n+k)) : mu ∈ horizontalExtensions lam k ↔ HorizontalStrip lam mu := by
  simp [horizontalExtensions, Specs.AdvancedFiniteGroupRepresentations.horizontalExtensions]

/-- Containment is precisely the weak inequality of every padded row. -/
theorem cells_subset_iff_rows {n m : ℕ} (lam : Partition n) (mu : Partition m) :
    cells lam ⊆ cells mu ↔ ∀ i, rowLength lam i ≤ rowLength mu i := by
  constructor
  · intro h i
    by_contra hi
    have hc := h ((cell_iff lam i (rowLength mu i)).mpr (by omega))
    have := (cell_iff mu i (rowLength mu i)).mp hc
    omega
  · intro h c hc
    exact (cell_iff mu c.1 c.2).mpr (((cell_iff lam c.1 c.2).mp hc).trans_le (h c.1))

/-- The geometric column condition agrees with the source's interlacing ranges. -/
theorem horizontalStrip_interlacing {n m : ℕ} (lam : Partition n) (mu : Partition m) :
    HorizontalStrip lam mu ↔
      (∀ i, rowLength lam i ≤ rowLength mu i) ∧
        ∀ i, rowLength mu (i+1) ≤ rowLength lam i := by
  constructor
  · rintro ⟨hsub, hinj⟩
    refine ⟨(cells_subset_iff_rows lam mu).mp hsub, fun i => ?_⟩
    by_contra hi
    have hnew : rowLength lam i < rowLength mu (i+1) := by omega
    have hfirst : (i, rowLength lam i) ∈ cells mu \ cells lam := by
      simp only [Finset.mem_sdiff, cell_iff]
      exact ⟨hnew.trans_le (rowLength_antitone mu (Nat.le_succ i)), lt_irrefl _⟩
    have hsecond : (i+1, rowLength lam i) ∈ cells mu \ cells lam := by
      simp only [Finset.mem_sdiff, cell_iff]
      exact ⟨hnew, not_lt.mpr (rowLength_antitone lam (Nat.le_succ i))⟩
    have he := hinj hfirst hsecond rfl
    have := congrArg Prod.fst he
    omega
  · rintro ⟨hsub, hinter⟩
    refine ⟨(cells_subset_iff_rows lam mu).mpr hsub, ?_⟩
    rintro ⟨i,q⟩ hi ⟨j,s⟩ hj he
    change q = s at he
    subst s
    have hi' := Finset.mem_sdiff.mp hi
    have hj' := Finset.mem_sdiff.mp hj
    have hqi := (cell_iff mu i q).mp hi'.1
    have hqj := (cell_iff mu j q).mp hj'.1
    have hli : rowLength lam i ≤ q := Nat.le_of_not_gt (fun h => hi'.2 ((cell_iff lam i q).mpr h))
    have hlj : rowLength lam j ≤ q := Nat.le_of_not_gt (fun h => hj'.2 ((cell_iff lam j q).mpr h))
    have hij : i = j := by
      rcases lt_trichotomy i j with hij | hij | hji
      · have hh := (rowLength_antitone mu (Nat.succ_le_of_lt hij)).trans (hinter i)
        omega
      · exact hij
      · have hh := (rowLength_antitone mu (Nat.succ_le_of_lt hji)).trans (hinter j)
        omega
    subst j
    rfl

theorem horizontalStrip_card {n k : ℕ} (lam : Partition n) (mu : Partition (n+k))
    (hstrip : HorizontalStrip lam mu) : (cells mu \ cells lam).card = k := by
  rw [Finset.card_sdiff_of_subset hstrip.1]
  change (diagram mu).card - (diagram lam).card = k
  rw [diagram_card, diagram_card, Nat.add_sub_cancel_left]

/-- No cells can be added while preserving the degree. -/
theorem horizontalStrip_zero {n : ℕ} (lam mu : Partition n) :
    HorizontalStrip lam mu ↔ lam = mu := by
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

/-- The single-row partition, including degree zero. -/
theorem parts_indiscrete_all (k : ℕ) :
    parts (Nat.Partition.indiscrete k) = if k = 0 then [] else [k] := by
  by_cases hk : k = 0
  · subst k
    rw [zero_partition_unique (Nat.Partition.indiscrete 0), empty_parts, ite_eq_left rfl]
  · rw [ite_eq_right hk, parts_eq_sorted_multiset, Nat.Partition.indiscrete_parts hk]
    exact Multiset.sort_singleton k (· ≥ ·)

theorem rowLength_indiscrete_zero (k : ℕ) : rowLength (Nat.Partition.indiscrete k) 0 = k := by
  rw [rowLength_eq_getD, parts_indiscrete_all]
  split_ifs with hk <;> simp_all

theorem length_indiscrete_le_one (k : ℕ) : length (Nat.Partition.indiscrete k) ≤ 1 := by
  change (parts (Nat.Partition.indiscrete k)).length ≤ 1
  rw [parts_indiscrete_all]
  split_ifs <;> simp

/-- Jacobi–Trudi with one row identifies h_k in every alphabet, even size zero. -/
theorem schurPolynomial_indiscrete (k r : ℕ) :
    schurPolynomial (Nat.Partition.indiscrete k) r = h r (k : ℤ) := by
  rw [← paddedJacobiTrudi_eq_schurPolynomial (Nat.Partition.indiscrete k) r 1
    (length_indiscrete_le_one k)]
  change (paddedJacobiTrudiMatrix (Nat.Partition.indiscrete k) r 1).det = _
  rw [Matrix.det_fin_one]
  change h r ((rowLength (Nat.Partition.indiscrete k) 0 : ℤ) - 0 + 0) = _
  rw [rowLength_indiscrete_zero]
  simp

theorem schurFunction_specialization {n : ℕ} (lam : Partition n) (r : ℕ) :
    stableSpecialization r (schurFunction lam) = schurPolynomial lam r := by
  exact (stableSpecialization_of n r (stableSchur lam)).trans (stableSchur_specialization lam r)

theorem completeFunction_specialization (k r : ℕ) :
    stableSpecialization r (completeFunction k) = h r (k : ℤ) := by
  exact (schurFunction_specialization (Nat.Partition.indiscrete k) r).trans
    (schurPolynomial_indiscrete k r)

theorem schurFunction_specialization_zero {n r : ℕ} (lam : Partition n)
    (hr : r < length lam) : stableSpecialization r (schurFunction lam) = 0 := by
  rw [schurFunction_specialization, schurPolynomial_eq_zero_of_length_gt lam hr]

/-- Adding a horizontal strip to the empty diagram produces exactly one row. -/
theorem horizontalStrip_empty {k : ℕ} (mu : Partition k) :
    HorizontalStrip emptyPartition mu ↔ mu = Nat.Partition.indiscrete k := by
  have he (i : ℕ) : rowLength emptyPartition i = 0 := by
    rw [rowLength_eq_getD, empty_parts]
    simp
  constructor
  · intro hs
    have hs := (horizontalStrip_interlacing emptyPartition mu).mp hs
    have hlen : length mu ≤ 1 := by
      by_contra hh
      have hh' := rowLength_pos_of_lt_length mu 1 (by omega)
      have hh'' := hs.2 0
      rw [he] at hh''
      change rowLength mu 1 ≤ 0 at hh''
      omega
    have hfirst : rowLength mu 0 = k := by
      simpa using (sum_rowLength_fin mu hlen)
    apply YoungDiagram.equivPartition.symm.injective
    apply Subtype.ext
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨i,j⟩
    change (i,j) ∈ cells mu ↔ (i,j) ∈ cells (Nat.Partition.indiscrete k)
    rw [cell_iff, cell_iff]
    cases i with
    | zero => rw [hfirst, rowLength_indiscrete_zero]
    | succ i =>
      rw [rowLength_zero_of_length_le mu (i+1) (by omega),
        rowLength_zero_of_length_le _ (i+1) ((length_indiscrete_le_one k).trans (by omega))]
  · rintro rfl
    apply (horizontalStrip_interlacing _ _).mpr
    refine ⟨fun i => by rw [he]; exact Nat.zero_le _, fun i => ?_⟩
    rw [he, rowLength_zero_of_length_le _ (i+1)
      ((length_indiscrete_le_one k).trans (by omega))]

@[simp] theorem horizontalExtensions_zero {n : ℕ} (lam : Partition n) :
    horizontalExtensions lam 0 = {lam} := by
  ext mu
  simp only [horizontalExtensions, Specs.AdvancedFiniteGroupRepresentations.horizontalExtensions,
    Finset.mem_filter, Finset.mem_univ, true_and, horizontalStrip_zero, Finset.mem_singleton]
  exact eq_comm

@[simp] theorem horizontalExtensions_empty (k : ℕ) :
    horizontalExtensions emptyPartition k = {Nat.Partition.indiscrete (0+k)} := by
  ext mu
  simp [mem_horizontalExtensions, horizontalStrip_empty]

/-- The empty strip identity is valid without any restriction on the alphabet. -/
theorem horizontal_pieri_finite_zero {n : ℕ} (lam : Partition n) (r : ℕ) :
    schurPolynomial lam r * h r (0 : ℤ) =
      ∑ mu ∈ horizontalExtensions lam 0, schurPolynomial mu r := by
  rw [h_zero, mul_one, horizontalExtensions_zero, Finset.sum_singleton]

/-- Starting at degree zero recovers the one-row Schur identity. -/
theorem horizontal_pieri_finite_empty (k r : ℕ) :
    schurPolynomial emptyPartition r * h r (k : ℤ) =
      ∑ mu ∈ horizontalExtensions emptyPartition k, schurPolynomial mu r := by
  rw [empty_schurPolynomial, one_mul, horizontalExtensions_empty, Finset.sum_singleton,
    schurPolynomial_indiscrete]
  simp

/-- Lifting a complete finite-alphabet identity requires no additional
stability assumption: the upstream realization is injective. -/
theorem horizontal_pieri_stable_of_finite
    (hpieri : Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_finiteType) :
    Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_stableType := by
  intro n lam k
  apply stableRealization_injective
  funext r
  change stableSpecialization r (schurFunction lam * completeFunction k) =
    stableSpecialization r (∑ mu ∈ horizontalExtensions lam k, schurFunction mu)
  rw [map_mul, schurFunction_specialization, completeFunction_specialization, map_sum]
  simpa only [schurFunction_specialization] using hpieri lam k r

/-- Conversely every alphabet, including zero letters, is a ring specialization. -/
theorem horizontal_pieri_finite_of_stable
    (hpieri : Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_stableType) :
    Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_finiteType := by
  intro n lam k r
  have he := congrArg (stableSpecialization r) (hpieri lam k)
  rw [map_mul, schurFunction_specialization, completeFunction_specialization, map_sum] at he
  simpa only [map_sum, schurFunction_specialization] using he

open private canonicalSpecht canonicalSpecht_inherited
  from MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification

/-- The classification's row and empty cases together identify the trivial
line in every degree, without imposing k > 0. -/
theorem indiscreteSpecht_trivial (k : ℕ)
    (rho : Representation ℂ (SymmetricGroup k) (SpechtModule (Nat.Partition.indiscrete k)))
    (hrho : InheritedSpechtAction _ rho) :
    Nonempty (rho.Equiv (Representation.trivial ℂ (SymmetricGroup k) ℂ)) := by
  have hline : ∃ e : SpechtModule (Nat.Partition.indiscrete k) ≃ₗ[ℂ] ℂ,
      ∀ g v, e (rho g v) = e v := by
    cases k with
    | zero => exact classification_empty rho hrho
    | succ k => exact classification_row (k+1) (Nat.succ_pos _) rho hrho
  obtain ⟨e, he⟩ := hline
  refine ⟨{ toLinearEquiv := e, isIntertwining' := ?_ }⟩
  intro g
  ext v
  exact he g v

theorem characteristic_trivial (k : ℕ) :
    characteristic (representationClassFunction
      (Representation.trivial ℂ (SymmetricGroup k) ℂ)) =
        stableSchur (Nat.Partition.indiscrete k) := by
  let rho := canonicalSpecht (Nat.Partition.indiscrete k)
  obtain ⟨e⟩ := indiscreteSpecht_trivial k rho (canonicalSpecht_inherited _)
  have hc : representationClassFunction rho = representationClassFunction
      (Representation.trivial ℂ (SymmetricGroup k) ℂ) := by
    funext c
    refine Quotient.inductionOn c ?_
    intro g
    exact congrFun (Representation.char_iso e) g
  rw [← hc]
  exact characteristic_specht _ rho (canonicalSpecht_inherited _)

/-- Injectivity of the actual characteristic, rather than a formal assumption
that characters are already symmetric functions. -/
theorem characteristic_injective (n : ℕ) :
    Function.Injective (characteristic (n := n)) := by
  obtain ⟨e, he⟩ := characteristic_linearEquiv n
  intro f g h
  exact e.injective (by simpa only [he] using h)

/-- The characteristic map carries stable Pieri to the induced-character decomposition. -/
theorem horizontal_pieri_character_of_stable
    (hpieri : Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_stableType) :
    Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_characterType := by
  intro n lam k rho sigma hrho hsigma
  apply characteristic_injective (n+k)
  apply DirectSum.of_injective (β := fun n => stableDegree n) (n+k)
  rw [characteristic_induction_product, characteristic_specht lam rho hrho,
    characteristic_trivial]
  change schurFunction lam * completeFunction k = _
  rw [hpieri lam k]
  obtain ⟨e, he⟩ := characteristic_linearEquiv (n+k)
  rw [← he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [he, characteristic_specht mu (sigma mu) (hsigma mu)]
  rfl

/-- The zero-one matrix recording the independent lower exponent bounds. -/
def pieriMatrix {r : ℕ} (b c : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => if b j ≤ c i then 1 else 0

/-- A prefix of a decreasing exponent vector has its expected cardinality. -/
theorem pieri_prefix_card {r : ℕ} (c : Fin r → ℕ) (hc : Antitone c) (d : ℕ)
    (i : Fin r) :
    d ≤ c i ↔ i.val < (Finset.univ.filter (fun j => d ≤ c j)).card := by
  let S := Finset.univ.filter (fun j => d ≤ c j)
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ S := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans (hc (Finset.mem_Iic.mp hj))⟩
    have hcard := Finset.card_le_card hsub
    simpa only [Fin.card_Iic, Nat.add_one_le_iff] using hcard
  · intro hi
    by_contra hnot
    have hsub : S ⊆ Finset.Iio i := by
      intro j hj
      have hj := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact hnot (hj.trans (hc (le_of_not_gt hji)))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    exact (not_lt_of_ge hcard) hi

/-- For ordered exponents, a nonzero bound matrix must have exactly one
new row in each successive column. -/
theorem pieriMatrix_det {r : ℕ} (b c : Fin r → ℕ)
    (hb : Antitone b) (hc : Antitone c) :
    (pieriMatrix b c).det =
      if (∀ i, b i ≤ c i) ∧ (∀ i j, i < j → c j < b i) then 1 else 0 := by
  let S (j : Fin r) := Finset.univ.filter (fun i => b j ≤ c i)
  have hsub {j k : Fin r} (hjk : j ≤ k) : S j ⊆ S k := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hb hjk).trans (Finset.mem_filter.mp hi).2⟩
  have hgood (hne : (pieriMatrix b c).det ≠ 0) :
      (∀ i, b i ≤ c i) ∧ (∀ i j, i < j → c j < b i) := by
    have hpos (j : Fin r) : 0 < (S j).card := by
      by_contra h
      have hz : S j = ∅ := Finset.card_eq_zero.mp (by omega)
      apply hne
      apply Matrix.det_eq_zero_of_column_eq_zero j
      intro i
      have hi : ¬ b j ≤ c i := by
        intro hi
        have : i ∈ S j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        rw [hz] at this
        exact Finset.notMem_empty _ this
      simp [pieriMatrix, hi]
    have hbound (j : Fin r) : (S j).card ≤ r := by
      simpa using Finset.card_le_card (Finset.filter_subset (fun i => b j ≤ c i) Finset.univ)
    have hstrict : StrictMono (fun j => (S j).card) := by
      intro j k hjk
      apply lt_of_le_of_ne (Finset.card_le_card (hsub hjk.le))
      intro he
      have heS : S j = S k := Finset.eq_of_subset_of_card_le (hsub hjk.le) he.ge
      apply hne
      apply Matrix.det_zero_of_column_eq hjk.ne
      intro i
      have heP : b j ≤ c i ↔ b k ≤ c i := by
        have heM := congrArg (fun T : Finset (Fin r) => i ∈ T) heS
        simpa [S] using heM
      simp only [pieriMatrix, heP]
    let q : Fin r → Fin r := fun j => ⟨(S j).card - 1, by
      have := hpos j
      have := hbound j
      omega⟩
    have hq : StrictMono q := by
      intro j k hjk
      have hs : (S j).card < (S k).card := hstrict hjk
      have := hpos j
      change (S j).card - 1 < (S k).card - 1
      omega
    have he (j : Fin r) : (S j).card = j.val + 1 := by
      have hh := congrArg Fin.val (hq.apply_eq (x := j))
      have := hpos j
      change (S j).card - 1 = j.val at hh
      omega
    constructor
    · intro i
      apply (pieri_prefix_card c hc (b i) i).mpr
      change i.val < (S i).card
      rw [he]
      omega
    · intro i j hij
      apply lt_of_not_ge
      intro h
      have hh := (pieri_prefix_card c hc (b i) j).mp h
      change j.val < (S i).card at hh
      rw [he] at hh
      have : i.val < j.val := hij
      omega
  by_cases hg : (∀ i, b i ≤ c i) ∧ (∀ i j, i < j → c j < b i)
  · rw [if_pos hg]
    have htri : (pieriMatrix b c).BlockTriangular id := by
      intro i j hij
      simp only [pieriMatrix, if_neg (not_le.mpr (hg.2 j i hij))]
    rw [Matrix.det_of_upperTriangular htri]
    simp [pieriMatrix, hg.1]
  · rw [if_neg hg]
    by_contra hne
    exact hg (hgood hne)

/-- Each weak composition occurs once in the complete homogeneous polynomial. -/
theorem h_coefficient (r k : ℕ) (d : Fin r →₀ ℕ) :
    (h r (k : ℤ)).coeff d = if (∑ i : Fin r, d i) = k then 1 else 0 := by
  rw [h_eq_sum_monomial, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, Finset.mem_finsuppAntidiag, Finsupp.sum_fintype]

/-- Coefficients of a shifted complete homogeneous polynomial are bound tests. -/
theorem monomial_mul_h_coefficient {r : ℕ} (a b : Fin r → ℕ) (k : ℕ)
    (hs : (∑ i, a i) = (∑ i, b i) + k) :
    naturalCoefficient a
      (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm b) 1 * h r (k : ℤ)) =
      if ∀ i, b i ≤ a i then 1 else 0 := by
  change (MvPolynomial.monomial _ 1 * h r (k : ℤ)).coeff _ = _
  rw [MvPolynomial.coeff_monomial_mul']
  have he : Finsupp.equivFunOnFinite.symm b ≤ Finsupp.equivFunOnFinite.symm a ↔
      ∀ i, b i ≤ a i := Iff.rfl
  simp only [he]
  split_ifs with h
  · rw [one_mul, h_coefficient]
    have hsum : (∑ i : Fin r,
        (Finsupp.equivFunOnFinite.symm a - Finsupp.equivFunOnFinite.symm b) i) = k := by
      change (∑ i : Fin r, (a i - b i)) = k
      rw [Finset.sum_tsub_distrib _ (fun i _ => h i), hs, Nat.add_sub_cancel_left]
    simpa only [Finsupp.tsub_apply] using (if_pos hsum : (if (∑ i : Fin r,
        (Finsupp.equivFunOnFinite.symm a - Finsupp.equivFunOnFinite.symm b) i) = k then (1 : ℂ) else 0) = 1)
  · rfl

/-- The ordered coefficient is a determinant of independent exponent bounds. -/
theorem alternant_mul_h_coefficient {r : ℕ} (a b : Fin r → ℕ) (k : ℕ)
    (hs : (∑ i, a i) = (∑ i, b i) + k) :
    naturalCoefficient a (alternant b * h r (k : ℤ)) = (pieriMatrix b a).det := by
  rw [alternant_eq_sum_monomial, Finset.sum_mul, Matrix.det_apply]
  change (∑ σ : Equiv.Perm (Fin r),
    (Equiv.Perm.sign σ • MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i))) 1) * h r (k : ℤ)).coeff _ = _
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc, MvPolynomial.coeff_smul]
  change Equiv.Perm.sign σ • naturalCoefficient a
    (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => b (σ.symm i))) 1 *
      h r (k : ℤ)) = _
  rw [monomial_mul_h_coefficient a _ k (by simpa only [Equiv.sum_comp σ.symm b] using hs)]
  congr 1
  have he : (∀ i, b (σ.symm i) ≤ a i) ↔ ∀ i, b i ≤ a (σ i) := by
    constructor
    · intro h i
      simpa using h (σ i)
    · intro h i
      simpa using h (σ.symm i)
  simp only [he]
  by_cases h : ∀ i, b i ≤ a (σ i)
  · simp [pieriMatrix, h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [pieriMatrix, hi]

/-- The independent strict-exponent bounds are exactly the diagram strip condition. -/
theorem horizontalStrip_shifted_iff {n m r : ℕ} (lam : Partition n) (mu : Partition m)
    (hlam : length lam ≤ r) (hmu : length mu ≤ r) :
    HorizontalStrip lam mu ↔
      (∀ i : Fin r, shiftedPartition r lam i ≤ shiftedPartition r mu i) ∧
      ∀ i j : Fin r, i < j → shiftedPartition r mu j < shiftedPartition r lam i := by
  rw [horizontalStrip_interlacing]
  constructor
  · rintro ⟨hsub, hinter⟩
    constructor
    · intro i
      exact Nat.add_le_add_right (hsub i.val) _
    · intro i j hij
      have hr := (rowLength_antitone mu (show i.val + 1 ≤ j.val by exact hij)).trans (hinter i.val)
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.val < j.val := hij
      change rowLength mu j.val + (r - 1 - j.val) < rowLength lam i.val + (r - 1 - i.val)
      omega
  · rintro ⟨hsub, hinter⟩
    constructor
    · intro i
      by_cases hi : i < r
      · exact Nat.le_of_add_le_add_right (hsub ⟨i,hi⟩)
      · rw [rowLength_zero_of_length_le lam i (by omega)]
        exact Nat.zero_le _
    · intro i
      by_cases hi : i + 1 < r
      · have hh := hinter ⟨i, by omega⟩ ⟨i+1,hi⟩ (by change i < i+1; omega)
        change rowLength mu (i+1) + (r - 1 - (i+1)) <
          rowLength lam i + (r - 1 - i) at hh
        omega
      · rw [rowLength_zero_of_length_le mu (i+1) (by omega)]
        exact Nat.zero_le _

/-- Ordered coefficients of a Schur numerator times h are the strip indicators. -/
theorem partitionAlternant_mul_h_coefficient {n k r : ℕ} (lam : Partition n)
    (mu : Partition (n+k)) (hlam : length lam ≤ r) (hmu : length mu ≤ r) :
    naturalCoefficient (shiftedPartition r mu) (partitionAlternant r lam * h r (k : ℤ)) =
      if HorizontalStrip lam mu then 1 else 0 := by
  change naturalCoefficient (shiftedPartition r mu) (alternant (shiftedPartition r lam) * _) = _
  rw [alternant_mul_h_coefficient _ _ k (by
    rw [sum_shiftedPartition mu hmu, sum_shiftedPartition lam hlam]
    omega), pieriMatrix_det _ _ (shiftedPartition_strictAnti lam).antitone
      (shiftedPartition_strictAnti mu).antitone]
  simp only [← horizontalStrip_shifted_iff lam mu hlam hmu]

/-- Pieri in an alphabet containing all shapes of the total degree. -/
theorem horizontal_pieri_finite_enough {n : ℕ} (lam : Partition n) (k r : ℕ)
    (hr : n+k ≤ r) :
    schurPolynomial lam r * h r (k : ℤ) =
      ∑ mu ∈ horizontalExtensions lam k, schurPolynomial mu r := by
  have hlam : length lam ≤ r := (partition_length_le_size lam).trans (by omega)
  have hmu (mu : Partition (n+k)) : length mu ≤ r := (partition_length_le_size mu).trans hr
  have hsum_sym : (∑ mu ∈ horizontalExtensions lam k, schurPolynomial mu r).IsSymmetric := by
    apply (MvPolynomial.symmetricSubalgebra (Fin r) ℂ).sum_mem
    intro mu _
    exact schurPolynomial_isSymmetric mu r
  have hsum_hom : (∑ mu ∈ horizontalExtensions lam k, schurPolynomial mu r).IsHomogeneous (n+k) := by
    apply MvPolynomial.IsHomogeneous.sum
    intro mu _
    exact schurPolynomial_isHomogeneous mu r
  have hh_sym : (h r (k : ℤ)).IsSymmetric := by
    rw [← schurPolynomial_indiscrete]
    exact schurPolynomial_isSymmetric _ _
  have hh_hom : (h r (k : ℤ)).IsHomogeneous k := by
    rw [← schurPolynomial_indiscrete]
    exact schurPolynomial_isHomogeneous _ _
  apply sub_eq_zero.mp
  apply eq_zero_of_alternating_coefficients_zero _
    (((schurPolynomial_isSymmetric lam r).mul hh_sym).sub hsum_sym)
    (((schurPolynomial_isHomogeneous lam r).mul hh_hom).sub hsum_hom)
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
      (vandermonde r * ∑ mu ∈ horizontalExtensions lam k, schurPolynomial mu r) =
        if HorizontalStrip lam nu then 1 else 0 := by
    rw [Finset.mul_sum]
    change (∑ mu ∈ horizontalExtensions lam k, vandermonde r * schurPolynomial mu r).coeff _ = _
    rw [MvPolynomial.coeff_sum]
    change (∑ mu ∈ horizontalExtensions lam k,
      naturalCoefficient (shiftedPartition r nu) (vandermonde r * schurPolynomial mu r)) = _
    simp only [hc]
    simp [eq_comm]
  rw [mul_sub]
  change naturalCoefficient (shiftedPartition r nu)
    (vandermonde r * (schurPolynomial lam r * h r (k : ℤ))) -
      naturalCoefficient (shiftedPartition r nu)
        (vandermonde r * ∑ mu ∈ horizontalExtensions lam k, schurPolynomial mu r) = 0
  rw [← mul_assoc, schurPolynomial_characterization lam r hlam,
    partitionAlternant_mul_h_coefficient lam nu hlam (hmu nu), hc_sum, sub_self]

/-- A single sufficiently large specialization proves the identity in its
homogeneous stable degree. -/
theorem horizontal_pieri_stable : Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_stableType := by
  intro n lam k
  change DirectSum.of (fun n => stableDegree n) n (stableSchur lam) *
    DirectSum.of (fun n => stableDegree n) k (stableSchur (Nat.Partition.indiscrete k)) =
      ∑ mu ∈ horizontalExtensions lam k, DirectSum.of (fun n => stableDegree n) (n+k) (stableSchur mu)
  rw [DirectSum.of_mul_of, ← map_sum]
  apply congrArg (DirectSum.of (fun n => stableDegree n) (n+k))
  apply degreeSpecialization_injective (n+k) (n+k) le_rfl
  change (stableSchur lam).val (n+k) * (stableSchur (Nat.Partition.indiscrete k)).val (n+k) =
    (∑ mu ∈ horizontalExtensions lam k, stableSchur mu).val (n+k)
  simp only [stableSchur_specialization, Submodule.coe_sum, Finset.sum_apply]
  rw [schurPolynomial_indiscrete]
  exact horizontal_pieri_finite_enough lam k (n+k) le_rfl

/-- Every alphabet, including the empty alphabet, is obtained by specialization. -/
theorem horizontal_pieri_finite : Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_finiteType :=
  horizontal_pieri_finite_of_stable horizontal_pieri_stable

/-- Multiplicity one for the ordinary induced class function. -/
theorem horizontal_pieri_character : Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_characterType :=
  horizontal_pieri_character_of_stable horizontal_pieri_stable

section MultiplicityFree

variable {I G : Type*} [Fintype I] [Group G] [Fintype G]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- For a multiplicity-free irreducible character sum, the corresponding
representation is the actual direct sum. -/
theorem equiv_directSum_of_character
    (sigma : (i : I) → Representation ℂ G (V i)) (rho : Representation ℂ G W)
    (hirr : ∀ i, (sigma i).IsIrreducible)
    (hdist : ∀ i j, Nonempty ((sigma i).Equiv (sigma j)) → i = j)
    (hchar : ∀ g, rho.character g = ∑ i, (sigma i).character g) :
    Nonempty (rho.Equiv (Representation.directSum sigma)) := by
  classical
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  letI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  have horth (i j : I) :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, (sigma j).character g * (sigma i).character g⁻¹ =
        if j = i then 1 else 0 := by
    haveI := hirr i
    haveI := hirr j
    have he : Nonempty ((sigma i).Equiv (sigma j)) ↔ j = i := by
      constructor
      · intro h; exact (hdist i j h).symm
      · rintro rfl; exact ⟨Representation.Equiv.refl _⟩
    simpa only [he] using Representation.char_orthonormal (sigma j) (sigma i)
  have hmaps (i : I) : ∃ f : (sigma i).IntertwiningMap rho,
      ∃ p : rho.IntertwiningMap (sigma i), ∀ v, p (f v) = v := by
    haveI := hirr i
    have hdim : (Module.finrank ℂ ((sigma i).IntertwiningMap rho) : ℂ) = 1 := by
      rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank (sigma i) rho]
      simp_rw [hchar, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      simp only [horth, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hdim_nat : Module.finrank ℂ ((sigma i).IntertwiningMap rho) = 1 := by exact_mod_cast hdim
    obtain ⟨f, hf⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)
      (M := (sigma i).IntertwiningMap rho)).mp (by rw [hdim_nat]; omega)
    have hf_inj : Function.Injective f :=
      (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
    let fA := Representation.IntertwiningMap.equivLinearMapAsModule (sigma i) rho f
    obtain ⟨pA, hpA⟩ := MonoidAlgebra.exists_leftInverse_of_injective fA
      (LinearMap.ker_eq_bot.mpr hf_inj)
    let p := (Representation.IntertwiningMap.equivLinearMapAsModule rho (sigma i)).symm pA
    exact ⟨f, p, fun v => congrArg (fun t => t v) hpA⟩
  choose f p hpf using hmaps
  have hpf_zero (i j : I) (hij : i ≠ j) : (p i).comp (f j) = 0 := by
    haveI := hirr i
    haveI := hirr j
    rcases Representation.IsIrreducible.bijective_or_eq_zero ((p i).comp (f j)) with h | h
    · exact False.elim (hij (hdist j i ⟨((p i).comp (f j)).ofBijective h⟩).symm)
    · exact h
  let F : (Representation.directSum sigma).IntertwiningMap rho :=
    { toLinearMap := DirectSum.toModule ℂ I W (fun i => (f i).toLinearMap)
      isIntertwining' g := by
        apply DirectSum.linearMap_ext
        intro i
        ext v
        simp only [LinearMap.comp_apply, Representation.directSum_apply,
          DirectSum.lmap_lof, DirectSum.toModule_lof]
        exact Representation.IntertwiningMap.isIntertwining (sigma i) rho (f i) g v }
  have hFof (j : I) (v : V j) : F (DirectSum.of V j v) = f j v :=
    DirectSum.toModule_lof ℂ j v
  have hproj (i : I) (x : ⨁ i, V i) : p i (F x) = x i := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j v =>
      by_cases hji : j = i
      · subst j
        simpa only [hFof, DirectSum.of_eq_same] using hpf i v
      · have hz := congrArg (fun t : (sigma j).IntertwiningMap (sigma i) => t v)
          (hpf_zero i j (Ne.symm hji))
        simpa [hFof, DirectSum.of_apply, hji] using hz
    | add x y hx hy =>
      change p i (F (x+y)) = x i + y i
      rw [map_add, map_add, hx, hy]
  have hF : Function.Injective F := by
    intro x y hxy
    apply DFinsupp.ext
    intro i
    rw [← hproj i x, ← hproj i y, hxy]
  have hdim : Module.finrank ℂ (⨁ i, V i) = Module.finrank ℂ W := by
    rw [Module.finrank_directSum]
    have hh := hchar 1
    simp only [Representation.char_one] at hh
    exact_mod_cast hh.symm
  exact ⟨(F.ofBijective ⟨hF,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hF⟩).symm⟩

end MultiplicityFree


private theorem horizontalPieriInduced_character {n : ℕ} {lam : Partition n}
    (rho : Representation ℂ (SymmetricGroup n) (SpechtModule lam)) (k : ℕ)
    (g : SymmetricGroup (n+k)) :
    (Representation.ind (A := TensorProduct ℂ (SpechtModule lam) ℂ)
      (blockEmbedding n k) (horizontalPieriInput rho k)).character g =
      inducedExternal (representationClassFunction rho)
        (representationClassFunction (Representation.trivial ℂ (SymmetricGroup k) ℂ))
          (ConjClasses.mk g) := by
  exact congrFun (blockInduced_character rho
    (Representation.trivial ℂ (SymmetricGroup k) ℂ)) (ConjClasses.mk g)

/-- The actual induced representation is the direct sum with one copy of each
horizontal-strip extension. -/
theorem horizontal_pieri_module :
    Specs.AdvancedFiniteGroupRepresentations.horizontal_pieri_moduleType := by
  intro n lam k rho sigma hrho hsigma
  let tau := Representation.ind (A := TensorProduct ℂ (SpechtModule lam) ℂ)
    (blockEmbedding n k) (horizontalPieriInput rho k)
  change Nonempty (tau.Equiv (Representation.directSum
    (fun mu : {mu : Partition (n+k) // HorizontalStrip lam mu} => sigma mu.val)))
  apply equiv_directSum_of_character
    (fun mu : {mu : Partition (n+k) // HorizontalStrip lam mu} => sigma mu.val) tau
  · intro mu
    exact classification_irreducible mu.val (sigma mu.val) (hsigma mu.val)
  · intro mu nu he
    apply Subtype.ext
    exact classification_distinct mu.val nu.val (sigma mu.val) (sigma nu.val)
      (hsigma mu.val) (hsigma nu.val) he
  · intro g
    rw [horizontalPieriInduced_character rho k g]
    have hc := congrFun (horizontal_pieri_character lam k rho sigma hrho hsigma)
      (ConjClasses.mk g)
    simp only [Finset.sum_apply] at hc
    change inducedExternal (representationClassFunction rho)
      (representationClassFunction (Representation.trivial ℂ (SymmetricGroup k) ℂ))
        (ConjClasses.mk g) = ∑ mu ∈ horizontalExtensions lam k, (sigma mu).character g at hc
    rw [hc]
    exact Finset.sum_subtype (horizontalExtensions lam k)
      (fun mu => mem_horizontalExtensions lam mu) (fun mu => (sigma mu).character g)

end AdvancedFiniteGroupRepresentations
