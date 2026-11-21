import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.YoungPermutationCharacter
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.AlternatingCauchyKernel
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.FrobeniusCharacterFormula
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace AdvancedFiniteGroupRepresentations

abbrev frobeniusCoefficient := @Specs.AdvancedFiniteGroupRepresentations.frobeniusCoefficient

/-- Separate coefficient extraction turns the two Cauchy identities into the
bilinear orthogonality of the proposed coefficient functions. -/
theorem frobeniusCoefficient_orthogonal {n : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (lam mu : Partition n) (hlam : length lam ≤ r) (hmu : length mu ≤ r) :
    (∑ nu : Partition n, (zFactor nu : ℂ)⁻¹ *
      frobeniusCoefficient r lam nu * frobeniusCoefficient r mu nu) =
        if lam = mu then 1 else 0 := by
  classical
  have hk := alternating_cauchy_coefficient r hr lam mu hlam hmu
  change pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r mu)
    (PowerSeries.coeff n (PowerSeries.C (pairedVandermonde r) * cauchyKernel r)) = _ at hk
  rw [PowerSeries.coeff_C_mul, cauchy_identity_degree r hr n] at hk
  have hf (nu : Partition n) : pairedVandermonde r *
      ((zFactor nu : ℂ)⁻¹ • pairedPartitionPowerSum r nu) =
      (zFactor nu : ℂ)⁻¹ •
        (xAlphabet r (vandermonde r * partitionPowerSum r nu) *
          yAlphabet r (vandermonde r * partitionPowerSum r nu)) := by
    simp only [pairedVandermonde,
      Specs.AdvancedFiniteGroupRepresentations.pairedVandermonde,
      pairedPartitionPowerSum,
      Specs.AdvancedFiniteGroupRepresentations.pairedPartitionPowerSum,
      map_mul, mul_smul_comm]
    rw [mul_mul_mul_comm]
  rw [Finset.mul_sum] at hk
  simp_rw [hf] at hk
  have he : diagram lam = diagram mu ↔ lam = mu :=
    ⟨partition_eq_of_diagram_eq lam mu, fun h => congrArg diagram h⟩
  rw [he] at hk
  have hs : pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r mu)
      (∑ nu : Partition n, (zFactor nu : ℂ)⁻¹ •
        (xAlphabet r (vandermonde r * partitionPowerSum r nu) *
          yAlphabet r (vandermonde r * partitionPowerSum r nu))) =
      ∑ nu : Partition n, (zFactor nu : ℂ)⁻¹ *
        frobeniusCoefficient r lam nu * frobeniusCoefficient r mu nu := by
    unfold pairedNaturalCoefficient
      Specs.AdvancedFiniteGroupRepresentations.pairedNaturalCoefficient
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro nu _
    rw [MvPolynomial.coeff_smul]
    change (zFactor nu : ℂ)⁻¹ *
      pairedNaturalCoefficient (shiftedPartition r lam) (shiftedPartition r mu)
        (xAlphabet r (vandermonde r * partitionPowerSum r nu) *
          yAlphabet r (vandermonde r * partitionPowerSum r nu)) = _
    rw [pairedNaturalCoefficient_mul]
    exact (mul_assoc _ _ _).symm
  by_cases h : lam = mu <;> simpa only [h, ite_true, ite_false] using hs.symm.trans hk

/-- Set the last variable equal to zero, retaining the other variable names. -/
def specializeLast (r : ℕ) : Alphabet (r + 1) →ₐ[ℂ] Alphabet r :=
  MvPolynomial.killCompl (Fin.castSucc_injective (n := r))

@[simp] theorem specializeLast_X_castSucc {r : ℕ} (i : Fin r) :
    specializeLast r (MvPolynomial.X i.castSucc) = MvPolynomial.X i := by
  change MvPolynomial.killCompl (Fin.castSucc_injective r) (MvPolynomial.X i.castSucc) = _
  rw [← MvPolynomial.rename_X Fin.castSucc i]
  exact MvPolynomial.killCompl_rename_app (Fin.castSucc_injective r) (MvPolynomial.X i)

@[simp] theorem specializeLast_X_last (r : ℕ) :
    specializeLast r (MvPolynomial.X (Fin.last r)) = 0 := by
  simp only [specializeLast, MvPolynomial.killCompl, MvPolynomial.aeval_X]
  have h : Fin.last r ∉ Set.range (Fin.castSucc : Fin r → Fin (r + 1)) := by
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    simp only [Fin.val_castSucc, Fin.val_last] at this
    omega
  simp only [h, dite_false]

/-- The factor from the last variable is precisely one copy of each variable. -/
theorem specializeLast_vandermonde (r : ℕ) :
    specializeLast r (vandermonde (r + 1)) =
      (∏ i : Fin r, (MvPolynomial.X i : Alphabet r)) * vandermonde r := by
  rw [vandermonde_product, vandermonde_product]
  have hlast (i : Fin (r + 1)) : ¬ Fin.last r < i := not_lt_of_ge (Fin.le_last i)
  simp only [map_prod, map_sub, map_mul, apply_ite, ← Finset.filter_lt_eq_Ioi, Finset.prod_filter,
    Fin.prod_univ_castSucc, map_one, specializeLast_X_castSucc,
    specializeLast_X_last, Fin.castSucc_lt_castSucc_iff,
    Fin.castSucc_lt_last, hlast, ite_true, ite_false, sub_zero,
    Finset.prod_const_one, mul_one]
  rw [Finset.prod_mul_distrib, mul_comm]

/-- All positive power sums are unchanged when a new zero variable is removed. -/
theorem specializeLast_powerSum (r j : ℕ) (hj : 0 < j) :
    specializeLast r (powerSum (r + 1) j) = powerSum r j := by
  simp only [powerSum, Specs.AdvancedFiniteGroupRepresentations.powerSum,
    map_sum, map_add, map_pow, Fin.sum_univ_castSucc, specializeLast_X_castSucc,
    specializeLast_X_last, zero_pow hj.ne', add_zero]

theorem specializeLast_partitionPowerSum {n : ℕ} (r : ℕ) (nu : Partition n) :
    specializeLast r (partitionPowerSum (r + 1) nu) = partitionPowerSum r nu := by
  change specializeLast r (∏ j ∈ nu.parts.toFinset,
    powerSum (r + 1) j ^ cycleMultiplicity nu j) =
      ∏ j ∈ nu.parts.toFinset, powerSum r j ^ cycleMultiplicity nu j
  simp only [map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [specializeLast_powerSum r j (nu.parts_pos (Multiset.mem_toFinset.mp hj))]

/-- Coefficients with last exponent zero are computed by specialization. -/
theorem naturalCoefficient_specializeLast {r : ℕ} (a : Fin (r + 1) → ℕ)
    (ha : a (Fin.last r) = 0) (p : Alphabet (r + 1)) :
    naturalCoefficient a p =
      naturalCoefficient (fun i : Fin r => a i.castSucc) (specializeLast r p) := by
  change p.coeff (Finsupp.equivFunOnFinite.symm a) =
    (MvPolynomial.killCompl (Fin.castSucc_injective r) p).coeff
      (Finsupp.equivFunOnFinite.symm (fun i : Fin r => a i.castSucc))
  rw [MvPolynomial.coeff_killCompl]
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hlast : Fin.last r ∉ Set.range (Fin.castSucc : Fin r → Fin (r + 1)) := by
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
    simp [Finsupp.mapDomain_of_notMem_range _ _ hlast, ha]
  · simp only [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective r)]
    rfl

theorem frobeniusCoefficient_succ {n : ℕ} (lam nu : Partition n) (r : ℕ)
    (hlam : length lam ≤ r) :
    frobeniusCoefficient (r + 1) lam nu = frobeniusCoefficient r lam nu := by
  have hlast : shiftedPartition (r + 1) lam (Fin.last r) = 0 := by
    change rowLength lam r + (r + 1 - 1 - r) = 0
    rw [rowLength_zero_of_length_le lam r hlam]
    omega
  change naturalCoefficient (shiftedPartition (r + 1) lam)
    (vandermonde (r + 1) * partitionPowerSum (r + 1) nu) = _
  rw [naturalCoefficient_specializeLast _ hlast, map_mul,
    specializeLast_vandermonde, specializeLast_partitionPowerSum, mul_assoc]
  have hshift (i : Fin r) : shiftedPartition (r + 1) lam i.castSucc =
      1 + shiftedPartition r lam i := by
    change rowLength lam i.val + (r + 1 - 1 - i.val) =
      1 + (rowLength lam i.val + (r - 1 - i.val))
    have hi := i.isLt
    omega
  simp_rw [hshift]
  have hx : (∏ i : Fin r, (MvPolynomial.X i : Alphabet r)) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun _ : Fin r => 1)) 1 := by
    simpa using prod_X_pow_eq_monomial (fun _ : Fin r => 1)
  rw [hx]
  change (MvPolynomial.monomial _ 1 * _).coeff _ = _
  have he : Finsupp.equivFunOnFinite.symm (fun i : Fin r => 1 + shiftedPartition r lam i) =
      Finsupp.equivFunOnFinite.symm (fun _ : Fin r => 1) +
        Finsupp.equivFunOnFinite.symm (shiftedPartition r lam) := by
    ext i
    rfl
  rw [he, MvPolynomial.coeff_monomial_mul, one_mul]
  rfl

/-- Padding invariance includes the zero-row case, when admissible. -/
theorem frobeniusCoefficient_padding {n : ℕ} (lam nu : Partition n) (r s : ℕ)
    (hlam : length lam ≤ r) (hrs : r ≤ s) :
    frobeniusCoefficient s lam nu = frobeniusCoefficient r lam nu := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    rw [frobeniusCoefficient_succ lam nu s (hlam.trans hrs), ih]

@[simp] theorem frobeniusCoefficient_empty_zero :
    frobeniusCoefficient 0 emptyPartition emptyPartition = 1 := by
  change naturalCoefficient _ (vandermonde 0 * partitionPowerSum 0 emptyPartition) = 1
  rw [zero_vandermonde, empty_partitionPowerSum, one_mul]
  have h : Finsupp.equivFunOnFinite.symm (shiftedPartition 0 emptyPartition) = 0 := by
    ext i
    exact Fin.elim0 i
  simp [naturalCoefficient, Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient, h]

/-- The empty Specht module is a line with the inherited trivial action. -/
theorem frobenius_character_empty
    (ρ : Representation ℂ (SymmetricGroup 0) (SpechtModule emptyPartition))
    (hρ : InheritedSpechtAction emptyPartition ρ) (g : SymmetricGroup 0) :
    ρ.character g = frobeniusCoefficient 0 emptyPartition emptyPartition ∧
      frobeniusCoefficient 0 emptyPartition emptyPartition = 1 := by
  obtain ⟨e, _⟩ := classification_empty ρ hρ
  have hd : Module.finrank ℂ (SpechtModule emptyPartition) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  rw [zero_labels_trivial g, Representation.char_one, hd, Nat.cast_one,
    frobeniusCoefficient_empty_zero]
  exact ⟨rfl, rfl⟩

/-- Every nonempty row contributes at least one cell. -/
theorem partition_length_le_size {n : ℕ} (p : Partition n) : length p ≤ n := by
  have hlist (w : List ℕ) (hw : ∀ x ∈ w, 0 < x) : w.length ≤ w.sum := by
    induction w with
    | nil => simp
    | cons x w ih =>
      have hx := hw x (by simp)
      have ht := ih (fun y hy => hw y (by simp [hy]))
      simp only [List.length_cons, List.sum_cons]
      omega
  change (parts p).length ≤ n
  exact (hlist (parts p) (parts_positive p)).trans_eq (parts_sum p)

/-- A unitriangular change between orthonormal families over a field is the
identity. Descending induction also works over ℂ with the bilinear character
pairing; it does not require an unproved reality assertion. -/
theorem orthonormal_unitriangular_unique {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [PartialOrder I] [WellFoundedGT I]
    (B : V →ₗ[K] V →ₗ[K] K) (f h : I → V) (u : I → I → K)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0)
    (hh : ∀ i j, B (h i) (h j) = if i = j then 1 else 0)
    (hu : ∀ i j, ¬ i ≤ j → u i j = 0)
    (hdiag : ∀ i, u i i = 1)
    (hexp : ∀ i, h i = ∑ j : I, u i j • f j) : h = f := by
  classical
  have hpair (i j : I) : B (h i) (f j) = u i j := by
    rw [hexp i]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hf,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  funext i
  refine (show WellFounded ((· > ·) : I → I → Prop) from wellFounded_gt).induction
    (C := fun j => h j = f j) i ?_
  intro i ih
  have hz (j : I) (hji : j ≠ i) : u i j = 0 := by
    by_cases hij : i ≤ j
    · have hlt : i < j := lt_of_le_of_ne hij (Ne.symm hji)
      rw [← hpair, ← ih j hlt, hh, ite_eq_right (Ne.symm hji)]
    · exact hu i j hij
  rw [hexp i, Finset.sum_eq_single i]
  · rw [hdiag, one_smul]
  · intro j _ hji
    rw [hz j hji, zero_smul]
  · simp

/-- The canonical restriction of the tabloid action. -/
abbrev spechtRepresentation {n : ℕ} (p : Partition n) :=
  (spechtSubrepresentation p).toRepresentation

/-- An inherited realization is uniquely the canonical restriction. -/
theorem inheritedSpechtAction_eq {n : ℕ} (p : Partition n)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hρ : InheritedSpechtAction p ρ) : ρ = spechtRepresentation p := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact Subtype.ext (hρ g v)

/-- The concrete Hom space from A06 is the library's space of intertwiners. -/
def spechtHomIntertwiningEquiv {n : ℕ} (p q : Partition n) :
    SpechtHom p q ≃ₗ[ℂ]
      Representation.IntertwiningMap (spechtRepresentation p) (permutationRepresentation q) where
  toFun f := f.val.intertwiningMap_of_isIntertwiningMap _ _
    ((mem_spechtHomSpace_iff f.val).mp f.property)
  invFun f := ⟨f.toLinearMap, (mem_spechtHomSpace_iff f.toLinearMap).mpr
    (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v)⟩
  left_inv f := rfl
  right_inv f := by apply Representation.IntertwiningMap.ext; rfl
  map_add' f h := by apply Representation.IntertwiningMap.ext; rfl
  map_smul' a f := by apply Representation.IntertwiningMap.ext; rfl

open private classCharacter characterPair canonicalSpecht spechtCharacterBasis
  spechtCharacterBasis_apply specht_character_pair
  from MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtClassification

/-- Multiplicity here means the dimension of actual equivariant maps. -/
def youngSpechtMultiplicity {n : ℕ} (q p : Partition n) : ℕ :=
  Module.finrank ℂ (SpechtHom p q)

@[simp] theorem youngSpechtMultiplicity_diagonal {n : ℕ} (p : Partition n) :
    youngSpechtMultiplicity p p = 1 := diagonal_hom_finrank p

theorem youngSpechtMultiplicity_eq_zero {n : ℕ} (q p : Partition n)
    (h : ¬ dominates p q) : youngSpechtMultiplicity q p = 0 := by
  haveI : Subsingleton (SpechtHom p q) := ⟨fun f g =>
    (spechtHom_eq_zero_of_not_dominates h f).trans
      (spechtHom_eq_zero_of_not_dominates h g).symm⟩
  exact Module.finrank_eq_zero_of_subsingleton ℂ (SpechtHom p q)

/-- The character pairing computes the original equivariant-map multiplicity. -/
theorem permutationCharacter_pair {n : ℕ} (q p : Partition n) :
    characterPair (spechtRepresentation p) (classCharacter (permutationRepresentation q)) =
      (youngSpechtMultiplicity q p : ℂ) := by
  letI : Invertible (Nat.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  change (Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
    ∑ g : SymmetricGroup n,
      (permutationRepresentation q).character g * (spechtRepresentation p).character g⁻¹ = _
  rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
    ← (spechtHomIntertwiningEquiv p q).finrank_eq]
  rfl

/-- The actual tabloid character has the unitriangular Specht expansion supplied
by A06. This uses the accepted basis of class functions, with coefficients
computed by the trace pairing rather than postulated decompositions. -/
theorem permutationCharacter_specht_expansion {n : ℕ} (q : Partition n)
    (g : SymmetricGroup n) :
    (permutationRepresentation q).character g =
      ∑ p : Partition n, (youngSpechtMultiplicity q p : ℂ) *
        (spechtRepresentation p).character g := by
  classical
  let b := spechtCharacterBasis n
  have hc (p : Partition n) :
      b.repr (classCharacter (permutationRepresentation q)) p =
        (youngSpechtMultiplicity q p : ℂ) := by
    have h := congrArg (characterPair (spechtRepresentation p))
      (b.sum_repr (classCharacter (permutationRepresentation q)))
    simp only [b, map_sum, map_smul, spechtCharacterBasis_apply,
      specht_character_pair, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, permutationCharacter_pair] at h
    exact h
  have h := congrFun (b.sum_repr (classCharacter (permutationRepresentation q)))
    (ConjClasses.mk g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc,
    b, spechtCharacterBasis_apply] at h
  exact h.symm

/-- Every label lies in one of the nonempty rows of its tableau. -/
theorem labelRow_lt_length {n : ℕ} {p : Partition n} (t : Tableau p) (a : Fin n) :
    labelRow t a < length p := by
  have hc := (cell_iff p _ _).mp (t.symm a).property
  by_contra h
  have hz := rowLength_zero_of_length_le p (labelRow t a) (Nat.le_of_not_gt h)
  change (t.symm a).val.2 < rowLength p (labelRow t a) at hc
  omega

/-- The rows of a tableau, retaining every padded empty row. -/
def tableauRowDecomposition {n : ℕ} {p : Partition n} (r : ℕ)
    (hr : length p ≤ r) (t : Tableau p) :
    @RowDecomposition n r (fun i => rowLength p i.val) := by
  let f : Fin n → Fin r := fun a => ⟨labelRow t a, (labelRow_lt_length t a).trans_le hr⟩
  refine ⟨f, fun i => ?_⟩
  change Nat.card {a // f a = i} = rowLength p i.val
  rw [← rowLabels_card t i.val]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun a => Fin.ext_iff)

/-- Tabloids and ordered row decompositions are the same finite permutation set. -/
def tabloidRowDecompositionMap {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) : Tabloid p → @RowDecomposition n r (fun i => rowLength p i.val) :=
  Quotient.lift (tableauRowDecomposition r hr) (by
    intro t u h
    apply Subtype.ext
    funext a
    exact Fin.ext (congrFun h a))

@[simp] theorem tabloidRowDecompositionMap_tabloid {n : ℕ} {p : Partition n} (r : ℕ)
    (hr : length p ≤ r) (t : Tableau p) :
    tabloidRowDecompositionMap p r hr (tabloid t) = tableauRowDecomposition r hr t := rfl

theorem tabloidRowDecompositionMap_bijective {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) : Function.Bijective (tabloidRowDecompositionMap p r hr) := by
  constructor
  · intro q s h
    induction q using Quotient.inductionOn with
    | _ t =>
      induction s using Quotient.inductionOn with
      | _ u =>
        apply Quotient.sound
        funext a
        exact congrArg Fin.val (congrFun (congrArg Subtype.val h) a)
  · intro q
    let t := canonicalTableau p
    let v := tableauRowDecomposition r hr t
    have hf (i : Fin r) :
        Nonempty ({a : Fin n // v.val a = i} ≃ {a : Fin n // q.val a = i}) := by
      apply Finite.card_eq.mp
      exact (v.property i).trans (q.property i).symm
    let e : Fin n ≃ Fin n := Equiv.ofFiberEquiv (fun i => Classical.choice (hf i))
    have he (a : Fin n) : q.val (e a) = v.val a := Equiv.ofFiberEquiv_map _ a
    refine ⟨tabloid (t.trans e), ?_⟩
    apply Subtype.ext
    funext a
    apply Fin.ext
    exact (congrArg Fin.val (he (e.symm a))).symm.trans (by simp)

def tabloidRowDecompositionEquiv {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) : Tabloid p ≃ @RowDecomposition n r (fun i => rowLength p i.val) :=
  Equiv.ofBijective _ (tabloidRowDecompositionMap_bijective p r hr)

theorem tabloidRowDecompositionMap_smul {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) (g : SymmetricGroup n) (q : Tabloid p) :
    tabloidRowDecompositionMap p r hr (g • q) =
      g • tabloidRowDecompositionMap p r hr q := by
  induction q using Quotient.inductionOn with
  | _ t => rfl

/-- Extending the row correspondence linearly identifies the two actual actions. -/
def tabloidOrderedRowRepresentationEquiv {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) :
    (permutationRepresentation p).Equiv
      (@orderedRowRepresentation n r (fun i => rowLength p i.val)) := by
  let e := MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ (tabloidRowDecompositionEquiv p r hr)
  refine { toLinearEquiv := e, isIntertwining' := fun g => ?_ }
  apply LinearMap.ext
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simpa only [LinearMap.comp_apply, map_add] using congrArg₂ (· + ·) hx hy
  | single q z =>
    change e (permutationRepresentation p g (MonoidAlgebra.single q z)) =
      orderedRowRepresentation _ g (e (MonoidAlgebra.single q z))
    rw [permutationRepresentation_basis]
    simp only [e, MonoidAlgebra.mapDomainLinearEquiv_single]
    simp only [orderedRowRepresentation,
      Specs.AdvancedFiniteGroupRepresentations.orderedRowRepresentation,
      Representation.ofMulAction_single]
    change MonoidAlgebra.single _ z = MonoidAlgebra.single _ z
    congr 1
    exact tabloidRowDecompositionMap_smul p r hr g q

/-- Empty padding changes neither the tabloid character nor its trace model. -/
theorem youngPermutationCharacter_padded {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) (g : SymmetricGroup n) :
    youngPermutationCharacter (fun i : Fin r => rowLength p i.val) g =
      (permutationRepresentation p).character g :=
  (congrFun (Representation.char_iso (tabloidOrderedRowRepresentationEquiv p r hr)) g).symm

/-- Unitriangular expansion for the literal ordered-row characters used by C01. -/
theorem youngPermutationCharacter_specht_expansion {n : ℕ} (q : Partition n) (r : ℕ)
    (hr : length q ≤ r) (g : SymmetricGroup n) :
    youngPermutationCharacter (fun i : Fin r => rowLength q i.val) g =
      ∑ p : Partition n, (youngSpechtMultiplicity q p : ℂ) *
        (spechtRepresentation p).character g := by
  rw [youngPermutationCharacter_padded q r hr, permutationCharacter_specht_expansion]

/-- A representative is chosen only after the accepted surjectivity theorem. -/
def cycleRepresentative {n : ℕ} (ν : Partition n) : SymmetricGroup n :=
  Classical.choose (cyclePartition_surjective n ν)

@[simp] theorem cycleRepresentative_type {n : ℕ} (ν : Partition n) :
    cyclePartition (cycleRepresentative ν) = ν :=
  Classical.choose_spec (cyclePartition_surjective n ν)

theorem character_eq_of_cyclePartition_eq {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (SymmetricGroup n) V)
    (g h : SymmetricGroup n) (he : cyclePartition g = cyclePartition h) :
    ρ.character g = ρ.character h :=
  congrArg (classCharacter ρ) (ConjClasses.mk_eq_mk_iff_isConj.mpr
    ((isConj_iff_cyclePartition_eq g h).mpr he))

@[simp] theorem cyclePartition_inv {n : ℕ} (g : SymmetricGroup n) :
    cyclePartition g⁻¹ = cyclePartition g := by
  apply Nat.Partition.ext
  simp only [cyclePartition_parts, Equiv.Perm.cycleType_inv, Equiv.Perm.support_inv]

theorem symmetricGroup_character_inv {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (SymmetricGroup n) V)
    (g : SymmetricGroup n) : ρ.character g⁻¹ = ρ.character g :=
  character_eq_of_cyclePartition_eq ρ _ _ (cyclePartition_inv g)

/-- The class weight 1/z is obtained from the actual cardinalities. -/
theorem cyclePartition_fiber_weight {n : ℕ} (ν : Partition n) :
    (Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
      (Nat.card {g : SymmetricGroup n // cyclePartition g = ν} : ℂ) =
        (zFactor ν : ℂ)⁻¹ := by
  let g := cycleRepresentative ν
  have hg : cyclePartition g = ν := cycleRepresentative_type ν
  have hf : Nat.card {h : SymmetricGroup n // cyclePartition h = ν} =
      Nat.card {h : SymmetricGroup n // IsConj g h} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun h => by
      rw [isConj_iff_cyclePartition_eq, hg, eq_comm])
  have hc : Nat.card {h : SymmetricGroup n // IsConj g h} * zFactor ν =
      Nat.card (SymmetricGroup n) := by
    change Nat.card {h : SymmetricGroup n // IsConj g h} * centralizerFactor ν = _
    rw [← hg, centralizerFactor_cyclePartition]
    simpa only [Set.coe_ofPred, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using
      Equiv.Perm.card_isConj_mul_eq g
  have hz : (zFactor ν : ℂ) ≠ 0 := by
    have : zFactor ν ≠ 0 := by
      intro h
      rw [h, mul_zero] at hc
      exact Nat.card_pos.ne' hc.symm
    exact_mod_cast this
  have hn : (Nat.card (SymmetricGroup n) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [hf]
  have hc' : (Nat.card {h : SymmetricGroup n // IsConj g h} : ℂ) *
      (zFactor ν : ℂ) = (Nat.card (SymmetricGroup n) : ℂ) := by exact_mod_cast hc
  apply (mul_right_inj' hz).mp
  calc
    (zFactor ν : ℂ) * ((Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
      (Nat.card {h : SymmetricGroup n // IsConj g h} : ℂ)) =
      (Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
        ((Nat.card {h : SymmetricGroup n // IsConj g h} : ℂ) * (zFactor ν : ℂ)) := by ring
    _ = 1 := by rw [hc', inv_mul_cancel₀ hn]
    _ = _ := (mul_inv_cancel₀ hz).symm

/-- Summing a function of cycle type with class weights is group averaging. -/
theorem sum_cyclePartition {n : ℕ} (f : Partition n → ℂ) :
    (Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
      ∑ g : SymmetricGroup n, f (cyclePartition g) =
        ∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ * f ν := by
  classical
  rw [← Fintype.sum_fiberwise (@cyclePartition n)]
  have hf (ν : Partition n) :
      (∑ g : {g : SymmetricGroup n // cyclePartition g = ν}, f (cyclePartition g.val)) =
        (Nat.card {g : SymmetricGroup n // cyclePartition g = ν} : ℂ) * f ν := by
    have he (g : {g : SymmetricGroup n // cyclePartition g = ν}) :
        cyclePartition g.val = ν := g.property
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp_rw [hf]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [← mul_assoc, cyclePartition_fiber_weight]

/-- Actual canonical Specht trace as a function of cycle type. -/
def spechtCycleCharacter {n : ℕ} (p ν : Partition n) : ℂ :=
  (spechtRepresentation p).character (cycleRepresentative ν)

/-- Bilinear orthogonality of the actual Specht traces, with the same class
weights as the polynomial orthogonality theorem. Inversion is harmless since
permutations and their inverses have the same complete cycle partition. -/
theorem spechtCycleCharacter_orthogonal {n : ℕ} (p q : Partition n) :
    (∑ ν : Partition n, (zFactor ν : ℂ)⁻¹ *
      spechtCycleCharacter p ν * spechtCycleCharacter q ν) =
        if p = q then 1 else 0 := by
  classical
  have hv (p : Partition n) (g : SymmetricGroup n) :
      spechtCycleCharacter p (cyclePartition g) = (spechtRepresentation p).character g := by
    exact character_eq_of_cyclePartition_eq _ _ _ (cycleRepresentative_type _)
  have he := sum_cyclePartition
    (fun ν => spechtCycleCharacter p ν * spechtCycleCharacter q ν)
  simp_rw [hv] at he
  simp_rw [← mul_assoc] at he
  rw [← he]
  have h := specht_character_pair p q
  change (Nat.card (SymmetricGroup n) : ℂ)⁻¹ *
    ∑ g : SymmetricGroup n, (spechtRepresentation p).character g *
      (spechtRepresentation q).character g⁻¹ = _ at h
  simp_rw [symmetricGroup_character_inv] at h
  exact h

/-- Multiplication by a monomial shifts coefficients, with the stipulated zero
value whenever one of the resulting integer exponents is negative. -/
theorem naturalCoefficient_monomial_mul {r : ℕ} (a b : Fin r → ℕ) (p : Alphabet r) :
    naturalCoefficient a
      (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm b) 1 * p) =
        coefficient (fun i => (a i : ℤ) - (b i : ℤ)) p := by
  classical
  have he : Finsupp.equivFunOnFinite.symm b ≤ Finsupp.equivFunOnFinite.symm a ↔
      ∀ i, b i ≤ a i := Iff.rfl
  change (MvPolynomial.monomial _ 1 * p).coeff _ = _
  rw [MvPolynomial.coeff_monomial_mul']
  simp only [he]
  by_cases h : ∀ i, b i ≤ a i
  · rw [ite_eq_left h, one_mul, coefficient_of_nonnegative _ _ (fun i => sub_nonneg.mpr (by exact_mod_cast h i))]
    congr 1
    ext i
    change a i - b i = ((a i : ℤ) - (b i : ℤ)).toNat
    omega
  · rw [ite_eq_right h, coefficient_of_negative]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by omega⟩

/-- The determinant expansion, in the exact descending-staircase convention. -/
theorem vandermonde_monomial_sum (r : ℕ) :
    vandermonde r = ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
      MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i => staircase r (σ.symm i))) (1 : ℂ) := by
  classical
  change (Matrix.of fun i j : Fin r => (MvPolynomial.X i : Alphabet r) ^ staircase r j).det = _
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← prod_X_pow_eq_monomial]
  apply Fintype.prod_equiv σ
  intro i
  simp

/-- Every candidate coefficient is a signed sum of the literal power-sum
coefficients at λ+δ-wδ, including the negative-exponent convention. -/
theorem frobeniusCoefficient_determinant_expansion {n : ℕ} (r : ℕ) (lam nu : Partition n) :
    frobeniusCoefficient r lam nu =
      ∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ •
        coefficient (fun i => (shiftedPartition r lam i : ℤ) - staircase r (σ.symm i))
          (partitionPowerSum r nu) := by
  change naturalCoefficient (shiftedPartition r lam)
    (vandermonde r * partitionPowerSum r nu) = _
  rw [vandermonde_monomial_sum, Finset.sum_mul]
  unfold naturalCoefficient Specs.AdvancedFiniteGroupRepresentations.naturalCoefficient
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp only [h, one_smul]
    exact naturalCoefficient_monomial_mul _ _ _
  · simp only [h, Units.neg_smul, one_smul, neg_mul, MvPolynomial.coeff_neg, neg_inj]
    exact naturalCoefficient_monomial_mul _ _ _

/-- The first k positions maximize an antitone vector's sum among subsets of
that cardinality. This form also applies when k exceeds the number of rows. -/
theorem sum_antitone_le_prefix {r : ℕ} (f : Fin r → ℕ) (hf : Antitone f)
    (k : ℕ) (s : Finset (Fin r))
    (hc : s.card = (Finset.univ.filter (fun i : Fin r => i.val < k)).card) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), f i := by
  classical
  let t := Finset.univ.filter (fun i : Fin r => i.val < k)
  have hec : Fintype.card ↥(s \ t) = Fintype.card ↥(t \ s) := by
    simp only [Fintype.card_coe]
    exact Finset.card_sdiff_comm hc
  let e : ↥(s \ t) ≃ ↥(t \ s) := Fintype.equivOfCardEq hec
  have hle : (∑ a : ↥(s \ t), f a.val) ≤ ∑ a : ↥(t \ s), f a.val := by
    rw [← e.sum_comp (fun a : ↥(t \ s) => f a.val)]
    apply Finset.sum_le_sum
    intro a _
    apply hf
    have ha := (Finset.mem_sdiff.mp a.property).2
    have hb := (Finset.mem_sdiff.mp (e a).property).1
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha hb
    exact le_of_lt (show (e a).val < a.val from by change (e a).val.val < a.val.val; omega)
  simp only [Finset.sum_coe_sort] at hle
  have hs := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : s ∩ t ⊆ s)
  have ht := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : s ∩ t ⊆ t)
  rw [Finset.sdiff_inter_self_left] at hs
  rw [Finset.sdiff_inter_self_right] at ht
  change (∑ i ∈ s, f i) ≤ ∑ i ∈ t, f i
  omega

/-- Prefix equality for a strictly decreasing vector forces the maximizing
subset itself to be the initial subset. -/
theorem sum_strictAnti_eq_prefix_iff {r : ℕ} (f : Fin r → ℕ) (hf : StrictAnti f)
    (k : ℕ) (s : Finset (Fin r))
    (hc : s.card = (Finset.univ.filter (fun i : Fin r => i.val < k)).card) :
    (∑ i ∈ s, f i) = (∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), f i) ↔
      s = Finset.univ.filter (fun i : Fin r => i.val < k) := by
  classical
  constructor
  · intro heq
    let t := Finset.univ.filter (fun i : Fin r => i.val < k)
    have hec : Fintype.card ↥(s \ t) = Fintype.card ↥(t \ s) := by
      simp only [Fintype.card_coe]
      exact Finset.card_sdiff_comm hc
    let e : ↥(s \ t) ≃ ↥(t \ s) := Fintype.equivOfCardEq hec
    by_contra hne
    have hnon : (s \ t).Nonempty := Finset.sdiff_nonempty.mpr (by
      intro hsub
      exact hne (Finset.eq_of_subset_of_card_le hsub hc.ge))
    obtain ⟨a, ha⟩ := hnon
    haveI : Nonempty ↥(s \ t) := ⟨⟨a, ha⟩⟩
    have hlt : (∑ a : ↥(s \ t), f a.val) < ∑ a : ↥(t \ s), f a.val := by
      rw [← e.sum_comp (fun a : ↥(t \ s) => f a.val)]
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      intro a _
      apply hf
      have ha := (Finset.mem_sdiff.mp a.property).2
      have hb := (Finset.mem_sdiff.mp (e a).property).1
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha hb
      change (e a).val.val < a.val.val
      omega
    simp only [Finset.sum_coe_sort] at hlt
    have hs := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : s ∩ t ⊆ s)
    have ht := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : s ∩ t ⊆ t)
    rw [Finset.sdiff_inter_self_left] at hs
    rw [Finset.sdiff_inter_self_right] at ht
    change (∑ i ∈ s, f i) = ∑ i ∈ t, f i at heq
    omega
  · intro h
    rw [h]

/-- Any nonnegative row vector can be sorted and identified with the canonical
partition, without deleting the padded zero positions. -/
theorem exists_sorted_rowPartition {n r : ℕ} (b : Fin r → ℕ) (hs : (∑ i, b i) = n) :
    ∃ (σ : Equiv.Perm (Fin r)) (μ : Partition n),
      length μ ≤ r ∧ ∀ i, rowLength μ i.val = b (σ i) := by
  let σ := Tuple.sort (show Fin r → OrderDual ℕ from b)
  have hb : Antitone (fun i => b (σ i)) := Tuple.monotone_sort (show Fin r → OrderDual ℕ from b)
  have hstrict : StrictAnti (fun i => b (σ i) + staircase r i) := by
    intro i j hij
    have h := hb hij.le
    dsimp only at h
    have hi := i.isLt
    have hj := j.isLt
    change b (σ j) + (r - 1 - j.val) < b (σ i) + (r - 1 - i.val)
    change i.val < j.val at hij
    omega
  have hsum : (∑ i : Fin r, (b (σ i) + staircase r i)) = n + staircaseDegree r := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ b, hs]
    rfl
  obtain ⟨μ, hμ, he⟩ := strictAnti_eq_shiftedPartition _ hstrict hsum
  refine ⟨σ, μ, hμ, fun i => ?_⟩
  have h := congrFun he i
  change rowLength μ i.val + staircase r i = b (σ i) + staircase r i at h
  omega

/-- Power sums are unchanged under a permutation of variables. -/
theorem rename_powerSum {r : ℕ} (σ : Equiv.Perm (Fin r)) (j : ℕ) :
    MvPolynomial.rename σ (powerSum r j) = powerSum r j := by
  change MvPolynomial.rename σ (∑ i : Fin r, (MvPolynomial.X i : Alphabet r) ^ j) = _
  simp only [map_sum, map_pow, MvPolynomial.rename_X]
  exact Equiv.sum_comp σ (fun i => (MvPolynomial.X i : Alphabet r) ^ j)

theorem rename_partitionPowerSum {n r : ℕ} (σ : Equiv.Perm (Fin r)) (ν : Partition n) :
    MvPolynomial.rename σ (partitionPowerSum r ν) = partitionPowerSum r ν := by
  change MvPolynomial.rename σ (∏ j ∈ ν.parts.toFinset, powerSum r j ^ cycleMultiplicity ν j) = _
  simp only [map_prod, map_pow, rename_powerSum]
  rfl

theorem naturalCoefficient_partitionPowerSum_comp_perm {n r : ℕ}
    (b : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) (ν : Partition n) :
    naturalCoefficient (fun i => b (σ i)) (partitionPowerSum r ν) =
      naturalCoefficient b (partitionPowerSum r ν) := by
  have hd : (Finsupp.equivFunOnFinite.symm b).mapDomain σ.symm =
      Finsupp.equivFunOnFinite.symm (fun i => b (σ i)) := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  have hc := MvPolynomial.coeff_rename_mapDomain σ.symm σ.symm.injective
    (partitionPowerSum r ν) (Finsupp.equivFunOnFinite.symm b)
  rw [hd, rename_partitionPowerSum] at hc
  exact hc

/-- Coefficient extraction for an arbitrary nonnegative row vector becomes the
actual tabloid trace after sorting its sizes. -/
theorem naturalCoefficient_sorted_rowPartition {n r : ℕ} (b : Fin r → ℕ)
    (σ : Equiv.Perm (Fin r)) (μ ν : Partition n) (hμ : length μ ≤ r)
    (hrow : ∀ i, rowLength μ i.val = b (σ i)) :
    naturalCoefficient b (partitionPowerSum r ν) =
      (permutationRepresentation μ).character (cycleRepresentative ν) := by
  rw [← naturalCoefficient_partitionPowerSum_comp_perm b σ ν]
  have he : (fun i : Fin r => b (σ i)) = (fun i => rowLength μ i.val) := funext (fun i => (hrow i).symm)
  have hc := young_permutation_character_of_permutation
    (fun i : Fin r => rowLength μ i.val) (cycleRepresentative ν)
  rw [cycleRepresentative_type] at hc
  rw [he, ← hc, youngPermutationCharacter_padded μ r hμ]

/-- Strict decrease of the descending staircase, including empty alphabets. -/
theorem staircase_strictAnti (r : ℕ) : StrictAnti (staircase r) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  change r - 1 - j.val < r - 1 - i.val
  change i.val < j.val at hij
  omega

/-- Finite-vector and source initial-row sums agree under the row cutoff. -/
theorem sum_rowLength_prefix {n r : ℕ} (p : Partition n) (hr : length p ≤ r) (k : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), rowLength p i.val) =
      ∑ i ∈ Finset.range k, rowLength p i := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < r
    · have he : Finset.univ.filter (fun i : Fin r => i.val < k + 1) =
          insert ⟨k, hk⟩ (Finset.univ.filter (fun i : Fin r => i.val < k)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]
        omega
      rw [he, Finset.sum_insert (by simp), ih, Finset.sum_range_succ]
      simp only [Fin.val_mk]
      omega
    · have he : Finset.univ.filter (fun i : Fin r => i.val < k + 1) =
          Finset.univ.filter (fun i : Fin r => i.val < k) := by
        ext i
        have hi := i.isLt
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [he, ih, Finset.sum_range_succ,
        rowLength_zero_of_length_le p k (hr.trans (by omega)), add_zero]

/-- Permuting a vector cannot increase an initial sum beyond the sorted vector. -/
theorem prefix_sum_comp_perm_le {r : ℕ} (b : Fin r → ℕ) (hb : Antitone b)
    (σ : Equiv.Perm (Fin r)) (k : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), b (σ i)) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), b i := by
  classical
  rw [← Finset.sum_image σ.injective.injOn]
  apply sum_antitone_le_prefix b hb
  exact Finset.card_image_of_injective _ σ.injective

/-- The key source dominance argument: if b+ wδ = λ+δ and the sorted b is μ,
then μ dominates λ. Equality of the shapes forces w to be the identity. -/
theorem shiftedRows_dominates {n r : ℕ} (lam mu : Partition n)
    (hlam : length lam ≤ r) (hmu : length mu ≤ r)
    (b : Fin r → ℕ) (w σ : Equiv.Perm (Fin r))
    (hrow : ∀ i, rowLength mu i.val = b (σ i))
    (hb : ∀ i, b i + staircase r (w i) = rowLength lam i.val + staircase r i) :
    dominates mu lam ∧ (mu = lam → w = 1) := by
  classical
  let t (k : ℕ) := Finset.univ.filter (fun i : Fin r => i.val < k)
  have hsorted : Antitone (fun i : Fin r => rowLength mu i.val) :=
    fun i j hij => rowLength_antitone mu hij
  have hsort (k : ℕ) : (∑ i ∈ t k, b i) ≤ ∑ i ∈ t k, rowLength mu i.val := by
    have h := prefix_sum_comp_perm_le (fun i : Fin r => rowLength mu i.val) hsorted σ.symm k
    simpa only [hrow, Equiv.apply_symm_apply] using h
  have hstair (k : ℕ) :
      (∑ i ∈ t k, staircase r (w i)) ≤ ∑ i ∈ t k, staircase r i :=
    prefix_sum_comp_perm_le _ (staircase_strictAnti r).antitone w k
  have heq (k : ℕ) : (∑ i ∈ t k, b i) + (∑ i ∈ t k, staircase r (w i)) =
      (∑ i ∈ t k, rowLength lam i.val) + (∑ i ∈ t k, staircase r i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hb i)
  constructor
  · intro k
    have h1 := hsort k
    have h2 := hstair k
    have h3 := heq k
    dsimp only [t] at h1 h2 h3
    rw [sum_rowLength_prefix mu hmu k] at h1
    rw [sum_rowLength_prefix lam hlam k] at h3
    change (∑ i ∈ Finset.range k, rowLength lam i) ≤ ∑ i ∈ Finset.range k, rowLength mu i
    omega
  · intro hm
    have himage (k : ℕ) : (t k).image w = t k := by
      apply (sum_strictAnti_eq_prefix_iff (staircase r) (staircase_strictAnti r) k
        ((t k).image w) (Finset.card_image_of_injective _ w.injective)).mp
      rw [Finset.sum_image w.injective.injOn]
      have h1 := hsort k
      have h2 := hstair k
      have h3 := heq k
      rw [hm] at h1
      dsimp only [t] at h1 h2 h3 ⊢
      omega
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hle : (w i).val < i.val + 1 := by
      have hi : i ∈ t (i.val + 1) := by simp [t]
      have := Finset.mem_image_of_mem w hi
      rw [himage] at this
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hn : ¬ (w i).val < i.val := by
      intro hi
      have hw : w i ∈ t i.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [← himage i.val] at hw
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hw
      have he : j = i := w.injective hji
      subst j
      simpa [t] using hj
    change (w i).val = i.val
    omega

/-- Each determinant term is a combination of actual Specht traces supported
on shapes dominating λ. Its λ coefficient is one exactly for the identity term. -/
theorem frobeniusTerm_specht_expansion {n r : ℕ} (lam : Partition n)
    (hlam : length lam ≤ r) (w : Equiv.Perm (Fin r)) :
    ∃ a : Partition n → ℂ,
      (∀ nu : Partition n,
        coefficient (fun i => (shiftedPartition r lam i : ℤ) - staircase r (w i))
          (partitionPowerSum r nu) = ∑ p : Partition n, a p * spechtCycleCharacter p nu) ∧
      (∀ p, ¬ dominates p lam → a p = 0) ∧
      a lam = if w = 1 then 1 else 0 := by
  classical
  by_cases hw : w = 1
  · subst w
    refine ⟨fun p => (youngSpechtMultiplicity lam p : ℂ), ?_, ?_, ?_⟩
    · intro nu
      have he : (fun i : Fin r => (shiftedPartition r lam i : ℤ) - staircase r ((1 : Equiv.Perm (Fin r)) i)) =
          (fun i => (rowLength lam i.val : ℤ)) := by
        funext i
        change ((rowLength lam i.val + staircase r i : ℕ) : ℤ) - staircase r i = _
        omega
      rw [he, coefficient_natCast,
        naturalCoefficient_sorted_rowPartition _ 1 lam nu hlam (fun _ => rfl),
        permutationCharacter_specht_expansion]
      rfl
    · intro p hp
      dsimp only
      rw [youngSpechtMultiplicity_eq_zero lam p hp, Nat.cast_zero]
    · simp
  · by_cases h : ∀ i, staircase r (w i) ≤ shiftedPartition r lam i
    · let b : Fin r → ℕ := fun i => shiftedPartition r lam i - staircase r (w i)
      have hb (i : Fin r) : b i + staircase r (w i) = rowLength lam i.val + staircase r i :=
        Nat.sub_add_cancel (h i)
      have hs : (∑ i, b i) = n := by
        have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin r))) rfl (fun i _ => hb i)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Equiv.sum_comp w (staircase r), sum_rowLength_fin lam hlam] at hh
        omega
      obtain ⟨σ, mu, hmu, hrow⟩ := exists_sorted_rowPartition b hs
      obtain ⟨hdom, hstrict⟩ := shiftedRows_dominates lam mu hlam hmu b w σ hrow hb
      have hne : mu ≠ lam := fun hm => hw (hstrict hm)
      refine ⟨fun p => (youngSpechtMultiplicity mu p : ℂ), ?_, ?_, ?_⟩
      · intro nu
        rw [coefficient_of_nonnegative _ _ (fun i => sub_nonneg.mpr (by exact_mod_cast h i))]
        have he : (fun i : Fin r => ((shiftedPartition r lam i : ℤ) - staircase r (w i)).toNat) = b := by
          funext i
          dsimp only [b]
          omega
        rw [he, naturalCoefficient_sorted_rowPartition b σ mu nu hmu hrow,
          permutationCharacter_specht_expansion]
        rfl
      · intro p hp
        dsimp only
        rw [youngSpechtMultiplicity_eq_zero mu p (fun hpm => hp (dominance_trans p mu lam hpm hdom)),
          Nat.cast_zero]
      · dsimp only
        rw [youngSpechtMultiplicity_eq_zero mu lam
          (fun hlm => hne (dominance_antisymm mu lam hdom hlm)), Nat.cast_zero, ite_eq_right hw]
    · refine ⟨fun _ => 0, ?_, fun _ _ => rfl, by simp [hw]⟩
      intro nu
      rw [coefficient_of_negative]
      · simp
      · push Not at h
        obtain ⟨i, hi⟩ := h
        exact ⟨i, by omega⟩

/-- Combining the determinant terms gives a unitriangular expansion of the
coefficient candidates in the actual Specht traces. -/
theorem frobeniusCoefficient_unitriangular {n : ℕ} (r : ℕ)
    (hr : ∀ p : Partition n, length p ≤ r) :
    ∃ u : Partition n → Partition n → ℂ,
      (∀ lam nu, frobeniusCoefficient r lam nu =
        ∑ p : Partition n, u lam p * spechtCycleCharacter p nu) ∧
      (∀ lam p, ¬ dominates p lam → u lam p = 0) ∧
      (∀ lam, u lam lam = 1) := by
  classical
  choose a ha using (fun (lam : Partition n) (w : Equiv.Perm (Fin r)) =>
    frobeniusTerm_specht_expansion lam (hr lam) w)
  let u (lam p : Partition n) : ℂ :=
    ∑ w : Equiv.Perm (Fin r), Equiv.Perm.sign w • a lam w.symm p
  refine ⟨u, ?_, ?_, ?_⟩
  · intro lam nu
    rw [frobeniusCoefficient_determinant_expansion]
    simp_rw [(ha _ _).1, Finset.smul_sum]
    simp only [u, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro p _
    rw [smul_mul_assoc]
  · intro lam p hp
    simp only [u, (ha _ _).2.1 p hp, smul_zero, Finset.sum_const_zero]
  · intro lam
    simp only [u, (ha _ _).2.2]
    have hw (w : Equiv.Perm (Fin r)) :
        Equiv.Perm.sign w • (if w.symm = 1 then (1 : ℂ) else 0) =
          if w = 1 then 1 else 0 := by
      by_cases h : w = 1
      · subst w
        simp [Equiv.Perm.one_symm]
      · have hs : w.symm ≠ 1 := fun hh => h (by simpa only [Equiv.symm_symm, Equiv.Perm.one_symm] using congrArg Equiv.symm hh)
        simp [h, hs]
    simp_rw [hw]
    simp

/-- The bilinear class-function pairing in the source's class weights. -/
def cycleCharacterPairing (n : ℕ) :
    (Partition n → ℂ) →ₗ[ℂ] (Partition n → ℂ) →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun h := ∑ nu : Partition n, (zFactor nu : ℂ)⁻¹ * f nu * h nu
      map_add' h k := by simp [mul_add, Finset.sum_add_distrib]
      map_smul' a h := by
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm] }
  map_add' f g := by
    ext h
    simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' a f := by
    ext h
    simp [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- First identify all shapes simultaneously in an alphabet large enough to
contain every partition of n. -/
theorem frobeniusCoefficient_eq_spechtCycleCharacter {n : ℕ} (r : ℕ)
    (hr : 1 ≤ r) (hn : n ≤ r) (lam nu : Partition n) :
    frobeniusCoefficient r lam nu = spechtCycleCharacter lam nu := by
  classical
  letI : PartialOrder (Partition n) :=
    { le p q := dominates q p
      le_refl p := dominance_refl p
      le_trans p q s hpq hqs := dominance_trans s q p hqs hpq
      le_antisymm p q hpq hqp := dominance_antisymm p q hqp hpq }
  have hlen (p : Partition n) : length p ≤ r := (partition_length_le_size p).trans hn
  obtain ⟨u, hexp, hu, hdiag⟩ := frobeniusCoefficient_unitriangular r hlen
  have hh : (fun p : Partition n => frobeniusCoefficient r p) = spechtCycleCharacter := by
    apply orthonormal_unitriangular_unique (cycleCharacterPairing n) spechtCycleCharacter
      (fun p : Partition n => frobeniusCoefficient r p) u
    · intro p q
      by_cases hpq : p = q <;>
        simpa [cycleCharacterPairing, hpq] using spechtCycleCharacter_orthogonal p q
    · intro p q
      by_cases hpq : p = q <;>
        simpa [cycleCharacterPairing, hpq] using
          frobeniusCoefficient_orthogonal r hr p q (hlen p) (hlen q)
    · exact hu
    · exact hdiag
    · intro p
      funext ν
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hexp p ν
  exact congrFun (congrFun hh lam) nu

/-- Frobenius's formula for the trace of the original Specht module, with the
source's full row cutoff, arbitrary cycle type, and every inherited realization. -/
theorem frobenius_character_formula {n : ℕ} (lam nu : Partition n) (r : ℕ)
    (hr : 1 ≤ r) (hlam : length lam ≤ r)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule lam))
    (hρ : InheritedSpechtAction lam ρ) (g : SymmetricGroup n)
    (hg : cyclePartition g = nu) :
    ρ.character g = frobeniusCoefficient r lam nu := by
  let R := max r n
  have hR : 1 ≤ R := hr.trans (Nat.le_max_left _ _)
  have hn : n ≤ R := Nat.le_max_right _ _
  calc
    ρ.character g = spechtCycleCharacter lam nu := by
      rw [inheritedSpechtAction_eq lam ρ hρ]
      exact character_eq_of_cyclePartition_eq _ _ _ (hg.trans (cycleRepresentative_type nu).symm)
    _ = frobeniusCoefficient R lam nu :=
      (frobeniusCoefficient_eq_spechtCycleCharacter R hR hn lam nu).symm
    _ = frobeniusCoefficient r lam nu :=
      frobeniusCoefficient_padding lam nu r R hlam (Nat.le_max_left _ _)

end AdvancedFiniteGroupRepresentations
