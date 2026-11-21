import MathGenome.Internal.Specs.D05.M10.InvariantFactors.CompanionPresentation
import MathGenome.Internal.D05.M10.Companion
import MathGenome.Internal.D05.M10.InvariantFactorComputation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.Pi.Units

noncomputable section
set_option maxHeartbeats 800000
open Polynomial Matrix
open scoped BigOperators
namespace D05.M10.InvariantFactors.CompanionPresentation
open Classical
open Specs.D05.M10.InvariantFactors.CompanionPresentation
open D05.M10.Smith D05.M10.InvariantFactorComputation

variable {K : Type*} [Field K]

/-- The relations x e_j - e_(j+1) have a unit maximal minor, in every
characteristic. This is the determinantal version of eliminating those relations. -/
lemma companion_unit_minor (d : K[X]) {k : ℕ} (hk : k < d.natDegree) :
    ∃ (ρ κ : Fin k → Fin d.natDegree),
      IsUnit (((Specs.D05.M10.Companion.companionMatrix_value K d).charmatrix.submatrix ρ κ).det) := by
  let ρ : Fin k → Fin d.natDegree := fun i => ⟨i.val + 1, by omega⟩
  let κ : Fin k → Fin d.natDegree := fun i => ⟨i.val, by omega⟩
  let M := (Specs.D05.M10.Companion.companionMatrix_value K d).charmatrix.submatrix ρ κ
  have hentry (i j : Fin k) : M i j =
      (if i.val + 1 = j.val then X else 0) -
        (if i.val = j.val then 1 else 0) := by
    have hj : j.val + 1 ≠ d.natDegree := by omega
    simp [M, ρ, κ, Matrix.charmatrix_apply, Matrix.diagonal_apply,
      Specs.D05.M10.Companion.companionMatrix_value, hj, Fin.ext_iff]
  have htri : M.IsUpperTriangular := by
    intro i j hji
    have hlt : j.val < i.val := hji
    rw [hentry]
    simp [show i.val + 1 ≠ j.val by omega, show i.val ≠ j.val by omega]
  have hdiag (i : Fin k) : M i i = -1 := by rw [hentry]; simp
  refine ⟨ρ, κ, ?_⟩
  change IsUnit M.det
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (isUnit_one.neg).pow k

lemma companion_minor_gcd (d : K[X]) {k : ℕ} (hk : k < d.natDegree) :
    minorGcd (Specs.D05.M10.Companion.companionMatrix_value K d).charmatrix k = 1 := by
  let M := (Specs.D05.M10.Companion.companionMatrix_value K d).charmatrix
  obtain ⟨ρ, κ, hu⟩ := companion_unit_minor d hk
  have htop : minorIdeal M k = ⊤ := Ideal.eq_top_of_isUnit_mem _
    (MinorIdeals.minor_mem M ρ κ) hu
  apply MinorIdeals.minorGcd_eq_monic_generator M k 1 (monic_one)
  simpa using htop

theorem companion_reduction :
    Specs.D05.M10.InvariantFactors.CompanionPresentation.companion_reduction := by
  intro K _ d hd hpos
  obtain ⟨_, _, _, ops, f, hred, hg, htop, _, _⟩ :=
    D05.M10.InvariantFactorComputation.characteristic_smith K d.natDegree
      (Specs.D05.M10.Companion.companionMatrix_value K d)
  have hchar := (D05.M10.Companion.matrix_polynomials d hd hpos).2
  rw [hchar] at htop
  have hf : f = companionEntries d := by
    funext i
    by_cases hi : i < d.natDegree
    · rw [hg.2.2.2 i hi]
      by_cases hs : i < d.natDegree - 1
      · rw [companion_minor_gcd d (by omega), companion_minor_gcd d hi]
        simp [companionEntries, hs]
      · have he : i + 1 = d.natDegree := by omega
        rw [he, htop, companion_minor_gcd d hi]
        simp [companionEntries, hs, hi]
    · rw [hred.2.2.1.2.1 i (by omega)]
      simp [companionEntries, hi, show ¬i < d.natDegree - 1 by omega]
  exact ⟨ops, hf ▸ hred⟩

/-- Every permitted elementary operation is multiplication by units over K[x]. -/
lemma operation_equivalence {n : ℕ} (op : Operation K n n)
    (M : Matrix (Fin n) (Fin n) K[X]) : Equivalent M (op.apply M) := by
  cases op with
  | swapRows i j =>
    let P : Matrix (Fin n) (Fin n) K[X] := (1 : Matrix (Fin n) (Fin n) K[X]).submatrix (Equiv.swap i j) id
    have hh : P * P = 1 := by ext a b : 1; simp [P, Matrix.mul_apply, Matrix.one_apply, Equiv.swap_apply_eq_iff]
    refine ⟨⟨P, P, hh, hh⟩, 1, ?_⟩
    ext a b : 1
    simp [P, Operation.apply, Matrix.mul_apply, Matrix.one_apply]
  | swapCols i j =>
    let P : Matrix (Fin n) (Fin n) K[X] := (1 : Matrix (Fin n) (Fin n) K[X]).submatrix id (Equiv.swap i j)
    have hh : P * P = 1 := by ext a b : 1; simp [P, Matrix.mul_apply, Matrix.one_apply]
    refine ⟨1, ⟨P, P, hh, hh⟩, ?_⟩
    ext a b : 1
    simp [P, Operation.apply, Matrix.mul_apply, Matrix.one_apply]
  | addRow i j h q =>
    have hu : IsUnit (Matrix.transvection i j q : Matrix (Fin n) (Fin n) K[X]) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [Matrix.det_transvection_of_ne i j h q]
      exact isUnit_one
    refine ⟨hu.unit, 1, ?_⟩
    ext a b : 1
    by_cases ha : a = i
    · subst a; simp [Operation.apply]
    · simp [Operation.apply, ha]
  | addCol i j h q =>
    have hu : IsUnit (Matrix.transvection j i q : Matrix (Fin n) (Fin n) K[X]) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [Matrix.det_transvection_of_ne j i h.symm q]
      exact isUnit_one
    refine ⟨1, hu.unit, ?_⟩
    ext a b : 1
    by_cases hb : b = i
    · subst b; simp [Operation.apply]
    · simp [Operation.apply, hb]
  | scaleRow i c =>
    have hu : IsUnit (Matrix.diagonal (fun a : Fin n => if a = i then C (c : K) else 1)) := by
      apply Matrix.isUnit_diagonal.mpr
      apply Pi.isUnit_iff.mpr
      intro a
      split_ifs
      · exact c.isUnit.map C
      · exact isUnit_one
    refine ⟨hu.unit, 1, ?_⟩
    ext a b : 1
    by_cases ha : a = i <;> simp [Operation.apply, Matrix.diagonal_mul, ha]
  | scaleCol i c =>
    have hu : IsUnit (Matrix.diagonal (fun a : Fin n => if a = i then C (c : K) else 1)) := by
      apply Matrix.isUnit_diagonal.mpr
      apply Pi.isUnit_iff.mpr
      intro a
      split_ifs
      · exact c.isUnit.map C
      · exact isUnit_one
    refine ⟨1, hu.unit, ?_⟩
    ext a b : 1
    by_cases hb : b = i <;> simp [Operation.apply, Matrix.mul_diagonal, hb, mul_comm]

lemma equivalent_trans {I : Type*} [Fintype I] [DecidableEq I]
    {M N P : Matrix I I K[X]} (h : Equivalent M N) (h' : Equivalent N P) :
    Equivalent M P := by
  obtain ⟨U, V, rfl⟩ := h
  obtain ⟨U', V', h'⟩ := h'
  exact ⟨U' * U, V * V', by simpa [Units.val_mul, Matrix.mul_assoc] using h'⟩

lemma run_equivalence {n : ℕ} (ops : List (Operation K n n))
    (M : Matrix (Fin n) (Fin n) K[X]) : Equivalent M (run ops M) := by
  induction ops generalizing M with
  | nil => exact ⟨1, 1, by simp [run]⟩
  | cons op ops ih => exact equivalent_trans (operation_equivalence op M) (ih (op.apply M))

theorem companion_equivalence :
    Specs.D05.M10.InvariantFactors.CompanionPresentation.companion_equivalence := by
  intro K _ d hd hpos
  obtain ⟨ops, hred⟩ := companion_reduction d hd hpos
  rw [← hred.2.2.2]
  exact run_equivalence ops _

lemma charmatrix_blocks {s : ℕ} (d : Fin s → K[X]) :
    (companionBlocks d).charmatrix = Matrix.blockDiagonal'
      (fun i => (Specs.D05.M10.Companion.companionMatrix_value K (d i)).charmatrix) := by
  classical
  change Matrix.diagonal (fun _ => X) - (Matrix.blockDiagonal'
    (fun i => Specs.D05.M10.Companion.companionMatrix_value K (d i))).map C = _
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.scalar_apply]
  rw [Matrix.blockDiagonal'_map _ C (map_zero C)]
  rw [← Matrix.blockDiagonal'_diagonal (fun i (_ : Fin (d i).natDegree) => (X : K[X]))]
  rw [← Matrix.blockDiagonal'_sub]
  rfl

lemma companion_diagonal (d : K[X]) :
    rectDiagonal d.natDegree d.natDegree (companionEntries d) =
      Matrix.diagonal (fun j : Fin d.natDegree => if j.val + 1 = d.natDegree then d else 1) := by
  ext i j : 1
  by_cases hij : i = j
  · subst j
    simp only [rectDiagonal, Matrix.diagonal_apply_eq, ite_true, companionEntries]
    split_ifs <;> first | rfl | omega
  · simp [rectDiagonal, Matrix.diagonal_apply_ne _ hij, show i.val ≠ j.val from fun h => hij (Fin.ext h)]

theorem block_equivalence :
    Specs.D05.M10.InvariantFactors.CompanionPresentation.block_equivalence := by
  intro K _ s d hd hp
  classical
  have h (i : Fin s) := companion_equivalence (d i) (hd i) (hp i)
  choose U V hUV using h
  let f := Matrix.blockDiagonal'RingHom (fun i => Fin (d i).natDegree) K[X]
  let u : (Matrix (BlockIndex d) (BlockIndex d) K[X])ˣ :=
    Units.map f.toMonoidHom (MulEquiv.piUnits.symm U)
  let v : (Matrix (BlockIndex d) (BlockIndex d) K[X])ˣ :=
    Units.map f.toMonoidHom (MulEquiv.piUnits.symm V)
  refine ⟨u, v, ?_⟩
  change Matrix.blockDiagonal' (fun i => (U i).val) * _ * Matrix.blockDiagonal' (fun i => (V i).val) = _
  rw [charmatrix_blocks, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  simp only [hUV, companion_diagonal, Matrix.blockDiagonal'_diagonal]
  rfl

/-- Separate the last relation in each nonempty block from the unit relations. -/
def splitBlockIndex {s : ℕ} (d : Fin s → K[X]) (hp : ∀ i, 0 < (d i).natDegree) :
    BlockIndex d ≃ (Σ i, Fin ((d i).natDegree - 1)) ⊕ Fin s where
  toFun z := if h : z.2.val < (d z.1).natDegree - 1 then
    Sum.inl ⟨z.1, ⟨z.2.val, h⟩⟩ else Sum.inr z.1
  invFun z := match z with
    | Sum.inl ⟨i, j⟩ => ⟨i, ⟨j.val, by have := j.isLt; omega⟩⟩
    | Sum.inr i => ⟨i, ⟨(d i).natDegree - 1, by have := hp i; omega⟩⟩
  left_inv := by
    rintro ⟨i, j⟩
    dsimp
    split_ifs with h
    · rfl
    · change (⟨i, ⟨(d i).natDegree - 1, _⟩⟩ : BlockIndex d) = ⟨i, j⟩
      congr 1
      apply Fin.ext
      have := j.isLt
      dsimp
      omega
  right_inv := by
    rintro (⟨i, j⟩ | i)
    · simp [j.isLt]
    · simp

lemma sorted_block_diagonal {s : ℕ} (d : Fin s → K[X])
    (hp : ∀ i, 0 < (d i).natDegree) :
    ∃ (t : ℕ) (e : Fin (t+s) ≃ BlockIndex d),
      t = ∑ i, ((d i).natDegree - 1) ∧ t+s = ∑ i, (d i).natDegree ∧
      (blockDiagonalPresentation d).submatrix e e =
        rectDiagonal (t+s) (t+s) (chainEntries d t) := by
  classical
  let A := Σ i, Fin ((d i).natDegree - 1)
  let t := Fintype.card A
  let a : Fin t ≃ A := (Fintype.equivFin A).symm
  let e : Fin (t+s) ≃ BlockIndex d :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr a (Equiv.refl (Fin s)))).trans
      (splitBlockIndex d hp).symm
  have ht : t = ∑ i, ((d i).natDegree - 1) := by simp [t, A, Fintype.card_sigma]
  have hsize : t+s = ∑ i, (d i).natDegree := by
    calc
      t+s = (∑ i, ((d i).natDegree - 1)) + ∑ _i : Fin s, 1 := by simp [ht]
      _ = ∑ i, ((d i).natDegree - 1 + 1) := (Finset.sum_add_distrib).symm
      _ = _ := Finset.sum_congr rfl (fun i _ => by have := hp i; omega)
  have el (j : Fin t) : e (Fin.castAdd s j) =
      ⟨(a j).1, ⟨(a j).2.val, by have := (a j).2.isLt; omega⟩⟩ := by
    dsimp [e, splitBlockIndex]
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp only [Equiv.sumCongr_apply, Sum.map_inl]
    rfl
  have er (j : Fin s) : e (Fin.natAdd t j) =
      ⟨j, ⟨(d j).natDegree - 1, by have := hp j; omega⟩⟩ := by
    dsimp [e, splitBlockIndex]
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  refine ⟨t, e, ht, hsize, ?_⟩
  change (Matrix.diagonal _).submatrix e e = _
  rw [Matrix.submatrix_diagonal_equiv]
  have hdiag : (fun ij => if ij.2.val + 1 = (d ij.1).natDegree then d ij.1 else 1) ∘ e =
      fun i : Fin (t+s) => chainEntries d t i.val := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Function.comp_apply, el]
      have hj := (a j).2.isLt
      simp [chainEntries, show ¬ (a j).2.val + 1 = (d (a j).1).natDegree by omega, j.isLt]
    · rw [Function.comp_apply, er]
      have hdj := hp j
      simp [chainEntries, show (d j).natDegree - 1 + 1 = (d j).natDegree by omega,
        show ¬ t + j.val < t by omega, show t + j.val < t+s by omega]
  rw [hdiag]
  ext i j : 1
  simp [Matrix.diagonal_apply, rectDiagonal, Fin.ext_iff]

lemma equivalent_submatrix {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {M N : Matrix I I K[X]}
    (e : J ≃ I) (h : Equivalent M N) : Equivalent (M.submatrix e e) (N.submatrix e e) := by
  obtain ⟨U, V, hUV⟩ := h
  let f := (Matrix.reindexRingEquiv K[X] e.symm).toMonoidHom
  refine ⟨Units.map f U, Units.map f V, ?_⟩
  change (U.val.submatrix e e) * (M.submatrix e e) * (V.val.submatrix e e) = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hUV]

lemma chainEntries_chain {s : ℕ} (d : Fin s → K[X]) (t : ℕ)
    (hd : ∀ i, (d i).Monic) (hc : ∀ i j, i ≤ j → d i ∣ d j) :
    DiagonalChain (chainEntries d t) (t+s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    dsimp [chainEntries]
    split_ifs
    · exact monic_one
    · exact hd _
  · intro i hi
    simp [chainEntries, show ¬i < t by omega, show ¬i < t+s by omega]
  · intro i j hij
    by_cases hj : j < t+s
    · by_cases hi : i < t
      · simp [chainEntries, hi]
      · by_cases hjt : j < t
        · omega
        · simp only [chainEntries, hi, hjt, hj, show i < t+s by omega, ↓reduceDIte]
          apply hc
          exact Nat.sub_le_sub_right hij t
    · simp [chainEntries, hj, show ¬j < t by omega]

lemma equivalent_computes {n : ℕ} {M : Matrix (Fin n) (Fin n) K[X]}
    {g : ℕ → K[X]} (hc : DiagonalChain g n)
    (h : Equivalent M (rectDiagonal n n g)) : ComputesMinors M n g := by
  obtain ⟨U, V, hUV⟩ := h
  exact MinorIdeals.transformed_gcd K n n n g M U V le_rfl le_rfl hc hUV

/-- Determinantal divisors identify every normalized reduction, rather than
merely a reduction selected by an existence theorem. -/
lemma computed_entries_unique {n : ℕ} {M : Matrix (Fin n) (Fin n) K[X]}
    {g : ℕ → K[X]} (hc : DiagonalChain g n) (hg : ComputesMinors M n g)
    {ops : List (Operation K n n)} {r : ℕ} {f : ℕ → K[X]}
    (hred : SmithReduction M ops r f) : r = n ∧ f = g := by
  have hf := D05.M10.InvariantFactorComputation.reduction_computes K n n M ops r f hred
  have hr : r = n := by
    apply le_antisymm hred.1
    by_contra h
    have hn : r < n := by omega
    have hz : minorGcd M n = 0 := hf.2.1 n hn
    have hnz := D05.M10.InvariantFactorComputation.gcd_ne_zero_of_le hc hg le_rfl
    exact hnz hz
  refine ⟨hr, funext fun i => ?_⟩
  by_cases hi : i < n
  · rw [hf.2.2.2 i (by omega), hg.2.2.2 i hi]
  · rw [hred.2.2.1.2.1 i (by omega), hc.2.1 i (by omega)]

lemma chainEntries_list {s : ℕ} (d : Fin s → K[X]) (t : ℕ) :
    List.ofFn (fun i : Fin (t+s) => chainEntries d t i.val) =
      List.replicate t 1 ++ List.ofFn d := by
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin t => chainEntries d t i.val) ++ _) = _
  have hleft : (fun i : Fin t => chainEntries d t i.val) = fun _ => 1 := by
    funext i
    simp [chainEntries, i.isLt]
  have hright : (fun i : Fin s => chainEntries d t (Fin.natAdd t i).val) = d := by
    funext i
    simp [chainEntries, show ¬t+i.val < t by omega, show t+i.val < t+s by omega]
  rw [hleft, hright, List.ofFn_const]

lemma nonunit_chain_list {s : ℕ} (d : Fin s → K[X]) (t : ℕ)
    (hd : ∀ i, (d i).Monic) (hp : ∀ i, 0 < (d i).natDegree) :
    (List.ofFn (fun i : Fin (t+s) => chainEntries d t i.val)).filter
      (fun p => decide (¬ IsUnit p)) = List.ofFn d := by
  classical
  have hnu (i : Fin s) : ¬ IsUnit (d i) := by
    intro hu
    have he := (hd i).isUnit_iff.mp hu
    have := hp i
    simp [he] at this
  have hfilter : (List.ofFn d).filter (fun p => decide (¬ IsUnit p)) = List.ofFn d := by
    apply List.filter_eq_self.mpr
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    simp [hnu i]
  rw [chainEntries_list, List.filter_append, hfilter]
  simp

theorem block_smith : Specs.D05.M10.InvariantFactors.CompanionPresentation.block_smith := by
  intro K _ s d hd hp hc
  classical
  obtain ⟨t, e, ht, hsize, hdiag⟩ := sorted_block_diagonal d hp
  have heq := equivalent_submatrix e (block_equivalence d hd hp)
  rw [hdiag] at heq
  have hchain := chainEntries_chain d t hd hc
  have hcomp := equivalent_computes hchain heq
  refine ⟨t, e, ht, hsize, heq, hcomp, ?_⟩
  intro ops r f hred
  obtain ⟨hr, hf⟩ := computed_entries_unique hchain hcomp hred
  exact ⟨hr, hf, by rw [hf]; exact nonunit_chain_list d t hd hp⟩

/-- Reindexing a square matrix by a permutation is invertible polynomial
row/column multiplication. This also covers empty matrices. -/
lemma equivalent_permutation {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I K[X]) (p : Equiv.Perm I) : Equivalent M (M.submatrix p p) := by
  let P : Matrix I I K[X] := (1 : Matrix I I K[X]).submatrix p id
  let P' : Matrix I I K[X] := (1 : Matrix I I K[X]).submatrix p.symm id
  let Q : Matrix I I K[X] := (1 : Matrix I I K[X]).submatrix id p
  let Q' : Matrix I I K[X] := (1 : Matrix I I K[X]).submatrix id p.symm
  have hP : P * P' = 1 := by
    ext i j : 1
    simp [P, P', Matrix.mul_apply, Matrix.one_apply, ← Equiv.eq_symm_apply]
  have hP' : P' * P = 1 := by
    ext i j : 1
    simp [P, P', Matrix.mul_apply, Matrix.one_apply, ← Equiv.eq_symm_apply]
  have hQ : Q * Q' = 1 := by
    ext i j : 1
    simp [Q, Q', Matrix.mul_apply, Matrix.one_apply]
  have hQ' : Q' * Q = 1 := by
    ext i j : 1
    simp [Q, Q', Matrix.mul_apply, Matrix.one_apply]
  refine ⟨⟨P, P', hP, hP'⟩, ⟨Q, Q', hQ, hQ'⟩, ?_⟩
  ext i j : 1
  simp [P, Q, Matrix.mul_apply, Matrix.one_apply]

lemma equivalent_symm {I : Type*} [Fintype I] [DecidableEq I]
    {M N : Matrix I I K[X]} (h : Equivalent M N) : Equivalent N M := by
  obtain ⟨U, V, hUV⟩ := h
  refine ⟨U⁻¹, V⁻¹, ?_⟩
  rw [← hUV]
  simp [← Matrix.mul_assoc]

theorem block_smith_any_enumeration :
    Specs.D05.M10.InvariantFactors.CompanionPresentation.block_smith_any_enumeration := by
  intro K _ s n d hd hp hc e
  classical
  obtain ⟨t, e₀, ht, hsize, heq, hcomp, _⟩ := block_smith d hd hp hc
  have hn : n = t+s := by
    have h := Fintype.card_congr (e.trans e₀.symm)
    simpa using h
  subst n
  let p : Equiv.Perm (Fin (t+s)) := e.trans e₀.symm
  have hperm := equivalent_permutation ((companionBlocks d).charmatrix.submatrix e₀ e₀) p
  have hmat : (((companionBlocks d).charmatrix.submatrix e₀ e₀).submatrix p p) =
      (companionBlocks d).charmatrix.submatrix e e := by
    ext i j : 1
    simp [p]
  rw [hmat] at hperm
  have heq' := equivalent_trans (equivalent_symm hperm) heq
  have hchain := chainEntries_chain d t hd hc
  have hcomp' := equivalent_computes hchain heq'
  refine ⟨t, ht, rfl, hcomp', ?_⟩
  intro ops r f hred
  obtain ⟨hr, hf⟩ := computed_entries_unique hchain hcomp' hred
  exact ⟨hr, hf, by rw [hf]; exact nonunit_chain_list d t hd hp⟩

end D05.M10.InvariantFactors.CompanionPresentation
