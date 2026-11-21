import MathGenome.Internal.Specs.D05.M10.InvariantFactors
import MathGenome.Internal.D05.M10.Rational
import MathGenome.Internal.D05.M10.InvariantFactors.CompanionPresentation
import MathGenome.Internal.D05.M08.BlockPolynomials

/-! Uniqueness of rational invariant factors over the original field. -/
noncomputable section
open Polynomial Matrix
open scoped BigOperators
namespace D05.M10.InvariantFactors
open Specs.D05.M10.InvariantFactors
open Specs.D05.M10.InvariantFactors.CompanionPresentation
open D05.M10.Smith D05.M10.InvariantFactorComputation

variable {K : Type*} [Field K] {n : ℕ}

/-- Constant conjugacy is polynomial-matrix equivalence of presentations. -/
lemma charmatrix_equivalent (A B : Matrix (Fin n) (Fin n) K) (h : Similar A B) :
    Equivalent A.charmatrix B.charmatrix := by
  obtain ⟨P, rfl⟩ := h
  let f : Matrix (Fin n) (Fin n) K →* Matrix (Fin n) (Fin n) K[X] :=
    (Polynomial.C : K →+* K[X]).mapMatrix.toMonoidHom
  let Q := Units.map f P
  refine ⟨Q⁻¹, Q, ?_⟩
  have hcomm : A * (P : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * ((P⁻¹).val * A * P.val) := by
    simp [← mul_assoc]
  have hc := Matrix.charmatrix_mul_map_C_of_mul_eq_mul hcomm
  change (↑P⁻¹ : Matrix (Fin n) (Fin n) K).map C * A.charmatrix *
    (P : Matrix (Fin n) (Fin n) K).map C = _
  rw [mul_assoc, hc, ← mul_assoc, ← Matrix.map_mul]
  simp

theorem similarity_minors : Specs.D05.M10.InvariantFactors.similarity_minors := by
  intro K _ n A B h k
  obtain ⟨U, V, hUV⟩ := charmatrix_equivalent A B h
  have he : minorIdeal A.charmatrix k = minorIdeal B.charmatrix k := by
    rw [← hUV]
    exact (MinorIdeals.invertible_invariance K[X] n n k A.charmatrix U V).symm
  exact ⟨he, MinorIdeals.minorGcd_eq_of_ideal_eq k he⟩

lemma matrixFactors_similar (A B : Matrix (Fin n) (Fin n) K) (h : Similar A B) :
    matrixFactors A = matrixFactors B := by
  unfold matrixFactors
  congr 2
  funext i
  rw [(similarity_minors A B h (i.val+1)).2, (similarity_minors A B h i.val).2]

/-- Basis-change matrices are bundled with both inverse identities. -/
def changeUnit {V : Type*} [AddCommGroup V] [Module K V]
    (b c : Module.Basis (Fin n) K V) : (Matrix (Fin n) (Fin n) K)ˣ where
  val := LinearMap.toMatrix c b LinearMap.id
  inv := LinearMap.toMatrix b c LinearMap.id
  val_inv := by rw [← LinearMap.toMatrix_comp b c b]; simp
  inv_val := by rw [← LinearMap.toMatrix_comp c b c]; simp

lemma matrices_similar {V : Type*} [AddCommGroup V] [Module K V]
    (b c : Module.Basis (Fin n) K V) (T : Module.End K V) :
    Similar (LinearMap.toMatrix b b T) (LinearMap.toMatrix c c T) := by
  refine ⟨changeUnit b c, ?_⟩
  change LinearMap.toMatrix b c LinearMap.id * LinearMap.toMatrix b b T *
    LinearMap.toMatrix c b LinearMap.id = _
  rw [← LinearMap.toMatrix_comp b b c, ← LinearMap.toMatrix_comp c b c]
  simp

theorem basis_independence : Specs.D05.M10.InvariantFactors.basis_independence := by
  intro K V _ _ _ _ n b T
  have hn : n = Module.finrank K V := by simpa using (Module.finrank_eq_card_basis b).symm
  subst n
  exact matrixFactors_similar _ _ (matrices_similar b (Module.finBasis K V) T)

/-- Compute a block list from ANY enumeration of its companion basis. -/
lemma matrixFactors_blocks {r : ℕ} (d : Fin r → K[X])
    (hm : ∀ i, (d i).Monic) (hp : ∀ i, 0 < (d i).natDegree)
    (hd : ∀ i j, i ≤ j → d i ∣ d j) (e : Fin n ≃ BlockIndex d) :
    matrixFactors ((companionBlocks d).submatrix e e) = List.ofFn d := by
  classical
  let A := (companionBlocks d).submatrix e e
  have hch : A.charmatrix = (companionBlocks d).charmatrix.submatrix e e := by
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using Matrix.charmatrix_reindex (companionBlocks d) e.symm
  obtain ⟨t, ht, hn, hc, hall⟩ := CompanionPresentation.block_smith_any_enumeration d hm hp hd e
  obtain ⟨_, _, _, ops, f, hred, hcomp, _⟩ := characteristic_smith K n A
  rw [← hch] at hall
  obtain ⟨_, _, hlist⟩ := hall ops n f hred
  unfold matrixFactors
  have hf : (fun i : Fin n => minorGcd A.charmatrix (i.val+1) /
      minorGcd A.charmatrix i.val) = fun i : Fin n => f i.val := by
    funext i
    exact (hcomp.2.2.2 i.val i.isLt).symm
  rw [hf]
  exact hlist

theorem rational_identification : Specs.D05.M10.InvariantFactors.rational_identification := by
  intro K V _ _ _ _ T r d h
  obtain ⟨hm, hp, hd, b, hb⟩ := h
  classical
  let e : Fin (Fintype.card (BlockIndex d)) ≃ BlockIndex d := (Fintype.equivFin _).symm
  have hb' : LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) T =
      (companionBlocks d).submatrix e e := by
    ext i j
    simpa only [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.coe_reindex, Function.comp_apply, Equiv.symm_symm, Matrix.submatrix_apply] using
      congrArg (fun M => M (e i) (e j)) hb
  rw [← basis_independence (b.reindex e.symm) T, hb']
  exact matrixFactors_blocks d hm hp hd e

theorem rational_unique : Specs.D05.M10.InvariantFactors.rational_unique := by
  intro K V _ _ _ _ T r s d e hd he
  exact (rational_identification T d hd).symm.trans (rational_identification T e he)

theorem module_identification : Specs.D05.M10.InvariantFactors.module_identification := by
  intro K V _ _ _ _ T r d hm hp hd he
  obtain ⟨e⟩ := he
  obtain ⟨b, hb, _⟩ := Rational.companion_basis_of_equiv T d hm hp e
  exact rational_identification T d ⟨hm, hp, hd, b, hb⟩

theorem exists_invariant_factors : Specs.D05.M10.InvariantFactors.exists_invariant_factors := by
  intro K V _ _ _ _ T
  obtain ⟨r, d, hm, hp, hd, _, b, hb, _⟩ := Rational.rational_form T
  have h : RationalFactors T d := ⟨hm, hp, hd, b, hb⟩
  exact ⟨r, d, h, rational_identification T d h⟩

theorem charpoly_product : Specs.D05.M10.InvariantFactors.charpoly_product := by
  intro K V _ _ _ _ T r d h
  obtain ⟨hm, hp, _, b, hb⟩ := h
  rw [← LinearMap.charpoly_toMatrix T b, hb]
  change (Matrix.blockDiagonal' _).charpoly = _
  rw [M08.BlockPolynomials.charpoly_blockDiagonal]
  apply Finset.prod_congr rfl
  intro i _
  exact (Companion.matrix_polynomials (d i) (hm i) (hp i)).2

/-- The block construction is an algebra map, including empty blocks. -/
def blockAlgHom {r : ℕ} (d : Fin r → K[X]) :
    (∀ i, Matrix (Fin (d i).natDegree) (Fin (d i).natDegree) K) →ₐ[K]
      Matrix (BlockIndex d) (BlockIndex d) K :=
  { Matrix.blockDiagonal'RingHom (fun i => Fin (d i).natDegree) K with
    commutes' := by
      intro a
      simp only [Pi.algebraMap_def, Matrix.algebraMap_eq_diagonal]
      change Matrix.blockDiagonal' (fun i => Matrix.diagonal (fun _ : Fin (d i).natDegree => a)) = _
      exact Matrix.blockDiagonal'_diagonal _ }

lemma aeval_blocks {r : ℕ} (d : Fin r → K[X]) (p : K[X]) :
    aeval (companionBlocks d) p =
      Matrix.blockDiagonal' (fun i => aeval (Specs.D05.M10.Companion.companionMatrix_value K (d i)) p) := by
  change aeval ((blockAlgHom d) (fun i => Specs.D05.M10.Companion.companionMatrix_value K (d i))) p = _
  rw [Polynomial.aeval_algHom_apply]
  change Matrix.blockDiagonal' (aeval (fun i =>
    Specs.D05.M10.Companion.companionMatrix_value K (d i)) p) = _
  apply congrArg (fun z : (∀ i, Matrix (Fin (d i).natDegree) (Fin (d i).natDegree) K) =>
    Matrix.blockDiagonal' z)
  funext i
  exact Polynomial.aeval_pi_apply₂ _ _ i

lemma blocks_annihilate_iff {r : ℕ} (d : Fin r → K[X])
    (hm : ∀ i, (d i).Monic) (hp : ∀ i, 0 < (d i).natDegree) (p : K[X]) :
    aeval (companionBlocks d) p = 0 ↔ ∀ i, d i ∣ p := by
  rw [aeval_blocks, ← Matrix.blockDiagonal'_zero, Matrix.blockDiagonal'_inj]
  constructor
  · intro h i
    have hi := congrFun h i
    have hdvd := minpoly.dvd_iff.mpr hi
    rwa [(Companion.matrix_polynomials (d i) (hm i) (hp i)).1] at hdvd
  · intro h
    funext i
    apply minpoly.dvd_iff.mp
    rw [(Companion.matrix_polynomials (d i) (hm i) (hp i)).1]
    exact h i

theorem minpoly_largest : Specs.D05.M10.InvariantFactors.minpoly_largest := by
  intro K V _ _ _ _ T r d h
  obtain ⟨hm, hp, hd, b, hb⟩ := h
  rw [← LinearMap.minpoly_toMatrix b T, hb]
  have h₁ : minpoly K (companionBlocks d) ∣ d (Fin.last r) := by
    apply minpoly.dvd_iff.mpr
    exact (blocks_annihilate_iff d hm hp _).mpr (fun i => hd i (Fin.last r) (Fin.le_last i))
  have h₂ : d (Fin.last r) ∣ minpoly K (companionBlocks d) :=
    (blocks_annihilate_iff d hm hp _).mp (minpoly.aeval K (companionBlocks d)) (Fin.last r)
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (by rw [← hb, LinearMap.minpoly_toMatrix]; exact M08.Minpoly.monic T) (hm _) h₁
  exact Polynomial.natDegree_le_of_dvd h₂ (by rw [← hb, LinearMap.minpoly_toMatrix]; exact M08.Minpoly.ne_zero T)

theorem nonempty_factors : Specs.D05.M10.InvariantFactors.nonempty_factors := by
  intro K V _ _ _ _ T r d h
  obtain ⟨_, hp, _, b, _⟩ := h
  have hdim : Module.finrank K V = ∑ i, (d i).natDegree := by
    simpa using Module.finrank_eq_card_basis b
  constructor
  · intro hr
    subst r
    simp [hdim]
  · intro hV
    by_contra hr
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hi : (d ⟨0, hrpos⟩).natDegree ≤ ∑ i, (d i).natDegree :=
      Finset.single_le_sum (f := fun i : Fin r => (d i).natDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨0, hrpos⟩ : Fin r))
    rw [← hdim, hV] at hi
    exact (Nat.not_lt_of_ge hi) (hp _)

theorem zero_case : Specs.D05.M10.InvariantFactors.zero_case := by
  intro K V _ _ _ _ T hV
  obtain ⟨r, d, hd, hf⟩ := exists_invariant_factors T
  have hr := (nonempty_factors T d hd).mpr hV
  subst r
  refine ⟨by simpa using hf, ?_, ?_⟩
  · simpa using charpoly_product T d hd
  · exact M08.Minpoly.zero_dimension T hV

lemma similar_symm (A B : Matrix (Fin n) (Fin n) K) (h : Similar A B) : Similar B A := by
  obtain ⟨P, rfl⟩ := h
  refine ⟨P⁻¹, ?_⟩
  simp [← mul_assoc]

lemma similar_trans (A B C : Matrix (Fin n) (Fin n) K)
    (h : Similar A B) (h' : Similar B C) : Similar A C := by
  obtain ⟨P, rfl⟩ := h
  obtain ⟨Q, rfl⟩ := h'
  refine ⟨P * Q, ?_⟩
  simp [mul_assoc]

theorem similarity_iff : Specs.D05.M10.InvariantFactors.similarity_iff := by
  intro K _ n A B
  classical
  constructor
  · exact matrixFactors_similar A B
  · intro h
    let b₀ := Pi.basisFun K (Fin n)
    let T := Matrix.toLin' A
    let S := Matrix.toLin' B
    have hA : LinearMap.toMatrix b₀ b₀ T = A := by simp [b₀, T]
    have hB : LinearMap.toMatrix b₀ b₀ S = B := by simp [b₀, S]
    obtain ⟨r, d, hd, hf⟩ := exists_invariant_factors T
    obtain ⟨s, e, he, hg⟩ := exists_invariant_factors S
    have hl : List.ofFn d = List.ofFn e := by
      rw [← hf, ← hg, ← basis_independence b₀ T, ← basis_independence b₀ S, hA, hB]
      exact h
    have hrs : r = s := by simpa using congrArg List.length hl
    subst s
    have hde : d = e := List.ofFn_injective hl
    subst e
    obtain ⟨_, _, _, b, hb⟩ := hd
    obtain ⟨_, _, _, c, hc⟩ := he
    have hcard : Fintype.card (Fin n) = Fintype.card (BlockIndex d) := by
      simpa using Module.finrank_eq_card_basis b
    let q : Fin n ≃ BlockIndex d := Fintype.equivOfCardEq hcard
    let b' := b.reindex q.symm
    let c' := c.reindex q.symm
    have hmat : LinearMap.toMatrix b' b' T = LinearMap.toMatrix c' c' S := by
      ext i j
      have heq := congrArg (fun M => M (q i) (q j)) (hb.trans hc.symm)
      simpa only [b', c', LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
        Module.Basis.coe_reindex, Function.comp_apply, Equiv.symm_symm] using heq
    have h₁ := matrices_similar b₀ b' T
    have h₂ := matrices_similar b₀ c' S
    rw [hA, hmat] at h₁
    rw [hB] at h₂
    exact similar_trans _ _ _ h₁ (similar_symm _ _ h₂)

end D05.M10.InvariantFactors
