import MathGenome.Internal.Specs.D05.M13.NormalClassification
import MathGenome.Internal.D05.M13.ComplexSpectral
import MathGenome.Internal.D05.M13.RealNormalBlocks
import MathGenome.Internal.D05.M08.Charpoly
import Mathlib.Data.Multiset.Fintype
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.Polynomial.SpecificDegree
import MathGenome.Internal.D05.Foundations.Factorization

noncomputable section
open scoped BigOperators
namespace D05.M13.NormalClassification
universe u v w

theorem charpoly_of_intertwiner :
    Specs.D05.M13.NormalClassification.charpoly_of_intertwiner.{u, v, w} := by
  intro F _ V W _ _ _ _ _ _ T S U hU
  have hconj : U.toLinearEquiv.conj T = S := by
    ext y
    change U (T (U.symm y)) = S y
    rw [hU, U.apply_symm_apply]
  rw [← hconj, LinearEquiv.charpoly_conj]

theorem dimension_of_charpoly :
    Specs.D05.M13.NormalClassification.dimension_of_charpoly.{u, v, w} := by
  intro F _ V W _ _ _ _ _ _ T S h
  rw [← T.charpoly_natDegree, ← S.charpoly_natDegree, h]

/-- Equality of finite multisets supplies a bijection preserving every label,
even if the label functions are noninjective. -/
theorem matching_labels {ι κ A : Type*} [Fintype ι] [Fintype κ]
    (f : ι → A) (g : κ → A)
    (h : (Finset.univ.val.map f) = (Finset.univ.val.map g)) :
    ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  classical
  have hc (a : A) : Fintype.card {i // f i = a} = Fintype.card {j // g j = a} := by
    have := congrArg (Multiset.count a) h
    simpa [Multiset.count_map, Fintype.card_subtype, ← Finset.filter_val, eq_comm] using this
  let e := Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hc a))
  exact ⟨e, Equiv.ofFiberEquiv_map _⟩

/-- The characteristic polynomial records each entry of any eigenbasis. -/
theorem charpoly_eigenbasis {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype ι]
    (T : V →ₗ[K] V) (b : Module.Basis ι K V) (μ : ι → K)
    (hb : ∀ i, T (b i) = μ i • b i) :
    T.charpoly = ∏ i, (Polynomial.X - Polynomial.C (μ i)) := by
  classical
  rw [← T.charpoly_toMatrix b]
  have hm : LinearMap.toMatrix b b T = Matrix.diagonal μ := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [LinearMap.toMatrix_apply, hb]
    · simp [LinearMap.toMatrix_apply, hb, hij]
  rw [hm, Matrix.charpoly_diagonal]

/-- A common eigenvalue list gives an isometric intertwiner by mapping bases. -/
theorem intertwiner_of_matching_eigenbases
    {F V W ι : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W] [Fintype ι]
    (T : V →ₗ[F] V) (S : W →ₗ[F] W)
    (b : OrthonormalBasis ι F V) (c : OrthonormalBasis ι F W)
    (μ : ι → F) (hb : ∀ i, T (b i) = μ i • b i)
    (hc : ∀ i, S (c i) = μ i • c i) :
    ∃ U : V ≃ₗᵢ[F] W, ∀ x, U (T x) = S (U x) := by
  let U := b.repr.trans c.repr.symm
  have hu (i : ι) : U (b i) = c i := by
    classical
    simp [U]
  refine ⟨U, ?_⟩
  have hh : U.toLinearEquiv.toLinearMap.comp T = S.comp U.toLinearEquiv.toLinearMap := by
    apply b.toBasis.ext
    intro i
    change U (T (b i)) = S (U (b i))
    rw [hb, map_smul, hu, hc]
  exact fun x => DFunLike.congr_fun hh x

/-- Equality of characteristic polynomials matches complete complex spectra
with multiplicity, so no ordering or simple-spectrum premise is needed. -/
theorem complex_classification :
    Specs.D05.M13.NormalClassification.complex_classification.{u, v} := by
  intro V W _ _ _ _ _ _ T S hT hS
  constructor
  · rintro ⟨U, hU⟩
    exact charpoly_of_intertwiner T S U hU
  · intro h
    classical
    obtain ⟨b, μ, hb⟩ := D05.M13.ComplexSpectral.exists_orthonormalBasis T hT
    obtain ⟨c, ν, hc⟩ := D05.M13.ComplexSpectral.exists_orthonormalBasis S hS
    have hrT : T.charpoly.roots = Finset.univ.val.map μ := by
      rw [charpoly_eigenbasis T b.toBasis μ hb, Polynomial.roots_prod _ _ (by
        simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
      simp
    have hrS : S.charpoly.roots = Finset.univ.val.map ν := by
      rw [charpoly_eigenbasis S c.toBasis ν hc, Polynomial.roots_prod _ _ (by
        simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
      simp
    obtain ⟨e, he⟩ := matching_labels μ ν (hrT.symm.trans ((congrArg Polynomial.roots h).trans hrS))
    apply intertwiner_of_matching_eigenbases T S b (c.reindex e.symm) μ hb
    intro i
    simpa only [OrthonormalBasis.reindex_apply, Equiv.symm_symm, he i] using hc (e i)

/-- The invariant of an oriented real normal plane. -/
def planePolynomial (a b : ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C a) ^ 2 + Polynomial.C (b ^ 2)

@[simp] theorem planePolynomial_natDegree (a b : ℝ) :
    (planePolynomial a b).natDegree = 2 := by
  simp only [planePolynomial, Polynomial.natDegree_add_C,
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

theorem planePolynomial_monic (a b : ℝ) : (planePolynomial a b).Monic := by
  apply ((Polynomial.monic_X_sub_C a).pow 2).add_of_left
  apply Polynomial.degree_lt_degree
  simp [Polynomial.natDegree_pow]

/-- This is the charpoly of [a,-b;b,a], with no sign or positivity premise. -/
theorem plane_charpoly (a b : ℝ) :
    (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℝ).charpoly = planePolynomial a b := by
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace, Matrix.diag, Matrix.det_fin_two, Fin.sum_univ_two, planePolynomial]
  ring

/-- Its evaluation is strictly positive on the real axis when b>0. -/
theorem planePolynomial_eval_pos (a b : ℝ) (hb : 0 < b) (x : ℝ) :
    0 < (planePolynomial a b).eval x := by
  simp only [planePolynomial, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  positivity

/-- A positive-imaginary-part plane contributes an irreducible real quadratic. -/
theorem planePolynomial_irreducible (a b : ℝ) (hb : 0 < b) :
    Irreducible (planePolynomial a b) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · intro x hx
    exact (planePolynomial_eval_pos a b hb x).ne' hx

/-- Strictly positive b removes the sign ambiguity of the plane representative. -/
theorem planePolynomial_parameters {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : planePolynomial a b = planePolynomial c d) : a = c ∧ b = d := by
  have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) h
  have h0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) h
  norm_num [planePolynomial, pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_succ] at h1 h0
  have hac : a = c := by linarith
  subst c
  exact ⟨rfl, by nlinarith⟩

/-- Unique factorization matches arbitrary finite irreducible block lists.
This helper does not assume distinct factors: all repetitions are retained. -/
theorem matching_irreducible_factors {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → Polynomial ℝ) (q : κ → Polynomial ℝ)
    (hp : ∀ i, (p i).Monic ∧ Irreducible (p i))
    (hq : ∀ j, (q j).Monic ∧ Irreducible (q j))
    (h : ∏ i, p i = ∏ j, q j) :
    ∃ e : ι ≃ κ, ∀ i, q (e i) = p i := by
  classical
  apply matching_labels p q
  have hpm : ∀ r ∈ Finset.univ.val.map p, r.Monic ∧ Irreducible r := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
    exact hp i
  have hqm : ∀ r ∈ Finset.univ.val.map q, r.Monic ∧ Irreducible r := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hr
    exact hq j
  exact (D05.Foundations.Factorization.factorizationUnique ℝ 1 1 _ _ hpm hqm
    (by simpa using h)).2


/-- Coordinates grouped into eigenlines and positively oriented planes. -/
structure RealBlockBasis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V →ₗ[ℝ] V) where
  L : Type
  P : Type
  [lineFinite : Fintype L]
  [planeFinite : Fintype P]
  basis : OrthonormalBasis (L ⊕ (Fin 2 × P)) ℝ V
  line : L → ℝ
  realPart : P → ℝ
  imagPart : P → ℝ
  positive : ∀ j, 0 < imagPart j
  line_action : ∀ i, T (basis (.inl i)) = line i • basis (.inl i)
  plane_action : ∀ j, Specs.D05.M13.RealNormalBlocks.PlaneAction T
    (basis (.inr (0, j))) (basis (.inr (1, j))) (realPart j) (imagPart j)

attribute [instance] RealBlockBasis.lineFinite RealBlockBasis.planeFinite

/-- Splitting the orbits of a finite involution into fixed points and pairs. -/
def involutionCoordinates {n : ℕ} (p : Fin n → Fin n) (hp : Function.Involutive p) :
    {i // p i = i} ⊕ (Fin 2 × {i // i < p i}) ≃ Fin n := by
  classical
  let f : {i // p i = i} ⊕ (Fin 2 × {i // i < p i}) → Fin n :=
    Sum.elim Subtype.val (fun x => if x.1 = 0 then x.2.val else p x.2.val)
  apply Equiv.ofBijective f
  constructor
  · rintro (i | ⟨k, i⟩) (j | ⟨l, j⟩) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have hi := i.property
      have hj := j.property
      fin_cases l <;> simp [f] at h
      · have : p j.val = j.val := h ▸ hi
        exact False.elim ((ne_of_lt hj) this.symm)
      · have : p (p j.val) = p j.val := h ▸ hi
        rw [hp] at this
        exact False.elim ((ne_of_lt hj) this)
    · have hi := i.property
      have hj := j.property
      fin_cases k <;> simp [f] at h
      · have : p i.val = i.val := h.symm ▸ hj
        exact False.elim ((ne_of_lt hi) this.symm)
      · have : p (p i.val) = p i.val := h.symm ▸ hj
        rw [hp] at this
        exact False.elim ((ne_of_lt hi) this)
    · have hi := i.property
      have hj := j.property
      fin_cases k <;> fin_cases l <;> simp [f] at h ⊢
      · exact Subtype.ext h
      · have h' := congrArg p h
        rw [hp] at h'
        have hh : p j.val < j.val := lt_of_lt_of_eq (h ▸ hi) (hp _)
        exact False.elim (lt_asymm hj hh)
      · have h' := congrArg p h
        rw [hp] at h'
        have hh : p i.val < i.val := lt_of_lt_of_eq (h.symm ▸ hj) (hp _)
        exact False.elim (lt_asymm hi hh)
      · exact Subtype.ext (hp.injective h)
  · intro i
    by_cases hi : p i = i
    · exact ⟨.inl ⟨i, hi⟩, rfl⟩
    · rcases lt_or_gt_of_ne (Ne.symm hi) with h | h
      · exact ⟨.inr (0, ⟨i, h⟩), by simp [f]⟩
      · exact ⟨.inr (1, ⟨p i, by simpa [hp i] using h⟩), by simp [f, hp i]⟩

/-- The real block theorem, with one index for each entire oriented plane. -/
theorem exists_realBlockBasis {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V) (hT : D05.normalOperator T) : Nonempty (RealBlockBasis T) := by
  classical
  obtain ⟨n, B, p, hp, hB⟩ := D05.M13.RealNormalBlocks.normal_blocks_partitioned T hT
  let L := {i // p i = i}
  let P := {i // i < p i}
  have hl (i : L) : ∃ a : ℝ, T (B i.val) = a • B i.val := by
    rcases hB i.val with h | h
    · exact h.2
    · exact False.elim (h.1 i.property)
  have hplane (j : P) : ∃ a b : ℝ, ∃ e : Equiv.Perm (Fin 2), 0 < b ∧
      Specs.D05.M13.RealNormalBlocks.PlaneAction T
        (B (involutionCoordinates p hp (.inr (e 0, j))))
        (B (involutionCoordinates p hp (.inr (e 1, j)))) a b := by
    rcases hB j.val with h | ⟨_, a, b, hb, h | h⟩
    · exact False.elim ((ne_of_lt j.property) h.1.symm)
    · exact ⟨a, b, Equiv.refl _, hb, h⟩
    · exact ⟨a, b, Equiv.swap 0 1, hb, by
      change Specs.D05.M13.RealNormalBlocks.PlaneAction T (B (p j.val)) (B j.val) a b
      exact h⟩
  choose a ha using hl
  choose c d e hd he using hplane
  let E := (Equiv.sumCongr (Equiv.refl L) (Equiv.prodCongrLeft e)).trans
    (involutionCoordinates p hp)
  let C := B.reindex E.symm
  refine ⟨{
    L := L
    P := P
    basis := C
    line := a
    realPart := c
    imagPart := d
    positive := hd
    line_action := ?_
    plane_action := ?_ }⟩
  · intro i
    simp only [C, OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    change T (B i.val) = a i • B i.val
    exact ha i
  · intro j
    simpa [C, E, OrthonormalBasis.reindex_apply] using he j


/-- Characteristic polynomials multiply across a finite diagonal block family. -/
theorem charpoly_blockDiagonal {K ι κ : Type*} [CommRing K] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : κ → Matrix ι ι K) :
    (Matrix.blockDiagonal M).charpoly = ∏ j, (M j).charpoly := by
  have hm : (Matrix.blockDiagonal M).charmatrix =
      Matrix.blockDiagonal (fun j => (M j).charmatrix) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hk : k = l
    · subst l
      by_cases hi : i = j <;>
        simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, Matrix.blockDiagonal, hi]
    · have hij : (i, k) ≠ (j, l) := fun h => hk (congrArg Prod.snd h)
      simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, Matrix.blockDiagonal, hk, hij]
  simp only [Matrix.charpoly, hm, Matrix.det_blockDiagonal]

namespace RealBlockBasis
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (T : V →ₗ[ℝ] V) (B : RealBlockBasis T)
local instance : DecidableEq B.L := Classical.decEq _
local instance : DecidableEq B.P := Classical.decEq _

/-- The actual basis matrix, with plane entries in column convention. -/
theorem toMatrix : LinearMap.toMatrix B.basis.toBasis B.basis.toBasis T =
    Matrix.fromBlocks (Matrix.diagonal B.line) 0 0
      (Matrix.blockDiagonal (fun j => !![B.realPart j, -B.imagPart j;
        B.imagPart j, B.realPart j])) := by
  classical
  ext (i | ⟨k, i⟩) (j | ⟨l, j⟩)
  · by_cases hij : i = j <;>
      simp [LinearMap.toMatrix_apply, B.line_action, hij]
  · fin_cases l
    · simp [LinearMap.toMatrix_apply, (B.plane_action j).1]
    · simp [LinearMap.toMatrix_apply, (B.plane_action j).2]
  · simp [LinearMap.toMatrix_apply, B.line_action]
  · by_cases hij : i = j <;> fin_cases k <;> fin_cases l <;>
      simp [LinearMap.toMatrix_apply, (B.plane_action j).1, (B.plane_action j).2,
        Matrix.blockDiagonal_apply, eq_comm, hij]

/-- Each real plane occurs once in the polynomial product. -/
theorem charpoly [FiniteDimensional ℝ V] : T.charpoly =
    (∏ i, (Polynomial.X - Polynomial.C (B.line i))) *
      ∏ j, planePolynomial (B.realPart j) (B.imagPart j) := by
  classical
  rw [← T.charpoly_toMatrix B.basis.toBasis, B.toMatrix T,
    Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_diagonal, charpoly_blockDiagonal]
  congr 1
  exact Finset.prod_congr rfl fun j _ => plane_charpoly _ _

end RealBlockBasis


namespace RealBlockBasis
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {T : V →ₗ[ℝ] V} {S : W →ₗ[ℝ] W}

/-- The irreducible label belongs to a whole block, rather than a column. -/
def factor (B : RealBlockBasis T) : B.L ⊕ B.P → Polynomial ℝ :=
  Sum.elim (fun i => Polynomial.X - Polynomial.C (B.line i))
    (fun j => planePolynomial (B.realPart j) (B.imagPart j))

theorem factor_properties (B : RealBlockBasis T) (i : B.L ⊕ B.P) :
    (B.factor i).Monic ∧ Irreducible (B.factor i) := by
  cases i with
  | inl i => exact ⟨Polynomial.monic_X_sub_C _, Polynomial.irreducible_X_sub_C _⟩
  | inr j => exact ⟨planePolynomial_monic _ _, planePolynomial_irreducible _ _ (B.positive j)⟩

/-- Unique factorization matches lines to lines and oriented planes to planes. -/
theorem matching_blocks [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (B : RealBlockBasis T) (C : RealBlockBasis S) (h : T.charpoly = S.charpoly) :
    ∃ l : B.L ≃ C.L, ∃ p : B.P ≃ C.P,
      (∀ i, C.line (l i) = B.line i) ∧
      (∀ j, C.realPart (p j) = B.realPart j ∧ C.imagPart (p j) = B.imagPart j) := by
  classical
  have hf : ∏ i, B.factor i = ∏ j, C.factor j := by
    simpa only [Fintype.prod_sum_type, factor, Sum.elim_inl, Sum.elim_inr] using
      (B.charpoly T).symm.trans (h.trans (C.charpoly S))
  obtain ⟨e, he⟩ := matching_irreducible_factors B.factor C.factor
    B.factor_properties C.factor_properties hf
  have hside (x : B.L ⊕ B.P) : x.isLeft ↔ (e x).isLeft := by
    have hd := congrArg Polynomial.natDegree (he x)
    cases x with
    | inl i => cases hx : e (.inl i) <;> simp [hx, factor] at hd ⊢
    | inr j => cases hx : e (.inr j) <;> simp [hx, factor] at hd ⊢
  have hside' (x : B.L ⊕ B.P) : x.isRight ↔ (e x).isRight := by
    simpa only [← Sum.not_isLeft] using not_congr (hside x)
  let l : B.L ≃ C.L := Equiv.sumIsLeft.symm.trans
    ((e.subtypeEquiv hside).trans Equiv.sumIsLeft)
  let p : B.P ≃ C.P := Equiv.sumIsRight.symm.trans
    ((e.subtypeEquiv hside').trans Equiv.sumIsRight)
  have hl (i : B.L) : e (.inl i) = .inl (l i) := (Sum.inl_getLeft _ _).symm
  have hp (j : B.P) : e (.inr j) = .inr (p j) := (Sum.inr_getRight _ _).symm
  refine ⟨l, p, ?_, ?_⟩
  · intro i
    have hh := he (.inl i)
    rw [hl] at hh
    simpa only [factor, Sum.elim_inl, sub_right_inj, Polynomial.C_inj] using hh
  · intro j
    have hh := he (.inr j)
    rw [hp] at hh
    exact planePolynomial_parameters (C.positive (p j)) (B.positive j) hh

/-- Send every line and each ordered pair to its matched orthonormal block. -/
theorem intertwiner_of_matching (B : RealBlockBasis T) (C : RealBlockBasis S)
    (l : B.L ≃ C.L) (p : B.P ≃ C.P)
    (hl : ∀ i, C.line (l i) = B.line i)
    (hp : ∀ j, C.realPart (p j) = B.realPart j ∧ C.imagPart (p j) = B.imagPart j) :
    ∃ U : V ≃ₗᵢ[ℝ] W, ∀ x, U (T x) = S (U x) := by
  classical
  let e := Equiv.sumCongr l (Equiv.prodCongr (Equiv.refl (Fin 2)) p)
  let D := C.basis.reindex e.symm
  let U := B.basis.repr.trans D.repr.symm
  have hu (i) : U (B.basis i) = C.basis (e i) := by simp [U, D]
  refine ⟨U, ?_⟩
  have hh : U.toLinearEquiv.toLinearMap.comp T = S.comp U.toLinearEquiv.toLinearMap := by
    apply B.basis.toBasis.ext
    rintro (i | ⟨k, j⟩)
    · change U (T (B.basis (.inl i))) = S (U (B.basis (.inl i)))
      rw [B.line_action, map_smul, hu]
      simp only [e, Equiv.sumCongr_apply, Sum.map_inl, C.line_action, hl]
    · fin_cases k
      · change U (T (B.basis (.inr (0, j)))) = S (U (B.basis (.inr (0, j))))
        rw [(B.plane_action j).1, map_add, map_smul, map_smul, hu, hu]
        simp only [e, Equiv.sumCongr_apply, Sum.map_inr, Equiv.prodCongr_apply,
          Prod.map_apply, Equiv.refl_apply, (C.plane_action (p j)).1, (hp j).1, (hp j).2]
      · change U (T (B.basis (.inr (1, j)))) = S (U (B.basis (.inr (1, j))))
        rw [(B.plane_action j).2, map_add, map_smul, map_smul, hu, hu]
        simp only [e, Equiv.sumCongr_apply, Sum.map_inr, Equiv.prodCongr_apply,
          Prod.map_apply, Equiv.refl_apply, (C.plane_action (p j)).2, (hp j).1, (hp j).2]
  exact fun x => DFunLike.congr_fun hh x
end RealBlockBasis

/-- Real normal operators are orthogonally equivalent exactly when their
characteristic polynomials agree, with all multiplicities and zero spaces. -/
theorem real_classification :
    Specs.D05.M13.NormalClassification.real_classification.{u, v} := by
  intro V W _ _ _ _ _ _ T S hT hS
  constructor
  · rintro ⟨U, hU⟩
    exact charpoly_of_intertwiner T S U hU
  · intro h
    obtain ⟨B⟩ := exists_realBlockBasis T hT
    obtain ⟨C⟩ := exists_realBlockBasis S hS
    obtain ⟨l, p, hl, hp⟩ := B.matching_blocks C h
    exact B.intertwiner_of_matching C l p hl hp

end D05.M13.NormalClassification
