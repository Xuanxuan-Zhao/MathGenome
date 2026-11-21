import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

open Matrix LieAlgebra Module
open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
open Specs.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry

namespace LieAlgebrasAndRepresentations.OrthogonalCompactGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

section SkewMatrices

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

private theorem skew_entry (X : Orthogonal.so ι K) (i j : ι) :
    X.val j i = -X.val i j :=
  congrArg (fun A : Matrix ι ι K => A i j) ((Orthogonal.mem_so _ _ _).mp X.property)

private def elementarySkew (i j : ι) : Orthogonal.so ι K :=
  ⟨Matrix.single i j 1 - Matrix.single j i 1, by
    rw [Orthogonal.mem_so, Matrix.transpose_sub, Matrix.transpose_single,
      Matrix.transpose_single, neg_sub]⟩

theorem commuting_with_skew_is_scalar (hcard : 2 < Fintype.card ι) (B : Matrix ι ι K)
    (hcomm : ∀ X : Orthogonal.so ι K, Commute B X.val) : ∃ c : K, B = c • 1 := by
  have hOff (i j : ι) (hij : i ≠ j) : B i j = 0 := by
    obtain ⟨k, hki, hkj⟩ : ∃ k : ι, k ≠ i ∧ k ≠ j := by
      by_contra! h
      have hs : (Finset.univ : Finset ι) ⊆ {i, j} := by
        intro a _
        by_cases ha : a = i
        · simp [ha]
        · simp [h a ha]
      have hh := Finset.card_le_card hs
      simp [hij] at hh
      omega
    have h := congrArg (fun C : Matrix ι ι K => C i k) (hcomm (elementarySkew j k)).eq
    change (B * (Matrix.single j k (1 : K) - Matrix.single k j (1 : K))) i k =
      ((Matrix.single j k (1 : K) - Matrix.single k j (1 : K)) * B) i k at h
    simpa [mul_sub, sub_mul, hkj, hki.symm, hij] using h
  have hDiag (i j : ι) : B i i = B j j := by
    by_cases hij : i = j
    · simp [hij]
    · have h := congrArg (fun C : Matrix ι ι K => C i j) (hcomm (elementarySkew i j)).eq
      change (B * (Matrix.single i j (1 : K) - Matrix.single j i (1 : K))) i j =
        ((Matrix.single i j (1 : K) - Matrix.single j i (1 : K)) * B) i j at h
      simpa [mul_sub, sub_mul, hij, Ne.symm hij] using h
  obtain ⟨i, _, _, _⟩ := Fintype.two_lt_card_iff.mp hcard
  refine ⟨B i i, ?_⟩
  ext a b
  by_cases h : a = b
  · subst b
    simpa using hDiag a i
  · simp [hOff a b h, Matrix.one_apply_ne h]

variable [CharZero K]

private theorem skew_diagonal (X : Orthogonal.so ι K) (i : ι) : X.val i i = 0 := by
  have h : (2 : K) * X.val i i = 0 := by rw [two_mul, ← neg_eq_iff_add_eq_zero]; exact (skew_entry X i i).symm
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

private theorem skew_center_eq_bot (hcard : 2 < Fintype.card ι) :
    LieAlgebra.center K (Orthogonal.so ι K) = ⊥ := by
  rw [eq_bot_iff]
  intro X hX
  have hcomm (Y : Orthogonal.so ι K) : Commute X.val Y.val := by
    have h := ((LieModule.mem_maxTrivSubmodule K _ _ X).mp hX) Y
    exact (sub_eq_zero.mp (congrArg Subtype.val h)).symm
  obtain ⟨c, hc⟩ := commuting_with_skew_is_scalar hcard X.val hcomm
  apply (LieSubmodule.mem_bot X).mpr
  apply Subtype.ext
  rw [hc]
  obtain ⟨i, _, _, _⟩ := Fintype.two_lt_card_iff.mp hcard
  have hz := skew_diagonal X i
  rw [hc] at hz
  simp at hz
  simp [hz]

variable [LinearOrder ι]

private abbrev Upper (ι : Type*) [LT ι] := {p : ι × ι // p.1 < p.2}

private def skewFromUpper (f : Upper ι → K) : Orthogonal.so ι K :=
  ⟨Matrix.of (fun i j => if h : i < j then f ⟨(i, j), h⟩
              else if h : j < i then -f ⟨(j, i), h⟩ else 0), by
    rw [Orthogonal.mem_so]
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp
    · simp [h, h.not_gt]⟩

private def skewCoordinates : Orthogonal.so ι K ≃ₗ[K] (Upper ι → K) where
  toFun X p := X.val p.val.1 p.val.2
  invFun := skewFromUpper
  left_inv X := Subtype.ext <| Matrix.ext fun i j => by
    change (skewFromUpper fun p => X.val p.val.1 p.val.2).val i j = _
    rcases lt_trichotomy i j with h | rfl | h
    · simp [skewFromUpper, h]
    · simpa [skewFromUpper] using (skew_diagonal X i).symm
    · simp [skewFromUpper, h, h.not_gt, skew_entry X i j]
  right_inv f := funext fun p => by simp [skewFromUpper, p.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def skewBasis : Basis (Upper ι) K (Orthogonal.so ι K) :=
  Basis.ofEquivFun skewCoordinates

private theorem skewBasis_apply (p : Upper ι) :
    (skewBasis (K := K) p) = elementarySkew p.val.1 p.val.2 := by
  apply (skewCoordinates (K := K)).injective
  rw [skewBasis, Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  funext q
  change Pi.single (M := fun _ => K) p 1 q =
    (Matrix.single p.val.1 p.val.2 (1 : K) - Matrix.single p.val.2 p.val.1 (1 : K))
      q.val.1 q.val.2
  have hrev : ¬(p.val.2 = q.val.1 ∧ p.val.1 = q.val.2) := by
    rintro ⟨h₁, h₂⟩
    exact p.property.not_gt (by simpa [← h₁, ← h₂] using q.property)
  by_cases hpq : p = q
  · subst q
    simp [Matrix.single, hrev]
  · have h : ¬(p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) :=
      fun he => hpq (Subtype.ext (Prod.ext he.1 he.2))
    simp [Pi.single_eq_of_ne (Ne.symm hpq), Matrix.single, h, hrev]

end SkewMatrices

theorem orthogonal_dimensions : orthogonal_dimensions_type := by
  intro K _ _ m
  have hd : Module.finrank K (Orthogonal.so (Fin m) K) = m * (m - 1) / 2 := by
    rw [Module.finrank_eq_card_basis (skewBasis (ι := Fin m) (K := K)),
      Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right]
  refine ⟨hd, ?_⟩
  by_cases hm : m = 2
  · subst m
    have hdim : Module.finrank K (Orthogonal.so (Fin 2) K) = 1 := hd
    obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp hdim
    have hab : IsLieAbelian (Orthogonal.so (Fin 2) K) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hv x
      obtain ⟨b, rfl⟩ := hv y
      simp [smul_lie, lie_smul]⟩
    rw [ite_eq_left rfl, (LieAlgebra.isLieAbelian_iff_center_eq_top _ _).mp hab]
    change Module.finrank K (⊤ : Submodule K (Orthogonal.so (Fin 2) K)) = 1
    rwa [finrank_top]
  · rw [ite_eq_right hm]
    by_cases h : 2 < m
    · rw [skew_center_eq_bot (by simpa using h)]
      change Module.finrank K (⊥ : Submodule K (Orthogonal.so (Fin m) K)) = 0
      exact finrank_bot K _
    · have hsmall : m = 0 ∨ m = 1 := by omega
      have hz : Module.finrank K (Orthogonal.so (Fin m) K) = 0 := by
        rcases hsmall with rfl | rfl <;> exact hd
      apply Nat.eq_zero_of_le_zero
      exact hz ▸ (LieAlgebra.center K (Orthogonal.so (Fin m) K)).toSubmodule.finrank_le

private def productCenterEquiv (K A B : Type*) [Field K] [LieRing A] [LieRing B]
    [LieAlgebra K A] [LieAlgebra K B] :
    LieAlgebra.center K (A × B) ≃ₗ[K] (LieAlgebra.center K A × LieAlgebra.center K B) := by
  let P := (LieAlgebra.center K A).toSubmodule
  let Q := (LieAlgebra.center K B).toSubmodule
  have h : (LieAlgebra.center K (A × B)).toSubmodule = P.prod Q := by
    ext z
    change z ∈ LieAlgebra.center K (A × B) ↔
      z.1 ∈ LieAlgebra.center K A ∧ z.2 ∈ LieAlgebra.center K B
    simp only [LieModule.mem_maxTrivSubmodule]
    constructor
    · intro hz
      exact ⟨fun x => congrArg Prod.fst (hz (x, 0)), fun y => congrArg Prod.snd (hz (0, y))⟩
    · intro hz x
      exact Prod.ext (hz.1 x.1) (hz.2 x.2)
  exact (LinearEquiv.ofEq _ _ h).trans (Submodule.prodEquiv P Q)

theorem signed_dimensions : signed_dimensions_type := by
  intro p q
  obtain ⟨hp, hzp⟩ := orthogonal_dimensions ℂ p
  obtain ⟨hq, hzq⟩ := orthogonal_dimensions ℂ q
  constructor
  · rw [Module.finrank_prod, hp, hq]
  · rw [(productCenterEquiv ℂ _ _).finrank_eq, Module.finrank_prod, hzp, hzq]

theorem general_linear_dimensions : general_linear_dimensions_type := by
  intro K _ n
  constructor
  · simp [Module.finrank_matrix, pow_two]
  · intro hn
    let i : Fin n := ⟨0, hn⟩
    let e : K ≃ₗ[K] LieAlgebra.center K (Matrix (Fin n) (Fin n) K) :=
      { toFun := fun c => ⟨Matrix.scalar (Fin n) c, (LieModule.mem_maxTrivSubmodule K _ _ _).mpr fun M =>
          sub_eq_zero.mpr (Matrix.scalar_commute c (Commute.all c) M).symm.eq⟩
        invFun := fun M => M.val i i
        left_inv := fun c => by simp
        right_inv := fun M => by
          apply Subtype.ext
          have hM : M.val ∈ Set.range (Matrix.scalar (Fin n) : K → Matrix (Fin n) (Fin n) K) := by
            apply Matrix.mem_range_scalar_iff_commute_single'.mpr
            intro j k
            exact sub_eq_zero.mp ((LieModule.mem_maxTrivSubmodule K _ _ M.val).mp M.property _)
          obtain ⟨c, hc⟩ := hM
          change Matrix.scalar (Fin n) (M.val i i) = M.val
          rw [← hc]
          simp
        map_add' := fun a b => Subtype.ext (map_add (Matrix.scalar (Fin n)) a b)
        map_smul' := fun a b => Subtype.ext <| Matrix.ext fun j k => by
          by_cases h : j = k
          · subst k; simp
          · simp [Matrix.scalar_apply, h] }
    simpa using e.finrank_eq.symm

section Compactness

private def realMatrixHom (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ →+* Matrix ι ι ℂ :=
  Complex.ofRealHom.mapMatrix

private theorem realEntry_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : (coefficientConjugation ι).fixed) (i j : ι) :
    ((X.val.val i j).re : ℂ) = X.val.val i j := by
  apply Complex.conj_eq_iff_re.mp
  exact congrArg (fun Y : Orthogonal.so ι ℂ => Y.val i j) X.property

private def coefficientFixedEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Orthogonal.so ι ℝ ≃ₗ⁅ℝ⁆ (coefficientConjugation ι).fixed := by
  let f : Orthogonal.so ι ℝ →ₗ⁅ℝ⁆ (coefficientConjugation ι).fixed :=
    { toFun := fun X => ⟨⟨realMatrixHom ι X.val, (Orthogonal.mem_so _ _ _).mpr <| by
          change realMatrixHom ι X.valᵀ = -(realMatrixHom ι X.val)
          rw [(Orthogonal.mem_so _ _ _).mp X.property, map_neg]⟩,
        Subtype.ext <| Matrix.ext fun i j => Complex.conj_ofReal (X.val i j)⟩
      map_add' := fun X Y => Subtype.ext <| Subtype.ext (map_add (realMatrixHom ι) X.val Y.val)
      map_smul' := fun a X => Subtype.ext <| Subtype.ext <| Matrix.ext fun i j => by
        change ((a * X.val i j : ℝ) : ℂ) = a • (X.val i j : ℂ)
        rw [Complex.ofReal_mul, Complex.real_smul]
      map_lie' := fun {X Y} => Subtype.ext <| Subtype.ext <| by
        change realMatrixHom ι (X.val * Y.val - Y.val * X.val) =
          realMatrixHom ι X.val * realMatrixHom ι Y.val - realMatrixHom ι Y.val * realMatrixHom ι X.val
        rw [map_sub, map_mul, map_mul] }
  refine LieEquiv.ofBijective f ⟨?_, ?_⟩
  · intro X Y h
    apply Subtype.ext
    ext i j
    exact Complex.ofReal_injective (congrArg (fun Z : (coefficientConjugation ι).fixed =>
      Z.val.val i j) h)
  · intro Y
    let X : Orthogonal.so ι ℝ := ⟨Y.val.val.map Complex.re, (Orthogonal.mem_so _ _ _).mpr <| by
      ext i j
      change (Y.val.val j i).re = -(Y.val.val i j).re
      rw [skew_entry Y.val, Complex.neg_re]⟩
    refine ⟨X, Subtype.ext <| Subtype.ext <| Matrix.ext fun i j => ?_⟩
    exact realEntry_fixed Y i j

theorem coefficient_fixed : coefficient_fixed_type := by
  intro N
  exact ⟨coefficientFixedEquiv (Fin N), fun _ _ _ => rfl⟩

private theorem trace_skew_basis {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (X : Orthogonal.so ι ℝ) (p : Upper ι) :
    Matrix.trace (X.val * (skewBasis (K := ℝ) p).val) =
      -(2 : ℝ) * ((skewBasis (ι := ι) (K := ℝ)).repr X p) := by
  rw [skewBasis_apply]
  change Matrix.trace (X.val * (Matrix.single p.val.1 p.val.2 (1 : ℝ) -
    Matrix.single p.val.2 p.val.1 1)) = _
  rw [mul_sub, Matrix.trace_sub, Matrix.trace_mul_comm X.val (Matrix.single p.val.1 p.val.2 1),
    Matrix.trace_mul_comm X.val (Matrix.single p.val.2 p.val.1 1),
    Matrix.trace_single_mul, Matrix.trace_single_mul, one_smul, one_smul, skew_entry X p.val.1 p.val.2]
  rw [skewBasis, Basis.ofEquivFun_repr_apply]
  change -X.val p.val.1 p.val.2 - X.val p.val.1 p.val.2 = -2 * X.val p.val.1 p.val.2
  ring

private theorem trace_commutator_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y Z : Matrix ι ι ℝ) :
    Matrix.trace ((X * Y - Y * X) * Z) = -Matrix.trace ((X * Z - Z * X) * Y) := by
  have h₁ : Matrix.trace ((X * Y) * Z) = Matrix.trace ((Z * X) * Y) := by
    rw [Matrix.trace_mul_comm (X * Y) Z, mul_assoc Z]
  have h₂ : Matrix.trace ((Y * X) * Z) = Matrix.trace ((X * Z) * Y) := by
    rw [mul_assoc Y, Matrix.trace_mul_comm Y]
  simp only [sub_mul, Matrix.trace_sub, h₁, h₂, neg_sub]

private theorem killing_real_skew_neg {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (hcard : 2 < Fintype.card ι) (X : Orthogonal.so ι ℝ) (hX : X ≠ 0) :
    killingForm ℝ (Orthogonal.so ι ℝ) X X < 0 := by
  let b : Basis (Upper ι) ℝ (Orthogonal.so ι ℝ) := skewBasis
  let A := LinearMap.toMatrix b b (LieAlgebra.ad ℝ (Orthogonal.so ι ℝ) X)
  have hA (p q : Upper ι) : A q p = -A p q := by
    have h := trace_commutator_invariant X.val (b p).val (b q).val
    change Matrix.trace ((⁅X, b p⁆ : Orthogonal.so ι ℝ).val * (b q).val) =
      -Matrix.trace ((⁅X, b q⁆ : Orthogonal.so ι ℝ).val * (b p).val) at h
    rw [trace_skew_basis, trace_skew_basis] at h
    simp only [A, LinearMap.toMatrix_apply, LieAlgebra.ad_apply, b]
    linarith
  have hA₀ : A ≠ 0 := by
    intro h
    have ha : LieAlgebra.ad ℝ (Orthogonal.so ι ℝ) X = 0 :=
      (LinearMap.toMatrix b b).injective (by simpa [A] using h)
    have hmem : X ∈ LieAlgebra.center ℝ (Orthogonal.so ι ℝ) := by
      rw [← LieAlgebra.self_module_ker_eq_center, ← LieAlgebra.ad_ker_eq_self_module_ker]
      exact ha
    rw [skew_center_eq_bot hcard] at hmem
    exact hX ((LieSubmodule.mem_bot X).mp hmem)
  obtain ⟨p, q, hpq⟩ : ∃ p q, A p q ≠ 0 := by
    by_contra! h
    exact hA₀ (Matrix.ext h)
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℝ b, ← Module.End.mul_eq_comp,
    LinearMap.toMatrix_mul]
  change Matrix.trace (A * A) < 0
  have ht : Matrix.trace (A * A) = -(∑ i, ∑ j, A i j ^ 2) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ← Finset.sum_neg_distrib]
    congr 1
    ext i
    apply Finset.sum_congr rfl
    intro j _
    rw [hA i j]
    ring
  rw [ht, neg_lt_zero]
  apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  exact ⟨p, Finset.mem_univ _, Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨q, Finset.mem_univ _, sq_pos_of_ne_zero hpq⟩⟩

theorem compact : compact_type := by
  intro N hN X hX
  let e := coefficientFixedEquiv (Fin N)
  have hc : 2 < Fintype.card (Fin N) := by simp; omega
  have hy : e.symm X ≠ 0 := fun h => hX (e.symm.injective (by simpa using h))
  simpa only [← LieAlgebra.killingForm_of_equiv_apply e (e.symm X) (e.symm X),
    LieEquiv.apply_symm_apply] using killing_real_skew_neg hc (e.symm X) hy

open private hermitian_positive from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

theorem semisimple : semisimple_type := by
  intro N hN
  let L := Orthogonal.so (Fin N) ℂ
  let ω := coefficientConjugation (Fin N)
  let : LieAlgebra.IsKilling ℂ L := ⟨by
    rw [eq_bot_iff]
    intro X hX
    apply (LieSubmodule.mem_bot X).mpr
    by_contra hn
    have hz : killingForm ℂ L (ω.map X) X = 0 :=
      (LieIdeal.mem_killingCompl ℂ L ⊤ |>.mp hX) (ω.map X) (LieSubmodule.mem_top _)
    have hp := hermitian_positive ω (compact N hN) hn
    change 0 < (-killingForm ℂ L (ω.map X) X).re at hp
    rw [hz] at hp
    simp at hp⟩
  exact ⟨inferInstanceAs (LieAlgebra.IsSemisimple ℂ L), LieAlgebra.radical_eq_bot (R := ℂ) (L := L)⟩

end Compactness

section Centralizer

variable {n : ℕ}

private def pairedMatrix {R : Type*} [Neg R] (U V : Matrix (Fin n) (Fin n) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  fromBlocks U V (-V) U

private theorem sourceJ_blocks (R : Type*) [CommRing R] :
    sourceJ n R = fromBlocks 0 1 (-1) 0 := by
  simp [sourceJ, Matrix.J, Matrix.fromBlocks_neg]

private theorem paired_multiply {R : Type*} [CommRing R] (U V P Q : Matrix (Fin n) (Fin n) R) :
    pairedMatrix U V * pairedMatrix P Q = pairedMatrix (U * P - V * Q) (U * Q + V * P) := by
  unfold pairedMatrix
  rw [fromBlocks_multiply]
  simp only [mul_neg, neg_mul, sub_eq_add_neg, neg_add, fromBlocks_inj, true_and]
  abel_nf
  simp

private theorem centralizer_blocks {R : Type*} [CommRing R]
    (X : skewCentralizer (sourceJ n R)) :
    X.val.val = pairedMatrix (toBlocks₁₁ X.val.val) (toBlocks₁₂ X.val.val) ∧
      (toBlocks₁₁ X.val.val)ᵀ = -toBlocks₁₁ X.val.val ∧
      (toBlocks₁₂ X.val.val)ᵀ = toBlocks₁₂ X.val.val := by
  let A := toBlocks₁₁ X.val.val
  let B := toBlocks₁₂ X.val.val
  let C := toBlocks₂₁ X.val.val
  let D := toBlocks₂₂ X.val.val
  have hx : fromBlocks A B C D = X.val.val := fromBlocks_toBlocks _
  have hc : Commute X.val.val (sourceJ n R) := X.property
  have h := hc.eq
  rw [← hx, sourceJ_blocks, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [mul_zero, mul_neg, mul_one, zero_mul, one_mul, neg_mul, zero_add, add_zero,
    fromBlocks_inj] at h
  have hs : X.val.valᵀ = -X.val.val := (Orthogonal.mem_so _ _ _).mp X.val.property
  rw [← hx, ← h.2.1, ← h.1] at hs
  simp only [fromBlocks_transpose, fromBlocks_neg, fromBlocks_inj, transpose_neg, neg_neg,
    neg_inj] at hs
  exact ⟨by rw [← hx, ← h.2.1, ← h.1]; rfl, hs.1, hs.2.2.1⟩

private def centralizerOfBlocks {R : Type*} [CommRing R] (U V : Matrix (Fin n) (Fin n) R)
    (hU : Uᵀ = -U) (hV : Vᵀ = V) : skewCentralizer (sourceJ n R) :=
  ⟨⟨pairedMatrix U V, (Orthogonal.mem_so _ _ _).mpr <| by
      simp [pairedMatrix, fromBlocks_transpose, fromBlocks_neg, hU, hV]⟩,
    by
      change pairedMatrix U V * sourceJ n R = sourceJ n R * pairedMatrix U V
      simp [pairedMatrix, sourceJ_blocks, fromBlocks_multiply]⟩

private def blockImage {R : Type*} [CommRing R] (f : R →+* ℂ)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) : Matrix (Fin n) (Fin n) ℂ :=
  X.toBlocks₁₁.map f + Complex.I • X.toBlocks₁₂.map f

private theorem blockImage_paired {R : Type*} [CommRing R] (f : R →+* ℂ)
    (U V : Matrix (Fin n) (Fin n) R) :
    blockImage f (pairedMatrix U V) = f.mapMatrix U + Complex.I • f.mapMatrix V := rfl

private theorem blockImage_add {R : Type*} [CommRing R] (f : R →+* ℂ)
    (X Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) : blockImage f (X + Y) = blockImage f X + blockImage f Y := by
  ext i j
  simp only [blockImage, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, map_add, smul_eq_mul, mul_add]
  abel

private theorem blockImage_sub {R : Type*} [CommRing R] (f : R →+* ℂ)
    (X Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) : blockImage f (X - Y) = blockImage f X - blockImage f Y := by
  ext i j
  simp only [blockImage, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, map_sub, smul_eq_mul, mul_sub]
  abel

private theorem blockImage_mul {R : Type*} [CommRing R] (f : R →+* ℂ)
    (X Y : skewCentralizer (sourceJ n R)) :
    blockImage f (X.val.val * Y.val.val) =
      blockImage f X.val.val * blockImage f Y.val.val := by
  obtain ⟨hx, -, -⟩ := centralizer_blocks X
  obtain ⟨hy, -, -⟩ := centralizer_blocks Y
  rw [hx, hy, paired_multiply, blockImage_paired, blockImage_paired, blockImage_paired]
  simp only [map_sub, map_add, map_mul, mul_add, add_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul, smul_add]
  abel

private theorem blockImage_lie {R : Type*} [CommRing R] (f : R →+* ℂ)
    (X Y : skewCentralizer (sourceJ n R)) :
    blockImage f (⁅X, Y⁆ : skewCentralizer (sourceJ n R)).val.val =
      ⁅blockImage f X.val.val, blockImage f Y.val.val⁆ := by
  change blockImage f (X.val.val * Y.val.val - Y.val.val * X.val.val) = _
  rw [blockImage_sub, blockImage_mul, blockImage_mul]
  rfl

private def complexBlockHom (n : ℕ) : skewCentralizer (sourceJ n ℂ) →ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) ℂ where
  toFun X := blockImage (RingHom.id ℂ) X.val.val
  map_add' X Y := blockImage_add _ X.val.val Y.val.val
  map_smul' a X := by
    ext i j
    change a * X.val.val (.inl i) (.inl j) + Complex.I * (a * X.val.val (.inl i) (.inr j)) =
      a * (X.val.val (.inl i) (.inl j) + Complex.I * X.val.val (.inl i) (.inr j))
    ring
  map_lie' {X Y} := blockImage_lie _ X Y

private theorem complexBlockHom_apply (X : skewCentralizer (sourceJ n ℂ)) :
    complexBlockHom n X = toBlocks₁₁ X.val.val + Complex.I • toBlocks₁₂ X.val.val := rfl

private theorem complexBlockHom_injective (n : ℕ) : Function.Injective (complexBlockHom n) := by
  apply (injective_iff_map_eq_zero (complexBlockHom n)).mpr
  intro X hX
  let U := toBlocks₁₁ X.val.val
  let V := toBlocks₁₂ X.val.val
  obtain ⟨hblock, hU, hV⟩ := centralizer_blocks X
  change Uᵀ = -U at hU
  change Vᵀ = V at hV
  change U + Complex.I • V = 0 at hX
  have ht := congrArg Matrix.transpose hX
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_zero, hU, hV] at ht
  have hu : U = 0 := by
    have h : U + U = 0 := by
      calc
        U + U = (U + Complex.I • V) - (-U + Complex.I • V) := by abel
        _ = 0 := by rw [hX, ht, sub_zero]
    exact (smul_eq_zero.mp (by rwa [two_smul] : (2 : ℂ) • U = 0)).resolve_left two_ne_zero
  have hv : V = 0 := by
    rw [hu, zero_add] at hX
    exact (smul_eq_zero.mp hX).resolve_left Complex.I_ne_zero
  apply Subtype.ext
  apply Subtype.ext
  change X.val.val = 0
  change X.val.val = pairedMatrix U V at hblock
  rw [hblock, hu, hv]
  simp [pairedMatrix]

private theorem complexBlockHom_surjective (n : ℕ) : Function.Surjective (complexBlockHom n) := by
  intro T
  let U : Matrix (Fin n) (Fin n) ℂ := (2 : ℂ)⁻¹ • (T - Tᵀ)
  let V : Matrix (Fin n) (Fin n) ℂ := (-(2 : ℂ)⁻¹ * Complex.I) • (T + Tᵀ)
  have hU : Uᵀ = -U := by simp [U, Matrix.transpose_smul, Matrix.transpose_sub, ← smul_neg, neg_sub]
  have hV : Vᵀ = V := by simp [V, Matrix.transpose_smul, Matrix.transpose_add, add_comm]
  refine ⟨centralizerOfBlocks U V hU hV, ?_⟩
  rw [complexBlockHom_apply]
  change U + Complex.I • V = T
  have hi : Complex.I * (-(2 : ℂ)⁻¹ * Complex.I) = (2 : ℂ)⁻¹ := by
    calc
      _ = -(2 : ℂ)⁻¹ * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  dsimp only [U, V]
  rw [smul_smul, hi, ← smul_add]
  have h : (T - Tᵀ) + (T + Tᵀ) = (2 : ℂ) • T := by rw [two_smul]; abel
  rw [h, inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]

theorem quaternionic_complex : quaternionic_complex_type := by
  intro n
  exact ⟨LieEquiv.ofBijective (complexBlockHom n)
    ⟨complexBlockHom_injective n, complexBlockHom_surjective n⟩, complexBlockHom_apply⟩

private theorem quaternionic_fixed_iff (n : ℕ)
    (a : Orthogonal.so (Fin n ⊕ Fin n) ℂ ≃ₗ⁅ℂ⁆ Orthogonal.so (Fin n ⊕ Fin n) ℂ)
    (ha : ∀ X, (a X).val = sourceJ n ℂ * X.val * (sourceJ n ℂ)ᵀ)
    (X : Orthogonal.so (Fin n ⊕ Fin n) ℂ) :
    a X = X ↔ Commute X.val (sourceJ n ℂ) := by
  have hJ : (sourceJ n ℂ)ᵀ * sourceJ n ℂ = 1 := by
    rw [Matrix.transpose_neg, Matrix.J_transpose, neg_neg, mul_neg, Matrix.J_squared, neg_neg]
  have hJ' : sourceJ n ℂ * (sourceJ n ℂ)ᵀ = 1 := mul_eq_one_comm.mp hJ
  constructor
  · intro hx
    have he := (ha X).symm.trans (congrArg Subtype.val hx)
    exact (by
      simpa only [mul_assoc, hJ, mul_one] using
        (congrArg (fun M => M * sourceJ n ℂ) he).symm : X.val * sourceJ n ℂ = _)
  · intro hx
    apply Subtype.ext
    rw [ha, ← hx.eq, mul_assoc, hJ', mul_one]

theorem quaternionic_automorphism : quaternionic_automorphism_type := by
  intro n a ha
  have hsets : (complexFixed a : Set (Orthogonal.so (Fin n ⊕ Fin n) ℂ)) =
      skewCentralizer (sourceJ n ℂ) := Set.ext (quaternionic_fixed_iff n a ha)
  obtain ⟨e, -⟩ := quaternionic_complex n
  exact ⟨(LieEquiv.ofEq _ _ hsets).trans e⟩

end Centralizer

section RealCentralizer

variable {n : ℕ}

private theorem realBlock_re (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (i j : Fin n) : (blockImage Complex.ofRealHom X i j).re = X.toBlocks₁₁ i j := by
  simp [blockImage, Complex.mul_re, smul_eq_mul]

private theorem realBlock_im (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (i j : Fin n) : (blockImage Complex.ofRealHom X i j).im = X.toBlocks₁₂ i j := by
  simp [blockImage, Complex.mul_im, smul_eq_mul]

private def realBlockHom (n : ℕ) : skewCentralizer (sourceJ n ℝ) →ₗ⁅ℝ⁆ unitaryAlgebra n where
  toFun X := ⟨blockImage Complex.ofRealHom X.val.val, by
    change (blockImage Complex.ofRealHom X.val.val)ᴴ = -(blockImage Complex.ofRealHom X.val.val)
    obtain ⟨-, hU, hV⟩ := centralizer_blocks X
    ext i j
    apply Complex.ext
    · simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re,
        Matrix.neg_apply, Matrix.transpose_apply, Complex.neg_re, realBlock_re] using
        congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hU
    · simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im,
        Matrix.neg_apply, Complex.neg_im, realBlock_im, neg_inj]
      simpa only [Matrix.transpose_apply] using congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hV⟩
  map_add' X Y := Subtype.ext (blockImage_add _ X.val.val Y.val.val)
  map_smul' r X := Subtype.ext <| Matrix.ext fun i j => by
    change ((r * X.val.val (.inl i) (.inl j) : ℝ) : ℂ) +
        Complex.I * ((r * X.val.val (.inl i) (.inr j) : ℝ) : ℂ) =
      r • ((X.val.val (.inl i) (.inl j) : ℂ) + Complex.I * (X.val.val (.inl i) (.inr j) : ℂ))
    rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  map_lie' {X Y} := Subtype.ext (blockImage_lie _ X Y)

private theorem realBlockHom_injective (n : ℕ) : Function.Injective (realBlockHom n) := by
  intro X Y h
  have hr : X.val.val.toBlocks₁₁ = Y.val.val.toBlocks₁₁ := by
    ext i j
    have hentry := congrArg (fun Z : unitaryAlgebra n => (Z.val i j).re) h
    change (blockImage Complex.ofRealHom X.val.val i j).re =
      (blockImage Complex.ofRealHom Y.val.val i j).re at hentry
    simpa only [realBlock_re] using hentry
  have hi : X.val.val.toBlocks₁₂ = Y.val.val.toBlocks₁₂ := by
    ext i j
    have hentry := congrArg (fun Z : unitaryAlgebra n => (Z.val i j).im) h
    change (blockImage Complex.ofRealHom X.val.val i j).im =
      (blockImage Complex.ofRealHom Y.val.val i j).im at hentry
    simpa only [realBlock_im] using hentry
  exact Subtype.ext <| Subtype.ext <| (centralizer_blocks X).1.trans
    (by rw [hr, hi, ← (centralizer_blocks Y).1])

private theorem realBlockHom_surjective (n : ℕ) : Function.Surjective (realBlockHom n) := by
  intro T
  let U := T.val.map Complex.re
  let V := T.val.map Complex.im
  have hT : T.valᴴ = -T.val := T.property
  have hU : Uᵀ = -U := by
    ext i j
    change (T.val j i).re = -(T.val i j).re
    simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re,
      Matrix.neg_apply, Complex.neg_re] using
      congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (A i j).re) hT
  have hV : Vᵀ = V := by
    ext i j
    change (T.val j i).im = (T.val i j).im
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (A i j).im) hT
    simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im,
      Matrix.neg_apply, Complex.neg_im, neg_inj] using h
  refine ⟨centralizerOfBlocks U V hU hV, Subtype.ext <| Matrix.ext fun i j => ?_⟩
  apply Complex.ext
  · exact realBlock_re (pairedMatrix U V) i j
  · exact realBlock_im (pairedMatrix U V) i j

theorem quaternionic_real : quaternionic_real_type := by
  intro n
  exact ⟨LieEquiv.ofBijective (realBlockHom n)
    ⟨realBlockHom_injective n, realBlockHom_surjective n⟩, fun _ => rfl⟩

theorem quaternionic_real_fixed : quaternionic_real_fixed_type := by
  intro n a hcomm ha
  let ι := Fin n ⊕ Fin n
  let ω := coefficientConjugation ι
  let κ := fixedConjugation ω a hcomm
  let e := coefficientFixedEquiv ι
  have hJ : realMatrixHom ι (sourceJ n ℝ) = sourceJ n ℂ := by
    rw [map_neg]
    congr 1
    exact Matrix.map_J (Fin n) Complex.ofRealHom
  have hmem (X : Orthogonal.so ι ℝ) :
      a (e X).val = (e X).val ↔ Commute X.val (sourceJ n ℝ) := by
    rw [quaternionic_fixed_iff n a ha]
    change Commute (realMatrixHom ι X.val) (sourceJ n ℂ) ↔ Commute X.val (sourceJ n ℝ)
    rw [← hJ]
    constructor
    · intro h
      have he := h.eq
      rw [← map_mul, ← map_mul] at he
      exact Matrix.ext fun i j =>
        Complex.ofReal_injective (congrArg (fun M : Matrix ι ι ℂ => M i j) he)
    · intro h
      exact h.map (realMatrixHom ι)
  let f : skewCentralizer (sourceJ n ℝ) →ₗ⁅ℝ⁆ κ.fixed :=
    { toFun := fun X => ⟨⟨(e X.val).val, (hmem X.val).mpr X.property⟩,
          Subtype.ext (e X.val).property⟩
      map_add' X Y := Subtype.ext <| Subtype.ext <| by
        change (e (X.val + Y.val)).val = (e X.val).val + (e Y.val).val
        exact congrArg (fun Z : ω.fixed => Z.val) (map_add e X.val Y.val)
      map_smul' r X := Subtype.ext <| Subtype.ext <| by
        change (e (r • X.val)).val = r • (e X.val).val
        exact congrArg (fun Z : ω.fixed => Z.val) (map_smul e r X.val)
      map_lie' {X Y} := Subtype.ext <| Subtype.ext <| by
        change (e ⁅X.val, Y.val⁆).val = ⁅(e X.val).val, (e Y.val).val⁆
        exact congrArg (fun Z : ω.fixed => Z.val) (e.map_lie X.val Y.val) }
  have hbij : Function.Bijective f := by
    constructor
    · intro X Y h
      exact Subtype.ext <| e.injective <| Subtype.ext <| congrArg (fun Z : κ.fixed => Z.val.val) h
    · intro Y
      let Z : ω.fixed := ⟨Y.val.val, congrArg Subtype.val Y.property⟩
      obtain ⟨X, hX⟩ := e.surjective Z
      have he : (e X).val = Y.val.val :=
        congrArg (fun W : ω.fixed => W.val) (show e X = Z from hX)
      have h : a (e X).val = (e X).val := by
        rw [he]
        exact Y.val.property
      exact ⟨⟨X, (hmem X).mp h⟩, Subtype.ext <| Subtype.ext he⟩
  obtain ⟨u, -⟩ := quaternionic_real n
  exact ⟨(LieEquiv.ofBijective f hbij).symm.trans u⟩

end RealCentralizer

end LieAlgebrasAndRepresentations.OrthogonalCompactGeometry
