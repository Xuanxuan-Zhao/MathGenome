import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SkolemNoether
import Mathlib.Analysis.Complex.Polynomial.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision
import Mathlib.Tactic.NoncommRing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.LinearAlgebra.Matrix.Adjugate
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.SemilinearDescent

namespace LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras

noncomputable section

open LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open MulOpposite

universe u v

theorem archimedean_splitting : ArchimedeanSplitting.{v} := by
  intro A _ _ hA
  let : IsSimpleRing A := hA.1
  let : FiniteDimensional ℂ A := hA.2.2
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ A
  have hd : degree ℂ A = n := by
    rw [degree, e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp [← pow_two]
  rw [hd]
  exact ⟨e⟩

variable {F E A : Type u} [Field F] [Field E] [Algebra F E]
  [Ring A] [Algebra F A] [Algebra E A]

private theorem conjugation_involutive (s : SecondKind F E A) (hA : Nontrivial A) :
    Function.Involutive s.conjugation := by
  let : Nontrivial A := hA
  intro x
  apply (algebraMap E A).injective
  rw [← s.adjoint_centre, ← s.adjoint_centre, s.adjoint_adjoint]

private theorem exists_conjugation_ne (s : SecondKind F E A) :
    ∃ z : E, s.conjugation z ≠ z := by
  by_contra! h
  exact s.conjugation_ne (AlgEquiv.ext h)

private theorem exists_conjugate_eq_mul (s : SecondKind F E A)
    (hσ : Function.Involutive s.conjugation) (c : E) (hc : c * s.conjugation c = 1) :
    ∃ a : E, a ≠ 0 ∧ s.conjugation a = c * a := by
  have h (b : E) : s.conjugation (b + s.conjugation c * s.conjugation b) =
      c * (b + s.conjugation c * s.conjugation b) := by
    rw [map_add, map_mul, hσ c, hσ b, mul_add, ← mul_assoc, hc, one_mul, add_comm]
  by_cases h₁ : 1 + s.conjugation c = 0
  · obtain ⟨z, hz⟩ := exists_conjugation_ne s
    refine ⟨z + s.conjugation c * s.conjugation z, ?_, h z⟩
    have hc' : s.conjugation c = -1 := eq_neg_of_add_eq_zero_right h₁
    rw [hc', neg_one_mul, ← sub_eq_add_neg]
    exact sub_ne_zero.mpr (Ne.symm hz)
  · exact ⟨1 + s.conjugation c, h₁, by simpa using h 1⟩

private abbrev adj (s : SecondKind F E A) (x : A) : A := (s.adjoint x).unop

private theorem adj_mul (s : SecondKind F E A) (x y : A) :
    adj s (x * y) = adj s y * adj s x := by
  simp [adj]

private theorem adj_add (s : SecondKind F E A) (x y : A) :
    adj s (x + y) = adj s x + adj s y := by
  simp [adj]

private theorem adj_one (s : SecondKind F E A) : adj s 1 = 1 := by
  simp [adj]

private theorem adj_zero (s : SecondKind F E A) : adj s 0 = 0 := by
  simp [adj]

private theorem adj_adj (s : SecondKind F E A) (x : A) : adj s (adj s x) = x :=
  s.adjoint_adjoint x

private theorem adj_scalar (s : SecondKind F E A) (c : E) :
    adj s (algebraMap E A c) = algebraMap E A (s.conjugation c) :=
  s.adjoint_centre c

section Matrix

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) E
local notation "†" => conjugateTranspose

private theorem dagger_mul (σ : E ≃ₐ[F] E) (X Y : M) :
    † σ (X * Y) = † σ Y * † σ X := by
  unfold conjugateTranspose
  rw [Matrix.transpose_mul]
  exact Matrix.map_mul (f := σ)

private theorem dagger_add (σ : E ≃ₐ[F] E) (X Y : M) :
    † σ (X + Y) = † σ X + † σ Y := by
  ext i j
  exact map_add σ _ _

private theorem dagger_one (σ : E ≃ₐ[F] E) : † σ (1 : M) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [conjugateTranspose]
  · simp [conjugateTranspose, h]

private theorem dagger_dagger (σ : E ≃ₐ[F] E) (hσ : Function.Involutive σ) (X : M) :
    † σ († σ X) = X := by
  ext i j
  exact hσ _

private theorem dagger_scalar (σ : E ≃ₐ[F] E) (c : E) :
    † σ (algebraMap E M c) = algebraMap E M (σ c) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [conjugateTranspose, Matrix.algebraMap_matrix_apply]
  · simp [conjugateTranspose, Matrix.algebraMap_matrix_apply, h, Ne.symm h]

private theorem dagger_smul (σ : E ≃ₐ[F] E) (c : E) (X : M) :
    † σ (c • X) = σ c • † σ X := by
  ext i j
  exact map_mul σ _ _

private def daggerUnit (σ : E ≃ₐ[F] E) (H : Mˣ) : Mˣ where
  val := † σ (H : M)
  inv := † σ (↑H⁻¹ : M)
  val_inv := by rw [← dagger_mul, H.inv_mul, dagger_one]
  inv_val := by rw [← dagger_mul, H.mul_inv, dagger_one]

private theorem hermitian_matrix [IsScalarTower F E A] (s : SecondKind F E A)
    (e : A ≃ₐ[E] M) :
    HasHermitianMatrix s e := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    let := h
    exact ⟨1, Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | inr h =>
    let := h
    have hA : Nontrivial A := e.toEquiv.nontrivial
    have hσ := conjugation_involutive s hA
    let σ := s.conjugation
    let φ (X : M) := e (adj s (e.symm († σ X)))
    have hφ : Function.Bijective φ :=
      let hs : Function.Involutive (adj s) := adj_adj s
      let hd : Function.Involutive († σ : M → M) := dagger_dagger σ hσ
      e.bijective.comp (hs.bijective.comp (e.symm.bijective.comp hd.bijective))
    let β : M ≃ₐ[E] M := AlgEquiv.ofBijective
      { toFun := φ
        map_zero' := by simp [φ, conjugateTranspose, adj_zero]
        map_one' := by simp [φ, dagger_one, adj_one]
        map_mul' := by intro X Y; simp [φ, dagger_mul, adj_mul]
        map_add' := by intro X Y; simp [φ, dagger_add, adj_add]
        commutes' := by intro c; simp [φ, dagger_scalar, adj_scalar, σ, hσ c] } hφ
    have hM : RM03.CSA.IsCentralSimple E M :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨g, hg⟩ := RM03.CSA.algEquiv_isInner hM β
    let H := g⁻¹
    have hstar (x : A) : e (adj s x) =
        (↑H⁻¹ : M) * † σ (e x) * (H : M) := by
      have h := hg († σ (e x))
      change φ († σ (e x)) = _ at h
      simpa [φ, H, dagger_dagger σ hσ] using h
    let K : Mˣ := H⁻¹ * daggerUnit σ H
    have hK (X : M) : (K : M) * X * (↑K⁻¹ : M) = X := by
      obtain ⟨x, rfl⟩ := e.surjective X
      have h := hstar (adj s x)
      rw [adj_adj, hstar x, dagger_mul, dagger_mul, dagger_dagger σ hσ] at h
      simpa [K, daggerUnit, mul_assoc] using h.symm
    have hcomm (X : M) : X * (K : M) = (K : M) * X := by
      simpa [mul_assoc] using congrArg (fun Y : M => Y * (K : M)) (hK X).symm
    obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff E (D := M)).mp
      (Subalgebra.mem_center_iff.mpr hcomm)
    have hH : † σ (H : M) = c • (H : M) := by
      calc
        † σ (H : M) = (H : M) * (K : M) := by simp [K, daggerUnit, ← mul_assoc]
        _ = c • (H : M) := by rw [hc, ← Algebra.commutes, ← Algebra.smul_def]
    have hnorm : c * σ c = 1 := by
      have he := dagger_dagger σ hσ (H : M)
      rw [hH, dagger_smul, hH, smul_smul, mul_comm (σ c)] at he
      apply (algebraMap E M).injective
      have he' : algebraMap E M (c * σ c) * (H : M) = (H : M) := by
        rw [← Algebra.smul_def, he]
      simpa [mul_assoc] using congrArg (fun X : M => X * (↑H⁻¹ : M)) he'
    obtain ⟨a, ha, hscale⟩ := exists_conjugate_eq_mul s hσ c hnorm
    let d : Eˣ := Units.mk0 a ha
    let J : Mˣ := Units.map (algebraMap E M).toMonoidHom d⁻¹ * H
    have hJ : † σ (J : M) = (J : M) := by
      change † σ (algebraMap E M a⁻¹ * (H : M)) = _
      rw [← Algebra.smul_def, dagger_smul, hH, smul_smul, map_inv₀]
      change ((s.conjugation a)⁻¹ * c) • (H : M) = algebraMap E M a⁻¹ * (H : M)
      rw [← Algebra.smul_def, hscale, mul_inv_rev, mul_assoc,
        inv_mul_cancel₀ (show c ≠ 0 from left_ne_zero_of_mul_eq_one hnorm), mul_one]
    refine ⟨J, hJ, fun x => (hstar x).trans ?_⟩
    change (↑H⁻¹ : M) * † σ (e x) * (H : M) =
      ((↑H⁻¹ : M) * algebraMap E M a) * † σ (e x) *
        (algebraMap E M a⁻¹ * (H : M))
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc (algebraMap E M a), Algebra.commutes a († σ (e x)),
      mul_assoc († σ (e x)), ← mul_assoc (algebraMap E M a),
      ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

end Matrix

open scoped Matrix in
theorem hermitian_adjoint : HermitianAdjoint.{u} := by
  intro F E A _ _ _ _ _ _ _ _ _ s n e
  obtain ⟨H, hH, hAdj⟩ := hermitian_matrix s e
  let σ := s.conjugation
  let conj (x : Fin n → E) : Fin n → E := fun i => σ (x i)
  let h (x y : Fin n → E) := conj x ⬝ᵥ ((↑H : Matrix (Fin n) (Fin n) E) *ᵥ y)
  have hmul (X : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
      conj (X *ᵥ y) = X.map σ *ᵥ conj y := by
    funext i
    exact σ.toRingHom.map_mulVec X y i
  have htranspose (X : Matrix (Fin n) (Fin n) E) :
      X.map σ = (conjugateTranspose σ X).transpose := by rfl
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨fun y z => by simp only [h, Matrix.mulVec_add, dotProduct_add],
      fun c y => by simp only [h, Matrix.mulVec_smul, dotProduct_smul]⟩
  · intro x y
    change σ.toRingHom (conj x ⬝ᵥ ((↑H : Matrix (Fin n) (Fin n) E) *ᵥ y)) = _
    have hxx : conj (conj x) = x := by
      funext i
      let : Nonempty (Fin n) := ⟨i⟩
      exact conjugation_involutive s e.toEquiv.nontrivial (x i)
    rw [σ.toRingHom.map_dotProduct]
    change conj (conj x) ⬝ᵥ conj ((↑H : Matrix (Fin n) (Fin n) E) *ᵥ y) = h y x
    rw [hxx, hmul, htranspose, hH, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
  · intro x hz
    have hcoord : (↑H : Matrix (Fin n) (Fin n) E) *ᵥ x = 0 := by
      funext i
      have hc : conj (Pi.single i 1) = Pi.single i 1 := by
        funext j
        by_cases hj : j = i <;> simp [conj, hj]
      have he := hz (Pi.single i 1)
      simpa [h, hc, single_dotProduct] using he
    calc
      x = (↑H⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ
          ((↑H : Matrix (Fin n) (Fin n) E) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, H.inv_mul, Matrix.one_mulVec]
      _ = 0 := by rw [hcoord, Matrix.mulVec_zero]
  · intro z x y
    have hmat : conjugateTranspose σ (e z) * (↑H : Matrix (Fin n) (Fin n) E) =
        (↑H : Matrix (Fin n) (Fin n) E) * e (adj s z) := by
      change _ = (↑H : Matrix (Fin n) (Fin n) E) * e (s.adjoint z).unop
      rw [hAdj, ← mul_assoc, ← mul_assoc, H.mul_inv, one_mul]
    change conj (e z *ᵥ x) ⬝ᵥ ((↑H : Matrix (Fin n) (Fin n) E) *ᵥ y) =
      conj x ⬝ᵥ ((↑H : Matrix (Fin n) (Fin n) E) *ᵥ (e (adj s z) *ᵥ y))
    rw [hmul, htranspose, dotProduct_comm _ ((↑H : Matrix (Fin n) (Fin n) E) *ᵥ y),
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm _ (conj x),
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]

section DivisionFactor

variable {D : Type u} [DivisionRing D] [Algebra E D] [Algebra F D] [IsScalarTower F E D]

private def transportSecondKind {C : Type u} [Ring C] [Algebra F C] [Algebra E C]
    [IsScalarTower F E C] (s : SecondKind F E A) (e : A ≃ₐ[E] C) : SecondKind F E C :=
  SecondKind.ofRingEquiv s.conjugation s.conjugation_ne
    (e.symm.toRingEquiv.trans (s.adjoint.toRingEquiv.trans e.toRingEquiv.op))
    (by intro x; change e (adj s (e.symm (e (adj s (e.symm x))))) = x
        rw [e.symm_apply_apply, adj_adj, e.apply_symm_apply])
    (by intro c; change e (adj s (e.symm (algebraMap E C c))) = _
        rw [e.symm.commutes, adj_scalar, e.commutes])

private theorem adj_smul (s : SecondKind F E A) (z : E) (x : A) :
    adj s (z • x) = s.conjugation z • adj s x := by
  rw [Algebra.smul_def, adj_mul, adj_scalar, ← Algebra.commutes, ← Algebra.smul_def]

private theorem adj_neg (s : SecondKind F E A) (x : A) : adj s (-x) = -adj s x := by
  simp [adj]

/-- Restrict to the first diagonal corner, using a self-adjoint invertible
element between that corner and its adjoint corner. -/
private theorem divisionFactorInvolution (r : ℕ) (hr : 0 < r)
    (s : SecondKind F E (Matrix (Fin r) (Fin r) D)) :
    Nonempty (SecondKind F E D) := by
  classical
  let i : Fin r := ⟨0, hr⟩
  let S (d : D) := Matrix.single i i d
  let e := S 1
  let e' := adj s e
  have he : e * e = e := by simp [e, S]
  have he' : e' * e' = e' := by
    change adj s e * adj s e = adj s e
    rw [← adj_mul, he]
  have he₀ : e ≠ 0 := by
    intro h
    simpa [e, S] using congrArg (fun M : Matrix (Fin r) (Fin r) D => M i i) h
  have he'₀ : e' ≠ 0 := by
    intro h
    apply he₀
    simpa [e', adj_adj, adj_zero] using congrArg (adj s) h
  have column : ∀ X : Matrix (Fin r) (Fin r) D, X * e = X →
      ∀ k l, l ≠ i → X k l = 0 := by
    intro X h k l hl
    rw [← h, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]
  obtain ⟨k, l, hkl⟩ : ∃ k l, e' k l ≠ 0 := by
    by_contra! H
    exact he'₀ (Matrix.ext H)
  let b₀ := e' * Matrix.single l i (1 : D)
  have hb₀ : b₀ ≠ 0 := by
    intro h
    apply hkl
    simpa [b₀] using congrArg (fun M : Matrix (Fin r) (Fin r) D => M k i) h
  have hleft : e' * b₀ = b₀ := by
    change e' * (e' * _) = e' * _
    rw [← mul_assoc, he']
  have hright : b₀ * e = b₀ := by simp [b₀, e, S, mul_assoc]
  have leftAdj (X : Matrix (Fin r) (Fin r) D) (h : X * e = X) :
      e' * adj s X = adj s X := by
    change adj s e * adj s X = adj s X
    rw [← adj_mul, h]
  have rightAdj (X : Matrix (Fin r) (Fin r) D) (h : e' * X = X) :
      adj s X * e = adj s X := by
    rw [show e = adj s e' from (adj_adj s e).symm, ← adj_mul, h]
  obtain ⟨b, hb, hbAdj, hbe', hbe⟩ :
      ∃ b : Matrix (Fin r) (Fin r) D,
        b ≠ 0 ∧ adj s b = b ∧ e' * b = b ∧ b * e = b := by
    have symmetrize (X : Matrix (Fin r) (Fin r) D) (hL : e' * X = X) (hR : X * e = X)
        (hn : X + adj s X ≠ 0) :
        ∃ b : Matrix (Fin r) (Fin r) D,
          b ≠ 0 ∧ adj s b = b ∧ e' * b = b ∧ b * e = b := by
      exact ⟨X + adj s X, hn, by rw [adj_add, adj_adj, add_comm],
        by rw [mul_add, hL, leftAdj X hR], by rw [add_mul, hR, rightAdj X hL]⟩
    by_cases h : b₀ + adj s b₀ = 0
    · obtain ⟨z, hz⟩ := exists_conjugation_ne s
      apply symmetrize (z • b₀)
      · rw [mul_smul_comm, hleft]
      · rw [smul_mul_assoc, hright]
      · rw [adj_smul, eq_neg_of_add_eq_zero_right h, smul_neg, ← sub_eq_add_neg, ← sub_smul]
        exact smul_ne_zero (sub_ne_zero.mpr (Ne.symm hz)) hb₀
    · exact symmetrize b₀ hleft hright h
  obtain ⟨j, hj⟩ : ∃ j, b j i ≠ 0 := by
    by_contra! H
    apply hb
    ext k l
    by_cases h : l = i
    · simpa [h] using H k
    · exact column b hbe k l h
  let d := Matrix.single i j (b j i)⁻¹
  have hdb : d * b = e := by
    ext k l
    by_cases hk : k = i
    · subst k
      by_cases hl : l = i
      · subst l
        simp [d, e, S, hj]
      · simp [d, e, S, column b hbe j l hl, Ne.symm hl]
    · simp [d, e, S, hk, Ne.symm hk]
  let c := d * e'
  have hcb : c * b = e := by
    change (d * e') * b = e
    rw [mul_assoc, hbe', hdb]
  have hce : e * c = c := by simp [c, d, e, S, ← mul_assoc]
  have hce' : c * e' = c := by
    change (d * e') * e' = d * e'
    rw [mul_assoc, he']
  have hbca : b * adj s c = e' := by
    rw [← hbAdj, ← adj_mul, hcb]
  have hcae : e * adj s c = adj s c := by
    rw [show e = adj s e' from (adj_adj s e).symm, ← adj_mul, hce']
  have hcAdj : adj s c = c := by
    calc
      adj s c = e * adj s c := hcae.symm
      _ = c * e' := by rw [← hcb, mul_assoc, hbca]
      _ = c := hce'
  have hbc : b * c = e' := hcAdj ▸ hbca
  have S_mul (x y : D) : S (x * y) = S x * S y := by simp [S]
  have S_add (x y : D) : S (x + y) = S x + S y := by
    ext k l
    by_cases hk : k = i <;> by_cases hl : l = i <;> simp [S, hk, hl, eq_comm]
  have S_inj : Function.Injective S := by
    intro x y h
    simpa [S] using congrArg (fun M : Matrix (Fin r) (Fin r) D => M i i) h
  have eSe (x : D) : e * S x * e = S x := by simp [e, S]
  let f (x : D) : D := (c * adj s (S x) * b) i i
  have hSf (x : D) : S (f x) = c * adj s (S x) * b := by
    have H (X : Matrix (Fin r) (Fin r) D) : e * X * e = S (X i i) := by simp [e, S]
    rw [← H, ← mul_assoc, ← mul_assoc, hce, mul_assoc _ b e, hbe]
  have hff (x : D) : f (f x) = x := by
    apply S_inj
    rw [hSf, hSf, adj_mul, adj_mul, hbAdj, hcAdj, adj_adj]
    calc
      c * (b * (S x * c)) * b = (c * b) * S x * (c * b) := by noncomm_ring
      _ = S x := by rw [hcb, eSe]
  have hfm (x y : D) : f (x * y) = f y * f x := by
    apply S_inj
    rw [S_mul (f y), hSf, hSf, hSf, S_mul, adj_mul]
    have hSupp : e' * adj s (S x) = adj s (S x) :=
      leftAdj (S x) (by simp [S, e])
    calc
      c * (adj s (S y) * adj s (S x)) * b =
          c * (adj s (S y) * (e' * adj s (S x))) * b := by rw [hSupp]
      _ = (c * adj s (S y) * b) * (c * adj s (S x) * b) := by rw [← hbc]; noncomm_ring
  have hfa (x y : D) : f (x + y) = f x + f y := by
    apply S_inj
    simp only [S_add (f x), hSf, S_add x, adj_add, mul_add, add_mul]
  have hf1 : f 1 = 1 := by
    apply S_inj
    change S (f 1) = e
    rw [hSf, show S 1 = e from rfl, ← show e' = adj s e from rfl, hce', hcb]
  have hf0 : f 0 = 0 := by
    have H := hfa 0 0
    rwa [add_zero, eq_comm, add_eq_left] at H
  let f' : D →+* Dᵐᵒᵖ :=
    { toFun := fun x => op (f x)
      map_zero' := congrArg op hf0
      map_one' := congrArg op hf1
      map_mul' := fun x y => congrArg op (hfm x y)
      map_add' := fun x y => congrArg op (hfa x y) }
  let a := RingEquiv.ofBijective f'
    (opEquiv.bijective.comp (show Function.Involutive f from hff).bijective)
  refine ⟨SecondKind.ofRingEquiv s.conjugation s.conjugation_ne a hff ?_⟩
  intro z
  change f (algebraMap E D z) = algebraMap E D (s.conjugation z)
  apply S_inj
  have hS (t : E) : S (algebraMap E D t) = t • e := by
    change Matrix.single i i (algebraMap E D t) = t • Matrix.single i i (1 : D)
    rw [Matrix.smul_single, Algebra.algebraMap_eq_smul_one]
  rw [hSf, hS, adj_smul, ← show e' = adj s e from rfl, hS,
    mul_smul_comm, smul_mul_assoc, hce', hcb]

end DivisionFactor

section LocalDivision

open scoped WithZero
open ValuativeRel
open LocalDivisionAlgebras

variable {D : Type u} [DivisionRing D] [Algebra E D] [Algebra F D]
  [IsScalarTower F E D]

private def adjointValuation (s : SecondKind F E D) (w : Valuation D ℤᵐ⁰) :
    Valuation D ℤᵐ⁰ where
  toFun x := w (adj s x)
  map_zero' := by rw [adj_zero, map_zero]
  map_one' := by rw [adj_one, map_one]
  map_mul' x y := by rw [adj_mul, map_mul, mul_comm]
  map_add_le_max' x y := by rw [adj_add]; exact w.map_add _ _

open private exists_subfield from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras in
private theorem adjointValuation_equiv
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [rE : ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension F E] [FiniteDimensional F E]
    (s : SecondKind F E D) (hD : isCentralSimple E D)
    (w : Valuation D ℤᵐ⁰) (hw : IsDivisionValuation hD w) :
    w.IsEquiv (adjointValuation s w) := by
  let w' := adjointValuation s w
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  have hv (a b : E) : w (algebraMap E D a) ≤ w (algebraMap E D b) ↔
      @ValuativeRel.vle E _ rE a b := by
    rw [hw.2, hw.2]
    have hpos : degree E D ≠ 0 := (RM03.CSA.degree_pos hD).ne'
    refine (pow_le_pow_iff_left₀ (a := baseValue E a) (b := baseValue E b)
      zero_le zero_le hpos).trans ?_
    exact ((e.toOrderIso.le_iff_le).trans (valuation E).vle_iff_le.symm)
  have hbase (a : F) :
      adj s (algebraMap E D (algebraMap F E a)) = algebraMap E D (algebraMap F E a) := by
    rw [adj_scalar, s.conjugation.commutes]
  have hrel : ValuativeRel.ofValuation (w'.comap (algebraMap E D)) = rE := by
    obtain ⟨r, _, _, _, _, _, huniq⟩ := finiteExtension_localField (K := F) (L := E)
    let r' := ValuativeRel.ofValuation (w'.comap (algebraMap E D))
    have hr' : @ValuativeExtension F E _ _ _ r' _ := by
      constructor
      intro a b
      change w (adj s (algebraMap E D (algebraMap F E a))) ≤
        w (adj s (algebraMap E D (algebraMap F E b))) ↔ a ≤ᵥ b
      rw [hbase, hbase, hv]
      exact @ValuativeExtension.vle_iff_vle F E _ _ _ rE _ (by assumption) a b
    exact (huniq r' hr').trans (huniq rE (by assumption)).symm
  have hE : (valuation E).IsEquiv (w'.comap (algebraMap E D)) := by
    intro a b
    rw [← (valuation E).vle_iff_le]
    change a ≤ᵥ b ↔ @ValuativeRel.vle E _ (ValuativeRel.ofValuation _) a b
    rw [hrel]
  apply Valuation.isEquiv_of_val_le_one
  intro x
  obtain ⟨L, hL, hAlg, _, i, y, rfl⟩ := exists_subfield hD x
  let W := (w'.comap i.toRingHom).map
    ⟨e.symm.toMulEquiv.toMonoidWithZeroHom, e.symm.toOrderIso.monotone⟩
  have hi : (valuation E).IsEquiv (W.comap (algebraMap E L)) := by
    intro a b
    change valuation E a ≤ valuation E b ↔
      e.symm (w' (i (algebraMap E L a))) ≤ e.symm (w' (i (algebraMap E L b)))
    rw [i.commutes, i.commutes]
    exact (hE a b).trans e.symm.toOrderIso.le_iff_le.symm
  have hy := restriction_to_subfields hD w hw i W hi y 1
  change w (i y) ≤ w (i 1) ↔ e.symm (w' (i y)) ≤ e.symm (w' (i 1)) at hy
  have hy' := hy.trans e.symm.toOrderIso.le_iff_le
  simpa only [map_one] using hy'

private theorem adjointValue_uniformizer (s : SecondKind F E D)
    (w : Valuation D ℤᵐ⁰) (h : w.IsEquiv (adjointValuation s w))
    (honto : Function.Surjective w) (π : Dˣ) (hπ : w (π : D) = WithZero.exp (-1)) :
    w (adj s (π : D)) = WithZero.exp (-1) := by
  have hlt (x y : D) : w x < w y ↔ w (adj s x) < w (adj s y) :=
    lt_iff_lt_of_le_iff_le (h y x)
  have hn (x : D) : w (adj s x) ≠ 0 ↔ x ≠ 0 := by
    rw [map_ne_zero]
    simpa only [adj_zero] using
      ((show Function.Involutive (adj s) from adj_adj s).injective.ne_iff (x := x) (y := 0))
  have H (x : D) (hx : w x ≠ 0) (h₁ : WithZero.exp (-1) < w x) (h₂ : w x < 1) : False := by
    have ha := (WithZero.log_lt_iff_lt_exp hx (a := (0 : ℤ))).2 (by simpa using h₂)
    have hb : (-1 : ℤ) < WithZero.log (w x) := by
      exact WithZero.exp_lt_exp.mp (h₁.trans_eq (WithZero.exp_log hx).symm)
    omega
  have ha : w (adj s (π : D)) < 1 := by
    have h₁ : w (π : D) < w 1 := by rw [hπ, map_one]; simp
    simpa [adj_one] using (hlt _ 1).1 h₁
  have hne : w (adj s (π : D)) ≠ 0 := (hn _).2 π.ne_zero
  apply le_antisymm
  · by_contra! hbad
    exact H _ hne hbad ha
  · by_contra! hbad
    obtain ⟨x, hx⟩ := honto (WithZero.exp (-1))
    have hb : w (adj s (adj s x)) = WithZero.exp (-1) := by rw [adj_adj, hx]
    have hb₁ : w (π : D) < w (adj s x) := (hlt _ _).2 (hb ▸ hbad)
    have hb₂ : w (adj s x) < w 1 := (hlt _ 1).2 (by rw [hb, adj_one, map_one]; simp)
    exact H _ (ne_of_gt (by rw [hπ] at hb₁; exact WithZero.exp_pos.trans hb₁))
      (hπ ▸ hb₁) (by simpa using hb₂)

private def adjointUnit (s : SecondKind F E D) (x : Dˣ) : Dˣ where
  val := adj s (x : D)
  inv := adj s (↑x⁻¹ : D)
  val_inv := by rw [← adj_mul, x.inv_mul, adj_one]
  inv_val := by rw [← adj_mul, x.mul_inv, adj_one]

private def adjointInteger (s : SecondKind F E D) (w : Valuation D ℤᵐ⁰)
    (h : w.IsEquiv (adjointValuation s w)) (x : w.integer) : w.integer :=
  ⟨adj s (x : D), by
    change w (adj s (x : D)) ≤ 1
    have hx : w (x : D) ≤ w 1 := by
      rw [map_one]
      exact x.2
    have hx' : w (adj s (x : D)) ≤ w (adj s 1) := (h (x : D) 1).1 hx
    simpa only [adj_one, map_one] using hx' ⟩

variable [ValuativeRel E]

private def residueAdjoint (s : SecondKind F E D) (w : Valuation D ℤᵐ⁰)
    (h : w.IsEquiv (adjointValuation s w)) (r : ResidueData (F := E) w) :
    ResidueRing w →+* ResidueRing w := by
  letI := r.isField.toField
  let f : w.integer →+* ResidueRing w :=
    { toFun x := residue w (adjointInteger s w h x)
      map_one' := by rw [show adjointInteger s w h 1 = 1 by exact Subtype.ext (adj_one s), map_one]
      map_zero' := by rw [show adjointInteger s w h 0 = 0 by exact Subtype.ext (adj_zero s), map_zero]
      map_mul' := fun x y => by
        rw [show adjointInteger s w h (x * y) =
          adjointInteger s w h y * adjointInteger s w h x by exact Subtype.ext (adj_mul s _ _),
          map_mul, mul_comm]
      map_add' := fun x y => by
        rw [show adjointInteger s w h (x + y) =
          adjointInteger s w h x + adjointInteger s w h y by exact Subtype.ext (adj_add s _ _), map_add] }
  refine (maximalIdeal w).ringCon.lift f ?_
  intro x y hxy
  change residue w (adjointInteger s w h x) = residue w (adjointInteger s w h y)
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  have hsub : adj s ((x : D) - (y : D)) = adj s (x : D) - adj s (y : D) := by
    rw [sub_eq_add_neg, adj_add, adj_neg, sub_eq_add_neg]
  change w (adj s (x : D) - adj s (y : D)) < 1
  rw [← hsub]
  have hlt : w ((x : D) - (y : D)) < w 1 := by
    rw [map_one]
    simpa [TwoSidedIdeal.rel_iff, maximalIdeal] using hxy
  have hlt' : w (adj s ((x : D) - (y : D))) < w (adj s 1) :=
    (lt_iff_lt_of_le_iff_le (h 1 ((x : D) - (y : D)))).1 hlt
  simpa only [adj_one, map_one] using hlt'

private theorem residueAdjoint_apply (s : SecondKind F E D) (w : Valuation D ℤᵐ⁰)
    (h : w.IsEquiv (adjointValuation s w)) (r : ResidueData (F := E) w) (x : w.integer) :
    residueAdjoint s w h r (residue w x) = residue w (adjointInteger s w h x) := rfl

private def conjugateInteger (w : Valuation D ℤᵐ⁰) (p : Dˣ) (x : w.integer) :
    w.integer :=
  ⟨(p : D) * (x : D) * (↑p⁻¹ : D), by
    change w ((p : D) * (x : D) * (↑p⁻¹ : D)) ≤ 1
    rw [map_mul, map_mul, mul_right_comm, ← map_mul, p.mul_inv, map_one, one_mul]
    exact x.2⟩

private theorem residue_conjugate_eq (w : Valuation D ℤᵐ⁰) (p q : Dˣ)
    (hpq : w (p : D) = w (q : D)) (x : w.integer) (r : ResidueData (F := E) w) :
    residue w (conjugateInteger w p x) = residue w (conjugateInteger w q x) := by
  let := r.isField.toField
  have hv : w ((p : D) * (↑q⁻¹ : D)) = 1 := by
    rw [map_mul, hpq, ← map_mul, q.mul_inv, map_one]
  let z : w.integer := ⟨(p : D) * (↑q⁻¹ : D), hv.le⟩
  have hz : residue w z ≠ 0 := by
    rw [ne_eq, residue_eq_zero_iff]
    exact hv.not_lt
  have he : conjugateInteger w p x * z = z * conjugateInteger w q x := by
    apply Subtype.ext
    change (↑p * ↑x * ↑p⁻¹ : D) * (↑p * ↑q⁻¹) =
      (↑p * ↑q⁻¹ : D) * (↑q * ↑x * ↑q⁻¹)
    simp [mul_assoc]
  have he' := congrArg (residue w) he
  rw [map_mul, map_mul, mul_comm (residue w z)] at he'
  exact mul_right_cancel₀ hz he'

private theorem degree_dvd_two
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension F E]
    [FiniteDimensional F E] (s : SecondKind F E D) (hD : isCentralSimple E D) :
    degree E D ∣ 2 := by
  obtain ⟨w, hw, _⟩ := valuation_exists hD
  obtain ⟨r⟩ := residue_field hD w hw
  let := r.isField.toField
  let := r.algebra
  obtain ⟨hsurj, _, ⟨c⟩⟩ := cyclic_structure hD w hw r
  let := c.fieldL
  let := c.algebraL
  let := c.galois
  have : FiniteDimensional E c.L := Module.finite_of_finrank_pos
    (c.degree ▸ RM03.CSA.degree_pos hD)
  let θ := c.residueAutEquiv c.τ
  let p := c.uniformizer
  have hconj (x : w.integer) : residue w (conjugateInteger w p x) = θ (residue w x) := by
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective
      (c.residueEquiv.symm (residue w x))
    let y : w.integer := ⟨c.embed (a : c.L), by
      change w (c.embed (a : c.L)) ≤ 1
      rw [c.restrict_val]
      exact pow_le_one₀ zero_le a.2⟩
    have hy : residue w y = residue w x := by
      rw [← c.residue_eq a y rfl, ha, c.residueEquiv.apply_symm_apply]
    let b : c.vL.valuationSubring := ⟨c.τ (a : c.L), by
      change c.vL (c.τ (a : c.L)) ≤ 1
      rw [c.τ_preserves_value]
      exact a.2⟩
    have hby : ((conjugateInteger w p y : w.integer) : D) = c.embed (b : c.L) := by
      change (c.uniformizer : D) * c.embed (a : c.L) * (↑c.uniformizer⁻¹ : D) =
        c.embed (c.τ (a : c.L))
      rw [c.conjugation, mul_assoc, Units.mul_inv, mul_one]
    have hs : residue w (conjugateInteger w p x) = residue w (conjugateInteger w p y) := by
      have he : conjugateInteger w p x - conjugateInteger w p y =
          conjugateInteger w p (x - y) := by
        apply Subtype.ext
        change (p : D) * (x : D) * (↑p⁻¹ : D) - (p : D) * (y : D) * (↑p⁻¹ : D) =
          (p : D) * ((x : D) - (y : D)) * (↑p⁻¹ : D)
        rw [mul_sub, sub_mul]
      apply sub_eq_zero.mp
      rw [← map_sub, he, residue_eq_zero_iff]
      change w ((p : D) * ((x : D) - (y : D)) * (↑p⁻¹ : D)) < 1
      rw [map_mul, map_mul, mul_right_comm, ← map_mul, p.mul_inv, map_one, one_mul]
      apply (residue_eq_zero_iff w (x - y)).1
      rw [map_sub, hy, sub_self]
    rw [hs, ← c.residue_eq b (conjugateInteger w p y) hby, c.residue_aut c.τ a b rfl, hy.symm]
    rw [c.residue_eq a y rfl]
  obtain ⟨m, _, hfrob⟩ := c.frobenius
  have hθ (a : ResidueRing w) : θ a = a ^ (Nat.card (BaseResidue E) ^ m) := by
    obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (c.residueEquiv.symm a)
    let y : c.vL.valuationSubring := ⟨c.τ (x : c.L), by
      change c.vL (c.τ (x : c.L)) ≤ 1
      rw [c.τ_preserves_value]
      exact x.2⟩
    have hx' : c.residueEquiv (IsLocalRing.residue _ x) = a := by rw [hx, c.residueEquiv.apply_symm_apply]
    rw [← hx', ← c.residue_aut c.τ x y rfl]
    exact hfrob x y rfl
  have heq := adjointValuation_equiv s hD w hw
  let q := adjointUnit s p
  have hq : w (q : D) = w (p : D) :=
    (adjointValue_uniformizer s w heq hsurj p c.value_uniformizer).trans c.value_uniformizer.symm
  let ρ := residueAdjoint s w heq r
  have hρ (x : w.integer) : ρ (residue w x) =
      residue w (adjointInteger s w heq x) := residueAdjoint_apply s w heq r x
  have hτρ (a : ResidueRing w) : θ (ρ a) = ρ (θ a) := by rw [hθ, hθ, map_pow]
  have hstar (x : w.integer) :
      conjugateInteger w q (adjointInteger s w heq (conjugateInteger w p x)) =
        adjointInteger s w heq x := by
    apply Subtype.ext
    change adj s (p : D) * adj s ((p : D) * (x : D) * (↑p⁻¹ : D)) *
      adj s (↑p⁻¹ : D) = adj s (x : D)
    rw [adj_mul, adj_mul, ← mul_assoc (adj s (p : D)), ← adj_mul, p.inv_mul, adj_one, one_mul,
      mul_assoc, ← adj_mul, p.inv_mul, adj_one, mul_one]
  have hsquare (a : ResidueRing w) : θ (θ a) = a := by
    obtain ⟨x, hx⟩ := residue_surjective w a
    let y := adjointInteger s w heq x
    have hy : residue w (adjointInteger s w heq y) = a := by
      rw [show adjointInteger s w heq y = x from Subtype.ext (adj_adj s (x : D)), hx]
    have h := congrArg (residue w) (hstar y)
    rw [residue_conjugate_eq w q p hq _ r, hconj, ← hρ, hconj, ← hτρ, hρ, hy] at h
    exact h
  have hpow : c.τ ^ 2 = 1 := by
    apply c.residueAutEquiv.injective
    rw [map_pow, map_one, pow_two]
    exact AlgEquiv.ext hsquare
  have ho := orderOf_dvd_of_pow_eq_one hpow
  rwa [orderOf_eq_card_of_zpowers_eq_top c.gen, IsGalois.card_aut_eq_finrank, c.degree] at ho

end LocalDivision

section QuaternionDescent

open scoped TensorProduct

variable {D : Type u} [DivisionRing D] [Algebra E D] [Algebra F D] [IsScalarTower F E D]

private theorem adjugate_eq_trace_sub {K : Type*} [Field K] {n : ℕ} (hn : n = 2)
    (X : Matrix (Fin n) (Fin n) K) :
    X.adjugate = algebraMap K (Matrix (Fin n) (Fin n) K) X.trace - X := by
  subst n
  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.algebraMap_matrix_apply, add_sub_cancel_left, add_sub_cancel_right]

private theorem adjugate_add_of_size_two {K : Type*} [Field K] {n : ℕ} (hn : n = 2)
    (X Y : Matrix (Fin n) (Fin n) K) :
    (X + Y).adjugate = X.adjugate + Y.adjugate := by
  rw [adjugate_eq_trace_sub hn (X + Y), adjugate_eq_trace_sub hn X, adjugate_eq_trace_sub hn Y,
    Matrix.trace_add, map_add, add_sub_add_comm]

private theorem quaternion_conjugation (s : SecondKind F E D) (hD : isCentralSimple E D)
    (h₂ : degree E D = 2) :
    ∃ j : D ≃ₐ[E] Dᵐᵒᵖ, (∀ x, (j (j x).unop).unop = x) ∧
      (∀ x, adj s (j x).unop = (j (adj s x)).unop) := by
  let K := AlgebraicClosure E
  let M := Matrix (Fin (degree E D)) (Fin (degree E D)) K
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hD
  have hcard : Fintype.card (Fin (degree E D)) = 2 := (Fintype.card_fin _).trans h₂
  let i : D →ₐ[E] M := (e.toAlgHom.restrictScalars E).comp Algebra.TensorProduct.includeRight
  let : Nonempty (Fin (degree E D)) := ⟨⟨0, RM03.CSA.degree_pos hD⟩⟩
  have hi : Function.Injective i := i.toRingHom.injective
  let t := LocalDivisionAlgebras.reducedTrace hD
  let j (x : D) := algebraMap E D (t x) - x
  have ht (x : D) : algebraMap E K (t x) = (i x).trace :=
    LocalDivisionAlgebras.reducedTrace_map hD e x
  have hmap (x : D) : i (j x) = (i x).adjugate := by
    rw [show j x = algebraMap E D (t x) - x from rfl, map_sub, i.commutes,
      IsScalarTower.algebraMap_apply E K M, ht, adjugate_eq_trace_sub h₂]
  have hjTwice : Function.Involutive j := by
    intro x
    apply hi
    rw [hmap, hmap, Matrix.adjugate_adjugate _ (by rw [hcard]; decide), hcard]
    simp
  have hjMul (x y : D) : j (x * y) = j y * j x := by
    apply hi
    rw [hmap, map_mul, map_mul, hmap, hmap, Matrix.adjugate_mul_distrib]
  have hjAdd (x y : D) : j (x + y) = j x + j y := by
    apply hi
    rw [hmap (x + y), map_add i, map_add i, hmap x, hmap y]
    exact adjugate_add_of_size_two h₂ (i x) (i y)
  have hjZero : j 0 = 0 := by
    have H := hjAdd 0 0
    rwa [add_zero, eq_comm, add_eq_left] at H
  have hjOne : j 1 = 1 := by
    apply hi
    rw [hmap, map_one, Matrix.adjugate_one]
  have hjScalar (z : E) : j (algebraMap E D z) = algebraMap E D z := by
    apply hi
    rw [hmap, i.commutes, IsScalarTower.algebraMap_apply E K M,
      Algebra.algebraMap_eq_smul_one, Matrix.adjugate_smul, Matrix.adjugate_one,
      hcard]
    simp
  let n := RM03.CSA.reducedNorm hD
  have hn (x : D) : (i x).det = algebraMap E K (n x) :=
    (RM03.CSA.reducedNorm_map hD x e).symm
  have hjNorm (x : D) : x * j x = algebraMap E D (n x) := by
    apply hi
    rw [map_mul, hmap, Matrix.mul_adjugate, hn, i.commutes,
      IsScalarTower.algebraMap_apply E K M]
    exact (Algebra.algebraMap_eq_smul_one (A := M) _).symm
  have hjComm (x : D) : j x * x = x * j x := by
    change (algebraMap E D (t x) - x) * x = x * (algebraMap E D (t x) - x)
    rw [sub_mul, mul_sub, Algebra.commutes]
  have hjAdj (x : D) : adj s (j x) = algebraMap E D (s.conjugation (t x)) - adj s x := by
    change adj s (algebraMap E D (t x) - x) = _
    simp only [sub_eq_add_neg, adj_add, adj_neg, adj_scalar]
  have hcomm (x : D) : adj s (j x) = j (adj s x) := by
    by_cases hs : ∃ z : E, algebraMap E D z = adj s x
    · obtain ⟨z, hz⟩ := hs
      have hx : x = algebraMap E D (s.conjugation z) := by
        rw [← adj_scalar, hz, adj_adj]
      rw [hx, hjScalar, adj_scalar, hjScalar]
    · let y := adj s x
      let δ := t y - s.conjugation (t x)
      have hδ : algebraMap E D δ * y =
          algebraMap E D (n y - s.conjugation (n x)) := by
        calc
          algebraMap E D δ * y = (j y - adj s (j x)) * y := by
            rw [hjAdj]
            change algebraMap E D (t y - s.conjugation (t x)) * y =
              (algebraMap E D (t y) - y - (algebraMap E D (s.conjugation (t x)) - y)) * y
            rw [map_sub]
            noncomm_ring
          _ = algebraMap E D (n y) - algebraMap E D (s.conjugation (n x)) := by
            rw [sub_mul, hjComm, hjNorm]
            change _ - adj s (j x) * adj s x = _
            rw [← adj_mul, hjNorm, adj_scalar]
          _ = _ := (map_sub _ _ _).symm
      have hδ₀ : δ = 0 := by
        by_contra hne
        apply hs
        refine ⟨δ⁻¹ * (n y - s.conjugation (n x)), ?_⟩
        rw [map_mul, ← hδ, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
      have he := sub_eq_zero.mp hδ₀
      rw [hjAdj, ← he]
  let f : D →+* Dᵐᵒᵖ :=
    { toFun := fun x => op (j x)
      map_zero' := congrArg op hjZero
      map_one' := congrArg op hjOne
      map_mul' := fun x y => congrArg op (hjMul x y)
      map_add' := fun x y => congrArg op (hjAdd x y) }
  let a : D ≃+* Dᵐᵒᵖ := RingEquiv.ofBijective f (opEquiv.bijective.comp hjTwice.bijective)
  refine ⟨AlgEquiv.ofRingEquiv (f := a) (fun z => congrArg op (hjScalar z)),
    hjTwice, hcomm⟩

open RM03.Brauer.SemilinearDescent (AlgebraAction)

private theorem quaternion_descends [Algebra.IsSeparable F E] (hFE : Module.finrank F E = 2)
    (s : SecondKind F E D) (hD : isCentralSimple E D) (hd : degree E D = 2) :
    ∃ C : Subalgebra F D, isCentralSimple F C ∧ degree F C = 2 ∧
      Nonempty (E ⊗[F] C ≃ₐ[E] D) := by
  classical
  let : Algebra.IsQuadraticExtension F E := ⟨hFE⟩
  have hgal : ∀ g : Gal(E/F), g = 1 ∨ g = s.conjugation := by
    obtain ⟨g, _, hg⟩ := (Nat.card_eq_two_iff' (1 : Gal(E/F))).1
      ((IsGalois.card_aut_eq_finrank F E).trans hFE)
    intro a
    by_cases ha : a = 1
    · exact Or.inl ha
    · exact Or.inr ((hg a ha).trans (hg _ s.conjugation_ne).symm)
  have hσ : s.conjugation * s.conjugation = 1 :=
    AlgEquiv.ext (conjugation_involutive s inferInstance)
  obtain ⟨j, hjj, hjs⟩ := quaternion_conjugation s hD hd
  let α (x : D) := (j (adj s x)).unop
  have hα : Function.Involutive α := by
    intro x
    change (j (adj s (j (adj s x)).unop)).unop = x
    rw [hjs, adj_adj, hjj]
  have hαs (a : E) (x : D) : α (a • x) = s.conjugation a • α x := by
    change (j (adj s (a • x))).unop = _
    rw [adj_smul, map_smul, MulOpposite.unop_smul]
  have hαm (x y : D) : α (x * y) = α x * α y := by
    simp [α, adj_mul]
  have hαa (x y : D) : α (x + y) = α x + α y := by
    simp [α, adj_add]
  have hα1 : α 1 = 1 := by simp [α, adj_one]
  let a : D ≃+ D :=
    { toFun := α
      invFun := α
      left_inv := hα
      right_inv := hα
      map_add' := hαa }
  let ρ : AlgebraAction F E D :=
    { act := fun g => if g = 1 then AddEquiv.refl D else a
      one_act := by intro x; simp
      mul_act := by
        intro g h x
        rcases hgal g with rfl | rfl <;> rcases hgal h with rfl | rfl <;>
          simp [hσ, s.conjugation_ne]
        exact (hα x).symm
      map_smul := by
        intro g z x
        rcases hgal g with rfl | rfl
        · simp
        · rw [ite_eq_right s.conjugation_ne]
          exact hαs z x
      map_one := by
        intro g
        rcases hgal g with rfl | rfl
        · simp
        · rw [ite_eq_right s.conjugation_ne]
          exact hα1
      map_mul := by
        intro g x y
        rcases hgal g with rfl | rfl
        · simp
        · rw [ite_eq_right s.conjugation_ne]
          exact hαm x y }
  let C := ρ.fixedSubalgebra
  let e := ρ.descentEquiv
  have hu : ∀ x : C, IsUnit x ∨ x = 0 := by
    intro x
    by_cases hx : x = 0
    · exact Or.inr hx
    · left
      have hx' : (x : D) ≠ 0 := fun h => hx (Subtype.ext h)
      let y : C := ⟨(x : D)⁻¹, by
        intro g
        change ρ.actRingEquiv g (x : D)⁻¹ = (x : D)⁻¹
        rw [map_inv₀, show ρ.actRingEquiv g (x : D) = (x : D) from x.property g]⟩
      exact ⟨⟨x, y, Subtype.ext (mul_inv_cancel₀ hx'), Subtype.ext (inv_mul_cancel₀ hx')⟩, rfl⟩
  let : DivisionRing C := DivisionRing.ofIsUnitOrEqZero hu
  have hcent : Algebra.IsCentral F C := by
    constructor
    intro z hz
    have hcomm : ∀ t : D, t * (z : D) = (z : D) * t := by
      intro t
      obtain ⟨w, rfl⟩ := e.surjective t
      induction w using TensorProduct.inductionOn with
      | tmul v w =>
        change (v • (w : D)) * (z : D) = (z : D) * (v • (w : D))
        have hc := congrArg (fun x : C => (x : D)) (Subalgebra.mem_center_iff.mp hz w)
        rw [smul_mul_assoc, mul_smul_comm]
        exact congrArg (v • ·) hc
      | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
    let : Algebra.IsCentral E D := hD.2.1
    obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff E (D := D)).mp
      (Subalgebra.mem_center_iff.mpr hcomm : (z : D) ∈ Subalgebra.center E D)
    have hfixed (g : Gal(E/F)) : g a = a := by
      apply (algebraMap E D).injective
      have hv := ρ.map_smul g a (1 : D)
      rw [ρ.map_one, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
        ← ha, z.property g] at hv
      exact hv.symm.trans ha
    obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed a).2 hfixed
    apply Algebra.mem_bot.mpr
    refine ⟨b, Subtype.ext ?_⟩
    change algebraMap F D b = (z : D)
    rw [ha, IsScalarTower.algebraMap_apply F E D, hb]
  have hfD : FiniteDimensional E D := hD.2.2
  let : FiniteDimensional F D := FiniteDimensional.trans F E D
  have hfC : FiniteDimensional F C := Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  have hC : isCentralSimple F C := ⟨inferInstance, hcent, hfC⟩
  have hrank : Module.finrank F C = Module.finrank E D :=
    (Module.finrank_baseChange (R := E) (S := F) (M' := C)).symm.trans e.toLinearEquiv.finrank_eq
  have hdeg : degree F C = 2 := by
    change Nat.sqrt (Module.finrank F C) = 2
    rw [hrank]
    exact hd
  exact ⟨C, hC, hdeg, ⟨e⟩⟩

private theorem division_degree_ne_two [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Algebra.IsSeparable F E] (hFE : Module.finrank F E = 2)
    (s : SecondKind F E D) (hD : isCentralSimple E D) :
    degree E D ≠ 2 := by
  intro hd
  obtain ⟨C, hC, hCd, ⟨e⟩⟩ := quaternion_descends hFE s hD hd
  obtain ⟨f⟩ := LocalQuadraticSplitting.quadratic_splitting (E := E) hC hCd hFE
  let m := f.symm.trans e
  let P : Matrix (Fin 2) (Fin 2) E := Matrix.diagonal (Pi.single 0 1)
  have hp : P ≠ 0 := by
    intro h
    simpa [P] using congrArg (fun X : Matrix (Fin 2) (Fin 2) E => X 0 0) h
  have hm : m P ≠ 0 := fun h => hp (m.injective (h.trans (map_zero m).symm))
  have hu : IsUnit (m P) := isUnit_iff_ne_zero.2 hm
  have hunit : IsUnit P := by simpa using hu.map m.symm.toMonoidHom
  have hdet : P.det = 0 := by simp [P, Matrix.det_diagonal, Fin.prod_univ_two]
  exact (hunit.map (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) E →* E)).ne_zero hdet

end QuaternionDescent

theorem local_splitting : LocalSplitting.{u} := by
  intro F E A _ _ _ _ _ _ _ _ _ _ _ hFE hA s
  have hfE : FiniteDimensional F E := Module.finite_of_finrank_pos (hFE ▸ by decide)
  obtain ⟨r, T, hval, hlocal, _, _, _⟩ := finiteExtension_localField (K := F) (L := E)
  let := r
  let := T
  let := hval
  let := hlocal
  obtain ⟨n, D, hDR, hDE, hD, hn, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation E A hA
  let : Algebra F D := Algebra.compHom D (algebraMap F E)
  let : IsScalarTower F E D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let S := transportSecondKind s e
  obtain ⟨sD⟩ := divisionFactorInvolution n hn S
  have hD' : isCentralSimple E D := RM03.CSA.isCentralSimple_of_isCentralDivision E D hD
  have hdiv := degree_dvd_two sD hD'
  have hne := division_degree_ne_two hFE sD hD'
  have hd : degree E D = 1 := ((Nat.dvd_prime Nat.prime_two).1 hdiv).resolve_right hne
  change RM03.CSA.degree E D = 1 at hd
  have hn' : degree E A = n := by
    change RM03.CSA.degree E A = n
    rw [RM03.CSA.degree_matrix_division hA hD hn e, hd, mul_one]
  have hf : Module.finrank E D = 1 := by
    rw [RM03.CSA.finrank_eq_degree_sq hD', hd, one_pow]
  let a : E ≃ₐ[E] D := AlgEquiv.ofBijective (Algebra.ofId E D)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hf)
  rw [hn']
  exact ⟨e.trans (a.symm.mapMatrix (m := Fin n))⟩

end

end LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
