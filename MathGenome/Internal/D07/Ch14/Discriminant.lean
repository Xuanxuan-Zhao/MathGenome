import MathGenome.Internal.Specs.D07.Ch14.Discriminant
import MathGenome.Internal.D07.Ch14.PolynomialRootAction
import MathGenome.Internal.D07.Ch14.AutomorphismBound
import Mathlib.LinearAlgebra.Vandermonde

universe u v

namespace D07.Ch14.Discriminant

open Polynomial Specs.D07.Ch14.Discriminant

/-- Evaluating Vandermonde at the negatives gives the source's order of
subtraction, rather than its global sign variant. -/
theorem differenceProduct_eq_det {L : Type v} [CommRing L] {n : ℕ}
    (a : Fin n → L) :
    differenceProduct a = Matrix.det (Matrix.vandermonde (fun i => -a i)) := by
  simp [differenceProduct, Matrix.det_vandermonde, sub_eq_add_neg, add_comm]

theorem permutation_sign : PermutationSign.{v} := by
  intro L _ n a π
  rw [differenceProduct_eq_det, differenceProduct_eq_det]
  exact Matrix.det_permute π (Matrix.vandermonde (fun i => -a i))

theorem product_nonzero : ProductNonzero.{v} := by
  intro L _ n a ha
  rw [differenceProduct_eq_det, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact ha (neg_injective hij)

/-- Conjugation by the numbering keeps the underlying field action. -/
theorem numberedAction_apply {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] {f : K[X]} {n : ℕ} (b : Fin n ≃ f.rootSet L)
    (σ : L ≃ₐ[K] L) (i : Fin n) :
    (b (numberedAction b σ i)).val = σ (b i).val := by
  change (b (b.symm (Specs.D07.Ch14.PolynomialRootAction.rootPermutationValue K L f σ
    (b i)))).val = _
  rw [b.apply_symm_apply]
  rfl

theorem automorphism_sign : AutomorphismSign.{u, v} := by
  intro K L _ _ _ f n b σ
  have hmap : σ (differenceProduct (fun i => (b i).val)) =
      differenceProduct (fun i => σ (b i).val) := by
    simp [differenceProduct, map_prod, map_sub]
  rw [hmap]
  have heq : (fun i => σ (b i).val) =
      (fun i => (b i).val) ∘ (numberedAction b σ) := by
    funext i
    exact (numberedAction_apply b σ i).symm
  rw [heq]
  exact permutation_sign L n (fun i => (b i).val) (numberedAction b σ)

/-- The full fixed-field theorem in the source's explicit splitting-field
interface. Finite dimension and Galoisness are derived, not assumed. -/
theorem exists_base_of_fixed {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (f : K[X]) (hsep : f.Separable)
    (hsplit : Specs.D07.Ch12.SplittingDefinition.splittingFieldValue K L f)
    (z : L) (hz : ∀ σ : L ≃ₐ[K] L, σ z = z) :
    ∃ c : K, algebraMap K L c = z := by
  let : FiniteDimensional K L :=
    (Ch12.DegreeDefinition.finite_iff_finiteDimensional K L).mp
      (SplittingCriterion.separableSplittingFieldFinite K L f hsep hsplit)
  obtain ⟨_, hnormal, hseparable⟩ :=
    SplittingCriterion.separableSplittingFieldGalois K L f hsep hsplit
  let : IsGalois K L := { to_isSeparable := hseparable, to_normal := hnormal }
  exact (IsGalois.mem_range_algebraMap_iff_fixed z).mpr hz

/-- Squaring the sign action makes D² fixed in every characteristic. -/
theorem square_fixed {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] {f : K[X]} {n : ℕ} (b : Fin n ≃ f.rootSet L)
    (σ : L ≃ₐ[K] L) :
    σ (differenceProduct (fun i => (b i).val) ^ 2) =
      differenceProduct (fun i => (b i).val) ^ 2 := by
  rw [map_pow, automorphism_sign K L f n b σ, mul_pow]
  have hs : (((Equiv.Perm.sign (numberedAction b σ) : ℤ) : L)) ^ 2 = 1 := by
    simp only [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq,
      Units.val_one, Int.cast_one]
  rw [hs, one_mul]

theorem discriminant_in_base : DiscriminantInBase.{u, v} := by
  intro K L _ _ _ f n hsep hsplit _hn b
  have hd : differenceProduct (fun i => (b i).val) ≠ 0 :=
    product_nonzero L n _ (Subtype.val_injective.comp b.injective)
  obtain ⟨Δ, hΔ⟩ := exists_base_of_fixed f hsep hsplit _ (square_fixed b)
  refine ⟨Δ, ?_, hΔ⟩
  intro hz
  have : differenceProduct (fun i => (b i).val) ^ 2 = 0 := by
    rw [← hΔ, hz, map_zero]
  exact (pow_ne_zero 2 hd) this

/-- The square criterion, with the same product and the same actual root
permutations throughout both directions. -/
theorem alternating_iff_square : AlternatingIffSquare.{u, v} := by
  intro K L _ _ _ f n hchar hsep hsplit _hn b Δ hΔ
  let D : L := differenceProduct (fun i => (b i).val)
  have hd : D ≠ 0 :=
    product_nonzero L n _ (Subtype.val_injective.comp b.injective)
  constructor
  · intro hA
    have hfix : ∀ σ : L ≃ₐ[K] L, σ D = D := by
      intro σ
      have hs := Equiv.Perm.mem_alternatingGroup.mp (hA (show
        numberedAction b σ ∈ (numberedAction b).range from ⟨σ, rfl⟩))
      simpa only [D, hs, Units.val_one, Int.cast_one, one_mul] using
        automorphism_sign K L f n b σ
    obtain ⟨c, hc⟩ := exists_base_of_fixed f hsep hsplit D hfix
    apply (isSquare_iff_exists_sq Δ).mpr
    refine ⟨c, (algebraMap K L).injective ?_⟩
    rw [map_pow, hc]
    exact hΔ
  · intro hsq
    obtain ⟨c, hc⟩ := hsq.exists_sq
    have hsqL : D ^ 2 = (algebraMap K L c) ^ 2 := by
      rw [← hΔ, hc, map_pow]
    have hfix : ∀ σ : L ≃ₐ[K] L, σ D = D := by
      rcases eq_or_eq_neg_of_sq_eq_sq D (algebraMap K L c) hsqL with h | h
      · intro σ
        rw [h, σ.commutes]
      · intro σ
        rw [h, map_neg, σ.commutes]
    have htwoL : (2 : L) ≠ 0 := by
      intro hz
      apply hchar
      exact (algebraMap K L).injective (by simpa only [map_ofNat, map_zero] using hz)
    rintro π ⟨σ, rfl⟩
    apply Equiv.Perm.mem_alternatingGroup.mpr
    rcases Int.units_eq_one_or (Equiv.Perm.sign (numberedAction b σ)) with hs | hs
    · exact hs
    · exfalso
      have hneg : D = -D := by
        simpa only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
          neg_one_mul] using (hfix σ).symm.trans (automorphism_sign K L f n b σ)
      have hzero : (2 : L) * D = 0 := by
        simpa only [two_mul] using (eq_neg_iff_add_eq_zero.mp hneg)
      exact (mul_ne_zero htwoL hd) hzero

/-- Multiplication by a nonzero square preserves squareness over a field. -/
theorem isSquare_mul_square_iff {K : Type u} [Field K] (c Δ : K) (hc : c ≠ 0) :
    IsSquare (c ^ 2 * Δ) ↔ IsSquare Δ := by
  constructor
  · intro h
    have hdiv := h.div (IsSquare.sq c)
    simpa only [mul_div_cancel_left₀ Δ (pow_ne_zero 2 hc)] using hdiv
  · exact (IsSquare.sq c).mul

theorem leadingCoefficient_square_test : LeadingCoefficientSquareTest.{u} := by
  intro K _ f Δ hf
  rw [show 2 * (f.natDegree - 1) = (f.natDegree - 1) * 2 from Nat.mul_comm _ _,
    pow_mul]
  exact isSquare_mul_square_iff _ Δ (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hf))

theorem discriminant_criterion : DiscriminantCriterion.{u, v} := by
  intro K L _ _ _ f n hchar hsep hsplit hn b
  obtain ⟨Δ, hne, hΔ⟩ := discriminant_in_base K L f n hsep hsplit hn b
  have hiff := alternating_iff_square K L f n hchar hsep hsplit hn b Δ hΔ
  refine ⟨Δ, hne, hΔ, hiff, ?_⟩
  rw [hiff, ← hn]
  exact (leadingCoefficient_square_test K f Δ hsplit.1).symm

end D07.Ch14.Discriminant
