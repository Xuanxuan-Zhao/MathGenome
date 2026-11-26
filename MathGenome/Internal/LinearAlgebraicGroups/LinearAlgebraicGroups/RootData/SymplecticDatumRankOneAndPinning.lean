import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import Batteries.Tactic.OpenPrivate

open CategoryTheory Matrix
open scoped Finset BigOperators
open scoped Matrix

set_option backward.isDefEq.respectTransparency false

universe u

namespace LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning

open Specs.SymplecticDatumRankOneAndPinning Specs.SymplecticMatrixStructure

noncomputable section

section Matrices

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {R S : Type*} [CommRing R] [CommRing S]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
@[simp] private theorem frameEquiv_left (e : A ↪ B) (i : A) :
    frameEquiv e (Sum.inl i) = e i := rfl

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
@[simp] private theorem frameEquiv_right (e : A ↪ B) (i : ↥((Set.range e)ᶜ : Set B)) :
    frameEquiv e (Sum.inr i) = i.val := rfl

@[simp] private theorem extendMatrix_one (e : A ↪ B) :
    extendMatrix e (1 : Matrix A A R) = 1 := by
  change reindexRingEquiv R (frameEquiv e) (fromBlocks (1 : Matrix A A R) 0 0 1) = 1
  rw [fromBlocks_one, map_one]

private theorem extendMatrix_mul (e : A ↪ B) (M N : Matrix A A R) :
    extendMatrix e (M * N) = extendMatrix e M * extendMatrix e N := by
  change reindexRingEquiv R (frameEquiv e) (fromBlocks (M * N) 0 0 1) =
    reindexRingEquiv R (frameEquiv e) (fromBlocks M 0 0 1) *
      reindexRingEquiv R (frameEquiv e) (fromBlocks N 0 0 1)
  rw [← map_mul, fromBlocks_multiply]
  simp

private theorem extendMatrix_map (f : R →+* S) (e : A ↪ B) (M : Matrix A A R) :
    (extendMatrix e M).map f = extendMatrix e (M.map f) := by
  unfold extendMatrix
  rw [reindex_apply, reindex_apply, ← Matrix.submatrix_map, fromBlocks_map]
  simp [Matrix.map_zero f (map_zero f), Matrix.map_one f (map_zero f) (map_one f)]

@[simp] private theorem extendMatrix_frame (e : A ↪ B) (M : Matrix A A R) (i j : A) :
    extendMatrix e M (e i) (e j) = M i j := by
  have he (x : A) : (frameEquiv e).symm (e x) = Sum.inl x :=
    (Equiv.symm_apply_eq _).mpr (frameEquiv_left e x).symm
  simp [extendMatrix, reindex_apply, he]

/-- Extending an isometry by identity preserves a form for which the chosen
coordinates are orthogonal to the remaining coordinates. -/
private theorem extendMatrix_preserves (e : A ↪ B) (M : Matrix A A R) (J : Matrix B B R)
    (h₁ : ∀ i (z : ↥((Set.range e)ᶜ : Set B)), J (e i) z = 0)
    (h₂ : ∀ i (z : ↥((Set.range e)ᶜ : Set B)), J z (e i) = 0)
    (h : Mᵀ * J.submatrix e e * M = J.submatrix e e) :
    (extendMatrix e M)ᵀ * J * extendMatrix e M = J := by
  let E := Matrix.reindexRingEquiv R (frameEquiv e).symm
  let C : Matrix ↥((Set.range e)ᶜ : Set B) ↥((Set.range e)ᶜ : Set B) R :=
    J.submatrix Subtype.val Subtype.val
  have hJ : E J = fromBlocks (J.submatrix e e) 0 0 C := by
    ext (i | i) (j | j)
    · exact congrArg₂ (fun x y => J x y) (frameEquiv_left e i) (frameEquiv_left e j)
    · simpa [E, reindexRingEquiv, reindex_apply, Matrix.submatrix_apply] using h₁ i j
    · simpa [E, reindexRingEquiv, reindex_apply, Matrix.submatrix_apply] using h₂ j i
    · rfl
  have hM : E (extendMatrix e M) = fromBlocks M 0 0 1 :=
    (Matrix.reindex (frameEquiv e) (frameEquiv e)).symm_apply_apply _
  apply E.injective
  rw [map_mul, map_mul]
  have ht : E (extendMatrix e M)ᵀ = (E (extendMatrix e M))ᵀ := rfl
  rw [ht, hM, hJ, fromBlocks_transpose]
  simp [fromBlocks_multiply, h]

end Matrices

section Symplectic

variable {I : Type u} [Fintype I] [DecidableEq I] {R S : Type u} [CommRing R] [CommRing S]

private theorem partner_partner (p : Indices I) : partner (partner p) = p :=
  Sum.swap_swap p

private theorem pairingSign_partner (p : Indices I) :
    pairingSign R (partner p) = -pairingSign R p := by
  cases p <;> simp [partner, pairingSign]

private theorem pairingSign_sq (p : Indices I) :
    pairingSign R p * pairingSign R p = 1 := by
  cases p <;> simp [pairingSign]

private theorem J_entry (p q : Indices I) :
    Matrix.J I R p q = if partner p = q then pairingSign R p else 0 := by
  rcases p with i | i <;> rcases q with j | j <;>
    simp [Matrix.J, Matrix.one_apply, pairingSign, partner, Matrix.neg_apply]
  split <;> simp_all

private theorem J_mixed {A : Type*} (e : A ↪ Indices I)
    (he : ∀ x, ∃ y, partner (e x) = e y)
    (i : A) (z : ↥((Set.range e)ᶜ : Set (Indices I))) :
    Matrix.J I R (e i) z = 0 := by
  rw [J_entry, if_neg]
  intro hz
  obtain ⟨j, hj⟩ := he i
  exact z.property ⟨j, hj.symm.trans hz⟩

private theorem J_mixed' {A : Type*} (e : A ↪ Indices I)
    (he : ∀ x, ∃ y, partner (e x) = e y)
    (i : A) (z : ↥((Set.range e)ᶜ : Set (Indices I))) :
    Matrix.J I R z (e i) = 0 := by
  have hn := Matrix.J_transpose I R
  have h := congrArg (fun M : Matrix (Indices I) (Indices I) R => M (e i) z) hn
  simpa [Matrix.transpose_apply, Matrix.neg_apply, J_mixed e he i z] using h

private theorem longFrame_closed (p : Indices I) (i : Fin 2) :
    ∃ j, partner (longFrame p i) = longFrame p j := by
  fin_cases i
  · exact ⟨1, rfl⟩
  · exact ⟨0, partner_partner p⟩

private theorem shortFrame_closed (p q : Indices I) (h : coordinate p ≠ coordinate q)
    (i : Fin 2 ⊕ Fin 2) :
    ∃ j, partner (shortFrame p q h i) = shortFrame p q h j := by
  rcases i with i | i <;> fin_cases i
  · exact ⟨.inr 0, rfl⟩
  · exact ⟨.inr 1, rfl⟩
  · exact ⟨.inl 0, partner_partner p⟩
  · exact ⟨.inl 1, partner_partner q⟩

private theorem longFrame_form (p : Indices I) :
    (Matrix.J I R).submatrix (longFrame p) (longFrame p) =
      !![0, pairingSign R p; -pairingSign R p, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> cases p <;>
    simp [Matrix.submatrix_apply, J_entry, longFrame, orderedPair, partner, pairingSign]

private theorem longMatrix_mem (p : Indices I) (g : SL₂ R) :
    longMatrix p g ∈ Matrix.symplecticGroup I R := by
  apply SymplecticGroup.mem_iff'.mpr
  apply extendMatrix_preserves _ _ _ (J_mixed _ (longFrame_closed p))
    (J_mixed' _ (longFrame_closed p))
  rw [longFrame_form]
  have hg := g.property
  change g.val.det = 1 at hg
  rw [Matrix.det_fin_two] at hg
  apply Matrix.ext
  intro i j
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · linear_combination (pairingSign R p) * hg
  · linear_combination -(pairingSign R p) * hg
  · ring

private theorem shortSigns_sq (p q : Indices I) :
    shortSigns R p q * shortSigns R p q = 1 := by
  rw [shortSigns, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [pairingSign_sq]

private theorem shortSigns_transpose (p q : Indices I) :
    (shortSigns R p q)ᵀ = shortSigns R p q := Matrix.diagonal_transpose _

private theorem shortFrame_form (p q : Indices I) (h : coordinate p ≠ coordinate q) :
    (Matrix.J I R).submatrix (shortFrame p q h) (shortFrame p q h) =
      fromBlocks 0 (shortSigns R p q) (-shortSigns R p q) 0 := by
  have hpq : p ≠ q := fun he => h (congrArg coordinate he)
  have heq : coordinate (partner p) = coordinate p := by cases p <;> rfl
  have hpq' : partner p ≠ q := fun he => h (heq.symm.trans (congrArg coordinate he))
  have hqp' : partner q ≠ p := fun he => hpq' (by rw [← he, partner_partner])
  have hp : partner p ≠ p := by cases p <;> simp [partner]
  have hq : partner q ≠ q := by cases q <;> simp [partner]
  have hppqq : partner p ≠ partner q :=
    fun he => hpq (by simpa only [partner_partner] using congrArg partner he)
  have f₀ : shortFrame p q h (.inl 0) = p := rfl
  have f₁ : shortFrame p q h (.inl 1) = q := rfl
  have f₂ : shortFrame p q h (.inr 0) = partner p := rfl
  have f₃ : shortFrame p q h (.inr 1) = partner q := rfl
  apply Matrix.ext
  rintro (i | i) (j | j)
  all_goals
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Matrix.submatrix_apply, f₀, f₁, f₂, f₃, J_entry, partner_partner, hpq, Ne.symm hpq,
      hpq', Ne.symm hpq', hqp', Ne.symm hqp', hp, hq, Ne.symm hp, Ne.symm hq, hppqq, Ne.symm hppqq,
      shortSigns, Matrix.diagonal_apply, Matrix.neg_apply, pairingSign_partner]

private theorem sl_inv_mul (g : SL₂ R) : (g⁻¹).val * g.val = 1 :=
  congrArg Subtype.val (inv_mul_cancel g)

private theorem sl_mul_inv (g : SL₂ R) : g.val * (g⁻¹).val = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

private theorem shortMatrix_mem (p q : Indices I) (h : coordinate p ≠ coordinate q) (g : SL₂ R) :
    shortMatrix p q h g ∈ Matrix.symplecticGroup I R := by
  apply SymplecticGroup.mem_iff'.mpr
  apply extendMatrix_preserves _ _ _ (J_mixed _ (shortFrame_closed p q h))
    (J_mixed' _ (shortFrame_closed p q h))
  rw [shortFrame_form]
  simp only [pairedBlock, fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_mul, Matrix.transpose_transpose, shortSigns_transpose,
    fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hD (N : Matrix (Fin 2) (Fin 2) R) :
      shortSigns R p q * (shortSigns R p q * N) = N := by
    rw [← Matrix.mul_assoc, shortSigns_sq, Matrix.one_mul]
  congr 1
  · simp only [Matrix.mul_assoc, hD]
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, sl_inv_mul, Matrix.transpose_one, Matrix.one_mul]
  · simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hD, sl_inv_mul,
      Matrix.mul_one]

private def longHom (p : Indices I) : SL₂ R →* PointGroup I R where
  toFun g := ⟨longMatrix p g, longMatrix_mem p g⟩
  map_one' := Subtype.ext (extendMatrix_one _)
  map_mul' g h := Subtype.ext (extendMatrix_mul _ g.val h.val)

private def shortHom (p q : Indices I) (h : coordinate p ≠ coordinate q) : SL₂ R →* PointGroup I R where
  toFun g := ⟨shortMatrix p q h g, shortMatrix_mem p q h g⟩
  map_one' := by
    apply Subtype.ext
    change extendMatrix _ (pairedBlock p q (1 : SL₂ R)) = 1
    rw [pairedBlock, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one,
      Matrix.mul_one, shortSigns_sq, fromBlocks_one, extendMatrix_one]
  map_mul' g l := by
    apply Subtype.ext
    change extendMatrix _ (pairedBlock p q (g * l)) =
      extendMatrix _ (pairedBlock p q g) * extendMatrix _ (pairedBlock p q l)
    rw [← extendMatrix_mul]
    unfold pairedBlock
    rw [fromBlocks_multiply, _root_.mul_inv_rev]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc]
    have hD (N : Matrix (Fin 2) (Fin 2) R) :
        shortSigns R p q * (shortSigns R p q * N) = N := by
      rw [← Matrix.mul_assoc, shortSigns_sq, Matrix.one_mul]
    rw [hD]

private theorem map_shortSigns (f : R →+* S) (p q : Indices I) :
    (shortSigns R p q).map f = shortSigns S p q := by
  rw [shortSigns, shortSigns, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · cases p <;> simp [pairingSign]
  · cases q <;> simp [pairingSign]

theorem longMaps : LongMaps.{u} := by
  intro k I _ _ _ p
  refine ⟨{ app := fun R => GrpCat.ofHom (longHom p), naturality := ?_ }, fun _ _ => rfl⟩
  intro R S f
  apply GrpCat.ext
  intro g
  exact Subtype.ext (extendMatrix_map f.hom.toRingHom _ g.val).symm

theorem shortMaps : ShortMaps.{u} := by
  intro k I _ _ _ p q h
  refine ⟨{ app := fun R => GrpCat.ofHom (shortHom p q h), naturality := ?_ }, fun _ _ => rfl⟩
  intro R S f
  apply GrpCat.ext
  intro g
  apply Subtype.ext
  let F := Matrix.SpecialLinearGroup.map (n := Fin 2) f.hom.toRingHom
  change shortMatrix p q h (F g) = (shortMatrix p q h g).map f.hom.toRingHom
  unfold shortMatrix
  rw [extendMatrix_map]
  congr 1
  unfold pairedBlock
  have hi : (F g)⁻¹ = F (g⁻¹) := (map_inv F g).symm
  rw [hi, fromBlocks_map]
  simp only [Matrix.map_zero _ (map_zero _), Matrix.map_mul, map_shortSigns, ← Matrix.transpose_map]
  rfl

theorem representedMaps : RepresentedMaps.{u} := by
  intro k I _ _ _ G c r
  cases r with
  | long p =>
    obtain ⟨F, hF⟩ := longMaps k I p
    refine ⟨F ≫ c.inv, fun R g => ?_⟩
    change (show PointGroup I R from c.hom.app R (c.inv.app R (F.app R g))).val = _
    have hh := congrArg (fun f => f.app R (F.app R g)) c.inv_hom_id
    exact (congrArg (fun z : PointGroup I R => z.val) hh).trans (hF R g)
  | short p q h =>
    obtain ⟨F, hF⟩ := shortMaps k I p q h
    refine ⟨F ≫ c.inv, fun R g => ?_⟩
    change (show PointGroup I R from c.hom.app R (c.inv.app R (F.app R g))).val = _
    have hh := congrArg (fun f => f.app R (F.app R g)) c.inv_hom_id
    exact (congrArg (fun z : PointGroup I R => z.val) hh).trans (hF R g)

private theorem fromBlocks_single_left {A B : Type*} [DecidableEq A] [DecidableEq B]
    (i j : A) (a : R) :
    fromBlocks (Matrix.single i j a) 0 0 (0 : Matrix B B R) =
      Matrix.single (Sum.inl i) (Sum.inl j) a := by
  ext (x | x) (y | y) <;> simp [Matrix.single_apply]

private theorem fromBlocks_single_right {A B : Type*} [DecidableEq A] [DecidableEq B]
    (i j : B) (a : R) :
    fromBlocks (0 : Matrix A A R) 0 0 (Matrix.single i j a) =
      Matrix.single (Sum.inr i) (Sum.inr j) a := by
  ext (x | x) (y | y) <;> simp [Matrix.single_apply]

private theorem reindex_single {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (i j : A) (a : R) :
    Matrix.reindex e e (Matrix.single i j a) = Matrix.single (e i) (e j) a := by
  ext x y
  simp [Matrix.reindex_apply, Matrix.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

private theorem extendMatrix_add_single {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ↪ B) (M : Matrix A A R) (i j : A) (a : R) :
    extendMatrix e (M + Matrix.single i j a) = extendMatrix e M + Matrix.single (e i) (e j) a := by
  change reindexRingEquiv R (frameEquiv e) (fromBlocks (M + Matrix.single i j a) 0 0 1) =
    reindexRingEquiv R (frameEquiv e) (fromBlocks M 0 0 1) + _
  rw [show fromBlocks (M + Matrix.single i j a) 0 0 (1 : Matrix ↥((Set.range e)ᶜ : Set B) _ R) =
      fromBlocks M 0 0 1 + fromBlocks (Matrix.single i j a) 0 0 0 by simp only [fromBlocks_add, add_zero, zero_add]]
  rw [map_add, fromBlocks_single_left]
  congr 1
  change Matrix.reindex (frameEquiv e) (frameEquiv e) (Matrix.single (Sum.inl i) (Sum.inl j) a) = _
  rw [reindex_single, frameEquiv_left, frameEquiv_left]

private theorem extendMatrix_single {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ↪ B) (i j : A) (a : R) :
    extendMatrix e (1 + Matrix.single i j a) = 1 + Matrix.single (e i) (e j) a := by
  rw [extendMatrix_add_single, extendMatrix_one]

private theorem upper_value (a : R) : (upper a).val = 1 + Matrix.single 0 1 a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.single_apply, Matrix.one_apply]

private theorem lower_value (a : R) : (lower a).val = 1 + Matrix.single 1 0 a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.single_apply, Matrix.one_apply]

private theorem upper_inv (a : R) : (upper a)⁻¹ = upper (-a) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  change !![1, -a; -(0 : R), 1] = !![1, -a; 0, 1]
  rw [neg_zero]

private theorem lower_inv (a : R) : (lower a)⁻¹ = lower (-a) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  change !![1, -(0 : R); -a, 1] = !![1, 0; -a, 1]
  rw [neg_zero]

private theorem diagonal_inv (a : Rˣ) : (diagonal a)⁻¹ = diagonal a⁻¹ := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  change !![(↑a⁻¹ : R), -(0 : R); -(0 : R), ↑a] =
    !![↑a⁻¹, 0; 0, (↑(a⁻¹)⁻¹ : R)]
  rw [neg_zero, inv_inv]

private theorem diagonal_value (a : Rˣ) :
    (diagonal a).val = Matrix.diagonal ![(↑a : R), ↑a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Specs.SymplecticDatumRankOneAndPinning.diagonal, Matrix.diagonal_apply]

private theorem shortSigns_single (p q : Indices I) (i j : Fin 2) (a : R) :
    shortSigns R p q * Matrix.single i j a * shortSigns R p q =
      Matrix.single i j (![pairingSign R p, pairingSign R q] i * a *
        ![pairingSign R p, pairingSign R q] j) := by
  ext x y
  simp only [shortSigns, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; rfl
  · simp

private theorem shortSigns_upper_inverse (p q : Indices I) (a : R) :
    shortSigns R p q * ((upper a)⁻¹).valᵀ * shortSigns R p q =
      1 + Matrix.single 1 0 (-(pairingSign R p * pairingSign R q) * a) := by
  rw [upper_inv, upper_value, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, shortSigns_sq, shortSigns_single]
  congr 2
  change pairingSign R q * (-a) * pairingSign R p = _
  ring

private theorem shortSigns_lower_inverse (p q : Indices I) (a : R) :
    shortSigns R p q * ((lower a)⁻¹).valᵀ * shortSigns R p q =
      1 + Matrix.single 0 1 (-(pairingSign R p * pairingSign R q) * a) := by
  rw [lower_inv, lower_value, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, shortSigns_sq, shortSigns_single]
  congr 2
  change pairingSign R p * (-a) * pairingSign R q = _
  ring

private theorem fromBlocks_add_singles (i j x y : Fin 2) (a b : R) :
    fromBlocks (1 + Matrix.single i j a) 0 0 (1 + Matrix.single x y b) =
      1 + Matrix.single (Sum.inl i : Fin 2 ⊕ Fin 2) (Sum.inl j) a +
        Matrix.single (Sum.inr x) (Sum.inr y) b := by
  rw [← fromBlocks_single_left, ← fromBlocks_single_right, ← fromBlocks_one]
  simp only [fromBlocks_add, add_zero, zero_add]

private theorem rootUpper_value (r : RootIndex I) (a : R) :
    r.matrix (upper a) = r.upperMatrix a := by
  cases r with
  | long p =>
    change extendMatrix (longFrame p) (upper a).val = 1 + Matrix.single p (partner p) a
    rw [upper_value, extendMatrix_single]
    rfl
  | short p q h =>
    change extendMatrix (shortFrame p q h) (fromBlocks (upper a).val 0 0
      (shortSigns R p q * ((upper a)⁻¹).valᵀ * shortSigns R p q)) = _
    rw [upper_value, shortSigns_upper_inverse, fromBlocks_add_singles,
      extendMatrix_add_single, extendMatrix_single]
    rfl

private theorem rootLower_value (r : RootIndex I) (a : R) :
    r.matrix (lower a) = r.lowerMatrix a := by
  cases r with
  | long p =>
    change extendMatrix (longFrame p) (lower a).val = 1 + Matrix.single (partner p) p a
    rw [lower_value, extendMatrix_single]
    rfl
  | short p q h =>
    change extendMatrix (shortFrame p q h) (fromBlocks (lower a).val 0 0
      (shortSigns R p q * ((lower a)⁻¹).valᵀ * shortSigns R p q)) = _
    rw [lower_value, shortSigns_lower_inverse, fromBlocks_add_singles,
      extendMatrix_add_single, extendMatrix_single]
    rfl

private theorem extendMatrix_diagonal {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ↪ B) (v : A → R) (w : B → R)
    (hin : ∀ i, w (e i) = v i) (hout : ∀ i ∉ Set.range e, w i = 1) :
    extendMatrix e (Matrix.diagonal v) = Matrix.diagonal w := by
  unfold extendMatrix
  rw [← Matrix.diagonal_one, fromBlocks_diagonal]
  ext x y
  obtain ⟨x, rfl⟩ := (frameEquiv e).surjective x
  obtain ⟨y, rfl⟩ := (frameEquiv e).surjective y
  simp only [reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.diagonal_apply,
    Equiv.apply_eq_iff_eq]
  split
  · next h => subst y; cases x with
    | inl i => exact (hin i).symm
    | inr i => exact (hout i.val i.property).symm
  · rfl

open RootIndex (signedCoordinate)

private theorem hyperbolicDiagonal_eq (t : I → Rˣ) :
    hyperbolicDiagonal t = Matrix.diagonal (fun p => (signedUnit t p : R)) := by
  congr 1
  funext p
  cases p <;> rfl

@[simp] private theorem signedUnit_partner (t : I → Rˣ) (p : Indices I) :
    signedUnit t (partner p) = (signedUnit t p)⁻¹ := by
  cases p <;> simp [signedUnit, partner]

private theorem coordinate_partner (p : Indices I) : coordinate (partner p) = coordinate p := by
  cases p <;> rfl

private theorem signedCoordinate_same (a : Rˣ) (p : Indices I) :
    signedUnit (torusTuple (signedCoordinate p) a) p = a := by
  cases p <;> simp [signedUnit, torusTuple, signedCoordinate]

private theorem signedCoordinate_other (a : Rˣ) (p x : Indices I) (h : coordinate x ≠ coordinate p) :
    signedUnit (torusTuple (signedCoordinate p) a) x = 1 := by
  cases p <;> cases x <;> simp_all [coordinate, signedUnit, torusTuple, signedCoordinate,
    Pi.single_apply]

private theorem signedUnit_sub (a : Rˣ) (y z : I → ℤ) (p : Indices I) :
    signedUnit (torusTuple (y - z) a) p =
      signedUnit (torusTuple y a) p / signedUnit (torusTuple z a) p := by
  cases p <;> simp [signedUnit, torusTuple, zpow_sub, div_eq_mul_inv, mul_inv, mul_comm]

private theorem long_torus (p : Indices I) (a : Rˣ) :
    longMatrix p (diagonal a) = hyperbolicDiagonal (torusTuple (signedCoordinate p) a) := by
  rw [hyperbolicDiagonal_eq]
  unfold longMatrix
  rw [diagonal_value]
  apply extendMatrix_diagonal
  · intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · change (signedUnit (torusTuple (signedCoordinate p) a) p : R) = a
      rw [signedCoordinate_same]
    · change (signedUnit (torusTuple (signedCoordinate p) a) (partner p) : R) = ↑a⁻¹
      rw [signedUnit_partner, signedCoordinate_same]
  · intro x hx
    have hn : coordinate x ≠ coordinate p := by
      intro he
      apply hx
      cases p <;> cases x <;> cases he
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    rw [signedCoordinate_other a p x hn, Units.val_one]

private theorem short_torus (p q : Indices I) (h : coordinate p ≠ coordinate q) (a : Rˣ) :
    shortMatrix p q h (diagonal a) =
      hyperbolicDiagonal (torusTuple (signedCoordinate p - signedCoordinate q) a) := by
  rw [hyperbolicDiagonal_eq]
  unfold shortMatrix
  have hh : shortSigns R p q * (diagonal a⁻¹).valᵀ * shortSigns R p q = (diagonal a⁻¹).val := by
    rw [diagonal_value, Matrix.diagonal_transpose]
    have hcomm : Commute (shortSigns R p q) (Matrix.diagonal ![(↑a⁻¹ : R), ↑(a⁻¹)⁻¹]) := by
      unfold shortSigns
      exact Matrix.commute_diagonal _ _
    rw [hcomm.eq, Matrix.mul_assoc, shortSigns_sq, Matrix.mul_one]
  rw [pairedBlock, diagonal_inv, hh, diagonal_value, diagonal_value, fromBlocks_diagonal]
  have hp : signedUnit (torusTuple (signedCoordinate p - signedCoordinate q) a) p = a := by
    rw [signedUnit_sub, signedCoordinate_same, signedCoordinate_other a q p h, div_one]
  have hq : signedUnit (torusTuple (signedCoordinate p - signedCoordinate q) a) q = a⁻¹ := by
    rw [signedUnit_sub, signedCoordinate_same, signedCoordinate_other a p q h.symm, one_div]
  apply extendMatrix_diagonal
  · rintro (i | i)
    all_goals
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi with rfl | rfl
    · change (↑(signedUnit (torusTuple (signedCoordinate p - signedCoordinate q) a) p) : R) = a
      rw [hp]
    · change (↑(signedUnit (torusTuple (signedCoordinate p - signedCoordinate q) a) q) : R) = ↑a⁻¹
      rw [hq]
    · change (↑(signedUnit (torusTuple (signedCoordinate p - signedCoordinate q) a) (partner p)) : R) = ↑a⁻¹
      rw [signedUnit_partner, hp]
    · change (↑(signedUnit (torusTuple (signedCoordinate p - signedCoordinate q) a) (partner q)) : R) = ↑(a⁻¹)⁻¹
      rw [signedUnit_partner, hq]
  · intro x hx
    have np : coordinate x ≠ coordinate p := by
      intro he
      apply hx
      cases p <;> cases x <;> cases he
      · exact ⟨.inl 0, rfl⟩
      · exact ⟨.inr 0, rfl⟩
      · exact ⟨.inr 0, rfl⟩
      · exact ⟨.inl 0, rfl⟩
    have nq : coordinate x ≠ coordinate q := by
      intro he
      apply hx
      cases q <;> cases x <;> cases he
      · exact ⟨.inl 1, rfl⟩
      · exact ⟨.inr 1, rfl⟩
      · exact ⟨.inr 1, rfl⟩
      · exact ⟨.inl 1, rfl⟩
    rw [signedUnit_sub, signedCoordinate_other a p x np, signedCoordinate_other a q x nq]
    simp

theorem matrixValues : MatrixValues.{u} := by
  intro I R _ _ _ r
  refine ⟨rootUpper_value r, rootLower_value r, ?_⟩
  intro a
  cases r with
  | long p => exact long_torus p a
  | short p q h => exact short_torus p q h a

private theorem first_ne_second (r : RootIndex I) : r.first ≠ r.second := by
  cases r with
  | long p => cases p <;> simp [RootIndex.first, RootIndex.second, partner]
  | short p q h => exact fun he => h (congrArg coordinate he)

private theorem rootUpper_entry (r : RootIndex I) (a : R) :
    r.matrix (upper a) r.first r.second = a := by
  cases r with
  | long p =>
    change extendMatrix (longFrame p) (upper a).val (longFrame p 0) (longFrame p 1) = a
    rw [extendMatrix_frame]
    rfl
  | short p q h =>
    change extendMatrix (shortFrame p q h) (pairedBlock p q (upper a))
      (shortFrame p q h (.inl 0)) (shortFrame p q h (.inl 1)) = a
    rw [extendMatrix_frame]
    rfl

private theorem rootLower_entry (r : RootIndex I) (a : R) :
    r.matrix (lower a) r.second r.first = a := by
  cases r with
  | long p =>
    change extendMatrix (longFrame p) (lower a).val (longFrame p 1) (longFrame p 0) = a
    rw [extendMatrix_frame]
    rfl
  | short p q h =>
    change extendMatrix (shortFrame p q h) (pairedBlock p q (lower a))
      (shortFrame p q h (.inl 1)) (shortFrame p q h (.inl 0)) = a
    rw [extendMatrix_frame]
    rfl

private theorem rootMatrix_frame (r : RootIndex I) (g : SL₂ R) :
    r.matrix g r.second r.first = g.val 1 0 := by
  cases r with
  | long p =>
    change extendMatrix (longFrame p) g.val (longFrame p 1) (longFrame p 0) = _
    exact extendMatrix_frame _ _ _ _
  | short p q h =>
    change extendMatrix (shortFrame p q h) (pairedBlock p q g)
      (shortFrame p q h (.inl 1)) (shortFrame p q h (.inl 0)) = _
    exact extendMatrix_frame _ _ _ _

private theorem diagonal_mul_single' (t : I → Rˣ) (i j : Indices I) (a : R) :
    hyperbolicDiagonal t * Matrix.single i j a =
      Matrix.single i j (↑(signedUnit t i / signedUnit t j) * a) * hyperbolicDiagonal t := by
  rw [hyperbolicDiagonal_eq]
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split
  · next h =>
    obtain ⟨rfl, rfl⟩ := h
    have he := congrArg (fun (b : Rˣ) => (b : R))
      (div_mul_cancel (signedUnit t i) (signedUnit t j))
    rw [Units.val_mul] at he
    rw [mul_right_comm, he]
  · simp

private theorem rootUpper_comm (r : RootIndex I) (t : I → Rˣ) (a : R) :
    hyperbolicDiagonal t * r.matrix (upper a) =
      r.matrix (upper (↑(signedUnit t r.first / signedUnit t r.second) * a)) *
        hyperbolicDiagonal t := by
  rw [rootUpper_value, rootUpper_value]
  cases r with
  | long p =>
    simp only [RootIndex.first, RootIndex.second, RootIndex.upperMatrix,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul_single']
  | short p q h =>
    simp only [RootIndex.first, RootIndex.second, RootIndex.upperMatrix,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul_single',
      signedUnit_partner, inv_div_inv]
    congr 3
    ring

private theorem rootLower_comm (r : RootIndex I) (t : I → Rˣ) (a : R) :
    hyperbolicDiagonal t * r.matrix (lower a) =
      r.matrix (lower (↑(signedUnit t r.second / signedUnit t r.first) * a)) *
        hyperbolicDiagonal t := by
  rw [rootLower_value, rootLower_value]
  cases r with
  | long p =>
    simp only [RootIndex.first, RootIndex.second, RootIndex.lowerMatrix,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul_single']
  | short p q h =>
    simp only [RootIndex.first, RootIndex.second, RootIndex.lowerMatrix,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul_single',
      signedUnit_partner, inv_div_inv]
    congr 3
    ring


private theorem signedCoordinate_monomial (t : I → Rˣ) (p : Indices I) :
    (∏ i, t i ^ signedCoordinate p i) = signedUnit t p := by
  have hs (i : I) (m : ℤ) : (∏ j, t j ^ ((Pi.single i m : I → ℤ) j)) = t i ^ m := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  cases p with
  | inl i => simpa [signedCoordinate, signedUnit] using hs i 1
  | inr i => simpa [signedCoordinate, signedUnit] using hs i (-1)

private theorem rootIndex_monomial (t : I → Rˣ) (r : RootIndex I) :
    (∏ i, t i ^ r.weight i) = signedUnit t r.first / signedUnit t r.second := by
  simp only [RootIndex.weight, Pi.sub_apply, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, signedCoordinate_monomial, div_eq_mul_inv]

end Symplectic


theorem rootMonomialValues : RootMonomialValues.{u} := by
  intro k I _ _ _ G c T m r α
  constructor <;> intro h R t
  · rw [rootIndex_monomial]
    exact h R t
  · have he := h R t
    rw [rootIndex_monomial] at he
    exact he

theorem diagonalMarkingExists : DiagonalMarkingExists.{u} := by
  intro k I _ _ _ G c
  obtain ⟨T, d, ht, hd, _, hm⟩ :=
    LinearAlgebraicGroups.SymplecticMatrixStructure.diagonalTorus k I G c
  refine ⟨T, ⟨Fintype.card I, ht⟩, hm, ⟨d, fun R t => ?_⟩⟩
  have hh := hd R (d.hom.app R t)
  have ht' : d.inv.app R (d.hom.app R t) = t :=
    congrArg (fun f => f.app R t) d.hom_inv_id
  change (show PointGroup I R from
    c.hom.app R (d.inv.app R (d.hom.app R t) ≫ T.inclusion.hom.hom)).val = _ at hh
  simpa only [ht'] using hh

private def specialLinearReindex {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [CommRing R] (e : A ≃ B) :
    Matrix.SpecialLinearGroup A R ≃* Matrix.SpecialLinearGroup B R where
  toFun g := ⟨Matrix.reindex e e g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  invFun g := ⟨Matrix.reindex e.symm e.symm g.val, by
    rw [Matrix.det_reindex_self]; exact g.property⟩
  left_inv g := Subtype.ext ((Matrix.reindex e e).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((Matrix.reindex e e).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((Matrix.reindexRingEquiv R e).map_mul g.val h.val)

private def standardRankOnePoints (k : Type u) [Field k] :
    Specs.StandardGroups.specialLinearPoints (k := k) (ULift.{u} (Fin 2)) ≅
      determinantOnePoints k :=
  NatIso.ofComponents (fun R =>
    (specialLinearReindex (R := R) (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)).toGrpIso)
    (by
      intro R S f
      apply GrpCat.ext
      intro g
      apply Subtype.ext
      rfl)

theorem representedSchemeMaps : RepresentedSchemeMaps.{u} := by
  intro k _
  let S := LinearAlgebraicGroups.StandardGroups.specialLinearGroup k (ULift.{u} (Fin 2))
  let e := LinearAlgebraicGroups.StandardGroups.specialLinearGroupPointsIso
    (k := k) (ι := ULift.{u} (Fin 2)) ≪≫ standardRankOnePoints k
  refine ⟨S, e, ?_⟩
  intro I _ _ G c r
  obtain ⟨F, hF⟩ := representedMaps k I G c r
  let f := (S.groupHomEquiv G).symm (e.hom ≫ F)
  refine ⟨f, fun R g => ?_⟩
  have hw := (S.groupHomEquiv G).apply_symm_apply (e.hom ≫ F)
  change (groupPointsFunctor k).map f = e.hom ≫ F at hw
  rw [hw]
  change (show PointGroup I R from c.hom.app R (F.app R
    (e.hom.app R (e.inv.app R g)))).val = _
  have he : e.hom.app R (e.inv.app R g) = g :=
    congrArg (fun m => m.app R g) e.inv_hom_id
  rw [he]
  exact hF R g

section Coordinates

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint rankOneWord CorootReflection)
open Specs.Pinning (RootCoordinate SplitBorelPair)
open Specs.AbstractPairing (Root IsAttachedCoroot)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open RootData.RootGroups (additivePoints isClosedImmersion_of_injectivePoints)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

open private additiveLineGroup additiveLinePointsIso rootPoint_eq rootPoint_comp
  characterUnit characterUnit_inv characterValue_eq_unit
  normalizes_of_point_conjugation tangent_weight_of_scalarAction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k}
variable {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I}
variable {T : ClosedSubgroup G.val}

private theorem upper_add {R : Type u} [CommRing R] (a b : R) :
    upper (a + b) = upper a * upper b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem lower_add {R : Type u} [CommRing R] (a b : R) :
    lower (a + b) = lower a * lower b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upper_zero {R : Type u} [CommRing R] : upper (0 : R) = 1 := by
  apply Subtype.ext
  rw [upper_value, Matrix.single_zero, add_zero]
  rfl

private theorem lower_zero {R : Type u} [CommRing R] : lower (0 : R) = 1 := by
  apply Subtype.ext
  rw [lower_value, Matrix.single_zero, add_zero]
  rfl

private def upperPoints : Specs.StandardGroups.additivePoints k ⟶ determinantOnePoints k where
  app R := GrpCat.ofHom
    { toFun := fun a => upper a.toAdd
      map_one' := upper_zero
      map_mul' := fun a b => upper_add a.toAdd b.toAdd }
  naturality R S f := by
    apply GrpCat.ext
    intro a
    change upper (f.hom (Multiplicative.toAdd a)) =
      Matrix.SpecialLinearGroup.map f.hom.toRingHom (upper (Multiplicative.toAdd a))
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper]

private def lowerPoints : Specs.StandardGroups.additivePoints k ⟶ determinantOnePoints k where
  app R := GrpCat.ofHom
    { toFun := fun a => lower a.toAdd
      map_one' := lower_zero
      map_mul' := fun a b => lower_add a.toAdd b.toAdd }
  naturality R S f := by
    apply GrpCat.ext
    intro a
    change lower (f.hom (Multiplicative.toAdd a)) =
      Matrix.SpecialLinearGroup.map f.hom.toRingHom (lower (Multiplicative.toAdd a))
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower]

private def rootMorphism (A : AdditiveLine k)
    (s : Specs.StandardGroups.additivePoints k ⟶ determinantOnePoints k)
    (F : determinantOnePoints k ⟶ (groupPointsFunctor k).obj G.val) :
    A.group ⟶ G.val :=
  (groupHomEquiv A.group G.val (additiveLineGroup A).property.1).symm
    ((additiveLinePointsIso A).inv ≫ s ≫ F)

private theorem rootMorphism_point (A : AdditiveLine k)
    (s : Specs.StandardGroups.additivePoints k ⟶ determinantOnePoints k)
    (F : determinantOnePoints k ⟶ (groupPointsFunctor k).obj G.val)
    (R : TestAlgebra k) (a : R) :
    rootPoint (rootMorphism A s F) R a = F.app R (s.app R (Multiplicative.ofAdd a)) := by
  have hf := (groupHomEquiv A.group G.val (additiveLineGroup A).property.1).apply_symm_apply
    ((additiveLinePointsIso A).inv ≫ s ≫ F)
  have he := congrArg (fun f => f.app R (additivePoints A R a)) hf
  rw [rootPoint_eq]
  refine he.trans ?_
  change F.app R (s.app R (Multiplicative.ofAdd ((additivePoints A R).symm
    (additivePoints A R a)))) = _
  rw [Equiv.symm_apply_apply]

private theorem additiveLine_smooth (A : AdditiveLine k) : Smooth A.group.X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap k (Polynomial k)).Smooth
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

private theorem additiveLine_split (A : AdditiveLine k) : Specs.RankOneFlag.IsSplitAdditive A.group :=
  ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨Iso.refl _⟩⟩

private theorem parameter_subgroup (α : Character T.group)
    (A : AdditiveLine k) (f : A.group ⟶ G.val)
    (inj : ∀ (R : TestAlgebra k), Function.Injective (rootPoint f R))
    (act : HasScalarAction T α f) :
    ∃ (U : ClosedSubgroup G.val) (x : RootCoordinate A T U α),
      IsRootSubgroup T U α ∧ x.val.hom ≫ U.inclusion = f := by
  have closed : IsClosedImmersion f.hom.hom.left :=
    isClosedImmersion_of_injectivePoints (additiveLineGroup A) G f (by
      intro R a b he
      obtain ⟨x, rfl⟩ := (additivePoints A R).surjective a
      obtain ⟨y, rfl⟩ := (additivePoints A R).surjective b
      change (additivePoints A R x ≫ f.hom.hom) = (additivePoints A R y ≫ f.hom.hom) at he
      rw [← rootPoint_eq, ← rootPoint_eq] at he
      exact congrArg (additivePoints A R) (inj R he))
  let U : ClosedSubgroup G.val := ⟨A.group, f, closed⟩
  have hcoord : HasScalarAction T α ((Iso.refl A.group).hom ≫ U.inclusion) := by
    simpa [U] using act
  refine ⟨U, ⟨Iso.refl A.group, hcoord⟩,
    ⟨additiveLine_smooth A, additiveLine_split A, ?_, ?_⟩, by simp [U]⟩
  · apply normalizes_of_point_conjugation
    intro R t p
    obtain ⟨a, rfl⟩ := (additivePoints A R).surjective p
    refine ⟨additivePoints A R (characterValue α R t * a), ?_⟩
    let z : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
    let fa : GroupPoints G.val R := additivePoints A R a ≫ f.hom.hom
    change (show GroupPoints G.val R from additivePoints A R (characterValue α R t * a) ≫
      f.hom.hom) = z * fa * z⁻¹
    dsimp only [fa]
    rw [← rootPoint_eq, ← rootPoint_eq]
    exact (act R t a).symm
  · exact tangent_weight_of_scalarAction T U α A (Iso.refl _) hcoord

private theorem scheme_conjugation_of_comm (m : DiagonalMarking c T) (α : Character T.group)
    {A : AdditiveLine k} (f : A.group ⟶ G.val) (M : ∀ R : TestAlgebra k, R → Matrix (Indices I) (Indices I) R)
    (hm : ∀ (R : TestAlgebra k) (a : R), (show PointGroup I R from c.hom.app R (rootPoint f R a)).val = M R a)
    (hcomm : ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (a : R),
      let z := m.points.hom.app R t
      hyperbolicDiagonal z * M R a = M R (characterValue α R t * a) * hyperbolicDiagonal z) :
    HasScalarAction T α f := by
  intro R t a
  dsimp only
  apply (mul_inv_eq_iff_eq_mul).mpr
  let C : GroupPoints G.val R →* PointGroup I R := (c.hom.app R).hom
  let z : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  have hinj : Function.Injective C := (ConcreteCategory.bijective_of_isIso (c.hom.app R)).injective
  apply hinj
  change C (z * rootPoint f R a) = C (rootPoint f R (characterValue α R t * a) * z)
  rw [map_mul, map_mul]
  apply Subtype.ext
  change (C (t ≫ T.inclusion.hom.hom)).val * (C (rootPoint f R a)).val =
    (C (rootPoint f R (characterValue α R t * a))).val * (C (t ≫ T.inclusion.hom.hom)).val
  change (show PointGroup I R from c.hom.app R (t ≫ T.inclusion.hom.hom)).val *
    (show PointGroup I R from c.hom.app R (rootPoint f R a)).val =
    (show PointGroup I R from c.hom.app R (rootPoint f R (characterValue α R t * a))).val *
      (show PointGroup I R from c.hom.app R (t ≫ T.inclusion.hom.hom)).val
  rw [m.diagonal_value, hm, hm]
  exact hcomm R t a

theorem rankOneCoordinates : RankOneCoordinates.{u} := by
  intro k I _ _ _ G c T m r α hmatch A
  obtain ⟨F, hF⟩ := representedMaps k I G c r
  let f := rootMorphism A upperPoints F
  let g := rootMorphism A lowerPoints F
  have hf (R : TestAlgebra k) (a : R) :
      (show PointGroup I R from c.hom.app R (rootPoint f R a)).val = r.matrix (upper a) := by
    rw [rootMorphism_point]
    exact hF R (upper a)
  have hg (R : TestAlgebra k) (a : R) :
      (show PointGroup I R from c.hom.app R (rootPoint g R a)).val = r.matrix (lower a) := by
    rw [rootMorphism_point]
    exact hF R (lower a)
  have hfa : HasScalarAction T α f := by
    apply scheme_conjugation_of_comm m α f (fun R a => r.matrix (upper a)) hf
    intro R t a
    rw [hmatch R t]
    exact rootUpper_comm r _ a
  have hga : HasScalarAction T α⁻¹ g := by
    apply scheme_conjugation_of_comm m α⁻¹ g (fun R a => r.matrix (lower a)) hg
    intro R t a
    let z := m.points.hom.app R t
    have he : characterUnit α R t = signedUnit z r.first / signedUnit z r.second :=
      Units.ext ((characterValue_eq_unit α R t).symm.trans (hmatch R t))
    rw [characterValue_eq_unit, characterUnit_inv, he, inv_div]
    exact rootLower_comm r z a
  obtain ⟨U, x, hx, hxu⟩ := parameter_subgroup α A f (by
    intro R a b h
    have he := (hf R a).symm.trans ((congrArg
      (fun z => (show PointGroup I R from c.hom.app R z).val) h).trans (hf R b))
    simpa only [rootUpper_entry] using congrArg (fun M => M r.first r.second) he) hfa
  obtain ⟨V, y, hy, hyv⟩ := parameter_subgroup α⁻¹ A g (by
    intro R a b h
    have he := (hg R a).symm.trans ((congrArg
      (fun z => (show PointGroup I R from c.hom.app R z).val) h).trans (hg R b))
    simpa only [rootLower_entry] using congrArg (fun M => M r.second r.first) he) hga
  exact ⟨U, V, x, y, hx, hy, fun R a => ⟨by rw [hxu]; exact hf R a, by rw [hyv]; exact hg R a⟩⟩

end Coordinates

private def scaledWord {R : Type u} [CommRing R] (b d : R) (a : Rˣ) : SL₂ R :=
  upper (b * (a : R)) * lower (d * (-(↑a⁻¹ : R))) * upper (b * (a : R))

private theorem scaledWord_value {R : Type u} [CommRing R] (b d : R) (a : Rˣ) :
    (scaledWord b d a).val =
      !![1 - b * d, b * (a : R) * (2 - b * d); -d * (↑a⁻¹ : R), 1 - b * d] := by
  have ha : (a : R) * (↑a⁻¹ : R) = 1 := Units.mul_inv a
  unfold scaledWord
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  all_goals simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -(b * d) * ha
  · linear_combination -(b * b * d * (a : R)) * ha
  · linear_combination -(b * d) * ha

private theorem scaledWord_ratio_entry {R : Type u} [CommRing R] (b d : R) (a : Rˣ) :
    (scaledWord b d a * (scaledWord b d 1)⁻¹).val 1 0 =
      d * (1 - b * d) * (1 - (↑a⁻¹ : R)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    scaledWord_value, scaledWord_value]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem scaledWord_normalized {R : Type u} [CommRing R] (b d : R) (hbd : b * d = 1)
    (a : Rˣ) :
    scaledWord b d a * (scaledWord b d 1)⁻¹ = diagonal a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    scaledWord_value, scaledWord_value, hbd]
  have hdb : d * b = 1 := (mul_comm d b).trans hbd
  apply Matrix.ext
  intro i j
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  all_goals simp [Specs.SymplecticDatumRankOneAndPinning.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (a : R) * hbd
  · linear_combination (↑a⁻¹ : R) * hdb

private def infinitesimalUnit (k : Type u) [Field k] : (DualNumber k)ˣ where
  val := ⟨1, 1⟩
  inv := ⟨1, -1⟩
  val_inv := by
    apply TrivSqZeroExt.ext
    · change (1 : k) * 1 = 1
      exact one_mul _
    · change (1 : k) * (-1) + 1 * 1 = 0
      simp
  inv_val := by
    apply TrivSqZeroExt.ext
    · change (1 : k) * 1 = 1
      exact one_mul _
    · change (1 : k) * 1 + (-1) * 1 = 0
      simp

private theorem normalization_from_word_entry {k : Type u} [Field k] (b d : kˣ)
    (h : (scaledWord (algebraMap k (DualNumber k) (b : k))
          (algebraMap k (DualNumber k) (d : k)) (infinitesimalUnit k) *
          (scaledWord (algebraMap k (DualNumber k) (b : k))
            (algebraMap k (DualNumber k) (d : k)) 1)⁻¹).val 1 0 = 0) :
    (b : k) * (d : k) = 1 := by
  rw [scaledWord_ratio_entry] at h
  have he := congrArg (fun x : DualNumber k => x.snd) h
  have hInv : (↑(infinitesimalUnit k)⁻¹ : DualNumber k).snd = -1 := rfl
  have he' : (d : k) * (1 - (b : k) * (d : k)) = 0 := by
    simpa [hInv, DualNumber.snd_mul, TrivSqZeroExt.algebraMap_eq_inl] using he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_left (Units.ne_zero d)) |>.symm

section Coroots

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots)
open Specs.RootGroups (AdditiveLine IsRootSubgroup rootPoint rankOneWord)
open Specs.AbstractPairing (Root IsAttachedCoroot)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

open private rootPoint_comp rootPoint_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private subgroupOf_mutual_iso subgroupOf_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private additiveIso_linear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k}
variable {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I}
variable {T : ClosedSubgroup G.val}

private theorem affine_coordinate_comparison
    (A : AdditiveLine k) (U V : ClosedSubgroup G.val)
    (i : U.group ≅ V.group) (hi : i.hom ≫ V.inclusion = U.inclusion)
    (x : A.group ≅ U.group) (y : A.group ≅ V.group) :
    ∃ b : kˣ, ∀ (R : TestAlgebra k) (a : R),
      rootPoint (x.hom ≫ U.inclusion) R a =
        rootPoint (y.hom ≫ V.inclusion) R (algebraMap k R (b : k) * a) := by
  let j := x ≪≫ i ≪≫ y.symm
  obtain ⟨b, hb⟩ := additiveIso_linear A A j
  refine ⟨b, fun R a => ?_⟩
  have hj : j.hom ≫ (y.hom ≫ V.inclusion) = x.hom ≫ U.inclusion := by simp [j, hi]
  rw [← hj, rootPoint_comp, hb R a, ← rootPoint_eq]

private theorem same_root_coordinates (hG : IsReductive G) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (α : Character T.group) (hα : α ∈ absoluteRoots T)
    (A : AdditiveLine k) (U V : ClosedSubgroup G.val)
    (hU : IsRootSubgroup T U α) (hV : IsRootSubgroup T V α)
    (x : A.group ≅ U.group) (y : A.group ≅ V.group) :
    ∃ b : kˣ, ∀ (R : TestAlgebra k) (a : R),
      rootPoint (x.hom ≫ U.inclusion) R a =
        rootPoint (y.hom ≫ V.inclusion) R (algebraMap k R (b : k) * a) := by
  obtain ⟨_, _, W, _, _, _, _, hu⟩ :=
    (RootData.RootGroups.rootSubgroups G hG T hT hmax).2 α hα
  obtain ⟨i, hi⟩ := subgroupOf_mutual_iso
    (subgroupOf_trans (hu U hU).2 (hu V hV).1) (subgroupOf_trans (hu V hV).2 (hu U hU).1)
  exact affine_coordinate_comparison A U V i hi x y

private theorem hyperbolicDiagonal_injective {R : Type u} [CommRing R] :
    Function.Injective (fun t : I → Rˣ => hyperbolicDiagonal t) := by
  intro z t h
  funext i
  apply Units.ext
  simpa [hyperbolicDiagonal] using congrArg (fun M => M (.inl i) (.inl i)) h

private theorem coroot_tuple_of_word (m : DiagonalMarking c T) (r : RootIndex I)
    {A : AdditiveLine k} (x y : A.group ⟶ G.val)
    (b d : kˣ) (cochar : Specs.CharacterDescent.Cocharacter T.group)
    (hx : ∀ (R : TestAlgebra k) (a : R),
      (show PointGroup I R from c.hom.app R (rootPoint x R a)).val =
        r.matrix (upper (algebraMap k R (b : k) * a)))
    (hy : ∀ (R : TestAlgebra k) (a : R),
      (show PointGroup I R from c.hom.app R (rootPoint y R a)).val =
        r.matrix (lower (algebraMap k R (d : k) * a)))
    (hw : ∀ (R : TestAlgebra k) (a : Rˣ),
      cocharacterPoint cochar R a ≫ T.inclusion.hom.hom =
        rankOneWord x y R a * (rankOneWord x y R 1)⁻¹) :
    ∀ (R : TestAlgebra k) (a : Rˣ),
      m.points.hom.app R (cocharacterPoint cochar R a) = torusTuple r.coroot a := by
  obtain ⟨F, hF⟩ := representedMaps k I G c r
  let H (R : TestAlgebra k) : SL₂ R →* PointGroup I R :=
    (c.hom.app R).hom.comp (F.app R).hom
  have hH (R : TestAlgebra k) (g : SL₂ R) : (H R g).val = r.matrix g := by
    change (show PointGroup I R from c.hom.app R (F.app R g)).val = _
    exact hF R g
  let w (R : TestAlgebra k) := scaledWord (algebraMap k R (b : k)) (algebraMap k R (d : k))
  have hw₁ (R : TestAlgebra k) (a : Rˣ) :
      (c.hom.app R).hom (rankOneWord x y R a) = H R (w R a) := by
    have hp (a : R) : (c.hom.app R).hom (rootPoint x R a) =
        H R (upper (algebraMap k R (b : k) * a)) :=
      Subtype.ext ((hx R a).trans (hH R _).symm)
    have hn (a : R) : (c.hom.app R).hom (rootPoint y R a) =
        H R (lower (algebraMap k R (d : k) * a)) :=
      Subtype.ext ((hy R a).trans (hH R _).symm)
    unfold rankOneWord w scaledWord
    simp only [map_mul, hp, hn]
  have hw₂ (R : TestAlgebra k) (a : Rˣ) :
      hyperbolicDiagonal (m.points.hom.app R (cocharacterPoint cochar R a)) =
        r.matrix (w R a * (w R 1)⁻¹) := by
    have hl := m.diagonal_value R (cocharacterPoint cochar R a)
    have hh := congrArg (fun z : GroupPoints G.val R => (c.hom.app R).hom z) (hw R a)
    rw [map_mul, map_inv, hw₁, hw₁, ← map_inv (H R), ← map_mul (H R)] at hh
    exact hl.symm.trans ((congrArg Subtype.val hh).trans (hH R _))
  have hn : (b : k) * (d : k) = 1 := by
    let R₀ := CommAlgCat.of k (DualNumber k)
    have hh := congrArg (fun M : Matrix (Indices I) (Indices I) R₀ => M r.second r.first)
      (hw₂ R₀ (infinitesimalUnit k))
    let z : I → (DualNumber k)ˣ := m.points.hom.app R₀ (cocharacterPoint cochar R₀ (infinitesimalUnit k))
    change hyperbolicDiagonal z r.second r.first =
      r.matrix (w R₀ (infinitesimalUnit k) * (w R₀ 1)⁻¹) r.second r.first at hh
    rw [rootMatrix_frame, hyperbolicDiagonal_eq, Matrix.diagonal_apply_ne _ (first_ne_second r).symm]
      at hh
    exact normalization_from_word_entry b d hh.symm
  intro R a
  have hnR : algebraMap k R (b : k) * algebraMap k R (d : k) = 1 := by
    rw [← map_mul, hn, map_one]
  apply hyperbolicDiagonal_injective
  refine (hw₂ R a).trans ?_
  change r.matrix
      (scaledWord (algebraMap k R (b : k)) (algebraMap k R (d : k)) a *
        (scaledWord (algebraMap k R (b : k)) (algebraMap k R (d : k)) 1)⁻¹) = _
  rw [scaledWord_normalized _ _ hnR]
  exact (matrixValues I R r).2.2 a

theorem attachedCorootValues : AttachedCorootValues.{u} := by
  intro k I _ _ _ G c T m hG hT hmax r α hmatch
  have hα : α.val ∈ absoluteRoots T := α.property
  have hneg : α.val⁻¹ ∈ absoluteRoots T :=
    (((RootData.RootGroups.rootSubgroups G hG T hT hmax).2 α.val hα).2.1
      α.val⁻¹ |>.mpr (Or.inr rfl)).1
  constructor
  · obtain ⟨C, t, hC, ht, D, E, hpair, Q, F, P, A, p, n, hp, hn, hp', hn', ⟨rr⟩⟩ :=
      RootData.RootGroups.rankOneRootGroups G hG T hT hmax α.val hα
    exact ⟨rr.coroot, C, t, hC, ht, D, E, hpair, Q, F, P, A, p, n, hp, hn, hp', hn', rr, rfl⟩
  · intro cochar hcochar
    obtain ⟨C, t, hC, ht, D, E, hpair, Q, F, P, A, p, n, hp, hn, _, _, rr, rfl⟩ := hcochar
    obtain ⟨U, V, x, y, hx, hy, hv⟩ := rankOneCoordinates m r α.val hmatch A
    obtain ⟨b, hb⟩ := same_root_coordinates hG hT hmax α.val hα A
      (subgroupOfSubgroup C.subgroup D.contracting) U hp hx p.root x.val
    obtain ⟨d, hd⟩ := same_root_coordinates hG hT hmax α.val⁻¹ hneg A
      (subgroupOfSubgroup C.subgroup E.contracting) V hn hy n.root y.val
    apply coroot_tuple_of_word m r _ _ b d rr.coroot _ _ rr.coroot_word
    · intro R a
      change (show PointGroup I R from c.hom.app R
        (rootPoint (p.root.hom ≫ (subgroupOfSubgroup C.subgroup D.contracting).inclusion) R a)).val = _
      exact (congrArg (fun z : GroupPoints G.val R =>
        (show PointGroup I R from c.hom.app R z).val) (hb R a)).trans (hv R _).1
    · intro R a
      change (show PointGroup I R from c.hom.app R
        (rootPoint (n.root.hom ≫ (subgroupOfSubgroup C.subgroup E.contracting).inclusion) R a)).val = _
      exact (congrArg (fun z : GroupPoints G.val R =>
        (show PointGroup I R from c.hom.app R z).val) (hd R a)).trans (hv R _).2

end Coroots

section Borel

open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (IsRegular)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (characterValue)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

private def laurentCharacter (k : Type u) [Field k] :
    Multiplicative ℤ →* (LaurentPolynomial k)ˣ where
  toFun i :=
    { val := LaurentPolynomial.T i.toAdd
      inv := LaurentPolynomial.T (-i.toAdd)
      val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
      inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero] }
  map_one' := Units.ext LaurentPolynomial.T_zero
  map_mul' i j := Units.ext (LaurentPolynomial.T_add i.toAdd j.toAdd)

private theorem laurentCharacter_power (k : Type u) [Field k] (i : ℤ) :
    (laurentCharacter k (Multiplicative.ofAdd (1 : ℤ))) ^ i =
      laurentCharacter k (Multiplicative.ofAdd i) := by
  rw [← map_zpow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

private theorem laurentUnit_zpow_eq_one (k : Type u) [Field k] (i : ℤ)
    (h : (laurentCharacter k (Multiplicative.ofAdd (1 : ℤ))) ^ i = 1) : i = 0 := by
  rw [laurentCharacter_power] at h
  have hT : LaurentPolynomial.T i = (1 : LaurentPolynomial k) := congrArg Units.val h
  by_contra hn
  have hc := congrArg (fun p : LaurentPolynomial k => p.coeff i) hT
  have hni : 0 ≠ i := fun he => hn he.symm
  rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply, LaurentPolynomial.T_apply] at hc
  simp [hni] at hc

private def decreasingExponent (n : ℕ) :
    Indices (ULift.{u} (Fin (n + 1))) → ℤ :=
  Sum.elim (fun i => ↑(n + 1 - i.down.val : ℕ)) (fun i => -(↑(n + 1 - i.down.val : ℕ) : ℤ))

private theorem decreasingExponent_injective (n : ℕ) :
    Function.Injective (decreasingExponent n : Indices (ULift.{u} (Fin (n + 1))) → ℤ) := by
  rintro (i | i) (j | j) h
  all_goals
    have hi := i.down.isLt
    have hj := j.down.isLt
    simp only [decreasingExponent, Sum.elim_inl, Sum.elim_inr] at h
  · apply congrArg Sum.inl
    apply ULift.ext
    apply Fin.ext
    omega
  · omega
  · omega
  · apply congrArg Sum.inr
    apply ULift.ext
    apply Fin.ext
    omega

private theorem signedUnit_decreasing {n : ℕ} {R : Type u} [CommRing R] (a : Rˣ)
    (p : Indices (ULift.{u} (Fin (n + 1)))) :
    signedUnit (fun i => a ^ (n + 1 - i.down.val)) p = a ^ decreasingExponent n p := by
  cases p with
  | inl i =>
    change a ^ (n + 1 - i.down.val) = a ^ (↑(n + 1 - i.down.val : ℕ) : ℤ)
    rw [zpow_natCast]
  | inr i =>
    change (a ^ (n + 1 - i.down.val))⁻¹ = a ^ (-(↑(n + 1 - i.down.val : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast]

private theorem decreasing_regular {k : Type u} [Field k] (n : ℕ)
    {G : AffineAlgebraicGroup k}
    {c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k (ULift.{u} (Fin (n + 1)))}
    {T : ClosedSubgroup G.val} (m : DiagonalMarking c T)
    (lambda : Cocharacter T.group)
    (hl : ∀ (R : TestAlgebra k) (a : Rˣ) (i : ULift.{u} (Fin (n + 1))),
      (m.points.hom.app R (cocharacterPoint lambda R a)) i = a ^ (n + 1 - i.down.val))
    (r : Root T → RootIndex (ULift.{u} (Fin (n + 1))))
    (hr : ∀ α, MatchesRoot m (r α) α.val) :
    IsRegular T lambda := by
  intro α hp
  let R := CommAlgCat.of k (LaurentPolynomial k)
  let a : Rˣ := laurentCharacter k (Multiplicative.ofAdd (1 : ℤ))
  let t := cocharacterPoint lambda R a
  let z : ULift.{u} (Fin (n + 1)) → Rˣ := m.points.hom.app R t
  have hz : z = fun i => a ^ (n + 1 - i.down.val) := funext (hl R a)
  have hm := hr α R t
  change characterValue α.val R t = ↑(signedUnit z (r α).first / signedUnit z (r α).second) at hm
  rw [hz, signedUnit_decreasing, signedUnit_decreasing, div_eq_mul_inv, ← zpow_sub] at hm
  have hv := (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition
    T.group α.val lambda).2 R a
  change characterValue α.val R t = _ at hv
  rw [hp, zpow_zero, Units.val_one] at hv
  have he : a ^ (decreasingExponent n (r α).first - decreasingExponent n (r α).second) = 1 :=
    Units.ext (hm.symm.trans hv)
  have key := laurentUnit_zpow_eq_one k _ he
  exact first_ne_second (r α) (decreasingExponent_injective n (sub_eq_zero.mp key))

theorem simplePinning : SimplePinning.{u} := by
  classical
  intro k _ n G c T m hG hT hm lambda hl r hr
  refine ⟨CocharacterDynamics.existsLimitDecomposition G (lambda ≫ T.inclusion), ?_⟩
  intro D A
  have hregular := decreasing_regular n m lambda hl r hr
  obtain ⟨_, hB, hTB, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel G hG T hT hm lambda hregular D
  choose U V x y hx hy hpoint using fun α =>
    rankOneCoordinates m (r α) α.val (hr α) A
  refine ⟨hB, hTB, (fun α => ⟨U α, hx α⟩), (fun α => x α.val), ?_⟩
  intro α R a
  exact (hpoint α.val R a).1

end Borel

end

end LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning
