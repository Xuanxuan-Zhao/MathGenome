import Specs.LinearAlgebraicGroups.Arithmetic.ProjectiveMatrixExample
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix Topology
open scoped MatrixGroups RestrictedProduct

namespace LinearAlgebraicGroups.Arithmetic.ProjectiveMatrixExample

variable {R : Type*} [CommRing R]

private abbrev E (i j : Fin 2) : Mat R := Matrix.single i j 1

private lemma E_mul (i j k l : Fin 2) :
    (E i j : Mat R) * E k l = if j = k then E i l else 0 := by
  by_cases h : j = k
  · subst k
    simp [Matrix.single_mul_single_same]
  · simp [h, Matrix.single_mul_single_of_ne]

private lemma matrixUnits_ext {a b : MatrixAut R}
    (h : ∀ i j, a (E i j) = b (E i j)) : a = b := by
  have he : a.toLinearEquiv.toLinearMap = b.toLinearEquiv.toLinearMap :=
    (Matrix.stdBasis R (Fin 2) (Fin 2)).ext fun ⟨i, j⟩ => by
      rw [Matrix.stdBasis_eq_single]
      exact h i j
  ext X : 1
  exact DFunLike.congr_fun he X

private lemma conjugation_injective : Function.Injective (conjugation (R := R)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  refine le_antisymm (fun g hg => ?_) bot_le
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [Subgroup.mem_bot, ProjGenLinGroup.mk_eq_one, Subgroup.mem_center_iff]
  intro H
  apply Units.ext
  have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) (H : Mat R)
  rw [conjugation_mk, matrixConjugation_apply, AlgEquiv.one_apply] at h
  simpa [mul_assoc] using (congrArg (fun X : Mat R => X * (G : Mat R)) h).symm

/-- The columns are obtained by applying the first-column matrix units to a fixed
column of the first diagonal idempotent. -/
private def intertwiner (a : MatrixAut R) (j : Fin 2) : Mat R :=
  fun r i => a (E i 0) r j

private lemma intertwiner_mul (a : MatrixAut R) (j i k : Fin 2) :
    a (E i k) * intertwiner a j = intertwiner a j * E i k := by
  ext r l
  have h := congrArg (fun M : Mat R => M r j) (map_mul a (E i k) (E l 0)).symm
  rw [E_mul] at h
  by_cases hl : l = k
  · subst l
    rw [Matrix.mul_single_apply_same]
    simpa [Matrix.mul_apply, intertwiner] using h
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]
    simpa [Matrix.mul_apply, intertwiner, Ne.symm hl] using h

private lemma intertwiner_conjugates (a : MatrixAut R) (j : Fin 2)
    (h : IsUnit (intertwiner a j).det) :
    conjugation (ProjGenLinGroup.mk (GeneralLinearGroup.mk'' _ h)) = a := by
  symm
  apply matrixUnits_ext
  intro i k
  simp only [conjugation_mk, matrixConjugation_apply]
  let B : GL (Fin 2) R := GeneralLinearGroup.mk'' (intertwiner a j) h
  have he : a (E i k) * B.val = B.val * E i k := intertwiner_mul a j i k
  change a (E i k) = B.val * E i k * (↑B⁻¹ : Mat R)
  rw [← he, mul_assoc, Units.mul_inv, mul_one]

private lemma exists_unit_entry [IsLocalRing R] (a : MatrixAut R) :
    ∃ k j, IsUnit (a (E 0 0) k j) := by
  classical
  by_contra! h
  let b := Matrix.stdBasis R (Fin 2) (Fin 2)
  let X : Mat R := a (E 0 0)
  have hx : ∑ t, X t.1 t.2 • b t = X := by
    simpa [b, Matrix.stdBasis] using b.sum_repr X
  have hm : (a.symm X) 0 0 ∈ IsLocalRing.maximalIdeal R := by
    rw [← hx, map_sum]
    simp only [Matrix.sum_apply, map_smul, Matrix.smul_apply]
    exact Ideal.sum_mem _ fun t _ =>
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (h t.1 t.2))
  change (a.symm (a (E 0 0))) 0 0 ∈ _ at hm
  rw [AlgEquiv.symm_apply_apply] at hm
  change Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : R) 0 0 ∈ _ at hm
  rw [Matrix.single_apply_same] at hm
  exact (IsLocalRing.mem_maximalIdeal (1 : R)).1 hm isUnit_one

private lemma exists_unit_intertwiner [IsLocalRing R] (a : MatrixAut R) :
    ∃ j, IsUnit (intertwiner a j).det := by
  obtain ⟨k, j, h⟩ := exists_unit_entry a
  let C : Mat R := fun i r => a (E 0 i) k r
  have hc : C * intertwiner a j = a (E 0 0) k j • (1 : Mat R) := by
    ext i l
    rw [Matrix.mul_apply]
    have hh := congrArg (fun M : Mat R => M k j) (map_mul a (E 0 i) (E l 0)).symm
    rw [E_mul] at hh
    by_cases hil : i = l
    · subst l
      simpa [C, intertwiner, Matrix.mul_apply, Matrix.one_apply] using hh
    · simpa [C, intertwiner, Matrix.mul_apply, Matrix.one_apply, hil] using hh
  have hd := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hd
  have hu : IsUnit (C.det * (intertwiner a j).det) := hd.symm ▸ (h.pow _)
  exact ⟨j, isUnit_of_mul_isUnit_right hu⟩

theorem localConjugation : Specs.ProjectiveMatrixExample.LocalConjugation := by
  intro R _ _
  refine ⟨conjugation_injective, fun a => ?_⟩
  obtain ⟨j, h⟩ := exists_unit_intertwiner a
  exact ⟨_, intertwiner_conjugates a j h⟩

private lemma coordinates_toMatrix (a : MatrixAut R) :
    coordinates a = LinearMap.toMatrix (Matrix.stdBasis R (Fin 2) (Fin 2))
      (Matrix.stdBasis R (Fin 2) (Fin 2)) a.toLinearEquiv.toLinearMap := by
  apply Matrix.ext
  rintro ⟨r, s⟩ ⟨i, j⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single]
  rfl

private lemma coordinates_one : coordinates (1 : MatrixAut R) = 1 := by
  rw [coordinates_toMatrix]
  exact LinearMap.toMatrix_id _

private lemma coordinates_mul (a b : MatrixAut R) :
    coordinates (a * b) = coordinates a * coordinates b := by
  simp only [coordinates_toMatrix, ← LinearMap.toMatrix_mul]
  rfl

private lemma coordinateAction_coordinates (a : MatrixAut R) :
    coordinateAction (coordinates a) = a.toLinearEquiv.toLinearMap := by
  rw [coordinates_toMatrix, coordinateAction, Matrix.toLin_toMatrix]

private lemma map_mul_of_matrixUnits (L : Mat R →ₗ[R] Mat R)
    (h : ∀ (i j : Fin 2 × Fin 2), L (E i.1 i.2 * E j.1 j.2) = L (E i.1 i.2) * L (E j.1 j.2)) :
    ∀ X Y, L (X * Y) = L X * L Y := by
  let b := Matrix.stdBasis R (Fin 2) (Fin 2)
  have h₁ (i : Fin 2 × Fin 2) (Y : Mat R) :
      L (E i.1 i.2 * Y) = L (E i.1 i.2) * L Y := by
    have he : L.comp (LinearMap.mulLeft R (E i.1 i.2)) =
        (LinearMap.mulLeft R (L (E i.1 i.2))).comp L :=
      b.ext fun ⟨j, k⟩ => by simpa [b, Matrix.stdBasis_eq_single] using h i (j, k)
    exact DFunLike.congr_fun he Y
  intro X Y
  have he : L.comp (LinearMap.mulRight R Y) = (LinearMap.mulRight R (L Y)).comp L :=
    b.ext fun ⟨i, j⟩ => by simpa [b, Matrix.stdBasis_eq_single] using h₁ (i, j) Y
  exact DFunLike.congr_fun he X

theorem conjugationModel : Specs.ProjectiveMatrixExample.ConjugationModel := by
  intro R _
  refine ⟨fun a => ?_, fun C => ?_⟩
  · have h₁ : coordinates a * coordinates a.symm = 1 := by
      rw [← coordinates_mul, show a * a.symm = 1 from mul_inv_cancel a, coordinates_one]
    have h₂ : coordinates a.symm * coordinates a = 1 := by
      rw [← coordinates_mul, show a.symm * a = 1 from inv_mul_cancel a, coordinates_one]
    exact ⟨⟨coordinates a, coordinates a.symm, h₁, h₂⟩, rfl, rfl⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    let b := Matrix.stdBasis R (Fin 2) (Fin 2)
    let l := Matrix.toLinOfInv b b C.val_inv C.inv_val
    let a := AlgEquiv.ofLinearEquiv l h₁ (map_mul_of_matrixUnits (coordinateAction C.val) h₂)
    refine ⟨a, ?_, ?_⟩
    · change coordinates a = C.val
      rw [coordinates_toMatrix]
      change LinearMap.toMatrix b b (Matrix.toLin b b C.val) = C.val
      exact LinearMap.toMatrix_toLin b b C.val
    · intro a' h
      have he : coordinateAction C.val = a'.toLinearEquiv.toLinearMap :=
        h ▸ coordinateAction_coordinates a'
      exact AlgEquiv.ext fun X => (DFunLike.congr_fun he X).symm
  · rintro ⟨a, ha, _⟩
    change coordinateAction C.val 1 = 1 ∧ _
    have he : coordinateAction C.val = a.toLinearEquiv.toLinearMap :=
      ha ▸ coordinateAction_coordinates a
    refine ⟨?_, ?_⟩
    · rw [he]
      exact map_one a
    · intro i j
      rw [he]
      exact map_mul a _ _

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F] [T2Space F] [IsTopologicalRing F]
  [ContinuousInv₀ F]

omit [T2Space F] [IsTopologicalRing F] [ContinuousInv₀ F] in
private lemma continuous_project : Continuous (ProjGenLinGroup.mk : GL (Fin 2) F → PGL(2, F)) :=
  QuotientGroup.continuous_mk

omit [T2Space F] [ContinuousInv₀ F] in
private lemma continuous_coordinates :
    Continuous (fun g : PGL(2, F) => coordinates (conjugation g)) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center (GL (Fin 2) F))).continuous_iff.mpr
  refine continuous_matrix fun i j => ?_
  change Continuous (fun A : GL (Fin 2) F => coordinates (conjugation (ProjGenLinGroup.mk A)) i j)
  simp only [coordinates, conjugation_mk, matrixConjugation_apply]
  fun_prop

omit [T2Space F] in
private lemma continuousOn_matrix_unit {X : Type*} [TopologicalSpace X]
    {A : X → Mat F} (hA : Continuous A) :
    Continuous (fun x : {x : X // (A x).det ≠ 0} =>
      GeneralLinearGroup.mkOfDetNeZero (A x) x.property) := by
  rw [Units.continuous_iff]
  constructor
  · exact hA.comp continuous_subtype_val
  · have hf : Continuous (fun x : {x : X // (A x).det ≠ 0} => A x) :=
      hA.comp continuous_subtype_val
    simp only [GeneralLinearGroup.coe_inv, Matrix.inv_def, Ring.inverse_eq_inv]
    exact (hf.matrix_det.inv₀ fun x => x.property).smul hf.matrix_adjugate

private lemma continuous_of_coordinates {X : Type*} [TopologicalSpace X] (c : X → PGL(2, F))
    (hc : Continuous (fun x => coordinates (conjugation (c x)))) : Continuous c := by
  rw [← continuousOn_univ]
  apply continuousOn_of_locally_continuousOn
  intro x _
  obtain ⟨j, hj⟩ := exists_unit_intertwiner (conjugation (c x))
  have hA : Continuous (fun y : X => intertwiner (conjugation (c y)) j) :=
    continuous_matrix fun r i => (continuous_apply_apply (r, j) (i, 0)).comp hc
  let U : Set X := {y | (intertwiner (conjugation (c y)) j).det ≠ 0}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage hA.matrix_det
  refine ⟨U, hU, hj.ne_zero, ?_⟩
  rw [Set.univ_inter, continuousOn_iff_continuous_domRestrict]
  have hsec := continuous_project.comp (continuousOn_matrix_unit hA)
  refine hsec.congr ?_
  intro y
  change ProjGenLinGroup.mk (GeneralLinearGroup.mkOfDetNeZero
    (intertwiner (conjugation (c y.val)) j) y.property) = c y.val
  apply conjugation_injective
  have hmk : GeneralLinearGroup.mkOfDetNeZero _ y.property =
      GeneralLinearGroup.mk'' _ (isUnit_iff_ne_zero.mpr y.property) := Units.ext rfl
  rw [hmk]
  exact intertwiner_conjugates (conjugation (c y.val)) j _

theorem conjugationTopology : Specs.ProjectiveMatrixExample.ConjugationTopology := by
  intro F _ _ _ _ _
  let f := fun g : PGL(2, F) => coordinates (conjugation g)
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp continuous_coordinates) ?_⟩, ?_⟩
  · have hc := @continuous_of_coordinates F _ _ _ _ _ (PGL(2, F))
      (TopologicalSpace.induced f inferInstance) id continuous_induced_dom
    simpa only [induced_id] using continuous_iff_le_induced.mp hc
  · intro g h e
    apply conjugation_injective
    apply matrixUnits_ext
    intro i j
    ext r s
    exact congrFun (congrFun e (r, s)) (i, j)

end Topology

theorem squareClass : Specs.ProjectiveMatrixExample.SquareClass := by
  intro F _ A
  constructor
  · rintro ⟨B, h, hs⟩
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
    have he : (A.det : F) = (B.det : F) * (u : F) ^ 2 := by
      rw [← hu, map_mul, GeneralLinearGroup.det_scalar, Units.val_mul, Units.val_pow_eq_pow_val]
      simp
    rw [he]
    exact hs.mul ⟨u, by rw [pow_two]⟩
  · intro h
    exact ⟨A, rfl, h⟩

private lemma mem_integralClasses_iff (p : Prime) (g : PGL(2, ℚ_[p.val])) :
    g ∈ integralClasses p ↔
      ∃ A : GL (Fin 2) ℤ_[p.val],
        ProjGenLinGroup.mk (GeneralLinearGroup.map PadicInt.Coe.ringHom A) = g := by
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective b
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨ProjGenLinGroup.mk A, rfl⟩

private lemma padic_unit_valuation {p : ℕ} [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ((u : ℤ_[p]) : ℚ_[p]).valuation = 0 := by
  have h₁ : 0 ≤ ((u : ℤ_[p]) : ℚ_[p]).valuation := PadicInt.valuation_coe_nonneg
  have h₂ : 0 ≤ (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]).valuation := PadicInt.valuation_coe_nonneg
  have he : ((u : ℤ_[p]) : ℚ_[p]) * ((↑u⁻¹ : ℤ_[p]) : ℚ_[p]) = 1 := by
    exact_mod_cast u.mul_inv
  have hx := congrArg Padic.valuation he
  rw [Padic.valuation_mul (by exact_mod_cast u.ne_zero)
      (by exact_mod_cast (u⁻¹).ne_zero), Padic.valuation_one] at hx
  omega

theorem evenValuations : Specs.ProjectiveMatrixExample.EvenValuations := by
  intro A hA
  have he : ∀ p : ℕ, p.Prime → Even (padicValRat p (A.det : ℚ)) := by
    intro p hp
    let w : Prime := ⟨p, hp⟩
    obtain ⟨B, hB⟩ := (mem_integralClasses_iff w _).mp (hA w)
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hB
    let : Fact p.Prime := ⟨hp⟩
    have hdet : ((A.det : ℚ) : ℚ_[p]) =
        (↑B.det : ℤ_[p]) * (u : ℚ_[p]) ^ 2 := by
      change GeneralLinearGroup.map PadicInt.Coe.ringHom B *
        GeneralLinearGroup.scalar (Fin 2) u = GeneralLinearGroup.map (Rat.castHom _) A at hu
      have hval := congrArg (fun C : GL (Fin 2) ℚ_[p] => (C.det : ℚ_[p])) hu
      rw [map_mul, GeneralLinearGroup.map_det, GeneralLinearGroup.map_det,
        GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map] at hval
      exact hval.symm
    rw [← Padic.valuation_ratCast, hdet, Padic.valuation_mul
      (by exact_mod_cast B.det.ne_zero) (pow_ne_zero _ u.ne_zero),
      padic_unit_valuation, Padic.valuation_pow, zero_add]
    exact ⟨(u : ℚ_[p]).valuation, by ring⟩
  refine ⟨he, ?_⟩
  by_cases h : 0 ≤ (A.det : ℚ)
  · exact Or.inl (Rat.isSquare_iff_even_factorization.mpr ⟨h, he⟩)
  · apply Or.inr
    refine Rat.isSquare_iff_even_factorization.mpr ⟨by linarith, fun p hp => ?_⟩
    simpa only [padicValRat.neg] using he p hp


section Integral

variable {p : ℕ} [Fact p.Prime]

private abbrev intEmbedding : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom

private def intMatrixEmbedding : Mat ℤ_[p] →+* Mat ℚ_[p] := intEmbedding.mapMatrix

private lemma mapIntMat_injective : Function.Injective (intMatrixEmbedding (p := p)) := by
  intro A B h
  apply Matrix.ext
  intro i j
  exact Subtype.val_injective (congrFun (congrFun h i) j)

private lemma mapMatrix_unit {S : Type*} [CommRing S] (f : R →+* S)
    (i j : Fin 2) : f.mapMatrix (E i j) = E i j := by
  change (E i j : Mat R).map f = E i j
  simp [E]

private lemma map_conjugation {S : Type*} [CommRing S] (f : R →+* S)
    (g : PGL(2, R)) (X : Mat R) :
    f.mapMatrix (conjugation g X) =
      conjugation (ProjGenLinGroup.map f g) (f.mapMatrix X) := by
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  simp only [ProjGenLinGroup.map_mk, conjugation_mk, matrixConjugation_apply, map_mul]
  rfl

private def liftMatrixAction (a : MatrixAut ℚ_[p])
    (ha : ∀ i j, ‖coordinates a i j‖ ≤ 1) (X : Mat ℤ_[p]) : Mat ℤ_[p] :=
  fun r s => ∑ t : Fin 2 × Fin 2, X t.1 t.2 * ⟨coordinates a (r, s) t, ha _ _⟩

private lemma map_liftMatrixAction (a : MatrixAut ℚ_[p])
    (ha : ∀ i j, ‖coordinates a i j‖ ≤ 1) (X : Mat ℤ_[p]) :
    intMatrixEmbedding (liftMatrixAction a ha X) = a (intMatrixEmbedding X) := by
  let Y : Mat ℚ_[p] := intEmbedding.mapMatrix X
  let b := Matrix.stdBasis ℚ_[p] (Fin 2) (Fin 2)
  have hy : ∑ t, Y t.1 t.2 • b t = Y := by
    simpa [b, Matrix.stdBasis] using b.sum_repr Y
  apply Matrix.ext
  intro r s
  change (↑(liftMatrixAction a ha X r s) : ℚ_[p]) = a Y r s
  conv_rhs => rw [← hy, map_sum]
  simp only [liftMatrixAction, PadicInt.coe_sum, PadicInt.coe_mul, Matrix.sum_apply,
    map_smul, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun ⟨i,j⟩ _ => ?_
  rw [show b (i,j) = E i j from Matrix.stdBasis_eq_single ℚ_[p] i j]
  rfl

private def restrictMatrixAut (a : MatrixAut ℚ_[p])
    (ha : ∀ i j, ‖coordinates a i j‖ ≤ 1)
    (hb : ∀ i j, ‖coordinates a.symm i j‖ ≤ 1) : MatrixAut ℤ_[p] where
  toFun := liftMatrixAction a ha
  invFun := liftMatrixAction a.symm hb
  left_inv X := mapIntMat_injective (by
    rw [map_liftMatrixAction, map_liftMatrixAction, AlgEquiv.symm_apply_apply])
  right_inv X := mapIntMat_injective (by
    rw [map_liftMatrixAction, map_liftMatrixAction, AlgEquiv.apply_symm_apply])
  map_mul' X Y := mapIntMat_injective (by
    rw [map_liftMatrixAction, map_mul, map_mul, map_mul, map_liftMatrixAction, map_liftMatrixAction])
  map_add' X Y := mapIntMat_injective (by
    rw [map_liftMatrixAction, map_add, map_add, map_add, map_liftMatrixAction, map_liftMatrixAction])
  commutes' r := mapIntMat_injective (by
    have he : intMatrixEmbedding (algebraMap ℤ_[p] (Mat ℤ_[p]) r) =
        algebraMap ℚ_[p] (Mat ℚ_[p]) (intEmbedding r) := by
      change (algebraMap ℤ_[p] (Mat ℤ_[p]) r).map intEmbedding = _
      rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero intEmbedding)]
      rfl
    rw [map_liftMatrixAction, he, AlgEquiv.commutes])

private lemma integral_conjugation_coordinates (w : Prime) (b : PGL(2, ℤ_[w.val]))
    (i j : Fin 2 × Fin 2) :
    ‖coordinates (conjugation (ProjGenLinGroup.map intEmbedding b)) i j‖ ≤ 1 := by
  have he := map_conjugation (intEmbedding (p := w.val)) b (E j.1 j.2)
  rw [mapMatrix_unit] at he
  rw [coordinates, ← he]
  exact (conjugation b (E j.1 j.2) i.1 i.2).property

theorem integralConjugation : Specs.ProjectiveMatrixExample.IntegralConjugation := by
  intro w g
  constructor
  · rintro ⟨b, rfl⟩ i j
    exact ⟨integral_conjugation_coordinates w b i j, by
      rw [← (ProjGenLinGroup.map (intEmbedding (p := w.val))).map_inv b]
      exact integral_conjugation_coordinates w b⁻¹ i j⟩
  · intro hg
    have he : conjugation g⁻¹ = (conjugation g).symm := map_inv conjugation g
    let ha : ∀ i j, ‖coordinates (conjugation g) i j‖ ≤ 1 := fun i j => (hg i j).1
    let hb : ∀ i j, ‖coordinates (conjugation g).symm i j‖ ≤ 1 := fun i j =>
      he ▸ (hg i j).2
    let a := restrictMatrixAut (conjugation g) ha hb
    obtain ⟨b, hba⟩ := (localConjugation ℤ_[w.val]).2 a
    refine ⟨b, conjugation_injective ?_⟩
    apply matrixUnits_ext
    intro i j
    have hu : (intEmbedding (p := w.val)).mapMatrix (E i j) = E i j := mapMatrix_unit _ _ _
    calc
      conjugation (ProjGenLinGroup.map PadicInt.Coe.ringHom b) (E i j) =
          intMatrixEmbedding (conjugation b (E i j)) := by
        rw [← hu, ← map_conjugation]
        rfl
      _ = conjugation g (E i j) := by
        rw [hba]
        change intMatrixEmbedding (liftMatrixAction (conjugation g) ha (E i j)) = _
        exact (map_liftMatrixAction (conjugation g) ha (E i j)).trans (congrArg (conjugation g) hu)

private lemma mem_integralGL (A : GL (Fin 2) ℚ_[p]) :
    A ∈ (GeneralLinearGroup.map (n := Fin 2) intEmbedding).range ↔
    ∀ i j, ‖A.val i j‖ ≤ 1 ∧ ‖A.inv i j‖ ≤ 1 := by
  constructor
  · rintro ⟨B, rfl⟩ i j
    exact ⟨(B.val i j).property, (B.inv i j).property⟩
  · intro h
    let B : Mat ℤ_[p] := fun i j => ⟨A.val i j, (h i j).1⟩
    let C : Mat ℤ_[p] := fun i j => ⟨A.inv i j, (h i j).2⟩
    have hB : intMatrixEmbedding B = A.val := rfl
    have hC : intMatrixEmbedding C = A.inv := rfl
    refine ⟨⟨B, C, ?_, ?_⟩, Units.ext hB⟩
    · apply mapIntMat_injective
      rw [map_mul, hB, hC, map_one, A.val_inv]
    · apply mapIntMat_injective
      rw [map_mul, hB, hC, map_one, A.inv_val]

private lemma integralGL_isOpen :
    IsOpen ((GeneralLinearGroup.map (n := Fin 2) (intEmbedding (p := p))).range :
      Set (GL (Fin 2) ℚ_[p])) := by
  let M : Set (Mat ℚ_[p]) := Set.range (intEmbedding (p := p)).mapMatrix
  have hM : IsOpen M := PadicInt.isOpenEmbedding_coe.matrix_map.isOpen_range
  have hEq : ((GeneralLinearGroup.map (n := Fin 2) (intEmbedding (p := p))).range :
      Set (GL (Fin 2) ℚ_[p])) = Units.val ⁻¹' M ∩ (fun A : GL (Fin 2) ℚ_[p] => A.inv) ⁻¹' M := by
    ext A
    change A ∈ (GeneralLinearGroup.map (n := Fin 2) intEmbedding).range ↔
      A.val ∈ M ∧ A.inv ∈ M
    rw [mem_integralGL]
    have hm (X : Mat ℚ_[p]) : X ∈ M ↔ ∀ i j, ‖X i j‖ ≤ 1 := by
      constructor
      · rintro ⟨Y, rfl⟩ i j
        exact (Y i j).property
      · exact fun hx => ⟨fun i j => ⟨X i j, hx i j⟩, rfl⟩
    simp only [hm]
    constructor
    · exact fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
    · exact fun h i j => ⟨h.1 i j, h.2 i j⟩
  rw [hEq]
  exact (hM.preimage Units.continuous_val).inter (hM.preimage (by
    change Continuous (fun A : GL (Fin 2) ℚ_[p] => (A⁻¹).val)
    fun_prop))

private lemma integralClasses_isOpen (w : Prime) :
    IsOpen (integralClasses w : Set PGL(2, ℚ_[w.val])) := by
  have hm : IsOpenMap (ProjGenLinGroup.mk : GL (Fin 2) ℚ_[w.val] → PGL(2, ℚ_[w.val])) :=
    QuotientGroup.isOpenMap_coe
  convert hm _ (integralGL_isOpen (p := w.val)) using 1
  ext g
  rw [Set.mem_image]
  change g ∈ integralClasses w ↔ _
  rw [mem_integralClasses_iff]
  exact ⟨fun ⟨A, hA⟩ => ⟨_, ⟨A, rfl⟩, hA⟩,
    fun ⟨_, ⟨A, rfl⟩, hA⟩ => ⟨A, hA⟩⟩

private lemma rational_integral_of_large_prime (x : ℚ) (w : Prime) (hw : x.den < w.val) :
    ‖(x : ℚ_[w.val])‖ ≤ 1 := by
  rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast, padicValRat_def,
    padicValNat.eq_zero_of_not_dvd (fun h => (not_le_of_gt hw) (Nat.le_of_dvd x.den_pos h))]
  simp

theorem rationalDiagonal : Specs.ProjectiveMatrixExample.RationalDiagonal := by
  have h (g : PGL(2, ℚ)) : ∀ᶠ w in Filter.cofinite, localClass w g ∈ integralClasses w := by
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
    let den (z : (Fin 2 × Fin 2) × Bool) :=
      if z.2 then (A.val z.1.1 z.1.2).den else (A.inv z.1.1 z.1.2).den
    let d := Finset.univ.sup den
    have hden (z) : den z ≤ d := Finset.le_sup (f := den) (Finset.mem_univ z)
    have hf : {w : Prime | w.val ≤ d}.Finite :=
      (Set.finite_Iic d).preimage (Set.injOn_of_injective Subtype.val_injective)
    filter_upwards [hf.compl_mem_cofinite] with w hw
    have hd : d < w.val := lt_of_not_ge hw
    change ProjGenLinGroup.mk (GeneralLinearGroup.map (Rat.castHom _) A) ∈ integralClasses w
    apply (mem_integralClasses_iff w _).mpr
    have hm : GeneralLinearGroup.map (Rat.castHom ℚ_[w.val]) A ∈
        (GeneralLinearGroup.map (n := Fin 2) intEmbedding).range := by
      apply (mem_integralGL _).mpr
      intro i j
      exact ⟨rational_integral_of_large_prime _ w (lt_of_le_of_lt
          (by simpa [den] using hden ((i, j), true)) hd),
        rational_integral_of_large_prime _ w (lt_of_le_of_lt
          (by simpa [den] using hden ((i, j), false)) hd)⟩
    obtain ⟨B, hB⟩ := hm
    exact ⟨B, congrArg ProjGenLinGroup.mk hB⟩
  refine ⟨{ toFun := fun g => ⟨fun w => localClass w g, h g⟩
            map_one' := by ext w; exact map_one (localClass w)
            map_mul' := fun a b => by ext w; exact map_mul (localClass w) a b },
    fun _ _ => rfl⟩

end Integral

section Examples

private def diagUnit (u : Rˣ) : GL (Fin 2) R where
  val := Matrix.diagonal fun i => if i = 0 then (u : R) else 1
  inv := Matrix.diagonal fun i => if i = 0 then (↑u⁻¹ : R) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i = 0 <;> simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i = 0 <;> simp [h]

@[simp] private lemma det_diagUnit (u : Rˣ) : (diagUnit u).val.det = (u : R) := by
  simp [diagUnit, Matrix.det_diagonal]

private lemma continuous_real_entry :
    Continuous (fun g : PGL(2, ℝ) => coordinates (conjugation g) (0, 1) (0, 1)) :=
  (continuous_apply_apply (0, 1) (0, 1)).comp continuous_coordinates

private lemma real_entry_diagUnit (u : ℝˣ) :
    coordinates (conjugation (ProjGenLinGroup.mk (diagUnit u))) (0, 1) (0, 1) = (u : ℝ) := by
  change ((diagUnit u).val * (E 0 1 : Mat ℝ) * (diagUnit u).inv) 0 1 = _
  simp [diagUnit, Matrix.mul_diagonal]

theorem realNoncompact : Specs.ProjectiveMatrixExample.RealNoncompact := by
  intro hc
  obtain ⟨b, hb⟩ := (hc.image continuous_real_entry).bddAbove
  let u : ℝˣ := Units.mk0 (max b 0 + 1) (by positivity)
  have hm : (u : ℝ) ∈
      (fun g : PGL(2, ℝ) => coordinates (conjugation g) (0, 1) (0, 1)) '' Set.univ :=
    ⟨ProjGenLinGroup.mk (diagUnit u), Set.mem_univ _, real_entry_diagUnit u⟩
  have hle := hb hm
  change max b 0 + 1 ≤ b at hle
  linarith [le_max_left b (0 : ℝ)]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma square_neg_one_five : IsSquare (-1 : ℚ_[five.val]) := by
  change IsSquare (-1 : ℚ_[5])
  let f : Polynomial ℤ_[5] := Polynomial.X ^ 2 + 1
  have hd : f.derivative = Polynomial.C 2 * Polynomial.X := by
    simp [f, Polynomial.derivative_pow, Polynomial.C_ofNat]
  have h : ‖f.aeval (2 : ℤ_[5])‖ < ‖f.derivative.aeval (2 : ℤ_[5])‖ ^ 2 := by
    rw [hd]
    have h5 : (2 : ℤ_[5]) ^ 2 + 1 = 5 := by ring
    have h4 : (2 : ℤ_[5]) * 2 = 4 := by ring
    simp only [f, map_add, map_pow, Polynomial.aeval_X, map_one, map_mul,
      Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, h5, h4]
    change ‖((5 : ℕ) : ℤ_[5])‖ < ‖((4 : ℕ) : ℤ_[5])‖ ^ 2
    rw [PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 5 4), one_pow]
    exact PadicInt.norm_natCast_lt_one_iff.mpr (dvd_refl 5)
  obtain ⟨z, hz, _⟩ := hensels_lemma h
  have hz' : z ^ 2 + 1 = 0 := by simpa [f] using hz
  refine ⟨(z : ℚ_[5]), ?_⟩
  have hcast := congrArg (PadicInt.Coe.ringHom : ℤ_[5] →+* ℚ_[5]) hz'
  simp only [map_add, map_pow, map_one, map_zero] at hcast
  change (z : ℚ_[5]) ^ 2 + 1 = 0 at hcast
  rw [← pow_two]
  linear_combination -hcast

private lemma nonsquare_two_five : ¬ IsSquare (2 : ℚ_[five.val]) := by
  change ¬ IsSquare (2 : ℚ_[5])
  rintro ⟨y, hy⟩
  have hy2 : y ^ 2 = 2 := by rw [pow_two, ← hy]
  have hv : (2 : ℚ_[5]).valuation = 0 := by
    change (((2 : ℕ) : ℚ_[5]).valuation = 0)
    rw [Padic.valuation_natCast]
    norm_num [padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 2)]
  have hvy := congrArg Padic.valuation hy2
  rw [Padic.valuation_pow, hv] at hvy
  have hi : ‖y‖ ≤ 1 := (Padic.norm_le_one_iff_val_nonneg _).2 (by omega)
  let z : ℤ_[5] := ⟨y, hi⟩
  have hz : z ^ 2 = 2 := by
    apply Subtype.val_injective
    change y ^ 2 = (2 : ℚ_[5])
    exact hy2
  have hmod : PadicInt.toZMod z ^ 2 = (2 : ZMod 5) := by
    simpa only [map_pow, map_ofNat] using congrArg (PadicInt.toZMod (p := 5)) hz
  exact (by decide : ∀ a : ZMod 5, a ^ 2 ≠ 2) _ hmod

private lemma square_mem_padicInts {p : ℕ} [Fact p.Prime] {x : ℚ_[p]}
    (hx : ‖x‖ ≤ 1) :
    IsSquare x ↔ x ∈ Set.range (fun z : ℤ_[p] => (z : ℚ_[p]) ^ 2) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : ‖y‖ ≤ 1 := by
      rw [norm_mul] at hx
      nlinarith [norm_nonneg y]
    exact ⟨⟨y, hy⟩, pow_two _⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(z : ℚ_[p]), pow_two _⟩

private lemma open_nonsquare_integral (w : Prime) :
    IsOpen {g : PGL(2, ℚ_[w.val]) | g ∈ integralClasses w ∧ ¬ squareDet g} := by
  let S := Set.range (fun z : ℤ_[w.val] => (z : ℚ_[w.val]) ^ 2)
  let : CompactSpace ℤ_[w.val] := PadicInt.compactSpace w.val
  have hcoe : Continuous (fun z : ℤ_[w.val] => (z : ℚ_[w.val])) := continuous_subtype_val
  have hc : IsClosed S := (isCompact_range (hcoe.pow 2)).isClosed
  let U : Set (GL (Fin 2) ℚ_[w.val]) :=
    ((GeneralLinearGroup.map (n := Fin 2) (intEmbedding (p := w.val))).range :
      Set (GL (Fin 2) ℚ_[w.val])) ∩
      (fun A => A.val.det) ⁻¹' Sᶜ
  have hU : IsOpen U := integralGL_isOpen.inter
    (hc.isOpen_compl.preimage Units.continuous_val.matrix_det)
  have hm : IsOpenMap (ProjGenLinGroup.mk : GL (Fin 2) ℚ_[w.val] → PGL(2, ℚ_[w.val])) :=
    QuotientGroup.isOpenMap_coe
  suffices he : {g : PGL(2, ℚ_[w.val]) | g ∈ integralClasses w ∧ ¬ squareDet g} =
      ProjGenLinGroup.mk '' U by rw [he]; exact hm _ hU
  ext g
  have hs (B : GL (Fin 2) ℤ_[w.val]) :
      squareDet (ProjGenLinGroup.mk (GeneralLinearGroup.map intEmbedding B)) ↔
        (GeneralLinearGroup.map intEmbedding B).val.det ∈ S := by
    rw [squareClass]
    apply square_mem_padicInts
    change ‖((GeneralLinearGroup.map intEmbedding B).det : ℚ_[w.val])‖ ≤ 1
    rw [GeneralLinearGroup.map_det, Units.coe_map]
    exact (B.det : ℤ_[w.val]).property
  change (_ ∧ _) ↔ _
  rw [mem_integralClasses_iff w, Set.mem_image]
  constructor
  · rintro ⟨⟨B, rfl⟩, hB⟩
    exact ⟨_, ⟨⟨B, rfl⟩, fun hsB => hB ((hs B).2 hsB)⟩, rfl⟩
  · rintro ⟨_, ⟨⟨B, rfl⟩, hB⟩, rfl⟩
    exact ⟨⟨B, rfl⟩, fun hsB => hB ((hs B).1 hsB)⟩

theorem adelicObstruction : Specs.ProjectiveMatrixExample.AdelicObstruction := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have hI : IsOpen {x : FiniteAdeles | ∀ w : Prime, x w ∈ integralClasses w} :=
      RestrictedProduct.isOpen_forall_mem integralClasses_isOpen
    have he : Continuous (fun x : FiniteAdeles => x five) :=
      RestrictedProduct.continuous_eval five
    have h5 := (open_nonsquare_integral five).preimage he
    convert hI.inter h5 using 1
    ext x
    change (_ ∧ _) ↔ (_ ∧ _ ∧ _)
    exact ⟨fun h => ⟨h.1, h.1 five, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · let u : ℤ_[five.val]ˣ := (PadicInt.isUnit_iff.mpr
        (PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 5 2))).unit
    let a : PGL(2, ℚ_[five.val]) :=
      ProjGenLinGroup.mk (GeneralLinearGroup.map intEmbedding (diagUnit u))
    let x (w : Prime) : PGL(2, ℚ_[w.val]) := if h : five = w then h ▸ a else 1
    have ha : a ∈ integralClasses five := (mem_integralClasses_iff five a).2 ⟨_, rfl⟩
    have hx (w : Prime) : x w ∈ integralClasses w := by
      by_cases h : five = w
      · subst w
        simpa [x] using ha
      · simp [x, h]
    refine ⟨⟨x, Filter.Eventually.of_forall hx⟩, hx, ?_⟩
    change ¬ squareDet (x five)
    rw [show x five = a by simp [x]]
    change ¬ squareDet (ProjGenLinGroup.mk (GeneralLinearGroup.map intEmbedding (diagUnit u)))
    rw [squareClass, GeneralLinearGroup.map_det, Units.coe_map]
    change ¬ IsSquare (intEmbedding (p := five.val) (diagUnit u).val.det)
    rw [det_diagUnit, show (u : ℤ_[five.val]) = 2 from IsUnit.unit_spec _]
    exact nonsquare_two_five
  · rintro x ⟨hx, hns⟩ ⟨g, hg⟩
    obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
    have hloc (w : Prime) := hg w ▸ hx w
    have hd := (evenValuations A hloc).2
    apply hns
    rw [hg five]
    change squareDet (ProjGenLinGroup.mk (GeneralLinearGroup.map (Rat.castHom ℚ_[five.val]) A))
    rw [squareClass, GeneralLinearGroup.map_det, Units.coe_map]
    change IsSquare ((A.det : ℚ) : ℚ_[five.val])
    rcases hd with hd | hd
    · exact hd.map (Rat.castHom _)
    · obtain ⟨r, hr⟩ := hd
      have hs : IsSquare (-((A.det : ℚ) : ℚ_[five.val])) := by
        refine ⟨(r : ℚ_[five.val]), ?_⟩
        exact_mod_cast hr
      have hp := square_neg_one_five.mul hs
      rwa [neg_mul, one_mul, neg_neg] at hp

end Examples

end LinearAlgebraicGroups.Arithmetic.ProjectiveMatrixExample
