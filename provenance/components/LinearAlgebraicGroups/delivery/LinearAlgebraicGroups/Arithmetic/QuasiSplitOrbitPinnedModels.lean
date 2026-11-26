import LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import LinearAlgebraicGroups.Descent.Forms
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import LinearAlgebraicGroups.Classification.PinnedEquivalence
import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import LinearAlgebraicGroups.Affine.GroupSchemes
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open Module
open HopfAlgebra Coalgebra
open scoped BigOperators CategoryTheory.MonObj TensorProduct LinearAlgebraicGroups.Descent

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels

open Specs.QuasiSplitOrbitPinnedModels

set_option linter.style.haveILetI false

noncomputable section

theorem quadraticTensorSplitting : QuadraticTensorSplitting.{u,v} := by
  intro F E _ _ _ _ _
  let σ := Specs.UnitaryRankOne.quadraticConjugation F E
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra! h
    exact Specs.UnitaryRankOne.quadraticConjugation_ne_one F E (AlgEquiv.ext h)
  let f : E ⊗[F] E →ₐ[E] E × E :=
    Algebra.TensorProduct.lift (Algebra.ofId E (E × E))
      ((AlgHom.id F E).prod σ.toAlgHom) (fun _ _ => Commute.all _ _)
  have hf (x y : E) : f (x ⊗ₜ[F] y) = (x * y, x * σ y) := rfl
  have hos : ∃ z, f z = (0, 1) := by
    let d := σ a - a
    have hd : d ≠ 0 := sub_ne_zero.mpr ha
    refine ⟨(d⁻¹ ⊗ₜ[F] a) - ((d⁻¹ * a) ⊗ₜ[F] 1), ?_⟩
    rw [map_sub, hf, hf]
    apply Prod.ext
    · simp
    · change d⁻¹ * σ a - (d⁻¹ * a) * σ 1 = 1
      rw [map_one, mul_one, ← mul_sub, inv_mul_cancel₀ hd]
  obtain ⟨z, hz⟩ := hos
  have hsurj : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨(x ⊗ₜ[F] 1) + ((y - x) ⊗ₜ[F] 1) * z, ?_⟩
    rw [map_add, map_mul, hf, hf, hz]
    apply Prod.ext <;> simp
  have hdeg := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hdeg ▸ Nat.zero_lt_succ _)
  have hdim : Module.finrank E (E ⊗[F] E) = Module.finrank E (E × E) := by
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_self, hdeg]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩


theorem unitaryScalarSplitting : UnitaryScalarSplitting.{u,v} := by
  intro F E _ _ _ _ _ R _ _ _ _
  obtain ⟨e, he⟩ := quadraticTensorSplitting F E
  let f : R ⊗[F] E ≃ₐ[R] R × R :=
    (Algebra.TensorProduct.cancelBaseChange F E R R E).symm.trans
      ((Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) e).trans
        ((Algebra.TensorProduct.prodRight E R R E E).trans
          ((Algebra.TensorProduct.rid E R R).prodCongr (Algebra.TensorProduct.rid E R R))))
  have hf (x : R) (y : E) : f (x ⊗ₜ[F] y) =
      (x * algebraMap E R y,
        x * algebraMap E R (Specs.UnitaryRankOne.quadraticConjugation F E y)) := by
    dsimp only [f, AlgEquiv.trans_apply]
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    change ((Algebra.TensorProduct.rid E R R).prodCongr (Algebra.TensorProduct.rid E R R))
      ((Algebra.TensorProduct.prodRight E R R E E) (x ⊗ₜ[E] e (1 ⊗ₜ[F] y))) = _
    rw [he, Algebra.TensorProduct.prodRight_tmul]
    ext <;> simp [Algebra.smul_def, mul_comm]
  refine ⟨f, hf, fun z => ?_⟩
  let σ := Specs.UnitaryRankOne.quadraticConjugation F E
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [quadraticTensorInvolution, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul]
      change f (x ⊗ₜ[F] σ y) = (f (x ⊗ₜ[F] y)).swap
      rw [hf, hf, Prod.swap_prod_mk]
      have hσ : σ (σ y) = y := by
        have hd := Algebra.IsQuadraticExtension.finrank_eq_two F E
        let : FiniteDimensional F E := .of_finrank_pos (hd ▸ Nat.zero_lt_succ 1)
        have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans hd
        have h := pow_card_eq_one' (x := σ)
        rw [hc, pow_two] at h
        exact DFunLike.congr_fun h y
      simp only [← show σ = Specs.UnitaryRankOne.quadraticConjugation F E from rfl, hσ]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      rfl

section UnitaryModel

open Matrix


private theorem hyperbolicDual_involutive {R : Type v} [CommRing R] (g : SL₃ R) :
    hyperbolicDual (hyperbolicDual g) = g := by
  have hi : (hyperbolicDual g)⁻¹ = hyperbolicDual g⁻¹ := (map_inv _ _).symm
  apply Subtype.ext
  change ((hyperbolicDual g)⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm = g.val
  rw [hi]
  ext i j
  change ((g⁻¹)⁻¹).val (Fin.rev (Fin.rev i)) (Fin.rev (Fin.rev j)) = g.val i j
  rw [inv_inv, Fin.rev_rev, Fin.rev_rev]

open Matrix.SpecialLinearGroup in
private theorem hyperbolicDual_map {R S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (g : SL₃ R) :
    hyperbolicDual (SpecialLinearGroup.map f g) = SpecialLinearGroup.map f (hyperbolicDual g) := by
  apply Subtype.ext
  change ((SpecialLinearGroup.map f g)⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm =
    f.mapMatrix ((g⁻¹).val.transpose.submatrix Fin.revPerm Fin.revPerm)
  rw [← map_inv]
  rfl

open Matrix.SpecialLinearGroup in
private def slProduct (R : Type v) [CommRing R] : SL₃ (R × R) ≃* SL₃ R × SL₃ R :=
  MulEquiv.ofBijective ((SpecialLinearGroup.map (RingHom.fst R R)).prod (SpecialLinearGroup.map (RingHom.snd R R))) (by
    constructor
    · intro a b h
      apply Subtype.ext
      ext1 i j
      exact Prod.ext (congrArg (fun g : SL₃ R × SL₃ R => g.1.val i j) h)
        (congrArg (fun g : SL₃ R × SL₃ R => g.2.val i j) h)
    · rintro ⟨a, b⟩
      let A : Matrix (Fin 3) (Fin 3) (R × R) := fun i j => (a.val i j, b.val i j)
      have ha : (RingHom.fst R R).mapMatrix A = a.val := rfl
      have hb : (RingHom.snd R R).mapMatrix A = b.val := rfl
      have hA : A.det = 1 := by
        apply Prod.ext
        · change (RingHom.fst R R) A.det = 1
          rw [RingHom.map_det, ha, a.property]
        · change (RingHom.snd R R) A.det = 1
          rw [RingHom.map_det, hb, b.property]
      exact ⟨⟨A, hA⟩, Prod.ext (Subtype.ext ha) (Subtype.ext hb)⟩)

open Matrix.SpecialLinearGroup in
private def slRingEquiv {A B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B) :
    SL₃ A ≃* SL₃ B where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply _
  right_inv g := by ext i j; exact e.apply_symm_apply _
  map_mul' := map_mul (SpecialLinearGroup.map e.toRingHom)

open Matrix.SpecialLinearGroup in
theorem splitUnitaryPoints : SplitUnitaryPoints.{u,v} := by
  intro F E _ _ _ _ _ R _ _ _ _ e he
  let σ := quadraticTensorInvolution F E R
  let τ : SL₃ (R ⊗[F] E) →* SL₃ (R ⊗[F] E) :=
    hyperbolicDual.comp (map σ.toRingEquiv.toRingHom)
  let t := (slRingEquiv e.toRingEquiv).trans (slProduct R)
  let U := τ.eqLocus (MonoidHom.id _)
  have first_eq (g : SL₃ (R ⊗[F] E)) : (t g).1 =
      SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g := by
    ext i j
    rfl
  have second_eq (g : SL₃ (R ⊗[F] E)) : (t g).2 =
      SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom) g := by
    ext i j
    rfl
  have act (g : SL₃ (R ⊗[F] E)) :
      t (τ g) = (hyperbolicDual (t g).2, hyperbolicDual (t g).1) := by
    have h₁ : SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom)
        (map σ.toRingEquiv.toRingHom g) =
        SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom) g := by
      ext i j
      exact congrArg Prod.fst (he (g.val i j))
    have h₂ : SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom)
        (map σ.toRingEquiv.toRingHom g) =
        SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g := by
      ext i j
      exact congrArg Prod.snd (he (g.val i j))
    apply Prod.ext
    · simp only [first_eq, second_eq]
      change SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom)
        (hyperbolicDual (map σ.toRingEquiv.toRingHom g)) =
        hyperbolicDual (SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom) g)
      rw [← hyperbolicDual_map, h₁]
    · simp only [first_eq, second_eq, ]
      change SpecialLinearGroup.map ((RingHom.snd R R).comp e.toRingEquiv.toRingHom)
        (hyperbolicDual (map σ.toRingEquiv.toRingHom g)) =
        hyperbolicDual (SpecialLinearGroup.map ((RingHom.fst R R).comp e.toRingEquiv.toRingHom) g)
      rw [← hyperbolicDual_map, h₂]
  let p : U →* SL₃ R := (MonoidHom.fst _ _).comp (t.toMonoidHom.comp U.subtype)
  have second (g : U) : hyperbolicDual (t g.val).1 = (t g.val).2 := by
    have hg : τ g.val = g.val := g.prop
    exact congrArg Prod.snd ((act g.val).symm.trans (congrArg t hg))
  have hp : Function.Bijective p := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply t.injective
      exact Prod.ext h (((second x).symm.trans (congrArg hyperbolicDual h)).trans (second y))
    · intro g
      let b := t.symm (g, hyperbolicDual g)
      have hb : t b = (g, hyperbolicDual g) := t.apply_symm_apply _
      have hbU : b ∈ U := by
        change τ b = b
        apply t.injective
        rw [act, hb, hyperbolicDual_involutive]
      exact ⟨⟨b, hbU⟩, congrArg Prod.fst hb⟩
  refine ⟨U, fun _ => Iff.rfl, MulEquiv.ofBijective p hp, ?_, ?_⟩
  · exact fun g => first_eq g.val
  · intro g
    rw [← second_eq]
    exact second g


open Specs.SpecialLinearDatum (coordinatePairUnits)

variable {R : Type u} [CommRing R]

private theorem matrixSimpleCoroot_inv (i : Fin 2) (t : Rˣ) :
    (matrixSimpleCoroot i t)⁻¹ = matrixSimpleCoroot i t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) R)
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases hj : j = i.castSucc
  · simp [coordinatePairUnits, hj]
  by_cases hk : j = i.succ
  · have hs : i.succ ≠ i.castSucc := ((Fin.castSucc_lt_succ_iff).2 (le_refl i)).ne'
    simp [coordinatePairUnits, hk, hs]
  · simp [coordinatePairUnits, hj, hk]

private theorem matrixSimpleCoroot_map (σ : R ≃+* R) (i : Fin 2) (t : Rˣ) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (matrixSimpleCoroot i t) =
      matrixSimpleCoroot i (Units.map σ.toRingHom.toMonoidHom t) := by
  apply Subtype.ext
  change (Matrix.diagonal _).map σ = Matrix.diagonal _
  rw [Matrix.diagonal_map σ.map_zero]
  congr 1
  funext j
  by_cases hj : j = i.castSucc
  · simp [coordinatePairUnits, hj]
  by_cases hk : j = i.succ
  · have hs : i.succ ≠ i.castSucc := ((Fin.castSucc_lt_succ_iff).2 (le_refl i)).ne'
    simp [coordinatePairUnits, hk, hs, ← map_inv]
  · simp [coordinatePairUnits, hj, hk]

theorem unitaryCorootInterchange : UnitaryCorootInterchange.{u} := by
  intro R _ σ i t
  rw [unitaryDescentOperator, matrixSimpleCoroot_map]
  generalize Units.map σ.toRingHom.toMonoidHom t = s
  apply Subtype.ext
  change ((matrixSimpleCoroot i s)⁻¹).val.transpose.submatrix
    Fin.revPerm Fin.revPerm = _
  rw [matrixSimpleCoroot_inv]
  change (Matrix.diagonal _).transpose.submatrix Fin.revPerm Fin.revPerm =
    Matrix.diagonal _
  rw [Matrix.diagonal_transpose, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;> simp [coordinatePairUnits]

open Matrix.SpecialLinearGroup in
private theorem mapTransvection {R : Type u} [CommRing R] (σ : R ≃+* R)
    {i j : Fin 3} (h : i ≠ j) (t : R) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (transvection h t) =
      transvection h (σ t) := by
  apply Subtype.ext
  change ((1 : Matrix (Fin 3) (Fin 3) R) + Matrix.single i j t).map σ =
    (1 : Matrix (Fin 3) (Fin 3) R) + Matrix.single i j (σ t)
  ext r s
  simp only [Matrix.map_apply, Matrix.add_apply, map_add]
  congr 1
  · by_cases h : r = s <;> simp [Matrix.one_apply, h]
  · by_cases h' : i = r ∧ j = s <;> simp [h']

open Matrix.SpecialLinearGroup in
theorem unitaryPinningInterchange : UnitaryPinningInterchange.{u} := by
  intro R _ σ t
  dsimp only
  constructor <;> rw [unitaryDescentOperator, mapTransvection] <;>
    apply Subtype.ext <;>
    simp only [hyperbolicInverseTranspose, transvection_inv, transvection_coe, map_neg, neg_neg]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

end UnitaryModel
section OrbitField

theorem orbitFieldDegree : OrbitFieldDegree.{u,v} := by
  intro F K _ _ _ _ _ I ρ i
  letI := MulAction.compHom I ρ
  change Module.finrank F (IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)) =
    (diagramOrbit ρ i).ncard ∧ Algebra.IsSeparable F (orbitField ρ i)
  refine ⟨?_, inferInstance⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.fixingSubgroup_fixedField,
    Subgroup.index_eq_card, ← Nat.card_coe_set_eq]
  exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Gal(K/F) i)).symm

private theorem tensorProductOfEmbeddings {F K L J : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [FiniteDimensional F L] [Fintype J]
    (emb : J → (L →ₐ[F] K)) (hemb : Function.Injective emb)
    (hdeg : Module.finrank F L = Fintype.card J) :
    ∃ e : K ⊗[F] L ≃ₐ[K] (J → K),
      ∀ (x : K) (y : L) (j : J), e (x ⊗ₜ[F] y) j = x * emb j y := by
  classical
  let f : K ⊗[F] L →ₐ[K] (J → K) := Algebra.TensorProduct.lift (Algebra.ofId K (J → K))
    (AlgHom.pi emb) (fun _ _ => Commute.all _ _)
  have hf (x : K) (y : L) (j : J) : f (x ⊗ₜ[F] y) j = x * emb j y := rfl
  have separate (j l : J) (hjl : j ≠ l) : ∃ z, f z j = 1 ∧ f z l = 0 := by
    obtain ⟨y, hy⟩ : ∃ y : L, emb j y ≠ emb l y := by
      by_contra! h
      exact hjl (hemb (AlgHom.ext h))
    let d := emb j y - emb l y
    refine ⟨(d⁻¹ ⊗ₜ[F] y) - ((d⁻¹ * emb l y) ⊗ₜ[F] 1), ?_, ?_⟩
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one, ← mul_sub]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hy)
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one, sub_self]
  have singleton (j : J) : ∃ z, f z = Pi.single j 1 := by
    have h (l : {l : J // j ≠ l}) := separate j l l.property
    choose z hz using h
    refine ⟨∏ l, z l, ?_⟩
    funext l
    rw [map_prod]
    change (Pi.evalRingHom (fun _ : J => K) l) (∏ q, f (z q)) =
      (Pi.single j (1 : K) : J → K) l
    rw [map_prod]
    by_cases hl : l = j
    · subst l
      simp only [Pi.single_eq_same]
      exact Finset.prod_eq_one fun q _ => (hz q).1
    · rw [Pi.single_eq_of_ne hl]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨l, Ne.symm hl⟩ : {q : J // j ≠ q}))
        (hz ⟨l, Ne.symm hl⟩).2
  choose z hz using singleton
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨∑ j, (a j ⊗ₜ[F] (1 : L)) * z j, ?_⟩
    funext l
    rw [map_sum, Fintype.sum_apply, Finset.sum_eq_single l]
    · simp [hf, hz]
    · intro j _ hj
      simp [hf, hz, Pi.single_eq_of_ne hj.symm]
    · simp
  have hdim : Module.finrank K (K ⊗[F] L) = Module.finrank K (J → K) := by
    rw [Module.finrank_baseChange, Module.finrank_pi, hdeg]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

theorem orbitScalarSplitting : OrbitScalarSplitting.{u} := by
  classical
  intro F K _ _ _ _ _ I ρ i
  let L := orbitField ρ i
  let J := diagramOrbit ρ i
  letI := MulAction.compHom I ρ
  let H := MulAction.stabilizer Gal(K/F) i
  let j₀ (g : Gal(K/F)) : J := ⟨ρ g i, ⟨g, rfl⟩⟩
  have hs (j : J) : ∃ g, j₀ g = j := by
    obtain ⟨g, hg⟩ := j.property
    exact ⟨g, Subtype.ext hg⟩
  letI : Finite J := Finite.of_surjective j₀ hs
  letI : Fintype J := Fintype.ofFinite J
  have hH : L.fixingSubgroup = H := IntermediateField.fixingSubgroup_fixedField H
  have hfix (g : Gal(K/F)) : (∀ y : L, g y.val = y.val) ↔ g ∈ H := by
    rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y.val y.property⟩
  have same (g h : Gal(K/F)) : (∀ y : L, g y.val = h y.val) ↔ j₀ g = j₀ h := by
    calc
      (∀ y : L, g y.val = h y.val) ↔ (∀ y : L, (h⁻¹ * g) y.val = y.val) := by
        constructor
        · intro eq y
          simp only [AlgEquiv.mul_apply, eq y]
          exact h.symm_apply_apply _
        · intro eq y
          have hh := congrArg h (eq y)
          change h (h.symm (g y.val)) = h y.val at hh
          simpa only [AlgEquiv.apply_symm_apply] using hh
      _ ↔ h⁻¹ * g ∈ H := hfix _
      _ ↔ j₀ g = j₀ h := by
        change ρ (h⁻¹ * g) i = i ↔ j₀ g = j₀ h
        rw [map_mul, map_inv, Equiv.Perm.mul_apply]
        change (ρ h).symm (ρ g i) = i ↔ j₀ g = j₀ h
        rw [(ρ h).symm_apply_eq]
        exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  let rep (j : J) := (hs j).choose
  have hrep (j : J) : j₀ (rep j) = j := (hs j).choose_spec
  let emb (j : J) : L →ₐ[F] K := (rep j).toAlgHom.comp L.val
  have hemb (g : Gal(K/F)) (y : L) : emb (j₀ g) y = g y.val :=
    (same (rep (j₀ g)) g).2 (hrep (j₀ g)) y
  have hinj : Function.Injective emb := by
    intro j l h
    rw [← hrep j, ← hrep l]
    exact (same (rep j) (rep l)).mp (fun y => DFunLike.congr_fun h y)
  have hdeg : Module.finrank F L = Fintype.card J := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact (orbitFieldDegree ρ i).1
  obtain ⟨e, he⟩ := tensorProductOfEmbeddings emb hinj hdeg
  refine ⟨emb, e, hemb, he, ?_⟩
  intro g z j
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, he, he, map_mul]
      obtain ⟨h, rfl⟩ := hs j
      have htr : orbitTranslate ρ i g⁻¹ (j₀ h) = j₀ (g⁻¹ * h) := by
        apply Subtype.ext
        exact (congrArg (fun p : Equiv.Perm I => p i) (map_mul ρ g⁻¹ h)).symm
      rw [htr, hemb, hemb]
      change g x * h y.val = g x * g (g.symm (h y.val))
      rw [AlgEquiv.apply_symm_apply]
  | add z w hz hw => simp only [map_add, Pi.add_apply, hz, hw]

theorem orbitScalarSplittingOverAlgebras : OrbitScalarSplittingOverAlgebras.{u,v} := by
  classical
  intro F K _ _ _ _ _ I ρ i
  let L := orbitField ρ i
  let J := diagramOrbit ρ i
  letI : Finite J := Finite.of_surjective (Set.rangeFactorization (fun g => ρ g i))
    Set.rangeFactorization_surjective
  letI : Fintype J := Fintype.ofFinite J
  obtain ⟨emb, e, hemb, he, _⟩ := orbitScalarSplitting ρ i
  refine ⟨emb, hemb, fun R _ _ _ _ => ?_⟩
  let f : R ⊗[F] L ≃ₐ[R] (J → R) :=
    (Algebra.TensorProduct.cancelBaseChange F K R R L).symm.trans
      ((Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) e).trans
        ((Algebra.TensorProduct.piRight K R R (fun _ : J => K)).trans
          (AlgEquiv.piCongrRight (fun _ => Algebra.TensorProduct.rid K R R))))
  refine ⟨f, fun x y j => ?_⟩
  dsimp only [f, AlgEquiv.trans_apply]
  rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  change Algebra.TensorProduct.rid K R R
    (Algebra.TensorProduct.piRight K R R (fun _ : J => K) (x ⊗ₜ[K] e (1 ⊗ₜ[F] y)) j) = _
  simp only [Algebra.TensorProduct.piRight_tmul, he, one_mul]
  simp [Algebra.smul_def, mul_comm]


private theorem permFinTwo_eq_one_of_fixed {p : Equiv.Perm (Fin 2)} {i : Fin 2}
    (h : p i = i) : p = 1 := by
  apply Equiv.ext
  intro j
  change p j = j
  by_cases hj : j = i
  · simpa [hj] using h
  · have hp : p j ≠ i := fun e => hj (p.injective (e.trans h.symm))
    fin_cases i <;> fin_cases j <;> first | contradiction |
      (generalize hq : p _ = q at hp ⊢; fin_cases q <;> simp_all)

theorem quadraticOrbitField : QuadraticOrbitField.{u} := by
  classical
  intro F K _ _ _ _ _ ρ i htrans
  letI := MulAction.compHom (Fin 2) ρ
  let J := MulAction.stabilizer Gal(K/F) i
  let E := orbitField ρ i
  have hJ : J = ρ.ker := by
    ext σ
    change ρ σ i = i ↔ ρ σ = 1
    exact ⟨permFinTwo_eq_one_of_fixed, by rintro h; rw [h]; rfl⟩
  have hE : E = IntermediateField.fixedField ρ.ker := congrArg IntermediateField.fixedField hJ
  have horb : diagramOrbit ρ i = Set.univ := Set.eq_univ_of_forall htrans
  have hfin : Module.finrank F E = 2 := by
    rw [(orbitFieldDegree ρ i).1, horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  letI : Algebra.IsQuadraticExtension F E := ⟨hfin⟩
  letI : Algebra.IsSeparable F E := (orbitFieldDegree ρ i).2
  letI : FiniteDimensional F E := .of_finrank_pos (hfin ▸ by decide)
  let c := Specs.UnitaryRankOne.quadraticConjugation F E
  have hc : c ≠ 1 := Specs.UnitaryRankOne.quadraticConjugation_ne_one F E
  have hcard : Nat.card Gal(E/F) = 2 := (IsGalois.card_aut_eq_finrank F E).trans hfin
  have hall : ∀ a : Gal(E/F), a = 1 ∨ a = c := by
    obtain ⟨b, hb, hall⟩ := (Nat.card_eq_two_iff' (1 : Gal(E/F))).mp hcard
    have hbc : c = b := hall c hc
    intro a
    by_cases ha : a = 1
    · exact Or.inl ha
    · exact Or.inr ((hall a ha).trans hbc.symm)
  have hfix : E.fixingSubgroup = ρ.ker :=
    hE ▸ IntermediateField.fixingSubgroup_fixedField ρ.ker
  refine ⟨hE, inferInstance, inferInstance, fun σ y => ?_⟩
  have hres : (σ.restrictNormal E = 1) ↔ ρ σ = 1 := by
    change σ ∈ (AlgEquiv.restrictNormalHom E).ker ↔ σ ∈ ρ.ker
    rw [IntermediateField.restrictNormalHom_ker, hfix]
  have hval : (σ.restrictNormal E y).val = σ y.val :=
    AlgEquiv.restrictNormal_apply E σ y
  by_cases h : ρ σ = 1
  · rw [ite_eq_left h, ← hval, hres.mpr h]
    rfl
  · rw [ite_eq_right h, ← hval, (hall _).resolve_left (hres.not.mpr h)]

end OrbitField
section MatrixDatum

open Specs.SpecialLinearDatum

theorem attachedMatrixCoroots : AttachedMatrixCoroots.{u} := by
  intro k _ r S s
  obtain ⟨T, L, M, B, D, hD, hpin, hsc⟩ :=
    RootData.SpecialLinearDatum.matrixPinnedDatum k r S s
  letI := D.comm
  refine ⟨T, L, M, B, D, hD, hpin, hsc, ?_, ?_⟩
  · intro i
    exact (hD.2 _).mpr ⟨i, rfl, rfl⟩
  · intro i R t
    dsimp only
    have h := hD.1 (adjacentRootIndex i)
    have hc := L.cocharacterPoint_eq (Specs.SpecialLinearDatum.coroot (r + 1) i.castSucc i.succ) R t
    change L.cocharacters (D.datum.rootDatum.coroot (M.indices (adjacentRootIndex i))) =
      Specs.SpecialLinearDatum.coroot (r + 1) i.castSucc i.succ at h
    rw [← h, LinearEquiv.symm_apply_apply] at hc
    rw [hc, h]
    congr 1
    funext j
    have hne : i.castSucc ≠ i.succ := ((Fin.castSucc_lt_succ_iff).mpr le_rfl).ne
    by_cases h₁ : j.down = i.castSucc
    · simp [Specs.SpecialLinearDatum.coroot, coordinate, coordinatePairUnits, h₁, hne.symm]
    by_cases h₂ : j.down = i.succ
    · simp [Specs.SpecialLinearDatum.coroot, coordinate, coordinatePairUnits, h₂, hne.symm]
    · simp [Specs.SpecialLinearDatum.coroot, coordinate, coordinatePairUnits, h₁, h₂]

end MatrixDatum

section HermitianModel

open Matrix

theorem unitaryScalarSplittingNaturality : UnitaryScalarSplittingNaturality.{u,v} := by
  intro F E _ _ _ _ _ R S _ _ _ _ _ _ _ _ f eR eS
  dsimp only
  intro hR hS z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, hS, hR]
      simp
  | add a b ha hb =>
      rw [map_add, map_add, ha, hb, map_add]
      exact Prod.ext (map_add f _ _).symm (map_add f _ _).symm

private theorem reverseEntries_eq {E : Type u} [CommRing E] (A : Matrix (Fin 3) (Fin 3) E) :
    A.submatrix Fin.revPerm Fin.revPerm =
      hyperbolicGram E * A * hyperbolicGram E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      hyperbolicGram]

theorem hyperbolicFixedEquation : HyperbolicFixedEquation.{u} := by
  intro E _ σ g
  let J := hyperbolicGram E
  let b := Matrix.SpecialLinearGroup.map σ.toRingHom g
  let B := b.val.transpose
  let C := (b⁻¹).val.transpose
  have hBC : B * C = 1 := by
    change b.val.transpose * (b⁻¹).val.transpose = 1
    rw [← Matrix.transpose_mul]
    change ((b⁻¹ * b).val).transpose = 1
    rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have hCB : C * B = 1 := by
    change (b⁻¹).val.transpose * b.val.transpose = 1
    rw [← Matrix.transpose_mul]
    change ((b * b⁻¹).val).transpose = 1
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have hJ : J * J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J, Matrix.mul_apply, Fin.sum_univ_three, hyperbolicGram]
  change unitaryDescentOperator σ g = g ↔ B * J * g.val = J
  have hformula : (unitaryDescentOperator σ g).val = J * C * J :=
    reverseEntries_eq _
  constructor
  · intro hg
    have hg' : J * C * J = g.val := hformula.symm.trans (congrArg Subtype.val hg)
    calc
      B * J * g.val = B * J * (J * C * J) := congrArg (B * J * ·) hg'.symm
      _ = (B * (J * J) * C) * J := by simp [mul_assoc]
      _ = J := by simp [hJ, hBC]
  · intro hg
    apply Subtype.ext
    rw [hformula]
    calc
      J * C * J = J * C * (B * J * g.val) := congrArg (J * C * ·) hg.symm
      _ = (J * (C * B) * J) * g.val := by simp [mul_assoc]
      _ = g.val := by simp [hCB, hJ]

theorem unitaryDescentFixedPoints : UnitaryDescentFixedPoints.{u,v} := by
  intro F E _ _ _ σ g
  exact hyperbolicFixedEquation σ.toRingEquiv g

end HermitianModel
section UnitaryScheme

open CategoryTheory.Limits
open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)

private def reindexSpecialLinear {I J R : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [CommRing R] (e : I ≃ J) :
    Matrix.SpecialLinearGroup I R ≃* Matrix.SpecialLinearGroup J R where
  toFun g := ⟨g.val.submatrix e.symm e.symm,
    by rw [Matrix.det_submatrix_equiv_self, g.property]⟩
  invFun g := ⟨g.val.submatrix e e, by rw [Matrix.det_submatrix_equiv_self, g.property]⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.submatrix_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.submatrix_apply]
  map_mul' g h := by
    apply Subtype.ext
    change (g.val * h.val).submatrix e.symm e.symm =
      g.val.submatrix e.symm e.symm * h.val.submatrix e.symm e.symm
    rw [Matrix.submatrix_mul_equiv]

private def specialLinearThreePointIso (E : Type u) [Field E] :
    (groupPointsFunctor E).obj (StandardGroups.specialLinearGroup E (ULift.{u} (Fin 3))).val ≅
      specialLinearThreePoints E :=
  StandardGroups.specialLinearGroupPointsIso E (ULift.{u} (Fin 3)) ≪≫
    NatIso.ofComponents (fun R => MulEquiv.toGrpIso (reindexSpecialLinear (R := R) Equiv.ulift)) (by
      intro R S f
      apply GrpCat.ext
      intro g
      apply Subtype.ext
      rfl)

set_option backward.isDefEq.respectTransparency false in
private def unitaryMatrixOperator (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] :
    let A := extendScalars F E ⋙ specialLinearThreePoints E
    A ⟶ A where
  app R := GrpCat.ofHom (hyperbolicDual.comp (Matrix.SpecialLinearGroup.map
    (quadraticTensorInvolution F E R).toRingEquiv.toRingHom))
  naturality {R S} f := by
    apply GrpCat.ext
    intro g
    let φ : R ⊗[F] E →+* S ⊗[F] E :=
      (Algebra.TensorProduct.map f.hom (AlgHom.id F E)).toRingHom
    let σ₁ := (quadraticTensorInvolution F E R).toRingEquiv
    let σ₂ := (quadraticTensorInvolution F E S).toRingEquiv
    change hyperbolicDual (Matrix.SpecialLinearGroup.map σ₂.toRingHom
      (Matrix.SpecialLinearGroup.map φ g)) = Matrix.SpecialLinearGroup.map φ
        (hyperbolicDual (Matrix.SpecialLinearGroup.map σ₁.toRingHom g))
    rw [← hyperbolicDual_map]
    congr 1
    apply Subtype.ext
    ext i j
    change σ₂ (φ (g.val i j)) = φ (σ₁ (g.val i j))
    generalize g.val i j = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem equalizerClosedSubgroup {k : Type u} [Field k] (A : AffineAlgebraicGroup k)
    (f g : A.val ⟶ A.val) :
    ∃ S : ClosedSubgroup A.val,
      RepresentsSubgroup S (fun _ x => x ≫ f.hom.hom = x ≫ g.hom.hom) := by
  let G := Grp.forget (SchemeOver k)
  let e := PreservesEqualizer.iso G f g
  let i := equalizer.ι f g
  have hi : e.inv ≫ i.hom.hom = equalizer.ι (G.map f) (G.map g) :=
    PreservesEqualizer.iso_inv_ι G f g
  have hi' : i.hom.hom = e.hom ≫ equalizer.ι (G.map f) (G.map g) := by
    rw [← hi, e.hom_inv_id_assoc]
  have hc : IsClosedImmersion i.hom.hom.left := by
    letI := A.property.1
    letI : IsAffineHom A.val.X.hom := inferInstance
    letI : IsSeparated (G.obj A.val).hom := inferInstanceAs (IsSeparated A.val.X.hom)
    letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    letI : IsClosedImmersion (equalizer.ι (G.map f) (G.map g)).left :=
      isClosedImmersion_equalizer_ι_left (G.map f) (G.map g)
    rw [hi', Over.comp_left]
    exact IsClosedImmersion.comp _ _
  refine ⟨⟨equalizer f g, i, hc⟩, fun X x => ?_⟩
  change x ≫ f.hom.hom = x ≫ g.hom.hom ↔ ∃ s, s ≫ i.hom.hom = x
  constructor
  · intro h
    refine ⟨equalizer.lift x h ≫ e.inv, ?_⟩
    rw [Category.assoc, hi]
    exact equalizer.lift_ι _ _
  · rintro ⟨s, rfl⟩
    have h := congrArg G.map (equalizer.condition f g)
    simp only [Functor.map_comp] at h
    change i.hom.hom ≫ f.hom.hom = i.hom.hom ≫ g.hom.hom at h
    simpa only [Category.assoc] using congrArg (s ≫ ·) h

set_option backward.isDefEq.respectTransparency false in
theorem hyperbolicUnitaryModel : HyperbolicUnitaryModel.{u} := by
  intro F E _ _ _ _ _
  letI : FiniteDimensional F E := .of_finrank_pos
    (Algebra.IsQuadraticExtension.finrank_eq_two F E ▸ Nat.zero_lt_succ 1)
  let A := StandardGroups.specialLinearGroup E (ULift.{u} (Fin 3))
  let W := LinearAlgebraicGroups.WeilRestriction.groupRepresentation F E A
  let m := W.2 ≪≫ Functor.isoWhiskerLeft (extendScalars F E) (specialLinearThreePointIso E)
  let d := unitaryMatrixOperator F E
  obtain ⟨s, hs⟩ := (groupHomComparison F W.1.val W.1.val W.1.property.1).2
    (m.hom ≫ d ≫ m.inv)
  have hmatrix (R : TestAlgebra F) (x : GroupPoints W.1.val R) :
      m.hom.app R (x ≫ s.hom.hom) =
        unitaryDescentOperator (quadraticTensorInvolution F E R).toRingEquiv (m.hom.app R x) := by
    have he := congrArg (fun n => n.app R x) hs
    change x ≫ s.hom.hom = m.inv.app R (d.app R (m.hom.app R x)) at he
    rw [he]
    exact GrpCat.hom_inv_apply (m.app R) _
  obtain ⟨U, hU⟩ := equalizerClosedSubgroup W.1 s (𝟙 W.1.val)
  have hinj (R : TestAlgebra F) :
      Function.Injective (fun x : GroupPoints W.1.val R => m.hom.app R x) :=
    Function.LeftInverse.injective (GrpCat.inv_hom_apply (m.app R))
  refine ⟨W.1, U, m, fun R g => ?_⟩
  dsimp only
  let x : GroupPoints W.1.val R := m.inv.app R g
  have hx : m.hom.app R x = g := GrpCat.hom_inv_apply (m.app R) g
  rw [← hx]
  rw [← hyperbolicFixedEquation, ← hmatrix]
  constructor
  · intro h
    have he : x ≫ s.hom.hom = x ≫ (𝟙 W.1.val : W.1.val ⟶ W.1.val).hom.hom := by
      rw [Grp.id_hom_hom, Category.comp_id]
      exact hinj R h
    obtain ⟨y, hy⟩ := (hU _ _).mp he
    exact ⟨y, congrArg (fun z => m.hom.app R z) hy⟩
  · rintro ⟨y, hy⟩
    have he := hinj R hy
    have h := (hU _ x).mpr ⟨y, he⟩
    rw [Grp.id_hom_hom, Category.comp_id] at h
    exact congrArg (fun z => m.hom.app R z) h

private theorem unitaryFirstProjection_tmul {F E : Type u} [Field F] [Field E] [Algebra F E]
    (R : TestAlgebra E) (x : (restrictTestAlgebra F E).obj R) (y : E) :
    unitaryFirstProjection (F := F) R (x ⊗ₜ[F] y) = x * algebraMap E R y := rfl

private theorem unitaryFirstProjection_natural {F E : Type u} [Field F] [Field E] [Algebra F E]
    {R S : TestAlgebra E} (a : R ⟶ S) :
    (unitaryFirstProjection (F := F) S).comp
        (Algebra.TensorProduct.map ((restrictTestAlgebra F E).map a).hom (AlgHom.id F E)).toRingHom =
      a.hom.toRingHom.comp (unitaryFirstProjection (F := F) R) := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      change unitaryFirstProjection (F := F) S (a.hom x ⊗ₜ[F] y) =
        a.hom (unitaryFirstProjection (F := F) R (x ⊗ₜ[F] y))
      rw [unitaryFirstProjection_tmul, unitaryFirstProjection_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

section SplitUnitaryScheme

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  {W : AffineAlgebraicGroup F} (U : ClosedSubgroup W.val)
  (m : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearThreePoints E)

private def unitaryBaseChangeMatrix (R : TestAlgebra E) :
    GroupPoints ((groupBaseChange F E).obj U.group) R →* SL₃ (((restrictTestAlgebra F E).obj R) ⊗[F] E) :=
  let R₀ := (restrictTestAlgebra F E).obj R
  (m.hom.app R₀).hom.comp ((((groupPointsFunctor F).map U.inclusion).app R₀).hom.comp
    (baseChangePointGroupEquiv E U.group R).toMonoidHom)

set_option backward.isDefEq.respectTransparency false in
private def unitarySplitPointMap : (groupPointsFunctor E).obj ((groupBaseChange F E).obj U.group) ⟶
    specialLinearThreePoints E where
  app R := GrpCat.ofHom ((Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) R)).comp
    (unitaryBaseChangeMatrix U m R))
  naturality {R S} a := by
    apply GrpCat.ext
    intro x
    let R₀ := (restrictTestAlgebra F E).obj R
    let S₀ := (restrictTestAlgebra F E).obj S
    let f := (restrictTestAlgebra F E).map a
    let φ := (Algebra.TensorProduct.map f.hom (AlgHom.id F E)).toRingHom
    let b := baseChangePoint F E U.group.X R x ≫ U.inclusion.hom.hom
    let z := m.hom.app R₀ b
    have h := baseChangePointsNaturality F E U.group.X a x
    have hz := m.hom.naturality_apply f b
    change m.hom.app S₀ (mapPoints f b) = Matrix.SpecialLinearGroup.map φ z at hz
    change Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) S)
      (m.hom.app S₀ (baseChangePoint F E U.group.X S (mapPoints a x) ≫ U.inclusion.hom.hom)) =
      Matrix.SpecialLinearGroup.map a.hom.toRingHom
        (Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) R) z)
    rw [h]
    change Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) S)
      (m.hom.app S₀ (mapPoints f b)) = _
    rw [hz]
    apply Subtype.ext
    ext i j
    exact DFunLike.congr_fun (unitaryFirstProjection_natural (F := F) a) (z.val i j)

set_option backward.isDefEq.respectTransparency false in
private theorem unitarySplitPointMap_bijective (h : RepresentsHyperbolicUnitary (E := E) U m)
    (R : TestAlgebra E) : Function.Bijective ((unitarySplitPointMap U m).app R) := by
  let R₀ := (restrictTestAlgebra F E).obj R
  letI : Algebra E R₀ := inferInstanceAs (Algebra E R)
  letI : IsScalarTower F E R₀ := IsScalarTower.of_algebraMap_eq' rfl
  let σ := (quadraticTensorInvolution F E R₀).toRingEquiv
  obtain ⟨a, ha, hswap⟩ := unitaryScalarSplitting F E R₀
  obtain ⟨M, hM, f, hf, _⟩ := splitUnitaryPoints F E R₀ a hswap
  have hfst : (RingHom.fst R₀ R₀).comp a.toRingEquiv.toRingHom = unitaryFirstProjection (F := F) R := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
        change (a (x ⊗ₜ[F] y)).1 = unitaryFirstProjection (F := F) R (x ⊗ₜ[F] y)
        rw [ha, unitaryFirstProjection_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  let b := baseChangePointGroupEquiv E U.group R
  let q := unitaryBaseChangeMatrix U m R
  let j (x : GroupPoints ((groupBaseChange F E).obj U.group) R) : M :=
    ⟨q x, (hM _).mpr ((hyperbolicFixedEquation σ _).mpr ((h R₀ _).mpr ⟨b x, rfl⟩))⟩
  have hj : Function.Bijective j := by
    constructor
    · intro x y hxy
      have he : q x = q y := congrArg Subtype.val hxy
      letI := U.isClosedImmersion
      letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
      have hi : Function.Injective (fun p : GroupPoints W.val R₀ => m.hom.app R₀ p) :=
        Function.LeftInverse.injective (GrpCat.inv_hom_apply (m.app R₀))
      apply b.injective
      exact (cancel_mono U.inclusion.hom.hom).mp (hi he)
    · intro g
      obtain ⟨p, hp⟩ := (h R₀ g.val).mp
        ((hyperbolicFixedEquation σ _).mp ((hM _).mp g.property))
      obtain ⟨x, hx⟩ := b.surjective p
      refine ⟨x, Subtype.ext ?_⟩
      change m.hom.app R₀ (b x ≫ U.inclusion.hom.hom) = g.val
      rw [hx]
      exact hp
  have hu : ⇑((unitarySplitPointMap U m).app R) = f ∘ j := by
    funext x
    change Matrix.SpecialLinearGroup.map (unitaryFirstProjection (F := F) R) (q x) = f (j x)
    rw [hf, hfst]
  rw [hu]
  exact f.bijective.comp hj

end SplitUnitaryScheme

set_option backward.isDefEq.respectTransparency false in
theorem hyperbolicUnitaryBaseChange : HyperbolicUnitaryBaseChange.{u} := by
  intro F E _ _ _ _ _ W U m hm A a
  let X := (groupBaseChange F E).obj U.group
  let W₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup U
  have hX : IsAffine X.X.left := (Specs.Unipotent.baseChangedAlgebraicGroup E W₀).property.1
  let P := groupPointsFunctor E
  let q := unitarySplitPointMap U m
  let i : P.obj X ≅ specialLinearThreePoints E := NatIso.ofComponents
    (fun R => MulEquiv.toGrpIso (MulEquiv.ofBijective (q.app R).hom (unitarySplitPointMap_bijective U m hm R)))
    (fun f => q.naturality f)
  let j := i ≪≫ a.symm
  obtain ⟨f, hf⟩ := (groupHomComparison E X A.val hX).2 j.hom
  obtain ⟨g, hg⟩ := (groupHomComparison E A.val X A.property.1).2 j.inv
  change P.map f = j.hom at hf
  change P.map g = j.inv at hg
  have hi : f ≫ g = 𝟙 X := by
    apply (groupHomComparison E X X hX).1
    change P.map (f ≫ g) = P.map (𝟙 X)
    rw [Functor.map_comp, hf, hg, Iso.hom_inv_id]
    exact (P.map_id X).symm
  have hj : g ≫ f = 𝟙 A.val := by
    apply (groupHomComparison E A.val A.val A.property.1).1
    change P.map (g ≫ f) = P.map (𝟙 A.val)
    rw [Functor.map_comp, hg, hf, Iso.inv_hom_id]
    exact (P.map_id A.val).symm
  refine ⟨⟨f, g, hi, hj⟩, fun R x => ?_⟩
  change a.hom.app R ((P.map f).app R x) = q.app R x
  rw [hf]
  exact GrpCat.hom_inv_apply (a.app R) (q.app R x)

end UnitaryScheme

section PinnedComparison

open Specs.Pinning (AttachedDatum BasedIso PinnedGroup PinnedIso)
open Specs.RootGroups (AdditiveLine)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open private rootEquiv coroot_transport from LinearAlgebraicGroups.Classification.Pinning
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence

theorem pinnedCartanComparison : PinnedCartanComparison.{u} := by
  intro k _ A P Q D E hD hE e h
  obtain ⟨c, hc, _⟩ :=
    (LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes.cartanDeterminesBasedDatum
      D.toBased E.toBased hD hE e).mp h
  obtain ⟨f, hf⟩ := pinnedLift P Q D E c
  refine ⟨f, fun i => ?_⟩
  letI := D.comm
  letI := E.comm
  have hi : (inducedBasedIso f D E).val.indexEquiv i.val = (e i).val := hf ▸ hc i
  change rootEquiv f i.val = (e i).val at hi
  refine ⟨congrArg Subtype.val hi, ?_⟩
  have hy := coroot_transport f D E i.val
  rw [hi] at hy
  change Additive.ofMul (Additive.toMul (E.datum.rootDatum.coroot (e i).val) ≫ f.torus.inv) =
    D.datum.rootDatum.coroot i.val at hy
  apply (cancel_mono f.torus.inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (congrArg Additive.toMul hy).symm

end PinnedComparison


section EquivariantComparison

open Specs.AdjointCocharacters (coordinateHopfMap coordinateHopfIso)
local notation "coordinateAlgebra" => Specs.AdjointCocharacters.coordinateHopf
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.Descent
open private descend_standard_iso extendedHom_injective extendedHom_comp baseHom_equivariant
  from LinearAlgebraicGroups.Descent.Forms
open private coordinateHopfMap_surjective coordinateHopfMap_comp
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private coordinatePresentationMap from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private tensorMap_surjective from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem coordinateHopfMap_injective_on_hom {F : Type u} [Field F]
    (G H : AffineAlgebraicGroup F) :
    Function.Injective (fun f : G.val ⟶ H.val => coordinateHopfMap (G := G) (H := H) f) := by
  intro f g h
  have hh := congrArg specGroupMap h
  rw [coordinatePresentationMap, coordinatePresentationMap] at hh
  exact (cancel_epi (coordinateHopfIso G).hom).mp
    ((cancel_mono (coordinateHopfIso H).inv).mp (by simpa only [Category.assoc] using hh))

private def groupIsoOfCoordinateIso {F : Type u} [Field F]
    (G H : AffineAlgebraicGroup F) (i : coordinateAlgebra H ≅ coordinateAlgebra G) :
    G.val ≅ H.val :=
  (coordinateHopfIso G).symm ≪≫ (hopfSpec (CommRingCat.of F)).mapIso i.op ≪≫
    coordinateHopfIso H

private theorem groupIsoOfCoordinateIso_hom {F : Type u} [Field F]
    (G H : AffineAlgebraicGroup F) (i : coordinateAlgebra H ≅ coordinateAlgebra G) :
    coordinateHopfMap (G := G) (H := H) (groupIsoOfCoordinateIso G H i).hom = i.hom := by
  apply Opposite.op_injective
  apply (hopfSpec.fullyFaithful (R := CommRingCat.of F)).map_injective
  change specGroupMap (coordinateHopfMap (G := G) (H := H) (groupIsoOfCoordinateIso G H i).hom) =
    specGroupMap i.hom
  rw [coordinatePresentationMap]
  simp [groupIsoOfCoordinateIso, specGroupMap, Category.assoc]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem markedHopfComparison : MarkedHopfComparison.{u} := by
  classical
  intro F K _ _ _ _ I G H S T e m he hm
  let A (i : I) := closedSubgroupAlgebraicGroup (S i)
  let B (i : I) := closedSubgroupAlgebraicGroup (T i)
  let s (i : I) := coordinateHopfMap (G := A i) (H := G) (S i).inclusion
  let t (i : I) := coordinateHopfMap (G := B i) (H := H) (T i).inclusion
  have hsquare (i : I) :
      e.hom ≫ extendedHopfMap K (s i) = extendedHopfMap K (t i) ≫ (m i).hom := hm i
  have hmi (i : I) : IsCoefficientEquivariant (m i) := by
    let q := extendedHopfMap K (t i)
    have ht : Function.Surjective (t i).hom :=
      coordinateHopfMap_surjective (G := B i) (H := H) (T i).inclusion (T i).isClosedImmersion
    have hq : Function.Surjective q.hom := tensorMap_surjective (K := K) (t i).hom.toAlgHom ht
    intro σ y
    obtain ⟨x, rfl⟩ := hq y
    have hh (x : extendedHopf K (coordinateAlgebra H)) :
        (m i).hom.hom (q.hom x) = (extendedHopfMap K (s i)).hom (e.hom.hom x) :=
      ConcreteCategory.congr_hom (hsquare i).symm x
    change (m i).hom.hom ((SemilinearAction.scalarExtension (K := K)
      (coordinateAlgebra (B i))).act σ (q.hom x)) = _
    have hq' :
        q.hom ((SemilinearAction.scalarExtension (K := K) (coordinateAlgebra H)).act σ x) =
          (SemilinearAction.scalarExtension (K := K) (coordinateAlgebra (B i))).act σ (q.hom x) :=
      baseHom_equivariant (K := K) (t i) σ x
    have hs' (y : extendedHopf K (coordinateAlgebra G)) :
        (extendedHopfMap K (s i)).hom
            ((SemilinearAction.scalarExtension (K := K) (coordinateAlgebra G)).act σ y) =
          (SemilinearAction.scalarExtension (K := K) (coordinateAlgebra (A i))).act σ
            ((extendedHopfMap K (s i)).hom y) :=
      baseHom_equivariant (K := K) (s i) σ y
    change (m i).hom.hom ((SemilinearAction.scalarExtension (K := K)
      (coordinateAlgebra (B i))).act σ (q.hom x)) =
      (SemilinearAction.scalarExtension (K := K) (coordinateAlgebra (A i))).act σ
        ((m i).hom.hom (q.hom x))
    rw [← hq', hh, he, hs', hh]
  obtain ⟨f₀, hf₀⟩ := descend_standard_iso e he
  have hex (i : I) : ∃ g : coordinateAlgebra (B i) ≅ coordinateAlgebra (A i),
      extendedHopfMap K g.hom = (m i).hom := descend_standard_iso (m i) (hmi i)
  choose g₀ hg₀ using hex
  let f := groupIsoOfCoordinateIso G H f₀
  let g (i : I) := groupIsoOfCoordinateIso (A i) (B i) (g₀ i)
  have hf := groupIsoOfCoordinateIso_hom G H f₀
  have hg (i : I) := groupIsoOfCoordinateIso_hom (A i) (B i) (g₀ i)
  refine ⟨f, g, hf ▸ hf₀, fun i => ⟨?_, (hg i) ▸ hg₀ i⟩⟩
  apply coordinateHopfMap_injective_on_hom (A i) H
  change coordinateHopfMap (G := A i) (H := H) ((S i).inclusion ≫ f.hom) =
    coordinateHopfMap (G := A i) (H := H) ((g i).hom ≫ (T i).inclusion)
  rw [coordinateHopfMap_comp (G := A i) (H := G) (J := H),
    coordinateHopfMap_comp (G := A i) (H := B i) (J := H)]
  change coordinateHopfMap (G := G) (H := H) f.hom ≫ s i =
    t i ≫ coordinateHopfMap (G := A i) (H := B i) (g i).hom
  rw [show coordinateHopfMap (G := G) (H := H) f.hom = f₀.hom from hf,
    show coordinateHopfMap (G := A i) (H := B i) (g i).hom = (g₀ i).hom from hg i]
  apply extendedHom_injective (K := K)
  rw [extendedHom_comp, extendedHom_comp, hf₀, hg₀]
  exact hsquare i

end EquivariantComparison


section PermutedMatrices

open Matrix
open private fixedFieldTensor fixedFieldTensor_injective fixedFieldTensor_range fixedFieldTensor_natural
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

private theorem mark_map {R S : Type u} [CommRing R] [CommRing S]
    {n : ℕ} (f : R →+* S) (m : MatrixMark) (g : SpecialLinearGroup (Fin n) R) :
    m.Holds g → m.Holds (SpecialLinearGroup.map f g) := by
  have hz (i j : Fin n) (h : g.val i j = 0) : (SpecialLinearGroup.map f g).val i j = 0 :=
    (congrArg f h).trans (map_zero f)
  have ho (i : Fin n) (h : g.val i i = 1) : (SpecialLinearGroup.map f g).val i i = 1 :=
    (congrArg f h).trans (map_one f)
  cases m <;> simp only [MatrixMark.Holds] <;>
    first | exact fun h i j hij => hz i j (h hij)
          | exact fun h i j hij => hz i j (h i j hij)
          | exact fun h => ⟨fun i j hij => hz i j (h.1 hij), fun i => ho i (h.2 i)⟩

private theorem mark_map_iff {R S : Type u} [CommRing R] [CommRing S]
    {n : ℕ} (f : R →+* S) (hf : Function.Injective f)
    (m : MatrixMark) (g : SpecialLinearGroup (Fin n) R) :
    m.Holds (SpecialLinearGroup.map f g) ↔ m.Holds g := by
  refine ⟨?_, mark_map f m g⟩
  have hz (i j : Fin n) (h : (SpecialLinearGroup.map f g).val i j = 0) : g.val i j = 0 :=
    hf (h.trans (map_zero f).symm)
  have ho (i : Fin n) (h : (SpecialLinearGroup.map f g).val i i = 1) : g.val i i = 1 :=
    hf (h.trans (map_one f).symm)
  cases m <;> simp only [MatrixMark.Holds] <;>
    first | exact fun h i j hij => hz i j (h hij)
          | exact fun h i j hij => hz i j (h i j hij)
          | exact fun h => ⟨fun i j hij => hz i j (h.1 hij), fun i => ho i (h.2 i)⟩

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem matrix_map_injective {A B : Type u} [CommRing A] [CommRing B]
    {n : ℕ} (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (SpecialLinearGroup.map (n := Fin n) f) := by
  intro a b h
  apply Subtype.ext
  ext j l
  exact hf (congrArg (fun g : SpecialLinearGroup (Fin n) B => g.val j l) h)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem orbitMatrixLift (R : TestAlgebra F) (J : Subgroup Gal(K/F)) (n : ℕ)
    (g : SpecialLinearGroup (Fin n) (K ⊗[F] R))
    (hg : ∀ σ ∈ J, SpecialLinearGroup.map (coefficientRingMap R σ) g = g) :
    ∃ a : SpecialLinearGroup (Fin n) (R ⊗[F] IntermediateField.fixedField J),
      SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom a = g := by
  classical
  let f := orbitScalarEmbedding R J
  have hentry (j l : Fin n) : ∃ x, f x = g.val j l := by
    change g.val j l ∈ Set.range (fixedFieldTensor R J)
    rw [fixedFieldTensor_range]
    intro σ hσ
    exact congrArg (fun a : SpecialLinearGroup (Fin n) (K ⊗[F] R) => a.val j l) (hg σ hσ)
  choose a₀ ha using hentry
  let a : Matrix (Fin n) (Fin n) (R ⊗[F] IntermediateField.fixedField J) := a₀
  have hmap : f.toRingHom.mapMatrix a = g.val := Matrix.ext ha
  have hdet : a.det = 1 := by
    apply fixedFieldTensor_injective R J
    change f a.det = f 1
    rw [show f 1 = 1 from f.map_one]
    exact (f.toRingHom.map_det a).trans (congrArg Matrix.det hmap |>.trans g.property)
  exact ⟨⟨a, hdet⟩, Subtype.ext hmap⟩

private theorem coefficientMatrix_mul {n : ℕ} (R : TestAlgebra F)
    (σ τ : Gal(K/F)) (a : SpecialLinearGroup (Fin n) (K ⊗[F] R)) :
    SpecialLinearGroup.map (coefficientRingMap R (σ * τ)) a =
      SpecialLinearGroup.map (coefficientRingMap R σ)
        (SpecialLinearGroup.map (coefficientRingMap R τ) a) := by
  apply Subtype.ext
  ext j l
  change coefficientRingMap R (σ * τ) (a.val j l) =
    coefficientRingMap R σ (coefficientRingMap R τ (a.val j l))
  generalize a.val j l = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem coefficientMatrix_one {n : ℕ} (R : TestAlgebra F)
    (a : SpecialLinearGroup (Fin n) (K ⊗[F] R)) :
    SpecialLinearGroup.map (coefficientRingMap R (1 : Gal(K/F))) a = a := by
  apply Subtype.ext
  ext j l
  change coefficientRingMap R (1 : Gal(K/F)) (a.val j l) = a.val j l
  generalize a.val j l = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem permutedMatrixPoints : PermutedMatrixPoints.{u} := by
  classical
  intro F K _ _ _ I ρ i htrans n R
  letI := MulAction.compHom I ρ
  let J := MulAction.stabilizer Gal(K/F) i
  let E := orbitField ρ i
  let f : SpecialLinearGroup (Fin n) (R ⊗[F] E) →* _ :=
    SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom
  have hf : Function.Injective f :=
    matrix_map_injective _ (fixedFieldTensor_injective R J)
  choose σ hσ using htrans
  let t (s : Gal(K/F)) : SpecialLinearGroup (Fin n) (K ⊗[F] R) →* _ :=
    SpecialLinearGroup.map (coefficientRingMap R s)
  let v (a : SpecialLinearGroup (Fin n) (R ⊗[F] E)) (j : I) := t (σ j) (f a)
  have hfix (a : SpecialLinearGroup (Fin n) (R ⊗[F] E)) (s : Gal(K/F)) (hs : s ∈ J) :
      t s (f a) = f a := by
    apply Subtype.ext
    ext l m
    have h := Set.mem_range_self (f := orbitScalarEmbedding R J) (a.val l m)
    change _ ∈ Set.range (fixedFieldTensor R J) at h
    rw [fixedFieldTensor_range] at h
    exact h s hs
  have hv (a : SpecialLinearGroup (Fin n) (R ⊗[F] E)) (s : Gal(K/F)) (j : I)
      (hs : ρ s i = j) : v a j = t s (f a) := by
    let q := s⁻¹ * σ j
    have hq : q ∈ J := by
      change ρ (s⁻¹ * σ j) i = i
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, hσ j, ← hs]
      exact (ρ s).symm_apply_apply i
    have hsq : s * q = σ j := by simp [q]
    change t (σ j) (f a) = _
    rw [← hsq, show t (s * q) (f a) = t s (t q (f a)) from coefficientMatrix_mul R s q _, hfix a q hq]
  have hv_eq (a : SpecialLinearGroup (Fin n) (R ⊗[F] E)) :
      v a ∈ permutedMatrices ρ R n := by
    intro s j
    rw [hv a (s * σ j) (ρ s j) (by rw [map_mul, Equiv.Perm.mul_apply, hσ j])]
    exact coefficientMatrix_mul R s (σ j) _
  let p : SpecialLinearGroup (Fin n) (R ⊗[F] E) →* permutedMatrices ρ R n :=
    { toFun a := ⟨v a, hv_eq a⟩
      map_one' := by
        apply Subtype.ext
        funext j
        exact (congrArg (t (σ j)) (map_one f)).trans (map_one _)
      map_mul' a b := by
        apply Subtype.ext
        funext j
        exact (congrArg (t (σ j)) (map_mul f _ _)).trans (map_mul _ _ _) }
  have hpi (a : SpecialLinearGroup (Fin n) (R ⊗[F] E)) : (p a).val i = f a :=
    (hv a 1 i (by rw [map_one]; rfl)).trans (coefficientMatrix_one R _)
  have hp : Function.Bijective p := by
    constructor
    · intro a b h
      apply hf
      rw [← hpi a, ← hpi b, h]
    · intro x
      obtain ⟨a, ha⟩ := orbitMatrixLift R J n (x.val i) (fun s hs => by
        have h := x.property s i
        rw [show ρ s i = i from hs] at h
        exact h.symm)
      refine ⟨a, Subtype.ext (funext fun j => ?_)⟩
      change t (σ j) (f a) = x.val j
      change f a = x.val i at ha
      exact (congrArg (t (σ j)) ha).trans
        ((x.property (σ j) i).symm.trans (congrArg x.val (hσ j)))
  let e := (MulEquiv.ofBijective p hp).symm
  have he (x : permutedMatrices ρ R n) : f (e x) = x.val i := by
    rw [← hpi (e x)]
    exact congrArg (fun y : permutedMatrices ρ R n => y.val i) (e.symm_apply_apply x)
  refine ⟨e, he, fun m x => ⟨fun h j => ?_, fun h => ?_⟩⟩
  · rw [← hσ j, x.property, ← he]
    exact mark_map _ m _ (mark_map _ m _ h)
  · apply (mark_map_iff _ (fixedFieldTensor_injective R J) m (e x)).mp
    change m.Holds (f (e x))
    rw [he]
    exact h i

end PermutedMatrices

section UnitaryMarks

open Matrix

private theorem sl_inv_upper {n : ℕ} {R : Type u} [CommRing R]
    (g : SpecialLinearGroup (Fin n) R) (h : g.val.IsUpperTriangular) :
    (g⁻¹).val.IsUpperTriangular := by
  have hd : IsUnit g.val.det := by rw [g.property]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet _ hd
  have hI : g.val⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular h
  have hh : g.val⁻¹ = (g⁻¹).val := by
    rw [SpecialLinearGroup.coe_inv, Matrix.nonsing_inv_apply _ hd]
    have hu : hd.unit = 1 := Units.ext (hd.unit_spec.trans g.property)
    rw [hu, inv_one, Units.val_one, one_smul]
  exact hh ▸ hI

private theorem sl_inv_lower {n : ℕ} {R : Type u} [CommRing R]
    (g : SpecialLinearGroup (Fin n) R) (h : g.val.IsLowerTriangular) :
    (g⁻¹).val.IsLowerTriangular := by
  let a : SpecialLinearGroup (Fin n) R :=
    ⟨g.val.transpose, (Matrix.det_transpose g.val).trans g.property⟩
  have ha : (a⁻¹).val = (g⁻¹).val.transpose := by
    rw [SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_inv]
    exact (Matrix.adjugate_transpose g.val).symm
  intro i j hij
  have he : (a⁻¹).val j i = (g⁻¹).val i j :=
    congrArg (fun m : Matrix (Fin n) (Fin n) R => m j i) ha
  exact he.symm.trans (sl_inv_upper a h.transpose (i := j) (j := i) hij)

private theorem sl_inv_diag_of_upper {n : ℕ} {R : Type u} [CommRing R]
    (g : SpecialLinearGroup (Fin n) R) (h : g.val.IsUpperTriangular)
    (hdiag : ∀ i, g.val i i = 1) (i : Fin n) : (g⁻¹).val i i = 1 := by
  have hi := sl_inv_upper g h
  have hd := congrArg (fun a : SpecialLinearGroup (Fin n) R => a.val i i) (mul_inv_cancel g)
  change (g.val * (g⁻¹).val) i i = (1 : Matrix (Fin n) (Fin n) R) i i at hd
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hdiag, one_mul, Matrix.one_apply_eq] at hd
  · exact hd
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [h hj, zero_mul]
    · rw [hi hj, mul_zero]
  · simp

private theorem sl_inv_diag_of_lower {n : ℕ} {R : Type u} [CommRing R]
    (g : SpecialLinearGroup (Fin n) R) (h : g.val.IsLowerTriangular)
    (hdiag : ∀ i, g.val i i = 1) (i : Fin n) : (g⁻¹).val i i = 1 := by
  have hi := sl_inv_lower g h
  have hd := congrArg (fun a : SpecialLinearGroup (Fin n) R => a.val i i) (mul_inv_cancel g)
  change (g.val * (g⁻¹).val) i i = (1 : Matrix (Fin n) (Fin n) R) i i at hd
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hdiag, one_mul, Matrix.one_apply_eq] at hd
  · exact hd
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hi hj, mul_zero]
    · rw [h hj, zero_mul]
  · simp

private theorem hyperbolicDual_mark {R : Type u} [CommRing R] (m : MatrixMark) (g : SL₃ R) :
    m.Holds g → m.Holds (hyperbolicDual g) := by
  have hu (h : g.val.IsUpperTriangular) : (hyperbolicDual g).val.IsUpperTriangular := by
    intro i j hij
    change (g⁻¹).val j.rev i.rev = 0
    exact sl_inv_upper g h (Fin.rev_lt_rev.mpr hij)
  have hl (h : g.val.IsLowerTriangular) : (hyperbolicDual g).val.IsLowerTriangular := by
    intro i j hij
    change (g⁻¹).val j.rev i.rev = 0
    exact sl_inv_lower g h (Fin.rev_lt_rev.mpr hij)
  cases m
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hl (fun _ _ hlt => h _ _ hlt.ne.symm) hij
    · exact hu (fun _ _ hlt => h _ _ hlt.ne.symm) hij
  · exact hu
  · exact hl
  · exact fun h => ⟨hu h.1, fun i => sl_inv_diag_of_upper g h.1 h.2 i.rev⟩
  · exact fun h => ⟨hl h.1, fun i => sl_inv_diag_of_lower g h.1 h.2 i.rev⟩

theorem unitaryMarkedPoints : UnitaryMarkedPoints.{u} := by
  intro F E _ _ _ _ _ R _ _ _ _
  obtain ⟨e, he, hswap⟩ := unitaryScalarSplitting F E R
  obtain ⟨U, hU, p, hp, hp'⟩ := splitUnitaryPoints F E R e hswap
  refine ⟨e, U, p, he, fun g => (hU g).trans (hyperbolicFixedEquation _ g), hp, fun m g => ?_⟩
  constructor
  · intro h
    have hr := hyperbolicDual_mark m (p g) h
    rw [hp g] at h
    change m.Holds (hyperbolicInverseTranspose (p g)) at hr
    rw [hp' g] at hr
    have hex : ∀ j l (a : R ⊗[F] E), (e a).1 = 0 → (e a).2 = 0 → a = 0 :=
      fun (_ _ : Fin 3) a h₁ h₂ => e.injective (Prod.ext h₁ h₂ |>.trans (map_zero e).symm)
    have hex₁ (a : R ⊗[F] E) : (e a).1 = 1 → (e a).2 = 1 → a = 1 :=
      fun h₁ h₂ => e.injective (Prod.ext h₁ h₂ |>.trans (map_one e).symm)
    cases m <;> simp only [MatrixMark.Holds] at h hr ⊢ <;>
      first
      | exact fun j l hjl => hex j l _ (h j l hjl) (hr j l hjl)
      | exact fun j l hjl => hex j l _ (h hjl) (hr hjl)
      | exact ⟨fun j l hjl => hex j l _ (h.1 hjl) (hr.1 hjl), fun j => hex₁ _ (h.2 j) (hr.2 j)⟩
  · intro h
    rw [hp]
    exact mark_map _ _ _ h

end UnitaryMarks

section SplitMatrixModels

open Specs.Pinning (AttachedDatum PinnedGroup SimpleRoot RootCoordinate)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.SpecialLinearDatum
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private additiveLineIso additiveLinePointsIso additiveLineGroup rootPoint_eq
  from LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent

private theorem additiveLineIso_rootPoint {k : Type u} [Field k] (A B : AdditiveLine k)
    (R : TestAlgebra k) (a : R) :
    rootPoint (additiveLineIso A B).hom R a = additivePoints B R a := by
  letI := (additiveLineGroup A).property.1
  letI := (additiveLineGroup B).property.1
  let e := (additiveLinePointsIso A).symm ≪≫ additiveLinePointsIso B
  have he : (groupPointsFunctor k).map (additiveLineIso A B).hom = e.hom :=
    (groupHomEquiv A.group B.group inferInstance).apply_symm_apply _
  rw [rootPoint_eq]
  change ((groupPointsFunctor k).map (additiveLineIso A B).hom).app R
    (additivePoints A R a) = _
  rw [he]
  exact congrArg (fun x => (additiveLinePointsIso B).hom.app R x)
    (GrpCat.inv_hom_apply ((additiveLinePointsIso A).app R) (Multiplicative.ofAdd a))

private def matrixSimpleVertices {k : Type u} [Field k] {r : ℕ}
    {S : AffineAlgebraicGroup k} {s : SpecialMatrixPoints S (r + 1)}
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    {B : UpperTriangularBorel T L M} {D : AttachedDatum B.pair} (hD : IsMatrixBasedDatum B D) :
    letI := D.comm
    Fin r ≃ D.base.support := by
  letI := D.comm
  let a (i : Fin r) : D.base.support :=
    ⟨M.indices (adjacentRootIndex i), (hD.2 _).mpr ⟨i, rfl, rfl⟩⟩
  refine Equiv.ofBijective a ⟨?_, ?_⟩
  · intro i j h
    have he : M.indices (adjacentRootIndex i) = M.indices (adjacentRootIndex j) :=
      congrArg (fun x : D.base.support => x.val) h
    have he := M.indices.injective he
    exact Fin.ext (congrArg (fun p : RootIndices (r + 1) => p.val.1.val) he)
  · intro i
    obtain ⟨p, hp⟩ := M.indices.surjective i.val
    have hi : M.indices p ∈ D.base.support := hp.symm ▸ i.property
    obtain ⟨j, hj, hj'⟩ := (hD.2 p).mp hi
    refine ⟨j, Subtype.ext ?_⟩
    have hh : adjacentRootIndex j = p := Subtype.ext (Prod.ext hj.symm hj'.symm)
    exact (congrArg M.indices hh).trans hp

private theorem matrixIntegralCartan {k : Type u} [Field k] {r : ℕ}
    {S : AffineAlgebraicGroup k} {s : SpecialMatrixPoints S (r + 1)}
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    {B : UpperTriangularBorel T L M} {D : AttachedDatum B.pair} (hD : IsMatrixBasedDatum B D)
    (i j : Fin r) :
    letI := D.comm
    RootData.integralCartan D.datum.rootDatum D.base
      (matrixSimpleVertices hD i) (matrixSimpleVertices hD j) =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  letI := D.comm
  change D.datum.rootDatum.pairing (M.indices (adjacentRootIndex j)) (M.indices (adjacentRootIndex i)) = _
  rw [← RootPairing.root_coroot_eq_pairing, D.datum.root_eq]
  change D.datum.rootDatum.toLinearMap (Additive.ofMul (M.indices (adjacentRootIndex j)).val)
    (Additive.ofMul (Additive.toMul (D.datum.rootDatum.coroot (M.indices (adjacentRootIndex i))))) = _
  rw [D.datum.pairing_eq, L.pairing_eq, M.character_eq]
  change dotPairing (r + 1) (root (r + 1) j.castSucc j.succ)
    (L.cocharacters (D.datum.rootDatum.coroot (M.indices (adjacentRootIndex i)))) = _
  rw [hD.1 (adjacentRootIndex i)]
  change dotPairing (r + 1) (root (r + 1) j.castSucc j.succ) (simpleCoroot r i) = _
  exact (RootData.SpecialLinearDatum.simpleCartanPairings r j i).trans (by
    simp only [eq_comm (a := j) (b := i), or_comm (a := j.val + 1 = i.val)])

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem signedMatrixPinning : SignedMatrixPinning.{u} := by
  classical
  intro k _ A r S s
  obtain ⟨T, L, M, B, D, hD, hpin, hsc, _, hcor⟩ := attachedMatrixCoroots r S s
  letI := D.comm
  obtain ⟨A₀, U, x, hx, p, hp⟩ := hpin
  let j := matrixSimpleVertices hD
  let aIso := additiveLineIso A A₀
  have hpre (f : A₀.group ⟶ S.val) (R : TestAlgebra k) (b : R) :
      rootPoint (aIso.hom ≫ f) R b = rootPoint f R b := by
    rw [rootPoint_comp, show rootPoint aIso.hom R b = additivePoints A₀ R b from
      additiveLineIso_rootPoint A A₀ R b, rootPoint_eq]
  let q₀ (α : SimpleRoot B.pair) : RootCoordinate A T.subgroup (U α.val).val α.val.val :=
    ⟨aIso ≪≫ (p α).val, by
      intro R t a
      change _ * rootPoint ((aIso.hom ≫ (p α).val.hom) ≫ (U α.val).val.inclusion) R a * _ =
        rootPoint ((aIso.hom ≫ (p α).val.hom) ≫ (U α.val).val.inclusion) R _
      rw [Category.assoc, hpre, hpre]
      exact (p α).property R t a⟩
  let rIndex (α : SimpleRoot B.pair) : Fin r :=
    j.symm ⟨α.val, (D.simple_iff _).mpr α.property⟩
  let z (α : SimpleRoot B.pair) : kˣ := if (rIndex α).val = 1 then -1 else 1
  obtain ⟨qEquiv, _, hq⟩ := Classification.Pinning.pinningVectors A B.pair U
  obtain ⟨q, hq, _⟩ := hq q₀ z
  refine ⟨T, L, M, B, D, U, q, j, hD, hsc, fun _ => rfl, matrixIntegralCartan hD, ?_, hcor⟩
  intro i R b
  let α : SimpleRoot B.pair := ⟨(j i).val, (D.simple_iff _).mp (j i).property⟩
  have hz : (algebraMap k R (z α : k)) * b = signedParameter i b := by
    have he : rIndex α = i := j.symm_apply_apply i
    simp only [z, he, signedParameter]
    split_ifs <;> simp
  have hw := hq.1 α R b
  rw [hz] at hw
  change (s.hom.app R (rootPoint ((q α).val.hom ≫ (U α.val).val.inclusion) R b)).val = _
  rw [hw]
  change (s.hom.app R (rootPoint ((aIso.hom ≫ (p α).val.hom) ≫ (U α.val).val.inclusion) R
    (signedParameter i b))).val = _
  rw [Category.assoc, hpre, hp α]
  exact hx (adjacentRootIndex i) R (signedParameter i b)

end SplitMatrixModels

section PinnedFixedPoints

open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.RootGroups (AdditiveLine)
open Specs.AutomorphismSequence (forgetPinning)
open Specs.AdjointCocharacters (coordinateHopfMap)
open LinearAlgebraicGroups.Descent (SemilinearAction)
local notation "coordinateAlgebra" => Specs.AdjointCocharacters.coordinateHopf
open private extendCoordinatePoint extendCoordinatePoint_injective
  extendCoordinatePoint_equivariant exists_extendCoordinatePoint
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem pinnedFixedPoints : PinnedFixedPoints.{u} := by
  intro F K _ _ _ _ A P D l G B T d R
  let C := coordinateAlgebra P.pair.G
  let H := coordinateAlgebra G
  let E := d.groupIso
  let extP (f : H →ₐ[F] R) := extendCoordinatePoint (K := K) R f
  let e (f : H →ₐ[F] R) := (extP f).comp E.hom.hom.toAlgHom
  change Function.Injective e ∧ _
  have hE₁ (x : extendedHopf K C) : E.inv.hom (E.hom.hom x) = x :=
    ConcreteCategory.congr_hom E.hom_inv_id x
  have hE₂ (x : extendedHopf K H) : E.hom.hom (E.inv.hom x) = x :=
    ConcreteCategory.congr_hom E.inv_hom_id x
  constructor
  · intro f g h
    apply extendCoordinatePoint_injective (K := K) R
    apply AlgHom.ext
    intro x
    have hx : extP f (E.hom.hom (E.inv.hom x)) = extP g (E.hom.hom (E.inv.hom x)) :=
      DFunLike.congr_fun h (E.inv.hom x)
    rwa [hE₂] at hx
  · intro p
    constructor
    · rintro ⟨f, rfl⟩ σ x
      let a := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv
      let z := (extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) a)).hom
        ((SemilinearAction.scalarExtension (K := K) C).act σ x)
      change extP f (E.hom.hom z) = (SemilinearAction.scalarExtension (K := K) R).act σ
        (extP f (E.hom.hom x))
      rw [← d.twistedAction σ x]
      exact extendCoordinatePoint_equivariant R f σ (E.hom.hom x)
    · intro hp
      let q := p.comp E.inv.hom.toAlgHom
      have hq (σ : Gal(K/F)) (y : extendedHopf K H) :
          q ((SemilinearAction.scalarExtension (K := K) H).act σ y) =
            (SemilinearAction.scalarExtension (K := K) R).act σ (q y) := by
        obtain ⟨x, rfl⟩ : ∃ x, E.hom.hom x = y := ⟨E.inv.hom y, hE₂ y⟩
        rw [d.twistedAction σ x]
        let a := (Functor.mapAut P (forgetPinning (A := A)) (l (d.outer σ))).asIso.inv
        let z := (extendedHopfMap K (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) a)).hom
          ((SemilinearAction.scalarExtension (K := K) C).act σ x)
        change p (E.inv.hom (E.hom.hom z)) =
          (SemilinearAction.scalarExtension (K := K) R).act σ (p (E.inv.hom (E.hom.hom x)))
        rw [hE₁ z, hE₁ x]
        exact hp σ x
      obtain ⟨f, hf⟩ := exists_extendCoordinatePoint R q hq
      refine ⟨f, AlgHom.ext fun x => ?_⟩
      change extP f (E.hom.hom x) = p x
      change extP f = q at hf
      rw [hf]
      exact congrArg p (hE₁ x)

end PinnedFixedPoints

section SplitSpecialLinearComparison

open Specs.Pinning (AttachedDatum PinnedGroup PinnedIso SimpleRoot pinGraph)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.GeometricRadicals (IsSemisimple)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.SpecialLinearDatum
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open LinearAlgebraicGroups.Classification.SimplyConnectedLattice (latticeCriterion)
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

private theorem pinnedRootMap {k : Type u} [Field k] {A : AdditiveLine k}
    {P Q : PinnedGroup A} (f : PinnedIso P Q)
    (a : SimpleRoot P.pair) (b : SimpleRoot Q.pair)
    (h : Specs.Pinning.transportCharacter f.torus a.val.val = b.val.val) :
    ((P.pin a).val.hom ≫ (P.roots a.val).val.inclusion) ≫ f.group.hom =
      (Q.pin b).val.hom ≫ (Q.roots b.val).val.inclusion := by
  let x := (a.val.val, (P.pin a).val.hom ≫ (P.roots a.val).val.inclusion)
  have hm : (Specs.Pinning.transportCharacter f.torus x.1, x.2 ≫ f.group.hom) ∈ pinGraph Q := by
    rw [← f.pin_comm]
    exact ⟨x, ⟨a, rfl⟩, rfl⟩
  obtain ⟨b', hb'⟩ := hm
  have hb : b' = b := Subtype.ext (Subtype.ext ((congrArg Prod.fst hb').trans h))
  subst b'
  exact (congrArg Prod.snd hb').symm

private theorem mappedTorusPoint {k : Type u} [Field k]
    {G H : GroupScheme k} (c : Specs.CharacterDescent.Cocharacter G) (f : G ⟶ H)
    (R : TestAlgebra k) (v : Rˣ) :
    cocharacterPoint c R v ≫ f.hom.hom = cocharacterPoint (c ≫ f) R v := by
  change ((groupPointsFunctor k).map f).app R (((groupPointsFunctor k).map c).app R _) =
    ((groupPointsFunctor k).map (c ≫ f)).app R _
  rw [Functor.map_comp]
  rfl

private theorem mapSubgroupSections {k : Type u} [Field k] {G H : GroupScheme k}
    {S : ClosedSubgroup G} {T : ClosedSubgroup H} (f : G ≅ H) (g : S.group ≅ T.group)
    (h : S.inclusion ≫ f.hom = g.hom ≫ T.inclusion)
    (R : TestAlgebra k) (x : GroupPoints G R) :
    x ∈ SubgroupSections S ((testSpec k).obj (Opposite.op R)) ↔
      x ≫ f.hom.hom.hom ∈ SubgroupSections T ((testSpec k).obj (Opposite.op R)) := by
  have hh := congrArg (fun (a : S.group ⟶ H) => a.hom.hom) h
  simp only [Grp.comp_hom_hom] at hh
  change (∃ w, w ≫ S.inclusion.hom.hom = x) ↔
    (∃ w, w ≫ T.inclusion.hom.hom = x ≫ f.hom.hom.hom)
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w ≫ g.hom.hom.hom, by simp only [Category.assoc, hh]⟩
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ g.inv.hom.hom, ?_⟩
    let F := Grp.forget (SchemeOver k)
    letI : IsIso (F.map f.hom) := F.map_isIso _
    apply (cancel_mono (F.map f.hom)).mp
    change (w ≫ g.inv.hom.hom ≫ S.inclusion.hom.hom) ≫ f.hom.hom.hom = _
    have hi : g.inv.hom.hom ≫ g.hom.hom.hom = 𝟙 _ := by
      change F.map g.inv ≫ F.map g.hom = 𝟙 (F.obj T.group)
      rw [← F.map_comp, g.inv_hom_id, F.map_id]
    simp only [Category.assoc, hh]
    rw [← Category.assoc g.inv.hom.hom, hi, Category.id_comp, hw]
    rfl

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
theorem splitPinnedSpecialLinearComparison : SplitPinnedSpecialLinearComparison.{u} := by
  classical
  intro k _ A P D hs hsc r S s j hc
  letI := D.comm
  obtain ⟨T, L, M, B, E, U, q, e, _, hSsc, _, hCartan, hpin, hcor⟩ :=
    signedMatrixPinning A r S s
  letI := E.comm
  let Q : PinnedGroup A := ⟨B.pair, U, q⟩
  have hD := (latticeCriterion P.pair.G hs P.pair.T P.pair.split P.pair.maximal D.datum).mp hsc
  have hSS := RootData.SpecialLinearDatum.semisimple k r S s
  have hE := (latticeCriterion S hSS T.subgroup T.split B.maximal E.datum).mp hSsc
  let j' := j.symm.trans e
  have hj (i : Fin r) : j' (j i) = e i := congrArg e (j.symm_apply_apply i)
  have hj' : Specs.AbsoluteDynkinTypes.PreservesCartan
      (RootData.integralCartan D.datum.rootDatum D.base)
      (RootData.integralCartan E.datum.rootDatum E.base) j' := by
    intro a b
    obtain ⟨i, rfl⟩ := j.surjective a
    obtain ⟨l, rfl⟩ := j.surjective b
    rw [hj i, hj l, hc, hCartan]
  obtain ⟨f, hf⟩ := pinnedCartanComparison P Q D E hD hE j' hj'
  refine ⟨f.group, fun R g => (mapSubgroupSections f.group f.torus f.torus_comm R g).trans
    (T.range R _), fun R g => (mapSubgroupSections f.group f.borel f.borel_comm R g).trans
    (B.matrix R _), fun i R a v => ?_⟩
  have hi := hf (j i)
  rw [hj i] at hi
  let α : SimpleRoot P.pair := ⟨(j i).val, (D.simple_iff _).mp (j i).property⟩
  let β : SimpleRoot Q.pair := ⟨(e i).val, (E.simple_iff _).mp (e i).property⟩
  have hroot := pinnedRootMap f α β hi.1
  constructor
  · change (s.hom.app R (rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) R a ≫
      f.group.hom.hom.hom)).val = _
    rw [← rootPoint_comp, hroot]
    exact hpin i R a
  · let c := Additive.toMul (D.datum.rootDatum.coroot (j i).val)
    let c' := Additive.toMul (E.datum.rootDatum.coroot (e i).val)
    have ht : P.pair.T.inclusion.hom.hom ≫ f.group.hom.hom.hom =
        f.torus.hom.hom.hom ≫ T.subgroup.inclusion.hom.hom := by
      simpa only [Grp.comp_hom_hom] using congrArg (fun (a : P.pair.T.group ⟶ S.val) => a.hom.hom)
        f.torus_comm
    change (s.hom.app R (cocharacterPoint c R v ≫ P.pair.T.inclusion.hom.hom ≫
      f.group.hom.hom.hom)).val = _
    rw [ht, ← Category.assoc, mappedTorusPoint, show c ≫ f.torus.hom = c' from hi.2]
    exact hcor i R v

end SplitSpecialLinearComparison

section QuadraticMatrixDescent

open Matrix
open private fixedFieldTensor_injective from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

set_option maxHeartbeats 1700000 in
set_option backward.isDefEq.respectTransparency false in
theorem quadraticOrbitMatrixPoints : QuadraticOrbitMatrixPoints.{u} := by
  classical
  intro F K _ _ _ _ _ ρ i hρ R
  letI := MulAction.compHom (Fin 2) ρ
  let J := MulAction.stabilizer Gal(K/F) i
  let E := orbitField ρ i
  obtain ⟨_, hquad, hsep, hres⟩ := quadraticOrbitField ρ i hρ
  letI : Algebra.IsQuadraticExtension F E := hquad
  letI : Algebra.IsSeparable F E := hsep
  let f := orbitScalarEmbedding R J
  let fM : SL₃ (R ⊗[F] E) →* SL₃ (K ⊗[F] R) := SpecialLinearGroup.map f.toRingHom
  let σR := (quadraticTensorInvolution F E R).toRingEquiv
  let τ : SL₃ (R ⊗[F] E) →* SL₃ (R ⊗[F] E) :=
    hyperbolicDual.comp (SpecialLinearGroup.map σR.toRingHom)
  let U := τ.eqLocus (MonoidHom.id _)
  have hf : Function.Injective fM := matrix_map_injective _ (fixedFieldTensor_injective R J)
  have hfield (σ : Gal(K/F)) (z : R ⊗[F] E) :
      coefficientRingMap R σ (f z) = if ρ σ = 1 then f z else f (σR z) := by
    by_cases hs : ρ σ = 1
    · rw [ite_eq_left hs]
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        change σ b.val ⊗ₜ[F] a = b.val ⊗ₜ[F] a
        rw [hres σ b, ite_eq_left hs]
      | add a b ha hb => simp only [map_add, ha, hb]
    · rw [ite_eq_right hs]
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        change σ b.val ⊗ₜ[F] a = (Specs.UnitaryRankOne.quadraticConjugation F E b).val ⊗ₜ[F] a
        rw [hres σ b, ite_eq_right hs]
      | add a b ha hb => simp only [map_add, ha, hb]
  have hmat (σ : Gal(K/F)) (g : SL₃ (R ⊗[F] E)) :
      SpecialLinearGroup.map (coefficientRingMap R σ) (fM g) =
        if ρ σ = 1 then fM g else fM (SpecialLinearGroup.map σR.toRingHom g) := by
    by_cases hs : ρ σ = 1
    · rw [ite_eq_left hs]
      apply Subtype.ext
      ext j l
      exact (hfield σ (g.val j l)).trans (ite_eq_left hs)
    · rw [ite_eq_right hs]
      apply Subtype.ext
      ext j l
      exact (hfield σ (g.val j l)).trans (ite_eq_right hs)
  have hnontriv : ∃ σ : Gal(K/F), ρ σ ≠ 1 := by
    obtain ⟨σ, hσ⟩ := hρ i.rev
    refine ⟨σ, fun h => ?_⟩
    rw [h, Equiv.Perm.one_apply] at hσ
    fin_cases i <;> contradiction
  have hU (g : SL₃ (R ⊗[F] E)) : g ∈ U ↔ fM g ∈ unitaryOrbitMatrices ρ R := by
    constructor
    · intro hg σ
      have hg' : hyperbolicDual (SpecialLinearGroup.map σR.toRingHom g) = g := hg
      have he := congrArg hyperbolicDual hg'
      rw [hyperbolicDual_involutive] at he
      change SpecialLinearGroup.map (coefficientRingMap R σ) (fM g) =
        if ρ σ = 1 then fM g else hyperbolicDual (fM g)
      rw [hmat]
      by_cases hs : ρ σ = 1
      · rw [ite_eq_left hs, ite_eq_left hs]
      · rw [ite_eq_right hs, ite_eq_right hs, he]
        exact (hyperbolicDual_map f.toRingHom g).symm
    · intro hg
      obtain ⟨σ, hσ⟩ := hnontriv
      have he := hg σ
      change SpecialLinearGroup.map (coefficientRingMap R σ) (fM g) =
        if ρ σ = 1 then fM g else hyperbolicDual (fM g) at he
      rw [hmat, ite_eq_right hσ, ite_eq_right hσ, hyperbolicDual_map] at he
      have h := congrArg hyperbolicDual (hf he)
      rw [hyperbolicDual_involutive] at h
      exact h
  let p : U →* unitaryOrbitMatrices ρ R :=
    { toFun := fun g => ⟨fM g.val, (hU _).mp g.property⟩
      map_one' := Subtype.ext (map_one fM)
      map_mul' x y := Subtype.ext (map_mul fM x.val y.val) }
  have hp : Function.Bijective p := by
    constructor
    · intro a b h
      exact Subtype.ext (hf (congrArg Subtype.val h))
    · intro g
      have hfix (σ : Gal(K/F)) (hs : σ ∈ J) :
          SpecialLinearGroup.map (coefficientRingMap R σ) g.val = g.val := by
        have hσ : ρ σ = 1 := permFinTwo_eq_one_of_fixed (show ρ σ i = i from hs)
        exact (g.property σ).trans (ite_eq_left hσ)
      obtain ⟨a, ha⟩ := orbitMatrixLift R J 3 g.val hfix
      change fM a = g.val at ha
      have hm : a ∈ U := (hU _).mpr (ha ▸ g.property)
      exact ⟨⟨a, hm⟩, Subtype.ext ha⟩
  refine ⟨hquad, hsep, U, MulEquiv.ofBijective p hp, ?_, fun _ => rfl, fun m g => ?_⟩
  · exact fun g => hyperbolicFixedEquation σR g
  · exact mark_map_iff _ (fixedFieldTensor_injective R J) m g.val

end QuadraticMatrixDescent

section AdjacentAutomorphism

open Matrix
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.Pinning (AttachedDatum PinnedGroup PinnedIso SimpleRoot transportCharacter)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.PinnedUniqueness (scalarGroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private rootEquiv coroot_transport from LinearAlgebraicGroups.Classification.Pinning
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

private def matrixSimpleRoot {R : Type u} [CommRing R] (i : Fin 2) (x : R) : SL₃ R :=
  SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ_iff).mpr (le_refl i)).ne
    (signedParameter i x)

private theorem dual_simpleRoot {R : Type u} [CommRing R] (i : Fin 2) (x : R) :
    hyperbolicDual (matrixSimpleRoot i x) = matrixSimpleRoot i.rev x := by
  have h := unitaryPinningInterchange (RingEquiv.refl R) x
  have hmap (g : SL₃ R) : SpecialLinearGroup.map (RingEquiv.refl R).toRingHom g = g := by
    apply Subtype.ext
    ext i j
    rfl
  simp only [unitaryDescentOperator, hmap, RingEquiv.refl_apply] at h
  fin_cases i
  · exact h.1
  · exact h.2

private theorem dual_simpleCoroot {R : Type u} [CommRing R] (i : Fin 2) (x : Rˣ) :
    hyperbolicDual (matrixSimpleCoroot i x) = matrixSimpleCoroot i.rev x := by
  have h := unitaryCorootInterchange (RingEquiv.refl R) i x
  have hmap : SpecialLinearGroup.map (RingEquiv.refl R).toRingHom (matrixSimpleCoroot i x) =
      matrixSimpleCoroot i x := by apply Subtype.ext; ext a b; rfl
  have he : Units.map (RingEquiv.refl R).toRingHom.toMonoidHom x = x := Units.ext rfl
  change hyperbolicInverseTranspose (matrixSimpleCoroot i x) = matrixSimpleCoroot i.rev x
  simpa only [unitaryDescentOperator, hmap, he] using h

private theorem diagonalSL₃_corootProduct {R : Type u} [CommRing R] (g : SL₃ R)
    (hg : MatrixMark.torus.Holds g) :
    ∃ v w : Rˣ, g = matrixSimpleCoroot 0 v * matrixSimpleCoroot 1 w := by
  let d (i : Fin 3) := g.val i i
  have hd : g.val = Matrix.diagonal d := by
    ext i j
    by_cases h : i = j
    · subst j; simp [d]
    · exact (hg i j h).trans (diagonal_apply_ne _ h).symm
  have hprod : d 0 * d 1 * d 2 = 1 := by
    have h := g.property
    rw [hd, Matrix.det_diagonal, Fin.prod_univ_three] at h
    simpa only [mul_assoc] using h
  let v : Rˣ := ⟨d 0, d 1 * d 2, by simpa only [mul_assoc] using hprod, by
    rw [mul_comm]; simpa only [mul_assoc] using hprod⟩
  let w : Rˣ := ⟨d 0 * d 1, d 2, hprod, by rw [mul_comm]; exact hprod⟩
  refine ⟨v, w, Subtype.ext ?_⟩
  change g.val = Matrix.diagonal _ * Matrix.diagonal _
  rw [hd, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp [Specs.SpecialLinearDatum.coordinatePairUnits, v]
  · simp only [Specs.SpecialLinearDatum.coordinatePairUnits, v, w]
    simp only [Fin.castSucc, Fin.succ, Fin.mk_one]
    change d 1 = (d 1 * d 2) * (d 0 * d 1)
    calc
      d 1 = d 1 * 1 := (mul_one _).symm
      _ = d 1 * (d 0 * d 1 * d 2) := congrArg (d 1 * ·) hprod.symm
      _ = _ := by ring
  · simp [Specs.SpecialLinearDatum.coordinatePairUnits, w]

private def matrixDiagramMap (swap : Bool) (k : Type u) [Field k] :
    specialLinearThreePoints k ⟶ specialLinearThreePoints k where
  app R := GrpCat.ofHom (if swap then hyperbolicDual else MonoidHom.id _)
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    cases swap with
    | false => rfl
    | true => exact hyperbolicDual_map f.hom.toRingHom x

private theorem pinnedAutCoroot {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} (D : AttachedDatum P.pair) (f : PinnedIso P P)
    (α β : SimpleRoot P.pair) (h : transportCharacter f.torus α.val.val = β.val.val) :
    letI := D.comm
    Additive.toMul (D.datum.rootDatum.coroot α.val) ≫ f.torus.hom =
      Additive.toMul (D.datum.rootDatum.coroot β.val) := by
  letI := D.comm
  have hi : rootEquiv f α.val = β.val := Subtype.ext h
  have hy := coroot_transport f D D α.val
  rw [hi] at hy
  change Additive.ofMul (Additive.toMul (D.datum.rootDatum.coroot β.val) ≫ f.torus.inv) =
    D.datum.rootDatum.coroot α.val at hy
  apply (cancel_mono f.torus.inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (congrArg Additive.toMul hy).symm

set_option maxHeartbeats 2200000 in
set_option backward.isDefEq.respectTransparency false in
theorem adjacentPinnedAutomorphisms : AdjacentPinnedAutomorphisms.{u} := by
  classical
  intro k _ A P D hss hsc j hc
  letI := D.comm
  let S := StandardGroups.specialLinearGroup k (ULift.{u} (Fin 3))
  let s := StandardGroups.specialLinearGroupPointsIso k (ULift.{u} (Fin 3))
  have hc' (i l : Fin 2) : RootData.integralCartan D.datum.rootDatum D.base (j i) (j l) =
      if i = l then 2 else if i.val + 1 = l.val ∨ l.val + 1 = i.val then -1 else 0 := by
    rw [hc]
    fin_cases i <;> fin_cases l <;> decide
  obtain ⟨f, ht, hB, hcoords⟩ := splitPinnedSpecialLinearComparison P D hss hsc 2 S s j hc'
  let F := groupPointsFunctor k
  let m := F.mapIso f ≪≫ specialLinearThreePointIso k
  let α (i : Fin 2) : SimpleRoot P.pair := ⟨(j i).val, (D.simple_iff _).mp (j i).property⟩
  let x (i : Fin 2) := (P.pin (α i)).val.hom ≫ (P.roots (α i).val).val.inclusion
  let c (i : Fin 2) := Additive.toMul (D.datum.rootDatum.coroot (j i).val)
  let y (i : Fin 2) (R : TestAlgebra k) (v : Rˣ) :=
    cocharacterPoint (c i) R v ≫ P.pair.T.inclusion.hom.hom
  have htor (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R) :
      g ∈ SubgroupSections P.pair.T ((testSpec k).obj (Opposite.op R)) ↔
        MatrixMark.torus.Holds (m.hom.app R g) := by
    refine (ht R g).trans ?_
    change (∀ i l : ULift.{u} (Fin 3), i ≠ l → (s.hom.app R (g ≫ f.hom.hom.hom)).val i l = 0) ↔
      (∀ i l : Fin 3, i ≠ l → (s.hom.app R (g ≫ f.hom.hom.hom)).val ⟨i⟩ ⟨l⟩ = 0)
    exact ⟨fun h i l hil => h ⟨i⟩ ⟨l⟩ (fun e => hil (congrArg ULift.down e)),
      fun h i l hil => h i.down l.down (fun e => hil (ULift.ext e))⟩
  have hroot (i : Fin 2) (R : TestAlgebra k) (a : R) :
      m.hom.app R (rootPoint (x i) R a) = matrixSimpleRoot i a := by
    apply Subtype.ext
    ext l r
    have h := congrArg (fun a : Matrix (ULift.{u} (Fin 3)) _ R => a ⟨l⟩ ⟨r⟩)
      (hcoords i R a 1).1
    change (s.hom.app R (rootPoint (x i) R a ≫ f.hom.hom.hom)).val ⟨l⟩ ⟨r⟩ =
      (matrixSimpleRoot i a).val l r
    rw [matrixSimpleRoot, SpecialLinearGroup.transvection_coe]
    exact h.trans (by simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply])
  have hcor (i : Fin 2) (R : TestAlgebra k) (v : Rˣ) :
      m.hom.app R (y i R v) = matrixSimpleCoroot i v := by
    apply Subtype.ext
    ext l r
    have h := congrArg (fun a : Matrix (ULift.{u} (Fin 3)) _ R => a ⟨l⟩ ⟨r⟩)
      (hcoords i R 0 v).2
    exact h.trans (by simp [matrixSimpleCoroot, Matrix.diagonal_apply])
  have hborel (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R) :
      g ∈ SubgroupSections P.pair.B ((testSpec k).obj (Opposite.op R)) ↔
        MatrixMark.positiveBorel.Holds (m.hom.app R g) := by
    refine (hB R g).trans ?_
    change (∀ i l : ULift.{u} (Fin 3), l < i →
      (s.hom.app R (g ≫ f.hom.hom.hom)).val i l = 0) ↔
      (∀ i l : Fin 3, l < i → (s.hom.app R (g ≫ f.hom.hom.hom)).val ⟨i⟩ ⟨l⟩ = 0)
    exact ⟨fun h i l hil => h ⟨i⟩ ⟨l⟩ hil, fun h i l hil => h i.down l.down hil⟩
  refine ⟨m, htor, hborel, ?_, ?_⟩
  · intro i R a v
    exact ⟨congrArg Subtype.val (hroot i R a), hcor i R v⟩
  intro swap b hb
  let g := F.map b.group.hom
  let δ := matrixDiagramMap swap k
  let z := g ≫ m.hom ≫ δ ≫ m.inv
  let R₀ := CommAlgCat.of k k
  let U := Under.forget R₀
  have hroot_b (i : Fin 2) (R : TestAlgebra k) (a : R) :
      g.app R (rootPoint (x i) R a) = rootPoint (x (adjacentPermutation swap i)) R a := by
    change rootPoint (x i) R a ≫ b.group.hom.hom.hom = _
    rw [← rootPoint_comp, pinnedRootMap b (α i) (α (adjacentPermutation swap i)) (hb i)]
  have hcor_b (i : Fin 2) (R : TestAlgebra k) (v : Rˣ) :
      g.app R (y i R v) = y (adjacentPermutation swap i) R v := by
    have ht' := congrArg (fun (a : P.pair.T.group ⟶ P.pair.G.val) => a.hom.hom) b.torus_comm
    simp only [Grp.comp_hom_hom] at ht'
    change (cocharacterPoint (c i) R v ≫ P.pair.T.inclusion.hom.hom) ≫ b.group.hom.hom.hom = _
    rw [Category.assoc, ht', ← Category.assoc, mappedTorusPoint,
      show c i ≫ b.torus.hom = c (adjacentPermutation swap i) from
        pinnedAutCoroot D b (α i) (α (adjacentPermutation swap i)) (hb i)]
  have hzroot (i : Fin 2) (R : TestAlgebra k) (a : R) :
      z.app R (rootPoint (x i) R a) = rootPoint (x i) R a := by
    apply ((m.app R).groupIsoToMulEquiv).injective
    change m.hom.app R (m.inv.app R (δ.app R (m.hom.app R (g.app R (rootPoint (x i) R a))))) = _
    have he (x : SL₃ R) : m.hom.app R (m.inv.app R x) = x :=
      GrpCat.hom_inv_apply (m.app R) x
    rw [he, hroot_b, hroot]
    change δ.app R (matrixSimpleRoot (adjacentPermutation swap i) a) =
      m.hom.app R (rootPoint (x i) R a)
    rw [hroot]
    cases swap with
    | false => rfl
    | true =>
      change hyperbolicDual (matrixSimpleRoot i.rev a) = matrixSimpleRoot i a
      rw [dual_simpleRoot, Fin.rev_rev]
  have hzcor (i : Fin 2) (R : TestAlgebra k) (v : Rˣ) :
      z.app R (y i R v) = y i R v := by
    apply ((m.app R).groupIsoToMulEquiv).injective
    change m.hom.app R (m.inv.app R (δ.app R (m.hom.app R (g.app R (y i R v))))) = _
    have he (x : SL₃ R) : m.hom.app R (m.inv.app R x) = x :=
      GrpCat.hom_inv_apply (m.app R) x
    rw [he, hcor_b, hcor]
    change δ.app R (matrixSimpleCoroot (adjacentPermutation swap i) v) = m.hom.app R (y i R v)
    rw [hcor]
    cases swap with
    | false => rfl
    | true =>
      change hyperbolicDual (matrixSimpleCoroot i.rev v) = matrixSimpleCoroot i v
      rw [dual_simpleCoroot, Fin.rev_rev]
  have htorz (R : TestAlgebra k) (t : GroupPoints P.pair.T.group R) :
      z.app R (t ≫ P.pair.T.inclusion.hom.hom) = t ≫ P.pair.T.inclusion.hom.hom := by
    let a : GroupPoints P.pair.G.val R := t ≫ P.pair.T.inclusion.hom.hom
    have ha : MatrixMark.torus.Holds (m.hom.app R a) := (htor R a).mp ⟨t, rfl⟩
    obtain ⟨v, w, hvw⟩ := diagonalSL₃_corootProduct (m.hom.app R a) ha
    have hprod : a = y 0 R v * y 1 R w := by
      apply (m.app R).groupIsoToMulEquiv.injective
      change m.hom.app R a = m.hom.app R (y 0 R v * y 1 R w)
      rw [map_mul, hcor, hcor]
      exact hvw
    change z.app R a = a
    rw [hprod, map_mul, hzcor, hzcor]
  have hid := Classification.PinnedUniqueness.scalarRigidity P R₀ (Functor.whiskerLeft U z)
    (fun S t => htorz S.right t) (fun S a v => by
      obtain ⟨i, hi⟩ := j.surjective ⟨a.val, (D.simple_iff _).mpr a.property⟩
      have he : α i = a := Subtype.ext (congrArg (fun z : D.base.support => z.val) hi)
      have h := hzroot i S.right v
      dsimp only [x] at h
      rwa [he] at h)
  intro R a
  let RR : Under R₀ := Under.mk (CommAlgCat.ofHom (Algebra.ofId k R))
  have h := congrArg (fun p : scalarGroupPoints R₀ P.pair.G.val ⟶ _ => p.app RR a) hid
  change m.inv.app R (δ.app R (m.hom.app R (g.app R a))) = a at h
  have he := congrArg (fun x => δ.app R (m.hom.app R x)) h
  have hri (x : SL₃ R) : m.hom.app R (m.inv.app R x) = x :=
    GrpCat.hom_inv_apply (m.app R) x
  rw [hri] at he
  cases swap with
  | false => exact he
  | true =>
    change hyperbolicDual (hyperbolicDual (m.hom.app R (a ≫ b.group.hom.hom.hom))) =
      hyperbolicDual (m.hom.app R a) at he
    rw [hyperbolicDual_involutive] at he
    exact he

end AdjacentAutomorphism

section RestrictedCoordinates

open LinearAlgebraicGroups.Descent (SemilinearAction)
open private tensorAutomorphism_apply from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

theorem restrictExtendedPointBijective : RestrictExtendedPointBijective.{u} := by
  intro F K _ _ _ C R
  constructor
  · intro p q h
    exact Algebra.TensorProduct.ext_ring h
  · intro p
    let f : K ⊗[F] C →ₐ[K] K ⊗[F] R :=
      Algebra.TensorProduct.lift (Algebra.ofId K (K ⊗[F] R)) p (fun _ _ => Commute.all _ _)
    refine ⟨f, AlgHom.ext ?_⟩
    intro a
    change f (1 ⊗ₜ[F] a) = p a
    simp [f]
    rw [← Algebra.TensorProduct.one_def, one_mul]

set_option maxHeartbeats 900000 in
theorem restrictedCoefficientEquation : RestrictedCoefficientEquation.{u} := by
  intro F K _ _ _ C R p b σ
  constructor
  · intro h c
    have he := h (1 ⊗ₜ[F] c)
    change p (σ (1 : K) ⊗ₜ[F] b.hom c) = coefficientRingMap R σ (p (1 ⊗ₜ[F] c)) at he
    rw [map_one] at he
    exact he
  · intro h x
    induction x using TensorProduct.inductionOn with
    | tmul r c =>
      change p (σ r ⊗ₜ[F] b.hom c) = coefficientRingMap R σ (p (r ⊗ₜ[F] c))
      have hp (t : K) (a : C) : p (t ⊗ₜ[F] a) =
          (t ⊗ₜ[F] (1 : R)) * p (1 ⊗ₜ[F] a) := by
        have he : (t ⊗ₜ[F] a : K ⊗[F] C) =
            (t ⊗ₜ[F] (1 : C)) * (1 ⊗ₜ[F] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [he, map_mul, show (t ⊗ₜ[F] (1 : C)) = algebraMap K (K ⊗[F] C) t from rfl,
          AlgHom.commutes]
        rfl
      rw [hp (σ r), hp r, map_mul]
      change (σ r ⊗ₜ[F] (1 : R)) * restrictExtendedPoint R p (b.hom c) =
        (σ r ⊗ₜ[F] (1 : R)) * coefficientRingMap R σ (restrictExtendedPoint R p c)
      rw [h]
    | add a c ha hc => simp only [map_add, ha, hc]

end RestrictedCoordinates

section OrbitDescentPoints

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AdjointCocharacters (coordinateHopfMap coordinateHopfIso)
local notation "coordinateAlgebra" => Specs.AdjointCocharacters.coordinateHopf
open Specs.AutomorphismSequence (forgetPinning)
open Specs.Pinning (PinnedGroup)
open LinearAlgebraicGroups.Descent (SemilinearAction)
open private coordinatePresentationMap from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private extendCoordinatePoint_mul tensorAutomorphism_apply extendedCoordinateIso
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private restrictConvolution restrictConvolution_mul extendedGroupIso extendedSpecIso_hom_fst
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private def coordinatePointIso (G : AffineAlgebraicGroup F) :
    convolutionPoints (coordinateAlgebra G) ≅ (groupPointsFunctor F).obj G.val :=
  hopfSpecPointIso _ ≪≫ (groupPointsFunctor F).mapIso (coordinateHopfIso G)

private theorem coordinatePointIso_comp {G H : AffineAlgebraicGroup F} (f : G.val ⟶ H.val)
    (R : TestAlgebra F) (p : coordinateAlgebra G →ₐ[F] R) :
    (coordinatePointIso H).hom.app R (WithConv.toConv (p.comp (coordinateHopfMap f).hom.toAlgHom)) =
      ((groupPointsFunctor F).map f).app R ((coordinatePointIso G).hom.app R (WithConv.toConv p)) := by
  have he : specGroupMap (coordinateHopfMap f) ≫ (coordinateHopfIso H).hom =
      (coordinateHopfIso G).hom ≫ f := by
    rw [coordinatePresentationMap]
    simp
  -- Both sides use the spectrum map of the same composite of algebra maps.
  have h₁ : ((hopfSpecPointIso (coordinateAlgebra H)).hom.app R
      (WithConv.toConv (p.comp (coordinateHopfMap f).hom.toAlgHom)) :
        GroupPoints (specGroup (coordinateAlgebra H)) R) =
      (hopfSpecPointIso (coordinateAlgebra G)).hom.app R (WithConv.toConv p) ≫
        (specGroupMap (coordinateHopfMap f)).hom.hom := by
    apply Over.OverMorphism.ext
    exact Spec.map_comp (CommRingCat.ofHom (coordinateHopfMap f).hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom p.toRingHom)
  change ((hopfSpecPointIso (coordinateAlgebra H)).hom.app R
      (WithConv.toConv (p.comp (coordinateHopfMap f).hom.toAlgHom)) :
        GroupPoints (specGroup (coordinateAlgebra H)) R) ≫ (coordinateHopfIso H).hom.hom.hom =
    (((hopfSpecPointIso (coordinateAlgebra G)).hom.app R (WithConv.toConv p) :
      GroupPoints (specGroup (coordinateAlgebra G)) R) ≫ (coordinateHopfIso G).hom.hom.hom) ≫ f.hom.hom
  rw [h₁, Category.assoc, Category.assoc]
  exact congrArg (fun a : specGroup (coordinateAlgebra G) ⟶ H.val =>
    ((hopfSpecPointIso (coordinateAlgebra G)).hom.app R (WithConv.toConv p) :
      GroupPoints (specGroup (coordinateAlgebra G)) R) ≫ a.hom.hom) he

private abbrev tensorPointAlgebra (K : Type u) [Field K] [Algebra F K]
    (R : TestAlgebra F) : TestAlgebra F :=
  CommAlgCat.of F (K ⊗[F] R)

private abbrev tensorPointMap (K : Type u) [Field K] [Algebra F K]
    {R S : TestAlgebra F} (f : R ⟶ S) :
    tensorPointAlgebra K R ⟶ tensorPointAlgebra K S :=
  CommAlgCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id K K) f.hom).restrictScalars F)

private def liftedCoordinatePoint (d : PinnedOrbitDescent F K) (R : TestAlgebra F)
    (p : coordinateAlgebra d.G →ₐ[F] R) :
    extendedHopf K (coordinateAlgebra d.P.pair.G) →ₐ[K] K ⊗[F] R :=
  (Algebra.TensorProduct.map (AlgHom.id K K) p).comp d.descent.groupIso.hom.hom.toAlgHom

private def liftedSplitPoint (d : PinnedOrbitDescent F K) (R : TestAlgebra F) :
    GroupPoints d.G.val R →* GroupPoints d.P.pair.G.val (tensorPointAlgebra K R) := by
  let C := coordinateAlgebra d.P.pair.G
  let B := coordinateAlgebra d.G
  letI := convolutionGroup B R
  letI := convolutionGroup C (tensorPointAlgebra K R)
  letI := convolutionGroup (extendedHopf K C) (CommAlgCat.of K (K ⊗[F] R))
  letI := convolutionGroup (extendedHopf K B) (CommAlgCat.of K (K ⊗[F] R))
  let v := ((coordinatePointIso d.G).inv.app R).hom
  let q (p : WithConv (B →ₐ[F] R)) := WithConv.toConv (liftedCoordinatePoint d R p.ofConv)
  have hq (p r : WithConv (B →ₐ[F] R)) : q (p * r) = q p * q r := by
    apply WithConv.ofConv_injective
    exact (congrArg (fun e => e.comp d.descent.groupIso.hom.hom.toAlgHom)
        (extendCoordinatePoint_mul R p r)).trans
      (AlgHom.convMul_comp_bialgHom_distrib _ _ d.descent.groupIso.hom.hom)
  let h (x : GroupPoints d.G.val R) :=
    (coordinatePointIso d.P.pair.G).hom.app (tensorPointAlgebra K R) (restrictConvolution (q (v x)))
  have hm (x y : GroupPoints d.G.val R) : h (x * y) = h x * h y := by
    change (coordinatePointIso d.P.pair.G).hom.app (tensorPointAlgebra K R)
      (restrictConvolution (q (v (x * y)))) = _
    rw [map_mul v, hq, restrictConvolution_mul, map_mul]
  refine { toFun := h, map_one' := ?_, map_mul' := hm }
  have hh := hm 1 1
  rw [one_mul] at hh
  exact mul_eq_left.mp hh.symm

private theorem liftedSplitPoint_natural (d : PinnedOrbitDescent F K)
    {R S : TestAlgebra F} (f : R ⟶ S) (x : GroupPoints d.G.val R) :
    liftedSplitPoint d S (mapPoints f x) =
      mapPoints (tensorPointMap K f) (liftedSplitPoint d R x) := by
  let p := ((coordinatePointIso d.G).inv.app R x).ofConv
  let q := ((coordinatePointIso d.G).inv.app S (mapPoints f x)).ofConv
  have he : q = f.hom.comp p := by
    exact congrArg WithConv.ofConv ((coordinatePointIso d.G).inv.naturality_apply f x)
  have hc : liftedCoordinatePoint d S q =
      ((Algebra.TensorProduct.map (AlgHom.id K K) f.hom).comp (liftedCoordinatePoint d R p)) := by
    rw [he]
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro b
    change (Algebra.TensorProduct.map (AlgHom.id K K) (f.hom.comp p))
      (d.descent.groupIso.hom.hom (1 ⊗ₜ[F] b)) =
      (Algebra.TensorProduct.map (AlgHom.id K K) f.hom)
        ((Algebra.TensorProduct.map (AlgHom.id K K) p) (d.descent.groupIso.hom.hom (1 ⊗ₜ[F] b)))
    generalize d.descent.groupIso.hom.hom (1 ⊗ₜ[F] b) = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  let r := WithConv.toConv (restrictExtendedPoint R (liftedCoordinatePoint d R p))
  have hr := (coordinatePointIso d.P.pair.G).hom.naturality_apply (tensorPointMap K f) r
  change (coordinatePointIso d.P.pair.G).hom.app (tensorPointAlgebra K S) (WithConv.toConv
    (restrictExtendedPoint S (liftedCoordinatePoint d S q))) = _
  rw [hc]
  exact hr

private abbrev pointCoefficient (K : Type u) [Field K] [Algebra F K] (R : TestAlgebra F)
    (σ : Gal(K/F)) : tensorPointAlgebra K R ⟶ tensorPointAlgebra K R :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id F R))

private theorem liftedSplitPoint_range [IsGalois F K] (d : PinnedOrbitDescent F K)
    (R : TestAlgebra F) :
    Function.Injective (liftedSplitPoint d R) ∧
    ∀ y : GroupPoints d.P.pair.G.val (tensorPointAlgebra K R),
      y ∈ Set.range (liftedSplitPoint d R) ↔
      ∀ σ : Gal(K/F),
        let a := (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv
        ((groupPointsFunctor F).map a).app (tensorPointAlgebra K R) y =
          mapPoints (pointCoefficient K R σ) y := by
  let C := coordinateAlgebra d.P.pair.G
  let B := coordinateAlgebra d.G
  let z := (coordinatePointIso d.P.pair.G).app (tensorPointAlgebra K R)
  let w := (coordinatePointIso d.G).app R
  let t := liftedCoordinatePoint d R
  let r := restrictExtendedPoint (K := K) (C := C) R
  have ht := pinnedFixedPoints d.descent R
  change Function.Injective t ∧ _ at ht
  have hr : Function.Bijective r := restrictExtendedPointBijective R
  have hp (x : GroupPoints d.G.val R) :
      liftedSplitPoint d R x = z.hom (WithConv.toConv (r (t (w.inv x).ofConv))) := rfl
  constructor
  · rw [show ⇑(liftedSplitPoint d R) = fun x =>
      z.hom (WithConv.toConv (r (t (w.inv x).ofConv))) from funext hp]
    exact z.groupIsoToMulEquiv.injective.comp (WithConv.toConv_injective.comp
      (hr.1.comp (ht.1.comp (WithConv.ofConv_injective.comp w.groupIsoToMulEquiv.symm.injective))))
  · intro y
    obtain ⟨p, hp'⟩ := hr.2 (z.inv y).ofConv
    have hy : y = z.hom (WithConv.toConv (r p)) := by
      rw [hp']
      exact (GrpCat.hom_inv_apply z y).symm
    rw [hy]
    have hmem : z.hom (WithConv.toConv (r p)) ∈ Set.range (liftedSplitPoint d R) ↔
        p ∈ Set.range t := by
      constructor
      · rintro ⟨x, hx⟩
        rw [hp] at hx
        exact ⟨(w.inv x).ofConv, hr.1 (WithConv.toConv_injective (z.groupIsoToMulEquiv.injective hx))⟩
      · rintro ⟨q, rfl⟩
        refine ⟨w.hom (WithConv.toConv q), ?_⟩
        rw [hp, GrpCat.inv_hom_apply]
    rw [hmem]
    refine (ht.2 p).trans ?_
    apply forall_congr'
    intro σ
    let a : d.P.pair.G.val ⟶ d.P.pair.G.val :=
      (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv
    change (∀ x, p ((extendedHopfMap K (coordinateHopfMap a)).hom
      ((SemilinearAction.scalarExtension (K := K) C).act σ x)) = coefficientRingMap R σ (p x)) ↔
      ((groupPointsFunctor F).map a).app (tensorPointAlgebra K R) (z.hom (WithConv.toConv (r p))) =
        mapPoints (pointCoefficient K R σ) (z.hom (WithConv.toConv (r p)))
    have ha := coordinatePointIso_comp a (tensorPointAlgebra K R) (r p)
    have hm := (coordinatePointIso d.P.pair.G).hom.naturality_apply
      (pointCoefficient K R σ) (WithConv.toConv (r p))
    change z.hom (WithConv.toConv ((r p).comp (coordinateHopfMap a).hom.toAlgHom)) =
      ((groupPointsFunctor F).map a).app (tensorPointAlgebra K R) (z.hom (WithConv.toConv (r p))) at ha
    change z.hom (WithConv.toConv ((pointCoefficient K R σ).hom.comp (r p))) =
      mapPoints (pointCoefficient K R σ) (z.hom (WithConv.toConv (r p))) at hm
    rw [← ha, ← hm]
    refine (restrictedCoefficientEquation R p (coordinateHopfMap a) σ).trans ⟨?_, ?_⟩
    · intro h
      have h' : (r p).comp (coordinateHopfMap a).hom.toAlgHom =
          (pointCoefficient K R σ).hom.comp (r p) := AlgHom.ext h
      rw [h']
    · intro h c
      exact DFunLike.congr_fun
        (WithConv.toConv_injective (z.groupIsoToMulEquiv.injective h)) c

private abbrev coordinateBasePoint (G : AffineAlgebraicGroup F) (R : TestAlgebra K)
    (p : extendedHopf K (coordinateAlgebra G) →ₐ[K] R) :
    GroupPoints ((groupBaseChange F K).obj G.val) R :=
  ((hopfSpecPointIso (extendedHopf K (coordinateAlgebra G))).hom.app R
    (WithConv.toConv p) : GroupPoints (specGroup (extendedHopf K (coordinateAlgebra G))) R) ≫
    (extendedCoordinateIso (K := K) G).hom.hom.hom

private theorem coordinateBasePoint_bijective (G : AffineAlgebraicGroup F) (R : TestAlgebra K) :
    Function.Bijective (coordinateBasePoint G R) :=
  (((groupPointsFunctor K).mapIso (extendedCoordinateIso (K := K) G)).app R).groupIsoToMulEquiv.bijective.comp
    (((hopfSpecPointIso (extendedHopf K (coordinateAlgebra G))).app R).groupIsoToMulEquiv.bijective.comp
      WithConv.toConv_bijective)

set_option maxHeartbeats 1100000 in
private theorem coordinateBasePoint_restrict (G : AffineAlgebraicGroup F) (R : TestAlgebra K)
    (p : extendedHopf K (coordinateAlgebra G) →ₐ[K] R) :
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    baseChangePoint F K G.val.X R (coordinateBasePoint G R p) =
      (coordinatePointIso G).hom.app R₀ (restrictConvolution (WithConv.toConv p)) := by
  let R₀ := (restrictTestAlgebra F K).obj R
  letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
  letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
  let C := coordinateAlgebra G
  let p₀ : extendedHopf K C →ₐ[K] R₀ := p
  let e := coordinateHopfIso G
  let f := extendedGroupIso K C
  apply Over.OverMorphism.ext
  let i : C →ₐ[F] K ⊗[F] C := Algebra.TensorProduct.includeRight
  let s := Spec.map (CommRingCat.ofHom p.toRingHom)
  let π := pullback.fst (specGroup C).X.hom (fieldSpecMap F K)
  have hπ : f.hom.hom.hom.left ≫ π = Spec.map (CommRingCat.ofHom i.toRingHom) :=
    extendedSpecIso_hom_fst K C
  change ((s ≫ f.hom.hom.hom.left) ≫ ((baseChange F K).map e.hom.hom.hom).left) ≫
    pullback.fst G.val.X.hom (fieldSpecMap F K) =
    Spec.map (CommRingCat.ofHom (p.toRingHom.comp i.toRingHom)) ≫ e.hom.hom.hom.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
  change s ≫ f.hom.hom.hom.left ≫ π ≫ e.hom.hom.hom.left = _
  rw [← Category.assoc f.hom.hom.hom.left, hπ, ← Category.assoc s]
  exact congrArg (· ≫ e.hom.hom.hom.left)
    (Spec.map_comp (CommRingCat.ofHom i.toRingHom) (CommRingCat.ofHom p.toRingHom)).symm

private theorem coordinateBasePoint_twist (d : PinnedOrbitDescent F K) (R : TestAlgebra K)
    (p : extendedHopf K (coordinateAlgebra d.G) →ₐ[K] R) :
    ((groupPointsFunctor K).map (d.trivialization (extendedGroupIso K)).hom).app R
        (coordinateBasePoint d.G R p) =
      coordinateBasePoint d.P.pair.G R (p.comp d.descent.groupIso.hom.hom.toAlgHom) := by
  let e := extendedCoordinateIso (K := K) d.G
  let f := extendedCoordinateIso (K := K) d.P.pair.G
  let h := (hopfSpec (CommRingCat.of K)).mapIso d.descent.groupIso.op
  let a := (hopfSpecPointIso (extendedHopf K (coordinateAlgebra d.G))).hom.app R (WithConv.toConv p)
  have he : d.trivialization (extendedGroupIso K) = e.symm ≪≫ h ≪≫ f := by
    simp [e, f, h, PinnedOrbitDescent.trivialization, extendedCoordinateIso]
  rw [he]
  change ((a : GroupPoints _ R) ≫ e.hom.hom.hom) ≫
    (e.symm ≪≫ h ≪≫ f).hom.hom.hom = _
  have hgf : e.hom ≫ (e.symm ≪≫ h ≪≫ f).hom = h.hom ≫ f.hom := by simp
  have hg := (Grp.forget (SchemeOver K)).congr_map hgf
  simp only [Grp.forget_map, Grp.comp_hom_hom] at hg
  rw [Category.assoc, hg, ← Category.assoc]
  apply congrArg (· ≫ f.hom.hom.hom)
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom d.descent.groupIso.hom.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom p.toRingHom)).symm

/-- Evaluation of the scalar tensor algebra along its coefficient field. -/
private def tensorEvaluation (R : TestAlgebra K) :
    tensorPointAlgebra K ((restrictTestAlgebra F K).obj R) ⟶ (restrictTestAlgebra F K).obj R := by
  let R₀ := (restrictTestAlgebra F K).obj R
  letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
  letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
  let a : K ⊗[F] R₀ →ₐ[K] R₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId K R₀) (AlgHom.id F R₀) (fun _ _ => Commute.all _ _)
  let b : K ⊗[F] R₀ →ₐ[F] R₀ := a.restrictScalars F
  exact @CommAlgCat.ofHom F _ (K ⊗[F] R₀) R₀ _ _ _ (inferInstance : Algebra F R₀) b

private theorem tensorEvaluation_tmul (R : TestAlgebra K) (a : K)
    (b : (restrictTestAlgebra F K).obj R) :
    (tensorEvaluation (F := F) R).hom (a ⊗ₜ[F] b) = algebraMap K R a * b := rfl

private theorem liftedSplitPoint_specialize (d : PinnedOrbitDescent F K) (R : TestAlgebra K)
    (x : GroupPoints ((groupBaseChange F K).obj d.G.val) R) :
    let R₀ := (restrictTestAlgebra F K).obj R
    baseChangePoint F K d.P.pair.G.val.X R
      (((groupPointsFunctor K).map (d.trivialization (extendedGroupIso K)).hom).app R x) =
      mapPoints (tensorEvaluation R)
        (liftedSplitPoint d R₀ (baseChangePoint F K d.G.val.X R x)) := by
  let R₀ := (restrictTestAlgebra F K).obj R
  letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
  letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨p, rfl⟩ := (coordinateBasePoint_bijective d.G R).2 x
  rw [coordinateBasePoint_twist, coordinateBasePoint_restrict, coordinateBasePoint_restrict]
  let w := (coordinatePointIso d.G).app R₀
  let p₀ : extendedHopf K (coordinateAlgebra d.G) →ₐ[K] R₀ := p
  let a : coordinateAlgebra d.G →ₐ[F] R₀ := (restrictConvolution (WithConv.toConv p₀)).ofConv
  let q := liftedCoordinatePoint d R₀ a
  change (coordinatePointIso d.P.pair.G).hom.app R₀ (restrictConvolution (WithConv.toConv
    (p₀.comp d.descent.groupIso.hom.hom.toAlgHom))) =
    mapPoints (tensorEvaluation R) (liftedSplitPoint d R₀ (w.hom (WithConv.toConv a)))
  have hq (y : GroupPoints d.G.val R₀) :
      liftedSplitPoint d R₀ y = (coordinatePointIso d.P.pair.G).hom.app (tensorPointAlgebra K R₀)
        (WithConv.toConv (restrictExtendedPoint R₀ (liftedCoordinatePoint d R₀ (w.inv y).ofConv))) := rfl
  rw [hq, GrpCat.inv_hom_apply]
  have hz := (coordinatePointIso d.P.pair.G).hom.naturality_apply (tensorEvaluation R)
    (WithConv.toConv (restrictExtendedPoint R₀ q))
  change (coordinatePointIso d.P.pair.G).hom.app R₀ (WithConv.toConv
    ((tensorEvaluation R).hom.comp (restrictExtendedPoint R₀ q))) =
      mapPoints (tensorEvaluation R) _ at hz
  rw [← hz]
  congr 2
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro z
  change p (d.descent.groupIso.hom.hom (1 ⊗ₜ[F] z)) =
    (tensorEvaluation R).hom ((Algebra.TensorProduct.map (AlgHom.id K K) a)
      (d.descent.groupIso.hom.hom (1 ⊗ₜ[F] z)))
  generalize d.descent.groupIso.hom.hom (1 ⊗ₜ[F] z) = b
  induction b using TensorProduct.inductionOn with
  | tmul t g =>
    change p (t ⊗ₜ[F] g) = (tensorEvaluation R).hom (t ⊗ₜ[F] a g)
    rw [tensorEvaluation_tmul]
    have h : (t ⊗ₜ[F] g : K ⊗[F] coordinateAlgebra d.G) =
        algebraMap K (extendedHopf K (coordinateAlgebra d.G)) t * (1 ⊗ₜ[F] g) := by
      change _ = (t ⊗ₜ[F] (1 : coordinateAlgebra d.G)) * (1 ⊗ₜ[F] g)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, AlgHom.commutes]
    rfl
  | add u v hu hv => simp only [map_add, hu, hv]

end OrbitDescentPoints

section MatrixOrbitComparison

set_option backward.isDefEq.respectTransparency false

open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (PinnedIso SimpleRoot PinnedGroup transportCharacter)
open Specs.RootGroups (rootPoint)
open Specs.AutomorphismSequence (forgetPinning)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private extendedGroupIso extendedSpecIso_hom_fst from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private fixedFieldTensor_injective fixedFieldTensor_natural
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem eq_one_or_rev (s : Equiv.Perm (Fin 2)) :
    s = 1 ∨ s = Fin.revPerm := by
  by_cases hs : s 0 = 0
  · exact Or.inl (permFinTwo_eq_one_of_fixed hs)
  · right
    have h₀ : s 0 = 1 := by
      obtain hs' := Fin.eq_zero_or_eq_succ (s 0)
      rcases hs' with hz | ⟨j, hj⟩
      · contradiction
      · have : j = 0 := Subsingleton.elim _ _
        simpa [this] using hj
    have h₁ : s 1 = 0 := by
      obtain hs' := Fin.eq_zero_or_eq_succ (s 1)
      rcases hs' with hz | ⟨j, hj⟩
      · exact hz
      · have : j = 0 := Subsingleton.elim _ _
        have h₁' : s 1 = 1 := by simpa [this] using hj
        exact False.elim ((by decide : (0 : Fin 2) ≠ 1) (s.injective (h₀.trans h₁'.symm)))
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h₀
    · exact h₁

private theorem labelledAction_apply (d : PinnedOrbitDescent F K)
    (j : Fin 2 ≃ SimpleRoot d.P.pair) (σ : Gal(K/F)) (i : Fin 2) :
    j (d.adjacentAction j σ i) = d.action σ (j i) := j.apply_symm_apply _

private theorem labelledAction_transitive (d : PinnedOrbitDescent F K)
    (j : Fin 2 ≃ SimpleRoot d.P.pair) (i l : Fin 2) :
    ∃ σ, d.adjacentAction j σ i = l := by
  obtain ⟨σ, hσ⟩ := d.transitive (j i) (j l)
  exact ⟨σ, j.injective ((labelledAction_apply d j σ i).trans hσ)⟩

private theorem labelledAction_ker (d : PinnedOrbitDescent F K)
    (j : Fin 2 ≃ SimpleRoot d.P.pair) : (d.adjacentAction j).ker = d.action.ker := by
  ext σ
  change j.symm.permCongrHom (d.action σ) = 1 ↔ d.action σ = 1
  rw [← map_one j.symm.permCongrHom]
  exact j.symm.permCongrHom.injective.eq_iff

private abbrev verticesOfDatum (d : PinnedOrbitDescent F K) :
    letI := d.D.comm
    SimpleRoot d.P.pair ≃ d.D.base.support := by
  letI := d.D.comm
  exact Equiv.subtypeEquivRight (fun a => (d.D.simple_iff a).symm)

private def adjacentMatrixPoint (d : PinnedOrbitDescent F K)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearThreePoints F)
    (R : TestAlgebra F) : GroupPoints d.G.val R →* SL₃ (K ⊗[F] R) :=
  (m.hom.app (tensorPointAlgebra K R)).hom.comp (liftedSplitPoint d R)

private theorem adjacentMatrixPoint_natural (d : PinnedOrbitDescent F K)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearThreePoints F)
    {R S : TestAlgebra F} (f : R ⟶ S) (x : GroupPoints d.G.val R) :
    adjacentMatrixPoint d m S (mapPoints f x) =
      SpecialLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K K) f.hom).toRingHom
        (adjacentMatrixPoint d m R x) := by
  change m.hom.app (tensorPointAlgebra K S) (liftedSplitPoint d S (mapPoints f x)) = _
  rw [liftedSplitPoint_natural]
  exact m.hom.naturality_apply (tensorPointMap K f) (liftedSplitPoint d R x)

private theorem adjacentMatrixPoint_range [IsGalois F K]
    (d : PinnedOrbitDescent F K) (j : Fin 2 ≃ SimpleRoot d.P.pair)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearThreePoints F)
    (hm : ∀ (swap : Bool) (b : PinnedIso d.P d.P),
      (∀ i, transportCharacter b.torus (j i).val.val =
        (j (adjacentPermutation swap i)).val.val) →
      ∀ (S : TestAlgebra F) (x : GroupPoints d.P.pair.G.val S),
        m.hom.app S (x ≫ b.group.hom.hom.hom) =
          if swap then hyperbolicDual (m.hom.app S x) else m.hom.app S x)
    (R : TestAlgebra F) :
    Function.Injective (adjacentMatrixPoint d m R) ∧
      Set.range (adjacentMatrixPoint d m R) = (unitaryOrbitMatrices (d.adjacentAction j) R : Set _) := by
  classical
  let ρ := d.adjacentAction j
  let S := tensorPointAlgebra K R
  let e := (m.app S).groupIsoToMulEquiv
  have he := liftedSplitPoint_range d R
  refine ⟨e.injective.comp he.1, ?_⟩
  ext y
  let x := e.symm y
  have hx : m.hom.app S x = y := e.apply_symm_apply y
  have hmem : y ∈ Set.range (adjacentMatrixPoint d m R) ↔ x ∈ Set.range (liftedSplitPoint d R) := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, e.injective (ha.trans hx.symm)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (congrArg e ha).trans hx⟩
  rw [hmem, he.2]
  change (∀ σ, _) ↔ ∀ σ, SpecialLinearGroup.map (coefficientRingMap R σ) y =
    if ρ σ = 1 then y else hyperbolicDual y
  refine forall_congr' fun σ => ?_
  let b := (d.lift (d.descent.outer σ⁻¹)).asIso.hom
  have hb : (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv =
      b.group.hom := by
    have hi : d.lift (d.descent.outer σ⁻¹) = (d.lift (d.descent.outer σ))⁻¹ := by
      rw [map_inv, map_inv]
    change _ = (Functor.mapAut d.P (forgetPinning (A := d.A))
      (d.lift (d.descent.outer σ⁻¹))).asIso.hom
    rw [hi, map_inv]
    rfl
  let s := decide (ρ σ ≠ 1)
  have hs (i : Fin 2) : ρ σ⁻¹ i = adjacentPermutation s i := by
    rcases eq_one_or_rev (ρ σ) with h | h
    · simp [ρ, s, h, adjacentPermutation]
    · have hne : ρ σ ≠ 1 := h ▸ (by decide : Fin.revPerm (n := 2) ≠ 1)
      rw [map_inv, h]
      change Fin.revPerm.symm i = adjacentPermutation s i
      simp [s, hne, adjacentPermutation, Fin.revPerm]
  have hpin (i : Fin 2) : transportCharacter b.torus (j i).val.val =
      (j (adjacentPermutation s i)).val.val := by
    change transportCharacter (d.lift (d.descent.outer σ⁻¹)).asIso.hom.torus (j i).val.val = _
    rw [d.action_eq, ← labelledAction_apply, hs]
  have hn := m.hom.naturality_apply (pointCoefficient K R σ) x
  change m.hom.app S (mapPoints (pointCoefficient K R σ) x) =
    SpecialLinearGroup.map (coefficientRingMap R σ) (m.hom.app S x) at hn
  dsimp only
  rw [hb]
  change (x ≫ b.group.hom.hom.hom = mapPoints (pointCoefficient K R σ) x) ↔ _
  have hh := e.injective.eq_iff (a := x ≫ b.group.hom.hom.hom)
    (b := mapPoints (pointCoefficient K R σ) x)
  refine hh.symm.trans ?_
  change (m.hom.app S (x ≫ b.group.hom.hom.hom) =
    m.hom.app S (mapPoints (pointCoefficient K R σ) x)) ↔ _
  rw [hm s b hpin S x, hn, hx, eq_comm]
  by_cases h : ρ σ = 1
  · simp [s, h]
  · simp [s, h]
    rfl

/-- Point embeddings into the same functor with equal images determine a
natural isomorphism with the same composites into that functor. -/
private theorem pointIso_of_equal_ranges {L M N : TestAlgebra F ⥤ GrpCat.{u}}
    (a : L ⟶ N) (b : M ⟶ N)
    (ha : ∀ R, Function.Injective (a.app R)) (hb : ∀ R, Function.Injective (b.app R))
    (h : ∀ R, Set.range (a.app R) = Set.range (b.app R)) :
    ∃ e : L ≅ M, e.hom ≫ b = a := by
  classical
  have he (R : TestAlgebra F) (x : L.obj R) : ∃ y : M.obj R, b.app R y = a.app R x := by
    have hm : a.app R x ∈ Set.range (a.app R) := ⟨x, rfl⟩
    rw [h] at hm
    exact hm
  choose e he using he
  let em (R : TestAlgebra F) : L.obj R →* M.obj R :=
    { toFun := e R
      map_one' := by
        apply hb R
        change b.app R (e R 1) = b.app R (1 : M.obj R)
        rw [he, map_one, map_one]
      map_mul' := by
        intro x y
        apply hb R
        rw [he, map_mul, map_mul, he, he] }
  let isoHom : L ⟶ M :=
    { app := fun R => GrpCat.ofHom (em R)
      naturality := by
        intros R S f
        apply GrpCat.ext
        intro x
        apply hb S
        change b.app S (e S (L.map f x)) = b.app S (M.map f (e R x))
        rw [he, a.naturality_apply, b.naturality_apply, he] }
  have hη (R : TestAlgebra F) : Function.Bijective (isoHom.app R) := by
    constructor
    · intro x y hxy
      apply ha R
      rw [← he, ← he]
      exact congrArg (b.app R) hxy
    · intro y
      have hy : b.app R y ∈ Set.range (a.app R) := (h R).symm ▸ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, hb R ((he R x).trans hx)⟩
  letI (R : TestAlgebra F) : IsIso (isoHom.app R) :=
    (MulEquiv.ofBijective (isoHom.app R).hom (hη R)).toGrpIso.isIso_hom
  letI : IsIso isoHom := NatIso.isIso_of_isIso_app isoHom
  refine ⟨asIso isoHom, ?_⟩
  ext R x
  exact he R x

private def tensorMatrixPoints (K : Type u) [Field K] [Algebra F K] :
    TestAlgebra F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (SL₃ (K ⊗[F] R))
  map f := GrpCat.ofHom (SpecialLinearGroup.map
    (Algebra.TensorProduct.map (AlgHom.id K K) f.hom).toRingHom)
  map_id R := by
    ext g i j
    change (Algebra.TensorProduct.map (AlgHom.id K K) (AlgHom.id F R)) (g.val i j) = _
    rw [Algebra.TensorProduct.map_id]
    rfl
  map_comp f g := by
    ext x i j
    change (Algebra.TensorProduct.map (AlgHom.id K K) (g.hom.comp f.hom)) (x.val i j) = 
      (Algebra.TensorProduct.map (AlgHom.id K K) g.hom)
        ((Algebra.TensorProduct.map (AlgHom.id K K) f.hom) (x.val i j))
    generalize x.val i j = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add a b ha hb => simp only [map_add, ha, hb]

private def adjacentPointEmbedding (d : PinnedOrbitDescent F K)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearThreePoints F) :
    (groupPointsFunctor F).obj d.G.val ⟶ tensorMatrixPoints K where
  app R := GrpCat.ofHom (adjacentMatrixPoint d m R)
  naturality {R S} f := by
    apply GrpCat.ext
    exact adjacentMatrixPoint_natural d m f

private def unitaryPointEmbedding {J : Subgroup Gal(K/F)} {W : AffineAlgebraicGroup F}
    (U : ClosedSubgroup W.val)
    (m : (groupPointsFunctor F).obj W.val ≅
      extendScalars F (IntermediateField.fixedField J) ⋙
        specialLinearThreePoints (IntermediateField.fixedField J)) :
    (groupPointsFunctor F).obj U.group ⟶ tensorMatrixPoints K where
  app R := GrpCat.ofHom ((SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom).comp
    ((m.hom.app R).hom.comp (((groupPointsFunctor F).map U.inclusion).app R).hom))
  naturality {R S} f := by
    apply GrpCat.ext
    intro p
    let x : GroupPoints U.group R := p
    let E := IntermediateField.fixedField J
    let q : SL₃ (R ⊗[F] E) := m.hom.app R (x ≫ U.inclusion.hom.hom)
    have hn := m.hom.naturality_apply f (show GroupPoints W.val R from x ≫ U.inclusion.hom.hom)
    change m.hom.app S ((mapPoints f x) ≫ U.inclusion.hom.hom) =
      SpecialLinearGroup.map (Algebra.TensorProduct.map f.hom (AlgHom.id F E)).toRingHom q at hn
    change SpecialLinearGroup.map (orbitScalarEmbedding S J).toRingHom
      (m.hom.app S ((mapPoints f x) ≫ U.inclusion.hom.hom)) =
      SpecialLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K K) f.hom).toRingHom
        (SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom q)
    rw [hn]
    apply Subtype.ext
    ext i j
    exact fixedFieldTensor_natural f J (q.val i j)

end MatrixOrbitComparison


section DescendedSubgroupSections

set_option backward.isDefEq.respectTransparency false

open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AdjointCocharacters (coordinateHopfMap)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
local notation "coordinateAlgebra" => Specs.AdjointCocharacters.coordinateHopf
open private coordinateHopfMap_surjective from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

set_option maxHeartbeats 700000 in
private theorem coordinatePoint_mem_subgroup
    (G : AffineAlgebraicGroup F) (H : ClosedSubgroup G.val)
    (R : TestAlgebra F) (p : coordinateAlgebra G →ₐ[F] R) :
    (coordinatePointIso G).hom.app R (WithConv.toConv p) ∈
        SubgroupSections H ((testSpec F).obj (Opposite.op R)) ↔
      ∃ q : coordinateAlgebra (closedSubgroupAlgebraicGroup H) →ₐ[F] R,
        q.comp (coordinateHopfMap (G := closedSubgroupAlgebraicGroup H)
          (H := G) H.inclusion).hom.toAlgHom = p := by
  let A := closedSubgroupAlgebraicGroup H
  let h := coordinateHopfMap (G := A) (H := G) H.inclusion
  let V := (coordinatePointIso G).app R
  let U := (coordinatePointIso A).app R
  change (∃ x : GroupPoints H.group R,
    ((groupPointsFunctor F).map H.inclusion).app R x = V.hom (WithConv.toConv p)) ↔
    ∃ q : coordinateAlgebra A →ₐ[F] R, q.comp h.hom.toAlgHom = p
  constructor
  · rintro ⟨x, hx⟩
    let q := (U.inv x).ofConv
    have hq : U.hom (WithConv.toConv q) = x := GrpCat.hom_inv_apply U x
    use q
    have he := coordinatePointIso_comp (G := A) (H := G) H.inclusion R q
    have hp' : V.hom (WithConv.toConv (q.comp h.hom.toAlgHom)) = V.hom (WithConv.toConv p) :=
      he.trans (congrArg (((groupPointsFunctor F).map H.inclusion).app R) hq |>.trans hx)
    exact WithConv.toConv_injective (V.groupIsoToMulEquiv.injective hp')
  · rintro ⟨q, hq⟩
    refine ⟨U.hom (WithConv.toConv q), ?_⟩
    have he := coordinatePointIso_comp (G := A) (H := G) H.inclusion R q
    change V.hom (WithConv.toConv (q.comp h.hom.toAlgHom)) = _ at he
    exact he.symm.trans (congrArg (fun a => V.hom (WithConv.toConv a)) hq)

/-- A point factors through a closed subgroup if and only if its scalar
extension does so. The reverse direction uses injectivity of the scalar map. -/
private theorem extendCoordinatePoint_factors (R : TestAlgebra F) {A B : HopfAlgebraCategory F}
    (b : A ⟶ B) (hb : Function.Surjective b.hom) (p : A →ₐ[F] R) :
    let extP := Algebra.TensorProduct.map (AlgHom.id K K) p
    (∃ q : extendedHopf K B →ₐ[K] K ⊗[F] R,
      q.comp (extendedHopfMap K b).hom.toAlgHom = extP) ↔
    ∃ q : B →ₐ[F] R, q.comp b.hom.toAlgHom = p := by
  dsimp only
  constructor
  · rintro ⟨q, hq⟩
    have hker : RingHom.ker b.hom.toAlgHom.toRingHom ≤ RingHom.ker p.toRingHom := by
      intro x hx
      change p x = 0
      change b.hom x = 0 at hx
      apply (Algebra.TensorProduct.includeRight_injective (B := R) (algebraMap F K).injective)
      have he := DFunLike.congr_fun hq (1 ⊗ₜ[F] x)
      change q ((1 : K) ⊗ₜ[F] b.hom x) = (1 : K) ⊗ₜ[F] p x at he
      rw [hx, TensorProduct.tmul_zero, map_zero] at he
      exact he.symm.trans (map_zero _).symm
    refine ⟨AlgHom.liftOfSurjective b.hom.toAlgHom hb p hker, ?_⟩
    exact AlgHom.liftOfSurjective_comp _ _ _ _
  · rintro ⟨q, hq⟩
    refine ⟨Algebra.TensorProduct.map (AlgHom.id K K) q, ?_⟩
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro c
    change (1 : K) ⊗ₜ[F] q (b.hom c) = (1 : K) ⊗ₜ[F] p c
    exact congrArg ((1 : K) ⊗ₜ[F] ·) (DFunLike.congr_fun hq c)

private theorem restrictExtendedPoint_factors (R : TestAlgebra F) {A B : HopfAlgebraCategory F}
    (b : A ⟶ B) (p : extendedHopf K A →ₐ[K] K ⊗[F] R) :
    (∃ q : B →ₐ[F] K ⊗[F] R, q.comp b.hom.toAlgHom = restrictExtendedPoint R p) ↔
    ∃ q : extendedHopf K B →ₐ[K] K ⊗[F] R, q.comp (extendedHopfMap K b).hom.toAlgHom = p := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨q', he⟩ := (restrictExtendedPointBijective (K := K) (C := B) R).2 q
    refine ⟨q', (restrictExtendedPointBijective (K := K) (C := A) R).1 ?_⟩
    change (restrictExtendedPoint R q').comp b.hom.toAlgHom = _
    rw [he, hq]
  · rintro ⟨q, hq⟩
    refine ⟨restrictExtendedPoint R q, ?_⟩
    change restrictExtendedPoint R (q.comp (extendedHopfMap K b).hom.toAlgHom) = _
    rw [hq]

private theorem factors_through_isomorphic_quotients
    {A B C D : HopfAlgebraCategory K}
    (h : A ≅ B) (e : C ≅ D) (i : A ⟶ C) (j : B ⟶ D)
    (he : h.hom ≫ j = i ≫ e.hom) (S : TestAlgebra K) (p : B →ₐ[K] S) :
    (∃ q : C →ₐ[K] S, q.comp i.hom.toAlgHom = p.comp h.hom.hom.toAlgHom) ↔
    ∃ q : D →ₐ[K] S, q.comp j.hom.toAlgHom = p := by
  have hc (a : A) : j.hom (h.hom.hom a) = e.hom.hom (i.hom a) :=
    ConcreteCategory.congr_hom he a
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q.comp e.inv.hom.toAlgHom, AlgHom.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ : ∃ a, h.hom.hom a = b :=
      ⟨h.inv.hom b, ConcreteCategory.congr_hom h.inv_hom_id b⟩
    change q (e.inv.hom (j.hom (h.hom.hom a))) = p (h.hom.hom a)
    rw [hc, show e.inv.hom (e.hom.hom (i.hom a)) = i.hom a from
      ConcreteCategory.congr_hom e.hom_inv_id _]
    exact DFunLike.congr_fun hq a
  · rintro ⟨q, hq⟩
    refine ⟨q.comp e.hom.hom.toAlgHom, AlgHom.ext fun a => ?_⟩
    change q (e.hom.hom (i.hom a)) = p (h.hom.hom a)
    rw [← hc]
    exact DFunLike.congr_fun hq (h.hom.hom a)

set_option maxHeartbeats 1600000 in
private theorem liftedSplitPoint_mem_subgroup (d : PinnedOrbitDescent F K)
    (H : ClosedSubgroup d.G.val) (Q : ClosedSubgroup d.P.pair.G.val)
    (e : extendedHopf K (coordinateAlgebra (closedSubgroupAlgebraicGroup Q)) ≅
      extendedHopf K (coordinateAlgebra (closedSubgroupAlgebraicGroup H)))
    (he : d.descent.groupIso.hom ≫ extendedHopfMap K
        (coordinateHopfMap (G := closedSubgroupAlgebraicGroup H) (H := d.G) H.inclusion) =
      extendedHopfMap K
        (coordinateHopfMap (G := closedSubgroupAlgebraicGroup Q) (H := d.P.pair.G) Q.inclusion) ≫ e.hom)
    (R : TestAlgebra F) (x : GroupPoints d.G.val R) :
    liftedSplitPoint d R x ∈ SubgroupSections Q ((testSpec F).obj (Opposite.op (tensorPointAlgebra K R))) ↔
      x ∈ SubgroupSections H ((testSpec F).obj (Opposite.op R)) := by
  let j := coordinateHopfMap (G := closedSubgroupAlgebraicGroup H) (H := d.G) H.inclusion
  let i := coordinateHopfMap (G := closedSubgroupAlgebraicGroup Q) (H := d.P.pair.G) Q.inclusion
  let p := ((coordinatePointIso d.G).inv.app R x).ofConv
  let v := (coordinatePointIso d.G).app R
  let h := d.descent.groupIso
  let extP := Algebra.TensorProduct.map (AlgHom.id K K) p
  let r := liftedCoordinatePoint d R p
  have hx : v.hom (WithConv.toConv p) = x := GrpCat.hom_inv_apply v x
  have hy : liftedSplitPoint d R x = (coordinatePointIso d.P.pair.G).hom.app (tensorPointAlgebra K R)
      (WithConv.toConv (restrictExtendedPoint R r)) := rfl
  have hright := coordinatePoint_mem_subgroup d.G H R p
  have hleft := coordinatePoint_mem_subgroup d.P.pair.G Q (tensorPointAlgebra K R)
    (restrictExtendedPoint R r)
  have hz : Function.Surjective j.hom :=
    coordinateHopfMap_surjective (G := closedSubgroupAlgebraicGroup H) (H := d.G)
      H.inclusion H.isClosedImmersion
  have hfac := extendCoordinatePoint_factors (K := K) R j hz p
  let S := CommAlgCat.of K (K ⊗[F] R)
  have hf := factors_through_isomorphic_quotients h e (extendedHopfMap K i)
    (extendedHopfMap K j) he S extP
  have hi := restrictExtendedPoint_factors R i r
  have hp : x ∈ SubgroupSections H ((testSpec F).obj (Opposite.op R)) ↔
      ∃ q : coordinateAlgebra (closedSubgroupAlgebraicGroup H) →ₐ[F] R,
        q.comp j.hom.toAlgHom = p := hx ▸ hright
  have hq := (hleft.trans hi).trans hf
  have ho := hq.trans (hfac.trans hp.symm)
  exact hy.symm ▸ ho


end DescendedSubgroupSections

section AdjacentOrbitModel

set_option backward.isDefEq.respectTransparency false

open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SimpleRoot)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open private extendedGroupIso extendedSpecIso_hom_fst from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private baseChangePointIso groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private fixedFieldTensor_injective from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem unitaryPointEmbedding_injective {J : Subgroup Gal(K/F)}
    {W : AffineAlgebraicGroup F} (U : ClosedSubgroup W.val)
    (m : (groupPointsFunctor F).obj W.val ≅
      extendScalars F (IntermediateField.fixedField J) ⋙
        specialLinearThreePoints (IntermediateField.fixedField J))
    (R : TestAlgebra F) :
    Function.Injective ((unitaryPointEmbedding U m).app R) := by
  letI := U.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  let e := (m.app R).groupIsoToMulEquiv
  intro p q h
  apply (cancel_mono U.inclusion.hom.hom).mp
  apply e.injective
  apply matrix_map_injective (orbitScalarEmbedding R J).toRingHom (fixedFieldTensor_injective R J)
  exact h

private theorem unitaryPointEmbedding_range [FiniteDimensional F K] [IsGalois F K]
    (ρ : Gal(K/F) →* Equiv.Perm (Fin 2)) (hρ : ∀ j, ∃ σ, ρ σ 0 = j)
    [Algebra.IsQuadraticExtension F (orbitField ρ 0)] [Algebra.IsSeparable F (orbitField ρ 0)]
    (R : TestAlgebra F) {W : AffineAlgebraicGroup F} (U : ClosedSubgroup W.val)
    (m : (groupPointsFunctor F).obj W.val ≅
      extendScalars F (orbitField ρ 0) ⋙ specialLinearThreePoints (orbitField ρ 0))
    (hU : RepresentsHyperbolicUnitary (E := orbitField ρ 0) U m) :
    letI := MulAction.compHom (Fin 2) ρ
    let J := MulAction.stabilizer Gal(K/F) (0 : Fin 2)
    Set.range (fun x : GroupPoints U.group R => (unitaryPointEmbedding (J := J) U m).app R x) =
      (unitaryOrbitMatrices ρ R : Set (SL₃ (K ⊗[F] R))) := by
  classical
  letI := MulAction.compHom (Fin 2) ρ
  let J := MulAction.stabilizer Gal(K/F) (0 : Fin 2)
  let E := orbitField ρ 0
  obtain ⟨_, _, M, e, hM, he, _⟩ := quadraticOrbitMatrixPoints ρ 0 hρ R
  let emb : SL₃ (R ⊗[F] E) →* SL₃ (K ⊗[F] R) :=
    SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    let x : GroupPoints U.group R := p
    let a : SL₃ (R ⊗[F] E) := m.hom.app R (x ≫ U.inclusion.hom.hom)
    have h := (hM a).mpr ((hU R a).mpr ⟨x, rfl⟩)
    change emb a ∈ unitaryOrbitMatrices ρ R
    rw [← he ⟨a, h⟩]
    exact (e ⟨a, h⟩).property
  · intro hg
    obtain ⟨a, ha⟩ := e.surjective ⟨g, hg⟩
    obtain ⟨p, hp⟩ := (hU R a.val).mp ((hM _).mp a.property)
    refine ⟨p, ?_⟩
    change emb (m.hom.app R (p ≫ U.inclusion.hom.hom)) = g
    exact (congrArg emb hp).trans ((he a).symm.trans (congrArg Subtype.val ha))

private theorem tensorEvaluation_orbitEmbedding (R : TestAlgebra K) (J : Subgroup Gal(K/F)) :
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    (tensorEvaluation R).hom.toRingHom.comp (orbitScalarEmbedding R₀ J).toRingHom =
      (Algebra.TensorProduct.lift (AlgHom.id F R₀)
        (((Algebra.ofId K R₀).restrictScalars F).comp (IntermediateField.val (IntermediateField.fixedField J)))
          (fun _ _ => Commute.all _ _)).toRingHom := by
  let R₀ := (restrictTestAlgebra F K).obj R
  letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
  letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
  let E := IntermediateField.fixedField J
  let e := (tensorEvaluation R).hom.toRingHom.comp (orbitScalarEmbedding R₀ J).toRingHom
  let f : R₀ ⊗[F] E →ₐ[F] R₀ :=
    Algebra.TensorProduct.lift (AlgHom.id F R₀)
      (((Algebra.ofId K R₀).restrictScalars F).comp E.val) (fun _ _ => Commute.all _ _)
  change e = f.toRingHom
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a y =>
    change (tensorEvaluation R).hom (y.val ⊗ₜ[F] a) = a * algebraMap K R y.val
    rw [tensorEvaluation_tmul, mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]

set_option maxHeartbeats 3200000 in
/-- The scheme isomorphism with the hyperbolic special unitary group, with
its pinned split comparison over the specified Galois field. -/
private theorem adjacentOrbitComparison : AdjacentOrbitComparison.{u} {MatrixMark.torus, MatrixMark.positiveBorel} := by
  classical
  intro F K _ _ _ _ _ d j hc
  letI := d.D.comm
  let ρ := d.adjacentAction j
  letI := MulAction.compHom (Fin 2) ρ
  let J := MulAction.stabilizer Gal(K/F) (0 : Fin 2)
  let E := orbitField ρ 0
  have htrans := labelledAction_transitive d j 0
  obtain ⟨hE, hq, hs, _⟩ := quadraticOrbitField ρ 0 htrans
  letI : Algebra.IsQuadraticExtension F E := hq
  letI : Algebra.IsSeparable F E := hs
  let j' := j.trans (verticesOfDatum d)
  have hc' (i l : Fin 2) : RootData.integralCartan d.D.datum.rootDatum d.D.base (j' i) (j' l) =
      if i = l then 2 else -1 := hc i l
  obtain ⟨a, htor, hborel, hcoords, ha⟩ := adjacentPinnedAutomorphisms
    d.P d.D d.splitSemisimple d.splitSimplyConnected j' hc'
  have hap (swap : Bool) (b : Specs.Pinning.PinnedIso d.P d.P)
      (hb : ∀ i, Specs.Pinning.transportCharacter b.torus (j i).val.val =
        (j (adjacentPermutation swap i)).val.val) :
      ∀ (S : TestAlgebra F) (x : GroupPoints d.P.pair.G.val S),
        a.hom.app S (x ≫ b.group.hom.hom.hom) = if swap then hyperbolicDual (a.hom.app S x)
          else a.hom.app S x :=
    ha swap b hb
  obtain ⟨W, U, m, hU⟩ := hyperbolicUnitaryModel F E
  let A := adjacentPointEmbedding d a
  let B := unitaryPointEmbedding (J := J) U m
  have hA (R : TestAlgebra F) := adjacentMatrixPoint_range d j a hap R
  obtain ⟨e, he⟩ := pointIso_of_equal_ranges A B (fun R => (hA R).1)
    (unitaryPointEmbedding_injective U m)
    (fun R => (hA R).2.trans (unitaryPointEmbedding_range ρ htrans R U m hU).symm)
  letI : IsAffine d.G.val.X.left := d.G.property.1
  letI : IsClosedImmersion U.inclusion.hom.hom.left := U.isClosedImmersion
  letI : IsAffine W.val.X.left := W.property.1
  letI : IsAffine U.group.X.left := isAffine_of_isAffineHom U.inclusion.hom.hom.left
  let f := groupIsoOfPointIso e
  have hf : (groupPointsFunctor F).map f.hom = e.hom :=
    (groupHomEquiv d.G.val U.group inferInstance).apply_symm_apply e.hom
  have heval (R : TestAlgebra F) (x : GroupPoints d.G.val R) :
      SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom
        (m.hom.app R (((groupPointsFunctor F).map (f.hom ≫ U.inclusion)).app R x)) =
        adjacentMatrixPoint d a R x := by
    have h := congrArg (fun z => z.app R x) he
    rw [(groupPointsFunctor F).map_comp, hf]
    exact h
  let t := extendedGroupIso (k := F) K
  let p := baseChangePointIso (K := K) d.P.pair.G.val ≪≫
    Functor.isoWhiskerLeft (restrictTestAlgebra F K) a
  refine ⟨hq, hs, W, U, m, f, t, p, ?_, hU, extendedSpecIso_hom_fst K, ?_, ?_, ?_⟩
  · exact hE.trans (congrArg IntermediateField.fixedField (labelledAction_ker d j))
  · intro b hb R x
    have hmat := mark_map_iff (orbitScalarEmbedding R J).toRingHom
      (fixedFieldTensor_injective R J) b
      (m.hom.app R (((groupPointsFunctor F).map (f.hom ≫ U.inclusion)).app R x))
    rw [heval R x] at hmat
    refine hmat.symm.trans ?_
    rcases Set.mem_insert_iff.mp hb with h | h
    · subst b
      exact (htor (tensorPointAlgebra K R) (liftedSplitPoint d R x)).symm.trans
        (liftedSplitPoint_mem_subgroup d d.T d.P.pair.T d.descent.torusIso
          d.descent.torusComm R x)
    · have h' : b = MatrixMark.positiveBorel := Set.mem_singleton_iff.mp h
      subst b
      exact (hborel (tensorPointAlgebra K R) (liftedSplitPoint d R x)).symm.trans
        (liftedSplitPoint_mem_subgroup d d.Bpos d.P.pair.B d.descent.borelIso
          d.descent.borelComm R x)
  · intro R x
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    let x₀ := baseChangePoint F K d.G.val.X R x
    let evaluation := (tensorEvaluation (F := F) R).hom.toRingHom
    let r := m.hom.app R₀ (((groupPointsFunctor F).map (f.hom ≫ U.inclusion)).app R₀ x₀)
    change a.hom.app R₀ (baseChangePoint F K d.P.pair.G.val.X R
      (((groupPointsFunctor K).map (d.trivialization t).hom).app R x)) = _
    have hn := a.hom.naturality_apply (tensorEvaluation (F := F) R) (liftedSplitPoint d R₀ x₀)
    change a.hom.app R₀ (mapPoints (tensorEvaluation R) (liftedSplitPoint d R₀ x₀)) =
      SpecialLinearGroup.map evaluation (adjacentMatrixPoint d a R₀ x₀) at hn
    rw [liftedSplitPoint_specialize, hn]
    change SpecialLinearGroup.map evaluation (adjacentMatrixPoint d a R₀ x₀) = _
    rw [← heval R₀ x₀]
    have hh := tensorEvaluation_orbitEmbedding R J
    change SpecialLinearGroup.map evaluation (SpecialLinearGroup.map
      (orbitScalarEmbedding R₀ J).toRingHom r) = _
    apply Subtype.ext
    ext i j
    exact DFunLike.congr_fun hh (r.val i j)
  · intro R i x v
    dsimp only
    intro x' y' hx hy
    change (a.hom.app ((restrictTestAlgebra F K).obj R)
       (baseChangePoint F K d.P.pair.G.val.X R x')).val = _ ∧
        a.hom.app ((restrictTestAlgebra F K).obj R)
          (baseChangePoint F K d.P.pair.G.val.X R y') = _
    rw [hx, hy]
    exact hcoords i ((restrictTestAlgebra F K).obj R) x v


end AdjacentOrbitModel

section OrthogonalOrbitDescent

set_option backward.isDefEq.respectTransparency false

open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SimpleRoot)
open Specs.AutomorphismSequence (forgetPinning)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private fixedFieldTensor_injective fixedFieldTensor_natural
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- The point functor of the product of the labelled determinant-one factors. -/
private def specialLinearFamilyPoints (F : Type u) [Field F] (I : Type u) (n : ℕ) :
    TestAlgebra F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (I → SpecialLinearGroup (Fin n) R)
  map f := GrpCat.ofHom (MonoidHom.pi fun i =>
    (SpecialLinearGroup.map f.hom.toRingHom).comp (Pi.evalMonoidHom _ i))
  map_id _ := by
    apply GrpCat.ext
    intro x
    funext i
    exact Subtype.ext (Matrix.ext fun _ _ => rfl)
  map_comp _ _ := by
    apply GrpCat.ext
    intro x
    funext i
    exact Subtype.ext (Matrix.ext fun _ _ => rfl)

private def tensorAlgebraPoints (K : Type u) [Field K] [Algebra F K] :
    TestAlgebra F ⥤ TestAlgebra F where
  obj R := tensorPointAlgebra K R
  map f := tensorPointMap K f
  map_id R := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id K K) (AlgHom.id F R) z = z
    rw [Algebra.TensorProduct.map_id]
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change Algebra.TensorProduct.map (AlgHom.id K K) (g.hom.comp f.hom) z =
      Algebra.TensorProduct.map (AlgHom.id K K) g.hom
        (Algebra.TensorProduct.map (AlgHom.id K K) f.hom z)
    induction z using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]

/-- Map ground-field points into the labelled split factors over the
tensor product with the Galois field. -/
private def familyOrbitPoint (d : PinnedOrbitDescent F K) (n : ℕ)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearFamilyPoints F (SimpleRoot d.P.pair) n)
    (R : TestAlgebra F) :
    GroupPoints d.G.val R →* (SimpleRoot d.P.pair → SpecialLinearGroup (Fin n) (K ⊗[F] R)) :=
  (m.hom.app (tensorPointAlgebra K R)).hom.comp (liftedSplitPoint d R)

private theorem familyOrbitPoint_range [IsGalois F K]
    (d : PinnedOrbitDescent F K) (n : ℕ)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearFamilyPoints F (SimpleRoot d.P.pair) n)
    (hm : ∀ (σ : Gal(K/F)) (R : TestAlgebra F) (x : GroupPoints d.P.pair.G.val R) (j : SimpleRoot d.P.pair),
      let a := (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv
      m.hom.app R (x ≫ a.hom.hom) j = m.hom.app R x (d.action σ j))
    (R : TestAlgebra F) :
    Function.Injective (familyOrbitPoint d n m R) ∧
      Set.range (familyOrbitPoint d n m R) =
        (permutedMatrices d.action R n : Set (SimpleRoot d.P.pair → _)) := by
  let S := tensorPointAlgebra K R
  let e := (m.app S).groupIsoToMulEquiv
  have he := liftedSplitPoint_range d R
  refine ⟨e.injective.comp he.1, ?_⟩
  ext y
  let x := e.symm y
  have hx : m.hom.app S x = y := e.apply_symm_apply y
  have hmem : y ∈ Set.range (familyOrbitPoint d n m R) ↔ x ∈ Set.range (liftedSplitPoint d R) := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, e.injective (ha.trans hx.symm)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (congrArg e ha).trans hx⟩
  rw [hmem, he.2]
  change (∀ σ, _) ↔ ∀ (σ : Gal(K/F)) j,
    y (d.action σ j) = SpecialLinearGroup.map (coefficientRingMap R σ) (y j)
  apply forall_congr'
  intro σ
  let a : d.P.pair.G.val ⟶ d.P.pair.G.val :=
    (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv
  have hn := m.hom.naturality_apply (pointCoefficient K R σ) x
  change m.hom.app S (mapPoints (pointCoefficient K R σ) x) =
    (fun j => SpecialLinearGroup.map (coefficientRingMap R σ) (m.hom.app S x j)) at hn
  change (x ≫ a.hom.hom = mapPoints (pointCoefficient K R σ) x) ↔ _
  constructor
  · intro h j
    rw [← hx]
    exact (hm σ S x j).symm.trans
      (congrFun (congrArg (m.hom.app S) h) j |>.trans (congrFun hn j))
  · intro h
    apply e.injective
    funext j
    change m.hom.app S (x ≫ a.hom.hom) j = m.hom.app S (mapPoints (pointCoefficient K R σ) x) j
    rw [hm σ S x j, hn, hx]
    exact h j

private def familyOrbitEmbedding (d : PinnedOrbitDescent F K) (n : ℕ)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearFamilyPoints F (SimpleRoot d.P.pair) n)
    (i : SimpleRoot d.P.pair) :
    (groupPointsFunctor F).obj d.G.val ⟶ tensorAlgebraPoints K ⋙ specialLinearPointsOfSize n F where
  app R := GrpCat.ofHom ((Pi.evalMonoidHom _ i).comp (familyOrbitPoint d n m R))
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    change m.hom.app (tensorPointAlgebra K S) (liftedSplitPoint d S (mapPoints f x)) i = _
    rw [liftedSplitPoint_natural]
    exact congrFun (m.hom.naturality_apply (tensorPointMap K f) (liftedSplitPoint d R x)) i

private def weilMatrixEmbedding (J : Subgroup Gal(K/F)) (n : ℕ) :
    extendScalars F (IntermediateField.fixedField J) ⋙ specialLinearPointsOfSize n (IntermediateField.fixedField J)
      ⟶ tensorAlgebraPoints K ⋙ specialLinearPointsOfSize n F where
  app R := GrpCat.ofHom (SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom)
  naturality {R S} f := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    ext i j
    exact fixedFieldTensor_natural f J (x.val i j)

private theorem orbitProjection_injective (d : PinnedOrbitDescent F K) (n : ℕ)
    (i : SimpleRoot d.P.pair) (R : TestAlgebra F) :
    Function.Injective (fun x : permutedMatrices d.action R n => x.val i) := by
  intro x y h
  apply Subtype.ext
  funext j
  obtain ⟨σ, rfl⟩ := d.transitive i j
  exact (x.property σ i).trans ((congrArg (SpecialLinearGroup.map (coefficientRingMap R σ)) h).trans
    (y.property σ i).symm)

set_option maxHeartbeats 1400000 in
/-- Once the split factors are identified with their actual pinned permutation
action, the descent is the Weil restriction, by the projection at a vertex. -/
private theorem orthogonalOrbitDescent [IsGalois F K]
    [FiniteDimensional F K] (d : PinnedOrbitDescent F K) (n : ℕ)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearFamilyPoints F (SimpleRoot d.P.pair) n)
    (hm : ∀ (σ : Gal(K/F)) (R : TestAlgebra F) (x : GroupPoints d.P.pair.G.val R) (j : SimpleRoot d.P.pair),
      let a := (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv
      m.hom.app R (x ≫ a.hom.hom) j = m.hom.app R x (d.action σ j))
    (i : SimpleRoot d.P.pair) :
    let E := orbitField d.action i
    ∃ (W : AffineAlgebraicGroup F) (f : d.G.val ≅ W.val)
      (w : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearPointsOfSize n E),
      ∀ (R : TestAlgebra F) (x : GroupPoints d.G.val R),
        letI := MulAction.compHom (SimpleRoot d.P.pair) d.action
        let J := MulAction.stabilizer Gal(K/F) i
        SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom
          (w.hom.app R (((groupPointsFunctor F).map f.hom).app R x)) = familyOrbitPoint d n m R x i := by
  letI := MulAction.compHom (SimpleRoot d.P.pair) d.action
  let J := MulAction.stabilizer Gal(K/F) i
  let E := orbitField d.action i
  let C := extendScalars F E ⋙ specialLinearPointsOfSize n E
  let a := familyOrbitEmbedding d n m i
  let b := weilMatrixEmbedding J n
  have hb (R : TestAlgebra F) : Function.Injective (b.app R) :=
    matrix_map_injective _ (fixedFieldTensor_injective R J)
  have hA (R : TestAlgebra F) := familyOrbitPoint_range d n m hm R
  have ha (R : TestAlgebra F) : Function.Injective (a.app R) := by
    intro x y hxy
    have hx : familyOrbitPoint d n m R x ∈ permutedMatrices d.action R n := by
      change _ ∈ (permutedMatrices d.action R n : Set (SimpleRoot d.P.pair → SpecialLinearGroup (Fin n) (K ⊗[F] R)))
      rw [← (hA R).2]
      exact ⟨x, rfl⟩
    have hy : familyOrbitPoint d n m R y ∈ permutedMatrices d.action R n := by
      change _ ∈ (permutedMatrices d.action R n : Set (SimpleRoot d.P.pair → SpecialLinearGroup (Fin n) (K ⊗[F] R)))
      rw [← (hA R).2]
      exact ⟨y, rfl⟩
    apply (hA R).1
    have h : (⟨_, hx⟩ : permutedMatrices d.action R n) = ⟨_, hy⟩ :=
      orbitProjection_injective d n i R hxy
    exact congrArg Subtype.val h
  have heq (R : TestAlgebra F) : Set.range (a.app R) = Set.range (b.app R) := by
    obtain ⟨p, hp, _⟩ := permutedMatrixPoints d.action i (d.transitive i) n R
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      have hx : familyOrbitPoint d n m R x ∈ permutedMatrices d.action R n := by
        change _ ∈ (permutedMatrices d.action R n : Set (SimpleRoot d.P.pair → SpecialLinearGroup (Fin n) (K ⊗[F] R)))
        rw [← (hA R).2]
        exact ⟨x, rfl⟩
      exact ⟨p ⟨_, hx⟩, hp ⟨_, hx⟩⟩
    · rintro ⟨y, rfl⟩
      let x := p.symm y
      have hx : x.val ∈ Set.range (familyOrbitPoint d n m R) := by
        rw [(hA R).2]
        exact x.property
      obtain ⟨g, hg⟩ := hx
      refine ⟨g, ?_⟩
      change familyOrbitPoint d n m R g i = SpecialLinearGroup.map (orbitScalarEmbedding R J).toRingHom y
      rw [hg, ← hp x]
      exact congrArg _ (p.apply_symm_apply y)
  obtain ⟨e, he⟩ := pointIso_of_equal_ranges a b ha hb heq
  let S := StandardGroups.specialLinearGroup E (ULift.{u} (Fin n))
  let s := StandardGroups.specialLinearGroupPointsIso E (ULift.{u} (Fin n)) ≪≫
    NatIso.ofComponents (G := specialLinearPointsOfSize n E)
      (fun R => MulEquiv.toGrpIso (reindexSpecialLinear (R := R) Equiv.ulift)) (by
        intro R T h
        apply GrpCat.ext
        intro g
        exact Subtype.ext rfl)
  let W := LinearAlgebraicGroups.WeilRestriction.groupRepresentation F E S
  let w := W.2 ≪≫ Functor.isoWhiskerLeft (extendScalars F E) s
  letI : IsAffine d.G.val.X.left := d.G.property.1
  letI : IsAffine W.1.val.X.left := W.1.property.1
  let f := groupIsoOfPointIso (e ≪≫ w.symm)
  have hf : (groupPointsFunctor F).map f.hom ≫ w.hom = e.hom := by
    rw [show (groupPointsFunctor F).map f.hom = (e ≪≫ w.symm).hom from
      (groupHomEquiv d.G.val W.1.val inferInstance).apply_symm_apply _]
    simp
  refine ⟨W.1, f, w, fun R x => ?_⟩
  have h := congrArg (fun p => p.app R x) (show (((groupPointsFunctor F).map f.hom) ≫ w.hom) ≫ b = a from
    hf ▸ he)
  exact h


end OrthogonalOrbitDescent

section AdjacentSubgroups

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private unitPointHom_apply unitEquiv unitPointHom
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent


private theorem diagonalWeights {k : Type u} [Field k] (G : GroupScheme k) [IsAffine G.X.left]
    (m : (groupPointsFunctor k).obj G ≅ specialLinearThreePoints k) (c : Cocharacter G)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), MatrixMark.torus.Holds (m.hom.app R (cocharacterPoint c R t))) :
    ∃ y : Fin 3 → ℤ, ∀ (R : TestAlgebra k) (t : Rˣ),
      (m.hom.app R (cocharacterPoint c R t)).val = Matrix.diagonal (fun i => (↑(t ^ y i) : R)) := by
  let S := StandardGroups.specialLinearGroup k (ULift.{u} (Fin 3))
  let s := StandardGroups.specialLinearGroupPointsIso k (ULift.{u} (Fin 3))
  obtain ⟨T, L, M, B, D, hD, hpin, hsc⟩ :=
    RootData.SpecialLinearDatum.matrixPinnedDatum k 2 S s
  letI := S.property.1
  let a := specialLinearThreePointIso k
  let e := groupIsoOfPointIso (m ≪≫ a.symm)
  let F := groupPointsFunctor k
  have he : F.map e.hom = (m ≪≫ a.symm).hom := (groupHomEquiv G S.val inferInstance).apply_symm_apply _
  have hem (R : TestAlgebra k) (p : GroupPoints G R) :
      a.hom.app R (p ≫ e.hom.hom.hom) = m.hom.app R p := by
    have hme := congrArg (fun q => q.app R p) he
    change p ≫ e.hom.hom.hom = a.inv.app R (m.hom.app R p) at hme
    rw [hme]
    exact GrpCat.hom_inv_apply (a.app R) _
  let g := c ≫ e.hom
  have hgt (R : TestAlgebra k) (t : Rˣ) :
      cocharacterPoint g R t ∈ SubgroupSections T.subgroup ((testSpec k).obj (Opposite.op R)) := by
    apply (T.range R _).mpr
    have hh := h R t
    rw [← hem] at hh
    intro i j hij
    change (s.hom.app R (cocharacterPoint c R t ≫ e.hom.hom.hom)).val i j = 0
    exact hh i.down j.down (fun hj => hij (ULift.ext hj))
  let M₀ := specGroup (groupAlgebra k IntegerCharacters)
  let R₀ := CommAlgCat.of k (MonoidAlgebra k IntegerCharacters)
  let idPt : GroupPoints M₀ R₀ := 𝟙 M₀.X
  let u₀ := unitEquiv R₀ idPt
  have hu₀ : unitPoint R₀ u₀ = idPt := by
    rw [← unitPointHom_apply]
    exact (unitEquiv R₀).symm_apply_apply _
  have hg₀ := hgt R₀ u₀
  change (unitPoint R₀ u₀ ≫ g.hom.hom) ∈ _ at hg₀
  rw [hu₀] at hg₀
  change (𝟙 M₀.X ≫ g.hom.hom) ∈ _ at hg₀
  rw [Category.id_comp] at hg₀
  obtain ⟨q, hq⟩ : ∃ q : M₀.X ⟶ T.subgroup.group.X, q ≫ T.subgroup.inclusion.hom.hom = g.hom.hom := hg₀
  letI := T.subgroup.isClosedImmersion
  letI := isMonHom_of_comp_closed q g T.subgroup.inclusion hq
  let b : Cocharacter T.subgroup.group := Grp.homMk q
  have hb : b ≫ T.subgroup.inclusion = g := Grp.hom_ext _ _ hq
  letI := L.comm
  let y := L.cocharacters (Additive.ofMul b)
  refine ⟨y.val, fun R t => ?_⟩
  have h1 := L.cocharacterPoint_eq y R t
  rw [LinearEquiv.symm_apply_apply] at h1
  have h2 := hem R (cocharacterPoint c R t)
  rw [← h2]
  apply Matrix.ext
  intro i j
  have h3 := congrArg (fun z : Matrix (ULift.{u} (Fin 3)) _ R => z ⟨i⟩ ⟨j⟩) h1
  have ht : cocharacterPoint b R t ≫ T.subgroup.inclusion.hom.hom =
      cocharacterPoint c R t ≫ e.hom.hom.hom := by
    change unitPoint R t ≫ b.hom.hom ≫ T.subgroup.inclusion.hom.hom =
      (unitPoint R t ≫ c.hom.hom) ≫ e.hom.hom.hom
    have heq := congrArg (fun f : M₀ ⟶ S.val => f.hom.hom) hb
    simp only [Grp.comp_hom_hom] at heq
    rw [heq, Category.assoc]
    rfl
  change (s.hom.app R (cocharacterPoint b R t ≫ T.subgroup.inclusion.hom.hom)).val ⟨i⟩ ⟨j⟩ = _ at h3
  rw [ht] at h3
  exact h3.trans (by simp [Matrix.diagonal_apply])

variable {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
  [Algebra E K] [IsScalarTower F E K] [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

private theorem unitaryProjection_preserves_mark (R : TestAlgebra K) (b : MatrixMark) :
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    let f := Algebra.TensorProduct.lift (AlgHom.id F R₀)
      (((Algebra.ofId K R₀).restrictScalars F).comp (IsScalarTower.toAlgHom F E K)) (fun _ _ => Commute.all _ _)
    ∀ g : SL₃ (R₀ ⊗[F] E),
      ((g.val.map (quadraticTensorInvolution F E R₀).toRingEquiv).transpose *
        hyperbolicGram (R₀ ⊗[F] E) * g.val = hyperbolicGram (R₀ ⊗[F] E)) →
      (b.Holds (SpecialLinearGroup.map f.toRingHom g) ↔ b.Holds g) := by
  let R₀ := (restrictTestAlgebra F K).obj R
  letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
  letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra E R₀ := ((algebraMap K R₀).comp (algebraMap E K)).toAlgebra
  letI : IsScalarTower F E R₀ := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap K R₀ (algebraMap F K r) =
      algebraMap K R₀ (algebraMap E K (algebraMap F E r))
    rw [IsScalarTower.algebraMap_apply F E K]
  let f : R₀ ⊗[F] E →ₐ[F] R₀ := Algebra.TensorProduct.lift (AlgHom.id F R₀)
    (((Algebra.ofId K R₀).restrictScalars F).comp (IsScalarTower.toAlgHom F E K)) (fun _ _ => Commute.all _ _)
  change ∀ g : SL₃ (R₀ ⊗[F] E), _ → (b.Holds (SpecialLinearGroup.map f.toRingHom g) ↔ b.Holds g)
  obtain ⟨e, U, p, he, hU, hp, hmark⟩ := unitaryMarkedPoints F E R₀
  have hf : (RingHom.fst R₀ R₀).comp e.toRingEquiv.toRingHom = f.toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      change (e (a ⊗ₜ[F] x)).1 = a * algebraMap E R₀ x
      rw [he]
    | add a z ha hz => simp only [map_add, ha, hz]
  intro g hg
  let x : U := ⟨g, (hU _).mpr hg⟩
  have hx := hp x
  rw [hf] at hx
  exact (hx ▸ hmark b x)

section OppositeBorelLimits

open Specs.GeometricRadicals (IsReductive IsUnipotentRadical IsMaximalTorus IsTorus)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.RankOneFlag (SameSubgroup IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.BorelsAndChambers (contractingSubgroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition HasExtension HasLimit)
open private smooth_extend_iff from LinearAlgebraicGroups.RootData.BorelNormalizer
open private restrictSubgroup compose_restrict local_maximal_of_ambient
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupOf_mutual_iso from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private pushSubgroup radical_transport from LinearAlgebraicGroups.RootData.OrderedRootProducts

variable {k : Type u} [Field k]

private theorem section_of_subgroupOf {G : GroupScheme k} {A B : ClosedSubgroup G}
    (h : IsSubgroupOf A B) (Y : SchemeOver k) (g : Y ⟶ G.X) :
    g ∈ SubgroupSections A Y → g ∈ SubgroupSections B Y := by
  obtain ⟨f, hf⟩ := h
  rintro ⟨x, rfl⟩
  have h := congrArg (fun q : A.group ⟶ G => q.hom.hom) hf
  simp only [Grp.comp_hom_hom] at h
  refine ⟨x ≫ f.hom.hom, ?_⟩
  change (x ≫ f.hom.hom) ≫ B.inclusion.hom.hom = x ≫ A.inclusion.hom.hom
  rw [Category.assoc, h]

private theorem radicalLimitComparison
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T B : ClosedSubgroup G.val) (hB : IsKBorel B) (hT : IsMaximalTorus T)
    (hTB : IsSubgroupOf T B) (U : ClosedSubgroup B.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    ∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      (∃ c₀ : Cocharacter T.group, c₀ ≫ T.inclusion = c) ∧
      SameSubgroup B D.parabolic ∧ SameSubgroup (subgroupOfSubgroup B U) D.contracting := by
  obtain ⟨i, hi⟩ := hTB
  let S := restrictSubgroup T B i hi
  have hS : IsMaximalTorus S := local_maximal_of_ambient B S ((compose_restrict T B i hi).symm ▸ hT)
  have hPar : Specs.BorelProper.IsParabolic G B := by
    obtain ⟨hi, hb⟩ := hB
    exact ⟨hG, (smooth_extend_iff (AlgebraicClosure k) B.group.X).mp hb.1.1,
      hi, _, hb, ⟨𝟙 _, Category.id_comp _⟩⟩
  obtain ⟨c₀, D, hB', _, hR⟩ := Relative.RationalCocharacter.rationalParabolicThroughTorus
    G B hPar S hS
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hB'.1 hB'.2
  let V := pushSubgroup e.symm (contractingSubgroup D)
  have hV : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) V :=
    radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic)
      (B := closedSubgroupAlgebraicGroup B) e.symm (contractingSubgroup D) hR.1
  have hVU : SameSubgroup (subgroupOfSubgroup B U) D.contracting := by
    have hv : V.inclusion ≫ B.inclusion = D.contracting.inclusion := by
      change (D.contractingToParabolic ≫ e.inv) ≫ B.inclusion = _
      rw [← he, Category.assoc, e.inv_hom_id_assoc, D.contracting_in_G]
    obtain ⟨f, hf⟩ := hV.2.2 U hU.1 hU.2.1
    obtain ⟨g, hg⟩ := hU.2.2 V hV.1 hV.2.1
    refine ⟨⟨f, ?_⟩, ⟨g, ?_⟩⟩
    · change f ≫ D.contracting.inclusion = U.inclusion ≫ B.inclusion
      rw [← hv, ← Category.assoc, hf]
    · change g ≫ U.inclusion ≫ B.inclusion = D.contracting.inclusion
      rw [← Category.assoc, hg, hv]
  refine ⟨_, D, ⟨c₀, ?_⟩, hB', hVU⟩
  change c₀ ≫ T.inclusion = c₀ ≫ (i ≫ B.inclusion)
  rw [hi]

private theorem extSubgroup_point_iff {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : GroupScheme F} (A : ClosedSubgroup G)
    (h : IsClosedImmersion ((groupBaseChange F K).map A.inclusion).hom.hom.left)
    (R : TestAlgebra K) (x : GroupPoints ((groupBaseChange F K).obj G) R) :
    x ∈ SubgroupSections (Specs.GeometricRadicals.baseChangedSubgroup K A h)
      ((testSpec K).obj (Opposite.op R)) ↔
    baseChangePoint F K G.X R x ∈ SubgroupSections A ((testSpec F).obj (Opposite.op
      ((restrictTestAlgebra F K).obj R))) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨baseChangePoint F K A.group.X R p,
      (baseChangePointsSchemeNaturality F K A.inclusion.hom.hom R p).symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq⟩ := (baseChangePoints F K A.group.X R).2 p
    refine ⟨q, (baseChangePoints F K G.X R).1 ?_⟩
    change baseChangePoint F K G.X R (q ≫ (baseChange F K).map A.inclusion.hom.hom) = _
    rw [baseChangePointsSchemeNaturality, hq]
    exact hp

variable {K : Type u} [Field K] [Algebra k K]

private theorem baseChangedBorelLimits
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T B : ClosedSubgroup G.val) (hB : IsKBorel B) (hT : IsMaximalTorus T)
    (hTB : IsSubgroupOf T B) (U : ClosedSubgroup B.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    ∃ c : Cocharacter ((groupBaseChange k K).obj G.val),
      (∀ (R : TestAlgebra K) (v : Rˣ), baseChangePoint k K G.val.X R (cocharacterPoint c R v) ∈
        SubgroupSections T ((testSpec k).obj (Opposite.op ((restrictTestAlgebra k K).obj R)))) ∧
      ∀ (R : TestAlgebra K) (x : GroupPoints ((groupBaseChange k K).obj G.val) R),
        let X := (testSpec k).obj (Opposite.op ((restrictTestAlgebra k K).obj R))
        let x₀ := baseChangePoint k K G.val.X R x
        (HasExtension c x ↔ x₀ ∈ SubgroupSections B X) ∧
        (HasLimit c x 1 ↔ x₀ ∈ SubgroupSections (subgroupOfSubgroup B U) X) := by
  obtain ⟨c, D, ⟨a, ha⟩, hP, hD⟩ := radicalLimitComparison G hG T B hB hT hTB U hU
  obtain ⟨e, he, hp, hu, hZ, hp', hu', _, _⟩ :=
    LinearAlgebraicGroups.CocharacterDynamics.limitSubgroupsBaseChange (K := K) G c D
  let cK := e.hom ≫ (groupBaseChange k K).map c
  refine ⟨cK, ?_, ?_⟩
  · intro R v
    let p := unitPoint R v ≫ e.hom.hom.hom
    change baseChangePoint k K G.val.X R (p ≫ (baseChange k K).map c.hom.hom) ∈ _
    rw [baseChangePointsSchemeNaturality, show baseChangePoint k K
      (specGroup (groupAlgebra k IntegerCharacters)).X R p =
        unitPoint ((restrictTestAlgebra k K).obj R) v from he R v, ← ha, Grp.comp_hom_hom]
    refine ⟨unitPoint ((restrictTestAlgebra k K).obj R) v ≫ a.hom.hom, ?_⟩
    change ((unitPoint ((restrictTestAlgebra k K).obj R) v ≫ a.hom.hom) ≫ T.inclusion.hom.hom) =
      unitPoint ((restrictTestAlgebra k K).obj R) v ≫ a.hom.hom ≫ T.inclusion.hom.hom
    exact Category.assoc _ _ _
  · intro R x
    dsimp only
    have h1 := (hp' R x).trans (extSubgroup_point_iff D.parabolic hp R x)
    have h2 := (hu' R x).trans (extSubgroup_point_iff D.contracting hu R x)
    exact ⟨h1.trans ⟨section_of_subgroupOf hP.2 _ _, section_of_subgroupOf hP.1 _ _⟩,
      h2.trans ⟨section_of_subgroupOf hD.2 _ _, section_of_subgroupOf hD.1 _ _⟩⟩

end OppositeBorelLimits

section AscendTestAlgebra

open Specs.AdjointCocharacters (coordinateHopfMap)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
local notation "coordinateAlgebra" => Specs.AdjointCocharacters.coordinateHopf
open private coordinateHopfMap_surjective from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem subgroup_section_of_algebra_injection (G : AffineAlgebraicGroup F)
    (B : ClosedSubgroup G.val) {R S : TestAlgebra F} (f : R ⟶ S)
    (hf : Function.Injective f.hom) (x : GroupPoints G.val R) :
    mapPoints f x ∈ SubgroupSections B ((testSpec F).obj (Opposite.op S)) ↔
      x ∈ SubgroupSections B ((testSpec F).obj (Opposite.op R)) := by
  obtain ⟨p, rfl⟩ := (coordinatePointIso G |>.app R).groupIsoToMulEquiv.surjective x
  let j := coordinateHopfMap (G := closedSubgroupAlgebraicGroup B) (H := G) B.inclusion
  have hj : Function.Surjective j.hom :=
    coordinateHopfMap_surjective (G := closedSubgroupAlgebraicGroup B) (H := G)
      B.inclusion B.isClosedImmersion
  have hn := (coordinatePointIso G).hom.naturality_apply f p
  change (coordinatePointIso G).hom.app S (WithConv.toConv (f.hom.comp p.ofConv)) =
    mapPoints f ((coordinatePointIso G).hom.app R p) at hn
  change mapPoints f ((coordinatePointIso G).hom.app R p) ∈ _ ↔
    (coordinatePointIso G).hom.app R p ∈ _
  rw [← hn]
  change (coordinatePointIso G).hom.app S (WithConv.toConv (f.hom.comp p.ofConv)) ∈ _ ↔
    (coordinatePointIso G).hom.app R (WithConv.toConv p.ofConv) ∈ _
  rw [coordinatePoint_mem_subgroup, coordinatePoint_mem_subgroup]
  constructor
  · rintro ⟨q, hq⟩
    have hker : RingHom.ker j.hom.toAlgHom.toRingHom ≤ RingHom.ker p.ofConv.toRingHom := by
      intro a ha
      change j.hom a = 0 at ha
      change p.ofConv a = 0
      apply hf
      have he := DFunLike.congr_fun hq a
      change q (j.hom a) = f.hom (p.ofConv a) at he
      rw [ha, map_zero] at he
      exact he.symm.trans (map_zero _).symm
    exact ⟨AlgHom.liftOfSurjective j.hom.toAlgHom hj p.ofConv hker, AlgHom.liftOfSurjective_comp _ _ _ _⟩
  · rintro ⟨q, hq⟩
    exact ⟨f.hom.comp q, (AlgHom.comp_assoc _ _ _).trans (congrArg f.hom.comp hq)⟩

private def testAlgebraInclusion (K : Type u) [Field K] [Algebra F K] (R : TestAlgebra F) :
    R ⟶ (restrictTestAlgebra F K).obj (CommAlgCat.of K (K ⊗[F] R)) := by
  let S := (restrictTestAlgebra F K).obj (CommAlgCat.of K (K ⊗[F] R))
  let j : R →ₐ[F] K ⊗[F] R := Algebra.TensorProduct.includeRight
  let f₀ : R →+* S := j.toRingHom
  have hf (x : F) : f₀ (algebraMap F R x) =
      algebraMap K (K ⊗[F] R) (algebraMap F K x) :=
    (j.commutes x).trans (IsScalarTower.algebraMap_apply F K (K ⊗[F] R) x)
  letI : Algebra F S := S.algebra
  let f : R →ₐ[F] S := { toRingHom := f₀, commutes' := hf }
  exact @CommAlgCat.ofHom F _ R S _ R.algebra _ S.algebra f

private theorem mark_section_of_algebra_injection {G : GroupScheme F}
    (E : Type u) [Field E] [Algebra F E]
    (m : (groupPointsFunctor F).obj G ⟶
      LinearAlgebraicGroups.WeilRestriction.extendScalars F E ⋙ specialLinearThreePoints E)
    {R S : TestAlgebra F} (f : R ⟶ S) (hf : Function.Injective f.hom)
    (b : MatrixMark) (x : GroupPoints G R) :
    b.Holds (m.app S (mapPoints f x)) ↔ b.Holds (m.app R x) := by
  let j : R ⊗[F] E →ₐ[F] S ⊗[F] E := Algebra.TensorProduct.map f.hom (AlgHom.id F E)
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat f.hom.toLinearMap (AlgHom.id F E).toLinearMap
      hf Function.injective_id
  have hn := m.naturality_apply f x
  change m.app S (mapPoints f x) = SpecialLinearGroup.map j.toRingHom (m.app R x) at hn
  rw [hn]
  exact mark_map_iff j.toRingHom hj b (m.app R x)


private theorem matchMarks_of_splitTestAlgebras
    (d : PinnedOrbitDescent F K) (E : Type u) [Field E] [Algebra F E]
    (m : (groupPointsFunctor F).obj d.G.val ⟶
      LinearAlgebraicGroups.WeilRestriction.extendScalars F E ⋙ specialLinearThreePoints E)
    (h : ∀ (b : MatrixMark) (R : TestAlgebra K) (x : GroupPoints d.G.val ((restrictTestAlgebra F K).obj R)),
      b.Holds (m.app ((restrictTestAlgebra F K).obj R) x) ↔
        x ∈ SubgroupSections (d.mark b) ((testSpec F).obj (Opposite.op ((restrictTestAlgebra F K).obj R)))) :
    d.MatchesMarks (fun R x => m.app R x) := by
  intro b R x
  let R' := CommAlgCat.of K (K ⊗[F] R)
  let S := (restrictTestAlgebra F K).obj R'
  let f : R ⟶ S := testAlgebraInclusion K R
  have hf : Function.Injective f.hom := by
    let j : R →ₐ[F] K ⊗[F] R := Algebra.TensorProduct.includeRight
    have he : ⇑f.hom = ⇑j := rfl
    rw [he]
    exact Algebra.TensorProduct.includeRight_injective (B := R) (algebraMap F K).injective
  exact (mark_section_of_algebra_injection E m f hf b x).symm.trans
    ((h b R' (mapPoints f x)).trans (subgroup_section_of_algebra_injection d.G _ f hf x))


end AscendTestAlgebra

section MatrixCocharacterLimits
open LinearAlgebraicGroups.CocharacterDynamics
  (cocharacterPoint HasExtension HasLimit orbit laurentAlgebra laurentParameter laurentConstants
    polynomialAlgebra polynomialToLaurent polynomialEvaluate)
open private laurentParameter_pow diagonalConjugate_apply
  from LinearAlgebraicGroups.RootData.SpecialLinearDatum
open private zero_of_negative polynomial_value orbitPolynomial orbitPolynomial_toLaurent
  from LinearAlgebraicGroups.Reductive.CocharacterLieWeights


variable {k : Type u} [Field k] {G : GroupScheme k} {n : ℕ}

private theorem specialLinear_point_map
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    {R S : TestAlgebra k} (f : R ⟶ S) (x : GroupPoints G R) :
    m.hom.app S (mapPoints f x) = SpecialLinearGroup.map f.hom.toRingHom (m.hom.app R x) :=
  m.hom.naturality_apply f x

private theorem diagonalOrbitEntry
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (c : Cocharacter G) (y : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y i) : R)))
    (R : TestAlgebra k) (g : GroupPoints G R) (i j : Fin n) :
    (m.hom.app (laurentAlgebra R) (orbit c g)).val i j =
      LaurentPolynomial.T (y i - y j) * LaurentPolynomial.C ((m.hom.app R g).val i j) := by
  let S := laurentAlgebra R
  let t := laurentParameter R
  let p := cocharacterPoint c S t
  let q : GroupPoints G S := mapPoints (laurentConstants R) g
  change (m.hom.app S (p * q * p⁻¹)).val i j = _
  rw [map_mul, map_mul, map_inv, diagonalConjugate_apply (h S t), specialLinear_point_map]
  change (↑(t ^ y i) : S) * LaurentPolynomial.C ((m.hom.app R g).val i j) * (↑(t ^ y j)⁻¹ : S) =
    LaurentPolynomial.T (y i - y j) * LaurentPolynomial.C ((m.hom.app R g).val i j)
  rw [mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, laurentParameter_pow]

private theorem exists_diagonalLimitPolynomial
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (c : Cocharacter G) (y : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y i) : R)))
    (R : TestAlgebra k) (g : GroupPoints G R)
    (hvan : ∀ i j, y i < y j → (m.hom.app R g).val i j = 0) :
    ∃ p : GroupPoints G (polynomialAlgebra R),
      mapPoints (polynomialToLaurent R) p = orbit c g := by
  let S := polynomialAlgebra R
  let L := laurentAlgebra R
  let g₀ := (m.hom.app R g).val
  let v := (m.hom.app L (orbit c g)).val
  have hv (i j) : v i j = LaurentPolynomial.T (y i - y j) * LaurentPolynomial.C (g₀ i j) :=
    diagonalOrbitEntry m c y h R g i j
  let a : Matrix (Fin n) (Fin n) (Polynomial R) :=
    fun i j => orbitPolynomial (y i - y j) (g₀ i j)
  have hp' (i j) : (a i j).toLaurent = v i j :=
    (orbitPolynomial_toLaurent _ _ (fun hj => hvan i j (sub_neg.mp hj))).trans (hv i j).symm
  have ha : a.det = 1 := by
    apply Polynomial.toLaurent_injective
    rw [(Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R).map_det a, map_one]
    have he : a.map Polynomial.toLaurent = v := Matrix.ext hp'
    change (a.map Polynomial.toLaurent).det = 1
    rw [he]
    exact (m.hom.app L (orbit c g)).property
  let e := (m.app S).groupIsoToMulEquiv
  let p := e.symm ⟨a, ha⟩
  have hma : m.hom.app S p = ⟨a, ha⟩ := e.apply_symm_apply _
  refine ⟨p, ?_⟩
  apply (m.app L).groupIsoToMulEquiv.injective
  change m.hom.app L (mapPoints (polynomialToLaurent R) p) = _
  rw [specialLinear_point_map m, hma]
  exact Subtype.ext (Matrix.ext hp')

/-- The entries of a diagonal cocharacter limit on every test algebra.
Negative-weight entries must vanish, and the degree-zero entries give the limit. -/
private theorem specialLinearHasLimit
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (c : Cocharacter G) (y : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y i) : R)))
    (R : TestAlgebra k) (g z : GroupPoints G R) :
    HasLimit c g z ↔
      (∀ i j, y i < y j → (m.hom.app R g).val i j = 0) ∧
      ∀ i j, (m.hom.app R z).val i j = if y i = y j then (m.hom.app R g).val i j else 0 := by
  let S := polynomialAlgebra R
  let L := laurentAlgebra R
  let g₀ := (m.hom.app R g).val
  let z₀ := (m.hom.app R z).val
  let v := (m.hom.app L (orbit c g)).val
  have hv (i j) : v i j = LaurentPolynomial.T (y i - y j) * LaurentPolynomial.C (g₀ i j) :=
    diagonalOrbitEntry m c y h R g i j
  constructor
  · rintro ⟨p, hp, hz⟩
    let a := (m.hom.app S p).val
    have hp' (i j) : (a i j).toLaurent = v i j := by
      have h₁ := (specialLinear_point_map m (polynomialToLaurent R) p).symm.trans
        (congrArg (m.hom.app L) hp)
      exact congrArg (fun t : SpecialLinearGroup (Fin n) L => t.val i j) h₁
    have hp'' (i j) := (hp' i j).trans (hv i j)
    refine ⟨fun i j hij => zero_of_negative (hp'' i j) (sub_neg.mpr hij), fun i j => ?_⟩
    have h₂ := (specialLinear_point_map m (polynomialEvaluate R 0) p).symm.trans
      (congrArg (m.hom.app R) hz)
    have he : (polynomialEvaluate R 0).hom (a i j) = z₀ i j :=
      congrArg (fun t : SpecialLinearGroup (Fin n) R => t.val i j) h₂
    exact he.symm.trans (by simpa only [sub_eq_zero] using polynomial_value (hp'' i j))
  · rintro ⟨hvan, hval⟩
    obtain ⟨p, hp⟩ := exists_diagonalLimitPolynomial m c y h R g hvan
    refine ⟨p, hp, ?_⟩
    apply (m.app R).groupIsoToMulEquiv.injective
    change m.hom.app R (mapPoints (polynomialEvaluate R 0) p) = _
    rw [specialLinear_point_map m]
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    let a := (m.hom.app S p).val
    have hp' : (a i j).toLaurent = v i j := by
      have h₁ := (specialLinear_point_map m (polynomialToLaurent R) p).symm.trans
        (congrArg (m.hom.app L) hp)
      exact congrArg (fun t : SpecialLinearGroup (Fin n) L => t.val i j) h₁
    have he : z₀ i j = if y i = y j then g₀ i j else 0 := hval i j
    change (polynomialEvaluate R 0).hom (a i j) = z₀ i j
    exact (by simpa only [sub_eq_zero] using polynomial_value (hp'.trans (hv i j)) :
      (polynomialEvaluate R 0).hom (a i j) = if y i = y j then g₀ i j else 0).trans he.symm

private theorem specialLinearHasExtension
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (c : Cocharacter G) (y : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y i) : R)))
    (R : TestAlgebra k) (g : GroupPoints G R) :
    HasExtension c g ↔ ∀ i j, y i < y j → (m.hom.app R g).val i j = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ((specialLinearHasLimit m c y h R g z).mp hz).1
  · intro hg
    obtain ⟨p, hp⟩ := exists_diagonalLimitPolynomial m c y h R g hg
    exact ⟨_, p, hp, rfl⟩

private def transvectionPoint
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (R : TestAlgebra k) {i j : Fin n} (hij : i ≠ j) : GroupPoints G R :=
  m.inv.app R (SpecialLinearGroup.transvection hij 1)

private theorem transvectionEntry
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (R : TestAlgebra k) {i j : Fin n} (hij : i ≠ j) (a b : Fin n) (hab : a ≠ b) :
    (m.hom.app R (transvectionPoint m R hij)).val a b =
      if i = a ∧ j = b then 1 else 0 := by
  have h := GrpCat.hom_inv_apply (m.app R) (SpecialLinearGroup.transvection hij (1 : R))
  change m.hom.app R (transvectionPoint m R hij) = _ at h
  rw [h, SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne hab, zero_add]
  simp only [Matrix.single_apply]

private theorem transvection_hasExtension
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (c : Cocharacter G) (y : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y i) : R)))
    (R : TestAlgebra k) {i j : Fin n} (hij : i ≠ j) (hy : y j ≤ y i) :
    HasExtension c (transvectionPoint m R hij) := by
  apply (specialLinearHasExtension m c y h R _).mpr
  intro a b hab
  have hn : a ≠ b := fun e => (lt_irrefl (y a)) (e ▸ hab)
  rw [transvectionEntry m R hij a b hn, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact (not_lt_of_ge hy) hab

private theorem limitMark_of_orderedWeights
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (c : Cocharacter G) (y : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y i) : R)))
    (upper : Bool)
    (hy : if upper then StrictAnti y else StrictMono y)
    (R : TestAlgebra k) (g : GroupPoints G R) :
    (HasExtension c g ↔ (if upper then MatrixMark.positiveBorel else MatrixMark.negativeBorel).Holds
      (m.hom.app R g)) ∧
    (HasLimit c g 1 ↔ (if upper then MatrixMark.positiveRadical else MatrixMark.negativeRadical).Holds
      (m.hom.app R g)) := by
  have hentry :
      (∀ i j, y i < y j → (m.hom.app R g).val i j = 0) ↔
      (if upper then MatrixMark.positiveBorel else MatrixMark.negativeBorel).Holds (m.hom.app R g) := by
    cases upper with
    | false =>
      change StrictMono y at hy
      change _ ↔ ∀ i j, i < j → (m.hom.app R g).val i j = 0
      exact ⟨fun hn i j hij => hn i j (hy hij), fun hn i j hij => hn i j (hy.lt_iff_lt.mp hij)⟩
    | true =>
      change StrictAnti y at hy
      change _ ↔ ∀ i j, j < i → (m.hom.app R g).val i j = 0
      exact ⟨fun hn i j hij => hn i j (hy hij), fun hn i j hij => hn i j (hy.lt_iff_gt.mp hij)⟩
  have hi : Function.Injective y := by
    cases upper
    · exact (show StrictMono y from hy).injective
    · exact (show StrictAnti y from hy).injective
  refine ⟨(specialLinearHasExtension m c y h R g).trans hentry,
    (specialLinearHasLimit m c y h R g 1).trans ?_⟩
  have hdiag :
      (∀ i j, (m.hom.app R (1 : GroupPoints G R)).val i j =
        if y i = y j then (m.hom.app R g).val i j else 0) ↔
          ∀ i, (m.hom.app R g).val i i = 1 := by
    rw [map_one]
    constructor
    · intro hz i
      simpa using (hz i i).symm
    · intro hz i j
      by_cases he : i = j
      · subst j
        simp [hz i]
      · simp [hi.eq_iff, Matrix.one_apply_ne he, he]
  rw [hentry, hdiag]
  cases upper <;> rfl

/-- The lower Borel and both radicals are determined by the diagonal
cocharacter limits and the marked intersection. -/
private theorem specialLinearOppositeMarks
    (m : (groupPointsFunctor k).obj G ≅ specialLinearPointsOfSize n k)
    (c c' : Cocharacter G) (y y' : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y i) : R)))
    (h' : ∀ (R : TestAlgebra k) (t : Rˣ), (m.hom.app R (cocharacterPoint c' R t)).val =
      Matrix.diagonal (fun i => (↑(t ^ y' i) : R)))
    (hp : ∀ (R : TestAlgebra k) (g : GroupPoints G R),
      HasExtension c g ↔ MatrixMark.positiveBorel.Holds (m.hom.app R g))
    (hopp : ∀ (R : TestAlgebra k) (g : GroupPoints G R),
      HasExtension c g → HasExtension c' g → MatrixMark.torus.Holds (m.hom.app R g)) :
    ∀ (R : TestAlgebra k) (g : GroupPoints G R),
      (HasExtension c' g ↔ MatrixMark.negativeBorel.Holds (m.hom.app R g)) ∧
      (HasLimit c g 1 ↔ MatrixMark.positiveRadical.Holds (m.hom.app R g)) ∧
      (HasLimit c' g 1 ↔ MatrixMark.negativeRadical.Holds (m.hom.app R g)) := by
  let R₀ := CommAlgCat.of k k
  have hy : StrictAnti y := by
    intro i j hij
    by_contra! hy
    let g := transvectionPoint m R₀ hij.ne.symm
    have hu := (hp R₀ g).mp (transvection_hasExtension m c y h R₀ hij.ne.symm hy)
    have hz := hu hij
    rw [transvectionEntry m R₀ hij.ne.symm j i hij.ne.symm] at hz
    simp at hz
  have hy' : StrictMono y' := by
    intro i j hij
    by_contra! hy'
    let g := transvectionPoint m R₀ hij.ne
    have hu : MatrixMark.positiveBorel.Holds (m.hom.app R₀ g) := by
      intro a b hab
      rw [transvectionEntry m R₀ hij.ne a b hab.ne.symm, ite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge hij.le) hab
    have ht := hopp R₀ g ((hp R₀ g).mpr hu) (transvection_hasExtension m c' y' h' R₀ hij.ne hy')
    have hz := ht i j hij.ne
    rw [transvectionEntry m R₀ hij.ne i j hij.ne] at hz
    simp at hz
  intro R g
  have hpos := limitMark_of_orderedWeights m c y h true hy R g
  have hneg := limitMark_of_orderedWeights m c' y' h' false hy' R g
  exact ⟨hneg.1, hpos.2, hneg.2⟩


end MatrixCocharacterLimits
section CompleteAdjacentMarks

open Specs.GeometricRadicals (IsReductive)
open Specs.Pinning (SimpleRoot)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (HasExtension HasLimit)
open private maximalTorus_of_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private reductive_of_semisimple from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private subgroupFactorThrough from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private isAffine_baseChange from LinearAlgebraicGroups.Affine.IdentityTangent

set_option maxHeartbeats 3500000 in
/-- The adjacent orbit is the marked hyperbolic special unitary group over
the separable quadratic field cut out by its two-vertex action. -/
theorem adjacentPinnedOrbitModel : AdjacentPinnedOrbitModel.{u} := by
  classical
  intro F K _ _ _ _ _ d j hCartan
  let E := orbitField (d.adjacentAction j) 0
  obtain ⟨hq, hs, W, U, m, f, t, p, hE, hU, ht, hmarks, hsplt, hcoords⟩ :=
    adjacentOrbitComparison d j hCartan
  letI : Algebra.IsQuadraticExtension F E := hq
  letI : Algebra.IsSeparable F E := hs
  let A := (groupBaseChange F K).obj d.G.val
  let a := (groupPointsFunctor K).mapIso (d.trivialization t) ≪≫ p
  let w := (groupPointsFunctor F).map (f.hom ≫ U.inclusion) ≫ m.hom
  letI : IsAffine d.G.val.X.left := d.G.property.1
  letI : IsAffine A.X.left := isAffine_baseChange K d.G.val
  let point (R : TestAlgebra K) (x : GroupPoints A R) := baseChangePoint F K d.G.val.X R x
  have hmat (b : MatrixMark) (R : TestAlgebra K) (x : GroupPoints A R) :
      b.Holds (a.hom.app R x) ↔ b.Holds (w.app ((restrictTestAlgebra F K).obj R) (point R x)) := by
    let R₀ := (restrictTestAlgebra F K).obj R
    let y : GroupPoints U.group R₀ := ((groupPointsFunctor F).map f.hom).app R₀ (point R x)
    let g : SL₃ (R₀ ⊗[F] E) := w.app R₀ (point R x)
    have h := (hU R₀ g).mpr ⟨y, rfl⟩
    have hm := unitaryProjection_preserves_mark (F := F) (E := E) R b g h
    have he := hsplt R x
    dsimp only at hm he
    refine (Iff.of_eq ?_).trans hm
    exact congrArg b.Holds he
  have ht₀ : d.T.inclusion.hom.hom ∈ SubgroupSections d.T d.T.group.X := by
    refine ⟨𝟙 d.T.group.X, ?_⟩
    change 𝟙 d.T.group.X ≫ d.T.inclusion.hom.hom = d.T.inclusion.hom.hom
    rw [Category.id_comp]
  have htpos := subgroupFactorThrough d.T d.Bpos ((d.opposite _ _).mp ht₀ _ (by simp))
  have htneg := subgroupFactorThrough d.T d.Bneg ((d.opposite _ _).mp ht₀ _ (by simp))
  have hr := reductive_of_semisimple d.G d.semisimple
  have hT := maximalTorus_of_geometricallyMaximal d.G d.T d.torus d.maximal
  obtain ⟨c, hc, hpos⟩ := baseChangedBorelLimits (K := K) d.G hr d.T d.Bpos
    d.isBorelPos hT htpos d.Upos d.isRadicalPos
  obtain ⟨c', hc', hneg⟩ := baseChangedBorelLimits (K := K) d.G hr d.T d.Bneg
    d.isBorelNeg hT htneg d.Uneg d.isRadicalNeg
  have inherited (b : MatrixMark) (hb : b ∈ ({MatrixMark.torus, MatrixMark.positiveBorel} : Set _))
      (R : TestAlgebra K) (x : GroupPoints A R) :
      b.Holds (a.hom.app R x) ↔ point R x ∈ SubgroupSections (d.mark b)
        ((testSpec F).obj (Opposite.op ((restrictTestAlgebra F K).obj R))) :=
    (hmat b R x).trans (hmarks b hb _ _)
  have htor := inherited MatrixMark.torus (by simp)
  have hupper := inherited MatrixMark.positiveBorel (by simp)
  obtain ⟨y, hy⟩ := diagonalWeights A a c (fun R v =>
    (htor R (cocharacterPoint c R v)).mpr (hc R v))
  obtain ⟨y', hy'⟩ := diagonalWeights A a c' (fun R v =>
    (htor R (cocharacterPoint c' R v)).mpr (hc' R v))
  have hpc (R : TestAlgebra K) (x : GroupPoints A R) :
      HasExtension c x ↔ MatrixMark.positiveBorel.Holds (a.hom.app R x) :=
    (hpos R x).1.trans (hupper R x).symm
  have hopc (R : TestAlgebra K) (x : GroupPoints A R) :
      HasExtension c x → HasExtension c' x → MatrixMark.torus.Holds (a.hom.app R x) := by
    intro hx hx'
    apply (htor R x).mpr
    apply (d.opposite _ _).mpr
    intro H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact (hpos R x).1.mp hx
    · obtain rfl := Set.mem_singleton_iff.mp hH
      exact (hneg R x).1.mp hx'
  have hl := specialLinearOppositeMarks a c c' y y' hy hy' hpc hopc
  have hAll (b : MatrixMark) (R : TestAlgebra K) (x : GroupPoints A R) :
      b.Holds (w.app ((restrictTestAlgebra F K).obj R) (point R x)) ↔
        point R x ∈ SubgroupSections (d.mark b) ((testSpec F).obj (Opposite.op ((restrictTestAlgebra F K).obj R))) := by
    refine (hmat b R x).symm.trans ?_
    cases b with
    | torus => exact htor R x
    | positiveBorel => exact hupper R x
    | negativeBorel => exact (hl R x).1.symm.trans (hneg R x).1
    | positiveRadical => exact (hl R x).2.1.symm.trans (hpos R x).2
    | negativeRadical => exact (hl R x).2.2.symm.trans (hneg R x).2
  have hFull := matchMarks_of_splitTestAlgebras d E w (fun b R x => by
    obtain ⟨x', rfl⟩ := (baseChangePoints F K d.G.val.X R).2 x
    exact hAll b R x')
  exact ⟨hq, hs, W, U, m, f, t, p, hE, hU, ht, fun b _ => hFull b, hsplt, hcoords⟩

end CompleteAdjacentMarks


end AdjacentSubgroups

section OrthogonalScalarProjections

set_option backward.isDefEq.respectTransparency false

open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SimpleRoot)
open Specs.AutomorphismSequence (forgetPinning)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private fixedFieldTensor_injective from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem tensorEvaluation_of_orbit_embedding (R : TestAlgebra K)
    (J : Subgroup Gal(K/F)) (σ : Gal(K/F)) :
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    let E := IntermediateField.fixedField J
    let a := σ.toAlgHom.comp E.val
    (tensorEvaluation R).hom.toRingHom.comp
      ((coefficientRingMap R₀ σ).comp (orbitScalarEmbedding R₀ J).toRingHom) =
        (Algebra.TensorProduct.lift (AlgHom.id F R₀)
          (((Algebra.ofId K R₀).restrictScalars F).comp a) (fun _ _ => Commute.all _ _)).toRingHom := by
  let R₀ := (restrictTestAlgebra F K).obj R
  letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
  letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
  let E := IntermediateField.fixedField J
  let a := σ.toAlgHom.comp E.val
  let g : R₀ ⊗[F] E →+* R₀ :=
    (tensorEvaluation R).hom.toRingHom.comp
      ((coefficientRingMap R₀ σ).comp (orbitScalarEmbedding R₀ J).toRingHom)
  let f : R₀ ⊗[F] E →ₐ[F] R₀ :=
    Algebra.TensorProduct.lift (AlgHom.id F R₀)
      (((Algebra.ofId K R₀).restrictScalars F).comp a) (fun _ _ => Commute.all _ _)
  change g = f.toRingHom
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change (tensorEvaluation R).hom ((σ y.val) ⊗ₜ[F] x) = x * algebraMap K R (σ y.val)
    rw [tensorEvaluation_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 2500000 in
/-- The scalar projections of the orthogonal descent are the embeddings
indexed by the actual vertices of the orbit. -/
private theorem orthogonalOrbitScalarComparison [IsGalois F K] [FiniteDimensional F K]
    (d : PinnedOrbitDescent F K) (n : ℕ)
    (m : (groupPointsFunctor F).obj d.P.pair.G.val ≅ specialLinearFamilyPoints F (SimpleRoot d.P.pair) n)
    (hm : ∀ (σ : Gal(K/F)) (R : TestAlgebra F) (x : GroupPoints d.P.pair.G.val R) (j : SimpleRoot d.P.pair),
      let a := (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv
      m.hom.app R (x ≫ a.hom.hom) j = m.hom.app R x (d.action σ j))
    (i : SimpleRoot d.P.pair) :
    let E := orbitField d.action i
    ∃ (W : AffineAlgebraicGroup F) (f : d.G.val ≅ W.val)
      (w : (groupPointsFunctor F).obj W.val ≅ extendScalars F E ⋙ specialLinearPointsOfSize n E)
      (emb : SimpleRoot d.P.pair → (E →ₐ[F] K)),
      (∀ (σ : Gal(K/F)) (x : E), emb (d.action σ i) x = σ x.val) ∧
      (∀ (R : TestAlgebra K) (j : SimpleRoot d.P.pair)
        (x : GroupPoints ((groupBaseChange F K).obj d.G.val) R),
        let R₀ := (restrictTestAlgebra F K).obj R
        letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
        letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
        let f₀ := Algebra.TensorProduct.lift (AlgHom.id F R₀)
          (((Algebra.ofId K R₀).restrictScalars F).comp (emb j)) (fun _ _ => Commute.all _ _)
        let y := ((groupPointsFunctor K).map (d.trivialization (extendedGroupIso K)).hom).app R x
        m.hom.app R₀ (baseChangePoint F K d.P.pair.G.val.X R y) j =
          SpecialLinearGroup.map f₀.toRingHom
            (w.hom.app R₀ (((groupPointsFunctor F).map f.hom).app R₀ (baseChangePoint F K d.G.val.X R x)))) ∧
      ∀ (b : MatrixMark) (R : TestAlgebra F) (x : GroupPoints d.G.val R),
        b.Holds (w.hom.app R (((groupPointsFunctor F).map f.hom).app R x)) ↔
          ∀ j, b.Holds (familyOrbitPoint d n m R x j) := by
  letI := MulAction.compHom (SimpleRoot d.P.pair) d.action
  let J := MulAction.stabilizer Gal(K/F) i
  let E := orbitField d.action i
  let O := diagramOrbit d.action i
  obtain ⟨W, f, w, hw⟩ := orthogonalOrbitDescent d n m hm i
  obtain ⟨a, e, ha, _, _⟩ := orbitScalarSplitting d.action i
  let l (j : SimpleRoot d.P.pair) : O := ⟨j, d.transitive i j⟩
  let emb (j : SimpleRoot d.P.pair) := a (l j)
  have hemb (σ : Gal(K/F)) (x : E) : emb (d.action σ i) x = σ x.val :=
    ha σ x
  have hfix (R : TestAlgebra F) (x : GroupPoints d.G.val R) :
      familyOrbitPoint d n m R x ∈ permutedMatrices d.action R n := by
    change _ ∈ (permutedMatrices d.action R n :
      Set (SimpleRoot d.P.pair → SpecialLinearGroup (Fin n) (K ⊗[F] R)))
    rw [← (familyOrbitPoint_range d n m hm R).2]
    exact ⟨x, rfl⟩
  refine ⟨W, f, w, emb, hemb, ?_, ?_⟩
  · intro R j x
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    let x₀ := baseChangePoint F K d.G.val.X R x
    let a := liftedSplitPoint d R₀ x₀
    let f₁ := (tensorEvaluation (F := F) R).hom.toRingHom
    let z := w.hom.app R₀ (((groupPointsFunctor F).map f.hom).app R₀ x₀)
    obtain ⟨σ, rfl⟩ := d.transitive i j
    have heq : emb (d.action σ i) = σ.toAlgHom.comp E.val := AlgHom.ext (hemb σ)
    dsimp only
    rw [heq, liftedSplitPoint_specialize]
    have hn := m.hom.naturality_apply (tensorEvaluation (F := F) R) a
    change m.hom.app R₀ (mapPoints (tensorEvaluation R) a) =
      (fun j => SpecialLinearGroup.map f₁ (familyOrbitPoint d n m R₀ x₀ j)) at hn
    rw [hn]
    have h := (hfix R₀ x₀) σ i
    change familyOrbitPoint d n m R₀ x₀ (d.action σ i) =
      SpecialLinearGroup.map (coefficientRingMap R₀ σ) (familyOrbitPoint d n m R₀ x₀ i) at h
    simp only [h, ← hw R₀ x₀]
    apply Subtype.ext
    ext a b
    exact DFunLike.congr_fun (tensorEvaluation_of_orbit_embedding R J σ) (z.val a b)
  · intro b R x
    constructor
    · intro h j
      obtain ⟨σ, rfl⟩ := d.transitive i j
      rw [show familyOrbitPoint d n m R x (d.action σ i) =
        SpecialLinearGroup.map (coefficientRingMap R σ) (familyOrbitPoint d n m R x i) from (hfix R x) σ i, ← hw]
      exact mark_map _ b _ (mark_map _ b _ h)
    · intro h
      apply (mark_map_iff (orbitScalarEmbedding R J).toRingHom
        (fixedFieldTensor_injective R J) b _).mp
      rw [hw]
      exact h i


end OrthogonalScalarProjections

section SplitProductPair

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

open Specs.Pinning (SplitBorelPair)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsTorus IsSplitTorus IsMaximalTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterDescent (Cocharacter compositionPairing)
open Specs.CharacterPairing (pairing)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open private affineProduct from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private productTorus productReductive splitProductTorus productTorus_geometricallyMaximal
  productRootEquiv from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private reductive_geometric connected_of_reductive isKBorel_iff_of_isAlgClosed
  split_of_maximal geometricMaximal_of_maximal extendSubgroup smooth_extend_iff
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private reductive_of_groupIso from LinearAlgebraicGroups.RootData.RankOneFlag
open private connected_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private maximal_of_square from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private maximalTorus_of_geometricallyMaximal from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem affineProduct_isReductive (G H : AffineAlgebraicGroup k)
    (hG : IsReductive G) (hH : IsReductive H) :
    IsReductive (affineProduct G H) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let P := affineProduct G H
  let e : (affineProduct (GeometricGroup G) (GeometricGroup H)).val ≅ (GeometricGroup P).val :=
    Functor.Monoidal.μIso F G.val H.val
  have hP := reductive_of_groupIso e (productReductive _ _ (reductive_geometric G hG)
    (reductive_geometric H hH))
  have hs : Smooth P.val.X.hom := (smooth_extend_iff K P.val.X).mp hP.1
  have hc : ConnectedSpace (GeometricGroup P).val.X.left :=
    connected_of_reductive (GeometricGroup P) hP
  letI : ConnectedSpace P.val.X.left := (connected_baseChange_iff (K := K) P).mp hc
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) P hs
    (geometricallyConnected_of_connected P)).mp hP

private def geometricSplitBorelPair (P : SplitBorelPair k) : SplitBorelPair (AlgebraicClosure k) := by
  let K := AlgebraicClosure k
  let G := GeometricGroup P.G
  let T := extendSubgroup K P.T
  have hT : IsMaximalTorus T := by
    obtain ⟨_, hT⟩ := P.maximal
    exact hT
  have hG := reductive_geometric P.G P.reductive
  let B := LinearAlgebraicGroups.GeometricBorelConjugacy.torusContainedInBorel G
    hG.1 (connected_of_reductive G hG) T hT.1
  exact ⟨G, hG, T, split_of_maximal (A := G) hT, geometricMaximal_of_maximal G T hT, B.choose,
    (isKBorel_iff_of_isAlgClosed G B.choose).mpr B.choose_spec.1, B.choose_spec.2⟩

private theorem productTorus_isGeometricallyMaximal (P Q : SplitBorelPair k) :
    IsGeometricallyMaximal (productTorus P Q) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let R := affineProduct P.G Q.G
  let T := productTorus P Q
  let P' := geometricSplitBorelPair P
  let Q' := geometricSplitBorelPair Q
  let S := productTorus P' Q'
  let T' := extendSubgroup K T
  let e : (affineProduct P'.G Q'.G).val ≅ (GeometricGroup R).val :=
    Functor.Monoidal.μIso F P.G.val Q.G.val
  let eT : S.group ≅ T'.group := Functor.Monoidal.μIso F P.T.group Q.T.group
  have hS := maximalTorus_of_geometricallyMaximal (affineProduct P'.G Q'.G) S
    (lattice_torus_of_split (splitProductTorus P' Q')) (productTorus_geometricallyMaximal P' Q')
  have he : eT.hom ≫ T'.inclusion = S.inclusion ≫ e.hom :=
    (Functor.LaxMonoidal.μ_natural F P.T.inclusion Q.T.inclusion).symm
  exact ⟨T'.isClosedImmersion, maximal_of_square e S T' eT he hS⟩

end SplitProductPair

section SplitProductPair

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SplitBorelPair PinnedGroup SimpleRoot IsSimple RootCoordinate)
open Specs.GeometricRadicals (IsReductive)
open Specs.RankOneFlag (SameSubgroup)
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (IsRegular subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (pairing)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition HasExtension HasLimit
  cocharacterPoint orbit polynomialAlgebra polynomialEvaluate polynomialToLaurent)
open private affineProduct tensorClosedImmersion
  from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private productTorus splitProductTorus productRootEquiv productPointEquiv
  firstInclusion secondInclusion productCharacterEquiv productCharacterEquiv_root_left
  productCharacterEquiv_root_right
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private def projectPoint {G H : GroupScheme k} (f : G ⟶ H) {R : TestAlgebra k}
    (x : GroupPoints G R) : GroupPoints H R :=
  ((groupPointsFunctor k).map f).app R x

@[simp] private theorem projectPoint_comp {G H J : GroupScheme k} (f : G ⟶ H) (g : H ⟶ J)
    {R : TestAlgebra k} (x : GroupPoints G R) :
    projectPoint g (projectPoint f x) = projectPoint (f ≫ g) x :=
  by
    change (x ≫ f.hom.hom) ≫ g.hom.hom = x ≫ f.hom.hom ≫ g.hom.hom
    exact Category.assoc _ _ _

@[simp] private theorem projectPoint_id {G : GroupScheme k} {R : TestAlgebra k} (x : GroupPoints G R) :
    projectPoint (𝟙 G) x = x := by
  change x ≫ 𝟙 G.X = x
  exact Category.comp_id _

@[simp] private theorem projectPoint_zero {G H : GroupScheme k} {R : TestAlgebra k}
    (x : GroupPoints G R) : projectPoint (0 : G ⟶ H) x = 1 := by
  change x ≫ (1 : G.X ⟶ H.X) = 1
  exact MonObj.comp_one _

private theorem projectPoint_natural {G H : GroupScheme k} (f : G ⟶ H) {R S : TestAlgebra k}
    (a : R ⟶ S) (x : GroupPoints G R) :
    mapPoints a (projectPoint f x) = projectPoint f (mapPoints a x) :=
  (((groupPointsFunctor k).map f).naturality_apply a x).symm

private theorem projectPoint_orbit {G H : GroupScheme k} (f : G ⟶ H) (c : Cocharacter G)
    {R : TestAlgebra k} (x : GroupPoints G R) :
    projectPoint f (orbit c x) = orbit (c ≫ f) (projectPoint f x) := by
  unfold orbit
  change ((groupPointsFunctor k).map f).app _ (_ * _ * _⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  change projectPoint f (cocharacterPoint c _ _) *
      projectPoint f (mapPoints _ x) * (projectPoint f (cocharacterPoint c _ _))⁻¹ = _
  simp only [← projectPoint_natural, cocharacterPoint]
  rfl

private theorem product_hasLimit {G H : GroupScheme k}
    (c : Cocharacter (G ⊗ H)) {R : TestAlgebra k} (x z : GroupPoints (G ⊗ H) R) :
    HasLimit c x z ↔
      HasLimit (c ≫ fst G H) (projectPoint (fst G H) x) (projectPoint (fst G H) z) ∧
      HasLimit (c ≫ snd G H) (projectPoint (snd G H) x) (projectPoint (snd G H) z) := by
  constructor
  · rintro ⟨p, hp, hz⟩
    refine ⟨⟨projectPoint (fst G H) p, ?_, ?_⟩, ⟨projectPoint (snd G H) p, ?_, ?_⟩⟩
    · rw [projectPoint_natural, hp, projectPoint_orbit]
    · rw [projectPoint_natural, hz]
    · rw [projectPoint_natural, hp, projectPoint_orbit]
    · rw [projectPoint_natural, hz]
  · rintro ⟨⟨p, hp, hz⟩, ⟨q, hq, hw⟩⟩
    let a := (productPointEquiv G H (polynomialAlgebra R)).symm (p, q)
    have hpa : projectPoint (fst G H) a = p :=
      congrArg Prod.fst ((productPointEquiv G H _).apply_symm_apply (p, q))
    have hqa : projectPoint (snd G H) a = q :=
      congrArg Prod.snd ((productPointEquiv G H _).apply_symm_apply (p, q))
    refine ⟨a, (productPointEquiv G H _).injective (Prod.ext ?_ ?_),
      (productPointEquiv G H _).injective (Prod.ext ?_ ?_)⟩
    · change projectPoint (fst G H) (mapPoints _ a) = projectPoint (fst G H) (orbit c x)
      rw [← projectPoint_natural, hpa, projectPoint_orbit, hp]
    · change projectPoint (snd G H) (mapPoints _ a) = projectPoint (snd G H) (orbit c x)
      rw [← projectPoint_natural, hqa, projectPoint_orbit, hq]
    · change projectPoint (fst G H) (mapPoints _ a) = projectPoint (fst G H) z
      rw [← projectPoint_natural, hpa, hz]
    · change projectPoint (snd G H) (mapPoints _ a) = projectPoint (snd G H) z
      rw [← projectPoint_natural, hqa, hw]

private theorem product_hasExtension {G H : GroupScheme k}
    (c : Cocharacter (G ⊗ H)) {R : TestAlgebra k} (x : GroupPoints (G ⊗ H) R) :
    HasExtension c x ↔
      HasExtension (c ≫ fst G H) (projectPoint (fst G H) x) ∧
      HasExtension (c ≫ snd G H) (projectPoint (snd G H) x) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨⟨_, ((product_hasLimit c x z).mp hz).1⟩, ⟨_, ((product_hasLimit c x z).mp hz).2⟩⟩
  · rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩
    let a := (productPointEquiv G H R).symm (z, w)
    refine ⟨a, (product_hasLimit c x a).mpr ⟨?_, ?_⟩⟩
    · have he : projectPoint (fst G H) a = z :=
        congrArg Prod.fst ((productPointEquiv G H R).apply_symm_apply (z, w))
      rwa [he]
    · have he : projectPoint (snd G H) a = w :=
        congrArg Prod.snd ((productPointEquiv G H R).apply_symm_apply (z, w))
      rwa [he]

private abbrev subgroupSection {G : GroupScheme k} (S : ClosedSubgroup G) {R : TestAlgebra k}
    (g : GroupPoints G R) : Prop :=
  g ∈ SubgroupSections S ((testSpec k).obj (Opposite.op R))

private def productSubgroup {G H : GroupScheme k} (S : ClosedSubgroup G) (T : ClosedSubgroup H) :
    ClosedSubgroup (G ⊗ H) :=
  ⟨S.group ⊗ T.group, S.inclusion ⊗ₘ T.inclusion, by
    letI := S.isClosedImmersion
    letI := T.isClosedImmersion
    exact tensorClosedImmersion S.inclusion.hom.hom T.inclusion.hom.hom⟩

private theorem product_subgroupSection {G H : GroupScheme k} (S : ClosedSubgroup G) (T : ClosedSubgroup H)
    {R : TestAlgebra k} (x : GroupPoints (G ⊗ H) R) :
    subgroupSection (productSubgroup S T) x ↔
      subgroupSection S (projectPoint (fst G H) x) ∧
      subgroupSection T (projectPoint (snd G H) x) := by
  let U := productSubgroup S T
  have hfirst (y : GroupPoints U.group R) :
      projectPoint (fst G H) (projectPoint U.inclusion y) =
        projectPoint S.inclusion (projectPoint (fst S.group T.group) y) := by
    change projectPoint (fst G H) (projectPoint (S.inclusion ⊗ₘ T.inclusion) y) = _
    simp only [projectPoint_comp, tensorHom_fst]
  have hsecond (y : GroupPoints U.group R) :
      projectPoint (snd G H) (projectPoint U.inclusion y) =
        projectPoint T.inclusion (projectPoint (snd S.group T.group) y) := by
    change projectPoint (snd G H) (projectPoint (S.inclusion ⊗ₘ T.inclusion) y) = _
    simp only [projectPoint_comp, tensorHom_snd]
  constructor
  · rintro ⟨y, rfl⟩
    change subgroupSection S (projectPoint (fst G H) (projectPoint U.inclusion y)) ∧
      subgroupSection T (projectPoint (snd G H) (projectPoint U.inclusion y))
    rw [hfirst, hsecond]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    let y := (productPointEquiv S.group T.group R).symm (s, t)
    have hys : projectPoint (fst S.group T.group) y = s :=
      congrArg Prod.fst ((productPointEquiv S.group T.group _).apply_symm_apply (s, t))
    have hyt : projectPoint (snd S.group T.group) y = t :=
      congrArg Prod.snd ((productPointEquiv S.group T.group _).apply_symm_apply (s, t))
    refine ⟨y, (productPointEquiv G H _).injective (Prod.ext ?_ ?_)⟩
    · change projectPoint (fst G H) (projectPoint U.inclusion y) = _
      rw [hfirst, hys]
      exact hs
    · change projectPoint (snd G H) (projectPoint U.inclusion y) = _
      rw [hsecond, hyt]
      exact ht

private structure SplitPairProduct (P Q : SplitBorelPair k) where
  B : ClosedSubgroup (affineProduct P.G Q.G).val
  borel : IsKBorel B
  containsTorus : IsSubgroupOf (productTorus P Q) B
  leftPositive : ∀ a : Root P.T, productRootEquiv P Q (Sum.inl a) ∈
    subgroupRoots (productTorus P Q) B ↔ a ∈ subgroupRoots P.T P.B
  rightPositive : ∀ a : Root Q.T, productRootEquiv P Q (Sum.inr a) ∈
    subgroupRoots (productTorus P Q) B ↔ a ∈ subgroupRoots Q.T Q.B
  borelSections : ∀ (R : TestAlgebra k) (x : GroupPoints (affineProduct P.G Q.G).val R),
    subgroupSection B x ↔ subgroupSection P.B (projectPoint (fst P.G.val Q.G.val) x) ∧
      subgroupSection Q.B (projectPoint (snd P.G.val Q.G.val) x)

private def SplitPairProduct.pair {P Q : SplitBorelPair k} (D : SplitPairProduct P Q) :
    SplitBorelPair k :=
  ⟨affineProduct P.G Q.G, affineProduct_isReductive P.G Q.G P.reductive Q.reductive,
    productTorus P Q, splitProductTorus P Q, productTorus_isGeometricallyMaximal P Q,
    D.B, D.borel, D.containsTorus⟩

set_option maxHeartbeats 1200000 in
private theorem existsSplitPairProduct (P Q : SplitBorelPair k) : Nonempty (SplitPairProduct P Q) := by
  let A := affineProduct P.G Q.G
  let T := productTorus P Q
  have hA := affineProduct_isReductive P.G Q.G P.reductive Q.reductive
  have hT := splitProductTorus P Q
  have hTm := productTorus_isGeometricallyMaximal P Q
  obtain ⟨c, L, hc, hcS, hcB⟩ := (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive
    P.T P.split P.maximal).1 P.B P.borel P.containsTorus
  obtain ⟨d, M, hd, hdS, hdB⟩ := (RootData.BorelsAndChambers.borelsThroughT Q.G Q.reductive
    Q.T Q.split Q.maximal).1 Q.B Q.borel Q.containsTorus
  let u : Cocharacter T.group := lift c d
  have hl (a : Root P.T) : pairing T.group ((productRootEquiv P Q) (Sum.inl a)).val u =
      pairing P.T.group a.val c := by
    unfold pairing compositionPairing
    rw [show ((productRootEquiv P Q) (Sum.inl a)).val = fst P.T.group Q.T.group ≫ a.val from rfl,
      show u ≫ fst P.T.group Q.T.group ≫ a.val = c ≫ a.val from lift_fst_assoc c d a.val]
  have hr (a : Root Q.T) : pairing T.group ((productRootEquiv P Q) (Sum.inr a)).val u =
      pairing Q.T.group a.val d := by
    unfold pairing compositionPairing
    rw [show ((productRootEquiv P Q) (Sum.inr a)).val = snd P.T.group Q.T.group ≫ a.val from rfl,
      show u ≫ snd P.T.group Q.T.group ≫ a.val = d ≫ a.val from lift_snd_assoc c d a.val]
  have hu : IsRegular T u := by
    intro a
    obtain ⟨a, rfl⟩ := (productRootEquiv P Q).surjective a
    rcases a with a | a
    · exact (hl a).symm ▸ hc a
    · exact (hr a).symm ▸ hd a
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition A (u ≫ T.inclusion)
  have hD := RootData.BorelsAndChambers.regularCocharacterBorel A hA T hT hTm u hu D
  refine ⟨⟨D.parabolic, hD.2.1, hD.2.2.1, ?_, ?_, ?_⟩⟩
  · intro a
    rw [hD.2.2.2.1, hcB]
    change 0 < pairing T.group ((productRootEquiv P Q) (Sum.inl a)).val u ↔ _
    rw [hl]
    rfl
  · intro a
    rw [hD.2.2.2.1, hdB]
    change 0 < pairing T.group ((productRootEquiv P Q) (Sum.inr a)).val u ↔ _
    rw [hr]
    rfl
  · intro R x
    have hc' : (u ≫ T.inclusion) ≫ fst P.G.val Q.G.val = c ≫ P.T.inclusion := by
      rw [Category.assoc, tensorHom_fst, lift_fst_assoc]
    have hd' : (u ≫ T.inclusion) ≫ snd P.G.val Q.G.val = d ≫ Q.T.inclusion := by
      rw [Category.assoc, tensorHom_snd, lift_snd_assoc]
    refine (D.parabolic_points R x).symm.trans ((product_hasExtension _ x).trans
      (and_congr ?_ ?_))
    · rw [hc']
      exact (L.parabolic_points R _).trans
        ⟨section_of_subgroupOf hcS.2 _ _, section_of_subgroupOf hcS.1 _ _⟩
    · rw [hd']
      exact (M.parabolic_points R _).trans
        ⟨section_of_subgroupOf hdS.2 _ _, section_of_subgroupOf hdS.1 _ _⟩

end SplitProductPair

section ProductPinning

open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory

open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SplitBorelPair PinnedGroup SimpleRoot IsSimple RootCoordinate)
open Specs.RankOneFlag (SameSubgroup)
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open private productTorus productRootEquiv productPointEquiv firstInclusion secondInclusion
  character_comp_mul project_first_torus project_second_torus
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag
open private rootPoint_comp rootPoint_zero from LinearAlgebraicGroups.RootData.RootGroups
open private rootSubgroup_of_coordinate from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private affineProduct from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

variable {k : Type u} [Field k]

private def leftRoot {P Q : SplitBorelPair k} (D : SplitPairProduct P Q) (a : Root P.T) :
    Root D.pair.T := productRootEquiv P Q (Sum.inl a)

private def rightRoot {P Q : SplitBorelPair k} (D : SplitPairProduct P Q) (a : Root Q.T) :
    Root D.pair.T := productRootEquiv P Q (Sum.inr a)

private def leftCharacter {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (χ : Character D.pair.T.group) : Character P.T.group :=
  firstInclusion P.T.group Q.T.group ≫ χ

private def rightCharacter {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (χ : Character D.pair.T.group) : Character Q.T.group :=
  secondInclusion P.T.group Q.T.group ≫ χ

@[simp] private theorem leftCharacter_mul {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a b : Character D.pair.T.group) : leftCharacter D (a * b) =
      leftCharacter D a * leftCharacter D b := character_comp_mul _ _ _

@[simp] private theorem rightCharacter_mul {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a b : Character D.pair.T.group) : rightCharacter D (a * b) =
      rightCharacter D a * rightCharacter D b := character_comp_mul _ _ _

@[simp] private theorem leftCharacter_leftRoot {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root P.T) : leftCharacter D (leftRoot D a).val = a.val := by
  change firstInclusion P.T.group Q.T.group ≫ fst _ _ ≫ a.val = _
  simp only [lift_fst_assoc, Category.id_comp]

@[simp] private theorem leftCharacter_rightRoot {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root Q.T) : leftCharacter D (rightRoot D a).val = 1 := by
  change firstInclusion P.T.group Q.T.group ≫ snd _ _ ≫ a.val = 0
  simp only [lift_snd_assoc, zero_comp]

@[simp] private theorem rightCharacter_leftRoot {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root P.T) : rightCharacter D (leftRoot D a).val = 1 := by
  change secondInclusion P.T.group Q.T.group ≫ fst _ _ ≫ a.val = 0
  simp only [lift_fst_assoc, zero_comp]

@[simp] private theorem rightCharacter_rightRoot {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root Q.T) : rightCharacter D (rightRoot D a).val = a.val := by
  change secondInclusion P.T.group Q.T.group ≫ snd _ _ ≫ a.val = _
  simp only [lift_snd_assoc, Category.id_comp]

private theorem leftRoot_simple {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root P.T) : IsSimple D.pair (leftRoot D a) ↔ IsSimple P a := by
  constructor
  · intro h
    refine ⟨(D.leftPositive a).mp h.1, fun b hb c hc he => h.2
      (leftRoot D b) ((D.leftPositive b).mpr hb)
      (leftRoot D c) ((D.leftPositive c).mpr hc) ?_⟩
    change fst P.T.group Q.T.group ≫ a.val =
      (fst P.T.group Q.T.group ≫ b.val) * (fst P.T.group Q.T.group ≫ c.val)
    rw [he, character_comp_mul]
  · intro h
    refine ⟨(D.leftPositive a).mpr h.1, ?_⟩
    intro b hb c hc he
    obtain ⟨b, rfl⟩ := (productRootEquiv P Q).surjective b
    obtain ⟨c, rfl⟩ := (productRootEquiv P Q).surjective c
    rcases b with b | b <;> rcases c with c | c
    · change (leftRoot D a).val = (leftRoot D b).val * (leftRoot D c).val at he
      exact h.2 b ((D.leftPositive b).mp hb) c ((D.leftPositive c).mp hc)
        (by simpa only [leftCharacter_mul, leftCharacter_leftRoot] using congrArg (leftCharacter D) he)
    · change (leftRoot D a).val = (leftRoot D b).val * (rightRoot D c).val at he
      exact c.property.1 (by simpa only [rightCharacter_mul, rightCharacter_leftRoot,
        rightCharacter_rightRoot, one_mul] using (congrArg (rightCharacter D) he).symm)
    · change (leftRoot D a).val = (rightRoot D b).val * (leftRoot D c).val at he
      exact b.property.1 (by simpa only [rightCharacter_mul, rightCharacter_leftRoot,
        rightCharacter_rightRoot, mul_one] using (congrArg (rightCharacter D) he).symm)
    · change (leftRoot D a).val = (rightRoot D b).val * (rightRoot D c).val at he
      exact a.property.1 (by simpa only [leftCharacter_mul, leftCharacter_leftRoot,
        leftCharacter_rightRoot, mul_one] using congrArg (leftCharacter D) he)

private theorem rightRoot_simple {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root Q.T) : IsSimple D.pair (rightRoot D a) ↔ IsSimple Q a := by
  constructor
  · intro h
    refine ⟨(D.rightPositive a).mp h.1, fun b hb c hc he => h.2
      (rightRoot D b) ((D.rightPositive b).mpr hb)
      (rightRoot D c) ((D.rightPositive c).mpr hc) ?_⟩
    change snd P.T.group Q.T.group ≫ a.val =
      (snd P.T.group Q.T.group ≫ b.val) * (snd P.T.group Q.T.group ≫ c.val)
    rw [he, character_comp_mul]
  · intro h
    refine ⟨(D.rightPositive a).mpr h.1, ?_⟩
    intro b hb c hc he
    obtain ⟨b, rfl⟩ := (productRootEquiv P Q).surjective b
    obtain ⟨c, rfl⟩ := (productRootEquiv P Q).surjective c
    rcases b with b | b <;> rcases c with c | c
    · change (rightRoot D a).val = (leftRoot D b).val * (leftRoot D c).val at he
      exact a.property.1 (by simpa only [rightCharacter_mul, rightCharacter_leftRoot,
        rightCharacter_rightRoot, mul_one] using congrArg (rightCharacter D) he)
    · change (rightRoot D a).val = (leftRoot D b).val * (rightRoot D c).val at he
      exact b.property.1 (by simpa only [leftCharacter_mul, leftCharacter_leftRoot,
        leftCharacter_rightRoot, mul_one] using (congrArg (leftCharacter D) he).symm)
    · change (rightRoot D a).val = (rightRoot D b).val * (leftRoot D c).val at he
      exact c.property.1 (by simpa only [leftCharacter_mul, leftCharacter_leftRoot,
        leftCharacter_rightRoot, one_mul] using (congrArg (leftCharacter D) he).symm)
    · change (rightRoot D a).val = (rightRoot D b).val * (rightRoot D c).val at he
      exact h.2 b ((D.rightPositive b).mp hb) c ((D.rightPositive c).mp hc)
        (by simpa only [rightCharacter_mul, rightCharacter_rightRoot] using congrArg (rightCharacter D) he)

private def productSimpleEquiv {P Q : SplitBorelPair k} (D : SplitPairProduct P Q) :
    (SimpleRoot P ⊕ SimpleRoot Q) ≃ SimpleRoot D.pair := by
  let toRoot : (SimpleRoot P ⊕ SimpleRoot Q) → (Root P.T ⊕ Root Q.T) :=
    Sum.map Subtype.val Subtype.val
  let f : (SimpleRoot P ⊕ SimpleRoot Q) → SimpleRoot D.pair := Sum.elim
    (fun a => ⟨leftRoot D a.val, (leftRoot_simple D _).mpr a.property⟩)
    (fun a => ⟨rightRoot D a.val, (rightRoot_simple D _).mpr a.property⟩)
  have hf (a) : (f a).val = productRootEquiv P Q (toRoot a) := by cases a <;> rfl
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    have h' : toRoot a = toRoot b := (productRootEquiv P Q).injective
      ((hf a).symm.trans ((congrArg Subtype.val h).trans (hf b)))
    exact (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩) h'
  · intro a
    obtain ⟨b, hb⟩ := (productRootEquiv P Q).surjective a.val
    rcases b with b | b
    · have he : leftRoot D b = a.val := hb
      exact ⟨Sum.inl ⟨b, (leftRoot_simple D b).mp (he ▸ a.property)⟩, Subtype.ext he⟩
    · have he : rightRoot D b = a.val := hb
      exact ⟨Sum.inr ⟨b, (rightRoot_simple D b).mp (he ▸ a.property)⟩, Subtype.ext he⟩

@[simp] private theorem productSimpleEquiv_inl {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : SimpleRoot P) : (productSimpleEquiv D (Sum.inl a)).val = leftRoot D a.val := rfl

@[simp] private theorem productSimpleEquiv_inr {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : SimpleRoot Q) : (productSimpleEquiv D (Sum.inr a)).val = rightRoot D a.val := rfl

private def leftSubgroup {G H : AffineAlgebraicGroup k} (U : ClosedSubgroup G.val) :
    ClosedSubgroup (affineProduct G H).val where
  group := U.group
  inclusion := U.inclusion ≫ firstInclusion G.val H.val
  isClosedImmersion := by
    let A := affineProduct G H
    letI := A.property.1
    let π := (fst G.val H.val).hom.hom.left
    haveI : IsSeparated (A.val.X.hom) := inferInstance
    haveI : IsSeparated (π ≫ G.val.X.hom) := by
      change IsSeparated ((fst G.val H.val).hom.hom.left ≫ G.val.X.hom)
      rw [Over.w]
      exact (inferInstance : IsSeparated A.val.X.hom)
    haveI : IsSeparated π := IsSeparated.of_comp π G.val.X.hom
    haveI : IsClosedImmersion ((U.inclusion ≫ firstInclusion G.val H.val).hom.hom.left ≫ π) := by
      change IsClosedImmersion
        (((U.inclusion ≫ firstInclusion G.val H.val) ≫ fst G.val H.val).hom.hom.left)
      rw [Category.assoc, lift_fst, Category.comp_id]
      exact U.isClosedImmersion
    exact IsClosedImmersion.of_comp _ π

private def rightSubgroup {G H : AffineAlgebraicGroup k} (U : ClosedSubgroup H.val) :
    ClosedSubgroup (affineProduct G H).val where
  group := U.group
  inclusion := U.inclusion ≫ secondInclusion G.val H.val
  isClosedImmersion := by
    let A := affineProduct G H
    letI := A.property.1
    let π := (snd G.val H.val).hom.hom.left
    haveI : IsSeparated (A.val.X.hom) := inferInstance
    haveI : IsSeparated (π ≫ H.val.X.hom) := by
      change IsSeparated ((snd G.val H.val).hom.hom.left ≫ H.val.X.hom)
      rw [Over.w]
      exact (inferInstance : IsSeparated A.val.X.hom)
    haveI : IsSeparated π := IsSeparated.of_comp π H.val.X.hom
    haveI : IsClosedImmersion ((U.inclusion ≫ secondInclusion G.val H.val).hom.hom.left ≫ π) := by
      change IsClosedImmersion
        (((U.inclusion ≫ secondInclusion G.val H.val) ≫ snd G.val H.val).hom.hom.left)
      rw [Category.assoc, lift_snd, Category.comp_id]
      exact U.isClosedImmersion
    exact IsClosedImmersion.of_comp _ π

@[simp] private theorem projectPoint_mul {G H : GroupScheme k} (f : G ⟶ H) {R : TestAlgebra k}
    (x y : GroupPoints G R) : projectPoint f (x * y) = projectPoint f x * projectPoint f y :=
  map_mul (((groupPointsFunctor k).map f).app R).hom x y

@[simp] private theorem projectPoint_inv {G H : GroupScheme k} (f : G ⟶ H) {R : TestAlgebra k}
    (x : GroupPoints G R) : projectPoint f x⁻¹ = (projectPoint f x)⁻¹ :=
  map_inv (((groupPointsFunctor k).map f).app R).hom x

@[simp] private theorem projectPoint_one {G H : GroupScheme k} (f : G ⟶ H) {R : TestAlgebra k} :
    projectPoint f (1 : GroupPoints G R) = 1 := map_one (((groupPointsFunctor k).map f).app R).hom

private theorem projectPoint_root {A : AdditiveLine k} {G H : GroupScheme k} (f : G ⟶ H)
    (x : A.group ⟶ G) (R : TestAlgebra k) (a : R) :
    projectPoint f (rootPoint x R a) = rootPoint (x ≫ f) R a :=
  (rootPoint_comp x f R a).symm

private theorem leftPin_scalarAction {A : AdditiveLine k} {P Q : SplitBorelPair k}
    (D : SplitPairProduct P Q) (a : Root P.T) (x : A.group ⟶ P.G.val)
    (hx : HasScalarAction P.T a.val x) :
    HasScalarAction D.pair.T (leftRoot D a).val (x ≫ firstInclusion P.G.val Q.G.val) := by
  intro R t u
  let G := P.G.val
  let H := Q.G.val
  let g : GroupPoints (G ⊗ H) R := projectPoint D.pair.T.inclusion t
  let t' := projectPoint (fst P.T.group Q.T.group) t
  let z := projectPoint (firstInclusion G H) (rootPoint x R u)
  let v := characterValue (leftRoot D a).val R t * u
  change g * rootPoint (x ≫ firstInclusion G H) R u * g⁻¹ =
    rootPoint (x ≫ firstInclusion G H) R v
  rw [← projectPoint_root, ← projectPoint_root]
  apply (productPointEquiv G H R).injective
  apply Prod.ext
  · change projectPoint (fst G H) (g * z * g⁻¹) =
      projectPoint (fst G H) (projectPoint (firstInclusion G H) (rootPoint x R v))
    simp only [projectPoint_mul, projectPoint_inv, z, projectPoint_comp, lift_fst, projectPoint_id]
    have hg : projectPoint (fst G H) g = projectPoint P.T.inclusion t' := by
      change projectPoint (fst G H) (projectPoint (P.T.inclusion ⊗ₘ Q.T.inclusion) t) = _
      dsimp only [t']
      rw [projectPoint_comp, projectPoint_comp]
      exact congrArg (fun f => projectPoint f t) (tensorHom_fst P.T.inclusion Q.T.inclusion)
    rw [hg]
    have hv : v = characterValue a.val R t' * u := by
      change characterValue (fst P.T.group Q.T.group ≫ a.val) R t * u = _
      rfl
    rw [hv]
    exact hx R t' u
  · change projectPoint (snd G H) (g * z * g⁻¹) =
      projectPoint (snd G H) (projectPoint (firstInclusion G H) (rootPoint x R v))
    simp only [projectPoint_mul, projectPoint_inv, z, projectPoint_comp, lift_snd,
      projectPoint_zero, mul_one, mul_inv_cancel]

private theorem rightPin_scalarAction {A : AdditiveLine k} {P Q : SplitBorelPair k}
    (D : SplitPairProduct P Q) (a : Root Q.T) (x : A.group ⟶ Q.G.val)
    (hx : HasScalarAction Q.T a.val x) :
    HasScalarAction D.pair.T (rightRoot D a).val (x ≫ secondInclusion P.G.val Q.G.val) := by
  intro R t u
  let G := P.G.val
  let H := Q.G.val
  let g : GroupPoints (G ⊗ H) R := projectPoint D.pair.T.inclusion t
  let t' := projectPoint (snd P.T.group Q.T.group) t
  let z := projectPoint (secondInclusion G H) (rootPoint x R u)
  let v := characterValue (rightRoot D a).val R t * u
  change g * rootPoint (x ≫ secondInclusion G H) R u * g⁻¹ =
    rootPoint (x ≫ secondInclusion G H) R v
  rw [← projectPoint_root, ← projectPoint_root]
  apply (productPointEquiv G H R).injective
  apply Prod.ext
  · change projectPoint (fst G H) (g * z * g⁻¹) =
      projectPoint (fst G H) (projectPoint (secondInclusion G H) (rootPoint x R v))
    simp only [projectPoint_mul, projectPoint_inv, z, projectPoint_comp, lift_fst,
      projectPoint_zero, mul_one, mul_inv_cancel]
  · change projectPoint (snd G H) (g * z * g⁻¹) =
      projectPoint (snd G H) (projectPoint (secondInclusion G H) (rootPoint x R v))
    simp only [projectPoint_mul, projectPoint_inv, z, projectPoint_comp, lift_snd, projectPoint_id]
    have hg : projectPoint (snd G H) g = projectPoint Q.T.inclusion t' := by
      change projectPoint (snd G H) (projectPoint (P.T.inclusion ⊗ₘ Q.T.inclusion) t) = _
      dsimp only [t']
      rw [projectPoint_comp, projectPoint_comp]
      exact congrArg (fun f => projectPoint f t) (tensorHom_snd P.T.inclusion Q.T.inclusion)
    rw [hg]
    have hv : v = characterValue a.val R t' * u := by
      change characterValue (snd P.T.group Q.T.group ≫ a.val) R t * u = _
      rfl
    rw [hv]
    exact hx R t' u

private def pinnedRootCoordinate {A : AdditiveLine k} (P : PinnedGroup A) (i : SimpleRoot P.pair) :
    A.group ⟶ P.pair.G.val := (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion

private theorem transferProductPin {A : AdditiveLine k} (P : SplitBorelPair k)
    (a : Root P.T) (U V : ClosedSubgroup P.G.val) (hV : IsRootSubgroup P.T V a.val)
    (p : RootCoordinate A P.T U a.val) (hU : IsRootSubgroup P.T U a.val) :
    ∃ q : RootCoordinate A P.T V a.val, q.val.hom ≫ V.inclusion = p.val.hom ≫ U.inclusion := by
  obtain ⟨_, _, W, _, _, _, _, huniq⟩ :=
    (RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2 a.val a.property
  have h : SameSubgroup U V := by
    constructor
    · obtain ⟨f, hf⟩ := (huniq U hU).2
      obtain ⟨g, hg⟩ := (huniq V hV).1
      exact ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩
    · obtain ⟨f, hf⟩ := (huniq V hV).2
      obtain ⟨g, hg⟩ := (huniq U hU).1
      exact ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩
  obtain ⟨e, he⟩ := subgroupIso_of_same h
  have hcomm : (p.val ≪≫ e).hom ≫ V.inclusion = p.val.hom ≫ U.inclusion := by
    change (p.val.hom ≫ e.hom) ≫ V.inclusion = _
    rw [Category.assoc, he]
  exact ⟨⟨p.val ≪≫ e, hcomm.symm ▸ p.property⟩, hcomm⟩

private structure PinnedProduct {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : SplitPairProduct P.pair Q.pair) where
  roots : RootSubgroupFamily D.pair.T
  pin : Specs.Pinning.Pinning A D.pair roots
  leftPin : ∀ a : SimpleRoot P.pair,
    let b := productSimpleEquiv D (Sum.inl a)
    (pin b).val.hom ≫ (roots b.val).val.inclusion =
      pinnedRootCoordinate P a ≫ firstInclusion P.pair.G.val Q.pair.G.val
  rightPin : ∀ a : SimpleRoot Q.pair,
    let b := productSimpleEquiv D (Sum.inr a)
    (pin b).val.hom ≫ (roots b.val).val.inclusion =
      pinnedRootCoordinate Q a ≫ secondInclusion P.pair.G.val Q.pair.G.val

private abbrev PinnedProduct.pinned {A : AdditiveLine k} {P Q : PinnedGroup A}
    {D : SplitPairProduct P.pair Q.pair} (M : PinnedProduct P Q D) : PinnedGroup A :=
  ⟨D.pair, M.roots, M.pin⟩

private theorem existsPinnedProduct {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : SplitPairProduct P.pair Q.pair) : Nonempty (PinnedProduct P Q D) := by
  classical
  obtain ⟨V, _⟩ := Classification.Pinning.pinningsExist A D.pair
  let e := productSimpleEquiv D
  let z : (SimpleRoot P.pair ⊕ SimpleRoot Q.pair) → (A.group ⟶ D.pair.G.val) :=
    Sum.elim (fun a => pinnedRootCoordinate P a ≫ firstInclusion P.pair.G.val Q.pair.G.val)
      (fun a => pinnedRootCoordinate Q a ≫ secondInclusion P.pair.G.val Q.pair.G.val)
  have hex (b : SimpleRoot D.pair) :
      ∃ q : RootCoordinate A D.pair.T (V b.val).val b.val.val,
        q.val.hom ≫ (V b.val).val.inclusion = z (e.symm b) := by
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [e.symm_apply_apply]
    rcases a with a | a
    · let U : ClosedSubgroup D.pair.G.val := leftSubgroup (P.roots a.val).val
      let p : RootCoordinate A D.pair.T U (e (Sum.inl a)).val.val :=
        ⟨(P.pin a).val, by
          change HasScalarAction D.pair.T (leftRoot D a.val).val
            ((P.pin a).val.hom ≫ ((P.roots a.val).val.inclusion ≫ firstInclusion _ _))
          rw [← Category.assoc]
          exact leftPin_scalarAction D a.val (pinnedRootCoordinate P a) (P.pin a).property⟩
      have hU := rootSubgroup_of_coordinate p (P.roots a.val).property.1 (P.roots a.val).property.2.1
      obtain ⟨q, hq⟩ := transferProductPin D.pair (e (Sum.inl a)).val U
        (V (e (Sum.inl a)).val).val (V (e (Sum.inl a)).val).property p hU
      exact ⟨q, hq.trans (Category.assoc _ _ _).symm⟩
    · let U : ClosedSubgroup D.pair.G.val := rightSubgroup (Q.roots a.val).val
      let p : RootCoordinate A D.pair.T U (e (Sum.inr a)).val.val :=
        ⟨(Q.pin a).val, by
          change HasScalarAction D.pair.T (rightRoot D a.val).val
            ((Q.pin a).val.hom ≫ ((Q.roots a.val).val.inclusion ≫ secondInclusion _ _))
          rw [← Category.assoc]
          exact rightPin_scalarAction D a.val (pinnedRootCoordinate Q a) (Q.pin a).property⟩
      have hU := rootSubgroup_of_coordinate p (Q.roots a.val).property.1 (Q.roots a.val).property.2.1
      obtain ⟨q, hq⟩ := transferProductPin D.pair (e (Sum.inr a)).val U
        (V (e (Sum.inr a)).val).val (V (e (Sum.inr a)).val).property p hU
      exact ⟨q, hq.trans (Category.assoc _ _ _).symm⟩
  choose q hq using hex
  refine ⟨V, q, fun a => ?_, fun a => ?_⟩
  · have h := hq (e (Sum.inl a))
    rw [e.symm_apply_apply] at h
    exact h
  · have h := hq (e (Sum.inr a))
    rw [e.symm_apply_apply] at h
    exact h

end ProductPinning

section MatrixProducts

open Matrix
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory Classical
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SplitBorelPair PinnedGroup AttachedDatum SimpleRoot IsSimple)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter compositionPairing)
open Specs.CharacterPairing (pairing)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.SpecialLinearDatum (coordinatePairUnits)
open Specs.SimplyConnectedLattice (corootLattice)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private productTorus productPointEquiv productRootEquiv firstInclusion secondInclusion
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag
open private base_isPos_iff_subgroupRoots from LinearAlgebraicGroups.Classification.PinnedEquivalence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]

private abbrev rankOneGroup (k : Type u) [Field k] : AffineAlgebraicGroup k :=
  StandardGroups.specialLinearGroup k (ULift.{u} (Fin 2))

private def rankOnePointsIso (k : Type u) [Field k] :
    (groupPointsFunctor k).obj (rankOneGroup k).val ≅ specialLinearPointsOfSize 2 k :=
  StandardGroups.specialLinearGroupPointsIso k (ULift.{u} (Fin 2)) ≪≫
    NatIso.ofComponents (G := specialLinearPointsOfSize 2 k)
      (fun R => MulEquiv.toGrpIso (reindexSpecialLinear (R := R) Equiv.ulift)) (by
        intro R T h
        apply GrpCat.ext
        intro g
        exact Subtype.ext rfl)

private def rankOneRoot {R : Type u} [CommRing R] (a : R) : SpecialLinearGroup (Fin 2) R :=
  SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) a

private def rankOneCoroot {R : Type u} [CommRing R] (t : Rˣ) : SpecialLinearGroup (Fin 2) R :=
  ⟨Matrix.diagonal ![(t : R), (↑t⁻¹ : R)], by rw [Matrix.det_fin_two]; simp⟩

private def factorPoint {I : Type u} {G : Type u} [One G] (i : I) (x : G) : I → G :=
  fun j => if _ : j = i then x else 1

@[simp] private theorem factorPoint_same {I G : Type u} [One G] (i : I) (x : G) :
    factorPoint i x i = x := by simp [factorPoint]

@[simp] private theorem factorPoint_ne {I G : Type u} [One G] {i j : I} (h : j ≠ i) (x : G) :
    factorPoint i x j = 1 := by simp [factorPoint, h]

private def reindexFamilyPoints {I J : Type u} (e : I ≃ J) :
    specialLinearFamilyPoints k I 2 ≅ specialLinearFamilyPoints k J 2 :=
  NatIso.ofComponents (F := specialLinearFamilyPoints k I 2) (G := specialLinearFamilyPoints k J 2)
    (fun R => MulEquiv.toGrpIso
    ({ toFun := fun x j => x (e.symm j)
       invFun := fun x i => x (e i)
       left_inv := fun x => funext fun i => congrArg x (e.symm_apply_apply i)
       right_inv := fun x => funext fun j => congrArg x (e.apply_symm_apply j)
       map_mul' := fun _ _ => rfl } :
      (I → SpecialLinearGroup (Fin 2) R) ≃* (J → SpecialLinearGroup (Fin 2) R))) (by
        intro R S f
        apply GrpCat.ext
        intro g
        rfl)

private def binaryFamilyPoints {G H : GroupScheme k} {I J : Type u}
    (a : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2)
    (b : (groupPointsFunctor k).obj H ≅ specialLinearFamilyPoints k J 2) :
    (groupPointsFunctor k).obj (G ⊗ H) ≅ specialLinearFamilyPoints k (I ⊕ J) 2 :=
  NatIso.ofComponents (fun R => MulEquiv.toGrpIso
    ((productPointEquiv G H R).trans
      (((a.app R).groupIsoToMulEquiv.prodCongr (b.app R).groupIsoToMulEquiv).trans
        ({ toEquiv := (Equiv.sumPiEquivProdPi
          (fun _ : I ⊕ J => SpecialLinearGroup (Fin 2) R)).symm,
           map_mul' := fun _ _ => funext fun j => by cases j <;> rfl } :
          ((I → SpecialLinearGroup (Fin 2) R) × (J → SpecialLinearGroup (Fin 2) R)) ≃*
            ((I ⊕ J) → SpecialLinearGroup (Fin 2) R))))) (by
              intro R S f
              apply GrpCat.ext
              intro x
              funext i
              cases i with
              | inl i =>
                have h := a.hom.naturality_apply f (projectPoint (fst G H) x)
                exact congrFun ((congrArg (a.hom.app S) (projectPoint_natural (fst G H) f x).symm).trans h) i
              | inr i =>
                have h := b.hom.naturality_apply f (projectPoint (snd G H) x)
                exact congrFun ((congrArg (b.hom.app S) (projectPoint_natural (snd G H) f x).symm).trans h) i)

private theorem projectPoint_cochar {G H : GroupScheme k} (f : G ⟶ H) (c : Cocharacter G)
    (R : TestAlgebra k) (t : Rˣ) :
    projectPoint f (cocharacterPoint c R t) = cocharacterPoint (c ≫ f) R t :=
  mappedTorusPoint c f R t

private theorem cocharacterPoint_zero {G : GroupScheme k} (R : TestAlgebra k) (v : Rˣ) :
    cocharacterPoint (0 : Cocharacter G) R v = 1 := by
  change projectPoint (0 : _ ⟶ G) _ = _
  exact projectPoint_zero _

private def cocharacterProduct (G H : GroupScheme k) [IsCommMonObj G.X] [IsCommMonObj H.X]
    [IsCommMonObj (G ⊗ H).X] :
    Additive (Cocharacter (G ⊗ H)) ≃ₗ[ℤ] (Additive (Cocharacter G) × Additive (Cocharacter H)) := by
  let e : Cocharacter (G ⊗ H) ≃* (Cocharacter G × Cocharacter H) :=
    { toFun := fun f => (f ≫ fst G H, f ≫ snd G H)
      invFun := fun f => lift f.1 f.2
      left_inv := lift_comp_fst_snd
      right_inv := fun _ => Prod.ext (lift_fst _ _) (lift_snd _ _)
      map_mul' := by
        intro a b
        let f : _ ⟶ (G ⊗ H).X := a.hom.hom
        let g : _ ⟶ (G ⊗ H).X := b.hom.hom
        apply Prod.ext
        · apply Grp.hom_ext
          change (f * g) ≫ fst G.X H.X = _
          exact MonObj.mul_comp f g (fst G.X H.X)
        · apply Grp.hom_ext
          change (f * g) ≫ snd G.X H.X = _
          exact MonObj.mul_comp f g (snd G.X H.X) }
  exact AddEquiv.toIntLinearEquiv
    ({ toEquiv := e.toEquiv, map_add' := e.map_mul } :
      Additive (Cocharacter (G ⊗ H)) ≃+
        (Additive (Cocharacter G) × Additive (Cocharacter H)))

private theorem productRoot_pairingLeft {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root P.T) (c : Cocharacter D.pair.T.group) :
    pairing D.pair.T.group (leftRoot D a).val c =
      pairing P.T.group a.val (c ≫ fst P.T.group Q.T.group) := by
  unfold pairing compositionPairing
  change Function.invFun _ (c ≫ fst P.T.group Q.T.group ≫ a.val) =
    Function.invFun _ ((c ≫ fst P.T.group Q.T.group) ≫ a.val)
  rw [Category.assoc]

private theorem productRoot_pairingRight {P Q : SplitBorelPair k} (D : SplitPairProduct P Q)
    (a : Root Q.T) (c : Cocharacter D.pair.T.group) :
    pairing D.pair.T.group (rightRoot D a).val c =
      pairing Q.T.group a.val (c ≫ snd P.T.group Q.T.group) := by
  unfold pairing compositionPairing
  change Function.invFun _ (c ≫ snd P.T.group Q.T.group ≫ a.val) =
    Function.invFun _ ((c ≫ snd P.T.group Q.T.group) ≫ a.val)
  rw [Category.assoc]

private structure MatrixProduct (A : AdditiveLine k) (I : Type u) where
  P : PinnedGroup A
  label : I ≃ SimpleRoot P.pair
  D : AttachedDatum P.pair
  basis : letI := D.comm; Basis I ℤ (Additive (Cocharacter P.pair.T.group))
  pairing_basis : letI := D.comm; ∀ i j,
    pairing P.pair.T.group (label j).val.val (Additive.toMul (basis i)) =
      if _ : i = j then 2 else 0
  positiveSimple : ∀ a ∈ subgroupRoots P.pair.T P.pair.B, IsSimple P.pair a
  points : (groupPointsFunctor k).obj P.pair.G.val ≅ specialLinearFamilyPoints k I 2
  torus : ∀ (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R),
    subgroupSection P.pair.T g ↔ ∀ i, MatrixMark.torus.Holds (points.hom.app R g i)
  borel : ∀ (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R),
    subgroupSection P.pair.B g ↔ ∀ i, MatrixMark.positiveBorel.Holds (points.hom.app R g i)
  root_point : ∀ (i : I) (R : TestAlgebra k) (a : R),
    points.hom.app R (rootPoint (pinnedRootCoordinate P (label i)) R a) =
      factorPoint i (rankOneRoot a)
  cochar_point : letI := D.comm; ∀ (i : I) (R : TestAlgebra k) (v : Rˣ),
    points.hom.app R (projectPoint P.pair.T.inclusion
      (cocharacterPoint (Additive.toMul (basis i)) R v)) = factorPoint i (rankOneCoroot v)

private theorem MatrixProduct.pairing_zero {A : AdditiveLine k} {I : Type u} (M : MatrixProduct A I)
    (j : I) : pairing M.P.pair.T.group (M.label j).val.val 0 = 0 := by
  letI := M.D.comm
  rw [← M.D.datum.pairing_eq]
  exact (M.D.datum.rootDatum.toLinearMap _).map_zero

private def MatrixProduct.reindex {A : AdditiveLine k} {I J : Type u} (M : MatrixProduct A I)
    (e : I ≃ J) : MatrixProduct A J where
  P := M.P
  label := e.symm.trans M.label
  D := M.D
  basis := letI := M.D.comm; M.basis.reindex e
  pairing_basis := by
    intro i j
    simp only [Equiv.trans_apply, Basis.reindex_apply, M.pairing_basis, e.symm.injective.eq_iff]
  positiveSimple := M.positiveSimple
  points := M.points ≪≫ reindexFamilyPoints e
  torus R x := by
    change subgroupSection M.P.pair.T x ↔
      ∀ j, MatrixMark.torus.Holds (M.points.hom.app R x (e.symm j))
    exact (M.torus R x).trans ⟨fun h j => h _, fun h i => by simpa using h (e i)⟩
  borel R x := by
    change subgroupSection M.P.pair.B x ↔
      ∀ j, MatrixMark.positiveBorel.Holds (M.points.hom.app R x (e.symm j))
    exact (M.borel R x).trans ⟨fun h j => h _, fun h i => by simpa using h (e i)⟩
  root_point i R a := by
    funext j
    change M.points.hom.app R (rootPoint (pinnedRootCoordinate M.P (M.label (e.symm i))) R a)
      (e.symm j) = _
    rw [M.root_point]
    by_cases he : j = i
    · subst j
      simp only [factorPoint_same]
    · rw [factorPoint_ne he, factorPoint_ne (fun h => he (e.symm.injective h))]
  cochar_point i R v := by
    funext j
    simp only [Basis.reindex_apply]
    change M.points.hom.app R (projectPoint M.P.pair.T.inclusion
      (cocharacterPoint (Additive.toMul (M.basis (e.symm i))) R v)) (e.symm j) = _
    rw [M.cochar_point]
    by_cases he : j = i
    · subst j
      simp only [factorPoint_same]
    · rw [factorPoint_ne he, factorPoint_ne (fun h => he (e.symm.injective h))]

private theorem rankOneMatrixProduct (A : AdditiveLine k) : Nonempty (MatrixProduct A (ULift.{u} (Fin 1))) := by
  classical
  let S := rankOneGroup k
  let s := StandardGroups.specialLinearGroupPointsIso k (ULift.{u} (Fin 2))
  obtain ⟨T, L, M, B, D, U, q, e, hD, hsc, he, _, hroot, hcor⟩ := signedMatrixPinning A 1 S s
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  let P : PinnedGroup A := ⟨B.pair, U, q⟩
  let j : ULift.{u} (Fin 1) ≃ SimpleRoot P.pair :=
    Equiv.ulift.trans (e.trans (Equiv.subtypeEquivRight D.simple_iff))
  let C := D.datum.rootDatum
  have hsc' : corootLattice D = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion S
      (RootData.SpecialLinearDatum.semisimple k 1 S s) T.subgroup T.split B.maximal D.datum).mp hsc
  have hspan : Submodule.span ℤ (Set.range fun i : D.base.support => C.coroot i.val) = ⊤ := by
    change Submodule.span ℤ (Set.range fun i : (↑D.base.support : Set (Root B.pair.T)) =>
      D.datum.rootDatum.coroot i.val) = ⊤
    rw [← Set.image_eq_range, D.base.span_int_coroot_support]
    exact hsc'
  let c := (Basis.mk D.base.linearIndepOn_coroot hspan.ge).reindex (e.symm.trans Equiv.ulift.symm)
  have hc (i : ULift.{u} (Fin 1)) : c i = C.coroot (e i.down).val := by
    simp [c, C]
  let p : (groupPointsFunctor k).obj S.val ≅ specialLinearFamilyPoints k (ULift.{u} (Fin 1)) 2 :=
    rankOnePointsIso k ≪≫ NatIso.ofComponents
      (G := specialLinearFamilyPoints k (ULift.{u} (Fin 1)) 2)
      (fun R => MulEquiv.toGrpIso
        ({ toFun := fun x _ => x
           invFun := fun x => x ⟨0⟩
           left_inv := fun _ => rfl
           right_inv := fun x => funext fun i => congrArg x (Subsingleton.elim ⟨0⟩ i)
           map_mul' := fun _ _ => rfl } :
          SpecialLinearGroup (Fin 2) R ≃* (ULift.{u} (Fin 1) → SpecialLinearGroup (Fin 2) R))) (by
            intro R S f
            apply GrpCat.ext
            intro x
            rfl)
  refine ⟨⟨P, j, D, c, ?_, ?_, p, ?_, ?_, ?_, ?_⟩⟩
  · intro i l
    have hi : l = i := Subsingleton.elim _ _
    subst l
    rw [hc, dite_eq_left rfl, ← D.datum.pairing_eq, ← D.datum.root_eq]
    exact C.root_coroot_two (e i.down).val
  · intro a ha
    obtain ⟨b, rfl⟩ := M.indices.surjective a
    have hb := (B.positive_iff b).mp ha
    have h1 : b.val.1 = 0 := by
      have := Fin.isLt b.val.2
      apply Fin.ext
      change b.val.1.val = 0
      omega
    have h2 : b.val.2 = 1 := by
      have := Fin.isLt b.val.2
      apply Fin.ext
      change b.val.2.val = 1
      omega
    exact (D.simple_iff _).mp ((hD.2 b).mpr ⟨0, h1, h2⟩)
  · intro R x
    exact (T.range R x).trans ⟨fun h _ i l hn =>
      h ⟨i⟩ ⟨l⟩ (fun he => hn (congrArg ULift.down he)),
      fun h i l hn => h ⟨0⟩ i.down l.down (fun he => hn (ULift.ext he))⟩
  · intro R x
    exact (B.matrix R x).trans ⟨fun h _ i l hl => h (show (⟨l⟩ : ULift.{u} (Fin 2)) < ⟨i⟩ from hl),
      fun h i l hl => h ⟨0⟩ (show l.down < i.down from hl)⟩
  · intro i R a
    funext l
    rw [show l = i from Subsingleton.elim l i, factorPoint_same]
    apply Subtype.ext
    ext b d
    have hh := congrArg (fun m : Matrix (ULift.{u} (Fin 2)) _ R => m ⟨b⟩ ⟨d⟩) (hroot i.down R a)
    change (s.hom.app R (rootPoint (pinnedRootCoordinate P (j i)) R a)).val ⟨b⟩ ⟨d⟩ =
      (rankOneRoot a).val b d
    rw [rankOneRoot, SpecialLinearGroup.transvection_coe]
    have hi : i = ⟨0⟩ := Subsingleton.elim _ _
    subst i
    exact hh.trans (by simp [signedParameter, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      ULift.ext_iff])
  · intro i R v
    funext l
    rw [show l = i from Subsingleton.elim l i, factorPoint_same]
    apply Subtype.ext
    ext b d
    have hh := congrArg (fun m : Matrix (ULift.{u} (Fin 2)) _ R => m ⟨b⟩ ⟨d⟩) (hcor i.down R v)
    change (s.hom.app R (cocharacterPoint (Additive.toMul (c i)) R v ≫ T.subgroup.inclusion.hom.hom)).val
      ⟨b⟩ ⟨d⟩ = (rankOneCoroot v).val b d
    rw [hc]
    refine hh.trans ?_
    have hi : i = ⟨0⟩ := Subsingleton.elim _ _
    subst i
    fin_cases b <;> fin_cases d <;> simp [rankOneCoroot, coordinatePairUnits]

private theorem rankProduct {A : AdditiveLine k} {I J : Type u} (M : MatrixProduct A I)
    (N : MatrixProduct A J) : Nonempty (MatrixProduct A (I ⊕ J)) := by
  classical
  obtain ⟨D⟩ := existsSplitPairProduct M.P.pair N.P.pair
  obtain ⟨P⟩ := existsPinnedProduct M.P N.P D
  let E := Classification.Pinning.attachedDatum D.pair
  letI := M.D.comm
  letI := N.D.comm
  letI := E.comm
  let T := M.P.pair.T.group
  let U := N.P.pair.T.group
  let G := M.P.pair.G.val
  let H := N.P.pair.G.val
  let j := (Equiv.sumCongr M.label N.label).trans (productSimpleEquiv D)
  letI : IsCommMonObj (T ⊗ U).X := E.comm
  let e : Additive (Cocharacter D.pair.T.group) ≃ₗ[ℤ]
      (Additive (Cocharacter T) × Additive (Cocharacter U)) := cocharacterProduct T U
  let c := (M.basis.prod N.basis).map e.symm
  let p : (groupPointsFunctor k).obj P.pinned.pair.G.val ≅ specialLinearFamilyPoints k (I ⊕ J) 2 :=
    binaryFamilyPoints M.points N.points
  have proj (a : I ⊕ J) :
      e (c a) = (M.basis.prod N.basis) a := by
    rw [show c a = e.symm ((M.basis.prod N.basis) a) from Basis.map_apply _ _ _]
    exact e.apply_symm_apply _
  have cLf (i : I) : Additive.toMul (c (Sum.inl i)) ≫ fst T U = Additive.toMul (M.basis i) :=
    (congrArg Prod.fst (proj (Sum.inl i))).trans (Basis.prod_apply_inl_fst M.basis N.basis i)
  have cLs (i : I) : Additive.toMul (c (Sum.inl i)) ≫ snd T U = 0 :=
    (congrArg Prod.snd (proj (Sum.inl i))).trans (Basis.prod_apply_inl_snd M.basis N.basis i)
  have cRf (i : J) : Additive.toMul (c (Sum.inr i)) ≫ fst T U = 0 :=
    (congrArg Prod.fst (proj (Sum.inr i))).trans (Basis.prod_apply_inr_fst M.basis N.basis i)
  have cRs (i : J) : Additive.toMul (c (Sum.inr i)) ≫ snd T U = Additive.toMul (N.basis i) :=
    (congrArg Prod.snd (proj (Sum.inr i))).trans (Basis.prod_apply_inr_snd M.basis N.basis i)
  refine ⟨⟨P.pinned, j, E, c, ?_, ?_, p, ?_, ?_, ?_, ?_⟩⟩
  · intro i l
    cases i with
    | inl i =>
      cases l with
      | inl l =>
        change pairing _ (leftRoot D (M.label l).val).val (Additive.toMul (c (Sum.inl i))) = _
        rw [productRoot_pairingLeft D]
        change pairing _ (M.label l).val.val
          (Additive.toMul (c (Sum.inl i)) ≫ fst T U) = _
        rw [cLf, M.pairing_basis]
        simp
      | inr l =>
        change pairing _ (rightRoot D (N.label l).val).val (Additive.toMul (c (Sum.inl i))) = _
        rw [productRoot_pairingRight D]
        change pairing _ (N.label l).val.val
          (Additive.toMul (c (Sum.inl i)) ≫ snd T U) = _
        rw [cLs, N.pairing_zero]
        simp
    | inr i =>
      cases l with
      | inl l =>
        change pairing _ (leftRoot D (M.label l).val).val (Additive.toMul (c (Sum.inr i))) = _
        rw [productRoot_pairingLeft D]
        change pairing _ (M.label l).val.val
          (Additive.toMul (c (Sum.inr i)) ≫ fst T U) = _
        rw [cRf, M.pairing_zero]
        simp
      | inr l =>
        change pairing _ (rightRoot D (N.label l).val).val (Additive.toMul (c (Sum.inr i))) = _
        rw [productRoot_pairingRight D]
        change pairing _ (N.label l).val.val
          (Additive.toMul (c (Sum.inr i)) ≫ snd T U) = _
        rw [cRs, N.pairing_basis]
        simp
  · intro a h
    obtain ⟨a, rfl⟩ := (productRootEquiv M.P.pair N.P.pair).surjective a
    rcases a with a | a
    · exact (leftRoot_simple D a).mpr (M.positiveSimple a ((D.leftPositive a).mp h))
    · exact (rightRoot_simple D a).mpr (N.positiveSimple a ((D.rightPositive a).mp h))
  · intro R x
    exact (product_subgroupSection M.P.pair.T N.P.pair.T x).trans
      ((and_congr (M.torus R _) (N.torus R _)).trans
        ⟨fun h i => Sum.rec (motive := fun i => MatrixMark.torus.Holds (p.hom.app R x i))
          h.1 h.2 i, fun h => ⟨fun i => h (Sum.inl i), fun i => h (Sum.inr i)⟩⟩)
  · intro R x
    exact (D.borelSections R x).trans ((and_congr (M.borel R _) (N.borel R _)).trans
      ⟨fun h i => Sum.rec (motive := fun i => MatrixMark.positiveBorel.Holds (p.hom.app R x i))
        h.1 h.2 i, fun h => ⟨fun i => h (Sum.inl i), fun i => h (Sum.inr i)⟩⟩)
  · intro i R a
    cases i with
    | inl i =>
      have hi : pinnedRootCoordinate P.pinned (j (Sum.inl i)) =
          pinnedRootCoordinate M.P (M.label i) ≫ firstInclusion G H := P.leftPin (M.label i)
      rw [hi, ← projectPoint_root]
      funext l
      cases l with
      | inl l =>
        change M.points.hom.app R (projectPoint (fst G H)
          (projectPoint (firstInclusion G H) (rootPoint (pinnedRootCoordinate M.P (M.label i)) R a))) l = _
        simp only [projectPoint_comp, lift_fst, projectPoint_id, M.root_point]
        by_cases hl : l = i
        · subst l; simp only [factorPoint_same]
        · rw [factorPoint_ne hl, factorPoint_ne (fun h => hl (Sum.inl.inj h))]
      | inr l =>
        change N.points.hom.app R (projectPoint (snd G H)
          (projectPoint (firstInclusion G H) (rootPoint (pinnedRootCoordinate M.P (M.label i)) R a))) l = _
        rw [factorPoint_ne (by simp), projectPoint_comp, lift_snd, projectPoint_zero, map_one]
        rfl
    | inr i =>
      have hi : pinnedRootCoordinate P.pinned (j (Sum.inr i)) =
          pinnedRootCoordinate N.P (N.label i) ≫ secondInclusion G H := P.rightPin (N.label i)
      rw [hi, ← projectPoint_root]
      funext l
      cases l with
      | inl l =>
        change M.points.hom.app R (projectPoint (fst G H)
          (projectPoint (secondInclusion G H) (rootPoint (pinnedRootCoordinate N.P (N.label i)) R a))) l = _
        rw [factorPoint_ne (by simp), projectPoint_comp, lift_fst, projectPoint_zero, map_one]
        rfl
      | inr l =>
        change N.points.hom.app R (projectPoint (snd G H)
          (projectPoint (secondInclusion G H) (rootPoint (pinnedRootCoordinate N.P (N.label i)) R a))) l = _
        simp only [projectPoint_comp, lift_snd, projectPoint_id, N.root_point]
        by_cases hl : l = i
        · subst l; simp only [factorPoint_same]
        · rw [factorPoint_ne hl, factorPoint_ne (fun h => hl (Sum.inr.inj h))]
  · intro i R v
    have hfst : D.pair.T.inclusion ≫ fst G H = fst T U ≫ M.P.pair.T.inclusion :=
      tensorHom_fst M.P.pair.T.inclusion N.P.pair.T.inclusion
    have hsnd : D.pair.T.inclusion ≫ snd G H = snd T U ≫ N.P.pair.T.inclusion :=
      tensorHom_snd M.P.pair.T.inclusion N.P.pair.T.inclusion
    funext l
    cases l with
    | inl l =>
      change M.points.hom.app R (projectPoint (fst G H) (projectPoint D.pair.T.inclusion
        (cocharacterPoint (Additive.toMul (c i)) R v))) l = _
      rw [projectPoint_comp, hfst, ← projectPoint_comp, projectPoint_cochar]
      cases i with
      | inl i =>
        rw [cLf, M.cochar_point]
        by_cases hl : l = i
        · subst l; simp only [factorPoint_same]
        · rw [factorPoint_ne hl, factorPoint_ne (fun h => hl (Sum.inl.inj h))]
      | inr i =>
        rw [cRf, cocharacterPoint_zero, projectPoint_one, map_one,
          factorPoint_ne (by simp)]
        rfl
    | inr l =>
      change N.points.hom.app R (projectPoint (snd G H) (projectPoint D.pair.T.inclusion
        (cocharacterPoint (Additive.toMul (c i)) R v))) l = _
      rw [projectPoint_comp, hsnd, ← projectPoint_comp, projectPoint_cochar]
      cases i with
      | inl i =>
        rw [cLs, cocharacterPoint_zero, projectPoint_one, map_one,
          factorPoint_ne (by simp)]
        rfl
      | inr i =>
        rw [cRs, N.cochar_point]
        by_cases hl : l = i
        · subst l; simp only [factorPoint_same]
        · rw [factorPoint_ne hl, factorPoint_ne (fun h => hl (Sum.inr.inj h))]

private theorem finiteMatrixProduct {I : Type u} [Finite I] [Nonempty I] (A : AdditiveLine k) :
    Nonempty (MatrixProduct A I) := by
  classical
  let S := (Fintype.ofFinite I)
  letI : Fintype I := S
  have h : ∀ n : ℕ, Nonempty (MatrixProduct A (ULift.{u} (Fin (n + 1)))) := by
    intro n
    induction n with
    | zero => exact rankOneMatrixProduct A
    | succ n ih =>
      obtain ⟨M⟩ := ih
      obtain ⟨N⟩ := rankOneMatrixProduct A
      obtain ⟨P⟩ := rankProduct M N
      exact ⟨P.reindex ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
        (finSumFinEquiv.trans Equiv.ulift.symm))⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := I))
  obtain ⟨M⟩ := h n
  let e : I ≃ ULift.{u} (Fin (n + 1)) :=
    (Fintype.equivFin I).trans ((finCongr hn).trans Equiv.ulift.symm)
  exact ⟨M.reindex e.symm⟩

end MatrixProducts

section OrthogonalPinnedComparison

open Matrix CategoryTheory.Limits
open scoped Classical
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SplitBorelPair PinnedGroup PinnedIso AttachedDatum SimpleRoot IsSimple transportCharacter)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.PinnedUniqueness (scalarGroupPoints)
open Specs.AutomorphismSequence (forgetPinning)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private base_isPos_iff_subgroupRoots from LinearAlgebraicGroups.Classification.PinnedEquivalence

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable {k : Type u} [Field k]

private def simpleRootSupport {P : SplitBorelPair k} (D : AttachedDatum P) :
    letI := D.comm; SimpleRoot P ≃ D.base.support := by
  letI := D.comm
  exact Equiv.subtypeEquivRight (fun a => (D.simple_iff a).symm)

@[simp] private theorem simpleRootSupport_val {P : SplitBorelPair k} (D : AttachedDatum P)
    (a : SimpleRoot P) :
    letI := D.comm; (simpleRootSupport D a).val = a.val := rfl

private theorem cartan_of_simple_positives {P : SplitBorelPair k} (D : AttachedDatum P)
    (h : ∀ a ∈ subgroupRoots P.T P.B, IsSimple P a) :
    letI := D.comm
    ∀ a b : D.base.support,
      RootData.integralCartan D.datum.rootDatum D.base a b = if a = b then 2 else 0 := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  intro a b
  let C := D.datum.rootDatum
  change C.toLinearMap (C.root b.val) (C.coroot a.val) = _
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    exact C.root_coroot_two a.val
  rw [ite_eq_right hab]
  let n := C.toLinearMap (C.root b.val) (C.coroot a.val)
  change n = 0
  obtain ⟨_, _, _, hCorr, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity P.G P.reductive P.T P.split P.maximal
  have hpos := base_isPos_iff_subgroupRoots D (hCorr.1 P.B P.borel P.containsTorus)
  let r := C.reflectionPerm a.val b.val
  have hb := D.base.isPos_of_mem_support b.property
  have hr : D.base.IsPos r := hb.reflectionPerm a.property
    (fun e => hab (Subtype.ext e.symm))
  let s : D.base.support := ⟨r, (D.simple_iff r).mpr (h r ((hpos r).mp hr))⟩
  let basis := D.base.toWeightBasisInt
  have eqr : basis s = basis b - n • basis a := by
    apply Subtype.ext
    simpa only [basis, RootPairing.Base.coe_toWeightBasisInt_apply,
      Submodule.coe_sub, Submodule.coe_smul] using (C.reflectionPerm_root a.val b.val).symm
  have hre (j : D.base.support) :
      Finsupp.single s (1 : ℤ) j = Finsupp.single b (1 : ℤ) j - n * Finsupp.single a (1 : ℤ) j := by
    have he : Finsupp.single s (1 : ℤ) =
        Finsupp.single b (1 : ℤ) - n • Finsupp.single a (1 : ℤ) :=
      (basis.repr_self s).symm.trans <| (congrArg basis.repr eqr).trans <|
        (basis.repr.map_sub (basis b) (n • basis a)).trans <|
          congrArg₂ (· - ·) (basis.repr_self b)
            ((basis.repr.map_smul n (basis a)).trans (congrArg (n • ·) (basis.repr_self a)))
    exact DFunLike.congr_fun he j
  have hsb : s = b := by
    by_contra hn
    simpa [Finsupp.single_apply, hn, hab] using hre b
  have he := hre a
  rw [hsb] at he
  simp [Ne.symm hab] at he
  exact he

private theorem MatrixProduct.basis_coroot {A : AdditiveLine k} {I : Type u} (M : MatrixProduct A I) :
    letI := M.D.comm
    ∀ i, M.basis i = M.D.datum.rootDatum.coroot (M.label i).val := by
  letI := M.D.comm
  let w := M.label.trans (simpleRootSupport M.D)
  have hC := cartan_of_simple_positives M.D M.positiveSimple
  have hB (j l : I) :
      M.D.datum.rootDatum.toLinearMap (M.D.datum.rootDatum.root (M.label j).val)
        (M.basis l) = if l = j then 2 else 0 := by
    rw [M.D.datum.root_eq]
    exact (M.D.datum.pairing_eq _ (Additive.toMul (M.basis l))).trans (M.pairing_basis l j)
  intro i
  apply M.basis.repr.injective
  ext j
  have eqF : M.D.datum.rootDatum.toLinearMap (M.D.datum.rootDatum.root (M.label j).val) =
      (2 : ℤ) • M.basis.coord j := by
    apply M.basis.ext
    intro l
    rw [hB, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases e : l = j
    · subst l
      simp
    · simp [e]
  have hEq : M.D.datum.rootDatum.toLinearMap (M.D.datum.rootDatum.root (M.label j).val) (M.basis i) =
      M.D.datum.rootDatum.toLinearMap (M.D.datum.rootDatum.root (M.label j).val)
        (M.D.datum.rootDatum.coroot (M.label i).val) := by
    have h := hC (w i) (w j)
    change M.D.datum.rootDatum.toLinearMap (M.D.datum.rootDatum.root (M.label j).val)
      (M.D.datum.rootDatum.coroot (M.label i).val) = _ at h
    rw [hB, h]
    by_cases e : i = j
    · subst j
      simp
    · rw [ite_eq_right e, ite_eq_right (fun h => e (w.injective h))]
  rw [eqF] at hEq
  simp only [LinearMap.smul_apply, Basis.coord_apply, Int.zsmul_eq_mul] at hEq
  omega

private theorem MatrixProduct.fullCorootLattice {A : AdditiveLine k} {I : Type u} (M : MatrixProduct A I) :
    letI := M.D.comm; corootLattice M.D = ⊤ := by
  letI := M.D.comm
  change Submodule.span ℤ (Set.range M.D.datum.rootDatum.coroot) = ⊤
  apply top_unique
  rw [← M.basis.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨(M.label i).val, (M.basis_coroot i).symm⟩

private structure OrthogonalMatrixComparison {A : AdditiveLine k} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) where
  points : (groupPointsFunctor k).obj P.pair.G.val ≅ specialLinearFamilyPoints k (SimpleRoot P.pair) 2
  torus : ∀ (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R),
    subgroupSection P.pair.T g ↔ ∀ i, MatrixMark.torus.Holds (points.hom.app R g i)
  borel : ∀ (R : TestAlgebra k) (g : GroupPoints P.pair.G.val R),
    subgroupSection P.pair.B g ↔ ∀ i, MatrixMark.positiveBorel.Holds (points.hom.app R g i)
  root_point : ∀ (i : SimpleRoot P.pair) (R : TestAlgebra k) (a : R),
    points.hom.app R (rootPoint (pinnedRootCoordinate P i) R a) = factorPoint i (rankOneRoot a)
  coroot_point : letI := D.comm; ∀ (i : SimpleRoot P.pair) (R : TestAlgebra k) (v : Rˣ),
    points.hom.app R (projectPoint P.pair.T.inclusion
      (cocharacterPoint (Additive.toMul (D.datum.rootDatum.coroot i.val)) R v)) =
        factorPoint i (rankOneCoroot v)

private theorem orthogonalMatrixComparison {F K : Type u} [Field F] [Field K] [Algebra F K]
    (d : PinnedOrbitDescent F K) (i : SimpleRoot d.P.pair)
    (horth : ∀ a b : SimpleRoot d.P.pair, a ≠ b → d.cartan a b = 0) :
    Nonempty (OrthogonalMatrixComparison d.P d.D) := by
  letI := d.D.comm
  letI := d.D.datum.finiteRoots
  letI : Nonempty (SimpleRoot d.P.pair) := ⟨i⟩
  obtain ⟨M⟩ := finiteMatrixProduct d.A (I := SimpleRoot d.P.pair)
  letI := M.D.comm
  let j := (verticesOfDatum d).symm.trans (M.label.trans (simpleRootSupport M.D))
  have hfull : corootLattice d.D = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion d.P.pair.G d.splitSemisimple
      d.P.pair.T d.P.pair.split d.P.pair.maximal d.D.datum).mp d.splitSimplyConnected
  obtain ⟨f, hf⟩ := pinnedCartanComparison d.P M.P d.D M.D hfull M.fullCorootLattice j (by
    intro a b
    rw [cartan_of_simple_positives M.D M.positiveSimple]
    change d.D.datum.rootDatum.pairing b.val a.val = _
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left rfl]
      exact d.D.datum.rootDatum.root_coroot_two a.val
    · rw [ite_eq_right (fun e => hab (j.injective e))]
      let a' := (verticesOfDatum d).symm a
      let b' := (verticesOfDatum d).symm b
      exact horth a' b' (fun e => hab ((verticesOfDatum d).symm.injective e)))
  let m := (groupPointsFunctor F).mapIso f.group ≪≫ M.points
  refine ⟨⟨m, ?_, ?_, ?_, ?_⟩⟩
  · intro R x
    exact (mapSubgroupSections (S := d.P.pair.T) (T := M.P.pair.T) f.group f.torus f.torus_comm R x).trans
      (M.torus R _)
  · intro R x
    exact (mapSubgroupSections (S := d.P.pair.B) (T := M.P.pair.B) f.group f.borel f.borel_comm R x).trans
      (M.borel R _)
  · intro a R v
    have h := hf (verticesOfDatum d a)
    have hx : transportCharacter f.torus a.val.val = (M.label a).val.val := by
      simpa [j] using h.1
    change M.points.hom.app R (projectPoint f.group.hom
      (rootPoint (pinnedRootCoordinate d.P a) R v)) = _
    rw [projectPoint_root]
    have hpin : pinnedRootCoordinate d.P a ≫ f.group.hom = pinnedRootCoordinate M.P (M.label a) :=
      pinnedRootMap f a (M.label a) hx
    rw [hpin]
    exact M.root_point a R v
  · intro a R v
    have h := hf (verticesOfDatum d a)
    let c := Additive.toMul (d.D.datum.rootDatum.coroot a.val)
    have hc : c ≫ f.torus.hom = Additive.toMul (M.basis a) := by
      have hv : (j (verticesOfDatum d a)).val = (M.label a).val := by
        simp [j]
      have hh := h.2
      rw [hv] at hh
      exact hh.trans (congrArg Additive.toMul (M.basis_coroot a).symm)
    change M.points.hom.app R (projectPoint f.group.hom
      (projectPoint d.P.pair.T.inclusion (cocharacterPoint c R v))) = _
    rw [projectPoint_comp, f.torus_comm, ← projectPoint_comp, projectPoint_cochar, hc]
    exact M.cochar_point a R v

private def rankOneCorootHom (R : Type u) [CommRing R] : Rˣ →* SpecialLinearGroup (Fin 2) R where
  toFun := rankOneCoroot
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal _ = (1 : Matrix (Fin 2) (Fin 2) R)
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' t v := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

private theorem rankOneDiagonal {R : Type u} [CommRing R] (g : SpecialLinearGroup (Fin 2) R)
    (hg : MatrixMark.torus.Holds g) : ∃ t : Rˣ, rankOneCoroot t = g := by
  have h := g.property
  rw [Matrix.det_fin_two, hg 0 1 (by decide), zero_mul, sub_zero] at h
  let v := Units.mkOfMulEqOne _ _ h
  refine ⟨v, Subtype.ext (Matrix.ext fun i j => ?_)⟩
  by_cases he : i = j
  · subst j
    rw [show (rankOneCoroot v).val i i = ![(v : R), (↑v⁻¹ : R)] i from Matrix.diagonal_apply_eq _ _]
    fin_cases i <;> rfl
  · exact (Matrix.diagonal_apply_ne _ he).trans (hg i j he).symm

private def familyCorootHom {I : Type u} (R : Type u) [CommRing R] :
    (I → Rˣ) →* (I → SpecialLinearGroup (Fin 2) R) where
  toFun v i := rankOneCoroot (v i)
  map_one' := funext fun _ => (rankOneCorootHom R).map_one
  map_mul' v w := funext fun i => (rankOneCorootHom R).map_mul (v i) (w i)

private theorem familyCorootHom_mulSingle {I R : Type u} [DecidableEq I] [CommRing R] (i : I) (v : Rˣ) :
    familyCorootHom (I := I) R (Pi.mulSingle i v) = factorPoint i (rankOneCoroot v) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [familyCorootHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_same, factorPoint_same]
  · rw [factorPoint_ne h]
    change rankOneCoroot ((Pi.mulSingle i v : I → Rˣ) j) = _
    rw [Pi.mulSingle_eq_of_ne h]
    exact (rankOneCorootHom R).map_one

private def permuteMatrixFamily {I : Type u} (π : Equiv.Perm I) :
    specialLinearFamilyPoints k I 2 ⟶ specialLinearFamilyPoints k I 2 where
  app R := GrpCat.ofHom
    ({ toFun g j := g (π j)
       map_one' := rfl
       map_mul' _ _ := rfl } :
      (I → SpecialLinearGroup (Fin 2) R) →* (I → SpecialLinearGroup (Fin 2) R))
  naturality {R S} f := by apply GrpCat.ext; intro g; rfl

private theorem permute_factorPoint {I R : Type u} [CommRing R] (π : Equiv.Perm I)
    (i j : I) (v : SpecialLinearGroup (Fin 2) R) :
    factorPoint (π i) v (π j) = factorPoint i v j := by
  by_cases h : j = i
  · subst j; simp only [factorPoint_same]
  · rw [factorPoint_ne h, factorPoint_ne (fun e => h (π.injective e))]

set_option maxHeartbeats 3000000 in
private theorem OrthogonalMatrixComparison.equivariant {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (M : OrthogonalMatrixComparison P D)
    (b : PinnedIso P P) (π : Equiv.Perm (SimpleRoot P.pair))
    (hπ : ∀ i, transportCharacter b.torus i.val.val = (π i).val.val) :
    ∀ (R : TestAlgebra k) (x : GroupPoints P.pair.G.val R) (j : SimpleRoot P.pair),
      M.points.hom.app R (projectPoint b.group.inv x) j = M.points.hom.app R x (π j) := by
  letI := D.comm
  letI := D.datum.finiteRoots
  let F := groupPointsFunctor k
  let m := M.points
  have inv_apply (R : TestAlgebra k) (v : SimpleRoot P.pair → SpecialLinearGroup (Fin 2) R) :
      m.hom.app R (m.inv.app R v) = v := GrpCat.hom_inv_apply (m.app R) v
  let δ := permuteMatrixFamily (k := k) π
  let g := F.map b.group.hom
  let z := g ≫ m.hom ≫ δ ≫ m.inv
  let R₀ := CommAlgCat.of k k
  let U := Under.forget R₀
  let x (i : SimpleRoot P.pair) (R : TestAlgebra k) (a : R) :=
    rootPoint (pinnedRootCoordinate P i) R a
  let c (i : SimpleRoot P.pair) := Additive.toMul (D.datum.rootDatum.coroot i.val)
  let y (i : SimpleRoot P.pair) (R : TestAlgebra k) (v : Rˣ) :=
    projectPoint P.pair.T.inclusion (cocharacterPoint (c i) R v)
  have hb_x (i : SimpleRoot P.pair) (R : TestAlgebra k) (v : R) :
      g.app R (x i R v) = x (π i) R v := by
    change projectPoint b.group.hom (rootPoint (pinnedRootCoordinate P i) R v) = _
    rw [projectPoint_root]
    exact congrArg (fun f => rootPoint f R v) (pinnedRootMap b i (π i) (hπ i))
  have hb_y (i : SimpleRoot P.pair) (R : TestAlgebra k) (v : Rˣ) :
      g.app R (y i R v) = y (π i) R v := by
    change projectPoint b.group.hom (projectPoint P.pair.T.inclusion (cocharacterPoint (c i) R v)) = _
    rw [projectPoint_comp, b.torus_comm, ← projectPoint_comp, projectPoint_cochar]
    exact congrArg (fun t => projectPoint P.pair.T.inclusion (cocharacterPoint t R v))
      (pinnedAutCoroot D b i (π i) (hπ i))
  have hz_x (i : SimpleRoot P.pair) (R : TestAlgebra k) (v : R) : z.app R (x i R v) = x i R v := by
    apply ((m.app R).groupIsoToMulEquiv).injective
    change m.hom.app R (m.inv.app R (δ.app R (m.hom.app R (g.app R (x i R v))))) =
      m.hom.app R (x i R v)
    rw [inv_apply R, hb_x, show m.hom.app R (x (π i) R v) =
      factorPoint (π i) (rankOneRoot v) from M.root_point _ _ _,
      show m.hom.app R (x i R v) = factorPoint i (rankOneRoot v) from M.root_point _ _ _]
    exact funext (permute_factorPoint π i · (rankOneRoot v))
  have hz_y (i : SimpleRoot P.pair) (R : TestAlgebra k) (v : Rˣ) :
      z.app R (y i R v) = y i R v := by
    apply ((m.app R).groupIsoToMulEquiv).injective
    change m.hom.app R (m.inv.app R (δ.app R (m.hom.app R (g.app R (y i R v))))) =
      m.hom.app R (y i R v)
    rw [inv_apply R, hb_y, show m.hom.app R (y (π i) R v) =
      factorPoint (π i) (rankOneCoroot v) from M.coroot_point _ _ _,
      show m.hom.app R (y i R v) = factorPoint i (rankOneCoroot v) from M.coroot_point _ _ _]
    exact funext (permute_factorPoint π i · (rankOneCoroot v))
  have hz_t (R : TestAlgebra k) (t : GroupPoints P.pair.T.group R) :
      z.app R (projectPoint P.pair.T.inclusion t) = projectPoint P.pair.T.inclusion t := by
    let a := projectPoint P.pair.T.inclusion t
    let h : (SimpleRoot P.pair → Rˣ) →* GroupPoints P.pair.G.val R :=
      (m.app R).groupIsoToMulEquiv.symm.toMonoidHom.comp (familyCorootHom R)
    have hh (i : SimpleRoot P.pair) (v : Rˣ) : h (Pi.mulSingle i v) = y i R v := by
      apply (m.app R).groupIsoToMulEquiv.injective
      change m.hom.app R (m.inv.app R (familyCorootHom R (Pi.mulSingle i v))) = _
      rw [inv_apply R]
      change (familyCorootHom R) (Pi.mulSingle i v) = m.hom.app R (y i R v)
      exact (familyCorootHom_mulSingle i v).trans (M.coroot_point i R v).symm
    have hz : (z.app R).hom.comp h = h := MonoidHom.pi_ext fun i v => by
      change z.app R (h (Pi.mulSingle i v)) = h (Pi.mulSingle i v)
      rw [hh, hz_y]
    have ha : ∀ i, MatrixMark.torus.Holds (m.hom.app R a i) :=
      (M.torus R a).mp ⟨t, rfl⟩
    choose v hv using fun i => rankOneDiagonal (m.hom.app R a i) (ha i)
    have hv' : h v = a := by
      apply (m.app R).groupIsoToMulEquiv.injective
      change m.hom.app R (m.inv.app R (familyCorootHom R v)) = _
      rw [inv_apply R]
      exact funext hv
    have he := DFunLike.congr_fun hz v
    change z.app R (h v) = h v at he
    rwa [hv'] at he
  have hid := Classification.PinnedUniqueness.scalarRigidity P R₀ (Functor.whiskerLeft U z)
    (fun S t => hz_t S.right t) (fun S i v => hz_x i S.right v)
  intro R a j
  let RR : Under R₀ := Under.mk (CommAlgCat.ofHom (Algebra.ofId k R))
  let x₀ := projectPoint b.group.inv a
  have heq : g.app R x₀ = a := by
    change projectPoint b.group.hom (projectPoint b.group.inv a) = _
    rw [projectPoint_comp, b.group.inv_hom_id, projectPoint_id]
  have h := congrArg (fun p : scalarGroupPoints R₀ P.pair.G.val ⟶ _ => p.app RR x₀) hid
  change m.inv.app R (δ.app R (m.hom.app R (g.app R x₀))) = x₀ at h
  have h' := congrArg (m.hom.app R) h
  rw [inv_apply R, heq] at h'
  exact (congrFun h' j).symm

end OrthogonalPinnedComparison

section MatrixFamilyLimits

open Matrix CategoryTheory.Limits
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint HasLimit HasExtension
  orbit polynomialAlgebra laurentAlgebra polynomialToLaurent polynomialEvaluate)
open private unitPointHom_apply unitEquiv from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

variable {k : Type u} [Field k]

private def matrixFamilyProjection {I : Type u} (j : I) :
    specialLinearFamilyPoints k I 2 ⟶ specialLinearPointsOfSize 2 k where
  app R := GrpCat.ofHom
    ({ toFun := (· j), map_one' := rfl, map_mul' := fun _ _ => rfl } :
      (I → SpecialLinearGroup (Fin 2) R) →* SpecialLinearGroup (Fin 2) R)
  naturality {R S} f := by apply GrpCat.ext; intro g; rfl

private def projectMatrixGroup {G : GroupScheme k} [IsAffine G.X.left] {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2) (j : I) :
    G ⟶ (rankOneGroup k).val :=
  letI := (rankOneGroup k).property.1
  (groupHomEquiv G (rankOneGroup k).val inferInstance).symm
    (m.hom ≫ matrixFamilyProjection j ≫ (rankOnePointsIso k).inv)

private theorem projectMatrixGroup_apply {G : GroupScheme k} [IsAffine G.X.left] {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2) (j : I)
    (R : TestAlgebra k) (x : GroupPoints G R) :
    (rankOnePointsIso k).hom.app R (projectPoint (projectMatrixGroup m j) x) =
      m.hom.app R x j := by
  letI := (rankOneGroup k).property.1
  have h := congrArg (fun q => q.app R x)
    ((groupHomEquiv G (rankOneGroup k).val inferInstance).apply_symm_apply
      (m.hom ≫ matrixFamilyProjection j ≫ (rankOnePointsIso k).inv))
  change projectPoint (projectMatrixGroup m j) x =
    (rankOnePointsIso k).inv.app R (m.hom.app R x j) at h
  rw [h]
  exact GrpCat.hom_inv_apply ((rankOnePointsIso k).app R) (m.hom.app R x j)

private def assembleMatrixGroup {G : GroupScheme k} {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2)
    (R : TestAlgebra k) (x : I → GroupPoints (rankOneGroup k).val R) :
    GroupPoints G R :=
  m.inv.app R (fun j => (rankOnePointsIso k).hom.app R (x j))

private theorem project_assembleMatrixGroup {G : GroupScheme k} [IsAffine G.X.left] {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2)
    (R : TestAlgebra k) (x : I → GroupPoints (rankOneGroup k).val R) (j : I) :
    projectPoint (projectMatrixGroup m j) (assembleMatrixGroup m R x) = x j := by
  apply ((rankOnePointsIso k).app R).groupIsoToMulEquiv.injective
  change (rankOnePointsIso k).hom.app R (projectPoint (projectMatrixGroup m j)
    (assembleMatrixGroup m R x)) = (rankOnePointsIso k).hom.app R (x j)
  rw [projectMatrixGroup_apply, assembleMatrixGroup]
  exact congrFun (GrpCat.hom_inv_apply (m.app R)
    (fun j => (rankOnePointsIso k).hom.app R (x j))) j

private theorem matrixProjections_injective {G : GroupScheme k} [IsAffine G.X.left] {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2)
    {R : TestAlgebra k} {x y : GroupPoints G R}
    (h : ∀ j, projectPoint (projectMatrixGroup m j) x = projectPoint (projectMatrixGroup m j) y) :
    x = y := by
  apply (m.app R).groupIsoToMulEquiv.injective
  funext j
  change m.hom.app R x j = m.hom.app R y j
  rw [← projectMatrixGroup_apply m j R x, ← projectMatrixGroup_apply m j R y, h j]

private theorem family_hasLimit {G : GroupScheme k} [IsAffine G.X.left] {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2)
    (c : Cocharacter G) {R : TestAlgebra k} (x z : GroupPoints G R) :
    HasLimit c x z ↔ ∀ j, HasLimit (c ≫ projectMatrixGroup m j)
      (projectPoint (projectMatrixGroup m j) x) (projectPoint (projectMatrixGroup m j) z) := by
  constructor
  · rintro ⟨p, hp, hz⟩ j
    refine ⟨projectPoint (projectMatrixGroup m j) p, ?_, ?_⟩
    · rw [projectPoint_natural, hp, projectPoint_orbit]
    · rw [projectPoint_natural, hz]
  · intro h
    choose p hp hz using h
    let q := assembleMatrixGroup m (polynomialAlgebra R) p
    refine ⟨q, matrixProjections_injective m (fun j => ?_), matrixProjections_injective m (fun j => ?_)⟩
    · rw [← projectPoint_natural, projectPoint_orbit, project_assembleMatrixGroup]
      exact hp j
    · rw [← projectPoint_natural, project_assembleMatrixGroup]
      exact hz j

private theorem family_hasExtension {G : GroupScheme k} [IsAffine G.X.left] {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2)
    (c : Cocharacter G) {R : TestAlgebra k} (x : GroupPoints G R) :
    HasExtension c x ↔ ∀ j, HasExtension (c ≫ projectMatrixGroup m j)
      (projectPoint (projectMatrixGroup m j) x) := by
  constructor
  · rintro ⟨z, hz⟩ j
    exact ⟨_, (family_hasLimit m c x z).mp hz j⟩
  · intro h
    choose z hz using h
    refine ⟨assembleMatrixGroup m R z, (family_hasLimit m c x _).mpr fun j => ?_⟩
    rw [project_assembleMatrixGroup]
    exact hz j

private theorem identity_hasLimit {G : GroupScheme k} (c : Cocharacter G) (R : TestAlgebra k) :
    HasLimit c (1 : GroupPoints G R) 1 := by
  refine ⟨1, ?_, map_one (((groupPointsFunctor k).obj G).map (polynomialEvaluate R 0)).hom⟩
  rw [show mapPoints (polynomialToLaurent R) (1 : GroupPoints G (polynomialAlgebra R)) = 1
    from map_one (((groupPointsFunctor k).obj G).map (polynomialToLaurent R)).hom]
  unfold orbit
  rw [show mapPoints _ (1 : GroupPoints G R) = 1
    from map_one (((groupPointsFunctor k).obj G).map _).hom]
  simp

private theorem identity_matrixMark (b : MatrixMark) (R : Type u) [CommRing R] :
    b.Holds (1 : SpecialLinearGroup (Fin 2) R) := by
  cases b with
  | torus => exact fun i j h => Matrix.one_apply_ne h
  | positiveBorel => exact fun i j h => Matrix.one_apply_ne h.ne.symm
  | negativeBorel => exact fun i j h => Matrix.one_apply_ne h.ne.symm
  | positiveRadical => exact ⟨fun i j h => Matrix.one_apply_ne h.ne.symm, Matrix.one_apply_eq⟩
  | negativeRadical => exact ⟨fun i j h => Matrix.one_apply_ne h.ne.symm, Matrix.one_apply_eq⟩

private theorem rankOneDiagonalWeights (c : Cocharacter (rankOneGroup k).val)
    (h : ∀ (R : TestAlgebra k) (t : Rˣ),
      MatrixMark.torus.Holds ((rankOnePointsIso k).hom.app R (cocharacterPoint c R t))) :
    ∃ y : Fin 2 → ℤ, ∀ (R : TestAlgebra k) (t : Rˣ),
      ((rankOnePointsIso k).hom.app R (cocharacterPoint c R t)).val =
        Matrix.diagonal (fun i => (↑(t ^ y i) : R)) := by
  let S := rankOneGroup k
  let s := StandardGroups.specialLinearGroupPointsIso k (ULift.{u} (Fin 2))
  obtain ⟨T, L, _, _, _, _, _, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k 1 S s
  have hgt (R : TestAlgebra k) (t : Rˣ) : subgroupSection T.subgroup (cocharacterPoint c R t) := by
    apply (T.range R _).mpr
    intro i j hij
    exact h R t i.down j.down (fun h => hij (ULift.ext h))
  let M₀ := specGroup (groupAlgebra k IntegerCharacters)
  let R₀ := CommAlgCat.of k (MonoidAlgebra k IntegerCharacters)
  let idPt : GroupPoints M₀ R₀ := 𝟙 M₀.X
  let u₀ := unitEquiv R₀ idPt
  have hu₀ : unitPoint R₀ u₀ = idPt := by
    rw [← unitPointHom_apply]
    exact (unitEquiv R₀).symm_apply_apply _
  have hg₀ := hgt R₀ u₀
  change (unitPoint R₀ u₀ ≫ c.hom.hom) ∈ _ at hg₀
  rw [hu₀] at hg₀
  change (𝟙 M₀.X ≫ c.hom.hom) ∈ _ at hg₀
  rw [Category.id_comp] at hg₀
  obtain ⟨q, hq⟩ : ∃ q : M₀.X ⟶ T.subgroup.group.X,
      q ≫ T.subgroup.inclusion.hom.hom = c.hom.hom := hg₀
  letI := T.subgroup.isClosedImmersion
  letI := isMonHom_of_comp_closed q c T.subgroup.inclusion hq
  let b : Cocharacter T.subgroup.group := Grp.homMk q
  have hb : b ≫ T.subgroup.inclusion = c := Grp.hom_ext _ _ hq
  letI := L.comm
  let y := L.cocharacters (Additive.ofMul b)
  refine ⟨y.val, fun R t => ?_⟩
  have h₁ := L.cocharacterPoint_eq y R t
  rw [LinearEquiv.symm_apply_apply] at h₁
  apply Matrix.ext
  intro i j
  have h₂ := congrArg (fun z : Matrix (ULift.{u} (Fin 2)) _ R => z ⟨i⟩ ⟨j⟩) h₁
  have heq := (projectPoint_cochar T.subgroup.inclusion b R t).trans (congrArg (fun a =>
    cocharacterPoint a R t) hb)
  change (s.hom.app R (projectPoint T.subgroup.inclusion (cocharacterPoint b R t))).val ⟨i⟩ ⟨j⟩ =
    _ at h₂
  rw [heq] at h₂
  exact h₂.trans (by simp [Matrix.diagonal_apply])

private theorem familyOppositeMarks {G : GroupScheme k} [IsAffine G.X.left] {I : Type u}
    (m : (groupPointsFunctor k).obj G ≅ specialLinearFamilyPoints k I 2)
    (c c' : Cocharacter G)
    (hc : ∀ (R : TestAlgebra k) (v : Rˣ) (j : I),
      MatrixMark.torus.Holds (m.hom.app R (cocharacterPoint c R v) j))
    (hc' : ∀ (R : TestAlgebra k) (v : Rˣ) (j : I),
      MatrixMark.torus.Holds (m.hom.app R (cocharacterPoint c' R v) j))
    (hp : ∀ (R : TestAlgebra k) (x : GroupPoints G R),
      HasExtension c x ↔ ∀ j, MatrixMark.positiveBorel.Holds (m.hom.app R x j))
    (hopp : ∀ (R : TestAlgebra k) (x : GroupPoints G R),
      HasExtension c x → HasExtension c' x → ∀ j, MatrixMark.torus.Holds (m.hom.app R x j)) :
    ∀ (R : TestAlgebra k) (x : GroupPoints G R),
      (HasExtension c' x ↔ ∀ j, MatrixMark.negativeBorel.Holds (m.hom.app R x j)) ∧
      (HasLimit c x 1 ↔ ∀ j, MatrixMark.positiveRadical.Holds (m.hom.app R x j)) ∧
      (HasLimit c' x 1 ↔ ∀ j, MatrixMark.negativeRadical.Holds (m.hom.app R x j)) := by
  classical
  let s := rankOnePointsIso k
  let P := projectMatrixGroup m
  let single (j : I) (R : TestAlgebra k) (g : GroupPoints (rankOneGroup k).val R) :
      GroupPoints G R := assembleMatrixGroup m R (factorPoint j g)
  have singleProj (j l : I) (R : TestAlgebra k) (g : GroupPoints (rankOneGroup k).val R) :
      projectPoint (P l) (single j R g) = factorPoint j g l :=
    project_assembleMatrixGroup m R _ l
  have singleMark (b : MatrixMark) (j : I) (R : TestAlgebra k)
      (g : GroupPoints (rankOneGroup k).val R) :
      (∀ l, b.Holds (m.hom.app R (single j R g) l)) ↔ b.Holds (s.hom.app R g) := by
    constructor
    · intro h
      have hl := h j
      rw [← projectMatrixGroup_apply m j, singleProj, factorPoint_same] at hl
      exact hl
    · intro h l
      rw [← projectMatrixGroup_apply m l, singleProj]
      by_cases he : l = j
      · subst l
        rwa [factorPoint_same]
      · rw [factorPoint_ne he, map_one]
        exact identity_matrixMark b R
  have singleLimit (a : Cocharacter G) (j : I) (R : TestAlgebra k)
      (g : GroupPoints (rankOneGroup k).val R) :
      HasExtension a (single j R g) ↔ HasExtension (a ≫ P j) g := by
    rw [family_hasExtension m]
    constructor
    · intro h
      have h' := h j
      rwa [singleProj, factorPoint_same] at h'
    · intro h l
      rw [singleProj]
      by_cases he : l = j
      · subst l
        rwa [factorPoint_same]
      · rw [factorPoint_ne he]
        exact ⟨1, identity_hasLimit _ R⟩
  have hfamily (j : I) (R : TestAlgebra k) (g : GroupPoints (rankOneGroup k).val R) :
      (HasExtension (c' ≫ P j) g ↔ MatrixMark.negativeBorel.Holds (s.hom.app R g)) ∧
      (HasLimit (c ≫ P j) g 1 ↔ MatrixMark.positiveRadical.Holds (s.hom.app R g)) ∧
      (HasLimit (c' ≫ P j) g 1 ↔ MatrixMark.negativeRadical.Holds (s.hom.app R g)) := by
    obtain ⟨y, hy⟩ := rankOneDiagonalWeights (c ≫ P j) (fun R v => by
      rw [← projectPoint_cochar, projectMatrixGroup_apply]
      exact hc R v j)
    obtain ⟨y', hy'⟩ := rankOneDiagonalWeights (c' ≫ P j) (fun R v => by
      rw [← projectPoint_cochar, projectMatrixGroup_apply]
      exact hc' R v j)
    exact specialLinearOppositeMarks s (c ≫ P j) (c' ≫ P j) y y' hy hy'
      (fun R x => (singleLimit c j R x).symm.trans
        ((hp R (single j R x)).trans (singleMark .positiveBorel j R x)))
      (fun R x hx hx' => (singleMark .torus j R x).mp
        (hopp R (single j R x) ((singleLimit c j R x).mpr hx) ((singleLimit c' j R x).mpr hx'))) R g
  intro R x
  refine ⟨(family_hasExtension m c' x).trans (forall_congr' fun j => ?_),
    (family_hasLimit m c x 1).trans (forall_congr' fun j => ?_),
    (family_hasLimit m c' x 1).trans (forall_congr' fun j => ?_)⟩
  · rw [← projectMatrixGroup_apply]
    exact (hfamily j R (projectPoint (P j) x)).1
  · rw [projectPoint_one, ← projectMatrixGroup_apply]
    exact (hfamily j R (projectPoint (P j) x)).2.1
  · rw [projectPoint_one, ← projectMatrixGroup_apply]
    exact (hfamily j R (projectPoint (P j) x)).2.2

end MatrixFamilyLimits

section OrthogonalDescentMarks

open Matrix
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (SimpleRoot)
open Specs.AutomorphismSequence (forgetPinning)
open Specs.RootGroups (rootPoint)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (baseChangedSubgroup)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint HasLimit HasExtension)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)
open private baseChangePointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private extendedGroupIso extendedSpecIso_hom_fst from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private subgroupFactorThrough from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private reductive_of_semisimple from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private maximalTorus_of_geometricallyMaximal from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private extendedCoordinateIso extendedCoordinateIso_comm
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private extendSubgroup from LinearAlgebraicGroups.RootData.BorelNormalizer
open Specs.AdjointCocharacters (coordinateHopfMap)
local notation "coordinateAlgebra" => Specs.AdjointCocharacters.coordinateHopf
open private isAffine_baseChange from LinearAlgebraicGroups.Affine.IdentityTangent
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2800000

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem orbitEmbedding_preserves_marks [IsGalois F K] [FiniteDimensional F K]
    (d : PinnedOrbitDescent F K) (i : SimpleRoot d.P.pair)
    (emb : SimpleRoot d.P.pair → (orbitField d.action i →ₐ[F] K))
    (hemb : ∀ (σ : Gal(K/F)) (x : orbitField d.action i), emb (d.action σ i) x = σ x.val)
    (R : TestAlgebra K) (b : MatrixMark) :
    let E := orbitField d.action i
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    ∀ g : SpecialLinearGroup (Fin 2) (R₀ ⊗[F] E),
      (∀ j : SimpleRoot d.P.pair,
        let f : R₀ ⊗[F] E →ₐ[F] R₀ := Algebra.TensorProduct.lift (AlgHom.id F R₀)
          (((Algebra.ofId K R₀).restrictScalars F).comp (emb j)) (fun _ _ => Commute.all _ _)
        b.Holds (SpecialLinearGroup.map f.toRingHom g)) ↔ b.Holds g := by
  let E := orbitField d.action i
  let R₀ := (restrictTestAlgebra F K).obj R
  letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
  letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨a, ha, he⟩ := orbitScalarSplittingOverAlgebras d.action i
  obtain ⟨e, he⟩ := he R₀
  let J := diagramOrbit d.action i
  let f (j : SimpleRoot d.P.pair) : R₀ ⊗[F] E →ₐ[F] R₀ :=
    Algebra.TensorProduct.lift (AlgHom.id F R₀)
      (((Algebra.ofId K R₀).restrictScalars F).comp (emb j)) (fun _ _ => Commute.all _ _)
  have hproj (j : J) (x : R₀ ⊗[F] E) : f j.val x = e x j := by
    obtain ⟨σ, hσ⟩ := j.property
    have hj : j = ⟨d.action σ i, ⟨σ, rfl⟩⟩ := Subtype.ext hσ.symm
    have haj (z : E) : emb j.val z = a j z := by
      rw [hj, hemb σ, ha]
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      change x * algebraMap K R₀ (emb j.val y) = e (x ⊗ₜ[F] y) j
      rw [he, haj]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  dsimp only
  intro g
  change (∀ j, b.Holds (SpecialLinearGroup.map (f j).toRingHom g)) ↔ b.Holds g
  refine ⟨fun h => (mark_map_iff e.toRingEquiv.toRingHom e.injective b g).mp ?_,
    fun h j => mark_map _ b _ h⟩
  have hV (i l : Fin 2) (r : R₀ ⊗[F] E)
      (hr : ∀ j, f j (g.val i l) = f j r) : e (g.val i l) = e r := by
    funext j
    simp only [← hproj]
    exact hr j.val
  cases b with
  | torus =>
    intro i l hil
    simpa using hV i l 0 (fun j => by simpa using h j i l hil)
  | positiveBorel =>
    intro i l hil
    simpa using hV i l 0 (fun j => by simpa using h j hil)
  | negativeBorel =>
    intro i l hil
    simpa using hV i l 0 (fun j => by simpa using h j hil)
  | positiveRadical =>
    exact ⟨fun i l hil => by simpa using hV i l 0 (fun j => by simpa using (h j).1 hil),
      fun i => by simpa using hV i i 1 (fun j => ((h j).2 i).trans (f j).map_one.symm)⟩
  | negativeRadical =>
    exact ⟨fun i l hil => by simpa using hV i l 0 (fun j => by simpa using (h j).1 hil),
      fun i => by simpa using hV i i 1 (fun j => ((h j).2 i).trans (f j).map_one.symm)⟩

private theorem trivialization_marks (d : PinnedOrbitDescent F K)
    (H : ClosedSubgroup d.G.val) (Q : ClosedSubgroup d.P.pair.G.val)
    (e : extendedHopf K (coordinateAlgebra (closedSubgroupAlgebraicGroup Q)) ≅
      extendedHopf K (coordinateAlgebra (closedSubgroupAlgebraicGroup H)))
    (he : d.descent.groupIso.hom ≫ extendedHopfMap K
        (coordinateHopfMap (G := closedSubgroupAlgebraicGroup H) (H := d.G) H.inclusion) =
      extendedHopfMap K
        (coordinateHopfMap (G := closedSubgroupAlgebraicGroup Q) (H := d.P.pair.G) Q.inclusion) ≫ e.hom)
    (R : TestAlgebra K) (x : GroupPoints ((groupBaseChange F K).obj d.G.val) R) :
    subgroupSection H (baseChangePoint F K d.G.val.X R x) ↔
      subgroupSection Q (baseChangePoint F K d.P.pair.G.val.X R
        (projectPoint (d.trivialization (extendedGroupIso K)).hom x)) := by
  let f := d.trivialization (extendedGroupIso K)
  let h := extendSubgroup K H
  let q := extendSubgroup K Q
  let a : h.group ≅ q.group := (extendedCoordinateIso (K := K)
    (closedSubgroupAlgebraicGroup H)).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso e.op ≪≫
    extendedCoordinateIso (K := K) (closedSubgroupAlgebraicGroup Q)
  have hf : h.inclusion ≫ f.hom = a.hom ≫ q.inclusion :=
    (extendedCoordinateIso_comm (K := K)
      (G := closedSubgroupAlgebraicGroup H) (G₀ := closedSubgroupAlgebraicGroup Q)
      (H := d.G) (H₀ := d.P.pair.G) H.inclusion Q.inclusion e d.descent.groupIso he).symm
  exact (extSubgroup_point_iff H h.isClosedImmersion R x).symm.trans
    ((mapSubgroupSections (S := h) (T := q) f a hf R x).trans
      (extSubgroup_point_iff Q q.isClosedImmersion R _))

private theorem splitMatrixMarks (d : PinnedOrbitDescent F K)
    (M : OrthogonalMatrixComparison d.P d.D) :
    let m := baseChangePointIso (K := K) d.P.pair.G.val ≪≫
      Functor.isoWhiskerLeft (restrictTestAlgebra F K) M.points
    let a := (groupPointsFunctor K).mapIso (d.trivialization (extendedGroupIso K)) ≪≫ m
    ∀ (R : TestAlgebra K) (x : GroupPoints ((groupBaseChange F K).obj d.G.val) R)
      (b : MatrixMark),
      (∀ j, b.Holds (a.hom.app R x j)) ↔
        subgroupSection (d.mark b) (baseChangePoint F K d.G.val.X R x) := by
  let G := (groupBaseChange F K).obj d.G.val
  letI : IsAffine d.G.val.X.left := d.G.property.1
  letI : IsAffine G.X.left := isAffine_baseChange K d.G.val
  let m : (groupPointsFunctor K).obj ((groupBaseChange F K).obj d.P.pair.G.val) ≅
      specialLinearFamilyPoints K (SimpleRoot d.P.pair) 2 :=
    baseChangePointIso (K := K) d.P.pair.G.val ≪≫
      Functor.isoWhiskerLeft (restrictTestAlgebra F K) M.points
  let a := (groupPointsFunctor K).mapIso (d.trivialization (extendedGroupIso K)) ≪≫ m
  let x₀ (R : TestAlgebra K) (x : GroupPoints G R) := baseChangePoint F K d.G.val.X R x
  have htor (R : TestAlgebra K) (x : GroupPoints G R) :
      (∀ j, MatrixMark.torus.Holds (a.hom.app R x j)) ↔ subgroupSection d.T (x₀ R x) :=
    ((trivialization_marks d d.T d.P.pair.T d.descent.torusIso d.descent.torusComm R x).trans
      (M.torus _ _)).symm
  have hupper (R : TestAlgebra K) (x : GroupPoints G R) :
      (∀ j, MatrixMark.positiveBorel.Holds (a.hom.app R x j)) ↔ subgroupSection d.Bpos (x₀ R x) :=
    ((trivialization_marks d d.Bpos d.P.pair.B d.descent.borelIso d.descent.borelComm R x).trans
      (M.borel _ _)).symm
  have ht₀ : d.T.inclusion.hom.hom ∈ SubgroupSections d.T d.T.group.X := by
    refine ⟨𝟙 d.T.group.X, ?_⟩
    change 𝟙 d.T.group.X ≫ d.T.inclusion.hom.hom = d.T.inclusion.hom.hom
    rw [Category.id_comp]
  have htpos := subgroupFactorThrough d.T d.Bpos ((d.opposite _ _).mp ht₀ _ (by simp))
  have htneg := subgroupFactorThrough d.T d.Bneg ((d.opposite _ _).mp ht₀ _ (by simp))
  have hr := reductive_of_semisimple d.G d.semisimple
  have hT := maximalTorus_of_geometricallyMaximal d.G d.T d.torus d.maximal
  obtain ⟨c, hc, hpos⟩ := baseChangedBorelLimits (K := K) d.G hr d.T d.Bpos
    d.isBorelPos hT htpos d.Upos d.isRadicalPos
  obtain ⟨c', hc', hneg⟩ := baseChangedBorelLimits (K := K) d.G hr d.T d.Bneg
    d.isBorelNeg hT htneg d.Uneg d.isRadicalNeg
  have hpc (R : TestAlgebra K) (x : GroupPoints G R) :
      HasExtension c x ↔ ∀ j, MatrixMark.positiveBorel.Holds (a.hom.app R x j) :=
    (hpos R x).1.trans (hupper R x).symm
  have hopc (R : TestAlgebra K) (x : GroupPoints G R) :
      HasExtension c x → HasExtension c' x → ∀ j, MatrixMark.torus.Holds (a.hom.app R x j) := by
    intro hx hx'
    apply (htor R x).mpr
    apply (d.opposite _ _).mpr
    intro H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact (hpos R x).1.mp hx
    · obtain rfl := Set.mem_singleton_iff.mp hH
      exact (hneg R x).1.mp hx'
  have h := familyOppositeMarks a c c'
    (fun R v => (htor R _).mpr (hc R v)) (fun R v => (htor R _).mpr (hc' R v)) hpc hopc
  dsimp only
  intro R x b
  change (∀ j, b.Holds (a.hom.app R x j)) ↔ subgroupSection (d.mark b) (x₀ R x)
  cases b with
  | torus => exact htor R x
  | positiveBorel => exact hupper R x
  | negativeBorel => exact (h R x).1.symm.trans (hneg R x).1
  | positiveRadical => exact (h R x).2.1.symm.trans (hpos R x).2
  | negativeRadical => exact (h R x).2.2.symm.trans (hneg R x).2

private theorem matrixMarks_of_algebra_injection {E : Type u} [Field E] [Algebra F E]
    {G : GroupScheme F} {n : ℕ}
    (m : (groupPointsFunctor F).obj G ⟶ extendScalars F E ⋙ specialLinearPointsOfSize n E)
    {R S : TestAlgebra F} (f : R ⟶ S) (hf : Function.Injective f.hom)
    (b : MatrixMark) (x : GroupPoints G R) :
    b.Holds (m.app S (mapPoints f x)) ↔ b.Holds (m.app R x) := by
  let j : R ⊗[F] E →ₐ[F] S ⊗[F] E := Algebra.TensorProduct.map f.hom (AlgHom.id F E)
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat f.hom.toLinearMap (AlgHom.id F E).toLinearMap
      hf Function.injective_id
  have hn := m.naturality_apply f x
  change m.app S (mapPoints f x) = SpecialLinearGroup.map j.toRingHom (m.app R x) at hn
  rw [hn]
  exact mark_map_iff j.toRingHom hj b (m.app R x)

set_option maxHeartbeats 4200000 in
/-- A transitive orthogonal orbit of a simply connected pinned group descends
to the marked Weil restriction from its vertex stabilizer field. -/
theorem orthogonalPinnedOrbitModel : OrthogonalPinnedOrbitModel.{u} := by
  classical
  intro F K _ _ _ _ _ d i horth
  let E := orbitField d.action i
  obtain ⟨M⟩ := orthogonalMatrixComparison d i horth
  let m := M.points
  have hm (σ : Gal(K/F)) (R : TestAlgebra F) (x : GroupPoints d.P.pair.G.val R)
      (j : SimpleRoot d.P.pair) :
      let a := (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso.inv
      m.hom.app R (x ≫ a.hom.hom) j = m.hom.app R x (d.action σ j) := by
    let b := (d.lift (d.descent.outer σ)).asIso.hom
    let s := (Functor.mapAut d.P (forgetPinning (A := d.A)) (d.lift (d.descent.outer σ))).asIso
    have hs : s.inv = b.group.inv := by
      apply (cancel_mono b.group.hom).mp
      exact s.inv_hom_id.trans b.group.inv_hom_id.symm
    change m.hom.app R (x ≫ s.inv.hom.hom) j = _
    rw [hs]
    exact M.equivariant b (d.action σ) (d.action_eq σ) R x j
  obtain ⟨W, f, w, emb, hemb, hsplt, _⟩ := orthogonalOrbitScalarComparison d 2 m hm i
  let t := extendedGroupIso (k := F) K
  let p : (groupPointsFunctor K).obj ((groupBaseChange F K).obj d.P.pair.G.val) ≅
      specialLinearFamilyPoints K (SimpleRoot d.P.pair) 2 :=
    baseChangePointIso (K := K) d.P.pair.G.val ≪≫
      Functor.isoWhiskerLeft (restrictTestAlgebra F K) m
  let w₀ := (groupPointsFunctor F).map f.hom ≫ w.hom
  let A := (groupBaseChange F K).obj d.G.val
  let a := (groupPointsFunctor K).mapIso (d.trivialization t) ≪≫ p
  let x₀ (R : TestAlgebra K) (x : GroupPoints A R) := baseChangePoint F K d.G.val.X R x
  have hvalues (R : TestAlgebra K) (b : MatrixMark) (x : GroupPoints A R) :
      (∀ j, b.Holds (a.hom.app R x j)) ↔
        b.Holds (w₀.app ((restrictTestAlgebra F K).obj R) (x₀ R x)) := by
    let R₀ := (restrictTestAlgebra F K).obj R
    letI : Algebra K R₀ := inferInstanceAs (Algebra K R)
    letI : IsScalarTower F K R₀ := IsScalarTower.of_algebraMap_eq' rfl
    let g := w₀.app R₀ (x₀ R x)
    let e (j : SimpleRoot d.P.pair) := Algebra.TensorProduct.lift (AlgHom.id F R₀)
      (((Algebra.ofId K R₀).restrictScalars F).comp (emb j)) (fun _ _ => Commute.all _ _)
    have heq (j : SimpleRoot d.P.pair) :
        a.hom.app R x j = SpecialLinearGroup.map (e j).toRingHom g := hsplt R j x
    simp only [heq]
    exact orbitEmbedding_preserves_marks d i emb hemb R b g
  have hmarks : d.MatchesMarks (fun R x => w₀.app R x) := by
    intro b R x
    let S := CommAlgCat.of K (K ⊗[F] R)
    let R₀ := (restrictTestAlgebra F K).obj S
    let g := testAlgebraInclusion K R
    have hg : Function.Injective g.hom :=
      Algebra.TensorProduct.includeRight_injective (B := R) (algebraMap F K).injective
    obtain ⟨y, hy⟩ := (baseChangePoints F K d.G.val.X S).2 (mapPoints g x)
    have h : b.Holds (w₀.app R₀ (x₀ S y)) ↔ subgroupSection (d.mark b) (x₀ S y) :=
      (hvalues S b y).symm.trans (splitMatrixMarks d M S y b)
    have hy' : x₀ S y = mapPoints g x := hy
    rw [hy'] at h
    exact (matrixMarks_of_algebra_injection w₀ g hg b x).symm.trans
      (h.trans (subgroup_section_of_algebra_injection d.G (d.mark b) g hg x))
  have hnatural {R S : TestAlgebra K} (g : R ⟶ S) (j : SimpleRoot d.P.pair)
      (x : GroupPoints ((groupBaseChange F K).obj d.P.pair.G.val) R) :
      p.hom.app S (mapPoints g x) j =
        SpecialLinearGroup.map g.hom.toRingHom (p.hom.app R x j) :=
    congrFun (p.hom.naturality_apply g x) j
  refine ⟨W, f, w, emb, t, (fun R => (p.app R).groupIsoToMulEquiv),
    extendedSpecIso_hom_fst K, hmarks, hemb, hnatural, hsplt, ?_⟩
  letI := d.D.comm
  intro R j u v
  dsimp only
  intro x' y' hx hy
  let R₀ := (restrictTestAlgebra F K).obj R
  let x := baseChangePoint F K d.P.pair.G.val.X R x'
  let y := baseChangePoint F K d.P.pair.G.val.X R y'
  change (m.hom.app R₀ x j).val = _ ∧ (m.hom.app R₀ y j).val = _ ∧
    ∀ l : SimpleRoot d.P.pair, l ≠ j → m.hom.app R₀ x l = 1 ∧ m.hom.app R₀ y l = 1
  change x = _ at hx
  change y = _ at hy
  rw [hx, hy]
  refine ⟨?_, ?_, ?_⟩
  · have h := congrFun (M.root_point j R₀ u) j
    rw [factorPoint_same] at h
    change (m.hom.app R₀ (rootPoint (pinnedRootCoordinate d.P j) R₀ u) j).val = _
    rw [h]
    exact SpecialLinearGroup.transvection_coe _ _
  · have h := congrFun (M.coroot_point j R₀ v) j
    rw [factorPoint_same] at h
    exact congrArg Subtype.val h
  · intro l hl
    exact ⟨(congrFun (M.root_point j R₀ u) l).trans (factorPoint_ne hl _),
      (congrFun (M.coroot_point j R₀ v) l).trans (factorPoint_ne hl _)⟩

end OrthogonalDescentMarks

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
