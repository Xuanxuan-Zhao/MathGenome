import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.Noetherian.Orzech
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct BigOperators Matrix
open Algebra.TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal

noncomputable section

open Specification
open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.Specs.StandardGroups
open LinearAlgebraicGroups.Descent.InnerTypeA.Specification
open RM03.CSA (algEquiv_matrix_algebraicClosure degree_eq_matrix_size)
open RM03.CSA.NormOneGroup (changeCoefficients extendSplitting extendSplitting_tmul
  normAt normAt_eq_det normAt_natural)

section MatrixNorm
variable {F B R S : Type*} [Field F] [Ring B] [Algebra F B]
  [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

/-- Scalar extension commutes with taking the full matrix algebra. -/
private def matrixBaseChange {m : ℕ} :
    R ⊗[F] Matrix (Fin m) (Fin m) B ≃ₐ[R] Matrix (Fin m) (Fin m) (R ⊗[F] B) :=
  let e :=
    (Algebra.TensorProduct.congr (.refl : R ≃ₐ[F] R) (matrixEquivTensor (Fin m) F B)).trans
      (((Algebra.TensorProduct.assoc F F F R B (Matrix (Fin m) (Fin m) F)).symm).trans
        (matrixEquivTensor (Fin m) F (R ⊗[F] B)).symm)
  AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
    intro r
    change e (r ⊗ₜ[F] 1) = _
    simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply]
    rw [map_one, Algebra.TensorProduct.one_def, Algebra.TensorProduct.assoc_symm_tmul,
      matrixEquivTensor_apply_symm]
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Algebra.algebraMap_eq_smul_one]
    exact IsScalarTower.algebraMap_smul (R ⊗[F] B) r
      (1 : Matrix (Fin m) (Fin m) (R ⊗[F] B)))

private theorem matrixBaseChange_single {m : ℕ} (r : R) (i j : Fin m) (b : B) :
    matrixBaseChange (r ⊗ₜ[F] Matrix.single i j b) = Matrix.single i j (r ⊗ₜ[F] b) := by
  change (matrixEquivTensor (Fin m) F (R ⊗[F] B)).symm
    ((Algebra.TensorProduct.assoc F F F R B (Matrix (Fin m) (Fin m) F)).symm
      (r ⊗ₜ[F] matrixEquivTensor (Fin m) F B (Matrix.single i j b))) = _
  rw [matrixEquivTensor_apply_single, Algebra.TensorProduct.assoc_symm_tmul,
    matrixEquivTensor_apply_symm, Matrix.map_single _ _ _ (algebraMap F (R ⊗[F] B)),
    Matrix.smul_single]
  simp

private theorem matrixBaseChange_diagonal {m : ℕ} (t : Fin m → R) :
    matrixBaseChange (scalarDiagonal (F := F) (B := B) t) =
      Matrix.diagonal (fun i => t i ⊗ₜ[F] (1 : B)) := by
  simp only [scalarDiagonal, map_sum, matrixBaseChange_single, Matrix.sum_single_eq_diagonal]

private theorem changeCoefficients_diagonal {m : ℕ} (f : R →ₐ[F] S) (t : Fin m → R) :
    changeCoefficients f (scalarDiagonal (F := F) (B := B) t) =
      scalarDiagonal (F := F) (B := B) (f ∘ t) := by
  simp [scalarDiagonal, changeCoefficients]

variable {K : Type*} [Field K] [Algebra F K] [Algebra K S] [IsScalarTower F K S]
  {m d : ℕ}

private def flattenSplitting (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K) :
    S ⊗[F] Matrix (Fin m) (Fin m) B ≃ₐ[S] Matrix (Fin m × Fin d) (Fin m × Fin d) S :=
  matrixBaseChange.trans ((extendSplitting e).mapMatrix.trans
    (Matrix.compAlgEquiv (Fin m) (Fin d) S S))

private theorem flattenSplitting_tmul (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    (s : S) (a : Matrix (Fin m) (Fin m) B) :
    flattenSplitting e (s ⊗ₜ[F] a) =
      s • (flattenSplitting (S := K) e (1 ⊗ₜ[F] a)).map (algebraMap K S) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single a]
  conv_rhs => rw [Matrix.matrix_eq_sum_single a]
  ext ⟨p, r⟩ ⟨q, t⟩
  simp only [TensorProduct.tmul_sum, map_sum, Matrix.smul_apply, Matrix.map_apply,
    Matrix.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [flattenSplitting, AlgEquiv.trans_apply, matrixBaseChange_single,
    AlgEquiv.mapMatrix_apply, Matrix.map_single, extendSplitting_tmul,
    one_smul, Algebra.algebraMap_self, Matrix.compAlgEquiv_apply, Matrix.comp_apply]
  by_cases hi : i = p <;> by_cases hj : j = q <;>
    simp [Matrix.single, hi, hj]

private theorem normAt_eq_flattenDet (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (x : S ⊗[F] Matrix (Fin m) (Fin m) B) :
    normAt hA b x = (flattenSplitting e x).det := by
  let e₀ := (flattenSplitting (S := K) (m := m) e).trans (Matrix.reindexAlgEquiv K K finProdFinEquiv)
  have hn := degree_eq_matrix_size hA e₀
  let r : (Fin m × Fin d) ≃ Fin (RM03.CSA.degree F (Matrix (Fin m) (Fin m) B)) :=
    finProdFinEquiv.trans (finCongr hn.symm)
  let e₁ := (flattenSplitting (S := K) (m := m) e).trans (Matrix.reindexAlgEquiv K K r)
  rw [normAt_eq_det hA b e₁]
  have hcomp : extendSplitting e₁ x =
      Matrix.reindexAlgEquiv S S r (flattenSplitting e x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s a =>
      rw [extendSplitting_tmul, flattenSplitting_tmul]
      rfl
  exact (congrArg Matrix.det hcomp).trans (Matrix.det_reindexAlgEquiv S S r _)

private theorem flattenSplitting_diagonal
    (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K) (t : Fin m → S) :
    flattenSplitting e (scalarDiagonal (F := F) (B := B) t) =
      Matrix.diagonal (fun p : Fin m × Fin d => t p.1) := by
  simp only [flattenSplitting, AlgEquiv.trans_apply, matrixBaseChange_diagonal,
    AlgEquiv.mapMatrix_apply]
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j <;> by_cases h' : a = b <;>
    simp [Matrix.compAlgEquiv_apply, Matrix.comp_apply, Matrix.diagonal, h, h',
      extendSplitting_tmul, ← Algebra.TensorProduct.one_def]

theorem diagonalNorm : DiagonalNorm := by
  classical
  intro F B R _ _ _ _ _ hB m _ hA ι _ b t
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure ⟨inferInstance, hB.1, hB.2⟩
  let K := AlgebraicClosure F
  let S := K ⊗[F] R
  let f : R →ₐ[F] S := includeRight
  have hf : Function.Injective f := includeRight_injective (algebraMap F K).injective
  apply hf
  change f (normAt hA b (scalarDiagonal t)) = f ((∏ i, t i) ^ RM03.CSA.degree F B)
  rw [← normAt_natural hA b f, changeCoefficients_diagonal, normAt_eq_flattenDet e,
    flattenSplitting_diagonal, Matrix.det_diagonal, Fintype.prod_prod_type,
    map_pow, map_prod]
  simp [← Finset.prod_pow]

end MatrixNorm

theorem centralSimpleMatrix : CentralSimpleMatrix := by
  intro F B _ _ _ m hm hB
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Algebra.IsCentral F B := hB.1
  let : FiniteDimensional F B := hB.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section DiagonalPoints

variable {F B R : Type u} [Field F] [Ring B] [Algebra F B]
  [CommRing R] [Algebra F R] {n : ℕ}

private theorem determinantOneTuple_prod (t : Fin n → Rˣ) :
    (∏ i, determinantOneTuple t i) = 1 := by
  simp [determinantOneTuple, Fin.prod_univ_succ]

private theorem exists_determinantOneTuple (t : Fin (n + 1) → Rˣ) :
    (∏ j, t j) = 1 ↔ ∃ v, determinantOneTuple v = t := by
  constructor
  · intro ht
    refine ⟨fun i => t i.succ, ?_⟩
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    rw [Fin.prod_univ_succ] at ht
    exact (eq_inv_of_mul_eq_one_left ht).symm
  · rintro ⟨v, rfl⟩
    exact determinantOneTuple_prod v

private def diagonalPoint (t : Fin n → Rˣ) :
    R ⊗[F] Matrix (Fin (n + 1)) (Fin (n + 1)) B :=
  scalarDiagonal (fun i => ↑(determinantOneTuple t i))

private theorem diagonalPoint_one :
    diagonalPoint (F := F) (B := B) (1 : Fin n → Rˣ) = 1 := by
  apply (matrixBaseChange (F := F) (R := R) (B := B) (m := n + 1)).injective
  rw [map_one]
  unfold diagonalPoint
  rw [matrixBaseChange_diagonal]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [determinantOneTuple, ← Algebra.TensorProduct.one_def]

private theorem diagonalPoint_mul (t v : Fin n → Rˣ) :
    diagonalPoint (F := F) (B := B) (t * v) = diagonalPoint t * diagonalPoint v := by
  apply (matrixBaseChange (F := F) (R := R) (B := B) (m := n + 1)).injective
  unfold diagonalPoint
  rw [map_mul]
  simp only [matrixBaseChange_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [determinantOneTuple, Finset.prod_mul_distrib, Algebra.TensorProduct.tmul_mul_tmul,
      mul_comm]

private theorem diagonalPoint_map {S : Type u} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (t : Fin n → Rˣ) :
    changeCoefficients f (diagonalPoint (F := F) (B := B) t) =
      diagonalPoint (F := F) (B := B) (fun i => Units.map f.toMonoidHom (t i)) := by
  unfold diagonalPoint
  rw [changeCoefficients_diagonal]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  simp only [Function.comp_apply, determinantOneTuple, Fin.cons_zero]
  change (↑(Units.map f.toMonoidHom ((∏ j, t j)⁻¹)) : S) = _
  rw [map_inv, map_prod]

private theorem diagonalPoint_norm {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralDivision F B)
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin (n + 1)) (Fin (n + 1)) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin (n + 1)) (Fin (n + 1)) B))
    (t : Fin n → Rˣ) :
    normAt hA b (diagonalPoint t) = 1 := by
  change _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b (scalarDiagonal _) = 1
  rw [diagonalNorm hB (Nat.succ_pos _) hA b]
  have h := congrArg (Units.coeHom R) (determinantOneTuple_prod t)
  rw [map_prod, map_one] at h
  change (∏ i, (↑(determinantOneTuple t i) : R)) = 1 at h
  rw [h, one_pow]

end DiagonalPoints

section Coordinates

variable {F B C R ι : Type u} [Field F] [DivisionRing B] [Algebra F B]
  [CommRing C] [Algebra F C] [CommRing R] [Algebra F R] [Fintype ι]

private def extendFunctional {A : Type u} [AddCommGroup A] [Module F A] (ℓ : A →ₗ[F] F) :
    R ⊗[F] A →ₗ[R] R :=
  (Algebra.TensorProduct.rid F R R).toLinearMap.comp (ℓ.baseChange R)

private theorem extendFunctional_tmul {A : Type u} [AddCommGroup A] [Module F A]
    (ℓ : A →ₗ[F] F) (r : R) (a : A) :
    extendFunctional ℓ (r ⊗ₜ[F] a) = r * algebraMap F R (ℓ a) := by
  simp [extendFunctional, Algebra.smul_def, mul_comm]

private theorem diagonalEntries_mem_range {m : ℕ}
    (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)) (c : C →ₐ[F] R)
    (t : Fin m → R) (w : ι → C)
    (h : ∀ j, (b.baseChange R).repr (scalarDiagonal t) j = c (w j))
    (i : Fin m) : t i ∈ c.range := by
  classical
  obtain ⟨ℓ₀, hℓ₀⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero (α := B))
  let ℓ := ℓ₀.comp (Matrix.entryLinearMap F B i i)
  let L : R ⊗[F] Matrix (Fin m) (Fin m) B →ₗ[R] R := extendFunctional ℓ
  have hentry : L (scalarDiagonal t) = t i := by
    simp only [scalarDiagonal, map_sum, L, extendFunctional_tmul]
    rw [Finset.sum_eq_single i]
    · simp [ℓ, hℓ₀]
    · intro j _ hji
      simp [ℓ, Matrix.single, hji]
    · simp
  refine ⟨∑ j, w j * algebraMap F C (ℓ (b j)), ?_⟩
  calc
    c (∑ j, w j * algebraMap F C (ℓ (b j))) =
        L (∑ j, (b.baseChange R).repr (scalarDiagonal t) j • (b.baseChange R) j) := by
      simp only [map_sum, map_mul, AlgHom.commutes, map_smul, ← h, Module.Basis.baseChange_apply,
        L, extendFunctional_tmul, smul_eq_mul, one_mul]
    _ = t i := by rw [Module.Basis.sum_repr, hentry]

open private basis_expansion from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

private theorem laurentUnits_surjective (c : C →ₐ[F] LaurentPowerCoordinates F ι)
    [DecidableEq ι] (t : ι → (LaurentPowerCoordinates F ι)ˣ)
    (ht : ∀ i, (t i).val = laurentVariable F ι i)
    (hp : ∀ i, (t i).val ∈ c.range) (hn : ∀ i, (t i)⁻¹.val ∈ c.range) :
    Function.Surjective c := by
  classical
  let ν := (AddMonoidAlgebra.of F (ι → ℤ)).toHomUnits
  have hv (i : ι) : ν (Multiplicative.ofAdd (Pi.single i 1)) = t i :=
    Units.ext (ht i).symm
  let U : Subgroup (LaurentPowerCoordinates F ι)ˣ :=
    { carrier := {x | x.val ∈ c.range ∧ (x⁻¹).val ∈ c.range}
      one_mem' := ⟨c.range.one_mem, c.range.one_mem⟩
      mul_mem' := fun hx hy => ⟨c.range.mul_mem hx.1 hy.1, c.range.mul_mem hy.2 hx.2⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by simpa only [inv_inv] using hx.1⟩ }
  have hm (d : ι → ℤ) : ν (Multiplicative.ofAdd d) ∈ U := by
    rw [← basis_expansion (ι := ι) (Multiplicative.ofAdd d), map_prod]
    apply U.prod_mem
    intro i _
    rw [map_zpow, hv]
    exact U.zpow_mem (show t i ∈ U from ⟨hp i, hn i⟩) _
  intro x
  change x ∈ c.range
  induction x using AddMonoidAlgebra.induction_on with
  | of d => exact (hm d).1
  | add x y hx hy => exact c.range.add_mem hx hy
  | smul r x hx => exact c.range.smul_mem hx r

end Coordinates

/-- The determinant-one scalar diagonal is a closed split subgroup of the F05 model. -/
theorem closedDiagonal : ClosedDiagonal.{u} := by
  classical
  intro F B _ _ _ hB n hA ι _ b
  let A := Matrix (Fin (n + 1)) (Fin (n + 1)) B
  let Q := NormOneCoordinates hA b
  let J := ULift.{u} (Fin n)
  let C := LaurentPowerCoordinates F J
  let T := multiplicativePowerGroup F J
  obtain ⟨H, P, p, hp1, hpm, hpn, eG, heG, e, hEval⟩ :=
    LinearAlgebraicGroups.Descent.InnerTypeA.normOneRepresentability hA b
  let := H.hopf
  let G := spectrum F Q
  obtain ⟨_, _, _, eT, heT, a, hLaurent⟩ :=
    LinearAlgebraicGroups.StandardGroups.multiplicativePowerSpecification F J
  have hGcoord (R : TestAlgebra F) (f : Q →ₐ[F] R) (x : Points G.val.X R)
      (hx : x.left = Spec.map (CommRingCat.ofHom f.toRingHom)) (j : ι) :
      (b.baseChange R).repr (p R (e.hom.app R x)).1 j =
        f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X j)) := by
    have hx' : x = eG.hom.app R (toConv f) := Over.OverMorphism.ext (hx.trans (heG R f).symm)
    rw [hx']
    exact hEval R f j
  have hTcoord (R : TestAlgebra F) (f : C →ₐ[F] R) (x : Points T.val.X R)
      (hx : x.left = Spec.map (CommRingCat.ofHom f.toRingHom)) (j : J) :
      ((show J → Rˣ from a.hom.app R x) j).val = f (laurentVariable F J j) := by
    have hx' : x = eT.hom.app R (toConv f) := Over.OverMorphism.ext (hx.trans (heT R f).symm)
    rw [hx']
    exact hLaurent R f j
  let D (R : TestAlgebra F) (t : (multiplicativePowerPoints F J).obj R) : R ⊗[F] A :=
    diagonalPoint (fun j => (show J → Rˣ from t) ⟨j⟩)
  let d : multiplicativePowerPoints F J ⟶ P :=
    { app := fun R => GrpCat.ofHom
        { toFun := fun t => (p R).symm ⟨D R t, diagonalPoint_norm hB hA b _⟩
          map_one' := by
            apply (p R).injective
            apply Subtype.ext
            rw [Equiv.apply_symm_apply, hp1]
            exact diagonalPoint_one
          map_mul' := by
            intro t v
            apply (p R).injective
            apply Subtype.ext
            rw [Equiv.apply_symm_apply, hpm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
            exact diagonalPoint_mul _ _ }
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro t
        apply (p S).injective
        apply Subtype.ext
        change (p S ((p S).symm _)).1 = (p S (P.map f ((p R).symm _))).1
        rw [Equiv.apply_symm_apply, hpn, Equiv.apply_symm_apply]
        exact (diagonalPoint_map f.hom _).symm }
  let θ := a.hom ≫ d ≫ e.inv
  obtain ⟨i, hi⟩ := (groupHomComparison F T.val G.val T.property.1).2 θ
  have hpoint (R : TestAlgebra F) (x : Points T.val.X R) :
      (p R (e.hom.app R (((groupPointsFunctor F).map i).app R x))).1 =
        D R (a.hom.app R x) := by
    change (groupPointsFunctor F).map i = θ at hi
    rw [hi]
    change (p R (e.hom.app R (e.inv.app R (d.app R (a.hom.app R x))))).1 = _
    rw [← GrpCat.comp_apply, e.inv_hom_id_app]
    change (p R ((p R).symm _)).1 = _
    rw [Equiv.apply_symm_apply]
  let R := CommAlgCat.of F C
  let x : Points T.val.X R := eT.hom.app R (toConv (AlgHom.id F C))
  let y : Points G.val.X R := ((groupPointsFunctor F).map i).app R x
  let c : Q →ₐ[F] C := (eG.inv.app R y).ofConv
  have hy : eG.hom.app R (toConv c) = y := by
    change eG.hom.app R (eG.inv.app R y) = y
    rw [← GrpCat.comp_apply, eG.inv_hom_id_app]
    rfl
  have hys : y.left = Spec.map (CommRingCat.ofHom c.toRingHom) := by
    rw [← hy]
    exact heG R c
  have hx : x.left = 𝟙 (Spec (CommRingCat.of C)) :=
    (heT R (AlgHom.id F C)).trans (Spec.map_id _)
  have his : i.hom.hom.left = Spec.map (CommRingCat.ofHom c.toRingHom) := by
    let g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of Q) := i.hom.hom.left
    change x.left ≫ g = _ at hys
    rw [hx] at hys
    exact (Category.id_comp g).symm.trans hys
  let t : J → Cˣ := a.hom.app R x
  let v : Fin n → Cˣ := fun j => t ⟨j⟩
  let w : Fin (n + 1) → Cˣ := determinantOneTuple v
  have hw (j : Fin (n + 1)) : (w j).val ∈ c.range :=
    diagonalEntries_mem_range b c _ _ (fun l => by
      have heval := hGcoord R c y hys l
      rw [hpoint R x] at heval
      exact heval) j
  have hv (j : J) : (t j).val ∈ c.range := hw j.down.succ
  have hinv (j : J) : ((t j)⁻¹).val ∈ c.range := by
    have hd : (∏ k ∈ Finset.univ.erase j.down.succ, w k) = (w j.down.succ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
      exact determinantOneTuple_prod v
    change ((w j.down.succ)⁻¹).val ∈ c.range
    rw [← hd]
    change (Units.coeHom C) (∏ k ∈ Finset.univ.erase j.down.succ, w k) ∈ c.range
    rw [map_prod]
    exact c.range.prod_mem fun k _ => hw k
  have hclosed : IsClosedImmersion i.hom.hom.left := by
    rw [his]
    apply IsClosedImmersion.spec_of_surjective
    exact laurentUnits_surjective c t (hLaurent R (AlgHom.id F C)) hv hinv
  exact ⟨H, P, p, e, a, i, hclosed, hp1, hpm, hpn, hGcoord, hTcoord, hpoint,
    fun _ => exists_determinantOneTuple⟩

section EqualRank

variable {F ι κ : Type u} [Field F] [Fintype ι] [Fintype κ]

private theorem surjective_of_closedSpec {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsClosedImmersion (Spec.map f)] : Function.Surjective f := by
  let eR := Scheme.ΓSpecIso R
  let eS := Scheme.ΓSpecIso S
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)).2
  intro y
  obtain ⟨x, hx⟩ := hs (eS.inv y)
  refine ⟨eR.hom x, ?_⟩
  have h := congrArg (fun g : _ ⟶ S => g x) (Scheme.ΓSpecIso_naturality f)
  change eS.hom ((Spec.map f).appTop x) = f (eR.hom x) at h
  rw [hx, Iso.inv_hom_id_apply] at h
  exact h.symm

private theorem sameRankPowers (hcard : Fintype.card ι = Fintype.card κ)
    (i : (multiplicativePowerGroup F ι).val ⟶ (multiplicativePowerGroup F κ).val)
    (hi : IsClosedImmersion i.hom.hom.left) : IsIso i := by
  classical
  let H := hopfSpec (CommRingCat.of F)
  let c : op (CommHopfAlgCat.of F (LaurentPowerCoordinates F ι)) ⟶
      op (CommHopfAlgCat.of F (LaurentPowerCoordinates F κ)) :=
    (hopfSpec.fullyFaithful (R := CommRingCat.of F)).preimage i
  have hc : H.map c = i := (hopfSpec.fullyFaithful (R := CommRingCat.of F)).map_preimage i
  let f : LaurentPowerCoordinates F κ →ₐc[F] LaurentPowerCoordinates F ι := c.unop.hom
  have hSpec : Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) = i.hom.hom.left :=
    congrArg (fun j => j.hom.hom.left) hc
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)) := hSpec ▸ hi
  have hs : Function.Surjective f := surjective_of_closedSpec
    (CommRingCat.ofHom f.toAlgHom.toRingHom)
  let φ : (κ → ℤ) →+ (ι → ℤ) := AddMonoidAlgebra.mapDomainOfBialgHom f
  have hφ := AddMonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom f
  have hmap (x : LaurentPowerCoordinates F κ) : AddMonoidAlgebra.mapDomain φ x = f x :=
    DFunLike.congr_fun hφ x
  have hsurj : Function.Surjective φ := by
    intro v
    by_contra hv
    obtain ⟨x, hx⟩ := hs (AddMonoidAlgebra.single v 1)
    have hz := Finsupp.mapDomain_of_notMem_range x.coeff v hv
    change (AddMonoidAlgebra.mapDomain φ x).coeff v = 0 at hz
    rw [hmap, hx, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hz
    exact one_ne_zero hz
  let r := LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivOfCardEq hcard : ι ≃ κ)
  have hinj : Function.Injective φ :=
    IsNoetherian.injective_of_surjective_of_injective r.toLinearMap φ.toIntLinearMap r.injective hsurj
  have hf : Function.Injective f := by
    intro x y h
    exact AddMonoidAlgebra.mapDomain_injective hinj (by simpa only [hmap] using h)
  have : IsIso c.unop := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hf, hs⟩
  have : IsIso c := by simpa only [Quiver.Hom.op_unop] using (inferInstance : IsIso c.unop.op)
  exact hc ▸ H.map_isIso c

/-- A closed inclusion between split tori of equal finite rank is an isomorphism. -/
theorem sameRankClosedImmersion : SameRankClosedImmersion.{u} := by
  intro F ι κ _ _ _ S T ⟨eS⟩ ⟨eT⟩ hcard i hi
  let V := Grp.forget (SchemeOver F) ⋙ Over.forget (Spec (CommRingCat.of F))
  let j := eS.inv ≫ i ≫ eT.hom
  have hj : IsClosedImmersion j.hom.hom.left := by
    change IsClosedImmersion (V.map j)
    dsimp only [j]
    rw [Functor.map_comp, Functor.map_comp]
    have : IsClosedImmersion (V.map i) := hi
    have : IsIso (V.map eS.inv) := V.map_isIso eS.inv
    have : IsIso (V.map eT.hom) := V.map_isIso eT.hom
    exact IsClosedImmersion.comp (V.map eS.inv) (V.map i ≫ V.map eT.hom)
  have h := sameRankPowers hcard j hj
  dsimp only [j] at h
  rwa [isIso_comp_left_iff, isIso_comp_right_iff] at h

end EqualRank

end

end LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal
