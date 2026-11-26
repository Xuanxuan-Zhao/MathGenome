import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleRing.Matrix
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeATorusWeightProjections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct BigOperators Matrix DirectSum
open Algebra.TensorProduct

namespace LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank

noncomputable section

open LinearAlgebraicGroups.Specs.InnerTypeASplitRank
open LinearAlgebraicGroups.Specs.InnerTypeARelativeContraction (scalarDiagonal blockEntry)
open LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal.Specification (determinantOneTuple)
open RM03.CSA (algEquiv_matrix_algebraicClosure degree_eq_matrix_size)
open RM03.CSA.NormOneGroup (changeCoefficients normAt normAt_natural)
open private changeCoefficients_diagonal normAt_eq_flattenDet flattenSplitting_diagonal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction

theorem diagonalAction : DiagonalAction := InnerTypeARelativeContraction.diagonalAction

theorem diagonalNorm : DiagonalNorm := by
  classical
  intro F B R _ _ _ _ _ hB m _ hA ι _ b t
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
  let K := AlgebraicClosure F
  let U := K ⊗[F] R
  let f : R →ₐ[F] U := includeRight
  have hf : Function.Injective f := includeRight_injective (algebraMap F K).injective
  apply hf
  change f (normAt hA b (scalarDiagonal t)) = f ((∏ i, t i) ^ RM03.CSA.degree F B)
  rw [← normAt_natural hA b f, changeCoefficients_diagonal, normAt_eq_flattenDet e,
    flattenSplitting_diagonal, Matrix.det_diagonal, Fintype.prod_prod_type, map_pow, map_prod]
  simp [← Finset.prod_pow]

theorem blockTransvections : BlockTransvections := InnerTypeARelativeContraction.blockTransvections

theorem blockSplitting : BlockSplitting := InnerTypeARelativeContraction.blockSplitting

open private matrixBaseChange matrixBaseChange_diagonal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
open private determinantOneTuple_prod exists_determinantOneTuple
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal

variable {F B R : Type*} [Field F] [Ring B] [Algebra F B] [CommRing R] [Algebra F R]

private theorem scalarDiagonal_injective [Nontrivial B] {n : ℕ} :
    Function.Injective (scalarDiagonal (F := F) (B := B) (R := R) (m := n)) := by
  intro t u h
  have h' := congrArg matrixBaseChange h
  rw [matrixBaseChange_diagonal, matrixBaseChange_diagonal] at h'
  have hu := Matrix.diagonal_injective h'
  have hf : Function.Injective (includeLeft : R →ₐ[F] R ⊗[F] B) :=
    includeLeft_injective (algebraMap F B).injective
  funext i
  exact hf (congrFun hu i)

theorem centralDiagonal : CentralDiagonal := by
  classical
  intro F B R _ _ _ _ _ hB n hA ι _ b
  dsimp only
  let D := fun t : Fin n → Rˣ =>
    scalarDiagonal (F := F) (B := B) (fun i => (↑(determinantOneTuple t i) : R))
  change D 1 = 1 ∧ Function.Injective D ∧ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (matrixBaseChange (F := F) (R := R) (B := B) (m := n + 1)).injective
    rw [map_one]
    unfold D
    rw [matrixBaseChange_diagonal]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [determinantOneTuple, ← Algebra.TensorProduct.one_def]
  · intro t u h
    have hd := scalarDiagonal_injective h
    funext i
    exact Units.ext (by simpa [determinantOneTuple] using congrFun hd i.succ)
  · intro t u
    apply (matrixBaseChange (F := F) (R := R) (B := B) (m := n + 1)).injective
    rw [map_mul]
    simp only [matrixBaseChange_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [determinantOneTuple, Finset.prod_mul_distrib, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  · intro t
    rw [diagonalNorm hB (Nat.succ_pos _) hA b]
    have h := congrArg (Units.coeHom R) (determinantOneTuple_prod t)
    rw [map_prod, map_one] at h
    change (∏ i, (↑(determinantOneTuple t i) : R)) = 1 at h
    rw [h, one_pow]
  · exact fun t => exists_determinantOneTuple t

theorem diagonalRootRays : DiagonalRootRays := InnerTypeARelativeContraction.diagonalRootRays

theorem diagonalRankBound : DiagonalRankBound := by
  classical
  intro F B _ _ _ hB m r hm hA ι _ b w hfaith hnorm
  cases m with
  | zero => omega
  | succ m =>
    rw [diagonalNorm hB hm hA b] at hnorm
    let e := MonoidAlgebra.of F (Multiplicative (Fin r → ℤ))
    have hrel := hnorm
    change (∏ i, e (Multiplicative.ofAdd (w i))) ^ _ = 1 at hrel
    rw [← map_prod e, ← ofAdd_sum, ← map_pow e, ← ofAdd_nsmul,
      ← e.map_one] at hrel
    have hsum : ∑ i, w i = 0 := by
      have h := (MonoidAlgebra.of_injective (R := F) (M := Multiplicative (Fin r → ℤ))) hrel
      have h' : _root_.Specs.RM03.CSA.degree F B • (∑ i, w i) = 0 := h
      have hd : 0 < _root_.Specs.RM03.CSA.degree F B := RM03.CSA.degree_pos hB
      funext j
      have hj := congrFun h' j
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at hj ⊢
      exact (mul_eq_zero.mp hj).resolve_left (by exact_mod_cast hd.ne')
    let L : (Fin r → ℤ) →ₗ[ℤ] (Fin m → ℤ) :=
      { toFun := fun c i => ∑ j, w i.castSucc j * c j
        map_add' := fun c c' => by
          ext i
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun a c => by
          ext i
          simp [Finset.mul_sum, mul_left_comm] }
    have hL : Function.Injective L := by
      intro c c' h
      have hz : L (c - c') = 0 := by rw [map_sub, h, sub_self]
      have hfull : ∀ i : Fin (m + 1), (∑ j, w i j * (c - c') j) = 0 := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · have htotal : (∑ i : Fin (m + 1), ∑ j, w i j * (c - c') j) = 0 := by
            rw [Finset.sum_comm]
            simp_rw [← Finset.sum_mul, ← Finset.sum_apply, hsum, Pi.zero_apply, zero_mul]
            simp
          rw [Fin.sum_univ_castSucc] at htotal
          have hrest : ∀ i : Fin m, (∑ j, w i.castSucc j * (c - c') j) = 0 := by
            intro i
            exact congrFun hz i
          rw [Finset.sum_eq_zero (fun i _ => hrest i), zero_add] at htotal
          exact htotal
        · exact congrFun hz i
      exact sub_eq_zero.mp (hfaith (c - c') hfull)
    simpa only [Module.finrank_pi, Fintype.card_fin, Nat.succ_sub_one] using
      LinearMap.finrank_le_finrank_of_injective hL

private theorem projectionBasisWithDimensions {B W : Type*} [DivisionRing B] [Fintype W]
    [DecidableEq W] {m : ℕ} (P : W → Matrix (Fin m) (Fin m) B)
    (hsum : ∑ a, P a = 1) (hP : ∀ a b, P a * P b = if a = b then P a else 0) :
    DirectSum.IsInternal (fun a => weightSpace (P a)) ∧
    ∃ (v : Module.Basis (Fin m) Bᵐᵒᵖ (Fin m → B)) (label : Fin m → W),
      (∀ a i, P a *ᵥ v i = if a = label i then v i else 0) ∧
      ∀ a, Nat.card {i // label i = a} =
        Module.finrank Bᵐᵒᵖ (LinearMap.range (Matrix.mulVecBilin B Bᵐᵒᵖ (P a))) := by
  classical
  let V := Fin m → B
  let A := Bᵐᵒᵖ
  let E := Matrix.mulVecBilin B A (A := B) (m := Fin m) (n := Fin m)
  let U : W → Submodule A V := fun a => LinearMap.range (E (P a))
  have hproj (a c : W) (v : U c) :
      E (P a) v.val = if a = c then v.val else 0 := by
    obtain ⟨x, hx⟩ := v.prop
    rw [← hx]
    change P a *ᵥ (P c *ᵥ x) = _
    rw [Matrix.mulVec_mulVec, hP]
    split_ifs with h
    · subst a
      rfl
    · exact Matrix.zero_mulVec x
  let L := DirectSum.coeLinearMap U
  let e := DirectSum.linearEquivFunOnFintype A W (fun a => U a)
  let J : V →ₗ[A] (a : W) → U a := LinearMap.pi (fun a => (E (P a)).rangeRestrict)
  have hinj : Function.Injective L := by
    have hl : J.comp L = e.toLinearMap := by
      apply DirectSum.linearMap_ext
      intro c
      ext v a : 2
      change (J (DirectSum.coeLinearMap U (DirectSum.lof A W (fun a => U a) c v))) a =
        (e (DirectSum.lof A W (fun a => U a) c v)) a
      rw [DirectSum.coeLinearMap_lof, DirectSum.linearEquivFunOnFintype_lof]
      apply Subtype.ext
      change E (P a) v.val = _
      rw [hproj]
      by_cases h : a = c
      · subst a
        simp
      · simp [h, Pi.single_eq_of_ne]
    intro x y h
    apply e.injective
    exact (DFunLike.congr_fun hl x).symm.trans ((congrArg J h).trans (DFunLike.congr_fun hl y))
  have hsur : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, eq_top_iff]
    intro x _
    have hx : (∑ a, E (P a) x) = x := by
      simpa only [map_sum, LinearMap.sum_apply, E, Matrix.mulVecBilin_apply, Matrix.one_mulVec]
        using congrArg (fun M => E M x) hsum
    rw [← hx]
    exact Submodule.sum_mem _ fun a _ => (le_iSup U a) ⟨x, rfl⟩
  have hU : DirectSum.IsInternal U := ⟨hinj, hsur⟩
  let v := hU.collectedBasis (fun a => Module.Free.chooseBasis A (U a))
  let o : A ≃ₗ[A] B :=
    { toEquiv := MulOpposite.opEquiv.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eV : (Fin m → A) ≃ₗ[A] V := LinearEquiv.piCongrRight (fun _ => o)
  let : Module.Finite A V := Module.Finite.of_surjective eV.toLinearMap eV.surjective
  let := FiniteDimensional.fintypeBasisIndex v
  have hcard : Fintype.card (Σ a, Module.Free.ChooseBasisIndex A (U a)) = m := by
    rw [← Module.finrank_eq_card_basis v, ← eV.finrank_eq, Module.finrank_pi, Fintype.card_fin]
  let r : (Σ a, Module.Free.ChooseBasisIndex A (U a)) ≃ Fin m :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨hU, v.reindex r, fun i => (r.symm i).1, ?_, ?_⟩
  · intro a i
    simpa only [Module.Basis.reindex_apply, E, Matrix.mulVecBilin_apply] using
      hproj a (r.symm i).1 ⟨v (r.symm i), hU.collectedBasis_mem _ _⟩
  · intro a
    let av := Module.Free.chooseBasis A (U a)
    let := FiniteDimensional.fintypeBasisIndex av
    let fiber : {i : Fin m // (r.symm i).1 = a} ≃ Module.Free.ChooseBasisIndex A (U a) :=
      (Equiv.subtypeEquiv r.symm (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype a)
    rw [Nat.card_congr fiber, Nat.card_eq_fintype_card]
    exact (Module.finrank_eq_card_basis av).symm

theorem projectionBasis : ProjectionBasis := by
  classical
  intro B W _ _ m P hsum hP
  obtain ⟨_, v, label, hv, _⟩ := projectionBasisWithDimensions P hsum hP
  exact ⟨v, label, hv⟩

theorem centralSimpleMatrix : CentralSimpleMatrix := by
  intro F B _ _ _ m hm hB
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : IsSimpleRing B := hB.1
  let : Algebra.IsCentral F B := hB.2.1
  let : FiniteDimensional F B := hB.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section NormOnWeights

private def rightLinearMatrix {D : Type*} [DivisionRing D] {m : ℕ}
    (f : (Fin m → D) →ₗ[Dᵐᵒᵖ] (Fin m → D)) : Matrix (Fin m) (Fin m) D :=
  Matrix.of fun i j => f (Pi.single j 1) i

private theorem rightLinearMatrix_mulVec {D : Type*} [DivisionRing D] {m : ℕ}
    (f : (Fin m → D) →ₗ[Dᵐᵒᵖ] (Fin m → D)) (x : Fin m → D) :
    rightLinearMatrix f *ᵥ x = f x := by
  let E := Matrix.mulVecBilin D Dᵐᵒᵖ (rightLinearMatrix f)
  let o : Dᵐᵒᵖ ≃ₗ[Dᵐᵒᵖ] D :=
    { toEquiv := MulOpposite.opEquiv.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let v := (Pi.basisFun Dᵐᵒᵖ (Fin m)).map (LinearEquiv.piCongrRight (fun _ => o))
  have hv (i : Fin m) : v i = Pi.single i 1 := by
    ext j
    by_cases h : j = i <;> simp [v, o, Pi.basisFun_apply, h]
  have he : E = f := by
    apply v.ext
    intro i
    rw [hv, Matrix.mulVecBilin_apply, Matrix.mulVec_single_one]
    rfl
  exact DFunLike.congr_fun he x

private def rightBasisMatrix {D : Type*} [DivisionRing D] {m : ℕ}
    (v : Module.Basis (Fin m) Dᵐᵒᵖ (Fin m → D)) : Matrix (Fin m) (Fin m) D :=
  Matrix.of fun i j => v j i

private theorem rightBasisMatrix_isUnit {D : Type*} [DivisionRing D] {m : ℕ}
    (v : Module.Basis (Fin m) Dᵐᵒᵖ (Fin m → D)) : IsUnit (rightBasisMatrix v) := by
  let o : Dᵐᵒᵖ ≃ₗ[Dᵐᵒᵖ] D :=
    { toEquiv := MulOpposite.opEquiv.symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := (LinearEquiv.piCongrRight (fun _ : Fin m => o)).symm.trans v.equivFun.symm
  have he (j : Fin m) : e (Pi.single j (1 : D)) = v j := by
    have h : (LinearEquiv.piCongrRight (fun _ : Fin m => o)).symm (Pi.single j (1 : D)) =
        Pi.single j (1 : Dᵐᵒᵖ) := by
      ext i
      by_cases hi : i = j <;> simp [o, hi]
    dsimp only [e, LinearEquiv.trans_apply]
    exact (congrArg v.equivFun.symm h).trans (Basis.equivFun_symm_single _ _)
  have hC : rightBasisMatrix v = rightLinearMatrix e.toLinearMap := by
    ext i j
    exact congrFun (he j).symm i
  let C := rightLinearMatrix e.toLinearMap
  let D' := rightLinearMatrix e.symm.toLinearMap
  have hCD : C * D' = 1 := Matrix.ext_iff_mulVec.mpr fun x => by
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    simp only [C, D', rightLinearMatrix_mulVec, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hDC : D' * C = 1 := Matrix.ext_iff_mulVec.mpr fun x => by
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    simp only [C, D', rightLinearMatrix_mulVec, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [hC]
  exact ⟨⟨C, D', hCD, hDC⟩, rfl⟩

private theorem projection_mul_basisMatrix {D W : Type*} [DivisionRing D] [DecidableEq W]
    {m : ℕ} (P : W → Matrix (Fin m) (Fin m) D)
    (v : Module.Basis (Fin m) Dᵐᵒᵖ (Fin m → D)) (label : Fin m → W)
    (hv : ∀ a i, P a *ᵥ v i = if a = label i then v i else 0) (a : W) :
    P a * rightBasisMatrix v =
      rightBasisMatrix v * Matrix.diagonal (fun i => if a = label i then 1 else 0) := by
  ext i j
  rw [Matrix.mul_diagonal]
  change (P a *ᵥ v j) i = v j i * (if a = label j then 1 else 0)
  rw [hv]
  split_ifs <;> simp

private theorem norm_weight_matrix {F B R W : Type*} [Field F] [DivisionRing B]
    [Algebra F B] [CommRing R] [Algebra F R] [Fintype W] [DecidableEq W]
    {m : ℕ} (hm : 0 < m) (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (P : W → Matrix (Fin m) (Fin m) B)
    (v : Module.Basis (Fin m) Bᵐᵒᵖ (Fin m → B)) (label : Fin m → W)
    (hv : ∀ a i, P a *ᵥ v i = if a = label i then v i else 0)
    (t : W → R) :
    normAt hA b (∑ a, t a ⊗ₜ[F] P a) =
      ∏ a, t a ^ (_root_.Specs.RM03.CSA.degree F B * Nat.card {i // label i = a}) := by
  let C := rightBasisMatrix v
  let Ĉ : R ⊗[F] Matrix (Fin m) (Fin m) B := 1 ⊗ₜ[F] C
  let D : W → Matrix (Fin m) (Fin m) B :=
    fun a => Matrix.diagonal (fun i => if a = label i then 1 else 0)
  have hdiag : (∑ a, t a ⊗ₜ[F] D a) = scalarDiagonal (F := F) (B := B) (t ∘ label) := by
    have hD (a : W) : D a = ∑ i : Fin m, if a = label i then Matrix.single i i (1 : B) else 0 := by
      rw [show D a = Matrix.diagonal (fun i => if a = label i then (1 : B) else 0) from rfl,
        ← Matrix.sum_single_eq_diagonal]
      simp_rw [apply_ite (Matrix.single _ _), Matrix.single_zero]
    simp_rw [hD, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
    simp only [apply_ite (TensorProduct.tmul F _), TensorProduct.tmul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, scalarDiagonal, Function.comp_apply]
  have hmatrix : (∑ a, t a ⊗ₜ[F] P a) * Ĉ =
      Ĉ * scalarDiagonal (F := F) (B := B) (t ∘ label) := by
    rw [← hdiag, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Ĉ, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact congrArg (TensorProduct.tmul F (t a)) (projection_mul_basisMatrix P v label hv a)
  let N : (R ⊗[F] Matrix (Fin m) (Fin m) B) →* R := RM03.CSA.NormOneGroup.normHom hA b
  have hu : IsUnit Ĉ := (rightBasisMatrix_isUnit v).map
    (Algebra.TensorProduct.includeRight : Matrix (Fin m) (Fin m) B →ₐ[F]
      R ⊗[F] Matrix (Fin m) (Fin m) B)
  have heq : N (∑ a, t a ⊗ₜ[F] P a) = N (scalarDiagonal (F := F) (B := B) (t ∘ label)) := by
    apply (hu.map N).mul_right_cancel
    rw [← N.map_mul, mul_comm (N _), ← N.map_mul, hmatrix]
  change _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b _ =
    _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b _ at heq
  change _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b _ = _
  rw [heq, diagonalNorm hB hm hA b, ← Finset.prod_pow]
  simp only [Function.comp_apply]
  rw [← Fintype.prod_fiberwise' label (fun a => t a ^ _root_.Specs.RM03.CSA.degree F B)]
  simp_rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card, ← pow_mul]

end NormOnWeights

private theorem rank_le_of_weight_relation {J W : Type*} [Fintype J] [Fintype W]
    [Nonempty W] (w : W → J → ℤ) (c : W → ℕ) (hc : ∀ a, 0 < c a)
    (hrel : (∑ a, c a • w a) = 0)
    (hfaith : ∀ x : J → ℤ, (∀ a, (∑ j, w a j * x j) = 0) → x = 0) :
    Fintype.card J ≤ Fintype.card W - 1 := by
  classical
  let a : W := Classical.choice inferInstance
  let L : (J → ℤ) →ₗ[ℤ] ({b : W // b ≠ a} → ℤ) :=
    { toFun := fun x b => ∑ j, w b.val j * x j
      map_add' := fun x y => by
        ext b
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext b
        simp [Finset.mul_sum, mul_left_comm] }
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply hfaith x
    have hout (b : W) (hb : b ≠ a) : (∑ j, w b j * x j) = 0 := congrFun hx ⟨b, hb⟩
    have hsum : (∑ b, (c b : ℤ) * (∑ j, w b j * x j)) = 0 := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_mul]
      have h := congrFun hrel j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h
      simp only [nsmul_eq_mul] at h
      rw [h, zero_mul]
    have hsum' : (c a : ℤ) * (∑ j, w a j * x j) = 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)] at hsum
      rw [Finset.sum_eq_zero (fun b hb => by rw [hout b (Finset.ne_of_mem_erase hb), mul_zero]),
        zero_add] at hsum
      exact hsum
    intro b
    by_cases hb : b = a
    · subst b
      exact (mul_eq_zero.mp hsum').resolve_left (by exact_mod_cast (hc a).ne')
    · exact hout b hb
  simpa only [Module.finrank_pi, Fintype.card_subtype_compl (· = a), Fintype.card_subtype_eq] using
    LinearMap.finrank_le_finrank_of_injective hL

universe u

open LinearAlgebraicGroups.Specs.InnerTypeATorusWeightProjections (WeightExpansion mapCharacter)
open LinearAlgebraicGroups.Specs.InnerTypeARelativeContraction (NormOnePoints ScalarDiagonalModel)
open LinearAlgebraicGroups.Specs.StandardGroups (multiplicativePowerGroup multiplicativePowerPoints)

private def powerCharacterPoints (F J : Type u) [Field F] [Fintype J] :
    (groupPointsFunctor F).obj (multiplicativePowerGroup F J).val ≅
      Specs.DiagonalizableGroups.characterValuedPoints F (Multiplicative (J → ℤ)) :=
  let e := CommHopfAlgCat.isoMk (AddMonoidAlgebra.toMultiplicativeBialgEquiv F F (J → ℤ))
  (groupPointsFunctor F).mapIso ((hopfSpec (CommRingCat.of F)).mapIso e.op.symm) ≪≫
    LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso F _

private theorem splitTorusWeightExpansion {F B J : Type u} [Field F] [DivisionRing B]
    [Algebra F B] {m : ℕ} {hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} (P : NormOnePoints hA b H) (T : ClosedSubgroup H.val)
    [Fintype J] (a : (groupPointsFunctor F).obj T.group ≅
      Specs.DiagonalizableGroups.characterValuedPoints F (Multiplicative (J → ℤ))) :
    WeightExpansion (splitTorusAction P T a) := by
  let i := a.inv ≫ (groupPointsFunctor F).map T.inclusion
  apply LinearAlgebraicGroups.InnerTypeATorusWeightProjections.faithfulPointWeights
  · intro R S f t
    have h := i.naturality_apply f t
    change i.app S (mapCharacter f t) = mapPoints f (i.app R t) at h
    change (P.point S (i.app S (mapCharacter f t))).val =
      Algebra.TensorProduct.map f.hom (AlgHom.id F _) (P.point R (i.app R t)).val
    rw [h, P.natural]
  · intro R s t h
    have hi : i.app R s = i.app R t := (P.point R).injective (Subtype.ext h)
    apply (ConcreteCategory.bijective_of_isIso (a.inv.app R)).1
    let _ : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
    let _ : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono T.inclusion.hom.hom).mp hi

set_option maxHeartbeats 600000 in
theorem splitTorusWeights : SplitTorusWeights.{u} := by
  classical
  intro F B J _ _ _ _ m hm hB hA ι _ b H P T ⟨e⟩
  let a := (groupPointsFunctor F).mapIso e ≪≫ powerCharacterPoints F J
  let ρ := splitTorusAction P T a
  let M := Multiplicative (J → ℤ)
  refine ⟨a, ?_⟩
  obtain ⟨Q, _, hproj, hsum, hρ, hgen, hfaith⟩ := splitTorusWeightExpansion P T a
  let W := ↥Q.support
  let μ (a : W) := Module.finrank Bᵐᵒᵖ (weightSpace (Q a.val))
  let Q' (a : W) := Q a.val
  have hsum' : (∑ a : W, Q' a) = 1 := (Finset.sum_subtype Q.support (fun _ => Iff.rfl) Q).symm.trans hsum
  have hproj' (a b : W) : Q' a * Q' b = if a = b then Q' a else 0 := by
    simpa only [Q', Subtype.coe_inj] using hproj a.val b.val
  obtain ⟨hsumInternal, v, label, hv, hcard⟩ := projectionBasisWithDimensions Q' hsum' hproj'
  have hweight (a : W) (x : Fin m → B) : x ∈ weightSpace (Q' a) ↔
      ∀ c : W, Q' c *ᵥ x = if c = a then x else 0 := by
    constructor
    · rintro ⟨y, rfl⟩ c
      change Q' c *ᵥ (Q' a *ᵥ y) = if c = a then Q' a *ᵥ y else 0
      rw [Matrix.mulVec_mulVec, hproj']
      split_ifs <;> simp [*]
    · intro hx
      have h := hx a
      rw [ite_eq_left rfl] at h
      exact ⟨x, h⟩
  have hspan : Submodule.span ℚ (Set.range (fun (a : W) (j : J) => (a.val.toAdd j : ℚ))) = ⊤ := by
    let castCharacter : (J → ℤ) →+ (J → ℚ) :=
      { toFun := fun a j => a j
        map_zero' := by ext j; simp
        map_add' := by intro a c; ext j; simp }
    let L := Submodule.span ℚ (Set.range (fun a : W => castCharacter a.val.toAdd))
    change L = ⊤
    have hL : (⊤ : Subgroup M) ≤ (L.toAddSubgroup.comap castCharacter).toSubgroup := by
      rw [← hgen]
      exact (Subgroup.closure_le _).mpr fun a ha => Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
    rw [eq_top_iff, ← (Pi.basisFun ℚ J).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    let v : J → ℤ := Pi.single j 1
    have hj : castCharacter v ∈ L :=
      hL (show Multiplicative.ofAdd v ∈ (⊤ : Subgroup M) from Subgroup.mem_top _)
    have hcast : castCharacter v = Pi.basisFun ℚ J j := by
      ext k
      simp only [v, castCharacter, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.basisFun_apply,
        Pi.single_apply]
      split_ifs <;> simp
    exact hcast ▸ hj
  have hcard' (a : W) : Nat.card {i // label i = a} = μ a := hcard a
  have hlabel : Function.Surjective label := by
    intro a
    by_contra! ha
    have hz : Q' a * rightBasisMatrix v = 0 := by
      rw [projection_mul_basisMatrix Q' v label hv a]
      simp [fun i => (ha i).symm]
    have hzero : Q' a = 0 := (rightBasisMatrix_isUnit v).mul_right_cancel (by rw [hz, zero_mul])
    exact (Finsupp.mem_support_iff.mp a.prop) hzero
  have hμ (a : W) : 0 < μ a := by
    obtain ⟨i, hi⟩ := hlabel a
    rw [← hcard' a, Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  have hμsum : (∑ a, μ a) = m := by
    calc
      _ = ∑ a, Nat.card {i // label i = a} := Finset.sum_congr rfl fun a _ => (hcard' a).symm
      _ = ∑ a, ∑ _ : {i // label i = a}, (1 : ℕ) := by simp
      _ = ∑ _ : Fin m, (1 : ℕ) := Fintype.sum_fiberwise label (fun _ => (1 : ℕ))
      _ = m := by simp
  have hsimple := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  let d := _root_.Specs.RM03.CSA.degree F B
  have hnorm (R : TestAlgebra F) (t : M →* Rˣ) :
      _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b (ρ R t) =
        ∏ a : W, (t a.val : R) ^ (d * μ a) := by
    rw [hρ, Finset.sum_subtype Q.support (fun _ => Iff.rfl)]
    have h := norm_weight_matrix hm hsimple hA b Q' v label hv (fun a => (t a.val : R))
    change _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b (∑ a : W, (t a.val : R) ⊗ₜ[F] Q a.val) =
      ∏ a : W, (t a.val : R) ^ (d * Nat.card {i // label i = a}) at h
    simpa only [hcard'] using h
  have hrel : (∏ a : W, a.val ^ (d * μ a)) = 1 := by
    let R₀ : TestAlgebra F := CommAlgCat.of F (MonoidAlgebra F M)
    let e₀ : M →* R₀ˣ := (MonoidAlgebra.of F M).toHomUnits
    have heq : _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b (ρ R₀ e₀) = 1 :=
      (P.point R₀ (((groupPointsFunctor F).map T.inclusion).app R₀ (a.inv.app R₀ e₀))).prop
    rw [hnorm] at heq
    let e := MonoidAlgebra.of F M
    apply MonoidAlgebra.of_injective (R := F) (M := M)
    change (∏ a : W, e a.val ^ (d * μ a)) = 1 at heq
    simpa only [map_prod, map_pow, map_one] using heq
  have hbound : Fintype.card J ≤ Fintype.card W - 1 := by
    let w (a : W) : J → ℤ := a.val.toAdd
    have hs : (∑ a, (d * μ a) • w a) = 0 := by
      simpa only [toAdd_prod, toAdd_pow, toAdd_one] using congrArg Multiplicative.toAdd hrel
    let _ : Nonempty W := ⟨label ⟨0, hm⟩⟩
    refine rank_le_of_weight_relation w (fun a => d * μ a) (fun a =>
      Nat.mul_pos (RM03.CSA.degree_pos hsimple) (hμ a)) hs ?_
    intro x hx
    let l : (J → ℤ) →+ ℤ :=
      { toFun := fun y => ∑ j, y j * x j
        map_zero' := by simp
        map_add' := fun y z => by simp [add_mul, Finset.sum_add_distrib] }
    have h := hfaith l.toMultiplicative 1 (fun a ha => hx ⟨a, ha⟩)
    funext j
    let y : J → ℤ := Pi.single j 1
    have hj := DFunLike.congr_fun h (Multiplicative.ofAdd y)
    change (∑ k, y k * x k) = 0 at hj
    simpa [y, Pi.single_apply] using hj
  refine ⟨Q, ?_, hsum, hρ, hgen, hspan, hsumInternal, hweight, hμ, hμsum,
    ⟨v, label, hv, hcard'⟩, hnorm, hrel, ?_, ?_⟩
  · intro a b
    by_cases h : a = b
    · simpa only [ite_eq_left h] using hproj a b
    · simpa only [ite_eq_right h] using hproj a b
  · simpa only [W, Fintype.card_coe] using hbound
  · simpa only [W, Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_surjective label hlabel

open private surjective_of_closedSpec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal

private theorem splitRank_le_of_closedImmersion {F I J : Type u} [Field F] [Fintype I]
    [Fintype J] {S T : GroupScheme F}
    (eS : S ≅ (multiplicativePowerGroup F I).val) (eT : T ≅ (multiplicativePowerGroup F J).val)
    (i : S ⟶ T) (hi : IsClosedImmersion i.hom.hom.left) : Fintype.card I ≤ Fintype.card J := by
  let V := Grp.forget (SchemeOver F) ⋙ Over.forget (Spec (CommRingCat.of F))
  let j := eS.inv ≫ i ≫ eT.hom
  have hj : IsClosedImmersion j.hom.hom.left := by
    change IsClosedImmersion (V.map j)
    dsimp only [j]
    rw [Functor.map_comp, Functor.map_comp]
    let : IsClosedImmersion (V.map i) := hi
    let : IsIso (V.map eS.inv) := V.map_isIso eS.inv
    let : IsIso (V.map eT.hom) := V.map_isIso eT.hom
    exact IsClosedImmersion.comp (V.map eS.inv) (V.map i ≫ V.map eT.hom)
  let H := hopfSpec (CommRingCat.of F)
  let f := (hopfSpec.fullyFaithful (R := CommRingCat.of F)).preimage j
  have hf : H.map f = j := (hopfSpec.fullyFaithful (R := CommRingCat.of F)).map_preimage j
  let c : Specs.StandardGroups.LaurentPowerCoordinates F J →ₐc[F]
      Specs.StandardGroups.LaurentPowerCoordinates F I := f.unop.hom
  have hSpec : Spec.map (CommRingCat.ofHom c.toAlgHom.toRingHom) = j.hom.hom.left :=
    congrArg (fun g => g.hom.hom.left) hf
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom c.toAlgHom.toRingHom)) := hSpec ▸ hj
  have hs : Function.Surjective c := surjective_of_closedSpec (CommRingCat.ofHom c.toAlgHom.toRingHom)
  let φ : (J → ℤ) →+ (I → ℤ) := AddMonoidAlgebra.mapDomainOfBialgHom c
  have hφ : Function.Surjective φ := by
    intro a
    by_contra ha
    obtain ⟨p, hp⟩ := hs (AddMonoidAlgebra.single a 1)
    have hz := Finsupp.mapDomain_of_notMem_range p.coeff a ha
    have he : AddMonoidAlgebra.mapDomain φ p = c p :=
      DFunLike.congr_fun (AddMonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom c) p
    change (AddMonoidAlgebra.mapDomain φ p).coeff a = 0 at hz
    rw [he, hp, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hz
    exact one_ne_zero hz
  simpa only [Module.finrank_pi] using
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toIntLinearMap) hφ

open LinearAlgebraicGroups.Specs.InnerTypeARelativeContraction
  (diagonalTuples CentralizesCharacterKernel IsBlockCharacter)
open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.Relative.RelativeChambers (relativeRoots)
open LinearAlgebraicGroups.Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open LinearAlgebraicGroups.Specs.CharacterDescent (Character)
open LinearAlgebraicGroups.Specs.CharacterPairing (characterValue)
open LinearAlgebraicGroups.Specs.EquivariantUnipotentSeries (onPoints)
open private unitPresentation unitPresentation_value transvectionPoint transvection_map
  transvection_centralizes normPoint_val_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
open private centralizes_iff_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private factors_of_range_subset from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private schemeKernel_exists schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem characterValue_comp {F : Type u} [Field F] {S T : GroupScheme F}
    (j : S ⟶ T) (a : Character T) (R : TestAlgebra F) (x : GroupPoints S R) :
    characterValue (j ≫ a) R x = characterValue a R (x ≫ j.hom.hom) := by
  have h : x ≫ (j ≫ a).hom.hom = (x ≫ j.hom.hom) ≫ a.hom.hom :=
    (Category.assoc (show Points S.X R from x) j.hom.hom a.hom.hom).symm
  unfold characterValue
  dsimp only
  rw [h]

private theorem centralizesFullKernel {F : Type u} [Field F] {G : GroupScheme F}
    (S : ClosedSubgroup G) (a : Character S.group) (K : ClosedSubgroup S.group)
    (hK : Specs.IsSchemeKernel a K)
    (R : TestAlgebra F) (g : GroupPoints G R) :
    CentralizesCharacterKernel S a g ↔ Centralizes (K.inclusion ≫ S.inclusion) g := by
  have he (T : TestAlgebra F) (t : GroupPoints S.group T) : characterValue a T t = 1 ↔
      ∃ s : GroupPoints K.group T, onPoints K.inclusion T s = t := by
    let v := (unitPresentation F).hom.app T
    have ht : (v (onPoints a T t) : Tˣ).val = characterValue a T t := by
      rw [unitPresentation_value]
      exact (characterValue_comp a (𝟙 _) T t).symm.trans (by rw [Category.comp_id])
    have h1 : (v 1 : Tˣ).val = 1 := congrArg Units.val v.hom.map_one
    have h : characterValue a T t = 1 ↔ onPoints a T t = 1 := by
      constructor
      · intro h
        exact (ConcreteCategory.bijective_of_isIso v).1 (Units.ext (ht.trans (h.trans h1.symm)))
      · intro h
        exact ht.symm.trans ((congrArg (fun x => (v x : Tˣ).val) h).trans h1)
    exact h.trans (schemeKernel_sections hK t).symm
  constructor
  · intro hg
    apply (centralizes_iff_affine _ _).mpr
    intro T f t
    let r : R ⟶ T := ((algSpec.fullyFaithful (R := CommRingCat.of F)).preimage f).unop
    have hr : (testSpec F).map r.op = f := (algSpec.fullyFaithful (R := CommRingCat.of F)).map_preimage f
    change Commute (show GroupPoints G T from f ≫ g)
      (onPoints S.inclusion T (onPoints K.inclusion T t))
    rw [← hr]
    exact hg T r _ ((he T _).mpr ⟨t, rfl⟩)
  · intro hg T f t ht
    obtain ⟨s, hs⟩ := (he T t).mp ht
    have h := (centralizes_iff_affine _ _).mp hg T ((testSpec F).map f.op) s
    change Commute (show GroupPoints G T from mapPoints f g)
      (onPoints S.inclusion T (onPoints K.inclusion T s)) at h
    rw [hs] at h
    exact h

set_option maxHeartbeats 600000 in
private theorem blockIdentityComponent {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {m : ℕ} (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    {hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} {P : NormOnePoints hA b H} {S : ClosedSubgroup H.val}
    (hS : IsMaximalSplitTorus S) (D : ScalarDiagonalModel P S)
    {i j : Fin m} (hij : i ≠ j) (a : relativeRoots S) (ha : IsBlockCharacter D i j a.val) :
    BlockIdentityComponent D i j a := by
  classical
  let Gm := specGroup (Specs.DiagonalizableGroups.groupAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)
  let _ : IsAffine Gm.X.left := inferInstanceAs (IsAffine (Spec
    (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters))))
  obtain ⟨K, hK⟩ := schemeKernel_exists (show S.group ⟶ Gm from a.val)
  let W := Specs.GeometricBorelConjugacy.subgroupOfSubgroup S K
  obtain ⟨Z, hZ⟩ := centralizerScheme F H W
  have hker (R : TestAlgebra F) (g : GroupPoints H.val R) :
      CentralizesCharacterKernel S a.val g ↔ ∃ z : GroupPoints Z.group R, z ≫ Z.inclusion.hom.hom = g :=
    (centralizesFullKernel S a.val K hK R g).trans (hZ _ g)
  obtain ⟨Q, C, q, inc, hi, _, _⟩ := identityComponentAndQuotient F (Specs.Unipotent.closedSubgroupAlgebraicGroup Z)
  let Z₀ : ClosedSubgroup Z.group := ⟨C, inc, hi.closedImmersion⟩
  have hr : Set.range Z₀.inclusion.hom.hom.left =
      connectedComponent ((MonObj.one (X := Z.group.X)).left (IsLocalRing.closedPoint F)) :=
    hi.identityComponent.trans (congrArg (fun p => connectedComponent ((MonObj.one (X := Z.group.X)).left p))
      (Subsingleton.elim (α := PrimeSpectrum F) _ _))
  let _ : FiniteDimensional F B := hB.2.2
  let v := Module.Free.chooseBasis F B
  let I := Module.Free.ChooseBasisIndex F B
  let _ := FiniteDimensional.fintypeBasisIndex v
  let A := CommAlgCat.of F (MvPolynomial I F)
  let y : A ⊗[F] B := ∑ l : I, MvPolynomial.X l ⊗ₜ[F] v l
  let f := transvectionPoint (P := P) hB A i j hij y
  obtain ⟨fz, hfz⟩ := (hker A f).mp (transvection_centralizes v D hB hij a ha A y)
  let z : Points Z.group.X A := fz
  let B₀ : TestAlgebra F := CommAlgCat.of F F
  let aug : A ⟶ B₀ := CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : I => (0 : F)))
  have hzero : changeCoefficients aug.hom y = 0 := by
    dsimp only [y]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro l _
    rw [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change MvPolynomial.aeval (fun _ : I => (0 : F)) (MvPolynomial.X l) ⊗ₜ[F] v l = 0
    rw [MvPolynomial.aeval_X, TensorProduct.zero_tmul]
  have hf1 : mapPoints aug f = (1 : GroupPoints H.val B₀) := by
    apply normPoint_val_injective P
    change (P.point B₀ (mapPoints aug f)).val = (P.point B₀ 1).val
    rw [transvection_map, P.one, hzero, map_zero, add_zero]
  have hfz1 : mapPoints aug fz = (1 : GroupPoints Z.group B₀) := by
    let _ : IsClosedImmersion Z.inclusion.hom.hom.left := Z.isClosedImmersion
    let _ : Mono Z.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono Z.inclusion.hom.hom).mp
    change ((testSpec F).map aug.op ≫ z) ≫ Z.inclusion.hom.hom = onPoints Z.inclusion B₀ 1
    have h : ((testSpec F).map aug.op ≫ z) ≫ Z.inclusion.hom.hom = mapPoints aug f :=
      (Category.assoc _ _ _).trans (congrArg ((testSpec F).map aug.op ≫ ·) hfz)
    exact h.trans (hf1.trans (map_one (onPoints Z.inclusion B₀)).symm)
  have hs : Set.range z.left ⊆ Set.range Z₀.inclusion.hom.hom.left := by
    rw [hr, ← Set.image_univ]
    have : ConnectedSpace ((testSpec F).obj (Opposite.op A)).left :=
      inferInstanceAs (ConnectedSpace (PrimeSpectrum (MvPolynomial I F)))
    apply (isConnected_univ.image _ z.left.continuous.continuousOn).subset_connectedComponent
    rw [Set.image_univ]
    exact ⟨((testSpec F).map aug.op).left (IsLocalRing.closedPoint F),
      congrArg (fun g : Points Z.group.X B₀ => g.left (IsLocalRing.closedPoint F)) hfz1⟩
  let _ : IsReduced ((testSpec F).obj (Opposite.op A)).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of (MvPolynomial I F))))
  obtain ⟨f₀, hf₀⟩ := factors_of_range_subset z Z₀.inclusion.hom.hom Z₀.isClosedImmersion hs
  refine ⟨K, Z, Z₀, hK, hZ, hi.openImmersion, hr, ?_⟩
  intro c hc R g
  have hfull := InnerTypeARelativeContraction.fullKernelContraction hB hA b H P S hS D i j hij a ha c hc R g
  constructor
  · rintro ⟨⟨z, hz⟩, hlimit⟩
    exact hfull.mp ⟨(hker R g).mpr ⟨z ≫ Z₀.inclusion.hom.hom, (Category.assoc _ _ _).trans hz⟩, hlimit⟩
  · intro hg
    have hlimit := (hfull.mpr hg).2
    obtain ⟨x, hx, _⟩ := hg
    let e : A ⟶ R := CommAlgCat.ofHom (MvPolynomial.aeval (fun l => (v.baseChange R).repr x l))
    have he : changeCoefficients e.hom y = x := by
      dsimp only [y]
      rw [map_sum]
      conv_rhs => rw [← (v.baseChange R).sum_repr x]
      apply Finset.sum_congr rfl
      intro l _
      rw [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change MvPolynomial.aeval (fun r => (v.baseChange R).repr x r) (MvPolynomial.X l) ⊗ₜ[F] v l =
        ((v.baseChange R).repr x l) • (v.baseChange R) l
      rw [MvPolynomial.aeval_X, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hg' : mapPoints e f = g := by
      apply normPoint_val_injective P
      exact (transvection_map hB e i j hij y).trans
        ((congrArg (fun x => 1 + blockEntry i j x) he).trans hx.symm)
    refine ⟨⟨mapPoints e f₀, ?_⟩, hlimit⟩
    change ((testSpec F).map e.op ≫ f₀) ≫ Z₀.inclusion.hom.hom ≫ Z.inclusion.hom.hom = _
    have h : ((testSpec F).map e.op ≫ f₀) ≫ Z₀.inclusion.hom.hom ≫ Z.inclusion.hom.hom = mapPoints e f :=
      (Category.assoc _ _ _).trans (congrArg ((testSpec F).map e.op ≫ ·)
        ((Category.assoc f₀ _ _).symm.trans ((congrArg (· ≫ Z.inclusion.hom.hom) hf₀).trans hfz)))
    exact h.trans hg'

private theorem relativeBlockDescription {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {m : ℕ} (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    {hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} {P : NormOnePoints hA b H} {S : ClosedSubgroup H.val}
    (hS : IsMaximalSplitTorus S) (D : ScalarDiagonalModel P S) : RelativeBlockDescription D := by
  obtain ⟨α, _, hα, _, _, hcochar⟩ := InnerTypeARelativeContraction.relativeRootPairing hA b H P S D
  have hroot := InnerTypeARelativeContraction.relativeRootCalculation hB hA b H P S hS D
  have ha (i j : Fin m) (hij : i ≠ j) : α i j ∈ relativeRoots S :=
    (hroot (α i j)).mpr ⟨i, j, hij, hα i j⟩
  refine ⟨α, ha, hα, ?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro hr
      obtain ⟨i, j, hij, hh⟩ := (hroot a).mp hr
      refine ⟨i, j, hij, RootData.CharacterPairing.characterValuesDetectCharacters hS.1 ?_⟩
      intro R t
      exact (hh R t).trans (hα i j R t).symm
    · rintro ⟨i, j, hij, rfl⟩
      exact ha i j hij
  · intro i j hij
    obtain ⟨w, hw⟩ := hcochar i j hij
    exact ⟨_, hw⟩
  · intro i j hij
    exact blockIdentityComponent hB hS D hij ⟨α i j, ha i j hij⟩ (hα i j)
  · intro i j hij c hc R g
    let a : relativeRoots S := ⟨α i j, ha i j hij⟩
    refine ⟨InnerTypeARelativeContraction.fullKernelContraction hB hA b H P S hS D i j hij
      a (hα i j) c hc R g, fun C => ?_⟩
    exact InnerTypeARelativeContraction.componentContraction hB hA b H P S hS D i j hij
      a (hα i j) C c hc R g

private def determinantOneEquiv {R : Type u} [CommRing R] (n : ℕ) :
    (ULift.{u} (Fin n) → Rˣ) ≃* diagonalTuples (n + 1) R where
  toFun t := ⟨determinantOneTuple (fun j => t ⟨j⟩), determinantOneTuple_prod _⟩
  invFun t j := t.val j.down.succ
  left_inv t := by funext j; cases j; rfl
  right_inv t := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have ht : (∏ j, t.val j) = 1 := t.prop
    rw [Fin.prod_univ_succ] at ht
    exact (eq_inv_of_mul_eq_one_left ht).symm
  map_mul' t s := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change (∏ j : Fin n, t ⟨j⟩ * s ⟨j⟩)⁻¹ = (∏ j : Fin n, t ⟨j⟩)⁻¹ * (∏ j : Fin n, s ⟨j⟩)⁻¹
    simp [Finset.prod_mul_distrib, mul_comm]

set_option maxHeartbeats 600000 in
theorem splitRank : SplitRank.{u} := by
  classical
  intro F B _ _ _ n hB hA ι _ b
  let J := ULift.{u} (Fin n)
  obtain ⟨h, U, p, e, a, i, hi, hone, hmul, hnatural, heval, _, hpoint, _⟩ :=
    InnerTypeAClosedDiagonal.closedDiagonal hB n hA b
  let A := LinearAlgebraicGroups.Descent.InnerTypeA.Specification.NormOneCoordinates hA b
  let H := @Specs.StandardGroups.spectrum F _ A _ h.hopf inferInstance
  let P : NormOnePoints hA b H :=
    { point := fun R => (e.app R).groupIsoToMulEquiv.toEquiv.trans (p R)
      one := fun R => by
        change (p R (e.hom.app R 1)).val = 1
        rw [(e.hom.app R).hom.map_one, hone]
      mul := fun R x y => by
        change (p R (e.hom.app R (x * y))).val = _
        rw [(e.hom.app R).hom.map_mul, hmul]
        rfl
      natural := fun f x =>
        (congrArg (fun y => (p _ y).val) (e.hom.naturality_apply f x)).trans (hnatural f _) }
  let S : ClosedSubgroup H.val := ⟨(multiplicativePowerGroup F J).val, i, hi⟩
  have hs : Nonempty (S.group ≅ (multiplicativePowerGroup F J).val) := ⟨Iso.refl _⟩
  have hbound (r : ℕ) (T : ClosedSubgroup H.val)
      (ht : Nonempty (T.group ≅ (multiplicativePowerGroup F (ULift.{u} (Fin r))).val)) : r ≤ n := by
    obtain ⟨_, Q, _, _, _, _, _, _, _, _, _, _, _, _, hr, hQ⟩ :=
      splitTorusWeights (Nat.succ_pos n) hB hA b H P T ht
    simp only [Fintype.card_ulift, Fintype.card_fin] at hr
    omega
  have hmax : IsMaximalSplitTorus S := by
    refine ⟨⟨n, hs⟩, ?_⟩
    rintro T ⟨r, hr⟩ ⟨j, hj⟩
    have hcomp : j.hom.hom.left ≫ T.inclusion.hom.hom.left = S.inclusion.hom.hom.left :=
      congrArg (fun f => f.hom.hom.left) hj
    let : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
    let : IsClosedImmersion (j.hom.hom.left ≫ T.inclusion.hom.hom.left) := hcomp.symm ▸ S.isClosedImmersion
    have hjc := IsClosedImmersion.of_comp_isClosedImmersion j.hom.hom.left T.inclusion.hom.hom.left
    obtain ⟨eT⟩ := hr
    have hle := splitRank_le_of_closedImmersion (Iso.refl S.group) eT j hjc
    change Fintype.card J ≤ Fintype.card (ULift.{u} (Fin r)) at hle
    simp only [J, Fintype.card_ulift, Fintype.card_fin] at hle
    have hcard : Fintype.card J = Fintype.card (ULift.{u} (Fin r)) := by
      simpa only [J, Fintype.card_ulift, Fintype.card_fin] using le_antisymm hle (hbound r T ⟨eT⟩)
    let : IsIso j := InnerTypeAClosedDiagonal.sameRankClosedImmersion hs ⟨eT⟩ hcard j hjc
    exact ⟨inv j, by rw [← hj, IsIso.inv_hom_id_assoc]⟩
  let D : ScalarDiagonalModel P S :=
    { tuple := fun R => (a.app R).groupIsoToMulEquiv.trans (determinantOneEquiv n)
      natural := fun {R T} f t i => by
        let x : J → Tˣ := a.hom.app T (mapPoints f t)
        let y : J → Rˣ := a.hom.app R t
        have hxy : x = fun j => Units.map f.hom.toMonoidHom (y j) := a.hom.naturality_apply f t
        change determinantOneTuple (fun j => x ⟨j⟩) i =
          Units.map f.hom.toMonoidHom (determinantOneTuple (fun j => y ⟨j⟩) i)
        rw [hxy]
        refine Fin.cases ?_ (fun _ => rfl) i
        simp [determinantOneTuple, map_prod]
      diagonal := hpoint }
  exact ⟨h, P, S, heval, hs, hmax,
    ⟨D, relativeBlockDescription hmax D (hB := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB)⟩,
    hbound⟩

open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsSplitTorus)
open LinearAlgebraicGroups.Specs.StandardGroups (specialLinearPoints)
open LinearAlgebraicGroups.Specs.CharacterPairing (characterValue)
open private reindexedSplitMatrixCoordinates reindexedSplitMatrixCoordinates_natural
  reindexedSplitMatrixCoordinates_diagonal normAt_eq_splitDet
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
open private baseChangePointIso affine_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
open private flattenSplitting flattenSplitting_tmul matrixBaseChange_block flattened_block_product
  sum_flattened_block from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
open RM03.CSA.NormOneGroup (extendSplitting extendSplitting_tmul)

private theorem splitBlockPointCoordinates {F B K : Type u} [Field F] [DivisionRing B]
    [Algebra F B] [Field K] [Algebra F K] {m d : ℕ}
    (s : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    {hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H) :
    let G := Specs.Unipotent.baseChangedAlgebraicGroup K H
    let κ := ULift.{u} (Fin m × Fin d)
    ∃ M : (groupPointsFunctor K).obj G.val ≅ specialLinearPoints K κ,
      ∀ (R : TestAlgebra K) (g : GroupPoints G.val R),
        (show Matrix.SpecialLinearGroup κ R from M.hom.app R g).val =
          Matrix.reindexAlgEquiv R R Equiv.ulift.symm
            (flattenSplitting (S := restrictTestAlgebraObj F K R) s
              (P.point (restrictTestAlgebraObj F K R)
                (baseChangePoint F K H.val.X R g)).val) := by
  classical
  let A := restrictTestAlgebra F K
  let κ := ULift.{u} (Fin m × Fin d)
  let E (R : TestAlgebra K) :
      A.obj R ⊗[F] Matrix (Fin m) (Fin m) B ≃ₐ[R] Matrix κ κ R :=
    (flattenSplitting (S := A.obj R) s).trans (Matrix.reindexAlgEquiv R R Equiv.ulift.symm)
  have norm (R : TestAlgebra K) (x : A.obj R ⊗[F] Matrix (Fin m) (Fin m) B) :
      normAt hA b x = (E R x).det :=
    (normAt_eq_flattenDet s hA b x).trans (Matrix.det_reindexAlgEquiv R R Equiv.ulift.symm _).symm
  let points (R : TestAlgebra K) : GroupPoints H.val (A.obj R) ≃*
      Matrix.SpecialLinearGroup κ R :=
    { (P.point _).trans ((E R).toEquiv.subtypeEquiv (fun x => by
        change normAt hA b x = 1 ↔ (E R x).det = 1
        rw [norm])) with
      map_mul' := fun g h => Subtype.ext (by
        change E R (P.point _ (g * h)).val = E R (P.point _ g).val * E R (P.point _ h).val
        rw [P.mul, map_mul]) }
  let M : A ⋙ (groupPointsFunctor F).obj H.val ≅ specialLinearPoints K κ :=
    NatIso.ofComponents (fun R => (points R).toGrpIso) (by
      intro R U f
      apply GrpCat.ext
      intro g
      apply Subtype.ext
      change E U (P.point _ (mapPoints (A.map f) g)).val =
        (E R (P.point _ g).val).map f.hom
      rw [P.natural]
      change E U (changeCoefficients (A.map f).hom (P.point _ g).val) = _
      generalize (P.point (A.obj R) g).val = x
      induction x using TensorProduct.inductionOn with
      | tmul r a =>
        change E U ((A.map f).hom r ⊗ₜ[F] a) = (E R (r ⊗ₜ[F] a)).map f.hom
        simp only [E, AlgEquiv.trans_apply]
        rw [flattenSplitting_tmul (S := A.obj U), flattenSplitting_tmul (S := A.obj R)]
        ext p q
        change f.hom r * algebraMap K U (flattenSplitting s (1 ⊗ₜ[F] a) p.down q.down) =
          f.hom (r * algebraMap K R (flattenSplitting s (1 ⊗ₜ[F] a) p.down q.down))
        rw [map_mul, AlgHom.commutes]
      | add x y hx hy =>
        rw [map_add, map_add, map_add, hx, hy]
        ext p q
        exact (map_add f.hom _ _).symm)
  exact ⟨baseChangePointIso (K := K) H.val ≪≫ M, fun _ _ => rfl⟩

private theorem splitTransvectionProduct {F B K : Type u} [Field F] [DivisionRing B]
    [Algebra F B] [Field K] [Algebra F K] {m d : ℕ}
    (s : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K) (R : TestAlgebra K)
    {i j : Fin m} (hij : i ≠ j) (x : restrictTestAlgebraObj F K R ⊗[F] B) :
    let κ := ULift.{u} (Fin m × Fin d)
    ∃ l : List (Fin d × Fin d), l.Nodup ∧ l.toFinset = Finset.univ ∧
      Matrix.reindexAlgEquiv R R Equiv.ulift.symm
        (flattenSplitting (S := restrictTestAlgebraObj F K R) s (1 + blockEntry i j x)) =
        (l.map (fun p => Matrix.transvection (⟨i, p.1⟩ : κ)
          (⟨j, p.2⟩ : κ) (extendSplitting (R := restrictTestAlgebraObj F K R) s x p.1 p.2))).prod := by
  let R_F := restrictTestAlgebraObj F K R
  let X : Matrix (Fin d) (Fin d) R := extendSplitting (R := R_F) s x
  obtain ⟨l, hn, hset, hprod⟩ := flattened_block_product i j hij X Finset.univ
  have hblock : flattenSplitting (S := R_F) s (1 + blockEntry i j x) =
      (l.map (fun p => Matrix.transvection (i, p.1) (j, p.2) (X p.1 p.2))).prod := by
    rw [hprod, sum_flattened_block]
    simp only [flattenSplitting, map_add, map_one, AlgEquiv.trans_apply, matrixBaseChange_block,
      AlgEquiv.mapMatrix_apply, Matrix.map_single, Matrix.compAlgEquiv_apply, X]
    rfl
  refine ⟨l, hn, hset, ?_⟩
  let T (p : Fin d × Fin d) : Matrix.TransvectionStruct (Fin m × Fin d) R :=
    ⟨(i, p.1), (j, p.2), fun h => hij (congrArg Prod.fst h), X p.1 p.2⟩
  rw [hblock, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact (Matrix.TransvectionStruct.toMatrix_reindexEquiv Equiv.ulift.symm (T p)).symm

/-- The split special linear coordinates carry the full product-one diagonal. -/
private theorem splitModelWithDiagonal {K κ : Type u} [Field K] [Fintype κ] [DecidableEq κ]
    {N : ℕ} (hN : 0 < N) (e : κ ≃ Fin N) :
    ∃ (G : AffineAlgebraicGroup K) (M : (groupPointsFunctor K).obj G.val ≅ specialLinearPoints K κ)
      (T : ClosedSubgroup G.val) (t : ∀ R : TestAlgebra K, GroupPoints T.group R ≃* diagonalTuples N R),
      IsSplitTorus T.group ∧
      (∀ {R U : TestAlgebra K} (f : R ⟶ U) (x : GroupPoints T.group R) i,
        (t U (mapPoints f x)).val i = Units.map f.hom.toMonoidHom ((t R x).val i)) ∧
      ∀ (R : TestAlgebra K) (x : GroupPoints T.group R),
        (show Matrix.SpecialLinearGroup κ R from M.hom.app R (x ≫ T.inclusion.hom.hom)).val =
          Matrix.diagonal (fun p => ((t R x).val (e p) : R)) := by
  cases N with
  | zero => omega
  | succ n =>
    have hK : _root_.Specs.RM03.CSA.isCentralDivision K K := ⟨inferInstance, inferInstance⟩
    have hA := centralSimpleMatrix hN (RM03.CSA.isCentralSimple_of_isCentralDivision K K hK)
    let b := (Matrix.stdBasis K (Fin (n + 1)) (Fin (n + 1))).reindex
      (Equiv.ulift.symm : Fin (n + 1) × Fin (n + 1) ≃ ULift.{u} (Fin (n + 1) × Fin (n + 1)))
    obtain ⟨h, P, T, _, _, hT, ⟨D, _⟩, _⟩ := splitRank n hK hA b
    let G := @Specs.StandardGroups.spectrum K _ _ _ h.hopf inferInstance
    let E := reindexedSplitMatrixCoordinates (k := K) e
    have hnorm (R : TestAlgebra K) (x : R ⊗[K] Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
        _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b x = (E R x).det :=
      (normAt_eq_splitDet hA b x).trans (Matrix.det_reindexAlgEquiv R R e.symm _).symm
    let M (R : TestAlgebra K) : GroupPoints G.val R ≃* Matrix.SpecialLinearGroup κ R :=
      { (P.point R).trans ((E R).toEquiv.subtypeEquiv (fun x => by rw [hnorm R]; rfl)) with
        map_mul' := fun x y => Subtype.ext (by
          change E R (P.point R (x * y)).val = E R (P.point R x).val * E R (P.point R y).val
          rw [P.mul, map_mul]) }
    let ψ : (groupPointsFunctor K).obj G.val ≅ specialLinearPoints K κ :=
      NatIso.ofComponents (fun R => (M R).toGrpIso) (by
        intro R U f
        apply GrpCat.ext
        intro x
        apply Subtype.ext
        change E U (P.point U (mapPoints f x)).val = (E R (P.point R x).val).map f.hom
        rw [P.natural]
        exact reindexedSplitMatrixCoordinates_natural e f _)
    refine ⟨G, ψ, T, D.tuple, hT.1, @D.natural, ?_⟩
    intro R x
    change E R (P.point R (x ≫ T.inclusion.hom.hom)).val = _
    rw [D.diagonal]
    exact reindexedSplitMatrixCoordinates_diagonal e R _

private theorem groupIsoOfPointIso {K : Type u} [Field K] (G H : AffineAlgebraicGroup K)
    (e : (groupPointsFunctor K).obj G.val ≅ (groupPointsFunctor K).obj H.val) :
    ∃ f : G.val ≅ H.val, (groupPointsFunctor K).map f.hom = e.hom := by
  obtain ⟨f, hf⟩ := (groupHomComparison K G.val H.val G.property.1).2 e.hom
  obtain ⟨g, hg⟩ := (groupHomComparison K H.val G.val H.property.1).2 e.inv
  change (groupPointsFunctor K).map f = e.hom at hf
  change (groupPointsFunctor K).map g = e.inv at hg
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (groupHomComparison K G.val G.val G.property.1).1
    change (groupPointsFunctor K).map (f ≫ g) = (groupPointsFunctor K).map (𝟙 G.val)
    rw [Functor.map_comp, hf, hg, e.hom_inv_id]
    exact ((groupPointsFunctor K).map_id G.val).symm
  · apply (groupHomComparison K H.val H.val H.property.1).1
    change (groupPointsFunctor K).map (g ≫ f) = (groupPointsFunctor K).map (𝟙 H.val)
    rw [Functor.map_comp, hf, hg, e.inv_hom_id]
    exact ((groupPointsFunctor K).map_id H.val).symm

private def repeatDiagonalTuple {R : Type u} [CommRing R] {m d : ℕ}
    (e : ULift.{u} (Fin m × Fin d) ≃ Fin (m * d)) :
    diagonalTuples m R →* diagonalTuples (m * d) R where
  toFun t := ⟨fun j => t.val (e.symm j).down.1, by
    have ht : (∏ i, t.val i) = 1 := t.prop
    change (∏ j, t.val (e.symm j).down.1) = 1
    calc
      _ = ∏ p : Fin m × Fin d, t.val p.1 := Fintype.prod_equiv (e.symm.trans Equiv.ulift) _ _ (fun _ => rfl)
      _ = ∏ i : Fin m, ∏ _j : Fin d, t.val i := Fintype.prod_prod_type _
      _ = (∏ i, t.val i) ^ d := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
      _ = 1 := by rw [ht, one_pow]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

set_option maxHeartbeats 800000 in
theorem splitAbsoluteBlocks : SplitAbsoluteBlocks.{u} := by
  classical
  intro F B _ _ _ m hm hB hA ι _ b H P S D K _ _ d e
  let κ := ULift.{u} (Fin m × Fin d)
  let G := Specs.Unipotent.baseChangedAlgebraicGroup K H
  let Q := (groupBaseChange F K).obj S.group
  let j₀ := (groupBaseChange F K).map S.inclusion
  let E : κ ≃ Fin (m * d) := Equiv.ulift.trans finProdFinEquiv
  have hsimple := RM03.CSA.isCentralSimple_of_isCentralDivision F B hB
  have hd : 0 < d := (degree_eq_matrix_size hsimple e) ▸ RM03.CSA.degree_pos hsimple
  let : Nonempty κ := ⟨⟨⟨⟨0, hm⟩, ⟨0, hd⟩⟩⟩⟩
  obtain ⟨M, hM⟩ := splitBlockPointCoordinates e H P
  have hMdiag (R : TestAlgebra K) (x : GroupPoints Q R) :
      (show Matrix.SpecialLinearGroup κ R from M.hom.app R (x ≫ j₀.hom.hom)).val =
        Matrix.diagonal (fun p => ((D.tuple (restrictTestAlgebraObj F K R)
          (baseChangePoint F K S.group.X R x)).val p.down.1 : R)) := by
    let R_F := restrictTestAlgebraObj F K R
    let z : GroupPoints S.group R_F := baseChangePoint F K S.group.X R x
    let A : R_F ⊗[F] Matrix (Fin m) (Fin m) B ≃ₐ[R] Matrix κ κ R :=
      (flattenSplitting (S := R_F) e).trans (Matrix.reindexAlgEquiv R R Equiv.ulift.symm)
    have hnat : baseChangePoint F K H.val.X R (x ≫ j₀.hom.hom) =
        z ≫ S.inclusion.hom.hom :=
      baseChangePointsSchemeNaturality F K S.inclusion.hom.hom R x
    calc
      _ = A (P.point R_F (baseChangePoint F K H.val.X R (x ≫ j₀.hom.hom))).val :=
        hM R (x ≫ j₀.hom.hom)
      _ = A (P.point R_F (z ≫ S.inclusion.hom.hom)).val :=
        congrArg (fun g : GroupPoints H.val R_F => A (P.point R_F g).val) hnat
      _ = A (scalarDiagonal fun p => ((D.tuple R_F z).val p : R_F)) :=
        congrArg A (D.diagonal R_F z)
      _ = _ := by
        simp only [A, AlgEquiv.trans_apply, flattenSplitting_diagonal]
        ext p q
        change Matrix.diagonal (fun p : Fin m × Fin d => ((D.tuple R_F z).val p.1 : R)) p.down q.down =
          Matrix.diagonal (fun p : κ => ((D.tuple R_F z).val p.down.1 : R)) p q
        simp [Matrix.diagonal, ULift.down_injective.eq_iff]
  obtain ⟨L, M', T', t, hT, ht, hΔ⟩ := splitModelWithDiagonal (K := K) (Nat.mul_pos hm hd) E
  obtain ⟨u, hu⟩ := groupIsoOfPointIso G L (M ≪≫ M'.symm)
  let T : ClosedSubgroup G.val := ⟨T'.group, T'.inclusion ≫ u.inv, by
    let V := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
    let : IsIso u.inv.hom.hom.left := V.map_isIso u.inv
    let : IsClosedImmersion T'.inclusion.hom.hom.left := T'.isClosedImmersion
    exact IsClosedImmersion.comp T'.inclusion.hom.hom.left u.inv.hom.hom.left⟩
  have hTu : T.inclusion ≫ u.hom = T'.inclusion := by simp [T]
  have huM : (groupPointsFunctor K).map u.hom ≫ M'.hom = M.hom := by
    rw [hu]
    change (M.hom ≫ M'.inv) ≫ M'.hom = M.hom
    simp
  have hΔ' (R : TestAlgebra K) (x : GroupPoints T.group R) :
      (show Matrix.SpecialLinearGroup κ R from M.hom.app R (x ≫ T.inclusion.hom.hom)).val =
        Matrix.diagonal (fun p => ((t R x).val (E p) : R)) := by
    have hx := congrArg (fun p => p.app R (x ≫ T.inclusion.hom.hom)) huM
    change M'.hom.app R ((x ≫ T.inclusion.hom.hom) ≫ u.hom.hom.hom) =
      M.hom.app R (x ≫ T.inclusion.hom.hom) at hx
    have hx' : ((x ≫ T.inclusion.hom.hom) ≫ u.hom.hom.hom) = x ≫ T'.inclusion.hom.hom :=
      (Category.assoc (show Points T.group.X R from x) T.inclusion.hom.hom u.hom.hom.hom).trans
        (congrArg ((show Points T.group.X R from x) ≫ ·) (congrArg (fun p => p.hom.hom) hTu))
    calc
      _ = (show Matrix.SpecialLinearGroup κ R from M'.hom.app R ((x ≫ T.inclusion.hom.hom) ≫ u.hom.hom.hom)).val :=
        congrArg (fun y : Matrix.SpecialLinearGroup κ R => y.val) hx.symm
      _ = (show Matrix.SpecialLinearGroup κ R from M'.hom.app R (x ≫ T'.inclusion.hom.hom)).val :=
        congrArg (fun y : GroupPoints L.val R =>
          (show Matrix.SpecialLinearGroup κ R from M'.hom.app R y).val) hx'
      _ = _ := hΔ R x
  let bci := baseChangePointIso (K := K) S.group
  let z (R : TestAlgebra K) : GroupPoints Q R ≃* diagonalTuples m R :=
    (bci.app R).groupIsoToMulEquiv.trans (D.tuple (restrictTestAlgebraObj F K R))
  have hzn {R U : TestAlgebra K} (f : R ⟶ U) (x : GroupPoints Q R) (i : Fin m) :
      (z U (mapPoints f x)).val i = Units.map f.hom.toMonoidHom ((z R x).val i) := by
    have h := bci.hom.naturality_apply f x
    change baseChangePoint F K S.group.X U (mapPoints f x) =
      mapPoints ((restrictTestAlgebra F K).map f) (baseChangePoint F K S.group.X R x) at h
    change (D.tuple (restrictTestAlgebraObj F K U)
      (baseChangePoint F K S.group.X U (mapPoints f x))).val i =
      Units.map f.hom.toMonoidHom
        ((D.tuple (restrictTestAlgebraObj F K R) (baseChangePoint F K S.group.X R x)).val i)
    exact (congrArg (fun y : GroupPoints S.group (restrictTestAlgebraObj F K U) =>
      (D.tuple _ y).val i) h).trans (D.natural ((restrictTestAlgebra F K).map f) _ i)
  let φ (R : TestAlgebra K) : ((groupPointsFunctor K).obj Q).obj R →*
      ((groupPointsFunctor K).obj T.group).obj R :=
    (t R).symm.toMonoidHom.comp ((repeatDiagonalTuple E).comp (z R).toMonoidHom)
  let θ : (groupPointsFunctor K).obj Q ⟶ (groupPointsFunctor K).obj T.group :=
    { app := fun R => ConcreteCategory.ofHom (C := GrpCat) (φ R)
      naturality := by
        intro R U f
        apply GrpCat.ext
        intro x
        change (t U).symm (repeatDiagonalTuple E (z U (mapPoints f x))) =
          mapPoints f ((t R).symm (repeatDiagonalTuple E (z R x)))
        apply (t U).injective
        rw [MulEquiv.apply_symm_apply]
        apply Subtype.ext
        funext i
        rw [ht, MulEquiv.apply_symm_apply]
        exact hzn f x (E.symm i).down.1 }
  have hQ : IsAffine Q.X.left := affine_baseChange S.group.X
    (Specs.Unipotent.closedSubgroupAlgebraicGroup S).property.1
  obtain ⟨j, hj⟩ := (groupHomComparison K Q T.group hQ).2 θ
  change (groupPointsFunctor K).map j = θ at hj
  have hjt (R : TestAlgebra K) (x : GroupPoints Q R) :
      t R (x ≫ j.hom.hom) = repeatDiagonalTuple E (z R x) := by
    have h := congrArg (fun p => p.app R x) hj
    change x ≫ j.hom.hom = (t R).symm (repeatDiagonalTuple E (z R x)) at h
    exact (congrArg (t R) h).trans ((t R).apply_symm_apply _)
  have hcomp : j ≫ T.inclusion = j₀ := by
    apply (groupHomComparison K Q G.val hQ).1
    change (groupPointsFunctor K).map (j ≫ T.inclusion) = (groupPointsFunctor K).map j₀
    rw [Functor.map_comp]
    ext R x
    change (x ≫ j.hom.hom) ≫ T.inclusion.hom.hom = x ≫ j₀.hom.hom
    apply (M.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    change (show Matrix.SpecialLinearGroup κ R from M.hom.app R ((x ≫ j.hom.hom) ≫ T.inclusion.hom.hom)).val =
      (show Matrix.SpecialLinearGroup κ R from M.hom.app R (x ≫ j₀.hom.hom)).val
    calc
      _ = Matrix.diagonal (fun p => ((t R (x ≫ j.hom.hom)).val (E p) : R)) :=
        hΔ' R (x ≫ j.hom.hom)
      _ = Matrix.diagonal (fun p => ((z R x).val p.down.1 : R)) := by
        refine congrArg Matrix.diagonal (funext fun p => ?_)
        refine (congrArg (fun a : diagonalTuples (m * d) R => (a.val (E p) : R)) (hjt R x)).trans ?_
        change ((z R x).val (E.symm (E p)).down.1 : R) = ((z R x).val p.down.1 : R)
        rw [E.symm_apply_apply]
      _ = _ := (hMdiag R x).symm
  obtain ⟨β, hβ, hroots⟩ := InnerTypeARelativeContraction.splitAbsoluteRootCalculation E G M T t hT ht hΔ'
  refine ⟨M, T, j, t, E, β, hT, hcomp, hΔ', hβ, hroots, ?_, ?_, ?_, ?_⟩
  · intro p q R x
    change characterValue (j ≫ β p q) R x =
      (((z R x).val p.down.1 / (z R x).val q.down.1 : Rˣ) : R)
    have hvalue : characterValue (j ≫ β p q) R x = characterValue (β p q) R (x ≫ j.hom.hom) := by
      exact characterValue_comp j (β p q) R x
    calc
      _ = _ := hvalue
      _ = (((t R (x ≫ j.hom.hom)).val (E p) / (t R (x ≫ j.hom.hom)).val (E q) : Rˣ) : R) :=
        hβ p q R (x ≫ j.hom.hom)
      _ = _ := by
        refine (congrArg (fun a : diagonalTuples (m * d) R => ((a.val (E p) / a.val (E q) : Rˣ) : R))
          (hjt R x)).trans ?_
        change (((z R x).val (E.symm (E p)).down.1 / (z R x).val (E.symm (E q)).down.1 : Rˣ) : R) =
          (((z R x).val p.down.1 / (z R x).val q.down.1 : Rˣ) : R)
        rw [E.symm_apply_apply, E.symm_apply_apply]
  · intro R x
    exact (z R).surjective x
  · intro R
    let R_F := restrictTestAlgebraObj F K R
    refine ⟨extendSplitting (R := R_F) e, extendSplitting_tmul e, ?_⟩
    intro i j hij x
    obtain ⟨l, hn, ht, hprod⟩ := splitTransvectionProduct e R hij x
    refine ⟨l, hn, ht, fun g => ?_⟩
    rw [hM R g, ← hprod]
    exact (((flattenSplitting (S := R_F) e).trans
      (Matrix.reindexAlgEquiv R R Equiv.ulift.symm)).injective.eq_iff).symm
  · intro p q hpq
    exact InnerTypeARelativeContraction.splitAbsoluteRootRestrictions K p.down q.down
      (fun h => hpq (ULift.ext h))

theorem splitRankAndRoots : SplitRankAndRoots.{u} := by
  intro F B _ _ _ n hB
  have hA := centralSimpleMatrix (Nat.succ_pos n) (RM03.CSA.isCentralSimple_of_isCentralDivision F B hB)
  refine ⟨hA, ?_⟩
  intro ι _ b
  obtain ⟨h, P, S, heval, hs, hmax, ⟨D, hrel⟩, hbound⟩ := splitRank n hB hA b
  exact ⟨h, P, S, D, heval, hs, hmax, hrel, splitAbsoluteBlocks (Nat.succ_pos n) hB hA b _ P S D, hbound⟩

end

end LinearAlgebraicGroups.Arithmetic.InnerTypeASplitRank
