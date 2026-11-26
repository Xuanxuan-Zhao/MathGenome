import Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
import LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
import Batteries.Tactic.OpenPrivate
import LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.NoncommRing
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm

namespace LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors

open LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
open _root_.Specs.RM03.CSA (degree isCentralSimple isCentralDivision reducedNorm)
open scoped Matrix TensorProduct BigOperators
open MulOpposite

universe u v

open private transportSecondKind adj_mul adj_add adj_adj adj_scalar adj_smul
  exists_conjugation_ne exists_conjugate_eq_mul divisionFactorInvolution
  conjugation_involutive from LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras

section Model

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

private def matrixAdjoint (σ : SecondKind K E D) :
    Mat r D ≃ₐ[K] (Mat r D)ᵐᵒᵖ :=
  σ.adjoint.mapMatrix.trans AlgEquiv.mopMatrix

private theorem matrixAdjoint_apply (σ : SecondKind K E D) (X : Mat r D) :
    (matrixAdjoint σ X).unop = dagger σ X := rfl

private theorem dagger_mul (σ : SecondKind K E D) (X Y : Mat r D) :
    dagger σ (X * Y) = dagger σ Y * dagger σ X :=
  congrArg unop (map_mul (matrixAdjoint σ) X Y)

private theorem dagger_dagger (σ : SecondKind K E D) (X : Mat r D) :
    dagger σ (dagger σ X) = X := by
  ext i j
  exact adj_adj σ (X i j)

private theorem dagger_scalar (σ : SecondKind K E D) (c : E) :
    dagger (r := r) σ (algebraMap E (Mat r D) c) =
      algebraMap E (Mat r D) (σ.conjugation c) := by
  ext i j
  by_cases h : j = i
  · subst j
    simp [dagger, Matrix.algebraMap_matrix_apply, adj_scalar]
  · simp [dagger, Matrix.algebraMap_matrix_apply, h, Ne.symm h]

private theorem dagger_smul (σ : SecondKind K E D) (c : E) (X : Mat r D) :
    dagger σ (c • X) = σ.conjugation c • dagger σ X := by
  rw [Algebra.smul_def, dagger_mul, dagger_scalar, ← Algebra.commutes, ← Algebra.smul_def]

private def daggerUnit (σ : SecondKind K E D) (H : (Mat r D)ˣ) : (Mat r D)ˣ where
  val := dagger σ H.val
  inv := dagger σ (H⁻¹).val
  val_inv := by rw [← dagger_mul]; simp [← matrixAdjoint_apply]
  inv_val := by rw [← dagger_mul]; simp [← matrixAdjoint_apply]

private theorem hermitianMatrixExists (hr : 0 < r) (hD : isCentralDivision E D)
    (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (hσ : σ.conjugation = s.conjugation) :
    ∃ H, HermitianMatrix s e σ H := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  letI : Algebra.IsCentral E D := hD.1
  letI : FiniteDimensional E D := hD.2
  have hM : RM03.CSA.IsCentralSimple E (Mat r D) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  let S := transportSecondKind s e
  have hS : ∀ x, adj S x = e (adj s (e.symm x)) := fun _ => rfl
  have hconj : Function.Involutive s.conjugation :=
    conjugation_involutive s e.toEquiv.nontrivial
  let β₀ : Mat r D ≃+* Mat r D :=
    (matrixAdjoint σ).toRingEquiv.trans S.adjoint.toRingEquiv.symm
  have hβ (X) : β₀ X = e (adj s (e.symm (dagger σ X))) := by
    change S.adjoint.symm (op (dagger σ X)) = _
    apply S.adjoint.injective
    rw [AlgEquiv.apply_symm_apply, ← hS, ← op_unop (S.adjoint _)]
    exact (congrArg op (S.adjoint_adjoint _)).symm
  let β : Mat r D ≃ₐ[E] Mat r D := AlgEquiv.ofRingEquiv (f := β₀) (by
    intro c
    rw [hβ, dagger_scalar, hσ, e.symm.commutes]
    exact (congrArg e (s.adjoint_centre (s.conjugation c))).trans (by rw [hconj, e.commutes]))
  obtain ⟨g, hg⟩ := RM03.CSA.algEquiv_isInner hM β
  let H := g⁻¹
  have hstar (x : A) : e (adj s x) =
      (H⁻¹).val * dagger σ (e x) * H.val := by
    have h := hg (dagger σ (e x))
    change β₀ (dagger σ (e x)) = _ at h
    simpa [hβ, H, dagger_dagger] using h
  let J := H⁻¹ * daggerUnit σ H
  have hJ (X : Mat r D) : J.val * X * (J⁻¹).val = X := by
    obtain ⟨x, rfl⟩ := e.surjective X
    have h := hstar (adj s x)
    rw [show adj s (adj s x) = x from s.adjoint_adjoint x, hstar x, dagger_mul, dagger_mul, dagger_dagger] at h
    simpa [J, daggerUnit, mul_assoc] using h.symm
  have hcomm (X : Mat r D) : X * J.val = J.val * X := by
    simpa [mul_assoc] using congrArg (fun Y : Mat r D => Y * J.val) (hJ X).symm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff E (D := Mat r D)).mp
    (Subalgebra.mem_center_iff.mpr hcomm)
  have hH : dagger σ H.val = c • H.val := by
    calc
      dagger σ H.val = H.val * J.val := by simp [J, daggerUnit, ← mul_assoc]
      _ = c • H.val := by rw [hc, ← Algebra.commutes, ← Algebra.smul_def]
  have hnorm : c * s.conjugation c = 1 := by
    have he := dagger_dagger σ H.val
    rw [hH, dagger_smul, hH, hσ, smul_smul, mul_comm (s.conjugation c)] at he
    apply (algebraMap E (Mat r D)).injective
    have he' : algebraMap E (Mat r D) (c * s.conjugation c) * H.val = H.val := by
      rw [← Algebra.smul_def, he]
    simpa [mul_assoc] using congrArg (fun X : Mat r D => X * (H⁻¹).val) he'
  obtain ⟨a, ha, hscale⟩ := exists_conjugate_eq_mul s hconj c hnorm
  let d : Eˣ := Units.mk0 a ha
  let B : (Mat r D)ˣ := Units.map (algebraMap E (Mat r D)).toMonoidHom d⁻¹ * H
  refine ⟨B, hσ, ?_, fun x => (hstar x).trans ?_⟩
  · change dagger σ (algebraMap E (Mat r D) a⁻¹ * H.val) = _
    rw [← Algebra.smul_def, dagger_smul, hH, smul_smul, hσ, map_inv₀]
    change ((s.conjugation a)⁻¹ * c) • H.val = algebraMap E (Mat r D) a⁻¹ * H.val
    rw [← Algebra.smul_def, hscale, mul_inv_rev, mul_assoc,
      inv_mul_cancel₀ (show c ≠ 0 from left_ne_zero_of_mul_eq_one hnorm), mul_one]
  · change (H⁻¹).val * dagger σ (e x) * H.val =
      ((H⁻¹).val * algebraMap E (Mat r D) a) * dagger σ (e x) *
        (algebraMap E (Mat r D) a⁻¹ * H.val)
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc (algebraMap E (Mat r D) a), Algebra.commutes a (dagger σ (e x)),
      mul_assoc (dagger σ (e x)), ← mul_assoc (algebraMap E (Mat r D) a),
      ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

private def divisionStar (σ : SecondKind K E D) : StarRing D where
  star := adj σ
  star_involutive := adj_adj σ
  star_mul := adj_mul σ
  star_add := adj_add σ

private theorem matrixForm (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (H : (Mat r D)ˣ) (hH : HermitianMatrix s e σ H) :
    IsHermitianForm s e σ (form σ H.val) := by
  classical
  letI : StarRing D := divisionStar σ
  have hHerm : H.val.IsHermitian := hH.2.1
  have hright (y : Fin r → D) (d : D) : rightMul y d = MulOpposite.op d • y := rfl
  change (∀ x y z, form σ H.val x (y + z) = _) ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    simp [form, Matrix.mulVec_add, dotProduct_add]
  · intro x y d
    simp only [form, hright, Matrix.mulVec_smul, dotProduct_smul]
    rfl
  · intro x y
    change star (star x ⬝ᵥ (H.val *ᵥ y)) = star y ⬝ᵥ (H.val *ᵥ x)
    exact hHerm.star_dotProduct_mulVec_comm x y
  · intro y hy
    have hzero : H.val *ᵥ y = 0 := by
      ext i
      have hi := hy (Pi.single i 1)
      have heq : (fun j => adj σ ((Pi.single i (1 : D) : Fin r → D) j)) = Pi.single i 1 := by
        funext j
        by_cases h : j = i <;> simp [adj, Pi.single_apply, h]
      simpa [form, heq, single_dotProduct] using hi
    have hh := congrArg (fun z => (H⁻¹).val *ᵥ z) hzero
    simpa [Matrix.mulVec_mulVec] using hh
  · intro a x y
    change star (e a *ᵥ x) ⬝ᵥ (H.val *ᵥ y) =
      star x ⬝ᵥ (H.val *ᵥ (e (adj s a) *ᵥ y))
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hH.2.2]
    change star x ⬝ᵥ ((dagger σ (e a) * H.val) *ᵥ y) = _
    simp [← mul_assoc]

private theorem sameConjugation [Algebra.IsSeparable K E]
    (hKE : Module.finrank K E = 2) (a b : E ≃ₐ[K] E) (ha : a ≠ 1) (hb : b ≠ 1) :
    a = b := by
  classical
  let : Algebra.IsQuadraticExtension K E := ⟨hKE⟩
  letI : Fintype (E ≃ₐ[K] E) := Fintype.ofFinite _
  have hc : Fintype.card (E ≃ₐ[K] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hKE]
  by_contra hab
  have h := Finset.card_le_univ ({a, b, 1} : Finset (E ≃ₐ[K] E))
  simp [Finset.card_insert_of_notMem, hab, ha, hb, hc] at h

end Model

theorem hermitianPresentation : HermitianPresentation.{u} := by
  intro K E A _ _ _ _ _ _ _ _ hKE hA s
  obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation E A hA
  let : Algebra K D := Algebra.compHom D (algebraMap K E)
  let : IsScalarTower K E D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨σ⟩ := divisionFactorInvolution r hr (transportSecondKind s e)
  have hs := sameConjugation hKE σ.conjugation s.conjugation
    σ.conjugation_ne s.conjugation_ne
  obtain ⟨H, hH⟩ := hermitianMatrixExists hr hD s e σ hs
  exact ⟨r, D, inferInstance, inferInstance, hD, hr, e, σ, H, hH, matrixForm s e σ H hH⟩


section Determinant

open private baseChangeMatrix from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting

variable {E L A D : Type u} [Field E] [Field L] [Algebra E L]
  [Ring A] [Algebra E A] [DivisionRing D] [Algebra E D] {r d : ℕ}

private theorem matrixBaseChange_tmul (a : L) (X : Mat r D) :
    baseChangeMatrix E L D (Fin r) (a ⊗ₜ[E] X) =
      X.map (fun x => a ⊗ₜ[E] x) := by
  ext i j
  rfl

private theorem detSplitColumnAction (e : A ≃ₐ[E] Mat r D)
    (f : L ⊗[E] D ≃ₐ[L] Mat d L) (a : A) :
    let X := (Matrix.compAlgEquiv (Fin r) (Fin d) L L)
      ((e a).map (fun x => f (1 ⊗ₜ[E] x)))
    LinearMap.det ((columnAction e a).baseChange L) = X.det ^ d := by
  classical
  let X := (Matrix.compAlgEquiv (Fin r) (Fin d) L L)
      ((e a).map (fun x => f (1 ⊗ₜ[E] x)))
  let C := Fin r × Fin d
  let p : (L ⊗[E] (Fin r → D)) ≃ₗ[L] (Fin r → L ⊗[E] D) :=
    TensorProduct.piRight E L L (fun _ : Fin r => D)
  let reorder : (Fin r → Mat d L) ≃ₗ[L] (Fin d → C → L) :=
    { toFun := fun x i j => x j.1 j.2 i
      invFun := fun x i j k => x k (i, j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q := (LinearEquiv.piCongrRight (fun _ : Fin r => f.toLinearEquiv)).trans reorder
  let h := p.trans q
  let T := LinearMap.pi (fun i : Fin d => X.mulVecLin ∘ₗ LinearMap.proj i)
  have hact :
      h.toLinearMap ∘ₗ (columnAction e a).baseChange L ∘ₗ h.symm.toLinearMap = T := by
    -- Compare the two actions on pure tensors before cancelling the equivalence.
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      funext i j
      change f (b ⊗ₜ[E] ((e a *ᵥ x) j.1)) j.2 i =
        ∑ k : C, f (1 ⊗ₜ[E] (e a j.1 k.1)) j.2 k.2 * f (b ⊗ₜ[E] x k.1) k.2 i
      rw [Fintype.sum_prod_type]
      simp only [Matrix.mulVec, dotProduct, TensorProduct.tmul_sum, map_sum, Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Matrix.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add x y hx hy => simp only [map_add, hx, hy]
  change LinearMap.det ((columnAction e a).baseChange L) = X.det ^ d
  rw [← LinearMap.det_conj _ h, hact, LinearMap.det_pi]
  simp [← Matrix.toLin'_apply', LinearMap.det_toLin']

theorem determinantComparison : DeterminantComparison.{u} := by
  intro E A D _ _ _ _ _ r hA hD e a
  classical
  let : FiniteDimensional E D := hD.2
  have hr : 0 < r := by
    let : IsSimpleRing A := hA.1
    by_contra! h
    have hz : r = 0 := Nat.le_zero.mp h
    subst r
    exact zero_ne_one (e.injective (by subsingleton))
  let L := AlgebraicClosure E
  let hD' : isCentralSimple E D := RM03.CSA.isCentralSimple_of_isCentralDivision E D hD
  obtain ⟨f⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hD'
  let fA := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e
    |>.trans (baseChangeMatrix E L D (Fin r))
    |>.trans f.mapMatrix
    |>.trans (Matrix.compAlgEquiv (Fin r) (Fin (degree E D)) L L)
  let η : (Fin r × Fin (degree E D)) ≃ Fin (degree E A) :=
    finProdFinEquiv.trans (finCongr (RM03.CSA.degree_matrix_division hA hD hr e).symm)
  let fA' := fA.trans (Matrix.reindexAlgEquiv L L η)
  apply (algebraMap E L).injective
  change _ = algebraMap E L (RM03.CSA.reducedNorm hA a ^ degree E D)
  rw [map_pow, RM03.CSA.reducedNorm_map hA a fA', ← LinearMap.det_baseChange,
    detSplitColumnAction e f]
  congr 1
  change _ = (Matrix.reindex η η (fA (1 ⊗ₜ[E] a))).det
  rw [Matrix.det_reindex_self]
  change _ = (Matrix.compAlgEquiv (Fin r) (Fin (degree E D)) L L
    (f.mapMatrix (baseChangeMatrix E L D (Fin r) (1 ⊗ₜ[E] e a)))).det
  rw [matrixBaseChange_tmul]
  rfl

end Determinant

section Tensors

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

private theorem rightMulGroundScalar (c : K) (x : Fin r → D) :
    rightMul x (algebraMap K D c) = c • x := by
  funext i
  exact ((Algebra.commutes c (x i)).symm.trans (Algebra.smul_def c (x i)).symm)

private def rightMulScalarLinear (x : Fin r → D) : D →ₗ[K] (Fin r → D) where
  toFun := rightMul x
  map_add' a b := by ext i; exact mul_add (x i) a b
  map_smul' c d := by ext i; exact mul_smul_comm c (x i) d

private theorem commuteAllRightMul {J : Type u} [Fintype J] (b : Module.Basis J K D)
    (g : (Fin r → D) →ₗ[K] (Fin r → D))
    (hg : ∀ j x, g (rightMul x (b j)) = rightMul (g x) (b j)) :
    ∀ x d, g (rightMul x d) = rightMul (g x) d := by
  intro x d
  have he : g.comp (rightMulScalarLinear x) = rightMulScalarLinear (g x) :=
    b.ext fun j => hg j x
  exact LinearMap.congr_fun he d

private theorem rightMulMatrix (e : A ≃ₐ[E] Mat r D)
    (g : (Fin r → D) →ₗ[K] (Fin r → D))
    (hg : ∀ x d, g (rightMul x d) = rightMul (g x) d) :
    ∃ a : A, ∀ x, g x = columnAction e a x := by
  let M : Mat r D := Matrix.of fun i j => g (Pi.single j (1 : D)) i
  refine ⟨e.symm M, fun x => ?_⟩
  change g x = e (e.symm M) *ᵥ x
  rw [e.apply_symm_apply]
  have hx : x = ∑ j, rightMul (Pi.single j (1 : D)) (x j) := by
    symm
    calc
      (∑ j, rightMul (Pi.single j (1 : D)) (x j)) = ∑ j, Pi.single j (x j) := by
        apply Finset.sum_congr rfl
        intro j _
        funext i
        by_cases h : i = j <;> simp [rightMul, h]
      _ = x := LinearMap.sum_single_apply (fun _ => D) x
  calc
    g x = g (∑ j, rightMul (Pi.single j (1 : D)) (x j)) := congrArg g hx
    _ = M *ᵥ x := by
      rw [map_sum]
      ext i
      simp [hg, rightMul, M, Matrix.mulVec, dotProduct]

private theorem columnActionFaithful (e : A ≃ₐ[E] Mat r D) :
    Function.Injective (columnAction e) := by
  intro a z h
  apply e.injective
  exact Matrix.mulVec_injective (congrArg (fun f : Module.End E (Fin r → D) => ⇑f) h)

theorem tensorStabilizer : TensorStabilizer (K := K) (E := E) (A := A)
    (D := D) (r := r) := by
  intro s e σ h hh I J _ _ _ b v g
  constructor
  · rintro ⟨hright, hform, hvol⟩
    have hg := commuteAllRightMul b g.toLinearMap hright
    have hginv (x : Fin r → D) (d : D) :
        g.symm (rightMul x d) = rightMul (g.symm x) d := by
      apply g.injective
      change g (g.symm (rightMul x d)) = g (rightMul (g.symm x) d)
      rw [g.apply_symm_apply]
      simpa only [LinearEquiv.coe_coe, g.apply_symm_apply] using (hg (g.symm x) d).symm
    obtain ⟨a, ha⟩ := rightMulMatrix e g.toLinearMap hg
    obtain ⟨z, hz⟩ := rightMulMatrix e g.symm.toLinearMap hginv
    have haz : a * z = 1 := by
      apply columnActionFaithful e
      rw [map_mul, map_one]
      apply LinearMap.ext
      intro x
      change columnAction e a (columnAction e z x) = x
      rw [← hz, ← ha]
      exact g.apply_symm_apply x
    have hza : z * a = 1 := by
      apply columnActionFaithful e
      rw [map_mul, map_one]
      apply LinearMap.ext
      intro x
      change columnAction e z (columnAction e a x) = x
      rw [← ha, ← hz]
      exact g.symm_apply_apply x
    refine ⟨⟨a, z, haz, hza⟩, ha, ?_, ?_⟩
    · apply columnActionFaithful e
      rw [map_one]
      apply LinearMap.ext
      intro y
      change columnAction e (adj s a * a) y = y
      have hzero (x) : h x (columnAction e (adj s a * a) y) = h x y := by
        have hadj := hh.2.2.2.2 a x (columnAction e a y)
        change h (columnAction e a x) (columnAction e a y) =
          h x (columnAction e (adj s a) (columnAction e a y)) at hadj
        rw [map_mul, Module.End.mul_apply, ← hadj, ← ha, ← ha]
        exact hform x y
      have hsub (x z w) : h x (z - w) = h x z - h x w := by
        have hz : rightMul z 0 = 0 := funext fun i => mul_zero (z i)
        have h0 : h x 0 = 0 := by simpa only [hz, mul_zero] using hh.2.1 x z 0
        let f : (Fin r → D) →+ D := ⟨⟨h x, h0⟩, hh.1 x⟩
        exact map_sub f z w
      exact sub_eq_zero.mp (hh.2.2.2.1 _ fun x => by rw [hsub, hzero, sub_self])
    · have hv := hvol v
      change v.det (g ∘ ⇑v) = v.det v at hv
      have hcomp : g ∘ ⇑v = columnAction e a ∘ ⇑v := funext fun i => ha (v i)
      rwa [hcomp, Module.Basis.det_comp, Module.Basis.det_self, mul_one] at hv
  · rintro ⟨a, ha, hunitary, hdet⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j x
      simp only [ha]
      funext i
      simp [columnAction, Matrix.mulVecBilin, Matrix.mulVec, dotProduct, rightMul,
        Finset.sum_mul, mul_assoc]
    · intro x y
      rw [ha x, ha y]
      have hadj := hh.2.2.2.2 a.val x (columnAction e a.val y)
      change h (columnAction e a.val x) (columnAction e a.val y) =
        h x (columnAction e (adj s a.val) (columnAction e a.val y)) at hadj
      rwa [← Module.End.mul_apply, ← map_mul, hunitary, map_one, Module.End.one_apply] at hadj
    · intro x
      have heq : g ∘ x = columnAction e a.val ∘ x := funext fun i => ha (x i)
      rw [heq, Module.Basis.det_comp, hdet, one_mul]

theorem groundFieldBilinearity : GroundFieldBilinearity (K := K) (E := E) (A := A)
    (D := D) (r := r) := by
  intro s e σ h hh
  have hd : ∀ c : K, adj σ (algebraMap K D c) = algebraMap K D c :=
    fun c => congrArg unop (σ.adjoint.commutes c)
  have hr (c : K) (x y) : h x (c • y) = c • h x y := by
    rw [← rightMulGroundScalar c y, hh.2.1, Algebra.smul_def, Algebra.commutes]
  let B (x) : (Fin r → D) →ₗ[K] D := ⟨⟨h x, hh.1 x⟩, fun c y => hr c x y⟩
  refine ⟨⟨⟨B, ?_⟩, ?_⟩, fun _ _ => rfl⟩
  · intro x y
    apply LinearMap.ext
    intro z
    change h (x + y) z = h x z + h y z
    rw [← hh.2.2.1 z (x + y), hh.1]
    exact (adj_add σ _ _).trans (congrArg₂ (· + ·) (hh.2.2.1 z x) (hh.2.2.1 z y))
  · intro c x
    apply LinearMap.ext
    intro y
    change h (c • x) y = c • h x y
    rw [← hh.2.2.1 y (c • x), ← rightMulGroundScalar c x, hh.2.1]
    calc
      adj σ (h y x * algebraMap K D c) = adj σ (algebraMap K D c) * adj σ (h y x) :=
        adj_mul σ _ _
      _ = c • h x y := by rw [hd, hh.2.2.1, Algebra.smul_def]

end Tensors

section Polynomials

variable {K V W I J : Type u} [CommRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype I]

theorem diagonalCoordinates : DiagonalCoordinates (K := K) (V := V) (W := W) (I := I)
    (J := J) := by
  intro b c h
  classical
  have hev (x : V) (j : J) :
      MvPolynomial.eval (fun i => b.repr x i) (diagonalPolynomial b c h j) =
        c.repr (h x x) j := by
    let v := ∑ i, b.repr x i • b i
    have hv : v = x := b.sum_repr x
    rw [← hv] at ⊢
    conv_lhs => rw [hv]
    change _ = c.repr (h (∑ i, b.repr x i • b i) (∑ i, b.repr x i • b i)) j
    simp only [diagonalPolynomial, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨?_, hev, ?_, ?_⟩
  · intro j
    unfold diagonalPolynomial
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
      MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
    exact (MvPolynomial.isHomogeneous_C_mul_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)
  · intro g hg x j
    rw [hev, hev, hg]
  · intro ha x hx
    by_contra! hn
    apply ha x hx
    apply c.repr.injective
    ext j
    simpa [hev] using hn j

end Polynomials

section Application

variable {K E A D : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D] {r : ℕ}

theorem tensorStabilizerNorm : TensorStabilizerNorm (K := K) (E := E) (A := A)
    (D := D) (r := r) := by
  intro hA hD s e σ h hh I J _ _ _ b v g hg
  obtain ⟨a, ha, hstar, hdet⟩ := (tensorStabilizer s e σ h hh b v g).mp hg
  rw [determinantComparison hA hD e] at hdet
  exact ⟨a, ha, hstar, hdet⟩

theorem groundFieldDeterminantOne : GroundFieldDeterminantOne (K := K) (E := E) (A := A)
    (D := D) (r := r) := by
  intro hA hD e a ha
  rw [LinearMap.det_restrictScalars, determinantComparison hA hD e, ha, one_pow, map_one]

private theorem centralTraceOne (σ : SecondKind K E D) :
    ∃ z : E, z + σ.conjugation z = 1 := by
  have hInv := conjugation_involutive σ (inferInstance : Nontrivial D)
  obtain ⟨w, hw⟩ : ∃ w : E, w + σ.conjugation w ≠ 0 := by
    by_cases h : (1 : E) + 1 = 0
    · obtain ⟨w, hw⟩ := exists_conjugation_ne σ
      refine ⟨w, ?_⟩
      intro hzero
      apply hw
      have hn : -(1 : E) = 1 := (eq_neg_of_add_eq_zero_left h).symm
      calc
        σ.conjugation w = -w := eq_neg_of_add_eq_zero_right hzero
        _ = w := by rw [← neg_one_mul, hn, one_mul]
    · exact ⟨1, by simpa only [map_one] using h⟩
  let t := w + σ.conjugation w
  have ht : σ.conjugation t = t := by rw [show t = w + σ.conjugation w from rfl, map_add, hInv, add_comm]
  refine ⟨w / t, ?_⟩
  rw [map_div₀, ht, ← add_div]
  exact div_self hw

private theorem hermitian_leftScalar (σ : SecondKind K E D)
    (h : (Fin r → D) → (Fin r → D) → D)
    (hR : ∀ x y d, h x (rightMul y d) = h x y * d)
    (hS : ∀ x y, adj σ (h x y) = h y x)
    (x y : Fin r → D) (d : D) :
    h (rightMul x d) y = adj σ d * h x y := by
  rw [← hS y (rightMul x d), hR]
  exact (adj_mul σ _ _).trans (congrArg (fun v => adj σ d * v) (hS y x))

theorem hyperbolicPartner : HyperbolicPartner (K := K) (E := E) (A := A) (D := D) (r := r) := by
  intro s e σ h hh x hx hxx
  obtain ⟨B, hB⟩ := groundFieldBilinearity s e σ h hh
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra! hy
    exact hx (hh.2.2.2.1 x fun z => by rw [← hh.2.2.1, hy z]; simp [adj])
  let f := rightMul y (h x y)⁻¹
  have hxf : h x f = 1 := (hh.2.1 x y _).trans (mul_inv_cancel₀ hy)
  have hfx : h f x = 1 := by rw [← hh.2.2.1, hxf]; simp [adj]
  obtain ⟨z, hz⟩ := centralTraceOne σ
  let c := algebraMap E D z * h f f
  have hc : c + adj σ c = h f f := by
    change algebraMap E D z * h f f + adj σ (algebraMap E D z * h f f) = _
    rw [show adj σ (algebraMap E D z * h f f) =
      adj σ (h f f) * adj σ (algebraMap E D z) from adj_mul σ _ _,
      hh.2.2.1, show adj σ (algebraMap E D z) = _ from σ.adjoint_centre z,
      ← Algebra.commutes, ← add_mul, ← map_add, hz, map_one, one_mul]
  let f' := f - rightMul x c
  have hrightSub (a b d : Fin r → D) : h a (b - d) = h a b - h a d := by
    simpa only [hB] using map_sub (B a) b d
  have hleftSub (a b d : Fin r → D) : h (a - b) d = h a d - h b d := by
    simpa only [LinearMap.sub_apply, hB] using
      congrArg (fun f : (Fin r → D) →ₗ[K] D => f d) (map_sub B a b)
  have hxf' : h x f' = 1 := by
    rw [show f' = f - rightMul x c from rfl, hrightSub, hh.2.1 x x c,
      hxx, zero_mul, sub_zero, hxf]
  refine ⟨f', hxf', ?_, ?_⟩
  · rw [← hh.2.2.1, hxf']
    simp [adj]
  · change h f' (f - rightMul x c) = 0
    rw [hrightSub, hh.2.1 f' x c]
    change h (f - rightMul x c) f - h f' x * c = 0
    rw [hleftSub, hermitian_leftScalar σ h hh.2.1 hh.2.2.1 x f c, hxf, mul_one]
    have hfx' : h f' x = 1 := by rw [← hh.2.2.1, hxf']; simp [adj]
    rw [hfx', one_mul, sub_sub, add_comm (adj σ c), hc, sub_self]


private theorem rightMul_assoc (x : Fin r → D) (a b : D) :
    rightMul (rightMul x a) b = rightMul x (a * b) :=
  funext fun i => mul_assoc (x i) a b

private theorem rightMul_one (x : Fin r → D) : rightMul x 1 = x :=
  funext fun i => mul_one (x i)

private theorem rightMul_zero (x : Fin r → D) : rightMul x 0 = 0 :=
  funext fun i => mul_zero (x i)

private theorem rightMul_add (x : Fin r → D) (a b : D) :
    rightMul x (a + b) = rightMul x a + rightMul x b :=
  funext fun i => mul_add (x i) a b

private theorem columnAction_apply (e : A ≃ₐ[E] Mat r D) (a : A) (x : Fin r → D) :
    columnAction e a x = e a *ᵥ x := rfl

private theorem columnAction_mul_apply (e : A ≃ₐ[E] Mat r D) (a b : A) (x : Fin r → D) :
    columnAction e (a * b) x = columnAction e a (columnAction e b x) := by
  rw [map_mul, Module.End.mul_apply]

private theorem columnAction_ext (e : A ≃ₐ[E] Mat r D) {a b : A}
    (h : ∀ x, columnAction e a x = columnAction e b x) : a = b :=
  columnActionFaithful e (LinearMap.ext h)

private theorem adjoint_ext (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D)
    (hh : IsHermitianForm s e σ h) {a b : A}
    (hab : ∀ x y, h (columnAction e a x) y = h x (columnAction e b y)) :
    adj s a = b := by
  obtain ⟨B, hB⟩ := groundFieldBilinearity s e σ h hh
  apply columnAction_ext e
  intro y
  apply sub_eq_zero.mp
  apply hh.2.2.2.1
  intro x
  rw [← hB, map_sub, hB, hB]
  exact sub_eq_zero.mpr ((hh.2.2.2.2 a x y).symm.trans (hab x y))

private noncomputable def rankOne (e : A ≃ₐ[E] Mat r D)
    (h : (Fin r → D) → (Fin r → D) → D) (v w : Fin r → D) : A :=
  e.symm (Matrix.of fun i j => v i * h w (Pi.single j (1 : D)))

private theorem rankOne_apply (e : A ≃ₐ[E] Mat r D)
    (h : (Fin r → D) → (Fin r → D) → D)
    (hR : ∀ x y d, h x (rightMul y d) = h x y * d)
    (B : (Fin r → D) →ₗ[K] (Fin r → D) →ₗ[K] D) (hB : ∀ x y, B x y = h x y)
    (v w z : Fin r → D) :
    columnAction e (rankOne e h v w) z = rightMul v (h w z) := by
  classical
  rw [columnAction_apply, rankOne, e.apply_symm_apply]
  have hz : (∑ j, rightMul (Pi.single j (1 : D)) (z j)) = z := by
    convert LinearMap.sum_single_apply (fun _ => D) z using 1
    apply Finset.sum_congr rfl
    intro j _
    funext i
    by_cases hij : i = j <;> simp [rightMul, hij]
  have he := congrArg (fun z => B w z) hz
  change B w (∑ j, rightMul (Pi.single j (1 : D)) (z j)) = B w z at he
  rw [map_sum] at he
  simp only [hB, hR] at he
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, rightMul, ← he, Finset.mul_sum, mul_assoc]

private theorem rankOne_adj (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D)
    (hh : IsHermitianForm s e σ h) (v w : Fin r → D) :
    adj s (rankOne e h v w) = rankOne e h w v := by
  obtain ⟨B, hB⟩ := groundFieldBilinearity s e σ h hh
  apply adjoint_ext s e σ h hh
  intro x y
  simp only [rankOne_apply e h hh.2.1 B hB, hh.2.1,
    hermitian_leftScalar σ h hh.2.1 hh.2.2.1, hh.2.2.1]

theorem hyperbolicIdempotents : HyperbolicIdempotents (K := K) (E := E) (A := A)
    (D := D) (r := r) := by
  intro s e σ h hh x hx hxx
  obtain ⟨y, hxy, hyx, hyy⟩ := hyperbolicPartner s e σ h hh x hx hxx
  obtain ⟨B, hB⟩ := groundFieldBilinearity s e σ h hh
  let p := rankOne e h x y
  let q := rankOne e h y x
  let a := rankOne e h x x
  let b := rankOne e h y y
  have hp : ∀ z, columnAction e p z = rightMul x (h y z) := rankOne_apply e h hh.2.1 B hB x y
  have hq : ∀ z, columnAction e q z = rightMul y (h x z) := rankOne_apply e h hh.2.1 B hB y x
  have ha : ∀ z, columnAction e a z = rightMul x (h x z) := rankOne_apply e h hh.2.1 B hB x x
  have hb : ∀ z, columnAction e b z = rightMul y (h y z) := rankOne_apply e h hh.2.1 B hB y y
  have hp₀ : p ≠ 0 := by
    intro hp₀
    apply hx
    have he := hp x
    rwa [hp₀, map_zero, LinearMap.zero_apply, hyx, rightMul_one, eq_comm] at he
  have hact (u v : A) (z : Fin r → D) :
      columnAction e (u * v) z = columnAction e u (columnAction e v z) := by
    rw [map_mul, Module.End.mul_apply]
  have hpp : p * p = p := columnAction_ext e fun z => by
    rw [hact, hp, hp, hh.2.1, hyx, one_mul]
  have hqq : q * q = q := columnAction_ext e fun z => by
    rw [hact, hq, hq, hh.2.1, hxy, one_mul]
  have hpq : p * q = 0 := columnAction_ext e fun z => by
    rw [hact, hq, hp, hh.2.1, hyy, zero_mul, rightMul_zero, map_zero, LinearMap.zero_apply]
  have hqp : q * p = 0 := columnAction_ext e fun z => by
    rw [hact, hp, hq, hh.2.1, hxx, zero_mul, rightMul_zero, map_zero, LinearMap.zero_apply]
  have hab : a * b = p := columnAction_ext e fun z => by
    rw [hact, hb, ha, hh.2.1, hxy, one_mul, hp]
  have hba : b * a = q := columnAction_ext e fun z => by
    rw [hact, ha, hb, hh.2.1, hyx, one_mul, hq]
  have haa : a * a = 0 := columnAction_ext e fun z => by
    rw [hact, ha, ha, hh.2.1, hxx, zero_mul, rightMul_zero, map_zero, LinearMap.zero_apply]
  have hbb : b * b = 0 := columnAction_ext e fun z => by
    rw [hact, hb, hb, hh.2.1, hyy, zero_mul, rightMul_zero, map_zero, LinearMap.zero_apply]
  have hpa : p * a = a := columnAction_ext e fun z => by
    rw [hact, ha, hp, hh.2.1, hyx, one_mul]
  have hqb : q * b = b := columnAction_ext e fun z => by
    rw [hact, hb, hq, hh.2.1, hxy, one_mul]
  have haq : a * q = a := by rw [← hba, ← mul_assoc, hab, hpa]
  have hbp : b * p = b := by rw [← hab, ← mul_assoc, hba, hqb]
  have hap : a * p = 0 := by rw [← hab, ← mul_assoc, haa, zero_mul]
  have hbq : b * q = 0 := by rw [← hba, ← mul_assoc, hbb, zero_mul]
  have hpb : p * b = 0 := by rw [← hab, mul_assoc, hbb, mul_zero]
  have hqa : q * a = 0 := by rw [← hba, mul_assoc, haa, mul_zero]
  let z := 1 - p - q
  have hzp : z * p = 0 := by
    simp [z, sub_mul, hpp, hqp]
  have hzq : z * q = 0 := by
    simp [z, sub_mul, hqq, hpq]
  have hzz : z * z = z := by
    change z * (1 - p - q) = z
    simp [mul_sub, hzp, hzq]
  have haz : a * z = 0 := by simp [z, mul_sub, hap, haq]
  have hbz : b * z = 0 := by simp [z, mul_sub, hbp, hbq]
  have hza : z * a = 0 := by simp [z, sub_mul, hpa, hqa]
  have hzb : z * b = 0 := by simp [z, sub_mul, hpb, hqb]
  let w := a + b + z
  have hww : w * w = 1 := by
    simp only [w, add_mul, mul_add, haa, hbb, hab, hba, haz, hbz, hza, hzb, hzz,
      zero_add, add_zero]
    dsimp [z]
    abel
  have hwpw : w * p * w = q := by
    have hwp : w * p = b := by simp [w, add_mul, hap, hbp, hzp]
    rw [hwp]
    simp [w, mul_add, hba, hbb, hbz]
  exact ⟨p, q, ⟨w, w, hww, hww⟩, hp₀, hpp, hqq, hpq, hqp, rankOne_adj s e σ h hh x y, hwpw⟩

private theorem nonzeroHermitianValue (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (σ : SecondKind K E D) (h : (Fin r → D) → (Fin r → D) → D)
    (hh : IsHermitianForm s e σ h) (hr : 0 < r) : ∃ x, h x x ≠ 0 := by
  obtain ⟨B, hB⟩ := groundFieldBilinearity s e σ h hh
  by_contra! hd
  have hp (x y) : h x y + h y x = 0 := by
    have h' : B (x + y) (x + y) = 0 := (hB _ _).trans (hd _)
    simpa only [map_add, LinearMap.add_apply, hB, hd, zero_add, add_zero, add_comm] using h'
  obtain ⟨z, hz⟩ := exists_conjugation_ne σ
  have hz' : algebraMap E D (z - σ.conjugation z) ≠ 0 := by
    exact (map_ne_zero (algebraMap E D)).mpr (sub_ne_zero.mpr hz.symm)
  have hzero (x y) : h x y = 0 := by
    have ht := hp x (rightMul y (algebraMap E D z))
    rw [hh.2.1, hermitian_leftScalar σ h hh.2.1 hh.2.2.1,
      show adj σ (algebraMap E D z) = _ from σ.adjoint_centre z,
      eq_neg_of_add_eq_zero_right (hp x y), mul_neg, ← sub_eq_add_neg,
      ← Algebra.commutes z (h x y), ← sub_mul, ← map_sub] at ht
    exact (mul_eq_zero.mp ht).resolve_left hz'
  let i : Fin r := ⟨0, hr⟩
  let x : Fin r → D := Pi.single i 1
  have hx : x = 0 := hh.2.2.2.1 x (fun y => hzero y x)
  exact (one_ne_zero : (1 : D) ≠ 0) (by simpa [x] using congrFun hx i)

private theorem adj_inv (σ : SecondKind K E D) (d : D) :
    adj σ d⁻¹ = (adj σ d)⁻¹ := by
  change (σ.adjoint d⁻¹).unop = (σ.adjoint d).unop⁻¹
  rw [map_inv₀]
  rfl

private noncomputable def twistAdjoint (σ : SecondKind K E D) {c : D} (hc : c ≠ 0)
    (hcstar : adj σ c = c) : SecondKind K E D := by
  let f (d : D) := c⁻¹ * adj σ d * c
  have hf (a b : D) : f (a * b) = f b * f a := by
    change c⁻¹ * adj σ (a * b) * c = (c⁻¹ * adj σ b * c) * (c⁻¹ * adj σ a * c)
    rw [show adj σ (a * b) = _ from adj_mul σ a b]
    simp [mul_assoc, ← mul_assoc c c⁻¹ _, mul_inv_cancel₀ hc]
  have hff (a : D) : f (f a) = a := by
    change c⁻¹ * adj σ (c⁻¹ * adj σ a * c) * c = a
    rw [show adj σ (c⁻¹ * adj σ a * c) =
      adj σ c * (adj σ (adj σ a) * adj σ c⁻¹) from by
        exact (adj_mul σ (c⁻¹ * adj σ a) c).trans (congrArg (adj σ c * ·) (adj_mul σ _ _)),
      show adj σ (adj σ a) = a from σ.adjoint_adjoint a, adj_inv, hcstar, ← mul_assoc, inv_mul_cancel₀ hc, one_mul,
      mul_assoc, inv_mul_cancel₀ hc, mul_one]
  let F : D →+* Dᵐᵒᵖ :=
    { toFun := fun x => op (f x)
      map_zero' := by simp [f, adj]
      map_one' := by simp [f, adj, hc]
      map_add' := fun x y => congrArg op (by
        change c⁻¹ * adj σ (x + y) * c = _
        rw [show adj σ (x + y) = _ from adj_add σ x y, mul_add, add_mul]
        rfl)
      map_mul' := fun x y => congrArg op (hf x y) }
  let g := RingEquiv.ofBijective F (opEquiv.bijective.comp (show Function.Involutive f from hff).bijective)
  refine SecondKind.ofRingEquiv σ.conjugation σ.conjugation_ne g hff fun z => ?_
  change c⁻¹ * adj σ (algebraMap E D z) * c = _
  rw [show adj σ (algebraMap E D z) = _ from σ.adjoint_centre z, ← Algebra.commutes,
    mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem selfAdjointCorner : SelfAdjointCorner (K := K) (E := E) (A := A) (D := D) (r := r) := by
  intro s e σ h hh hσ hr
  classical
  obtain ⟨x, hx⟩ := nonzeroHermitianValue s e σ h hh hr
  obtain ⟨B, hB⟩ := groundFieldBilinearity s e σ h hh
  have hx₀ : x ≠ 0 := by
    intro he
    apply hx
    rw [he, ← hB, map_zero]
  let c := h x x
  have hc : c ≠ 0 := hx
  have hcstar : adj σ c = c := hh.2.2.1 x x
  let τ := twistAdjoint σ hc hcstar
  let i : D →ₗ[E] A :=
    { toFun := fun d => rankOne e h (rightMul x (d * c⁻¹)) x
      map_add' := fun d z => by
        apply e.injective
        simp only [rankOne, AlgEquiv.apply_symm_apply, map_add]
        ext k j
        simp [rightMul, add_mul, mul_add]
      map_smul' := fun z d => by
        apply e.injective
        simp only [rankOne, AlgEquiv.apply_symm_apply, map_smul]
        ext k j
        simp [rightMul, smul_mul_assoc, mul_smul_comm] }
  let p := i 1
  have hia (d) (y) : columnAction e (i d) y = rightMul x (d * c⁻¹ * h x y) := by
    change columnAction e (rankOne e h (rightMul x (d * c⁻¹)) x) y = _
    rw [rankOne_apply e h hh.2.1 B hB, rightMul_assoc]
  have hix (d : D) : columnAction e (i d) x = rightMul x d := by
    rw [hia]
    change rightMul x (d * c⁻¹ * c) = _
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hii (d z : D) : i (d * z) = i d * i z := columnAction_ext e fun y => by
    rw [columnAction_mul_apply, hia d, hia z, hh.2.1, hia]
    change rightMul x (d * z * c⁻¹ * h x y) =
      rightMul x (d * c⁻¹ * (c * (z * c⁻¹ * h x y)))
    have hcancel : d * c⁻¹ * c = d := by rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [← mul_assoc (d * c⁻¹) c, hcancel]
    simp only [mul_assoc]
  have hinj : Function.Injective i := by
    intro a b hab
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra! he
      exact hx₀ (funext he)
    have h' := congrArg (fun z => columnAction e z x j) hab
    change columnAction e (i a) x j = columnAction e (i b) x j at h'
    rw [hix, hix] at h'
    exact mul_left_cancel₀ hj h'
  have histar (d : D) : adj s (i d) = i (adj τ d) := by
    apply adjoint_ext s e σ h hh
    intro y z
    rw [hia, hia, hermitian_leftScalar σ h hh.2.1 hh.2.2.1, hh.2.1]
    have hd : adj τ d = c⁻¹ * adj σ d * c := rfl
    rw [show adj σ (d * c⁻¹ * h x y) =
        adj σ (h x y) * (adj σ c⁻¹ * adj σ d) from by
          exact (adj_mul σ _ _).trans (congrArg (adj σ (h x y) * ·) (adj_mul σ _ _)),
      hh.2.2.1, adj_inv, hcstar, hd, mul_assoc (c⁻¹ * adj σ d) c c⁻¹,
      mul_inv_cancel₀ hc, mul_one]
    simp only [mul_assoc]
  have hpp : p * p = p := by
    change i 1 * i 1 = i 1
    rw [← hii, one_mul]
  have hpstar : adj s p = p := by
    change adj s (i 1) = i 1
    rw [histar]
    congr 1
    simp [adj]
  refine ⟨x, p, i, τ, hx₀, hpp, hpstar, ?_, rfl, hinj, hii, ?_, hσ, histar⟩
  · ext y
    exact ⟨fun ⟨z, hz⟩ => ⟨1 * c⁻¹ * h x z, (hia 1 z).symm.trans hz⟩,
      fun ⟨d, hd⟩ => ⟨rightMul x d, by rw [hia, hh.2.1]; change rightMul x (1 * c⁻¹ * (c * d)) = y
                                       rw [one_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, hd]⟩⟩
  · intro a
    constructor
    · intro ha
      refine ⟨c⁻¹ * h x (columnAction e a x), ?_⟩
      apply columnAction_ext e
      intro y
      conv_rhs => rw [← ha]
      change columnAction e (i (c⁻¹ * h x (columnAction e a x))) y =
        columnAction e (i 1 * a * i 1) y
      rw [columnAction_mul_apply, columnAction_mul_apply, hia (1 : D), hia (1 : D), one_mul]
      rw [hia]
      have hright : columnAction e a (rightMul x (c⁻¹ * h x y)) =
          rightMul (columnAction e a x) (c⁻¹ * h x y) := by
        funext j
        simp [columnAction_apply, Matrix.mulVec, dotProduct, rightMul, Finset.sum_mul, mul_assoc]
      rw [hright, hh.2.1]
      simp only [mul_assoc]
    · rintro ⟨d, rfl⟩
      change i 1 * i d * i 1 = i d
      rw [← hii, ← hii, one_mul, mul_one]

end Application

section Coefficients

variable {K E A D R : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [Ring D] [Algebra E D] [Algebra K D] [IsScalarTower K E D]
  [CommRing R] [Algebra K R] {r : ℕ}

theorem extendedColumnAction_tmul (e : A ≃ₐ[E] Mat r D)
    (c b : R) (a : A) (x : Fin r → D) :
    extendedColumnAction e (c ⊗ₜ[K] a) (b ⊗ₜ[K] x) =
      (c * b) ⊗ₜ[K] (columnAction e a x) := by
  rfl

theorem completionColumnAction : CompletionColumnAction.{u,v} (K := K) (E := E)
    (A := A) (D := D) (r := r) := by
  intro k w e
  letI : Algebra K (k.Completion w) := (k.embedding w).toAlgebra
  exact extendedColumnAction_tmul e

end Coefficients

section SplitTorus

open LinearAlgebraicGroups.UnitaryNormEquations
open private unitaryNormHom from LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations

variable {K E A R : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [CommRing R] [Algebra K R]

private def lineScale {B : Type u} [Ring B] [Algebra R B] (p : B) (hp : p * p = p) :
    R →* B where
  toFun t := t • p + (1 - p)
  map_one' := by simp
  map_mul' t z := by
    have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
    have h2 : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
    have h3 : (1 - p) * (1 - p) = 1 - p := by rw [mul_sub, mul_one, h2, sub_zero]
    rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, hp,
      smul_smul, smul_mul_assoc, h1, mul_smul_comm, h2, h3]
    simp

private theorem lineScale_commute {B : Type u} [Ring B] [Algebra R B]
    (p q : B) (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (hqp : q * p = 0) (a b : R) :
    Commute (lineScale p hp a) (lineScale q hq b) := by
  change (a • p + (1 - p)) * (b • q + (1 - q)) =
    (b • q + (1 - q)) * (a • p + (1 - p))
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hpq, hqp, smul_zero, zero_add]
  simp only [sub_mul, mul_sub, mul_one, one_mul, hpq, hqp, sub_zero]
  abel

private theorem lineScale_mulProj {B : Type u} [Ring B] [Algebra R B]
    (p q : B) (hp : p * p = p) (hq : q * q = q)
    (hqp : q * p = 0) (a b : R) :
    lineScale p hp a * lineScale q hq b * p = a • p := by
  change (a • p + (1 - p)) * (b • q + (1 - q)) * p = _
  have h : (b • q + (1 - q)) * p = p := by
    simp [add_mul, smul_mul_assoc, sub_mul, hqp]
  rw [mul_assoc, h]
  simp [add_mul, smul_mul_assoc, sub_mul, hp]

private def pairScale {B : Type u} [Ring B] [Algebra R B] (p q : B)
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) : Rˣ →* Bˣ where
  toFun t := Units.map (lineScale p hp) t * Units.map (lineScale q hq) t⁻¹
  map_one' := by simp
  map_mul' t z := by
    rw [show (t * z)⁻¹ = t⁻¹ * z⁻¹ by simp [mul_inv_rev, mul_comm], map_mul, map_mul]
    have h : Commute (Units.map (lineScale p hp) z) (Units.map (lineScale q hq) t⁻¹) :=
      Units.ext (lineScale_commute p q hp hq hpq hqp z.val t.inv).eq
    exact h.mul_mul_mul_comm _ _

private theorem pairScale_val {B : Type u} [Ring B] [Algebra R B] (p q : B)
    (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0)
    (t : Rˣ) :
    (pairScale p q hp hq hpq hqp t).val = t.val • p + t.inv • q + (1 - p - q) := by
  change (t.val • p + (1 - p)) * (t.inv • q + (1 - q)) = _
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hpq,
    smul_zero, one_mul, mul_one, sub_zero, zero_add]
  noncomm_ring

private theorem projectorFunctional (p q : A) (hp₀ : p ≠ 0)
    (hp : p * p = p) (hqp : q * p = 0) :
    ∃ l : A →ₗ[K] K, l p = 1 ∧ l q = 0 ∧ l (1 - p - q) = 0 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero K hp₀
  let m : A →ₗ[K] A :=
    { toFun := fun x => x * p
      map_add' := fun x y => add_mul x y p
      map_smul' := fun a x => smul_mul_assoc a x p }
  refine ⟨(l p)⁻¹ • (l.comp m), ?_, ?_, ?_⟩
  · change (l p)⁻¹ * l (p * p) = 1
    rw [hp, inv_mul_cancel₀ hl]
  · change (l p)⁻¹ * l (q * p) = 0
    rw [hqp, map_zero, mul_zero]
  · change (l p)⁻¹ * l ((1 - p - q) * p) = 0
    rw [sub_mul, sub_mul, one_mul, hp, hqp, sub_self, sub_zero, map_zero, mul_zero]

private theorem coefficientAt_tmul (l : A →ₗ[K] K) (t : R) (a : A) :
    coefficientAt l (t ⊗ₜ[K] a) = l a • t := rfl


private theorem adjointAt_lineScale (s : SecondKind K E A) (p : A) (t : R) :
    adjointAt s (t • ((1 : R) ⊗ₜ[K] p) + (1 - (1 ⊗ₜ[K] p))) =
    t • ((1 : R) ⊗ₜ[K] adj s p) + (1 - (1 ⊗ₜ[K] adj s p)) := by
  simp only [adjointAt, map_add, map_sub, map_one, MulOpposite.unop_add, MulOpposite.unop_sub,
    MulOpposite.unop_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

private theorem adjointAt_scaledProjector (s : SecondKind K E A) (p q : A)
    (hp : (1 : R) ⊗ₜ[K] p * (1 ⊗ₜ[K] p) = 1 ⊗ₜ[K] p)
    (hq : (1 : R) ⊗ₜ[K] q * (1 ⊗ₜ[K] q) = 1 ⊗ₜ[K] q)
    (hs : adj s p = q) (t : R) :
    adjointAt s (lineScale ((1 : R) ⊗ₜ[K] p) hp t) =
      lineScale ((1 : R) ⊗ₜ[K] q) hq t := by
  simpa only [lineScale, MonoidHom.coe_mk, OneHom.coe_mk, hs] using
    adjointAt_lineScale s p t


private theorem tmul_injective_of_ne_zero {a : A} (ha : a ≠ 0) :
    Function.Injective (fun t : R => t ⊗ₜ[K] a) := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K ha
  intro t z h
  apply_fun (TensorProduct.rid K R ∘ TensorProduct.map (LinearMap.id : R →ₗ[K] R) f) at h
  change f a • t = f a • z at h
  exact smul_right_injective R hf h

set_option maxHeartbeats 900000 in
theorem splitUnitaryTorusOfIdempotents : SplitUnitaryTorusOfIdempotents
    (K := K) (E := E) (A := A) := by
  intro I _ hA b s p q w hp₀ hp hq hpq hqp hstar hw
  let P (R : Type u) [CommRing R] [Algebra K R] : R ⊗[K] A := 1 ⊗ₜ[K] p
  let Q (R : Type u) [CommRing R] [Algebra K R] : R ⊗[K] A := 1 ⊗ₜ[K] q
  have hPP (R : Type u) [CommRing R] [Algebra K R] : P R * P R = P R := by
    simp [P, Algebra.TensorProduct.tmul_mul_tmul, hp]
  have hQQ (R : Type u) [CommRing R] [Algebra K R] : Q R * Q R = Q R := by
    simp [Q, Algebra.TensorProduct.tmul_mul_tmul, hq]
  have hPQ (R : Type u) [CommRing R] [Algebra K R] : P R * Q R = 0 := by
    simp [P, Q, Algebra.TensorProduct.tmul_mul_tmul, hpq]
  have hQP (R : Type u) [CommRing R] [Algebra K R] : Q R * P R = 0 := by
    simp [P, Q, Algebra.TensorProduct.tmul_mul_tmul, hqp]
  let T (R : Type u) [CommRing R] [Algebra K R] :=
    pairScale (R := R) (P R) (Q R) (hPP R) (hQQ R) (hPQ R) (hQP R)
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro R _ _ t z hz
    apply Units.ext
    have ht := congrArg (fun u : (R ⊗[K] A)ˣ => u.val * P R) hz
    change lineScale (P R) (hPP R) t.val * lineScale (Q R) (hQQ R) t.inv * P R =
      lineScale (P R) (hPP R) z.val * lineScale (Q R) (hQQ R) z.inv * P R at ht
    rw [lineScale_mulProj _ _ _ _ (hQP R), lineScale_mulProj _ _ _ _ (hQP R)] at ht
    apply tmul_injective_of_ne_zero (K := K) (R := R) hp₀
    simpa [P, TensorProduct.smul_tmul'] using ht
  · intro R _ _ t
    let U := unitaryNormHom (F := K) (R := R) hA b
    let lp : R →* (R ⊗[K] A) := lineScale (P R) (hPP R)
    let lq : R →* (R ⊗[K] A) := lineScale (Q R) (hQQ R)
    change adjointAt s (lp t.val * lq t.inv) * (lp t.val * lq t.inv) = 1 ∧
      U (lp t.val * lq t.inv) = 1
    have hpqadj (a : R) : adjointAt s (lp a) = lq a := by
      exact adjointAt_scaledProjector s p q (hPP R) (hQQ R) hstar a
    have hqpadj (a : R) : adjointAt s (lq a) = lp a := by
      exact (congrArg (adjointAt s) (hpqadj a).symm).trans (adjointAt_adj s (lp a))
    constructor
    · rw [adjointAt_mul, hpqadj t.val, hqpadj t.inv]
      have hcomm : Commute (lq t.val) (lp t.val) :=
        (lineScale_commute _ _ _ _ (hPQ R) (hQP R) _ _).symm
      have hp1 : lp t.inv * lp t.val = 1 := by rw [← map_mul, t.inv_val, map_one]
      have hq1 : lq t.val * lq t.inv = 1 := by rw [← map_mul, t.val_inv, map_one]
      calc
        (lp t.inv * lq t.val) * (lp t.val * lq t.inv) =
            (lp t.inv * lp t.val) * (lq t.val * lq t.inv) := hcomm.mul_mul_mul_comm _ _
        _ = 1 := by rw [hp1, hq1, mul_one]
    · let W : (R ⊗[K] A)ˣ :=
        Units.map (Algebra.TensorProduct.includeRight (R := K) (A := R) (B := A)).toMonoidHom w
      have hconj : W.val * P R * W.inv = Q R := by
        change ((1 : R) ⊗ₜ[K] w.val) * (1 ⊗ₜ[K] p) * (1 ⊗ₜ[K] w.inv) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, one_mul, hw]
      have hnorm (a : R) : U (lq a) = U (lp a) := by
        have hscale : W.val * lp a * W.inv = lq a := by
          change W.val * (a • P R + (1 - P R)) * W.inv = a • Q R + (1 - Q R)
          rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hconj, mul_sub, mul_one,
            sub_mul, hconj, W.val_inv]
        rw [← hscale, map_mul, map_mul, mul_right_comm, ← map_mul, W.val_inv, map_one, one_mul]
      rw [map_mul, hnorm, ← map_mul, ← map_mul, t.val_inv, map_one, map_one]
  · intro R S _ _ _ _ f t
    apply Units.ext
    change lineScale (P S) (hPP S) (f t.val) * lineScale (Q S) (hQQ S) (f t.inv) =
      Algebra.TensorProduct.map f (AlgHom.id K A)
        (lineScale (P R) (hPP R) t.val * lineScale (Q R) (hQQ R) t.inv)
    change ((f t.val) • P S + (1 - P S)) * ((f t.inv) • Q S + (1 - Q S)) =
      Algebra.TensorProduct.map f (AlgHom.id K A)
        ((t.val • P R + (1 - P R)) * (t.inv • Q R + (1 - Q R)))
    simp only [map_mul, map_add, map_sub, map_one, P, Q, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  · have hq₀ : q ≠ 0 := by
      intro h
      apply hp₀
      have he : (s.adjoint p).unop = (s.adjoint 0).unop := by
        rw [show (s.adjoint p).unop = q from hstar, h, map_zero, unop_zero]
      exact s.adjoint.injective (MulOpposite.unop_injective he)
    obtain ⟨l, hlp, hlq, hl⟩ := projectorFunctional (K := K) p q hp₀ hp hqp
    obtain ⟨m, hmq, hmp, hm⟩ := projectorFunctional (K := K) q p hq₀ hq hpq
    rw [sub_right_comm 1 q p] at hm
    have hval (R : Type u) [CommRing R] [Algebra K R] (t : Rˣ) : (T R t).val =
        t.val ⊗ₜ[K] p + t.inv ⊗ₜ[K] q + (1 : R) ⊗ₜ[K] (1 - p - q) := by
      change (pairScale (P R) (Q R) (hPP R) (hQQ R) (hPQ R) (hQP R) t).val = _
      rw [pairScale_val]
      change t.val • ((1 : R) ⊗ₜ[K] p) + t.inv • ((1 : R) ⊗ₜ[K] q) +
        (1 ⊗ₜ[K] (1 : A) - 1 ⊗ₜ[K] p - 1 ⊗ₜ[K] q) = _
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_sub]
    have hcoords (R : Type u) [CommRing R] [Algebra K R] (t : Rˣ) :
        coefficientAt l (T R t).val = t.val ∧ coefficientAt m (T R t).val = t.inv := by
      rw [hval]
      simp only [map_add, coefficientAt_tmul, hlp, hlq, hl, hmp, hmq, hm,
        zero_smul, zero_add, add_zero, one_smul, and_self]
    refine ⟨p, q, l, m, hcoords, ?_⟩
    intro R _ _ x
    dsimp only
    constructor
    · rintro ⟨t, rfl⟩
      rw [(hcoords R t).1, (hcoords R t).2]
      exact ⟨t.val_inv, hval R t⟩
    · rintro ⟨hab, hx⟩
      let t : Rˣ := ⟨coefficientAt l x.val, coefficientAt m x.val, hab,
        (mul_comm _ _).trans hab⟩
      exact ⟨t, Units.ext ((hval R t).trans hx.symm)⟩

theorem hermitianAnisotropy {D : Type u} [DivisionRing D] [Algebra K D] [Algebra E D]
    [IsScalarTower K E D] {r : ℕ} : HermitianAnisotropy (K := K) (E := E) (A := A) (D := D) (r := r) := by
  intro I _ hA b s e σ h hh hano x hx hxx
  obtain ⟨p, q, w, hp₀, hp, hq, hpq, hqp, hstar, hw⟩ :=
    hyperbolicIdempotents s e σ h hh x hx hxx
  exact hano (splitUnitaryTorusOfIdempotents hA b s p q w hp₀ hp hq hpq hqp hstar hw)

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.OuterTypeAModels (RepresentsUnitary)
open LinearAlgebraicGroups.Specs.StandardGroups

private theorem coefficientAt_natural {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (l : A →ₗ[K] K) (x : R ⊗[K] A) :
    coefficientAt l (Algebra.TensorProduct.map f (.id K A) x) = f (coefficientAt l x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t a => simp [coefficientAt_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem laurentSurjective {B : Type u} [CommRing B] [Algebra K B]
    (φ : B →ₐ[K] LaurentPolynomial K) {a b : B}
    (ha : φ a = LaurentPolynomial.T 1) (hb : φ b = LaurentPolynomial.T (-1)) :
    Function.Surjective φ := by
  intro z
  induction z using LaurentPolynomial.induction_on with
  | h_C c => exact ⟨algebraMap K B c, φ.commutes c⟩
  | @h_add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add φ _ _⟩
  | h_C_mul_T n c ih =>
    obtain ⟨x, hx⟩ := ih
    exact ⟨x * a, by rw [map_mul, hx, ha, mul_assoc, ← LaurentPolynomial.T_add]⟩
  | h_C_mul_T_Z n c ih =>
    obtain ⟨x, hx⟩ := ih
    exact ⟨x * b, by rw [map_mul, hx, hb, mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg]⟩

set_option maxHeartbeats 1000000 in
theorem splitTorusInUnitaryModel : SplitTorusInUnitaryModel (K := K) (E := E) (A := A) := by
  classical
  intro I _ hA b s G hG hT
  obtain ⟨point, hm, hn⟩ := hG
  obtain ⟨T, _, hunitary, hnatural, p, q, l, m, hcoords, _⟩ := hT
  let J := ULift.{u} (Fin 1)
  let L := LaurentPowerCoordinates K J
  let M := multiplicativePowerGroup K J
  let j : J := ⟨0⟩
  obtain ⟨e, he, c, hc⟩ := (LinearAlgebraicGroups.StandardGroups.multiplicativePowerSpecification K J).2.2.2
  let F := (groupPointsFunctor K).obj G.val
  let torusPoint (Q : TestAlgebra K) (a : Qˣ) : F.obj Q :=
    (point Q).symm ⟨T Q a, hunitary Q a⟩
  let component (Q : TestAlgebra K) : (multiplicativePowerPoints K J).obj Q →* F.obj Q :=
    MonoidHom.mk' (fun a => torusPoint Q (a j)) (by
      intro a b
      apply (point Q).injective
      apply Subtype.ext
      change (point Q (torusPoint Q ((a * b) j))).val =
        (point Q (torusPoint Q (a j) * torusPoint Q (b j))).val
      rw [hm Q (torusPoint Q (a j)) (torusPoint Q (b j))]
      dsimp only [torusPoint]
      simp only [Equiv.apply_symm_apply]
      exact (T Q).map_mul (a j) (b j))
  let α : multiplicativePowerPoints K J ⟶ (groupPointsFunctor K).obj G.val :=
    { app := fun Q => ConcreteCategory.ofHom (C := GrpCat)
        (X := (multiplicativePowerPoints K J).obj Q) (Y := F.obj Q) (component Q)
      naturality := by
        intro Q S f
        apply GrpCat.ext
        intro a
        apply (point S).injective
        apply Subtype.ext
        change (point S ((point S).symm ⟨T S (Units.map f.hom.toMonoidHom (a j)), _⟩)).val =
          (point S (mapPoints f ((point Q).symm ⟨T Q (a j), _⟩))).val
        rw [Equiv.apply_symm_apply, hn, Equiv.apply_symm_apply]
        exact hnatural Q S f.hom (a j) }
  obtain ⟨ι, hι⟩ := (LinearAlgebraicGroups.groupHomComparison K M.val G.val M.2.1).2 (c.hom ≫ α)
  refine ⟨ι, ?_⟩
  obtain ⟨Q, ⟨iQ⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.2.1
  let S := CommAlgCat.of K L
  let γ : Opposite.op S ⟶ Q :=
    (algSpec.fullyFaithful (R := CommRingCat.of K)).preimage (ι.hom.hom ≫ iQ.inv)
  have hγ : (testSpec K).map γ = ι.hom.hom ≫ iQ.inv :=
    (algSpec.fullyFaithful (R := CommRingCat.of K)).map_preimage _
  let uQ := (point Q.unop iQ.hom).val
  let a : Sˣ := (c.hom.app S (e.hom.app S (WithConv.toConv (AlgHom.id K L)))) j
  have ha : a.val = laurentVariable K J j := hc S (AlgHom.id K L) j
  have hi : (e.hom.app S (WithConv.toConv (AlgHom.id K L)) : Points M.val.X S) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    rw [he]
    exact Spec.map_id (CommRingCat.of L)
  have hh := DFunLike.congr_fun (congrArg (fun n => (n.app S).hom) hι)
    (e.hom.app S (WithConv.toConv (AlgHom.id K L)))
  change (e.hom.app S (WithConv.toConv (AlgHom.id K L)) : Points M.val.X S) ≫
    ι.hom.hom = (point S).symm ⟨T S a, hunitary S a⟩ at hh
  rw [hi] at hh
  change (𝟙 M.val.X) ≫ ι.hom.hom = torusPoint S a at hh
  rw [Category.id_comp] at hh
  have hu : Units.map (Algebra.TensorProduct.map γ.unop.hom (.id K A)).toMonoidHom uQ = T S a := by
    have hp : mapPoints γ.unop iQ.hom = ι.hom.hom := by
      change (testSpec K).map γ ≫ iQ.hom = _
      rw [hγ]
      exact (Category.assoc ι.hom.hom iQ.inv iQ.hom).trans (by
        rw [Iso.inv_hom_id, Category.comp_id])
    rw [show _ = (point S (mapPoints γ.unop iQ.hom)).val from (hn γ.unop iQ.hom).symm,
      hp, hh]
    exact congrArg Subtype.val ((point S).apply_symm_apply ⟨T S a, hunitary S a⟩)
  have hl : γ.unop.hom (coefficientAt l uQ.val) = a.val := by
    rw [← coefficientAt_natural]
    exact (congrArg (fun x : (S ⊗[K] A)ˣ => coefficientAt l x.val) hu).trans (hcoords S a).1
  have hm' : γ.unop.hom (coefficientAt m uQ.val) = a.inv := by
    rw [← coefficientAt_natural]
    exact (congrArg (fun x : (S ⊗[K] A)ˣ => coefficientAt m x.val) hu).trans (hcoords S a).2
  obtain ⟨_, d, _, hd⟩ :=
    LinearAlgebraicGroups.StandardGroups.tensorPowerCoordinatesSpecification.2.1 K J
  let φ := d.toAlgHom.comp γ.unop.hom
  have hφ₁ : φ (coefficientAt l uQ.val) = LaurentPolynomial.T 1 := by
    change d (γ.unop.hom _) = _
    rw [hl, ha, hd]
  have hφ₂ : φ (coefficientAt m uQ.val) = LaurentPolynomial.T (-1) := by
    change d (γ.unop.hom _) = _
    rw [hm']
    have hmul := congrArg d a.inv_val
    rw [map_mul, ha, hd, map_one] at hmul
    calc d a.inv = d a.inv * (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by
           rw [← LaurentPolynomial.T_add, show (1 : ℤ) + -1 = 0 by decide,
             LaurentPolynomial.T_zero, mul_one]
         _ = LaurentPolynomial.T (-1) := by rw [← mul_assoc, hmul, one_mul]
  have hsurj : Function.Surjective γ.unop.hom := by
    intro x
    obtain ⟨y, hy⟩ := laurentSurjective φ hφ₁ hφ₂ (d x)
    exact ⟨y, d.injective hy⟩
  have hcim : IsClosedImmersion ((testSpec K).map γ).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom γ.unop.hom.toRingHom) hsurj
  have hcomp : IsClosedImmersion (ι.hom.hom.left ≫ iQ.inv.left) := by
    rw [hγ] at hcim
    exact hcim
  letI : IsClosedImmersion (ι.hom.hom.left ≫ iQ.inv.left) := hcomp
  have hhcomp : IsClosedImmersion ((ι.hom.hom.left ≫ iQ.inv.left) ≫ iQ.hom.left) := by
    letI : IsIso iQ.hom.left :=
      inferInstanceAs (IsIso ((CategoryTheory.Over.forget _).map iQ.hom))
    infer_instance
  simpa using hhcomp

theorem schemeHermitianAnisotropy {D : Type u} [DivisionRing D]
    [Algebra K D] [Algebra E D] [IsScalarTower K E D] {r : ℕ} :
    SchemeHermitianAnisotropy (K := K) (E := E) (A := A) (D := D) (r := r) := by
  intro I _ hA b s G hG hano e σ h hh
  exact hermitianAnisotropy hA b s e σ h hh (fun t => hano (splitTorusInUnitaryModel hA b s G hG t))

theorem anisotropicHermitianModel : AnisotropicHermitianModel (K := K) (E := E) (A := A) := by
  intro _ hKE I _ hA _ b s G hG hano
  obtain ⟨r, D, _, _, hD, hr, e, σ, H, hH, hform⟩ := hermitianPresentation hKE hA s
  let : Algebra K D := Algebra.compHom D (algebraMap K E)
  let : IsScalarTower K E D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨x, p, i, τ, hcorner⟩ := selfAdjointCorner s e σ (form σ H.val) hform hH.1 hr
  obtain ⟨H', hH'⟩ := hermitianMatrixExists hr hD s e τ hcorner.2.2.2.2.2.2.2.2.1
  have hh := matrixForm s e τ H' hH'
  obtain ⟨B, hB⟩ := groundFieldBilinearity s e τ _ hh
  have han := schemeHermitianAnisotropy hA b s G hG hano e τ _ hh
  refine ⟨r, D, inferInstance, inferInstance, hD, hr, (RM03.CSA.centralDivision_degree hD).1,
    RM03.CSA.degree_matrix_division hA hD hr e, e, x, p, i, τ, H', hcorner, hH', hh, B, hB, ?_⟩
  intro y hy
  rw [hB]
  exact han y hy

end SplitTorus

section LocalInvariance

open LinearAlgebraicGroups.UnitaryNormEquations

variable {K E A D R : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D]
  [CommRing R] [Algebra K R] {r : ℕ}

private theorem extendForm_tmul {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (h : V →ₗ[K] V →ₗ[K] W)
    (c d : R) (x y : V) :
    extendForm h (c ⊗ₜ[K] x) (d ⊗ₜ[K] y) = (c * d) ⊗ₜ[K] h x y :=
  rfl

private theorem extendedAdjoint (s : SecondKind K E A) (e : A ≃ₐ[E] Mat r D)
    (B : (Fin r → D) →ₗ[K] (Fin r → D) →ₗ[K] D)
    (hB : ∀ a x y, B (columnAction e a x) y = B x (columnAction e (adj s a) y))
    (a : R ⊗[K] A) (x y : R ⊗[K] (Fin r → D)) :
    extendForm B (extendedColumnAction e a x) y =
      extendForm B x (extendedColumnAction e (adjointAt s a) y) := by
  have hadjAdd (a b : R ⊗[K] A) : adjointAt s (a + b) = adjointAt s a + adjointAt s b := by
    simp [adjointAt]
  induction a using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [hadjAdd, map_add, LinearMap.add_apply, ha, hb]
  | tmul a m =>
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
    | tmul b x =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
      | tmul c y =>
        simp only [extendedColumnAction_tmul, adjointAt_tmul, extendForm_tmul, hB]
        rw [mul_assoc, mul_left_comm a b]

theorem completionInvariance : CompletionInvariance.{u,v} (K := K) (E := E) (A := A)
    (D := D) (r := r) := by
  intro k w L I J _ _ hA b s e σ B hHerm v c R g hg f
  letI : Algebra K R := (k.embedding w).toAlgebra
  have hform (x y : R ⊗[K] (Fin r → D)) : extendForm B (f x) (f y) = extendForm B x y := by
    have h := extendedAdjoint s e B hHerm.2.2.2.2 g.val x (f y)
    change extendForm B (f x) (f y) = extendForm B x
      (extendedColumnAction e (adjointAt s g.val) (extendedColumnAction e g.val y)) at h
    rwa [← Module.End.mul_apply, ← map_mul, hg.1, map_one, Module.End.one_apply] at h
  refine ⟨hform, fun x j => ?_⟩
  have hpoly :
      (diagonalPolynomial v c B j).map (algebraMap K R) =
        diagonalPolynomial (v.baseChange R) (c.baseChange R) (extendForm B) j := by
    let φ := MvPolynomial.map (algebraMap K R) (σ := I)
    change φ _ = _
    unfold diagonalPolynomial
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      Module.Basis.baseChange_apply, extendForm_tmul, one_mul, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, mul_one, φ]
  change (diagonalPolynomial v c B j).eval₂ (algebraMap K R) _ =
    (diagonalPolynomial v c B j).eval₂ (algebraMap K R) _
  rw [← MvPolynomial.eval_map, ← MvPolynomial.eval_map, hpoly]
  rw [(diagonalCoordinates (v.baseChange R) (c.baseChange R) (extendForm B)).2.1,
    (diagonalCoordinates (v.baseChange R) (c.baseChange R) (extendForm B)).2.1, hform]

end LocalInvariance

section ExtendedDeterminant

open Algebra.TensorProduct (includeRight map)
open _root_.RM03.CSA.NormOneGroup
  (extendSplitting extendSplitting_tmul normAt_eq_det normAt_natural)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open private baseChangeMatrix from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting

variable {E T U A D : Type u} [Field E] [Ring A] [Algebra E A] [DivisionRing D] [Algebra E D]
  [CommRing T] [Algebra E T] [CommRing U] [Algebra E U] {r : ℕ}

/-- The action with coefficients extended over the centre. -/
private def centreAction (e : A ≃ₐ[E] Mat r D) :
    (T ⊗[E] A) →ₐ[T] Module.End T (T ⊗[E] (Fin r → D)) :=
  Algebra.TensorProduct.lift (R := E) (S := T) (Algebra.ofId T _)
    ((Module.End.baseChangeHom E T _).comp (columnAction e))
    (fun t _ => Algebra.commutes t _)

private theorem centreAction_tmul (e : A ≃ₐ[E] Mat r D) (c b : T)
    (a : A) (x : Fin r → D) :
    centreAction e (c ⊗ₜ[E] a) (b ⊗ₜ[E] x) =
      (c * b) ⊗ₜ[E] columnAction e a x := rfl

private theorem centreAction_natural_det (e : A ≃ₐ[E] Mat r D) [FiniteDimensional E D]
    (f : T →ₐ[E] U) (x : T ⊗[E] A) :
    LinearMap.det (centreAction e (map f (.id E A) x)) =
      f (LinearMap.det (centreAction e x)) := by
  classical
  let b := Module.Free.chooseBasis E (Fin r → D)
  rw [← LinearMap.det_toMatrix (b.baseChange U), ← LinearMap.det_toMatrix (b.baseChange T)]
  change _ = f.toRingHom _
  rw [RingHom.map_det]
  congr 1
  ext i j
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.toMatrix_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe,
      Module.Basis.baseChange_apply, centreAction_tmul, mul_one,
      Module.Basis.baseChange_repr_tmul, Algebra.smul_def, map_mul]
    exact congrArg (· * f t) (f.commutes _).symm
  | add x y hx hy =>
    simp only [map_add, LinearMap.toMatrix_apply, LinearMap.add_apply, Finsupp.add_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, AlgHom.toRingHom_eq_coe]
      at hx hy ⊢
    rw [hx, hy]

private def splitColumnCoordinates {d : ℕ}
    (f : U ⊗[E] D ≃ₐ[U] Mat d U) :
    U ⊗[E] (Fin r → D) ≃ₗ[U] (Fin d → (Fin r × Fin d) → U) :=
  let reorder : (Fin r → Mat d U) ≃ₗ[U] (Fin d → (Fin r × Fin d) → U) :=
    { toFun := fun x i j => x j.1 j.2 i
      invFun := fun x i j k => x k (i, j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  (TensorProduct.piRight E U U (fun _ : Fin r => D)).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin r => f.toLinearEquiv)).trans reorder)

private theorem detCentreAfterSplitting {L : Type u} [Field L] [Algebra E L] [Algebra L U]
    [IsScalarTower E L U] {I : Type u} [Fintype I]
    (hA : isCentralSimple E A) (hD : isCentralDivision E D)
    (b : Module.Basis I E A) (e : A ≃ₐ[E] Mat r D) (hr : 0 < r)
    (f : L ⊗[E] D ≃ₐ[L] Mat (degree E D) L) (x : U ⊗[E] A) :
    LinearMap.det (centreAction e x) = normAt hA b x ^ degree E D := by
  classical
  let d := degree E D
  let C := Fin r × Fin d
  let F := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e
    |>.trans (baseChangeMatrix E L D (Fin r))
    |>.trans f.mapMatrix
    |>.trans (Matrix.compAlgEquiv (Fin r) (Fin d) L L)
  let η : C ≃ Fin (degree E A) :=
    finProdFinEquiv.trans (finCongr (RM03.CSA.degree_matrix_division hA hD hr e).symm)
  let F' := F.trans (Matrix.reindexAlgEquiv L L η)
  let X := (Matrix.reindexAlgEquiv U U η.symm).toAlgHom.comp
    (extendSplitting (R := U) F').toAlgHom
  have hnorm : (X x).det = normAt hA b x := by
    exact (Matrix.det_reindex_self η.symm (extendSplitting F' x)).trans
      (normAt_eq_det hA b F' x).symm
  let p := splitColumnCoordinates (U := U) (r := r) (extendSplitting f)
  let S (a : U ⊗[E] A) :=
    LinearMap.pi (fun i : Fin d => (X a).mulVecLin ∘ₗ LinearMap.proj i)
  have hx (b : L) (M : Mat r D) : baseChangeMatrix E L D (Fin r) (b ⊗ₜ[E] M) =
      M.map (fun z => b ⊗ₜ[E] z) := matrixBaseChange_tmul _ _
  have hX (t : U) (a : A) (j k : C) :
      X (t ⊗ₜ[E] a) j k =
        t * (extendSplitting f ((1 : U) ⊗ₜ[E] (e a j.1 k.1))) j.2 k.2 := by
    change Matrix.reindex η.symm η.symm (extendSplitting F' (t ⊗ₜ[E] a)) j k = _
    rw [extendSplitting_tmul, extendSplitting_tmul, one_smul]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.map_apply, F', AlgEquiv.trans_apply, Matrix.reindexAlgEquiv_apply,
      Equiv.symm_symm, Equiv.symm_apply_apply]
    change t * algebraMap L U (F (1 ⊗ₜ[E] a) j k) = _
    change t * algebraMap L U
      (Matrix.compAlgEquiv (Fin r) (Fin d) L L
        (f.mapMatrix (baseChangeMatrix E L D (Fin r) (1 ⊗ₜ[E] e a))) j k) = _
    rw [hx]
    rfl
  have hact (a : U ⊗[E] A) (y : U ⊗[E] (Fin r → D)) :
      p (centreAction e a y) = S a (p y) := by
    induction a using TensorProduct.inductionOn with
    | add a a' ha ha' =>
      simp only [map_add, LinearMap.add_apply, ha, ha']
      funext i
      simp [S, Matrix.add_mulVec]
    | tmul t a =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp [hy, hy']
      | tmul u y =>
        rw [centreAction_tmul]
        funext i j
        let fU := extendSplitting (R := U) f
        change fU ((t * u) ⊗ₜ[E] (e a *ᵥ y) j.1) j.2 i =
          ∑ k : C, X (t ⊗ₜ[E] a) j k * fU (u ⊗ₜ[E] y k.1) k.2 i
        rw [Fintype.sum_prod_type]
        have hX' (k : C) : X (t ⊗ₜ[E] a) j k =
            t * fU ((1 : U) ⊗ₜ[E] (e a j.1 k.1)) j.2 k.2 := hX t a j k
        simp only [hX', mul_assoc, ← Finset.mul_sum]
        rw [show (t * u) ⊗ₜ[E] (e a *ᵥ y) j.1 =
          t • (u ⊗ₜ[E] (e a *ᵥ y) j.1) from rfl]
        simp only [map_smul, Matrix.smul_apply, smul_eq_mul]
        congr 1
        simp only [Matrix.mulVec, dotProduct, TensorProduct.tmul_sum, map_sum, Matrix.sum_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Matrix.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have heq : p.toLinearMap ∘ₗ centreAction e x ∘ₗ p.symm.toLinearMap = S x :=
    LinearMap.ext fun y => (hact x (p.symm y)).trans (congrArg (S x) (p.apply_symm_apply y))
  rw [← LinearMap.det_conj _ p, heq, ← hnorm]
  change LinearMap.det (LinearMap.pi (fun i : Fin d => (X x).mulVecLin ∘ₗ
    LinearMap.proj i)) = (X x).det ^ d
  rw [LinearMap.det_pi (fun _ : Fin d => (X x).mulVecLin)]
  simp [← Matrix.toLin'_apply', LinearMap.det_toLin']

private theorem centreDeterminant {I : Type u} [Fintype I]
    (hA : isCentralSimple E A) (hD : isCentralDivision E D)
    (b : Module.Basis I E A) (e : A ≃ₐ[E] Mat r D) (x : T ⊗[E] A) :
    LinearMap.det (centreAction e x) = normAt hA b x ^ degree E D := by
  classical
  let : FiniteDimensional E D := hD.2
  have hr : 0 < r := by
    let : IsSimpleRing A := hA.1
    by_contra! h
    have hz : r = 0 := Nat.le_zero.mp h
    subst r
    exact zero_ne_one (e.injective (by subsingleton))
  let L := AlgebraicClosure E
  let U := L ⊗[E] T
  let φ : T →ₐ[E] U := includeRight
  have hφ : Function.Injective φ :=
    Algebra.TensorProduct.includeRight_injective (algebraMap E L).injective
  let hD' : isCentralSimple E D := RM03.CSA.isCentralSimple_of_isCentralDivision E D hD
  obtain ⟨f⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hD'
  apply hφ
  have hnorm : normAt hA b (map φ (.id E A) x) = φ (normAt hA b x) :=
    normAt_natural hA b φ x
  rw [← centreAction_natural_det e φ, map_pow, ← hnorm]
  exact detCentreAfterSplitting hA hD b e hr f _

end ExtendedDeterminant

section DeterminantRestriction

open LinearAlgebraicGroups.UnitaryNormEquations
  (Centre associateCentre associateCentre_tmul IsSpecialUnitary unitaryNorm)

variable {K E A D R : Type u} [Field K] [Field E] [Algebra K E]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
  [DivisionRing D] [Algebra E D] [Algebra K D] [IsScalarTower K E D]
  [CommRing R] [Algebra K R] {r : ℕ}

local instance (priority := 2000) : Algebra E (Centre K E R) :=
  Algebra.TensorProduct.rightAlgebra

private theorem associateColumn_tmul (b : R) (x : Fin r → D) :
    associateColumn (b ⊗ₜ[K] x) = (b ⊗ₜ[K] (1 : E)) ⊗ₜ[E] x := rfl

private theorem associateColumn_action (e : A ≃ₐ[E] Mat r D)
    (a : R ⊗[K] A) (y : R ⊗[K] (Fin r → D)) :
    associateColumn (extendedColumnAction e a y) =
      centreAction e (associateCentre (E := E) a) (associateColumn y) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t x =>
      rw [extendedColumnAction_tmul, associateCentre_tmul, associateColumn_tmul,
        associateColumn_tmul, centreAction_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem completionDeterminantOne :
    CompletionDeterminantOne.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r) := by
  intro k w I _ hA hD b s e R g hg
  letI : Algebra K R := (k.embedding w).toAlgebra
  let : FiniteDimensional E D := hD.2
  let S := Centre K E R
  let p : R ⊗[K] (Fin r → D) ≃ₗ[R] S ⊗[E] (Fin r → D) := associateColumn
  let f := centreAction e (associateCentre (E := E) g.val)
  have hconj : p.toLinearMap ∘ₗ extendedColumnAction e g.val ∘ₗ p.symm.toLinearMap =
      f.restrictScalars R := by
    apply LinearMap.ext
    intro y
    change p (extendedColumnAction e g.val (p.symm y)) = f y
    rw [associateColumn_action, show associateColumn (p.symm y) = y from p.apply_symm_apply y]
  rw [← LinearMap.det_conj _ p, hconj, LinearMap.det_restrictScalars]
  change Algebra.norm R (LinearMap.det (centreAction e (associateCentre (E := E) g.val))) = 1
  rw [centreDeterminant hA hD b e]
  change Algebra.norm R (unitaryNorm hA b g.val ^ degree E D) = 1
  rw [hg.2, one_pow, map_one]

theorem completionVolumeInvariance :
    CompletionVolumeInvariance.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r) := by
  intro k w I J _ _ _ hA hD b s e v R g hg x
  letI : Algebra K R := (k.embedding w).toAlgebra
  let f := centreAction e (associateCentre (E := E) g.val)
  have hdet : LinearMap.det f = 1 := by
    change LinearMap.det (centreAction e (associateCentre (E := E) g.val)) = 1
    rw [centreDeterminant hA hD b e]
    change unitaryNorm hA b g.val ^ degree E D = 1
    rw [hg.2, one_pow]
  have hact : associateColumn ∘ (extendedColumnAction e g.val ∘ x) =
      f ∘ (associateColumn ∘ x) :=
    funext fun i => associateColumn_action e g.val (x i)
  unfold extendedVolume
  rw [hact, Module.Basis.det_comp, hdet, one_mul]

theorem completionRightMultiplication :
    CompletionRightMultiplication.{u,v} (K := K) (E := E) (A := A) (D := D) (r := r) := by
  intro k w e R a d
  letI : Algebra K R := (k.embedding w).toAlgebra
  let T := (rightMultiplication (K := K) (r := r) d).baseChange R
  apply LinearMap.ext
  intro x
  change extendedColumnAction e a (T x) = T (extendedColumnAction e a x)
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t x =>
      simp only [T, LinearMap.baseChange_tmul, extendedColumnAction_tmul]
      congr 1
      funext i
      simp [rightMultiplication, columnAction_apply, rightMul, Matrix.mulVec,
        dotProduct, Finset.sum_mul, mul_assoc]

end DeterminantRestriction

end LinearAlgebraicGroups.Arithmetic.AnisotropicUnitaryTensors
