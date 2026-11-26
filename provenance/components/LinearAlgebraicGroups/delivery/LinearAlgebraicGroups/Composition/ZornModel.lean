import Specs.LinearAlgebraicGroups.Composition.ZornModel
import LinearAlgebraicGroups.Composition.Adjoints

/-! The split octonion norm on Zorn matrices over a commutative ring. -/

namespace LinearAlgebraicGroups.Composition.Zorn

open scoped Matrix TensorProduct
open Specification

universe u v
variable {R : Type u} [CommRing R]

abbrev norm (R : Type u) [CommRing R] := ZornSpecification.norm R

abbrev first (R : Type u) [CommRing R] := ZornSpecification.first R

abbrev second (R : Type u) [CommRing R] := ZornSpecification.second R

noncomputable abbrev baseChange (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] := ZornSpecification.baseChange R S

@[simp] theorem coordinates_one : coordinates R (1 : Zorn R) = zornUnit := rfl

theorem coordinates_mul (x y : Zorn R) :
    coordinates R (x * y) = zornProduct (coordinates R x) (coordinates R y) := rfl

theorem product_and_unit : ZornSpecification.productAndUnit :=
  fun _ _ => ⟨coordinates_one, coordinates_mul, fun x => ⟨one_mul x, mul_one x⟩⟩

theorem cross_eq_det : ZornSpecification.determinantCross := by
  intro R _ x y z
  rw [dotProduct_comm, triple_product_permutation z x y, triple_product_eq_det]

theorem norm_formula (R : Type u) [CommRing R] (x : Zorn R) :
    norm R x = zornNorm (coordinates R x) := by
  rcases x with ⟨a, u, v, b⟩
  change (∑ i : Option (Fin 3), Option.elim i a u * Option.elim i b (-v)) = a * b - u ⬝ᵥ v
  rw [Fintype.sum_option]
  simp [dotProduct, sub_eq_add_neg, Finset.sum_neg_distrib]

@[simp] theorem norm_one (R : Type u) [CommRing R] : norm R 1 = 1 := by
  rw [norm_formula, coordinates_one]
  simp [zornNorm, zornUnit]

theorem norm_mul (x y : Zorn R) : norm R (x * y) = norm R x * norm R y := by
  simp only [norm_formula, coordinates_mul]
  rcases coordinates R x with ⟨a, u, v, b⟩
  rcases coordinates R y with ⟨c, w, t, d⟩
  simp only [zornNorm, zornProduct, sub_dotProduct, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [cross_dot_cross, dot_self_cross, dot_cross_self,
    dotProduct_comm (v ⨯₃ t) v, dotProduct_comm (v ⨯₃ t) t,
    dot_self_cross, dot_cross_self]
  rw [dotProduct_comm v u, dotProduct_comm t w, dotProduct_comm t u, dotProduct_comm w v]
  ring

theorem norm_laws : ZornSpecification.normLaws :=
  fun R _ => ⟨norm_one R, norm_mul⟩

theorem polar_formula (R : Type u) [CommRing R] (a b c d : R) (u v w t : Fin 3 → R) :
    (norm R).polarBilin (ofCoordinates (a, u, v, b)) (ofCoordinates (c, w, t, d)) =
      a * d + b * c - u ⬝ᵥ t - w ⬝ᵥ v := by
  rw [full_polar_formula]
  simp only [norm_formula, map_add, LinearEquiv.apply_symm_apply, Prod.mk_add_mk,
    zornNorm, add_dotProduct, dotProduct_add]
  ring

/-- The norm is isometric to the hyperbolic space on a free module of rank four. -/
def hyperbolicIsometry (R : Type u) [CommRing R] :
    (norm R).IsometryEquiv (QuadraticForm.dualProd R (Option (Fin 3) → R)) where
  toLinearEquiv := hyperbolicCoordinates R
  map_app' _ := rfl

theorem hyperbolic : ZornSpecification.hyperbolic :=
  fun R _ => ⟨hyperbolicIsometry R⟩

theorem perfect (R : Type u) [CommRing R] : (norm R).polarBilin.IsPerfPair := by
  let V := Option (Fin 3) → R
  let e : (Module.Dual R V × V) ≃ₗ[R] Module.Dual R (Module.Dual R V × V) :=
    (LinearEquiv.prodComm R (Module.Dual R V) V).trans <|
      ((Module.evalEquiv R V).prodCongr (LinearEquiv.refl R _)).trans
        (Module.dualProdDualEquivDual R _ _)
  have hp : (LinearMap.dualProd R V).IsPerfPair := by
    apply LinearMap.IsPerfPair.of_bijective
    have he : e.toLinearMap = LinearMap.dualProd R V := by
      apply LinearMap.ext₂
      intro x y
      rfl
    rw [← he]
    exact e.bijective
  let := hp
  have hpolar : (QuadraticForm.dualProd R V).polarBilin = LinearMap.dualProd R V := by
    apply LinearMap.ext₂
    intro x y
    rw [full_polar_formula]
    simp [QuadraticForm.dualProd_apply, LinearMap.dualProd_apply_apply]
    abel
  change ((QuadraticForm.dualProd R V).comp (hyperbolicCoordinates R).toLinearMap).polarBilin.IsPerfPair
  rw [QuadraticMap.polarBilin_comp, hpolar]
  infer_instance

theorem isOctonion (R : Type u) [CommRing R] : IsOctonionNorm (norm R) where
  finite := inferInstance
  projective := inferInstance
  rank_eight p := by
    let := p.nontrivial
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rw [(pairedColumns R).finrank_eq, Module.finrank_prod, Module.finrank_pi]
    simp
  perfect := perfect R
  multiplicative_after_baseChange := norm_comp_after_baseChange (norm R) norm_mul

theorem isSplit (R : Type u) [CommRing R] : IsSplitOctonion (norm R) :=
  ⟨coordinates R, coordinates_one, coordinates_mul, norm_formula R⟩

theorem octonion : ZornSpecification.octonion :=
  fun R _ => ⟨isOctonion R, isSplit R⟩

theorem trace_formula (R : Type u) [CommRing R] (a b : R) (u v : Fin 3 → R) :
    compositionTrace (norm R) (ofCoordinates (a, u, v, b)) = a + b := by
  rw [compositionTrace_apply]
  change (norm R).polarBilin (ofCoordinates (a, u, v, b)) (ofCoordinates (1, 0, 0, 1)) = _
  rw [polar_formula]
  simp

theorem conjugate_formula (R : Type u) [CommRing R] (a b : R) (u v : Fin 3 → R) :
    conjugate (norm R) (ofCoordinates (a, u, v, b)) = ofCoordinates (b, -u, -v, a) := by
  rw [conjugate_apply, trace_formula]
  change ((a + b) * 1 - a, (a + b) • (0 : Fin 3 → R) - u,
    (a + b) • (0 : Fin 3 → R) - v, (a + b) * 1 - b) = (b, -u, -v, a)
  simp

theorem complementary_idempotents : ZornSpecification.complementaryIdempotents := by
  intro R _
  change zornProduct ((1 : R), 0, 0, 0) (1, 0, 0, 0) = (1, 0, 0, 0) ∧
    zornProduct ((0 : R), 0, 0, 1) (0, 0, 0, 1) = (0, 0, 0, 1) ∧
    zornProduct ((1 : R), 0, 0, 0) (0, 0, 0, 1) = 0 ∧
    zornProduct ((0 : R), 0, 0, 1) (1, 0, 0, 0) = 0 ∧
    (((1 : R), 0, 0, 0) : ZornCoordinates R) + (0, 0, 0, 1) = (1, 0, 0, 1)
  refine ⟨by simp [zornProduct], by simp [zornProduct], by simp [zornProduct],
    by simp [zornProduct], ?_⟩
  change ((1 : R) + 0, (0 : Fin 3 → R) + 0, (0 : Fin 3 → R) + 0, (0 : R) + 1) =
    (1, 0, 0, 1)
  simp

theorem nonzero_idempotents : ZornSpecification.nonzeroIdempotents := by
  intro R _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (congrArg (fun x => (coordinates R x).1) h)
  · intro h
    exact one_ne_zero (congrArg (fun x => (coordinates R x).2.2.2) h)
  · rw [norm_formula]
    change zornNorm ((1 : R), 0, 0, 0) = 0
    simp [zornNorm]
  · rw [norm_formula]
    change zornNorm ((0 : R), 0, 0, 1) = 0
    simp [zornNorm]

theorem field_isotropic : ZornSpecification.fieldIsotropic := by
  intro k _
  obtain ⟨hne, _, hnorm, _⟩ := nonzero_idempotents k
  exact ⟨first k, hne, hnorm⟩

section BaseChange

variable {S : Type v} [CommRing S]

private lemma cross_map (f : R →+* S) (x y : Fin 3 → R) :
    (f ∘ (x ⨯₃ y)) = (f ∘ x) ⨯₃ (f ∘ y) := by
  funext i
  fin_cases i <;> simp [cross_apply]

theorem mapCoordinates_mul (f : R →+* S) (x y : Zorn R) :
    ZornSpecification.mapCoordinates f (x * y) =
      ZornSpecification.mapCoordinates f x * ZornSpecification.mapCoordinates f y := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨c, w, t, d⟩
  have hvect (o p : Fin 3 → R) (r s : R) :
      f ∘ (r • o + s • p) = f r • (f ∘ o) + f s • (f ∘ p) := by
    ext i
    simp
  change
    (f (a * c + u ⬝ᵥ t), f ∘ (a • w + d • u - v ⨯₃ t),
      f ∘ (c • v + b • t + u ⨯₃ w), f (b * d + v ⬝ᵥ w)) =
    (f a * f c + (f ∘ u) ⬝ᵥ (f ∘ t), f a • (f ∘ w) + f d • (f ∘ u) - (f ∘ v) ⨯₃ (f ∘ t),
      f c • (f ∘ v) + f b • (f ∘ t) + (f ∘ u) ⨯₃ (f ∘ w), f b * f d + (f ∘ v) ⬝ᵥ (f ∘ w))
  have hsub (o p : Fin 3 → R) : f ∘ (o - p) = (f ∘ o) - (f ∘ p) := by
    ext i
    simp
  have hadd (o p : Fin 3 → R) : f ∘ (o + p) = (f ∘ o) + (f ∘ p) := by
    ext i
    simp
  simp only [map_add, map_mul, f.map_dotProduct, hsub, hadd _ (_ ⨯₃ _), hvect, cross_map]

theorem mapCoordinates_norm (f : R →+* S) (x : Zorn R) :
    norm S (ZornSpecification.mapCoordinates f x) = f (norm R x) := by
  simp only [norm_formula]
  rcases x with ⟨a, u, v, b⟩
  change f a * f b - (f ∘ u) ⬝ᵥ (f ∘ v) = f (a * b - u ⬝ᵥ v)
  rw [map_sub, map_mul, f.map_dotProduct]

variable [Algebra R S]

theorem baseChange_tmul (s : S) (x : Zorn R) :
    baseChange R S (s ⊗ₜ[R] x) = s • ZornSpecification.mapCoordinates (algebraMap R S) x := by
  apply (pairedFunctions S).injective
  funext i
  simp only [baseChange, ZornSpecification.baseChange, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
  change ((Pi.basisFun R _).repr (pairedFunctions R x) i) • s =
    pairedFunctions S (s • ZornSpecification.mapCoordinates (algebraMap R S) x) i
  rw [Pi.basisFun_repr, LinearEquiv.map_smul, Pi.smul_apply]
  rcases x with ⟨a, u, v, b⟩
  rcases i with (i | i) <;> cases i
  · change a • s = s * algebraMap R S a
    rw [Algebra.smul_def, mul_comm]
  · rename_i i
    change u i • s = s * algebraMap R S (u i)
    rw [Algebra.smul_def, mul_comm]
  · change b • s = s * algebraMap R S b
    rw [Algebra.smul_def, mul_comm]
  · rename_i i
    change (-v i) • s = s * -algebraMap R S (v i)
    rw [Algebra.smul_def, map_neg, mul_comm]

theorem baseChange_coordinates : ZornSpecification.baseChangeCoordinates := by
  intro R _ S _ _ s a b u v
  rw [baseChange_tmul]
  rfl

theorem baseChange_one : baseChange R S (1 : S ⊗[R] Zorn R) = 1 := by
  change baseChange R S (1 ⊗ₜ[R] (1 : Zorn R)) = 1
  rw [baseChange_tmul, one_smul]
  change (algebraMap R S 1, (fun _ : Fin 3 => algebraMap R S 0),
    (fun _ : Fin 3 => algebraMap R S 0), algebraMap R S 1) =
      (1, (0 : Fin 3 → S), (0 : Fin 3 → S), 1)
  simp [Pi.zero_def]

theorem baseChange_mul (x y : S ⊗[R] Zorn R) :
    baseChange R S (x * y) = baseChange R S x * baseChange R S y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp [add_mul, hx, hz]
  | tmul s x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [mul_add, hy, hz]
    | tmul t y =>
      simp [Algebra.TensorProduct.tmul_mul_tmul, baseChange_tmul, mapCoordinates_mul,
        smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm s t]

theorem baseChange_norm :
    normBaseChange S (norm R) = (norm S).comp (baseChange R S).toLinearMap := by
  apply baseChange_ext
  intro x
  simp only [normBaseChange_tmul, one_mul, QuadraticMap.comp_apply,
    LinearEquiv.coe_coe, baseChange_tmul, one_smul, mapCoordinates_norm]

theorem baseChange_polar :
    (normBaseChange S (norm R)).polarBilin =
      (norm S).polarBilin.compl₁₂ (baseChange R S).toLinearMap (baseChange R S).toLinearMap := by
  rw [baseChange_norm, QuadraticMap.polarBilin_comp]

theorem baseChange_conjugate (x : S ⊗[R] Zorn R) :
    baseChange R S (conjugate (normBaseChange S (norm R)) x) =
      conjugate (norm S) (baseChange R S x) := by
  simp only [conjugate_apply, compositionTrace_apply, baseChange_polar,
    LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, map_sub, LinearEquiv.map_smul, baseChange_one]

theorem baseChange_first : baseChange R S (1 ⊗ₜ[R] first R) = first S := by
  rw [baseChange_tmul, one_smul]
  change (algebraMap R S 1, (fun _ : Fin 3 => algebraMap R S 0),
    (fun _ : Fin 3 => algebraMap R S 0), algebraMap R S 0) =
      (1, (0 : Fin 3 → S), (0 : Fin 3 → S), 0)
  simp [Pi.zero_def]

theorem baseChange_second : baseChange R S (1 ⊗ₜ[R] second R) = second S := by
  rw [baseChange_tmul, one_smul]
  change (algebraMap R S 0, (fun _ : Fin 3 => algebraMap R S 0),
    (fun _ : Fin 3 => algebraMap R S 0), algebraMap R S 1) =
      (0, (0 : Fin 3 → S), (0 : Fin 3 → S), 1)
  simp [Pi.zero_def]

theorem baseChange_laws : ZornSpecification.baseChangeLaws :=
  fun _ _ _ _ _ => ⟨baseChange_one, baseChange_mul, baseChange_norm, baseChange_polar,
    baseChange_conjugate, baseChange_first, baseChange_second⟩

end BaseChange

section MatrixDouble

open ZornSpecification (MatrixDouble matrixDoubleUnit matrixDoubleProduct matrixDoubleNorm
  matrixDoubleDiagonal)

private def doubleCoordinates (x : MatrixDouble R) : ZornCoordinates R :=
  (x.1 0 0, ![x.1 0 1, x.2 0 0, -x.2 1 0],
    ![x.1 1 0, x.2 1 1, x.2 0 1], x.1 1 1)

private def doubleLinearEquiv (R : Type u) [CommRing R] : MatrixDouble R ≃ₗ[R] Zorn R :=
  ({ toFun := doubleCoordinates
     invFun := fun ⟨a, u, v, b⟩ => (!![a, u 0; v 0, b], !![u 1, v 2; -u 2, v 1])
     left_inv := by
       rintro ⟨x, y⟩
       simp [doubleCoordinates, ← Matrix.eta_fin_two]
     right_inv := by
       rintro ⟨a, u, v, b⟩
       change (a, ![u 0, u 1, -(-u 2)], ![v 0, v 1, v 2], b) = (a, u, v, b)
       simp only [neg_neg, Prod.mk.injEq, true_and, and_true]
       constructor <;> (funext i; fin_cases i <;> rfl)
     map_add' := by
       rintro ⟨x, y⟩ ⟨z, w⟩
       simp [doubleCoordinates, Prod.mk_add_mk, add_comm]
     map_smul' := by
       rintro r ⟨x, y⟩
       simp [doubleCoordinates] } :
    MatrixDouble R ≃ₗ[R] ZornCoordinates R).trans (coordinates R).symm

theorem matrixDouble_norm_formula (R : Type u) [CommRing R] (x : MatrixDouble R) :
    matrixDoubleNorm R x = x.1.det - x.2.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  rfl

/-- Write the double as a Zorn matrix using the paired coordinate axes. -/
def matrixDoubleIsometry (R : Type u) [CommRing R] :
    (matrixDoubleNorm R).IsometryEquiv (norm R) where
  toLinearEquiv := doubleLinearEquiv R
  map_app' x := by
    rw [norm_formula, matrixDouble_norm_formula, Matrix.det_fin_two, Matrix.det_fin_two]
    change zornNorm (doubleCoordinates x) = _
    simp [doubleCoordinates, zornNorm]
    ring

theorem matrixDouble_unit (R : Type u) [CommRing R] :
    matrixDoubleIsometry R (matrixDoubleUnit R) = 1 := by
  change doubleCoordinates (matrixDoubleUnit R) = zornUnit
  simp [doubleCoordinates, matrixDoubleUnit, zornUnit, Matrix.one_fin_two]

theorem matrixDouble_mul (x y : MatrixDouble R) :
    matrixDoubleIsometry R (matrixDoubleProduct x y) =
      matrixDoubleIsometry R x * matrixDoubleIsometry R y := by
  change doubleCoordinates (matrixDoubleProduct x y) =
    zornProduct (doubleCoordinates x) (doubleCoordinates y)
  simp only [doubleCoordinates, matrixDoubleProduct, zornProduct, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.adjugate_fin_two]
    ring
  · funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.adjugate_fin_two] <;> ring
  · funext i
    fin_cases i <;>
      simp [cross_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.adjugate_fin_two] <;> ring
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.adjugate_fin_two]
    ring

theorem matrixDouble_model : ZornSpecification.matrixDoubleModel :=
  fun R _ => ⟨matrixDoubleIsometry R, matrixDouble_unit R, matrixDouble_mul⟩

theorem matrixDouble_split_norm : ZornSpecification.matrixDoubleSplitNorm := by
  intro k _
  have hinj : Function.Injective (matrixDoubleDiagonal k) :=
    fun _ _ h => congrArg Prod.fst h
  refine ⟨?_, ?_, ?_, ?_, ⟨(matrixDoubleIsometry k).trans (hyperbolicIsometry k)⟩⟩
  · simp [MatrixDouble, Module.finrank_prod, Module.finrank_matrix]
  · rw [LinearMap.finrank_range_of_inj hinj]
    simp [Module.finrank_matrix]
  · rintro _ ⟨x, rfl⟩
    rw [matrixDouble_norm_formula]
    exact sub_self x.det
  · refine ⟨(1, 1), ?_, ?_⟩
    · intro h
      exact one_ne_zero (congrArg Prod.fst h)
    · rw [matrixDouble_norm_formula]
      exact sub_self (1 : Matrix (Fin 2) (Fin 2) k).det

theorem matrixDouble_zero_divisors : ZornSpecification.matrixDoubleZeroDivisors := by
  intro k _ h
  let a : MatrixDouble k := (0, 1)
  let e := (2 : k)⁻¹ • (matrixDoubleUnit k + a)
  let f := (2 : k)⁻¹ • (matrixDoubleUnit k - a)
  change matrixDoubleProduct a a = matrixDoubleUnit k ∧
    e ≠ 0 ∧ f ≠ 0 ∧ matrixDoubleProduct e f = 0 ∧ matrixDoubleProduct f e = 0
  have ha : matrixDoubleProduct a a = matrixDoubleUnit k := by
    simp [a, matrixDoubleProduct, matrixDoubleUnit, Matrix.adjugate_one]
  have he : e ≠ 0 := by
    intro he
    have hs : (2 : k)⁻¹ = 0 := by
      simpa [e, a, matrixDoubleUnit] using congrArg (fun x : MatrixDouble k => x.1 0 0) he
    exact (inv_ne_zero h) hs
  have hf : f ≠ 0 := by
    intro hf
    have hs : (2 : k)⁻¹ = 0 := by
      simpa [f, a, matrixDoubleUnit] using congrArg (fun x : MatrixDouble k => x.1 0 0) hf
    exact (inv_ne_zero h) hs
  let g := matrixDoubleIsometry k
  have hg : g a * g a = 1 := by
    dsimp only [g]
    rw [← matrixDouble_mul, ha, matrixDouble_unit]
  have hef : (1 + g a) * (1 - g a) = 0 := by
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, hg]
    abel
  have hfe : (1 - g a) * (1 + g a) = 0 := by
    rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hg]
    abel
  have he' : g e = (2 : k)⁻¹ • (1 + g a) := by
    simp only [g, e, map_smul, map_add, matrixDouble_unit]
  have hf' : g f = (2 : k)⁻¹ • (1 - g a) := by
    simp only [g, f, map_smul, map_sub, matrixDouble_unit]
  refine ⟨ha, he, hf, ?_, ?_⟩
  · apply g.toLinearEquiv.injective
    change g (matrixDoubleProduct e f) = g 0
    rw [show g (matrixDoubleProduct e f) = g e * g f from matrixDouble_mul e f,
      map_zero, he', hf', smul_mul_assoc, mul_smul_comm, hef, smul_zero, smul_zero]
  · apply g.toLinearEquiv.injective
    change g (matrixDoubleProduct f e) = g 0
    rw [show g (matrixDoubleProduct f e) = g f * g e from matrixDouble_mul f e,
      map_zero, hf', he', smul_mul_assoc, mul_smul_comm, hfe, smul_zero, smul_zero]

end MatrixDouble
end LinearAlgebraicGroups.Composition.Zorn
