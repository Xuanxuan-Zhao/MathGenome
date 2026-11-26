import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.SemilinearHopfFromPoints

open CategoryTheory WithConv Coalgebra HopfAlgebra Algebra.TensorProduct
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {A : HopfAlgebraCategory K} (E : TwistedPointAction k A)

private abbrev coordinateAlgebra (A : HopfAlgebraCategory K) : TestAlgebra K :=
  CommAlgCat.of K A

private def universalPoint (A : HopfAlgebraCategory K) :
    (convolutionPoints A).obj (coordinateAlgebra A) :=
  toConv (AlgHom.id K A)

/-- The pullback is the image of the universal point, viewed as a ring map. -/
private noncomputable def pullback (σ : Gal(K/k)) : A →+* A :=
  (E.operator σ (coordinateAlgebra A) (universalPoint A)).ofConv.toRingHom

private theorem operator_apply (σ : Gal(K/k)) (R : TestAlgebra K)
    (f : (convolutionPoints A).obj R) (x : A) :
    (E.operator σ R f).ofConv x = f.ofConv (pullback E σ x) := by
  let m : coordinateAlgebra A ⟶ R := ConcreteCategory.ofHom (C := CommAlgCat K) f.ofConv
  exact congrArg
    (fun a : (convolutionPoints A).obj (coordinateAlgebra A) ⟶
      (convolutionPoints A).obj (inverseTwistAlgebra σ R) => (a (universalPoint A)).ofConv x)
    (E.natural σ m)

private theorem pullback_one (x : A) : pullback E 1 x = x :=
  E.identity (coordinateAlgebra A) (universalPoint A) x

private theorem pullback_mul (σ τ : Gal(K/k)) (x : A) :
    pullback E (σ * τ) x = pullback E τ (pullback E σ x) := by
  exact (E.composition σ τ (coordinateAlgebra A) (universalPoint A) x).trans
    (operator_apply E σ (inverseTwistAlgebra τ (coordinateAlgebra A))
      (E.operator τ (coordinateAlgebra A) (universalPoint A)) x)

private theorem pullback_scalar (σ : Gal(K/k)) (r : K) :
    pullback E σ (algebraMap K A r) = algebraMap K A (σ⁻¹ r) :=
  (E.operator σ (coordinateAlgebra A) (universalPoint A)).ofConv.commutes r

private noncomputable def coordinateAction : SemilinearAction k K A where
  act σ :=
    { (pullback E σ⁻¹).toAddMonoidHom with
      invFun := pullback E σ
      left_inv := fun x => by
        change pullback E σ (pullback E σ⁻¹ x) = x
        rw [← pullback_mul, inv_mul_cancel, pullback_one]
      right_inv := fun x => by
        change pullback E σ⁻¹ (pullback E σ x) = x
        rw [← pullback_mul, mul_inv_cancel, pullback_one] }
  one_act x := by
    change pullback E (1 : Gal(K/k))⁻¹ x = x
    rw [inv_one, pullback_one]
  mul_act σ τ x := by
    change pullback E (σ * τ)⁻¹ x = pullback E σ⁻¹ (pullback E τ⁻¹ x)
    rw [mul_inv_rev, pullback_mul]
  map_smul σ r x := by
    change pullback E σ⁻¹ (r • x) = σ r • pullback E σ⁻¹ x
    simp only [Algebra.smul_def, map_mul, pullback_scalar, inv_inv]

private theorem tensorInclusions_mul
    (x : A) :
    let T := CommAlgCat.of K (A ⊗[K] A)
    let l : (convolutionPoints A).obj T := toConv includeLeft
    let r : (convolutionPoints A).obj T := toConv includeRight
    (l * r).ofConv x = comul (R := K) x := by
  dsimp only
  rw [AlgHom.convMul_def]
  change ((lmul' K).comp (Algebra.TensorProduct.map
    (includeLeft : A →ₐ[K] A ⊗[K] A) (includeRight : A →ₐ[K] A ⊗[K] A)))
      (comul (R := K) x) = _
  rw [← productMap_eq_comp_map]
  have h : (productMap includeLeft includeRight : A ⊗[K] A →ₐ[K] A ⊗[K] A) =
      AlgHom.id K (A ⊗[K] A) := by
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [productMap_apply_tmul]
      change (a ⊗ₜ[K] (1 : A)) * ((1 : A) ⊗ₜ[K] b) = a ⊗ₜ[K] b
      simp only [tmul_mul_tmul, mul_one, one_mul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  rw [h]
  rfl

/-- A natural Galois action on convolution points gives a descent datum on the
same Hopf algebra, with coordinate operators given by inverse pullbacks. -/
noncomputable def hopfDescentDatumOfPointAction : HopfDescentDatum k A where
  action := coordinateAction E
  map_one σ := map_one (pullback E σ⁻¹)
  map_mul σ := map_mul (pullback E σ⁻¹)
  comul_equivariant := by
    intro σ x
    let T := CommAlgCat.of K (A ⊗[K] A)
    let l : (convolutionPoints A).obj T := toConv includeLeft
    let r : (convolutionPoints A).obj T := toConv includeRight
    have h := congrArg (fun f : (convolutionPoints A).obj (inverseTwistAlgebra σ⁻¹ T) =>
        f.ofConv x) (map_mul (E.operator σ⁻¹ T).hom l r)
    change (E.operator σ⁻¹ T (l * r)).ofConv x =
      (E.operator σ⁻¹ T l * E.operator σ⁻¹ T r).ofConv x at h
    rw [operator_apply, tensorInclusions_mul, AlgHom.convMul_def] at h
    change comul (R := K) (pullback E σ⁻¹ x) =
      ((lmul' K).comp (Algebra.TensorProduct.map
        (E.operator σ⁻¹ T l).ofConv (E.operator σ⁻¹ T r).ofConv)) (comul (R := K) x) at h
    rw [← productMap_eq_comp_map] at h
    change comul (R := K) (pullback E σ⁻¹ x) = _
    rw [h]
    generalize comul (R := K) x = z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [productMap_apply_tmul, SemilinearAction.tensor_act_tmul, operator_apply, operator_apply]
      change (pullback E σ⁻¹ a ⊗ₜ[K] (1 : A)) * ((1 : A) ⊗ₜ[K] pullback E σ⁻¹ b) =
        pullback E σ⁻¹ a ⊗ₜ[K] pullback E σ⁻¹ b
      simp only [tmul_mul_tmul, mul_one, one_mul]
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
      rfl
  counit_equivariant := by
    intro σ x
    let T := CommAlgCat.of K K
    have h := congrArg (fun f : (convolutionPoints A).obj (inverseTwistAlgebra σ⁻¹ T) =>
        f.ofConv x) (map_one (E.operator σ⁻¹ T).hom)
    change (E.operator σ⁻¹ T 1).ofConv x = (1 :
      (convolutionPoints A).obj (inverseTwistAlgebra σ⁻¹ T)).ofConv x at h
    rw [operator_apply] at h
    change counit (R := K) (pullback E σ⁻¹ x) = (σ⁻¹)⁻¹ (counit (R := K) x) at h
    rw [inv_inv] at h
    exact h
  antipode_equivariant := by
    intro σ x
    let T := coordinateAlgebra A
    let p := universalPoint A
    have h := congrArg (fun f : (convolutionPoints A).obj (inverseTwistAlgebra σ⁻¹ T) =>
        f.ofConv x) (map_inv (E.operator σ⁻¹ T).hom p)
    change (E.operator σ⁻¹ T p⁻¹).ofConv x =
      ((E.operator σ⁻¹ T p)⁻¹).ofConv x at h
    rw [operator_apply] at h
    change antipode K (pullback E σ⁻¹ x) = (E.operator σ⁻¹ T p).ofConv (antipode K x) at h
    rw [operator_apply] at h
    exact h

theorem hopfDescentDatumOfPointAction_apply (σ : Gal(K/k)) (R : TestAlgebra K)
    (f : (convolutionPoints A).obj R) (x : A) :
    (E.operator σ R f).ofConv x =
      f.ofConv ((hopfDescentDatumOfPointAction E).action.act σ⁻¹ x) := by
  change (E.operator σ R f).ofConv x = f.ofConv (pullback E (σ⁻¹)⁻¹ x)
  rw [inv_inv, operator_apply]

theorem semilinearHopfFromPoints : Specs.SemilinearHopfFromPoints := by
  intro k K _ _ _ A E
  exact ⟨hopfDescentDatumOfPointAction E, hopfDescentDatumOfPointAction_apply E⟩

end LinearAlgebraicGroups.Descent
