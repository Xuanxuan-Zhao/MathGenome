import Specs.LinearAlgebraicGroups.Descent.MatrixHilbert90
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Descent.NonabelianCohomology
import LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import Mathlib.LinearAlgebra.Matrix.Basis

open CategoryTheory Matrix Module LinearAlgebraicGroups.Specs
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Descent.NonabelianCohomology

namespace LinearAlgebraicGroups.Descent.MatrixHilbert90

universe u

section Matrices

variable {k K index : Type u} [Field k] [Field K] [Algebra k K]
  [Fintype index] [DecidableEq index]

private theorem glAction_val (σ : Gal(K/k)) (A : GL index K) :
    (glAction index σ A).val = A.val.map σ := rfl

/-- A matrix cocycle defines additive semilinear automorphisms of column space. -/
private def twistedColumns (a : Gal(K/k) → GL index K)
    (ha : ∀ σ τ, a (σ * τ) = a σ * glAction index σ (a τ)) :
    SemilinearAction k K (index → K) := by
  let f (σ : Gal(K/k)) (v : index → K) := (a σ).val *ᵥ (σ ∘ v)
  have ha₁ : a 1 = 1 := by simpa using ha 1 1
  have hone (v : index → K) : f 1 v = v := by
    simp [f, ha₁]
    rfl
  have hmul (σ τ : Gal(K/k)) (v : index → K) : f (σ * τ) v = f σ (f τ v) := by
    have hmap : σ ∘ f τ v = (a τ).val.map σ *ᵥ ((σ * τ) ∘ v) :=
      funext (RingHom.map_mulVec σ.toRingHom (a τ).val (τ ∘ v))
    simp only [f, ha, Units.val_mul, glAction_val] at ⊢
    rw [show (σ ∘ ((a τ).val *ᵥ (τ ∘ v))) = _ from hmap, mulVec_mulVec]
  refine
    { act := fun σ =>
        { toFun := f σ
          invFun := f σ⁻¹
          left_inv := fun v => by rw [← hmul, inv_mul_cancel, hone]
          right_inv := fun v => by rw [← hmul, mul_inv_cancel, hone]
          map_add' := fun v w => by
            change (a σ).val *ᵥ (σ ∘ (v + w)) = f σ v + f σ w
            rw [show σ ∘ (v + w) = (σ ∘ v) + (σ ∘ w) from funext fun i =>
              map_add σ (v i) (w i), mulVec_add] }
      one_act := hone
      mul_act := hmul
      map_smul := fun σ r v => ?_ }
  change (a σ).val *ᵥ (σ ∘ (r • v)) = σ r • ((a σ).val *ᵥ (σ ∘ v))
  rw [show σ ∘ (r • v) = σ r • (σ ∘ v) from funext fun i => map_mul σ r (v i),
    mulVec_smul]

/-- Matrix Hilbert 90 over a finite Galois extension, using a fixed column basis. -/
theorem finiteGL : Specification.FiniteGL.{u} := by
  intro k K index _ _ _ _ _ _ _ _ a ha
  classical
  let ρ := twistedColumns a ha
  obtain ⟨s, B, hB⟩ := ρ.exists_fixed_basis
  let := FiniteDimensional.fintypeBasisIndex B
  let E := Pi.basisFun K index
  let e : s ≃ index := Fintype.equivOfCardEq
    ((Module.finrank_eq_card_basis B).symm.trans (Module.finrank_eq_card_basis E))
  let B' := B.reindex e
  have hfixed (j : index) (σ : Gal(K/k)) :
      (a σ).val *ᵥ (σ ∘ B' j) = B' j := by
    change ρ.act σ (B' j) = B' j
    simpa [B'] using hB (e.symm j) σ
  let M : GL index K :=
    ⟨E.toMatrix B', B'.toMatrix E, E.toMatrix_mul_toMatrix_flip B',
      B'.toMatrix_mul_toMatrix_flip E⟩
  have hM (i j : index) : M.val i j = B' j i := by simp [M, E, Basis.toMatrix_apply]
  have h (σ : Gal(K/k)) : a σ * glAction index σ M = M := by
    apply GeneralLinearGroup.ext
    intro i j
    change ((a σ).val * M.val.map σ) i j = M.val i j
    simpa only [Matrix.mul_apply, Matrix.map_apply, hM, Matrix.mulVec, dotProduct,
      Function.comp_apply] using congrFun (hfixed j σ) i
  refine ⟨M⁻¹, fun σ => ?_⟩
  calc
    a σ = (a σ * glAction index σ M) * (glAction index σ M)⁻¹ := by simp
    _ = (M⁻¹)⁻¹ * glAction index σ M⁻¹ := by rw [h, inv_inv, map_inv]

/-- The determinant of a general linear witness for a special linear cocycle
can be removed by multiplying the witness on the left by a base-field matrix. -/
theorem finiteSL : Specification.FiniteSL.{u} := by
  intro k K index _ _ _ _ _ _ _ _ a ha
  let liftSL := (SpecialLinearGroup.toGL : SpecialLinearGroup index K →* GL index K)
  have heq (σ : Gal(K/k)) (x : SpecialLinearGroup index K) :
      liftSL (slAction index σ x) = glAction index σ (liftSL x) := by
    apply Units.ext
    rfl
  obtain ⟨b, hb⟩ := finiteGL (liftSL ∘ a) (fun σ τ => by
    change liftSL (a (σ * τ)) = liftSL (a σ) * glAction index σ (liftSL (a τ))
    rw [ha, map_mul, heq])
  let d := GeneralLinearGroup.det b
  have hdet (σ : Gal(K/k)) : Units.map σ.toRingHom d = d := by
    have h := congrArg GeneralLinearGroup.det (hb σ)
    change GeneralLinearGroup.det (liftSL (a σ)) =
      GeneralLinearGroup.det (b⁻¹ * glAction index σ b) at h
    rw [map_mul, map_inv, SpecialLinearGroup.coeToGL_det] at h
    have hmap : GeneralLinearGroup.det (glAction index σ b) = Units.map σ.toRingHom d :=
      GeneralLinearGroup.map_det σ.toRingHom b
    rw [hmap] at h
    exact (inv_mul_eq_one.mp h.symm).symm
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp
    ((IsGalois.mem_bot_iff_fixed d.val).mpr (fun σ => congrArg Units.val (hdet σ)))
  have hr₀ : r ≠ 0 := by
    intro h
    exact d.ne_zero (by simpa [h] using hr.symm)
  let rUnit := Units.mk0 r hr₀
  obtain ⟨D₀, hD₀⟩ := GeneralLinearGroup.det_surjective
    (n := index) (R := k) rUnit⁻¹
  let D := GeneralLinearGroup.map (algebraMap k K) D₀
  have hD : GeneralLinearGroup.det D = d⁻¹ := by
    rw [GeneralLinearGroup.map_det, hD₀, map_inv]
    congr 1
    exact Units.ext hr
  have hfix (σ : Gal(K/k)) : glAction index σ D = D := by
    apply GeneralLinearGroup.ext
    intro i j
    exact σ.commutes (D₀ i j)
  have hDb : GeneralLinearGroup.det (D * b) = 1 := by simp [hD, d]
  obtain ⟨c, hc⟩ := (MonoidHom.mem_range (f := liftSL)).mp
    (show D * b ∈ liftSL.range by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hDb)
  refine ⟨c, fun σ => SpecialLinearGroup.toGL_injective ?_⟩
  change liftSL (a σ) = liftSL (c⁻¹ * slAction index σ c)
  rw [map_mul, map_inv, heq, hc, map_mul, hfix, _root_.mul_inv_rev]
  simpa [Function.comp_apply, mul_assoc] using hb σ

end Matrices

section Transport

variable {Γ M N : Type u} [Group Γ] [Group M] [Group N]
  {ρ : Γ →* MulAut M} {ρN : Γ →* MulAut N}
  (e : M ≃* N) (he : ∀ σ m, e (ρ σ m) = ρN σ (e m))

include he in
private theorem equivariant_symm (σ : Γ) (n : N) :
    e.symm (ρN σ n) = ρ σ (e.symm n) := by
  apply e.injective
  simp [he]

include he in
private theorem cocycle_comp {a : Γ → M}
    (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    ∀ σ τ, (e ∘ a) (σ * τ) = (e ∘ a) σ * ρN σ ((e ∘ a) τ) := by
  intro σ τ
  simp only [Function.comp_apply, ha, map_mul, he]

include he in
private theorem transport_witness {a : Γ → M} {b : N}
    (hb : ∀ σ, (e ∘ a) σ = b⁻¹ * ρN σ b) :
    ∀ σ, a σ = (e.symm b)⁻¹ * ρ σ (e.symm b) := by
  intro σ
  have h := congrArg e.symm (hb σ)
  simpa only [Function.comp_apply, MulEquiv.symm_apply_apply, map_mul, map_inv,
    equivariant_symm e he] using h

private theorem neutral_of_coboundaries [TopologicalSpace Γ]
    (h : AllContinuousCoboundaries ρ) : AllClassesNeutral ρ := by
  let : TopologicalSpace M := ⊥
  change ∀ x : H1 ρ, x = basepoint ρ
  intro x
  refine Quotient.inductionOn x fun a => ?_
  obtain ⟨b, hb⟩ := h a
  apply classOf_eq_iff.mpr
  refine ⟨b⁻¹, fun σ => ?_⟩
  change 1 = (b⁻¹)⁻¹ * a σ * ρ σ b⁻¹
  rw [hb, inv_inv, ← mul_assoc b, mul_inv_cancel, one_mul, ← map_mul, mul_inv_cancel, map_one]

private theorem neutral_of_finite [TopologicalSpace Γ] (h : AllCoboundaries ρ) :
    AllClassesNeutral ρ :=
  neutral_of_coboundaries fun a => h a a.property.2

end Transport

section SchemePoints

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

/-- A natural matrix point comparison intertwines the two coefficient actions. -/
private theorem action_naturality {F : TestAlgebra k ⥤ GrpCat.{u}}
    {G : GroupScheme k} (i : (groupPointsFunctor k).obj G ≅ F)
    (σ : Gal(S/k)) (p : NonabelianCohomology.Points k S G.X) :
    (i.app (CommAlgCat.of k S)).groupIsoToMulEquiv (pointAction k S G.X σ p) =
      coefficientAction F σ ((i.app (CommAlgCat.of k S)).groupIsoToMulEquiv p) := by
  let R := CommAlgCat.of k S
  exact congrArg (fun f : ((groupPointsFunctor k).obj G).obj R ⟶ F.obj R => f p)
    (i.hom.naturality (CommAlgCat.ofHom σ.toAlgHom))

private theorem scheme_coboundaries [IsGalois k S] {F : TestAlgebra k ⥤ GrpCat.{u}}
    {G : GroupScheme k} (i : (groupPointsFunctor k).obj G ≅ F)
    (hfin : ∀ (L : FiniteGaloisIntermediateField k S),
      AllCoboundaries (coefficientAction (K := L) F)) :
    AllContinuousCoboundaries (pointAction k S G.X) := by
  let : TopologicalSpace (NonabelianCohomology.Points k S G.X) := ⊥
  let : DiscreteTopology (NonabelianCohomology.Points k S G.X) := ⟨rfl⟩
  change ∀ a : Cocycle (pointAction k S G.X), _
  intro a
  obtain ⟨L, c, -, hc⟩ := finiteLevel (⊥ : FiniteGaloisIntermediateField k S) a
  obtain ⟨e, _, he⟩ := finitePointsIdentification (H := G.X) L
  let eF := (i.app (CommAlgCat.of k L)).groupIsoToMulEquiv
  let f := e.symm.trans eF
  have hf (σ : Gal(L/k)) (x : LevelCoefficients (pointAction k S G.X) L) :
      f (levelAction (pointAction k S G.X) L σ x) = coefficientAction F σ (f x) := by
    change eF (e.symm (levelAction (pointAction k S G.X) L σ x)) = _
    rw [equivariant_symm e he]
    exact action_naturality i σ (e.symm x)
  obtain ⟨b, hb⟩ := hfin L (f ∘ c) (cocycle_comp f hf c.property.2)
  refine ⟨(f.symm b).val, fun σ => ?_⟩
  have h := congrArg Subtype.val (transport_witness f hf hb (restriction L σ))
  simpa only [hc σ, Subgroup.coe_mul, Subgroup.coe_inv, quotientAction_apply] using h

private theorem matrix_coboundaries [IsGalois k S] {F : TestAlgebra k ⥤ GrpCat.{u}}
    {G : GroupScheme k} (i : (groupPointsFunctor k).obj G ≅ F)
    (hfin : ∀ (L : FiniteGaloisIntermediateField k S),
      AllCoboundaries (coefficientAction (K := L) F)) :
    AllContinuousCoboundaries (coefficientAction (K := S) F) := by
  let e : NonabelianCohomology.Points k S G.X ≃* F.obj (CommAlgCat.of k S) :=
    (i.app (CommAlgCat.of k S)).groupIsoToMulEquiv
  let : TopologicalSpace (F.obj (CommAlgCat.of k S)) := ⊥
  let : DiscreteTopology (F.obj (CommAlgCat.of k S)) := ⟨rfl⟩
  let : TopologicalSpace (NonabelianCohomology.Points k S G.X) := ⊥
  change ∀ a : Cocycle (coefficientAction F), _
  intro a
  have he := equivariant_symm e (action_naturality i (S := S))
  let a' : Cocycle (pointAction k S G.X) :=
    ⟨e.symm ∘ a, continuous_of_discreteTopology.comp a.property.1,
      cocycle_comp e.symm he a.property.2⟩
  obtain ⟨b, hb⟩ := scheme_coboundaries i hfin a'
  exact ⟨e b, fun σ => transport_witness e.symm he hb σ⟩

end SchemePoints

/-- Continuous matrix Hilbert 90 over a chosen separable closure. -/
theorem continuousGL : Specification.ContinuousGL.{u} := by
  intro k S index _ _ _ _ _ _ _
  exact matrix_coboundaries (StandardGroups.generalLinearGroupPointsIso k index)
    (fun _ => finiteGL)

/-- Continuous special linear Hilbert 90 over a chosen separable closure. -/
theorem continuousSL : Specification.ContinuousSL.{u} := by
  intro k S index _ _ _ _ _ _ _
  exact matrix_coboundaries (StandardGroups.specialLinearGroupPointsIso k index)
    (fun _ => finiteSL)

theorem finiteGLH1 : Specification.FiniteGLH1.{u} := by
  intro k K index _ _ _ _ _ _ _ _
  exact neutral_of_finite finiteGL

theorem finiteSLH1 : Specification.FiniteSLH1.{u} := by
  intro k K index _ _ _ _ _ _ _ _
  exact neutral_of_finite finiteSL

theorem continuousGLH1 : Specification.ContinuousGLH1.{u} := by
  intro k S index _ _ _ _ _ _ _ G i
  exact neutral_of_coboundaries (scheme_coboundaries i fun _ => finiteGL)

theorem continuousSLH1 : Specification.ContinuousSLH1.{u} := by
  intro k S index _ _ _ _ _ _ _ G i
  exact neutral_of_coboundaries (scheme_coboundaries i fun _ => finiteSL)

section StandardGroupSchemes

variable {k S index : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
  [Fintype index] [DecidableEq index] [Nonempty index]

/-- The Galois cohomology set of the standard general linear group is a singleton. -/
theorem generalLinearGroupH1
    (x : groupH1 k (StandardGroups.generalLinearGroup k index).val.X S) :
    x = groupBasepoint k (StandardGroups.generalLinearGroup k index).val.X S :=
  continuousGLH1 _ (StandardGroups.generalLinearGroupPointsIso k index) x

/-- The Galois cohomology set of the standard special linear group is a singleton. -/
theorem specialLinearGroupH1
    (x : groupH1 k (StandardGroups.specialLinearGroup k index).val.X S) :
    x = groupBasepoint k (StandardGroups.specialLinearGroup k index).val.X S :=
  continuousSLH1 _ (StandardGroups.specialLinearGroupPointsIso k index) x

end StandardGroupSchemes

end LinearAlgebraicGroups.Descent.MatrixHilbert90
