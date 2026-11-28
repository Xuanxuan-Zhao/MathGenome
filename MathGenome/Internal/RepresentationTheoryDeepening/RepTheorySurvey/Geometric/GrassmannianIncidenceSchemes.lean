import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.GrassmannianIncidenceSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.PluckerEmbedding
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.LinearAlgebra.TensorProduct.Prod

namespace RepTheorySurvey.Geometric.GrassmannianIncidenceSchemes

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra pointsFunctor)
open LinearAlgebraicGroups.Specs.GrassmannianCharts (Family Plane planeFunctor)
open LinearAlgebraicGroups.GrassmannianCharts
  (affineProbesEquiv affineProbesEquiv_apply familyEquiv familyEquiv_apply hom_ext_on_affines)
open LatticeModelSpecs GrassmannianIncidenceSpecs
open Scheme.IdealSheafData
open scoped TensorProduct

theorem reducedClosureIncidence : ReducedClosureIncidence := by
  intro X Y j S T hj hST
  let f := reducedClosureInclusion X S
  let g := reducedClosureInclusion Y T
  have hf : IsClosedImmersion f.left := by
    change IsClosedImmersion (reducedClosureIdeal X S).subschemeι
    infer_instance
  have hg : IsClosedImmersion g.left := by
    change IsClosedImmersion (reducedClosureIdeal Y T).subschemeι
    infer_instance
  have hImage : j.left '' closure (pointLocation '' S) ⊆ closure (pointLocation '' T) := by
    apply Set.image_subset_iff.mpr
    apply closure_minimal _ (isClosed_closure.preimage j.left.continuous)
    rintro _ ⟨p, hp, rfl⟩
    exact subset_closure ⟨p ≫ j, hST p hp, pointLocation_comp p j⟩
  have hk : g.left.ker ≤ (f.left ≫ j.left).ker := by
    change (reducedClosureIdeal Y T).subschemeι.ker ≤
      ((reducedClosureIdeal X S).subschemeι ≫ j.left).ker
    rw [ker_subschemeι, Scheme.Hom.ker_comp, ker_subschemeι]
    unfold reducedClosureIdeal
    rw [map_vanishingIdeal]
    exact vanishingIdeal_antimono (Closeds.closure_le.mpr hImage)
  let i := IsClosedImmersion.lift g.left (f.left ≫ j.left) hk
  have hi : i ≫ g.left = f.left ≫ j.left := IsClosedImmersion.lift_fac _ _ _
  have hc : IsClosedImmersion (i ≫ g.left) := hi ▸ inferInstanceAs
    (IsClosedImmersion (f.left ≫ j.left))
  refine ⟨Over.homMk i ?_, IsClosedImmersion.of_comp_isClosedImmersion i g.left,
    Over.OverMorphism.ext hi⟩
  rw [← Over.w g, ← Category.assoc, hi, Category.assoc, Over.w j, Over.w f]

theorem stableGrassmannianIncidence : StableGrassmannianIncidence := by
  intro U W A C _ _ _ _ _ _ _ _ _ _ _ ι κ _ _ _ _ e bu bw d hd j Tu Tw
  dsimp only
  intro hj hformula hST
  obtain ⟨i, hi, hcomm⟩ := reducedClosureIncidence j _ _ hj hST
  refine ⟨i, hi, hcomm, fun q w ↦ ?_⟩
  unfold stableScheme at q
  let f := reducedClosureInclusion (grassmannianCharts bu hd).scheme {p | StablePlane bu hd Tu p}
  let hw := incidenceDimension_le e hd
  let g := reducedClosureInclusion (grassmannianCharts bw hw).scheme {p | StablePlane bw hw Tw p}
  change w ∈ grassmannianSubspace bw hw ((q ≫ i) ≫ g) ↔
    (e w).1 ∈ grassmannianSubspace bu hd (q ≫ f) ∧ (e w).2.2 = 0
  have hq : (q ≫ i) ≫ g = (q ≫ f) ≫ j :=
    (Category.assoc q i g).trans ((congrArg (fun z ↦ q ≫ z) hcomm).trans
      (Category.assoc q f j).symm)
  rw [hq]
  exact hformula _ w

section Affine

variable {U W A C : Type} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup C] [Module ℂ C]

/-- The given splitting after scalar extension to an affine test algebra. -/
private def extendedSplitting (e : W ≃ₗ[ℂ] U × (A × C)) (R : TestAlgebra ℂ) :
    (R ⊗[ℂ] W) ≃ₗ[R] (R ⊗[ℂ] U) × ((R ⊗[ℂ] A) × (R ⊗[ℂ] C)) :=
  e.baseChange ℂ R ≪≫ₗ TensorProduct.prodRight ℂ R R U (A × C) ≪≫ₗ
    (LinearEquiv.refl R _).prodCongr (TensorProduct.prodRight ℂ R R A C)

private theorem extendedSplitting_tmul (e : W ≃ₗ[ℂ] U × (A × C)) (R : TestAlgebra ℂ)
    (r : R) (w : W) :
    extendedSplitting e R (r ⊗ₜ[ℂ] w) =
      (r ⊗ₜ[ℂ] (e w).1, r ⊗ₜ[ℂ] (e w).2.1, r ⊗ₜ[ℂ] (e w).2.2) := by
  simp [extendedSplitting]

/-- The incidence plane is the kernel of the quotient with factors
`(U_R / P)` and `C_R`. -/
private def incidenceQuotient (e : W ≃ₗ[ℂ] U × (A × C)) (R : TestAlgebra ℂ)
    (P : Submodule R (R ⊗[ℂ] U)) :
    (R ⊗[ℂ] W) →ₗ[R] ((R ⊗[ℂ] U) ⧸ P) × (R ⊗[ℂ] C) :=
  (P.mkQ.prodMap (LinearMap.snd R (R ⊗[ℂ] A) (R ⊗[ℂ] C))).comp
    (extendedSplitting e R).toLinearMap

private theorem incidenceQuotient_surjective (e : W ≃ₗ[ℂ] U × (A × C))
    (R : TestAlgebra ℂ) (P : Submodule R (R ⊗[ℂ] U)) :
    Function.Surjective (incidenceQuotient e R P) := by
  rintro ⟨p, c⟩
  obtain ⟨u, hu⟩ := P.mkQ_surjective p
  refine ⟨(extendedSplitting e R).symm (u, 0, c), ?_⟩
  simp [incidenceQuotient, hu]

variable [Module.Finite ℂ U] [Module.Finite ℂ A] [Module.Finite ℂ C]

private def incidencePlane (e : W ≃ₗ[ℂ] U × (A × C)) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U) (R : TestAlgebra ℂ) (P : Plane ℂ U d R) :
    Plane ℂ W (d + Module.finrank ℂ A) R := by
  let f := incidenceQuotient e R P.toSubmodule
  let q := f.quotKerEquivOfSurjective (incidenceQuotient_surjective e R P.toSubmodule)
  refine ⟨f.ker, Module.Finite.equiv q.symm, Module.Projective.of_equiv q.symm, ?_⟩
  intro p
  rw [congrFun (Module.rankAtStalk_eq_of_equiv q) p, Module.rankAtStalk_prod,
    Pi.add_apply, P.rankAtStalk_eq, Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply]
  have hW : Module.finrank ℂ W = Module.finrank ℂ U + Module.finrank ℂ A +
      Module.finrank ℂ C := by
    rw [e.finrank_eq, Module.finrank_prod, Module.finrank_prod, Nat.add_assoc]
  change Module.finrank ℂ U - d + Module.finrank ℂ C =
    Module.finrank ℂ W - (d + Module.finrank ℂ A)
  omega

private theorem incidencePlane_mem (e : W ≃ₗ[ℂ] U × (A × C)) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U) (R : TestAlgebra ℂ) (P : Plane ℂ U d R)
    (w : R ⊗[ℂ] W) :
    w ∈ (incidencePlane e hd R P).toSubmodule ↔
      (extendedSplitting e R w).1 ∈ P.toSubmodule ∧ (extendedSplitting e R w).2.2 = 0 := by
  simp [incidencePlane, incidenceQuotient, LinearMap.mem_ker, Prod.ext_iff]

private theorem incidencePlane_injective (e : W ≃ₗ[ℂ] U × (A × C)) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U) (R : TestAlgebra ℂ) :
    Function.Injective (incidencePlane e hd R) := by
  intro P Q h
  apply Module.Grassmannian.ext
  ext u
  have hp := incidencePlane_mem e hd R P ((extendedSplitting e R).symm (u, 0, 0))
  have hq := incidencePlane_mem e hd R Q ((extendedSplitting e R).symm (u, 0, 0))
  rw [h] at hp
  exact (by simpa using hp.symm.trans hq)

open Module.Grassmannian (baseChangeMkQ baseChangeMkQEquiv)
open TensorProduct.AlgebraTensorModule (cancelBaseChange cancelBaseChange_symm_tmul)

private theorem incidencePlane_natural (e : W ≃ₗ[ℂ] U × (A × C)) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U) {R T : TestAlgebra ℂ} (a : R ⟶ T)
    (P : Plane ℂ U d R) :
    Module.Grassmannian.map a.hom (incidencePlane e hd R P) =
      incidencePlane e hd T (Module.Grassmannian.map a.hom P) := by
  let : Algebra R T := a.hom.toAlgebra
  let : IsScalarTower ℂ R T := IsScalarTower.of_algebraMap_eq' a.hom.comp_algebraMap.symm
  let f := incidenceQuotient e R P.toSubmodule
  let Q := (Module.Grassmannian.map a.hom P).toSubmodule
  let g := incidenceQuotient e T Q
  let ef := f.quotKerEquivOfSurjective (incidenceQuotient_surjective e R P.toSubmodule)
  let eq : ((T ⊗[ℂ] U) ⧸ Q) ≃ₗ[T] T ⊗[R] ((R ⊗[ℂ] U) ⧸ P.toSubmodule) :=
    baseChangeMkQEquiv P.toSubmodule
  let h := eq.prodCongr (cancelBaseChange ℂ R T T C).symm ≪≫ₗ
    (TensorProduct.prodRight R T T ((R ⊗[ℂ] U) ⧸ P.toSubmodule) (R ⊗[ℂ] C)).symm
  have hq (u : T ⊗[ℂ] U) : eq (Q.mkQ u) = baseChangeMkQ T P.toSubmodule u := rfl
  have hcomp :
      (ef.baseChange R T).toLinearMap.comp (baseChangeMkQ T f.ker) = h.toLinearMap.comp g := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro t w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, baseChangeMkQ,
      cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
      Submodule.mkQ_apply, LinearMap.quotKerEquivOfSurjective_apply_mk, ef]
    change t ⊗ₜ[R] f (1 ⊗ₜ[ℂ] w) = h (g (t ⊗ₜ[ℂ] w))
    simp only [f, g, h, incidenceQuotient, LinearMap.comp_apply, LinearEquiv.coe_coe,
      extendedSplitting_tmul, LinearMap.prodMap_apply, LinearMap.snd_apply,
      LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, hq, baseChangeMkQ,
      cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul, TensorProduct.prodRight_symm_tmul]
  apply Module.Grassmannian.ext
  rw [Module.Grassmannian.map_toSubmodule]
  change (baseChangeMkQ T f.ker).ker = g.ker
  exact (LinearEquiv.ker_comp _ _).symm.trans
    ((congrArg LinearMap.ker hcomp).trans (LinearEquiv.ker_comp _ _))

private def incidenceNatural (e : W ≃ₗ[ℂ] U × (A × C)) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U) :
    planeFunctor ℂ U d ⟶ planeFunctor ℂ W (d + Module.finrank ℂ A) where
  app R := ↾(incidencePlane e hd R)
  naturality {R T} a := by
    apply ConcreteCategory.hom_ext
    intro P
    exact (incidencePlane_natural e hd a P).symm

end Affine

/-- An isomorphism of affine point functors determines an isomorphism of their schemes. -/
private def schemeIsoOfAffinePoints {X Y : SchemeOver ℂ}
    (α : pointsFunctor X ≅ pointsFunctor Y) : X ≅ Y := by
  let f := (affineProbesEquiv X Y).symm α.hom
  let g := (affineProbesEquiv Y X).symm α.inv
  have hf (R : TestAlgebra ℂ) (p : Points X R) : p ≫ f = α.hom.app R p := by
    rw [← affineProbesEquiv_apply, Equiv.apply_symm_apply]
  have hg (R : TestAlgebra ℂ) (p : Points Y R) : p ≫ g = α.inv.app R p := by
    rw [← affineProbesEquiv_apply, Equiv.apply_symm_apply]
  refine ⟨f, g, ?_, ?_⟩
  · apply hom_ext_on_affines
    intro R p
    rw [← Category.assoc, hg, hf, Category.comp_id]
    exact congrArg (fun β : pointsFunctor X ⟶ pointsFunctor X ↦ β.app R p) α.hom_inv_id
  · apply hom_ext_on_affines
    intro R p
    rw [← Category.assoc, hf, hg, Category.comp_id]
    exact congrArg (fun β : pointsFunctor Y ⟶ pointsFunctor Y ↦ β.app R p) α.inv_hom_id

private theorem grassmannianProper {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ V) :
    IsProper (grassmannianCharts b hd).scheme.hom := by
  obtain ⟨P, hP, _, _⟩ :=
    LinearAlgebraicGroups.PluckerEmbedding.pluckerEquivariantGeometry ℂ V ι b d hd
  let e := schemeIsoOfAffinePoints ((grassmannianCharts b hd).affinePoints ≪≫
    P.charts.affinePoints.symm)
  have : IsProper
      (LinearAlgebraicGroups.Specs.ProjectiveSpaces.projectiveSpace ℂ
        (LinearAlgebraicGroups.Specs.PluckerEmbedding.Wedge ℂ d V)).hom :=
    LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper ℂ _
  have : IsProper P.charts.scheme.hom := by
    rw [← Over.w P.morphism]
    infer_instance
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  rw [← Over.w e.hom]
  infer_instance

theorem grassmannianIncidence : GrassmannianIncidence := by
  intro U W A C _ _ _ _ _ _ _ _ _ _ _ ι κ _ _ _ _ e bu bw d hd
  let hw := incidenceDimension_le e hd
  let X := grassmannianCharts bu hd
  let Y := grassmannianCharts bw hw
  let α : Family ℂ W (d + Module.finrank ℂ A) X.scheme :=
    X.affinePoints.hom ≫ incidenceNatural e hd
  let j : X.scheme ⟶ Y.scheme := (familyEquiv Y.affinePoints X.scheme).symm α
  have hpoints (R : TestAlgebra ℂ) (p : Points X.scheme R) :
      Y.affinePoints.hom.app R (p ≫ j) =
        incidencePlane e hd R (X.affinePoints.hom.app R p) := by
    rw [← familyEquiv_apply, Equiv.apply_symm_apply]
    rfl
  have : Mono j := by
    constructor
    intro S f g hfg
    apply hom_ext_on_affines
    intro R p
    apply (X.affinePoints.app R).toEquiv.injective
    change X.affinePoints.hom.app R (p ≫ f) = X.affinePoints.hom.app R (p ≫ g)
    apply incidencePlane_injective e hd R
    rw [← hpoints, ← hpoints, Category.assoc, Category.assoc, hfg]
  let : Module.Finite ℂ W := Module.Finite.of_basis bw
  have : IsProper Y.scheme.hom := grassmannianProper bw hw
  have : IsProper (j.left ≫ Y.scheme.hom) := by
    rw [Over.w j]
    exact grassmannianProper bu hd
  have : IsProper j.left := IsProper.of_comp j.left Y.scheme.hom
  refine ⟨j, (IsClosedImmersion.iff_isProper_and_mono j.left).mpr
    ⟨inferInstance, inferInstance⟩, ?_⟩
  intro p w
  have hp : grassmannianPlane bw hw (p ≫ j) =
      incidencePlane e hd complexAlgebra (grassmannianPlane bu hd p) := hpoints complexAlgebra p
  simp only [grassmannianSubspace, Submodule.mem_map_equiv, TensorProduct.lid_symm_apply, hp]
  refine (incidencePlane_mem e hd complexAlgebra (grassmannianPlane bu hd p)
    (1 ⊗ₜ[ℂ] w)).trans ?_
  rw [extendedSplitting_tmul]
  apply and_congr_right
  intro _
  constructor
  · intro h
    simpa using congrArg (TensorProduct.lid ℂ C) h
  · intro h
    rw [h, TensorProduct.tmul_zero]

end

end RepTheorySurvey.Geometric.GrassmannianIncidenceSchemes
