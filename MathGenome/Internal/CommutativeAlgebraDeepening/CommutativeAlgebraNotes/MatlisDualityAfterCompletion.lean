import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualityAfterCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteMatlisDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisHullUnderCompletion
import Mathlib.RingTheory.Finiteness.Small

noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped TensorProduct

namespace CommutativeAlgebraNotes

open MatlisDualityAfterCompletionSpecs CompleteMatlisDualitySpecs
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion IsPowerTorsion)
open CompletionOfTorsionModules MatlisHullUnderCompletion

universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "S" => Completion R

local instance : IsNoetherianRing S :=
  P103.Ch07.CompletedNoetherian.completed_noetherian R (maximalIdeal R)

attribute [local instance] restrictedHullModule restrictedHullScalarTower

private theorem artinianPowerTorsion {T : Type v} [AddCommGroup T] [Module R T]
    [IsArtinian R T] : IsPowerTorsion R T := by
  intro x
  change x ∈ idealTorsion (maximalIdeal R) T
  rw [idealTorsion_eq_top_of_isArtinian]
  exact Submodule.mem_top

private theorem restrictedPowerTorsion {T : Type v} [AddCommGroup T] [Module S T]
    (hT : IsArtinian S T) :
    letI := Module.compHom T (algebraMap R S)
    IsPowerTorsion R T := by
  let := Module.compHom T (algebraMap R S)
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact powerTorsion_restrictScalars (artinianPowerTorsion (T := T) (R := S))

private theorem originalDualFinite (E : ResidueFieldEnvelope S) (X : ModuleCat.{u} R)
    [IsArtinian R X] : Module.Finite S ((originalDual E).obj (op X)) := by
  let hX : IsPowerTorsion R X := artinianPowerTorsion
  let := completionModule hX
  let := completionScalarTower hX
  let : IsArtinian S X := (powerTorsion_artinian_iff hX).mp inferInstance
  let := matlisDual_finite_of_isArtinian E X
  exact Module.Finite.of_surjective (completedMatlisDualEquiv E hX).symm.toLinearMap
    (completedMatlisDualEquiv E hX).symm.surjective

private theorem completedDualArtinian (E : ResidueFieldEnvelope S) (X : ModuleCat.{u} S)
    [Module.Finite S X] : IsArtinian R ((completedDual E).obj (op X)) := by
  let D := MatlisDualModule E X
  let : Module R D := Module.compHom D (algebraMap R S)
  let : IsScalarTower R S D := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hD : IsArtinian S D := matlisDual_isArtinian_of_finite E X
  exact (powerTorsion_artinian_iff (restrictedPowerTorsion hD)).mpr hD

private def artinianEvaluation (E : ResidueFieldEnvelope S) (X : ModuleCat.{u} R)
    [IsArtinian R X] :
    X ≃ₗ[R] (completedDual E).obj (op ((originalDual E).obj (op X))) := by
  let hX : IsPowerTorsion R X := artinianPowerTorsion
  letI := completionModule hX
  letI := completionScalarTower hX
  letI : IsArtinian S X := (powerTorsion_artinian_iff hX).mp inferInstance
  let d := completedMatlisDualEquiv E hX
  let e := (LinearEquiv.ofBijective (matlisEvaluation E X)
    (matlisEvaluation_bijective_of_isArtinian E X)).trans (LinearEquiv.congrLeft E.carrier S d.symm)
  let f : X →ₗ[R] (completedDual E).obj (op ((originalDual E).obj (op X))) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun r x => by
        apply LinearMap.ext
        intro g
        exact g.map_smul r x }
  exact LinearEquiv.ofBijective f e.bijective

private def finiteEvaluation (E : ResidueFieldEnvelope S) (X : ModuleCat.{u} S)
    [Module.Finite S X] :
    X ≃ₗ[S] (originalDual E).obj (op ((completedDual E).obj (op X))) := by
  let D := MatlisDualModule E X
  letI : Module R D := Module.compHom D (algebraMap R S)
  letI : IsScalarTower R S D := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hD : IsPowerTorsion R D := restrictedPowerTorsion (matlisDual_isArtinian_of_finite E X)
  let d : (D →ₗ[S] E.carrier) ≃ₗ[S] (D →ₗ[R] E.carrier) := powerTorsionHomEquiv hD
  exact (LinearEquiv.ofBijective (matlisEvaluation E X)
    (matlisEvaluation_bijective_of_finite E X)).trans d

/-- Artinian modules over the original ring and finite modules over its completion are
contravariantly equivalent via the two residue-hull duals. -/
theorem matlisDualityAfterCompletion :
    MatlisDualityAfterCompletionSpecs.matlisDualityAfterCompletion.{u} := by
  intro R _ _ _ E
  let hA (X : (artinianModules R).FullSubcategoryᵒᵖ) :
      finiteModules (Completion R) ((originalDual E).obj (op X.unop.obj)) :=
    let : IsArtinian R X.unop.obj := X.unop.property
    originalDualFinite E X.unop.obj
  let hF (X : (finiteModules (Completion R)).FullSubcategoryᵒᵖ) :
      artinianModules R ((completedDual E).obj (op X.unop.obj)) :=
    let : Module.Finite (Completion R) X.unop.obj := X.unop.property
    completedDualArtinian E X.unop.obj
  let F := (finiteModules (Completion R)).lift ((artinianModules R).ι.op ⋙ originalDual E) hA
  let G := (artinianModules R).lift ((finiteModules (Completion R)).ι.op ⋙ completedDual E) hF
  let η : F ⋙ G.rightOp ≅ 𝟭 _ :=
    NatIso.ofComponents (fun X =>
      let : IsArtinian R X.unop.obj := X.unop.property
      ((artinianModules R).isoMk (artinianEvaluation E X.unop.obj).toModuleIso).op)
      (by
        intro X Y f
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => LinearMap.ext fun g => rfl)
  let ε : 𝟭 _ ≅ G.rightOp ⋙ F :=
    NatIso.ofComponents (fun X =>
      let : Module.Finite (Completion R) X.obj := X.property
      (finiteModules (Completion R)).isoMk (finiteEvaluation E X.obj).toModuleIso)
      (by
        intro X Y f
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => LinearMap.ext fun g => rfl)
  let e : (artinianModules R).FullSubcategoryᵒᵖ ≌ (finiteModules (Completion R)).FullSubcategory :=
    ⟨F, G.rightOp, η.symm, ε.symm, fun X => by
      have h : ε.hom.app (F.obj X) ≫ F.map (η.hom.app X) = 𝟙 (F.obj X) := by
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun f => LinearMap.ext fun x => rfl
      have h' : F.map (η.hom.app X) = ε.inv.app (F.obj X) := by
        apply (cancel_epi (ε.hom.app (F.obj X))).mp
        rw [h, ε.hom_inv_id_app]
        rfl
      change F.map (η.inv.app X) ≫ ε.inv.app (F.obj X) = 𝟙 (F.obj X)
      rw [← h', ← F.map_comp, η.inv_hom_id_app, F.map_id]
      rfl⟩
  exact ⟨hA, hF, e, rfl, rfl⟩

private def tensorBidual (E : ResidueFieldEnvelope S)
    (X : Type v) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    S ⊗[R] X ≃ₗ[S]
      MatlisDualModule (restrictResidueFieldEnvelope E)
        (MatlisDualModule (restrictResidueFieldEnvelope E) X) := by
  let B := S ⊗[R] X
  let D := MatlisDualModule E B
  letI : Module R D := Module.compHom D (algebraMap R S)
  letI : IsScalarTower R S D := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hD : IsPowerTorsion R D := restrictedPowerTorsion (matlisDual_isArtinian_of_finite E B)
  let d := completedHullHomAdjunction E X
  exact (LinearEquiv.ofBijective (matlisEvaluation E B)
    (matlisEvaluation_bijective_of_finite E B)).trans
    ((powerTorsionHomEquiv hD).trans
      (LinearEquiv.congrLeft E.carrier S (d.restrictScalars R).symm))

private theorem tensorBidual_tmul (E : ResidueFieldEnvelope S)
    {X : Type v} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (s : S) (x : X) (g : MatlisDualModule (restrictResidueFieldEnvelope E) X) :
    tensorBidual E X (s ⊗ₜ[R] x) g = s • g x :=
  rfl

private def transportedTensorBidual (E : ResidueFieldEnvelope S) (F : ResidueFieldEnvelope R)
    (e : (restrictResidueFieldEnvelope E).carrier ≃ₗ[R] F.carrier)
    (X : Type v) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    S ⊗[R] X ≃ₗ[R] MatlisDualModule F (MatlisDualModule F X) :=
  ((tensorBidual E X).restrictScalars R).trans
    (LinearEquiv.arrowCongr (LinearEquiv.congrRight (M := X) e) e)

private theorem transportedTensorBidual_tmul (E : ResidueFieldEnvelope S)
    (F : ResidueFieldEnvelope R)
    (e : (restrictResidueFieldEnvelope E).carrier ≃ₗ[R] F.carrier)
    {X : Type v} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (s : S) (x : X) (g : MatlisDualModule F X) :
    transportedTensorBidual E F e X (s ⊗ₜ[R] x) g = e (s • e.symm (g x)) := by
  change e (tensorBidual E X (s ⊗ₜ[R] x) ((LinearEquiv.congrRight (M := X) e).symm g)) = _
  rw [tensorBidual_tmul]
  rfl

private theorem transportedTensorBidual_naturality (E : ResidueFieldEnvelope S)
    (F : ResidueFieldEnvelope R)
    (e : (restrictResidueFieldEnvelope E).carrier ≃ₗ[R] F.carrier)
    {X Y : Type v} [AddCommGroup X] [Module R X] [Module.Finite R X]
    [AddCommGroup Y] [Module R Y] [Module.Finite R Y] (f : X →ₗ[R] Y) (t : S ⊗[R] X) :
    transportedTensorBidual E F e Y (f.baseChange S t) =
      matlisDualMap F (matlisDualMap F f) (transportedTensorBidual E F e X t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s x =>
    apply LinearMap.ext
    intro g
    rw [LinearMap.baseChange_tmul, transportedTensorBidual_tmul]
    change e (s • e.symm (g (f x))) =
      transportedTensorBidual E F e X (s ⊗ₜ[R] x) (matlisDualMap F f g)
    rw [transportedTensorBidual_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor description also applies when the finite module is in a different
universe from the ring, since a finite module can be shrunk to the ring's universe. -/
private theorem completionTensor_bijective (X : Type v) [AddCommGroup X] [Module R X]
    [Module.Finite R X] :
    Function.Bijective (AdicCompletion.ofTensorProduct (maximalIdeal R) X) := by
  let : Small.{u} X := Module.Finite.small R X
  let d := (Shrink.linearEquiv.{u} R X).symm
  let b := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) d
  let 𝔪 := maximalIdeal R
  have hn (x : S ⊗[R] X) :
      AdicCompletion.map 𝔪 d.toLinearMap (AdicCompletion.ofTensorProduct 𝔪 X x) =
        AdicCompletion.ofTensorProduct 𝔪 (Shrink.{u} X) (b x) :=
    DFunLike.congr_fun (AdicCompletion.ofTensorProduct_naturality 𝔪 d.toLinearMap) x
  refine ⟨fun x y h => b.injective ?_, AdicCompletion.ofTensorProduct_surjective_of_finite 𝔪 X⟩
  apply (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian 𝔪
    (Shrink.{u} X)).injective
  rw [← hn x, ← hn y, h]

/-- The original-ring Matlis bidual of each finite module is naturally its
adic completion, with evaluation corresponding to the canonical completion map. -/
theorem matlisBidualCompletion : MatlisDualityAfterCompletionSpecs.matlisBidualCompletion.{u, v} := by
  intro R _ _ _ F
  let 𝔪 := maximalIdeal R
  obtain ⟨E⟩ := residueFieldEnvelope_exists (Completion R)
  obtain ⟨e, _⟩ := residueFieldEnvelope_equiv (restrictResidueFieldEnvelope E) F
  let t (X : Type v) [AddCommGroup X] [Module R X] [Module.Finite R X] :=
    transportedTensorBidual E F e X
  let c (X : Type v) [AddCommGroup X] [Module R X] [Module.Finite R X] :=
    (LinearEquiv.ofBijective (AdicCompletion.ofTensorProduct 𝔪 X)
      (completionTensor_bijective X)).restrictScalars R
  refine ⟨fun X _ _ _ => (t X).symm.trans (c X), ?_, ?_⟩
  · intro X _ _ _ x
    have hx : t X ((1 : Completion R) ⊗ₜ[R] x) = matlisEvaluation F X x := by
      apply LinearMap.ext
      intro g
      rw [transportedTensorBidual_tmul, one_smul, LinearEquiv.apply_symm_apply]
      rfl
    change c X ((t X).symm (matlisEvaluation F X x)) = _
    rw [← hx, LinearEquiv.symm_apply_apply]
    exact (AdicCompletion.ofTensorProduct_tmul 𝔪 X (1 : Completion R) x).trans (one_smul _ _)
  · intro X Y _ _ _ _ _ _ f z
    let w := (t X).symm z
    have hz : t X w = z := (t X).apply_symm_apply z
    have hn : t Y (f.baseChange (Completion R) w) = matlisDualMap F (matlisDualMap F f) z :=
      (transportedTensorBidual_naturality E F e f w).trans (congrArg _ hz)
    change c Y ((t Y).symm (matlisDualMap F (matlisDualMap F f) z)) =
      AdicCompletion.map 𝔪 f (c X w)
    rw [← hn, LinearEquiv.symm_apply_apply]
    exact (DFunLike.congr_fun (AdicCompletion.ofTensorProduct_naturality 𝔪 f) w).symm

end CommutativeAlgebraNotes
