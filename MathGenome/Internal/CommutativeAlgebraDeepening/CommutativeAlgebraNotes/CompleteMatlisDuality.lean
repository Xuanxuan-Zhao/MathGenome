import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteMatlisDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ArtinianSocleCriterion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.EndomorphismsOfResidueHull
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualExactDetection
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Matlis duality over a complete Noetherian local ring. -/

noncomputable section

open CategoryTheory Opposite

namespace CommutativeAlgebraNotes

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (E : ResidueFieldEnvelope R)

section Noetherian

variable [IsNoetherianRing R]

/-- The Matlis dual of a finite module is Artinian. -/
theorem matlisDual_isArtinian_of_finite (X : Type v) [AddCommGroup X] [Module R X]
    [Module.Finite R X] : IsArtinian R (MatlisDualModule E X) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R X
  let : IsArtinian R E.carrier := residueHull_isArtinian E
  let e : MatlisDualModule E (Fin n → R) ≃ₗ[R] (Fin n → E.carrier) :=
    LinearEquiv.piRing R E.carrier (Fin n) R
  exact isArtinian_of_injective (e.toLinearMap.comp (matlisDualMap E f))
    (e.injective.comp (LinearMap.lcomp_injective_of_surjective f hf))

private theorem exists_hullPower_embedding_of_artinian (X : Type u) [AddCommGroup X]
    [Module R X] [IsArtinian R X] :
    ∃ (n : ℕ) (f : X →ₗ[R] (Fin n → E.carrier)), Function.Injective f := by
  have ht := idealTorsion_eq_top_of_isArtinian (R := R) (T := X)
  obtain ⟨f, hf, _⟩ := exists_residueHullPower_embedding E ht
    ((isArtinian_iff_socle_finiteDimensional ht).mp inferInstance)
  exact ⟨_, f, hf⟩

section Complete

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

private def hullScalarEquiv : R ≃ₐ[R] Module.End R E.carrier :=
  (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal R)).trans (residueHullEndomorphismEquiv E)

private theorem hullScalarEquiv_apply (r : R) (x : E.carrier) :
    hullScalarEquiv E r x = r • x := by
  have h := (hullScalarEquiv E).commutes r
  exact DFunLike.congr_fun h x

/-- Over a complete ring the Matlis dual of an Artinian module is finite. -/
theorem matlisDual_finite_of_isArtinian (X : Type u) [AddCommGroup X] [Module R X]
    [IsArtinian R X] : Module.Finite R (MatlisDualModule E X) := by
  obtain ⟨n, f, hf⟩ := exists_hullPower_embedding_of_artinian E X
  let e : (Fin n → R) ≃ₗ[R] MatlisDualModule E (Fin n → E.carrier) :=
    (LinearEquiv.piCongrRight fun _ => (hullScalarEquiv E).toLinearEquiv).trans
      (LinearMap.lsum R (fun _ : Fin n => E.carrier) R)
  exact Module.Finite.of_surjective ((matlisDualMap E f).comp e.toLinearMap)
    ((matlisDualMap_surjective E f hf).comp e.surjective)

private theorem matlisEvaluation_ring_surjective :
    Function.Surjective (matlisEvaluation E R) := by
  let d : MatlisDualModule E R ≃ₗ[R] E.carrier := LinearMap.ringLmapEquivSelf R R E.carrier
  let e : R ≃ₗ[R] MatlisDualModule E (MatlisDualModule E R) :=
    (hullScalarEquiv E).toLinearEquiv.trans (LinearEquiv.congrLeft E.carrier R d.symm)
  have h : matlisEvaluation E R = e.toLinearMap := by
    apply LinearMap.ext fun r => LinearMap.ext fun f => ?_
    change f r = hullScalarEquiv E r (f 1)
    rw [hullScalarEquiv_apply, ← map_smul, smul_eq_mul, mul_one]
  rw [h]
  exact e.surjective

private theorem matlisEvaluation_hull_surjective :
    Function.Surjective (matlisEvaluation E E.carrier) := by
  let d : MatlisDualModule E R ≃ₗ[R] E.carrier := LinearMap.ringLmapEquivSelf R R E.carrier
  let e : E.carrier ≃ₗ[R] MatlisDualModule E (MatlisDualModule E E.carrier) :=
    d.symm.trans (LinearEquiv.congrLeft E.carrier R (hullScalarEquiv E).toLinearEquiv)
  have h : matlisEvaluation E E.carrier = e.toLinearMap := by
    apply LinearMap.ext fun x => LinearMap.ext fun f => ?_
    change f x = (hullScalarEquiv E).symm f • x
    exact (DFunLike.congr_fun ((hullScalarEquiv E).apply_symm_apply f) x).symm.trans
      (hullScalarEquiv_apply E _ _)
  rw [h]
  exact e.surjective

end Complete

end Noetherian
private theorem matlisEvaluation_power_surjective {X : Type v} [AddCommGroup X] [Module R X]
    (hX : Function.Surjective (matlisEvaluation E X)) (n : ℕ) :
    Function.Surjective (matlisEvaluation E (Fin n → X)) := by
  classical
  let L : (Fin n → MatlisDualModule E X) ≃ₗ[R] MatlisDualModule E (Fin n → X) :=
    LinearMap.lsum R (fun _ : Fin n => X) R
  let K : (Fin n → MatlisDualModule E (MatlisDualModule E X)) ≃ₗ[R]
      MatlisDualModule E (Fin n → MatlisDualModule E X) :=
    LinearMap.lsum R (fun _ : Fin n => MatlisDualModule E X) R
  intro z
  obtain ⟨g, hg⟩ := K.surjective (z.comp L.toLinearMap)
  choose x hx using fun i => hX (g i)
  refine ⟨x, LinearMap.ext fun f => ?_⟩
  obtain ⟨f, rfl⟩ := L.surjective f
  change L f x = (z.comp L.toLinearMap) f
  rw [← hg]
  simp only [L, K, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, ← hx, matlisEvaluation_apply]

section Evaluation

variable {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

private theorem matlisEvaluation_naturality_apply (f : X →ₗ[R] Y) (x : X) :
    matlisDualMap E (matlisDualMap E f) (matlisEvaluation E X x) =
      matlisEvaluation E Y (f x) := by
  ext g
  rfl

private theorem matlisEvaluation_surjective_of_surjective (f : X →ₗ[R] Y)
    (hf : Function.Surjective f) (hX : Function.Surjective (matlisEvaluation E X)) :
    Function.Surjective (matlisEvaluation E Y) := by
  intro z
  obtain ⟨w, rfl⟩ := matlisDualMap_surjective E (matlisDualMap E f)
    (LinearMap.lcomp_injective_of_surjective f hf) z
  obtain ⟨x, rfl⟩ := hX w
  exact ⟨f x, (matlisEvaluation_naturality_apply E f x).symm⟩

private theorem matlisEvaluation_surjective_of_injective (f : X →ₗ[R] Y)
    (hf : Function.Injective f) (hY : Function.Surjective (matlisEvaluation E Y)) :
    Function.Surjective (matlisEvaluation E X) := by
  -- The bidual of the embedding is the kernel of the bidual of this quotient.
  let q := f.range.mkQ
  have he : Function.Exact f q := LinearMap.exact_map_mkQ_range f
  obtain ⟨hi, he', hs⟩ := matlisDualMap_shortExact E f q hf he f.range.mkQ_surjective
  obtain ⟨hi', he'', _⟩ := matlisDualMap_shortExact E _ _ hi he' hs
  intro z
  obtain ⟨y, hy⟩ := hY (matlisDualMap E (matlisDualMap E f) z)
  have hq : q y = 0 := by
    apply matlisEvaluation_injective E _
    rw [← matlisEvaluation_naturality_apply E q, hy, map_zero]
    exact (he'' _).mpr ⟨z, rfl⟩
  obtain ⟨x, hx⟩ := (he y).mp hq
  refine ⟨x, hi' ?_⟩
  rw [matlisEvaluation_naturality_apply, hx, hy]

end Evaluation

variable [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- The canonical evaluation of a finite module into its Matlis bidual is bijective. -/
theorem matlisEvaluation_bijective_of_finite (X : Type v) [AddCommGroup X] [Module R X]
    [Module.Finite R X] : Function.Bijective (matlisEvaluation E X) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R X
  exact ⟨matlisEvaluation_injective E X, matlisEvaluation_surjective_of_surjective E f hf
    (matlisEvaluation_power_surjective E (matlisEvaluation_ring_surjective E) n)⟩

/-- The canonical evaluation of an Artinian module into its Matlis bidual is bijective. -/
theorem matlisEvaluation_bijective_of_isArtinian (X : Type u) [AddCommGroup X] [Module R X]
    [IsArtinian R X] : Function.Bijective (matlisEvaluation E X) := by
  obtain ⟨n, f, hf⟩ := exists_hullPower_embedding_of_artinian E X
  exact ⟨matlisEvaluation_injective E X, matlisEvaluation_surjective_of_injective E f hf
    (matlisEvaluation_power_surjective E (matlisEvaluation_hull_surjective E) n)⟩

open CompleteMatlisDualitySpecs in
/-- The restricted Matlis duals give an anti-equivalence, with evaluation as the
bidual isomorphism on both full subcategories. -/
theorem completeMatlisDuality : CompleteMatlisDualitySpecs.completeMatlisDuality.{u} := by
  intro R _ _ _ _ E
  let hF (X : (finiteModules R).FullSubcategory) :
      IsArtinian R (MatlisDualModule E X.obj) :=
    let : Module.Finite R X.obj := X.property
    matlisDual_isArtinian_of_finite E X.obj
  let hA (Y : (artinianModules R).FullSubcategory) :
      Module.Finite R (MatlisDualModule E Y.obj) :=
    let : IsArtinian R Y.obj := Y.property
    matlisDual_finite_of_isArtinian E Y.obj
  let F := finiteDual E hF
  let G := artinianDual E hA
  let η : F ⋙ G.rightOp ≅ 𝟭 _ :=
    NatIso.ofComponents (fun X =>
      let : Module.Finite R X.unop.obj := X.unop.property
      ((finiteModules R).isoMk
        (LinearEquiv.ofBijective (matlisEvaluation E X.unop.obj)
          (matlisEvaluation_bijective_of_finite E X.unop.obj)).toModuleIso).op)
      (by
        intro X Y f
        apply Quiver.Hom.unop_inj
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => LinearMap.ext fun g => rfl)
  let ε : 𝟭 _ ≅ G.rightOp ⋙ F :=
    NatIso.ofComponents (fun Y =>
      let : IsArtinian R Y.obj := Y.property
      (artinianModules R).isoMk
        (LinearEquiv.ofBijective (matlisEvaluation E Y.obj)
          (matlisEvaluation_bijective_of_isArtinian E Y.obj)).toModuleIso)
      (by
        intro X Y f
        apply ObjectProperty.hom_ext
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => LinearMap.ext fun g => rfl)
  let e : (finiteModules R).FullSubcategoryᵒᵖ ≌ (artinianModules R).FullSubcategory :=
    ⟨F, G.rightOp, η.symm, ε.symm, fun X => by
      -- Evaluating a functional at an evaluation map recovers the functional.
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
  exact ⟨hF, hA, e, rfl, rfl, fun _ => HEq.rfl, fun _ => HEq.rfl⟩

end CommutativeAlgebraNotes
