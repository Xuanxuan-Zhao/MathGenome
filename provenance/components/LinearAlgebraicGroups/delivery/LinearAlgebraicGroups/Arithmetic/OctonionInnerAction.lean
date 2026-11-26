import Specs.LinearAlgebraicGroups.Arithmetic.OctonionInnerAction
import LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import Batteries.Tactic.OpenPrivate

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.OctonionInnerAction

open _root_.LinearAlgebraicGroups.Specs (GroupScheme OctonionInnerAction)
open Specs.AutomorphismSequence
open Specs.RelativeFormComparison
open Descent (SemilinearAction)
open _root_.LinearAlgebraicGroups.Composition (Zorn octonion_automorphism_invariance)
open Composition.Specification (normBaseChange)
open Composition.PeirceSpecification (tensorMap)
open Composition.OctonionAutomorphismSpecification (AutomorphismGroup)
open private innerAut_mul restrict_innerAut from
  LinearAlgebraicGroups.Descent.AutomorphismSequence
open private octonionAlgebra_preserves_iff subgroup_scalarChange from
  LinearAlgebraicGroups.Composition.OctonionAutomorphisms

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem restrictIso_identity {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K)) :
    restrictIso (𝟙 (fieldTest k K)) i = i := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  rcases U with ⟨⟨X, ⟨⟨⟩⟩, f⟩⟩
  change i.hom.app (op (Over.mk (f ≫ 𝟙 _))) = i.hom.app (op (Over.mk f))
  rw [Category.comp_id]

private theorem restrictIso_compose {G H : GroupScheme k}
    (a b : fieldTest k K ⟶ fieldTest k K)
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K)) :
    restrictIso (a ≫ b) i = restrictIso a (restrictIso b i) := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  change i.hom.app (op (Over.mk (U.unop.hom ≫ (a ≫ b)))) =
    i.hom.app (op (Over.mk ((U.unop.hom ≫ a) ≫ b)))
  rw [Category.assoc]

private theorem transported_one {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K)) :
    transportedAut k K i 1 = 1 := by
  apply Aut.ext
  change restrictIso (fieldMap k K 1) i ≪≫ i.symm = Iso.refl _
  rw [fieldMap_one, restrictIso_identity, Iso.self_symm_id]

private theorem transported_mul {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (σ τ : Gal(K/k)) :
    transportedAut k K i (σ * τ) =
      transportedAut k K i σ * restrictAut (fieldMap k K σ) (transportedAut k K i τ) := by
  apply Aut.ext
  let f := fieldMap k K σ
  change restrictIso (fieldMap k K (σ * τ)) i ≪≫ i.symm =
    restrictIso f (restrictIso (fieldMap k K τ) i ≪≫ i.symm) ≪≫
      (restrictIso f i ≪≫ i.symm)
  rw [fieldMap_mul, restrictIso_compose]
  change restrictIso f (restrictIso (fieldMap k K τ) i) ≪≫ i.symm =
    (restrictIso f (restrictIso (fieldMap k K τ) i) ≪≫ (restrictIso f i).symm) ≪≫
      (restrictIso f i ≪≫ i.symm)
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem inner_one (G : GroupScheme k) :
    innerAut (1 : fieldTest k K ⟶ G.X) = 1 := by
  have h := innerAut_mul (G := G) (1 : fieldTest k K ⟶ G.X) 1
  exact mul_left_cancel (by simpa only [mul_one] using h.symm)

private abbrev SplitSpace (k K : Type u) [Field k] [Field K] [Algebra k K] :=
  K ⊗[k] Zorn k

private abbrev coefficient (σ : Gal(K/k)) : SplitSpace k K ≃+ SplitSpace k K :=
  (SemilinearAction.scalarExtension (K := K) (Zorn k)).act σ

private theorem coefficient_eq_tensorMap (σ : Gal(K/k)) (x : SplitSpace k K) :
    coefficient σ x = tensorMap σ.toAlgHom x := by
  induction x using TensorProduct.inductionOn with
  | tmul s z => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem coefficient_mul (σ : Gal(K/k)) (x y : SplitSpace k K) :
    coefficient σ (x * y) = coefficient σ x * coefficient σ y := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  | tmul s z =>
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
    | tmul t w =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      change σ (s * t) ⊗ₜ[k] (z * w) = (σ s ⊗ₜ[k] z) * (σ t ⊗ₜ[k] w)
      rw [Algebra.TensorProduct.tmul_mul_tmul, map_mul]

private theorem coefficient_norm (σ : Gal(K/k)) (x : SplitSpace k K) :
    normBaseChange K (Composition.ZornSpecification.norm k) (coefficient σ x) =
      σ (normBaseChange K (Composition.ZornSpecification.norm k) x) := by
  have hq : normBaseChange K (Composition.ZornSpecification.norm k) =
      (Zorn.norm K).comp (Zorn.baseChange k K).toLinearMap := Zorn.baseChange_norm
  rw [hq, coefficient_eq_tensorMap]
  change Composition.ZornSpecification.norm K (Zorn.baseChange k K (tensorMap σ.toAlgHom x)) =
    σ (Composition.ZornSpecification.norm K (Zorn.baseChange k K x))
  rw [Composition.Peirce.zorn_baseChange_naturality]
  exact Zorn.mapCoordinates_norm σ.toRingHom _

private abbrev representation (A₀ : AutomorphismGroup k (Zorn k)) :
    (fieldTest k K ⟶ A₀.group.X) →* (Module.End K (SplitSpace k K))ˣ :=
  (Subgroup.subtype _).comp (A₀.subgroupPoints (CommAlgCat.of k K)).toMonoidHom

private theorem coefficient_intertwines (A₀ : AutomorphismGroup k (Zorn k))
    (σ : Gal(K/k)) (g : fieldTest k K ⟶ A₀.group.X) (x : SplitSpace k K) :
    coefficient σ ((representation A₀ g).val x) =
      (representation A₀ (fieldMap k K σ ≫ g)).val (coefficient σ x) := by
  rw [coefficient_eq_tensorMap, coefficient_eq_tensorMap]
  exact (subgroup_scalarChange A₀ (CommAlgCat.ofHom σ.toAlgHom) g x).symm

private def twistedAction (A₀ : AutomorphismGroup k (Zorn k))
    (c : Gal(K/k) → (fieldTest k K ⟶ A₀.group.X))
    (h₁ : c 1 = 1) (hm : ∀ σ τ, c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ)) :
    SemilinearAction k K (SplitSpace k K) where
  act σ := (coefficient σ).trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv (representation A₀ (c σ))).toAddEquiv
  one_act x := by
    change (representation A₀ (c 1)).val (coefficient 1 x) = x
    rw [h₁, map_one, (SemilinearAction.scalarExtension (K := K) (Zorn k)).one_act]
    rfl
  mul_act σ τ x := by
    change (representation A₀ (c (σ * τ))).val (coefficient (σ * τ) x) =
      (representation A₀ (c σ)).val (coefficient σ ((representation A₀ (c τ)).val
        (coefficient τ x)))
    rw [hm, map_mul, (SemilinearAction.scalarExtension (K := K) (Zorn k)).mul_act,
      coefficient_intertwines A₀ σ (c τ)]
    rfl
  map_smul σ a x := by
    change (representation A₀ (c σ)).val (coefficient σ (a • x)) =
      σ a • (representation A₀ (c σ)).val (coefficient σ x)
    rw [(SemilinearAction.scalarExtension (K := K) (Zorn k)).map_smul, map_smul]

/-- The normalized inner cocycle acts semilinearly on the Zorn algebra,
preserving its unit, multiplication and scalar-extended norm. -/
theorem octonionInnerAction : OctonionInnerAction.{u} := by
  intro k K _ _ _ _ _ A₀ H i c hc
  have h₁ : c 1 = 1 := by
    symm
    apply (hc 1).2
    rw [inner_one, transported_one]
  have hm (σ τ : Gal(K/k)) : c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ) := by
    symm
    apply (hc (σ * τ)).2
    rw [innerAut_mul, ← restrict_innerAut, (hc σ).1, (hc τ).1, transported_mul]
  have hpres (σ : Gal(K/k)) :
      (representation A₀ (c σ)).val 1 = 1 ∧
      ∀ x y, (representation A₀ (c σ)).val (x * y) =
        (representation A₀ (c σ)).val x * (representation A₀ (c σ)).val y :=
    (octonionAlgebra_preserves_iff K _).mp
      (A₀.subgroupPoints (CommAlgCat.of k K) (c σ)).property
  refine ⟨h₁, hm, twistedAction A₀ c h₁ hm, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro σ
    change (representation A₀ (c σ)).val (coefficient σ 1) = 1
    change (representation A₀ (c σ)).val (σ 1 ⊗ₜ[k] (1 : Zorn k)) = 1
    rw [map_one]
    exact (hpres σ).1
  · intro σ x y
    change (representation A₀ (c σ)).val (coefficient σ (x * y)) =
      (representation A₀ (c σ)).val (coefficient σ x) *
        (representation A₀ (c σ)).val (coefficient σ y)
    rw [coefficient_mul, (hpres σ).2]
  · intro σ x
    let f := LinearMap.GeneralLinearGroup.toLinearEquiv (representation A₀ (c σ))
    have hf := (octonion_automorphism_invariance (Zorn.isOctonion k) K f
      (hpres σ).1 (hpres σ).2).1
    change normBaseChange K (Composition.ZornSpecification.norm k) (f (coefficient σ x)) =
      σ (normBaseChange K (Composition.ZornSpecification.norm k) x)
    have hx := congrArg (fun q : QuadraticForm K (SplitSpace k K) => q (coefficient σ x)) hf
    exact hx.trans (coefficient_norm σ x)

end

end LinearAlgebraicGroups.Arithmetic.OctonionInnerAction
