import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerHullCriterion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SmallExtensionLiftFibers
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerProrepresentability
import Batteries.Tactic.OpenPrivate

/-! Schlessinger's prorepresentability criterion and its application to a given hull. -/

universe u w

namespace CommutativeAlgebraNotes.ArtinFunctor

open CategoryTheory LocalArtinAlgebra
open SchlessingerTangentVectorSpaceSpec SchlessingerSplitCorrectionsSpec
  SmallExtensionLiftFibersSpec SchlessingerProrepresentabilitySpec

open private representable_comparison_bijective Smooth.lift
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerConditionsFromHull

attribute [local instance] extensionKernelFinite

variable {k : Type u} [Field k] {F G : ArtinFunctor.{u,w} k}
  {A B C : LocalArtinAlgebra.{u,u} k}

private theorem component_bijective (τ : G.toFunctor ⟶ F.toFunctor) [IsIso τ]
    (A : LocalArtinAlgebra.{u,u} k) : Function.Bijective (τ.app A) :=
  (CategoryTheory.isIso_iff_bijective (τ.app A)).mp inferInstance

private theorem comparison_bijective_of_iso (τ : G.toFunctor ⟶ F.toFunctor) [IsIso τ]
    (f : Hom B A) (g : Hom C A) (hG : Function.Bijective (G.comparison f g)) :
    Function.Bijective (F.comparison f g) := by
  let p : CompatiblePairs (onHom G f) (onHom G g) →
      CompatiblePairs (onHom F f) (onHom F g) := fun x =>
    ⟨(τ.app B x.val.1, τ.app C x.val.2),
      ((ConcreteCategory.congr_hom (τ.naturality f) x.val.1).symm.trans
        (congrArg (τ.app A) x.property)).trans
          (ConcreteCategory.congr_hom (τ.naturality g) x.val.2)⟩
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      exact Subtype.ext (Prod.ext
        ((component_bijective τ B).injective (congrArg (fun t => t.val.1) hxy))
        ((component_bijective τ C).injective (congrArg (fun t => t.val.2) hxy)))
    · intro y
      obtain ⟨b, hb⟩ := (component_bijective τ B).surjective y.val.1
      obtain ⟨c, hc⟩ := (component_bijective τ C).surjective y.val.2
      have hbc : onHom G f b = onHom G g c := by
        apply (component_bijective τ A).injective
        exact (ConcreteCategory.congr_hom (τ.naturality f) b).trans
          ((congrArg (onHom F f) hb).trans (y.property.trans
            ((congrArg (onHom F g) hc).symm.trans
              (ConcreteCategory.congr_hom (τ.naturality g) c).symm)))
      exact ⟨⟨(b, c), hbc⟩, Subtype.ext (Prod.ext hb hc)⟩
  have hcomm (x : G.toFunctor.obj (pullback f g)) :
      F.comparison f g (τ.app (pullback f g) x) = p (G.comparison f g x) := by
    apply Subtype.ext
    apply Prod.ext
    · change onHom F (pullbackFst f g) (τ.app (pullback f g) x) =
        τ.app B (onHom G (pullbackFst f g) x)
      exact (ConcreteCategory.congr_hom (τ.naturality (pullbackFst f g)) x).symm
    · change onHom F (pullbackSnd f g) (τ.app (pullback f g) x) =
        τ.app C (onHom G (pullbackSnd f g) x)
      exact (ConcreteCategory.congr_hom (τ.naturality (pullbackSnd f g)) x).symm
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := (component_bijective τ (pullback f g)).surjective x
    obtain ⟨b, rfl⟩ := (component_bijective τ (pullback f g)).surjective y
    rw [hcomm, hcomm] at hxy
    exact congrArg (τ.app (pullback f g)) (hG.injective (hp.injective hxy))
  · intro y
    obtain ⟨p', rfl⟩ := hp.surjective y
    obtain ⟨x, rfl⟩ := hG.surjective p'
    exact ⟨τ.app (pullback f g) x, hcomm x⟩

private theorem h4_of_representing_iso (R : CompleteLocalAlgebra k)
    (τ : (R.representable : ArtinFunctor.{u,w} k).toFunctor ⟶ F.toFunctor)
    [IsIso τ] : F.H4 :=
  fun g _ => comparison_bijective_of_iso τ g g (representable_comparison_bijective R g g)

/-- Over a small extension, the hull induces a bijection of lift fibres. -/
private theorem liftFiber_bijective (h : F.Hull) (h₁ : F.H1) (h₂ : F.H2) (h₄ : F.H4)
    (g : Hom B A) (hg : SmallExtension g)
    (x : (CompleteLocalAlgebra.representable h.ring : ArtinFunctor.{u,w} k).toFunctor.obj A) :
    Function.Bijective (onLiftFiber h.transformation (g := g) (x := x)) := by
  let R := h.ring
  let P : ArtinFunctor.{u,w} k := CompleteLocalAlgebra.representable R
  let τ := h.transformation
  have hP₁ : P.H1 := fun f g _ => (representable_comparison_bijective R f g).surjective
  have hP₂ : P.H2 := fun A =>
    representable_comparison_bijective R (residueHom A) (residueHom (dualNumbers k))
  have hP₄ : P.H4 := fun g _ => representable_comparison_bijective R g g
  let lawsP := P.tangentVectorLaws hP₂
  let lawsF := F.tangentVectorLaws h₂
  let cP := P.splitTensorComparison hP₂ (ExtensionKernel g)
  let cF := F.splitTensorComparison h₂ (ExtensionKernel g)
  obtain ⟨DP⟩ := liftFiberCoordinates_exists P hP₁ hP₂ hP₄ g hg x lawsP cP
  obtain ⟨DF⟩ := liftFiberCoordinates_exists F h₁ h₂ h₄ g hg (τ.app A x) lawsF cF
  let := tangentAddCommGroupModel P lawsP
  let := tangentModuleModel P lawsP
  let := tangentAddCommGroupModel F lawsF
  let := tangentModuleModel F lawsF
  let l := P.tangentMap F τ hP₂ h₂
  have hl := P.tangentMap_apply F τ hP₂ h₂
  have hbij : Function.Bijective l := by
    constructor
    · intro s t hst
      apply h.tangent_bijective.injective
      exact (hl s).symm.trans (hst.trans (hl t))
    · intro t
      obtain ⟨s, hs⟩ := h.tangent_bijective.surjective t
      exact ⟨s, (hl s).trans hs⟩
  let e := TensorProduct.congr (LinearEquiv.ofBijective l hbij)
    (LinearEquiv.refl k (ExtensionKernel g))
  have hdiff := (liftFiberCoordinates_natural τ DP DF l hl).1
  constructor
  · intro y z hyz
    apply (DP.coordinates y).injective
    apply e.injective
    exact (hdiff y y).symm.trans ((congrArg
      (DF.coordinates (onLiftFiber τ y)) hyz).trans (hdiff y z))
  · intro y
    obtain ⟨b, hb, hy⟩ := Smooth.lift h.smooth g hg x y.val y.property.symm
    exact ⟨⟨b, hb⟩, Subtype.ext hy⟩

private theorem hull_injective_of_small (h : F.Hull) (h₁ : F.H1) (h₂ : F.H2) (h₄ : F.H4)
    (g : Hom B A) (hg : SmallExtension g) (hA : Function.Injective (h.transformation.app A)) :
    Function.Injective (h.transformation.app B) := by
  let P : ArtinFunctor.{u,w} k := CompleteLocalAlgebra.representable h.ring
  let τ := h.transformation
  intro b c hbc
  let x := onHom P g b
  have hc : onHom P g c = x := by
    apply hA
    exact (ConcreteCategory.congr_hom (τ.naturality g) c).trans
      ((congrArg (onHom F g) hbc.symm).trans
        (ConcreteCategory.congr_hom (τ.naturality g) b).symm)
  have hl : (⟨b, rfl⟩ : LiftFiber P g x) = ⟨c, hc⟩ :=
    (liftFiber_bijective h h₁ h₂ h₄ g hg x).injective (Subtype.ext hbc)
  exact congrArg Subtype.val hl

private theorem hull_injective_of_chain (h : F.Hull) (h₁ : F.H1) (h₂ : F.H2) (h₄ : F.H4)
    {g : Hom B A} {n : ℕ} (hg : SmallExtensionChain g n) :
    Function.Injective (h.transformation.app A) → Function.Injective (h.transformation.app B) := by
  induction hg with
  | @zero B A g hg =>
    intro hA b c hbc
    let P : ArtinFunctor.{u,w} k := CompleteLocalAlgebra.representable h.ring
    let τ := h.transformation
    have hmaps : onHom P g b = onHom P g c := hA
      ((ConcreteCategory.congr_hom (τ.naturality g) b).trans
        ((congrArg (onHom F g) hbc).trans
          (ConcreteCategory.congr_hom (τ.naturality g) c).symm))
    apply ULift.ext
    apply CompleteLocalAlgebra.Hom.ext
    intro r
    exact hg.injective (congrArg
      (fun a : P.toFunctor.obj A => (show CompleteLocalAlgebra.Hom h.ring A from a.down) r)
      hmaps)
  | single g hg => exact hull_injective_of_small h h₁ h₂ h₄ g hg
  | cons f _ hf _ ih => exact fun hA => hull_injective_of_small h h₁ h₂ h₄ f hf (ih hA)

private theorem hull_isIso_of_h4 (h : F.Hull) (h₁ : F.H1) (h₂ : F.H2) (h₄ : F.H4) :
    IsIso h.transformation := by
  let : ∀ B : LocalArtinAlgebra.{u,u} k, IsIso (h.transformation.app B) := fun B => by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    obtain ⟨_, hg⟩ := surjection_factors_smallExtensions (residueHom B) (residue_surjective B)
    exact ⟨hull_injective_of_chain h h₁ h₂ h₄ hg (fun _ _ _ => Subsingleton.elim _ _),
      hull_component_surjective h B⟩
  exact NatIso.isIso_of_isIso_app h.transformation

/-- The hull transformation itself is an isomorphism exactly under H4. -/
theorem hull_represents_iff : HullRepresentsIff.{u,w} := by
  intro k _ F h₁ h₂ _ h
  exact ⟨fun hi => h4_of_representing_iso h.ring h.transformation, hull_isIso_of_h4 h h₁ h₂⟩

/-- Prorepresentability implies H1–H4. The representing isomorphism is a hull,
so the finiteness assertion follows from the hull criterion. -/
theorem conditions_of_prorepresentable : ConditionsOfProrepresentable.{u,w} := by
  intro k _ F hF
  obtain ⟨R, ⟨e⟩⟩ := hF
  have smooth : Smooth e.hom := by
    intro A B g hg y
    obtain ⟨b, hb⟩ := (component_bijective e.hom B).surjective y.val.2
    refine ⟨b, Subtype.ext (Prod.ext ?_ hb)⟩
    apply (component_bijective e.hom A).injective
    exact (ConcreteCategory.congr_hom (e.hom.naturality g) b).trans
      ((congrArg (onHom F g) hb).trans y.property.symm)
  let h : Hull F := ⟨R, e.hom, component_bijective e.hom (dualNumbers k), smooth⟩
  obtain ⟨h₁, h₂, h₃⟩ := (has_hull_iff F).mp ⟨h⟩
  exact ⟨h₁, h₂, h₃, h4_of_representing_iso R e.hom⟩

end CommutativeAlgebraNotes.ArtinFunctor
