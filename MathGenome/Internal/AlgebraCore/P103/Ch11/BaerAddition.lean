import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.BaerAddition
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtensionClassification
import Mathlib.Algebra.Group.TransferInstance

namespace P103.Ch11.BaerAddition
open CategoryTheory
open P103.Specs.Ch11.ExtensionClassification P103.Specs.Ch11.BaerAddition
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
open P103.Ch11.ExtensionClassification
noncomputable section
universe u v
variable {R : Type u} [Ring R] {A B : ModuleCat.{v} R}

theorem directSum_exact (E F : Extension A B) : (directSumData E F).IsShortExact := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    exact Prod.ext (E.injective (congrArg Prod.fst h)) (F.injective (congrArg Prod.snd h))
  · intro x
    change (E.p x.1, F.p x.2) = 0 ↔ ∃ b : B × B, (E.i b.1, F.i b.2) = x
    constructor
    · intro h
      obtain ⟨b, hb⟩ := (E.exact x.1).mp (congrArg Prod.fst h)
      obtain ⟨c, hc⟩ := (F.exact x.2).mp (congrArg Prod.snd h)
      exact ⟨(b,c), Prod.ext hb hc⟩
    · rintro ⟨b, rfl⟩
      exact Prod.ext ((E.exact _).mpr ⟨b.1,rfl⟩) ((F.exact _).mpr ⟨b.2,rfl⟩)
  · intro a
    obtain ⟨x,hx⟩ := E.surjective a.1
    obtain ⟨y,hy⟩ := F.surjective a.2
    exact ⟨(x,y), Prod.ext hx hy⟩

def diagonalPullback (E F : Extension A B) :
    Extension A (ModuleCat.of R (B × B)) :=
  ⟨pullbackData ⟨directSumData E F, directSum_exact E F⟩ (diagonal A),
    pullback_exact _ _⟩

def baerExtension (E F : Extension A B) : Extension A B :=
  ⟨pushoutData (diagonalPullback E F) (addition B), pushout_exact _ _⟩

theorem baerExtension_spec (E F : Extension A B) : IsBaerSum E F (baerExtension E F) :=
  ⟨directSum_exact E F, pullback_exact _ _, rfl⟩

theorem baerSum_unique (E F G : Extension A B) (h : IsBaerSum E F G) :
    G = baerExtension E F := by
  obtain ⟨h,k,hG⟩ := h
  apply Subtype.ext
  exact hG

theorem baer_exact : baer_exactType.{u,v} := by
  intro R _ A B E F
  exact ⟨baerExtension E F, baerExtension_spec E F⟩

/-- Paired lifts into the diagonal pullback. -/
def pairedLift (S : Presentation A) (E F : Extension A B)
    (l : S.P →ₗ[R] E.middle) (l' : S.P →ₗ[R] F.middle)
    (φ φ' : S.K →ₗ[R] B)
    (hl : IsLiftRepresentative S E l φ) (hl' : IsLiftRepresentative S F l' φ') :
    S.P →ₗ[R] (diagonalPullback E F).middle :=
  ((l.prod l').prod S.ε).codRestrict _ (by
    intro p
    change (E.p (l p), F.p (l' p)) - (S.ε p, S.ε p) = 0
    rw [show E.p (l p) = S.ε p from LinearMap.congr_fun hl.1 p,
      show F.p (l' p) = S.ε p from LinearMap.congr_fun hl'.1 p, sub_self])

theorem pairedLift_spec (S : Presentation A) (E F : Extension A B)
    (l : S.P →ₗ[R] E.middle) (l' : S.P →ₗ[R] F.middle)
    (φ φ' : S.K →ₗ[R] B)
    (hl : IsLiftRepresentative S E l φ) (hl' : IsLiftRepresentative S F l' φ') :
    IsLiftRepresentative S (diagonalPullback E F) (pairedLift S E F l l' φ φ' hl hl')
      (φ.prod φ') := by
  constructor
  · ext p
    rfl
  · ext k
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (LinearMap.congr_fun hl.2 k) (LinearMap.congr_fun hl'.2 k)
    · change 0 = S.ε (S.j k)
      exact ((S.exact _).mpr ⟨k,rfl⟩).symm

theorem representatives : representativesType.{u,v} := by
  intro R _ A B S E F G l l' φ φ' hl hl' hG
  have heq := baerSum_unique E F G hG
  subst G
  let D := diagonalPullback E F
  let L := pairedLift S E F l l' φ φ' hl hl'
  have hL := pairedLift_spec S E F l l' φ φ' hl hl'
  refine ⟨(intoPushout D (addition B)).comp L, ?_, ?_⟩
  · ext p
    have hs := (pushout_squares D (addition B)).2
    exact (LinearMap.congr_fun hs (L p)).trans (LinearMap.congr_fun hL.1 p)
  · ext k
    have hs := LinearMap.congr_fun (pushout_squares D (addition B)).1 ((φ.prod φ') k)
    have hk := LinearMap.congr_fun hL.2 k
    exact hs.symm.trans (congrArg (intoPushout D (addition B)) hk)

theorem group_classification : group_classificationType.{u,v} := by
  intro R _ A B Q hQ
  obtain ⟨e, he, hz, hc⟩ := classification R A B Q hQ
  letI g : AddCommGroup (ExtensionClasses A B) := e.addCommGroup
  let ea : ExtensionClasses A B ≃+ ExtWith Q B 1 := e.addEquiv
  refine ⟨g, ea, he, ?_, ?_, ?_⟩
  · intro E F G hG
    let S := resolutionPresentation Q hQ
    obtain ⟨c, _, hf, _⟩ := hc S
    obtain ⟨l, φ, hl⟩ := (lift_representatives R A B S E).1
    obtain ⟨l', φ', hl'⟩ := (lift_representatives R A B S F).1
    obtain ⟨L, hL⟩ := representatives R A B S E F G l l' φ φ' hl hl' hG
    apply ea.injective
    rw [map_add]
    change e (extensionClass G) = e (extensionClass E) + e (extensionClass F)
    rw [hf G L (φ + φ') hL, hf E l φ hl, hf F l' φ' hl']
    change c ((LinearMap.range (restriction S B)).mkQ (φ + φ')) =
      c ((LinearMap.range (restriction S B)).mkQ φ) +
      c ((LinearMap.range (restriction S B)).mkQ φ')
    rw [map_add, map_add]
  · intro E
    rw [← ea.map_eq_zero_iff]
    exact hz E
  · intro S
    obtain ⟨c, hc, hf, _⟩ := hc S
    exact ⟨c, hc, hf⟩

theorem well_defined : well_definedType.{u,v} := by
  intro R _ A B E E' F F' G G' hE hF hG hG'
  obtain ⟨Q, hQ⟩ := P103.Ch10.ProjectiveResolutions.exists_projective_resolution R A
  obtain ⟨g, e, _, hsum, _, _⟩ := group_classification R A B Q hQ
  letI := g
  apply Quotient.exact (s := Extension.extensionSetoid (A := A) (B := B))
  change extensionClass G = extensionClass G'
  rw [hsum E F G hG, hsum E' F' G' hG']
  rw [show extensionClass E = extensionClass E' from Quotient.sound hE,
    show extensionClass F = extensionClass F' from Quotient.sound hF]

theorem additive_naturality : additive_naturalityType.{u,v} := by
  intro R _ A A' B B' Q Q' hQ hQ' T g gp gr
  letI := g
  letI := gp
  letI := gr
  intro e ep er he hep her β α
  obtain ⟨⟨push,hpush,hp⟩, ⟨pull,hpull,hr⟩⟩ :=
    naturality R A A' B B' Q Q' hQ hQ' T e.toEquiv ep.toEquiv er.toEquiv he hep her β α
  constructor
  · let f : ExtensionClasses A B →+ ExtensionClasses A B' :=
      ep.symm.toAddMonoidHom.comp
        ((T.map ⟨Q,hQ⟩ ⟨Q,hQ⟩ (𝟙 A) β).toAddMonoidHom.comp e.toAddMonoidHom)
    have hf (x) : f x = push x := by
      apply ep.injective
      exact (ep.apply_symm_apply _).trans (hp x).symm
    refine ⟨f, ?_, ?_⟩
    · intro E
      obtain ⟨h, hh⟩ := hpush E
      exact ⟨h, (hf _).trans hh⟩
    · intro x
      exact ep.apply_symm_apply _
  · let f : ExtensionClasses A B →+ ExtensionClasses A' B :=
      er.symm.toAddMonoidHom.comp
        ((T.map ⟨Q,hQ⟩ ⟨Q',hQ'⟩ α (𝟙 B)).toAddMonoidHom.comp e.toAddMonoidHom)
    have hf (x) : f x = pull x := by
      apply er.injective
      exact (er.apply_symm_apply _).trans (hr x).symm
    refine ⟨f, ?_, ?_⟩
    · intro E
      obtain ⟨h, hh⟩ := hpull E
      exact ⟨h, (hf _).trans hh⟩
    · intro x
      exact er.apply_symm_apply _

theorem right_group_classification : right_group_classificationType.{u,v} := by
  intro R _
  exact group_classification Rᵐᵒᵖ

end
end P103.Ch11.BaerAddition
