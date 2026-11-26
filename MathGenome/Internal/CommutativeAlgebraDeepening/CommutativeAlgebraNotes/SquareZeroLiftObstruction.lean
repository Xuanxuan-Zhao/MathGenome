import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SquareZeroLiftGraph
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftObstruction

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift.Presentation

open CategoryTheory Abelian Specs.CommutativeAlgebraNotes.SquareZeroLiftObstruction

universe u v w t n l s

variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}
  (p : Presentation e B σ) {c : e.CoefficientMap (B := B) N}

theorem factorsThrough_unique : factorsThroughUniqueType.{u,v,w,t,n} := by
  intro A' A B σ N _ _ _ _ _ _ e p c κ κ' h h'
  apply LinearMap.ext
  intro k
  obtain ⟨i, rfl⟩ := p.toK_surjective k
  exact (h i).trans (h' i).symm

private theorem nonempty_relationMaps_iff :
    Nonempty (p.RelationMaps c) ↔
      ∃ κ : p.K →ₗ[B] N, p.FactorsThrough c κ ∧ p.Extends κ := by
  constructor
  · rintro ⟨⟨ρ, hρ⟩⟩
    exact ⟨ρ.comp p.K.subtype, hρ, ⟨ρ, rfl⟩⟩
  · rintro ⟨κ, hκ, ρ, hρ⟩
    refine ⟨⟨ρ, fun i => ?_⟩⟩
    change (ρ.comp p.K.subtype) (p.toK i) = _
    rw [hρ]
    exact hκ i

theorem factorization_and_extension_of_lift : factorizationAndExtensionOfLiftType.{u,v,w,t,n,l} := by
  intro A' A B σ N _ _ _ _ _ _ e p c L
  exact p.nonempty_relationMaps_iff.mp ⟨(p.chooseVariables L).toRelationMaps⟩

/-- Giving every element of the target a variable gives a presentation of bounded universe. -/
private def presentationOnTarget : Presentation e B B where
  map := MvPolynomial.eval₂Hom ((algebraMap A B).comp e.hom) id
  over a := MvPolynomial.eval₂Hom_C _ _ a
  surjective b := ⟨MvPolynomial.X b, MvPolynomial.eval₂Hom_X' _ _ b⟩

theorem lift_iff_factorization_and_extension : liftIffFactorizationAndExtensionType.{u,v,w,t,n} := by
  intro A' A B σ N _ _ _ _ _ _ e p c
  constructor
  · rintro ⟨L⟩
    exact factorization_and_extension_of_lift p L
  · intro h
    obtain ⟨ρ⟩ := p.nonempty_relationMaps_iff.mpr h
    -- Rebuild the lift using variables indexed by B to remove the size of σ from the bound.
    let q : Presentation e B B := presentationOnTarget
    let L := (p.ofRelationMaps ρ).lift
    exact ⟨(q.ofRelationMaps (q.chooseVariables L).toRelationMaps).lift⟩

/-- Reduction kills precisely the image of the coefficient ideal, and is surjective. -/
theorem conormalSequence_shortExact : p.conormalSequence.{u,v,w,t,n}.ShortExact := by
  obtain ⟨hsurj, hker, _⟩ := conormalCokernel p
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change ULift.up (p.conormalReduction x.down) = ULift.up 0 ↔
      ∃ y : ULift.{max u w t n} p.K, ULift.up (y.down : p.Conormal) = x
    constructor
    · intro hx
      have hxK : x.down ∈ p.K := by
        rw [← hker]
        exact congrArg ULift.down hx
      exact ⟨ULift.up ⟨x.down, hxK⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact p.conormalSequence.{u,v,w,t,n}.zero_apply y
  · intro x y h
    exact ULift.ext (Subtype.ext (congrArg ULift.down h))
  · intro y
    obtain ⟨x, hx⟩ := hsurj y.down
    exact ⟨ULift.up x, ULift.ext hx⟩

theorem extension_iff_connectingClass_eq_zero :
    extensionIffConnectingClassEqZeroType.{u,v,w,t,n} := by
  intro A' A B σ N _ _ _ _ _ _ e p
  let S := p.conormalSequence.{u,v,w,t,n}
  let Y := ModuleCat.of B (ULift.{max u w t n} N)
  have hS : S.ShortExact := p.conormalSequence_shortExact
  refine ⟨hS, fun κ => ?_⟩
  let f : S.X₁ ⟶ Y := ModuleCat.ofHom (uliftLinearMap.{max u w t n} κ)
  change p.Extends κ ↔ Ext.δ hS 0 1 rfl (Ext.mk₀ f) = 0
  constructor
  · rintro ⟨ρ, hρ⟩
    let g : S.X₂ ⟶ Y := ModuleCat.ofHom (uliftLinearMap.{max u w t n} ρ)
    have hcomp : S.f ≫ g = f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg ULift.up (LinearMap.congr_fun hρ x.down)
    rw [← hcomp, ← Ext.mk₀_comp_mk₀, Ext.δ_apply, hS.extClass_comp_assoc, smul_zero]
  · intro h
    obtain ⟨x, hx⟩ := Ext.δ_exact₁ hS Y (Ext.mk₀ f) rfl h
    let g := Ext.addEquiv₀ x
    have hg : Ext.mk₀ g = x := Ext.mk₀_addEquiv₀_apply x
    rw [← hg, Ext.mk₀_comp_mk₀] at hx
    have hcomp : S.f ≫ g = f := Ext.addEquiv₀.symm.injective hx
    let ρ : p.Conormal →ₗ[B] N :=
      ULift.moduleEquiv.toLinearMap.comp (g.hom.comp ULift.moduleEquiv.symm.toLinearMap)
    refine ⟨ρ, LinearMap.ext fun k => ?_⟩
    exact congrArg (fun h : S.X₁ ⟶ Y => (h (ULift.up k)).down) hcomp

theorem lift_iff_factorization_and_vanishing : liftIffFactorizationAndVanishingType.{u,v,w,t,n} := by
  intro A' A B σ N _ _ _ _ _ _ e p c
  obtain ⟨hS, h⟩ := extension_iff_connectingClass_eq_zero (N := N) p
  refine ⟨hS, (lift_iff_factorization_and_extension p c).trans ?_⟩
  exact exists_congr fun κ => and_congr_right fun _ => h κ

theorem lift_criterion_independent : liftCriterionIndependentType.{u,v,w,t,s,n} := by
  intro A' A B σ τ N _ _ _ _ _ _ e p q c
  exact (lift_iff_factorization_and_extension p c).symm.trans
    (lift_iff_factorization_and_extension q c)

end CommutativeAlgebraNotes.SquareZeroLift.Presentation
