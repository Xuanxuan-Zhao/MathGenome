import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.RegularQuotientDuality
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KoszulRelativeDual
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.PerfectRelativeDual
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedScalarExtension

/-! Relative duality for the quotient by a regular sequence. -/

noncomputable section

namespace DerivedFormalization.RegularQuotientDuality

open CategoryTheory HomologicalComplex
open Specs.DerivedFormalization.Cochains (qValue stalkValue)
open Specs.DerivedFormalization.CochainCoefficientLift (liftDFactors)
open Specs.DerivedFormalization.DerivedCoinduction (comparison)
open Specs.DerivedFormalization.KoszulCochainResolution (augmentationValue cochainValue)
open Specs.DerivedFormalization.KoszulRelativeDual (liftedKoszul determinantDual)
open Specs.DerivedFormalization.PerfectComplex (isPerfectValue)
open Specs.DerivedFormalization.PerfectRelativeDual
  (algebraStalk source sourceModel targetAugmentation chainComparison)
open Specs.DerivedFormalization.RegularQuotientDuality
  (Duality IdentifiesDeterminant Realization determinantTensorComparison)
open AdvCommAlg.Koszul (listIdeal)

universe u v

attribute [local instance] HasDerivedCategory.standard

private theorem quotientPerfect {A : Type u} [CommRing A] (J : Ideal A)
    (a : List A) (h : listIdeal a = J) (ha : RingTheory.Sequence.IsRegular A a) :
    isPerfectValue ((qValue A).obj (algebraStalk.{u,u,v} (Ideal.Quotient.mk J))) := by
  subst J
  obtain ⟨haug, _, hterms, hbound⟩ := koszulCochain_finiteFree_resolution a ha
  let F := ModuleCat.uliftFunctor.{max u v,u} A
  let σ : (CochainCoefficientLift.lift.{max u v,u} A).obj
      ((stalkValue A).obj (ModuleCat.of A (A ⧸ listIdeal a))) ≅
      algebraStalk.{u,u,v} (Ideal.Quotient.mk (listIdeal a)) :=
    (singleMapHomologicalComplex F (.up ℤ) 0).app (ModuleCat.of A (A ⧸ listIdeal a))
  have hLift : QuasiIso ((CochainCoefficientLift.lift.{max u v,u} A).map (augmentationValue a)) :=
    (CochainCoefficientLift.quasiIso_iff (augmentationValue a)).2 haug
  let p : liftedKoszul.{u,max u v} a ⟶ algebraStalk.{u,u,v} (Ideal.Quotient.mk (listIdeal a)) :=
    (CochainCoefficientLift.lift.{max u v,u} A).map (augmentationValue a) ≫ σ.hom
  have hp : QuasiIso p := quasiIso_comp _ σ.hom
  have : IsIso ((qValue A).map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) p).2 hp
  refine ⟨liftedKoszul.{u,max u v} a, ⟨?_, ?_⟩, ⟨(asIso ((qValue A).map p)).symm⟩⟩
  · intro i
    have hfree : Module.Free A ((cochainValue a).X i) := (hterms i).1
    have hfinite : Module.Finite A ((cochainValue a).X i) := (hterms i).2
    let ei := Specs.DerivedFormalization.CochainCoefficientLift.termEquiv.{max u v} (cochainValue a) i
    exact ⟨Module.Finite.equiv ei, Module.Projective.of_equiv' ei⟩
  · refine ⟨-(a.length : ℤ), 0, by omega, ?_⟩
    intro i hi
    exact F.map_isZero (hbound i (by
      simp only [Set.mem_Icc, not_and_or, not_le]
      exact hi))

/-- Compose the normalized Koszul identification with the perfect-algebra
tensor-evaluation isomorphism for the quotient map. -/
theorem regularQuotientDuality : Duality.{u,v} := by
  intro A _ _ J a h ha A' B' _ _ e d MA MB T L G S
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨(exteriorPower.zeroEquiv (A ⧸ J) J.Cotangent).symm.dualMap.trans
      (LinearMap.ringLmapEquivSelf (A ⧸ J) (A ⧸ J) (A ⧸ J))⟩
  obtain ⟨_, δ, hδ, _⟩ := KoszulRelativeDual.relativeDual.{u,v} J G a h ha
  let f := Ideal.Quotient.mk J
  have hp := quotientPerfect.{u,v} J a h ha
  obtain ⟨φ, hφ, hmodel⟩ := PerfectRelativeDual.relativeDuality.{u,u,v} f MA T L G S hp
  let ρ := determinantTensorComparison.{u,v} J e T L G δ
  let θ := (asIso φ).symm ≪≫ ρ
  refine ⟨δ, (show IdentifiesDeterminant J G a.length δ from hδ), θ, ?_⟩
  have heq : ρ.hom ≫ θ.inv = φ := by simp [θ]
  rw [heq]
  refine ⟨?_, hmodel⟩
  obtain ⟨_, _, hOriginal⟩ := PerfectRelativeDual.relativeDualityOnOriginal.{u,u,v} f MA T L G S hp
  intro X I i _ hI X' Y
  obtain ⟨P, K, p, q, j, hpQ, hqQ, hP, hK, hj, haug, _⟩ := hOriginal X I i hI
  refine ⟨P, K, p, q, j, hpQ, hqQ, hP, hK, hj, haug, ?_⟩
  let qA := qValue.{max u v} A
  let qB := qValue.{max u v} (A ⧸ J)
  let F := source.{u,u,v} f e d T L G
  have hpIso : IsIso (qA.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) p).2 hpQ
  have hqIso : IsIso (qA.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) q).2 hqQ
  let α := (liftDFactors.{u,v} A).app X ≪≫ (asIso (qA.map p)).symm
  let β := (liftDFactors.{u,v} A).app X ≪≫ asIso (qA.map q)
  let aug := qA.map (targetAugmentation.{u,u,v} e MA i j)
  let c := comparison.{max u v} f G.adjunction K
  have hcIso : IsIso c := G.comparison_isIso K hK
  have hβ : α.hom ≫ aug = β.hom := by
    change ((liftDFactors.{u,v} A).hom.app X ≫ inv (qA.map p)) ≫
      qA.map (targetAugmentation.{u,u,v} e MA i j) =
      (liftDFactors.{u,v} A).hom.app X ≫ qA.map q
    rw [haug, qA.map_comp]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hc : (G.modelIso f K β hK).hom ≫ c = G.functor.map β.hom := by
    change (G.functor.map β.hom ≫ inv c) ≫ c = _
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  change φ.app Y ≫ (G.modelIso f K β hK).hom =
    F.map α.hom ≫ (sourceModel f e d T L G i hI P hP).hom ≫
      qB.map (chainComparison.{u,u,v} f d S I P K j)
  apply (cancel_mono c).1
  simp only [Category.assoc, hc]
  rw [← (hmodel I P K i hI hP j hK).2]
  have hnat : F.map α.hom ≫ φ.app (qA.obj P) = φ.app Y ≫ G.functor.map α.hom :=
    φ.naturality α.hom
  change φ.app Y ≫ G.functor.map β.hom =
    F.map α.hom ≫ φ.app (qA.obj P) ≫ G.functor.map aug
  rw [reassoc_of% hnat, ← G.functor.map_comp, hβ]

/-- Construct the derived functor models at the common level of the ring and the
original complexes, then apply the quotient formula. -/
theorem regularQuotientDualityExists : Realization.{u,v} := by
  intro A _ _ J a h ha f e d
  obtain ⟨MA⟩ := CochainTensorTransport.adequateModel.{u,max u v} e
  obtain ⟨MB⟩ := CochainTensorTransport.adequateModel.{u,max u v} d
  obtain ⟨TA⟩ := DerivedTensor.existsModel.{u,max u v} MA
  obtain ⟨TB⟩ := DerivedTensor.existsModel.{u,max u v} MB
  obtain ⟨NA⟩ := DerivedScalarExtension.ringTensor.{u,max u v} TA.toDescent
  obtain ⟨NB⟩ := DerivedScalarExtension.ringTensor.{u,max u v} TB.toDescent
  obtain ⟨_, _, L, _, _⟩ := DerivedScalarExtension.existsExtension.{u,u,max u v} f NA NB
  obtain ⟨G⟩ := derivedCoinductionExists.{v,u,u} f
  obtain ⟨S⟩ := ScalarExtensionTransport.modelStability d f
  exact ⟨MA, MB, TB, L, G, S, regularQuotientDuality.{u,v} J a h ha MA TB L G S⟩

end DerivedFormalization.RegularQuotientDuality
