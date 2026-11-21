import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.FilteredColimits

/-! FL-16. Unique component lifts are compatible and hence descend through the
colimit. The argument proves the stronger statement for every colimit cocone,
without a filteredness requirement. -/
namespace AdvCommAlg.FormalLifting

open CategoryTheory Limits
open Specs.AdvCommAlg.FormalLifting (reductionMap)
universe u v w t

variable {A : Type u} [CommRing A] {J : Type w} [Category.{t} J]
  {F : J ⥤ CommAlgCat.{max u v} A} {c : Cocone F}

/-- Uniqueness of lifts is preserved by arbitrary algebra colimits. -/
theorem formallyUnramified_of_isColimit (hc : IsColimit c)
    (h : ∀ j, FormallyUnramified A (F.obj j)) : FormallyUnramified A c.pt := by
  intro C _ _ N hN f g hfg
  have heq : CommAlgCat.ofHom f = CommAlgCat.ofHom g := hc.hom_ext fun j => by
    apply CommAlgCat.hom_ext
    apply unramified_reduction_injective (h j) N hN
    exact congrArg (fun k => k.comp (c.ι.app j).hom) hfg
  exact congrArg CommAlgCat.Hom.hom heq

/-- Unique lifts on the components assemble to a unique lift on the colimit. -/
theorem formallyEtale_of_isColimit (hc : IsColimit c)
    (h : ∀ j, FormallyEtale A (F.obj j)) : FormallyEtale A c.pt := by
  intro C _ _ N hN
  have hinj (j : J) := (etale_reduction_bijective (h j) N hN).1
  refine ⟨?_, ?_⟩
  · intro f g hfg
    have heq : CommAlgCat.ofHom f = CommAlgCat.ofHom g := hc.hom_ext fun j => by
      apply CommAlgCat.hom_ext
      apply hinj j
      exact congrArg (fun k => k.comp (c.ι.app j).hom) hfg
    exact congrArg CommAlgCat.Hom.hom heq
  · intro f
    choose lifts hlifts using fun j =>
      (etale_reduction_bijective (h j) N hN).2 (f.comp (c.ι.app j).hom)
    simp only [reductionMap] at hlifts
    let s : Cocone F :=
      { pt := CommAlgCat.of A C
        ι :=
          { app := fun j => CommAlgCat.ofHom (lifts j)
            naturality := by
              intro i j k
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
              apply CommAlgCat.hom_ext
              apply hinj i
              change (Ideal.Quotient.mkₐ A N).comp ((lifts j).comp (F.map k).hom) = _
              rw [← AlgHom.comp_assoc, hlifts j, AlgHom.comp_assoc]
              rw [← CommAlgCat.hom_comp, c.w k]
              exact (hlifts i).symm } }
    refine ⟨(hc.desc s).hom, ?_⟩
    have heq : hc.desc s ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ A N) =
        CommAlgCat.ofHom f := by
      apply hc.hom_ext
      intro j
      rw [← Category.assoc, hc.fac]
      exact CommAlgCat.hom_ext (hlifts j)
    exact congrArg CommAlgCat.Hom.hom heq

/-- FL-16: every filtered colimit of formally étale A-algebras is formally étale. -/
theorem filtered_colimit_formallyEtale :
    Specs.AdvCommAlg.FormalLifting.filteredColimitFormallyEtale.{u,v,w,t} := by
  intro A _ J _ _ F c hc h
  exact formallyEtale_of_isColimit hc h

/-- FL-16: every filtered colimit of formally unramified A-algebras is formally unramified. -/
theorem filtered_colimit_formallyUnramified :
    Specs.AdvCommAlg.FormalLifting.filteredColimitFormallyUnramified.{u,v,w,t} := by
  intro A _ J _ _ F c hc h
  exact formallyUnramified_of_isColimit hc h

end AdvCommAlg.FormalLifting
