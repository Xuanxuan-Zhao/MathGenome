import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace RepTheorySurvey.Geometric.SchubertProjectionBaseChangeSpecs

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs SchubertIntersectionConstructibilitySpecs

namespace Expected

/-- At an open orbit attachment, smooth projection pullback commutes with ordinary
derived direct image of the normalized intersection complex via the adjunction mate. -/
def SmoothProjectionBaseChange : Prop :=
  ∀ (T : TopCat.{0}) (e : ℕ),
    (∃ V : Opens (Fin e → ℂ), Nonempty (T ≃ₜ V)) →
    ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) (k : ℕ)
      {U Y : TopCat.{0}} (j : U ⟶ Y) (f : Y ⟶ SchubertSpace ab N hN)
      (P : Stratification Y) (Q : Stratification U) {s : ℕ}
      (D : DimensionFiltration U s),
      RealizesOrbitStage f (k + 1) P →
      IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D →
      let jT : TopCat.of (T × U) ⟶ TopCat.of (T × Y) :=
        TopCat.ofHom ⟨fun p => (p.1, j p.2),
          continuous_fst.prodMk (j.hom.continuous.comp continuous_snd)⟩
      let pU : TopCat.of (T × U) ⟶ U := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
      let pY : TopCat.of (T × Y) ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
      let square : jT ≫ pY = pU ≫ j := TopCat.ext (fun _ => rfl)
      ∀ (a : boundedBelowInverseImage jT ⊣ derivedDirectImage jT)
        (b : boundedBelowInverseImage j ⊣ derivedDirectImage j),
        IsIso (directImageComparison square a b (complex D))

end Expected
end RepTheorySurvey.Geometric.SchubertProjectionBaseChangeSpecs
