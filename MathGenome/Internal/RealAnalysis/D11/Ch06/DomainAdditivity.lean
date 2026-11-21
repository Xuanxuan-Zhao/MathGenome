import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.DomainAdditivity
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral

/-! Additivity and continuity in the domain (paper.tex:1974–1991).
The existing scalar bridge provides actual measurability and native absolute
integrability before any use of the library's integral. Disjoint additivity
applied to the real norm gives a summable positive majorant for the scalar
integrals. The library domain-continuity results require integrability on
the union (below), or on one term (above), both supplied by global
integrability; they impose no finite-measure hypothesis. -/
open Set Filter MeasureTheory
open scoped Topology
universe u
noncomputable section
namespace D11.Ch06.DomainAdditivity
open D11.Ch06.ScalarIntegral

theorem disjoint_domain_additivity :
    Specs.D11.Ch06.DomainAdditivity.disjoint_domain_additivity := by
  intro X 𝕜 _ _ _ _ μ f hf E hE hd
  have hi : Integrable f μ := ((scalarIntegrable_iff μ f).mp hf).2
  have hr (A : Set X) : scalarIntegrable (μ.restrict A) f :=
    (scalarIntegrable_iff (μ.restrict A) f).mpr ⟨hf.1, hi.integrableOn⟩
  have hs : HasSum (fun n => ∫ x in E n, f x ∂μ) (∫ x in ⋃ n, E n, f x ∂μ) :=
    hasSum_integral_iUnion hE hd hi.integrableOn
  have hn : Summable (fun n => ∫ x in E n, ‖f x‖ ∂μ) :=
    (hasSum_integral_iUnion hE hd hi.norm.integrableOn).summable
  have ha : Summable (fun n => ‖∫ x in E n, f x ∂μ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _) hn
  exact ⟨fun n => hr (E n), hr (⋃ n, E n), ha, hs, hs.tsum_eq.symm⟩

theorem continuity_from_below : Specs.D11.Ch06.DomainAdditivity.continuity_from_below := by
  intro X 𝕜 _ _ _ _ μ f hf E hE hmono
  have hi : Integrable f μ := ((scalarIntegrable_iff μ f).mp hf).2
  have hr (A : Set X) : scalarIntegrable (μ.restrict A) f :=
    (scalarIntegrable_iff (μ.restrict A) f).mpr ⟨hf.1, hi.integrableOn⟩
  exact ⟨fun n => hr (E n), hr (⋃ n, E n),
    tendsto_setIntegral_of_monotone hE hmono hi.integrableOn⟩

theorem continuity_from_above : Specs.D11.Ch06.DomainAdditivity.continuity_from_above := by
  intro X 𝕜 _ _ _ _ μ f hf E hE hanti
  have hi : Integrable f μ := ((scalarIntegrable_iff μ f).mp hf).2
  have hr (A : Set X) : scalarIntegrable (μ.restrict A) f :=
    (scalarIntegrable_iff (μ.restrict A) f).mpr ⟨hf.1, hi.integrableOn⟩
  exact ⟨fun n => hr (E n), hr (⋂ n, E n),
    tendsto_setIntegral_of_antitone hE hanti ⟨0, hi.integrableOn⟩⟩

end D11.Ch06.DomainAdditivity
