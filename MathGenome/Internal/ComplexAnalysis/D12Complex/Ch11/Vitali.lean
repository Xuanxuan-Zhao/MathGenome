import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.Vitali
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.Montel
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.IdentityTheorem
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-! Vitali convergence from finite-valued Montel and the identity theorem.
First extract one holomorphic limit. All further extracted limits agree
on E by uniqueness of finite pointwise limits, hence on Ω by identity.
The subsequence criterion for convergence then applies on each compact. -/

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Ch11.Vitali

theorem vitali_convergence :
    Specs.D12Complex.Ch11.Vitali.vitali_convergence_type := by
  intro Ω E F a hΩ hhol hb hE ha hacc hpoint
  have hn : Montel.FiniteNormal Ω (range F) :=
    (Montel.locallyBounded_iff_finiteNormal Ω (range F) hΩ.2.1 (by
      rintro g ⟨n, rfl⟩
      exact hhol n)).mp hb
  obtain ⟨φ, f, hφ, hf, hlim⟩ := hn F (fun n => mem_range_self n)
  have hfe : ∀ z ∈ E, Tendsto (fun n => F n z) atTop (𝓝 (f z)) := by
    intro z hz
    obtain ⟨L, hL⟩ := hpoint z hz
    have heq : L = f z :=
      tendsto_nhds_unique (hL.comp hφ.tendsto_atTop) (hlim.tendsto_at (hE hz))
    simpa only [heq] using hL
  refine ⟨f, hf, ?_⟩
  intro K hK hKΩ
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  change TendstoUniformly (fun n (z : K) => F n z) (fun z : K => f z) atTop
  apply (UniformFun.tendsto_iff_tendstoUniformly
    (F := fun n => UniformFun.ofFun (fun z : K => F n z))
    (f := UniformFun.ofFun (fun z : K => f z))).mp
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, g, hψ, hg, hglim⟩ := hn (fun n => F (ns n))
    (fun n => mem_range_self (ns n))
  have heq : EqOn g f Ω := by
    apply IdentityTheorem.identity_of_accPt Ω E g f a hΩ hg hf hE ha hacc
    intro z hz
    exact tendsto_nhds_unique (hglim.tendsto_at (hE hz))
      (((hfe z hz).comp hns).comp hψ.tendsto_atTop)
  refine ⟨ψ, ?_⟩
  apply UniformFun.tendsto_iff_tendstoUniformly.mpr
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ.2.1).mp
      (hglim.congr_right heq) K hKΩ hK)

end D12Complex.Ch11.Vitali
