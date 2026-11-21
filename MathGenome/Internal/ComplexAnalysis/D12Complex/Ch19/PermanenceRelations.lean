import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.PermanenceRelations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Set Filter
open scoped Topology
noncomputable section
namespace D12Complex.PermanenceRelations
open RelationData
abbrev jetGraph : Specs.D12Complex.Ch19.PermanenceRelations.jetGraph_type :=
  @RelationData.jetGraph
abbrev RepresentsTuple : Specs.D12Complex.Ch19.PermanenceRelations.RepresentsTuple_type :=
  @RelationData.RepresentsTuple
abbrev GraphsIn : Specs.D12Complex.Ch19.PermanenceRelations.GraphsIn_type :=
  @RelationData.GraphsIn

/-- Finitely many continuations admit simultaneous representatives after
intersecting both their space and parameter neighborhoods. -/
lemma simultaneous_representatives {m : ℕ} {γ : unitInterval → ℂ}
    {Φ : Fin m → GermFamily γ} (hΦ : ∀ i, LocallyRepresented γ (Φ i))
    (s : unitInterval) :
    ∃ (U : Set ℂ) (f : Fin m → ℂ → ℂ), IsOpen U ∧
      (∀ i, HolomorphicOn U (f i)) ∧
      ∀ᶠ t in 𝓝 s, γ t ∈ U ∧ RepresentsTuple (γ t) (fun i => Φ i t) f := by
  choose U f hf hr using fun i => (locallyRepresented_iff γ (Φ i)).mp (hΦ i) s
  refine ⟨⋂ i, U i, f, isOpen_iInter_of_finite (fun i => (hf i).1), ?_, ?_⟩
  · intro i
    exact ⟨isOpen_iInter_of_finite (fun i => (hf i).1),
      fun z hz => (hf i).2 z ((mem_iInter.mp hz) i)⟩
  · have h := eventually_all.mpr hr
    filter_upwards [h] with t ht
    refine ⟨mem_iInter.mpr (fun i => (ht i).choose), fun i => ?_⟩
    exact congrArg Subtype.val (ht i).choose_spec

/-- A neighborhood-local operation with holomorphic output near the path
induces a continuation, independently of all choices of representatives. -/
lemma continuation_transform {m : ℕ} {Ω : Set ℂ} {γ : unitInterval → ℂ}
    {Φ : Fin m → GermFamily γ} (hΩ : IsDomain Ω) (hγ : Continuous γ)
    (hγΩ : ∀ t, γ t ∈ Ω) (hΦ : ∀ i, LocallyRepresented γ (Φ i))
    (T : (Fin m → ℂ → ℂ) → ℂ → ℂ)
    (hcongr : ∀ (a : ℂ) (f g : Fin m → ℂ → ℂ),
      (∀ i, f i =ᶠ[𝓝 a] g i) → T f =ᶠ[𝓝 a] T g)
    (hlocal : ∀ t (U : Set ℂ) (f : Fin m → ℂ → ℂ), IsOpen U → γ t ∈ U →
      (∀ i, HolomorphicOn U (f i)) → RepresentsTuple (γ t) (fun i => Φ i t) f →
      ∃ V : Set ℂ, γ t ∈ V ∧ HolomorphicOn V (T f)) :
    ∃ Ψ : GermFamily γ, IsContinuation Ω γ (Ψ 0) Ψ ∧
      ∀ t (f : Fin m → ℂ → ℂ), RepresentsTuple (γ t) (fun i => Φ i t) f →
        (Ψ t).val = (T f : Germ (𝓝 (γ t)) ℂ) := by
  choose U f hU hf hr using simultaneous_representatives hΦ
  have hloc (t) := hlocal t (U t) (f t) (hU t) (hr t).self_of_nhds.1 (hf t)
    (hr t).self_of_nhds.2
  choose V hV hTf using hloc
  let Ψ : GermFamily γ := fun t => HolomorphicGerm.ofFunction (T (f t)) (hTf t) (hV t)
  have hrep (t) (g : Fin m → ℂ → ℂ)
      (hg : RepresentsTuple (γ t) (fun i => Φ i t) g) :
      (Ψ t).val = (T g : Germ (𝓝 (γ t)) ℂ) := by
    apply Germ.coe_eq.mpr
    apply hcongr
    intro i
    exact Germ.coe_eq.mp (((hr t).self_of_nhds.2 i).symm.trans (hg i))
  refine ⟨Ψ, ⟨hΩ, hγ, hγΩ, rfl, ?_⟩, hrep⟩
  apply (locallyRepresented_iff γ Ψ).mpr
  intro s
  refine ⟨V s, T (f s), hTf s, ?_⟩
  filter_upwards [hr s, hγ.continuousAt ((hTf s).1.mem_nhds (hV s))] with t ht htV
  exact ⟨htV, Subtype.ext (hrep t (f s) ht.2)⟩

theorem expression_representative_independence :
    Specs.D12Complex.Ch19.PermanenceRelations.expression_representative_independence_type := by
  intro m r a f g H hfg
  have hj : jetGraph r f =ᶠ[𝓝 a] jetGraph r g := by
    have he : ∀ p : Fin m × Fin (r + 1),
        iteratedDeriv p.2.val (f p.1) =ᶠ[𝓝 a] iteratedDeriv p.2.val (g p.1) :=
      fun p => (hfg p.1).iteratedDeriv p.2.val
    filter_upwards [eventually_all.mpr he] with z hz
    exact Prod.ext rfl (funext hz)
  exact ⟨hj.fun_comp H, hj.self_of_nhds⟩

/-- Holomorphy of a jet substitution on the actual inverse image of D. -/
lemma holomorphic_expression {m r : ℕ} {U : Set ℂ} {f : Fin m → ℂ → ℂ}
    (hU : IsOpen U) (hf : ∀ i, HolomorphicOn U (f i))
    {D : Set (ℂ × (Fin m × Fin (r + 1) → ℂ))}
    {H : (ℂ × (Fin m × Fin (r + 1) → ℂ)) → ℂ}
    (hD : IsOpen D) (hH : DifferentiableOn ℂ H D) :
    HolomorphicOn (U ∩ jetGraph r f ⁻¹' D) (fun z => H (jetGraph r f z)) := by
  have hd (z : ℂ) (hz : z ∈ U) : DifferentiableAt ℂ (jetGraph r f) z := by
    exact differentiableAt_id.prodMk (differentiableAt_pi.mpr (fun p =>
      ((DiskCauchyDerivatives.holomorphicOn_iteratedDeriv U (f p.1) (hf p.1) p.2.val).1.2 z hz)))
  have hopen : IsOpen (U ∩ jetGraph r f ⁻¹' D) := by
    exact ContinuousOn.isOpen_inter_preimage
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hU hD
  refine ⟨hopen, fun z hz => ?_⟩
  exact ((hH _ hz.2).differentiableAt (hD.mem_nhds hz.2)).comp z (hd z hz.1)

theorem expression_continuation :
    Specs.D12Complex.Ch19.PermanenceRelations.expression_continuation_type := by
  intro m r Ω γ φ Φ hΩ hγ hγΩ hΦ D H hD hH hgraphs
  apply continuation_transform hΩ hγ hγΩ (fun i => (hΦ i).2.2.2.2)
    (fun f z => H (jetGraph r f z))
  · intro a f g hfg
    exact (expression_representative_independence m r a f g H hfg).1
  · intro t U f ho ha hf hrep
    obtain ⟨V, g, hb, hg, hgreps, hgraph⟩ := hgraphs t
    have he : jetGraph r f (γ t) = jetGraph r g (γ t) :=
      (expression_representative_independence m r (γ t) f g H
        (fun i => Germ.coe_eq.mp ((hrep i).symm.trans (hgreps i)))).2
    exact ⟨U ∩ jetGraph r f ⁻¹' D, ⟨ha, by simpa only [mem_preimage, he] using hgraph⟩,
      holomorphic_expression ho hf hD hH⟩

theorem derivative_continuation :
    Specs.D12Complex.Ch19.PermanenceRelations.derivative_continuation_type := by
  intro k Ω γ φ Φ hΦ
  obtain ⟨Ψ, hΨ, hr⟩ := continuation_transform (m := 1) hΦ.1 hΦ.2.1 hΦ.2.2.1
    (Φ := fun _ => Φ) (fun _ => hΦ.2.2.2.2) (fun f => iteratedDeriv k (f 0))
    (fun _ _ _ h => (h 0).iteratedDeriv k)
    (fun t U f ho ha hf _ => ⟨U, ha,
      (DiskCauchyDerivatives.holomorphicOn_iteratedDeriv U (f 0) (hf 0) k).1⟩)
  exact ⟨Ψ, hΨ, fun t f hf => hr t (fun _ => f) (fun _ => hf)⟩

theorem sum_continuation :
    Specs.D12Complex.Ch19.PermanenceRelations.sum_continuation_type := by
  intro Ω γ φ ψ Φ Ψ hΦ hΨ
  have hloc : ∀ i : Fin 2, LocallyRepresented γ (![Φ, Ψ] i) := by
    intro i; fin_cases i
    · exact hΦ.2.2.2.2
    · exact hΨ.2.2.2.2
  obtain ⟨Θ, hΘ, hr⟩ := continuation_transform hΦ.1 hΦ.2.1 hΦ.2.2.1 hloc
    (fun f z => f 0 z + f 1 z) (fun _ _ _ h => (h 0).add (h 1))
    (fun t U f ho ha hf _ => ⟨U, ha, ho,
      fun z hz => ((hf 0).2 z hz).add ((hf 1).2 z hz)⟩)
  refine ⟨Θ, hΘ, fun t f g hf hg => hr t ![f, g] ?_⟩
  intro i; fin_cases i
  · exact hf
  · exact hg

theorem product_continuation :
    Specs.D12Complex.Ch19.PermanenceRelations.product_continuation_type := by
  intro Ω γ φ ψ Φ Ψ hΦ hΨ
  have hloc : ∀ i : Fin 2, LocallyRepresented γ (![Φ, Ψ] i) := by
    intro i; fin_cases i
    · exact hΦ.2.2.2.2
    · exact hΨ.2.2.2.2
  obtain ⟨Θ, hΘ, hr⟩ := continuation_transform hΦ.1 hΦ.2.1 hΦ.2.2.1 hloc
    (fun f z => f 0 z * f 1 z) (fun _ _ _ h => (h 0).mul (h 1))
    (fun t U f ho ha hf _ => ⟨U, ha, ho,
      fun z hz => ((hf 0).2 z hz).mul ((hf 1).2 z hz)⟩)
  refine ⟨Θ, hΘ, fun t f g hf hg => hr t ![f, g] ?_⟩
  intro i; fin_cases i
  · exact hf
  · exact hg

theorem quotient_continuation :
    Specs.D12Complex.Ch19.PermanenceRelations.quotient_continuation_type := by
  intro Ω γ φ ψ Φ Ψ hΦ hΨ hn
  have hloc : ∀ i : Fin 2, LocallyRepresented γ (![Φ, Ψ] i) := by
    intro i; fin_cases i
    · exact hΦ.2.2.2.2
    · exact hΨ.2.2.2.2
  obtain ⟨Θ, hΘ, hr⟩ := continuation_transform hΦ.1 hΦ.2.1 hΦ.2.2.1 hloc
    (fun f z => f 0 z / f 1 z) (fun _ _ _ h => (h 0).div (h 1)) (by
      intro t U f ho ha hf hrep
      have hval : (Ψ t).value = f 1 (γ t) := congrArg Germ.value (hrep 1)
      have hn' : f 1 (γ t) ≠ 0 := hval ▸ hn t
      have hnear : ∀ᶠ z in 𝓝 (γ t), z ∈ U ∧ f 1 z ≠ 0 :=
        Filter.inter_mem (ho.mem_nhds ha)
          (((hf 1).2 _ ha).continuousAt.eventually_ne hn')
      obtain ⟨V, hVU, hVo, haV⟩ := mem_nhds_iff.mp hnear
      exact ⟨V, haV, hVo, fun z hz =>
        ((hf 0).2 z (hVU hz).1).div ((hf 1).2 z (hVU hz).1) (hVU hz).2⟩)
  refine ⟨Θ, hΘ, fun t f g hf hg => hr t ![f, g] ?_⟩
  intro i; fin_cases i
  · exact hf
  · exact hg

theorem identity_permanence :
    Specs.D12Complex.Ch19.PermanenceRelations.identity_permanence_type := by
  intro m r Ω γ φ Φ hΩ hγ hγΩ hΦ D H hD hH hgraphs f₀ hf₀ hz t f hf
  obtain ⟨Ψ, hΨ, hrep⟩ := expression_continuation m r Ω γ φ Φ hΩ hγ hγΩ hΦ D H hD hH hgraphs
  let Z : GermFamily γ := fun t => HolomorphicGerm.ofFunction (fun _ => 0)
    ⟨isOpen_univ, fun _ _ => differentiableAt_const 0⟩ (mem_univ (γ t))
  have hinit : Ψ 0 = Z 0 := by
    apply Subtype.ext
    exact (hrep 0 f₀ (fun i => (congrArg Subtype.val (hΦ i).2.2.2.1).trans (hf₀ i))).trans
      (Germ.coe_eq.mpr hz)
  have hZ : IsContinuation Ω γ (Ψ 0) Z := by
    refine ⟨hΩ, hγ, hγΩ, hinit.symm, ?_⟩
    intro s
    exact ⟨univ, fun _ => 0, univ, isOpen_univ, mem_univ s,
      ⟨isOpen_univ, fun _ _ => differentiableAt_const 0⟩,
      fun t _ => ⟨mem_univ _, rfl⟩⟩
  have heq := ContinuationOperations.continuation_unique Ω γ (Ψ 0) Ψ Z hΨ hZ t
  apply Germ.coe_eq.mp
  exact (hrep t f hf).symm.trans (congrArg Subtype.val heq)
end D12Complex.PermanenceRelations

