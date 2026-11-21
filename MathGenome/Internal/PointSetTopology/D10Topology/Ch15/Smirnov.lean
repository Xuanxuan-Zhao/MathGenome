import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.Smirnov
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.StandardParacompactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.IndexedShrinking
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.NagataSmirnov
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.ParacompactNormal

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
universe u v w

namespace D10Topology.Ch15

/-- Every point has an open metrizable subspace neighborhood. -/
abbrev LocallyMetrizable (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch15.Smirnov.LocallyMetrizable X

/-- Locally finite families can be combined over a locally finite dominating family. -/
theorem locallyFinite_sigma_of_domination {X : Type u} [TopologicalSpace X]
    {I : Type v} {J : I → Type w} {V : I → Set X} {A : ∀ i, J i → Set X}
    (hV : LocallyFinite V) (hA : ∀ i, LocallyFinite (A i))
    (hAV : ∀ i j, A i j ⊆ V i) :
    LocallyFinite (fun j : Σ i, J i => A j.1 j.2) := by
  intro x
  obtain ⟨N, hN, hNfin⟩ := hV x
  choose T hT hTfin using fun i => hA i x
  let S := {i | (V i ∩ N).Nonempty}
  let M := N ∩ ⋂ i ∈ S, T i
  have hM : M ∈ 𝓝 x := inter_mem hN ((biInter_mem hNfin).mpr fun i _ => hT i)
  refine ⟨M, hM, ?_⟩
  have hfinite : (⋃ i ∈ S, Sigma.mk i '' {j | (A i j ∩ T i).Nonempty}).Finite :=
    hNfin.biUnion fun i _ => (hTfin i).image (Sigma.mk i)
  apply hfinite.subset
  rintro ⟨i, j⟩ ⟨y, hyA, hyM⟩
  have hiS : i ∈ S := ⟨y, hAV i j hyA, hyM.1⟩
  exact mem_iUnion₂.mpr ⟨i, hiS, ⟨j, ⟨y, hyA, mem_iInter₂.mp hyM.2 i hiS⟩, rfl⟩⟩

/-- A relative locally finite family restricted inside V stays locally finite
in the ambient space when the closure of V lies in the open subspace. -/
theorem locallyFinite_image_inter_of_closure_subset {X : Type u}
    [TopologicalSpace X] {I : Type v} {U V : Set X}
    (hU : IsOpen U) (hVU : closure V ⊆ U) (A : I → Set U)
    (hA : LocallyFinite A) :
    LocallyFinite (fun i => (Subtype.val '' A i) ∩ V) := by
  intro x
  by_cases hx : x ∈ U
  · obtain ⟨N, hN, hfin⟩ := hA ⟨x, hx⟩
    refine ⟨Subtype.val '' N, hU.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hN,
      hfin.subset ?_⟩
    rintro i ⟨y, ⟨⟨a, ha, hay⟩, _⟩, b, hb, hby⟩
    have hab : a = b := Subtype.ext (hay.trans hby.symm)
    exact ⟨a, ha, hab ▸ hb⟩
  · have hxV : x ∉ closure V := fun h => hx (hVU h)
    refine ⟨(closure V)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxV, ?_⟩
    have he : {i | (((Subtype.val '' A i) ∩ V) ∩ (closure V)ᶜ).Nonempty} = ∅ := by
      ext i
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨y, ⟨_, hyV⟩, hy⟩
      exact hy (subset_closure hyV)
    rw [he]
    exact finite_empty

/-- Combine countably many locally finite layers in each member of a locally
finite dominating family; all indexed repetitions are retained. -/
theorem SigmaLocallyFinite.sigma_of_locallyFinite {X : Type u}
    [TopologicalSpace X] {I : Type v} {J : I → Type w}
    {V : I → Set X} {A : ∀ i, J i → Set X}
    (hV : LocallyFinite V) (hA : ∀ i, SigmaLocallyFinite (A i))
    (hAV : ∀ i j, A i j ⊆ V i) :
    SigmaLocallyFinite (fun j : Σ i, J i => A j.1 j.2) := by
  choose L hL hfin using hA
  let K : ℕ → Set (Σ i, J i) := fun n => {j | j.2 ∈ L j.1 n}
  refine ⟨K, iUnion_eq_univ_iff.mpr ?_, fun n => ?_⟩
  · intro ⟨i, j⟩
    exact iUnion_eq_univ_iff.mp (hL i) j
  · have hf := locallyFinite_sigma_of_domination hV (fun i => hfin i n)
      (fun i j => hAV i j.val)
    let e : K n → Σ i, L i n := fun j => ⟨j.val.1, ⟨j.val.2, j.property⟩⟩
    have he : Function.Injective e := by
      intro a b hab
      exact Subtype.ext (congrArg (fun j : Σ i, L i n => (⟨j.1, j.2.val⟩ : Σ i, J i)) hab)
    exact hf.comp_injective he

/-- Local metrizable charts supply a global sigma locally finite basis after
shrinking. The resulting basis may be uncountable. -/
theorem sigmaLocallyFinite_basis_of_paracompact_locallyMetrizable
    (X : Type u) [TopologicalSpace X] (hH : Ch07.T2 X)
    (hP : Paracompact X) (hM : LocallyMetrizable X) :
    ∃ B : Set (Set X), IsTopologicalBasis B ∧
      SigmaLocallyFinite (fun b : B => (b : Set X)) := by
  classical
  choose U hUo hxU hUm using hM
  have hUcover : (⋃ i, U i) = univ :=
    iUnion_eq_univ_iff.mpr fun x => ⟨x, hxU x⟩
  obtain ⟨V, hVo, hVfin, hVcover, hVU⟩ := indexed_shrinking hP hH U hUo hUcover
  have hex (i : X) : ∃ B : Set (Set (U i)), IsTopologicalBasis B ∧
      SigmaLocallyFinite (fun b : B => (b : Set (U i))) := by
    letI : MetrizableSpace (U i) := (Ch09.metrizable_iff_mathlib _).mp (hUm i)
    letI : MetricSpace (U i) := metrizableSpaceMetric (U i)
    exact metric_sigmaLocallyFinite_basis (U i)
  choose B hB hBσ using hex
  let A (i : X) (b : B i) : Set X := (Subtype.val '' (b : Set (U i))) ∩ V i
  have hAσ (i : X) : SigmaLocallyFinite (A i) := by
    obtain ⟨L, hL, hfin⟩ := hBσ i
    exact ⟨L, hL, fun n => locallyFinite_image_inter_of_closure_subset (hUo i) (hVU i)
      (fun b : L n => (b.val : Set (U i))) (hfin n)⟩
  let a : (Σ i, B i) → Set X := fun j => A j.1 j.2
  have haσ : SigmaLocallyFinite a :=
    SigmaLocallyFinite.sigma_of_locallyFinite hVfin hAσ (fun _ _ => inter_subset_right)
  have hab : IsTopologicalBasis (range a) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨⟨i, b⟩, rfl⟩
      exact ((hUo i).isOpenMap_subtype_val _ ((hB i).isOpen b.property)).inter (hVo i)
    · intro x O hxO hO
      obtain ⟨i, hxi⟩ := iUnion_eq_univ_iff.mp hVcover x
      have hxiU : x ∈ U i := hVU i (subset_closure hxi)
      obtain ⟨b, hb, hxb, hbO⟩ := (hB i).exists_subset_of_mem_open
        (show (⟨x, hxiU⟩ : U i) ∈ Subtype.val ⁻¹' O from hxO)
        (hO.preimage continuous_subtype_val)
      refine ⟨A i ⟨b, hb⟩, ⟨⟨i, ⟨b, hb⟩⟩, rfl⟩,
        ⟨⟨⟨x, hxiU⟩, hxb, rfl⟩, hxi⟩, ?_⟩
      rintro y ⟨⟨z, hz, rfl⟩, _⟩
      exact hbO hz
  exact ⟨range a, hab, haσ.on_range⟩

/-- Smirnov's metrization theorem, with Hausdorffness kept explicit. -/
theorem smirnov (X : Type u) [t : TopologicalSpace X] (hH : Ch07.T2 X) :
    Ch09.Metrizable t ↔ Paracompact X ∧ LocallyMetrizable X := by
  constructor
  · intro hM
    letI : MetrizableSpace X := (Ch09.metrizable_iff_mathlib t).mp hM
    letI : MetricSpace X := metrizableSpaceMetric X
    refine ⟨metric_paracompact (metrizableSpaceMetric X), ?_⟩
    intro x
    exact ⟨univ, isOpen_univ, mem_univ x,
      (Ch09.metrizable_iff_mathlib _).mpr inferInstance⟩
  · rintro ⟨hP, hM⟩
    letI : T2Space X := hH
    letI : RegularSpace X := paracompact_hausdorff_regular X hP hH
    obtain ⟨B, hB, hBσ⟩ :=
      sigmaLocallyFinite_basis_of_paracompact_locallyMetrizable X hH hP hM
    exact exists_compatibleMetric_of_sigmaLocallyFinite_basis X B hB hBσ

end D10Topology.Ch15
