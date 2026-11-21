import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.MarkovKakutani
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ExpandedFA.PartV
open Set Filter
open scoped Topology Pointwise
open MarkovKakutaniSpec

universe u v

section Averages
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Recursive arithmetic means of x, f x, ..., f^[n] x. -/
noncomputable def affineOrbitAverage (f : E → E) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => ((n + 1 : ℝ) / (n + 2)) • affineOrbitAverage f x n +
      (1 / (n + 2 : ℝ)) • f^[n + 1] x

private lemma average_weights (n : ℕ) :
    0 ≤ (n + 1 : ℝ) / (n + 2) ∧ 0 ≤ 1 / (n + 2 : ℝ) ∧
    (n + 1 : ℝ) / (n + 2) + 1 / (n + 2 : ℝ) = 1 := by
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  refine ⟨by positivity, by positivity, ?_⟩
  field_simp
  ring

lemma affineOrbitAverage_mem {K : Set E} (hK : Convex ℝ K)
    {f : E → E} (hf : MapsTo f K K) {x : E} (hx : x ∈ K) (n : ℕ) :
    affineOrbitAverage f x n ∈ K := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    obtain ⟨ha, hb, hab⟩ := average_weights n
    exact hK ih (hf.iterate (n + 1) hx) ha hb hab

lemma affineOrbitAverage_error {K : Set E} (hK : Convex ℝ K)
    {f : E → E} (hf : MapsTo f K K) (haff : AffineOn K f)
    {x : E} (hx : x ∈ K) (n : ℕ) :
    f (affineOrbitAverage f x n) - affineOrbitAverage f x n =
      (1 / (n + 1 : ℝ)) • (f^[n + 1] x - x) := by
  induction n with
  | zero => simp [affineOrbitAverage]
  | succ n ih =>
    obtain ⟨ha, hb, hab⟩ := average_weights n
    have he := haff _ (affineOrbitAverage_mem hK hf hx n) _
      (hf.iterate (n + 1) hx) _ _ ha hb hab
    simp only [affineOrbitAverage, Nat.cast_add, Nat.cast_one] at he ⊢
    rw [he]
    have hmul : ((n + 1 : ℝ) / (n + 2)) * (1 / (n + 1 : ℝ)) =
        1 / (n + 2 : ℝ) := by
      have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
      have h2 : (n + 2 : ℝ) ≠ 0 := by positivity
      field_simp
    calc
      _ = ((n + 1 : ℝ) / (n + 2)) •
          (f (affineOrbitAverage f x n) - affineOrbitAverage f x n) +
          (1 / (n + 2 : ℝ)) • (f (f^[n + 1] x) - f^[n + 1] x) := by module
      _ = (1 / (n + 2 : ℝ)) • (f^[n + 1] x - x) +
          (1 / (n + 2 : ℝ)) • (f (f^[n + 1] x) - f^[n + 1] x) := by
        rw [ih, smul_smul, hmul]
      _ = (1 / (n + 2 : ℝ)) • (f (f^[n + 1] x) - x) := by module
      _ = _ := by
        simp only [Function.iterate_succ_apply']
        congr 2
        ring

end Averages

section Topology
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

omit [T2Space E] in
lemma affineOrbitAverage_displacement_tendsto {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) {f : E → E}
    (hf : MapsTo f K K) (haff : AffineOn K f) {x : E} (hx : x ∈ K) :
    Tendsto (fun n => f (affineOrbitAverage f x n) - affineOrbitAverage f x n)
      atTop (𝓝 0) := by
  have hb : Bornology.IsVonNBounded ℝ (K - K) :=
    (hK.isVonNBounded ℝ).sub (hK.isVonNBounded ℝ)
  have hm : ∀ᶠ n : ℕ in atTop, f^[n + 1] x - x ∈ K - K :=
    Eventually.of_forall fun n => sub_mem_sub (hf.iterate (n + 1) hx) hx
  have ht : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  convert hb.smul_tendsto_zero hm ht using 1
  funext n
  exact affineOrbitAverage_error hconv hf haff hx n

/-- The averaging proof uses compactness in the given topology, without a
metrizability, completeness, or local convexity assumption. -/
theorem affine_single_fixed_point : MarkovKakutaniSpec.SingleMap.{u} := by
  intro E _ _ _ _ _ _ K hne hcompact hconv f hcont hmaps haff
  obtain ⟨x, hx⟩ := hne
  let a := affineOrbitAverage f x
  have hamem : ∀ n, a n ∈ K := affineOrbitAverage_mem hconv hmaps hx
  have hmapK : Filter.map a atTop ≤ 𝓟 K :=
    Filter.le_principal_iff.mpr (Filter.mem_map.mpr (Eventually.of_forall hamem))
  obtain ⟨y, hyK, hy⟩ := hcompact.exists_mapClusterPt hmapK
  have herr := affineOrbitAverage_displacement_tendsto hcompact hconv hmaps haff hx
  let l : Filter E := 𝓝 y ⊓ Filter.map a atTop
  have : l.NeBot := hy
  have hle : l ≤ 𝓝[K] y := by
    refine le_inf inf_le_left ?_
    exact inf_le_of_right_le hmapK
  have hd : Tendsto (fun z => f z - z) l (𝓝 (f y - y)) :=
    ((hcont y hyK).mono_left hle).sub (tendsto_id.mono_left inf_le_left)
  have hz : Tendsto (fun z => f z - z) l (𝓝 0) := by
    apply Tendsto.mono_left _ inf_le_right
    exact (tendsto_map'_iff).mpr herr
  exact ⟨y, hyK, sub_eq_zero.mp (tendsto_nhds_unique hd hz)⟩

/-- Markov–Kakutani, with commutativity needed only at points of K.
The empty family is included in both the finite induction and the compactness
argument. No invertibility or family equicontinuity is assumed. -/
theorem markov_kakutani : MarkovKakutaniSpec.CommonFixedPoint.{u, v} := by
  intro E _ _ _ _ _ _ K hne hcompact hconv ι f hcont hmaps haff hcomm
  classical
  let F : ι → Set E := fun i => {x ∈ K | f i x = x}
  have hFclosed : ∀ i, IsClosed (F i) := fun i =>
    hcompact.isClosed.isClosed_eq (hcont i) continuousOn_id
  have hFconv : ∀ i, Convex ℝ (F i) := by
    intro i x hx y hy a b ha hb hab
    refine ⟨hconv hx.1 hy.1 ha hb hab, ?_⟩
    rw [haff i x hx.1 y hy.1 a b ha hb hab, hx.2, hy.2]
  have hfinite : ∀ s : Finset ι, ∃ x ∈ K, ∀ i ∈ s, f i x = x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by simp⟩
    | @insert i s his ih =>
      let L : Set E := K ∩ ⋂ j ∈ s, F j
      have hLK : L ⊆ K := inter_subset_left
      have hLne : L.Nonempty := by
        obtain ⟨x, hx, hfix⟩ := ih
        refine ⟨x, hx, ?_⟩
        simp only [mem_iInter]
        exact fun j hj => ⟨hx, hfix j hj⟩
      have hLcompact : IsCompact L :=
        hcompact.inter_right (isClosed_biInter fun j _ => hFclosed j)
      have hLconv : Convex ℝ L :=
        hconv.inter (convex_iInter fun j => convex_iInter fun _ => hFconv j)
      have hLmaps : MapsTo (f i) L L := by
        intro x hx
        refine ⟨hmaps i hx.1, ?_⟩
        simp only [mem_iInter]
        intro j hj
        refine ⟨hmaps i hx.1, ?_⟩
        have hxj : x ∈ F j := mem_iInter.mp (mem_iInter.mp hx.2 j) hj
        rw [← hcomm i j x hx.1, hxj.2]
      obtain ⟨x, hx, hfix⟩ := affine_single_fixed_point E L hLne hLcompact hLconv
        (f i) ((hcont i).mono hLK) hLmaps
        (fun x hx y hy => haff i x hx.1 y hy.1)
      refine ⟨x, hx.1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hfix
      · exact (mem_iInter.mp (mem_iInter.mp hx.2 j) hj).2
  obtain ⟨x, hxK, hx⟩ := hcompact.inter_iInter_nonempty F hFclosed (fun s => by
    obtain ⟨x, hxK, hx⟩ := hfinite s
    refine ⟨x, hxK, ?_⟩
    simp only [mem_iInter]
    exact fun i hi => ⟨hxK, hx i hi⟩)
  exact ⟨x, hxK, fun i => (mem_iInter.mp hx i).2⟩

/-- Convert genuine self-maps of K to functions on the ambient space by
assigning the identity outside K. Only their restrictions are used. -/
theorem markov_kakutani_subtype : MarkovKakutaniSpec.SubtypeCommonFixedPoint.{u, v} := by
  intro E _ _ _ _ _ _ K hne hcompact hconv ι f hcont haff hcomm
  classical
  let g : ι → E → E := fun i x => if hx : x ∈ K then (f i ⟨x, hx⟩ : E) else x
  have hg (i : ι) (x : K) : g i x = (f i x : E) := by simp [g, x.property]
  have hgcont : ∀ i, ContinuousOn (g i) K := by
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp (hcont i)).congr (fun x => (hg i x).symm)
  have hgmaps : ∀ i, MapsTo (g i) K K := by
    intro i x hx
    rw [hg i ⟨x, hx⟩]
    exact (f i ⟨x, hx⟩).property
  have hgaff : ∀ i, AffineOn K (g i) := by
    intro i x hx y hy a b ha hb hab
    rw [hg i ⟨_, hconv hx hy ha hb hab⟩, hg i ⟨x, hx⟩, hg i ⟨y, hy⟩]
    exact haff i ⟨x, hx⟩ ⟨y, hy⟩ a b ha hb hab
  have hgcomm : ∀ i j, ∀ x ∈ K, g i (g j x) = g j (g i x) := by
    intro i j x hx
    rw [hg j ⟨x, hx⟩, hg i (f j ⟨x, hx⟩), hg i ⟨x, hx⟩, hg j (f i ⟨x, hx⟩)]
    exact congrArg Subtype.val (hcomm i j ⟨x, hx⟩)
  obtain ⟨x, hx, hfix⟩ := markov_kakutani E K hne hcompact hconv ι g
    hgcont hgmaps hgaff hgcomm
  refine ⟨⟨x, hx⟩, fun i => Subtype.ext ?_⟩
  exact (hg i ⟨x, hx⟩).symm.trans (hfix i)

end Topology

/-- Complex affine self-maps, with real convexity as in the manuscript. -/
theorem markov_kakutani_complex : MarkovKakutaniSpec.ComplexCommonFixedPoint.{u, v} := by
  intro E _ _ _ _ _ _
  let : Module ℝ E := Module.compHom E Complex.ofRealHom
  have : ContinuousSMul ℝ E :=
    ⟨(Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd⟩
  exact markov_kakutani_subtype E

end ExpandedFA.PartV
