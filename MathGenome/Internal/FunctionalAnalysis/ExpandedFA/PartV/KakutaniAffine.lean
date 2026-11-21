import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.KakutaniAffine
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.MilmanConverse
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24KreinMilman
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
Kakutani's theorem (`fa2:p5:kakutani-affine`, paper.tex:23219–23244).
We minimize the nonempty closed convex invariant subsets of K. The closed
convex hull of the orbit of any midpoint is then that minimal set. Milman's
converse puts an extreme point in the midpoint orbit closure. Compactness
of the pair orbit supplies limiting endpoints, which extremality identifies.
Inverses and pointwise equicontinuity rule out this diagonal limit unless
the original endpoints coincide. Thus the minimal set is a fixed singleton.
All compactness and closure operations use the given topology.
-/

universe u v

namespace ExpandedFA.PartV

open Set Filter
open scoped Topology
open KakutaniAffineSpec ExpandedFA.P1.ExtremeAffineLiftingSpec

section Real

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  {G : Type v} [Group G] {K : Set E} (T : G → K ≃ₜ K)

/-- Invariance is relative to K, and does not require ambient extensions. -/
def AffineGroupInvariant (Q : Set E) : Prop :=
  ∀ g (x : K), (x : E) ∈ Q → (T g x : E) ∈ Q

private def Admissible (Q : Set E) : Prop :=
  Q.Nonempty ∧ IsClosed Q ∧ Convex ℝ Q ∧ Q ⊆ K ∧ AffineGroupInvariant T Q

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Group G] in
/-- Compactness gives lower bounds for chains of nonempty invariant convex sets. -/
private theorem exists_minimal_affineGroupInvariant (hne : K.Nonempty) (hK : IsCompact K)
    (hc : Convex ℝ K) : ∃ Q, Minimal (Admissible T) Q := by
  apply zorn_superset {Q | Admissible T Q}
  intro F hFS hF
  obtain rfl | hFn := F.eq_empty_or_nonempty
  · refine ⟨K, ⟨hne, hK.isClosed, hc, Subset.rfl, ?_⟩, ?_⟩
    · intro g x _
      exact (T g x).property
    · simp
  have hsub : ⋂₀ F ⊆ K :=
    (sInter_subset_of_mem hFn.choose_spec).trans (hFS hFn.choose_spec).2.2.2.1
  refine ⟨⋂₀ F, ⟨?_, isClosed_sInter (fun Q hQ => (hFS hQ).2.1),
    convex_sInter (fun Q hQ => (hFS hQ).2.2.1), hsub, ?_⟩,
    fun Q hQ => sInter_subset_of_mem hQ⟩
  · have : Nonempty (↥F) := hFn.to_subtype
    rw [sInter_eq_iInter]
    refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
      (fun A B => ?_) (fun A => (hFS A.property).1)
      (fun A => hK.of_isClosed_subset (hFS A.property).2.1 (hFS A.property).2.2.2.1)
      (fun A => (hFS A.property).2.1)
    obtain h | h := hF.total A.property B.property
    · exact ⟨A, Subset.rfl, h⟩
    · exact ⟨B, h, Subset.rfl⟩
  · intro g x hx
    exact mem_sInter.mpr fun Q hQ => (hFS hQ).2.2.2.2 g x (mem_sInter.mp hx Q hQ)

/-- The closed convex hull of an orbit is invariant, even for maps defined only on K. -/
theorem affineGroupInvariant_closedConvexOrbit
    (hK : IsCompact K) (hc : Convex ℝ K)
    (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (haff : ∀ g, PreservesConvexCombinations (T g)) (z : K) :
    AffineGroupInvariant T (closure (convexHull ℝ (range fun g => (T g z : E)))) := by
  classical
  let A : Set E := range fun g => (T g z : E)
  let H : Set E := closure (convexHull ℝ A)
  have hHc : Convex ℝ H := (convex_convexHull ℝ A).closure
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro g x hx
  let B : Set E := Subtype.val '' {y : K | (T g y : E) ∈ H}
  have hBc : IsCompact B :=
    ((isClosed_closure.preimage (continuous_subtype_val.comp (T g).continuous)).isCompact).image
      continuous_subtype_val
  have hBv : Convex ℝ B := by
    rintro a ⟨a', ha, rfl⟩ b ⟨b', hb, rfl⟩ s t hs ht hst
    let w : K := ⟨s • (a' : E) + t • (b' : E), hc a'.property b'.property hs ht hst⟩
    refine ⟨w, ?_, rfl⟩
    change (T g w : E) ∈ H
    rw [haff g a' b' w s t hs ht hst rfl]
    exact hHc ha hb hs ht hst
  have hAB : A ⊆ B := by
    rintro _ ⟨h, rfl⟩
    refine ⟨T h z, ?_, rfl⟩
    change (T g (T h z) : E) ∈ H
    rw [← hmul]
    exact subset_closure (subset_convexHull ℝ A (mem_range_self (g * h)))
  have hHB : H ⊆ B := closure_minimal (convexHull_min hAB hBv) hBc.isClosed
  obtain ⟨y, hy, hyx⟩ := hHB hx
  have : y = x := Subtype.ext hyx
  change (T g y : E) ∈ H at hy
  rw [this] at hy
  exact hy

omit [Module ℝ E] [ContinuousSMul ℝ E] in
/-- Inverses and equicontinuity prevent the orbit closure of a distinct pair
from meeting the diagonal. Pointwise equicontinuity at the proposed limit
suffices, so no uniform-equicontinuity hypothesis is added. -/
theorem diagonal_notMem_pairOrbitClosure
    (hone : ∀ x, T 1 x = x)
    (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (heq : EquicontinuousOnK T) (x y q : K) (hxy : x ≠ y) :
    (q, q) ∉ closure (range fun g => (T g x, T g y)) := by
  intro hcl
  have hdiff : (x : E) - (y : E) ≠ 0 := by
    intro h
    exact hxy (Subtype.ext (sub_eq_zero.mp h))
  let W : Set E := {(x : E) - (y : E)}ᶜ
  have hW : W ∈ 𝓝 (0 : E) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simpa [W] using hdiff.symm)
  have hsub : Tendsto (fun p : E × E => p.1 - p.2) (𝓝 (0, 0)) (𝓝 (0 : E)) := by
    have hc : Continuous (fun p : E × E => p.1 - p.2) := by fun_prop
    have ht := hc.tendsto ((0 : E), 0)
    rw [sub_self] at ht
    exact ht
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.mp (by
    simpa only [nhds_prod_eq, Filter.mem_map] using hsub hW)
  have hN : ∀ᶠ p : K × K in 𝓝 (q, q),
      (∀ g, (T g p.1 : E) - (T g q : E) ∈ U) ∧
      (∀ g, (T g p.2 : E) - (T g q : E) ∈ V) :=
    ((continuous_fst.tendsto (q, q)).eventually (heq q U hU)).and
      ((continuous_snd.tendsto (q, q)).eventually (heq q V hV))
  obtain ⟨p, hp, hpN⟩ := (mem_closure_iff_frequently.mp hcl |>.and_eventually hN).exists
  obtain ⟨g, rfl⟩ := hp
  have hx : T g⁻¹ (T g x) = x := by rw [← hmul, inv_mul_cancel, hone]
  have hy : T g⁻¹ (T g y) = y := by rw [← hmul, inv_mul_cancel, hone]
  have hbad := hUV (show ((T g⁻¹ (T g x) : E) - (T g⁻¹ q : E),
      (T g⁻¹ (T g y) : E) - (T g⁻¹ q : E)) ∈ U ×ˢ V from
        ⟨hpN.1 g⁻¹, hpN.2 g⁻¹⟩)
  have hcanc : ((T g⁻¹ (T g x) : E) - (T g⁻¹ q : E)) -
      ((T g⁻¹ (T g y) : E) - (T g⁻¹ q : E)) = (x : E) - (y : E) := by
    rw [hx, hy]
    abel
  exact hbad (by simpa only [hcanc] using Set.mem_singleton ((x : E) - (y : E)))

/-- Kakutani's equicontinuous affine-group theorem in the original real topology. -/
theorem real_kakutani_affine : realKakutaniType.{u, v} := by
  intro E _ _ _ _ _ _ _ G _ K T hne hK hc hone hmul haff heq
  classical
  obtain ⟨Q, hQ⟩ := exists_minimal_affineGroupInvariant T hne hK hc
  obtain ⟨hQn, hQclosed, hQconv, hQK, hQi⟩ := hQ.prop
  have hQc : IsCompact Q := hK.of_isClosed_subset hQclosed hQK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsingle : Q.Subsingleton := by
    intro x hx y hy
    by_contra hxy
    let x' : K := ⟨x, hQK hx⟩
    let y' : K := ⟨y, hQK hy⟩
    have hmidQ : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ Q :=
      hQconv hx hy (by norm_num) (by norm_num) (by norm_num)
    let z : K := ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y, hQK hmidQ⟩
    let A : Set E := range fun g => (T g z : E)
    let H : Set E := closure (convexHull ℝ A)
    have hHQ : H ⊆ Q := closure_minimal
      (convexHull_min (by rintro _ ⟨g, rfl⟩; exact hQi g z hmidQ) hQconv) hQclosed
    have hQH : Q = H := hQ.eq_of_ge
      ⟨⟨(T 1 z : E), subset_closure (subset_convexHull ℝ A (mem_range_self 1))⟩,
        isClosed_closure, (convex_convexHull ℝ A).closure, hHQ.trans hQK,
        affineGroupInvariant_closedConvexOrbit T hK hc hmul haff z⟩ hHQ
    obtain ⟨q, hqQ, hqext⟩ := ExpandedFA.P1.real_compact_convex_extremePoint Q hQn hQc hQconv
    have hqA : q ∈ closure A := ExpandedFA.P1.real_milman_converse Q A hQH hQc hqext
    let P : Set (K × K) := closure (range fun g => (T g x', T g y'))
    have hPc : IsCompact P := isClosed_closure.isCompact
    let m : K × K → E := fun p =>
      (1 / 2 : ℝ) • (p.1 : E) + (1 / 2 : ℝ) • (p.2 : E)
    have hm : Continuous m := by fun_prop
    have hAim : A ⊆ m '' P := by
      rintro _ ⟨g, rfl⟩
      refine ⟨(T g x', T g y'), subset_closure (mem_range_self g), ?_⟩
      exact (haff g x' y' z (1/2) (1/2) (by norm_num) (by norm_num)
        (by norm_num) rfl).symm
    obtain ⟨p, hp, hpq⟩ := closure_minimal hAim (hPc.image hm).isClosed hqA
    have hPR : P ⊆ {p : K × K | (p.1 : E) ∈ Q ∧ (p.2 : E) ∈ Q} := by
      apply closure_minimal
      · rintro _ ⟨g, rfl⟩
        exact ⟨hQi g x' hx, hQi g y' hy⟩
      · exact (hQclosed.preimage (continuous_subtype_val.comp continuous_fst)).inter
          (hQclosed.preimage (continuous_subtype_val.comp continuous_snd))
    have hhalf : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    have hmid : q = (1/2 : ℝ) • (p.1 : E) + (1 - (1/2 : ℝ)) • (p.2 : E) := by
      rw [hhalf]
      exact hpq.symm
    obtain ⟨hpa, hpb⟩ := hqext.2 (p.1 : E) (hPR hp).1 (p.2 : E) (hPR hp).2
      (1/2) (by norm_num) (by norm_num) hmid
    let q' : K := ⟨q, hQK hqQ⟩
    have hpqq : p = (q', q') := Prod.ext (Subtype.ext hpa) (Subtype.ext hpb)
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    exact diagonal_notMem_pairOrbitClosure T hone hmul heq x' y' q' hxy' (hpqq ▸ hp)
  obtain ⟨x, hx⟩ := hQn
  refine ⟨⟨x, hQK hx⟩, fun g => Subtype.ext ?_⟩
  exact hsingle (hQi g ⟨x, hQK hx⟩ hx) hx

end Real

/-- Complex scalars are restricted to real scalars without changing the topology. -/
theorem complex_kakutani_affine : complexKakutaniType.{u, v} := by
  intro E _ _ _ _ _ _ _ G _ K T hne hK hc hone hmul haff heq
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact real_kakutani_affine K T hne hK hc hone hmul haff heq

end ExpandedFA.PartV
