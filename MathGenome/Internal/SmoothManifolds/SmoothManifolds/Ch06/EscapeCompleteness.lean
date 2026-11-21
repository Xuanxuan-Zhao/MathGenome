import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.EscapeCompleteness
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.MaximalFlow
import Mathlib.Topology.Compactness.Compact

noncomputable section
namespace SmoothManifolds.EscapeCompleteness
open ModelData AtlasData TangentBundleData VectorFieldData IntegralCurveData
  MaximalFlowData Set Filter
open scoped Topology
universe u

section Families

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
  (X : SmoothField B) (F : CurveFamily M) (hF : IsMaximalFamily X F)

include X hF

/-- Openness at the zero-time section and compactness provide one two-sided
restart time valid at every state in K. -/
theorem uniform_restart (K : Set M) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ K,
      δ ∈ (F.interval q).carrier ∧ -δ ∈ (F.interval q).carrier := by
  have hD := (MaximalFlow.domain_open_smooth S B X F hF).1
  obtain ⟨U, V, hU, _, h0U, hKV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) hK hD
      (by rintro ⟨t, q⟩ ⟨ht, _⟩; simp only [mem_singleton_iff] at ht
          subst t; exact (hF q).1)
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (h0U (mem_singleton 0)))
  let δ : ℝ := min (-a) b / 2
  have ha : 0 < -a := by linarith [hab.1]
  have hb : 0 < b := hab.2
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hda : δ < -a := by dsimp [δ]; linarith [min_le_left (-a) b]
  have hdb : δ < b := by dsimp [δ]; linarith [min_le_right (-a) b]
  refine ⟨δ, hd, fun q hq => ?_⟩
  constructor
  · exact hUV (show (δ, q) ∈ U ×ˢ V from ⟨hsub ⟨by linarith, hdb⟩, hKV hq⟩)
  · exact hUV (show (-δ, q) ∈ U ×ˢ V from
      ⟨hsub ⟨by linarith, by linarith⟩, hKV hq⟩)

/-- Restarting a visit to K moves the original lifespan by the same amount. -/
theorem uniform_lifespan_extension (K : Set M) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p t, t ∈ (F.interval p).carrier → F.curve p t ∈ K →
      t + δ ∈ (F.interval p).carrier ∧ t - δ ∈ (F.interval p).carrier := by
  obtain ⟨δ, hd, hδ⟩ := uniform_restart X F hF K hK
  refine ⟨δ, hd, fun p t ht hK => ?_⟩
  have heq := (MaximalFlow.lifespan_flow_law S B X F hF p t ht).1
  obtain ⟨hp, hn⟩ := hδ (F.curve p t) hK
  rw [heq] at hp hn
  change t + -δ ∈ (F.interval p).carrier at hn
  exact ⟨hp, by simpa only [sub_eq_add_neg] using hn⟩

/-- A finite upper bound already suffices for the right escape estimate. -/
theorem family_escape_right (p : M) (b : ℝ)
    (hb : b ∈ upperBounds (F.interval p).carrier) (K : Set M) (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ (F.interval p).carrier,
      b - ε < t → F.curve p t ∉ K := by
  obtain ⟨δ, hd, hδ⟩ := uniform_lifespan_extension X F hF K hK
  refine ⟨δ, hd, fun t ht hbt hKt => ?_⟩
  have := hb (hδ p t ht hKt).1
  linarith

theorem family_escape_left (p : M) (a : ℝ)
    (ha : a ∈ lowerBounds (F.interval p).carrier) (K : Set M) (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ (F.interval p).carrier,
      t < a + ε → F.curve p t ∉ K := by
  obtain ⟨δ, hd, hδ⟩ := uniform_lifespan_extension X F hF K hK
  refine ⟨δ, hd, fun t ht hta hKt => ?_⟩
  have := ha (hδ p t ht hKt).2
  linarith

/-- If one state is an equilibrium, translation of its global constant
solution makes the original maximal lifespan global as well. -/
theorem family_complete_of_equilibrium_visit (p : M) (t : ℝ)
    (ht : t ∈ (F.interval p).carrier) (hz : X.val (F.curve p t) = 0) :
    (F.interval p).carrier = univ := by
  have he := IntegralCurves.maximal_unique S B X (F.curve p t)
    (F.interval (F.curve p t)) D13Unified.OpenTimeInterval.whole
    (F.curve (F.curve p t)) (fun _ => F.curve p t)
    (hF (F.curve p t)) (IntegralCurves.equilibrium_maximal X (F.curve p t) hz)
  have hs := (MaximalFlow.lifespan_flow_law S B X F hF p t ht).1
  apply eq_univ_of_forall
  intro r
  have hr : r - t ∈ (F.interval (F.curve p t)).carrier := by
    rw [he.1]; exact mem_univ _
  rw [hs] at hr
  simpa only [mem_ofPred_eq, add_sub_cancel] using hr

/-- A trajectory contained in a compact set cannot have either finite bound. -/
theorem family_complete_of_compact_range (p : M) (K : Set M) (hK : IsCompact K)
    (hrange : ∀ t ∈ (F.interval p).carrier, F.curve p t ∈ K) :
    (F.interval p).carrier = univ := by
  obtain ⟨δ, hd, hδ⟩ := uniform_lifespan_extension X F hF K hK
  have hAbove : ¬ BddAbove (F.interval p).carrier := by
    intro hb
    obtain ⟨t, ht, hbt⟩ := exists_lt_of_lt_csSup (F.interval p).nonempty
      (show sSup (F.interval p).carrier - δ < sSup (F.interval p).carrier by linarith)
    have := le_csSup hb (hδ p t ht (hrange t ht)).1
    linarith
  have hBelow : ¬ BddBelow (F.interval p).carrier := by
    intro hb
    obtain ⟨t, ht, htb⟩ := exists_lt_of_csInf_lt (F.interval p).nonempty
      (show sInf (F.interval p).carrier < sInf (F.interval p).carrier + δ by linarith)
    have := csInf_le hb (hδ p t ht (hrange t ht)).2
    linarith
  exact (F.interval p).ordConnected.isPreconnected.eq_univ_of_unbounded hBelow hAbove

/-- Outside the support the field vanishes; otherwise the whole trajectory is
confined to that compact support. Both cases give a global maximal lifespan. -/
theorem family_compact_support_complete (hK : IsCompact (sectionSupport X.val)) (p : M) :
    (F.interval p).carrier = univ := by
  classical
  by_cases hrange : ∀ t ∈ (F.interval p).carrier, F.curve p t ∈ sectionSupport X.val
  · exact family_complete_of_compact_range X F hF p _ hK hrange
  · push Not at hrange
    obtain ⟨t, ht, hnot⟩ := hrange
    apply family_complete_of_equilibrium_visit X F hF p t ht
    by_contra hz
    exact hnot (subset_closure hz)

omit F hF in
/-- Compare any maximal curve with the simultaneous family, only on its actual
domain. This makes the public conclusions independent of the chosen family. -/
theorem compare_family (p : M) (I : D13Unified.OpenTimeInterval) (γ : ℝ → M)
    (hγ : IsMaximalThrough X p I γ) :
    ∃ F : CurveFamily M, IsMaximalFamily X F ∧
      I.carrier = (F.interval p).carrier ∧ EqOn γ (F.curve p) I.carrier := by
  obtain ⟨F, hF⟩ := MaximalFlow.maximal_family_exists S B X
  exact ⟨F, hF, IntegralCurves.maximal_unique S B X p I (F.interval p)
    γ (F.curve p) hγ (hF p)⟩

end Families

/-- Escape at a finite right endpoint, for every maximal integral curve. -/
theorem escape_right :
    Specs.SmoothManifolds.Ch06.EscapeCompleteness.escape_rightType.{u} := by
  intro n M _ S B X p I γ hγ b hb K hK
  obtain ⟨F, hF, hI, heq⟩ := compare_family X p I γ hγ
  obtain ⟨ε, hε, hescape⟩ := family_escape_right X F hF p b
    (by rw [← hI]; exact hb.1) K hK
  refine ⟨ε, hε, fun t ht hbt => ?_⟩
  rw [heq ht]
  exact hescape t (hI ▸ ht) hbt

/-- Escape at a finite left endpoint, with no support assumption. -/
theorem escape_left :
    Specs.SmoothManifolds.Ch06.EscapeCompleteness.escape_leftType.{u} := by
  intro n M _ S B X p I γ hγ a ha K hK
  obtain ⟨F, hF, hI, heq⟩ := compare_family X p I γ hγ
  obtain ⟨ε, hε, hescape⟩ := family_escape_left X F hF p a
    (by rw [← hI]; exact ha.1) K hK
  refine ⟨ε, hε, fun t ht hta => ?_⟩
  rw [heq ht]
  exact hescape t (hI ▸ ht) hta

/-- Every compactly supported smooth field on a boundaryless manifold is complete. -/
theorem compact_support_complete :
    Specs.SmoothManifolds.Ch06.EscapeCompleteness.compact_support_completeType.{u} := by
  intro n M _ S B X hK p I γ hγ
  obtain ⟨F, hF, hI, _⟩ := compare_family X p I γ hγ
  exact hI.trans (family_compact_support_complete X F hF hK p)

/-- The support is closed in the base, and hence compact when the base is compact. -/
theorem compact_manifold_complete :
    Specs.SmoothManifolds.Ch06.EscapeCompleteness.compact_manifold_completeType.{u} := by
  intro n M _ _ S B X p I γ hγ
  exact compact_support_complete S B X isClosed_closure.isCompact p I γ hγ

end SmoothManifolds.EscapeCompleteness
