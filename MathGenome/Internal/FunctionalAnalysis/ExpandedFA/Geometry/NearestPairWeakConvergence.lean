import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.NearestPairWeakConvergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.MinimumDisplacement
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
open Filter
open scoped Pointwise InnerProductSpace Topology
namespace ExpandedFA.Geometry.NearestPairWeakConvergence
universe u v

section WeakCompactness
variable (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The inverse Riesz map is continuous from the weak-star dual to the weak space.
Over complex scalars its evaluations are conjugate evaluations. -/
theorem continuous_weak_riesz_inverse :
    Continuous (fun f : WeakDual 𝕜 H =>
      toWeakSpace 𝕜 H ((InnerProductSpace.toDual 𝕜 H).symm (WeakDual.toStrongDual f))) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro g
  let z := (InnerProductSpace.toDual 𝕜 H).symm g
  have heq (f : WeakDual 𝕜 H) :
      g ((InnerProductSpace.toDual 𝕜 H).symm (WeakDual.toStrongDual f)) =
        star (f z) := by
    rw [← InnerProductSpace.toDual_symm_apply, ← inner_conj_symm,
      InnerProductSpace.toDual_symm_apply]
    rfl
  change Continuous (fun f : WeakDual 𝕜 H =>
    g ((InnerProductSpace.toDual 𝕜 H).symm (WeakDual.toStrongDual f)))
  simp_rw [heq]
  exact (WeakDual.eval_continuous z).star

/-- Hilbert balls are weakly compact, with no separability restriction. -/
theorem weak_closedBall_compact (r : ℝ) :
    IsCompact (toWeakSpace 𝕜 H '' Metric.closedBall (0 : H) r) := by
  have hh := (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (0 : StrongDual 𝕜 H) r).image
    (continuous_weak_riesz_inverse 𝕜 H)
  convert hh using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual 𝕜 H y), ?_, ?_⟩
    · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hy
    · simp
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(InnerProductSpace.toDual 𝕜 H).symm (WeakDual.toStrongDual f), ?_, rfl⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map] using hf

/-- Closed real-convex sets remain closed in the scalar-linear weak topology. -/
theorem weak_image_closed (C : Set H) (hc : IsClosed C)
    (hv : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C) :
    IsClosed (toWeakSpace 𝕜 H '' C) := by
  let := Hilbert.Conventions.realification 𝕜 H
  letI : IsScalarTower ℝ 𝕜 H := IsScalarTower.restrictScalars ℝ 𝕜 H
  letI : LocallyConvexSpace ℝ H := NormedSpace.toLocallyConvexSpace' 𝕜
  have hh := (show Convex ℝ C from hv).toWeakSpace_closure 𝕜
  rw [hc.closure_eq] at hh
  exact closure_eq_iff_isClosed.mp hh.symm

theorem weak_image_compact (C : Set H) (hc : IsClosed C)
    (hv : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C) (hb : Bornology.IsBounded C) :
    IsCompact (toWeakSpace 𝕜 H '' C) := by
  obtain ⟨r, hr⟩ := (isBounded_iff_forall_norm_le).mp hb
  apply (weak_closedBall_compact 𝕜 H r).of_isClosed_subset (weak_image_closed 𝕜 H C hc hv)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, by simpa using hr x hx, rfl⟩

/-- Eberlein–Šmulian applied to a weakly compact Hilbert ball. -/
theorem bounded_weak_subsequence (s : ℕ → H) (hb : Bornology.IsBounded (Set.range s)) :
    ∃ (a : H) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (fun n => toWeakSpace 𝕜 H (s (r n))) atTop (𝓝 (toWeakSpace 𝕜 H a)) := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).mp hb
  let B := Metric.closedBall (0 : H) R
  have hc := weak_closedBall_compact 𝕜 H R
  let e := toWeakSpace 𝕜 H
  have hind : @Topology.IsInducing H (WeakSpace 𝕜 H)
      (P1.EberleinSmulian.Spec.weakTopology 𝕜 H) inferInstance e := by
    letI : TopologicalSpace H := P1.EberleinSmulian.Spec.weakTopology 𝕜 H
    exact ⟨rfl⟩
  have hseq : P1.EberleinSmulian.Spec.HasWeaklyConvergentSubsequences 𝕜 H B := by
    letI : TopologicalSpace H := P1.EberleinSmulian.Spec.weakTopology 𝕜 H
    have hcomp : IsCompact B := hind.isCompact_iff.mpr hc
    have hcl : IsClosed B := by
      convert (weak_image_closed 𝕜 H B Metric.isClosed_closedBall (by
        let := Hilbert.Conventions.realification 𝕜 H
        exact convex_closedBall (0 : H) R)).preimage hind.continuous using 1
      exact ((toWeakSpace 𝕜 H).injective.preimage_image _).symm
    exact P1.EberleinSmulian.compact_implies_subsequences 𝕜 H B
      (hcl.closure_eq.symm ▸ hcomp)
  obtain ⟨a, r, hr, ht⟩ := hseq s (fun n => by
    simpa [B] using hR (s n) (Set.mem_range_self n))
  refine ⟨a, r, hr, ?_⟩
  letI : TopologicalSpace H := P1.EberleinSmulian.Spec.weakTopology 𝕜 H
  exact hind.tendsto_nhds_iff.mp ht

end WeakCompactness

/-- If one set is bounded, its weak compactness makes the difference weakly closed. -/
theorem bounded_attainment : Spec.BoundedAttainment.{u, v} := by
  intro 𝕜 H _ _ _ _ C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ hb
  have hp := (MinimumDisplacement.minimum_displacement
    𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂).1.1
  have hclosed : IsClosed (toWeakSpace 𝕜 H '' (C₂ - C₁)) := by
    rw [Set.image_sub]
    rcases hb with hb | hb
    · rw [sub_eq_add_neg]
      exact (weak_image_closed 𝕜 H C₂ hc₂ hv₂).add_right_of_isCompact
        (weak_image_compact 𝕜 H C₁ hc₁ hv₁ hb).neg
    · rw [sub_eq_add_neg]
      exact (weak_image_closed 𝕜 H C₁ hc₁ hv₁).neg.add_left_of_isCompact
        (weak_image_compact 𝕜 H C₂ hc₂ hv₂ hb)
  have hnormclosed : IsClosed (C₂ - C₁) := by
    convert hclosed.preimage (toWeakSpaceCLM 𝕜 H).continuous using 1
    exact ((toWeakSpace 𝕜 H).injective.preimage_image _).symm
  rwa [hnormclosed.closure_eq] at hp



section Fejer
variable (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Cancellation of the quadratic term makes a difference of squared distances
weakly continuous. -/
theorem weak_square_difference (s : ℕ → H) (a z w : H)
    (hs : Tendsto (fun n => toWeakSpace 𝕜 H (s n)) atTop (𝓝 (toWeakSpace 𝕜 H a))) :
    Tendsto (fun n => ‖s n-z‖^2 - ‖s n-w‖^2) atTop
      (𝓝 (‖a-z‖^2 - ‖a-w‖^2)) := by
  have hz := (WeakBilin.eval_continuous (topDualPairing 𝕜 H).flip
    (InnerProductSpace.toDualMap 𝕜 H z)).tendsto _ |>.comp hs
  have hw := (WeakBilin.eval_continuous (topDualPairing 𝕜 H).flip
    (InnerProductSpace.toDualMap 𝕜 H w)).tendsto _ |>.comp hs
  change Tendsto (fun n => ⟪z, s n⟫_𝕜) atTop (𝓝 ⟪z,a⟫_𝕜) at hz
  change Tendsto (fun n => ⟪w, s n⟫_𝕜) atTop (𝓝 ⟪w,a⟫_𝕜) at hw
  have hzR := RCLike.continuous_re.continuousAt.tendsto.comp hz
  have hwR := RCLike.continuous_re.continuousAt.tendsto.comp hw
  have heq (x : H) : ‖x-z‖^2 - ‖x-w‖^2 =
      (‖z‖^2 - 2 * RCLike.re ⟪z,x⟫_𝕜) -
        (‖w‖^2 - 2 * RCLike.re ⟪w,x⟫_𝕜) := by
    rw [norm_sub_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜),
      inner_re_symm x z, inner_re_symm x w]
    ring
  simp_rw [heq]
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul hzR)).sub
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hwR))

/-- Fejér monotonicity plus membership of every weak subsequential limit gives
weak convergence. Subsequence compactness follows from Hilbert boundedness. -/
theorem fejer_weak_convergence (s : ℕ → H) (A : Set H) (hne : A.Nonempty)
    (hstep : ∀ a ∈ A, ∀ n, ‖s (n+1)-a‖ ≤ ‖s n-a‖)
    (hcluster : ∀ (r : ℕ → ℕ), Tendsto r atTop atTop → ∀ a,
      Tendsto (fun n => toWeakSpace 𝕜 H (s (r n))) atTop (𝓝 (toWeakSpace 𝕜 H a)) →
      a ∈ A) :
    ∃ a ∈ A, Tendsto (fun n => toWeakSpace 𝕜 H (s n)) atTop (𝓝 (toWeakSpace 𝕜 H a)) := by
  have hanti (a : H) (ha : a ∈ A) : Antitone (fun n => ‖s n-a‖) :=
    antitone_nat_of_succ_le (hstep a ha)
  obtain ⟨z, hz⟩ := hne
  have hb : Bornology.IsBounded (Set.range s) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖s 0-z‖ + ‖z‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (norm_le_norm_sub_add (s n) z).trans (add_le_add (hanti z hz (Nat.zero_le n)) le_rfl)
  have hlim (a : H) (ha : a ∈ A) :
      ∃ l : ℝ, Tendsto (fun n => ‖s n-a‖^2) atTop (𝓝 l) := by
    have hh := tendsto_atTop_ciInf (hanti a ha)
      (show BddBelow (Set.range (fun n => ‖s n-a‖)) from ⟨0, by
        rintro _ ⟨n, rfl⟩; exact norm_nonneg _⟩)
    exact ⟨_, hh.pow 2⟩
  obtain ⟨a, r, hr, hta⟩ := bounded_weak_subsequence 𝕜 H s hb
  have ha := hcluster r hr.tendsto_atTop a hta
  have hunique (t : ℕ → ℕ) (ht : Tendsto t atTop atTop) (b : H)
      (htb : Tendsto (fun n => toWeakSpace 𝕜 H (s (t n))) atTop (𝓝 (toWeakSpace 𝕜 H b))) : b = a := by
    have hba := hcluster t ht b htb
    obtain ⟨la, hla⟩ := hlim a ha
    obtain ⟨lb, hlb⟩ := hlim b hba
    have hd := hla.sub hlb
    have hda := weak_square_difference 𝕜 H (s ∘ r) a a b hta
    have hdb := weak_square_difference 𝕜 H (s ∘ t) b a b htb
    have hea := tendsto_nhds_unique (hd.comp hr.tendsto_atTop) hda
    have heb := tendsto_nhds_unique (hd.comp ht) hdb
    have he : ‖a-b‖^2 = 0 := by
      simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_sub,
        sub_zero, norm_sub_rev b a] at hea heb
      linarith
    exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))).symm
  refine ⟨a, ha, tendsto_of_subseq_tendsto ?_⟩
  intro ns hns
  have hbn : Bornology.IsBounded (Set.range (s ∘ ns)) :=
    hb.subset (Set.range_comp_subset_range _ _)
  obtain ⟨b, t, ht, htb⟩ := bounded_weak_subsequence 𝕜 H (s ∘ ns) hbn
  have heq := hunique (ns ∘ t) (hns.comp ht.tendsto_atTop) b htb
  exact ⟨t, heq ▸ htb⟩

end Fejer


/-- An attained minimum displacement is a two-cycle of the two projectors. -/
theorem nearest_pair_projections (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C₁ C₂ : Set H) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hc₁ : IsClosed C₁) (hc₂ : IsClosed C₂)
    (hv₁ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₁)
    (hv₂ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₂)
    (a b : H) (ha : a ∈ C₁) (hb : b ∈ C₂)
    (hp : b-a = MinimumDisplacement.Spec.minimumVector C₁ C₂) :
    Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁ b = a ∧
    Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂ a = b := by
  have hmin := (MinimumDisplacement.minimum_displacement
    𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂).1.2
  have haMin : ∀ z ∈ C₁, ‖b-a‖ ≤ ‖b-z‖ := by
    intro z hz
    rw [hp]
    exact hmin _ (subset_closure (Set.sub_mem_sub hb hz))
  have hbMin : ∀ z ∈ C₂, ‖a-b‖ ≤ ‖a-z‖ := by
    intro z hz
    rw [norm_sub_rev a b, norm_sub_rev a z, hp]
    exact hmin _ (subset_closure (Set.sub_mem_sub hz ha))
  constructor
  · exact (Hilbert.Projection.existsUnique_nearestPoint 𝕜 H C₁ hne₁ hc₁ hv₁ b).unique
      (Hilbert.Projection.convexProjection_spec 𝕜 H C₁ hne₁ hc₁ hv₁ b) ⟨ha, haMin⟩
  · exact (Hilbert.Projection.existsUnique_nearestPoint 𝕜 H C₂ hne₂ hc₂ hv₂ a).unique
      (Hilbert.Projection.convexProjection_spec 𝕜 H C₂ hne₂ hc₂ hv₂ a) ⟨hb, hbMin⟩

/-- Weak convergence to a nearest pair; the limiting pair can depend on the orbit. -/
theorem weak_nearest_pair : Spec.WeakNearestPair.{u,v} := by
  intro 𝕜 H _ _ _ _ C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ p P₁ P₂ hp s hs
  let A : Set H := {a | a ∈ C₁ ∧ a + p ∈ C₂}
  have hneA : A.Nonempty := by
    obtain ⟨b, hb, a, ha, hab⟩ := Set.mem_sub.mp hp
    refine ⟨a, ha, ?_⟩
    have : a+p = b := by rw [← hab]; abel
    rwa [this]
  have hcycle (a : H) (ha : a ∈ A) : P₁ (a+p) = a ∧ P₂ a = a+p :=
    nearest_pair_projections 𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂
      a (a+p) ha.1 ha.2 (by abel)
  have hmem₁ (n : ℕ) : s (2*n+1) ∈ C₁ := by
    rw [MinimumDisplacement.odd_step hs]
    exact (Hilbert.Projection.convexProjection_spec 𝕜 H C₁ hne₁ hc₁ hv₁ _).1
  have hmem₂ (n : ℕ) : s (2*n+2) ∈ C₂ := by
    rw [MinimumDisplacement.even_step hs]
    exact (Hilbert.Projection.convexProjection_spec 𝕜 H C₂ hne₂ hc₂ hv₂ _).1
  have hstep (a : H) (ha : a ∈ A) (n : ℕ) :
      ‖s (2*(n+1)+1)-a‖ ≤ ‖s (2*n+1)-a‖ := by
    obtain ⟨h₁, h₂⟩ := hcycle a ha
    calc
      ‖s (2*(n+1)+1)-a‖ = ‖P₁ (s (2*n+2))-P₁ (a+p)‖ := by
        rw [MinimumDisplacement.odd_step hs, show 2*(n+1) = 2*n+2 by omega, h₁]
      _ ≤ ‖s (2*n+2)-(a+p)‖ :=
        Hilbert.Projection.convexProjection_nonexpansive 𝕜 H C₁ hne₁ hc₁ hv₁ _ _
      _ = ‖P₂ (s (2*n+1))-P₂ a‖ := by rw [MinimumDisplacement.even_step hs, h₂]
      _ ≤ ‖s (2*n+1)-a‖ :=
        Hilbert.Projection.convexProjection_nonexpansive 𝕜 H C₂ hne₂ hc₂ hv₂ _ _
  have hgap := (MinimumDisplacement.minimum_displacement
    𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂).2.2 s hs |>.2
  have heven (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (a : H)
      (ha : Tendsto (fun n => toWeakSpace 𝕜 H (s (2*r n+1))) atTop (𝓝 (toWeakSpace 𝕜 H a))) :
      Tendsto (fun n => toWeakSpace 𝕜 H (s (2*r n+2))) atTop
        (𝓝 (toWeakSpace 𝕜 H (a+p))) := by
    have hg := (toWeakSpaceCLM 𝕜 H).continuous.tendsto p |>.comp (hgap.comp hr)
    convert ha.add hg using 1
    · ext n
      change toWeakSpace 𝕜 H (s (2*r n+2)) =
        toWeakSpace 𝕜 H (s (2*r n+1)) + toWeakSpaceCLM 𝕜 H (s (2*r n+2) - s (2*r n+1))
      rw [toWeakSpaceCLM_eq_toWeakSpace, ← map_add]
      congr 1
      abel
    · rw [map_add, toWeakSpaceCLM_eq_toWeakSpace]
  obtain ⟨a, ha, hta⟩ := fejer_weak_convergence 𝕜 H (fun n => s (2*n+1)) A hneA hstep (by
    intro r hr a hta
    constructor
    · have hm := (weak_image_closed 𝕜 H C₁ hc₁ hv₁).mem_of_tendsto hta
        (Eventually.of_forall fun n => ⟨s (2*r n+1), hmem₁ (r n), rfl⟩)
      obtain ⟨x, hx, hxa⟩ := hm
      exact (toWeakSpace 𝕜 H).injective hxa ▸ hx
    · have hm := (weak_image_closed 𝕜 H C₂ hc₂ hv₂).mem_of_tendsto (heven r hr a hta)
        (Eventually.of_forall fun n => ⟨s (2*r n+2), hmem₂ (r n), rfl⟩)
      obtain ⟨x, hx, hxa⟩ := hm
      exact (toWeakSpace 𝕜 H).injective hxa ▸ hx)
  exact ⟨a, ha.1, a+p, ha.2, by abel, hta, heven id tendsto_id a hta⟩

end ExpandedFA.Geometry.NearestPairWeakConvergence
