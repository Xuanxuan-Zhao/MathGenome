import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HyperbolicFormBoundsAndCarrier
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTriple
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Module.Basic

/-!
Uniform bounds and separable reducing carriers for the first paragraph of
`fa2:p3:hyperbolic-triple`, paper.tex:15253–15280. Scalar C¹ regularity is used
through secant slopes and Banach–Steinhaus; the finite-word carrier retains the
original V and H norms. Both scalar testing and the V′-valued distributional
equation lift to the ambient spaces, including L² acceleration membership.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff NNReal
universe u v w
namespace ExpandedFA.Evolution.HyperbolicFormBoundsAndCarrier
open HyperbolicFormSpec

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Banach–Steinhaus in each variable, with no countability assumption on I. -/
theorem bilinear_uniform_boundedness {I : Type w} (a : I → Form V)
    (h : ∀ u v, ∃ C : ℝ, ∀ i, ‖a i u v‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖a i‖ ≤ C := by
  apply P1.C07UniformBoundedness.uniform_boundedness ℝ V (StrongDual ℝ V) I a
  intro u
  obtain ⟨C, _, hC⟩ :=
    P1.C07UniformBoundedness.uniform_boundedness ℝ V ℝ I (fun i => a i u) (h u)
  exact ⟨C, hC⟩

@[simp] theorem representingOperator_inner (a : Form V) (u v : V) :
    inner ℝ (representingOperator a u) v = a u v := by
  change (InnerProductSpace.toDual ℝ V) ((InnerProductSpace.toDual ℝ V).symm (a u)) v = _
  rw [LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem representingOperator_norm (a : Form V) :
    ‖representingOperator a‖ = ‖a‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (representingOperator a) (norm_nonneg a)
    intro u
    change ‖(InnerProductSpace.toDual ℝ V).symm (a u)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact a.le_opNorm u
  · apply ContinuousLinearMap.opNorm_le_bound a (norm_nonneg (representingOperator a))
    intro u
    have hn : ‖a u‖ = ‖representingOperator a u‖ :=
      (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ V).symm (a u)).symm
    rw [hn]
    exact (representingOperator a).le_opNorm u

theorem representingOperator_selfAdjoint (a : Form V) (ha : ∀ u v, a u v = a v u) :
    IsSelfAdjoint (representingOperator a) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  change inner ℝ (representingOperator a u) v = inner ℝ u (representingOperator a v)
  rw [representingOperator_inner, real_inner_comm (representingOperator a v) u, representingOperator_inner]
  exact ha u v

theorem representation : RepresentationExpected (V := V) := by
  intro a
  exact ⟨representingOperator_inner a, representingOperator_norm a,
    representingOperator_selfAdjoint a⟩

/-- All secants, not just difference quotients at a fixed point, are uniformly bounded. -/
theorem form_secants_bounded (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T,
      ‖a t - a s‖ ≤ C * ‖t - s‖ := by
  let Q : (Set.Icc 0 T × Set.Icc 0 T) → Form V :=
    fun p => ((p.2 : ℝ) - (p.1 : ℝ))⁻¹ • (a p.2 - a p.1)
  have hQ : ∀ u v, ∃ K : ℝ, ∀ p, ‖Q p u v‖ ≤ K := by
    intro u v
    obtain ⟨K, hK⟩ := (ha u v).exists_lipschitzOnWith (by decide)
      (convex_Icc 0 T) isCompact_Icc
    refine ⟨K, ?_⟩
    intro p
    change ‖(((p.2 : ℝ) - (p.1 : ℝ))⁻¹) • (a p.2 u v - a p.1 u v)‖ ≤ _
    rw [norm_smul, norm_inv]
    by_cases hp : (p.2 : ℝ) = (p.1 : ℝ)
    · simp [hp]
    · calc
        ‖(p.2 : ℝ) - (p.1 : ℝ)‖⁻¹ * ‖a p.2 u v - a p.1 u v‖ ≤
            ‖(p.2 : ℝ) - (p.1 : ℝ)‖⁻¹ * ((K : ℝ) * ‖(p.2 : ℝ) - (p.1 : ℝ)‖) :=
          mul_le_mul_of_nonneg_left (hK.norm_sub_le p.2.property p.1.property)
            (inv_nonneg.mpr (norm_nonneg _))
        _ = K := by
          have hn : ‖(p.2 : ℝ) - (p.1 : ℝ)‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)
          field_simp
  obtain ⟨C, hC, hbound⟩ := bilinear_uniform_boundedness Q hQ
  refine ⟨C, hC, ?_⟩
  intro s hs t ht
  by_cases hts : t = s
  · subst t
    have he : a s - a s = 0 := sub_self (a s)
    rw [he, ContinuousLinearMap.opNorm_zero]
    simp
  · have hh := hbound (⟨s, hs⟩, ⟨t, ht⟩)
    change ‖(t - s)⁻¹ • (a t - a s)‖ ≤ C at hh
    apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
    intro u v
    have hscalar := ((t - s)⁻¹ • (a t - a s)).le_of_opNorm₂_le_of_le hh
      (le_refl ‖u‖) (le_refl ‖v‖)
    change ‖(t - s)⁻¹ • ((a t - a s) u v)‖ ≤ C * ‖u‖ * ‖v‖ at hscalar
    rw [norm_smul, norm_inv, ← div_eq_inv_mul] at hscalar
    have hout := (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hts))).mp hscalar
    convert hout using 1; ring

/-- The family of forms themselves is bounded on the compact time interval. -/
theorem form_values_bounded (T : ℝ) (a : ℝ → Form V) (ha : ScalarC1 T a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc 0 T, ‖a t‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := bilinear_uniform_boundedness
    (fun t : Set.Icc 0 T => a t) (by
      intro u v
      obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (ha u v).continuousOn
      exact ⟨K, fun t => hK t t.property⟩)
  exact ⟨C, hC, fun t ht => hb ⟨t, ht⟩⟩

/-- A bound on slopes bounds the canonical one-sided derivative as well.
The zero derivative chosen at non-accumulation points covers singleton intervals. -/
theorem norm_derivWithin_le_of_lipschitzOn {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hx : x ∈ s) {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ‖derivWithin f s x‖ ≤ K := by
  by_cases hu : UniqueDiffWithinAt ℝ s x
  · by_cases hd : DifferentiableWithinAt ℝ f s x
    · haveI : (𝓝[s \ {x}] x).NeBot := by
        rw [← accPt_principal_iff_nhdsWithin, ← uniqueDiffWithinAt_iff_accPt]
        exact hu
      apply le_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp hd.hasDerivWithinAt).norm
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyx : y ≠ x := by simpa using hy.2
      change ‖(y - x)⁻¹ • (f y - f x)‖ ≤ K
      rw [norm_smul, norm_inv, ← div_eq_inv_mul]
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hyx))).mpr
        (hf.norm_sub_le hy.1 hx)
    · rw [derivWithin_zero_of_not_differentiableWithinAt hd, norm_zero]
      exact K.coe_nonneg
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hu, norm_zero]
    exact K.coe_nonneg

@[simp] theorem representingOperator_sub (a b : Form V) :
    representingOperator (a - b) = representingOperator a - representingOperator b := by
  ext u
  change (InnerProductSpace.toDual ℝ V).symm (a u - b u) =
    (InnerProductSpace.toDual ℝ V).symm (a u) - (InnerProductSpace.toDual ℝ V).symm (b u)
  exact map_sub _ _ _

theorem uniform_bounds : UniformBoundsExpected (V := V) := by
  intro T a ha
  obtain ⟨C, hC, hc⟩ := form_secants_bounded T a ha
  obtain ⟨D, hD, hd⟩ := form_values_bounded T a ha
  refine ⟨D + C, add_nonneg hD hC, ?_, ?_⟩
  · intro t ht u v
    have hval : ‖a t u v‖ ≤ D * ‖u‖ * ‖v‖ :=
      (a t).le_of_opNorm₂_le_of_le (hd t ht) (le_refl _) (le_refl _)
    have hlip : LipschitzOnWith ⟨C * ‖u‖ * ‖v‖, by positivity⟩
        (fun t => a t u v) (Set.Icc 0 T) := by
      apply lipschitzOnWith_iff_norm_sub_le.mpr
      intro s hs r hr
      have hb := (a s - a r).le_of_opNorm₂_le_of_le
        (hc r hr s hs) (le_refl ‖u‖) (le_refl ‖v‖)
      change ‖a s u v - a r u v‖ ≤ _ at hb
      change ‖a s u v - a r u v‖ ≤ (C * ‖u‖ * ‖v‖) * ‖s - r‖
      convert hb using 1; ring
    have hder := norm_derivWithin_le_of_lipschitzOn ht hlip
    change ‖derivWithin (fun r => a r u v) (Set.Icc 0 T) t‖ ≤ C * ‖u‖ * ‖v‖ at hder
    simpa only [Real.norm_eq_abs, add_mul] using add_le_add hval hder
  · intro s hs t ht
    rw [← representingOperator_sub, representingOperator_norm]
    calc
      ‖a t - a s‖ ≤ C * ‖t - s‖ := hc s hs t ht
      _ ≤ (D + C) * |t - s| := by rw [Real.norm_eq_abs]; gcongr; linarith

/-- Finite words in a family of bounded operators, including the empty word. -/
def wordOperator {I : Type w} (B : I → V →L[ℝ] V) : List I → V →L[ℝ] V
  | [] => ContinuousLinearMap.id ℝ V
  | i :: l => (B i).comp (wordOperator B l)

/-- A separable set is contained in a closed separable subspace invariant
under any countable family of bounded operators. -/
theorem exists_separable_invariant_subspace {I : Type w} [Countable I]
    (B : I → V →L[ℝ] V) (s : Set V) (hs : TopologicalSpace.IsSeparable s) :
    ∃ S : Submodule ℝ V, IsClosed (S : Set V) ∧
      TopologicalSpace.IsSeparable (S : Set V) ∧ s ⊆ S ∧
      ∀ i x, x ∈ S → B i x ∈ S := by
  let o : Set V := ⋃ l : List I, wordOperator B l '' s
  let S : Submodule ℝ V := Submodule.span ℝ o
  have ho : TopologicalSpace.IsSeparable o :=
    .iUnion fun l => hs.image (wordOperator B l).continuous
  have hseed : s ⊆ S := by
    intro x hx
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨[], x, hx, rfl⟩
  have hinv : ∀ i x, x ∈ S → B i x ∈ S := by
    intro i x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, z, hzs, rfl⟩ := Set.mem_iUnion.mp hy
      apply Submodule.subset_span
      exact Set.mem_iUnion.mpr ⟨i :: l, z, hzs, rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using S.add_mem ihx ihy
    | smul r x hx ih => simpa only [map_smul] using S.smul_mem r ih
  refine ⟨S.topologicalClosure, S.isClosed_topologicalClosure, ho.span.closure,
    hseed.trans S.le_topologicalClosure, ?_⟩
  intro i x hx
  have hpre : (S.topologicalClosure : Set V) ⊆
      (B i) ⁻¹' (S.topologicalClosure : Set V) := by
    apply closure_minimal
    · exact fun y hy => S.le_topologicalClosure (hinv i y hy)
    · exact S.isClosed_topologicalClosure.preimage (B i).continuous
  exact hpre hx

section Carrier
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Mass invariance makes J carry the V-orthogonal complement into the
H-orthogonal complement of the closure of J S. -/
theorem embedding_orthogonal (j : HilbertTriple V H) (S : Submodule ℝ V)
    (hS : ∀ u ∈ S, (ContinuousLinearMap.adjoint j.embedding) (j.embedding u) ∈ S)
    (w : V) (hw : w ∈ Sᗮ) : j.embedding w ∈ (pivotSpace j S)ᗮ := by
  change j.embedding w ∈ (S.map j.embedding.toLinearMap).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨u, hu, rfl⟩
  rw [← j.embedding.adjoint_inner_left]
  exact S.inner_right_of_mem_orthogonal (hS u hu) hw

/-- Dense range of J is essential here: J* h in S implies h in closure(J S)
when S reduces the mass operator J*J. -/
theorem mem_pivotSpace_of_adjoint_mem (j : HilbertTriple V H) (S : Submodule ℝ V)
    (hclosed : IsClosed (S : Set V))
    (hS : ∀ u ∈ S, (ContinuousLinearMap.adjoint j.embedding) (j.embedding u) ∈ S)
    (h : H) (hh : (ContinuousLinearMap.adjoint j.embedding) h ∈ S) :
    h ∈ pivotSpace j S := by
  let K := pivotSpace j S
  haveI : CompleteSpace S := hclosed.completeSpace_coe
  haveI : CompleteSpace K := (S.map j.embedding.toLinearMap).isClosed_topologicalClosure.completeSpace_coe
  let p : H := K.starProjection h
  have hp : p ∈ K := (K.orthogonalProjectionOnto h).property
  have hq : h - p ∈ Kᗮ := K.sub_starProjection_mem_orthogonal h
  have heq : h = p := by
    apply Dense.eq_of_inner_left (𝕜 := ℝ) j.denseRange
    rintro _ ⟨v, rfl⟩
    obtain ⟨s, hs, w, hw, hv⟩ := S.exists_add_mem_mem_orthogonal v
    rw [hv, map_add, inner_add_right, inner_add_right]
    have hJs : j.embedding s ∈ K :=
      (S.map j.embedding.toLinearMap).le_topologicalClosure ⟨s, hs, rfl⟩
    have hsEq : inner ℝ h (j.embedding s) = inner ℝ p (j.embedding s) := by
      have hz := K.inner_left_of_mem_orthogonal hJs hq
      rw [inner_sub_left, sub_eq_zero] at hz
      exact hz
    have hw0 : inner ℝ h (j.embedding w) = 0 := by
      rw [← j.embedding.adjoint_inner_left]
      exact S.inner_right_of_mem_orthogonal hh hw
    have hpw0 : inner ℝ p (j.embedding w) = 0 :=
      K.inner_right_of_mem_orthogonal hp (embedding_orthogonal j S hS w hw)
    rw [hsEq, hw0, hpw0]
  rw [heq]
  exact hp

/-- A self-adjoint operator preserving S also preserves Sᗮ. -/
theorem selfAdjoint_preserves_orthogonal (B : V →L[ℝ] V) (hB : IsSelfAdjoint B)
    (S : Submodule ℝ V) (hS : ∀ u ∈ S, B u ∈ S) :
    ∀ w ∈ Sᗮ, B w ∈ Sᗮ := by
  intro w hw
  apply (S.mem_orthogonal _).mpr
  intro u hu
  have he := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB) u w
  change inner ℝ (B u) w = inner ℝ u (B w) at he
  rw [← he]
  exact S.inner_right_of_mem_orthogonal (hS u hu) hw

theorem exists_carrier : CarrierExistenceExpected (V := V) (H := H) := by
  intro j T a ha hsym u₀ v₀ f
  obtain ⟨M, hM, _, hBlip⟩ := uniform_bounds T a ha
  have hBc : Continuous (fun t : Set.Icc 0 T => representingOperator (a t)) := by
    have hlip : LipschitzOnWith ⟨M, hM⟩ (fun t => representingOperator (a t)) (Set.Icc 0 T) := by
      apply lipschitzOnWith_iff_norm_sub_le.mpr
      intro s hs t ht
      change ‖representingOperator (a s) - representingOperator (a t)‖ ≤ M * ‖s - t‖
      simpa only [Real.norm_eq_abs] using hBlip t ht s hs
    exact hlip.continuousOn.domRestrict
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Set.Icc 0 T)
  haveI : Countable D := hDcount.to_subtype
  let B : Option D → V →L[ℝ] V := fun i => match i with
    | none => (ContinuousLinearMap.adjoint j.embedding).comp j.embedding
    | some r => representingOperator (a r.val)
  obtain ⟨F, hFsep, hFae⟩ := (Lp.aestronglyMeasurable f).isSeparable_ae_range
  let s : Set V := {u₀} ∪ (ContinuousLinearMap.adjoint j.embedding) '' ({v₀} ∪ F)
  have hssep : TopologicalSpace.IsSeparable s :=
    (Set.finite_singleton u₀).isSeparable.union
      (((Set.finite_singleton v₀).isSeparable.union hFsep).image
        (ContinuousLinearMap.adjoint j.embedding).continuous)
  obtain ⟨S, hSc, hSs, hsS, hInv⟩ := exists_separable_invariant_subspace B s hssep
  have hmass : ∀ u ∈ S, (ContinuousLinearMap.adjoint j.embedding) (j.embedding u) ∈ S :=
    fun u hu => hInv none u hu
  have hform : ∀ t ∈ Set.Icc 0 T, ∀ u ∈ S, representingOperator (a t) u ∈ S := by
    intro t ht u hu
    apply hDdense.induction (P := fun r : Set.Icc 0 T => representingOperator (a r) u ∈ S)
      (fun r hr => hInv (some ⟨r, hr⟩) u hu)
      (hSc.preimage (hBc.clm_apply continuous_const)) ⟨t, ht⟩
  have hadjv : (ContinuousLinearMap.adjoint j.embedding) v₀ ∈ S :=
    hsS (Or.inr ⟨v₀, Or.inl rfl, rfl⟩)
  refine ⟨⟨S, hSc, hSs, hsS (Or.inl rfl),
    mem_pivotSpace_of_adjoint_mem j S hSc hmass v₀ hadjv, ?_, hmass, hform, ?_⟩⟩
  · filter_upwards [hFae] with t ht
    apply mem_pivotSpace_of_adjoint_mem j S hSc hmass
    exact hsS (Or.inr ⟨f t, Or.inr ht, rfl⟩)
  · intro t ht
    exact selfAdjoint_preserves_orthogonal _ (representingOperator_selfAdjoint _ (hsym t ht))
      S (hform t ht)

theorem carrier_geometry : CarrierGeometryExpected (V := V) (H := H) := by
  intro j T a u₀ v₀ f c
  have hKsep : TopologicalSpace.IsSeparable (pivotSpace j c.space : Set H) := by
    exact (c.separable.image j.embedding.continuous).closure
  refine ⟨hKsep, embedding_orthogonal j c.space c.massInvariant, ?_, ?_, ?_⟩
  · intro w hw
    apply (c.space.mem_orthogonal _).mpr
    intro u hu
    rw [j.embedding.adjoint_inner_right]
    exact (pivotSpace j c.space).inner_right_of_mem_orthogonal
      ((c.space.map j.embedding.toLinearMap).le_topologicalClosure ⟨u, hu, rfl⟩)
      (embedding_orthogonal j c.space c.massInvariant w hw)
  · intro t ht u hu w hw
    rw [← representingOperator_inner]
    exact c.space.inner_right_of_mem_orthogonal (c.formInvariant t ht u hu) hw
  · haveI : CompleteSpace c.space := c.closed.completeSpace_coe
    haveI : CompleteSpace (pivotSpace j c.space) :=
      (c.space.map j.embedding.toLinearMap).isClosed_topologicalClosure.completeSpace_coe
    let J₀ : c.space →L[ℝ] pivotSpace j c.space :=
      (j.embedding.comp c.space.subtypeL).codRestrict _ (fun u =>
        (c.space.map j.embedding.toLinearMap).le_topologicalClosure ⟨u, u.property, rfl⟩)
    have hi : Function.Injective J₀ := by
      intro u v huv
      apply Subtype.ext
      exact j.injective (congrArg Subtype.val huv)
    have hd : DenseRange J₀ := by
      intro y
      rw [closure_subtype]
      have hr : Subtype.val '' Set.range J₀ = (c.space.map j.embedding.toLinearMap : Set H) := by
        ext h
        constructor
        · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
          exact ⟨u, u.property, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨J₀ ⟨u, hu⟩, Set.mem_range_self _, rfl⟩
      rw [hr]
      exact y.property
    let j₀ : HilbertTriple c.space (pivotSpace j c.space) := ⟨J₀, hi, hd⟩
    refine ⟨j₀, (fun _ => rfl), ?_⟩
    intro h u
    change pivotInjection j₀ h u = pivotInjection j (h : H) (u : V)
    rw [pivotInjection_apply, pivotInjection_apply]
    rfl

/-- Every complementary test vanishes; a restricted weak solution therefore
satisfies the equation against every vector of the original space. -/
theorem carrier_equation_lift : CarrierEquationLiftExpected (V := V) (H := H) := by
  intro j T a u₀ v₀ f c u v hsol w
  haveI : CompleteSpace c.space := c.closed.completeSpace_coe
  obtain ⟨s, hs, z, hz, hw⟩ := c.space.exists_add_mem_mem_orthogonal w
  have hJz := embedding_orthogonal j c.space c.massInvariant z hz
  have hform : ∀ t ∈ Set.Icc 0 T, a t (u t) z = 0 := by
    intro t ht
    rw [← representingOperator_inner]
    exact c.space.inner_right_of_mem_orthogonal (c.formInvariant t ht _ (u t).property) hz
  have hlhs : (fun t => inner ℝ (v t : H) (j.embedding s)) =ᵐ[timeMeasure T]
      (fun t => inner ℝ (v t : H) (j.embedding w)) := by
    apply Filter.Eventually.of_forall
    intro t
    change inner ℝ (v t : H) (j.embedding s) = inner ℝ (v t : H) (j.embedding w)
    rw [hw, map_add, inner_add_right,
      (pivotSpace j c.space).inner_right_of_mem_orthogonal (v t).property hJz, add_zero]
  have hrhs : (fun t => inner ℝ (f t) (j.embedding s) - a t (u t) s) =ᵐ[timeMeasure T]
      (fun t => inner ℝ (f t) (j.embedding w) - a t (u t) w) := by
    have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Set.Icc 0 T := by
      exact (ae_restrict_mem measurableSet_Ioo).mono (fun _ h => ⟨h.1.le, h.2.le⟩)
    filter_upwards [c.forcing, ht] with t hft htt
    rw [hw, map_add, inner_add_right, map_add,
      (pivotSpace j c.space).inner_right_of_mem_orthogonal hft hJz, hform t htt,
      add_zero, add_zero]
  exact (hasTimeDerivative_congr T _ _ _ _ hlhs hrhs).mp (hsol ⟨s, hs⟩)

/-- Bounded linear maps commute with the distributional time derivative. -/
theorem hasTimeDerivative_comp {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (T : ℝ) (b g : ℝ → E) (hb : HasTimeDerivative T b g) :
    HasTimeDerivative T (fun t => L (b t)) (fun t => L (g t)) := by
  refine ⟨L.locallyIntegrableOn_comp hb.1, L.locallyIntegrableOn_comp hb.2.1, ?_⟩
  intro φ hφ
  have hi := hasTimeDerivative_test_integrable T b g hb φ hφ
  have he := congrArg L (hb.2.2 φ hφ)
  change L (∫ t, deriv φ t • b t ∂timeMeasure T) =
    L (-(∫ t, φ t • g t ∂timeMeasure T)) at he
  rw [map_neg, ← L.integral_comp_comm hi.1, ← L.integral_comp_comm hi.2] at he
  simpa only [map_smul, timeMeasure] using he

/-- The elementary Bochner L² mapping property for a bounded real linear map. -/
theorem memLp_comp_real {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (g : ℝ → E) (μ : Measure ℝ) (hg : MemLp g 2 μ) :
    MemLp (fun t => L (g t)) 2 μ :=
  hg.continuousLinearMap_comp L

/-- Extend a continuous functional by composing with the orthogonal projection. -/
def extendDual (S : Submodule ℝ V) [S.HasOrthogonalProjection] :
    StrongDual ℝ S →L[ℝ] StrongDual ℝ V :=
  (ContinuousLinearMap.compL ℝ V S ℝ).flip S.orthogonalProjectionOnto

/-- Restriction followed by extension recovers exactly the functionals that
annihilate the orthogonal complement. -/
theorem extendDual_restrict (S : Submodule ℝ V) [S.HasOrthogonalProjection]
    (ℓ : StrongDual ℝ V) (hℓ : ∀ z ∈ Sᗮ, ℓ z = 0) :
    extendDual S (ℓ.comp S.subtypeL) = ℓ := by
  ext w
  change ℓ (S.orthogonalProjectionOnto w : V) = ℓ w
  have hz := hℓ (w - S.starProjection w) (S.sub_starProjection_mem_orthogonal w)
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

set_option maxHeartbeats 800000 in
/-- The vector equation, including its common a.e. exceptional set, lifts
through the canonical extension V₀′ → V′. -/
theorem carrier_vector_lift : CarrierVectorLiftExpected (V := V) (H := H) := by
  intro j T a u₀ v₀ f c u v g hder heq
  haveI : CompleteSpace c.space := c.closed.completeSpace_coe
  generalize hL : extendDual c.space = L
  have hpivot : ∀ h ∈ pivotSpace j c.space,
      L ((pivotInjection j h).comp c.space.subtypeL) = pivotInjection j h := by
    intro h hh
    rw [← hL]
    apply extendDual_restrict
    intro z hz
    rw [pivotInjection_apply]
    exact (pivotSpace j c.space).inner_right_of_mem_orthogonal hh
      (embedding_orthogonal j c.space c.massInvariant z hz)
  have hext : HasTimeDerivative T
      (fun t => L ((pivotInjection j (v t)).comp c.space.subtypeL)) (fun t => L (g t)) :=
    hasTimeDerivative_comp L T _ g hder
  have hb : (fun t => L ((pivotInjection j (v t)).comp c.space.subtypeL)) =ᵐ[timeMeasure T]
      (fun t => pivotInjection j (v t)) :=
    Filter.Eventually.of_forall (fun t => hpivot _ (v t).property)
  have hg : (fun t => L (g t)) =ᵐ[timeMeasure T]
      (fun t => pivotInjection j (f t) - a t (u t)) := by
    have ht : ∀ᵐ t ∂timeMeasure T, t ∈ Set.Icc 0 T :=
      (ae_restrict_mem measurableSet_Ioo).mono (fun _ h => ⟨h.1.le, h.2.le⟩)
    filter_upwards [heq, c.forcing, ht] with t hgt hft htt
    rw [hgt]
    rw [← hL]
    apply extendDual_restrict
    intro z hz
    change (pivotInjection j (f t)) z - a t (u t) z = 0
    rw [pivotInjection_apply,
      (pivotSpace j c.space).inner_right_of_mem_orthogonal hft
        (embedding_orthogonal j c.space c.massInvariant z hz)]
    have hzero : a t (u t) z = 0 := by
      rw [← representingOperator_inner]
      exact c.space.inner_right_of_mem_orthogonal (c.formInvariant t htt _ (u t).property) hz
    rw [hzero, sub_self]
  refine ⟨(hasTimeDerivative_congr T _ _ _ _ hb hg).mp hext, ?_⟩
  intro hgLp
  change MemLp g 2 (timeMeasure T) at hgLp
  change MemLp (fun t => pivotInjection j (f t) - a t (u t)) 2 (timeMeasure T)
  have hLp : MemLp (fun t => L (g t)) 2 (timeMeasure T) :=
    memLp_comp_real (E := StrongDual ℝ c.space) (F := StrongDual ℝ V) L g (timeMeasure T) hgLp
  exact hLp.ae_eq hg

end Carrier
end ExpandedFA.Evolution.HyperbolicFormBoundsAndCarrier
