import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.GreenFormulas
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SmoothBoundaryDivergence
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Green's two identities on bounded C² domains, for real and complex scalars.
The accepted smooth divergence theorem supplies the geometric input for the
H¹ density argument. H² elements have genuine H¹ weak derivatives, so summing
the first identity gives the second identity without an H² density assumption.
All boundary integrals use the shared normalized Euclidean surface measure. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal ComplexConjugate Topology Function

namespace ExpandedFA.PartIV.GreenFormulas
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- The geometric C² hypothesis implies the existing C¹ hypothesis. -/
theorem IsC2Domain.isC1 (hΩ : IsC2Domain Ω) : C1Extension.IsC1Domain Ω := by
  intro x hx
  obtain ⟨i, Φ, hsource, hzero, hΦ, hInv, hside⟩ := hΩ x hx
  exact ⟨i, Φ, hsource, hzero, hΦ.of_le (by norm_num),
    hInv.of_le (by norm_num), hside⟩

/-- The actual L² trace is available from the accepted first trace theorem. -/
theorem l2_trace_exists
    (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (hb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω) :
    ∃! T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2, IsTrace T :=
  Trace.trace_exists 𝕜 d Ω hb hΩ.isC1 2 (by norm_num)

@[simp] theorem natIndex_indexOfNat {m : ℕ} (a : Fin d → ℕ) (ha : (∑ j, a j) ≤ m) :
    natIndex (indexOfNat a ha) = a := rfl

/-- The Spec index is the existing canonical bounded index. -/
theorem indexOfNat_eq_boundedIndex {m : ℕ} (a : Fin d → ℕ)
    (ha : (∑ j, a j) ≤ m) : indexOfNat a ha = boundedIndex a ha := rfl

theorem firstIndex_eq_coordinateIndex (j : Fin d) :
    firstIndex (m := 1) (by rfl) j = HalfSpace.coordinateIndex j := by
  rfl

/-- Derivatives of an H² element are H¹ elements, using the distributional
word permutation theorem, not any smooth H² approximation. -/
def derivativeH1 (u : H2 𝕜 Ω) (j : Fin d) : H1 𝕜 Ω := by
  let V : DerivativeTuple 𝕜 Ω 1 2 :=
    WithLp.toLp 1 (fun α => Smoothing.wordLp u (j :: multiIndexWord (natIndex α)))
  refine ⟨V, ?_⟩
  intro α
  have hlen : (j :: multiIndexWord (natIndex α)).length ≤ 2 := by
    simp only [List.length_cons, multiIndexWord_length]
    have ha := α.property
    change (∑ i, natIndex α i) ≤ 1 at ha
    omega
  have hz : multiIndexWord (natIndex (zeroIndex d 1)) = [] := by
    apply List.length_eq_zero_iff.mp
    simp [zeroIndex, natIndex]
  change lpDistribution (Smoothing.wordLp u (j :: multiIndexWord (natIndex α))) =
    distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex α))
      (lpDistribution (Smoothing.wordLp u (j :: multiIndexWord (natIndex (zeroIndex d 1)))))
  rw [Smoothing.wordLp_distribution u _ hlen, hz,
    Smoothing.wordLp_distribution u [j] (by simp)]
  exact Smoothing.distributionDerivative_append [j] (multiIndexWord (natIndex α)) _

@[simp] theorem derivativeH1_value (u : H2 𝕜 Ω) (j : Fin d) :
    value (derivativeH1 u j) = u.val (firstIndex (by decide) j) := by
  change Smoothing.wordLp u (j :: multiIndexWord (natIndex (zeroIndex d 1))) = _
  have hz : multiIndexWord (natIndex (zeroIndex d 1)) = [] := by
    apply List.length_eq_zero_iff.mp
    simp [zeroIndex, natIndex]
  rw [hz]
  simp only [Smoothing.wordLp, List.length_singleton, Nat.one_le_ofNat, ↓reduceDIte]
  apply congrArg (fun α : DerivativeIndex d 2 => u.val α)
  apply Subtype.ext
  funext k
  apply Fin.ext
  change [j].count k = (Pi.single j 1 : Fin d → ℕ) k
  by_cases h : k = j
  · subst k; simp
  · simp [Pi.single_apply, h, Ne.symm h]

@[simp] theorem derivativeH1_partial (u : H2 𝕜 Ω) (j k : Fin d) :
    weakPartial (derivativeH1 u j) k = u.val (secondIndex j k) := by
  change Smoothing.wordLp u (j :: multiIndexWord (natIndex (firstIndex (m := 1) (by rfl) k))) = _
  have hk : multiIndexWord (natIndex (firstIndex (m := 1) (by rfl) k)) = [k] := by
    simp [firstIndex, natIndex_indexOfNat, Lines.multiIndexWord_single]
  rw [hk]
  simp only [Smoothing.wordLp, List.length_cons, List.length_nil, Nat.reduceAdd,
    le_refl, ↓reduceDIte]
  apply congrArg (fun α : DerivativeIndex d 2 => u.val α)
  apply Subtype.ext
  funext i
  apply Fin.ext
  change [j, k].count i = (Pi.single j 1 : Fin d → ℕ) i +
    (Pi.single k 1 : Fin d → ℕ) i
  by_cases hj : i = j
  · subst i
    by_cases hk : j = k
    · subst k; simp
    · simp [Pi.single_apply, hk, Ne.symm hk]
  · by_cases hk : i = k
    · subst i; simp [Pi.single_apply, hj, Ne.symm hj]
    · simp [Pi.single_apply, hj, Ne.symm hj, hk, Ne.symm hk]

theorem derivativeH1_isDerivativeFamily (u : H2 𝕜 Ω) :
    IsDerivativeFamily u (derivativeH1 u) :=
  ⟨derivativeH1_value u, derivativeH1_partial u⟩

section Pairing
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The manuscript convention is linear in the unknown and conjugate-linear
in the test: it is the L² inner product with the arguments reversed. -/
theorem integral_mul_conj_eq_inner (f g : Lp 𝕜 2 μ) :
    (∫ x, f x * conj (g x) ∂μ) = inner 𝕜 g f := by
  simp only [L2.inner_def, RCLike.inner_apply]

theorem integrable_mul_conj (f g : Lp 𝕜 2 μ) :
    Integrable (fun x => f x * conj (g x)) μ := by
  simpa only [RCLike.inner_apply] using (L2.integrable_inner (𝕜 := 𝕜) g f)

/-- Joint continuity of the actual scalar integral for arbitrary measures. -/
theorem continuous_l2_pairing :
    Continuous (fun z : Lp 𝕜 2 μ × Lp 𝕜 2 μ => ∫ x, z.1 x * conj (z.2 x) ∂μ) := by
  simp only [integral_mul_conj_eq_inner]
  exact continuous_snd.inner continuous_fst

/-- A bounded measurable real coefficient acts continuously on L². -/
def realMultiplier (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ 1) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ := by
  let hmem : MemLp (fun x => (a x : 𝕜)) ∞ μ :=
    memLp_top_of_bound
      ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.comp_aestronglyMeasurable ha) 1
      (by simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using hbound)
  exact ((ContinuousLinearMap.mul 𝕜 𝕜).holderL μ ∞ 2 2) (hmem.toLp _)

lemma realMultiplier_coe (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ 1) (u : Lp 𝕜 2 μ) :
    realMultiplier a ha hbound u =ᵐ[μ] fun x => (a x : 𝕜) * u x := by
  let hmem : MemLp (fun x => (a x : 𝕜)) ∞ μ :=
    memLp_top_of_bound
      ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.comp_aestronglyMeasurable ha) 1
      (by simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using hbound)
  change (ContinuousLinearMap.mul 𝕜 𝕜).holder 2 (hmem.toLp _) u =ᵐ[μ] _
  filter_upwards [(ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder (r := 2) (hmem.toLp _) u,
    hmem.coeFn_toLp] with x hx hax
  simpa only [ContinuousLinearMap.mul_apply', hax] using hx


/-- Weighted boundary products are ordinary integrable scalar functions. -/
theorem integrable_boundary_product
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ 1) (f g : Lp 𝕜 2 μ) :
    Integrable (fun x => f x * conj (g x) * (a x : 𝕜)) μ := by
  apply (integrable_mul_conj (realMultiplier a ha hbound f) g).congr
  filter_upwards [realMultiplier_coe a ha hbound f] with x hx
  rw [hx]
  ring

lemma boundary_product_eq_inner
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ 1) (f g : Lp 𝕜 2 μ) :
    (∫ x, f x * conj (g x) * (a x : 𝕜) ∂μ) =
      inner 𝕜 g (realMultiplier a ha hbound f) := by
  rw [← integral_mul_conj_eq_inner]
  apply integral_congr_ae
  filter_upwards [realMultiplier_coe a ha hbound f] with x hx
  rw [hx]
  ring

/-- Joint continuity includes the surface product and the normal coefficient. -/
theorem continuous_boundary_product
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ 1) :
    Continuous (fun z : Lp 𝕜 2 μ × Lp 𝕜 2 μ =>
      ∫ x, z.1 x * conj (z.2 x) * (a x : 𝕜) ∂μ) := by
  simp only [boundary_product_eq_inner a ha hbound]
  exact continuous_snd.inner ((realMultiplier a ha hbound).continuous.comp continuous_fst)

end Pairing

lemma continuous_jet_component (α : DerivativeIndex d 1) :
    Continuous (fun u : H1 𝕜 Ω => u.val α) :=
  (PiLp.continuous_apply 1 _ α).comp continuous_subtype_val

lemma first_identity_lhs_split (u v : H1 𝕜 Ω) (j : Fin d) :
    (∫ x in (Ω : Set (Domain d)),
      value u x * conj (weakPartial v j x) + weakPartial u j x * conj (value v x)) =
    (∫ x in (Ω : Set (Domain d)), value u x * conj (weakPartial v j x)) +
    ∫ x in (Ω : Set (Domain d)), weakPartial u j x * conj (value v x) :=
  integral_add (integrable_mul_conj _ _) (integrable_mul_conj _ _)

/-- Both interior terms vary jointly continuously in the H¹ pair. -/
theorem continuous_first_identity_lhs (j : Fin d) :
    Continuous (fun z : H1 𝕜 Ω × H1 𝕜 Ω =>
      ∫ x in (Ω : Set (Domain d)),
        value z.1 x * conj (weakPartial z.2 j x) +
          weakPartial z.1 j x * conj (value z.2 x)) := by
  simp only [first_identity_lhs_split]
  apply Continuous.add
  · exact continuous_l2_pairing.comp
      (((continuous_jet_component (zeroIndex d 1)).comp continuous_fst).prodMk
        ((continuous_jet_component (firstIndex (by rfl) j)).comp continuous_snd))
  · exact continuous_l2_pairing.comp
      (((continuous_jet_component (firstIndex (by rfl) j)).comp continuous_fst).prodMk
        ((continuous_jet_component (zeroIndex d 1)).comp continuous_snd))

/-- The analytic density step: equality for ambient smooth representatives
extends to every H¹ pair by continuity of the interior and boundary pairings. -/
theorem firstIdentity_of_smooth
    (hb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω)
    (ν : Fin d → Domain d → ℝ) (hν : IsOutwardUnitNormal Ω ν)
    (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2)
    (hsmooth : ∀ u ∈ C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω 2,
      ∀ v ∈ C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω 2,
        ∀ j, FirstIdentity T ν u v j) :
    ∀ (u v : H1 𝕜 Ω) (j : Fin d), FirstIdentity T ν u v j := by
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hd := C1Extension.smooth_density 𝕜 d Ω hΩ.isC1 hc 2 (by norm_num)
  intro u v j
  have hright : Continuous (fun z : H1 𝕜 Ω × H1 𝕜 Ω =>
      ∫ x, (T z.1) x * conj ((T z.2) x) * (ν j x : 𝕜) ∂surfaceMeasure Ω) :=
    (continuous_boundary_product (ν j) (hν.1 j) (hν.2.1 j)).comp
      ((T.continuous.comp continuous_fst).prodMk (T.continuous.comp continuous_snd))
  have heq : EqOn
      (fun z : H1 𝕜 Ω × H1 𝕜 Ω =>
        ∫ x in (Ω : Set (Domain d)),
          value z.1 x * conj (weakPartial z.2 j x) +
            weakPartial z.1 j x * conj (value z.2 x))
      (fun z => ∫ x, (T z.1) x * conj ((T z.2) x) * (ν j x : 𝕜) ∂surfaceMeasure Ω)
      (C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω 2 ×ˢ
        C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω 2) := by
    intro z hz
    exact hsmooth z.1 hz.1 z.2 hz.2 j
  exact heq.closure (continuous_first_identity_lhs j) hright ((hd.prod hd) (u, v))


/-- The normal trace in the second formula really belongs to the original
surface L² space, rather than merely being a formal boundary expression. -/
theorem normalDerivative_memLp
    (ν : Fin d → Domain d → ℝ) (hν : IsOutwardUnitNormal Ω ν)
    (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2) (g : Fin d → H1 𝕜 Ω) :
    MemLp (normalDerivative T ν g) 2 (surfaceMeasure Ω) := by
  unfold normalDerivative
  apply memLp_finsetSum
  intro j _
  apply (Lp.memLp (realMultiplier (ν j) (hν.1 j) (hν.2.1 j) (T (g j)))).ae_eq
  filter_upwards [realMultiplier_coe (ν j) (hν.1 j) (hν.2.1 j) (T (g j))] with x hx
  rw [hx]
  exact mul_comm _ _

/-- The derivative family, and hence its normal trace, has no arbitrary
Sobolev representative choices. -/
theorem derivativeFamily_unique (u : H2 𝕜 Ω) (g h : Fin d → H1 𝕜 Ω)
    (hg : IsDerivativeFamily u g) (hh : IsDerivativeFamily u h) : g = h := by
  funext j
  exact sobolev_underlying_injective 𝕜 d Ω 1 2 ((hg.1 j).trans (hh.1 j).symm)

/-- Summing the established first identity gives the second one. The H²
hypothesis is used only through its genuine H¹ weak derivatives. -/
theorem secondIdentity_of_firstIdentity
    (ν : Fin d → Domain d → ℝ) (hν : IsOutwardUnitNormal Ω ν)
    (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2)
    (hfirst : ∀ (w v : H1 𝕜 Ω) (j : Fin d), FirstIdentity T ν w v j)
    (u : H2 𝕜 Ω) (v : H1 𝕜 Ω) :
    ∃ g, IsDerivativeFamily u g ∧ SecondIdentity T ν u v g := by
  let g := derivativeH1 u
  have hg : IsDerivativeFamily u g := derivativeH1_isDerivativeFamily u
  refine ⟨g, hg, ?_⟩
  have hsum :
      (∑ j, ∫ x in (Ω : Set (Domain d)),
        u.val (firstIndex (by decide) j) x * conj (weakPartial v j x)) +
      (∑ j, ∫ x in (Ω : Set (Domain d)),
        u.val (secondIndex j j) x * conj (value v x)) =
      ∑ j, ∫ x, (T (g j)) x * conj ((T v) x) * (ν j x : 𝕜) ∂surfaceMeasure Ω := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hj := hfirst (g j) v j
    unfold FirstIdentity at hj
    rw [first_identity_lhs_split, hg.1 j, hg.2 j j] at hj
    exact hj
  have hL :
      (∫ x in (Ω : Set (Domain d)), laplacian u x * conj (value v x)) =
      ∑ j, ∫ x in (Ω : Set (Domain d)),
        u.val (secondIndex j j) x * conj (value v x) := by
    simp only [laplacian, Finset.sum_mul]
    exact integral_finsetSum _ (fun j _ => integrable_mul_conj _ _)
  have hA :
      (∫ x in (Ω : Set (Domain d)),
        ∑ j, u.val (firstIndex (by decide) j) x * conj (weakPartial v j x)) =
      ∑ j, ∫ x in (Ω : Set (Domain d)),
        u.val (firstIndex (by decide) j) x * conj (weakPartial v j x) :=
    integral_finsetSum _ (fun j _ => integrable_mul_conj _ _)
  have hC :
      (∫ x, normalDerivative T ν g x * conj ((T v) x) ∂surfaceMeasure Ω) =
      ∑ j, ∫ x, (T (g j)) x * conj ((T v) x) * (ν j x : 𝕜) ∂surfaceMeasure Ω := by
    calc
      _ = ∫ x, ∑ j, (T (g j)) x * conj ((T v) x) * (ν j x : 𝕜) ∂surfaceMeasure Ω := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          simp only [normalDerivative, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring)
      _ = _ := integral_finsetSum _ (fun j _ =>
        integrable_boundary_product (ν j) (hν.1 j) (hν.2.1 j) _ _)
  unfold SecondIdentity
  rw [hL, hA, hC, ← hsum]
  ring

/-- The second identity follows from the first through the genuine H¹ weak
derivatives of each H² element. -/
theorem secondGreen_of_firstOrderGreen
    (hfirst : Specs.ExpandedFA.PartIV.GreenFormulas.FirstOrderGreen) :
    Specs.ExpandedFA.PartIV.GreenFormulas.SecondGreen := by
  intro 𝕜 _ d Ω hb hΩ ν hν T hT u v
  exact secondIdentity_of_firstIdentity ν hν T
    ((hfirst 𝕜 d Ω hb hΩ).2.2 ν hν T hT) u v

section NormalConstruction

/-- A smooth boundary chart gives a genuine defining function with
nonzero gradient throughout its source. -/
theorem chart_defining_function
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source)
    (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) :
    ∃ r : Domain d → ℝ,
      ContDiffOn ℝ 2 r Φ.source ∧
      (∀ y ∈ Φ.source, y ∈ Ω ↔ r y < 0) ∧
      (∀ y ∈ Φ.source ∩ frontier (Ω : Set (Domain d)), r y = 0) ∧
      ∀ x ∈ Φ.source, 0 < ∑ k, (definingPartial r k x) ^ 2 := by
  let r : Domain d → ℝ := fun y => -(Φ y i)
  have hr : ContDiffOn ℝ 2 r Φ.source :=
    ((contDiff_apply ℝ (fun _ : Fin d => ℝ) i).comp_contDiffOn hΦ).neg
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · intro y hy
    simpa only [r, neg_lt_zero] using hside y hy
  · intro y hy
    simp only [r, Trace.chart_boundary_iff Ω Φ i hside y hy.1 |>.mp hy.2, neg_zero]
  · intro x hx
    have hdΦ := (hΦ.contDiffAt (Φ.open_source.mem_nhds hx)).differentiableAt (by norm_num)
    have hdInv := (hInv.contDiffAt (Φ.open_target.mem_nhds
      (Φ.map_source hx))).differentiableAt (by norm_num)
    have hcomp : (fderiv ℝ Φ x).comp (fderiv ℝ Φ.symm (Φ x)) =
        ContinuousLinearMap.id ℝ (Domain d) := by
      have hdΦ' : HasFDerivAt Φ (fderiv ℝ Φ x) (Φ.symm (Φ x)) := by
        simpa only [Φ.left_inv hx] using hdΦ.hasFDerivAt
      have hc := hdΦ'.comp (Φ x) hdInv.hasFDerivAt
      exact (hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm (Φ.eventually_right_inverse' hx))).unique
        (hasFDerivAt_id (Φ x))
    have hdr : fderiv ℝ r x =
        -(ContinuousLinearMap.proj i).comp (fderiv ℝ Φ x) := by
      exact (((ContinuousLinearMap.proj i).hasFDerivAt.comp x hdΦ.hasFDerivAt).neg).fderiv
    have hn : ∃ k, definingPartial r k x ≠ 0 := by
      by_contra hn
      push Not at hn
      simp only [definingPartial, coordinateVector] at hn
      have hz : fderiv ℝ r x = 0 := by
        ext v
        rw [pi_eq_sum_univ' v, map_sum]
        simp only [map_smul, hn, smul_zero, Finset.sum_const_zero, zero_apply]
      have h := congrArg (fun A : Domain d →L[ℝ] Domain d => A (coordinateVector i) i) hcomp
      have hz' := congrArg (fun A : Domain d →L[ℝ] ℝ =>
        A (fderiv ℝ Φ.symm (Φ x) (coordinateVector i))) hz
      rw [hdr] at hz'
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.proj_apply, zero_apply, coordinateVector] at hz'
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        coordinateVector, Pi.single_eq_same] at h
      linarith
    obtain ⟨k, hk⟩ := hn
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hk)
      (Finset.single_le_sum (fun j _ => sq_nonneg (definingPartial r j x))
        (Finset.mem_univ k))

/-- The gradient is normalized using its Euclidean coordinate norm,
independently of the ambient coordinate sup norm. -/
def normalizedGradient (r : Domain d → ℝ) (j : Fin d) (x : Domain d) : ℝ :=
  definingPartial r j x / Real.sqrt (∑ k, (definingPartial r k x) ^ 2)

lemma normalizedGradient_bound (r : Domain d → ℝ) (x : Domain d)
    (hp : 0 < ∑ k, (definingPartial r k x) ^ 2) (j : Fin d) :
    |normalizedGradient r j x| ≤ 1 := by
  rw [normalizedGradient, abs_div, abs_of_pos (Real.sqrt_pos.2 hp)]
  apply (div_le_one (Real.sqrt_pos.2 hp)).2
  exact Real.abs_le_sqrt (Finset.single_le_sum
    (fun k _ => sq_nonneg (definingPartial r k x)) (Finset.mem_univ j))

lemma continuousOn_normalizedGradient (U : Opens (Domain d))
    (r : Domain d → ℝ) (hr : ContDiffOn ℝ 2 r U)
    (hp : ∀ x ∈ U, 0 < ∑ k, (definingPartial r k x) ^ 2) (j : Fin d) :
    ContinuousOn (normalizedGradient r j) U := by
  have hg (k : Fin d) : ContinuousOn (definingPartial r k) U :=
    (hr.continuousOn_fderiv_of_isOpen U.isOpen (by norm_num)).clm_apply continuousOn_const
  have hs : ContinuousOn (fun x => ∑ k, (definingPartial r k x) ^ 2) U :=
    continuousOn_finsetSum _ (fun k _ => (hg k).pow 2)
  exact (hg j).div hs.sqrt (fun x hx => (Real.sqrt_pos.2 (hp x hx)).ne')

/-- The pointwise geometric part of `IsOutwardUnitNormal`, used while
patching a finite family of local defining functions. -/
def HasOutwardNormalAt (Ω : Opens (Domain d))
    (ν : Fin d → Domain d → ℝ) (x : Domain d) : Prop :=
  ∃ (U : Opens (Domain d)) (r : Domain d → ℝ),
    x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
    (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
    0 < ∑ k, (definingPartial r k x) ^ 2 ∧
    ∀ j, ν j x = normalizedGradient r j x

lemma HasOutwardNormalAt.congr {ν η : Fin d → Domain d → ℝ} {x : Domain d}
    (h : HasOutwardNormalAt Ω ν x) (heq : ∀ j, η j x = ν j x) :
    HasOutwardNormalAt Ω η x := by
  obtain ⟨U, r, hx, hr, hz, hside, hp, hν⟩ := h
  exact ⟨U, r, hx, hr, hz, hside, hp, fun j => (heq j).trans (hν j)⟩

/-- A chart's normalized gradient is extended by zero off its source.
It is measurable even though the defining function need not be regular
outside that source. -/
theorem chart_normal_field
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source)
    (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) :
    ∃ ν : Fin d → Domain d → ℝ,
      (∀ j, Measurable (ν j)) ∧ (∀ j x, |ν j x| ≤ 1) ∧
      ∀ x ∈ Φ.source ∩ frontier (Ω : Set (Domain d)), HasOutwardNormalAt Ω ν x := by
  classical
  obtain ⟨r, hr, hside', hz, hp⟩ := chart_defining_function Φ i hΦ hInv hside
  let ν : Fin d → Domain d → ℝ := fun j =>
    Φ.source.piecewise (normalizedGradient r j) (fun _ => 0)
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro j
    exact (continuousOn_normalizedGradient ⟨Φ.source, Φ.open_source⟩ r hr hp j).measurable_piecewise
      continuousOn_const Φ.open_source.measurableSet
  · intro j x
    by_cases hx : x ∈ Φ.source
    · simpa only [ν, piecewise_eq_of_mem _ _ _ hx] using normalizedGradient_bound r x (hp x hx) j
    · simp [ν, hx]
  · intro x hx
    refine ⟨⟨Φ.source, Φ.open_source⟩, r, hx.1, hr, hz x hx, hside', hp x hx.1, ?_⟩
    intro j
    exact piecewise_eq_of_mem _ _ _ hx.1

/-- Finite measurable gluing does not require an arbitrary nonmeasurable
choice of a chart at each point. The geometric witness at a point comes
from the first chart selected by the finite recursion. -/
lemma normal_field_on_finite_cover {ι : Type*} (U : ι → Opens (Domain d))
    (ν : ι → Fin d → Domain d → ℝ)
    (hm : ∀ i j, Measurable (ν i j))
    (hb : ∀ i j x, |ν i j x| ≤ 1)
    (hn : ∀ i x, x ∈ U i → x ∈ frontier (Ω : Set (Domain d)) →
      HasOutwardNormalAt Ω (ν i) x) (s : Finset ι) :
    ∃ η : Fin d → Domain d → ℝ,
      (∀ j, Measurable (η j)) ∧ (∀ j x, |η j x| ≤ 1) ∧
      ∀ x ∈ frontier (Ω : Set (Domain d)),
        x ∈ ⋃ i ∈ s, (U i : Set (Domain d)) → HasOutwardNormalAt Ω η x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ _ => 0, fun _ => measurable_const, fun _ _ => by simp, ?_⟩
    intro x hx hcover
    simp at hcover
  | @insert i s hi ih =>
    obtain ⟨η, hηm, hηb, hηn⟩ := ih
    let ζ : Fin d → Domain d → ℝ := fun j =>
      (U i : Set (Domain d)).piecewise (ν i j) (η j)
    refine ⟨ζ, fun j => (hm i j).piecewise (U i).isOpen.measurableSet (hηm j), ?_, ?_⟩
    · intro j x
      by_cases hx : x ∈ U i
      · simpa [ζ, hx] using hb i j x
      · simpa [ζ, hx] using hηb j x
    · intro x hx hcover
      by_cases hxi : x ∈ U i
      · exact (hn i x hxi hx).congr (fun j => by simp [ζ, hxi])
      · apply (hηn x hx ?_).congr (fun j => by simp [ζ, hxi])
        rw [Finset.set_biUnion_insert] at hcover
        exact hcover.resolve_left hxi

/-- Every bounded C² domain admits an actual, surface-measurable outward
unit normal. Empty boundaries and dimension zero require no exception. -/
theorem outward_normal_exists
    (hb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω) :
    ∃ ν, IsOutwardUnitNormal Ω ν := by
  classical
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hlocal (x : frontier (Ω : Set (Domain d))) :
      ∃ (U : Opens (Domain d)) (ν : Fin d → Domain d → ℝ),
        x.val ∈ U ∧ (∀ j, Measurable (ν j)) ∧ (∀ j y, |ν j y| ≤ 1) ∧
        ∀ y ∈ U, y ∈ frontier (Ω : Set (Domain d)) → HasOutwardNormalAt Ω ν y := by
    obtain ⟨i, Φ, hx, hz, hΦ, hInv, hside⟩ := hΩ x.val x.property
    obtain ⟨ν, hm, hb, hn⟩ := chart_normal_field Φ i hΦ hInv hside
    exact ⟨⟨Φ.source, Φ.open_source⟩, ν, hx, hm, hb, fun y hy hf => hn y ⟨hy, hf⟩⟩
  choose U ν hx hm hb' hn using hlocal
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun x => (U x : Set (Domain d)))
    (fun x => (U x).isOpen) (fun x hx' => mem_iUnion.2 ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩)
  obtain ⟨η, hηm, hηb, hηn⟩ := normal_field_on_finite_cover U ν hm hb' hn s
  refine ⟨η, fun j => (hηm j).aestronglyMeasurable, ?_, ?_⟩
  · intro j
    exact Eventually.of_forall (hηb j)
  · intro x hx'
    exact hηn x hx' (hs hx')

end NormalConstruction

/-- The geometric predicate implies the full Euclidean unit-length
identity at every boundary point, in addition to its coordinate bounds. -/
theorem IsOutwardUnitNormal.sum_sq_eq_one
    {ν : Fin d → Domain d → ℝ} (hν : IsOutwardUnitNormal Ω ν)
    (x : Domain d) (hx : x ∈ frontier (Ω : Set (Domain d))) :
    ∑ j, (ν j x) ^ 2 = 1 := by
  obtain ⟨U, r, hxU, hr, hz, hside, hp, heq⟩ := hν.2.2 x hx
  simp_rw [heq, div_pow]
  rw [← Finset.sum_div, Real.sq_sqrt hp.le, div_self hp.ne']

section NormalUniqueness

lemma derivative_product_nonneg {r s : Domain d → ℝ} {x : Domain d}
    (hr : DifferentiableAt ℝ r x) (hs : DifferentiableAt ℝ s x)
    (hr0 : r x = 0) (hs0 : s x = 0)
    (hp : ∀ᶠ y in 𝓝 x, 0 ≤ r y * s y) (v : Domain d) :
    0 ≤ fderiv ℝ r x v * fderiv ℝ s x v := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    convert (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id 0).smul_const v) using 1 <;> first | rfl | simp
  have hdr := hr.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hds := hs.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hlimr := hdr.tendsto_slope_zero
  have hlims := hds.tendsto_slope_zero
  simp only [Function.comp_def, zero_add, zero_smul, add_zero, hr0, hs0, sub_zero, smul_eq_mul] at hlimr hlims
  apply ge_of_tendsto (hlimr.mul hlims)
  have hcont : Tendsto (fun t : ℝ => x + t • v) (𝓝[≠] 0) (𝓝 x) := by
    have h : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hcont.eventually hp] with t ht
  simpa only [← mul_mul_mul_comm, ← sq] using mul_nonneg (sq_nonneg t⁻¹) ht

lemma positive_proportional_of_mul_nonneg
    (A B : Domain d →L[ℝ] ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ v, 0 ≤ A v * B v) :
    ∃ c : ℝ, 0 < c ∧ B = c • A := by
  obtain ⟨u, hu⟩ : ∃ u, A u ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hA (ContinuousLinearMap.ext hn)
  let w : Domain d := (A u)⁻¹ • u
  have hw : A w = 1 := by simp [w, hu]
  have hker (v : Domain d) (hv : A v = 0) : B v = 0 := by
    by_contra hb
    have hh := h (w - ((B w + 1) / B v) • v)
    simp only [map_sub, map_smul, smul_eq_mul, hw, hv, mul_zero, sub_zero, one_mul] at hh
    have heq : (B w + 1) / B v * B v = B w + 1 := div_mul_cancel₀ _ hb
    rw [heq] at hh
    linarith
  have hc : 0 ≤ B w := by simpa only [hw, one_mul] using h w
  have heq : B = B w • A := by
    ext v
    have hk := hker (v - (A v) • w) (by simp [hw])
    simp only [map_sub, map_smul, smul_eq_mul] at hk
    simpa only [smul_apply, smul_eq_mul, mul_comm] using sub_eq_zero.mp hk
  refine ⟨B w, lt_of_le_of_ne hc ?_, heq⟩
  intro hz
  apply hB
  rw [heq, ← hz, zero_smul]

lemma fderiv_ne_zero_of_sum_sq_pos {r : Domain d → ℝ} {x : Domain d}
    (hp : 0 < ∑ k, (definingPartial r k x) ^ 2) : fderiv ℝ r x ≠ 0 := by
  intro hz
  have hh : (∑ k, (definingPartial r k x) ^ 2) = 0 := by
    simp [definingPartial, hz]
  linarith

/-- Local defining functions with the same sublevel set determine the same normal. -/
theorem HasOutwardNormalAt.eq
    {ν η : Fin d → Domain d → ℝ} {x : Domain d}
    (hν : HasOutwardNormalAt Ω ν x) (hη : HasOutwardNormalAt Ω η x) (j : Fin d) :
    ν j x = η j x := by
  obtain ⟨U, r, hxU, hr, hr0, hside_r, hpr, hνr⟩ := hν
  obtain ⟨V, s, hxV, hs, hs0, hside_s, hps, hηs⟩ := hη
  have hdr : DifferentiableAt ℝ r x :=
    (hr.contDiffAt (U.isOpen.mem_nhds hxU)).differentiableAt (by norm_num)
  have hds : DifferentiableAt ℝ s x :=
    (hs.contDiffAt (V.isOpen.mem_nhds hxV)).differentiableAt (by norm_num)
  have hp : ∀ᶠ y in 𝓝 x, 0 ≤ r y * s y := by
    filter_upwards [U.isOpen.mem_nhds hxU, V.isOpen.mem_nhds hxV] with y hyU hyV
    by_cases hnegative : r y < 0
    · exact mul_nonneg_of_nonpos_of_nonpos hnegative.le
        ((hside_s y hyV).mp ((hside_r y hyU).mpr hnegative)).le
    · have hsnonneg : 0 ≤ s y := by
        by_contra hh
        exact hnegative ((hside_r y hyU).mp ((hside_s y hyV).mpr (lt_of_not_ge hh)))
      exact mul_nonneg (le_of_not_gt hnegative) hsnonneg
  obtain ⟨c, hc, heq⟩ := positive_proportional_of_mul_nonneg
    (fderiv ℝ r x) (fderiv ℝ s x)
    (fderiv_ne_zero_of_sum_sq_pos hpr) (fderiv_ne_zero_of_sum_sq_pos hps)
    (derivative_product_nonneg hdr hds hr0 hs0 hp)
  have hcoef (k : Fin d) : definingPartial s k x = c * definingPartial r k x := by
    simp only [definingPartial, heq, smul_apply, smul_eq_mul]
  have hsum : (∑ k, (definingPartial s k x) ^ 2) =
      c ^ 2 * (∑ k, (definingPartial r k x) ^ 2) := by
    simp_rw [hcoef, mul_pow]
    rw [Finset.mul_sum]
  have hsqrt : Real.sqrt (∑ k, (definingPartial s k x) ^ 2) =
      c * Real.sqrt (∑ k, (definingPartial r k x) ^ 2) := by
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]
  rw [hνr j, hηs j, normalizedGradient, normalizedGradient, hcoef, hsqrt]
  exact (mul_div_mul_left _ _ hc.ne').symm

/-- The sublevel-set convention fixes a unique normalized conormal. -/
theorem IsOutwardUnitNormal.eqOn_frontier
    {ν η : Fin d → Domain d → ℝ}
    (hν : IsOutwardUnitNormal Ω ν) (hη : IsOutwardUnitNormal Ω η)
    {x : Domain d} (hx : x ∈ frontier (Ω : Set (Domain d))) (j : Fin d) :
    ν j x = η j x :=
  (show HasOutwardNormalAt Ω ν x from hν.2.2 x hx).eq (hη.2.2 x hx) j

/-- Any two geometric outward normals agree as actual surface-a.e. data. -/
theorem IsOutwardUnitNormal.ae_eq
    {ν η : Fin d → Domain d → ℝ}
    (hν : IsOutwardUnitNormal Ω ν) (hη : IsOutwardUnitNormal Ω η) (j : Fin d) :
    ν j =ᵐ[ExpandedFA.Sobolev.Trace.surfaceMeasure Ω] η j := by
  filter_upwards [ExpandedFA.Sobolev.Trace.surfaceMeasure_ae_frontier Ω] with x hx
  exact hν.eqOn_frontier hη hx j


end NormalUniqueness

/-- A continuous local defining function vanishes on the geometric frontier. -/
lemma definingFunction_eq_zero_on_frontier
    (U : Opens (Domain d)) (r : Domain d → ℝ) (hr : ContinuousOn r U)
    (hside : ∀ y ∈ U, y ∈ Ω ↔ r y < 0)
    (y : Domain d) (hyU : y ∈ U) (hy : y ∈ frontier (Ω : Set (Domain d))) :
    r y = 0 := by
  have hc : ContinuousAt r y := hr.continuousAt (U.isOpen.mem_nhds hyU)
  change y ∈ closure (Ω : Set (Domain d)) ∧ y ∉ interior (Ω : Set (Domain d)) at hy
  rw [Ω.isOpen.interior_eq] at hy
  have hclosure : y ∈ closure ((U : Set (Domain d)) ∩ Ω) :=
    U.isOpen.inter_closure ⟨hyU, hy.1⟩
  have hle : r y ∈ closure (Iio (0 : ℝ)) :=
    hc.continuousWithinAt.mem_closure hclosure (fun z hz => (hside z hz.1).mp hz.2)
  have hnonneg : 0 ≤ r y := by
    by_contra h
    exact hy.2 ((hside y hyU).mpr (lt_of_not_ge h))
  exact le_antisymm (by simpa only [closure_Iio, mem_Iic] using hle) hnonneg

/-- The geometric normal predicate already forces continuity along the boundary. -/
theorem IsOutwardUnitNormal.continuousOn_frontier
    {ν : Fin d → Domain d → ℝ} (hν : IsOutwardUnitNormal Ω ν) (j : Fin d) :
    ContinuousOn (ν j) (frontier (Ω : Set (Domain d))) := by
  intro x hx
  obtain ⟨U, r, hxU, hr, hr0, hside, hp, hνr⟩ := hν.2.2 x hx
  have hg (k : Fin d) : ContinuousAt (definingPartial r k) x :=
    ((hr.continuousOn_fderiv_of_isOpen U.isOpen (by norm_num)).clm_apply
      continuousOn_const).continuousAt (U.isOpen.mem_nhds hxU)
  have hs : ContinuousAt (fun y => ∑ k, (definingPartial r k y) ^ 2) x :=
    tendsto_finsetSum _ (fun k _ => (hg k).pow 2)
  have hpos : ∀ᶠ y in 𝓝 x, 0 < ∑ k, (definingPartial r k y) ^ 2 :=
    hs.eventually (lt_mem_nhds hp)
  have hc : ContinuousAt (normalizedGradient r j) x :=
    (hg j).div hs.sqrt (Real.sqrt_pos.2 hp).ne'
  apply hc.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ hx
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (U.isOpen.mem_nhds hxU),
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hpos] with y hy hyU hyp
  exact (show HasOutwardNormalAt Ω ν y from hν.2.2 y hy).eq
    ⟨U, r, hyU, hr, definingFunction_eq_zero_on_frontier U r hr.continuousOn hside y hyU hy,
      hside, hyp, fun _ => rfl⟩ j



section ClassicalBridge

/-- Continuous ambient functions belong to every Lp on a
bounded domain. This is used only to identify classical and graph derivatives. -/
lemma continuous_memLp_on_bounded
    (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (f : Domain d → 𝕜) (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (Ω : Set (Domain d))) := by
  letI : IsFiniteMeasure (volume.restrict (Ω : Set (Domain d))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hC x (subset_closure hx)

/-- A smooth representative determines the actual weak partials of the
shared Sobolev graph, not just its order-zero component. -/
theorem weakPartial_eq_smooth
    (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (u : H1 𝕜 Ω) (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : value u =ᵐ[volume.restrict (Ω : Set (Domain d))] f) (j : Fin d) :
    weakPartial u j =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => fderiv ℝ f x (coordinateVector j) := by
  have hD (k : Fin d) : Continuous (fun x => fderiv ℝ f x (coordinateVector k)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨w, hw, hder⟩ := C1Extension.Classical.c1_mem_sobolev f
    (hf.of_le (by simp)).contDiffOn (continuous_memLp_on_bounded hb f hf.continuous 2)
    (fun k => continuous_memLp_on_bounded hb _ (hD k) 2)
  have huw : u = w := sobolev_underlying_injective 𝕜 d Ω 1 2
    (Lp.ext (hu.trans hw.symm))
  subst w
  simpa only [weakPartial, firstIndex_eq_coordinateIndex] using hder j

lemma partial_mul_conj (f g : Domain d → 𝕜)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Domain d) (j : Fin d) :
    fderiv ℝ (fun y => f y * conj (g y)) x (coordinateVector j) =
      f x * conj (fderiv ℝ g x (coordinateVector j)) +
        fderiv ℝ f x (coordinateVector j) * conj (g x) := by
  have hc := (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).hasFDerivAt.comp x (hg x).hasFDerivAt
  have hp := (hf x).hasFDerivAt.mul hc
  simp only [RCLike.conjCLE_apply, Function.comp_def, Pi.mul_def] at hp
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, RCLike.conjCLE_apply, smul_eq_mul]
  ring

/-- Smooth scalar divergence implies Green's first identity, first for smooth
representatives and then by the proved H¹ density argument. -/
theorem firstIdentity_of_smooth_divergence
    (hb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω)
    (ν : Fin d → Domain d → ℝ) (hν : IsOutwardUnitNormal Ω ν)
    (hdiv : ∀ (f : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) f → ∀ j : Fin d,
      (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
      ∫ x, f x * (ν j x : 𝕜) ∂surfaceMeasure Ω)
    (T : H1 𝕜 Ω →L[𝕜] BoundaryLp 𝕜 Ω 2) (hT : IsTrace T) :
    ∀ (u v : H1 𝕜 Ω) (j : Fin d), FirstIdentity T ν u v j := by
  apply firstIdentity_of_smooth hb hΩ ν hν T
  intro u hu v hv j
  obtain ⟨f, hf, huf⟩ := hu
  obtain ⟨g, hg, hvg⟩ := hv
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * conj (g x)) :=
    hf.mul ((RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).contDiff.comp hg)
  unfold FirstIdentity
  calc
    _ = ∫ x in (Ω : Set (Domain d)),
        fderiv ℝ (fun y => f y * conj (g y)) x (coordinateVector j) := by
      apply integral_congr_ae
      filter_upwards [huf, hvg, weakPartial_eq_smooth hb u f hf huf j,
        weakPartial_eq_smooth hb v g hg hvg j] with x hfx hgx hdfx hdgx
      rw [hfx, hgx, hdfx, hdgx,
        partial_mul_conj f g (hf.differentiable (by simp)) (hg.differentiable (by simp))]
    _ = ∫ x, f x * conj (g x) * (ν j x : 𝕜) ∂surfaceMeasure Ω :=
      hdiv _ hF j
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hT u f hf huf, hT v g hg hvg] with x hfx hgx
      rw [hfx, hgx]

end ClassicalBridge

/-- Normal construction, trace existence, and density assemble the first
identity from smooth scalar divergence. -/
theorem firstOrderGreen_of_smooth_divergence
    (hdiv : ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
      Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
      ∀ (ν : Fin d → Domain d → ℝ), IsOutwardUnitNormal Ω ν →
      ∀ (f : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) f → ∀ j : Fin d,
        (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
        ∫ x, f x * (ν j x : 𝕜) ∂surfaceMeasure Ω) :
    Specs.ExpandedFA.PartIV.GreenFormulas.FirstOrderGreen := by
  intro 𝕜 _ d Ω hb hΩ
  refine ⟨outward_normal_exists hb hΩ, Trace.trace_exists 𝕜 d Ω hb hΩ.isC1 2 (by norm_num), ?_⟩
  intro ν hν T hT
  exact firstIdentity_of_smooth_divergence hb hΩ ν hν
    (hdiv 𝕜 d Ω hb hΩ ν hν) T hT

/-- For bounded domains, a smooth cutoff equal to one near the closure
reduces the geometric divergence formula to compactly supported functions. -/
theorem smooth_divergence_of_compact_support
    (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (ν : Fin d → Domain d → ℝ)
    (hdiv : ∀ (f : Domain d → 𝕜), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ j : Fin d,
      (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
      ∫ x, f x * (ν j x : 𝕜) ∂surfaceMeasure Ω)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin d) :
    (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
      ∫ x, f x * (ν j x : 𝕜) ∂surfaceMeasure Ω := by
  obtain ⟨R, hR, hbound⟩ := hb.closure.subset_ball_lt 0 (0 : Domain d)
  let B : ContDiffBump (0 : Domain d) := ⟨R, R + 1, hR, lt_add_one R⟩
  let g : Domain d → 𝕜 := fun x => B x • f x
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := B.contDiff.smul hf
  have hgc : HasCompactSupport g := B.hasCompactSupport.smul_right
  have heq (x : Domain d) (hx : x ∈ closure (Ω : Set (Domain d))) : g =ᶠ[𝓝 x] f := by
    have hB := B.eventuallyEq_one_of_mem_ball (hbound hx)
    filter_upwards [hB] with y hy
    simp only [g, hy, Pi.one_apply, one_smul]
  calc
    _ = ∫ x in (Ω : Set (Domain d)), fderiv ℝ g x (coordinateVector j) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [(heq x (subset_closure hx)).fderiv_eq]
    _ = ∫ x, g x * (ν j x : 𝕜) ∂surfaceMeasure Ω := hdiv g hg hgc j
    _ = _ := by
      apply integral_congr_ae
      have hfront : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier (Ω : Set (Domain d)) :=
        Measure.ae_smul_measure (ae_restrict_mem isClosed_frontier.measurableSet) _
      filter_upwards [hfront] with x hx
      rw [(heq x (frontier_subset_closure hx)).eq_of_nhds]


section RealDivergenceReduction

/-- Smooth boundary fluxes are integrable for the actual surface measure.
The real coefficient needs only the measurability and bound already present
in the geometric normal predicate. -/
theorem integrable_smooth_boundary_flux
    (hb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω)
    (ν : Fin d → Domain d → ℝ) (hν : IsOutwardUnitNormal Ω ν)
    (f : Domain d → 𝕜) (hf : Continuous f) (j : Fin d) :
    Integrable (fun x => f x * (ν j x : 𝕜)) (surfaceMeasure Ω) := by
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hi : Integrable f (surfaceMeasure Ω) := memLp_one_iff_integrable.mp
    (Trace.continuous_boundary_memLp Ω hΩ.isC1 hc 1 f hf)
  apply hi.mul_bdd
  · exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.comp_aestronglyMeasurable (hν.1 j)
  · simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using hν.2.1 j

/-- Composition with a real continuous linear functional commutes with a
classical coordinate partial. This also applies to the real and imaginary
parts without changing the underlying Euclidean coordinates. -/
lemma partial_clm_comp (L : 𝕜 →L[ℝ] ℝ) (f : Domain d → 𝕜)
    (hf : Differentiable ℝ f) (x : Domain d) (j : Fin d) :
    fderiv ℝ (fun y => L (f y)) x (coordinateVector j) =
      L (fderiv ℝ f x (coordinateVector j)) := by
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
    congrArg (fun A : Domain d →L[ℝ] ℝ => A (coordinateVector j))
      (L.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv

/-- The geometric divergence theorem only needs to be established over ℝ.
Both scalar conventions of the original targets follow by applying it to
the real and imaginary parts, with all integrability checked explicitly. -/
theorem smooth_divergence_of_real
    (hb : Bornology.IsBounded (Ω : Set (Domain d))) (hΩ : IsC2Domain Ω)
    (ν : Fin d → Domain d → ℝ) (hν : IsOutwardUnitNormal Ω ν)
    (hreal : ∀ (f : Domain d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → ∀ j : Fin d,
      (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
        ∫ x, f x * ν j x ∂surfaceMeasure Ω)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin d) :
    (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
      ∫ x, f x * (ν j x : 𝕜) ∂surfaceMeasure Ω := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hi : Integrable (fun x => fderiv ℝ f x (coordinateVector j))
      (volume.restrict (Ω : Set (Domain d))) := memLp_one_iff_integrable.mp
    (continuous_memLp_on_bounded hb _
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) 1)
  have hbdy := integrable_smooth_boundary_flux hb hΩ ν hν f hf.continuous j
  apply RCLike.ext
  · rw [← integral_re hi, ← integral_re hbdy]
    have hr := hreal (fun x => RCLike.re (f x))
      ((RCLike.reCLM : 𝕜 →L[ℝ] ℝ).contDiff.comp hf) j
    have hD (x : Domain d) :
        fderiv ℝ (fun y => RCLike.re (f y)) x (coordinateVector j) =
          RCLike.re (fderiv ℝ f x (coordinateVector j)) :=
      partial_clm_comp (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) f hd x j
    simp_rw [hD] at hr
    simpa only [RCLike.mul_re, RCLike.ofReal_re,
      RCLike.ofReal_im, mul_zero, sub_zero] using hr
  · rw [← integral_im hi, ← integral_im hbdy]
    have hr := hreal (fun x => RCLike.im (f x))
      ((RCLike.imCLM : 𝕜 →L[ℝ] ℝ).contDiff.comp hf) j
    have hD (x : Domain d) :
        fderiv ℝ (fun y => RCLike.im (f y)) x (coordinateVector j) =
          RCLike.im (fderiv ℝ f x (coordinateVector j)) :=
      partial_clm_comp (RCLike.imCLM : 𝕜 →L[ℝ] ℝ) f hd x j
    simp_rw [hD] at hr
    simpa only [RCLike.mul_im, RCLike.ofReal_re,
      RCLike.ofReal_im, mul_zero, zero_add] using hr

end RealDivergenceReduction

/-- Real compactly supported divergence gives the first identity over both
scalar fields, by a cutoff, real and imaginary parts, and H¹ density. -/
theorem firstOrderGreen_of_real_compact_divergence
    (hdiv : ∀ (d : ℕ) (Ω : Opens (Domain d)),
      Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
      ∀ (ν : Fin d → Domain d → ℝ), IsOutwardUnitNormal Ω ν →
      ∀ (f : Domain d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ j : Fin d,
        (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
          ∫ x, f x * ν j x ∂surfaceMeasure Ω) :
    Specs.ExpandedFA.PartIV.GreenFormulas.FirstOrderGreen := by
  apply firstOrderGreen_of_smooth_divergence
  intro 𝕜 _ d Ω hb hΩ ν hν f hf j
  exact smooth_divergence_of_real hb hΩ ν hν
    (smooth_divergence_of_compact_support hb ν (hdiv d Ω hb hΩ ν hν)) f hf j

/-- It suffices to prove real compactly supported divergence for a single
geometric outward normal on each domain. Normal uniqueness then gives the
universal normal quantifier in the independent original specification. -/
theorem firstOrderGreen_of_one_normal_divergence
    (hdiv : ∀ (d : ℕ) (Ω : Opens (Domain d)),
      Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
      ∃ (ν : Fin d → Domain d → ℝ), IsOutwardUnitNormal Ω ν ∧
        ∀ (f : Domain d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ∀ j : Fin d,
          (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
            ∫ x, f x * ν j x ∂surfaceMeasure Ω) :
    Specs.ExpandedFA.PartIV.GreenFormulas.FirstOrderGreen := by
  apply firstOrderGreen_of_real_compact_divergence
  intro d Ω hb hΩ ν hν f hf hcompact j
  obtain ⟨η, hη, hηdiv⟩ := hdiv d Ω hb hΩ
  calc
    _ = ∫ x, f x * η j x ∂surfaceMeasure Ω := hηdiv f hf hcompact j
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hη.ae_eq hν j] with x hx
      rw [hx]

/-- Green's first-order identity for all H¹ pairs, with existence of the
actual L² trace and geometric normal and with every supplied such trace and
normal. Both real and complex scalars and dimension zero are included. -/
theorem firstOrder_green :
    Specs.ExpandedFA.PartIV.GreenFormulas.FirstOrderGreen := by
  apply firstOrderGreen_of_real_compact_divergence
  intro d Ω hb hΩ ν hν
  exact ExpandedFA.SmoothBoundaryDivergence.compact_real_smooth_divergence
    d Ω hb hΩ ν hν.1 hν.2.1 hν.2.2

/-- Green's second identity for H² and H¹, using the L² traces of the weak
first derivatives in its outward normal derivative. -/
theorem second_green : Specs.ExpandedFA.PartIV.GreenFormulas.SecondGreen :=
  secondGreen_of_firstOrderGreen firstOrder_green

end ExpandedFA.PartIV.GreenFormulas
