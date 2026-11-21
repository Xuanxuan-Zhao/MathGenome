import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ImproperInterchange
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.D04.C08.UniformTailsContinuity

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter Topology
open scoped Classical ENNReal BigOperators
namespace D04.ImproperInterchange
open Darboux JordanRegions ImproperExhaustions
open Specs.D04.C08.ImproperInterchange.Model

variable {p q k : ℕ}

@[simp] lemma left_product (x : E p) (y : E q) : leftBlock (productPoint x y) = x := by
  ext i
  exact Fubini.blockPoint_left finSumFinEquiv x y i
@[simp] lemma right_product (x : E p) (y : E q) : rightBlock (productPoint x y) = y := by
  ext i
  exact Fubini.blockPoint_right finSumFinEquiv x y i
@[simp] lemma product_blocks (z : E (p + q)) : productPoint (leftBlock z) (rightBlock z) = z := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [productPoint, Specs.D04.C06.DarbouxFubini.Model.productPoint,
    leftBlock, rightBlock]

lemma continuous_left : Continuous (@leftBlock p q) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => PiLp.continuous_apply 2 _ _))
lemma continuous_right : Continuous (@rightBlock p q) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => PiLp.continuous_apply 2 _ _))

lemma blocks_mem {A : Box p} {B : Box q} {z : E (p+q)}
    (hz : z ∈ carrier (productBox A B)) : leftBlock z ∈ carrier A ∧ rightBlock z ∈ carrier B := by
  apply (Fubini.blockPoint_mem finSumFinEquiv).mp
  change productPoint (leftBlock z) (rightBlock z) ∈ carrier (productBox A B)
  simpa only [product_blocks] using hz

@[simp] lemma extension_product {V : Type} [Zero V] (S : Set (E q))
    (f : E p → E q → V) (x : E p) (y : E q) :
    productExtension S f (productPoint x y) = if y ∈ S then f x y else 0 := by
  simp [productExtension]

lemma null_product (A : Box p) {T : Set (E q)} (hT : NullCovers.Null T) :
    NullCovers.Null {z : E (p+q) | leftBlock z ∈ carrier A ∧ rightBlock z ∈ T} := by
  intro ε hε
  let δ := ε / (content A + 1)
  have hA := content_nonneg A
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨ι, hi, R, hcover, hsum⟩ := hT δ hδ
  letI := hi
  refine ⟨ι, hi, fun i => productBox A (R i), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz.2)
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hh := (Fubini.blockPoint_mem finSumFinEquiv).mpr ⟨hz.1, hi⟩
    change productPoint (leftBlock z) (rightBlock z) ∈ carrier (productBox A (R i)) at hh
    simpa only [product_blocks] using hh
  · have he (R : Box q) : content (productBox A R) = content A * content R :=
      productBox_content A R
    simp_rw [he, ENNReal.ofReal_mul hA]
    rw [ENNReal.tsum_mul_left]
    calc
      ENNReal.ofReal (content A) * ∑' i, ENNReal.ofReal (content (R i)) ≤
          ENNReal.ofReal (content A) * ENNReal.ofReal δ := by gcongr
      _ = ENNReal.ofReal (content A * δ) := (ENNReal.ofReal_mul hA).symm
      _ < ENNReal.ofReal ε := by
        apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
        have he : δ * (content A + 1) = ε := div_mul_cancel₀ _ (by positivity)
        nlinarith

lemma null_frontier {S : Set (E q)} (hS : Jordan S) : NullCovers.Null (frontier S) := by
  rcases q with _ | q
  · have he : frontier S = ∅ := (isClopen_discrete S).frontier_eq
    rw [he]
    exact ExceptionalSets.null_empty
  · exact NullCovers.contentZero_null
      ((jordan_iff_boundary (Nat.succ_pos _) S (jordan_bounded hS)).mp hS)

lemma continuous_integrable (A : Box p) {g : E p → ℝ}
    (hg : ContinuousOn g (carrier A)) : Integrable g A := by
  rcases p with _ | p
  · exact (Darboux.zero_dimension A g).2.1
  · exact ExceptionalSets.integrable_continuous (Nat.succ_pos _) A g hg

/-- Continuity is only required on the actual compact product. -/
lemma scalar_product_integrable (A : Box p) (B : Box q) {S : Set (E q)}
    (hS : IsCompact S) (hj : Jordan S) (f : E p → E q → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (carrier A ×ˢ S)) :
    Integrable (productExtension S f) (productBox A B) := by
  have hb := ((DiscontinuityCriterion.carrier_compact A).prod hS).image_of_continuousOn hf
  obtain ⟨M, hMpos, hM⟩ := hb.isBounded.exists_pos_norm_le
  have hbound : Bounded (productExtension S f) (productBox A B) := by
    apply bounded_of_abs_le (M := M)
    intro z hz
    by_cases hs : rightBlock z ∈ S
    · simpa [productExtension, hs] using hM _ ⟨(leftBlock z, rightBlock z),
        ⟨(blocks_mem hz).1, hs⟩, rfl⟩
    · simp [productExtension, hs, hMpos.le]
  by_cases hn : p + q = 0
  · have he : p = 0 ∧ q = 0 := Nat.add_eq_zero_iff.mp hn
    rcases he with ⟨rfl, rfl⟩
    exact (Darboux.zero_dimension _ _).2.1
  apply (DiscontinuityCriterion.integrable_iff_null_discontinuitySet
    (Nat.pos_of_ne_zero hn) _ _ hbound).mpr
  apply NullCovers.null_mono (T := {z : E (p+q) |
    leftBlock z ∈ carrier A ∧ rightBlock z ∈ frontier S}) _
    (null_product A (null_frontier hj))
  rintro z ⟨hz, hdisc⟩
  refine ⟨(blocks_mem hz).1, ?_⟩
  by_contra hnot
  have he : rightBlock z ∈ interior S ∨ rightBlock z ∈ (closure S)ᶜ := by
    by_cases hs : rightBlock z ∈ closure S
    · exact Or.inl (by by_contra hn; exact hnot ⟨hs, hn⟩)
    · exact Or.inr hs
  apply hdisc
  rcases he with hi | ho
  · have hnear : ∀ᶠ w in 𝓝 z, rightBlock w ∈ interior S :=
      continuous_right.continuousAt (isOpen_interior.mem_nhds hi)
    have hpair : ContinuousWithinAt (fun w : E (p+q) => (leftBlock w, rightBlock w))
        (carrier (productBox A B)) z :=
      (continuous_left.prodMk continuous_right).continuousWithinAt
    have hwithin : ∀ᶠ w in 𝓝[carrier (productBox A B)] z,
        (leftBlock w, rightBlock w) ∈ carrier A ×ˢ S := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear] with w hw hn
      exact ⟨(blocks_mem hw).1, interior_subset hn⟩
    have hc : ContinuousWithinAt (fun w => f (leftBlock w) (rightBlock w))
        (carrier (productBox A B)) z :=
      (hf _ ⟨(blocks_mem hz).1, interior_subset hi⟩).comp_of_preimage_mem_nhdsWithin
        hpair hwithin
    apply hc.congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds hnear] with w hw
      simp [productExtension, interior_subset hw]
    · simp [productExtension, interior_subset hi]
  · have hnear : ∀ᶠ w in 𝓝 z, rightBlock w ∈ (closure S)ᶜ :=
      continuous_right.continuousAt (isClosed_closure.isOpen_compl.mem_nhds ho)
    apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds hnear] with w hw
      exact if_neg (show rightBlock w ∉ S from fun hs => hw (subset_closure hs))
    · exact if_neg (show rightBlock z ∉ S from fun hs => ho (subset_closure hs))

lemma compact_region_integrable {S : Set (E q)} (hS : IsCompact S) (hj : Jordan S)
    {g : E q → ℝ} (hg : ContinuousOn g S) : RegionIntegrable (fun y : S => g y) := by
  rcases q with _ | q
  · exact region_integrable_zero_dim _ _
  apply integrable_of_null_relative_discontinuities (Nat.succ_pos _) hj
  · obtain ⟨M, hM⟩ := (hS.image_of_continuousOn hg).isBounded.exists_norm_le
    exact ⟨M, fun y => hM _ ⟨y, y.property, rfl⟩⟩
  · apply NullCovers.null_mono (T := ∅) _ ExceptionalSets.null_empty
    rintro y ⟨hy, hd⟩
    exact hd ((hg.restrict).continuousAt)

lemma scalar_proper_fubini (A : Box p) {S : Set (E q)}
    (hS : IsCompact S) (hj : Jordan S) (f : E p → E q → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (carrier A ×ˢ S)) :
    Integrable (productExtension S f) (productBox A (enclosingBox S)) ∧
    (∀ x ∈ carrier A, RegionIntegrable (fun y : S => f x y)) ∧
    Integrable (fun x => regionIntegral (fun y : S => f x y)) A ∧
    RegionIntegrable (fun y : S => lowerIntegral (fun x => f x y) A) ∧
    lowerIntegral (fun x => regionIntegral (fun y : S => f x y)) A =
      regionIntegral (fun y : S => lowerIntegral (fun x => f x y) A) := by
  let B := enclosingBox S
  have hB : Encloses S B := enclosingBox_encloses (jordan_bounded hj)
  have hy (x) (hx : x ∈ carrier A) : RegionIntegrable (fun y : S => f x y) :=
    compact_region_integrable hS hj
      (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hx, hy⟩))
  have hx (y) (hy : y ∈ S) : Integrable (fun x => f x y) A :=
    continuous_integrable A
      (hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, hy⟩))
  have hprod := scalar_product_integrable A B hS hj f hf
  have hinner (x) (hx : x ∈ carrier A) :
      Integrable (fun y => productExtension S f (productPoint x y)) B := by
    have he : (fun y => productExtension S f (productPoint x y)) =
        zeroExtension (fun y : S => f x y) := by
      funext y
      simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension]
    rw [he]
    exact (region_integrable_iff_box _ hB).mp (hy x hx)
  obtain ⟨hout, hout_eq⟩ := fubini_slices A B _ hprod hinner
    (fun x => regionIntegral (fun y : S => f x y)) (fun x hx => by
      have hh := integral_eq_on_enclosing_box _ (hy x hx) hB
        ((region_integrable_iff_box _ hB).mp (hy x hx))
      simpa only [integral, Specs.D04.C06.DarbouxIntegral.Model.integral,
        show (fun y => productExtension S f (productPoint x y)) =
          zeroExtension (fun y : S => f x y) from by
            funext y; simp [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension]] using hh)
  have hreverse (y) (_hy : y ∈ carrier B) :
      Integrable (fun x => productExtension S f (productPoint x y)) A := by
    by_cases hys : y ∈ S
    · simpa only [extension_product, if_pos hys] using hx y hys
    · simpa only [extension_product, if_neg hys] using integrable_const A 0
  obtain ⟨hrev, hrev_eq⟩ := fubini_slices_reverse A B _ hprod hreverse
    (zeroExtension (fun y : S => lowerIntegral (fun x => f x y) A)) (fun y hy => by
      by_cases hys : y ∈ S
      · simp only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
          dif_pos hys, extension_product, if_pos hys, integral,
          Specs.D04.C06.DarbouxIntegral.Model.integral]
      · simp only [zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
          dif_neg hys, extension_product, if_neg hys]
        simpa only [zero_mul] using (integral_const A 0 _).symm)
  have hregion : RegionIntegrable (fun y : S => lowerIntegral (fun x => f x y) A) :=
    (region_integrable_iff_box _ hB).mpr hrev
  refine ⟨hprod, hy, hout, hregion, ?_⟩
  exact hout_eq.trans (hrev_eq.symm.trans
    (integral_eq_on_enclosing_box _ hregion hB hrev).symm)

lemma proper_fubini : Specs.D04.C08.ImproperInterchange.proper_fubiniType := by
  intro p q k A S hS hj f hf
  have hs (i : Fin k) := scalar_proper_fubini A hS hj (fun x y => f x y i)
    ((PiLp.continuous_apply 2 _ i).continuousOn.comp hf (fun _ _ => mem_univ _))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have he : (fun z => productExtension S f z i) =
        productExtension S (fun x y => f x y i) := by
      funext z
      by_cases hz : rightBlock z ∈ S <;> simp [productExtension, hz]
    rw [he]
    exact (hs i).1
  · intro x hx
    exact ⟨jordan_bounded hj, fun i => (hs i).2.1 x hx⟩
  · intro i
    exact (hs i).2.2.1
  · exact ⟨jordan_bounded hj, fun i => (hs i).2.2.2.1⟩
  · ext i
    exact (hs i).2.2.2.2

lemma truncated_continuous (A : Box p) {Ω : Set (E q)} {K : ℕ → Set (E q)}
    (hK : RegularExhaustion Ω K) (f : E p → E q → E k)
    (hf : ContinuousOn (Function.uncurry f) (carrier A ×ˢ Ω)) (j : ℕ) :
    ContinuousOn (fun x => vectorRegionIntegral (fun y : K j => f x y)) (carrier A) := by
  have hc : Continuous (fun z : closure (K j) × carrier A => f z.2 z.1) :=
    hf.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)) (fun z =>
          ⟨z.2.property, (hK.1 j).2.2
            ((le_of_eq (hK.1 j).1.isClosed.closure_eq) z.1.property)⟩)
  have hi := ProperContinuity.joint_continuity (P := carrier A) (hK.1 j).2.1
    (fun z : closure (K j) × carrier A => f z.2 z.1) hc
  exact continuousOn_iff_continuous_restrict.mpr hi.2

lemma coordinate_uniform {ι : Type*} {l : Filter ι} {S : Set (E p)}
    {F : ι → E p → E k} {H : E p → E k}
    (hu : TendstoUniformlyOn F H l S) (i : Fin k) :
    TendstoUniformlyOn (fun j x => F j x i) (fun x => H x i) l S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with j hj x hx
  have he := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (H x - F j x) i
  exact lt_of_le_of_lt (by simpa [Real.dist_eq] using he)
    (by simpa only [dist_eq_norm] using hj x hx)

lemma box_integral_uniform_limit (A : Box p) (F : ℕ → E p → E k) (H : E p → E k)
    (hi : ∀ j, VectorIntegrable (F j) A)
    (hu : TendstoUniformlyOn F H atTop (carrier A)) :
    VectorIntegrable H A ∧
    Tendsto (fun j => boxIntegral A (F j)) atTop (𝓝 (boxIntegral A H)) := by
  have hc (i : Fin k) := Darboux.uniform_limit (fun j x => F j x i) (fun x => H x i)
    (fun j => hi j i) (coordinate_uniform hu i)
  refine ⟨fun i => (hc i).choose, ?_⟩
  exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun i => (hc i).choose_spec))

/-- The integrand in the reverse improper integral is locally Riemann
integrable on the entire open domain, not only on the chosen truncations. -/
lemma integrated_locally_integrable (A : Box p) {Ω : Set (E q)}
    (f : E p → E q → E k)
    (hf : ContinuousOn (Function.uncurry f) (carrier A ×ˢ Ω)) :
    AbsoluteConvergence.LocallyVectorRiemannIntegrable Ω
      (fun y => boxIntegral A (fun x => f x y)) := by
  intro i Q hQ
  have hc : ContinuousOn (Function.uncurry (fun x y => f x y i))
      (carrier A ×ˢ carrier Q) :=
    ((PiLp.continuous_apply 2 _ i).comp_continuousOn hf).mono (prod_mono_right hQ)
  have hp := scalar_product_integrable A Q (DiscontinuityCriterion.carrier_compact Q)
    (jordan_box Q) (fun x y => f x y i) hc
  have hs (y) (hy : y ∈ carrier Q) : Integrable
      (fun x => productExtension (carrier Q) (fun x y => f x y i) (productPoint x y)) A := by
    simp only [extension_product, if_pos hy]
    apply continuous_integrable A
    exact hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hx, hy⟩)
  obtain ⟨hi, _⟩ := fubini_slices_reverse A Q _ hp hs
    (fun y => lowerIntegral (fun x => f x y i) A) (fun y hy => by
      simp only [extension_product, if_pos hy, integral,
        Specs.D04.C06.DarbouxIntegral.Model.integral])
  exact hi

lemma improper_interchange : Specs.D04.C08.ImproperInterchange.improper_interchangeType := by
  intro p q k A Ω K f _hΩ hK hf hu
  obtain ⟨H, hH⟩ := hu
  change TendstoUniformlyOn (fun j x => vectorRegionIntegral (fun y : K j => f x y))
    H atTop (carrier A) at hH
  have hp (j : ℕ) := proper_fubini A (hK.1 j).1 (hK.1 j).2.1 f
    (hf.mono (prod_mono_right (hK.1 j).2.2))
  have hc : ContinuousOn H (carrier A) :=
    hH.continuousOn (Frequently.of_forall (truncated_continuous A hK f hf))
  have hl := box_integral_uniform_limit A
    (fun j x => vectorRegionIntegral (fun y : K j => f x y)) H
    (fun j => (hp j).2.2.1) hH
  have hr : AbsoluteConvergence.HasVectorIntegralAlong
      (fun y => boxIntegral A (fun x => f x y)) K (boxIntegral A H) := by
    change Tendsto _ _ _
    exact hl.2.congr (fun j => (hp j).2.2.2.2)
  refine ⟨H, hH, hc, hl.1, ?_, ?_, integrated_locally_integrable A f hf, hr, hr.limUnder_eq⟩
  · intro x hx
    have ht := hH.tendsto_at hx
    exact ⟨ht, ht.limUnder_eq.symm⟩
  · intro j
    exact ⟨(hp j).1, (hp j).2.2.2.1, (hp j).2.2.2.2⟩

/-- Real scalar data embed isometrically as a one-coordinate Euclidean target. -/
lemma scalar_interchange : Specs.D04.C08.ImproperInterchange.scalar_interchangeType := by
  intro p q A Ω K f hΩ hK hf hu
  let v : E p → E q → E 1 := fun x y => WithLp.toLp 2 (fun _ => f x y)
  have hv : ContinuousOn (Function.uncurry v) (carrier A ×ˢ Ω) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (continuousOn_pi.mpr (fun _ => hf))
  obtain ⟨G, hG⟩ := hu
  have hvg : Specs.D04.C08.UniformTailsContinuity.Model.UniformImproperConverges K
      (fun y x => v x y) (carrier A) := by
    refine ⟨fun x => WithLp.toLp 2 (fun _ : Fin 1 => G x), ?_⟩
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hG) ε hε] with j hj x hx
    have he : ∀ y : K j, v x y 0 = f x y := fun _ => rfl
    have hi : vectorRegionIntegral (fun y : K j => v x y) =
        WithLp.toLp 2 (fun _ : Fin 1 => regionIntegral (fun y : K j => f x y)) := rfl
    change dist (WithLp.toLp 2 (fun _ : Fin 1 => G x))
      (vectorRegionIntegral (fun y : K j => v x y)) < ε
    rw [hi, dist_eq_norm]
    change ‖WithLp.toLp 2 (fun _ : Fin 1 => G x - regionIntegral (fun y : K j => f x y))‖ < ε
    have hn : ‖WithLp.toLp 2 (fun _ : Fin 1 =>
        G x - regionIntegral (fun y : K j => f x y))‖ =
        |G x - regionIntegral (fun y : K j => f x y)| := by
      rw [EuclideanSpace.norm_eq]
      simpa using Real.sqrt_sq_eq_abs (G x - regionIntegral (fun y : K j => f x y))
    rw [hn]
    simpa only [Real.dist_eq] using hj x hx
  obtain ⟨H, hHu, hHc, hHi, hHx, hHp, hHlocal, hHr, _⟩ :=
    improper_interchange A v hΩ hK hv hvg
  refine ⟨fun x => H x 0, coordinate_uniform hHu 0,
    (PiLp.continuous_apply 2 _ 0).comp_continuousOn hHc, hHi 0, ?_, ?_, hHlocal 0, ?_⟩
  · intro x hx
    exact (PiLp.continuous_apply 2 _ 0).continuousAt.tendsto.comp (hHx x hx).1
  · intro j
    refine ⟨?_, (hHp j).2.1.2 0⟩
    have he : (fun z => productExtension (K j) v z 0) = productExtension (K j) f := by
      funext z
      by_cases hz : rightBlock z ∈ K j <;> simp [productExtension, hz, v]
    rw [← he]
    exact (hHp j).1 0
  · exact (PiLp.continuous_apply 2 _ 0).continuousAt.tendsto.comp hHr

end D04.ImproperInterchange
