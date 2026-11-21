import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.DirectionalQuotients
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.DirectionalSupport
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.Span

noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.ConvexAnalysis

private lemma finite_value {r : WithTop ℝ} (hr : r < ⊤) :
    r = ((r.untopD 0 : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hr)
  rw [← hs, WithTop.untopD_coe]

theorem subdifferential_eq_directional_le : Specs.subdifferential_eq_directional_le.{u} := by
  intro E _ _ f hp hc x hx
  ext y
  change y ∈ subdifferential f x ↔ ∀ d : E, (y d : EReal) ≤ directionalDerivative f x d
  rw [mem_subdifferential_iff (finite_value hx)]
  constructor
  · intro hy d
    apply le_iInf
    intro t
    change (y d : EReal) ≤ directionalQuotient f x d t
    by_cases htfin : f (x + t.val • d) = ⊤
    · simp [directionalQuotient, Specs.directionalQuotient, htfin]
    · have hfin : f (x + t.val • d) < ⊤ := lt_top_iff_ne_top.mpr htfin
      rw [directionalQuotient_of_finite hfin]
      apply EReal.coe_le_coe_iff.mpr
      apply (le_div_iff₀ t.property).mpr
      have h := hy (x + t.val • d)
      rw [finite_value hfin] at h
      have h' := WithTop.coe_le_coe.mp h
      simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at h'
      linarith
  · intro hy z
    by_cases hz : f z = ⊤
    · simp [hz]
    · have hzfin : f z < ⊤ := lt_top_iff_ne_top.mpr hz
      have hd : directionalDerivative f x (z - x) ≤ directionalQuotient f x (z - x) 1 :=
        iInf_le (fun t : {t : ℝ // 0 < t} => directionalQuotient f x (z - x) t) ⟨1, by norm_num⟩
      have hfz : f (x + (1 : ℝ) • (z - x)) < ⊤ := by simpa using hzfin
      rw [directionalQuotient_of_finite hfz] at hd
      have h := (hy (z - x)).trans hd
      simp only [one_smul, add_sub_cancel, div_one] at h
      rw [finite_value hzfin]
      apply WithTop.coe_le_coe.mpr
      have h' := EReal.coe_le_coe_iff.mp h
      linarith

/-- Algebraic Hahn–Banach, including the zero direction. -/
lemma exists_linear_le_sublinear_eq {E : Type u} [AddCommGroup E] [Module ℝ E]
    (p : E → ℝ) (hzero : p 0 = 0)
    (hhom : ∀ a : ℝ, 0 ≤ a → ∀ v, p (a • v) = a * p v)
    (hadd : ∀ v w, p (v + w) ≤ p v + p w) (d : E) :
    ∃ l : E →ₗ[ℝ] ℝ, (∀ v, l v ≤ p v) ∧ l d = p d := by
  by_cases hd : d = 0
  · obtain ⟨l, _, hl⟩ := exists_extension_of_le_sublinear
      (⟨⊥, 0⟩ : E →ₗ.[ℝ] ℝ) p (fun a ha => hhom a ha.le) hadd (by
        intro v
        have hv : (v : E) = 0 := v.property
        simp [hv, hzero])
    exact ⟨l, hl, by simp [hd, hzero]⟩
  · let S := Submodule.span ℝ ({d} : Set E)
    let c : S →ₗ[ℝ] ℝ := (LinearEquiv.coord ℝ E d hd).toLinearMap
    let l₀ : S →ₗ[ℝ] ℝ := (p d) • c
    have hdom : ∀ v : S, l₀ v ≤ p (v : E) := by
      intro v
      have hv : c v • d = (v : E) := LinearEquiv.coord_apply_smul ℝ E d hd v
      change p d * c v ≤ p (v : E)
      rw [← hv]
      by_cases ha : 0 ≤ c v
      · rw [hhom _ ha]
        exact le_of_eq (mul_comm _ _)
      · have ha' : 0 ≤ -c v := le_of_lt (neg_pos.mpr (lt_of_not_ge ha))
        have hn := hadd d (-d)
        rw [add_neg_cancel, hzero] at hn
        have hv' : c v • d = (-c v) • (-d) := by simp
        rw [hv', hhom _ ha']
        nlinarith
    obtain ⟨l, hl, hle⟩ := exists_extension_of_le_sublinear (⟨S, l₀⟩ : E →ₗ.[ℝ] ℝ)
      p (fun a ha => hhom a ha.le) hadd hdom
    refine ⟨l, hle, ?_⟩
    have h := hl (⟨d, Submodule.mem_span_singleton_self d⟩ : S)
    change l d = p d * (LinearEquiv.coord ℝ E d hd) ⟨d, _⟩ at h
    rw [LinearEquiv.coord_self, mul_one] at h
    exact h

/-- The two-sided norm bound makes every dominated algebraic functional
continuous; no completeness hypothesis is needed. -/
lemma exists_continuous_linear_le_sublinear_eq {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : E → ℝ) (hzero : p 0 = 0)
    (hhom : ∀ a : ℝ, 0 ≤ a → ∀ v, p (a • v) = a * p v)
    (hadd : ∀ v w, p (v + w) ≤ p v + p w)
    (K : ℝ) (hbound : ∀ v, |p v| ≤ K * ‖v‖) (d : E) :
    ∃ l : E →L[ℝ] ℝ, (∀ v, l v ≤ p v) ∧ l d = p d := by
  obtain ⟨l, hle, heq⟩ := exists_linear_le_sublinear_eq p hzero hhom hadd d
  have hlbound : ∀ v, ‖l v‖ ≤ K * ‖v‖ := by
    intro v
    rw [Real.norm_eq_abs, abs_le]
    have hu := (hle v).trans (le_abs_self (p v) |>.trans (hbound v))
    have hn := (hle (-v)).trans (le_abs_self (p (-v)) |>.trans (hbound (-v)))
    rw [map_neg, norm_neg] at hn
    exact ⟨by linarith, hu⟩
  exact ⟨l.mkContinuous K hlbound, hle, heq⟩

lemma directionalDerivative_max_of_localLipschitz {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → WithTop ℝ} (hp : Proper f) (hc : IsConvex f)
    {x : E} {U : Set E} {K : NNReal} (hU : U ∈ 𝓝 x)
    (hfin : ∀ v ∈ U, f v < ⊤)
    (hLip : LipschitzOnWith K (fun v => (f v).untopD 0) U) (d : E) :
    ∃ y ∈ subdifferential f x,
      directionalDerivative f x d = (y d : EReal) ∧
      ∀ z ∈ subdifferential f x, z d ≤ y d := by
  have h := directionalDerivative_of_localLipschitz f hp hc x U K hU hfin hLip
  obtain ⟨y, hy, hyd⟩ := exists_continuous_linear_le_sublinear_eq
    (realDirectionalDerivative f x) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    (K : ℝ) h.2.2.2.2.2 d
  have hchar : subdifferential f x =
      {y | ∀ v : E, (y v : EReal) ≤ directionalDerivative f x v} :=
    subdifferential_eq_directional_le f hp hc x (hfin x (mem_of_mem_nhds hU))
  have hfinite : ∀ v, directionalDerivative f x v = (realDirectionalDerivative f x v : EReal) := h.1
  have hymem : y ∈ subdifferential f x := by
    rw [hchar]
    intro v
    rw [hfinite v]
    exact EReal.coe_le_coe_iff.mpr (hy v)
  refine ⟨y, hymem, ?_, ?_⟩
  · rw [hfinite d, hyd]
  · intro z hz
    rw [hchar] at hz
    have hz' := hz d
    rw [hfinite d] at hz'
    rw [hyd]
    exact EReal.coe_le_coe_iff.mp hz'

theorem directionalDerivative_max : Specs.directionalDerivative_max.{u} := by
  intro E _ _ f hp hc x hnear d
  have h := directionalDerivative_continuous_sublinear f hp hc x hnear
  obtain ⟨U, hU, K, hfin, hLip, _⟩ := h.2.2.2.2.2
  exact directionalDerivative_max_of_localLipschitz hp hc hU hfin hLip d

theorem subdifferential_nonempty : Specs.subdifferential_nonempty.{u} := by
  intro E _ _ f hp hc x hnear
  obtain ⟨y, hy, _⟩ := directionalDerivative_max f hp hc x hnear 0
  exact ⟨y, hy⟩

/-- Pull back to the direction space at a relative-interior point, construct
support there, and extend it to the ambient continuous dual. -/
theorem subdifferential_nonempty_relativeInterior :
    Specs.subdifferential_nonempty_relativeInterior.{u} := by
  intro E _ _ _ f hp hc x hx
  obtain ⟨aA, haA, U, hU, K, hfin, hLip⟩ :=
    localLipschitz_relativeInterior f hp hc x hx
  let A := affineSpan ℝ (Specs.effectiveDomain f)
  let : Nonempty A := ⟨aA⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ aA
  let p : A.direction →ᵃ[ℝ] E := A.subtype.comp e.toAffineEquiv.toAffineMap
  let g : A.direction → WithTop ℝ := fun v => f (p v)
  have hp_apply (v : A.direction) : p v = (v : E) + x := by
    change (v : E) + (aA : E) = (v : E) + x
    rw [haA]
  have hp_zero : p 0 = x := by simp [hp_apply]
  have he_zero : e 0 = aA := by simp [e]
  let W : Set A.direction := e ⁻¹' U
  have hW : W ∈ 𝓝 (0 : A.direction) := by
    have hU' : U ∈ 𝓝 (e 0) := by rw [he_zero]; exact hU
    exact e.continuous.continuousAt.preimage_mem_nhds hU'
  have hWfin : ∀ v ∈ W, g v < ⊤ := fun v hv => hfin (e v) hv
  have hWlip : LipschitzOnWith K (fun v => (g v).untopD 0) W := by
    have h := hLip.comp e.lipschitzWith.lipschitzOnWith
      (show MapsTo e W U from fun _ hv => hv)
    simpa only [mul_one, Function.comp_def, g, p, AffineMap.comp_apply,
      AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv,
      AffineSubspace.subtype_apply] using h
  have hgproper : Proper g := ⟨0, hWfin 0 (mem_of_mem_nhds hW)⟩
  have hgconvex : IsConvex g := by
    apply (convex_iff_twoPoint g).mpr
    intro v w r s hv hw a b ha hb hab
    change f (p (a • v + b • w)) ≤ _
    rw [Convex.combo_affine_apply hab]
    exact convex_upper_bound hc hv.le hw.le ha hb hab
  obtain ⟨l, hl, _⟩ := directionalDerivative_max_of_localLipschitz
    hgproper hgconvex hW hWfin hWlip 0
  obtain ⟨y, hy⟩ := StrongDual.exists_extension A.direction l
  refine ⟨y, ?_⟩
  have hxfin : f x < ⊤ := by
    simpa only [g, hp_zero] using hWfin 0 (mem_of_mem_nhds hW)
  have hgzero : g 0 = (((f x).untopD 0 : ℝ) : WithTop ℝ) := by
    simpa only [g, hp_zero] using finite_value hxfin
  have hlsupport := (mem_subdifferential_iff hgzero l).mp hl
  apply (mem_subdifferential_iff (finite_value hxfin) y).mpr
  intro z
  by_cases hz : f z = ⊤
  · simp [hz]
  · have hzdom : z ∈ Specs.effectiveDomain f := lt_top_iff_ne_top.mpr hz
    let zA : A := ⟨z, subset_affineSpan ℝ _ hzdom⟩
    let v : A.direction := zA -ᵥ aA
    have hv : (v : E) = z - x := by
      change (zA : E) - (aA : E) = z - x
      rw [haA]
    have hpv : p v = z := by rw [hp_apply, hv]; abel
    have h := hlsupport v
    simp only [sub_zero] at h
    have hext : y (z - x) = l v := by rw [← hv]; exact hy v
    rw [hext]
    simpa only [g, hpv] using h

/-- All clauses of the source proposition, with their distinct hypotheses. -/
theorem directional_support : Specs.directional_support.{u} :=
  ⟨directionalQuotient_eq, directionalQuotient_monotone, directionalQuotient_tendsto,
    directionalDerivative_continuous_sublinear, subdifferential_eq_directional_le,
    directionalDerivative_max, subdifferential_nonempty,
    subdifferential_nonempty_relativeInterior⟩

end VariationalNotes.ConvexAnalysis
