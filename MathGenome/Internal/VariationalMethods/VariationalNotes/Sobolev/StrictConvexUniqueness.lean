import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.StrictConvexUniqueness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal
namespace VariationalNotes.Sobolev

/-- A finite signed energy with integrable negative part has an integrable
integrand. This does not assert integrability at other admissible maps. -/
theorem integrable_of_extendedIntegral_finite {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {f : S → ℝ} (hf : AEMeasurable f μ)
    (hn : NegativePartIntegrable μ f) (ht : extendedIntegral μ f ≠ ⊤) :
    Integrable f μ := by
  have hp : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    mt (extendedIntegral_eq_top_iff hf hn).mpr ht
  have hi : Integrable (fun x => max (f x) 0) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hf.max aemeasurable_const).aestronglyMeasurable
      (Eventually.of_forall (fun x => le_max_right (f x) 0))).mp
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)] using hp
  apply integrable_of_le_of_le hf.aestronglyMeasurable
    (Eventually.of_forall (fun x => ?_))
    (Eventually.of_forall (fun x => le_max_left (f x) 0)) hn.neg hi
  exact neg_le.mpr (le_max_left (-f x) 0)

/-- Equality in the midpoint energy comparison forces equality of the
integrands a.e. The lower bound is supplied by the midpoint's negative part. -/
theorem midpoint_integrand_eq {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {f g h : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : AEMeasurable h μ) (hn : NegativePartIntegrable μ h)
    (hle : ∀ᵐ x ∂μ, h x ≤ (1/2 : ℝ) * f x + (1/2 : ℝ) * g x)
    (heq : (∫ x, f x ∂μ) = ∫ x, g x ∂μ)
    (hmin : extendedIntegral μ f ≤ extendedIntegral μ h) :
    h =ᵐ[μ] (fun x => (1/2 : ℝ) * f x + (1/2 : ℝ) * g x) := by
  have hm := (hf.const_mul (1/2 : ℝ)).add (hg.const_mul (1/2 : ℝ))
  have hi : Integrable h μ :=
    integrable_of_le_of_le hh.aestronglyMeasurable
      (Eventually.of_forall (fun x => neg_le.mpr (le_max_left (-h x) 0))) hle hn.neg hm
  apply (integral_eq_iff_of_ae_le hi hm hle).mp
  have hlow : (∫ x, f x ∂μ) ≤ ∫ x, h x ∂μ := by
    simpa only [extendedIntegral_eq_integral hf, extendedIntegral_eq_integral hi,
      EReal.coe_le_coe_iff] using hmin
  have hup := integral_mono_ae hi hm hle
  simp only [Pi.add_apply] at hup ⊢
  rw [integral_add (hf.const_mul _) (hg.const_mul _), integral_const_mul,
    integral_const_mul, ← heq] at hup ⊢
  linarith

/-- The measure-theoretic core: two minimizers have the same field a.e.
The field can be the value/gradient pair or just the weak gradient. -/
theorem minimizers_fields_ae_eq {S V E : Type*} [MeasurableSpace S]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup E] [Module ℝ E]
    {μ : Measure S} {C : Set V} {T : V → S → E} {F : S → E → ℝ}
    (hC : ∀ u ∈ C, ∀ v ∈ C, (1/2 : ℝ) • u + (1/2 : ℝ) • v ∈ C)
    (hT : ∀ u v, T ((1/2 : ℝ) • u + (1/2 : ℝ) • v) =ᵐ[μ]
      (fun x => (1/2 : ℝ) • T u x + (1/2 : ℝ) • T v x))
    (hm : ∀ u ∈ C, AEMeasurable (fun x => F x (T u x)) μ)
    (hn : ∀ u ∈ C, NegativePartIntegrable μ (fun x => F x (T u x)))
    (hs : ∀ᵐ x ∂μ, StrictConvexOn ℝ univ (F x))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) {c : ℝ}
    (hfinite : extendedIntegral μ (fun x => F x (T u x)) = (c : EReal))
    (humin : ∀ w ∈ C, extendedIntegral μ (fun x => F x (T u x)) ≤
      extendedIntegral μ (fun x => F x (T w x)))
    (hvmin : ∀ w ∈ C, extendedIntegral μ (fun x => F x (T v x)) ≤
      extendedIntegral μ (fun x => F x (T w x))) :
    T u =ᵐ[μ] T v := by
  let w := (1/2 : ℝ) • u + (1/2 : ℝ) • v
  have hw : w ∈ C := hC u hu v hv
  have he : extendedIntegral μ (fun x => F x (T v x)) =
      extendedIntegral μ (fun x => F x (T u x)) := le_antisymm (hvmin u hu) (humin v hv)
  have hfu : Integrable (fun x => F x (T u x)) μ :=
    integrable_of_extendedIntegral_finite (hm u hu) (hn u hu) (by rw [hfinite]; exact EReal.coe_ne_top c)
  have hfv : Integrable (fun x => F x (T v x)) μ :=
    integrable_of_extendedIntegral_finite (hm v hv) (hn v hv)
      (by rw [he, hfinite]; exact EReal.coe_ne_top c)
  have hle : ∀ᵐ x ∂μ, F x (T w x) ≤
      (1/2 : ℝ) * F x (T u x) + (1/2 : ℝ) * F x (T v x) := by
    filter_upwards [hs, hT u v] with x hx ht
    rw [ht]
    exact hx.convexOn.2 (mem_univ _) (mem_univ _) (by norm_num) (by norm_num) (by norm_num)
  have hieq : (∫ x, F x (T u x) ∂μ) = ∫ x, F x (T v x) ∂μ := by
    rw [extendedIntegral_eq_integral hfu, extendedIntegral_eq_integral hfv] at he
    exact EReal.coe_injective he.symm
  have heq := midpoint_integrand_eq hfu hfv (hm w hw) (hn w hw) hle hieq (humin w hw)
  filter_upwards [hs, hT u v, heq] with x hx ht heq
  by_contra hne
  have hlt : F x ((1/2 : ℝ) • T u x + (1/2 : ℝ) • T v x) <
      (1/2 : ℝ) * F x (T u x) + (1/2 : ℝ) * F x (T v x) :=
    hx.2 (mem_univ _) (mem_univ _) hne (by norm_num) (by norm_num) (by norm_num)
  rw [← ht] at hlt
  exact (ne_of_lt hlt) heq

/-- The prescribed affine class is closed under taking midpoints. -/
theorem affineClass_midpoint {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u₀ : W1p Ω m p) {u v : W1p Ω m p}
    (hu : u ∈ affineClass Ω m p u₀) (hv : v ∈ affineClass Ω m p u₀) :
    (1/2 : ℝ) • u + (1/2 : ℝ) • v ∈ affineClass Ω m p u₀ := by
  have hc : Convex ℝ (affineClass Ω m p u₀) := by
    change Convex ℝ ((fun u : W1p Ω m p => u-u₀) ⁻¹' (zeroSubmodule Ω m p : Set _))
    exact (zeroSubmodule Ω m p).convex.affine_preimage
      (AffineMap.id ℝ _ - AffineMap.const ℝ _ u₀)
  exact hc hu hv (by norm_num) (by norm_num) (by norm_num)

/-- Linear maps into Lp preserve midpoint representatives almost everywhere. -/
theorem lp_linear_midpoint_ae {S V E : Type*} [MeasurableSpace S]
    [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure S} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (L : V →ₗ[ℝ] Lp E q μ) (u v : V) :
    (L ((1/2 : ℝ) • u + (1/2 : ℝ) • v) : S → E) =ᵐ[μ]
      (fun x => (1/2 : ℝ) • L u x + (1/2 : ℝ) • L v x) := by
  rw [L.map_add, L.map_smul, L.map_smul]
  filter_upwards [Lp.coeFn_add ((1/2 : ℝ) • L u) ((1/2 : ℝ) • L v),
    Lp.coeFn_smul (1/2 : ℝ) (L u), Lp.coeFn_smul (1/2 : ℝ) (L v)] with x ha hu hv
  exact ha.trans (congrArg₂ (· + ·) hu hv)

/-- Boundedness provides a coordinate strip; Poincaré gives injectivity of
the weak gradient on each prescribed affine class, on arbitrary open sets. -/
theorem affine_gradient_injective {d m : ℕ} (hd : 0 < d)
    (Ω : Opens (Domain d)) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (p : Exponent) (u₀ : W1p Ω m p) {u v : W1p Ω m p}
    (hu : u ∈ affineClass Ω m p u₀) (hv : v ∈ affineClass Ω m p u₀)
    (hgrad : gradient Ω m p u = gradient Ω m p v) : u = v := by
  obtain ⟨R, hR, hbound⟩ := hΩ.exists_pos_norm_lt
  let j : Fin d := ⟨0, hd⟩
  have hstrip : InCoordinateStrip Ω j (-R) R := by
    intro x hx
    have hn : |x j| < R := lt_of_le_of_lt (PiLp.norm_apply_le x j) (hbound x hx)
    exact abs_lt.mp hn
  have hsub : u-v ∈ zeroSubmodule Ω m p := by
    have hh := (zeroSubmodule Ω m p).sub_mem hu hv
    convert hh using 1
    abel
  let z : W1pZero Ω m p := ⟨u-v, hsub⟩
  have hz : z = 0 := zero_of_gradient_eq_zero Ω p j (by linarith) hstrip z
    (by change gradient Ω m p (u-v) = 0; rw [map_sub, hgrad, sub_self])
  exact sub_eq_zero.mp (congrArg Subtype.val hz)

/-- Joint strict convexity gives uniqueness of a finite global minimizer. -/
theorem strict_convex_uniqueness_of_measurable : UniquenessExpected.Joint := by
  intro d m hd hm Ω hΩ p u₀ F hmeas hs hn u hu c hfinite humin v hv hvmin
  let T := fun w : W1p Ω m p => fun x =>
    (value Ω m p w x, gradient Ω m p w x)
  have heq : T u =ᵐ[domainMeasure Ω] T v := by
    refine minimizers_fields_ae_eq (T := T)
      (C := affineClass Ω m p u₀) (F := fun x (y : Vector m × Gradient m d) => F x y.1 y.2)
      (fun u hu v hv => affineClass_midpoint Ω p u₀ hu hv)
      ?_ ?_ (fun w hw => hn w hw) hs hu hv hfinite humin hvmin
    · intro a b
      filter_upwards [lp_linear_midpoint_ae (value Ω m p).toLinearMap a b,
        lp_linear_midpoint_ae (gradient Ω m p).toLinearMap a b] with x hx hy
      exact Prod.ext hx hy
    · intro w hw
      exact hmeas w hw
  apply value_injective Ω p
  apply Lp.ext
  exact heq.mono (fun x hx => congrArg Prod.fst hx)

/-- For state-independent integrands, strict convexity of the gradient
suffices, because the zero-boundary difference has injective gradient. -/
theorem gradient_strict_convex_uniqueness_of_measurable : UniquenessExpected.GradientOnly := by
  intro d m hd hm Ω hΩ p u₀ F hmeas hind hs hn u hu c hfinite humin v hv hvmin
  have hcomp (w : W1p Ω m p) :
      (fun x => F x (value Ω m p w x) (gradient Ω m p w x)) =ᵐ[domainMeasure Ω]
      (fun x => F x 0 (gradient Ω m p w x)) := by
    filter_upwards [hind] with x hx
    exact hx _ _ _
  have he (w : W1p Ω m p) : energy Ω m p F w =
      extendedIntegral (domainMeasure Ω) (fun x => F x 0 (gradient Ω m p w x)) :=
    extendedIntegral_congr_ae (hcomp w)
  have heq : (gradient Ω m p u : Domain d → Gradient m d) =ᵐ[domainMeasure Ω]
      (gradient Ω m p v : Domain d → Gradient m d) := by
    apply minimizers_fields_ae_eq (C := affineClass Ω m p u₀)
      (F := fun x Z => F x 0 Z)
      (fun u hu v hv => affineClass_midpoint Ω p u₀ hu hv)
      (fun a b => lp_linear_midpoint_ae (gradient Ω m p).toLinearMap a b)
      (fun w hw => (hmeas w hw).congr (hcomp w))
      (fun w hw => (negativePartIntegrable_congr_ae (hcomp w)).mp (hn w hw))
      hs hu hv (by rw [← he]; exact hfinite)
      (fun w hw => ?_) (fun w hw => ?_)
    · rw [← he, ← he]
      exact humin w hw
    · rw [← he, ← he]
      exact hvmin w hw
  exact affine_gradient_injective hd Ω hΩ p u₀ hu hv (Lp.ext heq)

/-- The chapter's Carathéodory integrand satisfies the measurable-density
hypothesis by the upstream substitution theorem. -/
theorem strict_convex_uniqueness : UniquenessExpected.JointCaratheodory := by
  intro d m hd hm Ω hΩ p u₀ F hF hs hn
  apply strict_convex_uniqueness_of_measurable hd hm Ω hΩ p u₀ F ?_ hs hn
  intro w hw
  exact (show Caratheodory (domainMeasure Ω)
      (fun x (y : Vector m × Gradient m d) => F x y.1 y.2) from hF).aemeasurable_substitution
    ((Lp.aestronglyMeasurable (value Ω m p w)).aemeasurable.prodMk
      (Lp.aestronglyMeasurable (gradient Ω m p w)).aemeasurable)

/-- Carathéodory specialization of uniqueness for a state-independent energy. -/
theorem gradient_strict_convex_uniqueness : UniquenessExpected.GradientOnlyCaratheodory := by
  intro d m hd hm Ω hΩ p u₀ F hF hind hs hn
  apply gradient_strict_convex_uniqueness_of_measurable hd hm Ω hΩ p u₀ F ?_ hind hs hn
  intro w hw
  exact (show Caratheodory (domainMeasure Ω)
      (fun x (y : Vector m × Gradient m d) => F x y.1 y.2) from hF).aemeasurable_substitution
    ((Lp.aestronglyMeasurable (value Ω m p w)).aemeasurable.prodMk
      (Lp.aestronglyMeasurable (gradient Ω m p w)).aemeasurable)

end VariationalNotes.Sobolev
