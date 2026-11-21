import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanEqualsToral
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootStrings
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealRootSpace
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The Killing trace on the Cartan is the sum over one-dimensional root spaces.
Integral root evaluations on Lie coroots give both the real form and the rational
Gram entries. The rational span is then identified using a basis of roots. -/

open scoped BigOperators TensorProduct

universe u

namespace LieAlgebrasAndRepresentations.RealRootSpace

open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open LieAlgebrasAndRepresentations.RootStrings
open private rootWeight rootWeight_toLinear rootWeight_nonzero
  rootSpace_eq_generalized
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L}

theorem cartan_isMaximalToral (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    [H.IsCartanSubalgebra] : IsMaximalToral H :=
  (isCartan_iff_maximal_toral hss H).mp
    ((isCartan_iff_isCartanSubalgebra H).mpr ‹H.IsCartanSubalgebra›)

private theorem span_dual_of_separating {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (S : Set (Module.Dual K V))
    (hs : ∀ x : V, (∀ a ∈ S, a x = 0) → x = 0) :
    Submodule.span K S = ⊤ := by
  have h : (Submodule.span K S).dualCoannihilator = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply (Submodule.mem_bot K).mpr
    apply hs
    intro a ha
    exact (Submodule.mem_dualCoannihilator x).mp hx a (Submodule.subset_span ha)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K S),
    h, Submodule.dualAnnihilator_bot]

private theorem rootSet_spans (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) :
    Submodule.span ℂ (rootSet H) = ⊤ := by
  apply span_dual_of_separating
  intro x hx
  have hz : LieAlgebra.ad ℂ L (x : L) = 0 := by
    ext y
    have hy : y ∈ ⨆ a : Module.Dual ℂ H, rootSpace H a := by
      rw [iSup_rootSpace_eq_top H hH.1]
      trivial
    refine Submodule.iSup_induction (rootSpace H)
      (motive := fun z => (LieAlgebra.ad ℂ L (x : L)) z = 0) hy (fun a z hz => ?_) ?_ ?_
    · change ⁅(x : L), z⁆ = 0
      rw [(mem_rootSpace H a z).mp hz x]
      by_cases h : a ∈ rootSet H
      · rw [hx a h, zero_smul]
      · by_cases ha : a = 0
        · simp [ha]
        · rw [rootSpace_eq_bot_of_not_mem H a ha h, Submodule.mem_bot] at hz
          simp [hz]
    · exact map_zero _
    · intro y z hy hz
      rw [map_add, hy, hz, add_zero]
  have h0 := ((semisimple_iff_killingForm_nondegenerate ℂ L).mp hss).1 (x : L)
  apply Subtype.ext
  exact h0 fun y => by
    change LinearMap.trace ℂ L (LieAlgebra.ad ℂ L (x : L) * LieAlgebra.ad ℂ L y) = 0
    rw [hz, zero_mul, map_zero]

private theorem rootSet_separates (hs : Submodule.span ℂ (rootSet H) = ⊤) (x : H)
    (hx : ∀ a ∈ rootSet H, a x = 0) : x = 0 := by
  apply Module.eval_apply_injective ℂ
  rw [map_zero]
  apply LinearMap.ext_on hs
  intro a ha
  exact hx a ha

private theorem rootIndex_mem [H.IsCartanSubalgebra] (hH : IsMaximalToral H)
    (a : H.root) : (a.1 : Module.Dual ℂ H) ∈ rootSet H := by
  refine ⟨?_, ?_⟩
  · intro h
    apply LieSubalgebra.isNonZero_coe_root a
    exact funext fun x => congrArg (fun f : Module.Dual ℂ H => f x) h
  · intro h
    apply a.1.genWeightSpace_ne_bot
    apply LieSubmodule.toSubmodule_injective
    rw [rootSpace_eq_generalized H hH]
    exact h

private theorem exists_rootIndex [H.IsCartanSubalgebra] (hH : IsMaximalToral H)
    (a : Module.Dual ℂ H) (ha : a ∈ rootSet H) :
    ∃ i : H.root, (i.1 : Module.Dual ℂ H) = a := by
  classical
  exact ⟨⟨rootWeight H hH a ha, by
    simpa [LieSubalgebra.root] using rootWeight_nonzero H hH a ha⟩,
    rootWeight_toLinear H hH a ha⟩

private theorem killing_sum [H.IsCartanSubalgebra] (hss : IsSemisimple ℂ L) (x y : H) :
    killing H x y = ∑ a : H.root, (a.1 : Module.Dual ℂ H) x * (a.1 : Module.Dual ℂ H) y := by
  classical
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  change ((LieModule.traceForm ℂ L L).restrict H.toSubmodule) x y = _
  rw [LieAlgebra.IsKilling.restrict_killingForm_eq_sum,
    LinearMap.BilinForm.sum_apply, ← Finset.sum_coe_sort]
  rfl

private theorem coroot_mem_realCartan {a : Module.Dual ℂ H} (ha : a ∈ rootSet H) :
    killingCoroot H a ∈ realCartan H :=
  Submodule.subset_span ⟨a, ha, rfl⟩

private theorem root_eval_real (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (a : Module.Dual ℂ H) (ha : a ∈ rootSet H) (x : realCartan H) :
    a x = (rootRestriction H a x : ℂ) := by
  have h : (a x).im = 0 := by
    refine Submodule.span_induction
      (p := fun y _ => (a y).im = 0) ?_ ?_ ?_ ?_ x.property
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨n, hn, _⟩ := coroot_pairing_integral hss H hH b a hb ha
      rw [hn, Complex.intCast_im]
    · simp
    · intro y z _ _ hy hz
      rw [map_add, Complex.add_im, hy, hz, add_zero]
    · intro r y _ hy
      change (a ((r : ℂ) • y)).im = 0
      rw [map_smul, smul_eq_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hy]
      ring
  exact (Complex.ext (by rfl) (by simpa using h.symm)).symm

private theorem coroots_span_complex (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hs : Submodule.span ℂ (rootSet H) = ⊤) :
    Submodule.span ℂ (killingCoroot H '' rootSet H) = ⊤ := by
  have hsurj : Function.Surjective (rootDualMap H) := by
    intro x
    let B := killing H
    refine ⟨B x, ?_⟩
    exact (tAlpha_unique hss H hH (B x) x (fun _ => rfl)).symm
  have hmap := Submodule.map_span (rootDualMap H) (rootSet H)
  rw [hs, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj] at hmap
  apply top_unique
  rw [hmap]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, rfl⟩
  have hn := rootForm_self_ne_zero hss H hH a ha
  have hc : (2 / rootForm H a a) ≠ 0 := div_ne_zero (by norm_num) hn
  have hm := (Submodule.span ℂ (killingCoroot H '' rootSet H)).smul_mem
    (2 / rootForm H a a)⁻¹ (Submodule.subset_span (R := ℂ)
      (s := killingCoroot H '' rootSet H) ⟨a, ha, rfl⟩)
  have hm' : tAlpha H a ∈ Submodule.span ℂ (killingCoroot H '' rootSet H) := by
    simpa only [killingCoroot_eq, smul_smul, inv_mul_cancel₀ hc, one_smul] using hm
  exact hm'

private theorem cartanSum_bijective (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hs : Submodule.span ℂ (rootSet H) = ⊤) : Function.Bijective (cartanSum H) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    rintro ⟨x, y⟩ h
    change (x : H) + Complex.I • (y : H) = 0 at h
    have he (a : Module.Dual ℂ H) (ha : a ∈ rootSet H) :
        rootRestriction H a x = 0 ∧ rootRestriction H a y = 0 := by
      have hh := congrArg (fun z => a z) h
      rw [map_add, map_smul, smul_eq_mul, map_zero, root_eval_real hss hH a ha x,
        root_eval_real hss hH a ha y] at hh
      constructor
      · simpa [Complex.add_re, Complex.mul_re] using congrArg Complex.re hh
      · simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hh
    have hx : x = 0 := Subtype.ext (rootSet_separates hs _ fun a ha => by
      rw [root_eval_real hss hH a ha x, (he a ha).1, Complex.ofReal_zero])
    have hy : y = 0 := Subtype.ext (rootSet_separates hs _ fun a ha => by
      rw [root_eval_real hss hH a ha y, (he a ha).2, Complex.ofReal_zero])
    exact (Submodule.mem_bot ℝ).mpr (Prod.ext hx hy)
  · intro z
    have hz : z ∈ Submodule.span ℂ (killingCoroot H '' rootSet H) := by
      rw [coroots_span_complex hss hH hs]
      trivial
    change z ∈ (cartanSum H).range
    refine Submodule.span_induction (p := fun w _ => w ∈ (cartanSum H).range)
      ?_ (Submodule.zero_mem _) (fun x y _ _ => Submodule.add_mem _) ?_ hz
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨(⟨_, coroot_mem_realCartan ha⟩, 0), by simp [cartanSum]⟩
    · intro c w _ hw
      obtain ⟨⟨x, y⟩, rfl⟩ := hw
      refine ⟨(c.re • x - c.im • y, c.im • x + c.re • y), ?_⟩
      change ((c.re : ℂ) • (x : H) - (c.im : ℂ) • (y : H)) +
        Complex.I • ((c.im : ℂ) • (x : H) + (c.re : ℂ) • (y : H)) =
        c • ((x : H) + Complex.I • (y : H))
      conv_rhs => rw [← c.re_add_im]
      have hi : (↑c.im * Complex.I) * Complex.I = -(↑c.im : ℂ) := by
        rw [mul_assoc, Complex.I_mul_I, mul_neg, mul_one]
      have hcoef : ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * Complex.I =
          -(c.im : ℂ) + Complex.I * (c.re : ℂ) := by
        rw [add_mul, hi]
        ring
      rw [smul_add ((c.re : ℂ) + (c.im : ℂ) * Complex.I), smul_smul, hcoef]
      simp only [sub_eq_add_neg, add_smul, smul_add, smul_smul, neg_smul,
        mul_comm (↑c.im : ℂ) Complex.I]
      abel

section RealPairing

variable [H.IsCartanSubalgebra]
variable (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
include hss hH

private theorem realKilling_sum (x y : realCartan H) :
    realKilling H x y = ∑ a : H.root,
      rootRestriction H a.1 x * rootRestriction H a.1 y := by
  classical
  change (killing H x y).re = _
  rw [killing_sum hss]
  change Complex.reLm (∑ a : H.root, (a.1 : Module.Dual ℂ H) x * (a.1 : Module.Dual ℂ H) y) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change ((a.1 : Module.Dual ℂ H) x * (a.1 : Module.Dual ℂ H) y).re = _
  rw [root_eval_real hss hH _ (rootIndex_mem hH a) x,
    root_eval_real hss hH _ (rootIndex_mem hH a) y, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem killing_restrict_real (x y : realCartan H) :
    killing H x y = (realKilling H x y : ℂ) := by
  classical
  rw [killing_sum hss, realKilling_sum hss hH]
  push_cast
  exact Finset.sum_congr rfl fun a _ => by
    rw [root_eval_real hss hH _ (rootIndex_mem hH a) x,
      root_eval_real hss hH _ (rootIndex_mem hH a) y]

private theorem realKilling_positive (hs : Submodule.span ℂ (rootSet H) = ⊤) :
    Positive H := by
  classical
  intro x hx
  have hex : ∃ a ∈ rootSet H, a x ≠ 0 := by
    by_contra! h
    exact hx (Subtype.ext (rootSet_separates hs x h))
  obtain ⟨a, ha, hax⟩ := hex
  obtain ⟨i, hi⟩ := exists_rootIndex hH a ha
  rw [realKilling_sum hss hH]
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg _
  · refine ⟨i, Finset.mem_univ _, mul_self_pos.mpr ?_⟩
    rw [hi]
    intro hz
    apply hax
    rw [root_eval_real hss hH a ha x, hz, Complex.ofReal_zero]

private theorem riesz_pairing (hp : Positive H) (x : E H) (u : realCartan H) :
    killing H (riesz H hp x) u = (x u : ℂ) := by
  rw [killing_restrict_real hss hH]
  exact congrArg Complex.ofReal (LinearMap.BilinForm.apply_toDual_symm_apply x u)

private theorem extension_formula (hp : Positive H) (x : E H) (u v : realCartan H) :
    extension H hp x ((u : H) + Complex.I • (v : H)) =
      (x u : ℂ) + Complex.I * (x v : ℂ) := by
  change killing H (riesz H hp x) ((u : H) + Complex.I • (v : H)) = _
  rw [map_add, map_smul, smul_eq_mul, riesz_pairing hss hH, riesz_pairing hss hH]

private theorem extension_root (hp : Positive H) (hs : Function.Surjective (cartanSum H))
    (a : Module.Dual ℂ H) (ha : a ∈ rootSet H) :
    extension H hp (rootRestriction H a) = a := by
  ext z
  obtain ⟨⟨u, v⟩, rfl⟩ := hs z
  change extension H hp (rootRestriction H a) ((u : H) + Complex.I • (v : H)) = _
  rw [extension_formula hss hH]
  change _ = a ((u : H) + Complex.I • (v : H))
  rw [map_add, map_smul, smul_eq_mul, ← root_eval_real hss hH a ha u,
    ← root_eval_real hss hH a ha v]

omit [H.IsCartanSubalgebra] in
private theorem rootRestriction_spans (hs : Submodule.span ℂ (rootSet H) = ⊤) :
    Submodule.span ℝ (realRoots H) = ⊤ := by
  apply span_dual_of_separating
  intro x hx
  apply Subtype.ext
  apply rootSet_separates hs
  intro a ha
  rw [root_eval_real hss hH a ha x, hx _ ⟨a, ha, rfl⟩, Complex.ofReal_zero]

private theorem root_form_agrees (hp : Positive H) (hs : Function.Surjective (cartanSum H))
    (a : Module.Dual ℂ H) (ha : a ∈ rootSet H)
    (b : Module.Dual ℂ H) (hb : b ∈ rootSet H) :
    ((dualCore H hp).inner (rootRestriction H a) (rootRestriction H b) : ℂ) =
      rootForm H a b := by
  have ht (c : Module.Dual ℂ H) (hc : c ∈ rootSet H) :
      (riesz H hp (rootRestriction H c) : H) = tAlpha H c := by
    apply tAlpha_unique hss H hH
    exact LinearMap.congr_fun (extension_root hss hH hp hs c hc)
  change (realKilling H (riesz H hp (rootRestriction H a))
    (riesz H hp (rootRestriction H b)) : ℂ) = _
  rw [← killing_restrict_real hss hH, rootForm_apply]
  change killing H (riesz H hp (rootRestriction H a)) (riesz H hp (rootRestriction H b)) =
    killing H (tAlpha H a) (tAlpha H b)
  rw [ht a ha, ht b hb]

private theorem riesz_coroot (hp : Positive H) (hs : Function.Surjective (cartanSum H))
    (a : Module.Dual ℂ H) (ha : a ∈ rootSet H) :
    letI := (dualCore H hp).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (dualCore H hp).toCore
    (riesz H hp (LieAlgebrasAndRepresentations.coroot (rootRestriction H a)) : H) =
      killingCoroot H a := by
  have ht : (riesz H hp (rootRestriction H a) : H) = tAlpha H a := by
    apply tAlpha_unique hss H hH
    exact LinearMap.congr_fun (extension_root hss hH hp hs a ha)
  change (riesz H hp ((2 / (dualCore H hp).inner (rootRestriction H a)
    (rootRestriction H a)) • rootRestriction H a) : H) = _
  rw [map_smul]
  change (↑(2 / (dualCore H hp).inner (rootRestriction H a)
    (rootRestriction H a)) : ℂ) • (riesz H hp (rootRestriction H a) : H) = _
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, root_form_agrees hss hH hp hs a ha a ha, ht]
  rfl

private theorem coroot_evaluation (hp : Positive H) (hs : Function.Surjective (cartanSum H))
    (x : E H) (a : Module.Dual ℂ H) (ha : a ∈ rootSet H) :
    letI := (dualCore H hp).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (dualCore H hp).toCore
    extension H hp x (killingCoroot H a) =
      (inner ℝ x (LieAlgebrasAndRepresentations.coroot (rootRestriction H a)) : ℂ) := by
  let _ := (dualCore H hp).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (dualCore H hp).toCore
  rw [← riesz_coroot hss hH hp hs a ha]
  exact killing_restrict_real hss hH _ _

private theorem root_form_rational (hp : Positive H) (hs : Function.Surjective (cartanSum H))
    (a : Module.Dual ℂ H) (ha : a ∈ rootSet H)
    (b : Module.Dual ℂ H) (hb : b ∈ rootSet H) :
    ∃ r : ℚ, (dualCore H hp).inner (rootRestriction H a) (rootRestriction H b) = (r : ℝ) := by
  classical
  have hz (i : H.root) : ∃ n : ℤ, (i.1 : Module.Dual ℂ H) (killingCoroot H b) = (n : ℂ) := by
    obtain ⟨n, hn, _⟩ := coroot_pairing_integral hss H hH b _ hb (rootIndex_mem hH i)
    exact ⟨n, hn⟩
  choose n hn using hz
  have hB : killing H (killingCoroot H b) (killingCoroot H b) =
      ((∑ i, n i * n i : ℤ) : ℂ) := by
    rw [killing_sum hss]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [hn]
  have hbn := rootForm_self_ne_zero hss H hH b hb
  have hlength : ((∑ i, n i * n i : ℤ) : ℂ) * rootForm H b b = 4 := by
    rw [← hB, killingCoroot_eq]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have he : killing H (tAlpha H b) (tAlpha H b) = rootForm H b b :=
      (rootForm_apply H b b).symm
    rw [he]
    field_simp
    ring
  have hsum : ((∑ i, n i * n i : ℤ) : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hlength
    norm_num at hlength
  obtain ⟨m, _, hm⟩ := coroot_pairing_integral hss H hH b a hb ha
  refine ⟨(m : ℚ) * (4 / (∑ i, n i * n i : ℤ)) / 2, ?_⟩
  apply Complex.ofReal_injective
  rw [root_form_agrees hss hH hp hs a ha b hb]
  push_cast
  have he : rootForm H b b = 4 / ((∑ i, n i * n i : ℤ) : ℂ) := by
    apply (eq_div_iff hsum).mpr
    rw [mul_comm]
    exact hlength
  push_cast at he
  rw [← he, ← hm]
  field_simp

end RealPairing

private theorem complex_extension_bijective {U W : Type*} [AddCommGroup U]
    [Module ℝ U] [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
    (f : U →ₗ[ℝ] W)
    (hf : Function.Bijective (fun p : U × U => f p.1 + Complex.I • f p.2)) :
    Function.Bijective (extendScalars (S := ℂ) f) := by
  let e : ℂ ⊗[ℝ] U ≃ₗ[ℝ] U × U :=
    TensorProduct.equivFinsuppOfBasisLeft Complex.basisOneI ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℝ U (Fin 2) ≪≫ₗ LinearEquiv.finTwoArrow ℝ U
  let g : U × U →ₗ[ℝ] W :=
    f.coprod (((Complex.I • (LinearMap.id : W →ₗ[ℂ] W)).restrictScalars ℝ).comp f)
  have he : ∀ c : ℂ, ∀ x : U, e (c ⊗ₜ x) = (c.re • x, c.im • x) := by
    intro c x
    apply Prod.ext
    · change (TensorProduct.equivFinsuppOfBasisLeft Complex.basisOneI (c ⊗ₜ x)) 0 = _
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      rfl
    · change (TensorProduct.equivFinsuppOfBasisLeft Complex.basisOneI (c ⊗ₜ x)) 1 = _
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      rfl
  have h : (extendScalars (S := ℂ) f).restrictScalars ℝ = g.comp e.toLinearMap := by
    apply TensorProduct.ext'
    intro c x
    change extendScalars f (c ⊗ₜ x) = g (e (c ⊗ₜ x))
    rw [extendScalars_tmul, he]
    change c • f x = f (c.re • x) + Complex.I • f (c.im • x)
    rw [map_smul, map_smul]
    conv_lhs => rw [← c.re_add_im]
    rw [add_smul, mul_comm (↑c.im : ℂ) Complex.I, mul_smul]
    simp only [← Complex.coe_algebraMap, IsScalarTower.algebraMap_smul]
  change Function.Bijective ((extendScalars (S := ℂ) f).restrictScalars ℝ)
  rw [h]
  exact hf.comp e.bijective

private theorem dualComplexification_bijective (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hp : Positive H) (hs : Function.Bijective (cartanSum H)) :
    Function.Bijective (dualComplexification H hp) := by
  apply complex_extension_bijective
  let e := (killing H).toDual (killingForm_restrict_toral_nondegenerate hss H hH)
  have h (p : E H × E H) :
      extension H hp p.1 + Complex.I • extension H hp p.2 =
        e (cartanSum H ((riesz H hp).prodCongr (riesz H hp) p)) := by
    change killing H (riesz H hp p.1) + Complex.I • killing H (riesz H hp p.2) =
      killing H ((riesz H hp p.1 : H) + Complex.I • (riesz H hp p.2 : H))
    rw [map_add, map_smul]
  have he := e.bijective.comp (hs.comp ((riesz H hp).prodCongr (riesz H hp)).bijective)
  convert he using 1
  funext p
  exact h p

private theorem realRoots_system [H.IsCartanSubalgebra] (hss : IsSemisimple ℂ L)
    (hH : IsMaximalToral H) (hp : Positive H)
    (hs : Function.Surjective (cartanSum H))
    (hspan : Submodule.span ℂ (rootSet H) = ⊤) :
    letI := (dualCore H hp).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (dualCore H hp).toCore
    IsRootSystem (realRoots H) := by
  let _ := (dualCore H hp).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (dualCore H hp).toCore
  have hleft (x : E H) : rootRestriction H (extension H hp x) = x := by
    ext u
    change (killing H (riesz H hp x) u).re = _
    rw [riesz_pairing hss hH, Complex.ofReal_re]
  have hj : Function.Injective (extension H hp) :=
    Function.LeftInverse.injective hleft
  have hpair (a b : Module.Dual ℂ H) (ha : a ∈ rootSet H) (hb : b ∈ rootSet H) :
      ((2 * inner ℝ (rootRestriction H b) (rootRestriction H a) /
        inner ℝ (rootRestriction H a) (rootRestriction H a) : ℝ) : ℂ) =
        b (killingCoroot H a) := by
    change ((2 * (dualCore H hp).inner (rootRestriction H b) (rootRestriction H a) /
        (dualCore H hp).inner (rootRestriction H a) (rootRestriction H a) : ℝ) : ℂ) = _
    push_cast
    rw [root_form_agrees hss hH hp hs b hb a ha, root_form_agrees hss hH hp hs a ha a ha,
      killingCoroot_pairing hss H hH]
  refine ⟨⟨(rootSet_finite H hH.1).image _, ?_, ?_, ?_, ?_⟩,
    rootRestriction_spans hss hH hspan⟩
  · rintro _ ⟨a, ha, rfl⟩ hn
    apply ha.1
    rw [← extension_root hss hH hp hs a ha, hn, map_zero]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨RootStrings.rootReflection H a b, reflection_mem_rootSet hss H hH a b ha hb, hj ?_⟩
    rw [extension_root hss hH hp hs _ (reflection_mem_rootSet hss H hH a b ha hb),
      LieAlgebrasAndRepresentations.rootReflection, map_sub, map_smul, extension_root hss hH hp hs a ha,
      extension_root hss hH hp hs b hb]
    change RootStrings.rootReflection H a b = b - (↑(2 * inner ℝ (rootRestriction H b)
      (rootRestriction H a) / inner ℝ (rootRestriction H a) (rootRestriction H a)) : ℂ) • a
    rw [hpair a b ha hb]
    rfl
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨n, hn, _⟩ := coroot_pairing_integral hss H hH a b ha hb
    refine ⟨n, Complex.ofReal_injective ?_⟩
    rw [hpair a b ha hb, hn, Complex.ofReal_intCast]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
    have he := congrArg (extension H hp) hr
    rw [map_smul, extension_root hss hH hp hs a ha, extension_root hss hH hp hs b hb] at he
    change (r : ℂ) • a = b at he
    rcases proportional_root_eq hss H hH a b ha hb (r : ℂ) he.symm with h | h
    · exact Or.inl (congrArg (rootRestriction H) h)
    · right
      apply hj
      rw [map_neg, extension_root hss hH hp hs a ha, extension_root hss hH hp hs b hb, h]

/-- A spanning set with rational Gram entries for a nondegenerate real form
has the same real and rational basis. -/
private theorem rational_extension_bijective {V : Type*} [AddCommGroup V]
    [Module ℝ V] [Module ℚ V] [IsScalarTower ℚ ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (R : Set V) (hfinite : R.Finite) (hspan : Submodule.span ℝ R = ⊤)
    (hrat : ∀ x ∈ R, ∀ y ∈ R, ∃ r : ℚ, B x y = (r : ℝ)) :
    Function.Bijective (extendScalars (R := ℚ) (S := ℝ) (N := V)
      (Submodule.span ℚ R).subtype) := by
  classical
  obtain ⟨T, hTR, hTspan, hTind⟩ := exists_linearIndependent ℝ R
  let : Fintype T := (hfinite.subset hTR).fintype
  have hT : Submodule.span ℝ (Set.range (Subtype.val : T → V)) = ⊤ := by
    simpa only [Subtype.range_coe, hTspan] using hspan
  let b : Module.Basis T ℝ V := Module.Basis.mk hTind hT.ge
  have hb (i : T) : b i ∈ R := by
    rw [Module.Basis.mk_apply]
    exact hTR i.property
  have hG (i j : T) : ∃ r : ℚ, B (b i) (b j) = (r : ℝ) := hrat _ (hb i) _ (hb j)
  choose G hG using hG
  let A := Matrix.mulVecLin (R := ℚ) (G : Matrix T T ℚ)
  have pairing_sum (c : T → ℝ) (i : T) :
      B (b i) (b.equivFun.symm c) = ∑ j, c j * B (b i) (b j) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    simp only [map_smul, smul_eq_mul]
  have separates (v : V) (hv : ∀ i, B (b i) v = 0) : v = 0 := by
    apply hB.2 v
    have he : B.flip v = 0 := by
      apply LinearMap.ext_on b.span_eq
      rintro _ ⟨i, rfl⟩
      exact hv i
    intro w
    exact LinearMap.congr_fun he w
  have hA : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have hv : b.equivFun.symm (fun i => (c i : ℝ)) = 0 := by
      apply separates
      intro i
      rw [pairing_sum]
      have hci : ∑ j, G i j * c j = 0 := congrFun hc i
      have hci' : ((∑ j, G i j * c j : ℚ) : ℝ) = 0 := by exact_mod_cast hci
      push_cast at hci'
      simpa only [hG, mul_comm] using hci'
    have he := b.equivFun.symm.injective (hv.trans (map_zero b.equivFun.symm).symm)
    funext i
    have hi : (c i : ℝ) = 0 := congrFun he i
    change c i = 0
    exact_mod_cast hi
  have hsurj := LinearMap.injective_iff_surjective.mp hA
  have hspanQ : Submodule.span ℚ (Set.range b) = Submodule.span ℚ R := by
    apply le_antisymm (Submodule.span_mono (Set.range_subset_iff.mpr hb))
    apply Submodule.span_le.mpr
    intro v hv
    have hy (i : T) : ∃ r : ℚ, B (b i) v = (r : ℝ) := hrat _ (hb i) v hv
    choose y hy using hy
    obtain ⟨c, hc⟩ := hsurj y
    have he : b.equivFun.symm (fun i => (c i : ℝ)) = v := by
      apply sub_eq_zero.mp
      apply separates
      intro i
      rw [map_sub, pairing_sum, hy]
      have hci : ∑ j, G i j * c j = y i := congrFun hc i
      have hci' : ((∑ j, G i j * c j : ℚ) : ℝ) = (y i : ℝ) := by exact_mod_cast hci
      push_cast at hci'
      rw [sub_eq_zero]
      simpa only [hG, mul_comm] using hci'
    rw [← he, Module.Basis.equivFun_symm_apply]
    exact Submodule.sum_mem _ fun i _ => by
      rw [Rat.cast_smul_eq_qsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  let bQ := (b.restrictScalars ℚ).map (LinearEquiv.ofEq _ _ hspanQ)
  have hbQ (i : T) : ((bQ i : Submodule.span ℚ R) : V) = b i := by
    change (((b.restrictScalars ℚ) i : Submodule.span ℚ (Set.range b)) : V) = b i
    exact b.restrictScalars_apply ℚ i
  let f := extendScalars (R := ℚ) (S := ℝ) (N := V) (Submodule.span ℚ R).subtype
  have hfb : (⇑f ∘ ⇑(bQ.baseChange ℝ)) = ⇑b := by
    funext i
    change f ((bQ.baseChange ℝ) i) = b i
    rw [Module.Basis.baseChange_apply]
    change (1 : ℝ) • ((bQ i : Submodule.span ℚ R) : V) = b i
    rw [one_smul, hbQ]
  apply LinearMap.bijective_of_linearIndependent_of_span_eq_top (bQ.baseChange ℝ).span_eq
  · rw [hfb]
    exact b.linearIndependent
  · rw [hfb]
    exact b.span_eq

theorem realization_of_maximalToral (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) : Realization H := by
  let : H.IsCartanSubalgebra :=
    (isCartan_iff_isCartanSubalgebra H).mp ((isCartan_iff_maximal_toral hss H).mpr hH)
  have hs := rootSet_spans hss hH
  have hsum := cartanSum_bijective hss hH hs
  have hp := realKilling_positive hss hH hs
  refine
    { roots_span := hs
      cartan_sum := hsum
      killing_restrict_real := killing_restrict_real hss hH
      killing_positive := hp
      roots_restrict_real := root_eval_real hss hH
      riesz_pairing := riesz_pairing hss hH hp
      extension_formula := extension_formula hss hH hp
      extension_root := extension_root hss hH hp hsum.surjective
      dual_complexification := dualComplexification_bijective hss hH hp hsum
      root_system := realRoots_system hss hH hp hsum.surjective hs
      root_form_agrees := root_form_agrees hss hH hp hsum.surjective
      riesz_coroot := riesz_coroot hss hH hp hsum.surjective
      coroot_evaluation := coroot_evaluation hss hH hp hsum.surjective
      root_form_rational := root_form_rational hss hH hp hsum.surjective
      rational_extension := ?_ }
  let B : LinearMap.BilinForm ℝ (E H) :=
    (realKilling H).compl₁₂ (riesz H hp).toLinearMap (riesz H hp).toLinearMap
  have hB : B.Nondegenerate := by
    constructor
    · intro x hx
      apply (riesz H hp).injective
      rw [map_zero]
      apply (realKilling_nondegenerate H hp).1
      intro y
      obtain ⟨z, rfl⟩ := (riesz H hp).surjective y
      exact hx z
    · intro x hx
      apply (riesz H hp).injective
      rw [map_zero]
      apply (realKilling_nondegenerate H hp).2
      intro y
      obtain ⟨z, rfl⟩ := (riesz H hp).surjective y
      exact hx z
  apply rational_extension_bijective B hB (realRoots H)
  · exact (rootSet_finite H hH.1).image _
  · exact rootRestriction_spans hss hH hs
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact root_form_rational hss hH hp hsum.surjective a ha b hb

theorem realization (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] : Realization H :=
  realization_of_maximalToral hss H (cartan_isMaximalToral hss H)

theorem zero_rank [Subsingleton L] (H : LieSubalgebra ℂ L) :
    rootSet H = ∅ ∧ realRoots H = ∅ ∧ Subsingleton (E H) := by
  have hr : rootSet H = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    apply ha.1
    exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]
  refine ⟨hr, ?_, ⟨fun f g => LinearMap.ext fun x => ?_⟩⟩
  · change rootRestriction H '' rootSet H = ∅
    rw [hr, Set.image_empty]
  · rw [Subsingleton.elim x 0, map_zero, map_zero]

end LieAlgebrasAndRepresentations.RealRootSpace
