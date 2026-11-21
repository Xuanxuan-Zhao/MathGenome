import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootStrings
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Module

/-! LA-D04: ordinary root strings and the exponential representative of reflection. -/
universe u
namespace LieAlgebrasAndRepresentations.RootStrings

open private maximalToral_isCartan rootSpace_eq_generalized rootWeight
  rootWeight_nonzero coroot_rootWeight
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

/-- Reflection of the complex Cartan dual, using the Killing-normalized coroot. -/
noncomputable abbrev rootReflection (H : LieSubalgebra ℂ L)
    (α β : Module.Dual ℂ H) : Module.Dual ℂ H :=
  Specs.LieAlgebrasAndRepresentations.RootStrings.reflection_value H α β

noncomputable abbrev reflectionLiftLinear (e f : L) : Module.End ℂ L :=
  Specs.LieAlgebrasAndRepresentations.RootStrings.reflectionLiftLinear_value e f

theorem coroot_pairing_integral (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α β : Module.Dual ℂ H) (hα : α ∈ rootSet H) (hβ : β ∈ rootSet H) :
    ∃ z : ℤ, β (killingCoroot H α) = (z : ℂ) ∧
      2 * rootForm H β α / rootForm H α α = (z : ℂ) := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  let a := rootWeight H hH α hα
  let b := rootWeight H hH β hβ
  have hi := LieAlgebra.IsKilling.apply_coroot_eq_cast a b
  rw [coroot_rootWeight hss H hH] at hi
  change β (killingCoroot H α) = _ at hi
  refine ⟨_, hi, ?_⟩
  rw [← killingCoroot_pairing hss H hH]
  exact hi

theorem reflection_mem_rootSet (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α β : Module.Dual ℂ H) (hα : α ∈ rootSet H) (hβ : β ∈ rootSet H) :
    rootReflection H α β ∈ rootSet H := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  let a := rootWeight H hH α hα
  let b := rootWeight H hH β hβ
  let r := LieAlgebra.IsKilling.reflectRoot a b
  have he : (r : H → ℂ) = (rootReflection H α β : H → ℂ) := by
    change (b : H → ℂ) - b (LieAlgebra.IsKilling.coroot a) • (a : H → ℂ) = _
    rw [coroot_rootWeight hss H hH]
    rfl
  refine ⟨?_, ?_⟩
  · intro hz
    apply LieAlgebra.IsKilling.reflectRoot_isNonZero a b (rootWeight_nonzero H hH β hβ)
    change (r : H → ℂ) = 0
    rw [he, hz]
    rfl
  · have hr := r.2
    change (LieModule.genWeightSpace L (r : H → ℂ)) ≠ ⊥ at hr
    intro hz
    apply hr
    apply LieSubmodule.toSubmodule_injective
    rw [rootSpace_eq_generalized H hH, he]
    exact hz

-- Keep generated simplifier auxiliaries private to this module. In particular,
-- inverse simp lemmas must not become public declarations below `root_string`.
private theorem rootStringInterval (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α β : Module.Dual ℂ H) (hα : α ∈ rootSet H) (hβ : β ∈ rootSet H)
    (hba : β ≠ α) (hbna : β ≠ -α) :
    ∃ p q : ℕ, β (killingCoroot H α) = (p : ℂ) - (q : ℂ) ∧
      ∀ k : ℤ, β + k • α ∈ rootSet H ↔ -(p : ℤ) ≤ k ∧ k ≤ (q : ℤ) := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  let a := rootWeight H hH α hα
  let b := rootWeight H hH β hβ
  refine ⟨LieModule.chainBotCoeff a b, LieModule.chainTopCoeff a b, ?_, ?_⟩
  · have hi := LieAlgebra.IsKilling.apply_coroot_eq_cast a b
    rw [coroot_rootWeight hss H hH] at hi
    change β (killingCoroot H α) = _ at hi
    simpa only [Int.cast_sub, Int.cast_natCast] using hi
  · intro k
    have hn : β + k • α ≠ 0 := by
      intro hz
      have hb : β = (-(k : ℂ)) • α := by
        rw [neg_smul, Int.cast_smul_eq_zsmul]
        exact eq_neg_of_add_eq_zero_left hz
      rcases proportional_root_eq hss H hH α β hα hβ _ hb with h | h
      · exact hba h
      · exact hbna h
    have hi := LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff a b
      (rootWeight_nonzero H hH α hα) k
    have he : (k • (a : H → ℂ) + (b : H → ℂ)) = (β + k • α : Module.Dual ℂ H) := by
      ext h
      simp only [Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply]
      exact add_comm _ _
    change (LieModule.genWeightSpace L (k • (a : H → ℂ) + (b : H → ℂ))) ≠ ⊥ ↔ _ at hi
    simp only [ne_eq, ← LieSubmodule.toSubmodule_inj, rootSpace_eq_generalized H hH, he] at hi
    change ((β + k • α ≠ 0) ∧ rootSpace H (β + k • α) ≠ ⊥) ↔ _
    rw [and_iff_right hn]
    exact hi.trans (by omega)

/-- The exact interval of roots in the α-string through β. -/
theorem root_string (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α β : Module.Dual ℂ H) (hα : α ∈ rootSet H) (hβ : β ∈ rootSet H)
    (hba : β ≠ α) (hbna : β ≠ -α) :
    ∃ p q : ℕ, β (killingCoroot H α) = (p : ℂ) - (q : ℂ) ∧
      ∀ k : ℤ, β + k • α ∈ rootSet H ↔ -(p : ℤ) ≤ k ∧ k ≤ (q : ℤ) :=
  rootStringInterval hss H hH α β hα hβ hba hbna


theorem root_bracket_ne_zero (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α β : Module.Dual ℂ H) (hα : α ∈ rootSet H) (hβ : β ∈ rootSet H)
    (hab : α + β ∈ rootSet H)
    (e x : L) (he : e ∈ rootSpace H α) (hx : x ∈ rootSpace H β)
    (he0 : e ≠ 0) (hx0 : x ≠ 0) : ⁅e, x⁆ ≠ 0 := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  let a := rootWeight H hH α hα
  let b := rootWeight H hH β hβ
  have hab' : LieAlgebra.rootSpace H (a + b : H → ℂ) ≠ ⊥ := by
    simp only [ne_eq, ← LieSubmodule.toSubmodule_inj, rootSpace_eq_generalized H hH]
    exact hab.2
  obtain ⟨e', he', x', hx', hex⟩ :=
    LieAlgebra.IsKilling.exists_mem_rootSpace_lie_ne_zero
      (rootWeight_nonzero H hH α hα) hab'
  have he' : e' ∈ rootSpace H α := by
    change e' ∈ (LieModule.weightSpace L (α : H → ℂ)).toSubmodule
    rw [← rootSpace_eq_generalized H hH]
    exact he'
  have hx' : x' ∈ rootSpace H β := by
    change x' ∈ (LieModule.weightSpace L (β : H → ℂ)).toSubmodule
    rw [← rootSpace_eq_generalized H hH]
    exact hx'
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨e, he⟩ : rootSpace H α) (by simpa using he0)).mp
    (finrank_rootSpace_eq_one hss H hH α hα) ⟨e', he'⟩
  obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨x, hx⟩ : rootSpace H β) (by simpa using hx0)).mp
    (finrank_rootSpace_eq_one hss H hH β hβ) ⟨x', hx'⟩
  have hc' : c • e = e' := congrArg Subtype.val hc
  have hd' : d • x = x' := congrArg Subtype.val hd
  intro hz
  apply hex
  rw [← hc', ← hd', smul_lie, lie_smul, hz, smul_zero, smul_zero]


/-- Both directions of every successive nontrivial root-string bracket. -/
theorem successive_root_brackets (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α γ : Module.Dual ℂ H) (hα : α ∈ rootSet H) (hγ : γ ∈ rootSet H)
    (e f x : L) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hx : x ∈ rootSpace H γ) (he0 : e ≠ 0) (hf0 : f ≠ 0) (hx0 : x ≠ 0) :
    (α + γ ∈ rootSet H → ⁅e, x⁆ ≠ 0) ∧
    (-α + γ ∈ rootSet H → ⁅f, x⁆ ≠ 0) := by
  have hna : -α ∈ rootSet H := by
    refine ⟨neg_ne_zero.mpr hα.1, ?_⟩
    intro hz
    apply hf0
    simpa only [hz, Submodule.mem_bot] using hf
  exact ⟨fun h => root_bracket_ne_zero hss H hH α γ hα hγ h e x he hx he0 hx0,
    fun h => root_bracket_ne_zero hss H hH (-α) γ hna hγ h f x hf hx hf0 hx0⟩

noncomputable section Exponential

local instance : Module ℚ L := Module.restrictScalars ℚ ℂ L
local instance : IsScalarTower ℚ ℂ L := IsScalarTower.restrictScalars ℚ ℂ L

private noncomputable def expAd (x : L) (hx : IsNilpotent (LieAlgebra.ad ℂ L x)) :
    L ≃ₗ⁅ℂ⁆ L :=
  (LieDerivation.ad ℂ L x).exp (by
    simpa only [LieDerivation.coe_ad_apply_eq_ad_apply] using hx)

private theorem expAd_apply (x : L) (hx : IsNilpotent (LieAlgebra.ad ℂ L x)) (y : L) :
    expAd x hx y = IsNilpotent.exp (LieAlgebra.ad ℂ L x) y := by
  simp only [expAd, LieDerivation.exp_map_apply, LieDerivation.coe_ad_apply_eq_ad_apply]

private theorem exp_apply_of_sq_zero (D : Module.End ℂ L) (hD : IsNilpotent D)
    (y : L) (hy : (D ^ 2) y = 0) : IsNilpotent.exp D y = y + D y := by
  have hs := IsNilpotent.exp_smul_eq_sum (a := D) (m := y) (k := 2) hy hD
  simpa [Module.End.smul_def, Finset.sum_range_succ] using hs

private theorem exp_apply_of_cube_zero (D : Module.End ℂ L) (hD : IsNilpotent D)
    (y : L) (hy : (D ^ 3) y = 0) :
    IsNilpotent.exp D y = y + D y + (1 / 2 : ℂ) • (D (D y)) := by
  have hs := IsNilpotent.exp_smul_eq_sum (a := D) (m := y) (k := 3) hy hD
  norm_num [Module.End.smul_def, Finset.sum_range_succ, pow_succ, Module.End.mul_apply] at hs ⊢
  convert hs using 1; simp [← algebraMap_smul ℂ]

private theorem lift_cartan (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H)
    (ha : α (killingCoroot H α) = 2) (e f : L)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hef : ⁅e, f⁆ = (killingCoroot H α : L))
    (heN : IsNilpotent (LieAlgebra.ad ℂ L e))
    (hfN : IsNilpotent (LieAlgebra.ad ℂ L f)) (h : H) :
    reflectionLiftLinear e f (h : L) = (h : L) - α h • (killingCoroot H α : L) := by
  let E := LieAlgebra.ad ℂ L e
  let F := -LieAlgebra.ad ℂ L f
  let t : L := killingCoroot H α
  have heh (h : H) : E (h : L) = -(α h) • e := by
    change ⁅e, (h : L)⁆ = _
    rw [← lie_skew, (mem_rootSpace H α e).mp he h]
    simp
  have hfh (h : H) : F (h : L) = -(α h) • f := by
    change -⁅f, (h : L)⁆ = _
    rw [lie_skew, (mem_rootSpace H (-α) f).mp hf h]
    rfl
  have hEe : E e = 0 := lie_self e
  have hFf : F f = 0 := by change -⁅f, f⁆ = 0; simp
  have hFe : F e = t := by change -⁅f, e⁆ = t; rw [lie_skew]; exact hef
  have hFt : F t = (-2 : ℂ) • f := by simpa only [ha] using hfh (killingCoroot H α)
  have hFN : IsNilpotent F := hfN.neg
  have expEh (h : H) : IsNilpotent.exp E (h : L) = (h : L) - α h • e := by
    rw [exp_apply_of_sq_zero E heN _ (by
      simp [pow_succ, Module.End.mul_apply, heh, hEe]), heh]
    module
  have expFh (h : H) : IsNilpotent.exp F (h : L) = (h : L) - α h • f := by
    rw [exp_apply_of_sq_zero F hFN _ (by
      simp [pow_succ, Module.End.mul_apply, hfh, hFf]), hfh]
    module
  have expEe : IsNilpotent.exp E e = e := by
    rw [exp_apply_of_sq_zero E heN _ (by simp [pow_succ, Module.End.mul_apply, hEe]), hEe, add_zero]
  have expFe : IsNilpotent.exp F e = e + t - f := by
    rw [exp_apply_of_cube_zero F hFN _ (by
      simp [pow_succ, Module.End.mul_apply, hFe, hFt, hFf]), hFe, hFt]
    module
  have expEt : IsNilpotent.exp E t = t - (2 : ℂ) • e := by
    simpa only [ha] using expEh (killingCoroot H α)
  change IsNilpotent.exp E (IsNilpotent.exp F (IsNilpotent.exp E (h : L))) = _
  rw [expEh, map_sub, map_smul, expFh, expFe]
  simp only [map_sub, map_smul, map_add, expEh, expEe, expEt]
  module

private theorem rootSpace_map_of_cartan_reflection (H : LieSubalgebra ℂ L)
    (α : Module.Dual ℂ H) (ha : α (killingCoroot H α) = 2)
    (n : L ≃ₗ⁅ℂ⁆ L)
    (hn : ∀ h : H, n (h : L) = (h : L) - α h • (killingCoroot H α : L))
    (β : Module.Dual ℂ H) :
    (rootSpace H β).map n.toLinearMap = rootSpace H (rootReflection H α β) := by
  let s (h : H) : H := h - α h • killingCoroot H α
  have hs (h : H) : n (s h : L) = (h : L) := by
    rw [hn]
    change (h : L) - α h • (killingCoroot H α : L) -
      α (h - α h • killingCoroot H α) • (killingCoroot H α : L) = (h : L)
    rw [map_sub, map_smul, ha]
    simp only [smul_eq_mul]
    module
  have hb (h : H) : β (s h) = rootReflection H α β h := by
    dsimp [s, rootReflection, Specs.LieAlgebrasAndRepresentations.RootStrings.reflection_value]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hsb (h : H) : rootReflection H α β (s h) = β h := by
    change β (h - α h • killingCoroot H α) - β (killingCoroot H α) *
      α (h - α h • killingCoroot H α) = β h
    rw [map_sub, map_smul, map_sub, map_smul, ha]
    simp only [smul_eq_mul]
    ring
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (mem_rootSpace H _ _).mpr
    intro h
    change ⁅(h : L), n x⁆ = _
    rw [← hs h, ← n.map_lie, (mem_rootSpace H β x).mp hx (s h), map_smul, hb]
    rfl
  · intro hy
    refine ⟨n.symm y, ?_, n.apply_symm_apply y⟩
    apply (mem_rootSpace H β _).mpr
    intro h
    apply n.toLinearEquiv.injective
    change n ⁅(h : L), n.symm y⁆ = n (β h • n.symm y)
    rw [n.map_lie, n.apply_symm_apply, map_smul, n.apply_symm_apply]
    have hh : n (h : L) = (s h : L) := hn h
    rw [hh, (mem_rootSpace H _ y).mp hy (s h), hsb]

/-- The source's exponential product, with the whole-space transport assertion. -/
theorem reflection_lift (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H)
    (e f : L) (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hef : ⁅e, f⁆ = (killingCoroot H α : L)) :
    IsNilpotent (LieAlgebra.ad ℂ L e) ∧ IsNilpotent (LieAlgebra.ad ℂ L f) ∧
    ∃ n : L ≃ₗ⁅ℂ⁆ L, n.toLinearMap = reflectionLiftLinear e f ∧
      (∀ h : H, n (h : L) = (h : L) - α h • (killingCoroot H α : L)) ∧
      ∀ β : Module.Dual ℂ H,
        (rootSpace H β).map n.toLinearMap = rootSpace H (rootReflection H α β) := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  have hα' : (α : H → ℂ) ≠ 0 := by
    intro hz
    exact hα.1 (LinearMap.ext fun h => congrFun hz h)
  have he' : e ∈ LieAlgebra.rootSpace H (α : H → ℂ) := by
    change e ∈ (LieModule.genWeightSpace L (α : H → ℂ)).toSubmodule
    rw [rootSpace_eq_generalized H hH]
    exact he
  have hf' : f ∈ LieAlgebra.rootSpace H ((-α) : H → ℂ) := by
    change f ∈ (LieModule.genWeightSpace L ((-α) : H → ℂ)).toSubmodule
    rw [rootSpace_eq_generalized H hH]
    exact hf
  have heN := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα' he'
  have hfN := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (by simpa using hα') hf'
  have hnfN : IsNilpotent (LieAlgebra.ad ℂ L (-f)) := by simpa using hfN.neg
  have ha : α (killingCoroot H α) = 2 := by
    rw [killingCoroot_pairing hss H hH]
    exact mul_div_cancel_right₀ 2 (rootForm_self_ne_zero hss H hH α hα)
  let n := ((expAd e heN).trans (expAd (-f) hnfN)).trans (expAd e heN)
  have hn : n.toLinearMap = reflectionLiftLinear e f := by
    ext x
    change n x = (reflectionLiftLinear e f) x
    simp only [n, LieEquiv.trans_apply, expAd_apply, map_neg]
    rfl
  have hc (h : H) : n (h : L) = (h : L) - α h • (killingCoroot H α : L) := by
    change n.toLinearMap (h : L) = _
    rw [hn]
    exact lift_cartan H α ha e f he hf hef heN hfN h
  exact ⟨heN, hfN, n, hn, hc, rootSpace_map_of_cartan_reflection H α ha n hc⟩

private theorem matrix_exp_eq_of_nilpotent {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : IsNilpotent A) : IsNilpotent.exp A = NormedSpace.exp A := by
  obtain ⟨k, hk⟩ := hA
  rw [IsNilpotent.exp_eq_sum hk, NormedSpace.exp_eq_tsum_rat]
  symm
  apply tsum_eq_sum
  intro n hn
  rw [pow_eq_zero_of_le (by simpa only [Finset.mem_range, not_lt] using hn) hk, smul_zero]

theorem reflection_lift_matrix_exponential (d : ℕ) (b : Module.Basis (Fin d) ℂ L)
    (e f : L) (he : IsNilpotent (LieAlgebra.ad ℂ L e))
    (hf : IsNilpotent (LieAlgebra.ad ℂ L f)) :
    LinearMap.toMatrixAlgEquiv b (reflectionLiftLinear e f) =
      NormedSpace.exp (LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad ℂ L e)) *
      NormedSpace.exp (-LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad ℂ L f)) *
      NormedSpace.exp (LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad ℂ L e)) := by
  change LinearMap.toMatrixAlgEquiv b
    (IsNilpotent.exp (LieAlgebra.ad ℂ L e) * IsNilpotent.exp (-LieAlgebra.ad ℂ L f) *
      IsNilpotent.exp (LieAlgebra.ad ℂ L e)) = _
  rw [map_mul, map_mul, he.map_exp, hf.neg.map_exp,
    matrix_exp_eq_of_nilpotent _ (he.map _),
    matrix_exp_eq_of_nilpotent _ (hf.neg.map _), map_neg]


end Exponential
end LieAlgebrasAndRepresentations.RootStrings
