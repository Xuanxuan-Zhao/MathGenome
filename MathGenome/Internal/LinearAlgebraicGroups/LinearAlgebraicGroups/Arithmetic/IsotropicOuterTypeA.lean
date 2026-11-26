import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.HermitianMatrixGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.HermitianRadicalComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OuterTypeALocalModels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IsotropicNormOneRadicalsDensity
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA

open Spec
open LinearAlgebraicGroups.Specs.HermitianMatrixGeneration (HermitianForm)
open LinearAlgebraicGroups.Specs.UnitaryRankOne (quadraticConjugation quadraticConjugation_ne_one)
open private conj_conj conj_eq_iff trace_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
variable {V : Type w} [AddCommGroup V] [Module E V]

local notation "σ" => quadraticConjugation F E

variable (h : HermitianForm (W := V) (quadraticConjugation F E))
include h

private def formLinear (x : V) : V →ₗ[E] E :=
  (h.linear_second x).mk' (h.pairing x)

@[simp] private theorem formLinear_apply (x y : V) :
    formLinear h x y = h.pairing x y := rfl

@[simp] private theorem add_right (x y z : V) :
    h.pairing x (y + z) = h.pairing x y + h.pairing x z :=
  (formLinear h x).map_add y z

@[simp] private theorem smul_right (c : E) (x y : V) :
    h.pairing x (c • y) = c * h.pairing x y :=
  (formLinear h x).map_smul c y

@[simp] private theorem zero_right (x : V) : h.pairing x 0 = 0 :=
  (formLinear h x).map_zero

@[simp] private theorem sub_right (x y z : V) :
    h.pairing x (y - z) = h.pairing x y - h.pairing x z :=
  (formLinear h x).map_sub y z

@[simp] private theorem add_left (x y z : V) :
    h.pairing (x + y) z = h.pairing x z + h.pairing y z := by
  rw [← h.hermitian z (x + y), add_right, map_add, h.hermitian, h.hermitian]

@[simp] private theorem sub_left (x y z : V) :
    h.pairing (x - y) z = h.pairing x z - h.pairing y z := by
  rw [← h.hermitian z (x - y), sub_right, map_sub, h.hermitian, h.hermitian]

@[simp] private theorem smul_left (c : E) (x y : V) :
    h.pairing (c • x) y = σ c * h.pairing x y := by
  rw [← h.hermitian y (c • x), smul_right, map_mul, h.hermitian]

@[simp] private theorem zero_left (x : V) : h.pairing 0 x = 0 := by
  rw [← h.hermitian x 0, zero_right, map_zero]

/-- The linear map underlying a reflection with centre `Ez`. -/
private def reflectionMap (z : V) (η : E) : V →ₗ[E] V :=
  LinearMap.id + (((η - 1) / h.pairing z z) • formLinear h z).smulRight z

@[simp] private theorem reflectionMap_apply (z : V) (η : E) (x : V) :
    reflectionMap h z η x =
      x + ((η - 1) * (h.pairing z x / h.pairing z z)) • z := by
  simp only [reflectionMap, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, formLinear_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, ← mul_div_assoc]

private theorem reflectionMap_inverse (z : V) (η θ : E) (hz : h.pairing z z ≠ 0)
    (hη : η * θ = 1) (x : V) :
    reflectionMap h z η (reflectionMap h z θ x) = x := by
  simp only [reflectionMap_apply, add_right, smul_right]
  rw [add_assoc, ← add_smul]
  have hh : (θ - 1) * (h.pairing z x / h.pairing z z) +
      (η - 1) * ((h.pairing z x +
        (θ - 1) * (h.pairing z x / h.pairing z z) * h.pairing z z) /
        h.pairing z z) = 0 := by
    rw [mul_assoc (θ - 1), div_mul_cancel₀ _ hz]
    field_simp [hz]
    linear_combination h.pairing z x * hη
  simp [hh]

/-- Scaling the nonisotropic line by a scalar of norm one is invertible. -/
private def reflection (z : V) (η : E) (hz : h.pairing z z ≠ 0)
    (hη : η * σ η = 1) : V ≃ₗ[E] V :=
  LinearEquiv.ofLinearMap (reflectionMap h z η) (reflectionMap h z (σ η))
    (LinearMap.ext (reflectionMap_inverse h z η (σ η) hz hη))
    (LinearMap.ext (reflectionMap_inverse h z (σ η) η hz (by rwa [mul_comm])))

@[simp] private theorem reflection_apply (z : V) (η : E) (hz : h.pairing z z ≠ 0)
    (hη : η * σ η = 1) (x : V) :
    reflection h z η hz hη x = x + ((η - 1) * (h.pairing z x / h.pairing z z)) • z :=
  reflectionMap_apply h z η x

private theorem reflection_mem (z : V) (η : E) (hz : h.pairing z z ≠ 0)
    (hη : η * σ η = 1) : reflection h z η hz hη ∈ h.reflections :=
  ⟨z, η, hz, hη, reflection_apply h z η hz hη⟩

private theorem reflections_le_unitary : Subgroup.closure h.reflections ≤ h.unitaryGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨z, η, hz, hη, hg⟩ x y
  rw [hg x, hg y]
  simp only [HermitianForm.reflectionAction, add_left, add_right, smul_left, smul_right, map_mul,
    map_sub, map_one, map_div₀, h.hermitian]
  field_simp
  linear_combination (h.pairing x z * h.pairing z y) * hη

omit h in
private theorem nonfixed_exists : ∃ c : E, σ c ≠ c := by
  by_contra! H
  exact quadraticConjugation_ne_one F E (AlgEquiv.ext H)

omit h in
private theorem norm_one_ne_one : ∃ η : E, η * σ η = 1 ∧ η ≠ 1 := by
  obtain ⟨c, hc⟩ := nonfixed_exists (F := F) (E := E)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (map_zero σ)
  have hsc0 : σ c ≠ 0 := (map_ne_zero_iff σ (quadraticConjugation F E).injective).mpr hc0
  refine ⟨σ c / c, ?_, ?_⟩
  · rw [map_div₀, conj_conj]
    field_simp
  · intro he
    exact hc (by simpa only [one_mul] using (div_eq_iff hc0).mp he)

private def reflectionsIn (W : Submodule E V) : Set (V ≃ₗ[E] V) :=
  {g | ∃ (z : V) (_ : z ∈ W) (η : E), h.pairing z z ≠ 0 ∧ η * σ η = 1 ∧
    ∀ x, g x = x + ((η - 1) * (h.pairing z x / h.pairing z z)) • z}

private theorem reflection_mem_in {W : Submodule E V} {z : V} (hzW : z ∈ W) (η : E)
    (hz : h.pairing z z ≠ 0) (hη : η * σ η = 1) :
    reflection h z η hz hη ∈ Subgroup.closure (reflectionsIn h W) :=
  Subgroup.subset_closure ⟨z, hzW, η, hz, hη, reflection_apply h z η hz hη⟩

private theorem align_difference {W : Submodule E V} {x y : V} (hx : x ∈ W) (hy : y ∈ W)
    (heq : h.pairing x x = h.pairing y y) (hn : h.pairing (x - y) (x - y) ≠ 0) :
    ∃ g ∈ Subgroup.closure (reflectionsIn h W), g x = y := by
  let z := x - y
  let d := h.pairing z x
  have hq : h.pairing z z = d + σ d := by
    dsimp [d, z]
    rw [h.hermitian (x - y) x]
    simp only [sub_left, sub_right, heq]
    ring
  have hd : d ≠ 0 := by
    intro hd
    exact hn (by simp [z, hq, hd])
  let η := -(σ d) / d
  have hη : η * σ η = 1 := by
    dsimp [η]
    rw [map_div₀, map_neg, conj_conj]
    have hsd : σ d ≠ 0 := (map_ne_zero_iff σ (quadraticConjugation F E).injective).mpr hd
    field_simp
  refine ⟨reflection h z η hn hη, reflection_mem_in h (W.sub_mem hx hy) η hn hη, ?_⟩
  rw [reflection_apply]
  change x + ((η - 1) * (d / h.pairing z z)) • (x - y) = y
  have hscale : (η - 1) * (d / h.pairing z z) = -1 := by
    have hq0 : h.pairing z z ≠ 0 := hn
    dsimp only [η]
    field_simp [hd, hq0]
    linear_combination hq
  rw [hscale, neg_one_smul, neg_sub, add_comm x, sub_add_cancel]

private theorem align_scaled {W : Submodule E V} {x y : V} (hx : x ∈ W) (hy : y ∈ W)
    (heq : h.pairing x x = h.pairing y y) (hy0 : h.pairing y y ≠ 0)
    {η : E} (hη : η * σ η = 1)
    (hn : h.pairing (x - η • y) (x - η • y) ≠ 0) :
    ∃ g ∈ Subgroup.closure (reflectionsIn h W), g x = y := by
  have hnorm : h.pairing (η • y) (η • y) = h.pairing y y := by
    rw [smul_left, smul_right, ← mul_assoc, mul_comm (σ η), hη, one_mul]
  obtain ⟨g, hg, hgx⟩ := align_difference h hx (W.smul_mem η hy) (heq.trans hnorm.symm) hn
  have hη' : σ η * σ (σ η) = 1 := by rw [conj_conj, mul_comm, hη]
  let r := reflection h y (σ η) hy0 hη'
  refine ⟨r * g, Subgroup.mul_mem _ (reflection_mem_in h hy (σ η) hy0 hη') hg, ?_⟩
  change r (g x) = y
  rw [hgx]
  change reflection h y (σ η) hy0 hη' (η • y) = y
  rw [reflection_apply, smul_right, mul_div_cancel_right₀ _ hy0, ← add_smul]
  have hs : η + (σ η - 1) * η = 1 := by linear_combination (norm := ring_nf) hη
  rw [hs, one_smul]

private theorem norm_sub_smul (x y : V) (η : E) (hη : η * σ η = 1) :
    h.pairing (x - η • y) (x - η • y) =
      h.pairing x x + h.pairing y y - η * h.pairing x y - σ η * h.pairing y x := by
  simp only [sub_left, sub_right, smul_left, smul_right]
  linear_combination (h.pairing y y) * hη

private theorem align_nonorthogonal_char_two {W : Submodule E V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (heq : h.pairing x x = h.pairing y y)
    (hy0 : h.pairing y y ≠ 0) (hpair : h.pairing y x ≠ 0)
    (htwo : (2 : E) = 0) :
    ∃ g ∈ Subgroup.closure (reflectionsIn h W), g x = y := by
  by_cases hdiff : h.pairing (x - y) (x - y) = 0
  · have hsum : h.pairing y y + h.pairing y y = 0 := by rw [← two_mul, htwo, zero_mul]
    have hequal : h.pairing x y = h.pairing y x := by
      simp only [sub_left, sub_right, heq, sub_sub] at hdiff
      linear_combination -hdiff + hsum - htwo * h.pairing y x
    obtain ⟨η, hη, hηne⟩ := norm_one_ne_one (F := F) (E := E)
    apply align_scaled h hx hy heq hy0 hη
    intro hzero
    rw [norm_sub_smul h x y η hη, heq, hsum, hequal] at hzero
    have hsumη : η + σ η = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hpair
      linear_combination -hzero
    have hsame : σ η = η := by linear_combination hsumη - htwo * η
    have hsquare : η * η = 1 := by simpa only [hsame] using hη
    have hz : (η - 1) * (η - 1) = 0 := by
      linear_combination hsquare - htwo * (η - 1)
    exact hηne (sub_eq_zero.mp ((mul_eq_zero.mp hz).elim id id))
  · exact align_difference h hx hy heq hdiff

private theorem align [Infinite F] {W : Submodule E V} {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (heq : h.pairing x x = h.pairing y y)
    (hy0 : h.pairing y y ≠ 0) :
    ∃ g ∈ Subgroup.closure (reflectionsIn h W), g x = y := by
  by_cases htwo : (2 : E) = 0
  · by_cases hpair : h.pairing y x = 0
    · classical
      obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset F)
      have ha0 : a ≠ 0 := fun he => ha (by simp [he])
      have ha1 : a ≠ 1 := fun he => ha (by simp [he])
      let c : E := algebraMap F E a
      have hc : c ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr ha0
      have hc1 : c ≠ 1 := by
        intro hc1
        apply ha1
        exact (algebraMap F E).injective (by simpa only [map_one] using hc1)
      let z := c • x + (1 - c) • y
      have hz : z ∈ W := W.add_mem (W.smul_mem c hx) (W.smul_mem (1 - c) hy)
      have hpair' : h.pairing x y = 0 := by rw [← h.hermitian, hpair, map_zero]
      have hcz : σ c = c := (quadraticConjugation F E).commutes a
      have hzval : h.pairing z z = h.pairing y y := by
        dsimp only [z]
        simp only [add_left, add_right, smul_left, smul_right, hcz, hpair, hpair',
          mul_zero, zero_add, add_zero, map_sub, map_one, heq]
        linear_combination htwo * (c * c - c) * h.pairing y y
      have hzx : h.pairing z x ≠ 0 := by
        simpa only [z, add_left, smul_left, hcz, hpair, mul_zero, add_zero, heq] using
          mul_ne_zero hc hy0
      have hyz : h.pairing y z ≠ 0 := by
        simpa only [z, add_right, smul_right, hpair, mul_zero, zero_add] using
          mul_ne_zero (sub_ne_zero.mpr hc1.symm) hy0
      obtain ⟨g₁, hg₁, hg₁x⟩ := align_nonorthogonal_char_two h hx hz
        (heq.trans hzval.symm) (fun hz0 => hy0 (hzval.symm.trans hz0)) hzx htwo
      obtain ⟨g₂, hg₂, hg₂z⟩ := align_nonorthogonal_char_two h hz hy hzval hy0 hyz htwo
      exact ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂ hg₁, by
        change g₂ (g₁ x) = y
        rw [hg₁x, hg₂z]⟩
    · exact align_nonorthogonal_char_two h hx hy heq hy0 hpair htwo
  · by_cases hdiff : h.pairing (x - y) (x - y) = 0
    · have hη : (-1 : E) * σ (-1) = 1 := by simp
      apply align_scaled h hx hy heq hy0 hη
      intro hzero
      have hp := norm_sub_smul h x y (-1) hη
      simp only [map_neg, map_one, hzero, heq, neg_mul, one_mul, sub_neg_eq_add] at hp
      simp only [sub_left, sub_right, heq] at hdiff
      have hcontr : (2 : E) * 2 * h.pairing y y = 0 := by linear_combination hdiff - hp
      exact mul_ne_zero (mul_ne_zero htwo htwo) hy0 hcontr
    · exact align_difference h hx hy heq hdiff

private theorem exists_nonsingular_vector {W : Submodule E V} (hW : W ≠ ⊥)
    (hn : ∀ x ∈ W, (∀ y ∈ W, h.pairing y x = 0) → x = 0) :
    ∃ v ∈ W, h.pairing v v ≠ 0 := by
  by_contra! hzero
  obtain ⟨c, hc⟩ := nonfixed_exists (F := F) (E := E)
  apply hW
  refine le_antisymm (fun x hx => ?_) bot_le
  change x = 0
  refine hn x hx (fun y hy => ?_)
  have h₁ := hzero (x + y) (W.add_mem hx hy)
  have h₂ := hzero (c • x + y) (W.add_mem (W.smul_mem c hx) hy)
  simp only [add_left, add_right, smul_left, smul_right, hzero x hx, hzero y hy,
    mul_zero, add_zero, zero_add] at h₁ h₂
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc.symm)
  linear_combination h₂ - σ c * h₁

private theorem hyperbolicPartner (e : V) (he : e ≠ 0) (hee : h.pairing e e = 0)
    (hn : h.Nondegenerate) :
    ∃ f : V, h.pairing e f = 1 ∧ h.pairing f f = 0 := by
  have hpair : ∃ y, h.pairing e y ≠ 0 := by
    by_contra! hzero
    apply he
    apply hn e
    intro y
    rw [← h.hermitian, hzero, map_zero]
  obtain ⟨y, hy⟩ := hpair
  let y' := (h.pairing e y)⁻¹ • y
  have hey : h.pairing e y' = 1 := by
    rw [smul_right, inv_mul_cancel₀ hy]
  have hye : h.pairing y' e = 1 := by
    rw [← h.hermitian, hey, map_one]
  have hnorm : σ (h.pairing y' y') = h.pairing y' y' :=
    h.hermitian y' y'
  obtain ⟨a, ha⟩ := (conj_eq_iff _).mp hnorm
  have hd := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hd ▸ by decide)
  obtain ⟨b, hb⟩ := Algebra.trace_surjective (K := F) (L := E) (-a)
  have htr : b + σ b = -h.pairing y' y' := by
    rw [← trace_eq, hb, map_neg, ha]
  refine ⟨y' + b • e, ?_, ?_⟩
  · simp only [add_right, smul_right, hee, hey, mul_zero, add_zero]
  · simp only [add_right, add_left, smul_left, smul_right, hee, hey, hye, mul_one, mul_zero, add_zero]
    linear_combination htr

private theorem reflection_words_unitary {W : Submodule E V} {g : V ≃ₗ[E] V}
    (hg : g ∈ Subgroup.closure (reflectionsIn h W)) : g ∈ h.unitaryGroup :=
  reflections_le_unitary h <|
    (Subgroup.closure_mono (show reflectionsIn h W ⊆ h.reflections from
      fun _ ⟨z, _, η, hz, hη, hf⟩ => ⟨z, η, hz, hη, hf⟩)) hg

private theorem reflection_words_preserve {W : Submodule E V} {g : V ≃ₗ[E] V}
    (hg : g ∈ Subgroup.closure (reflectionsIn h W)) :
    ∀ x, g x ∈ W ↔ x ∈ W := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨z, hzW, η, hz, hη, hg⟩ := hg
    intro x
    rw [hg x]
    have hm := W.smul_mem ((η - 1) * (h.pairing z x / h.pairing z z)) hzW
    exact ⟨fun hsum => add_sub_cancel_right x _ ▸ W.sub_mem hsum hm,
      fun hx => W.add_mem hx hm⟩
  | one =>
    intro x
    rfl
  | mul g k _ _ hg hk =>
    intro x
    change g (k x) ∈ W ↔ x ∈ W
    rw [hg, hk]
  | inv g _ hg =>
    intro x
    change g.symm x ∈ W ↔ x ∈ W
    simpa only [LinearEquiv.apply_symm_apply] using (hg (g.symm x)).symm

private theorem reflection_words_fix {W : Submodule E V} {g : V ≃ₗ[E] V}
    (hg : g ∈ Subgroup.closure (reflectionsIn h W))
    (x : V) (hx : ∀ y ∈ W, h.pairing y x = 0) : g x = x := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨z, hzW, η, hz, hη, hg⟩ := hg
    simp [hg x, hx z hzW]
  | one => rfl
  | mul g k _ _ hg hk =>
    change g (k x) = x
    rw [hk, hg]
  | inv g _ hg =>
    change g.symm x = x
    rw [LinearEquiv.symm_apply_eq, hg]

private theorem unitary_mem_reflection_closure [Infinite F] [FiniteDimensional E V]
    {W : Submodule E V} (g : V ≃ₗ[E] V) (hg : g ∈ h.unitaryGroup)
    (hW : ∀ x ∈ W, g x ∈ W)
    (hn : ∀ x ∈ W, (∀ y ∈ W, h.pairing y x = 0) → x = 0)
    (hfix : ∀ x, (∀ y ∈ W, h.pairing y x = 0) → g x = x) :
    g ∈ Subgroup.closure (reflectionsIn h W) := by
  induction W using WellFounded.induction
    (measure (fun W : Submodule E V => Module.finrank E W)).wf generalizing g with
  | h W IH =>
    by_cases hW0 : W = ⊥
    · have he : g = 1 := by
        ext x
        apply hfix
        intro y hy
        have hy0 : y = 0 := by simpa [hW0] using hy
        simp [hy0]
      rw [he]
      exact Subgroup.one_mem _
    obtain ⟨v, hv, hv0⟩ := exists_nonsingular_vector h hW0 hn
    let W' := W ⊓ LinearMap.ker (formLinear h v)
    have hW' : W' < W := by
      refine lt_of_le_of_ne inf_le_left (fun he => hv0 ?_)
      have hvm : v ∈ W' := he ▸ hv
      exact hvm.2
    have hdim : Module.finrank E W' < Module.finrank E W :=
      Submodule.finrank_lt_finrank_of_lt hW'
    have hg' : ∀ x y, h.pairing (g x) (g y) = h.pairing x y := hg
    obtain ⟨r, hr, hrv⟩ := align h (hW v hv) hv (hg' v v) hv0
    let k := r * g
    have hk : k ∈ h.unitaryGroup := Subgroup.mul_mem _ (reflection_words_unitary h hr) hg
    have hk' : ∀ x y, h.pairing (k x) (k y) = h.pairing x y := hk
    have hkv : k v = v := hrv
    have hkW : ∀ x ∈ W', k x ∈ W' := by
      intro x hx
      refine ⟨?_, ?_⟩
      · exact (reflection_words_preserve h hr (g x)).mpr (hW x hx.1)
      · change h.pairing v (k x) = 0
        rw [← hkv, hk']
        exact hx.2
    have decompose (x : V) : h.pairing v
        (x - (h.pairing v x / h.pairing v v) • v) = 0 := by
      rw [sub_right, smul_right, div_mul_cancel₀ _ hv0, sub_self]
    have hn' : ∀ x ∈ W', (∀ y ∈ W', h.pairing y x = 0) → x = 0 := by
      intro x hx hperp
      apply hn x hx.1
      intro y hy
      let a := h.pairing v y / h.pairing v v
      have hy' : y - a • v ∈ W' :=
        ⟨W.sub_mem hy (W.smul_mem _ hv), decompose y⟩
      have hzero : h.pairing v x = 0 := hx.2
      simpa only [sub_left, smul_left, hzero, mul_zero, sub_zero] using hperp _ hy'
    have hfixW : ∀ x, (∀ y ∈ W, h.pairing y x = 0) → k x = x := by
      intro x hx
      change r (g x) = x
      rw [hfix x hx, reflection_words_fix h hr x hx]
    have hfix' : ∀ x, (∀ y ∈ W', h.pairing y x = 0) → k x = x := by
      intro x hx
      let a := h.pairing v x / h.pairing v v
      let z := x - a • v
      have hz : ∀ y ∈ W, h.pairing y z = 0 := by
        intro y hy
        let b := h.pairing v y / h.pairing v v
        have hy' : y - b • v ∈ W' :=
          ⟨W.sub_mem hy (W.smul_mem _ hv), decompose y⟩
        have hvz : h.pairing v z = 0 := decompose x
        have hyv : h.pairing (y - b • v) v = 0 := by
          rw [← h.hermitian, decompose y, map_zero]
        have h₁ : h.pairing (y - b • v) z = 0 := by
          simp only [z, sub_right, smul_right, hx _ hy', hyv, mul_zero, sub_zero]
        simpa only [sub_left, smul_left, hvz, mul_zero, sub_zero] using h₁
      have hxz : z + a • v = x := sub_add_cancel _ _
      rw [← hxz, map_add, map_smul, hfixW z hz, hkv]
    have hkwords := IH W' hdim k hk hkW hn' hfix'
    have hle : Subgroup.closure (reflectionsIn h W') ≤ Subgroup.closure (reflectionsIn h W) :=
      Subgroup.closure_mono (fun _ ⟨z, hzW', η, hz, hη, hf⟩ => ⟨z, hzW'.1, η, hz, hη, hf⟩)
    have hrg := Subgroup.mul_mem _ (Subgroup.inv_mem _ hr) (hle hkwords)
    simpa [k, ← mul_assoc] using hrg

omit h in
theorem hermitianReflectionGeneration : HermitianReflectionGeneration.{u,v,w} := by
  intro F E _ _ _ _ _ _ V _ _ _ h hn
  refine le_antisymm (reflections_le_unitary h) (fun g hg => ?_)
  have htop : reflectionsIn h (⊤ : Submodule E V) = h.reflections := by
    ext g
    constructor
    · rintro ⟨z, _, η, hz, hη, hf⟩
      exact ⟨z, η, hz, hη, hf⟩
    · rintro ⟨z, η, hz, hη, hf⟩
      exact ⟨z, Submodule.mem_top, η, hz, hη, hf⟩
  rw [← htop]
  apply unitary_mem_reflection_closure h g hg
  · intro x hx
    exact Submodule.mem_top
  · exact fun x _ hx => hn x (fun y => hx y Submodule.mem_top)
  · intro x hx
    have hzero := hn x (fun y => hx y Submodule.mem_top)
    simp [hzero]

end LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA

namespace LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA

open Spec
open LinearAlgebraicGroups.Specs.UnitaryRankOne (quadraticConjugation)
open private exists_trace_zero_unit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
open scoped TensorProduct Matrix

section QuadraticAlgebra

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

local notation "σ" => quadraticConjugation F E

private theorem independent_one_and_nonfixed (c : E) (hc : σ c ≠ c) :
    LinearIndependent F ![(1 : E), c] := by
  rw [LinearIndependent.pair_iff]
  intro s t he
  by_cases ht : t = 0
  · subst t
    exact ⟨(algebraMap F E).injective (by simpa [Algebra.smul_def] using he), rfl⟩
  · exfalso
    have he' : algebraMap F E s + algebraMap F E t * c = 0 := by simpa [Algebra.smul_def] using he
    have hσ := congrArg (quadraticConjugation F E) he'
    simp only [map_add, map_mul, AlgEquiv.commutes, map_zero] at hσ
    apply hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp (show algebraMap F E t * (σ c - c) = 0 by
      linear_combination hσ - he')).resolve_left ((map_ne_zero_iff _ (algebraMap F E).injective).mpr ht))

theorem quadraticFixedAlgebra : QuadraticFixedAlgebra.{u,v,w} := by
  intro F E _ _ _ _ _ R _ _
  obtain ⟨c, hc⟩ := nonfixed_exists (F := F) (E := E)
  let b := basisOfLinearIndependentOfCardEqFinrank (independent_one_and_nonfixed c hc)
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])
  have hb : ⇑b = ![(1 : E), c] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hb0 : b 0 = 1 := congrFun hb 0
  have hb1 : b 1 = c := congrFun hb 1
  let bR := b.baseChange R
  let C := R ⊗[F] E
  let a : R →+* C := algebraMap R C
  have ha : Function.Injective a := by
    intro s t hst
    have hst' : s ⊗ₜ[F] (1 : E) = t ⊗ₜ[F] (1 : E) := hst
    have hrepr := congrArg (fun y => (b.baseChange R).repr y 0) hst'
    rw [← hb0, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      Module.Basis.repr_self_apply, ite_eq_left rfl, one_smul, one_smul] at hrepr
    exact hrepr
  refine ⟨ha, ?_⟩
  intro x
  constructor
  · intro hx
    let p := bR.repr x 0
    let q := bR.repr x 1
    have hrepr : p ⊗ₜ[F] (1 : E) + q ⊗ₜ[F] c = x := by
      simpa only [Fin.sum_univ_two, Module.Basis.baseChange_apply, hb0, hb1,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one] using (b.baseChange R).sum_repr x
    have hx' := congrArg (conjugationAt (R := R) (quadraticConjugation F E)) hrepr
    simp only [map_add, conjugationAt, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.coe_toAlgHom, map_one] at hx'
    have hdiff : q ⊗ₜ[F] (quadraticConjugation F E c - c) = (0 : C) := by
      rw [TensorProduct.tmul_sub, sub_eq_zero]
      apply add_left_cancel (a := p ⊗ₜ[F] (1 : E))
      rw [hrepr]
      exact hx'.trans hx
    have hunit : IsUnit ((1 : R) ⊗ₜ[F] (quadraticConjugation F E c - c)) :=
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hc)).map
        (Algebra.TensorProduct.includeRight (R := F) (A := R)).toMonoidHom
    have hq : a q = 0 := by
      refine hunit.mul_right_cancel ?_
      change (q ⊗ₜ[F] (1 : E)) * (1 ⊗ₜ[F] (quadraticConjugation F E c - c)) =
        0 * (1 ⊗ₜ[F] (quadraticConjugation F E c - c))
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, zero_mul] using hdiff
    have hq0 : q = 0 := ha (hq.trans (map_zero a).symm)
    exact ⟨p, by simpa [a, hq0, Algebra.TensorProduct.algebraMap_apply] using hrepr⟩
  · rintro ⟨r, rfl⟩
    simp [conjugationAt, Algebra.TensorProduct.algebraMap_apply]
end QuadraticAlgebra

section HyperbolicPlane

private theorem hyperbolic_entry_condition {B : Type*} [CommRing B]
    (τ : B →+* B) (X : Matrix (Fin 2) (Fin 2) B) (hdet : X.det = 1) :
    (X.map τ).transpose * hyperbolicMatrix B * X = hyperbolicMatrix B ↔
      τ (X 0 0) = X 0 0 ∧ τ (X 1 1) = X 1 1 ∧
      τ (X 0 1) = -X 0 1 ∧ τ (X 1 0) = -X 1 0 := by
  let Y : Matrix (Fin 2) (Fin 2) B := !![X 1 1, -X 0 1; -X 1 0, X 0 0]
  have hXY : X * Y = 1 := by
    rw [Matrix.det_fin_two] at hdet
    conv_lhs => enter [1]; rw [Matrix.eta_fin_two X]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Y] <;> first | (solve | linear_combination hdet) | ring
  have hYX : Y * X = 1 := by
    rw [Matrix.det_fin_two] at hdet
    conv_lhs => enter [2]; rw [Matrix.eta_fin_two X]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Y] <;> first | (solve | linear_combination hdet) | ring
  have he : (X.map τ).transpose * hyperbolicMatrix B * X = hyperbolicMatrix B ↔
      (X.map τ).transpose * hyperbolicMatrix B = hyperbolicMatrix B * Y := by
    constructor
    · intro h
      simpa only [Matrix.mul_assoc, hXY, Matrix.mul_one] using congrArg (· * Y) h
    · intro h
      simpa only [Matrix.mul_assoc, hYX, Matrix.mul_one] using congrArg (· * X) h
  rw [he]
  have hL : (X.map τ).transpose * hyperbolicMatrix B =
      !![τ (X 1 0), τ (X 0 0); τ (X 1 1), τ (X 0 1)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : hyperbolicMatrix B * Y = !![-X 1 0, X 0 0; X 1 1, -X 0 1] := by
    simp [hyperbolicMatrix, Y]
  rw [hL, hR]
  constructor
  · intro h
    exact ⟨congrFun (congrFun h 0) 1, congrFun (congrFun h 1) 0,
      congrFun (congrFun h 1) 1, congrFun (congrFun h 0) 0⟩
  · rintro ⟨h₀₀,h₁₁,h₀₁,h₁₀⟩
    rw [h₀₀, h₁₁, h₀₁, h₁₀]

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable {R : Type w} [CommRing R] [Algebra F R]

private theorem comparison_entries (α : Eˣ) (B : Matrix (Fin 2) (Fin 2) R) :
    let a : R →+* (R ⊗[F] E) := algebraMap R _
    let s : R ⊗[F] E := (1 : R) ⊗ₜ[F] (α : E)
    let t : R ⊗[F] E := (1 : R) ⊗ₜ[F] (↑α⁻¹ : E)
    hyperbolicComparison (F := F) α B =
      !![a (B 0 0), s * a (B 0 1); a (B 1 0) * t, a (B 1 1)] := by
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicComparison, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
      mul_comm, Algebra.TensorProduct.tmul_mul_tmul]

private theorem comparison_det (α : Eˣ) (B : Matrix (Fin 2) (Fin 2) R) :
    (hyperbolicComparison (F := F) α B).det = algebraMap R (R ⊗[F] E) B.det := by
  rw [comparison_entries, Matrix.det_fin_two, Matrix.det_fin_two B, map_sub, map_mul, map_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  rw [mul_assoc, ← mul_assoc ((algebraMap R _) (B 0 1)), ← mul_assoc, mul_comm ((1 : R) ⊗ₜ[F] (α : E))]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem hyperbolicSpecialUnitary : HyperbolicSpecialUnitary.{u,v,w} := by
  intro F E _ _ _ _ _
  obtain ⟨α, hα⟩ := exists_trace_zero_unit (F := F) (E := E)
  have hα' : quadraticConjugation F E (α : E) = -(α : E) := eq_neg_of_add_eq_zero_right hα
  refine ⟨α, hα', ?_, ?_⟩
  · intro R _ _
    dsimp only
    let C := R ⊗[F] E
    let a : R →+* C := algebraMap R C
    let σR : C →ₐ[R] C := conjugationAt (quadraticConjugation F E)
    let s : C := (1 : R) ⊗ₜ[F] (α : E)
    let t : C := (1 : R) ⊗ₜ[F] (↑α⁻¹ : E)
    let f := hyperbolicComparison (F := F) (R := R) α
    have hst : s * t = 1 := by
      change Algebra.TensorProduct.includeRight (R := F) (A := R) (α : E) *
        Algebra.TensorProduct.includeRight (R := F) (A := R) (↑α⁻¹ : E) = 1
      rw [← map_mul, Units.mul_inv, map_one]
    have hs : σR s = -s := by
      change Algebra.TensorProduct.map (AlgHom.id R R)
        (quadraticConjugation F E).toAlgHom ((1 : R) ⊗ₜ[F] (α : E)) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, hα',
        TensorProduct.tmul_neg]
    have ht : σR t = -t := by
      have h := congrArg σR hst
      rw [map_mul, hs, neg_mul, map_one] at h
      apply (IsUnit.of_mul_eq_one _ hst).mul_left_cancel
      rw [mul_neg, hst]
      exact neg_eq_iff_eq_neg.mp h
    obtain ⟨ha, hfixed⟩ := quadraticFixedAlgebra (F := F) (E := E) R
    have haf (r : R) : σR (a r) = a r := AlgHom.commutes σR r
    have hunitS := IsUnit.of_mul_eq_one _ hst
    have hunitT := IsUnit.of_mul_eq_one _ ((mul_comm t s).trans hst)
    have hscaledS (r : R) : s * a r = 0 ↔ r = 0 := by
      constructor
      · intro hr
        exact ha (hunitS.mul_left_cancel (by simpa only [map_zero, mul_zero] using hr))
      · rintro rfl
        simp
    have hscaledT (r : R) : a r * t = 0 ↔ r = 0 := by
      constructor
      · intro hr
        exact ha (hunitT.mul_right_cancel (by simpa only [map_zero, zero_mul] using hr))
      · rintro rfl
        simp
    have hentry (B : Matrix (Fin 2) (Fin 2) R) :
        f B = !![a (B 0 0), s * a (B 0 1); a (B 1 0) * t, a (B 1 1)] :=
      comparison_entries α B
    have hD : Matrix.diagonal ![s, 1] * Matrix.diagonal ![t, 1] =
        (1 : Matrix (Fin 2) (Fin 2) C) := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hst]
    have hDi : Matrix.diagonal ![t, 1] * Matrix.diagonal ![s, 1] =
        (1 : Matrix (Fin 2) (Fin 2) C) := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [show t * s = 1 from (mul_comm t s).trans hst]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro B D hBD
      change f B = f D at hBD
      rw [hentry, hentry] at hBD
      ext i j
      fin_cases i <;> fin_cases j
      · exact ha (congrFun (congrFun hBD 0) 0)
      · exact ha (hunitS.mul_left_cancel (congrFun (congrFun hBD 0) 1))
      · exact ha (hunitT.mul_right_cancel (congrFun (congrFun hBD 1) 0))
      · exact ha (congrFun (congrFun hBD 1) 1)
    · change Matrix.diagonal ![s, 1] * a.mapMatrix 1 * Matrix.diagonal ![t, 1] = 1
      rw [map_one, mul_one, hD]
    · intro B D
      change Matrix.diagonal ![s, 1] * a.mapMatrix (B * D) * Matrix.diagonal ![t, 1] = _
      rw [map_mul]
      change _ = (Matrix.diagonal ![s, 1] * a.mapMatrix B * Matrix.diagonal ![t, 1]) *
        (Matrix.diagonal ![s, 1] * a.mapMatrix D * Matrix.diagonal ![t, 1])
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (_ * a.mapMatrix B) _ (Matrix.diagonal ![s, 1]), hDi,
        Matrix.mul_one]
    · intro X
      change X.det = 1 ∧ (X.map σR).transpose * hyperbolicMatrix C * X = hyperbolicMatrix C ↔
        ∃ B : Matrix (Fin 2) (Fin 2) R, B.det = 1 ∧ f B = X
      constructor
      · rintro ⟨hdet, hform⟩
        obtain ⟨h₀₀, h₁₁, h₀₁, h₁₀⟩ :=
          (hyperbolic_entry_condition σR.toRingHom X hdet).mp hform
        have hf₀₁ : σR (t * X 0 1) = t * X 0 1 := by
          change σR (X 0 1) = -X 0 1 at h₀₁
          rw [map_mul, ht, h₀₁, neg_mul_neg]
        have hf₁₀ : σR (s * X 1 0) = s * X 1 0 := by
          change σR (X 1 0) = -X 1 0 at h₁₀
          rw [map_mul, hs, h₁₀, neg_mul_neg]
        obtain ⟨b₀₀, hb₀₀⟩ := (hfixed _).mp h₀₀
        obtain ⟨b₁₁, hb₁₁⟩ := (hfixed _).mp h₁₁
        obtain ⟨b₀₁, hb₀₁⟩ := (hfixed _).mp hf₀₁
        obtain ⟨b₁₀, hb₁₀⟩ := (hfixed _).mp hf₁₀
        let B : Matrix (Fin 2) (Fin 2) R := !![b₀₀, b₀₁; b₁₀, b₁₁]
        have he : f B = X := by
          rw [hentry, Matrix.eta_fin_two X]
          have h₀₁' : s * (t * X 0 1) = X 0 1 := by rw [← mul_assoc, hst, one_mul]
          have h₁₀' : s * X 1 0 * t = X 1 0 := by
            rw [mul_comm s, mul_assoc, hst, mul_one]
          change !![a b₀₀, s * a b₀₁; a b₁₀ * t, a b₁₁] = _
          rw [hb₀₀, hb₀₁, hb₁₀, hb₁₁, h₀₁', h₁₀']
        refine ⟨B, ha ?_, he⟩
        rw [map_one, ← comparison_det α B]
        exact (congrArg Matrix.det he).trans hdet
      · rintro ⟨B, hdet, rfl⟩
        have hd : (f B).det = 1 := by
          change (hyperbolicComparison (F := F) α B).det = 1
          rw [comparison_det, hdet, map_one]
        refine ⟨hd, (hyperbolic_entry_condition σR.toRingHom (f B) hd).mpr ?_⟩
        rw [hentry]
        change σR (a (B 0 0)) = a (B 0 0) ∧ σR (a (B 1 1)) = a (B 1 1) ∧
          σR (s * a (B 0 1)) = -(s * a (B 0 1)) ∧
          σR (a (B 1 0) * t) = -(a (B 1 0) * t)
        refine ⟨haf _, haf _, ?_, ?_⟩
        · rw [map_mul, hs, haf, neg_mul]
        · rw [map_mul, ht, haf, mul_neg]
    · intro B i j
      change f B i j = 0 ↔ B i j = 0
      rw [hentry]
      fin_cases i <;> fin_cases j
      · exact map_eq_zero_iff a ha
      · exact hscaledS _
      · exact hscaledT _
      · exact map_eq_zero_iff a ha
    · intro B i
      change f B i i = 1 ↔ B i i = 1
      rw [hentry]
      fin_cases i <;> exact ⟨fun h => ha (h.trans (map_one a).symm), fun h => h ▸ map_one a⟩
  · intro R S _ _ _ _ f B
    rw [comparison_entries, comparison_entries]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.map_tmul]

end HyperbolicPlane

section HermitianGroups

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open LinearAlgebraicGroups.Specs
open Specs.HermitianMatrixGeneration (HermitianForm Space hyperbolicPairing)
open Specs.Arithmetic.HermitianRadicalComparison
open Specs.Arithmetic.OuterTypeALocalModels (RepresentsHermitian)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.UnitaryRankOne (quadraticConjugation quadraticConjugation_ne_one)
open private conj_conj from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
open private matrixHom matrix_injective matrix_preimage matrix_preserves
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.HermitianRadicalComparison

section MatrixPairing

variable {B : Type*} [CommRing B] {I J l : Type*} [Fintype I] [Fintype J]

private def adjointMatrix (σ : B →+* B) (X : Matrix I J B) : Matrix J I B :=
  (X.map σ).transpose

private theorem adjointMatrix_mul (σ : B →+* B) (X : Matrix I J B) (Y : Matrix J l B) :
    adjointMatrix σ (X * Y) = adjointMatrix σ Y * adjointMatrix σ X := by
  simp only [adjointMatrix, Matrix.map_mul, Matrix.transpose_mul]

private theorem adjointMatrix_one [DecidableEq I] (σ : B →+* B) :
    adjointMatrix σ (1 : Matrix I I B) = 1 := by
  simp [adjointMatrix, Matrix.map_one σ (map_zero _) (map_one _)]

private theorem adjointMatrix_involutive (σ : B →+* B) (hσ : ∀ a, σ (σ a) = a)
    (X : Matrix I J B) : adjointMatrix σ (adjointMatrix σ X) = X :=
  Matrix.ext fun i j => hσ (X i j)

private def matrixPairing (σ : B →+* B) (H : Matrix I I B) (x y : I → B) : B :=
  dotProduct (σ ∘ x) (H *ᵥ y)

private theorem matrixPairing_change (σ : B →+* B) (H : Matrix J J B)
    (A : Matrix J I B) (x y : I → B) :
    matrixPairing σ (adjointMatrix σ A * H * A) x y =
      matrixPairing σ H (A *ᵥ x) (A *ᵥ y) := by
  unfold matrixPairing
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    adjointMatrix, Matrix.vecMul_transpose]
  congr 1
  exact funext fun i => (σ.map_mulVec A x i).symm

private theorem map_single_one [DecidableEq I] (σ : B →+* B) (i : I) :
    σ ∘ Pi.single i 1 = (Pi.single i 1 : I → B) := by
  funext j
  by_cases hj : j = i <;> simp [hj]

private theorem matrixPairing_single_left [DecidableEq I] (σ : B →+* B)
    (H : Matrix I I B) (i : I) (y : I → B) :
    matrixPairing σ H (Pi.single i 1) y = (H *ᵥ y) i := by
  simp [matrixPairing, map_single_one, single_dotProduct]

private theorem matrixPairing_entry [DecidableEq I] (σ : B →+* B)
    (H : Matrix I I B) (i j : I) :
    matrixPairing σ H (Pi.single i 1) (Pi.single j 1) = H i j := by
  rw [matrixPairing_single_left, Matrix.mulVec_single_one]
  rfl

private theorem matrixPairing_isometry_iff [DecidableEq I] (σ : B →+* B)
    (H X : Matrix I I B) :
    adjointMatrix σ X * H * X = H ↔
      ∀ x y, matrixPairing σ H (X *ᵥ x) (X *ᵥ y) = matrixPairing σ H x y := by
  simp_rw [← matrixPairing_change]
  constructor
  · intro h x y
    rw [h]
  · intro h
    exact Matrix.ext fun i j => by
      simpa only [matrixPairing_entry] using h (Pi.single i 1) (Pi.single j 1)

end MatrixPairing

section FieldPairing

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  {I : Type*} [Fintype I] [DecidableEq I]

local notation "σ" => quadraticConjugation F E

private def formOfMatrix (H : Matrix I I E) (hH : adjointMatrix (σ).toRingHom H = H) :
    HermitianForm (W := I → E) σ where
  pairing := matrixPairing (σ).toRingHom H
  linear_second x := by
    constructor
    · intro y z
      simp [matrixPairing, Matrix.mulVec_add]
    · intro c y
      simp [matrixPairing, Matrix.mulVec_smul]
  hermitian x y := by
    change (σ).toRingHom (matrixPairing (σ).toRingHom H x y) = _
    unfold matrixPairing
    rw [RingHom.map_dotProduct]
    have hx : (σ).toRingHom ∘ (σ).toRingHom ∘ x = x := funext fun i => conj_conj (x i)
    have hy : (σ).toRingHom ∘ (H *ᵥ y) = H.map (σ).toRingHom *ᵥ ((σ).toRingHom ∘ y) :=
      funext fun i => (σ).toRingHom.map_mulVec H y i
    rw [hx, hy, ← Matrix.transpose_transpose (H.map (σ).toRingHom),
      Matrix.dotProduct_transpose_mulVec]
    exact congrArg (fun M => dotProduct ((σ).toRingHom ∘ y) (M *ᵥ x)) hH

private theorem formOfMatrix_nondegenerate (H : (Matrix I I E)ˣ)
    (hH : adjointMatrix (σ).toRingHom H.val = H.val) : (formOfMatrix H.val hH).Nondegenerate := by
  intro x hx
  have hz : H.val *ᵥ x = 0 := funext fun i => by
    simpa only [formOfMatrix, matrixPairing_single_left, Pi.zero_apply] using hx (Pi.single i 1)
  have h := congrArg (fun v => H.inv *ᵥ v) hz
  simpa only [Matrix.mulVec_mulVec, H.inv_val, Matrix.one_mulVec, Matrix.mulVec_zero] using h

end FieldPairing

section BasisChange

variable {B : Type*} [CommRing B] {I J : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem matricesOfEquiv_mul (b : (I → B) ≃ₗ[B] (J → B)) :
    LinearMap.toMatrix' b.toLinearMap * LinearMap.toMatrix' b.symm.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]

private def changeMatrix (T : Matrix J I B) (U : Matrix I J B)
    (hTU : T * U = 1) (hUT : U * T = 1) : Matrix J J B ≃* Matrix I I B where
  toFun X := U * X * T
  invFun X := T * X * U
  left_inv X := by
    simp only [← Matrix.mul_assoc]
    rw [hTU, Matrix.one_mul, Matrix.mul_assoc X T U, hTU, Matrix.mul_one]
  right_inv X := by
    simp only [← Matrix.mul_assoc]
    rw [hUT, Matrix.one_mul, Matrix.mul_assoc X U T, hUT, Matrix.mul_one]
  map_mul' X Y := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (U * X) T U, hTU, Matrix.mul_one]

private theorem changeMatrix_det (T : Matrix J I B) (U : Matrix I J B)
    (hTU : T * U = 1) (hUT : U * T = 1) (X : Matrix J J B) :
    (changeMatrix T U hTU hUT X).det = X.det :=
  Matrix.det_conj_of_mul_eq_one hUT hTU

private theorem changeMatrix_isometry (σ : B →+* B) (H : Matrix J J B)
    (T : Matrix J I B) (U : Matrix I J B) (hTU : T * U = 1) (hUT : U * T = 1)
    (X : Matrix J J B) :
    let H' := adjointMatrix σ T * H * T
    let X' := changeMatrix T U hTU hUT X
    adjointMatrix σ X' * H' * X' = H' ↔ adjointMatrix σ X * H * X = H := by
  have hUT' : adjointMatrix σ U * adjointMatrix σ T = 1 := by
    rw [← adjointMatrix_mul, hTU, adjointMatrix_one]
  have h (Y : Matrix J J B) :
      adjointMatrix σ U * (adjointMatrix σ T * Y * T) * U = Y := by
    simp only [← Matrix.mul_assoc]
    rw [hUT', Matrix.one_mul, Matrix.mul_assoc Y T U, hTU, Matrix.mul_one]
  change adjointMatrix σ (U * X * T) * (adjointMatrix σ T * H * T) * (U * X * T) = _ ↔ _
  have hform : adjointMatrix σ (U * X * T) * (adjointMatrix σ T * H * T) * (U * X * T) =
      adjointMatrix σ T * (adjointMatrix σ X * H * X) * T := by
    simp only [adjointMatrix_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (adjointMatrix σ T * adjointMatrix σ X) (adjointMatrix σ U)
      (adjointMatrix σ T), hUT', Matrix.mul_one,
      Matrix.mul_assoc (adjointMatrix σ T * adjointMatrix σ X * H) T U, hTU, Matrix.mul_one]
  rw [hform]
  constructor
  · intro eq
    have eq' := congrArg (fun Y => adjointMatrix σ U * Y * U) eq
    simpa only [h] using eq'
  · intro eq
    rw [eq]

private def changedGram (σ : B →+* B) (H : (Matrix J J B)ˣ)
    (T : Matrix J I B) (U : Matrix I J B) (hTU : T * U = 1) (hUT : U * T = 1) :
    (Matrix I I B)ˣ :=
  have hTU' : adjointMatrix σ T * adjointMatrix σ U = 1 := by
    rw [← adjointMatrix_mul, hUT, adjointMatrix_one]
  have hUT' : adjointMatrix σ U * adjointMatrix σ T = 1 := by
    rw [← adjointMatrix_mul, hTU, adjointMatrix_one]
  { val := adjointMatrix σ T * H.val * T
    inv := U * H.inv * adjointMatrix σ U
    val_inv := by
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (adjointMatrix σ T * H.val) T U, hTU, Matrix.mul_one,
        Matrix.mul_assoc (adjointMatrix σ T) H.val H.inv, H.val_inv, Matrix.mul_one, hTU']
    inv_val := by
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (U * H.inv) (adjointMatrix σ U) (adjointMatrix σ T), hUT',
        Matrix.mul_one, Matrix.mul_assoc U H.inv H.val, H.inv_val, Matrix.mul_one, hUT] }

private theorem changedGram_hermitian (σ : B →+* B) (hσ : ∀ a, σ (σ a) = a)
    (H : (Matrix J J B)ˣ) (hH : adjointMatrix σ H.val = H.val)
    (T : Matrix J I B) (U : Matrix I J B) (hTU : T * U = 1) (hUT : U * T = 1) :
    adjointMatrix σ (changedGram σ H T U hTU hUT).val = (changedGram σ H T U hTU hUT).val := by
  simp only [changedGram, adjointMatrix_mul, adjointMatrix_involutive σ hσ, hH, Matrix.mul_assoc]

end BasisChange

section ModelTransport

variable {F E I : Type u} {J : Type*} [Field F] [Field E] [Algebra F E]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {σ : E ≃ₐ[F] E} {G : AffineAlgebraicGroup F}

private abbrev coefficientInclusion (R : TestAlgebra F) : E →+* Coeff E R :=
  (Algebra.TensorProduct.includeRight (R := F) (A := R)).toRingHom

private theorem map_adjointMatrix (R : TestAlgebra F) (T : Matrix J I E) :
    (adjointMatrix (σ).toRingHom T).map (coefficientInclusion R) =
      adjointMatrix (conjugation σ R).toRingHom (T.map (coefficientInclusion R)) := by
  ext i j
  change (1 : R) ⊗ₜ[F] σ (T j i) = conjugation σ R ((1 : R) ⊗ₜ[F] T j i)
  simp [conjugation]

private theorem inclusion_natural {K L : Type*} {R S : TestAlgebra F} (a : R ⟶ S)
    (T : Matrix K L E) :
    (T.map (coefficientInclusion R)).map (changeCoefficients a) =
      T.map (coefficientInclusion S) := by
  ext i j
  change changeCoefficients a ((1 : R) ⊗ₜ[F] T i j) = (1 : S) ⊗ₜ[F] T i j
  simp [changeCoefficients]

private def changeMatrices (T : Matrix J I E) (U : Matrix I J E)
    (hTU : T * U = 1) (hUT : U * T = 1) (R : TestAlgebra F) :
    Matrix J J (Coeff E R) ≃* Matrix I I (Coeff E R) :=
  changeMatrix (T.map (coefficientInclusion R)) (U.map (coefficientInclusion R))
    (by rw [← Matrix.map_mul, hTU, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, hUT, Matrix.map_one _ (map_zero _) (map_one _)])

private theorem changeMatrices_properties (H : (Matrix J J E)ˣ)
    (T : Matrix J I E) (U : Matrix I J E) (hTU : T * U = 1) (hUT : U * T = 1)
    (R : TestAlgebra F) (X : Matrix J J (Coeff E R)) :
    let Y := changeMatrices T U hTU hUT R X
    let H' := (changedGram (σ).toRingHom H T U hTU hUT).val
    Y.det = X.det ∧ (Preserves σ H' Y ↔
      adjointMatrix (conjugation σ R).toRingHom X * H.val.map (coefficientInclusion R) * X =
        H.val.map (coefficientInclusion R)) := by
  refine ⟨changeMatrix_det .., ?_⟩
  have hgram : gram (changedGram (σ).toRingHom H T U hTU hUT).val R =
      adjointMatrix (conjugation σ R).toRingHom (T.map (coefficientInclusion R)) *
        H.val.map (coefficientInclusion R) * T.map (coefficientInclusion R) := by
    change (adjointMatrix (σ).toRingHom T * H.val * T).map (coefficientInclusion R) = _
    rw [Matrix.map_mul, Matrix.map_mul, map_adjointMatrix]
  unfold Preserves
  rw [hgram]
  exact changeMatrix_isometry ..

private def modelInBasis {n : ℕ} {H : (Matrix (Fin n) (Fin n) E)ˣ}
    (M : RepresentsHermitian σ H.val G)
    (T : Matrix (Fin n) I E) (U : Matrix I (Fin n) E) (hTU : T * U = 1) (hUT : U * T = 1) :
    Model G σ (changedGram (σ).toRingHom H T U hTU hUT).val := by
  let point := Classical.choose M
  have comparison := Classical.choose_spec M
  let H' := (changedGram (σ).toRingHom H T U hTU hUT).val
  let C (R : TestAlgebra F) := changeMatrices T U hTU hUT R
  let equiv (R : TestAlgebra F) :
      {X : Matrix.SpecialLinearGroup (Fin n) (Coeff E R) //
        Specs.Arithmetic.OuterTypeALocalModels.PreservesHermitianMatrix σ H.val R X} ≃
        {X : Matrix.SpecialLinearGroup I (Coeff E R) // Preserves σ H' X.val} :=
    { toFun := fun X =>
        have h := changeMatrices_properties (σ := σ) H T U hTU hUT R X.val.val
        ⟨⟨C R X.val.val, h.1.trans X.val.property⟩, h.2.mpr X.property⟩
      invFun := fun Y =>
        let X := (C R).symm Y.val.val
        have h := changeMatrices_properties (σ := σ) H T U hTU hUT R X
        have he : C R X = Y.val.val := (C R).apply_symm_apply _
        ⟨⟨X, h.1.symm.trans ((congrArg Matrix.det he).trans Y.val.property)⟩,
          h.2.mp (he ▸ Y.property)⟩
      left_inv := fun X => Subtype.ext (Subtype.ext ((C R).symm_apply_apply X.val.val))
      right_inv := fun Y => Subtype.ext (Subtype.ext ((C R).apply_symm_apply Y.val.val)) }
  refine ⟨fun R => (point R).trans (equiv R), ?_, ?_⟩
  · intro R x y
    apply Subtype.ext
    change C R (point R (x * y)).val.val = C R (point R x).val.val * C R (point R y).val.val
    rw [show (point R (x * y)).val.val = (point R x).val.val * (point R y).val.val from
      congrArg Subtype.val (comparison.1 R x y), map_mul]
  · intro R S a x
    change U.map (coefficientInclusion S) * (point S (mapPoints a x)).val.val *
        T.map (coefficientInclusion S) =
      (U.map (coefficientInclusion R) * (point R x).val.val * T.map (coefficientInclusion R)).map
        (changeCoefficients a)
    rw [show (point S (mapPoints a x)).val.val = (point R x).val.val.map (changeCoefficients a) from
      congrArg Subtype.val (comparison.2 a x), Matrix.map_mul, Matrix.map_mul, inclusion_natural,
      inclusion_natural]

end ModelTransport

section HermitianReductivity

open LinearAlgebraicGroups.UnitaryNormEquations (Centre centreAugmentation centreAugmentation_tmul)
open private centreProjections_bijective centreConjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
open private baseChangePointIso liftSpecialLinear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
open private connected_baseChange_iff smooth_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private reductive_of_semisimple from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open Specs.GeometricRadicals (IsReductive IsSemisimple)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.Arithmetic.OuterTypeALocalModels (PreservesHermitianMatrix)

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

local notation "σ" => quadraticConjugation F E

section SplitCoefficientAlgebra

variable {R : Type u} [CommRing R] [Algebra F R] [Algebra E R] [IsScalarTower F E R]

local instance (priority := 2000) : Algebra E (Centre F E R) := Algebra.TensorProduct.rightAlgebra

private abbrev firstFactor : (R ⊗[F] E) →+* R := centreAugmentation.toRingHom

private abbrev secondFactor : (R ⊗[F] E) →+* R :=
  (firstFactor (F := F) (E := E)).comp (centreConjugation (R := R) σ).toRingEquiv.toRingHom

private theorem scalarFactors_bijective :
    Function.Bijective (fun z : R ⊗[F] E => (firstFactor z, secondFactor z)) :=
  centreProjections_bijective (R := R) σ (quadraticConjugation_ne_one F E)

private theorem centre_conj_apply (z : R ⊗[F] E) :
    conjugation σ (CommAlgCat.of F R) z = centreConjugation (R := R) σ z := by
  induction z using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem centre_conj_conj (z : R ⊗[F] E) :
    centreConjugation (R := R) σ (centreConjugation (R := R) σ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul r a =>
    change r ⊗ₜ[F] σ (σ a) = r ⊗ₜ[F] a
    rw [conj_conj]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem matrix_eq_of_factors {n : ℕ} {X Y : Matrix (Fin n) (Fin n) (R ⊗[F] E)}
    (h₁ : X.map firstFactor = Y.map firstFactor)
    (h₂ : X.map secondFactor = Y.map secondFactor) : X = Y :=
  Matrix.ext fun i j => scalarFactors_bijective.1 <|
    Prod.ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

private theorem split_preserves_iff {n : ℕ} (H : Matrix (Fin n) (Fin n) E)
    (hH : adjointMatrix (σ).toRingHom H = H)
    (X : Matrix.SpecialLinearGroup (Fin n) (R ⊗[F] E)) :
    PreservesHermitianMatrix σ H (CommAlgCat.of F R) X ↔
      let J := H.map (algebraMap E R)
      (X.val.map secondFactor).transpose * J * X.val.map firstFactor = J := by
  let J := H.map (algebraMap E R)
  let C := H.map (coefficientInclusion (CommAlgCat.of F R))
  let D := adjointMatrix (conjugation σ (CommAlgCat.of F R)).toRingHom X.val
  have h₁ : C.map firstFactor = J := by
    ext i j
    change centreAugmentation ((1 : R) ⊗ₜ[F] H i j) = algebraMap E R (H i j)
    rw [centreAugmentation_tmul, one_mul]
  have h₂ : C.map secondFactor = J.transpose := by
    ext i j
    change centreAugmentation ((1 : R) ⊗ₜ[F] σ (H i j)) = algebraMap E R (H j i)
    rw [centreAugmentation_tmul, one_mul]
    exact congrArg (algebraMap E R) (congrFun (congrFun hH j) i)
  have hd₁ : D.map firstFactor = (X.val.map secondFactor).transpose :=
    Matrix.ext fun i j => congrArg firstFactor (centre_conj_apply (X.val j i))
  have hd₂ : D.map secondFactor = (X.val.map firstFactor).transpose := by
    ext i j
    change firstFactor (centreConjugation (R := R) σ
      (conjugation σ (CommAlgCat.of F R) (X.val j i))) = firstFactor (X.val j i)
    rw [centre_conj_apply, centre_conj_conj]
  change D * C * X.val = C ↔ (X.val.map secondFactor).transpose * J * X.val.map firstFactor = J
  constructor
  · intro h
    have hh := congrArg (fun A : Matrix (Fin n) (Fin n) (R ⊗[F] E) => A.map firstFactor) h
    simpa only [Matrix.map_mul, hd₁, h₁] using hh
  · intro h
    apply matrix_eq_of_factors
    · simpa only [Matrix.map_mul, hd₁, h₁] using h
    · have ht := congrArg Matrix.transpose h
      simpa only [Matrix.map_mul, hd₂, h₂, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc] using ht

private theorem split_special_unitary_bijective {n : ℕ} (H : (Matrix (Fin n) (Fin n) E)ˣ)
    (hH : adjointMatrix (σ).toRingHom H.val = H.val) :
    Function.Bijective
      (fun X : {x : Matrix.SpecialLinearGroup (Fin n) (R ⊗[F] E) //
        PreservesHermitianMatrix σ H.val (CommAlgCat.of F R) x} =>
        Matrix.SpecialLinearGroup.map firstFactor X.val) := by
  let J := H.val.map (algebraMap E R)
  let Jinv := H.inv.map (algebraMap E R)
  have hJi : J * Jinv = 1 := by
    change H.val.map (algebraMap E R) * H.inv.map (algebraMap E R) = 1
    rw [← Matrix.map_mul, H.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hiJ : Jinv * J = 1 := by
    change H.inv.map (algebraMap E R) * H.val.map (algebraMap E R) = 1
    rw [← Matrix.map_mul, H.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv (A : Matrix.SpecialLinearGroup (Fin n) R) : A.val * (A⁻¹).val = 1 :=
    congrArg Subtype.val (mul_inv_cancel A)
  have hinv' (A : Matrix.SpecialLinearGroup (Fin n) R) : (A⁻¹).val * A.val = 1 :=
    congrArg Subtype.val (inv_mul_cancel A)
  let other (A : Matrix.SpecialLinearGroup (Fin n) R) := (J * (A⁻¹).val * Jinv).transpose
  have determines (A : Matrix.SpecialLinearGroup (Fin n) R) (B : Matrix (Fin n) (Fin n) R)
      (h : B.transpose * J * A.val = J) : B = other A := by
    have eq := congrArg (fun X : Matrix (Fin n) (Fin n) R => X * (A⁻¹).val * Jinv) h
    rw [Matrix.mul_assoc (B.transpose * J) A.val (A⁻¹).val, hinv, Matrix.mul_one,
      Matrix.mul_assoc B.transpose J Jinv, hJi, Matrix.mul_one] at eq
    simpa only [other, Matrix.transpose_transpose] using congrArg Matrix.transpose eq
  constructor
  · intro X Y h
    let A := Matrix.SpecialLinearGroup.map firstFactor X.val
    have hx : (X.val.val.map secondFactor).transpose * J * A.val = J :=
      (split_preserves_iff H.val hH X.val).1 X.property
    have hy : (Y.val.val.map secondFactor).transpose * J * A.val = J := by
      change Matrix.SpecialLinearGroup.map firstFactor X.val =
        Matrix.SpecialLinearGroup.map firstFactor Y.val at h
      change (Y.val.val.map secondFactor).transpose * J *
        (Matrix.SpecialLinearGroup.map firstFactor X.val).val = J
      rw [h]
      exact (split_preserves_iff H.val hH Y.val).1 Y.property
    exact Subtype.ext (Subtype.ext (matrix_eq_of_factors (congrArg Subtype.val h)
      ((determines A (X.val.val.map secondFactor) hx).trans
        (determines A (Y.val.val.map secondFactor) hy).symm)))
  · intro A
    let B := other A
    let coef := Equiv.ofBijective (fun z : R ⊗[F] E => (firstFactor z, secondFactor z))
      scalarFactors_bijective
    let X : Matrix (Fin n) (Fin n) (R ⊗[F] E) := Matrix.of fun i j => coef.symm (A.val i j, B i j)
    have hX (i j : Fin n) : (firstFactor (X i j), secondFactor (X i j)) = (A.val i j, B i j) :=
      coef.apply_symm_apply _
    have ha : X.map firstFactor = A.val := Matrix.ext fun i j => congrArg Prod.fst (hX i j)
    have hb : X.map secondFactor = B := Matrix.ext fun i j => congrArg Prod.snd (hX i j)
    have hdB : B.det = 1 := by
      change (J * (A⁻¹).val * Jinv).transpose.det = 1
      rw [Matrix.det_transpose, Matrix.det_conj_of_mul_eq_one hJi hiJ]
      exact (A⁻¹).property
    have hd : X.det = 1 := by
      apply scalarFactors_bijective.1
      apply Prod.ext
      · change firstFactor X.det = firstFactor 1
        rw [map_one, RingHom.map_det]
        change (X.map firstFactor).det = 1
        rw [ha]
        exact A.property
      · change secondFactor X.det = secondFactor 1
        rw [map_one, RingHom.map_det]
        change (X.map secondFactor).det = 1
        rw [hb]
        exact hdB
    let Y : Matrix.SpecialLinearGroup (Fin n) (R ⊗[F] E) := ⟨X, hd⟩
    have he : PreservesHermitianMatrix σ H.val (CommAlgCat.of F R) Y := by
      apply (split_preserves_iff H.val hH Y).2
      change (X.map secondFactor).transpose * J * X.map firstFactor = J
      rw [ha, hb]
      change (J * (A⁻¹).val * Jinv).transpose.transpose * J * A.val = J
      rw [Matrix.transpose_transpose, Matrix.mul_assoc (J * (A⁻¹).val) Jinv J, hiJ,
        Matrix.mul_one, Matrix.mul_assoc J (A⁻¹).val A.val, hinv', Matrix.mul_one]
    exact ⟨⟨Y, he⟩, Subtype.ext ha⟩

end SplitCoefficientAlgebra

private def factorAt (R : TestAlgebra E) : (restrictTestAlgebraObj F E R ⊗[F] E) →+* R :=
  letI : Algebra F R := (restrictTestAlgebraObj F E R).algebra
  letI : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq' rfl
  firstFactor

private theorem firstFactor_natural {R S : TestAlgebra E} (a : R ⟶ S)
    (z : (restrictTestAlgebraObj F E R) ⊗[F] E) :
    factorAt S (Algebra.TensorProduct.map ((restrictTestAlgebra F E).map a).hom
      (AlgHom.id F E) z) = a.hom (factorAt R z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r c =>
    change a.hom r * algebraMap E S c = a.hom (r * algebraMap E R c)
    rw [map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

private def unitarySplitPoints {n : ℕ} (H : (Matrix (Fin n) (Fin n) E)ˣ)
    (hH : adjointMatrix (σ).toRingHom H.val = H.val) {G : AffineAlgebraicGroup F}
    (model : RepresentsHermitian σ H.val G) :
    SpecialMatrixPoints (baseChangedAlgebraicGroup E G) n := by
  let point := Classical.choose model
  have comparison := Classical.choose_spec model
  let f (R : TestAlgebra E) : GroupPoints G.val (restrictTestAlgebraObj F E R) →*
      Matrix.SpecialLinearGroup (Fin n) R :=
    (Matrix.SpecialLinearGroup.map (factorAt R)).comp
      (MonoidHom.mk' (fun x => (point (restrictTestAlgebraObj F E R) x).val) (comparison.1 _))
  let e (R : TestAlgebra E) : GroupPoints G.val (restrictTestAlgebraObj F E R) ≃*
      Matrix.SpecialLinearGroup (Fin n) R := by
    letI : Algebra F R := (restrictTestAlgebraObj F E R).algebra
    letI : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq' rfl
    exact MulEquiv.ofBijective (f R)
      ((split_special_unitary_bijective (R := R) H hH).comp (point _).bijective)
  refine baseChangePointIso G.val ≪≫ NatIso.ofComponents
    (fun R => ((e R).trans (liftSpecialLinear n)).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro x
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change factorAt S ((point _ (mapPoints ((restrictTestAlgebra F E).map a) x)).val.val i.down j.down) =
    a.hom (factorAt R ((point _ x).val.val i.down j.down))
  rw [comparison.2 ((restrictTestAlgebra F E).map a) x]
  exact firstFactor_natural a ((point _ x).val.val i.down j.down)

private theorem hermitian_isReductive {n : ℕ} (hn : 0 < n)
    (H : (Matrix (Fin n) (Fin n) E)ˣ) (hH : adjointMatrix (σ).toRingHom H.val = H.val)
    {G : AffineAlgebraicGroup F} (M : RepresentsHermitian σ H.val G) : IsReductive G := by
  let GE := baseChangedAlgebraicGroup E G
  let split := unitarySplitPoints H hH M
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hsem : IsSemisimple GE := by
    have hs : SpecialMatrixPoints GE n := split
    rw [hm] at hs
    exact RootData.SpecialLinearDatum.semisimple E m GE hs
  let := hsem.2.1
  have hsm : Smooth G.val.X.hom := (smooth_baseChange_iff (K := E) G.val.X).mp hsem.1
  have hconn : ConnectedSpace G.val.X.left := (connected_baseChange_iff (K := E) G).mp
    (GeometricallyConnected.connectedSpace_of_subsingleton (f := GE.val.X.hom))
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := E) G hsm
    (geometricallyConnected_of_connected G)).mp (reductive_of_semisimple GE hsem)

end HermitianReductivity

section RationalPoints

open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open private testPointSections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity

variable {F E I : Type u} [Field F] [Field E] [Algebra F E] [Fintype I] [DecidableEq I]
  {G : AffineAlgebraicGroup F} {σ : E ≃ₐ[F] E} {H : Matrix I I E}

private abbrev groundTest (F : Type u) [Field F] : TestAlgebra F := CommAlgCat.of F F

private def generatedTestPoints (G : AffineAlgebraicGroup F) :
    Subgroup (GroupPoints G.val (groundTest F)) :=
  (unipotentGenerated G).map (testPointSections G.val).symm.toMonoidHom

private theorem rationalMember_mem (x : GroupPoints G.val (groundTest F))
    (hx : RationalMember G x) : x ∈ generatedTestPoints G := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨s, hs, ?_⟩
  change (rationalSourceIso F).inv ≫ s = x
  exact (congrArg (· ≫ s) (toUnit_unique _ _)).trans hsx

private theorem subgroup_eq_top_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (S : Subgroup A) (h : ∀ b, b ∈ S.map e.toMonoidHom) : S = ⊤ := by
  apply (Subgroup.eq_top_iff' S).2
  intro a
  obtain ⟨x, hx, he⟩ := h (e a)
  exact e.injective he ▸ hx

private theorem unipotentGenerated_eq_top (h : ∀ x, x ∈ generatedTestPoints G) :
    unipotentGenerated G = ⊤ :=
  subgroup_eq_top_of_equiv (testPointSections G.val).symm (unipotentGenerated G) h

private abbrev groundCoefficients (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Coeff E (groundTest F) ≃+* E := (Algebra.TensorProduct.lid F E).toRingEquiv

private theorem ground_conjugation (x : Coeff E (groundTest F)) :
    groundCoefficients F E (conjugation σ (groundTest F) x) =
      σ (groundCoefficients F E x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp [conjugation, Algebra.TensorProduct.lid_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem ground_preserves_iff (X : Matrix I I (Coeff E (groundTest F))) :
    Preserves σ H X ↔
      let Y := X.map (groundCoefficients F E)
      adjointMatrix (σ).toRingHom Y * H * Y = H := by
  let a := groundCoefficients F E
  have hgram : (gram H (groundTest F)).map a = H := by
    ext i j
    change (Algebra.TensorProduct.lid F E) ((1 : F) ⊗ₜ[F] H i j) = _
    simp
  have hconj : (adjointMatrix (conjugation σ (groundTest F)).toRingHom X).map a =
      adjointMatrix (σ).toRingHom (X.map a) := by
    exact Matrix.ext (fun i j => ground_conjugation (σ := σ) (X j i))
  have hinj : Function.Injective (fun X : Matrix I I (Coeff E (groundTest F)) => X.map a) :=
    fun _ _ h => Matrix.ext fun i j => a.injective (congrFun (congrFun h i) j)
  change adjointMatrix (conjugation σ (groundTest F)).toRingHom X * gram H (groundTest F) * X =
    gram H (groundTest F) ↔ _
  rw [← hinj.eq_iff, Matrix.map_mul, Matrix.map_mul, hgram, hconj]

private def groundMatrix (M : Model G σ H) :
    GroupPoints G.val (groundTest F) →* Matrix.SpecialLinearGroup I E :=
  (Matrix.SpecialLinearGroup.map (groundCoefficients F E).toRingHom).comp (matrixHom M _)

private theorem groundMatrix_injective (M : Model G σ H) :
    Function.Injective (groundMatrix M) := by
  intro x y h
  apply matrix_injective M
  ext i j
  exact (groundCoefficients F E).injective (congrArg (fun a => a.val i j) h)

private theorem groundMatrix_preserves (M : Model G σ H) (x : GroupPoints G.val (groundTest F)) :
    adjointMatrix (σ).toRingHom (groundMatrix M x).val * H * (groundMatrix M x).val = H :=
  (ground_preserves_iff (M.matrix x)).1 (matrix_preserves M x)

private theorem groundMatrix_preimage (M : Model G σ H) (X : Matrix.SpecialLinearGroup I E)
    (hX : adjointMatrix (σ).toRingHom X.val * H * X.val = H) :
    ∃ x, groundMatrix M x = X := by
  let a := groundCoefficients F E
  let Z := Matrix.SpecialLinearGroup.map a.symm.toRingHom X
  have he : Z.val.map a = X.val := Matrix.ext fun i j => a.apply_symm_apply (X.val i j)
  obtain ⟨x, hx⟩ := matrix_preimage M Z.val Z.property
    ((ground_preserves_iff (σ := σ) (H := H) Z.val).2 (he.symm ▸ hX))
  exact ⟨x, Subtype.ext ((congrArg (fun A : Matrix I I (Coeff E (groundTest F)) => A.map a) hx).trans he)⟩

private theorem unitriangular_map_iff {C D : Type*} [CommRing C] [CommRing D] (a : C →+* D)
    (ha : Function.Injective a) (e f : I) (X : Matrix I I C) :
    Unitriangular e f (X.map a) ↔ Unitriangular e f X := by
  have hzero : zeroWeight e f (X.map a) = (zeroWeight e f X).map a := by
    ext i j
    by_cases h : weight e f i = weight e f j <;> simp [zeroWeight, h]
  have hinj : Function.Injective (fun X : Matrix I I C => X.map a) :=
    fun _ _ h => Matrix.ext fun i j => ha (congrFun (congrFun h i) j)
  unfold Unitriangular Regular
  rw [hzero, ← Matrix.map_one a (map_zero _) (map_one _), hinj.eq_iff]
  simp only [Matrix.map_apply, map_eq_zero_iff a ha]

private theorem unitriangular_of_entries {C : Type*} [Semiring C] {e f : I}
    (hef : e ≠ f) (A : Matrix I I C)
    (hcol : ∀ i, A i e = (1 : Matrix I I C) i e)
    (hrow : ∀ j, A f j = (1 : Matrix I I C) f j)
    (hmiddle : ∀ i j, i ≠ e → i ≠ f → j ≠ e → j ≠ f → A i j = (1 : Matrix I I C) i j) :
    Unitriangular e f A := by
  have heq (i j : I) (h : weight e f i ≤ weight e f j) : A i j = (1 : Matrix I I C) i j := by
    by_cases hje : j = e
    · subst j
      exact hcol i
    by_cases hif : i = f
    · subst i
      exact hrow j
    by_cases hie : i = e
    · by_cases hjf : j = f <;> simp [weight, hie, hje, hjf, hef.symm] at h
    by_cases hjf : j = f
    · simp [weight, hie, hif, hjf, hef.symm] at h
    exact hmiddle i j hie hif hje hjf
  constructor
  · intro i j hij
    rw [heq i j hij.le, Matrix.one_apply_ne (ne_of_apply_ne _ hij.ne)]
  · ext i j
    by_cases hw : weight e f i = weight e f j
    · simpa only [zeroWeight, ite_eq_left hw] using heq i j hw.le
    · simp only [zeroWeight, ite_eq_right hw, Matrix.one_apply_ne (ne_of_apply_ne _ hw)]

end RationalPoints

section AdaptedBasis

open Module (Basis)
open Specs.HermitianMatrixGeneration (radicalGenerators specialUnitary upperAction lowerAction)

variable {F E I W : Type u} [Field F] [Field E] [Algebra F E] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module E W] {σ : E ≃ₐ[F] E}

private structure AdaptedBasis (b : Basis I E (Space E W)) (e f : I) : Prop where
  distinct : e ≠ f
  first : b e = (1, 0, 0)
  last : b f = (0, 0, 1)
  middle : ∀ i, i ≠ e → i ≠ f → ∃ w : W, b i = (0, w, 0)

private theorem first_coordinate {b : Basis I E (Space E W)} {e f : I}
    (hb : AdaptedBasis b e f) (i : I) : (b i).1 = if i = e then 1 else 0 := by
  by_cases he : i = e
  · simp [he, hb.first]
  by_cases hf : i = f
  · simp [hf, hb.last, hb.distinct.symm]
  obtain ⟨w, hw⟩ := hb.middle i he hf
  simp [hw, he]

private theorem last_coordinate {b : Basis I E (Space E W)} {e f : I}
    (hb : AdaptedBasis b e f) (i : I) : (b i).2.2 = if i = f then 1 else 0 := by
  by_cases hf : i = f
  · simp [hf, hb.last]
  by_cases he : i = e
  · simp [he, hb.first, hb.distinct]
  obtain ⟨w, hw⟩ := hb.middle i he hf
  simp [hw, hf]

private theorem repr_first {b : Basis I E (Space E W)} {e f : I}
    (hb : AdaptedBasis b e f) (x : Space E W) : b.repr x e = x.1 := by
  have he : b.coord e = LinearMap.fst E E (W × E) :=
    b.ext fun i => by
      simpa only [Basis.coord_apply, Basis.repr_self_apply, LinearMap.fst_apply] using
        (first_coordinate hb i).symm
  exact LinearMap.congr_fun he x

private theorem repr_last {b : Basis I E (Space E W)} {e f : I}
    (hb : AdaptedBasis b e f) (x : Space E W) : b.repr x f = x.2.2 := by
  have hf : b.coord f = (LinearMap.snd E W E).comp (LinearMap.snd E E (W × E)) :=
    b.ext fun i => by
      simpa only [Basis.coord_apply, Basis.repr_self_apply, LinearMap.comp_apply,
        LinearMap.snd_apply] using (last_coordinate hb i).symm
  exact LinearMap.congr_fun hf x

private theorem gram_of_adapted_basis {h : HermitianForm (W := W) σ}
    {b : Basis I E (Space E W)} {e f : I} (hb : AdaptedBasis b e f) {H : Matrix I I E}
    (hcoords : ∀ x y, matrixPairing (σ).toRingHom H (b.equivFun x) (b.equivFun y) =
      hyperbolicPairing h x y) : HyperbolicPair H e f := by
  have hbasis (i : I) : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  have hent (i j : I) : H i j = hyperbolicPairing h (b i) (b j) := by
    simpa only [hbasis, matrixPairing_entry] using hcoords (b i) (b j)
  have hzero (x : W) : h.pairing x 0 = 0 := (h.linear x).map_zero
  have hzero' (x : W) : h.pairing 0 x = 0 := by rw [← h.hermitian, hzero, map_zero]
  refine ⟨hb.distinct, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hent, hb.first]
    simpa [hyperbolicPairing, hzero'] using last_coordinate hb j
  · intro j
    rw [hent, hb.last]
    simpa [hyperbolicPairing, hzero'] using first_coordinate hb j
  · intro i
    rw [hent, hb.first]
    simp [hyperbolicPairing, hzero, last_coordinate hb i, apply_ite]
  · intro i
    rw [hent, hb.last]
    simp [hyperbolicPairing, hzero, first_coordinate hb i, apply_ite]

private theorem generators_unitriangular {h : HermitianForm (W := W) σ}
    {b : Basis I E (Space E W)} {e f : I} (hb : AdaptedBasis b e f)
    {g : Space E W ≃ₗ[E] Space E W} (hg : g ∈ radicalGenerators h) :
    let X := LinearMap.toMatrix b b g.toLinearMap
    Unitriangular e f X ∨ Unitriangular f e X := by
  let X := LinearMap.toMatrix b b g.toLinearMap
  change Unitriangular e f X ∨ Unitriangular f e X
  have entry (i j : I) : X i j = b.repr (g (b j)) i := LinearMap.toMatrix_apply b b _ i j
  have one_entry (i j : I) : (1 : Matrix I I E) i j = b.repr (b j) i := by
    rw [Matrix.one_apply, Basis.repr_self_apply]
    by_cases h : i = j
    · subst j
      rfl
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h)]
  obtain ⟨z, a, _, hu | hl⟩ := hg
  · refine Or.inl (unitriangular_of_entries hb.distinct X ?_ ?_ ?_)
    · intro i
      rw [entry, one_entry, hu, hb.first]
      simp [upperAction, show h.pairing z 0 = 0 from (h.linear z).map_zero]
    · intro j
      rw [entry, one_entry, repr_last hb, repr_last hb, hu]
      rfl
    · intro i j hie hif hje hjf
      obtain ⟨w, hw⟩ := hb.middle j hje hjf
      have eq : g (b j) = b j + (-h.pairing z w) • b e := by
        simp [hu, hw, hb.first, upperAction]
      rw [entry, one_entry, eq]
      simp [hie.symm]
  · refine Or.inr (unitriangular_of_entries hb.distinct.symm X ?_ ?_ ?_)
    · intro i
      rw [entry, one_entry, hl, hb.last]
      simp [lowerAction, show h.pairing z 0 = 0 from (h.linear z).map_zero]
    · intro j
      rw [entry, one_entry, repr_first hb, repr_first hb, hl]
      rfl
    · intro i j hif hie hjf hje
      obtain ⟨w, hw⟩ := hb.middle j hje hjf
      have eq : g (b j) = b j + (-h.pairing z w) • b f := by
        simp [hl, hw, hb.last, lowerAction]
      rw [entry, one_entry, eq]
      simp [hif.symm]

private theorem preserves_iff_isometry {h : HermitianForm (W := W) σ}
    {b : Basis I E (Space E W)} {H : Matrix I I E}
    (hcoords : ∀ x y, matrixPairing (σ).toRingHom H (b.equivFun x) (b.equivFun y) =
      hyperbolicPairing h x y) (g : Space E W ≃ₗ[E] Space E W) :
    let X := LinearMap.toMatrix b b g.toLinearMap
    adjointMatrix (σ).toRingHom X * H * X = H ↔
      ∀ x y, hyperbolicPairing h (g x) (g y) = hyperbolicPairing h x y := by
  dsimp only
  rw [matrixPairing_isometry_iff]
  have hmul (x : Space E W) : LinearMap.toMatrix b b g.toLinearMap *ᵥ b.equivFun x =
      b.equivFun (g x) := LinearMap.toMatrix_mulVec_repr b b g.toLinearMap x
  constructor
  · intro hg x y
    simpa only [hmul, hcoords] using hg (b.equivFun x) (b.equivFun y)
  · intro hg x y
    obtain ⟨x, rfl⟩ := b.equivFun.surjective x
    obtain ⟨y, rfl⟩ := b.equivFun.surjective y
    simpa only [hmul, hcoords] using hg x y

private def linearMatrixAction (b : Basis I E (Space E W)) (A : Matrix.SpecialLinearGroup I E) :
    Space E W ≃ₗ[E] Space E W :=
  LinearEquiv.ofIsUnitDet (v := b) (v' := b) (f := Matrix.toLin b b A.val) (by
    rw [LinearMap.toMatrix_toLin, A.property]
    exact isUnit_one)

private theorem linearMatrixAction_toMatrix (b : Basis I E (Space E W))
    (A : Matrix.SpecialLinearGroup I E) :
    LinearMap.toMatrix b b (linearMatrixAction b A).toLinearMap = A.val := by
  rw [linearMatrixAction, LinearEquiv.coe_ofIsUnitDet, LinearMap.toMatrix_toLin]

private def linearMatrixRepresentation (b : Basis I E (Space E W)) :
    Matrix.SpecialLinearGroup I E →* (Space E W ≃ₗ[E] Space E W) :=
  MonoidHom.mk' (linearMatrixAction b) (fun A D => by
    apply LinearEquiv.toLinearMap_injective
    apply (LinearMap.toMatrix b b).injective
    change LinearMap.toMatrix b b (linearMatrixAction b (A * D)).toLinearMap =
      LinearMap.toMatrix b b ((linearMatrixAction b A).toLinearMap * (linearMatrixAction b D).toLinearMap)
    rw [LinearMap.toMatrix_mul, linearMatrixAction_toMatrix, linearMatrixAction_toMatrix,
      linearMatrixAction_toMatrix]
    rfl)

private theorem linearMatrixRepresentation_injective (b : Basis I E (Space E W)) :
    Function.Injective (linearMatrixRepresentation b) := by
  intro A D h
  apply Subtype.ext
  rw [← linearMatrixAction_toMatrix b A, ← linearMatrixAction_toMatrix b D]
  exact congrArg (fun g : Space E W ≃ₗ[E] Space E W => LinearMap.toMatrix b b g.toLinearMap) h

private theorem linearMatrixAction_of_toMatrix (b : Basis I E (Space E W))
    (g : Space E W ≃ₗ[E] Space E W) (hdet : (LinearMap.toMatrix b b g.toLinearMap).det = 1) :
    linearMatrixAction b ⟨LinearMap.toMatrix b b g.toLinearMap, hdet⟩ = g := by
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrix b b).injective
  rw [linearMatrixAction_toMatrix]

end AdaptedBasis

section AdaptedGeneration

open Module (Basis)
open Spec (hyperbolicComparison hyperbolicMatrix)
open Specs.HermitianMatrixGeneration (radicalGenerators specialUnitary)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)

variable {F E I : Type u} [Field F] [Field E] [Algebra F E] [Fintype I] [DecidableEq I]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  {G : AffineAlgebraicGroup F}

local notation "σ" => quadraticConjugation F E

private theorem unitriangular_in_generated (H : (Matrix I I E)ˣ)
    (hH : adjointMatrix (σ).toRingHom H.val = H.val) (e f : I) (hp : HyperbolicPair H.val e f)
    (hG : GeometricRadicals.IsReductive G) (M : Model G σ H.val)
    (x : GroupPoints G.val (groundTest F))
    (hx : Unitriangular e f (M.matrix x) ∨ Unitriangular f e (M.matrix x)) :
    x ∈ generatedTestPoints G := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hradical⟩ :=
    HermitianRadicalComparison.radicalComparison σ (quadraticConjugation_ne_one F E)
      (fun a => conj_conj a) H hH e f hp G hG M
  exact rationalMember_mem x (hradical x hx)

private theorem generateWithComplement [Infinite F] {W : Type u}
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] [Nontrivial W]
    (h : HermitianForm (W := W) σ) (hn : h.Nondegenerate)
    (b : Basis I E (Space E W)) {e f : I} (hb : AdaptedBasis b e f)
    (H : (Matrix I I E)ˣ) (hH : adjointMatrix (σ).toRingHom H.val = H.val)
    (hcoords : ∀ x y, matrixPairing (σ).toRingHom H.val (b.equivFun x) (b.equivFun y) =
      hyperbolicPairing h x y)
    (hG : GeometricRadicals.IsReductive G) (M : Model G σ H.val) : unipotentGenerated G = ⊤ := by
  let act := (linearMatrixRepresentation b).comp (groundMatrix M)
  have hinj : Function.Injective act :=
    (linearMatrixRepresentation_injective b).comp (groundMatrix_injective M)
  let P := (generatedTestPoints G).map act
  have hp := gram_of_adapted_basis hb hcoords
  have hgen : radicalGenerators h ⊆ P := by
    intro g hg
    have hs := (HermitianMatrixGeneration.unitriangularCoordinates h g).mp hg
    have hd : (LinearMap.toMatrix b b g.toLinearMap).det = 1 := by
      rw [LinearMap.det_toMatrix, ← LinearEquiv.coe_det, hs.1.1]
      rfl
    let X : Matrix.SpecialLinearGroup I E := ⟨LinearMap.toMatrix b b g.toLinearMap, hd⟩
    obtain ⟨x, hx⟩ := groundMatrix_preimage M X ((preserves_iff_isometry hcoords g).2 hs.1.2)
    have htri : Unitriangular e f (groundMatrix M x).val ∨ Unitriangular f e (groundMatrix M x).val :=
      hx.symm ▸ generators_unitriangular hb hg
    have transfer (i j : I) : Unitriangular i j (groundMatrix M x).val ↔
        Unitriangular i j (M.matrix x) :=
      unitriangular_map_iff (groundCoefficients F E).toRingHom (groundCoefficients F E).injective
        i j (M.matrix x)
    exact ⟨x, unitriangular_in_generated H hH e f hp hG M x
      (htri.imp (transfer e f).1 (transfer f e).1), by
        change linearMatrixAction b (groundMatrix M x) = g
        rw [hx, linearMatrixAction_of_toMatrix]⟩
  have href : ∀ A ∈ h.unitaryGroup, A ∈ Subgroup.closure h.reflections := by
    rw [hermitianReflectionGeneration h hn]
    exact fun _ hA => hA
  have hfull := HermitianMatrixGeneration.hermitianMatrixGeneration h hn href
  have hcontain : specialUnitary h ≤ P := hfull ▸ (Subgroup.closure_le P).2 hgen
  apply unipotentGenerated_eq_top
  intro x
  have hX : LinearMap.toMatrix b b (act x).toLinearMap = (groundMatrix M x).val :=
    linearMatrixAction_toMatrix b (groundMatrix M x)
  have hx : act x ∈ specialUnitary h := by
    constructor
    · apply Units.ext
      rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b, hX]
      exact (groundMatrix M x).property
    · apply (preserves_iff_isometry hcoords _).1
      rw [hX]
      exact groundMatrix_preserves M x
  obtain ⟨y, hy, hxy⟩ := hcontain hx
  exact hinj hxy ▸ hy

private theorem finTwo_orientation {i j : Fin 2} (hij : i ≠ j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp_all

private theorem finTwo_covers {i j : Fin 2} (hij : i ≠ j) (k : ULift.{u} (Fin 2)) :
    k = ULift.up i ∨ k = ULift.up j := by
  obtain ⟨k⟩ := k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

set_option maxHeartbeats 300000 in
private theorem generateHyperbolicPlane
    (H : (Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) E)ˣ)
    (hH : adjointMatrix (σ).toRingHom H.val = H.val)
    (hp : HyperbolicPair H.val (ULift.up 0) (ULift.up 1))
    (hG : GeometricRadicals.IsReductive G) (M : Model G σ H.val) : unipotentGenerated G = ⊤ := by
  let R := groundTest F
  let C := Coeff E R
  let small := Matrix.reindexRingEquiv C (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2)
  let J := hyperbolicMatrix C
  have hdet (X : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) C) : (small X).det = X.det :=
    Matrix.det_reindex_self _ X
  have hgram : small (gram H.val R) = J := by
    ext i j
    fin_cases i <;> fin_cases j
    · change coefficientInclusion R (H.val (ULift.up 0) (ULift.up 0)) = 0
      rw [hp.row_e]
      simp
    · change coefficientInclusion R (H.val (ULift.up 0) (ULift.up 1)) = 1
      rw [hp.row_e, ite_eq_left rfl, map_one]
    · change coefficientInclusion R (H.val (ULift.up 1) (ULift.up 0)) = 1
      rw [hp.row_f, ite_eq_left rfl, map_one]
    · change coefficientInclusion R (H.val (ULift.up 1) (ULift.up 1)) = 0
      rw [hp.row_f]
      simp
  have hpres (X : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) C) : Preserves σ H.val X ↔
      ((small X).map (Spec.conjugationAt (R := F) σ)).transpose * J * small X = J := by
    have hc : small ((X.map (conjugation σ R)).transpose) =
        ((small X).map (Spec.conjugationAt (R := F) σ)).transpose := rfl
    unfold Preserves
    rw [← small.injective.eq_iff, map_mul, map_mul, hc, hgram]
  have hmul (x y : GroupPoints G.val R) :
      small (M.matrix (x * y)) = small (M.matrix x) * small (M.matrix y) := by
    rw [show M.matrix (x * y) = M.matrix x * M.matrix y from congrArg Subtype.val (M.mul R x y), map_mul]
  obtain ⟨α, _, hc, _⟩ := hyperbolicSpecialUnitary (F := F) (E := E)
  obtain ⟨_, _, hcmp_mul, hcmp, hzero, hone⟩ := hc F
  let cmp := hyperbolicComparison (F := F) (R := F) α
  let Lifts (B : Matrix.SpecialLinearGroup (Fin 2) F) : Prop :=
    ∃ x : GroupPoints G.val R, x ∈ generatedTestPoints G ∧ small (M.matrix x) = cmp B.val
  have htrans (i j : Fin 2) (hij : i ≠ j) (a : F) :
      Lifts (Matrix.SpecialLinearGroup.transvection hij a) := by
    let B : Matrix.SpecialLinearGroup (Fin 2) F := Matrix.SpecialLinearGroup.transvection hij a
    let X := small.symm (cmp B.val)
    have hX : small X = cmp B.val := small.apply_symm_apply _
    have hB := (hcmp (cmp B.val)).2 ⟨B.val, B.property, rfl⟩
    obtain ⟨x, hx⟩ := matrix_preimage M X (by rw [← hdet, hX]; exact hB.1)
      ((hpres X).2 (hX.symm ▸ hB.2))
    have hsmall : small (M.matrix x) = cmp B.val := (congrArg small hx).trans hX
    have hentry (k l : Fin 2) : M.matrix x (ULift.up k) (ULift.up l) = cmp B.val k l :=
      congrFun (congrFun hsmall k) l
    have hd (k : Fin 2) : M.matrix x (ULift.up k) (ULift.up k) = 1 := by
      rw [hentry]
      apply (hone B.val k).2
      change ((1 : Matrix (Fin 2) (Fin 2) F) + Matrix.single i j a) k k = 1
      rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne i j a k k
        (fun ⟨hi, hj⟩ => hij (hi.trans hj.symm)), add_zero]
    have hz : M.matrix x (ULift.up j) (ULift.up i) = 0 := by
      rw [hentry]
      apply (hzero B.val j i).2
      change ((1 : Matrix (Fin 2) (Fin 2) F) + Matrix.single i j a) j i = 0
      rw [Matrix.add_apply, Matrix.one_apply_ne hij.symm,
        Matrix.single_apply_of_row_ne hij j i a, add_zero]
    have hne : ULift.up i ≠ (ULift.up j : ULift.{u} (Fin 2)) :=
      fun h => hij (congrArg ULift.down h)
    have ht : Unitriangular (ULift.up i) (ULift.up j) (M.matrix x) := by
      refine unitriangular_of_entries hne (M.matrix x) ?_ ?_
        (fun k _ hki hkj _ _ => ((finTwo_covers hij k).elim hki hkj).elim)
      · intro k
        rcases finTwo_covers hij k with rfl | rfl
        · rw [hd, Matrix.one_apply_eq]
        · rw [hz, Matrix.one_apply_ne hne.symm]
      · intro k
        rcases finTwo_covers hij k with rfl | rfl
        · rw [hz, Matrix.one_apply_ne hne.symm]
        · rw [hd, Matrix.one_apply_eq]
    refine ⟨x, unitriangular_in_generated H hH _ _ hp hG M x ?_, hsmall⟩
    rcases finTwo_orientation hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact Or.inl (by simpa only [hi, hj] using ht)
    · exact Or.inr (by simpa only [hi, hj] using ht)
  have hproduct (A B : Matrix.SpecialLinearGroup (Fin 2) F) (hA : Lifts A) (hB : Lifts B) :
      Lifts (A * B) := by
    obtain ⟨x, hx, hAx⟩ := hA
    obtain ⟨y, hy, hBy⟩ := hB
    refine ⟨x * y, (generatedTestPoints G).mul_mem hx hy, ?_⟩
    rw [hmul, hAx, hBy]
    exact (hcmp_mul A.val B.val).symm
  apply unipotentGenerated_eq_top
  intro x
  obtain ⟨B, hB, hBx⟩ := (hcmp (small (M.matrix x))).1
    ⟨(hdet _).trans (M.point R x).val.property, (hpres _).1 (matrix_preserves M x)⟩
  obtain ⟨y, hy, hBy⟩ := Matrix.SL2.transvection_induction Lifts htrans hproduct ⟨B, hB⟩
  exact matrix_injective M (small.injective (hBy.trans hBx)) ▸ hy

end AdaptedGeneration

section LocalGeneration

open Module (Basis)
open Spec (HermitianLocalGeneration)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)

variable {F E I W : Type u} [Field F] [Field E] [Algebra F E] [Fintype I] [DecidableEq I]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  [AddCommGroup W] [Module E W] {G : AffineAlgebraicGroup F}

local notation "σ" => quadraticConjugation F E

private theorem adaptedModel {n : ℕ} (H : (Matrix (Fin n) (Fin n) E)ˣ)
    (hH : adjointMatrix (σ).toRingHom H.val = H.val) (M : RepresentsHermitian σ H.val G)
    (h : HermitianForm (W := W) σ) (c : Space E W ≃ₗ[E] (Fin n → E))
    (hc : ∀ x y, matrixPairing (σ).toRingHom H.val (c x) (c y) = hyperbolicPairing h x y)
    (b : Basis I E (Space E W)) :
    ∃ (H' : (Matrix I I E)ˣ) (_ : Model G σ H'.val),
      adjointMatrix (σ).toRingHom H'.val = H'.val ∧
      ∀ x y, matrixPairing (σ).toRingHom H'.val (b.equivFun x) (b.equivFun y) =
        hyperbolicPairing h x y := by
  let d := b.equivFun.symm.trans c
  let T := LinearMap.toMatrix' d.toLinearMap
  let U := LinearMap.toMatrix' d.symm.toLinearMap
  have hTU : T * U = 1 := matricesOfEquiv_mul d
  have hUT : U * T = 1 := matricesOfEquiv_mul d.symm
  refine ⟨changedGram (σ).toRingHom H T U hTU hUT, modelInBasis M T U hTU hUT,
    changedGram_hermitian (σ).toRingHom (fun a => conj_conj a) H hH T U hTU hUT, ?_⟩
  intro x y
  change matrixPairing (σ).toRingHom (adjointMatrix (σ).toRingHom T * H.val * T)
    (b.equivFun x) (b.equivFun y) = _
  rw [matrixPairing_change]
  simpa only [T, d, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] using hc x y

private def planeBasis [Subsingleton W] : Basis (ULift.{u} (Fin 2)) E (Space E W) :=
  letI : Unique W := uniqueOfSubsingleton 0
  ((Basis.finTwoProd E).map ((LinearEquiv.refl E E).prodCongr
    (LinearEquiv.uniqueProd (R := E) (M₂ := W) (M := E)).symm)).reindex Equiv.ulift.symm

private theorem planeBasis_adapted [Subsingleton W] :
    AdaptedBasis (planeBasis (E := E) (W := W)) (ULift.up 0) (ULift.up 1) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp [planeBasis, Basis.finTwoProd_zero]
    exact Subsingleton.elim _ _
  · simp [planeBasis, Basis.finTwoProd_one]
    exact Subsingleton.elim _ _
  · rintro ⟨j⟩ h0 h1
    fin_cases j <;> contradiction

private def basisWithComplement [FiniteDimensional E W] :
    Basis (ULift.{u} (Fin 2 ⊕ Fin (Module.finrank E W))) E (Space E W) :=
  let p : ((E × E) × W) ≃ₗ[E] Space E W :=
    (LinearEquiv.prodAssoc E E E W).trans ((LinearEquiv.refl E E).prodCongr
      (LinearEquiv.prodComm E E W))
  (((Basis.finTwoProd E).prod (Module.finBasis E W)).map p).reindex Equiv.ulift.symm

private theorem basisWithComplement_adapted [FiniteDimensional E W] :
    AdaptedBasis (basisWithComplement (E := E) (W := W)) (ULift.up (Sum.inl 0))
      (ULift.up (Sum.inl 1)) := by
  refine ⟨fun h => (show (0 : Fin 2) ≠ 1 by decide) (Sum.inl.inj (congrArg ULift.down h)),
    ?_, ?_, ?_⟩
  · simp [basisWithComplement, Basis.finTwoProd_zero]
  · simp [basisWithComplement, Basis.finTwoProd_one]
  · rintro ⟨j | j⟩ h0 h1
    · fin_cases j <;> contradiction
    · exact ⟨Module.finBasis E W j, by simp [basisWithComplement]⟩

/-- An isotropic Hermitian special unitary group is generated on rational
points by the unipotent radicals of its parabolics. -/
theorem hermitianLocalGeneration : HermitianLocalGeneration.{u} := by
  intro F E _ _ _ _ _ _ n H
  dsimp only
  rintro hH ⟨e, he, hee⟩ G hmodel
  have hpos : 0 < n := by
    by_contra! hzero
    have hn : n = 0 := by omega
    subst n
    exact he (funext fun i => Fin.elim0 i)
  have hG := hermitian_isReductive hpos H hH hmodel
  let h := formOfMatrix H.val hH
  have hn : h.Nondegenerate := formOfMatrix_nondegenerate H hH
  obtain ⟨f, hef, hff⟩ := hyperbolicPartner h e he hee hn
  obtain ⟨hn', c, _, hc⟩ := HermitianMatrixGeneration.hyperbolicCoordinates h e f hee hff hef
  let P := h.hyperbolicComplement e f
  let hP := h.restrict P
  rcases subsingleton_or_nontrivial P with hzero | hnonzero
  · let : Subsingleton P := hzero
    let b := planeBasis (E := E) (W := P)
    have hb := planeBasis_adapted (E := E) (W := P)
    obtain ⟨B, M, hB, hcoords⟩ := adaptedModel H hH hmodel hP c hc b
    exact generateHyperbolicPlane B hB (gram_of_adapted_basis hb hcoords) hG M
  · let : Nontrivial P := hnonzero
    let b := basisWithComplement (E := E) (W := P)
    have hb := basisWithComplement_adapted (E := E) (W := P)
    obtain ⟨B, M, hB, hcoords⟩ := adaptedModel H hH hmodel hP c hc b
    exact generateWithComplement hP (hn' hn) b hb B hB hcoords hG M

end LocalGeneration

end HermitianGroups

section Approximation

open LinearAlgebraicGroups.Specs
open CocharacterDynamics (existsLimitDecomposition oppositeCocharacter)

/-- Local density at the completions implies the adelic assertion through
the fixed pair of global parabolics. -/
theorem strongApproximationOfLocalDensity : StrongApproximationOfLocalDensity.{u,v} := by
  intro localDensity K _ D G hG htype hiso i S hS
  obtain ⟨c, hc⟩ := hiso
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨Q⟩ :=
    existsLimitDecomposition G (oppositeCocharacter c)
  obtain ⟨_, _, _, _, happrox⟩ := OppositeRadicals.approximation D G i hG c hc P Q
  exact (happrox S hS).2 (fun w => localDensity D G hG htype ⟨c, hc⟩ i w.1)

open CategoryTheory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open Specs.Arithmetic.OppositeRadicals (IsNoncentral localPlus)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.OuterTypeAModels (DiagramField)
open private quadraticAut from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private noncentral_extend globalField_infinite completionPointEquiv completionPointEquiv_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

set_option maxHeartbeats 800000 in
set_option linter.style.haveILetI false in
/-- At each completion the rational parabolic radicals generate a dense subgroup. -/
theorem outerTypeALocalDensity : OuterTypeALocalDensity.{u,v} := by
  intro K _ D G hG htype hiso i w
  obtain ⟨r, hr, _, S, s, L, _, _, _, _, iso, χ, g, hχ, hg⟩ := htype
  obtain ⟨_, _, _, _, hdeg, hsep, ρ, _, hA, _, star, _, _, I, _, b, hU, hlocal⟩ :=
    OuterTypeALocalModels.localModelsForTrivialization.{u,v}
      (show 3 ≤ r + 1 by omega) s iso χ g hg hχ
  letI : Algebra.IsQuadraticExtension K (DiagramField χ) := ⟨hdeg⟩
  letI : Algebra.IsSeparable K (DiagramField χ) := hsep
  let F := D.Completion w
  let G' := baseChangedAlgebraicGroup F G
  letI : Infinite K := globalField_infinite D
  letI : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  obtain ⟨c, hc⟩ := hiso
  obtain ⟨P⟩ := existsLimitDecomposition G c
  obtain ⟨e, _⟩ := gm_baseChange K F
  have hco : ∃ c' : Specs.CharacterDescent.Cocharacter G'.val, IsNoncentral c' :=
    ⟨e.hom ≫ (groupBaseChange K F).map c, noncentral_extend hc P.centralizer_points e⟩
  rcases hlocal D w with hns | hs
  · obtain ⟨Q, _, _, _, _, hdim, τ, H, hτ, _, hH, _, hmodel, hi⟩ := hns
    letI : Algebra.IsQuadraticExtension F Q := ⟨hdim⟩
    have heq : τ = quadraticConjugation F Q :=
      (quadraticAut τ).resolve_left hτ
    subst τ
    have hall := hermitianLocalGeneration H hH (hi (Or.inl ⟨c, hc⟩)) G' hmodel
    have hset : localPlus D i w = Set.univ := by
      ext x
      constructor
      · exact fun _ => Set.mem_univ x
      · intro _
        obtain ⟨p, hp⟩ := (completionPointEquiv D i w).surjective x
        refine ⟨p, ?_, ?_⟩
        · rw [hall]
          exact Subgroup.mem_top p
        · exact (completionPointEquiv_apply D i w p).symm.trans hp
    rw [hset]
    exact dense_univ
  · obtain ⟨j, _⟩ := hs
    letI : Algebra (DiagramField χ) F := j.toRingHom.toAlgebra
    letI : IsScalarTower K (DiagramField χ) F := IsScalarTower.of_algebraMap_eq'
      j.comp_algebraMap.symm
    exact IsotropicNormOneRadicalsDensity.splitCentreCompletionDensity
      hA b star hU D i w hco

/-- Every globally isotropic simply connected outer form of type A satisfies
strong approximation outside every finite nonempty set of places. -/
theorem outerTypeAStrongApproximation : OuterTypeAStrongApproximation.{u,v} :=
  strongApproximationOfLocalDensity outerTypeALocalDensity

end Approximation

end LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
