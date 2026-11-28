import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.RankOneVermas
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.Category
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightExactness
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2Model
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalRootsA
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Semisimple.Basic

noncomputable section

namespace RepTheorySurvey.CategoryO.RankOneVermas

open Module UniversalEnvelopingAlgebra
open scoped ModuleCat.Algebra TensorProduct
open Specs.RepTheorySurvey.CategoryO.RankOneVermas
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA (cartan root coroot rootVector)
open LieAlgebrasAndRepresentations (sl2_h_val sl2_e_val sl2_f_val sl2_relations sl2_simple)
open LieAlgebrasAndRepresentations.ClassicalRootsA
  (cartan_isCartan root_set root_space rootVector_mem rootVector_ne_zero killing_coroot root_apply)

local notation "H₀" => cartan 1
local notation "r₊" => root 1 0 1
local notation "r₋" => root 1 1 0
local notation "h₀" => coroot 1 0 1

private theorem coroot_coe : (h₀ : G) = h := rfl

private def direction : Direction H₀ :=
  Complex.reLm.comp ((Module.Dual.eval ℂ H₀ h₀).restrictScalars ℝ)

local notation "Φ" => direction

private theorem direction_pos : Φ r₊ = 2 := by
  change (r₊ h₀).re = 2
  rw [root_apply]
  change ((h : G).val 0 0 - (h : G).val 1 1).re = 2
  norm_num [sl2_h_val]

private theorem direction_neg : Φ r₋ = -2 := by
  change (r₋ h₀).re = -2
  rw [root_apply]
  change ((h : G).val 1 1 - (h : G).val 0 0).re = -2
  norm_num [sl2_h_val]

private theorem root_cases {a : Module.Dual ℂ H₀}
    (ha : a ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value H₀) :
    a = r₊ ∨ a = r₋ := by
  obtain ⟨i, j, hij, rfl⟩ := (root_set 1 a).mp ha
  fin_cases i <;> fin_cases j <;> first | contradiction | exact Or.inl rfl | exact Or.inr rfl

private theorem regular : Regular H₀ Φ := by
  intro a ha
  rcases root_cases ha with rfl | rfl
  · rw [direction_pos]
    norm_num
  · rw [direction_neg]
    norm_num

private theorem simple_eq (i : Specs.LieAlgebrasAndRepresentations.SerreRelations.simple H₀ Φ) :
    i.val = r₊ := by
  rcases root_cases i.property.1.1 with ha | ha
  · exact ha
  · have hp : 0 < Φ i.val := i.property.1.2
    rw [ha, direction_neg] at hp
    norm_num at hp

private theorem root_neg : -r₊ = r₋ := by
  ext x
  simp [root_apply, neg_sub]

private def standardTriple :
    ∀ i : Specs.LieAlgebrasAndRepresentations.SerreRelations.simple H₀ Φ,
      RootTriple H₀ i.val := fun i => {
  e := e
  f := f
  e_mem := by
    rw [simple_eq i]
    exact rootVector_mem (n := 1) 0 1 (by decide)
  f_mem := by
    rw [simple_eq i, root_neg]
    exact rootVector_mem (n := 1) 1 0 (by decide)
  e_ne_zero := rootVector_ne_zero (n := 1) 0 1 (by decide)
  f_ne_zero := rootVector_ne_zero (n := 1) 1 0 (by decide)
  lie_e_f := by
    rw [simple_eq i, killing_coroot 1 0 1 (by decide), coroot_coe]
    exact (sl2_relations ℂ).2.2
  lie_h_e := by
    rw [simple_eq i, killing_coroot 1 0 1 (by decide), coroot_coe]
    exact (sl2_relations ℂ).1
  lie_h_f := by
    rw [simple_eq i, killing_coroot 1 0 1 (by decide), coroot_coe]
    exact (sl2_relations ℂ).2.1 }

/-- The finite-category setup for the standard matrix realization. -/
def matrixSetup : Setup G where
  semisimple := by
    let := sl2_simple ℂ
    exact LieAlgebra.HasTrivialRadical.radical_eq_bot
  cartan := H₀
  isCartan := cartan_isCartan 1
  direction := Φ
  regular := regular
  triple := standardTriple

private theorem root_space_eq_bot_of_sign
    {a : Module.Dual ℂ H₀}
    (hne : Φ a ≠ 0)
    (ha : a ∉ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value H₀) :
    Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value H₀ a = ⊥ := by
  by_contra hr
  exact ha ⟨fun hz => hne (hz ▸ map_zero Φ), hr⟩

theorem matrixSetup_standard : IsStandard matrixSetup := by
  have hp := (root_parts matrixSetup).1
  have hn := (root_parts matrixSetup).2
  change _ = ⨆ a : {a : Module.Dual ℂ H₀ // 0 < Φ a},
    Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value H₀ a.val at hp
  change _ = ⨆ a : {a : Module.Dual ℂ H₀ // Φ a < 0},
    Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value H₀ a.val at hn
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have hr : _ = ℂ ∙ e := root_space 1 0 1 (by decide)
    rw [hp, ← hr]
    refine le_antisymm (iSup_le fun a => ?_) (le_iSup_of_le ⟨r₊, by rw [direction_pos]; norm_num⟩ le_rfl)
    by_cases ha : a.val ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value H₀
    · rcases root_cases ha with he | he
      · rw [he]
      · have hs := a.property
        rw [he, direction_neg] at hs
        norm_num at hs
    · rw [root_space_eq_bot_of_sign (ne_of_gt a.property) ha]
      exact bot_le
  · have hr : _ = ℂ ∙ f := root_space 1 1 0 (by decide)
    rw [hn, ← hr]
    refine le_antisymm (iSup_le fun a => ?_) (le_iSup_of_le ⟨r₋, by rw [direction_neg]; norm_num⟩ le_rfl)
    by_cases ha : a.val ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value H₀
    · rcases root_cases ha with he | he
      · have hs := a.property
        rw [he, direction_pos] at hs
        norm_num at hs
      · rw [he]
    · rw [root_space_eq_bot_of_sign (ne_of_lt a.property) ha]
      exact bot_le
  · intro i
    refine ⟨rfl, rfl, ?_⟩
    change (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H₀ i.val : G) = h
    rw [simple_eq i, killing_coroot 1 0 1 (by decide), coroot_coe]

theorem standard_setup : standard_setup_type :=
  ⟨matrixSetup, matrixSetup_standard⟩

section Verma

variable (D : Setup G) (std : IsStandard D)

include std in
private theorem diagonal_expansion (x : D.cartan) :
    (x : G) = x.val.val 0 0 • h := by
  have hd : (x : G) ∈ H₀ := std.cartan ▸ x.property
  have hx01 := hd (show (0 : Fin 2) ≠ 1 by decide)
  have hx10 := hd (show (1 : Fin 2) ≠ 0 by decide)
  simpa only [hx01, hx10, zero_smul, zero_add] using
    LieAlgebrasAndRepresentations.sl2_expansion ℂ (x : G)

private def cartanH : D.cartan :=
  ⟨h, std.cartan.symm ▸ (show h ∈ H₀ from (h₀).property)⟩

private theorem weight_at_h (lam : ℂ) : weight D lam (cartanH D std) = lam := by
  change lam * (h : G).val 0 0 = lam
  simp [sl2_h_val]

theorem weight_parameter : weight_parameter_type := by
  intro D std
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    simpa only [weight_at_h D std] using congrArg (fun μ : D.Weight => μ (cartanH D std)) hab
  · intro μ
    refine ⟨μ (cartanH D std), LinearMap.ext fun x => ?_⟩
    have hx : x = x.val.val 0 0 • cartanH D std := Subtype.ext (diagonal_expansion D std x)
    change μ (cartanH D std) * x.val.val 0 0 = μ x
    conv_rhs => rw [hx, map_smul]
    exact mul_comm _ _
  · intro x hx lam
    have he : x = cartanH D std := Subtype.ext hx
    rw [he, weight_at_h D std]

private def lower : D.nMinus :=
  ⟨f, show f ∈ D.nMinus.toSubmodule by
    rw [std.negative]
    exact Submodule.mem_span_singleton_self f⟩

private theorem lower_ne_zero : lower D std ≠ 0 := by
  intro he
  exact rootVector_ne_zero (n := 1) 1 0 (by decide) (congrArg Subtype.val he)

private def lowerBasis : Basis (Fin 1) ℂ D.nMinus :=
  Basis.mk
    ((linearIndependent_unique_iff).mpr (lower_ne_zero D std) :
      LinearIndependent ℂ (fun _ : Fin 1 => lower D std))
    (by
      rw [Set.range_const]
      intro x _
      have hx : (x : G) ∈ ℂ ∙ f := std.negative ▸ x.property
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc⟩)

private theorem lowerBasis_apply (i : Fin 1) :
    lowerBasis D std i = lower D std := by
  simp only [lowerBasis, Basis.mk_apply]

open Shared.Lie.PBW (OrderedWord orderedBasis orderedMonomial monomial monomial_cons monomial_nil)

private def orderedLength : OrderedWord (Fin 1) ≃ ℕ where
  toFun w := w.val.length
  invFun n := ⟨List.replicate n 0, List.pairwise_replicate.mpr (Or.inr le_rfl)⟩
  left_inv _w := Subtype.ext ((List.eq_replicate_length.mpr fun i _ => Subsingleton.elim i 0).symm)
  right_inv _n := List.length_replicate

private theorem monomial_replicate (n : ℕ) :
    monomial (lowerBasis D std) (List.replicate n 0) = (ι ℂ (lower D std)) ^ n := by
  induction n with
  | zero => simp [monomial_nil]
  | succ n ih =>
    rw [List.replicate_succ, monomial_cons, ih, lowerBasis_apply, pow_succ']

include std in
private theorem basis_exists (lam : ℂ) :
    ∃ b : Basis ℕ ℂ (Verma D lam), ∀ j, b j = loweringPower D lam j := by
  let χ := character D (weight D lam)
  obtain ⟨E, hE, _⟩ := LieAlgebrasAndRepresentations.VermaModules.induced_free
    D.semisimple D.cartan D.direction D.regular χ
  refine ⟨((orderedBasis (lowerBasis D std)).map E).reindex orderedLength, ?_⟩
  intro j
  change ((orderedBasis (lowerBasis D std)).map E).reindex orderedLength j =
    (ι ℂ f : U G) ^ j • highest D lam
  rw [Basis.reindex_apply, Basis.map_apply, Shared.Lie.PBW.orderedBasis_apply]
  change E (monomial (lowerBasis D std) (List.replicate j 0)) = _
  rw [monomial_replicate, hE, map_pow]
  have he : envelopingMap D.nMinus.incl (ι ℂ (lower D std)) = (ι ℂ f : U G) := by
    rw [envelopingMap, lift_ι_apply]
    rfl
  rw [he]
  rfl

open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
  (inducedLieRingModule inducedLieModule)
open LieAlgebrasAndRepresentations.VermaWeightsUniversal (verma_weights)

local instance (D : Setup G) (lam : ℂ) : LieRingModule G (Verma D lam) :=
  inducedLieRingModule D.cartan D.direction (character D (weight D lam))

local instance (D : Setup G) (lam : ℂ) : LieModule ℂ G (Verma D lam) :=
  inducedLieModule D.cartan D.direction (character D (weight D lam))

private theorem lie_verma {lam : ℂ} (x : G) (v : Verma D lam) :
    ⁅x, v⁆ = (ι ℂ x : U G) • v := rfl

include std in
private theorem smul_h_highest (lam : ℂ) :
    (ι ℂ h : U G) • highest D lam = lam • highest D lam := by
  have hc := (character_unique D (weight D lam)).1
  obtain ⟨_, _, _, hline⟩ := verma_weights D.semisimple D.cartan D.direction D.regular
    (weight D lam) (character D (weight D lam)) hc
  have hm : highest D lam ∈ weightSpace D.cartan (Verma D lam) (weight D lam) := by
    change weightSpace D.cartan (Verma D lam) (weight D lam) = ℂ ∙ highest D lam at hline
    rw [hline]
    exact Submodule.mem_span_singleton_self _
  have he := (mem_weightSpace D.cartan (Verma D lam) (weight D lam) (highest D lam)).mp hm
    (cartanH D std)
  rwa [weight_at_h D std] at he

open private tensorClass_eq_smul from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

include std in
private theorem smul_e_highest (lam : ℂ) :
    (ι ℂ e : U G) • highest D lam = 0 := by
  let χ := character D (weight D lam)
  let x : D.nPlus := ⟨e, show e ∈ D.nPlus.toSubmodule by
    rw [std.positive]
    exact Submodule.mem_span_singleton_self e⟩
  let xb := LieSubalgebra.inclusion (show D.nPlus ≤ D.borel from le_sup_right) x
  have hb := LieAlgebrasAndRepresentations.VermaModules.tensor_balanced D.cartan D.direction χ
    1 (ι ℂ xb) 1
  have hχ : χ (ι ℂ xb) = 0 := (character_unique D (weight D lam)).1.2 x
  have hx : envelopingMap D.borel.incl (ι ℂ xb) = (ι ℂ e : U G) := by
    rw [envelopingMap, lift_ι_apply]
    rfl
  rw [one_mul, hχ, zero_mul, hx] at hb
  change (ι ℂ e : U G) • highestVector_value D.cartan D.direction χ = 0
  rw [← tensorClass_eq_smul]
  change _ = (balance D.cartan D.direction χ).mkQ ((1 : U G) ⊗ₜ[ℂ] (0 : ℂ)) at hb
  simpa only [TensorProduct.tmul_zero, map_zero] using hb

private theorem standardSl2Triple : IsSl2Triple h e f where
  h_ne_zero := by
    intro hz
    have h00 := congrArg (fun x : G => x.val 0 0) hz
    norm_num [sl2_h_val] at h00
  lie_e_f := (sl2_relations ℂ).2.2
  lie_h_e_nsmul := by simpa only [two_smul] using (sl2_relations ℂ).1
  lie_h_f_nsmul := by
    simpa only [neg_smul, two_smul, ← Nat.cast_ofNat (R := ℤ) (n := 2), natCast_zsmul]
      using (sl2_relations ℂ).2.1

include std in
private theorem primitive (lam : ℂ) :
    standardSl2Triple.HasPrimitiveVectorWith (highest D lam) lam where
  ne_zero := (LieAlgebrasAndRepresentations.VermaModules.induced_free
    D.semisimple D.cartan D.direction D.regular (character D (weight D lam))).choose_spec.2
  lie_h := smul_h_highest D std lam
  lie_e := smul_e_highest D std lam

private theorem pow_toEnd (lam : ℂ) (j : ℕ) :
    (LieModule.toEnd ℂ G (Verma D lam) f ^ j) (highest D lam) = loweringPower D lam j := by
  induction j with
  | zero => simp [loweringPower]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change (ι ℂ f : U G) • loweringPower D lam j = loweringPower D lam (j + 1)
    simp only [loweringPower, pow_succ', mul_smul]

include std in
private theorem h_action (lam : ℂ) (j : ℕ) :
    (ι ℂ h : U G) • loweringPower D lam j = (lam - 2 * j) • loweringPower D lam j := by
  simpa only [pow_toEnd D, lie_verma D] using (primitive D std lam).lie_h_pow_toEnd_f j

include std in
private theorem e_action (lam : ℂ) (j : ℕ) :
    (ι ℂ e : U G) • loweringPower D lam (j + 1) =
      ((j + 1 : ℂ) * (lam - j)) • loweringPower D lam j := by
  simpa only [pow_toEnd D, lie_verma D] using (primitive D std lam).lie_e_pow_succ_toEnd_f j

include std in
private theorem power_weight (lam : ℂ) (j : ℕ) :
    loweringPower D lam j ∈ weightSpace D.cartan (Verma D lam) (weight D (lam - 2 * j)) := by
  apply (mem_weightSpace D.cartan (Verma D lam) _ _).mpr
  intro x
  rw [diagonal_expansion D std x, map_smul, smul_assoc, h_action D std, smul_smul]
  change (x.val.val 0 0 * (lam - 2 * j)) • _ = ((lam - 2 * j) * x.val.val 0 0) • _
  rw [mul_comm]

theorem pbw_basis : pbw_basis_type :=
  fun D std lam => ⟨basis_exists D std lam, power_weight D std lam⟩

include std in
private theorem power_weight_injective (lam : ℂ) :
    Function.Injective (fun j : ℕ => weight D (lam - 2 * j)) := by
  intro j k he
  have he' := congrArg (fun a : D.Weight => a (cartanH D std)) he
  simp only [weight_at_h D std] at he'
  have hcast : (j : ℂ) = (k : ℂ) := by linear_combination -he' / 2
  exact_mod_cast hcast

private def weightFiber (lam : ℂ) (μ : D.Weight) : Set (Verma D lam) :=
  loweringPower D lam '' {j : ℕ | weight D (lam - 2 * j) = μ}

include std in
private theorem fiber_span (lam : ℂ) :
    (fun μ => Submodule.span ℂ (weightFiber D lam μ)) =
      WeightExactness.weightSpace (Verma D lam) (H := D.cartan) := by
  classical
  let F := fun μ => Submodule.span ℂ (weightFiber D lam μ)
  have hle : F ≤ WeightExactness.weightSpace (Verma D lam) (H := D.cartan) := by
    intro μ
    apply Submodule.span_le.mpr
    rintro _ ⟨j, (hj : weight D (lam - 2 * j) = μ), rfl⟩
    rw [← hj]
    exact power_weight D std lam j
  obtain ⟨b, hb⟩ := basis_exists D std lam
  have htop : iSup F = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [hb]
    exact Submodule.mem_iSup_of_mem (weight D (lam - 2 * j))
      (Submodule.subset_span ⟨j, rfl, rfl⟩)
  exact (iSupIndep.le_iff_eq_of_iSup_eq_top WeightExactness.weightSpaces_independent htop).mp hle

include std in
private theorem submodule_le_of_powers {lam : ℂ} {S T : Submodule (U G) (Verma D lam)}
    (hST : ∀ j : ℕ, loweringPower D lam j ∈ S → loweringPower D lam j ∈ T) : S ≤ T := by
  classical
  let Sₕ : LieSubmodule ℂ D.cartan (Verma D lam) :=
    ((submoduleOrderIso (Verma D lam)) S).restr D.cartan
  have hint : WeightExactness.IsWeightModule (H := D.cartan) (Verma D lam) :=
    (verma_weights D.semisimple D.cartan D.direction D.regular (weight D lam)
      (character D (weight D lam)) (character_unique D (weight D lam)).1).1
  have hs := (WeightExactness.stableSubspace (H := D.cartan) (X := Verma D lam) Sₕ hint).2.2
  have hs' : (⨆ μ : D.Weight, S.restrictScalars ℂ ⊓ Submodule.span ℂ (weightFiber D lam μ)) =
      S.restrictScalars ℂ := by
    simp_rw [congrFun (fiber_span D std lam)]
    exact hs
  change S.restrictScalars ℂ ≤ T.restrictScalars ℂ
  rw [← hs']
  apply iSup_le
  intro μ x hx
  by_cases hF : (weightFiber D lam μ).Nonempty
  · obtain ⟨_, j, (hj : weight D (lam - 2 * j) = μ), rfl⟩ := hF
    have hf : weightFiber D lam μ = {loweringPower D lam j} := by
      ext y
      simp only [weightFiber, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [power_weight_injective D std lam (hk.trans hj.symm)]
      · rintro rfl
        exact ⟨j, hj, rfl⟩
    have hxS : x ∈ S.restrictScalars ℂ := hx.1
    have hxF : x ∈ Submodule.span ℂ (weightFiber D lam μ) := hx.2
    rw [hf] at hxF
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxF
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact (T.restrictScalars ℂ).zero_mem
    · exact (T.restrictScalars ℂ).smul_mem _ (hST j
        (((S.restrictScalars ℂ).smul_mem_iff hc).mp hxS))
  · have hxF : x ∈ Submodule.span ℂ (weightFiber D lam μ) := hx.2
    rw [Set.not_nonempty_iff_eq_empty.mp hF, Submodule.span_empty, Submodule.mem_bot] at hxF
    rw [hxF]
    exact (T.restrictScalars ℂ).zero_mem

include std in
private theorem power_ne_zero (lam : ℂ) (j : ℕ) : loweringPower D lam j ≠ 0 := by
  obtain ⟨b, hb⟩ := basis_exists D std lam
  rw [← hb]
  exact b.ne_zero j

private theorem power_mem_of_le {lam : ℂ} (S : Submodule (U G) (Verma D lam))
    {j k : ℕ} (hj : loweringPower D lam j ∈ S) (hjk : j ≤ k) :
    loweringPower D lam k ∈ S := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  change (ι ℂ f : U G) ^ (j + n) • highest D lam ∈ S
  rw [Nat.add_comm, pow_add, mul_smul]
  exact S.smul_mem _ hj

include std in
private theorem proper_submodule (lam : ℂ) (S : Submodule (U G) (Verma D lam))
    (hn : S ≠ ⊥) (hp : S ≠ ⊤) :
    ∃ m : ℕ, lam = (m : ℂ) ∧
      S = Submodule.span (U G) ({loweringPower D lam (m + 1)} : Set (Verma D lam)) := by
  classical
  have hex : ∃ j : ℕ, loweringPower D lam j ∈ S := by
    by_contra! he
    exact hn (le_bot_iff.mp (submodule_le_of_powers D std fun j hj => (he j hj).elim))
  have hmin := Nat.find_spec hex
  have h0 : Nat.find hex ≠ 0 := by
    intro hz
    rw [hz] at hmin
    apply hp
    apply top_unique
    apply submodule_le_of_powers D std
    intro j _
    exact power_mem_of_le D S hmin (Nat.zero_le j)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  change Nat.find hex = m + 1 at hm
  have hs : loweringPower D lam (m + 1) ∈ S := by rwa [hm] at hmin
  have hbelow : loweringPower D lam m ∉ S := by
    apply Nat.find_min hex
    rw [hm]
    exact Nat.lt_succ_self m
  have hcoef : ((m + 1 : ℂ) * (lam - m)) • loweringPower D lam m ∈ S := by
    rw [← e_action D std]
    exact S.smul_mem _ hs
  have hparam : lam = (m : ℂ) := by
    by_contra h
    have hnz : (m + 1 : ℂ) * (lam - m) ≠ 0 := mul_ne_zero
      (by exact_mod_cast Nat.succ_ne_zero m) (sub_ne_zero.mpr h)
    exact hbelow (((S.restrictScalars ℂ).smul_mem_iff hnz).mp hcoef)
  refine ⟨m, hparam, le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr hs)⟩
  apply submodule_le_of_powers D std
  intro j hj
  apply power_mem_of_le D _ (Submodule.mem_span_singleton_self _)
  rw [← hm]
  exact Nat.find_min' hex hj

include std in
private theorem singular_map (m : ℕ) :
    ∃ F : Verma D (-(m : ℂ) - 2) →ₗ[U G] Verma D m,
      F.range = Submodule.span (U G) ({loweringPower D m (m + 1)} : Set (Verma D m)) ∧
      ∀ j : ℕ, F (loweringPower D (-(m : ℂ) - 2) j) = loweringPower D m (j + (m + 1)) := by
  let a := -(m : ℂ) - 2
  let v := loweringPower D m (m + 1)
  let χ := character D (weight D a)
  let J := definingIdeal_value D.cartan D.direction (weight D a) D.e
  obtain ⟨P, hP⟩ := LieAlgebrasAndRepresentations.VermaModules.induced_presentation
    D.semisimple D.cartan D.direction D.regular (weight D a) χ
    (character_unique D (weight D a)).1 D.e
    (fun i => ⟨(D.triple i).e_mem, (D.triple i).e_ne_zero⟩)
  let ev := LinearMap.toSpanSingleton (U G) (Verma D m) v
  have hweight : v ∈ weightSpace D.cartan (Verma D m) (weight D a) := by
    have hw := power_weight D std (m : ℂ) (m + 1)
    have ha : (m : ℂ) - 2 * ((m + 1 : ℕ) : ℂ) = a := by
      simp only [a, Nat.cast_add, Nat.cast_one]
      ring
    rwa [ha] at hw
  have hvh := (mem_weightSpace D.cartan (Verma D m) (weight D a) v).mp hweight
  have hve : (ι ℂ e : U G) • v = 0 := by
    change (ι ℂ e : U G) • loweringPower D m (m + 1) = 0
    rw [e_action D std, sub_self, mul_zero, zero_smul]
  have hJ : J ≤ ev.ker := by
    apply Submodule.span_le.mpr
    rintro _ (⟨x, rfl⟩ | ⟨i, rfl⟩)
    · change ((ι ℂ (x : G) - algebraMap ℂ (U G) (weight D a x)) : U G) • v = 0
      rw [sub_smul, algebraMap_smul, hvh, sub_self]
    · change (ι ℂ (D.e i) : U G) • v = 0
      rw [(std.triple i).1]
      exact hve
  let F : Verma D a →ₗ[U G] Verma D m := (J.liftQ ev hJ).comp P.symm.toLinearMap
  have hFE (u : U G) : F (P (J.mkQ u)) = ev u := by
    change J.liftQ ev hJ (P.symm (P (J.mkQ u))) = ev u
    rw [P.symm_apply_apply]
    rfl
  refine ⟨F, ?_, ?_⟩
  · have hr : F.range = ev.range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨z, rfl⟩ := P.surjective x
        obtain ⟨u, rfl⟩ := J.mkQ_surjective z
        exact ⟨u, (hFE u).symm⟩
      · rintro ⟨u, rfl⟩
        exact ⟨P (J.mkQ u), hFE u⟩
    rw [hr, LinearMap.range_toSpanSingleton]
  · have hv₀ : F (highest D a) = v := by
      have h₁ : P (J.mkQ 1) = highest D a := hP 1
      rw [← h₁, hFE, LinearMap.toSpanSingleton_apply_one]
    intro j
    change F ((ι ℂ f : U G) ^ j • highest D a) = (ι ℂ f : U G) ^ (j + (m + 1)) • highest D m
    rw [map_smul, hv₀, pow_add, mul_smul]
    rfl

theorem integral_submodule : integral_submodule_type := by
  intro D std m
  dsimp only
  let a := -(m : ℂ) - 2
  let S := Submodule.span (U G) ({loweringPower D m (m + 1)} : Set (Verma D m))
  obtain ⟨F, hF, hshift⟩ := singular_map D std m
  obtain ⟨b, hb⟩ := basis_exists D std (m : ℂ)
  obtain ⟨c, hc⟩ := basis_exists D std a
  have hF' (j : ℕ) : F (c j) = b (j + (m + 1)) := by rw [hc, hb, hshift]
  let Fc := F.restrictScalars ℂ
  have hinj : Function.Injective F := by
    change Function.Injective Fc
    apply LinearMap.injective_of_linearIndependent c.span_eq
    have heq : Fc ∘ c = b ∘ (fun j => j + (m + 1)) := funext hF'
    rw [heq]
    exact b.linearIndependent.comp _ (fun _ _ => Nat.add_right_cancel)
  have hs₀ : S ≠ ⊥ := by
    intro hz
    have hm : loweringPower D m (m + 1) ∈ S := Submodule.mem_span_singleton_self _
    rw [hz, Submodule.mem_bot] at hm
    exact power_ne_zero D std _ _ hm
  have hs₁ : S ≠ ⊤ := by
    intro hz
    have hy : b 0 ∈ F.range := by
      rw [hF, show Submodule.span (U G) {loweringPower D m (m + 1)} = S from rfl, hz]
      exact Submodule.mem_top
    obtain ⟨x, hx⟩ := hy
    have hcoord : (b.coord 0).comp Fc = 0 := by
      apply c.ext
      intro j
      change b.coord 0 (F (c j)) = 0
      rw [hF']
      simp [Basis.coord_apply]
    have hzero : b.coord 0 (b 0) = 0 := hx ▸ LinearMap.congr_fun hcoord x
    simp at hzero
  refine ⟨hs₀, hs₁, ?_, ?_⟩
  · intro T hT₀ hT₁
    obtain ⟨k, hmk, hk⟩ := proper_submodule D std _ T hT₀ hT₁
    have he : k = m := by exact_mod_cast hmk.symm
    simpa only [he] using hk
  · let Fs := F.codRestrict S (fun x => by
      change F x ∈ Submodule.span (U G) {loweringPower D m (m + 1)}
      rw [← hF]
      exact LinearMap.mem_range_self F x)
    have hs : Function.Surjective Fs := by
      intro y
      have hy : (y : Verma D m) ∈ F.range := by
        rw [hF]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
    let E := LinearEquiv.ofBijective Fs ⟨fun x y he => hinj (congrArg Subtype.val he), hs⟩
    have hE (j : ℕ) : (E (loweringPower D a j) : Verma D m) =
        loweringPower D m (j + (m + 1)) := hshift j
    refine ⟨E, hE, ?_⟩
    intro E' hE'
    have he : (E'.toLinearMap.restrictScalars ℂ) = E.toLinearMap.restrictScalars ℂ := by
      apply c.ext
      intro j
      apply Subtype.ext
      change (E' (c j) : Verma D m) = (E (c j) : Verma D m)
      rw [hc, hE', hE]
    apply LinearEquiv.ext
    exact fun x => LinearMap.congr_fun he x

theorem simple_iff : simple_iff_type := by
  intro D std lam
  constructor
  · intro hs m hm
    subst lam
    let S := Submodule.span (U G) ({loweringPower D m (m + 1)} : Set (Verma D m))
    have h := integral_submodule D std m
    have := (isSimpleModule_iff (U G) (Verma D (m : ℂ))).mp hs
    exact (eq_bot_or_eq_top S).elim h.1 h.2.1
  · intro h
    apply (isSimpleModule_iff (U G) (Verma D lam)).mpr
    have : Nontrivial (Verma D lam) := ⟨⟨loweringPower D lam 0, 0, power_ne_zero D std lam 0⟩⟩
    apply IsSimpleOrder.of_forall_eq_top
    intro S hS
    by_contra htop
    obtain ⟨m, hm, _⟩ := proper_submodule D std lam S hS htop
    exact h m hm

theorem quotient_kernel : quotient_kernel_type := by
  intro D std
  let q := fun lam => quotientMap D (weight D lam)
  have hq (lam : ℂ) : Function.Surjective (q lam) := quotientMap_surjective D (weight D lam)
  have hqs (lam : ℂ) : IsSimpleModule (U G) (Simple D lam) := simpleQuotient_simple D (weight D lam)
  refine ⟨q, fun lam x => quotientMap_apply D (weight D lam) x, ?_, ?_⟩
  · intro m
    have hker : IsCoatom (q m).ker := (q m).isCoatom_ker_of_surjective (hq m)
    have hne : (q m).ker ≠ ⊥ := by
      intro hz
      have hinj : Function.Injective (q m) := LinearMap.ker_eq_bot.mp hz
      have hs := (LinearEquiv.ofBijective (q m) ⟨hinj, hq m⟩).isSimpleModule_iff.mpr (hqs m)
      exact (simple_iff D std m).mp hs m rfl
    exact (integral_submodule D std m).2.2.1 _ hne hker.1
  · intro lam h
    have := (isSimpleModule_iff (U G) (Verma D lam)).mp ((simple_iff D std lam).mpr h)
    have hker : IsCoatom (q lam).ker := (q lam).isCoatom_ker_of_surjective (hq lam)
    exact ⟨LinearMap.ker_eq_bot.mp ((eq_bot_or_eq_top _).resolve_right hker.1), hq lam⟩

end Verma

end RepTheorySurvey.CategoryO.RankOneVermas
