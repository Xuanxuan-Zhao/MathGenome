import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.AffineSimpleTriples
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestRoot
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring

/-! The highest finite root and the simple triples of the untwisted affine algebra. -/

noncomputable section

universe u

namespace RepTheorySurvey.Affine

open LieAlgebrasAndRepresentations
open LieAlgebrasAndRepresentations.HighestRoot
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open _root_.Specs.RepTheorySurvey.Affine.LoopAlgebra
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces
open _root_.Specs.RepTheorySurvey.Affine.AffineSimpleTriples

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
variable [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]

omit [FiniteDimensional ℂ G] in
private theorem semisimple : LieAlgebrasAndRepresentations.IsSemisimple ℂ G := LieAlgebra.radical_eq_bot

private theorem maximalToral : IsMaximalToral H :=
  RealRootSpace.cartan_isMaximalToral semisimple H

theorem highestFiniteRoot : highestFiniteRoot_type.{u} := by
  intro G _ _ _ _ H _ φ hφ
  let : Nontrivial G := LieAlgebra.IsSimple.nontrivial ℂ G
  exact HighestRoot.highest_root H (maximalToral H) φ hφ

private theorem rootTripleChoice {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) :
    Nonempty (FiniteRootTriple H α) := by
  obtain ⟨e, f, he, hf, he0, hf0, hef, _, _⟩ :=
    exists_root_triple semisimple H (maximalToral H) α hα
  exact ⟨⟨e, f, he, hf, he0, hf0, hef⟩⟩

theorem finiteSimpleTripleChoices : finiteSimpleTripleChoices_type.{u} := by
  classical
  intro G _ _ _ _ H _ φ _ θ hθ
  exact ⟨Classical.choice (rootTripleChoice H hθ.1.1),
    fun i => Classical.choice (rootTripleChoice H i.property.1.1)⟩

private theorem coroot_self {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) :
    α (killingCoroot H α) = 2 := by
  rw [killingCoroot_pairing semisimple H (maximalToral H)]
  exact mul_div_cancel_right₀ _ (rootForm_self_ne_zero semisimple H (maximalToral H) α hα)

private theorem neg_root {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) : -α ∈ rootSet H := by
  obtain ⟨T⟩ := rootTripleChoice H hα
  exact ⟨neg_ne_zero.mpr hα.1, fun h => T.f_ne_zero (by simpa only [h, Submodule.mem_bot] using T.f_mem)⟩

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] in
private theorem monoid_nonneg (φ : Direction H) {α : Module.Dual ℂ H}
    (hα : α ∈ positiveRootMonoid H φ) : 0 ≤ φ α := by
  induction hα using AddSubmonoid.closure_induction with
  | mem a ha => exact ha.1.2.le
  | zero => simp
  | add a b _ _ ha hb => simpa only [map_add] using add_nonneg ha hb

omit [H.IsCartanSubalgebra] in
private theorem highest_no_raise {φ : Direction H} {θ α : Module.Dual ℂ H}
    (hθ : IsHighestFiniteRoot H φ θ) (hα : 0 < φ α) : θ + α ∉ rootSet H := by
  intro hs
  have h := monoid_nonneg H φ (hθ.2 _ hs)
  rw [map_sub, map_add] at h
  linarith

omit [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] in
private theorem rootForm_symm (α β : Module.Dual ℂ H) : rootForm H α β = rootForm H β α :=
  (LieModule.traceForm_isSymm ℂ G G).eq _ _

private theorem rootForm_self_pos {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) :
    0 < (rootForm H α α).re := by
  let R := RealRootSpace.realization semisimple H
  let := (Specs.LieAlgebrasAndRepresentations.RealRootSpace.dualCore H R.killing_positive).toNormedAddCommGroup
  let := InnerProductSpace.ofCore
    (Specs.LieAlgebrasAndRepresentations.RealRootSpace.dualCore H R.killing_positive).toCore
  let a := Specs.LieAlgebrasAndRepresentations.RealRootSpace.rootRestriction H α
  have ha : a ≠ 0 := by
    intro ha
    apply hα.1
    rw [← R.extension_root α hα]
    change Specs.LieAlgebrasAndRepresentations.RealRootSpace.extension H R.killing_positive a = 0
    rw [ha, map_zero]
  have h := congrArg Complex.re (R.root_form_agrees α hα α hα)
  change inner ℝ a a = (rootForm H α α).re at h
  rw [← h]
  exact real_inner_self_pos.mpr ha

private theorem rootForm_reflection {α β : Module.Dual ℂ H} (hα : α ∈ rootSet H) :
    let r := RootStrings.rootReflection H α β
    rootForm H r r = rootForm H β β := by
  dsimp only [RootStrings.rootReflection, Specs.LieAlgebrasAndRepresentations.RootStrings.reflection_value]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hc : β (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H α) = _ :=
    killingCoroot_pairing semisimple H (maximalToral H) α β
  rw [rootForm_symm H α β]
  let d := rootForm H α α
  let c := rootForm H β α
  let z := β (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H α)
  have he : z * d = 2 * c :=
    ((div_eq_iff (rootForm_self_ne_zero semisimple H (maximalToral H) α hα)).mp hc.symm).symm
  change rootForm H β β - z * c - z * (c - z * d) = rootForm H β β
  calc
    _ = rootForm H β β + z * (z * d - 2 * c) := by ring
    _ = _ := by rw [he, sub_self, mul_zero, add_zero]

private theorem rootForm_re_of_coroot {α β : Module.Dual ℂ H} (hα : α ∈ rootSet H)
    {z : ℤ} (hz : β (killingCoroot H α) = (z : ℂ)) :
    2 * (rootForm H β α).re = (z : ℝ) * (rootForm H α α).re := by
  rw [killingCoroot_pairing semisimple H (maximalToral H)] at hz
  have he := (div_eq_iff (rootForm_self_ne_zero semisimple H (maximalToral H) α hα)).mp hz
  simpa [Complex.mul_re] using congrArg Complex.re he

private theorem highest_dominant {φ : Direction H} {θ α : Module.Dual ℂ H}
    (hθ : IsHighestFiniteRoot H φ θ) (hα : α ∈ HighestRoot.positiveRoots H φ) :
    0 ≤ (rootForm H θ α).re := by
  by_cases h : θ = α
  · subst θ
    exact (rootForm_self_pos H hα.1).le
  have hn : θ ≠ -α := by
    intro he
    have hp := hθ.1.2
    rw [he, map_neg] at hp
    linarith [hα.2]
  obtain ⟨p, q, hpq, hstring⟩ :=
    RootStrings.root_string semisimple H (maximalToral H) α θ hα.1 hθ.1.1 h hn
  have hq : q = 0 := by
    by_contra hnq
    apply highest_no_raise H hθ hα.2
    simpa only [one_zsmul] using (hstring 1).2 (by omega)
  have he : 2 * (rootForm H θ α).re = (p : ℝ) * (rootForm H α α).re := by
    have hc : θ (killingCoroot H α) = ((p : ℤ) : ℂ) := by simpa [hq] using hpq
    simpa using rootForm_re_of_coroot H hα.1 hc
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ p from Nat.cast_nonneg p) (rootForm_self_pos H hα.1).le]

theorem highestFiniteRootIsLong : highestFiniteRootIsLong_type.{u} := by
  intro G _ _ _ _ H _ φ _ θ hθ
  let length := fun α : Module.Dual ℂ H => (rootForm H α α).re
  have hfinite := rootSet_finite H (maximalToral H).1
  obtain ⟨b₀, hb₀⟩ := hfinite.exists_maximalFor length (rootSet H) ⟨θ, hθ.1.1⟩
  have hmax (a : Module.Dual ℂ H) (ha : a ∈ rootSet H) : length a ≤ length b₀ :=
    le_of_not_gt fun hn => (not_le_of_gt hn) (hb₀.le_of_le ha hn.le)
  let longest := {a ∈ rootSet H | length a = length b₀}
  obtain ⟨b, hb⟩ := (hfinite.subset (show longest ⊆ rootSet H from fun _ h => h.1)).exists_maximalFor
    φ longest ⟨b₀, hb₀.prop, rfl⟩
  have hbdom (a : Module.Dual ℂ H) (ha : a ∈ HighestRoot.positiveRoots H φ) : 0 ≤ (rootForm H b a).re := by
    obtain ⟨z, hz, _⟩ := RootStrings.coroot_pairing_integral semisimple H (maximalToral H)
      a b ha.1 hb.prop.1
    have hz0 : 0 ≤ z := by
      by_contra! hn
      let r := RootStrings.rootReflection H a b
      have hr : r ∈ longest :=
        ⟨RootStrings.reflection_mem_rootSet semisimple H (maximalToral H) a b ha.1 hb.prop.1,
          (congrArg Complex.re (rootForm_reflection H (β := b) ha.1)).trans hb.prop.2⟩
      have hφr : φ r = φ b - (z : ℝ) * φ a := by
        change φ (b - b (killingCoroot H a) • a) = _
        rw [map_sub, hz]
        have hcast : ((z : ℝ) : ℂ) = (z : ℂ) := by norm_cast
        rw [← hcast]
        change φ b - φ ((z : ℝ) • a) = _
        rw [map_smul, smul_eq_mul]
      have hgt : φ b < φ r := by
        rw [hφr]
        linarith [mul_neg_of_neg_of_pos (show (z : ℝ) < 0 by exact_mod_cast hn) ha.2]
      exact (not_le_of_gt hgt) (hb.le_of_le hr hgt.le)
    have he := rootForm_re_of_coroot H ha.1 hz
    nlinarith [mul_nonneg (show 0 ≤ (z : ℝ) by exact_mod_cast hz0) (rootForm_self_pos H ha.1).le]
  have hd (a : Module.Dual ℂ H) (ha : a ∈ positiveRootMonoid H φ) :
      0 ≤ (rootForm H (θ + b) a).re := by
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha =>
      simpa only [map_add, LinearMap.add_apply, Complex.add_re] using
        add_nonneg (highest_dominant H hθ ha.1) (hbdom a ha.1)
    | zero => rw [map_zero]; exact le_refl 0
    | add a c _ _ ha hc => simpa only [map_add, Complex.add_re] using add_nonneg ha hc
  have h := hd (θ - b) (hθ.2 b hb.prop.1)
  simp only [map_add, LinearMap.add_apply, map_sub, Complex.add_re, Complex.sub_re] at h
  rw [rootForm_symm H b θ] at h
  intro a
  have hba := hmax a.val a.property
  change length a.val ≤ length θ
  have hbb := hb.prop.2
  change length b = length b₀ at hbb
  unfold length at *
  linarith

theorem highestRootNormalization : highestRootNormalization_type.{u} := by
  intro G _ _ _ _ B H _ φ hB hφ θ hθ T
  obtain ⟨h, hh, htwo⟩ := hB.2 ⟨θ, hθ.1.1⟩ (highestFiniteRootIsLong H φ hφ θ hθ)
  have heq (y : H) : B.form (killingCoroot H θ : G) (y : G) = θ y * B.form T.e T.f := by
    rw [← T.lie_e_f, B.invariant, ← lie_skew T.e (y : G),
      (mem_rootSpace H θ T.e).1 T.e_mem y]
    rw [map_neg, neg_neg, map_smul, smul_eq_mul, B.symmetric.eq T.f T.e]
  have h := heq h
  rw [B.symmetric.eq, hh, coroot_self H hθ.1.1, htwo] at h
  have hp : B.form T.e T.f = 1 := by linear_combination -h / 2
  exact ⟨hp, fun y => by rw [heq, hp, mul_one]⟩

open private homogeneousLinear_apply coordinates_homogeneous coordinates_d
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces

section Coordinates

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

private theorem cartan_K (B : InvariantForm L) (H : LieSubalgebra ℂ L) :
    K B ∈ affineCartan_value B H :=
  (cartanK B H).property

private theorem cartan_d (B : InvariantForm L) (H : LieSubalgebra ℂ L) :
    d B ∈ affineCartan_value B H :=
  (cartanD B H).property

private theorem cartan_homogeneous (B : InvariantForm L) (H : LieSubalgebra ℂ L) (x : H) :
    homogeneous B 0 (x : L) ∈ affineCartan_value B H :=
  (cartanIncl B H x).property

private theorem cartanProjection_homogeneous (B : InvariantForm L) (H : LieSubalgebra ℂ L) (x : H) :
    cartanProjection B H ⟨homogeneous B 0 (x : L), cartan_homogeneous B H x⟩ = x := by
  apply Subtype.ext
  change (coordinates B (homogeneous B 0 (x : L))).1.1 0 = x
  rw [coordinates_homogeneous, Finsupp.single_eq_same]

private theorem alphaZero_ne_zero (B : InvariantForm L) (H : LieSubalgebra ℂ L)
    (θ : Module.Dual ℂ H) : alphaZero B H θ ≠ 0 := by
  intro he
  have hf := LinearMap.congr_fun he ⟨d B, cartan_d B H⟩
  change (coordinates B (d B)).2 - θ (cartanProjection B H ⟨d B, cartan_d B H⟩) = 0 at hf
  have hc : cartanProjection B H ⟨d B, cartan_d B H⟩ = 0 := by
    apply Subtype.ext
    change (coordinates B (d B)).1.1 0 = 0
    simp
  rw [hc, coordinates_d, map_zero] at hf
  exact one_ne_zero (by simpa only [sub_zero] using hf)

private theorem extendFiniteRoot_ne_zero (B : InvariantForm L) (H : LieSubalgebra ℂ L)
    {α : Module.Dual ℂ H} (hα : α ≠ 0) : extendFiniteRoot_value B H α ≠ 0 := by
  intro he
  apply hα
  ext x
  have hx := LinearMap.congr_fun he ⟨homogeneous B 0 (x : L), cartan_homogeneous B H x⟩
  change α (cartanProjection B H ⟨homogeneous B 0 (x : L), cartan_homogeneous B H x⟩) = 0 at hx
  rw [cartanProjection_homogeneous] at hx
  exact hx

end Coordinates

private theorem lifted_weight (B : InvariantForm G)
    (α : rootSet H) (m : ℤ) {x : G} (hx : x ∈ rootSpace H α.val) :
    IsAdjointWeightVector B H (extendFiniteRoot_value B H α.val + (m : ℂ) • delta_value B H)
      (homogeneous B m x) :=
  ((realWeightSpace B H α m).1 _).mpr ⟨x, hx, homogeneousLinear_apply B m x⟩

theorem affineSimpleRootWeights : affineSimpleRootWeights_type.{u} := by
  intro G _ _ _ _ B H _ φ _ _ θ hθ T S i
  have hnθ := neg_root H hθ.1.1
  cases i with
  | none =>
    refine ⟨(affineCartan_value B H).sub_mem (cartan_K B H) (cartan_homogeneous B H _),
      alphaZero_ne_zero B H θ, ?_, ?_⟩
    · change IsAdjointWeightVector B H (alphaZero B H θ) (homogeneous B 1 T.f)
      have he := lifted_weight H B ⟨-θ, hnθ⟩ 1 T.f_mem
      convert he using 1
      ext x
      change (delta_value B H x - θ (cartanProjection B H x)) = _
      simp [extendFiniteRoot_value, sub_eq_add_neg, add_comm]
    · change IsAdjointWeightVector B H (-alphaZero B H θ) (homogeneous B (-1) T.e)
      have hf := lifted_weight H B ⟨θ, hθ.1.1⟩ (-1) T.e_mem
      convert hf using 1
      ext x
      change -(delta_value B H x - θ (cartanProjection B H x)) = _
      simp [extendFiniteRoot_value, sub_eq_add_neg, add_comm]
  | some i =>
    have hi : i.val ∈ rootSet H := i.property.1.1
    refine ⟨cartan_homogeneous B H _, extendFiniteRoot_ne_zero B H hi.1, ?_, ?_⟩
    · simpa [affineSimpleRoot, affineSimpleE] using lifted_weight H B ⟨i.val, hi⟩ 0 (S i).e_mem
    · have hf := lifted_weight H B ⟨-i.val, neg_root H hi⟩ 0 (S i).f_mem
      simpa [affineSimpleRoot, affineSimpleF, extendFiniteRoot_value] using hf

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] in
private theorem bracket_eq_zero_of_no_root {a b : Module.Dual ℂ H}
    (hn : a + b ≠ 0) (ha : a + b ∉ rootSet H)
    {x y : G} (hx : x ∈ rootSpace H a) (hy : y ∈ rootSpace H b) : ⁅x, y⁆ = 0 := by
  have hm := rootSpace_bracket H a b x y hx hy
  rwa [rootSpace_eq_bot_of_not_mem H _ hn ha, Submodule.mem_bot] at hm

omit [H.IsCartanSubalgebra] in
private theorem highest_killed {φ : Direction H} {θ a : Module.Dual ℂ H}
    (hθ : IsHighestFiniteRoot H φ θ) (ha : 0 < φ a)
    {x y : G} (hx : x ∈ rootSpace H a) (hy : y ∈ rootSpace H θ) : ⁅x, y⁆ = 0 := by
  rw [← lie_skew x y, neg_eq_zero]
  refine bracket_eq_zero_of_no_root H ?_ (highest_no_raise H hθ ha) hy hx
  intro hz
  have hp := hθ.1.2
  have h := congrArg φ hz
  simp only [map_add, map_zero] at h
  linarith

private theorem lowest_killed {φ : Direction H} {θ a : Module.Dual ℂ H}
    (hθ : IsHighestFiniteRoot H φ θ) (ha : φ a < 0)
    {x y : G} (hx : x ∈ rootSpace H a) (hy : y ∈ rootSpace H (-θ)) : ⁅x, y⁆ = 0 := by
  have he : -(a + -θ) = θ + -a := by abel
  refine bracket_eq_zero_of_no_root H ?_ (fun hb => highest_no_raise H hθ ?_ (he ▸ neg_root H hb)) hx hy
  · intro hz
    have hp := hθ.1.2
    have h := congrArg φ hz
    simp only [map_add, map_neg, map_zero] at h
    linarith
  · simpa only [map_neg] using neg_pos.mpr ha

private theorem simple_mixed {φ : Direction H} (hφ : Regular H φ)
    (S : ∀ i : HighestRoot.simpleRoots H φ, FiniteRootTriple H i.val)
    {i j : HighestRoot.simpleRoots H φ} (hij : i ≠ j) : ⁅(S i).e, (S j).f⁆ = 0 := by
  apply bracket_eq_zero_of_no_root H _ _ (S i).e_mem (S j).f_mem
  · intro hz
    exact hij (Subtype.ext (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)))
  · intro hd
    rcases lt_or_gt_of_ne (hφ _ hd) with hneg | hpos
    · have hnr : -(i.val + -j.val) ∈ HighestRoot.positiveRoots H φ :=
        ⟨neg_root H hd, by simpa only [map_neg] using neg_pos.mpr hneg⟩
      exact j.property.2 _ hnr _ i.property.1 (by abel)
    · exact i.property.2 _ ⟨hd, hpos⟩ _ j.property.1 (by abel)

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] in
private theorem homogeneousBracket_of_ne (B : InvariantForm G) (m n : ℤ) (x y : G)
    (hmn : m ≠ -n) : ⁅homogeneous B m x, homogeneous B n y⁆ = homogeneous B (m + n) ⁅x, y⁆ := by
  rw [homogeneousBracket, ite_eq_right hmn, zero_smul, add_zero]

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] in
private theorem bracket_at_degree_zero (B : InvariantForm G) (m : ℤ) (x y : G) :
    ⁅homogeneous B 0 x, homogeneous B m y⁆ = homogeneous B m ⁅x, y⁆ := by
  rw [homogeneousBracket]
  simp

theorem affineSimpleTripleRelations : affineSimpleTripleRelations_type.{u} := by
  intro G _ _ _ _ B H _ φ hB hφ θ hθ T S
  have hθ2 := coroot_self H hθ.1.1
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | none =>
      simp only [affineSimpleH, affineSimpleE, affineSimpleF, hZero, eZero, fZero, ← affineBracket_eq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hz
        have h := congrArg (fun z => (coordinates B z).1.2) hz
        simp at h
      · rw [homogeneousBracket, ← lie_skew T.f T.e, T.lie_e_f]
        have hpair := (highestRootNormalization B H φ hB hφ θ hθ T).1
        rw [B.symmetric.eq T.f T.e, hpair]
        norm_num
        rw [← homogeneousLinear_apply, map_neg, homogeneousLinear_apply]
        abel
      · rw [sub_lie, centralGenerator, zero_sub, bracket_at_degree_zero,
          (mem_rootSpace H (-θ) T.f).1 T.f_mem, LinearMap.neg_apply, hθ2,
          ← homogeneousLinear_apply, map_smul, homogeneousLinear_apply, neg_smul, neg_neg]
      · rw [sub_lie, centralGenerator, zero_sub, bracket_at_degree_zero,
          (mem_rootSpace H θ T.e).1 T.e_mem, hθ2,
          ← homogeneousLinear_apply, map_smul, homogeneousLinear_apply, neg_smul]
    | some i =>
      have hi : i.val ∈ rootSet H := i.property.1.1
      have hi2 := coroot_self H hi
      simp only [affineSimpleH, affineSimpleE, affineSimpleF, ← affineBracket_eq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hz
        have h := congrArg (fun z => (coordinates B z).1.1 0) hz
        simp only [coordinates_homogeneous, Finsupp.single_eq_same, map_zero, Prod.fst_zero, Finsupp.zero_apply] at h
        have hh : killingCoroot H i.val = 0 := Subtype.ext h
        rw [hh, map_zero] at hi2
        norm_num at hi2
      · rw [bracket_at_degree_zero, (S i).lie_e_f]
      · rw [bracket_at_degree_zero, (mem_rootSpace H _ _).1 (S i).e_mem, hi2,
          ← homogeneousLinear_apply, map_smul, homogeneousLinear_apply]
      · rw [bracket_at_degree_zero, (mem_rootSpace H _ _).1 (S i).f_mem, LinearMap.neg_apply, hi2,
          ← homogeneousLinear_apply, map_smul, homogeneousLinear_apply]
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        simp only [affineSimpleE, affineSimpleF, eZero, ← affineBracket_eq]
        rw [homogeneousBracket_of_ne B 1 0 _ _ (by decide), ← lie_skew T.f (S j).f,
          lowest_killed H hθ (by simpa using neg_lt_zero.mpr j.property.1.2) (S j).f_mem T.f_mem,
          neg_zero, ← homogeneousLinear_apply, map_zero]
    | some i =>
      cases j with
      | none =>
        simp only [affineSimpleE, affineSimpleF, fZero, ← affineBracket_eq]
        rw [bracket_at_degree_zero, highest_killed H hθ i.property.1.2 (S i).e_mem T.e_mem,
          ← homogeneousLinear_apply, map_zero]
      | some j =>
        simp only [affineSimpleE, affineSimpleF, ← affineBracket_eq]
        rw [bracket_at_degree_zero, simple_mixed H hφ S (fun h => hij (congrArg some h)),
          ← homogeneousLinear_apply, map_zero]

section Generation

open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (positive_value negative_value rootPart)
open private positive_le_of_simple
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
open private rootSpace_le_of_nonzero
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations
open private loweringSpan loweringSpan_eq_top
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestRoot
open private Lowered
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestRoot
open private components_induction homogeneous_mem_components side_lie_mem
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] in
private theorem affineLieSpan_eq (B : InvariantForm G) (s : Set (AffineAlgebra B)) :
    affineLieSpan B s = (LieSubalgebra.lieSpan ℂ (AffineAlgebra B) s).toSubmodule := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨LieSubalgebra.subset_lieSpan, ?_⟩
    intro x y hx hy
    rw [← affineBracket_eq]
    exact (LieSubalgebra.lieSpan ℂ (AffineAlgebra B) s).lie_mem hx hy
  · apply le_sInf
    intro P hP
    let A : LieSubalgebra ℂ (AffineAlgebra B) := { P with lie_mem' := fun hx hy => hP.2 hx hy }
    change LieSubalgebra.lieSpan ℂ (AffineAlgebra B) s ≤ A
    exact LieSubalgebra.lieSpan_le.mpr hP.1

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] in
private theorem positive_root_mem {φ : Direction H} {a : Module.Dual ℂ H}
    (ha : 0 < φ a) {x : G} (hx : x ∈ rootSpace H a) : x ∈ positive_value H φ :=
  LieSubalgebra.subset_lieSpan ⟨a, ha, hx⟩

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] in
private theorem negative_eq_positive (φ : Direction H) :
    negative_value H φ = positive_value H (-φ) := by
  unfold negative_value positive_value rootPart
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_Ioi, LinearMap.neg_apply, neg_pos]

private theorem neg_simple {φ : Direction H} {a : Module.Dual ℂ H}
    (ha : a ∈ HighestRoot.simpleRoots H (-φ)) : -a ∈ HighestRoot.simpleRoots H φ := by
  have hpos {b : Module.Dual ℂ H} (hb : b ∈ HighestRoot.positiveRoots H φ) :
      -b ∈ HighestRoot.positiveRoots H (-φ) :=
    ⟨neg_root H hb.1, by simpa only [LinearMap.neg_apply, map_neg, neg_neg] using hb.2⟩
  refine ⟨⟨neg_root H ha.1.1, by simpa only [map_neg, LinearMap.neg_apply] using ha.1.2⟩, ?_⟩
  intro b hb c hc he
  apply ha.2 _ (hpos hb) _ (hpos hc)
  calc
    a = -(-a) := (neg_neg a).symm
    _ = -(b + c) := congrArg Neg.neg he
    _ = -b + -c := by abel

private theorem finiteSide_le (B : InvariantForm G) (φ : Direction H)
    (A : LieSubalgebra ℂ (AffineAlgebra B))
    (h : ∀ i : HighestRoot.simpleRoots H φ, ∃ x ∈ rootSpace H i.val,
      x ≠ 0 ∧ homogeneous B 0 x ∈ A) :
    ∀ x ∈ positive_value H φ, homogeneous B 0 x ∈ A := by
  let P := A.comap (constantIncl B)
  have hP : positive_value H φ ≤ P := by
    apply positive_le_of_simple H φ semisimple (maximalToral H)
    intro i
    obtain ⟨x, hx, hx0, hA⟩ := h i
    exact rootSpace_le_of_nonzero H semisimple (maximalToral H) i.property.1.1 P hx hx0 hA
  exact fun x hx => hP hx

private theorem extremal_degree_mem (B : InvariantForm G) (φ : Direction H)
    (hφ : Regular H φ) (A : LieSubalgebra ℂ (AffineAlgebra B))
    (hfinite : ∀ x ∈ positive_value H φ, homogeneous B 0 x ∈ A)
    (s : ℤ) {μ : Module.Dual ℂ H} {v : G} (hv : v ∈ rootSpace H μ) (hv0 : v ≠ 0)
    (hgen : homogeneous B s v ∈ A)
    (hkill : ∀ α ∈ HighestRoot.positiveRoots H (-φ), ∀ x ∈ rootSpace H α, ⁅x, v⁆ = 0) :
    ∀ x : G, homogeneous B s x ∈ A := by
  have htop := loweringSpan_eq_top semisimple H (maximalToral H) (-φ)
    (fun α hα => by simpa only [LinearMap.neg_apply, neg_ne_zero] using hφ α hα)
    μ v hv hv0 hkill
  intro x
  have hx : x ∈ loweringSpan H (-φ) μ v := by rw [htop]; trivial
  change x ∈ Submodule.span ℂ {z | ∃ γ, Lowered H (-φ) μ v γ z} at hx
  change homogeneousLinear B s x ∈ A
  refine Submodule.span_induction (p := fun z _ => homogeneousLinear B s z ∈ A)
    ?_ (by simp) (fun a b _ _ ha hb => by rw [map_add]; exact A.add_mem ha hb)
    (fun c z _ hz => by rw [map_smul]; exact A.smul_mem c hz) hx
  rintro z ⟨γ, hγ⟩
  induction hγ with
  | base => exact hgen
  | @step α γ y z _ hyφ hy _ ih =>
    have hypos : 0 < φ α := by simpa only [LinearMap.neg_apply, neg_lt_zero] using hyφ
    change homogeneous B s ⁅y, z⁆ ∈ A
    rw [← bracket_at_degree_zero]
    exact A.lie_mem (hfinite y (positive_root_mem H hypos hy)) ih

omit [FiniteDimensional ℂ G] in
private theorem bracket_span_eq_top :
    Submodule.span ℂ {⁅x, y⁆ | (x : G) (y : G)} = ⊤ := by
  have htop : LieAlgebra.derivedSeries ℂ G 1 = ⊤ :=
    (LieAlgebra.IsSimple.eq_bot_or_eq_top _).resolve_left (fun h =>
      LieAlgebra.IsSimple.non_abelian ℂ (L := G)
        ((lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv).mp
          ((LieAlgebra.abelian_iff_derived_one_eq_bot (⊤ : LieIdeal ℂ G)).mpr h)))
  rw [← LieAlgebra.coe_derivedSeries_one_eq, htop]
  rfl

private theorem higher_degree_mem (B : InvariantForm G) (A : LieSubalgebra ℂ (AffineAlgebra B))
    (s : ℤ) (hs : s = 1 ∨ s = -1) (hgen : ∀ x : G, homogeneous B s x ∈ A)
    (m : ℤ) (hm : 0 < s * m) (x : G) : homogeneous B m x ∈ A := by
  have all (k : ℕ) (x : G) : homogeneous B (s * ((k : ℤ) + 1)) x ∈ A := by
    induction k generalizing x with
    | zero => simpa using hgen x
    | succ k ih =>
      have hm : s * ((k.succ : ℤ) + 1) = s + s * ((k : ℤ) + 1) := by push_cast; ring
      have hn : s ≠ -(s * ((k : ℤ) + 1)) := by rcases hs with rfl | rfl <;> simp <;> omega
      rw [hm]
      let P := A.toSubmodule.comap (homogeneousLinear B (s + s * ((k : ℤ) + 1)))
      change x ∈ P
      have hP : Submodule.span ℂ {⁅x, y⁆ | (x : G) (y : G)} ≤ P := by
        apply Submodule.span_le.mpr
        rintro _ ⟨a, b, rfl⟩
        change homogeneous B (s + s * ((k : ℤ) + 1)) ⁅a, b⁆ ∈ A
        rw [← homogeneousBracket_of_ne B s _ a b hn]
        exact A.lie_mem (hgen a) (ih b)
      exact hP (by rw [bracket_span_eq_top]; trivial)
  have he : ((s * m - 1).toNat : ℤ) = s * m - 1 := Int.toNat_of_nonneg (by omega)
  have he' : s * (((s * m - 1).toNat : ℤ) + 1) = m := by
    rw [he, sub_add_cancel]
    rcases hs with rfl | rfl <;> simp
  rw [← he']
  exact all _ x

private def sideGenerators (B : InvariantForm G) (φ : Direction H) (s : ℤ) (v : G)
    (g : HighestRoot.simpleRoots H φ → G) : AffineSimpleIndex H φ → AffineAlgebra B
  | none => homogeneous B s v
  | some i => homogeneous B 0 (g i)

private theorem side_generated (B : InvariantForm G) (φ : Direction H) (hφ : Regular H φ)
    (s : ℤ) (hs : s = 1 ∨ s = -1) {μ : Module.Dual ℂ H} {v : G}
    (hv : v ∈ rootSpace H μ) (hv0 : v ≠ 0)
    (hkill : ∀ α ∈ HighestRoot.positiveRoots H (-φ), ∀ x ∈ rootSpace H α, ⁅x, v⁆ = 0)
    (g : ∀ i : HighestRoot.simpleRoots H φ, G)
    (hg : ∀ i, g i ∈ rootSpace H i.val) (hg0 : ∀ i, g i ≠ 0) :
    affineLieSpan B (Set.range (sideGenerators H B φ s v g)) =
      components B (sideDegrees (positive_value H φ) s) ⊥ ⊥ := by
  let a := sideGenerators H B φ s v g
  let A := LieSubalgebra.lieSpan ℂ (AffineAlgebra B) (Set.range a)
  let M := components B (sideDegrees (positive_value H φ) s) ⊥ ⊥
  let L : LieSubalgebra ℂ (AffineAlgebra B) := { M with lie_mem' := side_lie_mem B _ s hs }
  have hgen (i) : a i ∈ A := LieSubalgebra.subset_lieSpan (Set.mem_range_self i)
  have hf := finiteSide_le H B φ A (fun i => ⟨g i, hg i, hg0 i, hgen (some i)⟩)
  have hvA := extremal_degree_mem H B φ hφ A hf s hv hv0 (hgen none) hkill
  change affineLieSpan B (Set.range a) = M
  rw [affineLieSpan_eq]
  apply le_antisymm
  · change A ≤ L
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    change a i ∈ M
    cases i with
    | none =>
      apply homogeneous_mem_components
      rcases hs with rfl | rfl <;> simp [sideDegrees]
    | some i =>
      apply homogeneous_mem_components
      simpa only [sideDegrees, ite_true, LieSubalgebra.mem_toSubmodule] using positive_root_mem H i.property.1.2 (hg i)
  · intro x hx
    change x ∈ A
    refine components_induction B (p := fun y => y ∈ A) hx A.zero_mem (fun _ _ => A.add_mem)
      ?_ ?_ ?_
    · intro m y hy
      by_cases hm : m = 0
      · subst m
        exact hf y (by simpa only [sideDegrees, ite_true, LieSubalgebra.mem_toSubmodule] using hy)
      by_cases hpos : 0 < s * m
      · exact higher_degree_mem B A s hs hvA m hpos y
      · have hzero : y = 0 := by simpa [sideDegrees, hm, hpos] using hy
        rw [← homogeneousLinear_apply, hzero, map_zero]
        exact A.zero_mem
    · intro c hc
      rw [(Submodule.mem_bot ℂ).mp hc, zero_smul]
      exact A.zero_mem
    · intro c hc
      rw [(Submodule.mem_bot ℂ).mp hc, zero_smul]
      exact A.zero_mem

private def negSimpleEquiv (φ : Direction H) :
    HighestRoot.simpleRoots H (-φ) ≃ HighestRoot.simpleRoots H φ where
  toFun i := ⟨-i.val, neg_simple H i.property⟩
  invFun i := ⟨-i.val, neg_simple H (φ := -φ) (by simpa only [neg_neg] using i.property)⟩
  left_inv i := Subtype.ext (neg_neg i.val)
  right_inv i := Subtype.ext (neg_neg i.val)

theorem affineSimpleGenerators : affineSimpleGenerators_type.{u} := by
  intro G _ _ _ _ B H _ φ _ hφ θ hθ T S
  refine ⟨?_, ?_⟩
  · exact side_generated H B φ hφ 1 (Or.inl rfl) T.f_mem T.f_ne_zero
      (fun α hα x hx => lowest_killed H hθ
        (by simpa only [LinearMap.neg_apply, neg_pos] using hα.2) hx T.f_mem)
      (fun i => (S i).e) (fun i => (S i).e_mem) (fun i => (S i).e_ne_zero)
  · let e := negSimpleEquiv H φ
    have hreg : Regular H (-φ) := fun α hα => by
      simpa only [LinearMap.neg_apply, neg_ne_zero] using hφ α hα
    have hside := side_generated H B (-φ) hreg (-1) (Or.inr rfl) T.e_mem T.e_ne_zero
      (fun α hα x hx => highest_killed H hθ
        (by simpa only [neg_neg] using hα.2) hx T.e_mem)
      (fun i => (S (e i)).f) (fun i => by
        have hmem := (S (e i)).f_mem
        change (S (e i)).f ∈ rootSpace H (- -i.val) at hmem
        simpa only [neg_neg] using hmem)
      (fun i => (S (e i)).f_ne_zero)
    have hfun : sideGenerators H B (-φ) (-1) T.e (fun i => (S (e i)).f) =
        affineSimpleF B T S ∘ Equiv.optionCongr e := by
      funext i
      cases i <;> rfl
    rw [hfun, Set.range_comp, (Equiv.optionCongr e).surjective.range_eq, Set.image_univ] at hside
    simpa only [affineNegative_value, negative_eq_positive H φ] using hside

end Generation

end RepTheorySurvey.Affine
