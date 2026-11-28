import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanData
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Affine.CartanRealization
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.AffineTriangularDecomposition
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots

noncomputable section

namespace LieNotes.Affine

open RepTheorySurvey.Affine
open LieAlgebrasAndRepresentations hiding simpleRoots positiveRoots
open LieAlgebrasAndRepresentations.HighestRoot (simpleRoots positiveRoots)
open _root_.Specs.LieAlgebrasAndRepresentations.RealRootSpace
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces
  (coordinates cartanProjection)
open LieNotes.Contragredient
open Module
open private highest_dominant rootForm_self_pos rootForm_symm coroot_self
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.AffineSimpleTriples
open private cartanExpansion cartanProjection_cartanIncl cartanProjection_cartanK
  cartanProjection_cartanD coordinates_homogeneous
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces
open private rootSet_nonempty
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestRoot

universe u

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
  [LieAlgebra.IsSimple ℂ G] (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]

omit [FiniteDimensional ℂ G] in
private theorem finiteSemisimple : IsSemisimple ℂ G := LieAlgebra.radical_eq_bot

private theorem cartanToral : IsMaximalToral H :=
  RealRootSpace.cartan_isMaximalToral finiteSemisimple H

private theorem simpleRootData (φ : Direction H) (hφ : Regular H φ) :
    ∃ b : Basis (simpleRoots H φ) ℂ (Module.Dual ℂ H),
      (∀ i, b i = i.val) ∧
      ∀ i j : simpleRoots H φ, i ≠ j → (rootForm H j.val i.val).re ≤ 0 := by
  classical
  let R := RealRootSpace.realization finiteSemisimple H
  let := R.normedAddCommGroup
  let := R.innerProductSpace
  -- Restrict the chosen direction to the real root space and use its Riesz vector.
  let w : E H := (InnerProductSpace.toDual ℝ (E H)).symm (φ.comp R.j).toContinuousLinearMap
  have hw (x : E H) : inner ℝ w x = φ (R.j x) := InnerProductSpace.toDual_symm_apply
  have hj {x : E H} (hx : x ∈ realRoots H) :
      R.j x ∈ rootSet H ∧ rootRestriction H (R.j x) = x := by
    obtain ⟨a, ha, rfl⟩ := hx
    rw [R.extension_root a ha]
    exact ⟨ha, rfl⟩
  have hreg : RootRegular (realRoots H) w := by
    intro x hx
    rw [hw]
    exact hφ _ (hj hx).1
  have hpos {x : E H} (hx : x ∈ realRoots H) :
      x ∈ LieAlgebrasAndRepresentations.positiveRoots (realRoots H) w ↔
        R.j x ∈ positiveRoots H φ := by
    change (x ∈ realRoots H ∧ 0 < inner ℝ w x) ↔ (R.j x ∈ rootSet H ∧ 0 < φ (R.j x))
    rw [hw, and_iff_right hx, and_iff_right (hj hx).1]
  have hrestrict {a : Module.Dual ℂ H} (ha : a ∈ positiveRoots H φ) :
      rootRestriction H a ∈ LieAlgebrasAndRepresentations.positiveRoots (realRoots H) w := by
    apply (hpos ⟨a, ha.1, rfl⟩).2
    simpa only [R.extension_root a ha.1] using ha
  let r : Module.Dual ℂ H →ₗ[ℝ] E H :=
    { toFun := rootRestriction H
      map_add' := by intros; ext; simp [rootRestriction]
      map_smul' := by intros; ext; simp [rootRestriction] }
  have into (i : simpleRoots H φ) :
      r i.val ∈ LieAlgebrasAndRepresentations.simpleRoots (realRoots H) w := by
    refine ⟨hrestrict i.property.1, ?_⟩
    intro a ha b hb hab
    apply i.property.2 (R.j a) ((hpos ha.1).1 ha) (R.j b) ((hpos hb.1).1 hb)
    rw [← map_add, ← hab]
    exact (R.extension_root i.val i.property.1.1).symm
  have out (x : LieAlgebrasAndRepresentations.simpleRoots (realRoots H) w) :
      R.j x.val ∈ simpleRoots H φ := by
    refine ⟨(hpos x.property.1.1).1 x.property.1, ?_⟩
    intro a ha b hb hab
    apply x.property.2 (r a) (hrestrict ha) (r b) (hrestrict hb)
    change x.val = r a + r b
    rw [← (hj x.property.1.1).2]
    change r (R.j x.val) = r a + r b
    rw [hab, map_add]
  let e : simpleRoots H φ ≃ LieAlgebrasAndRepresentations.simpleRoots (realRoots H) w :=
    { toFun := fun i => ⟨r i.val, into i⟩
      invFun := fun i => ⟨R.j i.val, out i⟩
      left_inv := fun i => Subtype.ext (R.extension_root i.val i.property.1.1)
      right_inv := fun i => Subtype.ext (hj i.property.1.1).2 }
  obtain ⟨b, hb⟩ := simpleRoots_basis (realRoots H) R.root_system w hreg
  let c := ((b.reindex e.symm).baseChange ℂ).map R.complexification
  refine ⟨c, ?_, ?_⟩
  · intro i
    dsimp only [c]
    rw [Basis.map_apply, Basis.baseChange_apply, R.complexification_tmul, one_smul,
      Basis.reindex_apply, Equiv.symm_symm, hb]
    exact R.extension_root i.val i.property.1.1
  · intro i j hij
    have h := simpleRoots_pairwise_nonpos R.root_system.1 hreg (e j).property
      (e i).property (fun he => (e.injective.ne hij.symm) (Subtype.ext he))
    have he := congrArg Complex.re (R.root_form_agrees j.val j.property.1.1 i.val i.property.1.1)
    change inner ℝ (rootRestriction H j.val) (rootRestriction H i.val) =
      (rootForm H j.val i.val).re at he
    rw [← he]
    exact h

private theorem simpleCorootBasis (φ : Direction H)
    (b : Basis (simpleRoots H φ) ℂ (Module.Dual ℂ H)) (hb : ∀ i, b i = i.val) :
    ∃ c : Basis (simpleRoots H φ) ℂ H, ∀ i, c i = killingCoroot H i.val := by
  let form := (_root_.killingForm ℂ G).restrict H.toSubmodule
  let e := (form.toDual (killingForm_restrict_toral_nondegenerate finiteSemisimple H
    (cartanToral H))).symm
  have ht (a : Module.Dual ℂ H) : e a = tAlpha H a :=
    tAlpha_unique finiteSemisimple H (cartanToral H) a (e a) fun x => by
      change form (e a) x = a x
      exact LinearMap.BilinForm.apply_toDual_symm_apply a x
  let z (i : simpleRoots H φ) : ℂˣ :=
    Units.mk0 (2 / rootForm H i.val i.val)
      (div_ne_zero (by norm_num) (rootForm_self_ne_zero finiteSemisimple H
        (cartanToral H) i.val i.property.1.1))
  refine ⟨(b.map e).unitsSMul z, fun i => ?_⟩
  rw [Basis.unitsSMul_apply, Basis.map_apply, hb, ht]
  rfl


/-- Rescale the Killing form using the length of a longest finite root. -/
theorem existsNormalizedForm :
    _root_.Specs.LieNotes.Affine.CartanRealization.ExistsNormalizedForm.{u} := by
  classical
  intro G _ _ _ _ H _
  obtain ⟨γ, hg⟩ := (rootSet_finite H (cartanToral H).1).exists_maximalFor
    (fun a => (rootForm H a a).re) (rootSet H)
    (rootSet_nonempty finiteSemisimple H (cartanToral H))
  let γ' : rootSet H := ⟨γ, hg.prop⟩
  have hlong : IsLongRoot γ' := fun a => le_of_not_gt fun h =>
    h.not_ge (hg.le_of_le a.property h.le)
  let c := rootForm H γ γ / 2
  have hc : c ≠ 0 :=
    div_ne_zero (rootForm_self_ne_zero finiteSemisimple H (cartanToral H) _ hg.prop) (by norm_num)
  let B : InvariantForm G :=
    { form := c • _root_.killingForm ℂ G
      invariant := fun x y z => by
        change c * _root_.killingForm ℂ G ⁅x, y⁆ z =
          - (c * _root_.killingForm ℂ G y ⁅x, z⁆)
        rw [LieModule.traceForm_apply_lie_apply' ℂ G G x y z, mul_neg]
      symmetric := ⟨fun x y => by
        change c * _root_.killingForm ℂ G x y = c * _root_.killingForm ℂ G y x
        rw [LieModule.traceForm_comm ℂ G G x y]⟩ }
  refine ⟨B, γ', hlong, rfl, ?_, ?_⟩
  · let : LieAlgebra.HasTrivialRadical ℂ G := ⟨finiteSemisimple⟩
    have hk := LieAlgebra.IsKilling.killingForm_nondegenerate ℂ G
    exact ⟨fun x hx => hk.1 x fun y => (mul_eq_zero.mp (hx y)).resolve_left hc,
      fun y hy => hk.2 y fun x => (mul_eq_zero.mp (hy x)).resolve_left hc⟩
  · intro a ha
    let R := RealRootSpace.realization finiteSemisimple H
    have hreal (x : rootSet H) :
        ((rootForm H x.val x.val).re : ℂ) = rootForm H x.val x.val := by
      rw [← R.root_form_agrees x.val x.property x.val x.property, Complex.ofReal_re]
    have hlen : rootForm H a.val a.val = rootForm H γ γ := by
      rw [← hreal a, ← hreal γ']
      exact congrArg Complex.ofReal (le_antisymm (hlong a) (ha γ'))
    refine ⟨c⁻¹ • tAlpha H a.val, fun y => ?_, ?_⟩
    · change c * _root_.killingForm ℂ G (c⁻¹ • (tAlpha H a.val : G)) y = _
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      exact tAlpha_pairing finiteSemisimple H (cartanToral H) a.val y
    · rw [map_smul, smul_eq_mul, ← rootForm_eq_apply finiteSemisimple H (cartanToral H), hlen]
      have hc2 : c * 2 = rootForm H γ γ := div_mul_cancel₀ _ (by norm_num)
      rw [← hc2, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

section Coordinates

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra]

variable (B : InvariantForm G)

private def centralCoordinate : affineCartan B H →ₗ[ℂ] ℂ :=
  ((LinearMap.snd ℂ (ℤ →₀ G) ℂ).comp
    (LinearMap.fst ℂ ((ℤ →₀ G) × ℂ) ℂ)).comp
      ((coordinates B).toLinearMap.comp (affineCartan B H).subtype)

@[simp] private theorem centralCoordinate_incl (x : H) :
    centralCoordinate H B (cartanIncl B H x) = 0 := by
  change (coordinates B (homogeneous B 0 (x : G))).1.2 = 0
  rw [coordinates_homogeneous]

@[simp] private theorem centralCoordinate_K :
    centralCoordinate H B (cartanK B H) = 1 := rfl

@[simp] private theorem centralCoordinate_d :
    centralCoordinate H B (cartanD B H) = 0 := rfl

private def cartanCoordinateEquiv : affineCartan B H ≃ₗ[ℂ] H × (ℂ × ℂ) := by
  let f := (cartanProjection B H).prod ((centralCoordinate H B).prod (delta B H))
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y he
    have h₁ : cartanProjection B H x = cartanProjection B H y := congrArg Prod.fst he
    have h₂ : centralCoordinate H B x = centralCoordinate H B y :=
      congrArg (fun p : H × (ℂ × ℂ) => p.2.1) he
    have h₃ : delta B H x = delta B H y := congrArg (fun p : H × (ℂ × ℂ) => p.2.2) he
    calc
      x = cartanIncl B H (cartanProjection B H x) +
          centralCoordinate H B x • cartanK B H + delta B H x • cartanD B H :=
        cartanExpansion B H x
      _ = y := by rw [h₁, h₂, h₃]; exact (cartanExpansion B H y).symm
  · rintro ⟨x, z, t⟩
    refine ⟨cartanIncl B H x + z • cartanK B H + t • cartanD B H, ?_⟩
    apply Prod.ext
    · change cartanProjection B H _ = x
      simp only [map_add, map_smul, cartanProjection_cartanIncl, cartanProjection_cartanK,
        cartanProjection_cartanD, smul_zero, add_zero]
    · apply Prod.ext
      · change centralCoordinate H B _ = z
        simp
      · change delta B H _ = t
        simp

end Coordinates


private theorem outsideSpanOfCoordinate {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] ℂ) (v : ι → V) (x : V) (hv : ∀ i, f (v i) = 0) (hx : f x ≠ 0) :
    x ∉ Submodule.span ℂ (Set.range v) := by
  have h : Submodule.span ℂ (Set.range v) ≤ f.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hv i
  exact fun hm => hx (h hm)

private theorem rank_of_pairing {I V : Type*} [Fintype I] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (e : Module.Dual ℂ V →ₗ[ℂ] (I → ℂ))
    (he : Function.Injective e) (a : I → Module.Dual ℂ V)
    (ha : Submodule.span ℂ (Set.range a) = ⊤) (M : Matrix I I ℂ)
    (hM : ∀ j, M.col j = e (a j)) :
    M.rank = Module.finrank ℂ V := by
  have hcols : Set.range M.col = e '' Set.range a := by
    rw [← Set.range_comp, show M.col = e ∘ a from funext hM]
  rw [Matrix.rank_eq_finrank_span_cols, hcols, Submodule.span_image, ha,
    Submodule.map_top, LinearMap.finrank_range_of_inj he, Subspace.dual_finrank_eq]

/-- The untwisted affine simple roots and coroots realize a symmetrizable
generalized Cartan matrix of rank equal to the finite Cartan dimension. -/
theorem affineCartanRealization :
    _root_.Specs.LieNotes.Affine.CartanRealization.AffineCartanRealization.{u} := by
  classical
  intro G _ _ _ _ B H _ φ hB hφ θ hθ
  obtain ⟨b, hb, hoff⟩ := simpleRootData H φ hφ
  obtain ⟨c, hc⟩ := simpleCorootBasis H φ b hb
  let : Fintype (simpleRoots H φ) := FiniteDimensional.fintypeBasisIndex c
  let I := AffineSimpleIndex H φ
  -- Projection to the finite Cartan sends the extra root and coroot to the negatives.
  let a : I → rootSet H
    | none => ⟨θ, hθ.1.1⟩
    | some i => ⟨i.val, i.property.1.1⟩
  let s : I → ℤ
    | none => -1
    | some _ => 1
  let signedRoot (i : I) : Module.Dual ℂ H := (s i : ℂ) • (a i).val
  let signedCoroot (i : I) : H := (s i : ℂ) • killingCoroot H (a i).val
  let h : I → affineCartan B H
    | none => cartanK B H - cartanIncl B H (killingCoroot H θ)
    | some i => cartanIncl B H (killingCoroot H i.val)
  let α (i : I) : Module.Dual ℂ (affineCartan B H) := affineSimpleRoot B H θ i
  have hval (i : I) : (h i : AffineAlgebra B) = affineSimpleH B H θ i := by
    cases i <;> rfl
  have hproj (i : I) : cartanProjection B H (h i) = signedCoroot i := by
    cases i <;> simp [h, signedCoroot, s, a, cartanProjection_cartanK,
      cartanProjection_cartanIncl]
  have hz (i : I) : delta B H (h i) = 0 := by
    cases i <;> simp [h]
  have hα (j : I) (x : affineCartan B H) (hx : delta B H x = 0) :
      α j x = signedRoot j (cartanProjection B H x) := by
    cases j with
    | none =>
      change delta B H x - θ (cartanProjection B H x) = _
      simp [hx, signedRoot, s, a]
    | some j =>
      change j.val (cartanProjection B H x) = _
      simp [signedRoot, s, a]
  obtain ⟨_, _, d', _, _, _, _, _, hδd, hext⟩ :=
    (affineTriangularDecomposition B H φ hB hφ).cartan_weight_values
  have hαind : LinearIndependent ℂ α := by
    rw [linearIndependent_option]
    constructor
    · let liftRoot : Module.Dual ℂ H →ₗ[ℂ] Module.Dual ℂ (affineCartan B H) :=
        (cartanProjection B H).dualMap
      have hlift : Function.Injective liftRoot := by
        intro β γ hβγ
        ext x
        have hh := LinearMap.congr_fun hβγ (cartanIncl B H x)
        change β (cartanProjection B H (cartanIncl B H x)) =
          γ (cartanProjection B H (cartanIncl B H x)) at hh
        simpa only [cartanProjection_cartanIncl] using hh
      have he : (α ∘ some) = liftRoot ∘ b := by
        funext i
        change extendFiniteRoot B H i.val = liftRoot (b i)
        rw [hb]
        rfl
      rw [he]
      exact b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hlift)
    · apply outsideSpanOfCoordinate (Module.Dual.eval ℂ (affineCartan B H) d')
      · intro i
        exact (hext i.val).2.2
      · change delta B H d' - extendFiniteRoot B H θ d' ≠ 0
        rw [hδd, (hext θ).2.2, sub_zero]
        exact one_ne_zero
  have hhind : LinearIndependent ℂ h := by
    rw [linearIndependent_option]
    constructor
    · have hincl : Function.Injective (cartanIncl B H) := by
        intro x y hxy
        simpa only [cartanProjection_cartanIncl] using congrArg (cartanProjection B H) hxy
      have he : (h ∘ some) = cartanIncl B H ∘ c := by
        funext i
        change cartanIncl B H (killingCoroot H i.val) = cartanIncl B H (c i)
        rw [hc]
      rw [he]
      exact c.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hincl)
    · apply outsideSpanOfCoordinate (centralCoordinate H B)
      · intro i
        exact centralCoordinate_incl H B _
      · change centralCoordinate H B (cartanK B H - cartanIncl B H (killingCoroot H θ)) ≠ 0
        rw [map_sub, centralCoordinate_K, centralCoordinate_incl, sub_zero]
        exact one_ne_zero
  have hint (i j : I) :
      ∃ z : ℤ, (a j).val (killingCoroot H (a i).val) = (z : ℂ) :=
    (RootStrings.coroot_pairing_integral finiteSemisimple H (cartanToral H)
      _ _ (a i).property (a j).property).imp fun _ hp => hp.1
  choose n hn using hint
  let A : Matrix I I ℤ := fun i j => (s i * s j) * n i j
  have hentry (i j : I) : signedRoot j (signedCoroot i) = (A i j : ℂ) := by
    simp only [signedRoot, signedCoroot, LinearMap.smul_apply, map_smul, smul_eq_mul, hn,
      A, Int.cast_mul]
    ring
  let R : Realization A (affineCartan B H) :=
    ⟨h, α, hhind, hαind, fun i j => by rw [hα j (h i) (hz i), hproj, hentry]⟩
  let len (i : I) := (rootForm H (a i).val (a i).val).re / 2
  have hlen (i : I) : 0 < len i := half_pos (rootForm_self_pos H (a i).property)
  have hnum (i j : I) :
      len i * (n i j : ℝ) = (rootForm H (a j).val (a i).val).re := by
    have hp := hn i j
    rw [killingCoroot_pairing finiteSemisimple H (cartanToral H)] at hp
    have hmul := (div_eq_iff (rootForm_self_ne_zero finiteSemisimple H (cartanToral H)
      _ (a i).property)).mp hp
    have hre := congrArg Complex.re hmul
    have hreal :
        2 * (rootForm H (a j).val (a i).val).re =
          (n i j : ℝ) * (rootForm H (a i).val (a i).val).re := by
      simpa [Complex.mul_re] using hre
    change (rootForm H (a i).val (a i).val).re / 2 * (n i j : ℝ) = _
    linear_combination -hreal / 2
  have hweighted (i j : I) :
      len i * (A i j : ℝ) =
        ((s i : ℝ) * (s j : ℝ)) * (rootForm H (a j).val (a i).val).re := by
    simp only [A, Int.cast_mul]
    linear_combination ((s i : ℝ) * (s j : ℝ)) * hnum i j
  have hsym (i j : I) : len i * (A i j : ℝ) = len j * (A j i : ℝ) := by
    rw [hweighted, hweighted, rootForm_symm H (a j).val (a i).val, mul_comm (s i : ℝ)]
  have hdiag (i : I) : A i i = 2 := by
    have hn' : n i i = 2 := by
      apply Int.cast_injective (α := ℂ)
      rw [← hn, coroot_self H (a i).property]
      norm_num
    change s i * s i * n i i = 2
    rw [hn']
    cases i <;> rfl
  have hnonpos (i j : I) (hij : i ≠ j) : A i j ≤ 0 := by
    have hw : len i * (A i j : ℝ) ≤ 0 := by
      rw [hweighted]
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j =>
          change ((-1 : ℤ) : ℝ) * ((1 : ℤ) : ℝ) * (rootForm H j.val θ).re ≤ 0
          rw [rootForm_symm H j.val θ]
          simpa using highest_dominant H hθ j.property.1
      | some i =>
        cases j with
        | none =>
          change ((1 : ℤ) : ℝ) * ((-1 : ℤ) : ℝ) * (rootForm H θ i.val).re ≤ 0
          simpa using highest_dominant H hθ i.property.1
        | some j =>
          change ((1 : ℤ) : ℝ) * ((1 : ℤ) : ℝ) * (rootForm H j.val i.val).re ≤ 0
          simpa using hoff i j (fun e => hij (congrArg some e))
    exact_mod_cast (nonpos_of_mul_nonpos_right hw (hlen i))
  have hzero (i j : I) (hz : A i j = 0) : A j i = 0 := by
    have he := hsym i j
    rw [hz, Int.cast_zero, mul_zero] at he
    exact_mod_cast (mul_eq_zero.mp he.symm).resolve_left (hlen j).ne'
  have hcartan : IsGeneralizedCartanMatrix A :=
    ⟨hdiag, hnonpos, fun i j => ⟨hzero i j, hzero j i⟩⟩
  -- All columns come from the finite dual, and the finite columns span its image.
  let eval : Module.Dual ℂ H →ₗ[ℂ] (I → ℂ) :=
    LinearMap.pi fun i => Module.Dual.eval ℂ H (signedCoroot i)
  have heval : Function.Injective eval := by
    intro x y hxy
    apply c.ext
    intro i
    have hii := congrFun hxy (some i)
    change x (signedCoroot (some i)) = y (signedCoroot (some i)) at hii
    simpa [hc, signedCoroot, a, s] using hii
  have hspan : Submodule.span ℂ (Set.range signedRoot) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨some i, by simp [hb, signedRoot, s, a]⟩
  have hrank : (A.map fun z : ℤ => (z : ℂ)).rank = Fintype.card (simpleRoots H φ) := by
    rw [← Module.finrank_eq_card_basis c]
    apply rank_of_pairing eval heval signedRoot hspan
    intro j
    ext i
    exact (hentry i j).symm
  refine ⟨inferInstance, A, R, hval, fun _ => rfl, hcartan, ⟨len, hlen, hsym⟩, ?_, hrank⟩
  let e := cartanCoordinateEquiv H B
  have hdim : FiniteDimensional ℂ (affineCartan B H) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  refine ⟨hdim, ?_⟩
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    Module.finrank_eq_card_basis c, hrank, Fintype.card_option]
  omega

end LieNotes.Affine
