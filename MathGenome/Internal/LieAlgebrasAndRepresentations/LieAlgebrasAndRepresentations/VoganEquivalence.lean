import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VoganEquivalence
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactCartanConjugacy
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RegularSemisimple
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StableCartanVoganData
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootStrings
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.Push
import Batteries.Tactic.OpenPrivate

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LieAlgebrasAndRepresentations.VoganEquivalence

open Specs.LieAlgebrasAndRepresentations.VoganEquivalence

universe u v

theorem normalizeMultipliers : normalizeMultipliersType.{v} := by
  classical
  intro ι σ hσ m n hm hn
  constructor
  · rintro ⟨z, hz⟩ j hj
    simpa [multiplierGauge, hj] using congrFun hz j
  · intro h
    let orbit (j : ι) : {s : Set ι // s.Nonempty} :=
      ⟨{k | k = j ∨ k = σ j}, ⟨j, Or.inl rfl⟩⟩
    let s : Set ι := {j | σ j ≠ j ∧ j = (orbit j).property.some}
    have hs {j : ι} (hj : σ j ≠ j) : σ j ∈ s ↔ j ∉ s := by
      have ho : orbit (σ j) = orbit j := by
        apply Subtype.ext
        ext k
        change k = σ j ∨ k = σ (σ j) ↔ k = j ∨ k = σ j
        rw [hσ j, or_comm]
      have hc : (orbit j).property.some = j ∨ (orbit j).property.some = σ j :=
        (orbit j).property.some_mem
      have hσj : σ (σ j) ≠ σ j := by simpa only [hσ j] using Ne.symm hj
      change (σ (σ j) ≠ σ j ∧ σ j = (orbit (σ j)).property.some) ↔
        ¬ (σ j ≠ j ∧ j = (orbit j).property.some)
      rw [ho, and_iff_right hj, and_iff_right hσj]
      rcases hc with hc | hc <;> simp [hc, hj, Ne.symm hj]
    let z (j : ι) : Circle := if j ∈ s then n j / m j else 1
    refine ⟨z, funext fun j => ?_⟩
    by_cases hj : σ j = j
    · simp [multiplierGauge, hj, h j hj]
    · by_cases hj' : j ∈ s
      · have hsj : σ j ∉ s := fun hh => (hs hj).mp hh hj'
        simp [multiplierGauge, z, hj', hsj]
      · have hsj := (hs hj).mpr hj'
        simp [multiplierGauge, z, hj', hsj, hm, hn, div_eq_mul_inv, mul_comm]

theorem colorParity : colorParityType.{v} := by
  intro ι A i j b
  have cases (x : ZMod 2) : x = 0 ∨ x = 1 := by fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases cases (b i) with hi | hi
  · simp [reflectedColors, hi, colorSign]
  · have sub (x : ZMod 2) : x - 1 ≠ x := by
      intro h
      have h' : (1 : ZMod 2) = 0 := sub_eq_self.mp h
      exact one_ne_zero h'
    rcases Int.even_or_odd (A i j) with he | ho
    · have hz := ZMod.intCast_eq_zero_iff_even.mpr he
      have he' : Even (-A i j) := he.neg
      have hn : ¬ Odd (A i j) := fun h =>
        zero_ne_one (hz.symm.trans (ZMod.intCast_eq_one_iff_odd.mpr h))
      simp [reflectedColors, hz, hi, colorSign, he'.neg_one_zpow, hn]
    · have hz := ZMod.intCast_eq_one_iff_odd.mpr ho
      have ho' : Odd (-A i j) := ho.neg
      constructor
      · rcases cases (b j) with hj | hj <;>
          norm_num [reflectedColors, colorSign, hz, hi, hj, ho'.neg_one_zpow]
      · simp [reflectedColors, hz, hi, ho, sub]

section CartanAdjustment

open LieAlgebrasAndRepresentations.RealForms
open LieAlgebrasAndRepresentations.CompactCartanConjugacy
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature (complexFixed)
open Specs.LieAlgebrasAndRepresentations.RegularSemisimple (algebraNorm elementCentralizer)
open Specs.LieAlgebrasAndRepresentations.CartanConjugacy (exponentialOperator)
open private compact_intertwiner from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
open scoped ComplexConjugate

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private def restrictReal (H : LieSubalgebra ℂ L) : LieSubalgebra ℝ L where
  toSubmodule := H.toSubmodule.restrictScalars ℝ
  lie_mem' := H.lie_mem

/-- Real subalgebra fixed by both involutions, with its inclusion into L. -/
private def fixedCompact (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) : LieSubalgebra ℝ L :=
  ω.fixed ⊓ restrictReal (complexFixed a)

omit [FiniteDimensional ℂ L] in
private theorem mem_fixedCompact (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) (x : L) :
    x ∈ fixedCompact ω a ↔ ω.map x = x ∧ a x = x := Iff.rfl

private def positiveCartan (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L)
    (H : LieSubalgebra ℂ L) : LieSubalgebra ℝ (fixedCompact ω a) :=
  (restrictReal H).comap (fixedCompact ω a).incl

private theorem centralizes_positiveCartan
    (hss : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L)
    {ω : Conjugation L} {a : L ≃ₗ⁅ℂ⁆ L} (hwa : Intertwines ω ω a)
    {H : LieSubalgebra ℂ L} (hH : StableCartan ω a H) {x : L} :
    (∀ y ∈ positiveCartan ω a H, ⁅(y : L), x⁆ = 0) ↔ x ∈ H := by
  have comm {x y : L} (hx : x ∈ H) (hy : y ∈ H) : ⁅x, y⁆ = 0 :=
    congrArg Subtype.val (hH.toral.1.1.trivial (⟨x, hx⟩ : H) ⟨y, hy⟩)
  refine ⟨fun hx => ?_, fun hx y hy => comm hy hx⟩
  let K := fixedCartan a H
  have har : ∀ α ∈ rootSet_value H, ∃ y : K, α ⟨(y.val : L), y.property⟩ ≠ 0 := by
    intro α hα
    obtain ⟨y, hfix, hne⟩ := hH.root_nonvanishing α hα
    exact ⟨⟨⟨y, hfix⟩, y.property⟩, hne⟩
  letI : Finite (rootSet_value H) := (rootSet_finite H hH.toral.1).to_subtype
  let f (α : rootSet_value H) : Module.Dual ℂ K :=
    α.val.comp (((complexFixed a).incl.toLinearMap.comp K.incl.toLinearMap).codRestrict
      H.toSubmodule (fun y => y.property))
  have hf (α : rootSet_value H) : ∃ y, f α y ≠ 0 := har α.val α.property
  obtain ⟨y, hy⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  let z : H := ⟨(y.val : L), y.property⟩
  have hz : elementCentralizer (z : L) = H :=
    RegularSemisimple.centralizer_eq_torus_of_rootRegular hss H hH.toral z
      (fun α hα => hy ⟨α, hα⟩)
  rw [← hz]
  change ⁅(z : L), x⁆ = 0
  obtain ⟨p, q, hp, hq, hpq⟩ := fixed_parts_formula ω (z : L)
  have hza : a (z : L) = (z : L) := y.val.property
  have hwa' : a (ω.map (z : L)) = ω.map (z : L) := by rw [← hwa, hza]
  have pair_mem (v : ω.fixed) (hv : (v : L) ∈ H) (h : a (v : L) = (v : L)) :
      ⁅(v : L), x⁆ = 0 :=
    hx (⟨v, (mem_fixedCompact ω a v).mpr ⟨v.property, h⟩⟩) hv
  have hp' : ⁅(p : L), x⁆ = 0 := by
    apply pair_mem
    · rw [hp]
      exact H.smul_mem _ (H.add_mem z.property (hH.compact_stable _ z.property))
    · rw [hp, map_smul, map_add, hza, hwa']
  have hq' : ⁅(q : L), x⁆ = 0 := by
    apply pair_mem
    · rw [hq]
      exact H.smul_mem _ (H.sub_mem z.property (hH.compact_stable _ z.property))
    · rw [hq, map_smul, map_sub, hza, hwa']
  rw [← hpq, add_lie, smul_lie, hp', hq', smul_zero, add_zero]

private theorem lie_eq_zero_of_abelian {V : Type*} [LieRing V] [LieAlgebra ℝ V]
    {T : LieSubalgebra ℝ V} (hT : IsLieAbelian T) {x y : V} (hx : x ∈ T) (hy : y ∈ T) :
    ⁅x, y⁆ = 0 :=
  congrArg Subtype.val (hT.trivial (⟨x, hx⟩ : T) ⟨y, hy⟩)

private theorem maximal_positiveCartan
    (hss : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L)
    {ω : Conjugation L} {a : L ≃ₗ⁅ℂ⁆ L} (hwa : Intertwines ω ω a)
    {H : LieSubalgebra ℂ L} (hH : StableCartan ω a H) :
    Maximal (fun T : LieSubalgebra ℝ (fixedCompact ω a) => IsLieAbelian T)
      (positiveCartan ω a H) := by
  constructor
  · refine ⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩
    change ⁅(x.val : L), (y.val : L)⁆ = 0
    exact congrArg (fun t : H => (t : L))
      (hH.toral.1.1.trivial (⟨x.val, x.property⟩ : H) ⟨y.val, y.property⟩)
  · intro T hab hle x hx
    exact (centralizes_positiveCartan hss hwa hH).mp
      (fun y hy => congrArg Subtype.val (lie_eq_zero_of_abelian hab (hle hy) hx))

private def inheritedKilling (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) :
    LinearMap.BilinForm ℝ (fixedCompact ω a) :=
  let f : fixedCompact ω a →ₗ[ℝ] ω.fixed :=
    (fixedCompact ω a).toSubmodule.inclusion inf_le_left
  (-killingForm ℝ ω.fixed).compl₁₂ f f

omit [FiniteDimensional ℂ L] in
private theorem inheritedKilling_invariant (ω : Conjugation L) (a : L ≃ₗ⁅ℂ⁆ L) :
    (inheritedKilling ω a).lieInvariant (fixedCompact ω a) := by
  intro z x y
  let f : fixedCompact ω a →ₗ⁅ℝ⁆ ω.fixed := LieSubalgebra.inclusion inf_le_left
  change -(killingForm ℝ ω.fixed (f ⁅z, x⁆) (f y)) =
    -(-(killingForm ℝ ω.fixed (f x) (f ⁅z, y⁆)))
  rw [f.map_lie, f.map_lie, killingForm, LieModule.traceForm_apply_lie_apply']

omit [FiniteDimensional ℂ L] in
private theorem inheritedKilling_pos (ω : Conjugation L) (hc : IsCompact ω) (a : L ≃ₗ⁅ℂ⁆ L)
    (x : fixedCompact ω a) (hx : x ≠ 0) :
    0 < inheritedKilling ω a x x := by
  let f : fixedCompact ω a →ₗ⁅ℝ⁆ ω.fixed := LieSubalgebra.inclusion inf_le_left
  change 0 < -(killingForm ℝ ω.fixed (f x) (f x))
  exact neg_pos.mpr (hc (f x) (fun h =>
    hx (Subtype.ext (congrArg (fun z : ω.fixed => (z : L)) h))))

@[instance_reducible] private def fixedCore (ω : Conjugation L) (hc : IsCompact ω) (a : L ≃ₗ⁅ℂ⁆ L) :
    InnerProductSpace.Core ℝ (fixedCompact ω a) where
  inner := fun x y => inheritedKilling ω a x y
  conj_inner_symm x y := by
    let f : fixedCompact ω a →ₗ⁅ℝ⁆ ω.fixed := LieSubalgebra.inclusion inf_le_left
    change star (-(killingForm ℝ ω.fixed (f y) (f x))) = -(killingForm ℝ ω.fixed (f x) (f y))
    rw [star_trivial, killingForm, LieModule.traceForm_comm]
  re_inner_nonneg x := by
    change 0 ≤ inheritedKilling ω a x x
    by_cases h : x = 0
    · simp [h]
    · exact (inheritedKilling_pos ω hc a x h).le
  definite x hx := by
    by_contra hn
    exact (inheritedKilling_pos ω hc a x hn).ne' hx
  add_left x y z := by simp
  smul_left x y r := by simp [smul_eq_mul]

private theorem exp_natural {𝕜 𝕜' X Y : Type*}
    [RCLike 𝕜] [RCLike 𝕜']
    [NormedAddCommGroup X] [CompleteSpace X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    [NormedAddCommGroup Y] [CompleteSpace Y] [NormedSpace 𝕜' Y] [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜' Y]
    (D : X →L[𝕜] X) (E : Y →L[𝕜'] Y) (f : X →L[ℝ] Y)
    (hf : ∀ x, f (D x) = E (f x)) (x : X) :
    f (NormedSpace.exp D x) = NormedSpace.exp E (f x) := by
  have hp (n : ℕ) (y : X) : f ((D ^ n) y) = (E ^ n) (f y) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', mul_apply_eq_comp, hf, ih]
  have hD := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) D).mapL
    (f.comp ((ContinuousLinearMap.apply 𝕜 X x).restrictScalars ℝ))
  have hE := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜') E).mapL
    (ContinuousLinearMap.apply 𝕜' Y (f x))
  have hterm (n : ℕ) :
      f ((n.factorial⁻¹ : 𝕜) • (D ^ n) x) =
        (n.factorial⁻¹ : 𝕜') • (E ^ n) (f x) := by
    calc
      _ = f ((n.factorial⁻¹ : ℝ) • (D ^ n) x) := by
        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.ofReal_inv, RCLike.ofReal_natCast]
      _ = (n.factorial⁻¹ : ℝ) • (E ^ n) (f x) := by rw [map_smul, hp]
      _ = _ := by
        rw [RCLike.real_smul_eq_coe_smul (K := 𝕜'), RCLike.ofReal_inv, RCLike.ofReal_natCast]
  change HasSum (fun n : ℕ => f ((n.factorial⁻¹ : 𝕜) • (D ^ n) x))
    (f (NormedSpace.exp D x)) at hD
  change HasSum (fun n : ℕ => (n.factorial⁻¹ : 𝕜') • (E ^ n) (f x))
    (NormedSpace.exp E (f x)) at hE
  rw [funext hterm] at hD
  exact hD.unique hE

private theorem expAd_commute (f : L →ₗ⁅ℝ⁆ L) (z : L) (hf : f z = z) (x : L) :
    f (RegularSemisimple.expAdEquiv z x) = RegularSemisimple.expAdEquiv z (f x) := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : NormedSpace ℝ L := NormedSpace.restrictScalars ℝ ℂ L
  letI : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L z)
  exact exp_natural D D f.toLinearMap.toContinuousLinearMap (by
    intro y
    change f ⁅z, y⁆ = ⁅z, f y⁆
    rw [f.map_lie, hf]) x

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup
attribute [local instance] LieAlgebrasAndRepresentations.CompactCartanConjugacy.coreInnerProductSpace

local instance realEndTopologicalRing {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    IsTopologicalRing (V →L[ℝ] V) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (inferInstance : NonUnitalSeminormedRing (V →L[ℝ] V))

private theorem expAd_restrict {V : Type*} [LieRing V] [LieAlgebra ℝ V]
    [InnerProductSpace.Core ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ⁅ℝ⁆ L) (z x : V) :
    RegularSemisimple.expAdEquiv (f z) (f x) = f (NormedSpace.exp (adContinuous z) x) := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (Module.finrank ℂ L) → ℂ) (Module.finBasis ℂ L).equivFun
  letI : NormedSpace ℝ L := NormedSpace.restrictScalars ℝ ℂ L
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L (f z))
  exact (exp_natural (adContinuous z) D f.toLinearMap.toContinuousLinearMap (f.map_lie z) x).symm

private def expAdProduct (xs : List L) : L ≃ₗ⁅ℂ⁆ L :=
  xs.foldr (fun z g => g.trans (RegularSemisimple.expAdEquiv z)) LieEquiv.refl

private theorem expAdProduct_linear (xs : List L) :
    (expAdProduct xs).toLinearMap = (xs.map exponentialOperator).prod := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    ext x
    change RegularSemisimple.expAdEquiv z (expAdProduct xs x) =
      exponentialOperator z (((xs.map exponentialOperator).prod : Module.End ℂ L) x)
    rw [← ih]
    rfl

private theorem expAdProduct_commute (f : L →ₗ⁅ℝ⁆ L) (xs : List L)
    (hf : ∀ x ∈ xs, f x = x) (x : L) : f (expAdProduct xs x) = expAdProduct xs (f x) := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    change f (RegularSemisimple.expAdEquiv z (expAdProduct xs x)) =
      RegularSemisimple.expAdEquiv z (expAdProduct xs (f x))
    rw [expAd_commute f z (hf z (List.mem_cons_self)), ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))]

private theorem expAdProduct_restrict {V : LieSubalgebra ℝ L} [InnerProductSpace.Core ℝ V]
    [FiniteDimensional ℝ V] (xs : List V) (x : V) :
    expAdProduct (xs.map Subtype.val) (x : L) =
      (((innerProduct xs : V →L[ℝ] V) x : V) : L) := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    change RegularSemisimple.expAdEquiv (z : L)
      (expAdProduct (xs.map Subtype.val) (x : L)) =
        ((NormedSpace.exp (adContinuous z) ((innerProduct xs : V →L[ℝ] V) x) : V) : L)
    rw [ih]
    exact expAd_restrict V.incl z _

private theorem cartan_map_of_positive_image
    (hss : Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value ℂ L)
    (ω : Conjugation L) (a b g : L ≃ₗ⁅ℂ⁆ L)
    (hwa : Intertwines ω ω a) (hwb : Intertwines ω ω b)
    (H K : LieSubalgebra ℂ L) (hH : StableCartan ω a H) (hK : StableCartan ω b K)
    (hmap : g '' ((Subtype.val : fixedCompact ω a → L) '' (positiveCartan ω a H : Set _)) =
      (Subtype.val : fixedCompact ω b → L) '' (positiveCartan ω b K : Set _)) :
    H.map g.toLieHom = K := by
  ext x
  obtain ⟨y, rfl⟩ := g.surjective x
  change (g y ∈ H.map g.toLieHom) ↔ g y ∈ K
  rw [LieSubalgebra.mem_map]
  have hleft : (∃ z ∈ H, g.toLieHom z = g y) ↔ y ∈ H := by
    constructor
    · rintro ⟨z, hz, heq⟩
      exact g.injective heq ▸ hz
    · exact fun h => ⟨y, h, rfl⟩
  rw [hleft, ← centralizes_positiveCartan hss hwa hH,
    ← centralizes_positiveCartan hss hwb hK]
  constructor
  · intro hy z hz
    have him : (z : L) ∈ g '' ((Subtype.val : fixedCompact ω a → L) ''
        (positiveCartan ω a H : Set _)) := hmap ▸ ⟨z, hz, rfl⟩
    obtain ⟨_, ⟨t, ht, rfl⟩, e⟩ := him
    rw [← e, ← LieEquiv.map_lie, hy t ht, map_zero]
  · intro hy z hz
    have him : g (z : L) ∈ (Subtype.val : fixedCompact ω b → L) ''
        (positiveCartan ω b K : Set _) := hmap ▸ ⟨z, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨t, ht, et⟩ := him
    apply g.injective
    change g ⁅(z : L), y⁆ = g 0
    rw [LieEquiv.map_lie, ← et, hy t ht, map_zero]

private def mapFixedCompact {ω : Conjugation L} {a b g : L ≃ₗ⁅ℂ⁆ L}
    (hwg : Intertwines ω ω g) (hbg : ∀ x, b (g x) = g (a x)) :
    fixedCompact ω a ≃ₗ⁅ℝ⁆ fixedCompact ω b where
  toFun x := ⟨g (x : L), by
    obtain ⟨h₁, h₂⟩ := (mem_fixedCompact ω a x).mp x.property
    exact (mem_fixedCompact _ _ _).mpr ⟨by rw [hwg, h₁], by rw [hbg, h₂]⟩⟩
  invFun y := ⟨g.symm (y : L), by
    obtain ⟨h₁, h₂⟩ := (mem_fixedCompact ω b y).mp y.property
    apply (mem_fixedCompact _ _ _).mpr
    constructor <;> apply g.injective
    · change g (ω.map (g.symm (y : L))) = g (g.symm (y : L))
      rw [← hwg, g.apply_symm_apply, h₁]
    · change g (a (g.symm (y : L))) = g (g.symm (y : L))
      rw [← hbg, g.apply_symm_apply, h₂]⟩
  left_inv x := Subtype.ext (g.symm_apply_apply (x : L))
  right_inv x := Subtype.ext (g.apply_symm_apply (x : L))
  map_add' x y := Subtype.ext (map_add g (x : L) (y : L))
  map_smul' r x := Subtype.ext (g.toLinearEquiv.restrictScalars ℝ |>.map_smul r (x : L))
  map_lie' := by intro x y; exact Subtype.ext (g.map_lie (x : L) (y : L))

private theorem map_maximal_abelian {V W : Type*} [LieRing V] [LieAlgebra ℝ V]
    [LieRing W] [LieAlgebra ℝ W] (f : V ≃ₗ⁅ℝ⁆ W) {T : LieSubalgebra ℝ V}
    (hT : Maximal (fun S : LieSubalgebra ℝ V => IsLieAbelian S) T) :
    Maximal (fun S : LieSubalgebra ℝ W => IsLieAbelian S) (T.map f.toLieHom) := by
  constructor
  · refine ⟨fun x y => Subtype.ext ?_⟩
    obtain ⟨a, ha, ea⟩ := (T.mem_map f.toLieHom _).mp x.property
    obtain ⟨b, hb, eb⟩ := (T.mem_map f.toLieHom _).mp y.property
    change ⁅x.val, y.val⁆ = 0
    rw [← ea, ← eb, ← LieHom.map_lie, lie_eq_zero_of_abelian hT.1 ha hb, map_zero]
  · intro U hab hle y hy
    have ha : IsLieAbelian (U.comap f.toLieHom) :=
      ⟨fun x z => Subtype.ext (f.injective (by
        change f ⁅x.val, z.val⁆ = f 0
        rw [LieEquiv.map_lie, map_zero]
        exact lie_eq_zero_of_abelian hab x.property z.property))⟩
    have hl : T ≤ U.comap f.toLieHom :=
      fun x hx => hle ((T.mem_map f.toLieHom _).mpr ⟨x, hx, rfl⟩)
    exact (T.mem_map f.toLieHom _).mpr
      ⟨f.symm y, hT.2 ha hl (show f (f.symm y) ∈ U by simpa using hy), f.apply_symm_apply y⟩

theorem cartanAdjustment : cartanAdjustmentType.{u} := by
  intro L _ _ _ hss ω hc a b ha hb hwa hwb H K hH hK g hwg hbg
  let V := fixedCompact ω b
  letI : FiniteDimensional ℝ L := FiniteDimensional.trans ℝ ℂ L
  letI : FiniteDimensional ℝ V := FiniteDimensional.of_injective
    (fixedCompact ω b).incl.toLinearMap Subtype.val_injective
  letI : InnerProductSpace.Core ℝ V := fixedCore ω hc b
  let f := mapFixedCompact hwg hbg
  let T := (positiveCartan ω a H).map f.toLieHom
  let U := positiveCartan ω b K
  have hred := CartanDecompositionSignature.reductive_of_positive_invariant V
    (inheritedKilling ω b) (inheritedKilling_invariant ω b) (inheritedKilling_pos ω hc b)
  have hInv (z x y : V) : inner ℝ ⁅z, x⁆ y = -inner ℝ x ⁅z, y⁆ :=
    inheritedKilling_invariant ω b z x y
  obtain ⟨zs, hzs⟩ := maximalAbelian_conjugacy hred hInv T U
    (map_maximal_abelian f (maximal_positiveCartan hss hwa hH))
    (maximal_positiveCartan hss hwb hK)
  let xs : List L := zs.map Subtype.val
  let c := expAdProduct xs
  have hxs (x) (hx : x ∈ xs) : ω.map x = x ∧ b x = x := by
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
    exact (mem_fixedCompact ω b z).mp z.property
  refine ⟨c, ⟨xs, hxs, expAdProduct_linear xs⟩, ?_, ?_, ?_⟩
  · exact expAdProduct_commute ω.map xs (fun x hx => (hxs x hx).1)
  · exact expAdProduct_commute
      { (b.toLinearEquiv.restrictScalars ℝ).toLinearMap with map_lie' := fun {x y} => b.map_lie x y } xs
      (fun x hx => (hxs x hx).2)
  · apply cartan_map_of_positive_image hss ω a b _ hwa hwb H K hH hK
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hfx : f x ∈ T := ⟨x, hx, rfl⟩
      refine ⟨(innerProduct zs : V →L[ℝ] V) (f x), hzs ▸ ⟨f x, hfx, rfl⟩, ?_⟩
      exact (expAdProduct_restrict zs (f x)).symm
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, hxe⟩ := hzs.symm ▸ hz
      obtain ⟨t, ht, rfl⟩ := hx
      refine ⟨t, ⟨t, ht, rfl⟩, ?_⟩
      exact (expAdProduct_restrict zs (f t)).trans (congrArg Subtype.val hxe)

theorem realFormsIffCartanConjugates : realFormsIffCartanConjugatesType.{u} := by
  intro L _ _ _ hss ω hc a b ha hb hwa hwb H K hH hK
  rw [forms_isomorphic_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨g, hwg, hg⟩ := compact_intertwiner ω hc a b hwa hwb ha hb x hx
    obtain ⟨c, _, hwc, hbc, hmap⟩ :=
      cartanAdjustment hss ω hc a b ha hb hwa hwb H K hH hK g hwg hg
    exact ⟨g.trans c, fun z => (hwc (g z)).trans (congrArg c (hwg z)),
      fun z => (hbc (g z)).trans (congrArg c (hg z)), hmap⟩
  · rintro ⟨g, hwg, hg, _⟩
    exact ⟨g, fun z => by
      change b (ω.map (g z)) = g (a (ω.map z))
      rw [hwg, hg]⟩


open private serrePresentation exponential_eigenvector generators_ext
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

theorem torusCoordinates : torusCoordinatesType.{u} := by
  classical
  intro L _ _ _ hss ω H hH hω φ hφ e f hn hcompact z
  obtain ⟨c, a, A, hbasis, hA, hnonpos, P, he, hf, hh⟩ :=
    serrePresentation hss hH hφ e f hn
  letI := FiniteDimensional.fintypeBasisIndex a
  let h : H := (Module.evalEquiv ℂ H).symm
    (a.dualBasis.equivFun.symm (fun i => Complex.log (z i : ℂ)))
  have hz (i : _) : i.val h = Complex.log (z i : ℂ) := by
    rw [← (hbasis i).2]
    change (a i) ((Module.evalEquiv ℂ H).symm _) = _
    rw [Module.apply_evalEquiv_symm_apply, ← Module.Basis.dualBasis_equivFun,
      LinearEquiv.apply_symm_apply]
  let h' : H := ⟨ω.map (h : L), hω _ h.property⟩
  have hw : h' = h := by
    apply (Module.evalEquiv ℂ H).injective
    apply a.ext
    intro i
    change a i h' = a i h
    rw [(hbasis i).2, hz i]
    have Hf := (mem_rootSpace H (-i.val) (f i)).mp (hn i).2.1 h'
    have He := (mem_rootSpace H i.val (e i)).mp (hn i).1 h
    have Hw := congrArg ω.map He
    rw [LieHom.map_lie, ω.antilinear, hcompact i, hz, lie_neg, smul_neg, neg_inj] at Hw
    change ⁅(h' : L), f i⁆ = star (Complex.log (z i : ℂ)) • f i at Hw
    have Eq := smul_left_injective ℂ (hn i).2.2.2.1 (Hf.symm.trans Hw)
    change -(i.val h') = star (Complex.log (z i : ℂ)) at Eq
    have hre : (Complex.log (z i : ℂ)).re = 0 := by
      rw [Complex.log_re, Circle.norm_coe, Real.log_one]
    have hstar : -star (Complex.log (z i : ℂ)) = Complex.log (z i : ℂ) := by
      apply Complex.ext <;> simp [hre]
    exact (neg_eq_iff_eq_neg.mp Eq).trans hstar
  have hw' : ω.map (h : L) = (h : L) := congrArg Subtype.val hw
  let t := RegularSemisimple.expAdEquiv (h : L)
  refine ⟨h, hw', t, expAd_commute ω.map _ hw', rfl, ?_, ?_⟩
  · intro h'
    have hcomm : ⁅(h : L), (h' : L)⁆ = 0 :=
      congrArg Subtype.val (hH.1.1.trivial h h')
    have heig : ⁅(h : L), (h' : L)⁆ = (0 : ℂ) • (h' : L) := by simpa using hcomm
    rw [show t (h' : L) = Complex.exp 0 • (h' : L) from exponential_eigenvector _ _ _ heig,
      Complex.exp_zero, one_smul]
  · intro i
    have hne : (z i : ℂ) ≠ 0 := Circle.coe_ne_zero (z i)
    constructor
    · change RegularSemisimple.expAdEquiv (h : L) (e i) = _
      rw [exponential_eigenvector _ _ _ ((mem_rootSpace H _ _).mp (hn i).1 h),
        hz, Complex.exp_log hne]
    · change RegularSemisimple.expAdEquiv (h : L) (f i) = _
      rw [exponential_eigenvector _ _ _ ((mem_rootSpace H _ _).mp (hn i).2.1 h),
        LinearMap.neg_apply, hz, Complex.exp_neg, Complex.exp_log hne]

open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)

theorem torusKernel : torusKernelType.{u} := by
  classical
  intro L _ _ _ hss ω H hH hω φ hφ e f hn hcompact g
  constructor
  · rintro ⟨hgw, hg⟩
    obtain ⟨c, a, A, hbasis, hA, hnonpos, P, he, hf, hh⟩ :=
      serrePresentation hss hH hφ e f hn
    have hdiag (i : simple H φ) : ∃ z : Circle,
        g (e i) = (z : ℂ) • e i ∧ g (f i) = ((z : ℂ)⁻¹) • f i := by
      have hge : g (e i) ∈ rootSpace_value H i.val := by
        apply (mem_rootSpace H _ _).mpr
        intro h
        rw [← hg h, ← g.map_lie, (mem_rootSpace H _ _).mp (hn i).1, map_smul]
      have hline : rootSpace_value H i.val = ℂ ∙ e i :=
        eq_span_singleton_of_mem_of_finrank_eq_one
          (finrank_rootSpace_eq_one hss H hH i.val i.property.1.1)
          (hn i).1 (hn i).2.2.1
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hline ▸ hge)
      have hgf : g (f i) = star k • f i := by
        have h := congrArg ω.map hk.symm
        rw [hgw, hcompact i, ω.antilinear, hcompact i, map_neg, smul_neg, neg_inj] at h
        exact h
      have hbr : ⁅e i, f i⁆ = (c i : L) := by
        rw [(hbasis i).1]
        exact (hn i).2.2.2.2
      have hcor : (c i : L) ≠ 0 := fun hz => c.ne_zero i (Subtype.ext hz)
      have hmul := g.map_lie (e i) (f i)
      rw [hbr, hg, ← hk, hgf, smul_lie, lie_smul, smul_smul, hbr] at hmul
      have hks : k * star k = 1 := smul_left_injective ℂ hcor
        (hmul.symm.trans (one_smul ℂ (c i : L)).symm)
      have hnorm : ‖k‖ = 1 := by
        have hh' := congrArg Complex.re hks
        rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re,
          Complex.normSq_eq_norm_sq] at hh'
        nlinarith [norm_nonneg k]
      let z : Circle := ⟨k, mem_sphere_zero_iff_norm.mpr hnorm⟩
      have hki : star k = k⁻¹ := by
        apply mul_left_cancel₀ z.coe_ne_zero
        change k * star k = k * k⁻¹
        rw [hks, mul_inv_cancel₀ z.coe_ne_zero]
      refine ⟨z, hk.symm, ?_⟩
      exact hgf.trans (congrArg (fun s : ℂ => s • f i) hki)
    choose z hz using hdiag
    obtain ⟨h, hw, t, htw, htexp, hth, ht⟩ :=
      torusCoordinates hss ω H hH hω φ hφ e f hn hcompact z
    have heq : g = t := generators_ext e f c A P he hf hh
      (fun i => (hz i).1.trans (ht i).1.symm)
      (fun i => (hz i).2.trans (ht i).2.symm)
      (fun i => (hg (c i)).trans (hth (c i)).symm)
    exact ⟨h, hw, heq.symm ▸ htexp⟩
  · rintro ⟨h, hw, he⟩
    have heq : g = RegularSemisimple.expAdEquiv (h : L) := by
      apply LieEquiv.ext
      intro z
      exact LinearMap.congr_fun he z
    subst g
    refine ⟨expAd_commute ω.map _ hw, ?_⟩
    intro y
    have hzero : ⁅(h : L), (y : L)⁆ = (0 : ℂ) • (y : L) := by
      rw [zero_smul]
      exact congrArg (fun t : H => (t : L)) (hH.1.1.trivial h y)
    rw [exponential_eigenvector _ _ _ hzero, Complex.exp_zero, one_smul]


theorem torusConjugacy : torusConjugacyType.{u} := by
  classical
  intro L _ _ _ hss ω H hH hω φ hφ e f hnorm hcompact a b σ hσ m n hm hn ha hb
  obtain ⟨c, ar, A, hbasis, hA, hnonpos, P, he, hf, hh⟩ :=
    serrePresentation hss hH hφ e f hnorm
  constructor
  · intro hfix
    obtain ⟨z, hz⟩ := (normalizeMultipliers σ hσ m n hm hn).mpr hfix
    obtain ⟨h, hw, t, htw, hexp, hth, ht⟩ :=
      torusCoordinates hss ω H hH hω φ hφ e f hnorm hcompact z
    have hcoeff (i) : (z i : ℂ) * m i = (n i : ℂ) * z (σ i) := by
      have h := congrFun hz i
      change z i / z (σ i) * m i = n i at h
      have h' : z i * m i = n i * z (σ i) := by
        rwa [div_mul_eq_mul_div, div_eq_iff_eq_mul] at h
      exact congrArg (fun w : Circle => (w : ℂ)) h'
    have hce (i) : (c i : L) = (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H i.val : L) :=
      congrArg Subtype.val (hbasis i).1
    have hg : t.trans a = b.trans t := by
      apply generators_ext e f c A P he hf hh
      · intro i
        change a (t (e i)) = t (b (e i))
        rw [(ht i).1, (hb i).1, map_smul, map_smul, (ha i).1, (ht (σ i)).1,
          smul_smul, smul_smul, hcoeff]
      · intro i
        change a (t (f i)) = t (b (f i))
        rw [(ht i).2, (hb i).2.1, map_smul, map_smul, (ha i).2.1, (ht (σ i)).2,
          smul_smul, smul_smul, ← mul_inv, ← mul_inv, hcoeff]
      · intro i
        change a (t (c i : L)) = t (b (c i : L))
        rw [hth, hce, (ha i).2.2, (hb i).2.2, hth]
    exact ⟨t, htw, hth, fun x => congrArg (fun g : L ≃ₗ⁅ℂ⁆ L => g x) hg⟩
  · rintro ⟨t, htw, hth, ht⟩ i hi
    have hte : t (e i) ∈ rootSpace_value H i.val := by
      apply (mem_rootSpace H _ _).mpr
      intro h
      rw [← hth h, ← t.map_lie, (mem_rootSpace H _ _).mp (hnorm i).1, map_smul]
    have hline : rootSpace_value H i.val = ℂ ∙ e i :=
      eq_span_singleton_of_mem_of_finrank_eq_one
        (finrank_rootSpace_eq_one hss H hH i.val i.property.1.1)
        (hnorm i).1 (hnorm i).2.2.1
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hline ▸ hte)
    have hnz : t (e i) ≠ 0 := fun ht0 => (hnorm i).2.2.1
      (t.injective (ht0.trans (map_zero t).symm))
    have ha' : a (t (e i)) = (m i : ℂ) • t (e i) := by
      calc
        _ = a (k • e i) := congrArg a hk.symm
        _ = k • ((m i : ℂ) • e i) := by rw [map_smul, (ha i).1, hi]
        _ = (m i : ℂ) • (k • e i) := smul_comm k (m i : ℂ) (e i)
        _ = _ := congrArg (fun y : L => (m i : ℂ) • y) hk
    have hb' : t (b (e i)) = (n i : ℂ) • t (e i) := by
      rw [(hb i).1, hi, map_smul]
    exact Circle.ext (smul_left_injective ℂ hnz (ha'.symm.trans ((ht (e i)).trans hb')))

end CartanAdjustment

section InnerDatum

open LieAlgebrasAndRepresentations.RealForms (Conjugation)
open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition (diagramAutomorphisms inner)
open Specs.LieAlgebrasAndRepresentations.CartanConjugacy (innerAutomorphisms_value)
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData (DiagramData)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open private serrePresentation generators_ext toAut asLieEquiv
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

/-- A normalized Vogan involution is inner exactly when it fixes the Cartan
pointwise, or equivalently when its diagram permutation is the identity. -/
theorem normalizedInnerIffFixesCartan
    {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (ω : Conjugation L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (hω : ∀ h ∈ H, ω.map h ∈ H)
    (φ : Direction H) (hφ : Regular H φ)
    (e f : simple H φ → L) (hn : Normalized H φ e f) (hw : ∀ i, ω.map (e i) = -f i)
    (A : Matrix (simple H φ) (simple H φ) ℤ) (d : DiagramData A) (a : L ≃ₗ⁅ℂ⁆ L)
    (hA : ∀ i j, (A i j : ℂ) = j.val (coroot_value H i.val))
    (ha : ∀ i, a (e i) = d.sign i • e (d.perm i) ∧
      a (f i) = d.sign i • f (d.perm i) ∧
      a (coroot_value H i.val : L) = (coroot_value H (d.perm i).val : L)) :
    (a.toLinearEquiv ∈ innerAutomorphisms_value L ↔ ∀ h : H, a (h : L) = (h : L)) ∧
    ((∀ h : H, a (h : L) = (h : L)) ↔ ∀ i, d.perm i = i) := by
  classical
  obtain ⟨c, _, B, hbasis, _, _, P, he, hf, hh⟩ := serrePresentation hss hH hφ e f hn
  obtain ⟨_, s, hs, hintersection, _⟩ :=
    AutomorphismDecomposition.decomposition hss H hH φ hφ e f hn
  let p : diagramAutomorphisms H φ := ⟨d.perm, by
    intro i j
    rw [← hA, ← hA, d.preserves]⟩
  let z (i : simple H φ) : Circle :=
    ⟨d.sign i, mem_sphere_zero_iff_norm.mpr (by
      rcases d.sign_cases i with hi | hi <;> simp [hi])⟩
  obtain ⟨h, _, t, _, ht_exp, ht_cartan, ht⟩ :=
    torusCoordinates hss ω H hH hω φ hφ e f hn hw z
  have hcor (i : simple H φ) :
      (c i : L) = (coroot_value H i.val : L) := congrArg Subtype.val (hbasis i).1
  have ha_cor (i : simple H φ) : a (c i : L) = (c (d.perm i) : L) := by
    rw [hcor, (ha i).2.2, hcor]
  have ha_factor : a = t.trans (asLieEquiv (s p)) := by
    apply generators_ext e f c B P he hf hh
    · intro i
      change a (e i) = asLieEquiv (s p) (t (e i))
      rw [(ht i).1, map_smul, (ha i).1]
      exact congrArg (d.sign i • ·) (hs p i).1.symm
    · intro i
      change a (f i) = asLieEquiv (s p) (t (f i))
      rw [(ht i).2, map_smul, (ha i).2.1]
      have hi : (d.sign i)⁻¹ = d.sign i := by
        rcases d.sign_cases i with hi | hi <;> simp [hi]
      change d.sign i • f (d.perm i) = (d.sign i)⁻¹ • (s p).val (f i)
      rw [hi, (hs p i).2.1]
    · intro i
      change a (c i : L) = asLieEquiv (s p) (t (c i : L))
      rw [ht_cartan, hcor, (ha i).2.2]
      exact (hs p i).2.2.symm
  have ht_inner : toAut t ∈ inner L := by
    rw [AutomorphismDecomposition.innerGenerated L]
    exact Subgroup.subset_closure ⟨(h : L), ht_exp⟩
  have ha_inner : a.toLinearEquiv ∈ innerAutomorphisms_value L ↔ p = 1 := by
    have ha_mul : toAut a = s p * toAut t := by
      rw [ha_factor]
      rfl
    change toAut a ∈ inner L ↔ p = 1
    rw [← hintersection p, ha_mul]
    exact ⟨fun hm => by simpa using (inner L).mul_mem hm ((inner L).inv_mem ht_inner),
      fun hm => (inner L).mul_mem hm ht_inner⟩
  have hfix : (∀ x : H, a (x : L) = (x : L)) ↔ ∀ i, d.perm i = i := by
    constructor
    · intro hfixed i
      exact c.injective (Subtype.ext ((ha_cor i).symm.trans (hfixed (c i))))
    · intro hperm
      have heq : a.toLinearMap.comp H.incl.toLinearMap = H.incl.toLinearMap := by
        apply c.ext
        intro i
        change a (c i : L) = (c i : L)
        rw [ha_cor, hperm]
      exact fun x => LinearMap.congr_fun heq x
  have hp : p = 1 ↔ ∀ i, d.perm i = i := by
    constructor
    · intro h i
      exact congrArg (fun g : diagramAutomorphisms H φ => g.val i) h
    · intro h
      exact Subtype.ext (Equiv.ext h)
  exact ⟨ha_inner.trans (hp.trans hfix.symm), hfix⟩

end InnerDatum

section RootTransport

open Module (Dual)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
open Specs.LieAlgebrasAndRepresentations.VoganEquivalence
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures (IsCompact)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {H K : LieSubalgebra ℂ L}

theorem transportRoots_apply (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = K)
    (α : Dual ℂ H) (x : H) :
    transportRoots g hg α (g.ofSubalgebras H K hg x) = α x := by
  change α ((g.ofSubalgebras H K hg).toLinearEquiv.symm
    ((g.ofSubalgebras H K hg).toLinearEquiv x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem mem_rootSpace_transport (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = K)
    (α : Dual ℂ H) (x : L) :
    g x ∈ rootSpace_value K (transportRoots g hg α) ↔ x ∈ rootSpace_value H α := by
  rw [mem_rootSpace, mem_rootSpace]
  let k := g.ofSubalgebras H K hg
  have eqn (y : H) :
      (⁅(k y : L), g x⁆ = transportRoots g hg α (k y) • g x) ↔
        ⁅(y : L), x⁆ = α y • x := by
    change (⁅g (y : L), g x⁆ = transportRoots g hg α (k y) • g x) ↔ _
    rw [transportRoots_apply, ← g.map_lie, ← map_smul g]
    exact g.injective.eq_iff
  refine ⟨fun h y => (eqn y).mp (h (k y)), ?_⟩
  intro h y
  obtain ⟨z, rfl⟩ := k.surjective y
  exact (eqn z).mpr (h z)

theorem rootSpace_map_transport (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = K)
    (α : Dual ℂ H) :
    (rootSpace_value H α).map g.toLinearMap = rootSpace_value K (transportRoots g hg α) := by
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  change g x ∈ (rootSpace_value H α).map g.toLinearMap ↔
    g x ∈ rootSpace_value K (transportRoots g hg α)
  rw [mem_rootSpace_transport g hg]
  exact ⟨fun ⟨z, hz, he⟩ => g.injective he ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩

theorem transportRoots_mem (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = K)
    (α : Dual ℂ H) : transportRoots g hg α ∈ rootSet_value K ↔ α ∈ rootSet_value H := by
  change (_ ≠ 0 ∧ rootSpace_value K _ ≠ ⊥) ↔ (α ≠ 0 ∧ rootSpace_value H α ≠ ⊥)
  rw [← rootSpace_map_transport g hg]
  exact and_congr ((transportRoots g hg).map_ne_zero_iff)
    (Submodule.map_ne_bot_iff (e := g.toLinearEquiv))

theorem involutionCartanMap (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a)
    (hs : ∀ x ∈ H, a x ∈ H) : H.map a.toLieHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hs y hy
  · intro hx
    exact ⟨a x, hs x hx, ha x⟩

theorem transportRoots_involution (a : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a)
    (hs : ∀ x ∈ H, a x ∈ H) (α : Dual ℂ H) :
    transportRoots a (involutionCartanMap a ha hs) α = rootAction a H hs α := by
  ext y
  let k := a.ofSubalgebras H H (involutionCartanMap a ha hs)
  obtain ⟨x, rfl⟩ := k.surjective y
  change transportRoots a (involutionCartanMap a ha hs) α (k x) = rootAction a H hs α (k x)
  rw [transportRoots_apply]
  change α x = α ⟨a (a (x : L)), _⟩
  exact congrArg α (Subtype.ext (ha x).symm)

variable [FiniteDimensional ℂ L]

theorem coroot_map_transport (hss : IsSemisimple ℂ L)
    (hH : IsMaximalToral H) (hK : IsMaximalToral K)
    (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = K) (α : Dual ℂ H) :
    (g.ofSubalgebras H K hg) (coroot_value H α) = coroot_value K (transportRoots g hg α) := by
  let k := g.ofSubalgebras H K hg
  have ht : k (tAlpha H α) = tAlpha K (transportRoots g hg α) := by
    apply tAlpha_unique hss K hK
    intro x
    obtain ⟨y, rfl⟩ := k.surjective x
    change _root_.killingForm ℂ L (g (tAlpha H α : L)) (g (y : L)) =
      transportRoots g hg α (g.ofSubalgebras H K hg y)
    rw [transportRoots_apply]
    exact (LieAlgebra.killingForm_of_equiv_apply g _ _).trans (tAlpha_pairing hss H hH α y)
  have hB : rootForm K (transportRoots g hg α) (transportRoots g hg α) = rootForm H α α := by
    rw [rootForm_apply, ← ht, rootForm_apply]
    exact LieAlgebra.killingForm_of_equiv_apply g _ _
  change k (killingCoroot H α) = killingCoroot K (transportRoots g hg α)
  simp only [killingCoroot_eq, map_smul, ht, hB]

/-- A Cartan transporter induces an isomorphism of the complete root systems. -/
def rootIsomOfTransport (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hK : IsMaximalToral K) (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = K) : RootIsom H K where
  linear := transportRoots g hg
  roots := transportRoots_mem g hg
  pairing α _ β _ := by
    rw [← coroot_map_transport hss hH hK g hg, transportRoots_apply]

theorem eqOnCartan_of_same_transport (g n : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = K)
    (hn : H.map n.toLieHom = K) (h : transportRoots g hg = transportRoots n hn) (x : H) :
    g (x : L) = n (x : L) := by
  have hk : g.ofSubalgebras H K hg x = n.ofSubalgebras H K hn x := by
    apply (Module.evalEquiv ℂ K).injective
    ext β
    obtain ⟨α, rfl⟩ := (transportRoots n hn).surjective β
    change transportRoots n hn α (g.ofSubalgebras H K hg x) =
      transportRoots n hn α (n.ofSubalgebras H K hn x)
    rw [transportRoots_apply, ← h, transportRoots_apply]
  exact congrArg Subtype.val hk

end RootTransport

section RootLifts

open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations
open PolarRealStructures (IsCompact)
open MaximalTori (IsMaximalToral_value)
open SolvableRadical (IsSemisimple_value)
open RootDecomposition (rootSet_value rootSpace_value)
open RootForm (coroot_value)
open VermaModules (Direction Regular)
open SerreRelations (simple positive)
open IntegrableHighestWeightQuotient (Normalized)
open Module (Dual)

open private rootSet_spans from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
open private compact_triple root_conjugation from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.StableCartanVoganData
open private serrePresentation from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem rootIsom_finite (hss : IsSemisimple_value ℂ L)
    {H K : LieSubalgebra ℂ L}
    (hH : IsMaximalToral_value H) (hK : IsMaximalToral_value K) :
    Finite (RootIsom H K) := by
  classical
  let : Finite (rootSet_value H) := (rootSet_finite H hH.1).to_subtype
  let : Finite (rootSet_value K) := (rootSet_finite K hK.1).to_subtype
  let e (r : RootIsom H K) (α : rootSet_value H) : rootSet_value K :=
    ⟨r.linear α.val, (r.roots α.val).mpr α.property⟩
  refine Finite.of_injective e ?_
  intro r s h
  have hl : r.linear = s.linear := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on (rootSet_spans hss hH)
    intro α hα
    exact congrArg Subtype.val (congrFun h ⟨α, hα⟩)
  cases r
  cases s
  cases hl
  rfl

private def pullbackDirection {H K : LieSubalgebra ℂ L} (r : RootIsom H K)
    (φ : Direction K) : Direction H :=
  φ.comp (r.linear.toLinearMap.restrictScalars ℝ)

private theorem pullback_regular {H K : LieSubalgebra ℂ L} (r : RootIsom H K)
    {φ : Direction K} (hφ : Regular K φ) : Regular H (pullbackDirection r φ) :=
  fun α hα => hφ (r.linear α) ((r.roots α).mpr hα)

private def positiveSimpleEquiv {H K : LieSubalgebra ℂ L} {ψ : Direction H} {φ : Direction K}
    (r : Dual ℂ H ≃ₗ[ℂ] Dual ℂ K)
    (hpos : ∀ α, α ∈ positive H ψ ↔ r α ∈ positive K φ) :
    simple H ψ ≃ simple K φ := by
  apply r.toEquiv.subtypeEquiv
  intro α
  change (α ∈ positive H ψ ∧ ∀ β ∈ positive H ψ, ∀ γ ∈ positive H ψ, α ≠ β + γ) ↔
    (r α ∈ positive K φ ∧ ∀ β ∈ positive K φ, ∀ γ ∈ positive K φ, r α ≠ β + γ)
  refine and_congr (hpos α) ⟨?_, ?_⟩
  · intro h β hβ γ hγ he
    obtain ⟨β, rfl⟩ := r.surjective β
    obtain ⟨γ, rfl⟩ := r.surjective γ
    apply h β ((hpos β).mpr hβ) γ ((hpos γ).mpr hγ)
    exact r.injective (he.trans (r.map_add β γ).symm)
  · intro h β hβ γ hγ he
    exact h _ ((hpos β).mp hβ) _ ((hpos γ).mp hγ)
      ((congrArg r he).trans (r.map_add β γ))

private def liftSimpleEquiv {H K : LieSubalgebra ℂ L} (r : RootIsom H K)
    (φ : Direction K) : simple H (pullbackDirection r φ) ≃ simple K φ :=
  positiveSimpleEquiv r.linear (fun α => by
    change (α ∈ rootSet_value H ∧ 0 < φ (r.linear α)) ↔ _
    exact and_congr_left' (r.roots α).symm)

private theorem liftSimpleEquiv_apply {H K : LieSubalgebra ℂ L} (r : RootIsom H K)
    (φ : Direction K) (i : simple H (pullbackDirection r φ)) :
    (liftSimpleEquiv r φ i).val = r.linear i.val :=
  rfl

private theorem compact_pinning (hss : IsSemisimple_value ℂ L)
    (ω : Conjugation L) (hc : IsCompact ω)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral_value H)
    (hw : ∀ x ∈ H, ω.map x ∈ H) (φ : Direction H) :
    ∃ e f : simple H φ → L, Normalized H φ e f ∧ ∀ i, ω.map (e i) = -f i := by
  classical
  choose e he hne hbr using fun i : simple H φ =>
    compact_triple hss ω hc H hH hw i.val i.property.1.1
  refine ⟨e, fun i => -ω.map (e i), ?_, fun i => (neg_neg _).symm⟩
  intro i
  refine ⟨he i, Submodule.neg_mem _ (root_conjugation ω hc H hw _ (he i) (hne i)),
    hne i, neg_ne_zero.mpr ?_, hbr i⟩
  intro hz
  exact hne i (ω.involutive.injective (hz.trans (map_zero ω.map).symm))

omit [FiniteDimensional ℂ L] in
private theorem pinning_intertwines (ω : Conjugation L)
    {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)
    (P : Serre.Algebra A ≃ₗ⁅ℂ⁆ L) (g : L ≃ₗ⁅ℂ⁆ L)
    (e f c e' f' c' : ι → L)
    (he : ∀ i, P (Serre.e A i) = e i) (hf : ∀ i, P (Serre.f A i) = f i)
    (hh : ∀ i, P (Serre.h A i) = c i)
    (hc : ∀ i, c i = ⁅e i, f i⁆) (hc' : ∀ i, c' i = ⁅e' i, f' i⁆)
    (hw : ∀ i, ω.map (e i) = -f i) (hw' : ∀ i, ω.map (e' i) = -f' i)
    (hge : ∀ i, g (e i) = e' i) (hgf : ∀ i, g (f i) = f' i)
    (hgc : ∀ i, g (c i) = c' i) : Intertwines ω ω g := by
  have wneg {x y : L} (h : ω.map x = -y) : ω.map y = -x := by
    have hh := congrArg ω.map h
    rw [ω.involutive, map_neg] at hh
    exact neg_eq_iff_eq_neg.mp hh.symm
  have wc {e f c : L} (he : ω.map e = -f) (hc : c = ⁅e, f⁆) : ω.map c = -c := by
    rw [hc, LieHom.map_lie, he, wneg he, neg_lie, lie_neg, neg_neg, lie_skew]
  let d : L →ₗ⁅ℂ⁆ L :=
    { toFun := fun x => ω.map (g (ω.map x))
      map_add' := by intro x y; simp
      map_smul' := by intro a x; simp [ω.antilinear]
      map_lie' := by intro x y; rw [LieHom.map_lie, g.map_lie, LieHom.map_lie] }
  have hd : d.comp P.toLieHom = g.toLieHom.comp P.toLieHom := by
    apply Serre.hom_ext A <;> intro i
    · change ω.map (g (ω.map (P (Serre.e A i)))) = g (P (Serre.e A i))
      rw [he, hw, map_neg, hgf, map_neg, wneg (hw' i), neg_neg, hge]
    · change ω.map (g (ω.map (P (Serre.f A i)))) = g (P (Serre.f A i))
      rw [hf, wneg (hw i), map_neg, hge, map_neg, hw', neg_neg, hgf]
    · change ω.map (g (ω.map (P (Serre.h A i)))) = g (P (Serre.h A i))
      rw [hh, wc (hw i) (hc i), map_neg, hgc, map_neg, wc (hw' i) (hc' i), neg_neg]
  intro x
  obtain ⟨y, hy⟩ := P.surjective (ω.map x)
  have h := LieHom.congr_fun hd y
  change ω.map (g (ω.map (P y))) = g (P y) at h
  change P y = _ at hy
  rwa [hy, ω.involutive] at h

set_option maxHeartbeats 1200000 in
theorem compactRootLifts : compactRootLiftsType.{u} := by
  classical
  intro L _ _ _ hss ω hw H K hH hK hwH hwK φ hφ
  refine ⟨rootIsom_finite hss hH hK, ?_⟩
  intro r
  let ψ := pullbackDirection r φ
  let : DecidableEq (simple H ψ) := fun i j => Subtype.instDecidableEq i j
  have hψ := pullback_regular r hφ
  let p := liftSimpleEquiv r φ
  have hp (i : simple H ψ) : (p i).val = r.linear i.val := liftSimpleEquiv_apply r φ i
  obtain ⟨e, f, hn, hc⟩ := compact_pinning hss ω hw H hH hwH ψ
  obtain ⟨e', f', hn', hc'⟩ := compact_pinning hss ω hw K hK hwK φ
  obtain ⟨c, a, A, hca, hA, hAnon, P, hPe, hPf, hPh⟩ :=
    serrePresentation hss hH hψ e f hn
  obtain ⟨c', _, _, hca', _, _, _, _, _, _⟩ :=
    serrePresentation hss hK hφ e' f' hn'
  obtain ⟨A', hA', hbasic, hserre, hspan⟩ := serre_relations hss K hK φ hφ e' f' hn'
  have hmat (i j : simple H ψ) : A' (p i) (p j) = A i j := by
    apply Int.cast_injective (α := ℂ)
    rw [← hA', hA, (hca _).1, hp, hp]
    exact r.pairing _ i.property.1.1 _ j.property.1.1
  have hrel : Serre.RelationsHold A (e' ∘ p) (f' ∘ p) (fun i => (c' (p i) : L)) := by
    have hcv (j) : c' j = coroot_value K j.val := (hca' j).1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      simpa only [hcv] using (hbasic (p i) (p j)).1
    · intro i j
      simpa only [Function.comp_apply, hcv, hmat, Int.cast_smul_eq_zsmul ℂ] using
        (hbasic (p i) (p j)).2.1
    · intro i j
      simpa only [Function.comp_apply, hcv, hmat, neg_smul, Int.cast_smul_eq_zsmul ℂ] using
        (hbasic (p i) (p j)).2.2.1
    · intro i j
      simpa only [Function.comp_apply, hcv, p.injective.eq_iff] using
        (hbasic (p i) (p j)).2.2.2
    · intro i j hij
      rw [Serre.iterBracket_eq_pow, Function.comp_apply, Function.comp_apply, ← hmat]
      exact (hserre (p i) (p j) (p.injective.ne hij)).2.1
    · intro i j hij
      rw [Serre.iterBracket_eq_pow, Function.comp_apply, Function.comp_apply, ← hmat]
      exact (hserre (p i) (p j) (p.injective.ne hij)).2.2
  let g₀ := (Serre.lift A hAnon (e' ∘ p) (f' ∘ p) _ hrel).comp P.symm.toLieHom
  have hge (i) : g₀ (e i) = e' (p i) := by
    rw [← hPe i]
    simp [g₀]
  have hgf (i) : g₀ (f i) = f' (p i) := by
    rw [← hPf i]
    simp [g₀]
  have hgc (i) : g₀ (c i : L) = (c' (p i) : L) := by
    rw [← hPh i]
    simp [g₀]
  have hg_surj : Function.Surjective g₀ := by
    rw [← LieHom.range_eq_top, ← top_le_iff, ← hspan, LieSubalgebra.lieSpan_le]
    rintro x ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    all_goals obtain ⟨i, rfl⟩ := p.surjective j
    · exact ⟨e i, hge i⟩
    · exact ⟨f i, hgf i⟩
    · refine ⟨(c i : L), ?_⟩
      change g₀ (c i : L) = (coroot_value K (p i).val : L)
      rw [hgc, (hca' _).1]
  let g := LieEquiv.ofBijective g₀
    ⟨LinearMap.injective_iff_surjective.mpr hg_surj, hg_surj⟩
  let w := c.equiv c' p
  have hwg (x : H) : g (x : L) = (w x : L) := by
    have h : g.toLinearMap.comp H.toSubmodule.subtype =
        K.toSubmodule.subtype.comp w.toLinearMap := by
      apply c.ext
      intro i
      change g (c i : L) = (w (c i) : L)
      rw [Module.Basis.equiv_apply]
      exact hgc i
    exact LinearMap.congr_fun h x
  have hgmap : H.map g.toLieHom = K := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      change g x ∈ K
      rw [hwg ⟨x, hx⟩]
      exact (w ⟨x, hx⟩).property
    · intro hx
      obtain ⟨y, hy⟩ := w.surjective ⟨x, hx⟩
      exact ⟨y, y.property, (hwg y).trans (congrArg Subtype.val hy)⟩
  refine ⟨g, ?_, hgmap, ?_⟩
  · exact pinning_intertwines ω A P g e f (fun i => (c i : L))
      (e' ∘ p) (f' ∘ p) (fun i => (c' (p i) : L))
      hPe hPf hPh
      (fun i => by rw [(hca i).1]; exact (hn i).2.2.2.2.symm)
      (fun i => by rw [(hca' (p i)).1]; exact (hn' (p i)).2.2.2.2.symm)
      hc (fun i => hc' (p i)) hge hgf hgc
  · have heq : (g.ofSubalgebras H K hgmap).toLinearEquiv = w := by
      apply LinearEquiv.ext
      intro x
      exact Subtype.ext (hwg x)
    unfold transportRoots
    rw [heq]
    apply LinearEquiv.toLinearMap_injective
    apply a.ext
    intro i
    apply c'.ext
    intro j
    obtain ⟨k, rfl⟩ := p.surjective j
    change (a i) (w.symm (c' (p k))) = (r.linear (a i)) (c' (p k))
    have hwk : w.symm (c' (p k)) = c k := by
      apply w.injective
      rw [w.apply_symm_apply]
      exact (Module.Basis.equiv_apply (b := c) (i := k) (b' := c') (e := p)).symm
    rw [hwk, (hca i).2, (hca k).1, (hca' (p k)).1, hp]
    exact (r.pairing _ k.property.1.1 _ i.property.1.1).symm

end RootLifts

section FiniteTest

open Module (Dual)
open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
open Specs.LieAlgebrasAndRepresentations.RootDecomposition
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open scoped ComplexConjugate

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {K : LieSubalgebra ℂ L} {φ : Direction K}

omit [FiniteDimensional ℂ L] in
private theorem compact_symm (ω : Conjugation L) (g : L ≃ₗ⁅ℂ⁆ L)
    (h : Intertwines ω ω g) : Intertwines ω ω g.symm := by
  intro x
  apply g.injective
  change g (ω.map (g.symm x)) = g (g.symm (ω.map x))
  rw [← h]
  simp only [g.apply_symm_apply]

/-- A compact involution with the prescribed simple-root action has reciprocal
unit multipliers, and its actions on the opposite lines and coroots are forced. -/
theorem involutionMultipliers (hss : IsSemisimple ℂ L) (hK : IsMaximalToral K)
    (ω : Conjugation L) (c : L ≃ₗ⁅ℂ⁆ L) (hc : Function.Involutive c)
    (hcw : Intertwines ω ω c) (hcs : ∀ x ∈ K, c x ∈ K)
    (e f : simple K φ → L) (hn : Normalized K φ e f)
    (hcompact : ∀ i, ω.map (e i) = -f i)
    (σ : Equiv.Perm (simple K φ)) (hσ : Function.Involutive σ)
    (hline : ∀ i, c (e i) ∈ rootSpace_value K (σ i).val) :
    ∃ m : simple K φ → Circle, (∀ i, m (σ i) = (m i)⁻¹) ∧
      ∀ i, c (e i) = (m i : ℂ) • e (σ i) ∧
        c (f i) = ((m i : ℂ)⁻¹) • f (σ i) ∧
        c (coroot_value K i.val : L) = (coroot_value K (σ i).val : L) := by
  classical
  let hmap := involutionCartanMap c hc hcs
  have hdiag (i : simple K φ) : ∃ z : Circle,
      c (e i) = (z : ℂ) • e (σ i) ∧
      c (f i) = ((z : ℂ)⁻¹) • f (σ i) ∧
      c (coroot_value K i.val : L) = (coroot_value K (σ i).val : L) := by
    have hnz : c (e i) ≠ 0 := fun h => (hn i).2.2.1
      (c.injective (h.trans (map_zero c).symm))
    have hroot : transportRoots c hmap i.val = (σ i).val := by
      ext x
      apply smul_left_injective ℂ hnz
      exact (((mem_rootSpace K _ _).mp
        ((mem_rootSpace_transport c hmap _ _).mpr (hn i).1)) x).symm.trans
        ((mem_rootSpace K _ _).mp (hline i) x)
    have hcor := congrArg (fun x : K => (x : L)) (coroot_map_transport hss hK hK c hmap i.val)
    change c (coroot_value K i.val : L) = (coroot_value K (transportRoots c hmap i.val) : L) at hcor
    rw [hroot] at hcor
    have hspan : rootSpace_value K (σ i).val = ℂ ∙ e (σ i) :=
      eq_span_singleton_of_mem_of_finrank_eq_one
        (finrank_rootSpace_eq_one hss K hK (σ i).val (σ i).property.1.1)
        (hn (σ i)).1 (hn (σ i)).2.2.1
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hline i)
    have hcf : c (f i) = star k • f (σ i) := by
      have h := congrArg ω.map hk.symm
      rwa [hcw, hcompact i, ω.antilinear, hcompact (σ i), map_neg, smul_neg, neg_inj] at h
    obtain ⟨E, F, hE, hF, hEn, hFn, _, hbr, _⟩ :=
      exists_root_triple hss K hK (σ i).val (σ i).property.1.1
    have hcn : (coroot_value K (σ i).val : L) ≠ 0 := by
      intro h
      have hz : (2 : ℂ) • E = 0 := by simpa only [h, zero_lie] using hbr.symm
      exact (smul_ne_zero (by norm_num) hEn) hz
    have hbracket (j : simple K φ) : ⁅e j, f j⁆ = (coroot_value K j.val : L) :=
      (hn j).2.2.2.2
    have h := c.map_lie (e i) (f i)
    rw [hbracket i, hcor, ← hk, hcf, smul_lie, lie_smul, smul_smul, hbracket] at h
    have hmul : k * star k = 1 := smul_left_injective ℂ hcn
      (h.symm.trans (one_smul ℂ _).symm)
    have hnorm : ‖k‖ = 1 := by
      have hr := congrArg Complex.re hmul
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re,
        Complex.normSq_eq_norm_sq] at hr
      nlinarith [norm_nonneg k]
    let z : Circle := ⟨k, mem_sphere_zero_iff_norm.mpr hnorm⟩
    have hinv : star k = k⁻¹ := by
      apply mul_left_cancel₀ z.coe_ne_zero
      rw [hmul, mul_inv_cancel₀ z.coe_ne_zero]
    exact ⟨z, hk.symm, hcf.trans (congrArg (· • f (σ i)) hinv), hcor⟩
  choose m hm using hdiag
  refine ⟨m, ?_, hm⟩
  intro i
  have h := hc (e i)
  rw [(hm i).1, map_smul, (hm (σ i)).1, hσ i, smul_smul] at h
  have hk : (m i : ℂ) * (m (σ i) : ℂ) = 1 :=
    smul_left_injective ℂ (hn i).2.2.1 (h.trans (one_smul ℂ _).symm)
  apply Circle.ext
  change (m (σ i) : ℂ) = (m i : ℂ)⁻¹
  apply mul_left_cancel₀ (Circle.coe_ne_zero (m i))
  rw [hk, mul_inv_cancel₀ (Circle.coe_ne_zero (m i))]

omit [FiniteDimensional ℂ L] in
private theorem fixes_rootSpace (t : L ≃ₗ⁅ℂ⁆ L) (ht : ∀ x : K, t (x : L) = x)
    {α : Dual ℂ K} {x : L} (hx : x ∈ rootSpace_value K α) :
    t x ∈ rootSpace_value K α := by
  apply (mem_rootSpace K _ _).mpr
  intro y
  rw [← ht y, ← t.map_lie, (mem_rootSpace K _ _).mp hx y, map_smul]

/-- The finite test for any regular direction whose simple roots are permuted
by the target involution. -/
theorem finiteEquivalenceTestOfRegular
    (hss : IsSemisimple ℂ L) (ω : Conjugation L) (hw : IsCompact ω)
    (a b : L ≃ₗ⁅ℂ⁆ L) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hwa : Intertwines ω ω a) (hwb : Intertwines ω ω b)
    (H K : LieSubalgebra ℂ L) (hH : StableCartan ω a H) (hK : StableCartan ω b K)
    (φ : Direction K) (hφ : Regular K φ)
    (e f : simple K φ → L) (hnorm : Normalized K φ e f)
    (hcompact : ∀ i, ω.map (e i) = -f i) (σ : Equiv.Perm (simple K φ))
    (hσ : Function.Involutive σ) (hperm : ∀ i, rootAction b K hK.stable i.val = (σ i).val) :
    Finite (RootIsom H K) ∧
    (∃ lift : RootIsom H K → L ≃ₗ⁅ℂ⁆ L, ∀ r, CompactRootLift ω r (lift r)) ∧
    ∀ lift : RootIsom H K → L ≃ₗ⁅ℂ⁆ L,
      (∀ r, CompactRootLift ω r (lift r)) →
      (Nonempty ((involutionConjugation ω a hwa ha).fixed ≃ₗ⁅ℝ⁆
          (involutionConjugation ω b hwb hb).fixed) ↔
        ∃ r, PassesRootTest a b (lift r) σ e) := by
  classical
  obtain ⟨hfinite, hlifts⟩ := compactRootLifts hss ω hw H K hH.toral hK.toral
    hH.compact_stable hK.compact_stable φ hφ
  choose chooseLift hchooseLift using hlifts
  refine ⟨hfinite, ⟨chooseLift, hchooseLift⟩, ?_⟩
  intro lift hlift
  have hbline (i) : b (e i) ∈ rootSpace_value K (σ i).val := by
    rw [← hperm, ← transportRoots_involution b hb hK.stable]
    exact (mem_rootSpace_transport b _ _ _).mpr (hnorm i).1
  obtain ⟨n, hn, hnb⟩ := involutionMultipliers hss hK.toral ω b hb hwb hK.stable
     e f hnorm hcompact σ hσ hbline
  rw [realFormsIffCartanConjugates hss ω hw a b ha hb hwa hwb H K hH hK]
  constructor
  · rintro ⟨v, hvw, hv, hvmap⟩
    let r := rootIsomOfTransport hss hH.toral hK.toral v hvmap
    let g := lift r
    obtain ⟨hgw, hgmap, hg⟩ := hlift r
    let t := v.symm.trans g
    let c := (g.symm.trans a).trans g
    have ht (y : K) : t (y : L) = y := by
      obtain ⟨x, rfl⟩ := (v.ofSubalgebras H K hvmap).surjective y
      change g (v.symm (v (x : L))) = v (x : L)
      rw [LieEquiv.symm_apply_apply]
      exact eqOnCartan_of_same_transport g v hgmap hvmap hg x
    have hts (y : K) : t.symm (y : L) = y :=
      t.injective ((t.apply_symm_apply _).trans (ht y).symm)
    have hct (x : L) : c (t x) = t (b x) := by
      change g (a (g.symm (g (v.symm x)))) = g (v.symm (b x))
      rw [g.symm_apply_apply]
      congr 1
      apply v.injective
      change v (a (v.symm x)) = v (v.symm (b x))
      rw [v.apply_symm_apply]
      exact (hv _).symm.trans (congrArg b (v.apply_symm_apply x))
    have heq (i) : c (e i) = t (b (t.symm (e i))) := by
      simpa only [LieEquiv.apply_symm_apply] using hct (t.symm (e i))
    refine ⟨r, ?_, ?_⟩
    · intro i
      change c (e i) ∈ _
      rw [heq]
      apply fixes_rootSpace t ht
      rw [← hperm, ← transportRoots_involution b hb hK.stable]
      exact (mem_rootSpace_transport b _ _ _).mpr
        (fixes_rootSpace t.symm hts (hnorm i).1)
    · intro i hi
      change c (e i) = _
      rw [heq]
      have hs : rootSpace_value K i.val = ℂ ∙ e i :=
        eq_span_singleton_of_mem_of_finrank_eq_one
          (finrank_rootSpace_eq_one hss K hK.toral i.val i.property.1.1) (hnorm i).1 (hnorm i).2.2.1
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
        (hs ▸ fixes_rootSpace t.symm hts (hnorm i).1)
      have he : b (t.symm (e i)) = (n i : ℂ) • t.symm (e i) := by
        rw [← hk, map_smul, (hnb i).1, hi, smul_comm]
      rw [he, map_smul, LieEquiv.apply_symm_apply, (hnb i).1, hi]
  · rintro ⟨r, hline, hsign⟩
    let g := lift r
    obtain ⟨hgw, hgmap, hg⟩ := hlift r
    let c := (g.symm.trans a).trans g
    have hc : Function.Involutive c := by
      intro x
      change g (a (g.symm (g (a (g.symm x))))) = x
      rw [g.symm_apply_apply, ha, g.apply_symm_apply]
    have hcw : Intertwines ω ω c := by
      intro x
      change ω.map (g (a (g.symm x))) = g (a (g.symm (ω.map x)))
      rw [hgw, hwa, compact_symm ω g hgw]
    have hcs (x : L) (hx : x ∈ K) : c x ∈ K := by
      obtain ⟨y, hy, rfl⟩ := show x ∈ H.map g.toLieHom from hgmap.symm ▸ hx
      change g (a (g.symm (g y))) ∈ K
      rw [g.symm_apply_apply, ← hgmap]
      exact ⟨a y, hH.stable y hy, rfl⟩
    obtain ⟨m, hm, hmc⟩ :=
      involutionMultipliers hss hK.toral ω c hc hcw hcs e f hnorm hcompact σ hσ hline
    have hfix (i) (hi : σ i = i) : m i = n i := by
      apply Circle.ext
      apply smul_left_injective ℂ (hnorm i).2.2.1
      have hh : c (e i) = b (e i) := hsign i hi
      rwa [(hmc i).1, (hnb i).1, hi] at hh
    obtain ⟨t, htw, htk, hct⟩ := (torusConjugacy hss ω K hK.toral hK.compact_stable
      φ hφ e f hnorm hcompact c b σ hσ m n hm hn hmc hnb).mp hfix
    refine ⟨g.trans t.symm, ?_, ?_, ?_⟩
    · intro x
      change ω.map (t.symm (g x)) = t.symm (g (ω.map x))
      rw [compact_symm ω t htw, hgw]
    · intro x
      change b (t.symm (g x)) = t.symm (g (a x))
      apply t.injective
      change t (b (t.symm (g x))) = t (t.symm (g (a x)))
      rw [t.apply_symm_apply, ← hct, t.apply_symm_apply]
      change g (a (g.symm (g x))) = _
      rw [g.symm_apply_apply]
    · have htks (y : K) : t.symm (y : L) = y :=
        t.injective ((t.apply_symm_apply _).trans (htk y).symm)
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hgy : g y ∈ K := hgmap ▸ (show g y ∈ H.map g.toLieHom from ⟨y, hy, rfl⟩)
        change t.symm (g y) ∈ K
        rw [htks ⟨g y, hgy⟩]
        exact hgy
      · intro hx
        obtain ⟨y, hy, he⟩ := show x ∈ H.map g.toLieHom from hgmap.symm ▸ hx
        refine ⟨y, hy, ?_⟩
        change t.symm (g y) = x
        change g y = x at he
        rw [he]
        exact htks ⟨x, hx⟩

theorem finiteEquivalenceTest : finiteEquivalenceTestType.{u} := by
  intro L _ _ _ hss ω hw a b ha hb hwa hwb H K hH hK z hz e f hnorm hcompact σ hσ hperm
  exact finiteEquivalenceTestOfRegular hss ω hw a b ha hb hwa hwb H K hH hK
    (evaluation K z) hz.regular e f hnorm hcompact σ hσ hperm

end FiniteTest

section OuterReflection

open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.RootStrings (reflection_value)
open Specs.LieAlgebrasAndRepresentations.StableCartanVoganData
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open private simple_ne_neg simple_sub_not_root ad_pow_mem
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem coroot_diagonal (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) :
    α (coroot_value H α) = 2 := by
  rw [killingCoroot_pairing hss H hH]
  exact mul_div_cancel_right₀ 2 (rootForm_self_ne_zero hss H hH α hα)

private theorem reflection_involutive (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) :
    Function.Involutive (reflection_value H α) := by
  intro β
  ext z
  change (β z - β (coroot_value H α) * α z) -
    (β (coroot_value H α) - β (coroot_value H α) * α (coroot_value H α)) * α z = β z
  rw [coroot_diagonal hss H hH hα]
  ring

theorem rootReflection_isRootIsom (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) :
    ∃ r : RootIsom H H, ∀ β, r.linear β = reflection_value H α β := by
  let s : Module.Dual ℂ H →ₗ[ℂ] Module.Dual ℂ H :=
    { toFun := reflection_value H α
      map_add' := fun β γ => by
        simp only [reflection_value, LinearMap.add_apply, add_smul]
        abel
      map_smul' := fun c β => by
        simp only [reflection_value, LinearMap.smul_apply, smul_eq_mul, smul_sub,
          smul_smul, RingHom.id_apply] }
  have hs : Function.Involutive s := reflection_involutive hss H hH hα
  refine ⟨⟨LinearEquiv.ofInvolutive s hs, ?_, ?_⟩, fun _ => rfl⟩
  · intro β
    change s β ∈ rootSet H ↔ β ∈ rootSet H
    constructor
    · intro hb
      have h := RootStrings.reflection_mem_rootSet hss H hH α (s β) hα hb
      change s (s β) ∈ rootSet H at h
      rwa [hs β] at h
    · exact RootStrings.reflection_mem_rootSet hss H hH α β hα
  · have hnz := rootForm_self_ne_zero hss H hH α hα
    have hsymm (γ : Module.Dual ℂ H) : rootForm H α γ = rootForm H γ α := by
      simp only [rootForm_apply]
      exact LieModule.traceForm_comm ℂ L L _ _
    have hform (β γ : Module.Dual ℂ H) : rootForm H (s β) (s γ) = rootForm H β γ := by
      change rootForm H (β - β (coroot_value H α) • α) (γ - γ (coroot_value H α) • α) = _
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hsymm γ, show coroot_value H α = killingCoroot H α from rfl]
      rw [killingCoroot_pairing hss H hH α β, killingCoroot_pairing hss H hH α γ]
      field_simp
      ring
    intro β hb γ hc
    change (s γ) (killingCoroot H (s β)) = γ (killingCoroot H β)
    rw [killingCoroot_pairing hss H hH, killingCoroot_pairing hss H hH, hform, hform]


omit [FiniteDimensional ℂ L] in
private theorem map_root_vector (H : LieSubalgebra ℂ L) (n : L ≃ₗ⁅ℂ⁆ L)
    (hn : H.map n.toLieHom = H) {α β : Module.Dual ℂ H}
    (hr : transportRoots n hn α = β) {x : L} (hx : x ∈ rootSpace H α) :
    n x ∈ rootSpace H β := by
  let k := (n.ofSubalgebras H H hn).toLinearEquiv
  apply (mem_rootSpace H _ _).mpr
  intro h
  obtain ⟨y, rfl⟩ := k.surjective h
  have he : α y = β (k y) := by
    have hh := LinearMap.congr_fun hr (k y)
    change α (k.symm (k y)) = β (k y) at hh
    rwa [LinearEquiv.symm_apply_apply] at hh
  change ⁅n (y : L), n x⁆ = β (k y) • n x
  rw [← n.map_lie, (mem_rootSpace H _ _).mp hx, map_smul, he]

private theorem reflection_lift_on_cartan (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (hα : α ∈ rootSet H)
    (n : L ≃ₗ⁅ℂ⁆ L) (hn : H.map n.toLieHom = H)
    (hr : ∀ β, transportRoots n hn β = reflection_value H α β) (h : H) :
    n (h : L) = (h : L) - α h • (coroot_value H α : L) := by
  let k := (n.ofSubalgebras H H hn).toLinearEquiv
  have he : k h = h - α h • coroot_value H α := by
    apply (Module.evalEquiv ℂ H).injective
    ext β
    have hh := LinearMap.congr_fun (hr (reflection_value H α β)) (k h)
    rw [reflection_involutive hss H hH hα β] at hh
    change (reflection_value H α β) (k.symm (k h)) = β (k h) at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    change β (k h) = β (h - α h • coroot_value H α)
    simpa only [reflection_value, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, mul_comm] using hh.symm
  exact congrArg Subtype.val he

private theorem simple_reflection_fixed_eigenvector
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (φ : Direction H) (hφ : Regular H φ)
    (a : L ≃ₗ⁅ℂ⁆ L) (e f : simple H φ → L) (he : Normalized H φ e f)
    (i j : simple H φ) (A : ℤ) (hA : (A : ℂ) = j.val (coroot_value H i.val))
    (si sj : ℂ) (hai : a (e i) = si • e i) (haj : a (e j) = sj • e j)
    (hfi : a (f i) = si • f i)
    (hs : si = 1 ∨ si = -1) :
    ∃ x ∈ rootSpace H (reflection_value H i.val j.val), x ≠ 0 ∧
      a x = (sj * si ^ (-A)) • x := by
  classical
  by_cases hij : i = j
  · subst j
    have hsij : si = sj := smul_left_injective ℂ (he i).2.2.1 (hai.symm.trans haj)
    have hh := coroot_diagonal hss H hH i.property.1.1
    have hA' : A = 2 := by
      apply Int.cast_injective (α := ℂ)
      simpa using hA.trans hh
    have hrefl : reflection_value H i.val i.val = -i.val := by
      ext h
      simp only [reflection_value, hh, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.neg_apply, smul_eq_mul]
      ring
    refine ⟨f i, hrefl.symm ▸ (he i).2.1, (he i).2.2.2.1, ?_⟩
    rw [hfi, hA', ← hsij]
    rcases hs with hs | hs <;> norm_num [hs]
  · obtain ⟨p, q, hpq, hstring⟩ := RootStrings.root_string hss H hH i.val j.val
      i.property.1.1 j.property.1.1
      (fun h => hij (Subtype.ext h.symm)) (simple_ne_neg H φ i j)
    have hp : p = 0 := by
      by_contra h
      have hm := (hstring (-1)).mpr (by omega)
      have hs := simple_sub_not_root H φ hss hH hφ j i
      exact hs (by simpa [sub_eq_add_neg] using hm)
    subst p
    have hA' : A = -(q : ℤ) := by
      apply Int.cast_injective (α := ℂ)
      simpa using hA.trans hpq
    have hr (k : ℕ) (hk : k ≤ q) : j.val + k • i.val ∈ rootSet H := by
      have hm := (hstring (k : ℤ)).mpr (by constructor <;> omega)
      simpa only [natCast_zsmul] using hm
    let x (k : ℕ) := ((LieAlgebra.ad ℂ L (e i)) ^ k) (e j)
    have hx (k : ℕ) (hk : k ≤ q) :
        x k ∈ rootSpace H (j.val + k • i.val) ∧ x k ≠ 0 ∧
          a (x k) = (sj * si ^ k) • x k := by
      induction k with
      | zero =>
        refine ⟨?_, ?_, ?_⟩
        · simpa only [x, pow_zero, Module.End.one_apply, zero_nsmul, add_zero] using (he j).1
        · simpa only [x, pow_zero, Module.End.one_apply] using (he j).2.2.1
        · simpa only [x, pow_zero, Module.End.one_apply, mul_one] using haj
      | succ k ih =>
        obtain ⟨hm, hn, ha⟩ := ih (by omega)
        have hroot : i.val + (j.val + k • i.val) = j.val + (k + 1) • i.val := by
          rw [add_nsmul, one_nsmul]
          abel
        have heq : x (k + 1) = ⁅e i, x k⁆ := by
          change ((LieAlgebra.ad ℂ L (e i)) ^ (k + 1)) (e j) = _
          rw [pow_succ', Module.End.mul_apply]
          rfl
        refine ⟨ad_pow_mem H (he i).1 (he j).1 (k + 1), ?_, ?_⟩
        · rw [heq]
          exact RootStrings.root_bracket_ne_zero hss H hH _ _ i.property.1.1
            (hr k (by omega)) (hroot.symm ▸ hr (k + 1) hk) _ _ (he i).1 hm (he i).2.2.1 hn
        · rw [heq, a.map_lie, hai, ha, smul_lie, lie_smul, smul_smul, pow_succ]
          congr 1
          ring
    obtain ⟨hm, hne, hax⟩ := hx q le_rfl
    have hrefl : reflection_value H i.val j.val = j.val + q • i.val := by
      rw [reflection_value, ← hA, hA', Int.cast_neg, Int.cast_natCast, neg_smul,
        sub_neg_eq_add, Nat.cast_smul_eq_nsmul]
    exact ⟨x q, hrefl.symm ▸ hm, hne, by simpa [hA'] using hax⟩

private theorem orbit_representatives {I : Type*} (σ : I ≃ I)
    (hσ : Function.Involutive σ) :
    ∃ s : Set I, (∀ j, σ j = j → j ∉ s) ∧
      (∀ j, σ j ≠ j → (σ j ∈ s ↔ j ∉ s)) := by
  classical
  let orbit (j : I) : {s : Set I // s.Nonempty} :=
    ⟨{k | k = j ∨ k = σ j}, ⟨j, Or.inl rfl⟩⟩
  let s : Set I := {j | σ j ≠ j ∧ j = (orbit j).property.some}
  refine ⟨s, fun j h hj => hj.1 h, ?_⟩
  intro j hj
  have he : orbit (σ j) = orbit j := by
    apply Subtype.ext
    ext k
    change k = σ j ∨ k = σ (σ j) ↔ k = j ∨ k = σ j
    rw [hσ j, or_comm]
  have hm : (orbit j).property.some = j ∨ (orbit j).property.some = σ j :=
    (orbit j).property.some_mem
  have hn : σ (σ j) ≠ σ j := by simpa only [hσ j] using Ne.symm hj
  change (σ (σ j) ≠ σ j ∧ σ j = (orbit (σ j)).property.some) ↔
    ¬ (σ j ≠ j ∧ j = (orbit j).property.some)
  rw [he]
  rcases hm with h | h
  · rw [h]
    simp [hn, hj]
  · rw [h]
    simp [hn, hj, Ne.symm hj]

private theorem outerColorSign_injective : Function.Injective colorSign := by
  intro j k h
  fin_cases j <;> fin_cases k <;> first | rfl | norm_num [colorSign] at h

theorem outerReflection_from_lifts (hlift : compactRootLiftsType.{u}) :
    outerReflectionType.{u} := by
  classical
  intro L _ _ _ hss ω hw a ha hwa H hH φ hφ e f he hwf A d hA hdperm haction i hi
  obtain ⟨r, hr⟩ := rootReflection_isRootIsom hss H hH.toral i.val i.property.1.1
  obtain ⟨n, hnω, hn, hnroot⟩ :=
    (hlift hss ω hw H H hH.toral hH.toral hH.compact_stable hH.compact_stable φ hφ).2 r
  have hroot (α : Module.Dual ℂ H) :
      transportRoots n hn α = reflection_value H i.val α :=
    (congrArg (fun p : Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H => p α) hnroot).trans (hr α)
  let b := n.symm.trans (a.trans n)
  have hb (x : L) : b (n x) = n (a x) := by
    change n (a (n.symm (n x))) = _
    rw [LieEquiv.symm_apply_apply]
  have hbinv : Function.Involutive b := by
    intro x
    obtain ⟨y, rfl⟩ := n.surjective x
    change b (b (n y)) = n y
    rw [hb, hb, ha]
  have hbω : Intertwines ω ω b := by
    intro x
    obtain ⟨y, rfl⟩ := n.surjective x
    change ω.map (b (n y)) = b (ω.map (n y))
    rw [hnω y, hb, hb, hnω (a y), hwa y]
  have hnH := reflection_lift_on_cartan hss H hH.toral i.property.1.1 n hn hroot
  have hacomm (h : H) : a (n (h : L)) = n (a (h : L)) := by
    have hv := LinearMap.congr_fun (hdperm i) h
    rw [hi] at hv
    change i.val h = i.val ⟨a (h : L), hH.stable _ h.property⟩ at hv
    rw [hnH h, map_sub, map_smul, (haction i).2.2, hi]
    rw [hnH ⟨a (h : L), hH.stable _ h.property⟩, hv]
  have hbH (h : H) : b (h : L) = a (h : L) := by
    obtain ⟨z, rfl⟩ := (n.ofSubalgebras H H hn).surjective h
    change b (n (z : L)) = a (n (z : L))
    rw [hb, hacomm]
  have hbC (j : simple H φ) :
      b (coroot_value H j.val : L) = (coroot_value H (d.perm j).val : L) :=
    (hbH (coroot_value H j.val)).trans (haction j).2.2
  have hfixed (j : simple H φ) (hj : d.perm j = j) :
      b (e j) = (d.sign j * d.sign i ^ (-A i j)) • e j ∧
      b (f j) = (d.sign j * d.sign i ^ (-A i j)) • f j := by
    have hei : a (e i) = d.sign i • e i := by simpa only [hi] using (haction i).1
    have hej : a (e j) = d.sign j • e j := by simpa only [hj] using (haction j).1
    have hfi : a (f i) = d.sign i • f i := by simpa only [hi] using (haction i).2.1
    obtain ⟨x, hx, hnx, hax⟩ :=
      simple_reflection_fixed_eigenvector hss H hH.toral φ hφ a e f he i j _
        (hA i j) (d.sign i) (d.sign j) hei hej hfi (d.sign_cases i)
    have hm := map_root_vector H n hn
      ((hroot _).trans (reflection_involutive hss H hH.toral i.property.1.1 j.val)) hx
    have hnn : n x ≠ 0 := (map_ne_zero_iff n n.injective).mpr hnx
    have hlin : rootSpace H j.val = ℂ ∙ n x :=
      eq_span_singleton_of_mem_of_finrank_eq_one
        (finrank_rootSpace_eq_one hss H hH.toral j.val j.property.1.1) hm hnn
    have hmem : e j ∈ rootSpace H j.val := (he j).1
    rw [hlin] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hes : b (e j) = (d.sign j * d.sign i ^ (-A i j)) • e j := by
      rw [← hc, map_smul, hb, hax, map_smul, smul_comm c]
    refine ⟨hes, ?_⟩
    have h := congrArg ω.map hes
    rw [hbω, hwf j, ω.antilinear, hwf j, map_neg, smul_neg, neg_inj] at h
    rcases d.sign_cases j with hsj | hsj <;>
      rcases d.sign_cases i with hsi | hsi <;>
      simpa [star_mul, star_zpow₀, hsj, hsi] using h
  have hbmem (γ : Module.Dual ℂ H) {x : L} (hx : x ∈ rootSpace H γ) :
      b x ∈ rootSpace H (rootAction a H hH.stable γ) := by
    apply (mem_rootSpace H _ _).mpr
    intro h
    let y : H := ⟨a (h : L), hH.stable _ h.property⟩
    have hh := congrArg b ((mem_rootSpace H _ _).mp hx y)
    have hby : b (y : L) = (h : L) := (hbH y).trans (ha (h : L))
    rw [b.map_lie, hby, map_smul] at hh
    exact hh
  have hbE (j : simple H φ) : b (e j) ∈ rootSpace H (d.perm j).val := by
    rw [hdperm]
    exact hbmem _ (he j).1
  have hbF (j : simple H φ) : b (f j) ∈ rootSpace H (-(d.perm j).val) := by
    have hneg : rootAction a H hH.stable (-j.val) = -(d.perm j).val := by
      rw [hdperm]
      ext h
      rfl
    exact hneg ▸ hbmem _ (he j).2.1
  obtain ⟨s, hsf, hsorb⟩ := orbit_representatives d.perm d.involutive
  let E (j : simple H φ) := if j ∈ s then b (e (d.perm j)) else e j
  let F (j : simple H φ) := if j ∈ s then b (f (d.perm j)) else f j
  have hEF : Normalized H φ E F := by
    intro j
    by_cases hjs : j ∈ s
    · have hm := hbE (d.perm j)
      have hn := hbF (d.perm j)
      rw [d.involutive j] at hm hn
      have hbr : ⁅b (e (d.perm j)), b (f (d.perm j))⁆ = (coroot_value H j.val : L) := by
        rw [← b.map_lie, (he (d.perm j)).2.2.2.2, hbC, d.involutive j]
      simpa only [E, F, ite_eq_left hjs] using And.intro hm
        ⟨hn, (map_ne_zero_iff b b.injective).mpr (he (d.perm j)).2.2.1,
          (map_ne_zero_iff b b.injective).mpr (he (d.perm j)).2.2.2.1, hbr⟩
    · simpa only [E, F, ite_eq_right hjs] using he j
  have hwEF (j : simple H φ) : ω.map (E j) = -F j := by
    by_cases hjs : j ∈ s
    · simp only [E, F, ite_eq_left hjs, hbω (e (d.perm j)), hwf, map_neg]
    · simpa only [E, F, ite_eq_right hjs] using hwf j
  let colors (j : simple H φ) : ZMod 2 := if d.sign j = 1 then 0 else 1
  have hcolors (j : simple H φ) : colorSign (colors j) = d.sign j := by
    rcases d.sign_cases j with hh | hh <;> norm_num [colors, colorSign, hh]
  have hblack (j : simple H φ) : colors j = 1 ↔ d.sign j = -1 := by
    rcases d.sign_cases j with hh | hh <;> norm_num [colors, hh]
  let d' : DiagramData A :=
    { perm := d.perm
      involutive := d.involutive
      preserves := d.preserves
      sign := fun j => if d.perm j = j then colorSign (reflectedColors A i colors j) else 1
      sign_cases := fun j => by
        simp only [colorSign]
        split_ifs with h h0
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
      paired := fun j hj => ite_eq_right hj }
  have hsign (j : simple H φ) (hj : d.perm j = j) :
      d'.sign j = d.sign j * d.sign i ^ (-A i j) ∧
        (d'.sign j ≠ d.sign j ↔ d.sign i = -1 ∧ Odd (A i j)) := by
    change (if d.perm j = j then colorSign (reflectedColors A i colors j) else 1) = _ ∧
      ((if d.perm j = j then colorSign (reflectedColors A i colors j) else 1) ≠ d.sign j ↔ _)
    rw [ite_eq_left hj, ← hcolors j, ← hcolors i, ← (colorParity A i j colors).1,
      outerColorSign_injective.ne_iff, (colorParity A i j colors).2]
    exact ⟨rfl, by rw [hcolors i, hblack]⟩
  refine ⟨n, hn, hnω, hroot, b, hb, hbH, hbω, hbinv, d', E, F, rfl, hEF, hwEF,
    hsign, ?_⟩
  intro j
  refine ⟨?_, ?_, hbC j⟩
  · change b (E j) = d'.sign j • E (d.perm j)
    by_cases hj : d.perm j = j
    · simpa only [E, ite_eq_right (hsf j hj), hj, (hsign j hj).1] using (hfixed j hj).1
    · have hsg : d'.sign j = 1 := d'.paired j hj
      by_cases hjs : j ∈ s
      · have hn : d.perm j ∉ s := fun hs => ((hsorb j hj).mp hs) hjs
        simp only [E, ite_eq_left hjs, ite_eq_right hn, hbinv _, hsg, one_smul]
      · have hm : d.perm j ∈ s := (hsorb j hj).mpr hjs
        simp only [E, ite_eq_right hjs, ite_eq_left hm, d.involutive j, hsg, one_smul]
  · change b (F j) = d'.sign j • F (d.perm j)
    by_cases hj : d.perm j = j
    · simpa only [F, ite_eq_right (hsf j hj), hj, (hsign j hj).1] using (hfixed j hj).2
    · have hsg : d'.sign j = 1 := d'.paired j hj
      by_cases hjs : j ∈ s
      · have hn : d.perm j ∉ s := fun hs => ((hsorb j hj).mp hs) hjs
        simp only [F, ite_eq_left hjs, ite_eq_right hn, hbinv _, hsg, one_smul]
      · have hm : d.perm j ∈ s := (hsorb j hj).mpr hjs
        simp only [F, ite_eq_right hjs, ite_eq_left hm, d.involutive j, hsg, one_smul]

theorem outerReflection : outerReflectionType.{u} :=
  outerReflection_from_lifts compactRootLifts

end OuterReflection

section InnerCharacters

open Module (Dual Basis)
open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations
open PolarRealStructures SerreRelations VermaModules RootDecomposition RealRootSpace
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)

open private basedRootSystem exponential_eigenvector
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
open private direction_vector simple_equiv vector_regular
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

theorem rootLatticeBasis : rootLatticeBasisType.{u} := by
  classical
  intro L _ _ _ hss H hH φ hφ
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  letI : Fact (Realization H) := ⟨d⟩
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨_, _, _, _, a, _, ha, _⟩ := basedRootSystem d hφ
  obtain ⟨v, hdir⟩ := direction_vector d φ
  have hv := vector_regular d φ hdir hφ
  obtain ⟨s, hs⟩ := simple_equiv d φ hdir
  have hspan : Submodule.span ℤ (Set.range a) = voganRootLattice H := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro α ⟨i, rfl⟩
      rw [(ha i).2.2]
      exact Submodule.subset_span i.property.1.1
    · refine Submodule.span_le.mpr ?_
      intro α hα
      let x := rootRestriction H α
      obtain ⟨c, hc, _⟩ := simpleRoots_coefficients (realRoots H) d.root_system v hv x
        ⟨α, hα, rfl⟩
      have hsub (j : simpleRoots (realRoots H) v) :
          d.j j.val ∈ Submodule.span ℤ (Set.range a) := by
        obtain ⟨i, rfl⟩ := s.surjective j
        rw [hs i, ← (ha i).2.2]
        exact Submodule.subset_span (Set.mem_range_self i)
      rw [← d.extension_root α hα, ← show Finsupp.linearCombination ℤ
        (fun b : simpleRoots (realRoots H) v => (b : E H)) c = rootRestriction H α from hc]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_zsmul]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hsub i))
  refine ⟨(a.restrictScalars ℤ).map (LinearEquiv.ofEq _ _ hspan), fun i => ?_⟩
  apply Subtype.ext
  change (a.restrictScalars ℤ i : Dual ℂ H) = i.val
  rw [Basis.restrictScalars_apply, (ha i).2.2]

theorem signCharacterCoordinates : signCharacterCoordinatesType.{u} := by
  intro L _ _ _ hss H hH φ hφ
  obtain ⟨q, hq⟩ := rootLatticeBasis hss H hH φ hφ
  let e : SignCharacter H ≃ (simple H φ → ZMod 2) :=
    { toFun := fun χ i => χ (latticeSimple i)
      invFun := fun b => (q.constr ℤ b).toAddMonoidHom
      left_inv := by
        intro χ
        apply AddMonoidHom.toIntLinearMap_injective
        apply q.ext
        intro i
        change q.constr ℤ (fun j => χ (latticeSimple j)) (q i) = χ (q i)
        rw [q.constr_basis, hq]
      right_inv := by
        intro b
        funext i
        change q.constr ℤ b (latticeSimple i) = b i
        rw [← hq, q.constr_basis] }
  exact ⟨e, fun _ _ => rfl⟩

private theorem binary_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem colorSign_ne_zero (b : ZMod 2) : colorSign b ≠ 0 := by
  rcases binary_cases b with rfl | rfl <;> norm_num [colorSign]

private theorem colorSign_injective : Function.Injective colorSign := by
  intro b c h
  rcases binary_cases b with rfl | rfl <;>
    rcases binary_cases c with rfl | rfl <;> norm_num [colorSign] at *

private theorem colorSign_mul (b c : ZMod 2) :
    colorSign (b + c) = colorSign b * colorSign c := by
  rcases binary_cases b with rfl | rfl <;>
    rcases binary_cases c with rfl | rfl
  · simp [colorSign]
  · simp [colorSign]
  · simp [colorSign]
  · rw [show (1 + 1 : ZMod 2) = 0 by decide]
    norm_num [colorSign]

private theorem colorSign_sq (b : ZMod 2) : colorSign b * colorSign b = 1 := by
  rcases binary_cases b with rfl | rfl <;> norm_num [colorSign]

private def signUnits : ZMod 2 →+ Additive ℂˣ where
  toFun b := Additive.ofMul (Units.mk0 (colorSign b) (colorSign_ne_zero b))
  map_zero' := by
    apply Units.ext
    simp [colorSign]
  map_add' b c := by
    apply Units.ext
    exact colorSign_mul b c

private def exponentUnits {H : LieSubalgebra ℂ L} (h : H) :
    voganRootLattice H →+ Additive ℂˣ where
  toFun α := Additive.ofMul (Units.mk0 (Complex.exp (α.val h)) (Complex.exp_ne_zero _))
  map_zero' := by
    apply Units.ext
    exact Complex.exp_zero
  map_add' x y := by
    apply Units.ext
    exact Complex.exp_add (x.val h) (y.val h)

private theorem exponent_matches_character
    {H : LieSubalgebra ℂ L} {φ : Direction H}
    (q : Basis (simple H φ) ℤ (voganRootLattice H))
    (hq : ∀ i, q i = latticeSimple i) (h : H) (χ : SignCharacter H)
    (hc : ∀ i : simple H φ, Complex.exp (i.val h) = colorSign (χ (latticeSimple i))) :
    ∀ α : voganRootLattice H, Complex.exp (α.val h) = colorSign (χ α) := by
  have he : (exponentUnits h).toIntLinearMap = (signUnits.comp χ).toIntLinearMap := by
    apply q.ext
    intro i
    rw [hq]
    apply Units.ext
    exact hc i
  intro α
  exact congrArg (fun z : Additive ℂˣ => (z.toMul : ℂ)) (LinearMap.congr_fun he α)

private theorem exponential_on_root (H : LieSubalgebra ℂ L) (h : H)
    (a : L ≃ₗ⁅ℂ⁆ L) (ha : a.toLinearMap = CartanConjugacy.exponentialOperator (h : L))
    (α : Dual ℂ H) (x : L) (hx : x ∈ rootSpace_value H α) :
    a x = Complex.exp (α h) • x :=
  (LinearMap.congr_fun ha x).trans
    (exponential_eigenvector (h : L) x (α h) ((mem_rootSpace H α x).mp hx h))

private theorem root_summands_ext (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) {a b : L ≃ₗ⁅ℂ⁆ L}
    (hh : ∀ h : H, a (h : L) = b (h : L))
    (hr : ∀ (α : rootSet_value H) (x : L), x ∈ rootSpace_value H α → a x = b x) :
    a = b := by
  letI : DecidableEq (Option (rootSet_value H)) := Classical.decEq _
  let S := a.toLinearMap.eqLocus b.toLinearMap
  have hs (i : Option (rootSet_value H)) : rootSummand_value H i ≤ S := by
    intro x hx
    change a x = b x
    cases i with
    | none => exact hh ⟨x, hx⟩
    | some α => exact hr α x hx
  have htop : (⊤ : Submodule ℂ L) ≤ S := by
    rw [← (root_decomposition hss H hH).submodule_iSup_eq_top]
    exact iSup_le hs
  exact LieEquiv.ext fun x => htop (show x ∈ (⊤ : Submodule ℂ L) from trivial)

theorem innerCharacters : innerCharactersType.{u} := by
  classical
  intro L _ _ _ hss ω H hH hω φ hφ e f hn hw
  obtain ⟨q, hq⟩ := rootLatticeBasis hss H hH φ hφ
  have real_of_exp (a : L ≃ₗ⁅ℂ⁆ L) (h : H)
      (ha : a.toLinearMap = CartanConjugacy.exponentialOperator (h : L))
      (χ : SignCharacter H)
      (hc : ∀ i : simple H φ, Complex.exp (i.val h) = colorSign (χ (latticeSimple i))) :
      RealizesCharacter H a χ := by
    intro α x hx
    rw [exponential_on_root H h a ha α x hx]
    exact congrArg (fun z : ℂ => z • x) (exponent_matches_character q hq h χ hc (latticeRoot α))
  have he_simple (a : L ≃ₗ⁅ℂ⁆ L) (χ : SignCharacter H) (ha : RealizesCharacter H a χ)
      (i : simple H φ) : a (e i) = colorSign (χ (latticeSimple i)) • e i :=
    ha ⟨i.val, i.property.1.1⟩ (e i) (hn i).1
  constructor
  · intro a haw hai hah
    obtain ⟨h, _, ha⟩ := (torusKernel hss ω H hH hω φ hφ e f hn hw a).mp ⟨haw, hah⟩
    have hdiag (i : simple H φ) :
        ∃ b : ZMod 2, Complex.exp (i.val h) = colorSign b := by
      have hi := exponential_on_root H h a ha i.val (e i) (hn i).1
      have hsq := hai (e i)
      conv_lhs at hsq => rw [hi, map_smul, hi, smul_smul]
      have hc : Complex.exp (i.val h) * Complex.exp (i.val h) = 1 :=
        smul_left_injective ℂ (hn i).2.2.1 (hsq.trans (one_smul ℂ _).symm)
      rcases mul_self_eq_one_iff.mp hc with hp | hp
      · exact ⟨0, by simpa [colorSign] using hp⟩
      · exact ⟨1, by simpa [colorSign] using hp⟩
    choose b hb using hdiag
    let χ := (q.constr ℤ b).toAddMonoidHom
    have hχ (i : simple H φ) : χ (latticeSimple i) = b i := by
      rw [← hq]
      exact q.constr_basis ℤ b i
    have hc (i : simple H φ) : Complex.exp (i.val h) = colorSign (χ (latticeSimple i)) := by
      rw [hχ, hb]
    have hr := real_of_exp a h ha χ hc
    refine ⟨χ, hr, fun χ' hr' => ?_⟩
    apply AddMonoidHom.toIntLinearMap_injective
    apply q.ext
    intro i
    rw [hq]
    exact colorSign_injective (smul_left_injective ℂ (hn i).2.2.1
      ((he_simple a χ' hr' i).symm.trans (he_simple a χ hr i)))
  · intro χ
    let b (i : simple H φ) := χ (latticeSimple i)
    let z (i : simple H φ) : Circle :=
      ⟨colorSign (b i), mem_sphere_zero_iff_norm.mpr (by
        rcases binary_cases (b i) with hb | hb <;> simp [hb, colorSign])⟩
    obtain ⟨h, _, t, htw, htexp, hth, ht⟩ :=
      torusCoordinates hss ω H hH hω φ hφ e f hn hw z
    have hc (i : simple H φ) : Complex.exp (i.val h) = colorSign (χ (latticeSimple i)) :=
      smul_left_injective ℂ (hn i).2.2.1
        ((exponential_on_root H h t htexp i.val (e i) (hn i).1).symm.trans (ht i).1)
    have hr := real_of_exp t h htexp χ hc
    have hti : Function.Involutive t := by
      have heq : t.trans t = LieEquiv.refl := by
        apply root_summands_ext hss H hH
        · intro y
          change t (t (y : L)) = (y : L)
          rw [hth, hth]
        · intro α x hx
          change t (t x) = x
          have htα := hr α x hx
          conv_lhs => rw [htα, map_smul, htα, smul_smul, colorSign_sq, one_smul]
      intro x
      exact DFunLike.congr_fun heq x
    refine ⟨t, ⟨htw, hti, hth, hr⟩, ?_⟩
    rintro a ⟨_, _, hah, har⟩
    exact root_summands_ext hss H hH (fun x => (hah x).trans (hth x).symm)
      (fun α x hx => (har α x hx).trans (hr α x hx).symm)

theorem innerCharacterTransport : innerCharacterTransportType.{u} := by
  intro L _ _ _ ω H K r g a χ hg ha β x hx
  obtain ⟨_, hg, hr⟩ := hg
  let α : rootSet_value H :=
    ⟨r.linear.symm β.val, (r.roots _).mp (by simpa using β.property)⟩
  have hα : r.linear α.val = β.val := r.linear.apply_symm_apply β.val
  have hx' : g.symm x ∈ rootSpace_value H α := by
    apply (mem_rootSpace_transport g hg α.val (g.symm x)).mp
    rw [g.apply_symm_apply, hr, hα]
    exact hx
  change g (a (g.symm x)) = colorSign (χ (latticeRoot α)) • x
  rw [ha α (g.symm x) hx', map_smul, g.apply_symm_apply]

theorem innerReflection : innerReflectionType.{u} := by
  intro L _ _ _ hss H hH φ A i hA
  obtain ⟨r, hr⟩ := rootReflection_isRootIsom hss H hH i.val i.property.1.1
  refine ⟨r, hr, fun χ j => ?_⟩
  obtain ⟨e, f, he, hf, hne, hnf, hef, hbr, _⟩ :=
    exists_root_triple hss H hH i.val i.property.1.1
  have hd : i.val (RootForm.coroot_value H i.val) = 2 :=
    smul_left_injective ℂ hne (((mem_rootSpace H _ _).mp he _).symm.trans hbr)
  have hii : A i i = 2 :=
    Int.cast_injective (α := ℂ) (by simpa using (hA i).symm.trans hd)
  have hinv : r.linear.symm j.val = j.val - (A i j) • i.val := by
    apply r.linear.injective
    rw [LinearEquiv.apply_symm_apply, map_sub, map_zsmul, hr j.val, hr i.val]
    simp only [RootStrings.reflection_value, hA, hii, Int.cast_ofNat, Int.cast_smul_eq_zsmul]
    module
  have h : (latticeTransport r).symm (latticeSimple j) =
      latticeSimple j - A i j • latticeSimple i := Subtype.ext hinv
  change χ ((latticeTransport r).symm (latticeSimple j)) = _
  rw [h, map_sub, map_zsmul]
  simp [reflectedColors, zsmul_eq_mul]

end InnerCharacters

section InnerCharacterOrbits

open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations
open PolarRealStructures StableCartanVoganData RootDecomposition Set

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

private theorem same_character_of_same_root_actions {H : LieSubalgebra ℂ L}
    {a : L ≃ₗ⁅ℂ⁆ L} {χ ψ : SignCharacter H}
    (hχ : RealizesCharacter H a χ) (hψ : RealizesCharacter H a ψ) : χ = ψ := by
  have hr (α : rootSet_value H) : χ (latticeRoot α) = ψ (latticeRoot α) := by
    obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot α.property.2
    exact colorSign_injective (smul_left_injective ℂ hne ((hχ α x hx).symm.trans (hψ α x hx)))
  ext ⟨x, hx⟩
  induction hx using Submodule.span_induction with
  | mem x h => exact hr ⟨x, h⟩
  | zero => exact (map_zero χ).trans (map_zero ψ).symm
  | add x y hx hy h₁ h₂ =>
    change χ (⟨x, hx⟩ + ⟨y, hy⟩) = ψ (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, h₁, h₂]
  | smul n x hx h =>
    change χ (n • ⟨x, hx⟩) = ψ (n • ⟨x, hx⟩)
    rw [map_zsmul, map_zsmul, h]

variable [FiniteDimensional ℂ L]

theorem innerCharacterOrbit : innerCharacterOrbitType.{u} := by
  intro L _ _ _ hss ω hc a b ha hb hwa hwb H K hH hK hah hbk φ hφ χ ψ hχ hψ
  rw [realFormsIffCartanConjugates hss ω hc a b ha hb hwa hwb H K hH hK]
  constructor
  · rintro ⟨g, hgw, hgab, hg⟩
    let r := rootIsomOfTransport hss hH.toral hK.toral g hg
    refine ⟨r, ?_⟩
    have hc := innerCharacterTransport ω H K r g a χ ⟨hgw, hg, rfl⟩ hχ
    have he : (g.symm.trans a).trans g = b := by
      apply LieEquiv.ext
      intro x
      change g (a (g.symm x)) = b x
      rw [← hgab, g.apply_symm_apply]
    exact same_character_of_same_root_actions (he ▸ hc) hψ
  · rintro ⟨r, hr⟩
    obtain ⟨g, hgw, hg, hgr⟩ :=
      (compactRootLifts hss ω hc H K hH.toral hK.toral hH.compact_stable hK.compact_stable φ hφ).2 r
    have hc := innerCharacterTransport ω H K r g a χ ⟨hgw, hg, hgr⟩ hχ
    let c := (g.symm.trans a).trans g
    have hck (x : K) : c (x : L) = (x : L) := by
      obtain ⟨y, rfl⟩ := (g.ofSubalgebras H K hg).surjective x
      change g (a (g.symm (g (y : L)))) = g (y : L)
      rw [g.symm_apply_apply, hah]
    have hcp : RealizesCharacter K c ψ := hr ▸ hc
    have he : c = b := root_summands_ext hss K hK.toral (fun x => (hck x).trans (hbk x).symm)
      (fun α x hx => (hcp α x hx).trans (hψ α x hx).symm)
    refine ⟨g, hgw, fun x => ?_, hg⟩
    rw [← he]
    change g (a (g.symm (g x))) = g (a x)
    rw [g.symm_apply_apply]

end InnerCharacterOrbits

section WeylDecomposition

open Module (Dual)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Specs.LieAlgebrasAndRepresentations.RootStrings (reflection_value)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open private direction_vector vector_regular from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open scoped Pointwise

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L}

private theorem extend_rootReflection (d : Realization H) (α : rootSet H) (x : E H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    d.j (rootReflectionEquiv (rootRestriction H α.val) x) =
      reflection_value H α.val (d.j x) := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  have he := d.coroot_evaluation x α.val α.property
  rw [inner_coroot, rootCartan] at he
  rw [rootReflectionEquiv_apply, rootReflection, map_sub, map_smul, d.extension_root _ α.property]
  change _ = d.j x - d.j x (killingCoroot H α.val) • α.val
  rw [he]
  rfl

private theorem weyl_subgroup_normal (H : LieSubalgebra ℂ L)
    (hspan : Submodule.span ℂ (rootSet H) = ⊤) : (voganWeylGroup H).Normal := by
  refine ⟨fun g hg k => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hα, hr⟩ := hg
    apply Subgroup.subset_closure
    refine ⟨k.val α, (k.property.1 α).mpr hα, fun β => ?_⟩
    let f := (Module.Dual.eval ℂ H (killingCoroot H (k.val α))).comp k.val.toLinearMap
    let q := Module.Dual.eval ℂ H (killingCoroot H α)
    have h : f = q := LinearMap.ext_on hspan (fun x hx => k.property.2 α hα x hx)
    have hc : k.val (k.val.symm β) (killingCoroot H (k.val α)) =
        k.val.symm β (killingCoroot H α) := LinearMap.congr_fun h _
    change k.val (k.val.symm β) (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H (k.val α)) =
      k.val.symm β (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H α) at hc
    rw [k.val.apply_symm_apply] at hc
    change k.val (g.val (k.val.symm β)) = _
    rw [hr, reflection_value, reflection_value, map_sub, map_smul, k.val.apply_symm_apply, hc]
  | one => simp
  | mul a b ha hb iha ihb =>
    have h := (voganWeylGroup H).mul_mem iha ihb
    convert h using 1 <;> group
  | inv a ha iha =>
    have h := (voganWeylGroup H).inv_mem iha
    convert h using 1 <;> group

private theorem complexWeyl_of_real (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (d : Realization H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    ∀ w : rootWeylGroup (realRoots H),
      ∃ g ∈ voganWeylGroup H, ∀ x : E H, g.val (d.j x) = d.j (w.val x) := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  rintro ⟨w, hw⟩
  change ∃ g ∈ voganWeylGroup H, ∀ x : E H, g.val (d.j x) = d.j (w x)
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨_, ⟨α, hα, rfl⟩, rfl⟩ := hw
    obtain ⟨r, hr⟩ := rootReflection_isRootIsom hss H hH α hα
    refine ⟨⟨r.linear, r.roots, r.pairing⟩, Subgroup.subset_closure ⟨α, hα, hr⟩, ?_⟩
    exact fun x => (hr (d.j x)).trans (extend_rootReflection d ⟨α, hα⟩ x).symm
  | one => exact ⟨1, (voganWeylGroup H).one_mem, fun x => rfl⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨g, hg, hga⟩ := iha
    obtain ⟨k, hk, hkb⟩ := ihb
    refine ⟨g * k, (voganWeylGroup H).mul_mem hg hk, fun x => ?_⟩
    change g.val (k.val (d.j x)) = d.j (a (b x))
    rw [hkb, hga]
  | inv a ha iha =>
    obtain ⟨g, hg, hga⟩ := iha
    refine ⟨g⁻¹, (voganWeylGroup H).inv_mem hg, fun x => ?_⟩
    change g.val.symm (d.j x) = d.j (a.symm x)
    apply g.val.injective
    rw [g.val.apply_symm_apply, hga, a.apply_symm_apply]

private theorem realWeyl_of_complex (d : Realization H)
    {g : rootAutomorphisms H} (hg : g ∈ voganWeylGroup H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    ∃ w : rootWeylGroup (realRoots H), ∀ x : E H, g.val (d.j x) = d.j (w.val x) := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hα, hr⟩ := hg
    refine ⟨⟨rootReflectionEquiv (rootRestriction H α),
      Subgroup.subset_closure ⟨_, ⟨α, hα, rfl⟩, rfl⟩⟩, ?_⟩
    exact fun x => (hr (d.j x)).trans (extend_rootReflection d ⟨α, hα⟩ x).symm
  | one => exact ⟨1, fun _ => rfl⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨g, hg⟩ := iha
    obtain ⟨k, hk⟩ := ihb
    refine ⟨g * k, fun x => ?_⟩
    change a.val (b.val (d.j x)) = d.j (g.val (k.val x))
    rw [hk, hg]
  | inv a ha iha =>
    obtain ⟨g, hg⟩ := iha
    refine ⟨g⁻¹, fun x => ?_⟩
    change a.val.symm (d.j x) = d.j (g.val.symm x)
    apply a.val.injective
    rw [a.val.apply_symm_apply, hg, g.val.apply_symm_apply]

theorem weylDiagramDecomposition : weylDiagramDecompositionType.{u} := by
  classical
  intro L _ _ _ hss H hH φ hφ
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  letI : Fact (Realization H) := ⟨d⟩
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨v, hv⟩ := direction_vector d φ
  have hvr := vector_regular d φ hv hφ
  have hj (x : E H) (hx : x ∈ realRoots H) : d.j x ∈ rootSet H := by
    obtain ⟨α, hα, rfl⟩ := hx
    simpa only [d.extension_root α hα]
  refine ⟨weyl_subgroup_normal H d.roots_span, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · apply Subgroup.disjoint_def.mpr
    intro g hg hp
    obtain ⟨w, hw⟩ := realWeyl_of_complex d hg
    have hpos (x : E H) (hx : x ∈ positiveRoots (realRoots H) v) :
        0 < inner ℝ v (w.val x) := by
      have hx' : d.j x ∈ positive H φ := ⟨hj _ hx.1, by rw [hv]; exact hx.2⟩
      have hh := (hp (d.j x)).mpr hx'
      have hs := hh.2
      rwa [hw, hv] at hs
    have hinv : inversionRoots (realRoots H) v w.val = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      exact fun x hx => (not_lt_of_ge (hpos x hx.1).le) hx.2
    have hlen := weyl_length_eq_inversions (realRoots H) d.root_system v hvr w
    rw [hinv, Set.ncard_empty] at hlen
    obtain ⟨l, hl, hll, _⟩ := weyl_shortest_word (realRoots H) d.root_system v hvr w
    have hnil : l = [] := List.length_eq_zero_iff.mp (hll.trans hlen)
    have hw1 : w.val = 1 := by simpa [hnil, weylWordProduct] using hl.symm
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on d.roots_span
    intro α hα
    change g.val α = α
    simpa only [d.extension_root α hα, hw1, LinearEquiv.coe_one, id_eq] using hw (rootRestriction H α)
  · apply Set.eq_univ_of_forall
    intro g
    let ψ : Direction H := φ.comp (g.val.symm.toLinearMap.restrictScalars ℝ)
    have hψ : Regular H ψ := by
      intro α hα
      apply hφ
      apply (g.property.1 (g.val.symm α)).mp
      simpa
    obtain ⟨v', hv'⟩ := direction_vector d ψ
    have hvr' := vector_regular d ψ hv' hψ
    obtain ⟨w, hw⟩ := exists_weyl_into_closedSimpleChamber d.root_system v v'
    have hreg := rootWeylGroup_regular d.root_system.toRootAxioms w hvr'
    have hch : w.val v' ∈ simpleChamber (realRoots H) v :=
      fun a ha => lt_of_le_of_ne (hw a ha) (Ne.symm (hreg a ha.1.1))
    have hsign (x : E H) (hx : x ∈ realRoots H) :
        0 < inner ℝ (w.val v') x ↔ 0 < inner ℝ v x := by
      constructor
      · intro hp
        rcases positive_or_neg_positive d.root_system.toRootAxioms hvr hx with h | h
        · exact h.2
        · have hneg := simpleChamber_pairing_positive d.root_system.toRootAxioms hch h
          rw [inner_neg_right] at hneg
          linarith
      · intro hp
        exact simpleChamber_pairing_positive d.root_system.toRootAxioms hch ⟨hx, hp⟩
    obtain ⟨k, hk, hkw⟩ := complexWeyl_of_real hss hH d w
    refine ⟨k⁻¹, (voganWeylGroup H).inv_mem hk, k * g, ?_, by group⟩
    change ∀ α, k.val (g.val α) ∈ positive H φ ↔ α ∈ positive H φ
    intro α
    have hm : k.val (g.val α) ∈ rootSet H ↔ α ∈ rootSet H :=
      (k.property.1 _).trans (g.property.1 _)
    by_cases hα : α ∈ rootSet H
    · let x := rootRestriction H (g.val α)
      have hx : x ∈ realRoots H := ⟨_, (g.property.1 _).mpr hα, rfl⟩
      have hdx : d.j x = g.val α := d.extension_root _ ((g.property.1 _).mpr hα)
      have hwx := (rootWeylGroup_mem_iff d.root_system.toRootAxioms w.property _).mp hx
      have he : ψ (d.j x) = φ α := by
        rw [hdx]
        change φ (g.val.symm (g.val α)) = φ α
        rw [g.val.symm_apply_apply]
      change (_ ∈ rootSet H ∧ 0 < φ _) ↔ (_ ∈ rootSet H ∧ 0 < φ _)
      rw [hm, and_iff_right hα, and_iff_right hα, ← hdx, hkw, hv, ← hsign _ hwx,
        rootWeylGroup_inner w.property, ← hv', he]
    · exact iff_of_false (fun h => hα (hm.mp h.1)) (fun h => hα h.1)

end WeylDecomposition

section PositiveDiagram

open LieAlgebrasAndRepresentations.RealForms
open Specs.LieAlgebrasAndRepresentations
open MaximalTori (IsMaximalToral_value)
open SolvableRadical (IsSemisimple_value)
open RootDecomposition (rootSet_value rootSpace_value)
open RootForm (coroot_value)
open VermaModules (Direction Regular)
open SerreRelations (simple positive)
open IntegrableHighestWeightQuotient (Normalized)
open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition (diagramAutomorphisms)
open Module (Dual)

open private serrePresentation asLieEquiv from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem preserves_positive_of_simple {H : LieSubalgebra ℂ L} {φ : Direction H}
    (hH : IsMaximalToral_value H) (g : Dual ℂ H ≃ₗ[ℂ] Dual ℂ H)
    (hroot : ∀ α, g α ∈ rootSet_value H ↔ α ∈ rootSet_value H)
    (hsimple : ∀ i : simple H φ, g i.val ∈ positive H φ) :
    ∀ α, α ∈ positive H φ → g α ∈ positive H φ := by
  classical
  have hfin : (positive H φ).Finite := (rootSet_finite H hH.1).subset (fun _ h => h.1)
  have hwf : (positive H φ).WellFoundedOn (fun a b => φ a < φ b) :=
    Set.wellFoundedOn_image.mp ((hfin.image φ).wellFoundedOn (r := (· < ·)))
  intro α hα
  refine hwf.induction hα (P := fun a => g a ∈ positive H φ) ?_
  intro a ha ih
  by_cases hs : a ∈ simple H φ
  · exact hsimple ⟨a, hs⟩
  · change ¬ (a ∈ positive H φ ∧
      ∀ β ∈ positive H φ, ∀ γ ∈ positive H φ, a ≠ β + γ) at hs
    rw [and_iff_right ha] at hs
    push Not at hs
    obtain ⟨β, hb, γ, hc, heq⟩ := hs
    have hβ : g β ∈ positive H φ := ih β hb (show φ β < φ a by
      rw [heq, map_add]
      exact lt_add_of_pos_right _ hc.2)
    have hγ : g γ ∈ positive H φ := ih γ hc (show φ γ < φ a by
      rw [heq, map_add]
      exact lt_add_of_pos_left _ hb.2)
    refine ⟨(hroot _).2 ha.1, ?_⟩
    rw [heq, map_add, map_add]
    exact add_pos hβ.2 hγ.2

set_option maxHeartbeats 800000 in
theorem positiveRootStabilizerIsDynkin : positiveRootStabilizerIsDynkinType.{u} := by
  classical
  intro L _ _ _ hss H hH φ hφ
  have hpin (i : simple H φ) : ∃ (e f : L),
      e ∈ rootSpace_value H i.val ∧ f ∈ rootSpace_value H (-i.val) ∧
        e ≠ 0 ∧ f ≠ 0 ∧ ⁅e, f⁆ = (coroot_value H i.val : L) := by
    obtain ⟨e, f, he, hf, hne, hnf, hb, _, _⟩ :=
      exists_root_triple hss H hH i.val i.property.1.1
    exact ⟨e, f, he, hf, hne, hnf, hb⟩
  choose e f hn using hpin
  obtain ⟨c, a, _, hca, _, _, _, _, _, _⟩ := serrePresentation hss hH hφ e f hn
  obtain ⟨_, s, hs, _, _⟩ :=
    LieAlgebrasAndRepresentations.AutomorphismDecomposition.decomposition hss H hH φ hφ e f hn
  let simpleMap (g : positiveRootStabilizer H φ) : Equiv.Perm (simple H φ) :=
    positiveSimpleEquiv g.val.val (fun α => (g.property α).symm)
  let F : positiveRootStabilizer H φ →* diagramAutomorphisms H φ :=
    { toFun := fun g => ⟨simpleMap g, fun i j =>
        g.val.property.2 _ i.property.1.1 _ j.property.1.1⟩
      map_one' := by
        apply Subtype.ext
        apply Equiv.ext
        intro i
        exact Subtype.ext rfl
      map_mul' := by
        intro g h
        apply Subtype.ext
        apply Equiv.ext
        intro i
        exact Subtype.ext rfl }
  have hF (g : positiveRootStabilizer H φ) (i : simple H φ) :
      ((F g).val i).val = g.val.val i.val := rfl
  have hFinj : Function.Injective F := by
    intro g h heq
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply a.ext
    intro i
    change g.val.val (a i) = h.val.val (a i)
    rw [(hca i).2, ← hF, ← hF, heq]
  have hFsurj : Function.Surjective F := by
    intro p
    let g := asLieEquiv (s p)
    let w := c.equiv c p.val
    have hwg (x : H) : g (x : L) = (w x : L) := by
      have h : g.toLinearMap.comp H.toSubmodule.subtype =
          H.toSubmodule.subtype.comp w.toLinearMap := by
        apply c.ext
        intro i
        change (s p).val (c i : L) = (w (c i) : L)
        rw [Module.Basis.equiv_apply, (hca i).1, (hca (p.val i)).1]
        exact (hs p i).2.2
      exact LinearMap.congr_fun h x
    have hgmap : H.map g.toLieHom = H := by
      ext x
      constructor
      · rintro ⟨x, hx, rfl⟩
        change g x ∈ H
        rw [hwg ⟨x, hx⟩]
        exact (w ⟨x, hx⟩).property
      · intro hx
        obtain ⟨y, hy⟩ := w.surjective ⟨x, hx⟩
        exact ⟨y, y.property, (hwg y).trans (congrArg Subtype.val hy)⟩
    let r := rootIsomOfTransport hss hH hH g hgmap
    have hpres (i : simple H φ) : r.linear i.val = (p.val i).val := by
      apply c.ext
      intro j
      obtain ⟨k, rfl⟩ := p.val.surjective j
      have hk : g.ofSubalgebras H H hgmap (c k) = c (p.val k) := by
        apply Subtype.ext
        change g (c k : L) = (c (p.val k) : L)
        rw [hwg, Module.Basis.equiv_apply]
      change transportRoots g hgmap i.val (c (p.val k)) = _
      calc
        _ = i.val (c k) := by rw [← hk, transportRoots_apply]
        _ = _ := by
          rw [(hca k).1, (hca (p.val k)).1]
          exact (p.property k i).symm
    have hpos (α : Dual ℂ H) : r.linear α ∈ positive H φ ↔ α ∈ positive H φ := by
      constructor
      · intro hα
        have hr : ∀ β, r.linear.symm β ∈ rootSet_value H ↔ β ∈ rootSet_value H := by
          intro β
          simpa using (r.roots (r.linear.symm β)).symm
        have hs' (i : simple H φ) : r.linear.symm i.val = (p.val.symm i).val := by
          apply r.linear.injective
          rw [LinearEquiv.apply_symm_apply, hpres, Equiv.apply_symm_apply]
        simpa using preserves_positive_of_simple hH r.linear.symm hr
          (fun i => (hs' i).symm ▸ (p.val.symm i).property.1) (r.linear α) hα
      · exact preserves_positive_of_simple hH r.linear r.roots
          (fun i => (hpres i).symm ▸ (p.val i).property.1) α
    let q : positiveRootStabilizer H φ := ⟨⟨r.linear, r.roots, r.pairing⟩, hpos⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact hpres i
  exact ⟨MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩, hF⟩

end PositiveDiagram

section InnerSemidirectProduct

theorem innerSemidirectProduct : innerSemidirectProductType.{u} := by
  intro L _ _ _ hss H hH φ hφ
  obtain ⟨hN, hc⟩ := weylDiagramDecomposition hss H hH φ hφ
  obtain ⟨e, he⟩ := positiveRootStabilizerIsDynkin hss H hH φ hφ
  let s := (positiveRootStabilizer H φ).subtype.comp e.symm.toMonoidHom
  let m := SemidirectProduct.lift (φ := weylDiagramAction hN e) (voganWeylGroup H).subtype s
    (fun d => by
      ext w
      rfl)
  have hb : Function.Bijective (fun x : voganWeylGroup H × _ => x.1.val * s x.2) :=
    hc.comp (Equiv.prodCongr (Equiv.refl _) e.symm.toEquiv).bijective
  have hm : Function.Bijective m := (SemidirectProduct.equivProd.bijective_comp _).mpr hb
  refine ⟨hN, e, he, MulEquiv.ofBijective m hm, fun _ => rfl, ?_⟩
  intro x χ
  change (x.left.val * (e.symm x.right).val) • χ = _
  exact mul_smul _ _ _

end InnerSemidirectProduct

theorem innerWeylDiagramOrbit : innerWeylDiagramOrbitType.{u} := by
  intro L _ _ _ hss ω hc a b ha hb hwa hwb H hHa hHb hah hbh φ hφ
  obtain ⟨e, he⟩ := positiveRootStabilizerIsDynkin hss H hHa.toral φ hφ
  refine ⟨e, he, fun χ ψ hχ hψ => ?_⟩
  rw [innerCharacterOrbit hss ω hc a b ha hb hwa hwb H H hHa hHb hah hbh φ hφ χ ψ hχ hψ]
  constructor
  · rintro ⟨r, hr⟩
    let g : rootAutomorphisms H := ⟨r.linear, r.roots, r.pairing⟩
    obtain ⟨⟨w, d⟩, h⟩ := (weylDiagramDecomposition hss H hHa.toral φ hφ).2.2 g
    refine ⟨w, e d, ?_⟩
    change w.val * d.val = g at h
    rw [e.symm_apply_apply, ← mul_smul, h]
    exact hr
  · rintro ⟨w, p, hp⟩
    refine ⟨asRootIsom H (w.val * (e.symm p).val), ?_⟩
    change (w.val * (e.symm p).val) • χ = ψ
    rwa [mul_smul]

end LieAlgebrasAndRepresentations.VoganEquivalence
