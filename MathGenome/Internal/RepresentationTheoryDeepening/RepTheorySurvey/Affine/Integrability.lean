import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.Integrability
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.VermaModules
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.AdjointLocalNilpotence
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PrincipalTriple
import Mathlib.Algebra.Lie.Sl2
import Batteries.Tactic.OpenPrivate

/-! Integrability of simple affine highest-weight modules. -/

noncomputable section

set_option linter.style.haveILetI false

namespace RepTheorySurvey.Affine

open _root_.Specs.RepTheorySurvey.Affine.Integrability
open _root_.Specs.RepTheorySurvey.Affine.LoopAlgebra (affineBracket_value)
open _root_.Specs.RepTheorySurvey.Affine.VermaModules (centralCartanElement)
open _root_.Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)

open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)
open _root_.Specs.RepTheorySurvey.Affine.VermaWeightSpaces
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open UniversalEnvelopingAlgebra (ι)
open scoped BigOperators DirectSum

universe u v

abbrev affineSimpleCoroot := @affineSimpleCoroot_value
abbrev IsIntegrable := @IsIntegrable_value

theorem affineLevelFormula : affineLevelFormula_type.{u} := by
  intro G _ _ _ B H φ θ a ha Λ
  have hfinite (i : simpleRoots H φ) :
      affineSimpleCoroot B H θ (some i) = cartanIncl B H (coroot_value H i.val) :=
    Subtype.ext (coe_affineSimpleCoroot θ (some i))
  have hcentral :
      affineSimpleCoroot (φ := φ) B H θ none + cartanIncl B H (coroot_value H θ) =
        centralCartanElement B H := by
    apply Subtype.ext
    change ((affineSimpleCoroot B H θ (none : AffineSimpleIndex H φ) : AffineAlgebra B) +
      homogeneous B 0 (coroot_value H θ : G)) = K B
    rw [coe_affineSimpleCoroot]
    exact sub_add_cancel _ _
  calc
    _ = Λ (affineSimpleCoroot (φ := φ) B H θ none + cartanIncl B H (coroot_value H θ)) :=
      congrArg Λ hcentral.symm
    _ = _ := by
      rw [map_add]
      congr 1
      simp only [hfinite]
      rw [ha]
      change (Λ.comp (cartanIncl B H)) (a.sum (fun i n => n • coroot_value H i.val)) =
        a.sum (fun i n => (n : ℂ) * (Λ.comp (cartanIncl B H)) (coroot_value H i.val))
      simp only [Finsupp.sum, map_sum, map_nsmul, nsmul_eq_mul]

section RankOne

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [Module (U L) V]
  [IsScalarTower ℂ (U L) V]

/-- The rank-one identity for the enveloping action on a primitive vector. -/
private theorem raising_lowering_power {h e f : L} (t : IsSl2Triple h e f)
    {w : V} {c : ℂ} (hw : w ≠ 0) (hh : ι ℂ h • w = c • w)
    (he : ι ℂ e • w = 0) (n : ℕ) :
    ι ℂ e • ((ι ℂ f) ^ (n + 1) • w) =
      ((n + 1 : ℂ) * (c - n)) • ((ι ℂ f) ^ n • w) := by
  letI : LieRingModule (U L) V := LieRingModule.ofAssociativeModule
  letI : LieModule ℂ (U L) V := LieModule.ofAssociativeModule
  letI : LieRingModule L V := LieRingModule.compLieHom V (ι ℂ)
  letI : LieModule ℂ L V := LieModule.compLieHom V (ι ℂ)
  have hprim : t.HasPrimitiveVectorWith w c := ⟨hw, hh, he⟩
  have hend : LieModule.toEnd ℂ L V f = Algebra.lsmul ℂ ℂ V (ι ℂ f) := rfl
  have hpow := hprim.lie_e_pow_succ_toEnd_f n
  simp only [hend, ← map_pow (Algebra.lsmul ℂ ℂ V)] at hpow
  exact hpow

private theorem coroot_value_nat {h e f : L} (t : IsSl2Triple h e f)
    {w : V} {c : ℂ} (hw : w ≠ 0) (hh : ι ℂ h • w = c • w)
    (he : ι ℂ e • w = 0) (hn : ∃ n : ℕ, (ι ℂ f) ^ n • w = 0) :
    ∃ n : ℕ, c = (n : ℂ) := by
  obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun n => (ι ℂ f) ^ n • w = 0) (by simpa using hw) hn
  refine ⟨n, ?_⟩
  have hs := raising_lowering_power t hw hh he n
  rw [hn₂, smul_zero, eq_comm, smul_eq_zero_iff_left hn₁, mul_eq_zero, sub_eq_zero] at hs
  exact hs.resolve_left (Nat.cast_add_one_ne_zero n)

private theorem enveloping_commutator (x y : L) :
    (ι ℂ x : U L) * ι ℂ y - ι ℂ y * ι ℂ x = ι ℂ ⁅x, y⁆ :=
  ((ι ℂ).map_lie x y).symm

end RankOne

section FiniteCoroots

open LieAlgebrasAndRepresentations (IsSemisimple killingCoroot rootForm)
open private pairingRoot_range cartanBase simpleRootEquiv pairing_coroot_eq from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PrincipalTriple
open private highest_dominant rootForm_self_pos rootForm_re_of_coroot coroot_self from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.AffineSimpleTriples

theorem highestFiniteCorootCoordinates : highestFiniteCorootCoordinates_type.{u} := by
  classical
  intro G _ _ _ _ H _ φ hφ θ hθ
  have hss : IsSemisimple ℂ G := LieAlgebra.radical_eq_bot
  letI : LieAlgebra.HasTrivialRadical ℂ G := ⟨hss⟩
  have hH := LieAlgebrasAndRepresentations.RealRootSpace.cartan_isMaximalToral hss H
  let P := LieAlgebra.IsKilling.rootSystem H
  let b := cartanBase H hH φ hφ
  let e := simpleRootEquiv H hH φ hφ
  obtain ⟨k, hk⟩ : θ ∈ Set.range P.root := (pairingRoot_range H hH).symm ▸ hθ.1.1
  obtain ⟨n, _, hn⟩ := b.flip.exists_root_eq_sum_nat_or_neg k
  change P.coroot k = ∑ j ∈ b.support, n j • P.coroot j ∨
    P.coroot k = -(∑ j ∈ b.support, n j • P.coroot j) at hn
  have hk' : P.coroot k = coroot_value H θ := by
    rw [pairing_coroot_eq H hH hss, hk]
  have hsimple (j : b.support) : P.coroot j = coroot_value H (e j).val :=
    pairing_coroot_eq H hH hss j
  have hnonneg : 0 ≤ (θ (∑ j ∈ b.support, n j • P.coroot j)).re := by
    rw [map_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun j hj => ?_
    let a := e ⟨j, hj⟩
    rw [show P.coroot j = coroot_value H a.val from hsimple ⟨j, hj⟩]
    obtain ⟨z, hz, _⟩ :=
      LieAlgebrasAndRepresentations.RootStrings.coroot_pairing_integral hss H hH
        a.val θ a.2.1.1 hθ.1.1
    have hprod := rootForm_re_of_coroot H a.2.1.1 hz
    have hz' : 0 ≤ (z : ℝ) := nonneg_of_mul_nonneg_left
      (by rw [← hprod]; exact mul_nonneg (by norm_num) (highest_dominant H hθ a.2.1))
      (rootForm_self_pos H a.2.1.1)
    rw [map_nsmul, show θ (coroot_value H a.val) = (z : ℂ) from hz]
    simpa only [nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.intCast_re, zero_mul, sub_zero] using mul_nonneg (Nat.cast_nonneg (n j)) hz'
  have hsum : P.coroot k = ∑ j ∈ b.support, n j • P.coroot j := by
    rcases hn with hn | hn
    · exact hn
    · have he := congrArg (fun x : H => (θ x).re) hn
      change (θ (P.coroot k)).re = (θ (-(∑ j ∈ b.support, n j • P.coroot j))).re at he
      rw [hk', coroot_self H hθ.1.1, Complex.re_ofNat, map_neg, Complex.neg_re] at he
      linarith [hnonneg]
  letI : Fintype (simpleRoots H φ) := Fintype.ofEquiv b.support e
  let a : simpleRoots H φ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => n (e.symm j))
  have ha (j : simpleRoots H φ) : a j = n (e.symm j) := rfl
  refine ⟨a, ?_⟩
  rw [← hk', hsum, Finsupp.sum_fintype a
    (fun j (m : ℕ) => m • coroot_value H j.val) (fun _ => zero_nsmul _)]
  simp only [ha]
  rw [← Equiv.sum_comp e]
  simp only [Equiv.symm_apply_apply, ← hsimple]
  exact Finset.sum_subtype b.support (p := fun j => j ∈ b.support)
    (fun _ => Iff.rfl) (fun j => n j • P.coroot j)

end FiniteCoroots

section HighestWeight

open _root_.Specs.RepTheorySurvey.Affine.AdjointLocalNilpotence (CompatibleLieStructure)
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces (ClosedUnderBracket)
open _root_.Specs.LieAlgebrasAndRepresentations.HighestWeightData (positiveRootCone_value)
open private simpleWord simpleWordWeight simpleWord_mem_weight heightScore heightScore_pos
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.VermaWeightSpaces
open private le_affineVermaRadical from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.VermaModules

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]
  {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H}
  (D : Model B H φ)
  {θ : Module.Dual ℂ H} (T : FiniteRootTriple H θ)
  (S : ∀ i : simpleRoots H φ, FiniteRootTriple H i.val)

private theorem raising_mem_positive
    (hgen : affineLieSpan B (Set.range (affineSimpleE B T S)) = affinePositive B H φ)
    (i : AffineSimpleIndex H φ) : (show Carrier D from affineSimpleE B T S i) ∈ positive D := by
  change affineSimpleE B T S i ∈ affinePositive B H φ
  rw [← hgen]
  exact Submodule.mem_sInf.mpr (fun p hp => hp.1 (Set.mem_range_self i))

private theorem positive_kills_of_generators
    {V : Type v} [AddCommGroup V] [Module ℂ V] [Module (U (Carrier D)) V]
    [IsScalarTower ℂ (U (Carrier D)) V] (w : V)
    (hgen : affineLieSpan B (Set.range (affineSimpleE B T S)) = affinePositive B H φ)
    (hw : ∀ i, ι ℂ (show Carrier D from affineSimpleE B T S i) • w = 0) :
    ∀ x : positive D, ι ℂ (x : Carrier D) • w = 0 := by
  let annihilator : Submodule ℂ (AffineAlgebra B) := {
    carrier := {x | ι ℂ (show Carrier D from x) • w = 0}
    zero_mem' := by
      change ι ℂ (0 : Carrier D) • w = 0
      rw [map_zero, zero_smul]
    add_mem' := by
      intro x y hx hy
      let x' : Carrier D := x
      let y' : Carrier D := y
      change ι ℂ x' • w = 0 at hx
      change ι ℂ y' • w = 0 at hy
      change ι ℂ (x' + y') • w = 0
      rw [map_add, add_smul, hx, hy, add_zero]
    smul_mem' := by
      intro c x hx
      let x' : Carrier D := x
      change ι ℂ x' • w = 0 at hx
      change ι ℂ (c • x') • w = 0
      rw [map_smul, smul_assoc, hx, smul_zero] }
  have hclosed : ClosedUnderBracket B annihilator := by
    intro x y hx hy
    change (ι ℂ (show Carrier D from x)) • w = 0 at hx
    change (ι ℂ (show Carrier D from y)) • w = 0 at hy
    change ι ℂ (⁅(show Carrier D from x), (show Carrier D from y)⁆) • w = 0
    rw [← enveloping_commutator, sub_smul, mul_smul, mul_smul, hx, hy, smul_zero,
      smul_zero, sub_zero]
  intro x
  have hle : affinePositive B H φ ≤ annihilator := by
    rw [← hgen]
    refine sInf_le ⟨?_, hclosed⟩
    rintro _ ⟨i, rfl⟩
    exact hw i
  exact hle x.property

variable [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra]

/-- A highest vector of strictly smaller height generates a proper submodule. -/
private theorem lower_highest_mem_radical (hB : B.IsNormalized H) (hφ : Regular H φ)
    (hθ : IsHighestFiniteRoot H φ θ) (Λ μ : Weight B H)
    (χ : U (affineBorel D) →ₐ[ℂ] ℂ) (hχ : IsWeightCharacter D Λ χ)
    (w : affineVerma D χ) (hw : IsHighestVector D μ w)
    (hbelow : heightScore B H φ θ μ < heightScore B H φ θ Λ) :
    w ∈ affineVermaRadical D χ := by
  classical
  obtain ⟨χ', hχ', _⟩ := affineVermaCharacter B H φ D hB hφ μ
  obtain ⟨f, hf, _⟩ := (affineVermaUniversal.{u,u} B H φ D hB hφ μ χ' hχ').2
    (affineVerma D χ) w hw
  let g := f.restrictScalars ℂ
  let W := affineVermaWeightSpace D χ
  let W' := affineVermaWeightSpace D χ'
  let lower := ⨆ (ν : Weight B H) (_ : ν ≠ Λ), W ν
  obtain ⟨hW, _, htop, hspace⟩ := affineVermaWeights B H φ D hB hφ Λ χ hχ
  have hW' : DirectSum.IsInternal W' := (affineVermaWeights B H φ D hB hφ μ χ' hχ').1
  have hvanish : W' Λ = ⊥ := by
    by_contra hnonzero
    have hcone := affineVermaWeightSupport B H φ D hB hφ μ χ' hχ' θ hθ Λ hnonzero
    have hscore : 0 ≤ heightScore B H φ θ (μ - Λ) := by
      refine Submodule.span_induction (p := fun x _ => 0 ≤ heightScore B H φ θ x)
        ?_ (by simp) ?_ ?_ hcone
      · rintro _ ⟨i, rfl⟩
        exact (heightScore_pos (B := B) θ i).le
      · intro x y _ _ hx hy
        rw [map_add]
        exact add_nonneg hx hy
      · intro n x _ hx
        rw [map_nsmul]
        exact nsmul_nonneg hx _
    rw [map_sub] at hscore
    exact (not_le_of_gt hbelow) (sub_nonneg.mp hscore)
  have hmap (ν : Weight B H) : (W' ν).map g ≤ W ν := by
    rintro _ ⟨z, hz, rfl⟩
    apply (mem_affineVermaWeightSpace D χ ν _).mpr
    intro h
    have hz' := (mem_affineVermaWeightSpace D χ' ν z).mp hz h
    change ι ℂ (show Carrier D from h.1) • z = ν h • z at hz'
    change ι ℂ (show Carrier D from h.1) • f z = ν h • f z
    rw [← f.map_smul, hz']
    exact g.map_smul (ν h) z
  have hrange : LinearMap.range g ≤ lower := by
    rw [← Submodule.map_top, ← hW'.submodule_iSup_eq_top, Submodule.map_iSup]
    refine iSup_le fun ν => ?_
    by_cases hν : ν = Λ
    · subst ν
      change (W' Λ).map g ≤ lower
      rw [hvanish, Submodule.map_bot]
      exact bot_le
    · exact (hmap ν).trans (le_iSup_of_le ν (le_iSup (fun _ : ν ≠ Λ => W ν) hν))
  have hproper : LinearMap.range f ≠ ⊤ := by
    intro he
    have hmem : affineVermaTop D χ ∈ LinearMap.range g := by
      obtain ⟨z, hz⟩ := LinearMap.range_eq_top.mp he (affineVermaTop D χ)
      exact ⟨z, hz⟩
    have ht : affineVermaTop D χ ∈ W Λ := by
      change affineVermaTop_value D χ ∈ affineVermaWeightSpace_value D χ Λ
      rw [hspace]
      exact Submodule.mem_span_singleton_self _
    have hd : Disjoint (W Λ) lower := iSupIndep_def.mp hW.submodule_iSupIndep Λ
    exact htop (Submodule.disjoint_def.mp hd _ ht (hrange hmem))
  exact le_affineVermaRadical D χ hproper ⟨_, hf⟩

theorem affineSimpleIntegrable : affineSimpleIntegrable_type.{u} := by
  intro G _ _ _ _ B H _ φ D hB hφ θ hθ T S Λ χ hχ
  let I := AffineSimpleIndex H φ
  let e : I → Carrier D := affineSimpleE B T S
  let f : I → Carrier D := affineSimpleF B T S
  let h : I → cartan D := fun i =>
    ⟨(affineSimpleCoroot B H θ i).1, (affineSimpleCoroot B H θ i).2⟩
  let α : I → Weight B H := affineSimpleRoot B H θ
  let c : I → ℂ := fun i => Λ (affineSimpleCoroot B H θ i)
  let v := affineSimpleTop D χ
  obtain ⟨_, hv, hvtop, hcyclic⟩ := affineSimpleHighestWeight B H φ D hB hφ Λ χ hχ
  have hgen := (affineSimpleGenerators B H φ hB hφ θ hθ T S).1
  have hemem (i : I) : e i ∈ positive D := raising_mem_positive D T S hgen i
  have hrelations := affineSimpleTripleRelations B H φ hB hφ θ hθ T S
  have htriple (i : I) : IsSl2Triple (h i : Carrier D) (e i) (f i) := by
    obtain ⟨hn, hef, hhe, hhf⟩ := hrelations.1 i
    have hi : (h i : Carrier D) = (show Carrier D from affineSimpleH B H θ i) :=
      coe_affineSimpleCoroot θ i
    rw [hi]
    refine ⟨hn, hef, ?_, ?_⟩
    · change affineBracket_value B (affineSimpleH B H θ i) (affineSimpleE B T S i) =
        (2 : ℕ) • affineSimpleE B T S i
      simpa only [two_smul, two_nsmul] using hhe
    · change affineBracket_value B (affineSimpleH B H θ i) (affineSimpleF B T S i) =
        -((2 : ℕ) • affineSimpleF B T S i)
      simpa only [neg_smul, two_smul, two_nsmul] using hhf
  have he_top (i : I) : ι ℂ (e i) • v = 0 := hvtop.2 ⟨e i, hemem i⟩
  constructor
  · intro hint i
    exact coroot_value_nat (htriple i) hv (hvtop.1 (h i)) (he_top i) ((hint i).2 v)
  · intro hdom i
    have hlocal (x : Carrier D)
        (hx : x = e i ∨ x = f i) (hn : ∃ n : ℕ, (ι ℂ x) ^ n • v = 0) :
        ∀ y : affineSimple D χ, ∃ n : ℕ, (ι ℂ x) ^ n • y = 0 := by
      let ring : LieRing (Carrier D) := inferInstance
      let algebra : LieAlgebra ℂ (Carrier D) := inferInstance
      have hcompat : CompatibleLieStructure B ring algebra := ⟨rfl, HEq.rfl, fun _ _ => rfl⟩
      intro y
      obtain ⟨a, rfl⟩ := hcyclic y
      have hmem : a • v ∈ Submodule.span (U (Carrier D)) ({v} : Set (affineSimple D χ)) :=
        Submodule.mem_span_singleton.mpr ⟨a, rfl⟩
      exact @affineSimpleLocallyNilpotentOnCyclic.{u,u} G _ _ _ _ B H _ φ hB hφ θ hθ T S
        i x hx ring algebra hcompat (affineSimple D χ) _
        (inferInstance : Module (U (Carrier D)) (affineSimple D χ)) v hn _ hmem
    refine ⟨hlocal (e i) (Or.inl rfl) ⟨1, by simpa only [pow_one] using he_top i⟩, ?_⟩
    apply hlocal (f i) (Or.inr rfl)
    obtain ⟨m, hm⟩ := hdom i
    change c i = (m : ℂ) at hm
    let w := affineVermaTop D χ
    let z := (ι ℂ (f i)) ^ (m + 1) • w
    let μ := Λ - (m + 1) • α i
    have hw := (affineVermaUniversal.{u,u} B H φ D hB hφ Λ χ hχ).1
    have hwnz := (affineVermaWeights B H φ D hB hφ Λ χ hχ).2.2.1
    have he_w (j : I) : ι ℂ (e j) • w = 0 := hw.2 ⟨e j, hemem j⟩
    have he_z (j : I) : ι ℂ (e j) • z = 0 := by
      by_cases hj : j = i
      · subst j
        have hx := raising_lowering_power (htriple i) hwnz (hw.1 (h i)) (he_w i) m
        change ι ℂ (e i) • z = ((m + 1 : ℂ) * (c i - m)) •
          ((ι ℂ (f i)) ^ m • w) at hx
        simpa only [hm, sub_self, mul_zero, zero_smul] using hx
      · have hc : Commute (ι ℂ (e j)) (ι ℂ (f i)) := by
          apply sub_eq_zero.mp
          rw [enveloping_commutator]
          have hz : ⁅e j, f i⁆ = 0 := hrelations.2 j i hj
          rw [hz, map_zero]
        change ι ℂ (e j) • ((ι ℂ (f i)) ^ (m + 1) • w) = 0
        rw [← mul_smul, (hc.pow_right (m + 1)).eq, mul_smul, he_w, smul_zero]
    have hf_weight (j : I) (a : affineCartan B H) :
        ⁅(show Carrier D from a.1), f j⁆ = (-α j a) • f j :=
      (affineSimpleRootWeights B H φ hB hφ θ hθ T S j).2.2.2 a
    have hz_weight : z ∈ affineVermaWeightSpace D χ μ := by
      have hz' := simpleWord_mem_weight D Λ χ hχ θ f hf_weight (List.replicate (m + 1) i)
      simpa only [simpleWord, simpleWordWeight, List.map_replicate, List.prod_replicate,
        List.sum_replicate, α, μ, z, w] using hz'
    have hz_top : IsHighestVector D μ z := by
      refine ⟨fun a => (mem_affineVermaWeightSpace D χ μ z).mp hz_weight ⟨a.1, a.2⟩,
        positive_kills_of_generators D T S z hgen he_z⟩
    have hbelow : heightScore B H φ θ μ < heightScore B H φ θ Λ := by
      change heightScore B H φ θ (Λ - (m + 1) • α i) < _
      rw [map_sub, map_nsmul]
      exact sub_lt_self _ (nsmul_pos (heightScore_pos (B := B) θ i) (Nat.succ_ne_zero m))
    have hz_rad := lower_highest_mem_radical D hB hφ hθ Λ μ χ hχ z hz_top hbelow
    refine ⟨m + 1, ?_⟩
    let q := affineSimpleProjection D χ
    change (ι ℂ (f i)) ^ (m + 1) • q w = 0
    rw [← q.map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hz_rad

theorem affineIntegrableLevel : affineIntegrableLevel_type.{u} := by
  classical
  intro G _ _ _ _ B H _ φ D hB hφ θ hθ T S Λ χ hχ hint
  obtain ⟨a, ha⟩ := highestFiniteCorootCoordinates H φ hφ θ hθ
  have hdom := (affineSimpleIntegrable B H φ D hB hφ θ hθ T S Λ χ hχ).mp hint
  choose n hn using hdom
  refine ⟨n none + a.sum (fun i m => m * n (some i)), ?_⟩
  rw [affineLevelFormula B H φ θ a ha Λ]
  simp only [Finsupp.sum, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, hn]

end HighestWeight

end RepTheorySurvey.Affine
