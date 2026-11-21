import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealSimpleBranches
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormLowRanks
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactRealForm
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SemisimpleBaseChange
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsConjugations
import Mathlib.LinearAlgebra.Projection

import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormLowRanks
noncomputable section

open scoped TensorProduct

universe u

namespace LieAlgebrasAndRepresentations.RealSimpleBranches

open RealForms LieAlgebra Complex
open Specs.LieAlgebrasAndRepresentations.RealSimpleBranches

section ConjugationIdeals

variable {V : Type u} [LieRing V] [LieAlgebra ℂ V]

/-- Conjugation acts on complex ideals by inverse image, which agrees with
its image since it is involutive. -/
private def conjugateIdeal (σ : Conjugation V) (I : LieIdeal ℂ V) : LieIdeal ℂ V where
  carrier := {x | σ.map x ∈ I}
  zero_mem' := by
    change σ.map 0 ∈ I
    rw [map_zero]
    exact I.zero_mem
  add_mem' {x y} hx hy := by
    change σ.map (x + y) ∈ I
    rw [map_add]
    exact I.add_mem hx hy
  smul_mem' a x hx := by
    change σ.map (a • x) ∈ I
    rw [σ.antilinear]
    exact I.smul_mem (star a) hx
  lie_mem {x y} hy := by
    change σ.map ⁅x, y⁆ ∈ I
    rw [σ.map.map_lie]
    exact I.lie_mem hy

private theorem conjugateIdeal_involutive (σ : Conjugation V) :
    Function.Involutive (conjugateIdeal σ) := by
  intro I
  ext x
  change σ.map (σ.map x) ∈ I ↔ x ∈ I
  rw [σ.involutive x]

private def conjugateIdealEquiv (σ : Conjugation V) : LieIdeal ℂ V ≃o LieIdeal ℂ V where
  toEquiv := (conjugateIdeal_involutive σ).toPerm _
  map_rel_iff' := by
    intro I J
    change conjugateIdeal σ I ≤ conjugateIdeal σ J ↔ I ≤ J
    constructor
    · intro h x hx
      have hm : σ.map x ∈ conjugateIdeal σ I := by
        change σ.map (σ.map x) ∈ I
        rwa [σ.involutive x]
      have hj := h hm
      change σ.map (σ.map x) ∈ J at hj
      rwa [σ.involutive x] at hj
    · exact fun h _ hx => h hx

private def fixedIdeal (σ : Conjugation V) (I : LieIdeal ℂ V) : LieIdeal ℝ σ.fixed where
  carrier := {x | (x : V) ∈ I}
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' a _ hx := I.smul_mem (a : ℂ) hx
  lie_mem := I.lie_mem

private theorem stableIdeal_eq_bot_or_top (σ : Conjugation V) [IsSimple ℝ σ.fixed]
    (I : LieIdeal ℂ V) (hI : conjugateIdeal σ I = I) : I = ⊥ ∨ I = ⊤ := by
  have hparts (x : V) (hx : x ∈ I) :
      ∃ a b : σ.fixed, a ∈ fixedIdeal σ I ∧ b ∈ fixedIdeal σ I ∧
        (a : V) + Complex.I • (b : V) = x := by
    have hσx : σ.map x ∈ I := by
      change x ∈ conjugateIdeal σ I
      rwa [hI]
    obtain ⟨a, b, ha, hb, hab⟩ := fixed_parts_formula σ x
    refine ⟨a, b, ?_, ?_, hab⟩
    · change (a : V) ∈ I
      rw [ha]
      exact I.smul_mem _ (I.add_mem hx hσx)
    · change (b : V) ∈ I
      rw [hb]
      exact I.smul_mem _ (I.sub_mem hx hσx)
  rcases IsSimple.eq_bot_or_eq_top (fixedIdeal σ I) with h | h
  · left
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨a, b, ha, hb, hab⟩ := hparts x hx
    rw [h, LieSubmodule.mem_bot] at ha hb
    rw [← hab, ha, hb]
    simp
  · right
    apply top_unique
    intro x _
    obtain ⟨a, b, hab⟩ := fixed_decomposition σ x
    have ha : a ∈ fixedIdeal σ I := by rw [h]; exact LieSubmodule.mem_top a
    have hb : b ∈ fixedIdeal σ I := by rw [h]; exact LieSubmodule.mem_top b
    rw [← hab]
    exact I.add_mem ha (I.smul_mem _ hb)

private def fixedProjection (σ : Conjugation V) (I J : LieIdeal ℂ V)
    (hJ : conjugateIdeal σ I = J) (e : (I × J) ≃ₗ⁅ℂ⁆ V)
    (he : ∀ x y, e (x, y) = (x : V) + (y : V)) :
    σ.fixed ≃ₗ⁅ℝ⁆ I := by
  let f : σ.fixed →ₗ⁅ℝ⁆ I :=
    { toFun := fun x => (e.symm (x : V)).1
      map_add' := fun x y => congrArg Prod.fst (e.symm.map_add (x : V) (y : V))
      map_smul' := fun a x => congrArg Prod.fst (e.symm.map_smul (a : ℂ) (x : V))
      map_lie' := fun {x y} => congrArg Prod.fst (e.symm.map_lie (x : V) (y : V)) }
  have hIJ (x : I) : σ.map (x : V) ∈ J := by
    rw [← hJ]
    change σ.map (σ.map (x : V)) ∈ I
    rw [σ.involutive]
    exact x.property
  have hJI (y : J) : σ.map (y : V) ∈ I := by
    change (y : V) ∈ conjugateIdeal σ I
    rw [hJ]
    exact y.property
  have hsecond (x : σ.fixed) : ((e.symm (x : V)).2 : V) = σ.map (f x : V) := by
    let p := e.symm (x : V)
    have hp : (p.1 : V) + (p.2 : V) = (x : V) :=
      (he p.1 p.2).symm.trans (e.apply_symm_apply _)
    have hfix : σ.map (x : V) = (x : V) := x.property
    have hp' : e (⟨σ.map (p.2 : V), hJI p.2⟩, ⟨σ.map (p.1 : V), hIJ p.1⟩) = e p := by
      rw [he]
      change σ.map (p.2 : V) + σ.map (p.1 : V) = e (e.symm (x : V))
      rw [add_comm, ← map_add, hp, hfix, e.apply_symm_apply]
    exact (congrArg (fun t : I × J => (t.2 : V)) (e.injective hp')).symm
  apply LieEquiv.ofBijective f
  constructor
  · intro x y h
    have h₁ : (e.symm (x : V)).1 = (e.symm (y : V)).1 := h
    have h₂ : (e.symm (x : V)).2 = (e.symm (y : V)).2 := by
      apply Subtype.ext
      rw [hsecond, hsecond, h]
    exact Subtype.ext (e.symm.injective (Prod.ext h₁ h₂))
  · intro x
    let y : J := ⟨σ.map (x : V), hIJ x⟩
    let z : σ.fixed := ⟨e (x, y), by
      change σ.map (e (x, y)) = e (x, y)
      rw [he, map_add]
      change σ.map (x : V) + σ.map (σ.map (x : V)) = (x : V) + σ.map (x : V)
      rw [σ.involutive, add_comm]⟩
    refine ⟨z, ?_⟩
    change (e.symm (e (x, y))).1 = x
    rw [e.symm_apply_apply]

end ConjugationIdeals

private theorem simple_of_equiv {R A B : Type*} [CommRing R]
    [LieRing A] [LieAlgebra R A] [LieRing B] [LieAlgebra R B] [IsSimple R A]
    (e : A ≃ₗ⁅R⁆ B) : IsSimple R B where
  non_abelian h := IsSimple.non_abelian R ((lie_abelian_iff_equiv_lie_abelian e).mpr h)
  eq_bot_or_eq_top I := by
    let f := e.symm.toLieHom
    rcases IsSimple.eq_bot_or_eq_top (I.map f) with h | h
    · exact Or.inl (LieIdeal.bot_of_map_eq_bot e.symm.injective h)
    · right
      apply top_unique
      intro x _
      have hm : f x ∈ I.map f := h ▸ LieSubmodule.mem_top (f x)
      obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective e.symm.surjective hm
      exact e.symm.injective hy ▸ y.property

private theorem exists_conjugation (V : Type u) [LieRing V] [LieAlgebra ℂ V]
    [FiniteDimensional ℂ V] [IsSimple ℂ V] : Nonempty (Conjugation V) := by
  have h : LieAlgebrasAndRepresentations.IsSemisimple ℂ V := HasTrivialRadical.radical_eq_bot
  obtain ⟨σ, -, -⟩ := CompactRealForm.compact_real_form h
  exact ⟨σ⟩

private def equivConjugateIdeal {V : Type u} [LieRing V] [LieAlgebra ℂ V]
    (σ : Conjugation V) (I : LieIdeal ℂ V) (ω : Conjugation I) :
    I ≃ₗ⁅ℂ⁆ conjugateIdeal σ I := by
  let f : I →ₗ⁅ℂ⁆ conjugateIdeal σ I :=
    { toFun := fun x => ⟨σ.map (ω.map x : V), by
        change σ.map (σ.map (ω.map x : V)) ∈ I
        rw [σ.involutive]
        exact (ω.map x).property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change σ.map (ω.map (x + y) : V) = σ.map (ω.map x : V) + σ.map (ω.map y : V)
        rw [map_add, LieSubmodule.coe_add, map_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        change σ.map (ω.map (a • x) : V) = a • σ.map (ω.map x : V)
        rw [ω.antilinear, LieSubmodule.coe_smul, σ.antilinear, star_star]
      map_lie' := by
        intro x y
        apply Subtype.ext
        change σ.map (ω.map ⁅x, y⁆ : V) = ⁅σ.map (ω.map x : V), σ.map (ω.map y : V)⁆
        rw [ω.map.map_lie]
        exact σ.map.map_lie _ _ }
  refine LieEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact ω.involutive.injective (Subtype.ext (σ.involutive.injective (congrArg Subtype.val h)))
  · intro y
    let x : I := ⟨σ.map (y : V), y.property⟩
    refine ⟨ω.map x, Subtype.ext ?_⟩
    change σ.map (ω.map (ω.map x) : V) = (y : V)
    rw [ω.involutive x]
    exact σ.involutive (y : V)

private def sumOfComplementaryIdeals {V : Type u} [LieRing V] [LieAlgebra ℂ V]
    (I J : LieIdeal ℂ V) (h : IsCompl I J) : (I × J) ≃ₗ⁅ℂ⁆ V := by
  let e := I.toSubmodule.prodEquivOfIsCompl J.toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr h)
  refine { e with map_lie' := ?_ }
  have commutes (x y : V) (hx : x ∈ I) (hy : y ∈ J) : ⁅x, y⁆ = 0 := by
    have hm : ⁅x, y⁆ ∈ I ⊓ J := ⟨lie_mem_left ℂ V I x y hx, lie_mem_right ℂ V J x y hy⟩
    simpa [h.disjoint.eq_bot] using hm
  rintro ⟨x, y⟩ ⟨x', y'⟩
  change ⁅(x : V), (x' : V)⁆ + ⁅(y : V), (y' : V)⁆ =
    ⁅(x : V) + (y : V), (x' : V) + (y' : V)⁆
  rw [add_lie, lie_add, lie_add, commutes _ _ x.property y'.property,
    ← lie_skew (y : V) (x' : V), commutes _ _ x'.property y.property]
  simp

private theorem real_simple_branches_proof : real_simple_branches_type.{u} := by
  intro L _ _ _ hsimple
  let : IsSimple ℝ L := hsimple
  let V := ℂ ⊗[ℝ] L
  let σ : Conjugation V := coefficientConjugation L
  obtain ⟨f, -⟩ := coefficient_fixed_equiv L
  let : IsSimple ℝ σ.fixed := simple_of_equiv f
  let : Nontrivial L := IsSimple.nontrivial ℝ L
  let : Nontrivial V :=
    Function.Injective.nontrivial (f := fun x : L => (1 : ℂ) ⊗ₜ[ℝ] x) one_tmul_injective
  let : LieAlgebra.IsSemisimple ℂ V :=
    LieAlgebrasAndRepresentations.semisimple_structure ℂ V
      (semisimple_complexification L HasTrivialRadical.radical_eq_bot)
  have hex : ∃ I : LieIdeal ℂ V, IsAtom I := by
    by_contra! hn
    have he : {I : LieIdeal ℂ V | IsAtom I} = ∅ := Set.eq_empty_iff_forall_notMem.mpr hn
    have ht := LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := ℂ) (L := V)
    rw [he, sSup_empty] at ht
    exact bot_ne_top ht
  obtain ⟨I, hI⟩ := hex
  let J := conjugateIdeal σ I
  have hJ : IsAtom J := ((conjugateIdealEquiv σ).isAtom_iff I).mpr hI
  have hII : IsSimple ℂ I := IsSemisimple.isSimple_of_isAtom I hI
  by_cases h : J = I
  · have hi := (stableIdeal_eq_bot_or_top σ I h).resolve_left hI.ne_bot
    left
    rw [hi] at hII
    let : IsSimple ℂ (⊤ : LieIdeal ℂ V) := hII
    exact simple_of_equiv LieIdeal.topEquiv
  · right
    have hinv : conjugateIdeal σ J = I := conjugateIdeal_involutive σ I
    have hstable : conjugateIdeal σ (I ⊔ J) = I ⊔ J := by
      change conjugateIdealEquiv σ (I ⊔ J) = I ⊔ J
      rw [OrderIso.map_sup]
      change J ⊔ conjugateIdeal σ J = I ⊔ J
      rw [hinv, sup_comm]
    have htop := (stableIdeal_eq_bot_or_top σ _ hstable).resolve_left (by
      intro hb
      exact hI.ne_bot (le_bot_iff.mp (le_sup_left.trans hb.le)))
    have hc : IsCompl I J := ⟨hI.disjoint_of_ne hJ (Ne.symm h), codisjoint_iff.mpr htop⟩
    let e := sumOfComplementaryIdeals I J hc
    have he (x : I) (y : J) : e (x, y) = (x : V) + (y : V) := rfl
    obtain ⟨ω⟩ := exists_conjugation I
    refine ⟨I, J, hc, hII, IsSemisimple.isSimple_of_isAtom J hJ, ?_,
      ⟨equivConjugateIdeal σ I ω⟩, ⟨f.trans (fixedProjection σ I J rfl e he)⟩, e, he⟩
    intro z
    change z ∈ I ↔ σ.map (σ.map z) ∈ I
    rw [σ.involutive]

private theorem simple_restrictScalars (L : Type u) [LieRing L] [LieAlgebra ℂ L]
    [IsSimple ℂ L] : IsSimple ℝ L where
  non_abelian h := IsSimple.non_abelian ℂ h
  eq_bot_or_eq_top I := by
    by_cases hb : I = ⊥
    · exact Or.inl hb
    · right
      let J : LieIdeal ℂ L :=
        { carrier := {x | x ∈ I ∧ Complex.I • x ∈ I}
          zero_mem' := by simp
          add_mem' hx hy := ⟨I.add_mem hx.1 hy.1, by
            rw [smul_add]
            exact I.add_mem hx.2 hy.2⟩
          smul_mem' a x hx := by
            have hmul (b : ℂ) : b • x ∈ I := by
              have heq : b • x = b.re • x + b.im • (Complex.I • x) := by
                change b • x = (b.re : ℂ) • x + (b.im : ℂ) • (Complex.I • x)
                simpa only [add_smul, mul_smul] using
                  congrArg (fun c : ℂ => c • x) (Complex.re_add_im b).symm
              rw [heq]
              exact I.add_mem (I.smul_mem b.re hx.1) (I.smul_mem b.im hx.2)
            exact ⟨hmul a, by rw [smul_smul]; exact hmul _⟩
          lie_mem := fun {x y} hy => ⟨I.lie_mem hy.1, by
            rw [← lie_smul]
            exact I.lie_mem hy.2⟩ }
      have hJ : J ≠ ⊥ := by
        intro hJ
        apply hb
        apply le_antisymm _ bot_le
        intro x hx
        have hxcenter : x ∈ center ℂ L := by
          change ∀ y : L, ⁅y, x⁆ = 0
          intro y
          have hy : ⁅y, x⁆ ∈ J := ⟨I.lie_mem hx, by
            rw [← smul_lie]
            exact I.lie_mem hx⟩
          simpa [hJ] using hy
        rwa [center_eq_bot ℂ L] at hxcenter
      have htop := (IsSimple.eq_bot_or_eq_top J).resolve_left hJ
      apply top_unique
      intro x _
      have hx : x ∈ J := by rw [htop]; exact LieSubmodule.mem_top x
      exact hx.1

private def exchangeConjugation {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (σ : Conjugation L) : Conjugation (L × L) where
  map :=
    { toFun := fun x => (σ.map x.2, σ.map x.1)
      map_add' := fun x y => Prod.ext (σ.map.map_add x.2 y.2) (σ.map.map_add x.1 y.1)
      map_smul' := fun a x => Prod.ext (σ.map.map_smul a x.2) (σ.map.map_smul a x.1)
      map_lie' := fun {x y} => Prod.ext (σ.map.map_lie x.2 y.2) (σ.map.map_lie x.1 y.1) }
  antilinear := fun a x => Prod.ext (σ.antilinear a x.2) (σ.antilinear a x.1)
  involutive := fun x => Prod.ext (σ.involutive x.1) (σ.involutive x.2)

private def exchangeFixedEquiv {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (σ : Conjugation L) : L ≃ₗ⁅ℝ⁆ (exchangeConjugation σ).fixed := by
  let f : L →ₗ⁅ℝ⁆ (exchangeConjugation σ).fixed :=
    { toFun := fun x => ⟨(x, σ.map x), Prod.ext (σ.involutive x) rfl⟩
      map_add' := fun x y => Subtype.ext (Prod.ext rfl (σ.map.map_add x y))
      map_smul' := fun a x => Subtype.ext (Prod.ext rfl (σ.map.map_smul a x))
      map_lie' := fun {x y} => Subtype.ext (Prod.ext rfl (σ.map.map_lie x y)) }
  refine LieEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact congrArg (fun z : (exchangeConjugation σ).fixed => (z : L × L).1) h
  · intro x
    have hx := congrArg Prod.snd x.property
    exact ⟨(x : L × L).1, Subtype.ext (Prod.ext rfl hx)⟩

private theorem complex_simple_restriction_proof : complex_simple_restriction_type.{u} := by
  intro L _ _ _ hsimple
  let : IsSimple ℂ L := hsimple
  obtain ⟨σ⟩ := exists_conjugation L
  let τ := exchangeConjugation σ
  let f := exchangeFixedEquiv σ
  obtain ⟨g, hg⟩ := fixed_complexification τ
  let e := (complexifyEquiv f).trans g
  have he (a : ℂ) (x : L) : e (a ⊗ₜ[ℝ] x) = (a • x, a • σ.map x) := by
    change g (a ⊗ₜ[ℝ] f x) = _
    rw [hg]
    rfl
  refine ⟨simple_restrictScalars L, σ, e, he, ?_⟩
  intro z
  change e (coefficientConjugationMap L z) = τ.map (e z)
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [coefficientConjugationMap_tmul, he, he]
    change (star a • x, star a • σ.map x) =
      (σ.map (a • σ.map x), σ.map (a • x))
    rw [σ.antilinear, σ.antilinear, σ.involutive]

open Specs.LieAlgebrasAndRepresentations.RealFormLowRanks

/-- Conditional derivation of `real_simple_branches_type` with the low-rank premises. -/
theorem real_simple_branches_conditional
    (_b1_compact : b1_compact_type)
    (_b1_split : b1_split_type)
    (_b2_compact : b2_compact_type)
    (_b2_quaternionic : b2_quaternionic_type)
    (_b2_split : b2_split_type)
    (_d2_abstract_classification : d2_abstract_classification_type.{u})
    (_d2_classification : d2_classification_type)
    (_d2_compact : d2_compact_type)
    (_d2_complex : d2_complex_type)
    (_d2_distinct : d2_distinct_type)
    (_d2_lorentz : d2_lorentz_type)
    (_d2_models_real_forms : d2_models_real_forms_type)
    (_d2_quaternionic : d2_quaternionic_type)
    (_d2_quaternionic_compact : d2_quaternionic_compact_type)
    (_d2_split : d2_split_type)
    (_d3_compact : d3_compact_type)
    (_d3_orthogonal_quaternionic : d3_orthogonal_quaternionic_type)
    (_d3_quaternionic : d3_quaternionic_type)
    (_d3_split : d3_split_type)
    (_d3_unitary : d3_unitary_type)
    (_d4_triality : d4_triality_type)
    : real_simple_branches_type.{u} :=
  real_simple_branches_proof

/-- Conditional derivation of `complex_simple_restriction_type` with the low-rank premises. -/
theorem complex_simple_restriction_conditional
    (_b1_compact : b1_compact_type)
    (_b1_split : b1_split_type)
    (_b2_compact : b2_compact_type)
    (_b2_quaternionic : b2_quaternionic_type)
    (_b2_split : b2_split_type)
    (_d2_abstract_classification : d2_abstract_classification_type.{u})
    (_d2_classification : d2_classification_type)
    (_d2_compact : d2_compact_type)
    (_d2_complex : d2_complex_type)
    (_d2_distinct : d2_distinct_type)
    (_d2_lorentz : d2_lorentz_type)
    (_d2_models_real_forms : d2_models_real_forms_type)
    (_d2_quaternionic : d2_quaternionic_type)
    (_d2_quaternionic_compact : d2_quaternionic_compact_type)
    (_d2_split : d2_split_type)
    (_d3_compact : d3_compact_type)
    (_d3_orthogonal_quaternionic : d3_orthogonal_quaternionic_type)
    (_d3_quaternionic : d3_quaternionic_type)
    (_d3_split : d3_split_type)
    (_d3_unitary : d3_unitary_type)
    (_d4_triality : d4_triality_type)
    : complex_simple_restriction_type.{u} :=
  complex_simple_restriction_proof

end LieAlgebrasAndRepresentations.RealSimpleBranches

universe v8_closure_62a47918e16adcd7_u0
theorem _root_.«LieAlgebrasAndRepresentations».«RealSimpleBranches».«complex_simple_restriction» : _root_.«Specs».«LieAlgebrasAndRepresentations».«RealSimpleBranches».«complex_simple_restriction_type».{v8_closure_62a47918e16adcd7_u0} :=
  @_root_.«LieAlgebrasAndRepresentations».«RealSimpleBranches».«complex_simple_restriction_conditional».{v8_closure_62a47918e16adcd7_u0} (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b1_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b1_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b2_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b2_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b2_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_abstract_classification».{v8_closure_62a47918e16adcd7_u0}) (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_classification») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_complex») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_distinct») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_lorentz») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_models_real_forms») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_quaternionic_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_orthogonal_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_unitary») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d4_triality»)
theorem _root_.«LieAlgebrasAndRepresentations».«RealSimpleBranches».«real_simple_branches» : _root_.«Specs».«LieAlgebrasAndRepresentations».«RealSimpleBranches».«real_simple_branches_type».{v8_closure_62a47918e16adcd7_u0} :=
  @_root_.«LieAlgebrasAndRepresentations».«RealSimpleBranches».«real_simple_branches_conditional».{v8_closure_62a47918e16adcd7_u0} (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b1_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b1_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b2_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b2_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«b2_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_abstract_classification».{v8_closure_62a47918e16adcd7_u0}) (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_classification») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_complex») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_distinct») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_lorentz») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_models_real_forms») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_quaternionic_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d2_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_compact») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_orthogonal_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_quaternionic») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_split») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d3_unitary») (@_root_.«LieAlgebrasAndRepresentations».«RealFormLowRanks».«d4_triality»)
