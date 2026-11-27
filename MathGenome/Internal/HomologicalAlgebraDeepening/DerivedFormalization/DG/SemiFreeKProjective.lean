import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.SemiFreeKProjective
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex

universe u v w j

namespace DerivedFormalization.RightDGModule

theorem kProjectiveClosure :
    Specs.DerivedFormalization.DG.SemiFreeKProjective.Closure.{u,v,w,j} :=
  ⟨fun s h => IsKProjective.shift s h, fun f hP hQ => IsKProjective.cone f hP hQ,
    fun c hc h => IsKProjective.coproduct c hc h⟩

open Specs.DerivedFormalization.DG

open private acyclic_iff_boundaries d_d_apply precomp precomp_app restrict restrict_app
  restrict_zero restrict_sub restrict_d gradedHom_ext_apply
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N P Q : RightDGModule A} {r : ℤ}

private theorem restrict_comp (f : M ⟶ P) (g : P ⟶ Q) (h : GradedHom Q N r) :
    restrict (f ≫ g) h = restrict f (restrict g h) := by
  apply gradedHom_ext_apply
  intro a i q e x
  rw [restrict_app, restrict_app, restrict_app]
  rfl

private theorem restrict_id (h : GradedHom M N r) : restrict (𝟙 M) h = h := by
  apply gradedHom_ext_apply
  intro a i q e x
  rw [restrict_app]
  rfl

private theorem restrict_add (f : M ⟶ P) (g h : GradedHom P N r) :
    restrict f (g + h) = restrict f g + restrict f h := by
  unfold restrict precomp
  rw [map_add, LinearMap.add_apply]

private theorem graded_zero_app (a : A.Obj) (i q : ℤ) (e : i+r = q)
    (x : (M.complex a).X i) :
    (0 : GradedHom M N r).app a i q e x = 0 := by
  change (0 : Cochain (M.complex a) (N.complex a) r).v i q e x = 0
  rw [Cochain.zero_v]
  rfl

private theorem representable_kProjective (a : A.Obj) : (representable a).IsKProjective := by
  intro N hN
  apply (acyclic_iff_boundaries _).2
  intro r f hf
  have hf' : (N.complex a).d (r+1) (r+1+1) (yonedaEquiv a N (r+1) f) = 0 := by
    rw [← yonedaEquiv_comm_d, hf, map_zero]
  obtain ⟨x, hx⟩ := (acyclic_iff_boundaries _).1 (hN a) r _ hf'
  refine ⟨(yonedaEquiv a N r).symm x, (yonedaEquiv a N (r+1)).injective ?_⟩
  rw [yonedaEquiv_comm_d, LinearEquiv.apply_symm_apply, hx]

section Attachment

open IndexedSemiFree

variable {I : Type j} {C : IndexedCellFamily P I} (E : IndexedAttachment C Q)

/-- Degreewise inclusion of one new cell in the graded splitting. -/
private def cellEmbedding (s : I) (a : A.Obj) (i : ℤ) :
    ((cells C s).complex a).X i →ₗ[k] (Q.complex a).X i :=
  (E.coordinates a i).symm.toLinearMap.comp
    ((LinearMap.inr k _ _).comp (summand (cells C) a i s))

private theorem cellEmbedding_coordinates (s : I) (a : A.Obj) (i : ℤ)
    (x : ((cells C s).complex a).X i) :
    E.coordinates a i (cellEmbedding E s a i x) = (0, summand (cells C) a i s x) :=
  (E.coordinates a i).apply_symm_apply _

private theorem cellEmbedding_act (s : I) {a b : A.Obj} (i l n : ℤ) (e : i+l = n)
    (x : ((cells C s).complex b).X i) (z : (A.hom a b).X l) :
    cellEmbedding E s a n ((cells C s).act i l n e x z) =
      Q.act i l n e (cellEmbedding E s b i x) z := by
  classical
  apply (E.coordinates a n).injective
  rw [cellEmbedding_coordinates]
  obtain ⟨h₁, h₂⟩ := E.coordinate_act i l n e (cellEmbedding E s b i x) z
  dsimp only at h₁ h₂
  rw [cellEmbedding_coordinates] at h₁ h₂
  apply Prod.ext
  · exact (h₁.trans (by simp)).symm
  · apply DFinsupp.ext
    intro t
    rw [h₂ t]
    change summand (cells C) a n s _ t = (cells C t).act i l n e
      (summand (cells C) b i s x t) z
    simp only [summand, DirectSum.lof_eq_of]
    by_cases h : t = s
    · subst t
      simp
    · simp [DirectSum.of_eq_of_ne _ _ _ h]

private theorem cellEmbedding_d (s : I) (a : A.Obj) (i : ℤ)
    (x : ((cells C s).complex a).X i) :
    (Q.complex a).d i (i+1) (cellEmbedding E s a i x) =
      (E.inclusion.app a).f (i+1) (boundaryMap C a i (summand (cells C) a i s x)) +
        cellEmbedding E s a (i+1) (((cells C s).complex a).d i (i+1) x) := by
  classical
  apply (E.coordinates a (i+1)).injective
  rw [map_add, E.coordinate_inclusion, cellEmbedding_coordinates]
  obtain ⟨h₁, h₂⟩ := E.coordinate_d a i (cellEmbedding E s a i x)
  dsimp only at h₁ h₂
  rw [cellEmbedding_coordinates] at h₁ h₂
  apply Prod.ext
  · simpa using h₁
  · apply DFinsupp.ext
    intro t
    rw [Prod.snd_add, zero_add, h₂ t]
    change ((cells C t).complex a).d i (i+1) (summand (cells C) a i s x t) =
      summand (cells C) a (i+1) s (((cells C s).complex a).d i (i+1) x) t
    simp only [summand, DirectSum.lof_eq_of]
    by_cases h : t = s
    · subst t
      simp only [DirectSum.of_eq_same]
    · simp only [DirectSum.of_eq_of_ne _ _ _ h, map_zero]

private def attachmentRetraction : GradedHom Q P 0 :=
  GradedHom.mk (fun a i q e => by
    obtain rfl : i = q := by omega
    exact ModuleCat.ofHom ((LinearMap.fst k _ _).comp (E.coordinates a i).toLinearMap)) (by
    intro a b i l n ir nr h hi hn x z
    obtain rfl : i = ir := by omega
    obtain rfl : n = nr := by omega
    exact (E.coordinate_act i l n h x z).1)

private def cellSection (s : I) : GradedHom (cells C s) Q 0 :=
  GradedHom.mk (fun a i q e => by
    obtain rfl : i = q := by omega
    exact ModuleCat.ofHom (cellEmbedding E s a i)) (by
    intro a b i l n ir nr h hi hn x z
    obtain rfl : i = ir := by omega
    obtain rfl : n = nr := by omega
    exact cellEmbedding_act E s i l n h x z)

private theorem restrict_inclusion_extend (g : GradedHom P N r) :
    restrict E.inclusion (precomp (attachmentRetraction E) g) = g := by
  apply gradedHom_ext_apply
  intro a i q e x
  rw [restrict_app, precomp_app]
  change g.app a i q e ((E.coordinates a i ((E.inclusion.app a).f i x)).1) = _
  rw [E.coordinate_inclusion]

private theorem attachment_linear_ext {V : Type*} [AddCommMonoid V] [Module k V]
    (a : A.Obj) (i : ℤ) {f g : (Q.complex a).X i →ₗ[k] V}
    (h₀ : ∀ x, f ((E.inclusion.app a).f i x) = g ((E.inclusion.app a).f i x))
    (h₁ : ∀ s x, f (cellEmbedding E s a i x) = g (cellEmbedding E s a i x)) :
    f = g := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨⟨p, y⟩, rfl⟩ := (E.coordinates a i).symm.surjective x
  have split : (p, y) = (p, 0) + (0, y) := by simp
  have old : (E.coordinates a i).symm (p, 0) = (E.inclusion.app a).f i p := by
    rw [← E.coordinate_inclusion, LinearEquiv.symm_apply_apply]
  rw [split, map_add, map_add, map_add, old, h₀]
  congr 1
  let left := f.comp ((E.coordinates a i).symm.toLinearMap.comp (LinearMap.inr k _ _))
  let right := g.comp ((E.coordinates a i).symm.toLinearMap.comp (LinearMap.inr k _ _))
  change left y = right y
  have eq : left = right := DirectSum.linearMap_ext k fun s => LinearMap.ext (h₁ s)
  rw [eq]

private def correctionComponent (g : ∀ s, GradedHom (cells C s) N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) :
    (Q.complex a).X i →ₗ[k] (N.complex a).X q := by
  classical
  exact (DirectSum.toModule k I _ fun s => (g s).app a i q e |>.hom).comp
    ((LinearMap.snd k _ _).comp (E.coordinates a i).toLinearMap)

private theorem correctionComponent_inclusion (g : ∀ s, GradedHom (cells C s) N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (x : (P.complex a).X i) :
    correctionComponent E g a i q e ((E.inclusion.app a).f i x) = 0 := by
  classical
  simp [correctionComponent, E.coordinate_inclusion]

private theorem correctionComponent_cell (g : ∀ s, GradedHom (cells C s) N r)
    (a : A.Obj) (i q : ℤ) (e : i+r = q) (s : I) (x : ((cells C s).complex a).X i) :
    correctionComponent E g a i q e (cellEmbedding E s a i x) = (g s).app a i q e x := by
  classical
  change DirectSum.toModule k I _ (fun t => ((g t).app a i q e).hom)
    (E.coordinates a i (cellEmbedding E s a i x)).2 = _
  rw [cellEmbedding_coordinates]
  change DirectSum.toModule k I _ (fun t => ((g t).app a i q e).hom)
    (DirectSum.lof k I (fun t => ((cells C t).complex a).X i) s x) = _
  rw [DirectSum.toModule_lof]

private def correction (g : ∀ s, GradedHom (cells C s) N r) : GradedHom Q N r :=
  GradedHom.mk (fun a i q e => ModuleCat.ofHom (correctionComponent E g a i q e)) (by
    intro a b i l n ir nr h hi hn x z
    let f := (correctionComponent E g a n nr hn).comp ((Q.act i l n h).flip z)
    let f' := ((N.act ir l nr (by omega)).flip z).comp (correctionComponent E g b i ir hi)
    change f x = f' x
    apply LinearMap.congr_fun (attachment_linear_ext E b i _ _)
    · intro y
      change correctionComponent E g a n nr hn (Q.act i l n h ((E.inclusion.app b).f i y) z) =
        N.act ir l nr _ (correctionComponent E g b i ir hi ((E.inclusion.app b).f i y)) z
      rw [← E.inclusion.comm_act, correctionComponent_inclusion, correctionComponent_inclusion]
      simp
    · intro s y
      change correctionComponent E g a n nr hn (Q.act i l n h (cellEmbedding E s b i y) z) =
        N.act ir l nr _ (correctionComponent E g b i ir hi (cellEmbedding E s b i y)) z
      rw [← cellEmbedding_act, correctionComponent_cell, correctionComponent_cell]
      exact (g s).comm_act i l n ir nr h hi hn y z)

private theorem correction_inclusion (g : ∀ s, GradedHom (cells C s) N r) :
    restrict E.inclusion (correction E g) = 0 := by
  apply gradedHom_ext_apply
  intro a i q e x
  rw [restrict_app, graded_zero_app]
  exact correctionComponent_inclusion E g a i q e x

private theorem correction_cell (g : ∀ s, GradedHom (cells C s) N r) (s : I) :
    precomp (cellSection E s) (correction E g) = g s := by
  apply gradedHom_ext_apply
  intro a i q e x
  rw [precomp_app]
  exact correctionComponent_cell E g a i q e s x

private theorem eq_of_attachment_restrictions {f g : GradedHom Q N r}
    (h₀ : restrict E.inclusion f = restrict E.inclusion g)
    (h₁ : ∀ s, precomp (cellSection E s) f = precomp (cellSection E s) g) :
    f = g := by
  apply gradedHom_ext_apply
  intro a i q e x
  change (f.app a i q e).hom x = (g.app a i q e).hom x
  apply LinearMap.congr_fun (attachment_linear_ext E a i _ _)
  · intro y
    simpa only [restrict_app] using congrArg (fun z : GradedHom P N r => z.app a i q e y) h₀
  · intro s y
    have eq := congrArg (fun z : GradedHom (cells C s) N r => z.app a i q e y) (h₁ s)
    change (precomp (cellSection E s) f).app a i q e y =
      (precomp (cellSection E s) g).app a i q e y at eq
    rw [precomp_app, precomp_app] at eq
    exact eq

private theorem cellRestriction_d (s : I) (g : GradedHom Q N r)
    (hg : restrict E.inclusion g = 0) :
    precomp (cellSection E s) ((homComplex Q N).d r (r+1) g) =
      (homComplex (cells C s) N).d r (r+1) (precomp (cellSection E s) g) := by
  apply gradedHom_ext_apply
  intro a i q e x
  rw [precomp_app, differentialFormula, differentialFormula, precomp_app, precomp_app]
  change _ - r.negOnePow • g.app a (i+1) q _ ((Q.complex a).d i (i+1)
      (cellEmbedding E s a i x)) =
    _ - r.negOnePow • g.app a (i+1) q _ (cellEmbedding E s a (i+1)
      (((cells C s).complex a).d i (i+1) x))
  rw [cellEmbedding_d, map_add, ← restrict_app E.inclusion g, hg, graded_zero_app, zero_add]

/-- Extend a primitive over the graded attachment. After extending by zero on
the new cells, the remaining cocycle vanishes on the preceding stage, so it
restricts to a cocycle on each quotient cell. -/
private theorem extend_primitive (hN : N.Acyclic)
    (f : GradedHom Q N (r+1))
    (hf : (homComplex Q N).d (r+1) (r+1+1) f = 0)
    (g : GradedHom P N r)
    (hg : (homComplex P N).d r (r+1) g = restrict E.inclusion f) :
    ∃ h : GradedHom Q N r,
      (homComplex Q N).d r (r+1) h = f ∧ restrict E.inclusion h = g := by
  let D := homComplex Q N
  let b := precomp (attachmentRetraction E) g
  let z : GradedHom Q N (r+1) := f - D.d r (r+1) b
  have hz : D.d (r+1) (r+1+1) z = 0 := by
    dsimp only [z]
    rw [map_sub, hf, d_d_apply, sub_zero]
  have hzi : restrict E.inclusion z = 0 := by
    dsimp only [z]
    rw [restrict_sub, restrict_d, restrict_inclusion_extend E g, hg, sub_self]
  have hzc (s : I) : (homComplex (cells C s) N).d (r+1) (r+1+1)
      (precomp (cellSection E s) z) = 0 := by
    rw [← cellRestriction_d E s z hzi, hz]
    unfold precomp
    rw [map_zero, LinearMap.zero_apply]
  have hcell (s : I) : IsKProjective (cells C s) :=
    (representable_kProjective (C.object s)).shift (-C.degree s)
  choose c hc using fun s => (acyclic_iff_boundaries _).1 (hcell s N hN) r _ (hzc s)
  have hd : D.d r (r+1) (correction E c) = z := by
    apply eq_of_attachment_restrictions E
    · rw [restrict_d, correction_inclusion, map_zero, hzi]
    · intro s
      rw [cellRestriction_d E s _ (correction_inclusion E c), correction_cell, hc s]
  refine ⟨b + correction E c, ?_, ?_⟩
  · change D.d r (r+1) (b + correction E c) = f
    rw [map_add, hd]
    exact (add_comm _ _).trans (sub_add_cancel _ _)
  · rw [restrict_add, restrict_inclusion_extend E g, correction_inclusion, add_zero]

end Attachment

section Filtration

variable (F : SemiFreePresentation.{u,v,w,j} M)

private def stageInclusion (j : ℕ) : F.stage j ⟶ F.stage (j+1) :=
  (F.extension j).inclusion

@[simp] private theorem stageInclusion_into (j : ℕ) :
    stageInclusion F j ≫ F.into (j+1) = F.into j := by
  exact F.compatible j

private abbrev StagePrimitive (f : GradedHom M N (r+1)) (j : ℕ) :=
  {g : GradedHom (F.stage j) N r //
    (homComplex (F.stage j) N).d r (r+1) g = restrict (F.into j) f}

private def bottomPrimitive (f : GradedHom M N (r+1)) : StagePrimitive F f 0 := by
  refine ⟨0, ?_⟩
  rw [map_zero]
  apply gradedHom_ext_apply
  intro a i q e x
  rw [graded_zero_app, restrict_app, F.bottom a i x, map_zero, map_zero]

private theorem successorPrimitive (hN : N.Acyclic) (f : GradedHom M N (r+1))
    (hf : (homComplex M N).d (r+1) (r+1+1) f = 0) (j : ℕ)
    (g : StagePrimitive F f j) :
    ∃ h : StagePrimitive F f (j+1), restrict (stageInclusion F j) h.val = g.val := by
  let z := restrict (F.into (j+1)) f
  have hz : (homComplex (F.stage (j+1)) N).d (r+1) (r+1+1) z = 0 := by
    dsimp only [z]
    rw [← restrict_d, hf, restrict_zero]
  have hg : (homComplex (F.stage j) N).d r (r+1) g.val =
      restrict (stageInclusion F j) z := by
    dsimp only [z]
    rw [g.property, ← restrict_comp, stageInclusion_into]
  obtain ⟨h, dh, hh⟩ := extend_primitive (F.extension j) hN z hz g.val hg
  exact ⟨⟨h, dh⟩, hh⟩

private def stagePrimitives (hN : N.Acyclic) (f : GradedHom M N (r+1))
    (hf : (homComplex M N).d (r+1) (r+1+1) f = 0) :
    ∀ j : ℕ, StagePrimitive F f j :=
  Nat.rec (bottomPrimitive F f)
    (fun j g => (successorPrimitive F hN f hf j g).choose)

private theorem stagePrimitives_compatible (hN : N.Acyclic) (f : GradedHom M N (r+1))
    (hf : (homComplex M N).d (r+1) (r+1+1) f = 0) (j : ℕ) :
    restrict (stageInclusion F j) (stagePrimitives F hN f hf (j+1)).val =
      (stagePrimitives F hN f hf j).val :=
  (successorPrimitive F hN f hf j (stagePrimitives F hN f hf j)).choose_spec

variable (g : ∀ j, GradedHom (F.stage j) N r)
variable (hg : ∀ j, restrict (stageInclusion F j) (g (j+1)) = g j)

include hg in
private theorem exists_stageTransition {i j : ℕ} (h : i ≤ j) :
    ∃ t : F.stage i ⟶ F.stage j, t ≫ F.into j = F.into i ∧ restrict t (g j) = g i := by
  induction h with
  | refl => exact ⟨𝟙 _, Category.id_comp _, restrict_id _⟩
  | @step l hl ih =>
    obtain ⟨t, ht, hgt⟩ := ih
    refine ⟨t ≫ stageInclusion F l, ?_, ?_⟩
    · rw [Category.assoc, stageInclusion_into, ht]
    · rw [restrict_comp, hg, hgt]

include hg in
private theorem stage_values_eq (a : A.Obj) (i q : ℤ) (e : i+r = q)
    {m n : ℕ} {x : ((F.stage m).complex a).X i} {y : ((F.stage n).complex a).X i}
    (h : ((F.into m).app a).f i x = ((F.into n).app a).f i y) :
    (g m).app a i q e x = (g n).app a i q e y := by
  obtain ⟨s, hs, hgs⟩ := exists_stageTransition F g hg (Nat.le_max_left m n)
  obtain ⟨t, ht, hgt⟩ := exists_stageTransition F g hg (Nat.le_max_right m n)
  have he : (s.app a).f i x = (t.app a).f i y := F.injective (max m n) a i (by
    change ((s ≫ F.into (max m n)).app a).f i x = ((t ≫ F.into (max m n)).app a).f i y
    rw [hs, ht]
    exact h)
  rw [← hgs, ← hgt, restrict_app, restrict_app, he]

private def gluedValue (a : A.Obj) (i q : ℤ) (e : i+r = q)
    (x : (M.complex a).X i) : (N.complex a).X q :=
  let hx := F.exhaustive a i x
  (g hx.choose).app a i q e hx.choose_spec.choose

include hg in
private theorem gluedValue_into (a : A.Obj) (i q : ℤ) (e : i+r = q)
    (l : ℕ) (x : ((F.stage l).complex a).X i) :
    gluedValue F g a i q e (((F.into l).app a).f i x) = (g l).app a i q e x := by
  unfold gluedValue
  exact stage_values_eq F g hg a i q e (F.exhaustive a i _).choose_spec.choose_spec

private def gluedComponent (a : A.Obj) (i q : ℤ) (e : i+r = q) :
    (M.complex a).X i ⟶ (N.complex a).X q :=
  ModuleCat.ofHom
    { toFun := gluedValue F g a i q e
      map_add' := by
        intro x y
        obtain ⟨m, x₀, hx⟩ := F.exhaustive a i x
        obtain ⟨n, y₀, hy⟩ := F.exhaustive a i y
        let l := max m n
        obtain ⟨s, hs, _⟩ := exists_stageTransition F g hg (Nat.le_max_left m n)
        obtain ⟨t, ht, _⟩ := exists_stageTransition F g hg (Nat.le_max_right m n)
        let x' := (s.app a).f i x₀
        let y' := (t.app a).f i y₀
        have hx' : ((F.into l).app a).f i x' = x := by
          change ((s ≫ F.into l).app a).f i x₀ = x
          rw [hs, hx]
        have hy' : ((F.into l).app a).f i y' = y := by
          change ((t ≫ F.into l).app a).f i y₀ = y
          rw [ht, hy]
        rw [← hx', ← hy', ← map_add (((F.into l).app a).f i).hom,
          gluedValue_into F g hg, map_add, gluedValue_into F g hg, gluedValue_into F g hg]
      map_smul' := by
        intro c x
        obtain ⟨l, y, rfl⟩ := F.exhaustive a i x
        rw [← map_smul (((F.into l).app a).f i).hom, gluedValue_into F g hg,
          gluedValue_into F g hg, map_smul]
        rfl }

private def gluedMap : GradedHom M N r :=
  GradedHom.mk (gluedComponent F g hg) (by
    intro a b i j n ir nr h hi hn x z
    obtain ⟨l, y, rfl⟩ := F.exhaustive b i x
    change gluedValue F g a n nr hn (M.act i j n h (((F.into l).app b).f i y) z) =
      N.act ir j nr _ (gluedValue F g b i ir hi (((F.into l).app b).f i y)) z
    rw [← (F.into l).comm_act, gluedValue_into F g hg, gluedValue_into F g hg]
    exact (g l).comm_act i j n ir nr h hi hn y z)

private theorem restrict_gluedMap (l : ℕ) :
    restrict (F.into l) (gluedMap F g hg) = g l := by
  apply gradedHom_ext_apply
  intro a i q e x
  rw [restrict_app]
  exact gluedValue_into F g hg a i q e l x

private theorem eq_of_stage_restrictions {f f' : GradedHom M N r}
    (h : ∀ l, restrict (F.into l) f = restrict (F.into l) f') : f = f' := by
  apply gradedHom_ext_apply
  intro a i q e x
  obtain ⟨l, y, rfl⟩ := F.exhaustive a i x
  rw [← restrict_app, ← restrict_app, h l]

end Filtration

/-- A semi-free right dg module is K-projective. -/
theorem SemiFreePresentation.isKProjective (F : SemiFreePresentation.{u,v,w,j} M) :
    IsKProjective M := by
  intro N hN
  apply (acyclic_iff_boundaries _).2
  intro r f hf
  let stages := stagePrimitives F hN f hf
  let g (l : ℕ) := (stages l).val
  have hg : ∀ l, restrict (stageInclusion F l) (g (l+1)) = g l :=
    stagePrimitives_compatible F hN f hf
  refine ⟨gluedMap F g hg, eq_of_stage_restrictions F ?_⟩
  intro l
  rw [restrict_d, restrict_gluedMap]
  exact (stages l).property

/-- The canonical semi-free predicate yields K-projectivity. -/
theorem IsSemiFree.isKProjective (hM : IsSemiFree M) : IsKProjective M := by
  obtain ⟨F⟩ := hM
  exact SemiFreePresentation.isKProjective F

end
end DerivedFormalization.RightDGModule
