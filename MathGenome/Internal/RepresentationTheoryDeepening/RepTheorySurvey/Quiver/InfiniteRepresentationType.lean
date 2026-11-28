import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.InfiniteRepresentationType
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.NonpositiveDimension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.DimensionOrbits
import Mathlib.Data.Set.Finite.Range

/-! The failure of positive definiteness forces infinite representation type. -/

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators ZeroObject

namespace RepTheorySurvey.Quiver.InfiniteRepresentationType

universe u v w d

section BoundedDimension

variable {k : Type w} [Field k] {Q : Type u} [Quiver.{v} Q]

private abbrev classOf (V : Forms.FiniteRepresentation.{u, v, w, d} k Q) :
    Forms.RepresentationClass.{u, v, w, d} k Q :=
  Quotient.mk _ V

private noncomputable def zeroRepresentation : Forms.FiniteRepresentation.{u, v, w, d} k Q :=
  ⟨0, fun i => by
    change Module.Finite k ((0 : RM03.QuiverRepresentation.{u, v, w, d} k Q).obj (i : Paths Q))
    have := ModuleCat.isZero_iff_subsingleton.mp
      ((Functor.isZero_iff (0 : RM03.QuiverRepresentation.{u, v, w, d} k Q)).mp (isZero_zero _) (i : Paths Q))
    infer_instance⟩

private noncomputable def biprodVertexIso
    (V W : RM03.QuiverRepresentation.{u, v, w, d} k Q) (i : Q) :
    RM03.QuiverRepresentation.vertex (V ⊞ W) i ≅
      ModuleCat.of k (RM03.QuiverRepresentation.vertex V i ×
        RM03.QuiverRepresentation.vertex W i) :=
  ((biprod.uniqueUpToIso V W (pointwiseBinaryBicone.isBilimit V W)).symm.app
      (i : Paths Q)) ≪≫ ModuleCat.biprodIsoProd _ _

private noncomputable def sumRepresentation
    (V W : Forms.FiniteRepresentation.{u, v, w, d} k Q) :
    Forms.FiniteRepresentation.{u, v, w, d} k Q :=
  ⟨V.obj ⊞ W.obj, fun i => by
    have : Module.Finite k (RM03.QuiverRepresentation.vertex V.obj i) := V.property i
    have : Module.Finite k (RM03.QuiverRepresentation.vertex W.obj i) := W.property i
    let e := (biprodVertexIso V.obj W.obj i).symm.toLinearEquiv
    exact Module.Finite.of_surjective e.toLinearMap e.surjective⟩

private noncomputable def classSum (c₁ c₂ : Forms.RepresentationClass.{u, v, w, d} k Q) :
    Forms.RepresentationClass.{u, v, w, d} k Q :=
  Quotient.liftOn₂ c₁ c₂ (fun V W => classOf (sumRepresentation V W))
    (fun _ _ _ _ ⟨e⟩ ⟨f⟩ => Quotient.sound ⟨biprod.mapIso e f⟩)

private def forgetIndecomposable (c : Forms.IndecomposableClass.{u, v, w, d} k Q) :
    Forms.RepresentationClass.{u, v, w, d} k Q :=
  Quotient.liftOn c (fun V => classOf V.val) (fun _ _ h => Quotient.sound h)

variable [Fintype Q]

private noncomputable def totalDimension (V : Forms.FiniteRepresentation.{u, v, w, d} k Q) : ℕ :=
  ∑ i : Q, Module.finrank k (RM03.QuiverRepresentation.vertex V.obj i)

private theorem totalDimension_iso {V W : Forms.FiniteRepresentation.{u, v, w, d} k Q}
    (e : V.obj ≅ W.obj) :
    totalDimension V = totalDimension W :=
  Finset.sum_congr rfl fun i _ => (e.app (i : Paths Q)).toLinearEquiv.finrank_eq

private theorem totalDimension_sum (V W : Forms.FiniteRepresentation.{u, v, w, d} k Q) :
    totalDimension (sumRepresentation V W) = totalDimension V + totalDimension W := by
  unfold totalDimension
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Module.Finite k (RM03.QuiverRepresentation.vertex V.obj i) := V.property i
  have : Module.Finite k (RM03.QuiverRepresentation.vertex W.obj i) := W.property i
  exact (biprodVertexIso V.obj W.obj i).toLinearEquiv.finrank_eq.trans
    (Module.finrank_prod (R := k))

private theorem totalDimension_eq_zero_iff (V : Forms.FiniteRepresentation.{u, v, w, d} k Q) :
    totalDimension V = 0 ↔ IsZero V.obj := by
  rw [Functor.isZero_iff]
  unfold totalDimension
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_univ, true_implies]
  exact forall_congr' fun i => by
    have : Module.Finite k (RM03.QuiverRepresentation.vertex V.obj i) := V.property i
    exact Module.finrank_zero_iff.trans ModuleCat.isZero_iff_subsingleton.symm

private noncomputable def classDimension (c : Forms.RepresentationClass.{u, v, w, d} k Q) : ℕ :=
  Quotient.liftOn c totalDimension (fun _ _ ⟨e⟩ => totalDimension_iso e)

/-- A uniform bound on total dimension bounds the classes when the indecomposable classes
are finite. In a nontrivial binary decomposition both summands have smaller dimension. -/
private theorem finite_boundedDimension [Finite (Forms.IndecomposableClass.{u, v, w, d} k Q)] (n : ℕ) :
    {c : Forms.RepresentationClass.{u, v, w, d} k Q | classDimension c ≤ n}.Finite := by
  classical
  let zeroClass := classOf (zeroRepresentation.{u, v, w, d} (k := k) (Q := Q))
  have zeroClass_eq (V : Forms.FiniteRepresentation.{u, v, w, d} k Q)
      (h : IsZero V.obj) : classOf V = zeroClass :=
    Quotient.sound ⟨h.isoZero⟩
  induction n with
  | zero =>
    refine (Set.finite_singleton zeroClass).subset ?_
    intro c
    refine Quotient.inductionOn c fun V h => ?_
    have hV : totalDimension V = 0 := Nat.eq_zero_of_le_zero h
    exact Set.mem_singleton_iff.mpr (zeroClass_eq V ((totalDimension_eq_zero_iff V).mp hV))
  | succ n ih =>
    let S : Set (Forms.RepresentationClass.{u, v, w, d} k Q) := {c | classDimension c ≤ n}
    let _ : Finite S := ih
    let sums (p : S × S) : Forms.RepresentationClass.{u, v, w, d} k Q := classSum p.1.val p.2.val
    refine ((Set.finite_singleton zeroClass).union
      ((Set.finite_range (forgetIndecomposable (k := k) (Q := Q))).union
        (Set.finite_range sums))).subset ?_
    intro c
    refine Quotient.inductionOn c fun V h => ?_
    by_cases hzero : IsZero V.obj
    · exact Or.inl (Set.mem_singleton_iff.mpr (zeroClass_eq V hzero))
    by_cases hindecomp : Indecomposable V.obj
    · exact Or.inr (Or.inl ⟨Quotient.mk _ ⟨V, hindecomp⟩, rfl⟩)
    have hsplit : ¬ ∀ Y Z : RM03.QuiverRepresentation.{u, v, w, d} k Q,
        (V.obj ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z :=
      fun h' => hindecomp ⟨hzero, h'⟩
    push Not at hsplit
    obtain ⟨Y, Z, e, hY, hZ⟩ := hsplit
    let Y' : Forms.FiniteRepresentation.{u, v, w, d} k Q :=
      ⟨Y, Forms.finite_of_retract (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp) V.property⟩
    let Z' : Forms.FiniteRepresentation.{u, v, w, d} k Q :=
      ⟨Z, Forms.finite_of_retract (biprod.inr ≫ e.inv) (e.hom ≫ biprod.snd) (by simp) V.property⟩
    have hsum : totalDimension V = totalDimension Y' + totalDimension Z' :=
      (totalDimension_iso (W := sumRepresentation Y' Z') e).trans (totalDimension_sum Y' Z')
    have hy : 0 < totalDimension Y' := Nat.pos_of_ne_zero
      fun hz => hY ((totalDimension_eq_zero_iff Y').mp hz)
    have hz : 0 < totalDimension Z' := Nat.pos_of_ne_zero
      fun hz => hZ ((totalDimension_eq_zero_iff Z').mp hz)
    change totalDimension V ≤ n + 1 at h
    have hy' : classOf Y' ∈ S := by
      change totalDimension Y' ≤ n
      omega
    have hz' : classOf Z' ∈ S := by
      change totalDimension Z' ≤ n
      omega
    have eq : classOf (sumRepresentation Y' Z') = classOf V := Quotient.sound ⟨e.symm⟩
    exact Or.inr (Or.inr ⟨(⟨classOf Y', hy'⟩, ⟨classOf Z', hz'⟩), eq⟩)

private theorem finite_fixedDimension [Finite (Forms.IndecomposableClass.{u, v, w, d} k Q)]
    (x : Forms.DimensionVector Q) :
    Finite (DimensionOrbitsSpec.FixedDimensionClass.{u, v, w, d} k x) := by
  have h (c : DimensionOrbitsSpec.FixedDimensionClass.{u, v, w, d} k x) :
      classDimension c.val ≤ ∑ i : Q, (x i).toNat := by
    rcases c with ⟨c, V, rfl, hV⟩
    change totalDimension V ≤ _
    unfold totalDimension
    apply le_of_eq
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hV]
    exact (Int.toNat_natCast _).symm
  let S : Set (Forms.RepresentationClass.{u, v, w, d} k Q) :=
    {c | classDimension c ≤ ∑ i : Q, (x i).toNat}
  let _ : Finite S := finite_boundedDimension _
  exact Finite.of_injective (fun c => (⟨c.val, h c⟩ : S))
    (fun _ _ eq => Subtype.ext (congrArg (fun y : S => y.val) eq))

end BoundedDimension

/-- The dimension obstruction to finite representation type over an infinite field. -/
theorem infinite_indecomposableClasses :
    InfiniteRepresentationTypeSpec.InfiniteIndecomposableClasses.{u, v, w, d} := by
  intro k Q _ _ _ _ _ hacyclic hnotpos
  obtain ⟨x, hx, hxnonneg, hq⟩ := NonpositiveDimension.exists_nonpositive_dimension hacyclic hnotpos
  have : Infinite (DimensionOrbitsSpec.FixedDimensionClass.{u, v, w, max w d} k x) :=
    DimensionOrbits.infinite_fixedDimensionClasses k hacyclic x hx hxnonneg hq
  apply not_finite_iff_infinite.mp
  intro hfinite
  let _ := hfinite
  let _ := finite_fixedDimension.{u, v, w, max w d} (k := k) x
  exact not_finite (DimensionOrbitsSpec.FixedDimensionClass.{u, v, w, max w d} k x)

end RepTheorySurvey.Quiver.InfiniteRepresentationType
