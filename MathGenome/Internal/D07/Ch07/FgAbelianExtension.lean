import MathGenome.Internal.Specs.D07.Ch07.FgAbelianExtension
import MathGenome.Internal.D07.Ch16.StructureExistence
import MathGenome.Internal.D07.Ch07.InvariantFactorExistence
import MathGenome.Internal.D07.Ch07.InvariantFactorUniqueness
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
namespace D07.Ch07.FgAbelianExtension

universe u
open D07.Ch07.ClassificationDataConversion
open Specs.D07.Ch07.FgAbelianExtension

/-- Normalized cyclic factors are nonzero moduli, so their product is finite. -/
theorem invariantGroup_finite (d : List ℕ) (hd : IsInvariant d) :
    Finite (InvariantGroup d) := by
  have : ∀ i : Fin d.length, NeZero (d.getD i 1) := by
    intro i
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact ⟨by have := hd.1 _ (List.getElem_mem i.isLt); omega⟩
  infer_instance

theorem existence : Existence.{u} := by
  intro A _ hA
  let : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr hA
  obtain ⟨r, s, a, ha, _, ⟨E⟩⟩ := D07.Ch16.StructureExistence.invariantFactors ℤ A
  let T := (i : Fin s) → ℤ ⧸ Ideal.span {a i}
  have : ∀ i : Fin s, NeZero (a i).natAbs :=
    fun i => ⟨Int.natAbs_ne_zero.mpr (ha i).1⟩
  have : ∀ i : Fin s, Finite (ℤ ⧸ Ideal.span {a i}) :=
    fun i => Finite.of_equiv _ (Int.quotientSpanEquivZMod (a i)).symm.toEquiv
  have : Finite T := inferInstance
  obtain ⟨d, hd, ⟨F⟩⟩ := D07.Ch07.InvariantFactorExistence.invariant_factor_existence T
  exact ⟨r, d, hd, ⟨E.toAddEquiv.trans ((AddEquiv.refl _).prodCongr F)⟩⟩

/-- Torsion in a free-by-finite product is exactly the zero free fiber. -/
theorem mem_torsion_iff {A : Type u} [AddCommGroup A] (r : ℕ) (d : List ℕ)
    (hd : IsInvariant d) (E : A ≃+ Model r d) (a : A) :
    a ∈ AddCommGroup.torsion A ↔ (E a).1 = 0 := by
  have := invariantGroup_finite d hd
  have he : a ∈ AddCommGroup.torsion A ↔ E a ∈ AddCommGroup.torsion (Model r d) := by
    change a ∈ AddCommGroup.torsion A ↔ a ∈ (AddCommGroup.torsion (Model r d)).comap E
    rw [E.comap_torsion]
  rw [he]
  change IsOfFinAddOrder (E a) ↔ _
  rw [IsOfFinAddOrder.prod_iff, isOfFinAddOrder_iff_eq_zero]
  exact and_iff_left (isOfFinAddOrder_of_finite _)

theorem torsion_description : TorsionDescription.{u} := by
  intro A _ r d hd E
  refine ⟨mem_torsion_iff r d hd E, ?_⟩
  let f : AddCommGroup.torsion A →+ InvariantGroup d :=
    (AddMonoidHom.snd _ _).comp (E.toAddMonoidHom.comp (AddCommGroup.torsion A).subtype)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply E.injective
      apply Prod.ext
      · exact ((mem_torsion_iff r d hd E a.val).mp a.property).trans
          ((mem_torsion_iff r d hd E b.val).mp b.property).symm
      · exact hab
    · intro t
      refine ⟨⟨E.symm (0, t), (mem_torsion_iff r d hd E _).mpr ?_⟩, ?_⟩
      · simp
      · change (E (E.symm (0, t))).2 = t
        simp
  exact ⟨AddEquiv.ofBijective f hf, fun _ => rfl⟩

theorem quotient_description : QuotientDescription.{u} := by
  intro A _ r d hd E
  let f : A →+ (Fin r → ℤ) := (AddMonoidHom.fst _ _).comp E.toAddMonoidHom
  have hker : f.ker = AddCommGroup.torsion A := by
    ext a
    exact (mem_torsion_iff r d hd E a).symm
  have hsurj : Function.Surjective f := by
    intro x
    exact ⟨E.symm (x, 0), by change (E (E.symm (x, 0))).1 = x; simp⟩
  refine ⟨(QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj), ?_⟩
  intro a
  rfl

/-- An isomorphism restricts to the intrinsic torsion subgroups. -/
def torsionEquiv {A : Type u} {B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) : AddCommGroup.torsion A ≃+ AddCommGroup.torsion B :=
  (E.addSubgroupMap (AddCommGroup.torsion A)).trans
    (AddEquiv.addSubgroupCongr E.map_torsion)

theorem uniqueness : Uniqueness := by
  intro r r' d e hd he E
  obtain ⟨Fd, _⟩ := (torsion_description (Model r d) r d hd (.refl _)).2
  obtain ⟨Fe, _⟩ := (torsion_description (Model r' e) r' e he (.refl _)).2
  have hde : d = e := D07.Ch07.InvariantFactorUniqueness.invariant_factor_uniqueness
    d e hd he (Fd.symm.trans ((torsionEquiv E).trans Fe))
  obtain ⟨Qd, _⟩ := quotient_description (Model r d) r d hd (.refl _)
  obtain ⟨Qe, _⟩ := quotient_description (Model r' e) r' e he (.refl _)
  let Q := QuotientAddGroup.congr (AddCommGroup.torsion (Model r d))
    (AddCommGroup.torsion (Model r' e)) E E.map_torsion
  have hr := (Qd.symm.trans (Q.trans Qe)).toIntLinearEquiv.finrank_eq
  simp only [Module.finrank_pi, Fintype.card_fin] at hr
  exact ⟨hr, hde⟩

theorem finiteness_criterion : FinitenessCriterion.{u} := by
  intro A _ r d hd E
  constructor
  · intro hA
    let := hA
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hf : Function.Surjective (fun a : A => (E a).1 i) := by
      intro z
      exact ⟨E.symm ((fun _ => z), 0), by simp⟩
    have : Finite ℤ := Finite.of_surjective _ hf
    exact not_finite ℤ
  · rintro rfl
    have := invariantGroup_finite d hd
    exact Finite.of_equiv _ E.symm.toEquiv

/-- The rational numbers with denominator dividing a fixed natural number. -/
private def denominatorSubgroup (d : ℕ) : AddSubgroup ℚ where
  carrier := {q | ∃ m : ℤ, q = (m : ℚ) / (d : ℚ)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by push_cast; rw [add_div]⟩
  neg_mem' := by
    rintro x ⟨m, rfl⟩
    exact ⟨-m, by rw [Int.cast_neg, neg_div]⟩

/-- Products of the individual positive denominators clear a finite list. -/
private theorem list_denominator (l : List ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∀ q ∈ l, ∃ m : ℤ, q = (m : ℚ) / (d : ℚ) := by
  induction l with
  | nil => exact ⟨1, by omega, by simp⟩
  | cons q l ih =>
    obtain ⟨d, hd, hl⟩ := ih
    have hD : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    refine ⟨q.den * d, Nat.mul_pos q.den_pos hd, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with h | hx
    · subst x
      refine ⟨q.num * (d : ℤ), ?_⟩
      calc
        q = (q.num : ℚ) / (q.den : ℚ) := q.num_div_den.symm
        _ = _ := by push_cast; field_simp
    · obtain ⟨m, rfl⟩ := hl x hx
      refine ⟨m * (q.den : ℤ), ?_⟩
      push_cast
      field_simp

theorem rational_common_denominator : RationalCommonDenominator := by
  intro l
  obtain ⟨d, hd, hl⟩ := list_denominator l
  refine ⟨d, hd, ?_⟩
  have h : AddSubgroup.closure (l.toFinset : Set ℚ) ≤ denominatorSubgroup d := by
    apply (AddSubgroup.closure_le _).mpr
    intro q hq
    exact hl q (List.mem_toFinset.mp hq)
  exact fun q hq => h hq

theorem rational_denominator_obstruction : RationalDenominatorObstruction := by
  intro d hd ⟨m, hm⟩
  have hD : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h : (1 : ℚ) = 2 * (m : ℚ) := by
    field_simp at hm
    nlinarith
  have hz : (1 : ℤ) = 2 * m := by exact_mod_cast h
  omega

theorem rational_not_finitely_generated : RationalNotFinitelyGenerated := by
  intro hfg
  obtain ⟨_, S, _, hS⟩ := AddGroup.fg_iff'.mp hfg
  obtain ⟨d, hd, h⟩ := rational_common_denominator S.toList
  apply rational_denominator_obstruction d hd
  apply h
  rw [Finset.toList_toFinset, hS]
  trivial

end D07.Ch07.FgAbelianExtension
