import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.NormalizedCohomology

namespace ALG02GroupTheory.Extensions.NormalizedCohomology

universe u v

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-- Two cocycles represent the same class exactly when their difference is a coboundary. -/
theorem classOf_eq_iff (c d : TwoCocycle Q A) :
    classOf Q A c = classOf Q A d ↔
      ∃ a : Q → A, ∀ q r : Q, c.val (q, r) - d.val (q, r) = differential a (q, r) := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
  change c - d ∈ (coboundary Q A).range ↔ _
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun q r => congrArg (fun z : TwoCocycle Q A => z.val (q, r)) ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext (funext (fun (q, r) => (ha q r).symm))⟩

/-- Every second cohomology class has a normalized two-cocycle representative. -/
theorem exists_normalized_representative (x : H2 Q A) :
    ∃ c : TwoCocycle Q A, IsNormalized c.val ∧ classOf Q A c = x := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (twoCoboundaries Q A) x
  let a : Q → A := fun _ => c.val (1, 1)
  refine ⟨c - coboundary Q A a, ?_, ?_⟩
  · intro q
    have hc : IsTwoCocycle c.val := c.property
    have hleft : c.val (1, q) = c.val (1, 1) := by
      simpa only [one_mul, one_smul, add_left_inj] using (hc 1 1 q).symm
    have hright : c.val (q, 1) = q • c.val (1, 1) := by
      simpa only [mul_one, add_left_inj] using hc q 1 1
    change c.val (1, q) - differential a (1, q) = 0 ∧
      c.val (q, 1) - differential a (q, 1) = 0
    simp [differential, a, hleft, hright]
  · symm
    apply (classOf_eq_iff c _).2
    refine ⟨a, fun q r => ?_⟩
    change c.val (q, r) - (c.val (q, r) - differential a (q, r)) = differential a (q, r)
    abel

/-- For normalized cocycles the cochain witnessing equality of classes vanishes at the identity. -/
theorem normalized_class_eq_iff (c d : TwoCocycle Q A)
    (hc : IsNormalized c.val) (hd : IsNormalized d.val) :
    classOf Q A c = classOf Q A d ↔
      ∃ a : Q → A, a 1 = 0 ∧ ∀ q r : Q, c.val (q, r) - d.val (q, r) = differential a (q, r) := by
  rw [classOf_eq_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_, ha⟩
    simpa [differential, (hc 1).1, (hd 1).1] using (ha 1 1).symm
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩

end ALG02GroupTheory.Extensions.NormalizedCohomology
