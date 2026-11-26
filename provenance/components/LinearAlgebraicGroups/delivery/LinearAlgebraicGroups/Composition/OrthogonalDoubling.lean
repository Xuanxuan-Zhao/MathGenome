import Specs.LinearAlgebraicGroups.Composition.OrthogonalDoubling
import LinearAlgebraicGroups.Composition.Adjoints

namespace LinearAlgebraicGroups.Composition

universe u v

variable {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
  [IsScalarTower k C C] [SMulCommClass k C C]
variable {n : QuadraticForm k C} {D : UnitalSubalgebra k C} {a : C}

namespace UnitalSubalgebra

omit [IsScalarTower k C C] [SMulCommClass k C C] in
@[simp]
theorem restrictNorm_apply (D : UnitalSubalgebra k C) (n : QuadraticForm k C) (x : D) :
    D.restrictNorm n x = n (x : C) :=
  rfl

omit [IsScalarTower k C C] [SMulCommClass k C C] in
@[simp]
theorem polarBilin_restrictNorm (D : UnitalSubalgebra k C) (n : QuadraticForm k C) (x y : D) :
    (D.restrictNorm n).polarBilin x y = n.polarBilin (x : C) (y : C) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, restrictNorm_apply]
  rfl

omit [IsScalarTower k C C] [SMulCommClass k C C] in
@[simp]
theorem coe_conjugate_restrictNorm (D : UnitalSubalgebra k C) (n : QuadraticForm k C) (x : D) :
    (conjugate (D.restrictNorm n) x : C) = conjugate n (x : C) := by
  simp only [conjugate_apply, compositionTrace_apply, polarBilin_restrictNorm]
  rfl

theorem mem_rightMultiple {z : C} :
    z ∈ D.rightMultiple a ↔ ∃ y : D, (y : C) * a = z := by
  change (∃ y ∈ D.toSubmodule, y * a = z) ↔ ∃ y : D, (y : C) * a = z
  exact ⟨fun ⟨y, hy, he⟩ => ⟨⟨y, hy⟩, he⟩, fun ⟨y, he⟩ => ⟨y, y.property, he⟩⟩

end UnitalSubalgebra

private theorem mem_doubling_sum {z : C} :
    z ∈ D.toSubmodule ⊔ D.rightMultiple a ↔ ∃ x y : D, (x : C) + (y : C) * a = z := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨y, rfl⟩ := UnitalSubalgebra.mem_rightMultiple.mp hw
    exact ⟨⟨x, hx⟩, y, rfl⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, x.property, (y : C) * a, UnitalSubalgebra.mem_rightMultiple.mpr ⟨y, rfl⟩, rfl⟩

omit [IsScalarTower k C C] [SMulCommClass k C C] in
private theorem full_polar_symm (n : QuadraticForm k C) (x y : C) :
    n.polarBilin x y = n.polarBilin y x := by
  simpa only [QuadraticMap.polarBilin_apply_apply] using QuadraticMap.polar_comm n x y

private theorem right_product_polarization (h : NormLaws n) (x y z : C) :
    (x * y) * conjugate n z + (x * z) * conjugate n y = n.polarBilin y z • x := by
  have hsum := (conjugate_right_products h (y + z) x).1
  rw [mul_add, map_add, add_mul, mul_add, mul_add, QuadraticMap.map_add n,
    add_smul, add_smul, (conjugate_right_products h y x).1,
    (conjugate_right_products h z x).1] at hsum
  calc
    _ = (n y • x + (x * y) * conjugate n z + ((x * z) * conjugate n y + n z • x)) -
          (n y • x + n z • x) := by abel
    _ = _ := by rw [hsum]; abel

omit [IsScalarTower k C C] [SMulCommClass k C C] in
private theorem trace_zero_of_orthogonal
    (hz : a ∈ D.toSubmodule.orthogonalBilin n.polarBilin) :
    compositionTrace n a = 0 := by
  rw [compositionTrace_apply, full_polar_symm n a 1]
  exact hz 1 D.one_mem'

omit [IsScalarTower k C C] [SMulCommClass k C C] in
private theorem conjugate_eq_neg_of_orthogonal
    (hz : a ∈ D.toSubmodule.orthogonalBilin n.polarBilin) :
    conjugate n a = -a := by
  rw [conjugate_apply, trace_zero_of_orthogonal hz, zero_smul, zero_sub]

private theorem mul_orthogonal_eq_mul_conjugate (h : NormLaws n) (x : D)
    (hz : a ∈ D.toSubmodule.orthogonalBilin n.polarBilin) :
    (x : C) * a = a * conjugate n (x : C) := by
  have he := polar_mul_conjugate h (x : C) a
  rw [conjugate_eq_neg_of_orthogonal hz, mul_neg, hz (x : C) x.property, zero_smul,
    add_comm, ← sub_eq_add_neg] at he
  exact (sub_eq_zero.mp he).symm

/-- An internal Cayley–Dickson double, with the ambient multiplication and norm. -/
theorem orthogonal_doubling : DoublingSpecification.internalDoubling := by
  intro k C _ _ _ _ _ n D a hn hD ha ha0
  dsimp only
  have : Module.Finite k C := hn.finite
  have : Nontrivial C := hn.nontrivial
  have h := IsFieldCompositionNorm.toNormLaws hn
  have hbar := conjugate_eq_neg_of_orthogonal ha
  have hsquare (w : C) : (w * a) * a = (-n a) • w := by
    have he := (conjugate_right_products h a w).1
    rw [hbar, mul_neg] at he
    rw [neg_smul, ← he, neg_neg]
  have horth : D.rightMultiple a ≤ D.toSubmodule.orthogonalBilin n.polarBilin := by
    intro z hz
    obtain ⟨y, rfl⟩ := UnitalSubalgebra.mem_rightMultiple.mp hz
    intro d hd
    have he : n.polarBilin ((y : C) * a) d = n.polarBilin a (conjugate n (y : C) * d) :=
      left_mul_adjoint h (y : C) a d
    rw [full_polar_symm n d, he, full_polar_symm n a]
    have hy : conjugate n (y : C) ∈ D.toSubmodule := by
      rw [← UnitalSubalgebra.coe_conjugate_restrictNorm]
      exact (conjugate (D.restrictNorm n) y).property
    exact ha _ (D.mul_mem' hy hd)
  have hmul (y : D) : (y : C) * a ∈ D.rightMultiple a :=
    UnitalSubalgebra.mem_rightMultiple.mpr ⟨y, rfl⟩
  have hdisjoint : Disjoint D.toSubmodule (D.rightMultiple a) := by
    rw [Submodule.disjoint_def]
    intro z hz hz'
    have he : (⟨z, hz⟩ : D) = 0 := by
      apply hD.nondegenerate.2
      intro d
      rw [UnitalSubalgebra.polarBilin_restrictNorm]
      exact horth hz' (d : C) d.property
    exact congrArg Subtype.val he
  have hinj : Function.Injective (fun y : D => (y : C) * a) := by
    intro x y he
    apply Subtype.ext
    apply smul_right_injective C ha0
    change (x : C) * a = (y : C) * a at he
    change n a • (x : C) = n a • (y : C)
    rw [← (conjugate_right_products h a (x : C)).1,
      ← (conjugate_right_products h a (y : C)).1, he]
  have hright (y u : D) :
      ((y : C) * a) * (u : C) = ((y : C) * conjugate n (u : C)) * a := by
    have he := right_product_polarization h (y : C) a (conjugate n (u : C))
    have hb : n.polarBilin a (conjugate n (u : C)) = 0 := by
      rw [full_polar_symm n a, ← UnitalSubalgebra.coe_conjugate_restrictNorm]
      exact ha _ (conjugate (D.restrictNorm n) u).property
    rw [conjugate_involutive h (u : C), hbar, hb, zero_smul, mul_neg, ← sub_eq_add_neg] at he
    exact sub_eq_zero.mp he
  have hleft (x v : D) : (x : C) * ((v : C) * a) = ((v : C) * (x : C)) * a := by
    rw [mul_orthogonal_eq_mul_conjugate h x (horth (hmul v)),
      ← UnitalSubalgebra.coe_conjugate_restrictNorm D n x,
      hright v (conjugate (D.restrictNorm n) x), UnitalSubalgebra.coe_conjugate_restrictNorm,
      conjugate_involutive h]
  have hboth (y v : D) :
      ((y : C) * a) * ((v : C) * a) = (-n a) • (conjugate n (v : C) * (y : C)) := by
    calc
      _ = (a * conjugate n (y : C)) * ((v : C) * a) := by
        rw [← mul_orthogonal_eq_mul_conjugate h y ha]
      _ = (a * (conjugate n (y : C) * (v : C))) * a :=
        (composition_isAlternative h).moufang_middle a (v : C) (conjugate n (y : C))
      _ = ((conjugate n (v : C) * (y : C)) * a) * a := by
        let w : D := conjugate (D.restrictNorm n) y * v
        have hw := mul_orthogonal_eq_mul_conjugate h (conjugate (D.restrictNorm n) w) ha
        rw [UnitalSubalgebra.coe_conjugate_restrictNorm, conjugate_involutive h] at hw
        change conjugate n ((conjugate (D.restrictNorm n) y : C) * (v : C)) * a =
          a * ((conjugate (D.restrictNorm n) y : C) * (v : C)) at hw
        rw [UnitalSubalgebra.coe_conjugate_restrictNorm, conjugate_mul h,
          conjugate_involutive h] at hw
        rw [← hw]
      _ = _ := hsquare _
  have hprod (x y u v : D) :
      ((x : C) + (y : C) * a) * ((u : C) + (v : C) * a) =
        ((x : C) * (u : C) + (-n a) • (conjugate n (v : C) * (y : C))) +
          ((v : C) * (x : C) + (y : C) * conjugate n (u : C)) * a := by
    rw [add_mul, mul_add, mul_add, hleft, hright, hboth, add_mul]
    abel
  let E : UnitalSubalgebra k C :=
    { toSubmodule := D.toSubmodule ⊔ D.rightMultiple a
      one_mem' := Submodule.mem_sup_left D.one_mem'
      mul_mem' := by
        rintro z w hz hw
        obtain ⟨x, y, rfl⟩ := mem_doubling_sum.mp hz
        obtain ⟨u, v, rfl⟩ := mem_doubling_sum.mp hw
        refine mem_doubling_sum.mpr
          ⟨x * u + (-n a) • (conjugate (D.restrictNorm n) v * y),
            v * x + y * conjugate (D.restrictNorm n) u, ?_⟩
        exact (hprod x y u v).symm }
  have hregular : (E.restrictNorm n).polarBilin.SeparatingLeft := by
    intro z hz
    obtain ⟨x, y, hzxy⟩ := mem_doubling_sum.mp z.property
    have hx : x = 0 := by
      apply hD.nondegenerate.1
      intro d
      have hd := hz ⟨(d : C), Submodule.mem_sup_left d.property⟩
      rw [UnitalSubalgebra.polarBilin_restrictNorm] at hd ⊢
      change n.polarBilin (z : C) (d : C) = 0 at hd
      rw [← hzxy, LinearMap.map_add₂, full_polar_symm n ((y : C) * a) (d : C),
        horth (hmul y) (d : C) d.property, add_zero] at hd
      exact hd
    have hy : y = 0 := by
      apply hD.nondegenerate.1
      intro d
      have hd := hz ⟨(d : C) * a, Submodule.mem_sup_right (hmul d)⟩
      rw [UnitalSubalgebra.polarBilin_restrictNorm] at hd ⊢
      change n.polarBilin (z : C) ((d : C) * a) = 0 at hd
      rw [← hzxy, hx, show ((0 : D) : C) = 0 from rfl, zero_add,
        right_norm_similarity h.map_mul a (y : C) (d : C)] at hd
      exact (mul_eq_zero.mp hd).resolve_left ha0
    apply Subtype.ext
    rw [← hzxy, hx, hy]
    change (0 : C) + 0 * a = 0
    rw [zero_mul, add_zero]
  have hE : IsFieldCompositionNorm (E.restrictNorm n) := by
    refine ⟨Module.Finite.of_injective (SMulMemClass.subtype E) Subtype.val_injective,
      ?_, ⟨hregular, ?_⟩, fun x y => h.map_mul (x : C) (y : C)⟩
    · exact ⟨⟨0, 1, fun he => zero_ne_one (congrArg Subtype.val he)⟩⟩
    · intro z hz
      apply hregular z
      intro w
      rw [UnitalSubalgebra.polarBilin_restrictNorm, full_polar_symm]
      exact hz w
  refine ⟨?_, horth, hdisjoint, hinj, ⟨E, rfl, hE⟩, hprod, ?_, ?_⟩
  · simpa only [one_mul] using hsquare 1
  · intro x y
    rw [QuadraticMap.map_add n, ← QuadraticMap.polarBilin_apply_apply, horth (hmul y) (x : C) x.property, add_zero,
      h.map_mul, neg_mul, sub_neg_eq_add, mul_comm (n a)]
  · intro x y
    rw [map_add, conjugate_eq_neg_of_orthogonal (horth (hmul y)), sub_eq_add_neg]

end LinearAlgebraicGroups.Composition
