import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.SnakeLemma
import MathGenome.Internal.AlgebraCore.P103.Ch01.ModuleExactness

namespace P103.Ch01.SnakeLemma
open P103.Specs.Ch01.SnakeLemma

universe u v w
variable {R : Type u} [Ring R] (D : Diagram.{u,v} R)

lemma left_apply (x : D.A) : D.b (D.i x) = D.i' (D.a x) :=
  DFunLike.congr_fun D.left x

lemma right_apply (y : D.B) : D.c (D.p y) = D.p' (D.b y) :=
  DFunLike.congr_fun D.right y

/-- Both lifts needed to evaluate the connecting map exist. -/
lemma lifts (z : LinearMap.ker D.c) :
    ∃ (y : D.B) (x' : D.A'), D.p y = z.val ∧ D.i' x' = D.b y := by
  obtain ⟨y, hy⟩ := D.onto z.val
  have hz : D.p' (D.b y) = 0 := by
    rw [← right_apply D y, hy]
    exact z.property
  obtain ⟨x', hx⟩ := (D.bottom (D.b y)).mp hz
  exact ⟨y, x', hy, hx⟩

/-- Two lift pairs give the same class, by exactness of the top row. -/
lemma lift_classes_eq (z : LinearMap.ker D.c) (y₁ y₂ : D.B) (x₁ x₂ : D.A')
    (hy₁ : D.p y₁ = z.val) (hy₂ : D.p y₂ = z.val)
    (hx₁ : D.i' x₁ = D.b y₁) (hx₂ : D.i' x₂ = D.b y₂) :
    (LinearMap.range D.a).mkQ x₁ = (LinearMap.range D.a).mkQ x₂ := by
  have hp : D.p (y₁ - y₂) = 0 := by rw [map_sub, hy₁, hy₂, sub_self]
  obtain ⟨x, hx⟩ := (D.top (y₁ - y₂)).mp hp
  have ha : x₁ - x₂ = D.a x := by
    apply D.mono
    rw [map_sub, hx₁, hx₂, ← map_sub, ← hx]
    exact DFunLike.congr_fun D.left x
  apply (Submodule.Quotient.eq (LinearMap.range D.a)).mpr
  exact ⟨x, ha.symm⟩

/-- The representative formula determines a linear map. -/
lemma exists_connecting :
    ∃ δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a), D.Connecting δ := by
  classical
  choose y x hy hx using lifts D
  let f : LinearMap.ker D.c → (D.A' ⧸ LinearMap.range D.a) :=
    fun z => (LinearMap.range D.a).mkQ (x z)
  have hf : ∀ z y' x', D.p y' = z.val → D.i' x' = D.b y' →
      f z = (LinearMap.range D.a).mkQ x' := by
    intro z y' x' hy' hx'
    exact lift_classes_eq D z (y z) y' (x z) x' (hy z) hy' (hx z) hx'
  let δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a) :=
    { toFun := f
      map_add' := by
        intro z t
        rw [hf (z + t) (y z + y t) (x z + x t)]
        · exact map_add _ _ _
        · change D.p (y z + y t) = z.val + t.val
          simp only [map_add, hy]
        · simp only [map_add, hx]
      map_smul' := by
        intro r z
        rw [hf (r • z) (r • y z) (r • x z)]
        · exact map_smul _ _ _
        · change D.p (r • y z) = r • z.val
          simp only [map_smul, hy]
        · simp only [map_smul, hx] }
  exact ⟨δ, hf⟩

/-- Exactness at the middle kernel uses injectivity of the lower left arrow. -/
lemma exact_kernel_middle : Function.Exact D.kerFirst D.kerSecond := by
  intro y
  constructor
  · intro hy
    have hp : D.p y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (D.top y.val).mp hp
    have ha : D.a x = 0 := by
      apply D.mono
      have h := DFunLike.congr_fun D.left x
      change D.b (D.i x) = D.i' (D.a x) at h
      rw [hx, show D.b y.val = 0 from y.property] at h
      simpa using h.symm
    exact ⟨⟨x, ha⟩, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact D.top.apply_apply_eq_zero x.val

lemma exact_kernel_connecting
    (δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a))
    (hδ : D.Connecting δ) : Function.Exact D.kerSecond δ := by
  intro z
  constructor
  · intro hz
    obtain ⟨y, x', hy, hx'⟩ := lifts D z
    have hq : (LinearMap.range D.a).mkQ x' = 0 := (hδ z y x' hy hx').symm.trans hz
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range D.a)).mp hq
    have hb : D.b (y - D.i x) = 0 := by
      rw [map_sub, left_apply D x, hx, hx', sub_self]
    refine ⟨⟨y - D.i x, hb⟩, Subtype.ext ?_⟩
    change D.p (y - D.i x) = z.val
    rw [map_sub, D.top.apply_apply_eq_zero, sub_zero, hy]
  · rintro ⟨y, rfl⟩
    have h := hδ (D.kerSecond y) y.val 0 rfl (by
      simpa only [map_zero] using (show D.b y.val = 0 from y.property).symm)
    simpa using h

@[simp] lemma cokerFirst_mk (x' : D.A') :
    D.cokerFirst ((LinearMap.range D.a).mkQ x') =
      (LinearMap.range D.b).mkQ (D.i' x') := rfl

@[simp] lemma cokerSecond_mk (y' : D.B') :
    D.cokerSecond ((LinearMap.range D.b).mkQ y') =
      (LinearMap.range D.c).mkQ (D.p' y') := rfl

lemma exact_connecting_cokernel
    (δ : LinearMap.ker D.c →ₗ[R] (D.A' ⧸ LinearMap.range D.a))
    (hδ : D.Connecting δ) : Function.Exact δ D.cokerFirst := by
  intro q
  obtain ⟨x', rfl⟩ := (LinearMap.range D.a).mkQ_surjective q
  constructor
  · intro hq
    rw [cokerFirst_mk] at hq
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range D.b)).mp hq
    have hz : D.c (D.p y) = 0 := by
      rw [right_apply, hy, D.bottom.apply_apply_eq_zero]
    exact ⟨⟨D.p y, hz⟩, hδ ⟨D.p y, hz⟩ y x' rfl hy.symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, x, hy, hx⟩ := lifts D z
    rw [← hz, hδ z y x hy hx, cokerFirst_mk, hx]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range D.b)).mpr ⟨y, rfl⟩

lemma exact_cokernel_middle : Function.Exact D.cokerFirst D.cokerSecond := by
  intro q
  obtain ⟨y', rfl⟩ := (LinearMap.range D.b).mkQ_surjective q
  constructor
  · intro hq
    rw [cokerSecond_mk] at hq
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range D.c)).mp hq
    obtain ⟨y, hy⟩ := D.onto z
    have hp : D.p' (y' - D.b y) = 0 := by
      rw [map_sub, ← right_apply, hy, hz, sub_self]
    obtain ⟨x', hx⟩ := (D.bottom (y' - D.b y)).mp hp
    refine ⟨(LinearMap.range D.a).mkQ x', ?_⟩
    rw [cokerFirst_mk, hx, map_sub]
    have hb : (LinearMap.range D.b).mkQ (D.b y) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range D.b)).mpr ⟨y, rfl⟩
    rw [hb, sub_zero]
  · rintro ⟨q, hq⟩
    obtain ⟨x', rfl⟩ := (LinearMap.range D.a).mkQ_surjective q
    rw [← hq, cokerFirst_mk, cokerSecond_mk, D.bottom.apply_apply_eq_zero, map_zero]

lemma first_injective (hi : Function.Injective D.i) : Function.Injective D.kerFirst := by
  intro x y h
  apply Subtype.ext
  exact hi (congrArg Subtype.val h)

lemma last_surjective (hp : Function.Surjective D.p') : Function.Surjective D.cokerSecond := by
  intro q
  obtain ⟨z', rfl⟩ := (LinearMap.range D.c).mkQ_surjective q
  obtain ⟨y', hy⟩ := hp z'
  exact ⟨(LinearMap.range D.b).mkQ y', by rw [cokerSecond_mk, hy]⟩

/-- The snake sequence, with its unique linear connecting map and all endpoints. -/
theorem snake : snakeType.{u,v} := by
  intro R _ D
  obtain ⟨δ, hδ⟩ := exists_connecting D
  refine ⟨δ, ⟨hδ, exact_kernel_middle D, exact_kernel_connecting D δ hδ,
    exact_connecting_cokernel D δ hδ, exact_cokernel_middle D,
    first_injective D, last_surjective D⟩, ?_⟩
  intro ε hε
  ext z
  obtain ⟨y, x', hy, hx⟩ := lifts D z
  exact (hε.1 z y x' hy hx).trans (hδ z y x' hy hx).symm

/-- Right modules over any ring, using the source's opposite-ring convention. -/
theorem snake_right : snakeRightType.{u,v} := by
  intro R _ D
  exact snake Rᵐᵒᵖ D

/-- Every map of diagrams induces a commuting map of the six-term sequences. -/
theorem naturality : naturalityType.{u,v,w} := by
  intro R _ D E h δ ε hδ hε
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    exact DFunLike.congr_fun h.topLeft x.val
  · ext y
    exact DFunLike.congr_fun h.topRight y.val
  · ext z
    obtain ⟨y, x', hy, hx⟩ := lifts D z
    rw [LinearMap.comp_apply, hδ z y x' hy hx]
    change (LinearMap.range E.a).mkQ (h.a' x') =
      ε (kerMap D.c E.c h.c h.c' h.verticalRight z)
    apply Eq.symm
    apply hε _ (h.b y) (h.a' x')
    · change E.p (h.b y) = h.c z.val
      exact (DFunLike.congr_fun h.topRight y).symm.trans (congrArg h.c hy)
    · calc
        E.i' (h.a' x') = h.b' (D.i' x') := (DFunLike.congr_fun h.bottomLeft x').symm
        _ = h.b' (D.b y) := congrArg h.b' hx
        _ = E.b (h.b y) := DFunLike.congr_fun h.verticalMiddle y
  · apply (LinearMap.range D.a).quot_hom_ext
    intro x'
    change (LinearMap.range E.b).mkQ (h.b' (D.i' x')) =
      (LinearMap.range E.b).mkQ (E.i' (h.a' x'))
    exact congrArg (LinearMap.range E.b).mkQ (DFunLike.congr_fun h.bottomLeft x')
  · apply (LinearMap.range D.b).quot_hom_ext
    intro y'
    change (LinearMap.range E.c).mkQ (h.c' (D.p' y')) =
      (LinearMap.range E.c).mkQ (E.p' (h.b' y'))
    exact congrArg (LinearMap.range E.c).mkQ (DFunLike.congr_fun h.bottomRight y')

end P103.Ch01.SnakeLemma
