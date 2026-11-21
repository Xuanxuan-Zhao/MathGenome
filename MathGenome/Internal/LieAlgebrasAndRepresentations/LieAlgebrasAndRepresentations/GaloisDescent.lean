import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.GaloisDescent
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-!
LA-J02-Descent: notes/005/lie-algebras-and-representations.tex, lines 4583–4691,
with descent and finite splitting at lines 4619–4650. Fixed-point descent
uses Artin independence and an invariant basis, without division by the group
order. Forms are recovered by transporting the coefficient action, and fixed
algebras are isomorphic precisely when the actions are conjugate. Removing
the coefficient action identifies these conjugacies with coboundaries.
Finite splitting descends the matrix entries of an isomorphism and its inverse
to their finite Galois closure. No finite dimension or characteristic restriction
is imposed on the Lie algebras in the classification.
-/

open scoped TensorProduct
open Module

universe u v w

namespace LieAlgebrasAndRepresentations.GaloisDescent

variable {K : Type u} {L : Type v} {V : Type w}
variable [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

namespace SemilinearAction

variable (ρ : SemilinearAction K L V)

omit [FiniteDimensional K L] [Module K V] [IsScalarTower K L V] in
@[simp] theorem one_apply (x : V) : ρ.act 1 x = x := by
  exact ρ.one_act x

omit [FiniteDimensional K L] [Module K V] [IsScalarTower K L V] in
@[simp] theorem mul_apply (g h : Gal(L/K)) (x : V) :
    ρ.act (g * h) x = ρ.act g (ρ.act h x) := by
  exact ρ.mul_act g h x

/-- Galois averaging needs no division by the group order. -/
noncomputable def average (x : V) : V := ∑ g : Gal(L/K), ρ.act g x

theorem average_fixed (x : V) : ρ.average x ∈ ρ.fixed := by
  intro g
  simp only [average, map_sum, ← ρ.mul_apply]
  exact Fintype.sum_bijective (fun h => g * h) (Group.mulLeft_bijective g) _ _
    (fun _ => rfl)

omit [FiniteDimensional K L] in
/-- Distinct field automorphisms remain independent as scalar-valued functions. -/
theorem automorphisms_linearIndependent :
    LinearIndependent L (fun g : Gal(L/K) => (g : L → L)) :=
  (linearIndependent_monoidHom L L).comp (fun g : Gal(L/K) => g.toMonoidHom)
    (by intro g h e; ext x; exact DFunLike.congr_fun e x)

/-- Invariant vectors span even when the space is infinite-dimensional and
when the characteristic divides the group order. -/
theorem invariant_span : Submodule.span L (ρ.fixed : Set V) = ⊤ := by
  classical
  by_contra h
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr h) (inferInstance : Module.Projective L
      (V ⧸ Submodule.span L (ρ.fixed : Set V)))
  have vanish (x : V) (hx : x ∈ ρ.fixed) : f x = 0 := by
    have : f x ∈ (Submodule.span L (ρ.fixed : Set V)).map f :=
      Submodule.mem_map.mpr ⟨x, Submodule.subset_span hx, rfl⟩
    simpa only [hfW, Submodule.mem_bot] using this
  have coeff (x : V) : ∀ g : Gal(L/K), f (ρ.act g x) = 0 := by
    apply (Fintype.linearIndependent_iff.mp (automorphisms_linearIndependent (K := K) (L := L)))
    funext a
    have hav := vanish (ρ.average (a • x)) (ρ.average_fixed _)
    simpa only [average, map_sum, ρ.map_smul, _root_.map_smul, smul_eq_mul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm, Pi.zero_apply] using hav
  apply hf
  ext x
  simpa only [ρ.one_apply, LinearMap.zero_apply] using coeff x 1

omit [FiniteDimensional K L] in
/-- In an invariant basis the action changes only scalar coefficients. -/
theorem repr_act {ι : Type*} (b : Basis ι L V) (hb : ∀ i, b i ∈ ρ.fixed)
    (g : Gal(L/K)) (x : V) (i : ι) :
    b.repr (ρ.act g x) i = g (b.repr x i) := by
  classical
  have h : ρ.act g x = (b.repr x).sum (fun j a => g a • b j) := by
    conv_lhs => rw [← b.linearCombination_repr x]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, ρ.map_smul,
      hb _ g]
  rw [h]
  simp [Finsupp.sum, _root_.map_smul, Finsupp.single_apply, Finsupp.mem_support_iff]
  intro hi
  rw [hi, map_zero]

variable [IsGalois K L]

/-- Coefficients of a fixed vector in an invariant basis lie in the base field. -/
theorem repr_mem_base {ι : Type*} (b : Basis ι L V) (hb : ∀ i, b i ∈ ρ.fixed)
    (x : ρ.fixed) (i : ι) : b.repr (x : V) i ∈ Set.range (algebraMap K L) := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro g
  rw [← ρ.repr_act b hb g, x.property g]

/-- An invariant basis over the extension is a basis over the base field of
its fixed vectors. -/
noncomputable def basisFixed {ι : Type*} (b : Basis ι L V)
    (hb : ∀ i, b i ∈ ρ.fixed) : Basis ι K ρ.fixed := by
  classical
  let v : ι → ρ.fixed := fun i => ⟨b i, hb i⟩
  apply Basis.mk (v := v)
  · apply LinearIndependent.of_comp (ρ.fixed.subtype)
    exact b.linearIndependent.restrict_scalars' K
  · intro x _
    have heq : x = (b.repr (x : V)).sum (fun i a =>
        (Classical.choose (ρ.repr_mem_base b hb x i)) • v i) := by
      apply Subtype.ext
      have h := b.linearCombination_repr (x : V)
      rw [Finsupp.linearCombination_apply] at h
      convert h.symm using 1
      simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul_of_tower]
      apply Finset.sum_congr rfl
      intro i hi
      change (Classical.choose (ρ.repr_mem_base b hb x i)) • b i = _
      rw [← IsScalarTower.algebraMap_smul L,
        Classical.choose_spec (ρ.repr_mem_base b hb x i)]
    rw [heq]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

@[simp] theorem basisFixed_apply {ι : Type*} (b : Basis ι L V)
    (hb : ∀ i, b i ∈ ρ.fixed) (i : ι) : (ρ.basisFixed b hb i : V) = b i := by
  simp [basisFixed, Basis.mk_apply]

/-- Finite Galois fixed-point descent for arbitrary vector spaces. -/
theorem fixed_point_descent : Function.Bijective ρ.descentMap := by
  classical
  let b := Basis.ofSpan (ρ.invariant_span.ge)
  have hb : ∀ i, b i ∈ ρ.fixed := fun i =>
    Basis.ofSpan_subset (ρ.invariant_span.ge) (Set.mem_range_self i)
  let c := ρ.basisFixed b hb
  let e := (c.baseChange L).equiv b (Equiv.refl _)
  have he : ρ.descentMap = e.toLinearMap := by
    apply (c.baseChange L).ext
    intro i
    change ρ.descentMap ((c.baseChange L) i) = e ((c.baseChange L) i)
    rw [show e ((c.baseChange L) i) = b i from
      (c.baseChange L).equiv_apply i b (Equiv.refl _)]
    simp [c, descentMap]
  rw [he]
  exact e.bijective

end SemilinearAction

section Lie
variable {W : Type w} [LieRing W] [LieAlgebra L W] [LieAlgebra K W]
variable [IsScalarTower K L W]

namespace LieDescentData
variable (ρ : LieDescentData K L W)

/-- The scalar-extension map respects the bracket on fixed points. -/
noncomputable def descentHom : (L ⊗[K] ρ.fixedLie) →ₗ⁅L⁆ W :=
  { ρ.toSemilinearAction.descentMap with
    map_lie' := by
      intro x y
      let F : (L ⊗[K] ρ.fixedLie) →ₗ[L] W := ρ.toSemilinearAction.descentMap
      change F ⁅x, y⁆ = ⁅F x, F y⁆
      induction x using TensorProduct.inductionOn with
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | tmul b y =>
          change F ((a * b) ⊗ₜ[K] ⁅x, y⁆) = ⁅F (a ⊗ₜ[K] x), F (b ⊗ₜ[K] y)⁆
          change (a * b) • (⁅x, y⁆ : ρ.fixedLie).val = ⁅a • (x : W), b • (y : W)⁆
          simp only [LieSubalgebra.coe_bracket, smul_lie, lie_smul, mul_smul]
          exact smul_comm a b _
        | add y z hy hz =>
          simp only [LieRing.lie_add, map_add, hy, hz]
      | add x y hx hy =>
        simp only [LieRing.add_lie, map_add, hx, hy] }

variable [IsGalois K L]

/-- The fixed algebra is a form and its scalar-extension isomorphism is canonical. -/
theorem fixed_lie_descent : ∃ e : (L ⊗[K] ρ.fixedLie) ≃ₗ⁅L⁆ W,
    ∀ a x, e (a ⊗ₜ[K] x) = a • (x : W) := by
  let e := LieEquiv.ofBijective ρ.descentHom ρ.toSemilinearAction.fixed_point_descent
  exact ⟨e, fun _ _ => rfl⟩

end LieDescentData
end Lie


/-- Lie fixed-point descent for an arbitrary extension-field Lie algebra;
no separately assumed base-field Lie structure is needed. -/
theorem fixed_lie_descent
    {W : Type w} [LieRing W] [LieAlgebra L W] [Module K W]
    [IsScalarTower K L W] (ρ : LieDescentData K L W) [IsGalois K L] :
    letI := restrictLieAlgebra K L W
    ∃ e : (L ⊗[K] ρ.fixedLie) ≃ₗ⁅L⁆ W,
      ∀ a x, e (a ⊗ₜ[K] x) = a • (x : W) := by
  let := restrictLieAlgebra K L W
  exact ρ.fixed_lie_descent

section Cocycles
omit [FiniteDimensional K L]
variable {W : Type w} [LieRing W] [LieAlgebra L W]
namespace LieDescentData

@[simp] theorem act_inv_act (ρ : LieDescentData K L W) (g : Gal(L/K)) (x : W) :
    ρ.act g⁻¹ (ρ.act g x) = x := by
  rw [← ρ.mul_act, inv_mul_cancel, ρ.one_act]

@[simp] theorem act_act_inv (ρ : LieDescentData K L W) (g : Gal(L/K)) (x : W) :
    ρ.act g (ρ.act g⁻¹ x) = x := by
  rw [← ρ.mul_act, mul_inv_cancel, ρ.one_act]

@[simp] theorem coefficientAction_apply (τ : LieDescentData K L W)
    (g : Gal(L/K)) (b : W ≃ₗ⁅L⁆ W) (x : W) :
    τ.coefficientAction g b x = τ.act g (b (τ.act g⁻¹ x)) := rfl

@[simp] theorem coefficientAction_inv_apply (τ : LieDescentData K L W)
    (g : Gal(L/K)) (b : W ≃ₗ⁅L⁆ W) (x : W) :
    (τ.coefficientAction g b)⁻¹ x = τ.act g (b.symm (τ.act g⁻¹ x)) := rfl

@[simp] theorem coefficientAction_one (τ : LieDescentData K L W)
    (b : W ≃ₗ⁅L⁆ W) : τ.coefficientAction 1 b = b := by
  ext x
  simp only [coefficientAction_apply, inv_one, τ.one_act]

@[simp] theorem coefficientAction_map_one (τ : LieDescentData K L W)
    (g : Gal(L/K)) : τ.coefficientAction g 1 = 1 := by
  ext x
  simp only [coefficientAction_apply, one_apply_eq_self, act_act_inv]

theorem coefficientAction_mul (τ : LieDescentData K L W)
    (g : Gal(L/K)) (b c : W ≃ₗ⁅L⁆ W) :
    τ.coefficientAction g (b * c) = τ.coefficientAction g b * τ.coefficientAction g c := by
  ext x
  simp only [coefficientAction_apply, lieAut_mul_apply, act_inv_act]

theorem coefficientAction_mul_apply (τ : LieDescentData K L W)
    (g h : Gal(L/K)) (b : W ≃ₗ⁅L⁆ W) :
    τ.coefficientAction (g * h) b = τ.coefficientAction g (τ.coefficientAction h b) := by
  ext x
  simp only [coefficientAction_apply, mul_inv_rev, τ.mul_act]

/-- Remove the coefficient action from an arbitrary semilinear action. -/
def difference (τ ρ : LieDescentData K L W) (g : Gal(L/K)) : W ≃ₗ⁅L⁆ W where
  toFun x := ρ.act g (τ.act g⁻¹ x)
  invFun x := τ.act g (ρ.act g⁻¹ x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    simp only [ρ.map_smul, τ.map_smul, RingHom.id_apply]
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]
    rfl
  map_lie' := by intros; simp only [τ.map_lie, ρ.map_lie]
  left_inv x := by simp only [act_inv_act, act_act_inv]
  right_inv x := by simp only [act_inv_act, act_act_inv]

@[simp] theorem difference_apply (τ ρ : LieDescentData K L W) (g : Gal(L/K)) (x : W) :
    difference τ ρ g x = ρ.act g (τ.act g⁻¹ x) := rfl

/-- The cocycle identity follows from the action identity, with its coefficient action. -/
theorem difference_law (τ ρ : LieDescentData K L W) (g h : Gal(L/K)) :
    difference τ ρ (g * h) = difference τ ρ g * τ.coefficientAction g (difference τ ρ h) := by
  ext x
  simp only [difference_apply, coefficientAction_apply, lieAut_mul_apply,
    act_inv_act, mul_inv_rev, τ.mul_act, ρ.mul_act]

def toCocycle (τ ρ : LieDescentData K L W) : τ.Cocycle :=
  ⟨difference τ ρ, difference_law τ ρ⟩

namespace Cocycle
variable {τ : LieDescentData K L W}

@[simp] theorem val_one (c : τ.Cocycle) : c.val 1 = 1 := by
  have h := c.law 1 1
  rw [one_mul, coefficientAction_one] at h
  apply mul_left_cancel (a := c.val 1)
  simpa only [mul_one] using h.symm

/-- Twisting the coefficient action by a cocycle gives a descent datum. -/
def toData (c : τ.Cocycle) : LieDescentData K L W where
  act g := (τ.act g).trans (c.val g).toLinearEquiv.toAddEquiv
  one_act x := by change c.val 1 (τ.act 1 x) = x; simp [τ.one_act]
  mul_act g h x := by
    change c.val (g * h) (τ.act (g * h) x) =
      c.val g (τ.act g (c.val h (τ.act h x)))
    rw [c.law]
    simp only [lieAut_mul_apply, coefficientAction_apply, τ.mul_act, act_inv_act]
  map_smul g a x := by
    change c.val g (τ.act g (a • x)) = g a • c.val g (τ.act g x)
    rw [τ.map_smul, map_smul]
  map_lie g x y := by
    change c.val g (τ.act g ⁅x, y⁆) = ⁅c.val g (τ.act g x), c.val g (τ.act g y)⁆
    rw [τ.map_lie, (c.val g).map_lie]

@[simp] theorem toData_apply (c : τ.Cocycle) (g : Gal(L/K)) (x : W) :
    c.toData.act g x = c.val g (τ.act g x) := rfl

@[ext] theorem ext {c d : τ.Cocycle} (h : ∀ g, c.val g = d.val g) : c = d := by
  cases c; cases d
  congr
  exact funext h

end Cocycle

@[ext] theorem ext {ρ σ : LieDescentData K L W}
    (h : ∀ g x, ρ.act g x = σ.act g x) : ρ = σ := by
  have ha : ρ.act = σ.act := by funext g; exact AddEquiv.ext (h g)
  rcases ρ with ⟨⟨a, _, _, _⟩, _⟩
  rcases σ with ⟨⟨b, _, _, _⟩, _⟩
  change a = b at ha
  cases ha
  rfl

/-- Cocycles and actions are in bijection before taking equivalence classes. -/
def cocycleEquiv (τ : LieDescentData K L W) :
    LieDescentData K L W ≃ τ.Cocycle where
  toFun := toCocycle τ
  invFun := Cocycle.toData
  left_inv ρ := by
    ext g x
    simp only [Cocycle.toData_apply, toCocycle, difference_apply, act_inv_act]
  right_inv c := by
    apply Cocycle.ext
    intro g
    ext x
    simp only [toCocycle, difference_apply, Cocycle.toData_apply, act_act_inv]

/-- Coboundaries are exactly conjugacies of semilinear descent data. -/
theorem equivalent_iff_cohomologous (τ ρ σ : LieDescentData K L W) :
    Equivalent ρ σ ↔ τ.Cohomologous (toCocycle τ ρ) (toCocycle τ σ) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, fun g => ?_⟩
    ext x
    change σ.act g (τ.act g⁻¹ x) =
      b (ρ.act g (τ.act g⁻¹ ((τ.coefficientAction g b)⁻¹ x)))
    rw [hb]
    simp only [coefficientAction_inv_apply, act_inv_act]
  · rintro ⟨b, hb⟩
    refine ⟨b, fun g x => ?_⟩
    have h := DFunLike.congr_fun (hb g) (τ.act g x)
    change σ.act g (τ.act g⁻¹ (τ.act g x)) =
      b (ρ.act g (τ.act g⁻¹ ((τ.coefficientAction g b)⁻¹ (τ.act g x)))) at h
    simpa only [coefficientAction_inv_apply, act_inv_act] using h

end LieDescentData
end Cocycles

section Forms
universe w' z
variable {W : Type w} {W' : Type w'}
variable [LieRing W] [LieAlgebra K W] [LieAlgebra L W] [IsScalarTower K L W]
variable [LieRing W'] [LieAlgebra K W'] [LieAlgebra L W'] [IsScalarTower K L W']

namespace LieDescentData

/-- Transfer a semilinear Lie action through an extension-field Lie isomorphism. -/
def transport (ρ : LieDescentData K L W) (e : W ≃ₗ⁅L⁆ W') : LieDescentData K L W' where
  act g := (e.toLinearEquiv.toAddEquiv.symm.trans (ρ.act g)).trans e.toLinearEquiv.toAddEquiv
  one_act x := by change e (ρ.act 1 (e.symm x)) = x; rw [ρ.one_act, e.apply_symm_apply]
  mul_act g h x := by
    change e (ρ.act (g * h) (e.symm x)) = e (ρ.act g (e.symm (e (ρ.act h (e.symm x)))))
    rw [e.symm_apply_apply, ρ.mul_act]
  map_smul g a x := by
    change e (ρ.act g (e.symm (a • x))) = g a • e (ρ.act g (e.symm x))
    rw [map_smul, ρ.map_smul, map_smul]
  map_lie g x y := by
    change e (ρ.act g (e.symm ⁅x, y⁆)) = ⁅e (ρ.act g (e.symm x)), e (ρ.act g (e.symm y))⁆
    rw [e.symm.map_lie, ρ.map_lie, e.map_lie]

/-- An equivariant extension-field isomorphism restricts to the fixed Lie algebras. -/
def fixedEquiv (ρ : LieDescentData K L W) (σ : LieDescentData K L W')
    (e : W ≃ₗ⁅L⁆ W') (he : ∀ g x, σ.act g (e x) = e (ρ.act g x)) :
    ρ.fixedLie ≃ₗ⁅K⁆ σ.fixedLie where
  toFun x := ⟨e x, by intro g; rw [he, x.property g]⟩
  invFun y := ⟨e.symm y, by
    intro g
    apply e.toLinearEquiv.injective
    change e (ρ.act g (e.symm (y : W'))) = e (e.symm (y : W'))
    rw [← he, e.apply_symm_apply, y.property g]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add e (x : W) (y : W))
  map_smul' a x := by
    apply Subtype.ext
    change e (a • (x : W)) = a • e (x : W)
    rw [← IsScalarTower.algebraMap_smul L a (x : W), map_smul,
      IsScalarTower.algebraMap_smul]
  map_lie' := by intros; apply Subtype.ext; exact e.map_lie _ _

noncomputable def descentEquiv (ρ : LieDescentData K L W) [IsGalois K L] :
    (L ⊗[K] ρ.fixedLie) ≃ₗ⁅L⁆ W :=
  LieEquiv.ofBijective ρ.descentHom ρ.toSemilinearAction.fixed_point_descent

@[simp] theorem descentEquiv_tmul (ρ : LieDescentData K L W) [IsGalois K L]
    (a : L) (x : ρ.fixedLie) : ρ.descentEquiv (a ⊗ₜ[K] x) = a • (x : W) := rfl

end LieDescentData

/-- Extension of scalars for a Lie isomorphism, retaining its bracket. -/
def baseChangeLieEquiv {A : Type w} {B : Type w'} [LieRing A] [LieAlgebra K A]
    [LieRing B] [LieAlgebra K B] (e : A ≃ₗ⁅K⁆ B) :
    (L ⊗[K] A) ≃ₗ⁅L⁆ (L ⊗[K] B) :=
  { e.toLinearEquiv.baseChange K L A B with
    map_lie' := by
      intro x y
      let F := (e.toLinearEquiv.baseChange K L A B).toLinearMap
      change F ⁅x, y⁆ = ⁅F x, F y⁆
      induction x using TensorProduct.inductionOn with
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | tmul b y =>
          change (a * b) ⊗ₜ[K] e ⁅x, y⁆ = (a * b) ⊗ₜ[K] ⁅e x, e y⁆
          rw [e.map_lie]
        | add y z hy hz => simp only [lie_add, map_add, hy, hz]
      | add x y hx hy => simp only [add_lie, map_add, hx, hy] }

omit [FiniteDimensional K L] in
@[simp] theorem baseChangeLieEquiv_tmul {A : Type w} {B : Type w'}
    [LieRing A] [LieAlgebra K A] [LieRing B] [LieAlgebra K B]
    (e : A ≃ₗ⁅K⁆ B) (a : L) (x : A) :
    baseChangeLieEquiv (L := L) e (a ⊗ₜ[K] x) = a ⊗ₜ[K] e x := rfl

/-- Conjugate descent data are precisely those with isomorphic descended algebras. -/
theorem equivalent_iff_fixed_isomorphic [IsGalois K L]
    (ρ σ : LieDescentData K L W) :
    LieDescentData.Equivalent ρ σ ↔ Nonempty (ρ.fixedLie ≃ₗ⁅K⁆ σ.fixedLie) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨ρ.fixedEquiv σ b (by intro g x; rw [hb, b.symm_apply_apply])⟩
  · rintro ⟨f⟩
    let b := ρ.descentEquiv.symm.trans ((baseChangeLieEquiv (L := L) f).trans σ.descentEquiv)
    have hb (a : L) (x : ρ.fixedLie) : b (a • (x : W)) = a • (f x : W) := by
      change σ.descentEquiv ((baseChangeLieEquiv (L := L) f)
        (ρ.descentEquiv.symm (a • (x : W)))) = _
      rw [show ρ.descentEquiv.symm (a • (x : W)) = a ⊗ₜ[K] x from
        ρ.descentEquiv.symm_apply_eq.mpr rfl, baseChangeLieEquiv_tmul,
        σ.descentEquiv_tmul]
    have hc (g : Gal(L/K)) (x : W) : σ.act g (b x) = b (ρ.act g x) := by
      obtain ⟨t, rfl⟩ := ρ.descentEquiv.surjective x
      induction t using TensorProduct.inductionOn with
      | tmul a x =>
        change σ.act g (b (a • (x : W))) = b (ρ.act g (a • (x : W)))
        rw [hb, σ.map_smul, ρ.map_smul,
          x.property g, (f x).property g, hb]
      | add x y hx hy => simp only [map_add, hx, hy]
    exact ⟨b, fun g x => by simpa only [b.apply_symm_apply] using hc g (b.symm x)⟩

/-- The fixed algebra of the coefficient action is the original algebra. -/
theorem scalar_fixed_equiv (A : Type w) [LieRing A] [LieAlgebra K A] [IsGalois K L] :
    ∃ e : A ≃ₗ⁅K⁆ (scalarAction (K := K) (L := L) A).fixedLie,
      ∀ x, (e x : L ⊗[K] A) = 1 ⊗ₜ[K] x := by
  classical
  let ρ := scalarAction (K := K) (L := L) A
  let b := Module.Free.chooseBasis K A
  have hb : ∀ i, b.baseChange L i ∈ ρ.toSemilinearAction.fixed := by
    intro i g
    simp only [Basis.baseChange_apply, ρ, scalarAction_tmul, map_one]
  let c := ρ.toSemilinearAction.basisFixed (b.baseChange L) hb
  let e := b.equiv c (Equiv.refl _)
  have he (x : A) : (e x : L ⊗[K] A) = 1 ⊗ₜ[K] x := by
    have h : ρ.toSemilinearAction.fixed.subtype ∘ₗ e.toLinearMap = TensorProduct.mk K L A 1 := by
      apply b.ext
      intro i
      change (e (b i) : L ⊗[K] A) = 1 ⊗ₜ[K] b i
      rw [show e (b i) = c i from b.equiv_apply i c (Equiv.refl _)]
      simpa only [Basis.baseChange_apply] using
        ρ.toSemilinearAction.basisFixed_apply (b.baseChange L) hb i
    exact DFunLike.congr_fun h x
  refine ⟨{ e with map_lie' := ?_ }, he⟩
  intro x y
  apply Subtype.ext
  change (e ⁅x, y⁆ : L ⊗[K] A) = ⁅(e x : L ⊗[K] A), (e y : L ⊗[K] A)⁆
  rw [he, he, he, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

/-- Every form trivialized over `L` is obtained by taking fixed points. -/
theorem forms_recovered (A : Type w) (B : Type w') [LieRing A] [LieAlgebra K A]
    [LieRing B] [LieAlgebra K B] [IsGalois K L]
    (e : (L ⊗[K] B) ≃ₗ⁅L⁆ (L ⊗[K] A)) :
    ∃ ρ : LieDescentData K L (L ⊗[K] A), Nonempty (B ≃ₗ⁅K⁆ ρ.fixedLie) := by
  let σ := scalarAction (K := K) (L := L) B
  obtain ⟨f, _⟩ := scalar_fixed_equiv (K := K) (L := L) B
  refine ⟨σ.transport e, ⟨f.trans (σ.fixedEquiv (σ.transport e) e ?_)⟩⟩
  intro g x
  change e (σ.act g (e.symm (e x))) = e (σ.act g x)
  rw [e.symm_apply_apply]

end Forms

/-- The complete cocycle correspondence, including its coboundary equivalence. -/
theorem cocycle_classification {W : Type w} [LieRing W] [LieAlgebra L W]
    (τ : LieDescentData K L W) :
    ∃ e : LieDescentData K L W ≃ τ.Cocycle,
      (∀ ρ g x, (e ρ).val g x = ρ.act g (τ.act g⁻¹ x)) ∧
      ∀ ρ σ, LieDescentData.Equivalent ρ σ ↔ τ.Cohomologous (e ρ) (e σ) := by
  exact ⟨τ.cocycleEquiv, fun _ _ _ => rfl, τ.equivalent_iff_cohomologous⟩

section Cohomology
variable {W : Type w} [LieRing W] [LieAlgebra L W]
namespace LieDescentData

omit [FiniteDimensional K L] in
theorem equivalent_equivalence : Equivalence (Equivalent (K := K) (L := L) (W := W)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ; exact ⟨1, fun _ _ => rfl⟩
  · rintro ρ σ ⟨b, hb⟩
    refine ⟨b.symm, fun g x => ?_⟩
    change ρ.act g x = b.symm (σ.act g (b x))
    rw [hb, b.symm_apply_apply, b.symm_apply_apply]
  · rintro ρ σ υ ⟨b, hb⟩ ⟨c, hc⟩
    refine ⟨b.trans c, fun g x => ?_⟩
    change υ.act g x = c (b (ρ.act g (b.symm (c.symm x))))
    rw [hc, hb]

omit [FiniteDimensional K L] in
theorem cohomologous_equivalence (τ : LieDescentData K L W) :
    Equivalence τ.Cohomologous := by
  have h (c d : τ.Cocycle) :
      τ.Cohomologous c d ↔ Equivalent c.toData d.toData := by
    rw [equivalent_iff_cohomologous τ]
    change τ.Cohomologous c d ↔
      τ.Cohomologous (τ.cocycleEquiv (τ.cocycleEquiv.symm c))
        (τ.cocycleEquiv (τ.cocycleEquiv.symm d))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact ⟨fun c => (h c c).mpr (equivalent_equivalence.refl _),
    fun hcd => (h _ _).mpr (equivalent_equivalence.symm ((h _ _).mp hcd)),
    fun hcd hde => (h _ _).mpr
      (equivalent_equivalence.trans ((h _ _).mp hcd) ((h _ _).mp hde))⟩

omit [FiniteDimensional K L] in
/-- Equality of cohomology classes is exactly the specified coboundary relation. -/
theorem h1_eq_iff (τ : LieDescentData K L W) (c d : τ.Cocycle) :
    (Quot.mk τ.Cohomologous c : τ.H1) = Quot.mk τ.Cohomologous d ↔ τ.Cohomologous c d := by
  let s : Setoid τ.Cocycle := ⟨τ.Cohomologous, τ.cohomologous_equivalence⟩
  exact ⟨fun h => @Quotient.exact _ s c d h, Quot.sound⟩

end LieDescentData

/-- Descent data modulo isomorphism give exactly nonabelian Galois cohomology.
Together with `forms_recovered`, this classifies every `K`-form of `A_L`. -/
theorem forms_classified_by_h1 [LieAlgebra K W] [IsScalarTower K L W] [IsGalois K L]
    (τ : LieDescentData K L W) :
    ∃ classify : LieDescentData K L W → τ.H1,
      Function.Surjective classify ∧ ∀ ρ σ,
        classify ρ = classify σ ↔ Nonempty (ρ.fixedLie ≃ₗ⁅K⁆ σ.fixedLie) := by
  refine ⟨fun ρ => Quot.mk _ (τ.cocycleEquiv ρ), ?_, ?_⟩
  · intro c
    induction c using Quot.inductionOn with
    | h c => exact ⟨τ.cocycleEquiv.symm c, congrArg (Quot.mk _) (τ.cocycleEquiv.apply_symm_apply c)⟩
  · intro ρ σ
    exact (τ.h1_eq_iff _ _).trans
      ((τ.equivalent_iff_cohomologous ρ σ).symm.trans (equivalent_iff_fixed_isomorphic ρ σ))

end Cohomology

section FiniteSplitting
universe w'
variable {Ω : Type v} [Field Ω] [Algebra K Ω]
variable (F : IntermediateField K Ω) (A : Type w) [LieRing A] [LieAlgebra K A]

/-- Inclusion into an overfield on the first tensor factor. -/
def scalarInclusion : F ⊗[K] A →ₗ[F] Ω ⊗[K] A :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap F Ω) (LinearMap.id : A →ₗ[K] A)

@[simp] theorem scalarInclusion_tmul (a : F) (x : A) :
    scalarInclusion F A (a ⊗ₜ[K] x) = (a : Ω) ⊗ₜ[K] x := rfl

@[simp] theorem scalarInclusion_basis {ι : Type*} (b : Basis ι K A) (i : ι) :
    scalarInclusion F A (b.baseChange F i) = b.baseChange Ω i := by
  simp only [Basis.baseChange_apply, scalarInclusion_tmul, OneMemClass.coe_one]

theorem scalarInclusion_smul (a : F) (x : F ⊗[K] A) :
    scalarInclusion F A (a • x) = (a : Ω) • scalarInclusion F A x := by
  rw [map_smul, ← IsScalarTower.algebraMap_smul Ω a]
  rfl

theorem scalarInclusion_injective : Function.Injective (scalarInclusion F A) := by
  exact TensorProduct.map_injective_of_flat_flat F.val.toLinearMap (LinearMap.id : A →ₗ[K] A)
    F.val.injective Function.injective_id

theorem scalarInclusion_lie (x y : F ⊗[K] A) :
    scalarInclusion F A ⁅x, y⁆ = ⁅scalarInclusion F A x, scalarInclusion F A y⁆ := by
  exact (LieAlgebra.ExtendScalars.map F.val (LieHom.id : A →ₗ⁅K⁆ A)).map_lie x y

variable {F A}

/-- A linear map whose finitely many matrix coefficients lie in `F` descends to `F`. -/
theorem linear_map_over_intermediateField
    {B : Type w'} [LieRing B] [LieAlgebra K B]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (b : Basis ι K A) (c : Basis κ K B)
    (f : Ω ⊗[K] A →ₗ[Ω] Ω ⊗[K] B)
    (hf : ∀ i j, (c.baseChange Ω).repr (f (b.baseChange Ω i)) j ∈ F) :
    ∃ f₀ : F ⊗[K] A →ₗ[F] F ⊗[K] B,
      ∀ x, scalarInclusion F B (f₀ x) = f (scalarInclusion F A x) := by
  classical
  let v : ι → F ⊗[K] B := fun i => ∑ j,
    (⟨(c.baseChange Ω).repr (f (b.baseChange Ω i)) j, hf i j⟩ : F) • c.baseChange F j
  let f₀ := (b.baseChange F).constr F v
  refine ⟨f₀, ?_⟩
  have h : (scalarInclusion F B).comp f₀ =
      (f.restrictScalars F).comp (scalarInclusion F A) := by
    apply (b.baseChange F).ext
    intro i
    simp only [LinearMap.comp_apply, f₀, Basis.constr_basis, v, map_sum,
      scalarInclusion_smul, scalarInclusion_basis, LinearMap.restrictScalars_apply]
    exact (c.baseChange Ω).sum_repr _
  intro x
  exact DFunLike.congr_fun h x

end FiniteSplitting

section FiniteGaloisSplitting
universe w'
variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable {A : Type w} {B : Type w'} [LieRing A] [LieAlgebra K A]
variable [LieRing B] [LieAlgebra K B] [FiniteDimensional K A] [FiniteDimensional K B]

/-- An isomorphism over an algebraic Galois extension is defined over a finite
Galois subextension: adjoin the entries of both it and its inverse. -/
theorem finite_galois_isomorphism
    (e : (Ω ⊗[K] A) ≃ₗ⁅Ω⁆ (Ω ⊗[K] B)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      Nonempty ((F ⊗[K] A) ≃ₗ⁅F⁆ (F ⊗[K] B)) := by
  classical
  let b := Module.finBasis K A
  let c := Module.finBasis K B
  let s : Set Ω :=
    Set.range (fun p : Fin (finrank K A) × Fin (finrank K B) =>
      (c.baseChange Ω).repr (e (b.baseChange Ω p.1)) p.2) ∪
    Set.range (fun p : Fin (finrank K B) × Fin (finrank K A) =>
      (b.baseChange Ω).repr (e.symm (c.baseChange Ω p.1)) p.2)
  let F := FiniteGaloisIntermediateField.adjoin K s
  have hF : s ⊆ F.toIntermediateField := FiniteGaloisIntermediateField.subset_adjoin K s
  obtain ⟨f, hf⟩ := linear_map_over_intermediateField (F := F.toIntermediateField)
    b c e.toLinearEquiv.toLinearMap (fun i j => hF (Or.inl ⟨(i, j), rfl⟩))
  obtain ⟨g, hg⟩ := linear_map_over_intermediateField (F := F.toIntermediateField)
    c b e.symm.toLinearEquiv.toLinearMap (fun i j => hF (Or.inr ⟨(i, j), rfl⟩))
  change ∀ x, scalarInclusion F.toIntermediateField B (f x) =
    e (scalarInclusion F.toIntermediateField A x) at hf
  change ∀ y, scalarInclusion F.toIntermediateField A (g y) =
    e.symm (scalarInclusion F.toIntermediateField B y) at hg
  have hgf (x) : g (f x) = x := by
    apply scalarInclusion_injective F.toIntermediateField A
    rw [hg, hf, e.symm_apply_apply]
  have hfg (y) : f (g y) = y := by
    apply scalarInclusion_injective F.toIntermediateField B
    rw [hf, hg, e.apply_symm_apply]
  refine ⟨F, ⟨{ f with invFun := g, left_inv := hgf, right_inv := hfg, map_lie' := ?_ }⟩⟩
  intro x y
  apply scalarInclusion_injective F.toIntermediateField B
  change scalarInclusion F.toIntermediateField B (f ⁅x, y⁆) =
    scalarInclusion F.toIntermediateField B ⁅f x, f y⁆
  rw [hf, scalarInclusion_lie, e.map_lie, scalarInclusion_lie, hf, hf]

end FiniteGaloisSplitting

/-- In characteristic zero, isomorphism after extension to an algebraic closure
already holds over a finite Galois extension of the original field. -/
theorem finite_galois_splitting [CharZero K]
    {A : Type w} {B : Type*} [LieRing A] [LieAlgebra K A]
    [LieRing B] [LieAlgebra K B] [FiniteDimensional K A] [FiniteDimensional K B]
    (h : Nonempty (((AlgebraicClosure K) ⊗[K] A) ≃ₗ⁅AlgebraicClosure K⁆
      ((AlgebraicClosure K) ⊗[K] B))) :
    ∃ F : FiniteGaloisIntermediateField K (AlgebraicClosure K),
      Nonempty ((F ⊗[K] A) ≃ₗ⁅F⁆ (F ⊗[K] B)) := by
  obtain ⟨e⟩ := h
  exact finite_galois_isomorphism e

end LieAlgebrasAndRepresentations.GaloisDescent
