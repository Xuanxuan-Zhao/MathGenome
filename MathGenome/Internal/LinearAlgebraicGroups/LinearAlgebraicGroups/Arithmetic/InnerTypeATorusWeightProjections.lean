import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeATorusWeightProjections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct MonoidAlgebra

universe u

namespace LinearAlgebraicGroups.InnerTypeATorusWeightProjections

noncomputable section

open Specs.InnerTypeATorusWeightProjections

private theorem sum_support_select {M A : Type*} [AddCommMonoid A]
    (P : M →₀ A) [DecidableEq M] (a : M) (g : M → A) (h : P a = 0 → g a = 0) :
    (∑ i ∈ P.support, if i = a then g i else 0) = g a := by
  by_cases ha : a ∈ P.support
  · simp [ha]
  · simp [ha, h (Finsupp.notMem_support_iff.mp ha)]

theorem faithfulPointWeights : FaithfulPointWeights.{u} := by
  intro k M A _ _ _ _ ρ natural injective
  classical
  let R₀ : TestAlgebra k := CommAlgCat.of k (MonoidAlgebra k M)
  let e₀ : M →* R₀ˣ := (MonoidAlgebra.of k M).toHomUnits
  let P := TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis M k) (ρ R₀ e₀)
  have universal : ρ R₀ e₀ =
      ∑ a ∈ P.support, (MonoidAlgebra.of k M a ⊗ₜ[k] P a) := by
    exact ((TensorProduct.equivFinsuppOfBasisLeft
      (MonoidAlgebra.basis M k)).symm_apply_apply _).symm.trans
        (TensorProduct.equivFinsuppOfBasisLeft_symm_apply _ P)
  have evaluate (R : TestAlgebra k) (t : M →* Rˣ) :
      ρ R t = ∑ a ∈ P.support, ((t a : R) ⊗ₜ[k] P a) := by
    let f := CommAlgCat.ofHom
      (MonoidAlgebra.lift k R M ((Units.coeHom R).comp t))
    have hf (a : M) : f.hom (MonoidAlgebra.of k M a) = (t a : R) :=
      MonoidAlgebra.lift_of _ _
    have ht : mapCharacter f e₀ = t := by
      apply MonoidHom.ext
      intro a
      exact Units.ext (hf a)
    calc
      ρ R t = Algebra.TensorProduct.map f.hom (AlgHom.id k A) (ρ R₀ e₀) :=
        ht ▸ natural f e₀
      _ = _ := by
        rw [universal, map_sum]
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hf]
  have sum_eq_one : (∑ a ∈ P.support, P a) = 1 := by
    have h := evaluate (CommAlgCat.of k k) 1
    rw [map_one] at h
    have hh := congrArg (TensorProduct.lid k A) h
    simpa only [Algebra.TensorProduct.one_def, map_sum, TensorProduct.lid_tmul, one_smul,
      MonoidHom.one_apply, Units.val_one] using hh.symm
  have orthogonal (a b : M) : P a * P b = if a = b then P a else 0 := by
    let R₂ : TestAlgebra k := CommAlgCat.of k (MonoidAlgebra k (M × M))
    let e : (M × M) →* R₂ˣ := (MonoidAlgebra.of k (M × M)).toHomUnits
    let x : M →* R₂ˣ := e.comp (MonoidHom.inl M M)
    let y : M →* R₂ˣ := e.comp (MonoidHom.inr M M)
    have hx (i : M) : (x i : R₂) = MonoidAlgebra.of k (M × M) (i, 1) := rfl
    have hy (i : M) : (y i : R₂) = MonoidAlgebra.of k (M × M) (1, i) := rfl
    have hxy (i j : M) : (x i : R₂) * (y j : R₂) =
        MonoidAlgebra.of k (M × M) (i, j) := by
      rw [hx, hy, ← map_mul]
      simp
    let c : (R₂ ⊗[k] A) →ₗ[k] A :=
      (Finsupp.lapply (a, b)).comp
        (TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis (M × M) k)).toLinearMap
    have hc (i : M × M) (v : A) :
        c (MonoidAlgebra.of k (M × M) i ⊗ₜ[k] v) = if i = (a, b) then v else 0 := by
      change TensorProduct.equivFinsuppOfBasisLeft (MonoidAlgebra.basis (M × M) k)
        (MonoidAlgebra.basis (M × M) k i ⊗ₜ[k] v) (a, b) = _
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self]
      by_cases hi : i = (a, b) <;> simp [hi]
    have h := congrArg c ((ρ R₂).map_mul x y)
    rw [evaluate R₂ (x * y), evaluate R₂ x, evaluate R₂ y, Finset.sum_mul] at h
    simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum,
      MonoidHom.mul_apply, Units.val_mul, hxy, hc, Prod.mk.injEq] at h
    have diagonal : (∑ i ∈ P.support, if i = a ∧ i = b then P i else 0) =
        if a = b then P a else 0 := by
      by_cases hab : a = b
      · subst b
        simp only [and_self, ite_true]
        exact sum_support_select P a P id
      · rw [ite_eq_right hab]
        apply Finset.sum_eq_zero
        intro i _
        exact ite_eq_right (fun hi => hab (hi.1.symm.trans hi.2))
    have product : (∑ i ∈ P.support, ∑ j ∈ P.support,
        if i = a ∧ j = b then P i * P j else 0) = P a * P b := by
      calc
        _ = ∑ i ∈ P.support, if i = a then P i * P b else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i = a
          · simp only [hi, true_and, ite_true]
            exact sum_support_select P b (fun j => P a * P j) (fun hzero => by simp [hzero])
          · simp [hi]
        _ = _ :=
          sum_support_select P a (fun i => P i * P b) (fun hzero => by simp [hzero])
    exact product.symm.trans (h.symm.trans diagonal)
  have generates : Subgroup.closure (↑P.support : Set M) = ⊤ := by
    let N := Subgroup.closure (↑P.support : Set M)
    let Q : TestAlgebra k := CommAlgCat.of k (MonoidAlgebra k (M ⧸ N))
    let q := (MonoidAlgebra.of k (M ⧸ N)).toHomUnits.comp (QuotientGroup.mk' N)
    have hq (a : M) (ha : a ∈ P.support) : q a = 1 := by
      change (MonoidAlgebra.of k (M ⧸ N)).toHomUnits (QuotientGroup.mk' N a) = 1
      have ha' : QuotientGroup.mk' N a = 1 :=
        (QuotientGroup.eq_one_iff a).mpr (Subgroup.subset_closure ha)
      rw [ha', map_one]
    have he : q = (1 : M →* Qˣ) := by
      apply injective Q
      rw [evaluate Q q, evaluate Q 1]
      exact Finset.sum_congr rfl (fun a ha => by rw [hq a ha]; rfl)
    apply top_unique
    intro a _
    apply (QuotientGroup.eq_one_iff a).mp
    apply (MonoidAlgebra.of_injective (R := k))
    have h := congrArg (fun t : M →* Qˣ => (t a : Q)) he
    exact h.trans (map_one (MonoidAlgebra.of k (M ⧸ N))).symm
  refine ⟨P, rfl, orthogonal, sum_eq_one, evaluate, generates, ?_⟩
  intro l μ h
  exact MonoidHom.eq_of_eqOn_dense generates (fun _ ha => h _ ha)

theorem closedTorusWeights : ClosedTorusWeights.{u} := by
  intro k M A _ _ _ _ _ G e i hi p natural injective
  let j := e.inv ≫ (groupPointsFunctor k).map i
  apply faithfulPointWeights
  · intro R S f t
    change p S (j.app S (mapCharacter f t)) =
      Algebra.TensorProduct.map f.hom (AlgHom.id k A) (p R (j.app R t))
    have h := j.naturality_apply f t
    change j.app S (mapCharacter f t) = ((groupPointsFunctor k).obj G).map f (j.app R t) at h
    rw [h, natural f]
  · intro R s t h
    have he : ((groupPointsFunctor k).map i).app R (e.inv.app R s) =
        ((groupPointsFunctor k).map i).app R (e.inv.app R t) := injective R h
    apply (ConcreteCategory.bijective_of_isIso (e.inv.app R)).1
    let _ : IsClosedImmersion i.hom.hom.left := hi
    let _ : Mono i.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono i.hom.hom).mp he

open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)
open Specs.StandardGroups (spectrum)

theorem normOneTorusWeights : NormOneTorusWeights.{u} := by
  intro k A _ _ _ ι _ hA b
  obtain ⟨H, F, point, point_one, point_mul, point_natural, e, e_spec, c, coordinate⟩ :=
    Descent.InnerTypeA.normOneRepresentability hA b
  let := H.hopf
  let G := spectrum k (NormOneCoordinates hA b)
  let p (R : TestAlgebra k) : ((groupPointsFunctor k).obj G.val).obj R →* (R ⊗[k] A) :=
    { toFun := fun x => (point R (c.hom.app R x)).val
      map_one' := by rw [map_one]; exact point_one R
      map_mul' := fun x y => by rw [map_mul]; exact point_mul R _ _ }
  have injective (R : TestAlgebra k) : Function.Injective (p R) :=
    Subtype.val_injective.comp ((point R).injective.comp
      (ConcreteCategory.bijective_of_isIso (c.hom.app R)).1)
  have natural {R S : TestAlgebra k} (f : R ⟶ S)
      (x : ((groupPointsFunctor k).obj G.val).obj R) :
      p S (((groupPointsFunctor k).obj G.val).map f x) =
        Algebra.TensorProduct.map f.hom (AlgHom.id k A) (p R x) := by
    change (point S (c.hom.app S (((groupPointsFunctor k).obj G.val).map f x))).val = _
    rw [c.hom.naturality_apply f x]
    exact point_natural f _
  refine ⟨H, p, injective, ?_, natural, ?_, ?_⟩
  · intro R
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (point R (c.hom.app R y)).property
    · intro hx
      obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (c.hom.app R)).2
        ((point R).symm ⟨x, hx⟩)
      refine ⟨y, ?_⟩
      change (point R (c.hom.app R y)).val = x
      rw [hy, Equiv.apply_symm_apply]
  · intro R f x hx j
    have he : x = e.hom.app R (WithConv.toConv f) := by
      apply Over.OverMorphism.ext
      exact hx.trans (e_spec R f).symm
    rw [he]
    exact coordinate R f j
  · intro M _ _
    obtain ⟨e₀, e₀_spec, eT, eT_eval⟩ :=
      LinearAlgebraicGroups.DiagonalizableGroups.diagonalPoints k M
    refine ⟨eT, ?_, fun i hi => closedTorusWeights G.val eT i hi p natural injective⟩
    intro R f x hx a
    have he : x = e₀.hom.app R (WithConv.toConv f) := by
      apply Over.OverMorphism.ext
      exact hx.trans (e₀_spec R f).symm
    rw [he]
    exact eT_eval R f a

theorem matrixNormOneTorusWeights : MatrixNormOneTorusWeights.{u} := by
  intro k B _ _ _ m hB hm
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Algebra.IsCentral k B := hB.1
  let : FiniteDimensional k B := hB.2
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩, fun b => normOneTorusWeights _ b⟩

end

end LinearAlgebraicGroups.InnerTypeATorusWeightProjections
