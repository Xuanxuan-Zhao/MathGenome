import Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Classification.IntegralRootRelations
open scoped TensorProduct
open Algebra.TensorProduct Coalgebra HopfAlgebra WithConv

universe u

namespace LinearAlgebraicGroups.Classification.IntegralCentralQuotient

open Specs.IntegralCentralQuotient

noncomputable section

variable {R A M : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup M]
variable (π : A →ₐc[R] MonoidAlgebra R M)

local notation "H" => MonoidAlgebra R M
local notation "χ" => MonoidAlgebra.of R M

private theorem orbitMap_tmul (a b : A) :
    orbitMap π (a ⊗ₜ[R] b) = (includeLeft : A →ₐ[R] A ⊗[R] H) a * rightCoaction π b :=
  rfl

/-- The graph of right translation by a closed diagonalizable subgroup is closed. -/
theorem orbitMap_surjective (hπ : Function.Surjective π) : Function.Surjective (orbitMap π) := by
  let F := orbitMap π
  let l : A →ₐ[R] A ⊗[R] A := includeLeft
  let r : A →ₐ[R] A ⊗[R] A := includeRight
  let L : A →ₐ[R] A ⊗[R] H := includeLeft
  let Q : A →ₐ[R] A ⊗[R] H := includeRight.comp π.toAlgHom
  have hl : F.comp l = L := by
    ext a
    change F (a ⊗ₜ[R] 1) = L a
    simp [F, L, orbitMap_tmul]
  have hr : toConv (F.comp r) = toConv L * toConv Q := by
    apply ofConv_injective
    ext a
    change F (1 ⊗ₜ[R] a) = ((toConv L * toConv Q).ofConv) a
    rw [show F = orbitMap π from rfl, orbitMap_tmul, map_one, one_mul, AlgHom.convMul_def]
    change (_ : A ⊗[R] H) = ((lmul' R).comp (Algebra.TensorProduct.map L Q))
      (Bialgebra.comulAlgHom R A a)
    unfold rightCoaction
    suffices (lmul' R).comp (Algebra.TensorProduct.map L Q) =
        Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom by
      rw [this]
      rfl
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [L, Q]
  let lInv := (toConv l : WithConv (A →ₐ[R] A ⊗[R] A))⁻¹
  let s := (lInv * toConv r).ofConv
  have hs : F.comp s = Q := by
    apply toConv_injective
    rw [show s = (lInv * toConv r).ofConv from rfl, AlgHom.comp_convMul_distrib, hr]
    change toConv (F.comp (l.comp (antipodeAlgHom R A))) * _ = _
    rw [← AlgHom.comp_assoc, hl]
    change (toConv L)⁻¹ * (toConv L * toConv Q) = toConv Q
    exact inv_mul_cancel_left (toConv L) (toConv Q)
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a z =>
    obtain ⟨b, hb⟩ := hπ z
    refine ⟨l a * s b, ?_⟩
    rw [map_mul, show F (l a) = L a from DFunLike.congr_fun hl a,
      show F (s b) = Q b from DFunLike.congr_fun hs b]
    change (a ⊗ₜ[R] (1 : H)) * (1 ⊗ₜ[R] π b) = _
    rw [tmul_mul_tmul, mul_one, one_mul, hb]
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add F x' y'⟩

private theorem coaction_tmul_sum (a : A) (w : Coalgebra.Repr R a ι) :
    rightCoaction π a = ∑ i ∈ w.index, w.left i ⊗ₜ[R] π (w.right i) := by
  change Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom (comul a) = _
  rw [← w.eq, map_sum]
  rfl

private theorem coaction_assoc (a : A) :
    (LinearMap.rTensor H (rightCoaction π).toLinearMap) (rightCoaction π a) =
      (TensorProduct.assoc R A H H).symm
        ((LinearMap.lTensor A (comul (R := R) (A := H))) (rightCoaction π a)) := by
  let w := ℛ R a
  have h := congrArg (TensorProduct.map (LinearMap.id : A →ₗ[R] A)
    (TensorProduct.map π.toLinearMap π.toLinearMap)) (Coalgebra.coassoc_apply (R := R) a)
  rw [TensorProduct.map_map_assoc] at h
  apply (TensorProduct.assoc R A H H).injective
  rw [LinearEquiv.apply_symm_apply]
  refine (congrArg (TensorProduct.assoc R A H H) ?_).trans (h.trans ?_)
  · rw [coaction_tmul_sum π a w, ← w.eq, map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
    change Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom (comul (w.left i)) ⊗ₜ[R]
      π (w.right i) = TensorProduct.map LinearMap.id π.toLinearMap (comul (w.left i)) ⊗ₜ[R] _
    rfl
  · rw [coaction_tmul_sum π a w, ← w.eq, map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      show ∀ z : A, TensorProduct.map π.toLinearMap π.toLinearMap (comul z) =
        comul (π z) from fun z => CoalgHomClass.map_comp_comul_apply π z]

open Classical in
private theorem sum_basis {X : Type*} [AddCommGroup X] [Module R X] [Fintype M]
    (t : X ⊗[R] H) :
    ∑ m : M, (TensorProduct.equivFinsuppOfBasisRight
      (M := X) (MonoidAlgebra.basis M R) t m) ⊗ₜ[R] χ m = t := by
  let F := TensorProduct.equivFinsuppOfBasisRight (M := X) (MonoidAlgebra.basis M R)
  calc
    _ = F.symm (F t) := by
      rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype]
      · simp only [F, MonoidAlgebra.basis_apply, MonoidAlgebra.of_apply]
      · intro
        exact TensorProduct.zero_tmul _ _
    _ = t := F.symm_apply_apply t

private def tensorCoeff (X : Type*) [AddCommGroup X] [Module R X] (m : M) :
    X ⊗[R] H →ₗ[R] X := by
  classical
  exact (Finsupp.lapply m).comp
    (TensorProduct.equivFinsuppOfBasisRight (MonoidAlgebra.basis M R)).toLinearMap

open Classical in
private theorem tensorCoeff_basis (X : Type*) [AddCommGroup X] [Module R X] (m n : M)
    (x : X) :
    tensorCoeff X m (x ⊗ₜ[R] χ n) = if n = m then x else 0 := by
  classical
  change TensorProduct.equivFinsuppOfBasisRight (MonoidAlgebra.basis M R)
    (x ⊗ₜ[R] χ n) m = _
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  change ((MonoidAlgebra.basis M R).repr ((MonoidAlgebra.basis M R) n)) m • x = _
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split <;> simp

private def degreePart (m : M) : A →ₗ[R] A :=
  (tensorCoeff A m).comp (rightCoaction π).toLinearMap

private theorem rightCoaction_eq_sum [Fintype M] (a : A) :
    rightCoaction π a = ∑ m : M, degreePart π m a ⊗ₜ[R] χ m :=
  (sum_basis (rightCoaction π a)).symm

private theorem degreePart_degree [Fintype M] (m : M) (a : A) :
    HasDegree π m (degreePart π m a) := by
  classical
  have h := congrArg (tensorCoeff (A ⊗[R] H) m) (coaction_assoc π a)
  rw [rightCoaction_eq_sum π a, map_sum, map_sum, map_sum, map_sum, map_sum] at h
  unfold HasDegree
  simpa only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      (MonoidAlgebra.isGroupLikeElem_of (R := R) (M := M) _).comul_eq_tmul_self,
      TensorProduct.assoc_symm_tmul, AlgHom.toLinearMap_apply, tensorCoeff_basis, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using h

open Classical in
private theorem degreePart_eq (a : A) (m n : M) (ha : HasDegree π n a) :
    degreePart π m a = if n = m then a else 0 := by
  change tensorCoeff A m (rightCoaction π a) = _
  rw [ha, tensorCoeff_basis]

private theorem sum_degreePart [Fintype M] (a : A) : ∑ m : M, degreePart π m a = a := by
  let ε : H →ₗ[R] R := counit
  have hc : ε.lTensor A (rightCoaction π a) = a ⊗ₜ[R] (1 : R) := by
    let w := ℛ R a
    rw [coaction_tmul_sum π a w, map_sum, ← Coalgebra.lTensor_counit_comul (R := R) a,
      ← w.eq, map_sum]
    simp only [LinearMap.lTensor_tmul, CoalgHomClass.counit_comp_apply, ε]
  have h := congrArg (TensorProduct.rid R A) hc
  rw [rightCoaction_eq_sum π a, map_sum, map_sum] at h
  simpa only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    show ∀ m : M, ε (χ m) = 1 from
      fun m => (MonoidAlgebra.isGroupLikeElem_of (R := R) (M := M) m).counit_eq_one,
    one_smul] using h

private theorem degree_mul {m n : M} {a b : A} (ha : HasDegree π m a)
    (hb : HasDegree π n b) : HasDegree π (m * n) (a * b) := by
  change rightCoaction π (a * b) = _
  rw [map_mul, ha, hb, tmul_mul_tmul, map_mul]

private theorem tensorCoeff_mul_left (a : A) (m : M) (t : A ⊗[R] H) :
    tensorCoeff A m ((a ⊗ₜ[R] (1 : H)) * t) = a * tensorCoeff A m t := by
  classical
  induction t using TensorProduct.inductionOn with
  | tmul x c =>
    rw [tmul_mul_tmul]
    simp only [tensorCoeff, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    rw [one_mul, mul_smul_comm]
  | add x y hx hy => simp [mul_add, hx, hy]

/-- Each degree contains a finite family whose products with the opposite degree sum to one. -/
theorem strongGrading [Finite M] (hπ : Function.Surjective π) : StrongGrading π := by
  classical
  let := Fintype.ofFinite M
  intro m
  obtain ⟨x, hx⟩ := orbitMap_surjective π hπ (1 ⊗ₜ[R] χ m)
  obtain ⟨n, a, b, hn⟩ := TensorProduct.exists_sum_tmul_eq x
  have h := congrArg (tensorCoeff A m) hx
  rw [hn, map_sum, map_sum, tensorCoeff_basis, ite_eq_left rfl] at h
  simp only [orbitMap_tmul, includeLeft_apply, tensorCoeff_mul_left] at h
  have hh := congrArg (degreePart π 1) h
  have hone : HasDegree π (1 : M) (1 : A) := (invariants π).one_mem
  rw [map_sum, degreePart_eq π 1 1 1 hone, ite_eq_left rfl] at hh
  refine ⟨n, fun i => degreePart π m⁻¹ (a i), fun i => degreePart π m (b i),
    fun _ => degreePart_degree π _ _, fun _ => degreePart_degree π _ _, ?_⟩
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro i _
  change degreePart π m⁻¹ (a i) * degreePart π m (b i) =
    degreePart π 1 (a i * degreePart π m (b i))
  conv_rhs => rw [← sum_degreePart π (a i)]
  rw [Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single m⁻¹]
  · rw [degreePart_eq π _ _ _ (degree_mul π (degreePart_degree π _ _) (degreePart_degree π _ _)),
      inv_mul_cancel, ite_eq_left rfl]
  · intro j _ hj
    rw [degreePart_eq π _ _ _ (degree_mul π (degreePart_degree π _ _) (degreePart_degree π _ _)),
      ite_eq_right (fun h => hj (eq_inv_of_mul_eq_one_left h))]
  · simp

local notation "B" => (invariants π)

private theorem degreePart_mul_invariant [Fintype M] (m : M) (b : B) (a : A) :
    degreePart π m ((b : A) * a) = (b : A) * degreePart π m a := by
  change tensorCoeff A m (rightCoaction π ((b : A) * a)) = _
  have hb : rightCoaction π (b : A) = (b : A) ⊗ₜ[R] (1 : H) := by
    simpa only [HasDegree, map_one] using (show HasDegree π 1 (b : A) from b.property)
  rw [map_mul, hb, tensorCoeff_mul_left]
  rfl

private def invariantProjection [Fintype M] : A →ₗ[B] B where
  toFun a := ⟨degreePart π 1 a, degreePart_degree π 1 a⟩
  map_add' a b := Subtype.ext (map_add (degreePart π 1) a b)
  map_smul' b a := Subtype.ext (degreePart_mul_invariant π 1 b a)

private theorem invariantProjection_comp [Fintype M] :
    (invariantProjection π).comp (Algebra.linearMap B A) = LinearMap.id := by
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  change degreePart π 1 (b : A) = (b : A)
  rw [degreePart_eq π _ _ _ b.property, ite_eq_left rfl]

/-- The opposite-degree decompositions give a finite dual family over the invariants. -/
theorem finite_flat_of_strongGrading [Finite M] (h : StrongGrading π) :
    Module.Finite B A ∧ Module.FaithfullyFlat B A := by
  classical
  let := Fintype.ofFinite M
  choose n a b ha hb hab using h
  let I := Σ m : M, Fin (n m)
  let coeff (i : I) : A →ₗ[B] B :=
    { toFun x := ⟨a i.1 i.2 * degreePart π i.1 x, by
        change HasDegree π 1 _
        simpa only [inv_mul_cancel] using
          degree_mul π (ha i.1 i.2) (degreePart_degree π i.1 x)⟩
      map_add' x y := Subtype.ext (by dsimp; rw [map_add, mul_add])
      map_smul' c x := Subtype.ext (by
        change a i.1 i.2 * degreePart π i.1 ((c : A) * x) = (c : A) * _
        rw [degreePart_mul_invariant]
        exact mul_left_comm _ _ _) }
  let f : A →ₗ[B] (I → B) := LinearMap.pi coeff
  let g : (I → B) →ₗ[B] A :=
    ∑ i : I, (LinearMap.toSpanSingleton B A (b i.1 i.2)).comp (LinearMap.proj i)
  have hfg : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change g (fun i => coeff i x) = x
    simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.toSpanSingleton_apply]
    simp only [coeff, LinearMap.coe_mk, AddHom.coe_mk, Subalgebra.smul_def, smul_eq_mul]
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ m : M, (∑ i, a m i * b m i) * degreePart π m x := by
        simp only [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by
          ac_rfl
      _ = x := by simp only [hab, one_mul, sum_degreePart]
  have hg : Function.Surjective g := fun x => ⟨f x, DFunLike.congr_fun hfg x⟩
  refine ⟨Module.Finite.of_surjective g hg, ?_⟩
  refine (Module.FaithfullyFlat.iff_flat_and_lTensor_faithful B A).mpr
    ⟨Module.Flat.of_retract f g hfg, ?_⟩
  intro N _ _ hN
  have hi : Function.Injective ((Algebra.linearMap B A).rTensor N) := by
    apply Function.LeftInverse.injective (g := (invariantProjection π).rTensor N)
    intro t
    rw [← LinearMap.rTensor_comp_apply, invariantProjection_comp, LinearMap.rTensor_id]
    rfl
  exact (hi.comp (TensorProduct.lid B N).symm.injective).nontrivial

private def torsorMap : A ⊗[B] A →ₐ[A] A ⊗[R] H :=
  lift (Algebra.ofId A _) {
    toRingHom := (rightCoaction π).toRingHom
    commutes' b := by
      change rightCoaction π (b : A) = (b : A) ⊗ₜ[R] (1 : H)
      simpa only [HasDegree, map_one] using (show HasDegree π 1 (b : A) from b.property)
  } (fun _ _ => Commute.all _ _)

private theorem torsorMap_tmul (a b : A) :
    torsorMap π (a ⊗ₜ[B] b) = (a ⊗ₜ[R] (1 : H)) * rightCoaction π b := rfl

set_option maxHeartbeats 800000 in
/-- The canonical torsor map over the invariant ring is invertible. -/
private theorem torsorMap_bijective [Finite M] (h : StrongGrading π) :
    Function.Bijective (torsorMap π) := by
  classical
  let := Fintype.ofFinite M
  choose n a b ha hb hab using h
  let basis := (MonoidAlgebra.basis M R).baseChange A
  let inv : A ⊗[R] H →ₗ[A] A ⊗[B] A :=
    basis.constr A (fun m => ∑ i, a m i ⊗ₜ[B] b m i)
  have basis_eq (m : M) : basis m = 1 ⊗ₜ[R] χ m := by
    rw [Module.Basis.baseChange_apply]
    rfl
  have hInv (m : M) : inv (1 ⊗ₜ[R] χ m) = ∑ i, a m i ⊗ₜ[B] b m i := by
    rw [← basis_eq, Module.Basis.constr_basis]
  have rightInv : (torsorMap π).toLinearMap.comp inv = LinearMap.id := by
    apply basis.ext
    intro m
    rw [basis_eq, LinearMap.comp_apply, hInv, map_sum]
    simp only [AlgHom.toLinearMap_apply, torsorMap_tmul, LinearMap.id_apply]
    simp_rw [show ∀ i, rightCoaction π (b m i) = b m i ⊗ₜ[R] χ m from hb m,
      tmul_mul_tmul, one_mul, ← TensorProduct.sum_tmul, hab]
  have pure (x y : A) (m : M) (hy : HasDegree π m y) :
      inv (torsorMap π (x ⊗ₜ[B] y)) = x ⊗ₜ[B] y := by
    rw [torsorMap_tmul, hy, tmul_mul_tmul, one_mul]
    have hx : (x * y) • (1 ⊗ₜ[R] χ m) = (x * y) ⊗ₜ[R] χ m := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [← hx]
    rw [map_smul, hInv, Finset.smul_sum]
    calc
      _ = ∑ i, x ⊗ₜ[B] (y * (a m i * b m i)) := by
        apply Finset.sum_congr rfl
        intro i _
        let c : B := ⟨y * a m i, by
          change HasDegree π 1 _
          simpa only [mul_inv_cancel] using degree_mul π hy (ha m i)⟩
        rw [TensorProduct.smul_tmul']
        have hxa : (x * y) • a m i = c • x := by
          change (x * y) * a m i = (y * a m i) * x
          ac_rfl
        rw [hxa]
        rw [TensorProduct.smul_tmul]
        congr 1
        change (y * a m i) * b m i = y * (a m i * b m i)
        exact mul_assoc _ _ _
      _ = x ⊗ₜ[B] y := by rw [← TensorProduct.tmul_sum, ← Finset.mul_sum, hab, mul_one]
  have leftInv : Function.LeftInverse inv (torsorMap π) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [← sum_degreePart π y, TensorProduct.tmul_sum, map_sum, map_sum]
      exact Finset.sum_congr rfl fun m _ => pure x _ m (degreePart_degree π m y)
    | add x y hx hy => simp [hx, hy]
  exact ⟨leftInv.injective, fun y => ⟨inv y, DFunLike.congr_fun rightInv y⟩⟩

/-- The degree-zero algebra gives the finite faithfully flat torsor over the base. -/
theorem coordinateQuotient : CoordinateQuotient.{u} := by
  intro R A M _ _ _ _ _ _ _ _ π hπ
  classical
  let := Fintype.ofFinite M
  have h := strongGrading π hπ
  obtain ⟨hfin, hff⟩ := finite_flat_of_strongGrading π h
  have hflat : Module.Flat R ↥(invariants π) := by
    apply Module.Flat.of_retract (invariants π).val.toLinearMap
      ((invariantProjection π).restrictScalars R)
    apply LinearMap.ext
    intro b
    exact DFunLike.congr_fun (invariantProjection_comp π) b
  have hfp : Algebra.FinitePresentation R ↥(invariants π) := by
    apply Algebra.FinitePresentation.of_finiteType.mp
    exact ⟨fg_of_fg_of_fg R ↥(invariants π) A Algebra.FiniteType.out hfin.1
      Subtype.val_injective⟩
  refine ⟨orbitMap_surjective π hπ, h, hfin, hff, hflat, hfp,
    (AlgEquiv.ofBijective (torsorMap π) (torsorMap_bijective π h)).restrictScalars _, ?_⟩
  exact torsorMap_tmul π

private def contractRight {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : Y →ₗ[R] R) :
    X ⊗[R] Y →ₗ[R] X :=
  (TensorProduct.rid R X).toLinearMap.comp (f.lTensor X)

private def contractLeft {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] R) :
    X ⊗[R] Y →ₗ[R] Y :=
  (TensorProduct.lid R Y).toLinearMap.comp (f.rTensor Y)

@[simp] private theorem contractRight_tmul {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : Y →ₗ[R] R) (x : X) (y : Y) :
    contractRight f (x ⊗ₜ[R] y) = f y • x := by simp [contractRight]

@[simp] private theorem contractLeft_tmul {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] R) (x : X) (y : Y) :
    contractLeft f (x ⊗ₜ[R] y) = f x • y := by simp [contractLeft]

private def characterCoefficient (m : M) : A →ₗ[R] R :=
  ((MonoidAlgebra.basis M R).coord m).comp π.toLinearMap

private theorem degreePart_contract (m : M) (a : A) :
    degreePart π m a = contractRight (characterCoefficient π m) (comul a) := by
  classical
  unfold degreePart
  change tensorCoeff A m (rightCoaction π a) = _
  let w := ℛ R a
  rw [coaction_tmul_sum π a w, ← w.eq, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [tensorCoeff, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, characterCoefficient,
    Module.Basis.coord_apply, contractRight_tmul]
  rfl

private theorem degreePart_contract_left (h : IsCentral π) (m : M) (a : A) :
    degreePart π m a = contractLeft (characterCoefficient π m) (comul a) := by
  classical
  change tensorCoeff A m (rightCoaction π a) = _
  unfold IsCentral at h
  rw [h]
  let w := ℛ R a
  change tensorCoeff A m ((Algebra.TensorProduct.comm R H A)
    ((Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R A)) (comul a))) = _
  rw [← w.eq, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul,
    AlgHom.id_apply, tensorCoeff, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lapply_apply, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
    contractLeft_tmul, characterCoefficient, Module.Basis.coord_apply]
  rfl

private theorem comul_contract_right (f : A →ₗ[R] R) (a : A) :
    comul (contractRight f (comul a)) =
      (LinearMap.lTensor A (contractRight f ∘ₗ comul)) (comul a) := by
  have h := congrArg (contractRight (X := A ⊗[R] A) f)
    (congrArg (TensorProduct.assoc R A A A).symm (Coalgebra.coassoc_apply (R := R) a))
  rw [LinearEquiv.symm_apply_apply] at h
  let w := ℛ R a
  rw [← w.eq, map_sum, map_sum, map_sum, map_sum, map_sum] at h
  rw [← w.eq, map_sum, map_sum, map_sum]
  have hd (x : A) (t : A ⊗[R] A) :
      contractRight f ((TensorProduct.assoc R A A A).symm (x ⊗ₜ[R] t)) =
        x ⊗ₜ[R] contractRight f t := by
    induction t using TensorProduct.inductionOn with
    | tmul y z => simp [TensorProduct.tmul_smul]
    | add v w hv hw => simp [TensorProduct.tmul_add, hv, hw]
  simpa only [LinearMap.rTensor_tmul, contractRight_tmul, LinearMap.lTensor_tmul,
    hd, LinearMap.comp_apply, map_smul] using h

private theorem comul_contract_left (f : A →ₗ[R] R) (a : A) :
    comul (contractLeft f (comul a)) =
      (LinearMap.rTensor A (contractLeft f ∘ₗ comul)) (comul a) := by
  have h := congrArg (contractLeft (Y := A ⊗[R] A) f) (Coalgebra.coassoc_apply (R := R) a)
  let w := ℛ R a
  rw [← w.eq, map_sum, map_sum, map_sum, map_sum, map_sum] at h
  rw [← w.eq, map_sum, map_sum, map_sum]
  have hd (t : A ⊗[R] A) (x : A) :
      contractLeft f (TensorProduct.assoc R A A A (t ⊗ₜ[R] x)) =
        contractLeft f t ⊗ₜ[R] x := by
    induction t using TensorProduct.inductionOn with
    | tmul y z => simp [TensorProduct.smul_tmul']
    | add v w hv hw => simp [TensorProduct.add_tmul, hv, hw]
  simpa only [LinearMap.rTensor_tmul, contractLeft_tmul, LinearMap.lTensor_tmul,
    hd, LinearMap.comp_apply, map_smul] using h.symm

private theorem comul_degreePart_right (m : M) (a : A) :
    comul (degreePart π m a) = (LinearMap.lTensor A (degreePart π m)) (comul a) := by
  have hf : degreePart π m = contractRight (characterCoefficient π m) ∘ₗ comul :=
    LinearMap.ext (degreePart_contract π m)
  rw [hf, LinearMap.comp_apply, comul_contract_right]

private theorem comul_degreePart_left (h : IsCentral π) (m : M) (a : A) :
    comul (degreePart π m a) = (LinearMap.rTensor A (degreePart π m)) (comul a) := by
  have hf : degreePart π m = contractLeft (characterCoefficient π m) ∘ₗ comul :=
    LinearMap.ext (degreePart_contract_left π h m)
  rw [hf, LinearMap.comp_apply, comul_contract_left]

private theorem antipode_invariant (h : IsCentral π) (b : B) :
    HasDegree π 1 (antipode R (b : A)) := by
  let L : A →ₐ[R] A ⊗[R] H := includeLeft
  let Q : A →ₐ[R] A ⊗[R] H := includeRight.comp π.toAlgHom
  let S := antipodeAlgHom R A
  let T := antipodeAlgHom R H
  have hl : toConv (rightCoaction π) = toConv L * toConv Q := by
    apply WithConv.ext
    rw [AlgHom.convMul_def]
    change (rightCoaction π) = (lmul' R).comp ((Algebra.TensorProduct.map L Q).comp
      (Bialgebra.comulAlgHom R A))
    unfold rightCoaction
    rw [← AlgHom.comp_assoc]
    congr 1
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [L, Q]
  have hr : toConv (rightCoaction π) = toConv Q * toConv L := by
    apply WithConv.ext
    rw [AlgHom.convMul_def]
    change (rightCoaction π) = (lmul' R).comp ((Algebra.TensorProduct.map Q L).comp
      (Bialgebra.comulAlgHom R A))
    unfold IsCentral at h
    rw [h, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    congr 1
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [L, Q]
  have hπ : π.toAlgHom.comp S = T.comp π.toAlgHom := by
    have h₁ : toConv (π.toAlgHom.comp S) * toConv π.toAlgHom = 1 := by
      exact inv_mul_cancel (toConv π.toAlgHom)
    have h₂ : toConv π.toAlgHom * toConv (T.comp π.toAlgHom) = 1 := by
      have hc := congrArg (fun f : H →ₐ[R] H => toConv (f.comp π.toAlgHom))
        (WithConv.ofConv_injective.eq_iff.mpr (AlgHom.id_antipode_cancel (R := R) (A := H)))
      rw [AlgHom.convMul_comp_bialgHom_distrib] at hc
      rw [AlgHom.convOne_def] at hc
      simp only [toConv_ofConv, AlgHom.id_comp,
        AlgHom.comp_assoc, π.counitAlgHom_comp] at hc
      exact hc
    exact toConv_injective (left_inv_eq_right_inv h₁ h₂)
  let U : A ⊗[R] H →ₐ[R] A ⊗[R] H := Algebra.TensorProduct.map S T
  have huv : (toConv (rightCoaction π))⁻¹ = toConv (U.comp (rightCoaction π)) := by
    conv_rhs => rw [show rightCoaction π = (toConv L * toConv Q).ofConv from
      WithConv.ofConv_injective.eq_iff.mpr hl]
    rw [AlgHom.comp_convMul_distrib, hr, toConv_ofConv]
    refine (mul_inv_rev (toConv Q) (toConv L)).trans ?_
    change toConv (L.comp S) * toConv (Q.comp S) = _
    congr 1
    · ext x
      change S x ⊗ₜ[R] (1 : H) = S x ⊗ₜ[R] T 1
      rw [map_one]
    · rw [show Q.comp S = includeRight.comp (π.toAlgHom.comp S) from rfl, hπ]
      ext x
      change (1 : A) ⊗ₜ[R] T (π x) = S 1 ⊗ₜ[R] T (π x)
      rw [map_one]
  have hb : rightCoaction π (b : A) = (b : A) ⊗ₜ[R] (1 : H) := by
    simpa only [HasDegree, map_one] using (show HasDegree π 1 (b : A) from b.property)
  unfold HasDegree
  rw [map_one]
  have hx := DFunLike.congr_fun (WithConv.toConv_injective huv) (b : A)
  change rightCoaction π (S (b : A)) = U (rightCoaction π (b : A)) at hx
  change rightCoaction π (S (b : A)) = S (b : A) ⊗ₜ[R] (1 : H)
  rw [hx, hb]
  change S (b : A) ⊗ₜ[R] T 1 = _
  rw [map_one]

private theorem tensorMap_leftInverse
    {X Y Z W : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup W] [Module R W]
    (i : X →ₗ[R] Y) (p : Y →ₗ[R] X) (j : Z →ₗ[R] W) (q : W →ₗ[R] Z)
    (hi : Function.LeftInverse p i) (hj : Function.LeftInverse q j) :
    Function.LeftInverse (TensorProduct.map p q) (TensorProduct.map i j) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp only [TensorProduct.map_tmul, hi a, hj b]
  | add u v hu hv => simp only [map_add, hu, hv]

section

variable [Fintype M]
local notation "ιB" => Subalgebra.val (invariants π)
local notation "iB" => AlgHom.toLinearMap (Subalgebra.val (invariants π))
local notation "pB" => LinearMap.restrictScalars R (invariantProjection π)
local notation "iBB" => TensorProduct.map iB iB

private lemma invariantProjection_leftInverse :
    Function.LeftInverse pB iB := by
  intro b
  exact DFunLike.congr_fun (invariantProjection_comp π) b

private lemma tensorInclusion_injective : Function.Injective iBB :=
  (tensorMap_leftInverse iB pB iB pB (invariantProjection_leftInverse π)
    (invariantProjection_leftInverse π)).injective

private def restrictedComulLinear : B →ₗ[R] B ⊗[R] B :=
  TensorProduct.map pB pB ∘ₗ comul ∘ₗ iB

private lemma tensorInclusion_restrictedComul (h : IsCentral π) (b : B) :
    iBB (restrictedComulLinear π b) = comul (b : A) := by
  let P := degreePart π (1 : M)
  have hp : iB ∘ₗ pB = P := by
    ext a
    rfl
  change (TensorProduct.map iB iB ∘ₗ TensorProduct.map pB pB) (comul (b : A)) = _
  rw [← TensorProduct.map_comp, hp]
  have compose : TensorProduct.map P P = (P.rTensor A) ∘ₗ (P.lTensor A) := by
    rw [LinearMap.rTensor_def, LinearMap.lTensor_def, ← TensorProduct.map_comp]
    simp
  have hb : P (b : A) = (b : A) := by
    exact (invariantProjection_leftInverse π b |> congrArg Subtype.val)
  rw [compose, LinearMap.comp_apply, ← comul_degreePart_right, show
    degreePart π (1 : M) (b : A) = (b : A) from hb,
    ← comul_degreePart_left π h, show degreePart π (1 : M) (b : A) = (b : A) from hb]

private def restrictedComul (h : IsCentral π) : B →ₐ[R] B ⊗[R] B :=
  AlgHom.ofLinearMap (restrictedComulLinear π)
    ((tensorInclusion_injective π) (by
      rw [tensorInclusion_restrictedComul π h]
      change comul (R := R) (1 : A) = Algebra.TensorProduct.map ιB ιB 1
      simp only [map_one, Bialgebra.comul_one]))
    (fun b c => (tensorInclusion_injective π) (by
      rw [tensorInclusion_restrictedComul π h]
      change comul (R := R) ((b : A) * (c : A)) =
        Algebra.TensorProduct.map ιB ιB (restrictedComulLinear π b * restrictedComulLinear π c)
      rw [map_mul (Algebra.TensorProduct.map ιB ιB)]
      change _ = iBB (restrictedComulLinear π b) * iBB (restrictedComulLinear π c)
      rw [tensorInclusion_restrictedComul π h, tensorInclusion_restrictedComul π h,
        Bialgebra.comul_mul]))

private def restrictedCounit : B →ₐ[R] R :=
  (Bialgebra.counitAlgHom R A).comp ιB

private def restrictedAntipode (h : IsCentral π) : B →ₐ[R] B :=
  (antipodeAlgHom R A).comp ιB |>.codRestrict (invariants π) (antipode_invariant π h)

private theorem restrictedComul_comm (h : IsCentral π) :
    (Algebra.TensorProduct.map ιB ιB).comp (restrictedComul π h) =
      (Bialgebra.comulAlgHom R A).comp ιB :=
  AlgHom.ext (tensorInclusion_restrictedComul π h)

section
variable (h : IsCentral π)

private theorem restrictedComul_coassoc :
    (Algebra.TensorProduct.assoc R R R B B B).toAlgHom.comp
      ((Algebra.TensorProduct.map (restrictedComul π h) (AlgHom.id R B)).comp
        (restrictedComul π h)) =
    (Algebra.TensorProduct.map (AlgHom.id R B) (restrictedComul π h)).comp
      (restrictedComul π h) := by
  let Φ := TensorProduct.map iB (TensorProduct.map iB iB)
  have hΦ : Function.Injective Φ :=
    (tensorMap_leftInverse iB pB iBB (TensorProduct.map pB pB)
      (invariantProjection_leftInverse π)
      (tensorMap_leftInverse iB pB iB pB (invariantProjection_leftInverse π)
        (invariantProjection_leftInverse π))).injective
  let δ := (restrictedComul π h).toLinearMap
  let Δ := (Bialgebra.comulAlgHom R A).toLinearMap
  have hi : iBB ∘ₗ δ = Δ ∘ₗ iB :=
    LinearMap.ext (tensorInclusion_restrictedComul π h)
  have hleft : (TensorProduct.map iBB iB) ∘ₗ (LinearMap.rTensor B δ) =
      (LinearMap.rTensor A Δ) ∘ₗ iBB := by
    simp only [LinearMap.rTensor_def, ← TensorProduct.map_comp, hi, LinearMap.comp_id,
      LinearMap.id_comp]
  have hright : Φ ∘ₗ (LinearMap.lTensor B δ) = (LinearMap.lTensor A Δ) ∘ₗ iBB := by
    simp only [Φ, LinearMap.lTensor_def, ← TensorProduct.map_comp, hi, LinearMap.comp_id,
      LinearMap.id_comp]
  apply AlgHom.ext
  intro b
  apply hΦ
  change Φ (TensorProduct.assoc R B B B (δ.rTensor B (δ b))) = Φ (δ.lTensor B (δ b))
  change TensorProduct.map iB iBB (TensorProduct.assoc R B B B (δ.rTensor B (δ b))) =
    (Φ ∘ₗ (δ.lTensor B)) (δ b)
  rw [TensorProduct.map_map_assoc, hright]
  change TensorProduct.assoc R A A A (((TensorProduct.map iBB iB) ∘ₗ (δ.rTensor B)) (δ b)) =
    Δ.lTensor A (iBB (δ b))
  rw [hleft, LinearMap.comp_apply]
  rw [show iBB (δ b) = comul (b : A) from tensorInclusion_restrictedComul π h b]
  exact Coalgebra.coassoc_apply (R := R) (b : A)

private theorem restrictedComul_counit_left :
    (Algebra.TensorProduct.map (restrictedCounit π) (AlgHom.id R B)).comp (restrictedComul π h) =
      (Algebra.TensorProduct.lid R B).symm := by
  have hinj := (tensorMap_leftInverse (LinearMap.id : R →ₗ[R] R) LinearMap.id iB pB
    (fun _ => rfl) (invariantProjection_leftInverse π)).injective
  apply AlgHom.ext
  intro b
  apply hinj
  change ((Algebra.TensorProduct.map (AlgHom.id R R) ιB).comp
    (Algebra.TensorProduct.map (restrictedCounit π) (AlgHom.id R B))) (restrictedComul π h b)
    = (1 : R) ⊗ₜ[R] (b : A)
  rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]
  rw [show (Algebra.TensorProduct.map (restrictedCounit π) ιB) =
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (AlgHom.id R A)).comp
      (Algebra.TensorProduct.map ιB ιB) by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    rfl]
  rw [AlgHom.comp_apply, ← AlgHom.comp_apply (Algebra.TensorProduct.map ιB ιB),
    restrictedComul_comm π h, AlgHom.comp_apply]
  exact Coalgebra.rTensor_counit_comul (R := R) (b : A)

private theorem restrictedComul_counit_right :
    (Algebra.TensorProduct.map (AlgHom.id R B) (restrictedCounit π)).comp (restrictedComul π h) =
      (Algebra.TensorProduct.rid R R B).symm := by
  have hinj := (tensorMap_leftInverse iB pB (LinearMap.id : R →ₗ[R] R) LinearMap.id
    (invariantProjection_leftInverse π) (fun _ => rfl)).injective
  apply AlgHom.ext
  intro b
  apply hinj
  change ((Algebra.TensorProduct.map ιB (AlgHom.id R R)).comp
    (Algebra.TensorProduct.map (AlgHom.id R B) (restrictedCounit π))) (restrictedComul π h b)
    = (b : A) ⊗ₜ[R] (1 : R)
  rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]
  rw [show (Algebra.TensorProduct.map ιB (restrictedCounit π)) =
    (Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.counitAlgHom R A)).comp
      (Algebra.TensorProduct.map ιB ιB) by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    rfl]
  rw [AlgHom.comp_apply, ← AlgHom.comp_apply (Algebra.TensorProduct.map ιB ιB),
    restrictedComul_comm π h, AlgHom.comp_apply]
  exact Coalgebra.lTensor_counit_comul (R := R) (b : A)

private abbrev invariantBialgebra : Bialgebra R B :=
  Bialgebra.ofAlgHom (restrictedComul π h) (restrictedCounit π)
    (restrictedComul_coassoc π h) (restrictedComul_counit_left π h)
    (restrictedComul_counit_right π h)

private abbrev invariantHopfAlgebra : HopfAlgebra R B := by
  letI := invariantBialgebra π h
  have ha : (ιB).comp (restrictedAntipode π h) = (antipodeAlgHom R A).comp ιB := rfl
  have hmul (f g : B →ₐ[R] B) (F G : A →ₐ[R] A)
      (hf : (ιB).comp f = F.comp ιB) (hg : (ιB).comp g = G.comp ιB) :
      (ιB).comp (lift f g (fun _ _ => Commute.all _ _)) =
        (lift F G (fun _ _ => Commute.all _ _)).comp (Algebra.TensorProduct.map ιB ιB) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, lift_tmul, map_mul, Algebra.TensorProduct.map_tmul]
    rw [← AlgHom.comp_apply ιB f, ← AlgHom.comp_apply ιB g, hf, hg]
    rfl
  have comm_counit : (ιB).comp ((Algebra.ofId R B).comp (restrictedCounit π)) =
    ((Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)).comp ιB := by
    ext x
    exact (ιB).commutes (Bialgebra.counitAlgHom R A (x : A))
  refine HopfAlgebra.ofAlgHom (restrictedAntipode π h) ?_ ?_
  · apply AlgHom.ext
    intro b
    apply Subtype.val_injective
    change ((ιB).comp ((lift (restrictedAntipode π h) (AlgHom.id R B)
      (fun _ _ => Commute.all _ _)).comp (restrictedComul π h))) b =
      ((ιB).comp ((Algebra.ofId R B).comp (restrictedCounit π))) b
    rw [comm_counit, ← AlgHom.comp_assoc, hmul _ _ _ (AlgHom.id R A) ha (by simp), AlgHom.comp_assoc,
      restrictedComul_comm π h]
    have hs := congrArg (fun f : WithConv (A →ₐ[R] A) => f.ofConv (b : A))
      (AlgHom.antipode_id_cancel (R := R) (A := A))
    rw [AlgHom.convMul_apply] at hs
    exact hs
  · apply AlgHom.ext
    intro b
    apply Subtype.val_injective
    change ((ιB).comp ((lift (AlgHom.id R B) (restrictedAntipode π h)
      (fun _ _ => Commute.all _ _)).comp (restrictedComul π h))) b =
      ((ιB).comp ((Algebra.ofId R B).comp (restrictedCounit π))) b
    rw [comm_counit, ← AlgHom.comp_assoc, hmul _ _ (AlgHom.id R A) _ (by simp) ha, AlgHom.comp_assoc,
      restrictedComul_comm π h]
    have hs := congrArg (fun f : WithConv (A →ₐ[R] A) => f.ofConv (b : A))
      (AlgHom.id_antipode_cancel (R := R) (A := A))
    rw [AlgHom.convMul_apply] at hs
    exact hs

end

end

/-- Centrality allows the invariant algebra to inherit the Hopf operations. -/
theorem hopfQuotient : HopfQuotient.{u} := by
  intro R A M _ _ _ _ _ π h
  classical
  let := Fintype.ofFinite M
  let Hinv := invariantHopfAlgebra π h
  refine ⟨Hinv, ?_⟩
  let : HopfAlgebra R ↥(invariants π) := Hinv
  exact ⟨BialgHom.ofAlgHom (invariants π).val rfl (restrictedComul_comm π h), fun _ => rfl⟩

section SchemeQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

variable [Fintype M]

private abbrev quotientInclusion (h : IsCentral π) :
    letI : HopfAlgebra R ↥(invariants π) := invariantHopfAlgebra π h
    ↥(invariants π) →ₐc[R] A :=
  letI : HopfAlgebra R ↥(invariants π) := invariantHopfAlgebra π h
  BialgHom.ofAlgHom (invariants π).val rfl (restrictedComul_comm π h)

/-- The spectrum of the degree-zero ring carries the finite fppf torsor projection. -/
theorem spectrumTorsor [IsNoetherianRing R] [Algebra.FinitePresentation R A] [Module.Flat R A]
    (h : IsCentral π) (hs : Function.Surjective π) :
    let : HopfAlgebra R ↥(invariants π) := invariantHopfAlgebra π h
    IsRightTorsor (quotientInclusion π h) π := by
  let : HopfAlgebra R ↥(invariants π) := invariantHopfAlgebra π h
  obtain ⟨_, hg, hf, hff, _, hp, _⟩ := coordinateQuotient π hs
  let : Algebra.FinitePresentation R ↥(invariants π) := hp
  let : IsNoetherianRing ↥(invariants π) :=
    Algebra.FiniteType.isNoetherianRing R ↥(invariants π)
  let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
  change IsFinite q ∧ Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
    IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)))
      (Spec.map (CommRingCat.ofHom (rightCoaction π).toRingHom)) q q
  have hn : (algebraMap B A).Finite := RingHom.finite_algebraMap.mpr hf
  have hqfin : IsFinite q := (IsFinite.SpecMap_iff _).mpr hn
  have hqff : Flat q ∧ Surjective q :=
    (flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  have hqfp : LocallyOfFinitePresentation q :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.FinitePresentation.of_finiteType.mp hn.finiteType)
  refine ⟨hqfin, hqff.1, hqff.2, hqfp, ?_⟩
  let e := AlgEquiv.ofBijective (torsorMap π) (torsorMap_bijective π hg)
  let f := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫ (pullbackSpecIso B A A).symm
  have he (a b : A) : e (a ⊗ₜ[B] b) = (a ⊗ₜ[R] (1 : H)) * rightCoaction π b :=
    torsorMap_tmul π a b
  have hfst : f.hom ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] H)) := by
    change Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
      (pullbackSpecIso B A A).inv ≫ pullback.fst q q = _
    rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
    congr 1
    ext a
    change e (a ⊗ₜ[B] 1) = a ⊗ₜ[R] (1 : H)
    rw [he, map_one, mul_one]
  have hsnd : f.hom ≫ pullback.snd q q =
      Spec.map (CommRingCat.ofHom (rightCoaction π).toRingHom) := by
    change Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
      (pullbackSpecIso B A A).inv ≫ pullback.snd q q = _
    rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
    congr 1
    ext a
    change e (1 ⊗ₜ[B] a) = rightCoaction π a
    rw [he, ← Algebra.TensorProduct.one_def, one_mul]
  refine IsPullback.of_iso_pullback ⟨?_⟩ f hfst hsnd
  simp only [← hfst, ← hsnd, Category.assoc, pullback.condition]

end SchemeQuotient

section TorusQuotient

variable {X : Type u} [CommGroup X] [Fintype M] (z : X →* M)

local notation "D" => MonoidAlgebra R X
local notation "D₀" => MonoidAlgebra R (MonoidHom.ker z)
local notation "ψ" => MonoidAlgebra.mapDomainBialgHom R z
local notation "e₀" => MonoidAlgebra.mapDomainBialgHom R (Subgroup.subtype (MonoidHom.ker z))

private def torusProjection : D →ₗ[R] D₀ := by
  classical
  exact (MonoidAlgebra.basis X R).constr R fun x =>
    if hx : z x = 1 then MonoidAlgebra.of R (MonoidHom.ker z) ⟨x, hx⟩ else 0

omit [Fintype M] in
open Classical in
private theorem torusProjection_of (x : X) :
    torusProjection (R := R) z (MonoidAlgebra.of R X x) =
      (if hx : z x = 1 then MonoidAlgebra.of R (MonoidHom.ker z) ⟨x, hx⟩ else 0) := by
  classical
  exact Module.Basis.constr_basis _ _ _ _

omit [Fintype M] in
private theorem torusProjection_leftInverse :
    Function.LeftInverse (torusProjection (R := R) z) (e₀ : D₀ →ₐc[R] D) := by
  have h : (torusProjection (R := R) z).comp (e₀ : D₀ →ₐc[R] D).toLinearMap =
      LinearMap.id := by
    apply (MonoidAlgebra.basis (MonoidHom.ker z) R).ext
    intro x
    change torusProjection (R := R) z (e₀ (MonoidAlgebra.of R (MonoidHom.ker z) x)) =
      MonoidAlgebra.of R (MonoidHom.ker z) x
    rw [show e₀ (MonoidAlgebra.of R (MonoidHom.ker z) x) =
      MonoidAlgebra.of R X (x : X) from MonoidAlgebra.mapDomainBialgHom_single ..,
      torusProjection_of]
    rw [dite_eq_left (show z (x : X) = 1 from x.property)]
  exact DFunLike.congr_fun h

omit [Fintype M] in
private theorem torusProjection_degreePart (s : D) :
    (e₀ : D₀ →ₐc[R] D) (torusProjection (R := R) z s) = degreePart ψ 1 s := by
  classical
  suffices (e₀ : D₀ →ₐc[R] D).toLinearMap.comp (torusProjection (R := R) z) =
      degreePart ψ 1 by
    exact DFunLike.congr_fun this s
  apply (MonoidAlgebra.basis X R).ext
  intro x
  let χx := MonoidAlgebra.of R X x
  have χx_homogeneous : HasDegree ψ (z x) χx := by
    change (Algebra.TensorProduct.map (AlgHom.id R D) (ψ).toAlgHom) (comul χx) = _
    rw [(MonoidAlgebra.isGroupLikeElem_of (R := R) x).comul_eq_tmul_self,
      Algebra.TensorProduct.map_tmul]
    change _ ⊗ₜ[R] ψ (MonoidAlgebra.single x 1) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    rfl
  change e₀ (torusProjection (R := R) z χx) = degreePart ψ 1 χx
  rw [torusProjection_of, degreePart_eq _ _ _ _ χx_homogeneous]
  split_ifs <;> simp [χx, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainBialgHom_single]

omit [Fintype M] in
private theorem torus_degreePart_comm (t : A →ₐc[R] D) (m : M) (a : A) :
    t (degreePart ((ψ).comp t) m a) = degreePart ψ m (t a) := by
  let F : A ⊗[R] H →ₐ[R] D ⊗[R] H :=
    Algebra.TensorProduct.map t.toAlgHom (AlgHom.id R H)
  have hcoaction : (rightCoaction ψ).comp t.toAlgHom =
      F.comp (rightCoaction ((ψ).comp t)) := by
    unfold rightCoaction
    rw [AlgHom.comp_assoc, ← t.map_comp_comulAlgHom, ← AlgHom.comp_assoc,
      ← Algebra.TensorProduct.map_comp, ← AlgHom.comp_assoc,
      ← Algebra.TensorProduct.map_comp]
    rfl
  have h := DFunLike.congr_fun hcoaction a
  change rightCoaction ψ (t a) = F (rightCoaction ((ψ).comp t) a) at h
  change t (tensorCoeff A m (rightCoaction ((ψ).comp t) a)) =
    tensorCoeff D m (rightCoaction ψ (t a))
  rw [h]
  generalize (rightCoaction ((ψ).comp t) a) = w
  classical
  induction w using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [F, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorCoeff,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    exact (map_smul t.toLinearMap _ _)
  | add s q hs hq => simp only [map_add, hs, hq]

private abbrev torusRestriction (t : A →ₐc[R] D) : A →ₐc[R] H := (ψ).comp t

omit [Fintype M] in
set_option maxHeartbeats 800000 in
private theorem torusProjection_restriction (t : A →ₐc[R] D)
    (b : invariants (R := R) (A := A) (torusRestriction z t)) :
    (e₀ : D₀ →ₐc[R] D) (torusProjection (R := R) z (t (b : A))) = t (b : A) := by
  have hb : HasDegree (torusRestriction z t) 1 (b : A) := b.property
  have hd : degreePart (torusRestriction z t) 1 (b : A) = (b : A) := by
    rw [degreePart_eq _ _ _ _ hb, ite_eq_left rfl]
  calc
    _ = degreePart ψ 1 (t (b : A)) := torusProjection_degreePart z _
    _ = t (degreePart (torusRestriction z t) 1 (b : A)) :=
      (torus_degreePart_comm z t 1 (b : A)).symm
    _ = _ := congrArg t hd

private abbrev TorusInvariants (t : A →ₐc[R] D) : Type u :=
  invariants (R := R) (A := A) (torusRestriction z t)

private def quotientTorusAlgHom (t : A →ₐc[R] D) : TorusInvariants z t
    →ₐ[R] MonoidAlgebra R (MonoidHom.ker z) := by
  let f : TorusInvariants z t →ₗ[R] D₀ := (torusProjection (R := R) z).comp
    (t.toLinearMap.comp (invariants (torusRestriction z t)).val.toLinearMap)
  have hf (b : TorusInvariants z t) : (e₀ : D₀ →ₐc[R] D) (f b) = t (b : A) :=
    torusProjection_restriction z t b
  refine AlgHom.ofLinearMap f ?_ ?_
  · apply (torusProjection_leftInverse (R := R) z).injective
    rw [hf, map_one (e₀ : D₀ →ₐc[R] D)]
    exact map_one t
  · intro a b
    apply (torusProjection_leftInverse (R := R) z).injective
    rw [map_mul (e₀ : D₀ →ₐc[R] D), hf, hf, hf]
    exact map_mul t (a : A) (b : A)

omit [Fintype M] in
private theorem quotientTorusAlgHom_factors (t : A →ₐc[R] D) :
    (e₀ : D₀ →ₐc[R] D).toAlgHom.comp (quotientTorusAlgHom z t) =
      t.toAlgHom.comp (invariants (torusRestriction z t)).val :=
  AlgHom.ext (torusProjection_restriction z t)

private theorem quotientTorusAlgHom_surjective (t : A →ₐc[R] D) (ht : Function.Surjective t) :
    Function.Surjective (quotientTorusAlgHom z t) := by
  intro y
  obtain ⟨a, ha⟩ := ht (e₀ y)
  refine ⟨⟨degreePart (torusRestriction z t) 1 a, degreePart_degree (torusRestriction z t) 1 a⟩, ?_⟩
  change torusProjection (R := R) z (t (degreePart (torusRestriction z t) 1 a)) = y
  rw [torus_degreePart_comm, ha, ← torusProjection_degreePart, torusProjection_leftInverse,
    torusProjection_leftInverse]

/-- The restrictions of invariant functions to the source torus give exactly the group
algebra of the kernel of the character restriction. -/
theorem quotientTorus (t : A →ₐc[R] D) (ht : Function.Surjective t)
    (h : IsCentral (torusRestriction z t)) :
    let : HopfAlgebra R (TorusInvariants z t) := invariantHopfAlgebra (torusRestriction z t) h
    ∃ t₀ : TorusInvariants z t →ₐc[R] D₀,
      (e₀).comp t₀ = t.comp (quotientInclusion (torusRestriction z t) h) ∧
        Function.Surjective t₀ := by
  let : HopfAlgebra R (TorusInvariants z t) := invariantHopfAlgebra (torusRestriction z t) h
  let t₀ := quotientTorusAlgHom z t
  let incl : D₀ →ₐc[R] D := e₀
  let B₀ := TorusInvariants z t
  let j : B₀ →ₐc[R] A := quotientInclusion (torusRestriction z t) h
  have ht₀ : incl.toAlgHom.comp t₀ = t.toAlgHom.comp j.toAlgHom :=
    quotientTorusAlgHom_factors z t
  have hc : (Bialgebra.counitAlgHom R D₀).comp t₀ = Bialgebra.counitAlgHom R B₀ := by
    rw [← incl.counitAlgHom_comp, AlgHom.comp_assoc, ht₀,
      ← AlgHom.comp_assoc, t.counitAlgHom_comp, j.counitAlgHom_comp]
  have hd : (Algebra.TensorProduct.map t₀ t₀).comp (Bialgebra.comulAlgHom R B₀) =
      (Bialgebra.comulAlgHom R D₀).comp t₀ := by
    have hi : Function.Injective (Algebra.TensorProduct.map incl.toAlgHom incl.toAlgHom) :=
      (tensorMap_leftInverse incl.toLinearMap (torusProjection (R := R) z)
        incl.toLinearMap (torusProjection (R := R) z) (torusProjection_leftInverse z)
        (torusProjection_leftInverse z)).injective
    suffices (Algebra.TensorProduct.map incl.toAlgHom incl.toAlgHom).comp
        ((Algebra.TensorProduct.map t₀ t₀).comp (Bialgebra.comulAlgHom R B₀)) =
        (Algebra.TensorProduct.map incl.toAlgHom incl.toAlgHom).comp
          ((Bialgebra.comulAlgHom R D₀).comp t₀) by
      exact AlgHom.ext fun b => hi (DFunLike.congr_fun this b)
    rw [← AlgHom.comp_assoc _ _ (Bialgebra.comulAlgHom R B₀),
      ← Algebra.TensorProduct.map_comp, ht₀, Algebra.TensorProduct.map_comp,
      AlgHom.comp_assoc, j.map_comp_comulAlgHom, ← AlgHom.comp_assoc,
      t.map_comp_comulAlgHom, AlgHom.comp_assoc, ← AlgHom.comp_assoc _ _ t₀,
      incl.map_comp_comulAlgHom, AlgHom.comp_assoc, ht₀]
  refine ⟨BialgHom.ofAlgHom t₀ hc hd, ?_, quotientTorusAlgHom_surjective z t ht⟩
  apply DFunLike.ext
  intro b
  change incl (t₀ b) = t (j b)
  exact DFunLike.congr_fun ht₀ b

end TorusQuotient

section RankOne

open CategoryTheory
variable {C : Type u} [CommRing C] [HopfAlgebra R C]

/-- Composition with a Hopf algebra map gives the induced rank-one morphism. -/
def pushforwardRankOne (j : C →ₐc[R] A) (r : RankOneMap R A) : RankOneMap R C where
  hom S :=
    { toFun := fun w => toConv ((r.hom S w).ofConv.comp j.toAlgHom)
      map_one' := by
        rw [map_one, AlgHom.convOne_def]
        simp only [AlgHom.comp_assoc, j.counitAlgHom_comp]
        rfl
      map_mul' := fun x y => by
        rw [map_mul, AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv] }
  naturality f w := by
    change ((r.hom _ (Matrix.SpecialLinearGroup.map f.hom.toRingHom w)).ofConv).comp j.toAlgHom =
      f.hom.comp ((r.hom _ w).ofConv.comp j.toAlgHom)
    rw [r.naturality, AlgHom.comp_assoc]

private theorem cocharacterEval_map {X Y : Type u} [CommGroup X] [CommGroup Y]
    (f : Y →* X) (c : X →* Multiplicative ℤ) (S : CommAlgCat.{u} R) (s : Sˣ) :
    (cocharacterEval c S s).comp (MonoidAlgebra.mapDomainBialgHom R f).toAlgHom =
      cocharacterEval (c.comp f) S s := by
  apply MonoidAlgebra.algHom_ext
  · intro y
    change (cocharacterEval c S s) (MonoidAlgebra.mapDomainBialgHom R f
      (MonoidAlgebra.single y 1)) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    change (cocharacterEval c S s) (MonoidAlgebra.of R X (f y)) =
      (cocharacterEval (c.comp f) S s) (MonoidAlgebra.of R Y y)
    simp only [cocharacterEval, MonoidAlgebra.lift_of]
    rfl
  · ext

/-- The induced rank-one map has the original root parameters and the image coroot. -/
theorem rankOneCompatibility_pushforward {X Y : Type u} [CommGroup X] [CommGroup Y]
    (j : C →ₐc[R] A) (t : A →ₐc[R] MonoidAlgebra R X)
    (t₀ : C →ₐc[R] MonoidAlgebra R Y) (f : Y →* X)
    (ht : (MonoidAlgebra.mapDomainBialgHom R f).comp t₀ = t.comp j)
    {x y : A →ₐ[R] Polynomial R} {c : X →* Multiplicative ℤ} {r : RankOneMap R A}
    (h : RankOneCompatibility t x y c r) :
    RankOneCompatibility t₀ (x.comp j.toAlgHom) (y.comp j.toAlgHom)
      (c.comp f) (pushforwardRankOne j r) := by
  constructor
  · intro S a
    obtain ⟨hx, hy⟩ := h.1 S a
    constructor
    · change (r.hom S (Specs.IntegralRootRelations.upper a)).ofConv.comp j.toAlgHom = _
      rw [hx, AlgHom.comp_assoc]
    · change (r.hom S (Specs.IntegralRootRelations.lower a)).ofConv.comp j.toAlgHom = _
      rw [hy, AlgHom.comp_assoc]
  · intro S s
    change (r.hom S (Specs.IntegralRootRelations.diagonal s)).ofConv.comp j.toAlgHom = _
    have htf : (MonoidAlgebra.mapDomainBialgHom R f).toAlgHom.comp t₀.toAlgHom =
        t.toAlgHom.comp j.toAlgHom := congrArg BialgHom.toAlgHom ht
    rw [h.2, AlgHom.comp_assoc, ← htf, ← AlgHom.comp_assoc, cocharacterEval_map]

end RankOne

/-- The character kernel of a finite diagonalizable subgroup of a split torus
is again a finite free lattice. -/
theorem characterKernel_finite_free {X : Type u} [CommGroup X] [Module.Free ℤ (Additive X)]
    [Module.Finite ℤ (Additive X)] (z : X →* M) :
    Module.Free ℤ (Additive ↥z.ker) ∧ Module.Finite ℤ (Additive ↥z.ker) := by
  let f : Additive ↥z.ker →ₗ[ℤ] Additive X := z.ker.subtype.toAdditive.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  let : Module.Finite ℤ (Additive ↥z.ker) := Module.Finite.of_injective f hf
  let : Module.IsTorsionFree ℤ (Additive ↥z.ker) := Function.Injective.moduleIsTorsionFree f hf (map_smul f)
  exact ⟨inferInstance, inferInstance⟩

end

section Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

private theorem isPullback_of_torsor_relations
    {W U V G Q : Scheme.{u}} {p r : W ⟶ U} {v : U ⟶ V} {i : U ⟶ G}
    {j : V ⟶ Q} {q : G ⟶ Q}
    (hc : v ≫ j = i ≫ q) (hU : IsPullback p r v v)
    (hG : IsPullback p (r ≫ i) (v ≫ j) q)
    [Surjective v] [Flat v] [QuasiCompact v] : IsPullback v i j q := by
  let D := pullback j q
  let f : U ⟶ D := pullback.lift v i hc
  have hfst : f ≫ pullback.fst j q = v := pullback.lift_fst _ _ _
  have hsnd : f ≫ pullback.snd j q = i := pullback.lift_snd _ _ _
  have hD : IsPullback p (r ≫ f) v (pullback.fst j q) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd j q) (v₂₂ := j)
    · simpa only [Category.assoc, hsnd] using hG
    · simpa only [Category.assoc, hfst] using hU.w
    · exact IsPullback.of_hasPullback j q
  have hPB : IsPullback (𝟙 W) r (r ≫ f) f := by
    apply IsPullback.of_right (h₁₂ := p) (h₂₂ := pullback.fst j q) (v₁₃ := v)
    · simpa only [Category.id_comp, hfst] using hU
    · simp
    · exact hD
  have hf : IsIso f := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    hPB ⟨⟨MorphismProperty.of_isPullback hD inferInstance,
      MorphismProperty.of_isPullback hD inferInstance⟩,
      MorphismProperty.of_isPullback hD inferInstance⟩
    (by change IsIso (𝟙 W); infer_instance)
  exact IsPullback.of_iso_pullback ⟨hc⟩ (asIso f) hfst hsnd

section Products

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

private theorem tensor_fst_isPullback {X Y : C} (f : X ⟶ Y) (Z : C) :
    IsPullback (fst X Z) (f ⊗ₘ 𝟙 Z) f (fst Y Z) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.isLimitAux' _ fun s => ?_⟩⟩
  refine ⟨CartesianMonoidalCategory.lift s.fst (s.snd ≫ snd Y Z), by simp, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simpa using s.condition
    · simp
  · intro m h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₁
    · have h := congrArg (fun a => a ≫ snd Y Z) h₂
      simpa using h

private def middleProjection (N T P : C) : N ⊗ (T ⊗ P) ⟶ T :=
  snd N (T ⊗ P) ≫ fst T P

private theorem middleProjection_isPullback (N P : C) {T T₀ : C} (q : T ⟶ T₀) :
    IsPullback (middleProjection N T P) (𝟙 N ⊗ₘ (q ⊗ₘ 𝟙 P)) q
      (middleProjection N T₀ P) := by
  refine ⟨⟨by simp [middleProjection]⟩, ⟨PullbackCone.isLimitAux' _ fun s => ?_⟩⟩
  simp only [PullbackCone.mk_fst, PullbackCone.mk_snd]
  let l := CartesianMonoidalCategory.lift
    (s.snd ≫ fst N (T₀ ⊗ P)) (CartesianMonoidalCategory.lift s.fst
      (s.snd ≫ snd N (T₀ ⊗ P) ≫ snd T₀ P))
  refine ⟨l, by simp [l, middleProjection], ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simp [l]
    · apply CartesianMonoidalCategory.hom_ext
      · simpa [l, middleProjection] using s.condition
      · simp [l]
  · intro m h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun a => a ≫ fst N (T₀ ⊗ P)) h₂
      simpa [l] using h
    · apply CartesianMonoidalCategory.hom_ext
      · simpa [l, middleProjection] using h₁
      · have h := congrArg (fun a => a ≫ snd N (T₀ ⊗ P) ≫ snd T₀ P) h₂
        simpa [l] using h

end Products

private def quotientCoforkOfCover {C : Type*} [Category C]
    (J : GrothendieckTopology C) [J.Subcanonical] {W X Y : C}
    {left right : W ⟶ X} {q : X ⟶ Y} (h : IsPullback left right q q)
    (hcover : Sieve.generate (Presieve.singleton q) ∈ J Y) :
    IsColimit (Cofork.ofπ (J.yoneda.map q) (f := J.yoneda.map left) (g := J.yoneda.map right)
      (by simpa only [← Functor.map_comp] using congrArg J.yoneda.map h.w)) := by
  refine Cofork.IsColimit.mk' _ fun s => ?_
  have hs := ((isSheaf_iff_isSheaf_of_type _ _).mp s.pt.property).isSheafFor _ hcover
  rw [Presieve.isSheafFor_singleton] at hs
  have hex := hs (J.yonedaEquiv s.π) (fun {Z} a b hab => by
    let v := h.lift a b hab
    have hA : v ≫ left = a := h.lift_fst a b hab
    have hB : v ≫ right = b := h.lift_snd a b hab
    rw [J.yonedaEquiv_naturality, J.yonedaEquiv_naturality]
    congr 1
    rw [← hA, ← hB, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, s.condition])
  let x := hex.exists.choose
  have hx := hex.exists.choose_spec
  refine ⟨J.yonedaEquiv.symm x, ?_, ?_⟩
  · change J.yoneda.map q ≫ J.yonedaEquiv.symm x = s.π
    apply J.yonedaEquiv.injective
    rw [← J.yonedaEquiv_naturality, Equiv.apply_symm_apply, hx]
  · intro f hf
    change J.yoneda.map q ≫ f = s.π at hf
    apply J.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply hex.unique _ hx
    rw [J.yonedaEquiv_naturality]
    exact congrArg J.yonedaEquiv hf

private lemma singleton_mem_fppfOver {S : Scheme.{u}} {X Y : Over S} (q : X ⟶ Y)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Sieve.generate (Presieve.singleton q) ∈ (Scheme.fppfTopology.over S) Y := by
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0},
    ← Sieve.ofArrows, Sieve.overEquiv_ofArrows, Sieve.ofArrows, Presieve.ofArrows_pUnit.{0}]
  exact Precoverage.generate_mem_toGrothendieck q.left.singleton_mem_fppfPrecoverage

section Spectra

variable {R A M : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup M]
variable (π : A →ₐc[R] MonoidAlgebra R M)

local notation "H" => MonoidAlgebra R M
private abbrev SpecOver (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R B))

private abbrev specProductIso (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] :
    SpecOver R B ⊗ SpecOver R C ≅ SpecOver R (B ⊗[R] C) :=
  Over.isoMk (pullbackSpecIso R B C) (pullbackSpecIso_hom_base R B C)

private theorem specProductIso_fst (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] : (specProductIso R B C).hom ≫
    spectrumOfAlgHom (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C) = fst _ _ :=
  Over.OverMorphism.ext (pullbackSpecIso_hom_fst R B C)

private theorem specProductIso_snd (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] : (specProductIso R B C).hom ≫
    spectrumOfAlgHom (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C) = snd _ _ :=
  Over.OverMorphism.ext (pullbackSpecIso_hom_snd R B C)

private theorem spectrumOfAlgHom_comp {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D] (f : B →ₐ[R] C) (g : C →ₐ[R] D) :
    spectrumOfAlgHom (g.comp f) = spectrumOfAlgHom g ≫ spectrumOfAlgHom f := by
  exact Functor.map_comp (algSpec (CommRingCat.of R))
    (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op

private theorem spectrumOfHopfHom_comp {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R D] (f : B →ₐc[R] C) (g : C →ₐc[R] D) :
    spectrumOfHopfHom (g.comp f) = spectrumOfHopfHom g ≫ spectrumOfHopfHom f := by
  exact Functor.map_comp (hopfSpec (CommRingCat.of R))
    (CommHopfAlgCat.ofHom g).op (CommHopfAlgCat.ofHom f).op

private theorem eval_comul {B : Type u} [CommRing B] [Algebra R B] (f g : A →ₐ[R] B) :
    (toConv f * toConv g).ofConv =
      (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom R A) := by
  simp only [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp

private abbrev spectrumPoint {C : Type u} [CommRing C] [Algebra R C] (f : A →ₐ[R] C) :
    SpecOver R C ⟶ (HopfSpectrum R A).X :=
  spectrumOfAlgHom f

private theorem rightCoaction_product :
    (specProductIso R A H).hom ≫ spectrumOfAlgHom (rightCoaction π) =
      fst (HopfSpectrum R A).X (HopfSpectrum R H).X *
        (snd _ _ ≫ (spectrumOfHopfHom π).hom.hom) := by
  let f : A →ₐ[R] A ⊗[R] H := Algebra.TensorProduct.includeLeft
  let g : A →ₐ[R] A ⊗[R] H := Algebra.TensorProduct.includeRight.comp π.toAlgHom
  have hconv : (toConv f * toConv g).ofConv = rightCoaction π := by
    rw [eval_comul]
    unfold rightCoaction
    congr 1
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [f, g]
  change (specProductIso R A H).hom ≫ spectrumPoint (rightCoaction π) = _
  have hspec : spectrumPoint (rightCoaction π) = spectrumPoint f * spectrumPoint g := by
    rw [← hconv]
    exact (Spec.mapMulEquiv (R := R)).map_mul (toConv f) (toConv g)
  rw [hspec, MonObj.comp_mul]
  congr 1
  · exact specProductIso_fst R A H
  · change (specProductIso R A H).hom ≫ spectrumOfAlgHom g =
      snd _ _ ≫ (spectrumOfHopfHom π).hom.hom
    rw [show g = Algebra.TensorProduct.includeRight.comp π.toAlgHom from rfl,
      spectrumOfAlgHom_comp, ← Category.assoc, specProductIso_snd]
    rfl

private theorem rightTorsor_over {B : Type u} [CommRing B] [HopfAlgebra R B]
    (j : B →ₐc[R] A) (h : IsRightTorsor j π) :
    IsPullback (fst (HopfSpectrum R A).X (HopfSpectrum R H).X)
      (fst _ _ * (snd _ _ ≫ (spectrumOfHopfHom π).hom.hom))
      (spectrumOfHopfHom j).hom.hom (spectrumOfHopfHom j).hom.hom := by
  let F := Over.forget (Spec (CommRingCat.of R))
  apply IsPullback.of_map_of_faithful F
  refine h.2.2.2.2.of_iso' (F.mapIso (specProductIso R A H))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (congrArg (fun f : _ ⟶ (HopfSpectrum R A).X => f.left)
      (specProductIso_fst R A H)).trans (Category.comp_id _).symm
  · exact (congrArg (fun f : _ ⟶ (HopfSpectrum R A).X => f.left)
      (rightCoaction_product π)).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- A finite right torsor presents the quotient in the fppf sheaf category over the base. -/
def rightTorsorFppfQuotient {B : Type u} [CommRing B] [HopfAlgebra R B]
    (j : B →ₐc[R] A) (h : IsRightTorsor j π) :
    let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
    let p := fst (HopfSpectrum R A).X (HopfSpectrum R H).X
    let a := p * (snd _ _ ≫ (spectrumOfHopfHom π).hom.hom)
    let q := (spectrumOfHopfHom j).hom.hom
    IsColimit (Cofork.ofπ (J.yoneda.map q) (f := J.yoneda.map p) (g := J.yoneda.map a)
      (by simpa only [← Functor.map_comp] using congrArg J.yoneda.map (rightTorsor_over π j h).w)) := by
  let : Flat (spectrumOfHopfHom j).hom.hom.left := h.2.1
  let : Surjective (spectrumOfHopfHom j).hom.hom.left := h.2.2.1
  let : LocallyOfFinitePresentation (spectrumOfHopfHom j).hom.hom.left := h.2.2.2.1
  exact quotientCoforkOfCover _ (rightTorsor_over π j h) (singleton_mem_fppfOver _)

private theorem central_convolution {C : Type u} [CommRing C] [Algebra R C]
    (h : IsCentral π) (f : A →ₐ[R] C) (s : H →ₐ[R] C) :
    toConv f * toConv (s.comp π.toAlgHom) = toConv (s.comp π.toAlgHom) * toConv f := by
  let l : A ⊗[R] H →ₐ[R] C := Algebra.TensorProduct.lift f s (fun _ _ => Commute.all _ _)
  have hl : l.comp (Algebra.TensorProduct.map (AlgHom.id R A) π.toAlgHom) =
      Algebra.TensorProduct.lift f (s.comp π.toAlgHom) (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [l]
  have hr : l.comp ((Algebra.TensorProduct.comm R H A).toAlgHom.comp
      (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R A))) =
      Algebra.TensorProduct.lift (s.comp π.toAlgHom) f (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [l, mul_comm]
  apply ofConv_injective
  rw [eval_comul, eval_comul, ← hl, ← hr, AlgHom.comp_assoc, AlgHom.comp_assoc]
  exact congrArg l.comp h

private theorem central_translation (h : IsCentral π) {Y : OverBase R}
    (a : Y ⟶ (HopfSpectrum R A).X) (b : Y ⟶ (HopfSpectrum R H).X) :
    a * (b ≫ (spectrumOfHopfHom π).hom.hom) = (b ≫ (spectrumOfHopfHom π).hom.hom) * a := by
  let f : A →ₐ[R] A ⊗[R] H := Algebra.TensorProduct.includeLeft
  let s : H →ₐ[R] A ⊗[R] H := Algebra.TensorProduct.includeRight
  let z := (spectrumOfHopfHom π).hom.hom
  have hComm := congrArg (Spec.mapMulEquiv (R := R) (S := A) (T := A ⊗[R] H))
    (central_convolution π h f s)
  simp only [map_mul] at hComm
  change spectrumPoint f * spectrumPoint (s.comp π.toAlgHom) =
    spectrumPoint (s.comp π.toAlgHom) * spectrumPoint f at hComm
  have hRight :
      (specProductIso R A H).hom ≫ spectrumPoint (s.comp π.toAlgHom) = snd _ _ ≫ z := by
    change (specProductIso R A H).hom ≫ spectrumOfAlgHom (s.comp π.toAlgHom) = _
    rw [spectrumOfAlgHom_comp, ← Category.assoc, specProductIso_snd]
    rfl
  have hLeft : (specProductIso R A H).hom ≫ spectrumPoint f = fst _ _ :=
    specProductIso_fst R A H
  have hProduct := congrArg ((specProductIso R A H).hom ≫ ·) hComm
  simp only [MonObj.comp_mul, hLeft, hRight] at hProduct
  let G := (HopfSpectrum R A).X
  let Z := (HopfSpectrum R H).X
  change (fst G Z * (snd G Z ≫ z) : G ⊗ Z ⟶ G) =
    (snd G Z ≫ z) * fst G Z at hProduct
  have hPair := congrArg (fun f : G ⊗ Z ⟶ G => CartesianMonoidalCategory.lift a b ≫ f) hProduct
  have hF : CartesianMonoidalCategory.lift a b ≫ fst G Z = a :=
    CartesianMonoidalCategory.lift_fst _ _
  have hS : CartesianMonoidalCategory.lift a b ≫ snd G Z ≫ z = b ≫ z := by
    rw [← Category.assoc]
    exact congrArg (· ≫ z) (CartesianMonoidalCategory.lift_snd a b)
  simpa only [MonObj.comp_mul, hF, hS] using hPair

end Spectra

section Cell

variable {R : Type u} [CommRing R]

private def markedCell {T G : Grp (OverBase R)} (t : T ⟶ G)
    {N P : OverBase R} (l : N ⟶ G.X) (p : P ⟶ G.X) :
    N ⊗ (T.X ⊗ P) ⟶ G.X :=
  (fst N (T.X ⊗ P) ≫ l) *
    (snd N (T.X ⊗ P) ≫ ((fst T.X P ≫ t.hom.hom) * (snd T.X P ≫ p)))

private def translateCell {T Z : Grp (OverBase R)} (e : Z ⟶ T) (N P : OverBase R) :
    (N ⊗ (T.X ⊗ P)) ⊗ Z.X ⟶ N ⊗ (T.X ⊗ P) :=
  let U := N ⊗ (T.X ⊗ P)
  let u := fst U Z.X
  let z := snd U Z.X
  CartesianMonoidalCategory.lift (u ≫ fst N (T.X ⊗ P))
    (CartesianMonoidalCategory.lift
      ((u ≫ middleProjection N T.X P) * (z ≫ e.hom.hom))
      (u ≫ snd N (T.X ⊗ P) ≫ snd T.X P))

private theorem translateCell_relation {T T₀ Z : Grp (OverBase R)}
    (d : T ⟶ T₀) (e : Z ⟶ T) (N P : OverBase R)
    (h : IsPullback (fst T.X Z.X) (fst T.X Z.X * (snd T.X Z.X ≫ e.hom.hom)) d.hom.hom d.hom.hom) :
    IsPullback (fst (N ⊗ (T.X ⊗ P)) Z.X) (translateCell e N P)
      (𝟙 N ⊗ₘ (d.hom.hom ⊗ₘ 𝟙 P)) (𝟙 N ⊗ₘ (d.hom.hom ⊗ₘ 𝟙 P)) := by
  let p := middleProjection N T.X P
  let v := 𝟙 N ⊗ₘ (d.hom.hom ⊗ₘ 𝟙 P)
  have hp := middleProjection_isPullback N P d.hom.hom
  have hfull := (tensor_fst_isPullback p Z.X).flip.paste_horiz h.flip
  have hmid : translateCell e N P ≫ p =
      (p ⊗ₘ 𝟙 Z.X) ≫ (fst T.X Z.X * (snd T.X Z.X ≫ e.hom.hom)) := by
    simp [translateCell, p, middleProjection, MonObj.comp_mul]
  have hcomm : fst (N ⊗ (T.X ⊗ P)) Z.X ≫ v = translateCell e N P ≫ v := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [v, translateCell]
    · apply CartesianMonoidalCategory.hom_ext
      · have H := congrArg ((p ⊗ₘ 𝟙 Z.X) ≫ ·) h.w
        have eq : fst (N ⊗ (T.X ⊗ P)) Z.X ≫ p ≫ d.hom.hom =
            translateCell e N P ≫ p ≫ d.hom.hom := by
          rw [← Category.assoc (translateCell e N P), hmid]
          simpa only [Category.assoc, tensorHom_fst_assoc] using H
        simpa only [v, p, middleProjection, Category.assoc, tensorHom_snd_assoc, tensorHom_fst,
          Category.id_comp] using eq
      · simp [v, translateCell]
  refine IsPullback.of_bot (v₂₁ := p) (v₂₂ := middleProjection N T₀.X P) ?_ hcomm hp.flip
  rw [hmid, ← hp.w]
  exact hfull.flip

private theorem translateCell_commutes {T G Z : Grp (OverBase R)}
    (t : T ⟶ G) (e : Z ⟶ T)
    {N P : OverBase R} (l : N ⟶ G.X) (p : P ⟶ G.X)
    (central : ∀ {Y : OverBase R} (a : Y ⟶ G.X) (b : Y ⟶ Z.X),
      (b ≫ (e ≫ t).hom.hom) * a = a * (b ≫ (e ≫ t).hom.hom)) :
    translateCell e N P ≫ markedCell t l p =
      (markedCell t l p ⊗ₘ 𝟙 Z.X) ≫
        (fst G.X Z.X * (snd G.X Z.X ≫ (e ≫ t).hom.hom)) := by
  simp only [translateCell, markedCell, middleProjection, MonObj.comp_mul, Category.assoc,
    CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_snd_assoc,
    tensorHom_snd_assoc, tensorHom_fst, Category.id_comp, MonObj.mul_comp]
  have hcomp : (e ≫ t).hom.hom = e.hom.hom ≫ t.hom.hom := rfl
  simp only [hcomp, mul_assoc]
  have hcomm := central
    (fst (N ⊗ (T.X ⊗ P)) Z.X ≫ snd N (T.X ⊗ P) ≫ snd T.X P ≫ p)
    (snd (N ⊗ (T.X ⊗ P)) Z.X)
  rw [hcomp] at hcomm
  rw [hcomm]

private theorem markedCell_open {T T₀ Z G Q : Grp (OverBase R)}
    (d : T ⟶ T₀) (e : Z ⟶ T) (t : T ⟶ G) (t₀ : T₀ ⟶ Q) (q : G ⟶ Q)
    {N P : OverBase R} (l : N ⟶ G.X) (p : P ⟶ G.X)
    (ht : d ≫ t₀ = t ≫ q)
    (hopen : IsOpenImmersion (markedCell t l p).left)
    (central : ∀ {Y : OverBase R} (a : Y ⟶ G.X) (b : Y ⟶ Z.X),
      (b ≫ (e ≫ t).hom.hom) * a = a * (b ≫ (e ≫ t).hom.hom))
    (hT : IsPullback (fst T.X Z.X) (fst T.X Z.X * (snd T.X Z.X ≫ e.hom.hom)) d.hom.hom d.hom.hom)
    (hG : IsPullback (fst G.X Z.X) (fst G.X Z.X * (snd G.X Z.X ≫ (e ≫ t).hom.hom))
      q.hom.hom q.hom.hom)
    [Flat d.hom.hom.left] [Surjective d.hom.hom.left] [QuasiCompact d.hom.hom.left]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] [QuasiCompact q.hom.hom.left] :
    let i := markedCell t l p
    let i₀ := markedCell t₀ (l ≫ q.hom.hom) (p ≫ q.hom.hom)
    let v := 𝟙 N ⊗ₘ (d.hom.hom ⊗ₘ 𝟙 P)
    IsOpenImmersion i₀.left ∧ IsPullback v i i₀ q.hom.hom := by
  dsimp only
  let i := markedCell t l p
  let i₀ := markedCell t₀ (l ≫ q.hom.hom) (p ≫ q.hom.hom)
  let v := 𝟙 N ⊗ₘ (d.hom.hom ⊗ₘ 𝟙 P)
  let U := N ⊗ (T.X ⊗ P)
  let r := translateCell e N P
  have htv : d.hom.hom ≫ t₀.hom.hom = t.hom.hom ≫ q.hom.hom :=
    congrArg (fun f : T ⟶ Q => f.hom.hom) ht
  have hc : v ≫ i₀ = i ≫ q.hom.hom := by
    simp only [v, i, i₀, markedCell, MonObj.comp_mul, Category.assoc, MonObj.mul_comp,
      tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp, htv]
  let F := Over.forget (Spec (CommRingCat.of R))
  have hv := (middleProjection_isPullback N P d.hom.hom).map F
  let : Flat v.left := MorphismProperty.of_isPullback hv (by assumption)
  let : Surjective v.left := MorphismProperty.of_isPullback hv (by assumption)
  let : QuasiCompact v.left := MorphismProperty.of_isPullback hv (by assumption)
  have hU := translateCell_relation d e N P hT
  have hG' : IsPullback (fst U Z.X) (r ≫ i) (v ≫ i₀) q.hom.hom := by
    rw [hc, translateCell_commutes t e l p central]
    exact ((tensor_fst_isPullback i Z.X).flip.paste_horiz hG.flip).flip
  have h := isPullback_of_torsor_relations
    (congrArg (fun f : U ⟶ Q.X => f.left) hc) (hU.map F) (hG'.map F)
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      h.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hopen,
    IsPullback.of_map_of_faithful F h⟩

end Cell

section SplitTorus

variable {R X M : Type u} [CommRing R] [CommGroup X] [CommGroup M]

/-- A closed diagonalizable subgroup of a split torus over a domain is specified by a
surjection on characters. -/
theorem characterRestriction_of_surjective [IsDomain R]
    (f : MonoidAlgebra R X →ₐc[R] MonoidAlgebra R M) (hf : Function.Surjective f) :
    ∃ z : X →* M, Function.Surjective z ∧ MonoidAlgebra.mapDomainBialgHom R z = f := by
  let z := MonoidAlgebra.mapDomainOfBialgHom f
  have hz : MonoidAlgebra.mapDomainBialgHom R z = f :=
    MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom f
  refine ⟨z, fun m => ?_, hz⟩
  obtain ⟨a, ha⟩ := hf (MonoidAlgebra.single m 1)
  rw [← hz] at ha
  apply Finsupp.mem_range_of_mapDomain_ne_zero (x := a.coeff)
  have hm := congrArg (fun b : MonoidAlgebra R M => b.coeff m) ha
  change Finsupp.mapDomain z a.coeff m = (MonoidAlgebra.single m (1 : R)).coeff m at hm
  simp [hm]

private theorem characterRestriction_surjective (z : X →* M) (h : Function.Surjective z) :
    Function.Surjective (MonoidAlgebra.mapDomainBialgHom R z) := by
  intro a
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective h a.coeff
  exact ⟨MonoidAlgebra.ofCoeff x, MonoidAlgebra.coeff_injective hx⟩

private theorem characterRestriction_central (z : X →* M) :
    IsCentral (MonoidAlgebra.mapDomainBialgHom R z) := by
  apply MonoidAlgebra.algHom_ext
  · intro x
    let s := MonoidAlgebra.of R X x
    change Algebra.TensorProduct.map (AlgHom.id R (MonoidAlgebra R X))
      (MonoidAlgebra.mapDomainBialgHom R z).toAlgHom (Coalgebra.comul (R := R) s) =
      (Algebra.TensorProduct.comm R (MonoidAlgebra R M) (MonoidAlgebra R X))
        (Algebra.TensorProduct.map (MonoidAlgebra.mapDomainBialgHom R z).toAlgHom
          (AlgHom.id R (MonoidAlgebra R X)) (Coalgebra.comul (R := R) s))
    rw [(MonoidAlgebra.isGroupLikeElem_of (R := R) x).comul_eq_tmul_self]
    rfl
  · ext

set_option maxHeartbeats 1500000 in
private theorem torusProjection_torsor [IsNoetherianRing R] [Module.Finite ℤ (Additive X)]
    [Fintype M] (z : X →* M) (hz : Function.Surjective z) :
    let D := MonoidAlgebra R X
    let H := MonoidAlgebra R M
    let T := HopfSpectrum R D
    let Z := HopfSpectrum R H
    let q := (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype)).hom.hom
    let a := fst T.X Z.X * (snd T.X Z.X ≫
      (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R z)).hom.hom)
    IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsPullback (fst T.X Z.X) a q q := by
  classical
  let D := MonoidAlgebra R X
  let D₀ := MonoidAlgebra R ↥z.ker
  let H := MonoidAlgebra R M
  let q : (HopfSpectrum R D).X ⟶ (HopfSpectrum R D₀).X :=
    (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype)).hom.hom
  let ψ : D →ₐc[R] H := MonoidAlgebra.mapDomainBialgHom R z
  let : Monoid.FG X := by
    rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
    infer_instance
  let : Algebra.FinitePresentation R D := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Module.Free R D := Module.Free.of_basis (MonoidAlgebra.basis X R)
  have hi : torusRestriction z (BialgHom.id R D) = ψ := BialgHom.comp_id _
  let hc : IsCentral (torusRestriction z (BialgHom.id R D)) := hi.symm ▸ characterRestriction_central z
  let B := TorusInvariants z (BialgHom.id R D)
  let : HopfAlgebra R B := invariantHopfAlgebra _ hc
  let j : B →ₐc[R] D := quotientInclusion _ hc
  obtain ⟨f, hf, hs⟩ := quotientTorus z (BialgHom.id R D) Function.surjective_id hc
  have heq : (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype).comp f = j := by
    simpa only [BialgHom.id_comp] using hf
  have hf_inj : Function.Injective f := by
    intro a b h
    have hj : Function.Injective j := Subtype.val_injective
    apply hj
    rw [← heq]
    exact congrArg (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype) h
  let e : B ≃ₐ[R] D₀ := AlgEquiv.ofBijective f.toAlgHom ⟨hf_inj, hs⟩
  let u := Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op
  let q₁ := (spectrumOfHopfHom j).hom.hom
  have hqu : q₁.left ≫ u.hom = q.left := by
    change Spec.map (CommRingCat.ofHom j.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) =
        Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype).toAlgHom.toRingHom)
    rw [← Spec.map_comp]
    congr 1
    apply ConcreteCategory.hom_ext
    intro a
    change j (e.symm a) = (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype) a
    rw [← heq]
    change (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype) (e (e.symm a)) = _
    rw [AlgEquiv.apply_symm_apply]
  have hS : Function.Surjective (torusRestriction z (BialgHom.id R D)) :=
    hi.symm ▸ characterRestriction_surjective z hz
  have hT := spectrumTorsor (torusRestriction z (BialgHom.id R D)) hc hS
  let : IsFinite q₁.left := hT.1
  let : Flat q₁.left := hT.2.1
  let : Surjective q₁.left := hT.2.2.1
  let T := HopfSpectrum R D
  let Z := HopfSpectrum R H
  let act (ψ' : D →ₐc[R] H) : T.X ⊗ Z.X ⟶ T.X :=
    fst T.X Z.X * (snd T.X Z.X ≫ (spectrumOfHopfHom ψ').hom.hom)
  have hact : act (torusRestriction z (BialgHom.id R D)) = act ψ := congrArg act hi
  have hrel : IsPullback (fst T.X Z.X) (act ψ) q₁ q₁ :=
    hact ▸ rightTorsor_over _ j hT
  let F := Over.forget (Spec (CommRingCat.of R))
  have hrelQ : IsPullback (fst T.X Z.X).left (act ψ).left q.left q.left := by
    refine (hrel.map F).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) u ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact hqu.trans (Category.id_comp _).symm
    · exact hqu.trans (Category.id_comp _).symm
  let : IsIso u.hom := u.isIso_hom
  change IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ _
  refine ⟨?_, ?_, ?_, IsPullback.of_map_of_faithful F hrelQ⟩
  · rw [← hqu]
    exact MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsFinite.{u}) q₁.left u.hom hT.1
      ((IsFinite.SpecMap_iff _).mpr (RingHom.Finite.of_surjective _ e.symm.surjective))
  · rw [← hqu]
    exact MorphismProperty.IsStableUnderComposition.comp_mem (P := @Flat.{u}) q₁.left u.hom hT.2.1
      (Flat.SpecMap_iff.mpr (RingHom.Flat.of_bijective e.symm.bijective))
  · rw [← hqu]
    exact ⟨u.hom.surjective.comp hT.2.2.1.surj⟩

end SplitTorus

section RootCoordinates

variable {R A C X M I : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing C] [HopfAlgebra R C] [CommGroup X] [CommGroup M]

private def convolutionMap {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (j : C →ₐc[R] A) (f : S →ₐ[R] T) :
    WithConv (A →ₐ[R] S) →* WithConv (C →ₐ[R] T) where
  toFun x := toConv (f.comp (x.ofConv.comp j.toAlgHom))
  map_one' := by
    simp only [AlgHom.convOne_def, ofConv_toConv, AlgHom.comp_assoc, j.counitAlgHom_comp]
    apply toConv_injective
    ext a
    exact f.commutes _
  map_mul' x y := by
    change toConv (f.comp ((x * y).ofConv.comp j.toAlgHom)) =
      toConv (f.comp (x.ofConv.comp j.toAlgHom)) *
        toConv (f.comp (y.ofConv.comp j.toAlgHom))
    rw [AlgHom.convMul_comp_bialgHom_distrib, AlgHom.comp_convMul_distrib, toConv_ofConv]

private def inversePoint {S : Type u} [CommRing S] [Algebra R S]
    (x : WithConv (A →ₐ[R] S)) : WithConv (A →ₐ[R] S) :=
  toConv (x.ofConv.comp (HopfAlgebra.antipodeAlgHom R A))

private theorem inversePoint_mul {S : Type u} [CommRing S] [Algebra R S]
    (x : WithConv (A →ₐ[R] S)) : inversePoint x * x = 1 := by
  let F := convolutionMap (BialgHom.id R A) x.ofConv
  have h := congrArg F (AlgHom.antipode_id_cancel (R := R) (A := A))
  rw [map_mul, map_one] at h
  exact h

private theorem mul_inversePoint {S : Type u} [CommRing S] [Algebra R S]
    (x : WithConv (A →ₐ[R] S)) : x * inversePoint x = 1 := by
  let F := convolutionMap (BialgHom.id R A) x.ofConv
  have h := congrArg F (AlgHom.id_antipode_cancel (R := R) (A := A))
  rw [map_mul, map_one] at h
  exact h

private theorem convolutionMap_inversePoint {S T : Type u}
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (j : C →ₐc[R] A) (f : S →ₐ[R] T) (x : WithConv (A →ₐ[R] S)) :
    convolutionMap j f (inversePoint x) = inversePoint (convolutionMap j f x) := by
  let F := convolutionMap j f
  have h := congrArg F (inversePoint_mul x)
  rw [map_mul, map_one] at h
  change F (inversePoint x) = inversePoint (F x)
  calc
    _ = F (inversePoint x) * (F x * inversePoint (F x)) := by rw [mul_inversePoint, mul_one]
    _ = _ := by rw [← mul_assoc, h, one_mul]

private theorem aeval_comp_algHom {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (g : S →ₐ[R] T) (a : S) : g.comp (Polynomial.aeval a) = Polynomial.aeval (g a) := by
  apply Polynomial.algHom_ext
  simp

private theorem rootCharacter_trivial [Nontrivial R] (z : X →* M) (t : A →ₐc[R] MonoidAlgebra R X)
    (x : A →ₐ[R] Polynomial R) (α : X) (hx : Function.Surjective x)
    (hc : IsCentral ((MonoidAlgebra.mapDomainBialgHom R z).comp t))
    (ha : RootScalarAction t x α) : z α = 1 := by
  let H := MonoidAlgebra R M
  let S := CommAlgCat.of R H
  let ψ : MonoidAlgebra R X →ₐc[R] H := MonoidAlgebra.mapDomainBialgHom R z
  let a : A →ₐ[R] H := (Polynomial.aeval (1 : H)).comp x
  let p := toConv (ψ.toAlgHom.comp t.toAlgHom)
  have hC : toConv a * p = p * toConv a :=
    central_convolution (ψ.comp t) hc a (AlgHom.id R H)
  have h := ha S 1 ψ.toAlgHom
  change p * toConv a * p⁻¹ =
    toConv ((Polynomial.aeval (ψ (MonoidAlgebra.of R X α) * (1 : H))).comp x) at h
  rw [← hC, mul_inv_cancel_right, mul_one] at h
  obtain ⟨b, hb⟩ := hx Polynomial.X
  have he := congrArg (fun g : WithConv (A →ₐ[R] H) => g.ofConv b) h
  change (Polynomial.aeval (1 : H)) (x b) =
    (Polynomial.aeval (ψ (MonoidAlgebra.of R X α))) (x b) at he
  rw [hb, Polynomial.aeval_X, Polynomial.aeval_X] at he
  apply (MonoidAlgebra.of_injective (R := R) (M := M))
  rw [map_one, he]
  exact (MonoidAlgebra.mapDomainBialgHom_single z α (1 : R)).symm

set_option maxHeartbeats 1200000 in
private theorem rootScalarAction_descends (z : X →* M)
    (t : A →ₐc[R] MonoidAlgebra R X) (j : C →ₐc[R] A)
    (t₀ : C →ₐc[R] MonoidAlgebra R ↥z.ker)
    (ht : (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype).comp t₀ = t.comp j)
    {x : A →ₐ[R] Polynomial R} {α : X} (h : RootScalarAction t x α) (hα : z α = 1) :
    RootScalarAction t₀ (x.comp j.toAlgHom) (⟨α, hα⟩ : z.ker) := by
  intro S a s
  let D := MonoidAlgebra R X
  let D₀ := MonoidAlgebra R ↥z.ker
  let e : D₀ →ₐc[R] D := MonoidAlgebra.mapDomainBialgHom R z.ker.subtype
  let E := D ⊗[R] S
  let E₀ := D₀ ⊗[R] S
  let l : D →ₐ[R] E := Algebra.TensorProduct.includeLeft
  let r : S →ₐ[R] E := Algebra.TensorProduct.includeRight
  let l₀ : D₀ →ₐ[R] E₀ := Algebra.TensorProduct.includeLeft
  let r₀ : S →ₐ[R] E₀ := Algebra.TensorProduct.includeRight
  let f : E₀ →ₐ[R] E := Algebra.TensorProduct.map e.toAlgHom (AlgHom.id R S)
  let x₀ := x.comp j.toAlgHom
  let b : D₀ := MonoidAlgebra.of R (↥z.ker) ⟨α, hα⟩
  let P := toConv (l₀.comp t₀.toAlgHom)
  let F := convolutionMap (BialgHom.id R C) f
  let J := convolutionMap j (AlgHom.id R E)
  have hf : Function.Injective f :=
    (tensorMap_leftInverse e.toLinearMap (torusProjection z)
      (LinearMap.id : S →ₗ[R] S) LinearMap.id (torusProjection_leftInverse z) (fun _ => rfl)).injective
  have hF : Function.Injective F := by
    intro u v huv
    apply ofConv_injective
    exact AlgHom.ext fun c => hf (congrArg (fun g : WithConv (C →ₐ[R] E) => g.ofConv c) huv)
  have hP : F P = J (toConv (l.comp t.toAlgHom)) := by
    apply ofConv_injective
    ext c
    change l (e (t₀ c)) = l (t (j c))
    exact congrArg l (DFunLike.congr_fun ht c)
  have hroot (v : E₀) : F (toConv ((Polynomial.aeval v).comp x₀)) =
      J (toConv ((Polynomial.aeval (f v)).comp x)) := by
    apply ofConv_injective
    change f.comp ((Polynomial.aeval v).comp x₀) = ((Polynomial.aeval (f v)).comp x).comp j.toAlgHom
    rw [← AlgHom.comp_assoc, aeval_comp_algHom, AlgHom.comp_assoc]
  have hr : f (r₀ a) = r a := by
    change (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id R S)) (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have hb : f (l₀ b) = l (MonoidAlgebra.of R X α) := by
    change e b ⊗ₜ[R] (1 : S) = MonoidAlgebra.of R X α ⊗ₜ[R] (1 : S)
    change MonoidAlgebra.mapDomainBialgHom R z.ker.subtype
        (MonoidAlgebra.single ⟨α, hα⟩ 1) ⊗ₜ[R] (1 : S) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    rfl
  have hFinv (x : WithConv (C →ₐ[R] E₀)) : F (inversePoint x) = inversePoint (F x) :=
    convolutionMap_inversePoint _ _ x
  have hJinv (x : WithConv (A →ₐ[R] E)) : J (inversePoint x) = inversePoint (J x) :=
    convolutionMap_inversePoint _ _ x
  have hu : P * toConv ((Polynomial.aeval (r₀ a)).comp x₀) * inversePoint P =
      toConv ((Polynomial.aeval (l₀ b * r₀ a)).comp x₀) := by
    apply hF
    simp only [map_mul, hFinv, hP, hroot, hr, hb]
    rw [← hJinv, ← map_mul, ← map_mul]
    exact congrArg J (h (CommAlgCat.of R E) (r a) l)
  let ev : E₀ →ₐ[R] S := Algebra.TensorProduct.lift s (AlgHom.id R S) (fun _ _ => Commute.all _ _)
  let L := convolutionMap (BialgHom.id R C) ev
  have hL : L P = toConv (s.comp t₀.toAlgHom) := by
    apply ofConv_injective
    ext c
    change ev (l₀ (t₀ c)) = s (t₀ c)
    change ev (t₀ c ⊗ₜ[R] (1 : S)) = s (t₀ c)
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hLroot (v : E₀) : L (toConv ((Polynomial.aeval v).comp x₀)) =
      toConv ((Polynomial.aeval (ev v)).comp x₀) := by
    apply ofConv_injective
    change ev.comp ((Polynomial.aeval v).comp x₀) = _
    rw [← AlgHom.comp_assoc, aeval_comp_algHom]
  have hav : ev (r₀ a) = a := by
    change ev (1 ⊗ₜ[R] a) = a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.id_apply]
  have hbv : ev (l₀ b) = s b := by
    change ev (b ⊗ₜ[R] (1 : S)) = s b
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hh := congrArg L hu
  have hLinv (x : WithConv (C →ₐ[R] E₀)) : L (inversePoint x) = inversePoint (L x) :=
    convolutionMap_inversePoint _ _ x
  simp only [map_mul, hLinv, hL, hLroot, hav, hbv] at hh
  exact hh

end RootCoordinates

section RootPlacement

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R A C I X : Type u} [CommRing R] [CommRing A] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R C] [CommGroup X]

private abbrev RootLine (R : Type u) [CommRing R] := SpecOver R (Polynomial R)

private def zeroParameter (R : Type u) [CommRing R] : RootLine R ⟶ RootLine R :=
  spectrumOfAlgHom (Polynomial.aeval (0 : Polynomial R))

private theorem upper_zero : Specs.IntegralRootRelations.upper (0 : R) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Specs.IntegralRootRelations.upper]

private theorem rankOne_root_zero (t : A →ₐc[R] MonoidAlgebra R X)
    (x y : A →ₐ[R] Polynomial R) (c : X →* Multiplicative ℤ) (r : RankOneMap R A)
    (h : RankOneCompatibility t x y c r) :
    zeroParameter R ≫ spectrumPoint x = (1 : RootLine R ⟶ (HopfSpectrum R A).X) := by
  have he := (h.1 (CommAlgCat.of R (Polynomial R)) 0).1
  rw [upper_zero, map_one] at he
  have ht : toConv ((Polynomial.aeval (0 : Polynomial R)).comp x) =
      (1 : WithConv (A →ₐ[R] Polynomial R)) := ofConv_injective he.symm
  have hSpec := congrArg (Spec.mapMulEquiv (R := R) (S := A) (T := Polynomial R)) ht
  rw [map_one] at hSpec
  change spectrumPoint ((Polynomial.aeval (0 : Polynomial R)).comp x) = _ at hSpec
  exact (spectrumOfAlgHom_comp x (Polynomial.aeval (0 : Polynomial R))).symm.trans hSpec

private def zeroCoordinates : (l : List I) → RootLine R ⟶ lineProduct R l
  | [] => toUnit _
  | _ :: l => CartesianMonoidalCategory.lift (zeroParameter R) (zeroCoordinates l)

private theorem zeroCoordinates_rootProduct (x : I → A →ₐ[R] Polynomial R)
    (hx : ∀ i, zeroParameter R ≫ spectrumPoint (x i) = (1 : RootLine R ⟶ (HopfSpectrum R A).X))
    (l : List I) : zeroCoordinates l ≫ rootProduct x l = 1 := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons i l ih =>
    simp only [zeroCoordinates, rootProduct, MonObj.comp_mul, CartesianMonoidalCategory.lift_fst_assoc,
      CartesianMonoidalCategory.lift_snd_assoc]
    change (zeroParameter R ≫ spectrumPoint (x i)) * (zeroCoordinates l ≫ rootProduct x l) = 1
    rw [hx, ih, one_mul]

private theorem rootProduct_insertion (x : I → A →ₐ[R] Polynomial R)
    (hx : ∀ i, zeroParameter R ≫ spectrumPoint (x i) = (1 : RootLine R ⟶ (HopfSpectrum R A).X))
    {i : I} {l : List I} (hi : i ∈ l) :
    ∃ (a : RootLine R ⟶ lineProduct R l) (p : lineProduct R l ⟶ RootLine R),
      a ≫ p = 𝟙 _ ∧ a ≫ rootProduct x l = spectrumPoint (x i) := by
  induction l with
  | nil => exact (List.not_mem_nil hi).elim
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · refine ⟨CartesianMonoidalCategory.lift (𝟙 _) (zeroCoordinates l), fst _ _, by simp, ?_⟩
      simp only [rootProduct, MonObj.comp_mul, CartesianMonoidalCategory.lift_fst_assoc,
        CartesianMonoidalCategory.lift_snd_assoc, Category.id_comp,
        zeroCoordinates_rootProduct x hx, mul_one]
    · obtain ⟨a, p, hp, ha⟩ := ih hi
      refine ⟨CartesianMonoidalCategory.lift (zeroParameter R) a, snd _ _ ≫ p, by simp [hp], ?_⟩
      simp only [rootProduct, MonObj.comp_mul, CartesianMonoidalCategory.lift_fst_assoc,
        CartesianMonoidalCategory.lift_snd_assoc, ha]
      change (zeroParameter R ≫ spectrumPoint (x j)) * spectrumPoint (x i) = _
      rw [hx, one_mul]

private theorem cellMap_root_insertion (t : A →ₐc[R] MonoidAlgebra R X)
    (x : I → A →ₐ[R] Polynomial R)
    (hx : ∀ i, zeroParameter R ≫ spectrumPoint (x i) = (1 : RootLine R ⟶ (HopfSpectrum R A).X))
    (negative positive : List I) {i : I} (hi : i ∈ negative ++ positive) :
    ∃ a : RootLine R ⟶ _,
      (∃ p : _ ⟶ RootLine R, a ≫ p = 𝟙 _) ∧
        a ≫ cellMap t x negative positive = spectrumPoint (x i) := by
  let T := HopfSpectrum R (MonoidAlgebra R X)
  let N := lineProduct R negative
  let P := lineProduct R positive
  let oneT : RootLine R ⟶ T.X := 1
  rcases List.mem_append.mp hi with hn | hp
  · obtain ⟨a, p, hpa, ha⟩ := rootProduct_insertion x hx hn
    refine ⟨CartesianMonoidalCategory.lift a (CartesianMonoidalCategory.lift oneT (zeroCoordinates positive)),
      ⟨fst N (T.X ⊗ P) ≫ p, by
        rw [CartesianMonoidalCategory.lift_fst_assoc]
        exact hpa⟩, ?_⟩
    simp only [cellMap, MonObj.comp_mul,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_snd_assoc, ha,
      zeroCoordinates_rootProduct x hx]
    change spectrumPoint (x i) * (oneT ≫ (spectrumOfHopfHom t).hom.hom * 1) = _
    rw [show oneT = 1 from rfl, MonObj.one_comp, mul_one, mul_one]
  · obtain ⟨a, p, hpa, ha⟩ := rootProduct_insertion x hx hp
    refine ⟨CartesianMonoidalCategory.lift (zeroCoordinates negative) (CartesianMonoidalCategory.lift oneT a),
      ⟨snd N (T.X ⊗ P) ≫ snd T.X P ≫ p, by
        rw [CartesianMonoidalCategory.lift_snd_assoc, CartesianMonoidalCategory.lift_snd_assoc]
        exact hpa⟩, ?_⟩
    simp only [cellMap, MonObj.comp_mul,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_snd_assoc, ha,
      zeroCoordinates_rootProduct x hx]
    change (1 : RootLine R ⟶ (HopfSpectrum R A).X) *
      (oneT ≫ (spectrumOfHopfHom t).hom.hom * spectrumPoint (x i)) = _
    rw [show oneT = 1 from rfl, MonObj.one_comp, one_mul, one_mul]

private theorem rootProduct_pushforward (j : C →ₐc[R] A) (x : I → A →ₐ[R] Polynomial R)
    (l : List I) :
    rootProduct (fun i => (x i).comp j.toAlgHom) l =
      rootProduct x l ≫ (spectrumOfHopfHom j).hom.hom := by
  induction l with
  | nil => exact (MonObj.one_comp _).symm
  | cons i l ih =>
    simp only [rootProduct, MonObj.mul_comp, Category.assoc, spectrumOfAlgHom_comp, ih]
    rfl

private theorem quotient_rootRestriction_surjective
    (j : C →ₐc[R] A) (t : C →ₐc[R] MonoidAlgebra R X)
    (x : I → A →ₐ[R] Polynomial R) (negative positive : List I)
    (hx : ∀ i, zeroParameter R ≫ spectrumPoint ((x i).comp j.toAlgHom) =
      (1 : RootLine R ⟶ (HopfSpectrum R C).X))
    (hopen : IsOpenImmersion (cellMap t (fun i => (x i).comp j.toAlgHom) negative positive).left)
    [IsFinite (spectrumOfHopfHom j).hom.hom.left] {i : I} (hi : i ∈ negative ++ positive)
    (hxi : Function.Surjective (x i)) :
    Function.Surjective ((x i).comp j.toAlgHom) := by
  let x₀ := fun i => (x i).comp j.toAlgHom
  obtain ⟨a, ⟨p, hp⟩, h⟩ := cellMap_root_insertion t x₀ hx negative positive hi
  let f := spectrumPoint (x₀ i)
  let e := cellMap t x₀ negative positive
  let F := Over.forget (Spec (CommRingCat.of R))
  have ha : IsSplitMono a.left := IsSplitMono.mk'
    ⟨p.left, congrArg (fun k : RootLine R ⟶ RootLine R => k.left) hp⟩
  have hm : Mono f.left := by
    have he : a.left ≫ e.left = f.left :=
      congrArg (fun g : RootLine R ⟶ (HopfSpectrum R C).X => g.left) h
    rw [← he]
    let : Mono a.left := inferInstance
    let : Mono e.left := inferInstance
    exact mono_comp a.left e.left
  have hc : IsClosedImmersion (spectrumPoint (x i)).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (x i).toRingHom) hxi
  have hfin : IsFinite f.left := by
    change IsFinite (F.map (spectrumOfAlgHom ((x i).comp j.toAlgHom)))
    rw [spectrumOfAlgHom_comp, Functor.map_comp]
    exact inferInstanceAs (IsFinite ((spectrumPoint (x i)).left ≫ (spectrumOfHopfHom j).hom.hom.left))
  have hclosed : IsClosedImmersion f.left :=
    (IsClosedImmersion.iff_isFinite_and_mono f.left).mpr ⟨hfin, hm⟩
  let g := CommRingCat.ofHom ((x i).comp j.toAlgHom).toRingHom
  let P := RingHom.toMorphismProperty (fun g => Function.Surjective g)
  let : P.RespectsIso := by
    dsimp [P]
    rw [← RingHom.toMorphismProperty_respectsIso_iff]
    exact RingHom.surjective_respectsIso
  let : IsAffine (HopfSpectrum R C).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  exact (MorphismProperty.arrow_mk_iso_iff P (arrowIsoΓSpecOfIsAffine g)).mpr
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2

end RootPlacement

section QuotientCell

variable {R A C X M I : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing C] [HopfAlgebra R C] [CommGroup X] [CommGroup M]
  [IsNoetherianRing R] [Module.Finite ℤ (Additive X)] [Fintype M]

set_option maxHeartbeats 1000000 in
private theorem quotientCell (z : X →* M) (hz : Function.Surjective z)
    (t : A →ₐc[R] MonoidAlgebra R X) (j : C →ₐc[R] A)
    (t₀ : C →ₐc[R] MonoidAlgebra R ↥z.ker)
    (ht : (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype).comp t₀ = t.comp j)
    (x : I → A →ₐ[R] Polynomial R) (negative positive : List I)
    (hopen : IsOpenImmersion (cellMap t x negative positive).left)
    (hc : IsCentral ((MonoidAlgebra.mapDomainBialgHom R z).comp t))
    (hq : IsRightTorsor j ((MonoidAlgebra.mapDomainBialgHom R z).comp t)) :
    let x₀ := fun i => (x i).comp j.toAlgHom
    IsOpenImmersion (cellMap t₀ x₀ negative positive).left ∧
    IsPullback (cellTorusQuotient z negative positive) (cellMap t x negative positive)
      (cellMap t₀ x₀ negative positive) (spectrumOfHopfHom j).hom.hom := by
  let d := spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype)
  let e := spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R z)
  let i := spectrumOfHopfHom t
  let i₀ := spectrumOfHopfHom t₀
  let q := spectrumOfHopfHom j
  let π := (MonoidAlgebra.mapDomainBialgHom R z).comp t
  let : IsFinite q.hom.hom.left := hq.1
  let : Flat q.hom.hom.left := hq.2.1
  let : Surjective q.hom.hom.left := hq.2.2.1
  let : QuasiCompact q.hom.hom.left := inferInstance
  have hT := torusProjection_torsor (R := R) z hz
  let : IsFinite d.hom.hom.left := hT.1
  let : Flat d.hom.hom.left := hT.2.1
  let : Surjective d.hom.hom.left := hT.2.2.1
  let : QuasiCompact d.hom.hom.left := inferInstance
  have he : e ≫ i = spectrumOfHopfHom π := (spectrumOfHopfHom_comp t _).symm
  have hit : d ≫ i₀ = i ≫ q :=
    (spectrumOfHopfHom_comp t₀ _).symm.trans
      ((congrArg spectrumOfHopfHom ht).trans (spectrumOfHopfHom_comp j t))
  have hcent {Y : OverBase R} (a : Y ⟶ (HopfSpectrum R A).X)
      (b : Y ⟶ (HopfSpectrum R (MonoidAlgebra R M)).X) :
      (b ≫ (e ≫ i).hom.hom) * a = a * (b ≫ (e ≫ i).hom.hom) := by
    rw [he]
    exact (central_translation π hc a b).symm
  have hrel := rightTorsor_over π j hq
  have hrel' : IsPullback (fst (HopfSpectrum R A).X (HopfSpectrum R (MonoidAlgebra R M)).X)
      (fst _ _ * (snd _ _ ≫ (e ≫ i).hom.hom)) q.hom.hom q.hom.hom := by
    rw [he]
    exact hrel
  have h := markedCell_open d e i i₀ q (rootProduct x negative) (rootProduct x positive)
    hit hopen hcent hT.2.2.2 hrel'
  rw [← rootProduct_pushforward j x negative, ← rootProduct_pushforward j x positive] at h
  exact h

end QuotientCell

private theorem spectrumCoordinateProperties (R A : Type u) [CommRing R] [CommRing A]
    [HopfAlgebra R A] (hs : Smooth (HopfSpectrum R A).X.hom) :
    Algebra.FinitePresentation R A ∧ Module.Flat R A := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let : Smooth f := hs
  exact ⟨RingHom.finitePresentation_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
        (show LocallyOfFinitePresentation f from inferInstance)),
    RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp (show Flat f from inferInstance))⟩

open _root_.LinearAlgebraicGroups.Specs
open Specs.IntegralCentralQuotient
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section BaseChange

variable {R : Type u} [CommRing R]

private theorem fibreMap_isPullback (K : Type u) [Field K] [Algebra R K]
    {G Q : Grp (OverBase R)} (f : G ⟶ Q) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
    IsPullback ((fibreGroup K).map f).hom.hom.left (pullback.fst G.X.hom b)
      (pullback.fst Q.X.hom b) f.hom.hom.left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  change IsPullback ((Over.pullback b).map f.hom.hom).left
    (pullback.fst G.X.hom b) (pullback.fst Q.X.hom b) f.hom.hom.left
  apply IsPullback.of_right (h₁₂ := pullback.snd Q.X.hom b) (h₂₂ := Q.X.hom) (v₁₃ := b)
  · have h : ((Over.pullback b).map f.hom.hom).left ≫ pullback.snd Q.X.hom b =
        pullback.snd G.X.hom b := pullback.lift_snd _ _ _
    rw [h, Over.w]
    exact (IsPullback.of_hasPullback G.X.hom b).flip
  · exact pullback.lift_fst _ _ _
  · exact (IsPullback.of_hasPullback Q.X.hom b).flip

private theorem fibreMap_property (K : Type u) [Field K] [Algebra R K]
    {G Q : Grp (OverBase R)} (f : G ⟶ Q)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (h : P f.hom.hom.left) :
    P ((fibreGroup K).map f).hom.hom.left :=
  MorphismProperty.of_isPullback (fibreMap_isPullback K f).flip h

private def affineFibre (K : Type u) [Field K] [Algebra R K]
    (A : Type u) [CommRing A] [HopfAlgebra R A] [Algebra.FiniteType R A] : AffineAlgebraicGroup K := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let G := HopfSpectrum R A
  letI : IsAffine G.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  letI : IsAffineHom G.X.hom := isAffineHom_of_isAffine G.X.hom
  letI : LocallyOfFiniteType G.X.hom := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  refine ⟨(fibreGroup K).obj G, ?_, ?_, ?_⟩
  · let : IsAffineHom (pullback.snd G.X.hom b) :=
      MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom b inferInstance
    exact isAffine_of_isAffineHom (pullback.snd G.X.hom b)
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom b))
  · exact inferInstanceAs (QuasiCompact (pullback.snd G.X.hom b))

private def fibreHopfSpectrumIso (K : Type u) [Field K] [Algebra R K]
    (A : Type u) [CommRing A] [HopfAlgebra R A] :
    (fibreGroup K).obj (HopfSpectrum R A) ≅ HopfSpectrum K (K ⊗[R] A) := by
  let e := (pullbackSymmetry _ _ ≪≫ pullbackSpecIso' R K A)
  let f := e.hom.asOver (Spec (CommRingCat.of K))
  have hf : IsMonHom f := inferInstanceAs (IsMonHom
    ((pullbackSymmetry _ _ ≪≫ pullbackSpecIso' R K A).hom.asOver (Spec (CommRingCat.of K))))
  have : IsIso ((Over.forget _).map f) := inferInstanceAs (IsIso e.hom)
  let : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  exact Grp.mkIso (asIso f) (IsMonHom.one_hom (f := f)) (IsMonHom.mul_hom (f := f))

private def monoidAlgebra_scalarExtension (K M : Type u) [Field K] [Algebra R K] [CommGroup M] :
    (K ⊗[R] MonoidAlgebra R M) ≃ₐc[K] MonoidAlgebra K M := by
  let f := MonoidAlgebra.scalarTensorEquiv R K (M := M)
  let basis := (MonoidAlgebra.basis M R).baseChange K
  have hf (m : M) : f (basis m) = MonoidAlgebra.of K M m := by
    rw [show basis m = _ from Module.Basis.baseChange_apply _ _ _]
    exact (f.toEquiv.eq_symm_apply).mp
      (MonoidAlgebra.scalarTensorEquiv_symm_single (R := R) (A := K) m 1).symm
  have hLike (m : M) : IsGroupLikeElem K (basis m) := by
    rw [show basis m = _ from Module.Basis.baseChange_apply _ _ _]
    change IsGroupLikeElem K ((1 : K) ⊗ₜ[R] MonoidAlgebra.of R M m)
    constructor
    · simp [TensorProduct.counit_tmul]
    · rw [TensorProduct.comul_tmul,
        (MonoidAlgebra.isGroupLikeElem_of (R := R) m).comul_eq_tmul_self]
      simp
  apply BialgEquiv.ofAlgEquiv f
  · change (Bialgebra.counitAlgHom K _).comp f.toAlgHom = Bialgebra.counitAlgHom K _
    apply AlgHom.toLinearMap_injective
    apply basis.ext
    intro m
    change Coalgebra.counit (R := K) (f (basis m)) = Coalgebra.counit (R := K) (basis m)
    rw [hf, (hLike m).counit_eq_one,
      (MonoidAlgebra.isGroupLikeElem_of (R := K) m).counit_eq_one]
  · apply AlgHom.toLinearMap_injective
    apply basis.ext
    intro m
    simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      Bialgebra.comulAlgHom_apply, (hLike m).comul_eq_tmul_self,
      Algebra.TensorProduct.map_tmul, hf,
      (MonoidAlgebra.isGroupLikeElem_of (R := K) m).comul_eq_tmul_self]

end BaseChange

section FiniteMorphisms

variable {k : Type u} [Field k]

private theorem finiteOverField_discrete (X : SchemeOver k) [IsFinite X.hom] :
    DiscreteTopology X.left := by
  let := isAffine_of_isAffineHom X.hom
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr (show IsAffine X.left from inferInstance)
  let f := ((algSpec (CommRingCat.of k)).obj A).hom
  let F := Over.forget (Spec (CommRingCat.of k))
  have hef : f = e.hom.left ≫ X.hom := (Over.w e.hom).symm
  have hf : IsFinite f := by
    rw [hef]
    let : IsIso e.hom.left := F.map_isIso e.hom
    infer_instance
  let : Module.Finite k A.unop := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  let : IsArtinianRing A.unop := IsArtinianRing.of_finite k A.unop
  let : DiscreteTopology (F.obj ((algSpec (CommRingCat.of k)).obj A)) :=
    inferInstanceAs (DiscreteTopology (PrimeSpectrum A.unop))
  exact (F.mapIso e).hom.homeomorph.discreteTopology

private theorem smooth_connected_quotient [IsAlgClosed k] {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    Smooth Q.val.X.hom ∧ GeometricallyConnected Q.val.X.hom := by
  let := G.property.1
  let := Q.property.1
  let := Q.property.2.1
  let : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  let : ConnectedSpace Q.val.X.left :=
    q.hom.hom.left.surjective.connectedSpace q.hom.hom.left.continuous
  have hinj := ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q.hom.hom.left).mp
    ⟨inferInstance, inferInstance⟩).injective
  let : _root_.IsReduced Γ(Q.val.X.left, ⊤) := isReduced_of_injective _ hinj
  let : IsReduced Q.val.X.left := isReduced_of_isAffine_isReduced _
  refine ⟨smoothOfReducedOverPerfectField k Q.val inferInstance, ?_⟩
  exact geometricallyConnected_of_connected Q

end FiniteMorphisms

section SplitFibres

variable {R : Type u} [CommRing R]

private theorem latticeEquiv (M : Type u) [CommGroup M] [Module.Free ℤ (Additive M)]
    [Module.Finite ℤ (Additive M)] :
    ∃ r : ℕ, Nonempty (M ≃* Specs.CharacterDescent.StandardLattice.{u} r) := by
  classical
  let I := Module.Free.ChooseBasisIndex ℤ (Additive M)
  let b := Module.Free.chooseBasis ℤ (Additive M)
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I
  let e := (b.reindex (Fintype.equivFin I)).equivFun.toAddEquiv
  refine ⟨r, ⟨{
    toFun := fun x i => ⟨Multiplicative.ofAdd (e (Additive.ofMul x) i)⟩
    invFun := fun u => Additive.toMul (e.symm fun i => Multiplicative.toAdd (u i).down)
    left_inv := fun x => e.symm_apply_apply (Additive.ofMul x)
    right_inv := ?_
    map_mul' := ?_ }⟩⟩
  · intro x
    funext i
    apply ULift.ext
    exact congrFun (e.apply_symm_apply fun j => Multiplicative.toAdd (x j).down) i
  · intro x y
    funext i
    apply ULift.ext
    exact congrFun (e.map_add (Additive.ofMul x) (Additive.ofMul y)) i

private theorem splitFibreOfFreeLattice (K X : Type u) [Field K] [Algebra R K] [CommGroup X]
    [Module.Free ℤ (Additive X)] [Module.Finite ℤ (Additive X)] :
    Specs.GeometricRadicals.IsSplitTorus ((fibreGroup K).obj (HopfSpectrum R (MonoidAlgebra R X))) := by
  obtain ⟨r, ⟨e⟩⟩ := latticeEquiv X
  obtain ⟨e₀⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) r
  let f := MonoidAlgebra.mapDomainBialgHom K e.toMonoidHom
  have hfi : Function.Injective f := MonoidAlgebra.mapDomain_injective e.injective
  have hfs : Function.Surjective f := by
    intro a
    obtain ⟨b, hb⟩ := Finsupp.mapDomain_surjective e.surjective (MonoidAlgebra.coeff a)
    exact ⟨MonoidAlgebra.ofCoeff b, MonoidAlgebra.coeff_injective hb⟩
  let e₁ := CommHopfAlgCat.isoMk (monoidAlgebra_scalarExtension (R := R) K X)
  let e₂ := CommHopfAlgCat.isoMk (BialgEquiv.ofBijective f ⟨hfi, hfs⟩)
  let F := hopfSpec (CommRingCat.of K)
  exact ⟨r, ⟨fibreHopfSpectrumIso K (MonoidAlgebra R X) ≪≫
    (F.mapIso e₁.op).symm ≪≫ (F.mapIso e₂.op).symm ≪≫ e₀⟩⟩

end SplitFibres
section Reductivity

open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive IsTorus IsTrivialSubgroup
  geometricUnipotentRadical identitySubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsSolvable)
open private ReducedIdentityComponent.factorHom from LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private schemeKernel_exists schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private factor_closed isIso_of_schemeIso solvable_iff_sections rationalSections
  trivial_of_subsingleton_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private torus_smooth_connected_solvable from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isTorus_iff_coordinates torus_of_iso from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_multiplicativeType torus_of_split from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isIso_of_trivial_kernel from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem finite_zero_isTrivial {G Q : AffineAlgebraicGroup k} (f : G.val ⟶ Q.val)
    (hfin : IsFinite f.hom.hom.left) (hzero : f = 0)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    Nonempty (G.val ≅ Grp.trivial (SchemeOver k)) := by
  let s := (identitySubgroup Q).inclusion.hom.hom.left
  have hf : f.hom.hom.left = G.val.X.hom ≫ s := by
    rw [hzero]
    rfl
  let : IsClosedImmersion s := (identitySubgroup Q).isClosedImmersion
  let : IsFinite (G.val.X.hom ≫ s) := hf ▸ hfin
  let : IsFinite G.val.X.hom := IsFinite.of_comp G.val.X.hom s
  let : DiscreteTopology G.val.X.left := finiteOverField_discrete G.val.X
  let : Subsingleton G.val.X.left := subsingleton_of_preconnected_totallyDisconnected
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  let : Subsingleton (rationalSections G.val) := ⟨fun x y => Over.OverMorphism.ext
    (ext_of_apply_closedPoint_eq G.val.X.hom (Over.w x) (Over.w y) (Subsingleton.elim _ _))⟩
  exact trivial_of_subsingleton_sections G hs

omit [IsAlgClosed k] in
private theorem surjective_zero_isTrivial {G Q : AffineAlgebraicGroup k} (f : G.val ⟶ Q.val)
    (hf : Surjective f.hom.hom.left) (hzero : f = 0) (hs : Smooth Q.val.X.hom) :
    Nonempty (Q.val ≅ Grp.trivial (SchemeOver k)) := by
  let j := (identitySubgroup Q).inclusion
  let s := j.hom.hom.left
  have hcomp : f.hom.hom.left = G.val.X.hom ≫ s := by
    rw [hzero]
    rfl
  let : IsClosedImmersion s := (identitySubgroup Q).isClosedImmersion
  let : IsReduced Q.val.X.left := isReduced_of_smooth_over_field Q.val.X.hom
  let : Surjective s := ⟨by
    intro y
    obtain ⟨x, hx⟩ := hf.surj y
    exact ⟨G.val.X.hom x, (congrArg (fun a : G.val.X.left ⟶ Q.val.X.left => a x)
      hcomp).symm.trans hx⟩⟩
  let : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  let : IsIso j := isIso_of_schemeIso j
  exact ⟨(asIso j).symm⟩

private theorem reducedIdentityPreimage {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) [IsFinite q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (N : ClosedSubgroup Q.val) (hN : ConnectedSpace N.group.X.left) :
    ∃ (C : ClosedSubgroup G.val) (p : C.group ⟶ N.group),
      C.inclusion ≫ q = p ≫ N.inclusion ∧
      Smooth C.group.X.hom ∧ ConnectedSpace C.group.X.left ∧
      IsFinite p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      (IsNormalSubgroup N.inclusion → IsNormalSubgroup C.inclusion) ∧
      ∀ (T : ClosedSubgroup G.val) (f : T.group ⟶ N.group),
        T.inclusion ≫ q = f ≫ N.inclusion →
        Smooth T.group.X.hom → ConnectedSpace T.group.X.left → IsSubgroupOf T C := by
  let P := pullback q N.inclusion
  let j : P ⟶ G.val := pullback.fst q N.inclusion
  let p : P ⟶ N.group := pullback.snd q N.inclusion
  let F := Grp.forget (SchemeOver k)
  let L := Over.forget (Spec (CommRingCat.of k))
  have hOver : IsPullback j.hom.hom p.hom.hom q.hom.hom N.inclusion.hom.hom :=
    (IsPullback.of_hasPullback q N.inclusion).map F
  have hSch := hOver.map L
  have hj : IsClosedImmersion j.hom.hom.left := MorphismProperty.of_isPullback hSch.flip N.isClosedImmersion
  let : IsFinite p.hom.hom.left := MorphismProperty.of_isPullback hSch
    (show IsFinite q.hom.hom.left from inferInstance)
  let : Flat p.hom.hom.left := MorphismProperty.of_isPullback hSch
    (show Flat q.hom.hom.left from inferInstance)
  let : Surjective p.hom.hom.left := MorphismProperty.of_isPullback hSch
    (show Surjective q.hom.hom.left from inferInstance)
  let : LocallyOfFinitePresentation p.hom.hom.left := MorphismProperty.of_isPullback hSch
    (show LocallyOfFinitePresentation q.hom.hom.left from inferInstance)
  let P₀ : ClosedSubgroup G.val := ⟨P, j, hj⟩
  let H := closedSubgroupAlgebraicGroup P₀
  obtain ⟨C₀⟩ := EquivariantUnipotentSeries.exists_smooth_identity_component H
  let i := C₀.subgroup.inclusion
  let : IsClosedImmersion i.hom.hom.left := C₀.subgroup.isClosedImmersion
  let C : ClosedSubgroup G.val :=
    ⟨C₀.subgroup.group, i ≫ j, inferInstanceAs (IsClosedImmersion (i.hom.hom.left ≫ j.hom.hom.left))⟩
  let f : C.group ⟶ N.group := i ≫ p
  have hfin : IsFinite f.hom.hom.left :=
    inferInstanceAs (IsFinite (i.hom.hom.left ≫ p.hom.hom.left))
  have hsurj : Surjective f.hom.hom.left := by
    have hr : Set.range f.hom.hom.left =
        p.hom.hom.left '' Set.range i.hom.hom.left := by
      change Set.range (⇑p.hom.hom.left ∘ ⇑i.hom.hom.left) = _
      exact Set.range_comp _ _
    let : IsFinite f.hom.hom.left := hfin
    have hclosed : IsClosed (Set.range f.hom.hom.left) :=
      f.hom.hom.left.isClosedMap.isClosed_range
    have hopen : IsOpen (Set.range f.hom.hom.left) :=
      hr.symm ▸ p.hom.hom.left.isOpenMap _ C₀.open_range
    let : ConnectedSpace N.group.X.left := hN
    have hnonempty : Nonempty C.group.X.left := C₀.connected.toNonempty
    exact ⟨Set.range_eq_univ.mp ((show IsClopen (Set.range f.hom.hom.left) from ⟨hclosed, hopen⟩).eq_univ
      (Set.range_nonempty _))⟩
  refine ⟨C, f, ?_, C₀.smooth, C₀.connected, hfin, hsurj, ?_, ?_⟩
  · change (i ≫ j) ≫ q = (i ≫ p) ≫ N.inclusion
    rw [Category.assoc, Category.assoc, pullback.condition]
  · intro hn
    apply EquivariantUnipotentSeries.smooth_identity_component_normal hs hc P₀ _ C₀
    let x := fst G.val.X P.X
    let y := snd G.val.X P.X
    obtain ⟨a, ha⟩ := normalSubgroup_conjugate_sections hn (x ≫ q.hom.hom) (y ≫ p.hom.hom)
    have hcomm : subgroupConjugation j ≫ q.hom.hom = a ≫ N.inclusion.hom.hom := by
      rw [ha]
      simp only [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hOver.w, x, y]
    exact ⟨hOver.lift (subgroupConjugation j) a hcomm, hOver.lift_fst _ _ _⟩
  · intro T g hg hsT hcT
    let a : T.group ⟶ P := pullback.lift T.inclusion g hg
    obtain ⟨b, hb⟩ := ReducedIdentityComponent.factorHom C₀
      (A := closedSubgroupAlgebraicGroup T) a hsT hcT
    refine ⟨b, ?_⟩
    change b ≫ i ≫ j = T.inclusion
    rw [← Category.assoc, hb, pullback.lift_fst]

private theorem soluble_of_finite_to_commutative {G Q : AffineAlgebraicGroup k}
    (f : G.val ⟶ Q.val) [IsFinite f.hom.hom.left] [IsCommMonObj Q.val.X]
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) : IsSolvable G.val := by
  let := Q.property.1
  obtain ⟨K, hK⟩ := schemeKernel_exists f
  let L := Over.forget (Spec (CommRingCat.of k))
  let : IsFinite K.group.X.hom := MorphismProperty.of_isPullback (hK.map L)
    (show IsFinite f.hom.hom.left from inferInstance)
  let : DiscreteTopology K.group.X.left := finiteOverField_discrete K.group.X
  let : LocallyOfFiniteType K.group.X.hom := (closedSubgroupAlgebraicGroup K).property.2.1
  let W := G.val.X ⊗ G.val.X
  let a := fst G.val.X G.val.X
  let b := snd G.val.X G.val.X
  let c : W ⟶ G.val.X := a * b * a⁻¹ * b⁻¹
  have hkill : c ≫ f.hom.hom = 1 := by
    simp only [c, MonObj.mul_comp, GrpObj.inv_comp]
    rw [mul_comm (a ≫ f.hom.hom) (b ≫ f.hom.hom), mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨v, hv⟩ := (schemeKernel_sections hK c).mpr hkill
  change v ≫ K.inclusion.hom.hom = c at hv
  let : ConnectedSpace W.left := (WordDomainGeometry.smoothConnectedGroupProduct G G hs hc hs hc).2.1
  have hr := (isPreconnected_range v.left.continuous).subsingleton
  apply (solvable_iff_sections G hs hc).mpr
  apply Group.isSolvable_of_comm
  intro x y
  let p := CartesianMonoidalCategory.lift x y
  let o := CartesianMonoidalCategory.lift (1 : rationalSections G.val) (1 : rationalSections G.val)
  have he : p ≫ v = o ≫ v := Over.OverMorphism.ext
    (ext_of_apply_closedPoint_eq K.group.X.hom (Over.w (p ≫ v)) (Over.w (o ≫ v))
      (hr ⟨p.left (IsLocalRing.closedPoint k), rfl⟩ ⟨o.left (IsLocalRing.closedPoint k), rfl⟩))
  have heq : x * y * x⁻¹ * y⁻¹ = 1 := by
    calc
      _ = p ≫ c := by simp only [p, c, a, b, MonObj.comp_mul, GrpObj.comp_inv,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
      _ = o ≫ c := by rw [← hv, ← Category.assoc, he, Category.assoc]
      _ = _ := by simp only [o, c, a, b, MonObj.comp_mul, GrpObj.comp_inv,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd, inv_one, mul_one]
  calc
    x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = _ := by rw [heq, one_mul]

private theorem maximalTorus_finiteImage {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) [IsFinite q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (T : ClosedSubgroup G.val) (T₀ : ClosedSubgroup Q.val) (d : T.group ⟶ T₀.group)
    (hT : IsMaximalTorus T) (hT₀ : IsTorus T₀.group) (hd : T.inclusion ≫ q = d ≫ T₀.inclusion) :
    IsMaximalTorus T₀ := by
  refine ⟨hT₀, ?_⟩
  intro S hS hTS
  obtain ⟨a, ha⟩ := hTS
  let S₀ := closedSubgroupAlgebraicGroup S
  have hsS := torus_smooth_connected_solvable S₀ hS
  have hsT := torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup T) hT.1
  obtain ⟨C, p, hp, hsC, hcC, hpfin, hps, _, hlift⟩ :=
    reducedIdentityPreimage q hs hc S hsS.2.1
  let A := closedSubgroupAlgebraicGroup C
  have hTC : IsSubgroupOf T C := hlift T (d ≫ a) (by rw [hd, Category.assoc, ha]) hsT.1 hsT.2.1
  let := torus_commutative S₀ hS
  let := hpfin
  obtain ⟨U, D, v, hU, hv, hD, _⟩ :=
    GeometricTorusSplitting.splitting A hsC hcC
      (soluble_of_finite_to_commutative (G := A) (Q := S₀) p hsC hcC)
  let U₀ := closedSubgroupAlgebraicGroup U
  have hUzero : U.inclusion ≫ p = 0 :=
    Unipotent.homFromUnipotentToMultiplicativeType U₀ S₀ (U.inclusion ≫ p) hU.2.2.2.1
      (torus_multiplicativeType ((isTorus_iff_coordinates S₀).mp hS))
  let := U.isClosedImmersion
  have hUfin : IsFinite (U.inclusion ≫ p).hom.hom.left :=
    inferInstanceAs (IsFinite (U.inclusion.hom.hom.left ≫ p.hom.hom.left))
  have hUtr := finite_zero_isTrivial (G := U₀) (Q := S₀) _ hUfin hUzero hU.1 hU.2.1
  let : IsIso v := isIso_of_trivial_kernel v U hv hUtr
  have hCTorus : IsTorus C.group :=
    torus_of_iso (asIso v).symm ((isTorus_iff_coordinates D).mpr (torus_of_split hD))
  obtain ⟨c, hcF⟩ := hT.2 C hCTorus hTC
  let := S.isClosedImmersion
  let : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  let : Smooth S.group.X.hom := hsS.1
  have hpa : (c ≫ d) ≫ a = p := by
    apply Grp.hom_ext
    apply (cancel_mono S.inclusion.hom.hom).mp
    change (((c ≫ d) ≫ a) ≫ S.inclusion).hom.hom = (p ≫ S.inclusion).hom.hom
    rw [Category.assoc, ha, Category.assoc, ← hd, ← Category.assoc, hcF, hp]
  let : IsClosedImmersion a.hom.hom.left := factor_closed ha
  let : Surjective a.hom.hom.left :=
    ⟨Function.Surjective.of_comp (show Function.Surjective ((c ≫ d) ≫ a).hom.hom.left from hpa.symm ▸ hps.surj)⟩
  let : IsReduced S.group.X.left := isReduced_of_smooth_over_field S.group.X.hom
  let : IsIso a.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  let : IsIso a := isIso_of_schemeIso a
  exact ⟨inv a, by rw [← ha, IsIso.inv_hom_id_assoc]⟩

private theorem reductive_finiteImage {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) [IsFinite q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hG : IsReductive G) : IsReductive Q := by
  let : GeometricallyConnected G.val.X.hom := hG.2.1
  have hcon : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  obtain ⟨hQ, hQc⟩ := smooth_connected_quotient q hG.1 hcon
  refine ⟨hQ, hQc, ?_⟩
  let K := AlgebraicClosure k
  let G₁ := GeometricGroup G
  let Q₁ := GeometricGroup Q
  let q₁ : G₁.val ⟶ Q₁.val := (groupBaseChange k K).map q
  let : IsFinite q₁.hom.hom.left := fibreMap_property K q @IsFinite inferInstance
  let : Flat q₁.hom.hom.left := fibreMap_property K q @Flat inferInstance
  let : Surjective q₁.hom.hom.left := fibreMap_property K q @Surjective inferInstance
  let : LocallyOfFinitePresentation q₁.hom.hom.left := fibreMap_property K q @LocallyOfFinitePresentation inferInstance
  have hGs : Smooth G₁.val.X.hom := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hG.1
  have hGc : ConnectedSpace G₁.val.X.left := by
    let := hG.2.1
    exact pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := G.val.X.hom))
      K (fieldSpecMap k K)
  let U := geometricUnipotentRadical Q
  have hU := GeometricRadicals.geometricUnipotentRadicalLargest Q
  obtain ⟨C, p, _, hsC, hcC, hpfin, hps, hnorm, _⟩ :=
    reducedIdentityPreimage q₁ hGs hGc U hU.1.2.1
  let H := closedSubgroupAlgebraicGroup C
  let V := closedSubgroupAlgebraicGroup U
  have hunip : Specs.Unipotent.IsUnipotent H := by
    apply TorusFreeUnipotent.torusFreeUnipotent H hsC hcC
    intro T hT
    let E := AlgebraicClosure K
    let V' := baseChangedAlgebraicGroup E V
    let T' := closedSubgroupAlgebraicGroup T
    let f : T'.val ⟶ V'.val := T.inclusion ≫ (groupBaseChange K E).map p
    let : IsFinite ((groupBaseChange K E).map p).hom.hom.left :=
      fibreMap_property E p @IsFinite hpfin
    let := T.isClosedImmersion
    have hf : IsFinite f.hom.hom.left := inferInstanceAs
      (IsFinite (T.inclusion.hom.hom.left ≫ ((groupBaseChange K E).map p).hom.hom.left))
    have hz : f = 0 := Unipotent.homFromMultiplicativeTypeToUnipotent T' V' f
      (torus_multiplicativeType ((isTorus_iff_coordinates T').mp hT))
      ((Unipotent.unipotenceFieldExtension (K := E) V).mpr hU.2.1)
    have ht := torus_smooth_connected_solvable T' hT
    exact finite_zero_isTrivial f hf hz ht.1 ht.2.1
  obtain ⟨i, hi⟩ := (GeometricRadicals.geometricUnipotentRadicalLargest G).2.2
    C ⟨hsC, hcC, hnorm hU.1.2.2⟩ hunip
  obtain ⟨e⟩ := hG.2.2
  have hiz : i = 0 := ((Grp.isZero_trivial (SchemeOver K)).of_iso e).eq_zero_of_tgt i
  have hCz : C.inclusion = 0 := by rw [← hi, hiz, zero_comp]
  let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  let : Mono C.inclusion := (Grp.forget (SchemeOver K) ⋙ Over.forget _).mono_of_mono_map
    (show Mono C.inclusion.hom.hom.left from inferInstance)
  have hcZ : IsZero C.group := IsZero.of_mono_eq_zero C.inclusion hCz
  exact surjective_zero_isTrivial (G := H) (Q := V) p hps (hcZ.eq_zero_of_src p) hU.1.1

end Reductivity

section GeometricApplication

open Specs.GeometricRadicals (IsMaximalTorus IsReductive IsTorus)
open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_of_split from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

variable {R A C X M : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing C] [HopfAlgebra R C] [CommGroup X] [CommGroup M] [Algebra.FiniteType R C]

set_option maxHeartbeats 1400000 in
private theorem quotientReductiveFibres (z : X →* M)
    (j : C →ₐc[R] A) (t : A →ₐc[R] MonoidAlgebra R X)
    (t₀ : C →ₐc[R] MonoidAlgebra R ↥z.ker)
    (ht : (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype).comp t₀ = t.comp j)
    (ht₀ : Function.Surjective t₀)
    (hq : IsRightTorsor j ((MonoidAlgebra.mapDomainBialgHom R z).comp t))
    (hred : ReductiveFibres (spectrumOfHopfHom t))
    [Module.Free ℤ (Additive ↥z.ker)] [Module.Finite ℤ (Additive ↥z.ker)] :
    ReductiveFibres (spectrumOfHopfHom t₀) := by
  intro K _ _ _
  let G := fibreGroup K (R := R)
  let Q := affineFibre (R := R) K C
  let d := spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R z.ker.subtype)
  let i := spectrumOfHopfHom t
  let i₀ := spectrumOfHopfHom t₀
  let p := spectrumOfHopfHom j
  obtain ⟨H, e, hTi, hHr, hMT⟩ := hred K
  let q : H.val ⟶ Q.val := e.inv ≫ G.map p
  have hkfin : IsFinite (G.map p).hom.hom.left := fibreMap_property K p @IsFinite hq.1
  have hkflat : Flat (G.map p).hom.hom.left := fibreMap_property K p @Flat hq.2.1
  have hkS : Surjective (G.map p).hom.hom.left := fibreMap_property K p @Surjective hq.2.2.1
  have hkfp : LocallyOfFinitePresentation (G.map p).hom.hom.left :=
    fibreMap_property K p @LocallyOfFinitePresentation hq.2.2.2.1
  let := hkfin
  let := hkflat
  let := hkS
  let := hkfp
  let FF := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let : IsIso e.inv.hom.hom.left := FF.map_isIso e.inv
  let : IsFinite q.hom.hom.left :=
    inferInstanceAs (IsFinite (e.inv.hom.hom.left ≫ (G.map p).hom.hom.left))
  let : Flat q.hom.hom.left :=
    inferInstanceAs (Flat (e.inv.hom.hom.left ≫ (G.map p).hom.hom.left))
  let : Surjective q.hom.hom.left :=
    inferInstanceAs (Surjective (e.inv.hom.hom.left ≫ (G.map p).hom.hom.left))
  let : LocallyOfFinitePresentation q.hom.hom.left :=
    inferInstanceAs (LocallyOfFinitePresentation (e.inv.hom.hom.left ≫ (G.map p).hom.hom.left))
  have hi₀ : IsClosedImmersion i₀.hom.hom.left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom t₀.toAlgHom.toRingHom) ht₀
  have hTK : IsClosedImmersion (G.map i₀).hom.hom.left :=
    fibreMap_property K i₀ @IsClosedImmersion hi₀
  let T : ClosedSubgroup H.val := ⟨_, G.map i ≫ e.hom, hTi⟩
  let T₀ : ClosedSubgroup Q.val := ⟨_, G.map i₀, hTK⟩
  let : Monoid.FG (↥z.ker) := by
    rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]
    infer_instance
  let U := affineFibre (R := R) K (MonoidAlgebra R ↥z.ker)
  have hT₀ : IsTorus T₀.group :=
    (isTorus_iff_coordinates U).mpr (torus_of_split (splitFibreOfFreeLattice (R := R) K ↥z.ker))
  have hd : d ≫ i₀ = i ≫ p :=
    (spectrumOfHopfHom_comp t₀ _).symm.trans
      ((congrArg spectrumOfHopfHom ht).trans (spectrumOfHopfHom_comp j t))
  have hTD : T.inclusion ≫ q = G.map d ≫ T₀.inclusion := by
    change (G.map i ≫ e.hom) ≫ e.inv ≫ G.map p = G.map d ≫ G.map i₀
    rw [Category.assoc, e.hom_inv_id_assoc, ← G.map_comp i p, ← G.map_comp d i₀, hd]
  let : GeometricallyConnected H.val.X.hom := hHr.2.1
  have hC : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  have hMT₀ : IsMaximalTorus T₀ :=
    maximalTorus_finiteImage q hHr.1 hC T T₀ (G.map d) hMT hT₀ hTD
  refine ⟨Q, Iso.refl _, ?_⟩
  dsimp only
  simpa only [Iso.refl_hom, Category.comp_id] using
    (show ∃ h : IsClosedImmersion (G.map i₀).hom.hom.left,
      IsReductive Q ∧ IsMaximalTorus ⟨_, G.map i₀, h⟩ from
    ⟨hTK, reductive_finiteImage q hHr, hMT₀⟩)

end GeometricApplication

set_option maxHeartbeats 1800000 in
private theorem geometricQuotient : GeometricQuotient.{u} := by
  let R := IntegralRing.{u}
  intro A X M I _ _ _ _ _ _ _ z t π x negative positive opposite α coroot rankOne
    hz ht hc hs hred _ hmem hopen hroot
  let : IsNoetherianRing R := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let : Fintype M := Fintype.ofFinite M
  obtain ⟨hAf, hAa⟩ := spectrumCoordinateProperties R A hs
  let := hAf
  let := hAa
  have hπ : Function.Surjective π := (characterRestriction_surjective z hz).comp ht
  obtain ⟨_, _, _, _, hflat, hfp, _⟩ := coordinateQuotient π hπ
  let B := ↥(invariants π)
  let hB : HopfAlgebra R B := invariantHopfAlgebra π hc
  let : HopfAlgebra R B := hB
  let j : B →ₐc[R] A := quotientInclusion π hc
  let : Algebra.FinitePresentation R B := hfp
  obtain ⟨t₀, ht₀, ht₁⟩ := quotientTorus z t ht hc
  have hTor : IsRightTorsor j π := spectrumTorsor π hc hπ
  have hBQ : Flat (HopfSpectrum R B).X.hom := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  have hBF : LocallyOfFinitePresentation (HopfSpectrum R B).X.hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨hFree, hFinite⟩ := characterKernel_finite_free z
  let := hFree
  let := hFinite
  have hQR : ReductiveFibres (spectrumOfHopfHom t₀) :=
    quotientReductiveFibres z j t t₀ ht₀ ht₁ hTor hred
  obtain ⟨hopen₀, hPB⟩ := quotientCell z hz t j t₀ ht₀ x negative positive hopen hc hTor
  let x₀ := fun i => (x i).comp j.toAlgHom
  have hRank (i : I) : RankOneCompatibility t₀ (x₀ i) (x₀ (opposite i))
      ((coroot i).comp z.ker.subtype) (pushforwardRankOne j (rankOne i)) :=
    rankOneCompatibility_pushforward j t t₀ z.ker.subtype ht₀ (hroot i).2.2
  have hZero (i : I) : zeroParameter R ≫ spectrumPoint (x₀ i) =
      (1 : RootLine R ⟶ (HopfSpectrum R B).X) :=
    rankOne_root_zero t₀ _ _ _ _ (hRank i)
  let : IsFinite (spectrumOfHopfHom j).hom.hom.left := hTor.1
  refine ⟨hB, j, t₀, (fun _ => rfl), hTor, hBQ, hBF, hQR, hFree, hFinite, ht₀, hopen₀, hPB, ?_⟩
  intro i
  have hα := rootCharacter_trivial z t (x i) (α i) (hroot i).1 hc (hroot i).2.1
  exact ⟨quotient_rootRestriction_surjective j t₀ x negative positive hZero hopen₀
      (hmem i) (hroot i).1, hα,
    rootScalarAction_descends z t j t₀ ht₀ (hroot i).2.1 hα,
    pushforwardRankOne j (rankOne i), (fun _ _ => rfl), hRank i⟩

/-- The integral central quotient construction under the designated upstream premises.
The construction starts from the marked integral group given in the statement. -/
theorem integralCentralQuotient_conditional
    (_ : Specs.IntegralRootRelations.RankTwo.CentralBracketCoefficientsIntegral)
    (_ : Specs.IntegralRootRelations.FundamentalWeights.{u})
    (_ : Specs.IntegralRootRelations.Statement.{u})
    (_ : Specs.IntegralRootRelations.RelationsInRealization.{u})
    (_ : Specs.IntegralRootRelations.RankOneDenominator.{u}) :
    Specs.IntegralCentralQuotient.Statement.{u} :=
  ⟨coordinateQuotient, hopfQuotient, geometricQuotient⟩

end

end Geometry

end LinearAlgebraicGroups.Classification.IntegralCentralQuotient

universe v8_closure_e261a9fd9cc61ca1_u0
theorem _root_.«LinearAlgebraicGroups».«Classification».«IntegralCentralQuotient».«integralCentralQuotient» : _root_.«LinearAlgebraicGroups».«Specs».«IntegralCentralQuotient».«Statement».{v8_closure_e261a9fd9cc61ca1_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«IntegralCentralQuotient».«integralCentralQuotient_conditional».{v8_closure_e261a9fd9cc61ca1_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRootRelations».«RankTwo».«centralBracketCoefficients_integral») (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRootRelations».«fundamentalWeights».{v8_closure_e261a9fd9cc61ca1_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRootRelations».«integralRootRelations».{v8_closure_e261a9fd9cc61ca1_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRootRelations».«integralRootRelationsForRealization».{v8_closure_e261a9fd9cc61ca1_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«IntegralRootRelations».«rankOneDenominator».{v8_closure_e261a9fd9cc61ca1_u0})
