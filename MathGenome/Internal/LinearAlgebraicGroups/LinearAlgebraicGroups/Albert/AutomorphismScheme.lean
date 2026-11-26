import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.AutomorphismScheme
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticJordan
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Basis.Bilinear

namespace LinearAlgebraicGroups.Albert.Automorphisms

open TensorProduct
open AlgebraicGeometry CategoryTheory Opposite
open Specs.LinearAlgebraicGroups.Albert
open Specs.LinearAlgebraicGroups.Albert.Automorphisms
open scoped DualNumber

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem bilinearUnitDerivation : BilinearUnitDerivation.{u,v} := by
  intro R _ M _ _ A D h e he
  have hh := h e e
  rw [A.unit_mul e he, A.unit_mul e he, A.mul_unit e he] at hh
  exact add_left_cancel ((add_zero (D e)).trans hh).symm

section DualNumbers

local notation "E" => DualNumber R
local notation "ME" => E ⊗[R] M

private def includeModule : M →ₗ[R] ME := TensorProduct.mk R E M 1

private def epsilonModule : M →ₗ[R] ME := TensorProduct.mk R E M ε

private def firstCoefficient : ME →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp dualModuleReduction

private def secondCoefficient : ME →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp
    ((TrivSqZeroExt.sndHom R R).rTensor M)

@[simp] private theorem firstCoefficient_tmul (a : E) (m : M) :
    firstCoefficient (a ⊗ₜ[R] m) = a.fst • m := rfl

@[simp] private theorem secondCoefficient_tmul (a : E) (m : M) :
    secondCoefficient (a ⊗ₜ[R] m) = a.snd • m := rfl

private theorem dualCoefficient_expansion (x : ME) :
    includeModule (firstCoefficient x) + epsilonModule (secondCoefficient x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      simp only [firstCoefficient_tmul, secondCoefficient_tmul]
      change 1 ⊗ₜ[R] (a.fst • m) + ε ⊗ₜ[R] (a.snd • m) = a ⊗ₜ[R] m
      rw [← smul_tmul, ← smul_tmul, ← add_tmul]
      congr 1
      ext <;> simp
  | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, hx, hy]

private theorem scalar_eps_tmul (x : M) :
    (ε : E) • (1 ⊗ₜ[R] x : ME) = ε ⊗ₜ[R] x := by
  rw [smul_tmul', smul_eq_mul, mul_one]

private theorem infinitesimal_apply (D : Module.End R M) (x : ME) :
    infinitesimal D x = x + (ε : E) • D.baseChange E x := rfl

private theorem squareZero_cancel {S P : Type*} [CommRing S] [AddCommGroup P] [Module S P]
    (D : Module.End S P) (t : S) (ht : t * t = 0) (x : P) :
    (x + t • (-D) x) + t • D (x + t • (-D) x) = x := by
  simp only [LinearMap.neg_apply, smul_neg, ← sub_eq_add_neg]
  rw [map_sub, map_smul, smul_sub, smul_smul, ht, zero_smul, sub_zero, sub_add_cancel]

private theorem squareZero_cancel_reverse {S P : Type*} [CommRing S] [AddCommGroup P] [Module S P]
    (D : Module.End S P) (t : S) (ht : t * t = 0) (x : P) :
    (x + t • D x) + t • (-D) (x + t • D x) = x := by
  simpa only [neg_neg] using squareZero_cancel (-D) t ht x

private def infinitesimalUnit (D : Module.End R M) : (Module.End E ME)ˣ where
  val := infinitesimal D
  inv := infinitesimal (-D)
  val_inv := by
    apply LinearMap.ext
    intro x
    change infinitesimal D (infinitesimal (-D) x) = x
    simpa only [infinitesimal_apply, LinearMap.baseChange_neg] using
      squareZero_cancel (D.baseChange E) ε DualNumber.eps_mul_eps x
  inv_val := by
    apply LinearMap.ext
    intro x
    change infinitesimal (-D) (infinitesimal D x) = x
    simpa only [infinitesimal_apply, LinearMap.baseChange_neg] using
      squareZero_cancel_reverse (D.baseChange E) ε DualNumber.eps_mul_eps x

private theorem infinitesimal_reduction (D : Module.End R M) (m : M) :
    dualModuleReduction (infinitesimal D (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] m := by
  simp [infinitesimal_apply, scalar_eps_tmul, dualModuleReduction]

private theorem infinitesimal_injective :
    Function.Injective (infinitesimal (R := R) (M := M)) := by
  intro D F h
  apply LinearMap.ext
  intro m
  have hh := congrArg (fun a : Module.End E ME => secondCoefficient (a (1 ⊗ₜ[R] m))) h
  simpa [infinitesimal_apply, scalar_eps_tmul] using hh

private theorem exists_infinitesimal (g : Module.End E ME)
    (h : ∀ m : M, dualModuleReduction (g (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] m) :
    ∃ D : Module.End R M, g = infinitesimal D := by
  let g₀ : M →ₗ[R] ME :=
    { toFun := fun m => g (1 ⊗ₜ[R] m)
      map_add' := fun x y => by rw [tmul_add, map_add]
      map_smul' := fun r m => by
        change g (1 ⊗ₜ[R] (r • m)) = r • g (1 ⊗ₜ[R] m)
        rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
        have he : ((algebraMap R E r) ⊗ₜ[R] m) =
            algebraMap R E r • (1 ⊗ₜ[R] m : ME) := by rw [smul_tmul', smul_eq_mul, mul_one]
        rw [he, map_smul]
        exact algebraMap_smul E r _ }
  let D := secondCoefficient.comp g₀
  refine ⟨D, ?_⟩
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  suffices hg : g (1 ⊗ₜ[R] m) = infinitesimal D (1 ⊗ₜ[R] m) by
    have ha : a ⊗ₜ[R] m = a • (1 ⊗ₜ[R] m : ME) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [ha, map_smul, map_smul, hg]
  clear a
  have hf : firstCoefficient (g (1 ⊗ₜ[R] m)) = m := by
    change (TensorProduct.lid R M) (dualModuleReduction (g (1 ⊗ₜ[R] m))) = m
    rw [h]
    simp
  calc
    _ = includeModule (firstCoefficient (g (1 ⊗ₜ[R] m))) +
          epsilonModule (secondCoefficient (g (1 ⊗ₜ[R] m))) :=
      (dualCoefficient_expansion _).symm
    _ = _ := by rw [hf]; simp [includeModule, epsilonModule, D, g₀, infinitesimal_apply, scalar_eps_tmul]


private theorem tangentEquivalence
    (P : Module.End E ME → Prop) (Q : Module.End R M → Prop)
    (h : ∀ D, P (infinitesimal D) ↔ Q D) :
    ∃ e : {D // Q D} ≃ Tangent P, ∀ D, (e D).val.val = infinitesimal D.val := by
  let f : {D // Q D} → Tangent P := fun d =>
    ⟨infinitesimalUnit d.val, (h d.val).mpr d.property, infinitesimal_reduction d.val⟩
  have hi : Function.Injective f := fun d d' he =>
    Subtype.ext (infinitesimal_injective (congrArg (fun g : Tangent P => g.val.val) he))
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨D, hD⟩ := exists_infinitesimal g.val.val g.property.2
    refine ⟨⟨D, (h D).mp (hD ▸ g.property.1)⟩, ?_⟩
    exact Subtype.ext (Units.ext hD.symm)
  exact ⟨Equiv.ofBijective f ⟨hi, hs⟩, fun _ => rfl⟩

private theorem infinitesimal_fixes (D : Module.End R M) (e : M) :
    infinitesimal D (1 ⊗ₜ[R] e) = 1 ⊗ₜ[R] e ↔ D e = 0 := by
  simp only [infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul]
  have he : (1 ⊗ₜ[R] e : ME) + ε ⊗ₜ[R] D e = 1 ⊗ₜ[R] e ↔
      (ε ⊗ₜ[R] D e : ME) = 0 := by
    nth_rw 2 [← add_zero (1 ⊗ₜ[R] e : ME)]
    exact add_left_cancel_iff
  rw [he]
  constructor
  · intro h
    have he := congrArg (secondCoefficient (R := R) (M := M)) h
    simpa using he
  · intro h
    rw [h, tmul_zero]

end DualNumbers

section Bilinear

variable {S : Type u} [CommRing S] [Algebra R S]

private theorem bilinear_eq_of_tmul {b c : LinearMap.BilinMap S (S ⊗[R] M) (S ⊗[R] M)}
    (h : ∀ m n : M, b (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] n) = c (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] n)) :
    b = c := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  apply TensorProduct.AlgebraTensorModule.ext
  intro s n
  have ha : a ⊗ₜ[R] m = a • (1 ⊗ₜ[R] m : S ⊗[R] M) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hs : s ⊗ₜ[R] n = s • (1 ⊗ₜ[R] n : S ⊗[R] M) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  simp only [ha, hs, map_smul, LinearMap.smul_apply, h]

private def leibnizLeft (p : LinearMap.BilinMap S (S ⊗[R] M) (S ⊗[R] M))
    (D : Module.End S (S ⊗[R] M)) := p.compr₂ D

private def leibnizRight (p : LinearMap.BilinMap S (S ⊗[R] M) (S ⊗[R] M))
    (D : Module.End S (S ⊗[R] M)) := LinearMap.compl₁₂ p D .id + LinearMap.compl₁₂ p .id D

private theorem derivation_baseChange {D : Module.End R M} {p : LinearMap.BilinMap R M M}
    (h : IsDerivation p D) : IsDerivation (p.baseChange S) (D.baseChange S) := by
  have hb : leibnizLeft (p.baseChange S) (D.baseChange S) =
      leibnizRight (p.baseChange S) (D.baseChange S) := by
    apply bilinear_eq_of_tmul
    intro m n
    simp [leibnizLeft, leibnizRight, h m n, tmul_add]
  intro x y
  exact DFunLike.congr_fun (DFunLike.congr_fun hb x) y

private theorem bilinear_expand {S P : Type*} [CommRing S] [AddCommGroup P] [Module S P]
    (p : LinearMap.BilinMap S P P) (d : Module.End S P) (t : S) (ht : t * t = 0)
    (x y : P) :
    p x y + t • d (p x y) = p (x + t • d x) (y + t • d y) ↔
      t • d (p x y) = t • (p (d x) y + p x (d y)) := by
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_add, smul_smul,
    ht, zero_smul, add_zero]
  rw [add_assoc, add_left_cancel_iff]

private theorem infinitesimal_product_iff (b : LinearMap.BilinMap R M M) (D : Module.End R M) :
    (∀ x y, infinitesimal D (b.baseChange (DualNumber R) x y) =
      b.baseChange (DualNumber R) (infinitesimal D x) (infinitesimal D y)) ↔
      IsDerivation b D := by
  let p := b.baseChange (DualNumber R)
  let d := D.baseChange (DualNumber R)
  have hexpand (x y : DualNumber R ⊗[R] M) :
      infinitesimal D (p x y) = p (infinitesimal D x) (infinitesimal D y) ↔
        (ε : DualNumber R) • d (p x y) = (ε : DualNumber R) • (p (d x) y + p x (d y)) := by
    simp only [infinitesimal_apply]
    exact bilinear_expand p d ε DualNumber.eps_mul_eps x y
  constructor
  · intro h x y
    have he := (hexpand (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)).mp (h _ _)
    have he' : (ε : DualNumber R) • ((1 : DualNumber R) ⊗ₜ[R] D (b x y)) =
        (ε : DualNumber R) • ((1 : DualNumber R) ⊗ₜ[R] (b (D x) y + b x (D y))) := by
      simpa only [p, d, LinearMap.BilinMap.baseChange_tmul, LinearMap.baseChange_tmul, one_mul,
        tmul_add] using he
    rw [scalar_eps_tmul, scalar_eps_tmul] at he'
    simpa using congrArg (secondCoefficient (R := R) (M := M)) he' 
  · intro h x y
    apply (hexpand x y).mpr
    exact congrArg ((ε : DualNumber R) • ·) (derivation_baseChange (S := DualNumber R) h x y)

private theorem infinitesimal_bilinear_iff (A : BilinearAlgebra R M) (D : Module.End R M) :
    PreservesBilinear A (DualNumber R) (infinitesimal D) ↔ IsDerivation A.product D := by
  constructor
  · intro h
    exact (infinitesimal_product_iff A.product D).mp h.2
  · intro h
    exact ⟨fun e he => (infinitesimal_fixes D e).mpr (bilinearUnitDerivation A D h e he),
      (infinitesimal_product_iff A.product D).mpr h⟩

theorem bilinearTangent : BilinearTangent.{u,v} := by
  intro R _ M _ _ A
  exact tangentEquivalence _ _ (infinitesimal_bilinear_iff A)

end Bilinear

section Quadratic

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

private theorem baseChange_natural (f : S →ₐ[R] T) (D : Module.End R M) (x : S ⊗[R] M) :
    f.toLinearMap.rTensor M (D.baseChange S x) =
      D.baseChange T (f.toLinearMap.rTensor M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem polar_natural (J : QuadraticJordan R M) (f : S →ₐ[R] T)
    (x z y : S ⊗[R] M) :
    f.toLinearMap.rTensor M (J.polar S x z y) =
      J.polar T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M z)
        (f.toLinearMap.rTensor M y) := by
  change f.toLinearMap.rTensor M (J.op S (x + z) y - J.op S x y - J.op S z y) =
    J.op T (f.toLinearMap.rTensor M x + f.toLinearMap.rTensor M z) (f.toLinearMap.rTensor M y) -
      J.op T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y) -
      J.op T (f.toLinearMap.rTensor M z) (f.toLinearMap.rTensor M y)
  simp only [map_sub, J.natural, map_add]

private def operatorDefect {K P : Type*} [CommRing K] [AddCommGroup P] [Module K P]
    (q : QuadraticMap K P (Module.End K P)) (d : Module.End K P) :
    QuadraticMap K P (Module.End K P) :=
  (LinearMap.mulLeft K d).compQuadraticMap' q -
    ((LinearMap.mulRight K d).compQuadraticMap' q +
      LinearMap.BilinMap.toQuadraticMap
        (LinearMap.compl₁₂ (QuadraticMap.polarBilin (R := K) (N := Module.End K P) q) .id d))

private def quadraticDefect (J : QuadraticJordan R M) (D : Module.End R M) :
    QuadraticMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M)) :=
  operatorDefect (J.op S) (D.baseChange S)

private theorem quadraticDefect_apply (J : QuadraticJordan R M) (D : Module.End R M)
    (x y : S ⊗[R] M) :
    quadraticDefect J D x y =
      D.baseChange S (J.op S x y) -
        (J.op S x (D.baseChange S y) + J.polar S x (D.baseChange S x) y) := rfl

private theorem quadraticDefect_natural (J : QuadraticJordan R M) (D : Module.End R M)
    (f : S →ₐ[R] T) (x y : S ⊗[R] M) :
    f.toLinearMap.rTensor M (quadraticDefect J D x y) =
      quadraticDefect J D (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y) := by
  simp only [quadraticDefect_apply, map_sub, map_add, baseChange_natural, J.natural, polar_natural]

private theorem zero_sub_twice {P : Type*} [AddGroup P] : (0 : P) - 0 - 0 = 0 := by simp

/-- The diagonal and the polar values detect a quadratic map on a spanning family. -/
private theorem quadratic_zero_of_tmul
    (Q : QuadraticMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M)))
    (h : ∀ m n : M, Q (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] n) = 0) : Q = 0 := by
  have hQ (m : M) : Q (1 ⊗ₜ[R] m) = 0 := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a n
    have ha : a ⊗ₜ[R] n = a • (1 ⊗ₜ[R] n : S ⊗[R] M) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    simp [ha, h]
  let pol := QuadraticMap.polarBilin (R := S) (N := Module.End S (S ⊗[R] M)) Q
  have hpol : pol = 0 := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    apply TensorProduct.AlgebraTensorModule.ext
    intro b n
    have ha : a ⊗ₜ[R] m = a • (1 ⊗ₜ[R] m : S ⊗[R] M) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    have hb : b ⊗ₜ[R] n = b • (1 ⊗ₜ[R] n : S ⊗[R] M) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    have hp : pol (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] n) = 0 := by
      change Q (1 ⊗ₜ[R] m + 1 ⊗ₜ[R] n) - Q (1 ⊗ₜ[R] m) - Q (1 ⊗ₜ[R] n) = 0
      rw [← tmul_add, hQ, hQ, hQ]
      exact zero_sub_twice (P := Module.End S (S ⊗[R] M))
    simp [ha, hb, hp]
  apply QuadraticMap.ext
  intro x
  change Q x = 0
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      have ha : a ⊗ₜ[R] m = a • (1 ⊗ₜ[R] m : S ⊗[R] M) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [ha, Q.map_smul, hQ, smul_zero]
  | add x y hx hy =>
      rw [QuadraticMap.map_add Q, hx, hy]
      have hp : QuadraticMap.polar (N := Module.End S (S ⊗[R] M)) Q x y = 0 :=
        DFunLike.congr_fun (DFunLike.congr_fun hpol x) y
      rw [hp]
      simp


private theorem quadratic_expand {K P : Type*} [CommRing K] [AddCommGroup P] [Module K P]
    (q : QuadraticMap K P (Module.End K P)) (d : Module.End K P)
    (t : K) (ht : t * t = 0) (x y : P) :
    q x y + t • d (q x y) = q (x + t • d x) (y + t • d y) ↔
      t • operatorDefect q d x y = 0 := by
  let b := QuadraticMap.polarBilin (R := K) (N := Module.End K P) q
  have hq : q (x + t • d x) = q x + t • b x (d x) := by
    rw [QuadraticMap.map_add q, QuadraticMap.map_smul, ht, zero_smul, add_zero]
    change q x + b x (t • d x) = _
    rw [map_smul]
  rw [hq]
  have hd : operatorDefect q d x y = d (q x y) - (q x (d y) + b x (d x) y) := rfl
  rw [hd, smul_sub, sub_eq_zero]
  simp only [LinearMap.add_apply, map_add, map_smul, LinearMap.smul_apply, smul_add, smul_smul,
    ht, zero_smul, add_zero, add_assoc, add_left_cancel_iff]
  rw [add_comm (t • b x (d x) y)]

private theorem secondCoefficient_eps (x : DualNumber R ⊗[R] M) :
    secondCoefficient ((ε : DualNumber R) • x) = firstCoefficient x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      rw [smul_tmul', secondCoefficient_tmul, firstCoefficient_tmul, smul_eq_mul]
      simp
  | add x y hx hy =>
      have h : (ε : DualNumber R) • (x + y) = (ε : DualNumber R) • x + (ε : DualNumber R) • y :=
        smul_add (ε : DualNumber R) x y
      rw [h, map_add, map_add, hx, hy]

private theorem quadratic_preservation_defect (J : QuadraticJordan R M) (D : Module.End R M)
    (x y : DualNumber R ⊗[R] M) :
    infinitesimal D (J.op (DualNumber R) x y) =
        J.op (DualNumber R) (infinitesimal D x) (infinitesimal D y) ↔
      (ε : DualNumber R) • quadraticDefect J D x y = 0 := by
  simp only [infinitesimal_apply, quadraticDefect]
  exact quadratic_expand (J.op (DualNumber R)) (D.baseChange (DualNumber R))
    ε DualNumber.eps_mul_eps x y

private theorem infinitesimal_quadratic_iff (J : QuadraticJordan R M) (D : Module.End R M) :
    PreservesQuadratic J (DualNumber R) (infinitesimal D) ↔ IsQuadraticDerivation J D := by
  constructor
  · intro h
    refine ⟨(infinitesimal_fixes D J.unit).mp h.1, ?_⟩
    have hground (m n : M) :
        quadraticDefect J D ((1 : R) ⊗ₜ[R] m) ((1 : R) ⊗ₜ[R] n) = 0 := by
      let f := TrivSqZeroExt.fstHom R R R
      have he := (quadratic_preservation_defect J D (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] n)).mp (h.2 _ _)
      have hcoeff := congrArg (secondCoefficient (R := R) (M := M)) he
      rw [secondCoefficient_eps, map_zero] at hcoeff
      apply (TensorProduct.lid R M).injective
      rw [map_zero]
      simpa only [firstCoefficient, LinearMap.comp_apply, LinearEquiv.coe_coe, dualModuleReduction,
        quadraticDefect_natural, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hcoeff
    intro S _ _ x y
    have hS : quadraticDefect (S := S) J D = 0 := by
      apply quadratic_zero_of_tmul
      intro m n
      have hh := quadraticDefect_natural J D (Algebra.ofId R S)
        ((1 : R) ⊗ₜ[R] m) ((1 : R) ⊗ₜ[R] n)
      rw [hground, map_zero] at hh
      simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hh.symm
    apply sub_eq_zero.mp
    rw [← quadraticDefect_apply, hS]
    rfl
  · intro h
    refine ⟨(infinitesimal_fixes D J.unit).mpr h.1, ?_⟩
    intro x y
    apply (quadratic_preservation_defect J D x y).mpr
    rw [quadraticDefect_apply, h.2 (DualNumber R) x y, sub_self]
    exact smul_zero _

theorem quadraticTangent : QuadraticTangent.{u,v} := by
  intro R _ M _ _ J
  exact tangentEquivalence _ _ (infinitesimal_quadratic_iff J)

end Quadratic

section JordanComparison

private theorem preserves_polar (J : QuadraticJordan R M) (S : Type u) [CommRing S] [Algebra R S]
    {g : Module.End S (S ⊗[R] M)} (h : PreservesQuadratic J S g) (x z y : S ⊗[R] M) :
    g (J.polar S x z y) = J.polar S (g x) (g z) (g y) := by
  change g (J.op S (x + z) y - J.op S x y - J.op S z y) =
    J.op S (g x + g z) (g y) - J.op S (g x) (g y) - J.op S (g z) (g y)
  simp only [map_sub, h.2, map_add]

theorem jordanDerivationComparison : JordanDerivationComparison.{u,v} := by
  intro R _ M _ _ J d hd D
  let g := infinitesimal D
  let p := J.linearProduct (DualNumber R) d
  have hp : (J.groundProduct d).baseChange (DualNumber R) = p :=
    LinearAlgebraicGroups.Albert.QuadraticJordan.groundProduct_baseChange J (DualNumber R) d
  have hprod : (∀ x y, g (p x y) = p (g x) (g y)) ↔ IsDerivation (J.groundProduct d) D := by
    rw [← hp]
    exact infinitesimal_product_iff (J.groundProduct d) D
  rw [← infinitesimal_quadratic_iff, ← hprod]
  constructor
  · intro h x y
    have hl (z w : (DualNumber R) ⊗[R] M) :
        p z w = algebraMap R (DualNumber R) (↑d⁻¹ : R) • J.polar (DualNumber R) z w (1 ⊗ₜ[R] J.unit) :=
      LinearAlgebraicGroups.Albert.QuadraticJordan.linearProduct_apply J (DualNumber R) d z w
    rw [hl, hl, map_smul, preserves_polar J (DualNumber R) h, h.1]
  · intro h
    have hu : g ((1 : DualNumber R) ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] J.unit := by
      let dE := D.baseChange (DualNumber R)
      let e : (DualNumber R) ⊗[R] M := (1 : DualNumber R) ⊗ₜ[R] J.unit
      have hD : IsDerivation p dE := by
        rw [← hp]
        exact derivation_baseChange (hprod.mp h)
      have hunit z : p e z = z :=
        LinearAlgebraicGroups.Albert.QuadraticJordan.linearProduct_unit J (DualNumber R) d hd z
      have hright z : p z e = z := by
        rw [LinearAlgebraicGroups.Albert.QuadraticJordan.linearProduct_comm J (DualNumber R) d]
        exact hunit z
      have he := hD e e
      rw [hunit, hright, hunit] at he
      have hzero := add_left_cancel ((add_zero (dE e)).trans he).symm
      change g e = e
      rw [show g e = e + (ε : DualNumber R) • dE e from infinitesimal_apply D e, hzero]
      exact add_zero _
    refine ⟨hu, ?_⟩
    intro x y
    simp only [LinearAlgebraicGroups.Albert.QuadraticJordan.op_eq_operatorOfProduct J (DualNumber R) d hd]
    change g ((2 : DualNumber R) • p x (p x y) - p (p x x) y) =
      (2 : DualNumber R) • p (g x) (p (g x) (g y)) - p (p (g x) (g x)) (g y)
    simp only [map_sub, map_smul, h]

end JordanComparison
section Commutator

theorem bilinearCommutator : BilinearCommutator.{u,v} := by
  intro R _ M _ _ A D E hD hE x y
  change D (E (A.product x y)) - E (D (A.product x y)) =
    A.product (D (E x) - E (D x)) y + A.product x (D (E y) - E (D y))
  rw [hE x y, hD x y]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  rw [hD (E x) y, hD x (E y), hE (D x) y, hE x (D y)]
  abel

private theorem derivation_polar {K P : Type*} [CommRing K] [AddCommGroup P] [Module K P]
    (Q : QuadraticMap K P (Module.End K P)) (D : Module.End K P)
    (hD : ∀ x y, D (Q x y) = Q x (D y) +
      QuadraticMap.polarBilin (R := K) (N := Module.End K P) Q x (D x) y)
    (x z y : P) :
    let B := QuadraticMap.polarBilin (R := K) (N := Module.End K P) Q
    D (B x z y) = B x z (D y) + B x (D z) y + B z (D x) y := by
  let B := QuadraticMap.polarBilin (R := K) (N := Module.End K P) Q
  change D (B x z y) = B x z (D y) + B x (D z) y + B z (D x) y
  have hb (w : P) : B x z w = Q (x + z) w - Q x w - Q z w := rfl
  rw [hb y, map_sub, map_sub, hD (x + z) y, hD x y, hD z y, hb (D y)]
  rw [QuadraticMap.map_add Q x z]
  simp only [map_add, LinearMap.add_apply]
  abel

private theorem commutator_derivation {K P : Type*} [CommRing K] [AddCommGroup P] [Module K P]
    (Q : QuadraticMap K P (Module.End K P)) (D E : Module.End K P) :
    let B := QuadraticMap.polarBilin (R := K) (N := Module.End K P) Q
    (∀ x y, D (Q x y) = Q x (D y) + B x (D x) y) →
    (∀ x y, E (Q x y) = Q x (E y) + B x (E x) y) →
    ∀ x y, (D * E - E * D) (Q x y) =
      Q x ((D * E - E * D) y) + B x ((D * E - E * D) x) y := by
  let B := QuadraticMap.polarBilin (R := K) (N := Module.End K P) Q
  change (∀ x y, D (Q x y) = Q x (D y) + B x (D x) y) →
    (∀ x y, E (Q x y) = Q x (E y) + B x (E x) y) → _
  intro hD hE x y
  change D (E (Q x y)) - E (D (Q x y)) =
    Q x (D (E y) - E (D y)) + B x (D (E x) - E (D x)) y
  rw [hE x y, hD x y]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  rw [hD x (E y), hE x (D y), derivation_polar Q D hD x (E x) y,
    derivation_polar Q E hE x (D x) y]
  have hs : B (E x) (D x) y = B (D x) (E x) y := by
    change QuadraticMap.polar (N := Module.End K P) Q (E x) (D x) y = _
    rw [QuadraticMap.polar_comm]
    rfl
  rw [hs]
  abel

theorem quadraticCommutator : QuadraticCommutator.{u,v} := by
  intro R _ M _ _ J D E hD hE
  refine ⟨?_, ?_⟩
  · change D (E J.unit) - E (D J.unit) = 0
    rw [hD.1, hE.1, map_zero, map_zero, sub_self]
  · intro S _ _ x y
    simp only [Specs.LinearAlgebraicGroups.Albert.Automorphisms.commutator, show (D * E - E * D).baseChange S =
      D.baseChange S * E.baseChange S - E.baseChange S * D.baseChange S from
      map_sub (Module.End.baseChangeHom R S M) (D * E) (E * D) |>.trans
        (congrArg₂ (· - ·) (LinearMap.baseChange_mul D E) (LinearMap.baseChange_mul E D))]
    exact commutator_derivation (J.op S) (D.baseChange S) (E.baseChange S) (hD.2 S) (hE.2 S) x y

private theorem squareZero_commutator {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (s t : K) (hs : s * s = 0) (ht : t * t = 0) (d e : A) :
    (1 + s • d) * (1 + t • e) * (1 - s • d) * (1 - t • e) =
      1 + (s * t) • (d * e - e * d) := by
  let a := s • d
  let b := t • e
  have h₁ : a * a = 0 := by simp only [a, smul_mul_smul_comm, hs, zero_smul]
  have h₂ : b * b = 0 := by simp only [b, smul_mul_smul_comm, ht, zero_smul]
  have h₃ : a * b * a = 0 := by
    simp only [a, b, smul_mul_smul_comm, show s * t * s = 0 by rw [mul_right_comm, hs, zero_mul],
      zero_smul]
  have h₄ : b * a * b = 0 := by
    simp only [a, b, smul_mul_smul_comm, show t * s * t = 0 by rw [mul_right_comm, ht, zero_mul],
      zero_smul]
  calc
    _ = 1 + (a * b - b * a) - a * a - a * b * a - b * b - a * (b * b) +
        a * a * b + b * a * b + (a * b * a) * b := by
      change (1 + a) * (1 + b) * (1 - a) * (1 - b) = _
      noncomm_ring
    _ = 1 + (s * t) • (d * e - e * d) := by
      rw [h₃, h₄, h₁, h₂]
      simp only [sub_zero, mul_zero, zero_mul, add_zero, a, b, smul_mul_smul_comm, mul_comm t s, smul_sub]

private theorem squareZero_baseChange_commutator {B : Type u} [CommRing B] [Algebra R B]
    (D E : Module.End R M) (s t : B) (hs : s * s = 0) (ht : t * t = 0) :
    (1 + s • D.baseChange B) * (1 + t • E.baseChange B) *
        (1 - s • D.baseChange B) * (1 - t • E.baseChange B) =
      1 + (s * t) • (Specs.LinearAlgebraicGroups.Albert.Automorphisms.commutator D E).baseChange B := by
  let F := Module.End.baseChangeHom R B M
  change _ = 1 + (s * t) • F (D * E - E * D)
  rw [map_sub, map_mul, map_mul]
  exact squareZero_commutator s t hs ht (D.baseChange B) (E.baseChange B)

theorem infinitesimalCommutator : InfinitesimalCommutator.{u,v} := by
  intro R _ M _ _ D E
  let B := LinearAlgebraicGroups.InfinitesimalCommutator.TwoVariables R
  let s : B := TrivSqZeroExt.inl (ε : DualNumber R)
  let t : B := ε
  have hs : s * s = 0 := by
    change (TrivSqZeroExt.inlAlgHom R (DualNumber R) (DualNumber R)) ε *
      (TrivSqZeroExt.inlAlgHom R (DualNumber R) (DualNumber R)) ε = 0
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  exact squareZero_baseChange_commutator D E s t hs DualNumber.eps_mul_eps

end Commutator

section Matrices

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {S : Type u} [CommRing S] [Algebra R S]

local notation "C" => MatrixCoordinates R n

private abbrev polynomialMatrix : Matrix n n (MvPolynomial (n × n) R) :=
  genericMatrix R n

private theorem universalDet_isUnit : IsUnit (coordinateMatrix (R := R) (ι := n)).det := by
  change IsUnit ((algebraMap (MvPolynomial (n × n) R) C).mapMatrix (polynomialMatrix (R := R))).det
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (polynomialMatrix (R := R) (n := n)).det

private def evaluateMatrix (f : C →ₐ[R] S) : Matrix.GeneralLinearGroup n S :=
  Matrix.GeneralLinearGroup.mk'' (f.mapMatrix coordinateMatrix) (by
    rw [← AlgHom.map_det]
    exact (universalDet_isUnit (R := R) (n := n)).map f)

private def matrixEvaluation (g : Matrix.GeneralLinearGroup n S) :
    MvPolynomial (n × n) R →ₐ[R] S :=
  MvPolynomial.aeval (fun ij => g.val ij.1 ij.2)

private theorem matrixEvaluation_det (g : Matrix.GeneralLinearGroup n S) :
    IsUnit (matrixEvaluation (R := R) g (polynomialMatrix (R := R)).det) := by
  have h : (matrixEvaluation (R := R) g).mapMatrix polynomialMatrix = g.val := by
    ext i j
    exact MvPolynomial.aeval_X _ (i, j)
  rw [AlgHom.map_det, h]
  exact (Matrix.GeneralLinearGroup.det g).isUnit

private def evaluateCoordinates (g : Matrix.GeneralLinearGroup n S) : C →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (polynomialMatrix (R := R) (n := n)).det (matrixEvaluation_det g)

@[simp] private theorem evaluateCoordinates_entry (g : Matrix.GeneralLinearGroup n S) (i j : n) :
    evaluateCoordinates (R := R) g (coordinateMatrix i j) = g.val i j := by
  change evaluateCoordinates (R := R) g
    (algebraMap (MvPolynomial (n × n) R) C (MvPolynomial.X (i,j))) = _
  rw [evaluateCoordinates, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (S := C)]
  exact MvPolynomial.aeval_X _ (i,j)

private theorem coordinate_ext {f g : C →ₐ[R] S}
    (h : ∀ i j, f (coordinateMatrix i j) = g (coordinateMatrix i j)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (polynomialMatrix (R := R) (n := n)).det)
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact h i j

private def matrixCoordinateEquiv : (C →ₐ[R] S) ≃ Matrix.GeneralLinearGroup n S where
  toFun := evaluateMatrix
  invFun := evaluateCoordinates
  left_inv f := coordinate_ext fun i j => evaluateCoordinates_entry (evaluateMatrix f) i j
  right_inv g := Matrix.GeneralLinearGroup.ext fun i j => evaluateCoordinates_entry g i j

theorem matrixCoordinateEvaluation : MatrixCoordinateEvaluation.{u} := by
  intro R n _ _ _ S _ _
  exact ⟨matrixCoordinateEquiv, fun _ => rfl⟩


private def quotientMatrixEquiv {H : MatrixSubgroup R n} {I : Ideal C} (h : CutsOut I H) :
    (C ⧸ I →ₐ[R] S) ≃ H.subgroup S where
  toFun f :=
    let a := f.comp (Ideal.Quotient.mkₐ R I)
    ⟨evaluateMatrix a, (h S a _ rfl).mpr fun x hx => by
      change f (Ideal.Quotient.mk I x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
  invFun g :=
    let a := evaluateCoordinates g.val
    Ideal.Quotient.liftₐ I a ((h S a g.val
      (Matrix.ext fun i j => (evaluateCoordinates_entry g.val i j).symm)).mp g.property)
  left_inv f := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (evaluateCoordinates
      (evaluateMatrix (f.comp (Ideal.Quotient.mkₐ R I)))) a = f (Ideal.Quotient.mk I a)
    exact DFunLike.congr_fun (matrixCoordinateEquiv.left_inv (f.comp (Ideal.Quotient.mkₐ R I))) a
  right_inv g := by
    apply Subtype.ext
    change evaluateMatrix ((Ideal.Quotient.liftₐ _ _ _).comp (Ideal.Quotient.mkₐ R I)) = g.val
    rw [Ideal.Quotient.liftₐ_comp]
    exact matrixCoordinateEquiv.right_inv g.val

private def fullMatrixEquiv : (C →ₐ[R] S) ≃ (MatrixSubgroup.full R n).subgroup S where
  toFun f := ⟨evaluateMatrix f, Subgroup.mem_top _⟩
  invFun g := evaluateCoordinates g.val
  left_inv := matrixCoordinateEquiv.left_inv
  right_inv g := Subtype.ext (matrixCoordinateEquiv.right_inv g.val)

open scoped CategoryTheory.MonObj CategoryTheory.Obj

private abbrev algebraGroupPresheaf (H : MatrixSubgroup R n) :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} := unopUnop _ ⋙ H.points

private def quotientRepresentation {H : MatrixSubgroup R n} {I : Ideal C} (h : CutsOut I H) :
    (algebraGroupPresheaf H ⋙ forget _).RepresentableBy (op (CommAlgCat.of R (C ⧸ I))) where
  homEquiv :=
    { toFun := fun f => quotientMatrixEquiv h f.unop.hom
      invFun := fun g => (CommAlgCat.ofHom ((quotientMatrixEquiv h).symm g)).op
      left_inv := fun f => by
        apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        exact (quotientMatrixEquiv h).left_inv f.unop.hom
      right_inv := (quotientMatrixEquiv h).right_inv }
  homEquiv_comp a f := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

private def fullRepresentation :
    (algebraGroupPresheaf (MatrixSubgroup.full R n) ⋙ forget _).RepresentableBy
      (op (CommAlgCat.of R C)) where
  homEquiv :=
    { toFun := fun f => fullMatrixEquiv f.unop.hom
      invFun := fun g => (CommAlgCat.ofHom (fullMatrixEquiv.symm g)).op
      left_inv := fun f => by
        apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        exact fullMatrixEquiv.left_inv f.unop.hom
      right_inv := fullMatrixEquiv.right_inv }
  homEquiv_comp a f := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

private def includeMatrixSubgroup {H K : MatrixSubgroup R n}
    (h : ∀ S : CommAlgCat.{u} R, H.subgroup S ≤ K.subgroup S) :
    algebraGroupPresheaf H ⟶ algebraGroupPresheaf K where
  app S := GrpCat.ofHom (Subgroup.inclusion (h S.unop.unop))
  naturality _ _ _ := GrpCat.ext fun _ => rfl

private abbrev scalarSpec (R : Type u) [CommRing R] := algSpec (CommRingCat.of R)

private def groupSpecFunctor (R : Type u) [CommRing R] :
    Grp (CommAlgCat.{u} R)ᵒᵖ ⥤ Grp (Over (Spec (CommRingCat.of R))) :=
  letI : (algSpec (CommRingCat.of R)).Braided := AlgebraicGeometry.braidedAlgSpec
  (algSpec (CommRingCat.of R)).mapGrp

set_option maxHeartbeats 800000 in
private def groupSpecPointIso (A : Grp (CommAlgCat.{u} R)ᵒᵖ) :
    (schemePoints R).obj ((groupSpecFunctor R).obj A) ≅
      opOp _ ⋙ yonedaGrpObj A.X := by
  letI : (algSpec (CommRingCat.of R)).Braided := AlgebraicGeometry.braidedAlgSpec
  exact NatIso.ofComponents (fun S => MulEquiv.toGrpIso
    { toEquiv := (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm
      map_mul' := by
        intro x y
        apply (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.injective
        change (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv
          ((algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm (x * y)) = _
        rw [Equiv.apply_symm_apply]
        let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
        change x * y = (algSpec (CommRingCat.of R)).map (ff.preimage x * ff.preimage y)
        have hm := (algSpec (CommRingCat.of R)).map_mul (ff.preimage x) (ff.preimage y)
        exact (hm.trans (congrArg₂ (· * ·) (ff.map_preimage x) (ff.map_preimage y))).symm })
    (fun a => by
      apply GrpCat.ext
      intro x
      let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
      change ff.preimage ((scalarSpec R).map a.op ≫ x) = a.op ≫ ff.preimage x
      apply ff.map_injective
      rw [ff.map_preimage, Functor.map_comp, ff.map_preimage])

set_option maxHeartbeats 800000 in
private theorem representMatrixInclusion {H K : MatrixSubgroup R n}
    {A B : (CommAlgCat.{u} R)ᵒᵖ}
    (r : (algebraGroupPresheaf H ⋙ forget _).RepresentableBy A)
    (s : (algebraGroupPresheaf K ⋙ forget _).RepresentableBy B)
    (h : ∀ S : CommAlgCat.{u} R, H.subgroup S ≤ K.subgroup S)
    (q : B.unop ⟶ A.unop) (hqsurj : Function.Surjective q.hom)
    (hqeval : ∀ (X : (CommAlgCat.{u} R)ᵒᵖ) (a : X ⟶ A),
      (s.homEquiv (a ≫ q.op)).val = (r.homEquiv a).val) :
    ∃ (G L : Grp (Over (Spec (CommRingCat.of R)))) (j : G ⟶ L),
      ∃ (a : G.X ≅ (scalarSpec R).obj A) (b : L.X ≅ (scalarSpec R).obj B)
        (e : (schemePoints R).obj G ≅ H.points) (l : (schemePoints R).obj L ≅ K.points),
        IsClosedImmersion j.hom.hom.left ∧
        j.hom.hom ≫ b.hom = a.hom ≫ (scalarSpec R).map q.op ∧
        ∀ (S : CommAlgCat.{u} R) (g : ((schemePoints R).obj G).obj S),
          (l.hom.app S (((schemePoints R).map j).app S g)).val = (e.hom.app S g).val := by
  let : GrpObj A := GrpObj.ofRepresentableBy A (algebraGroupPresheaf H) r
  let : GrpObj B := GrpObj.ofRepresentableBy B (algebraGroupPresheaf K) s
  let GA : Grp (CommAlgCat.{u} R)ᵒᵖ := Grp.mk A
  let GB : Grp (CommAlgCat.{u} R)ᵒᵖ := Grp.mk B
  let ea := yonedaGrpObjIsoOfRepresentableBy A (algebraGroupPresheaf H) r
  let eb := yonedaGrpObjIsoOfRepresentableBy B (algebraGroupPresheaf K) s
  let inclus := includeMatrixSubgroup h
  let f : GA ⟶ GB := yonedaGrpFullyFaithful.preimage (ea.hom ≫ inclus ≫ eb.inv)
  have hf : yonedaGrp.map f ≫ eb.hom = ea.hom ≫ inclus := by simp [f]
  have hfpoint (X : (CommAlgCat.{u} R)ᵒᵖ) (g : X ⟶ A) :
      (eb.hom.app (op X) (g ≫ f.hom.hom)).val = (ea.hom.app (op X) g).val := by
    have he := DFunLike.congr_fun (congrArg (fun t => (t.app (op X)).hom) hf) g
    exact congrArg Subtype.val he
  have hq : f.hom.hom = q.op := by
    apply s.homEquiv.injective
    apply Subtype.ext
    have hf' := hfpoint A (𝟙 A)
    have hq' := hqeval A (𝟙 A)
    rw [Category.id_comp] at hf' hq'
    exact hf'.trans hq'.symm
  let j := (groupSpecFunctor R).map f
  let e := groupSpecPointIso GA ≪≫ Functor.isoWhiskerLeft (opOp _) ea
  let l := groupSpecPointIso GB ≪≫ Functor.isoWhiskerLeft (opOp _) eb
  refine ⟨_, _, j, Iso.refl _, Iso.refl _, e, l, ?_, ?_, ?_⟩
  · change IsClosedImmersion ((scalarSpec R).map f.hom.hom).left
    rw [hq]
    exact IsClosedImmersion.spec_of_surjective _ hqsurj
  · change (scalarSpec R).map f.hom.hom ≫ 𝟙 _ = 𝟙 _ ≫ (scalarSpec R).map q.op
    simp [hq]
  · intro S g
    let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
    change (eb.hom.app _ (ff.preimage (g ≫ (scalarSpec R).map f.hom.hom))).val =
      (ea.hom.app _ (ff.preimage g)).val
    nth_rw 1 [← ff.map_preimage g]
    rw [← Functor.map_comp, ff.preimage_map]
    exact hfpoint (op S) (ff.preimage g)

theorem closedMatrixSubgroup : ClosedMatrixSubgroup.{u} := by
  intro R n _ _ _ H I h
  exact representMatrixInclusion (quotientRepresentation h) fullRepresentation
    (fun _ => le_top) (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I))
    Ideal.Quotient.mk_surjective (fun _ _ => rfl)

theorem matrixEquationsPresent : MatrixEquationsPresent.{u,v} := by
  intro R n _ _ _ H E h
  let X := evaluateMatrix (R := R) (n := n) (AlgHom.id R (MatrixCoordinates R n))
  let c := E.equation (MatrixCoordinates R n) X
  have hc (S : Type u) [CommRing S] [Algebra R S] (f : MatrixCoordinates R n →ₐ[R] S)
      (g : Matrix.GeneralLinearGroup n S) (hg : g.val = f.mapMatrix coordinateMatrix) (a : E.Index) :
      f (c a) = E.equation S g a := by
    have he : Matrix.GeneralLinearGroup.map f.toRingHom X = g := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [hg]
      rfl
    exact (E.natural f X a).trans (congrArg (fun m => E.equation S m a) he)
  refine ⟨c, ?_, hc⟩
  intro S _ _ f g hg
  rw [h S g]
  change (∀ a, E.equation S g a = 0) ↔ Ideal.span (Set.range c) ≤ RingHom.ker f.toRingHom
  rw [Ideal.span_le, Set.range_subset_iff]
  change (∀ a, E.equation S g a = 0) ↔ ∀ a, f (c a) = 0
  simp only [hc S f g hg]


end Matrices

section FreeModules

open Matrix
open scoped BigOperators

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (b : Module.Basis n R M)

omit [Fintype n] [DecidableEq n] in
private theorem basisChange_natural (f : S →ₐ[R] T) (x : S ⊗[R] M) (i : n) :
    (b.baseChange T).repr (f.toLinearMap.rTensor M x) i =
      f ((b.baseChange S).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, Module.Basis.baseChange_repr_tmul]
      exact (f.toLinearMap.map_smul (b.repr m i) a).symm
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

private theorem action_repr (g : Matrix.GeneralLinearGroup n S) (x : S ⊗[R] M) :
    g.val *ᵥ (b.baseChange S).repr x = (b.baseChange S).repr (matrixAction b S g x) := by
  have h := LinearMap.toMatrix_mulVec_repr (b.baseChange S) (b.baseChange S) (matrixAction b S g) x
  simpa [matrixAction, Matrix.toLinAlgEquiv, LinearMap.toMatrixAlgEquiv] using h

private theorem matrixAction_natural (f : S →ₐ[R] T) (g : Matrix.GeneralLinearGroup n S)
    (x : S ⊗[R] M) :
    f.toLinearMap.rTensor M (matrixAction b S g x) =
      matrixAction b T (Matrix.GeneralLinearGroup.map f.toRingHom g)
        (f.toLinearMap.rTensor M x) := by
  apply (b.baseChange T).repr.injective
  apply Finsupp.ext
  intro i
  rw [basisChange_natural b f, ← action_repr b, ← action_repr b]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.GeneralLinearGroup.map_apply,
    basisChange_natural]
  rfl

private theorem bilinear_natural (p : LinearMap.BilinMap R M M) (f : S →ₐ[R] T)
    (x y : S ⊗[R] M) :
    f.toLinearMap.rTensor M (p.baseChange S x y) =
      p.baseChange T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      induction y using TensorProduct.inductionOn with
      | tmul c n =>
          simp only [LinearMap.BilinMap.baseChange_tmul, LinearMap.rTensor_tmul,
            AlgHom.toLinearMap_apply, map_mul]
      | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

private def matrixActionEquiv (S : Type u) [CommRing S] [Algebra R S] :
    Matrix.GeneralLinearGroup n S ≃* (Module.End S (S ⊗[R] M))ˣ :=
  Units.mapEquiv (Matrix.toLinAlgEquiv (b.baseChange S)).toMulEquiv

private def actionUnits (b : Module.Basis n R M) (S : Type u) [CommRing S] [Algebra R S] :
    Matrix.GeneralLinearGroup n S →* (Module.End S (S ⊗[R] M))ˣ :=
  Units.map (Matrix.toLinAlgEquiv (b.baseChange S)).toMonoidHom


omit [Fintype n] [DecidableEq n] in
private theorem basisOperationTest_natural (f : S →ₐ[R] T) (i : n ⊕ (n × n)) :
    f.toLinearMap.rTensor M (basisOperationTest b S i) = basisOperationTest b T i := by
  rcases i with i | ⟨i, j⟩ <;>
    simp only [basisOperationTest, Module.Basis.baseChange_apply, map_add, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_one]

private def operationEquations
    (p : ∀ (S : Type u) [CommRing S] [Algebra R S], S ⊗[R] M → S ⊗[R] M → S ⊗[R] M)
    (e : Option M)
    (hp : ∀ {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
      (f : S →ₐ[R] T) (x y : S ⊗[R] M), f.toLinearMap.rTensor M (p S x y) =
        p T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y)) :
    MatrixEquations.{u,u} R n where
  Index := OperationEquationIndex n
  finite := inferInstance
  equation S _ _ g a := operationDiscrepancy b S (p S) e g a
  natural := by
    intro S T _ _ _ _ f g a
    rcases a with ⟨k, _ | ⟨i, j⟩⟩
    · cases e with
      | none => simp [operationDiscrepancy]
      | some v =>
          change f ((b.baseChange S).repr (matrixAction b S g (1 ⊗ₜ[R] v) - 1 ⊗ₜ[R] v) k) = _
          rw [← basisChange_natural b f]
          simp only [map_sub, matrixAction_natural, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
            map_one, operationDiscrepancy, Option.elim]
    · let x := basisOperationTest b S i
      let y := b.baseChange S j
      let a := matrixAction b S g
      change f ((b.baseChange S).repr (a (p S x y) - p S (a x) (a y)) k) = _
      rw [← basisChange_natural b f]
      simp only [a, x, y, operationDiscrepancy, map_sub, matrixAction_natural, hp, basisOperationTest_natural,
        Module.Basis.baseChange_apply, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

omit [Fintype n] [DecidableEq n] in
private theorem coordinates_zero_iff (x : S ⊗[R] M) :
    (∀ i : n, (b.baseChange S).repr x i = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply (b.baseChange S).repr.injective
    ext i
    rw [h, map_zero]
    rfl
  · rintro rfl i
    rw [map_zero]
    rfl

private theorem operationEquations_iff
    (p : ∀ (S : Type u) [CommRing S] [Algebra R S], S ⊗[R] M → S ⊗[R] M → S ⊗[R] M)
    (e : Option M)
    (h : ∀ {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
      (f : S →ₐ[R] T) (x y : S ⊗[R] M), f.toLinearMap.rTensor M (p S x y) =
        p T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y))
    (g : Matrix.GeneralLinearGroup n S) :
    (∀ a, (operationEquations b p e @h).equation S g a = 0) ↔
      (∀ u ∈ e, matrixAction b S g (1 ⊗ₜ[R] u) = 1 ⊗ₜ[R] u) ∧
      ∀ i j, matrixAction b S g (p S (basisOperationTest b S i) (b.baseChange S j)) =
        p S (matrixAction b S g (basisOperationTest b S i)) (matrixAction b S g (b.baseChange S j)) := by
  constructor
  · intro hh
    constructor
    · intro u hu
      have he : e = some u := Option.mem_def.mp hu
      apply sub_eq_zero.mp
      apply (coordinates_zero_iff b _).mp
      intro k
      simpa only [operationEquations, operationDiscrepancy, he, Option.elim] using hh (k, .inl ())
    · intro i j
      apply sub_eq_zero.mp
      exact (coordinates_zero_iff b _).mp (fun k => hh (k, .inr (i,j)))
  · rintro ⟨hu, hop⟩ ⟨k, choice⟩
    rcases choice with _ | ⟨i, j⟩
    · cases e with
      | none => simp [operationEquations, operationDiscrepancy]
      | some u =>
          change (b.baseChange S).repr (matrixAction b S g (1 ⊗ₜ[R] u) - 1 ⊗ₜ[R] u) k = 0
          rw [hu u (by simp), sub_self, map_zero]
          rfl
    · change (b.baseChange S).repr
        (matrixAction b S g (p S (basisOperationTest b S i) (b.baseChange S j)) -
          p S (matrixAction b S g (basisOperationTest b S i)) (matrixAction b S g (b.baseChange S j))) k = 0
      rw [hop, sub_self, map_zero]
      rfl


private theorem operation_presentation
    (p : ∀ (S : Type u) [CommRing S] [Algebra R S], S ⊗[R] M → S ⊗[R] M → S ⊗[R] M)
    (e : Option M)
    (hp : ∀ {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
      (f : S →ₐ[R] T) (x y : S ⊗[R] M), f.toLinearMap.rTensor M (p S x y) =
        p T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y))
    (ht : ∀ (S : Type u) [CommRing S] [Algebra R S]
      (a : Module.End S (S ⊗[R] M)),
        (∀ i j, a (p S (basisOperationTest b S i) (b.baseChange S j)) =
          p S (a (basisOperationTest b S i)) (a (b.baseChange S j))) →
        ∀ x y, a (p S x y) = p S (a x) (a y)) :
    ActionPresentation b p e := by
  let E := operationEquations b p e @hp
  let H (S : Type u) [CommRing S] [Algebra R S] : Subgroup (Matrix.GeneralLinearGroup n S) :=
    (operationStabilizer (p S) {z | ∃ u ∈ e, (1 ⊗ₜ[R] u : S ⊗[R] M) = z}).comap (actionUnits b S)
  have hmem (S : Type u) [CommRing S] [Algebra R S] (g : Matrix.GeneralLinearGroup n S) :
      g ∈ H S ↔ ((∀ u ∈ e, matrixAction b S g (1 ⊗ₜ[R] u) = 1 ⊗ₜ[R] u) ∧
        ∀ x y, matrixAction b S g (p S x y) = p S (matrixAction b S g x) (matrixAction b S g y)) := by
    change ((∀ z, (∃ u ∈ e, (1 ⊗ₜ[R] u : S ⊗[R] M) = z) →
      matrixAction b S g z = z) ∧ _) ↔ _
    constructor
    · intro h
      exact ⟨fun u hu => h.1 _ ⟨u, hu, rfl⟩, h.2⟩
    · intro h
      refine ⟨?_, h.2⟩
      rintro _ ⟨u, hu, rfl⟩
      exact h.1 u hu
  have ht' (S : Type u) [CommRing S] [Algebra R S] (g : Matrix.GeneralLinearGroup n S) :
      g ∈ H S ↔ ∀ i, E.equation S g i = 0 := by
    rw [hmem, operationEquations_iff]
    exact and_congr_right fun _ => ⟨fun h _ _ => h _ _, ht S _⟩
  let K : MatrixSubgroup R n :=
    { subgroup := @H
      map_mem := by
        intro S T _ _ _ _ f g hg
        apply (ht' T _).mpr
        intro i
        rw [← E.natural f g i, (ht' S g).mp hg i, map_zero] }
  obtain ⟨c, hc, he⟩ := matrixEquationsPresent R n K E ht'
  exact ⟨K, c, hc, hmem, he⟩

omit [Fintype n] [DecidableEq n] in
private theorem bilinear_tests
    (p : LinearMap.BilinMap S (S ⊗[R] M) (S ⊗[R] M))
    (g : Module.End S (S ⊗[R] M))
    (h : ∀ i j, g (p (basisOperationTest b S i) (b.baseChange S j)) =
      p (g (basisOperationTest b S i)) (g (b.baseChange S j)))
    (x y : S ⊗[R] M) :
    g (p x y) = p (g x) (g y) := by
  have he : p.compr₂ g = LinearMap.compl₁₂ p g g := by
    apply LinearMap.ext_basis (b.baseChange S) (b.baseChange S)
    intro i j
    exact h (.inl i) j
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y

set_option maxHeartbeats 500000 in
theorem bilinearCoordinates : BilinearCoordinates.{u,v} := by
  intro R n _ _ _ M _ _ b A
  exact operation_presentation b (fun S _ _ x y => A.product.baseChange S x y) A.unit
    (bilinear_natural A.product) (fun _ _ _ => bilinear_tests b (A.product.baseChange _))

private theorem quadratic_eq_of_basis {K P N : Type*} [CommRing K] [AddCommGroup P]
    [Module K P] [AddCommGroup N] [Module K N] {n : Type*} [Fintype n]
    (b : Module.Basis n K P) (Q Q' : QuadraticMap K P N)
    (hd : ∀ i, Q (b i) = Q' (b i))
    (hs : ∀ i j, Q (b i + b j) = Q' (b i + b j)) : Q = Q' := by
  classical
  have hB : Q.polarBilin = Q'.polarBilin := by
    apply LinearMap.ext_basis b b
    intro i j
    change Q (b i + b j) - Q (b i) - Q (b j) =
      Q' (b i + b j) - Q' (b i) - Q' (b j)
    rw [hd, hd, hs]
  apply QuadraticMap.ext
  intro x
  have hx : x = ∑ i, (b.repr x i) • b i := (b.sum_repr x).symm
  nth_rw 1 2 [hx]
  let a := b.repr x
  change Q (∑ i, a i • b i) = Q' (∑ i, a i • b i)
  suffices h : ∀ t : Finset n, Q (∑ i ∈ t, a i • b i) = Q' (∑ i ∈ t, a i • b i) from h _
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, QuadraticMap.map_add Q, QuadraticMap.map_add Q',
        ← QuadraticMap.polarBilin_apply_apply, ← QuadraticMap.polarBilin_apply_apply,
        hB, ih, QuadraticMap.map_smul, QuadraticMap.map_smul, hd]

omit [DecidableEq n] in
private theorem quadratic_tests    (p : QuadraticMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M)))
    (g : Module.End S (S ⊗[R] M))
    (h : ∀ i j, g (p (basisOperationTest b S i) (b.baseChange S j)) =
      p (g (basisOperationTest b S i)) (g (b.baseChange S j)))
    (x y : S ⊗[R] M) :
    g (p x y) = p (g x) (g y) := by
  let Q : QuadraticMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M)) :=
    (LinearMap.mulLeft S g).compQuadraticMap' (p)
  let Q' : QuadraticMap S (S ⊗[R] M) (Module.End S (S ⊗[R] M)) :=
    (LinearMap.mulRight S g).compQuadraticMap' ((p).comp g)
  have htest i : Q (basisOperationTest b S i) = Q' (basisOperationTest b S i) :=
    (b.baseChange S).ext (h i)
  have he : Q = Q' :=
    quadratic_eq_of_basis (N := Module.End S (S ⊗[R] M)) (b.baseChange S) Q Q' (fun i => htest (.inl i))
      (fun i j => htest (.inr (i,j)))
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y

theorem quadraticCoordinates : QuadraticCoordinates.{u,v} := by
  intro R n _ _ _ M _ _ b J
  exact operation_presentation b (fun S _ _ x y => J.op S x y) (some J.unit)
    (fun f x y => J.natural f x y) (fun _ _ _ => quadratic_tests b (J.op _))

end FreeModules

section ProjectiveModules

variable {W : Type*} [AddCommGroup W] [Module R W]
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

private structure ModuleRetraction (R : Type*) [CommRing R]
    (M W : Type*) [AddCommGroup M] [AddCommGroup W] [Module R M] [Module R W] where
  proj : W →ₗ[R] M
  incl : M →ₗ[R] W
  proj_incl : ∀ x, proj (incl x) = x

namespace ModuleRetraction

variable (r : ModuleRetraction R M W)

private def baseChange (S : Type u) [CommRing S] [Algebra R S] :
    ModuleRetraction S (S ⊗[R] M) (S ⊗[R] W) where
  proj := r.proj.baseChange S
  incl := r.incl.baseChange S
  proj_incl := by
    have h : r.proj.comp r.incl = LinearMap.id := LinearMap.ext r.proj_incl
    have hb := congrArg (LinearMap.baseChange S) h
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hb
    exact DFunLike.congr_fun hb

private theorem incl_injective : Function.Injective r.incl :=
  Function.LeftInverse.injective r.proj_incl

private def restrict (a : Module.End R W) : Module.End R M :=
  r.proj.comp (a.comp r.incl)

/-- Extend an endomorphism to act as the identity on the complementary summand. -/
private def extend (a : Module.End R M) : Module.End R W :=
  LinearMap.id + r.incl.comp ((a - LinearMap.id).comp r.proj)

@[simp] private theorem restrict_apply (a : Module.End R W) (x : M) :
    r.restrict a x = r.proj (a (r.incl x)) := rfl

private theorem extend_apply (a : Module.End R M) (x : W) :
    r.extend a x = x + r.incl (a (r.proj x) - r.proj x) := rfl

@[simp] private theorem proj_extend (a : Module.End R M) (x : W) :
    r.proj (r.extend a x) = a (r.proj x) := by
  rw [extend_apply, map_add, r.proj_incl, add_sub_cancel]

@[simp] private theorem extend_incl (a : Module.End R M) (x : M) :
    r.extend a (r.incl x) = r.incl (a x) := by
  rw [extend_apply, r.proj_incl, ← map_add, add_sub_cancel]

private def extendHom : Module.End R M →* Module.End R W where
  toFun := r.extend
  map_one' := by
    ext x
    simp [extend_apply]
  map_mul' a b := by
    ext x
    change r.extend (a * b) x = r.extend a (r.extend b x)
    rw [r.extend_apply a, r.proj_extend, r.extend_apply (a * b), r.extend_apply b]
    change x + r.incl (a (b (r.proj x)) - r.proj x) = _
    simp only [map_sub]
    abel

private def extendUnits : (Module.End R M)ˣ →* (Module.End R W)ˣ :=
  Units.map r.extendHom

private theorem extendUnits_injective : Function.Injective r.extendUnits := by
  intro a b h
  apply Units.ext
  ext x
  have hh := DFunLike.congr_fun (congrArg Units.val h) (r.incl x)
  change r.extend a.val (r.incl x) = r.extend b.val (r.incl x) at hh
  simpa only [r.extend_incl] using r.incl_injective (by simpa only [r.extend_incl] using hh)

private theorem extendUnits_range (g : (Module.End R W)ˣ) :
    (∃ a, r.extendUnits a = g) ↔ g.val = r.extend (r.restrict g.val) := by
  constructor
  · rintro ⟨a, rfl⟩
    change r.extend a.val = r.extend (r.restrict (r.extend a.val))
    congr 1
    ext x
    simp [r.proj_incl]
  · intro h
    have hp (x : W) : r.proj (g.val x) = r.restrict g.val (r.proj x) := by
      nth_rw 1 [h]
      exact r.proj_extend _ _
    have hi (x : M) : g.val (r.incl x) = r.incl (r.restrict g.val x) := by
      nth_rw 1 [h]
      exact r.extend_incl _ _
    have hmul (x : W) : g.val (g.inv x) = x := DFunLike.congr_fun g.val_inv x
    have hinv (x : W) : g.inv (g.val x) = x := DFunLike.congr_fun g.inv_val x
    let a : (Module.End R M)ˣ :=
      { val := r.restrict g.val
        inv := r.restrict g.inv
        val_inv := by
          ext x
          change r.restrict g.val (r.proj (g.inv (r.incl x))) = x
          rw [← hp, hmul, r.proj_incl]
        inv_val := by
          ext x
          change r.proj (g.inv (r.incl (r.restrict g.val x))) = x
          rw [← hi, hinv, r.proj_incl] }
    exact ⟨a, Units.ext h.symm⟩

end ModuleRetraction

private theorem changeScalar_linear {N : Type*} [AddCommGroup N] [Module R N]
    (f : S →ₐ[R] T) (a : M →ₗ[R] N) (x : S ⊗[R] M) :
    f.toLinearMap.rTensor N (a.baseChange S x) =
      a.baseChange T (f.toLinearMap.rTensor M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul _ _ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {n : Type u} [Fintype n] [DecidableEq n]
variable (r : ModuleRetraction R M W) (b : Module.Basis n R W)

private def summandSubgroup (S : Type u) [CommRing S] [Algebra R S] :
    Subgroup (Matrix.GeneralLinearGroup n S) :=
  ((r.baseChange S).extendUnits.range).comap (actionUnits b S)

private theorem summandSubgroup_iff (g : Matrix.GeneralLinearGroup n S) :
    g ∈ summandSubgroup r b S ↔
      matrixAction b S g = (r.baseChange S).extend ((r.baseChange S).restrict (matrixAction b S g)) :=
  (r.baseChange S).extendUnits_range (actionUnits b S g)

private def summandEquations : MatrixEquations.{u,u} R n where
  Index := n × n
  finite := inferInstance
  equation S _ _ g ij :=
    let a := matrixAction b S g
    let a' := (r.baseChange S).extend ((r.baseChange S).restrict a)
    (b.baseChange S).repr ((a - a') (b.baseChange S ij.2)) ij.1
  natural := by
    intro S T _ _ _ _ f g ij
    change f ((b.baseChange S).repr _ ij.1) = _
    rw [← basisChange_natural b f]
    simp only [LinearMap.sub_apply, map_sub, matrixAction_natural, ModuleRetraction.extend_apply,
      ModuleRetraction.restrict_apply, ModuleRetraction.baseChange, map_add, changeScalar_linear,
      Module.Basis.baseChange_apply, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

set_option maxRecDepth 2048 in
private theorem summandEquations_iff (g : Matrix.GeneralLinearGroup n S) :
    g ∈ summandSubgroup r b S ↔ ∀ a, (summandEquations r b).equation S g a = 0 := by
  rw [summandSubgroup_iff]
  let m := matrixAction b S g
  let m' := (r.baseChange S).extend ((r.baseChange S).restrict m)
  change m = m' ↔ ∀ a : n × n, (b.baseChange S).repr ((m - m') (b.baseChange S a.2)) a.1 = 0
  constructor
  · intro h ij
    rw [← h, LinearMap.sub_apply, sub_self, map_zero]
    rfl
  · intro h
    apply (b.baseChange S).ext
    intro j
    apply (b.baseChange S).repr.injective
    apply Finsupp.ext
    intro i
    have hi := h (i, j)
    change (b.baseChange S).repr ((m - m') (b.baseChange S j)) i = 0 at hi
    rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply] at hi
    exact sub_eq_zero.mp hi

set_option maxRecDepth 2048 in
private def summandMatrixSubgroup : MatrixSubgroup R n where
  subgroup S _ _ := summandSubgroup r b S
  map_mem := by
    intro S T _ _ _ _ f g h
    apply (summandEquations_iff r b _).mpr
    intro a
    rw [← (summandEquations r b).natural f g a, (summandEquations_iff r b g).mp h a, map_zero]

private def extendMatrix (S : Type u) [CommRing S] [Algebra R S] :
    (Module.End S (S ⊗[R] M))ˣ →* Matrix.GeneralLinearGroup n S :=
  (matrixActionEquiv b S).symm.toMonoidHom.comp (r.baseChange S).extendUnits

private theorem extendMatrix_injective :
    Function.Injective (extendMatrix r b S) :=
  (matrixActionEquiv b S).symm.injective.comp (r.baseChange S).extendUnits_injective

private theorem action_extendMatrix (a : (Module.End S (S ⊗[R] M))ˣ) :
    matrixAction b S (extendMatrix r b S a) = (r.baseChange S).extend a.val :=
  congrArg Units.val ((matrixActionEquiv b S).apply_symm_apply ((r.baseChange S).extendUnits a))

private theorem summandSubgroup_range (g : Matrix.GeneralLinearGroup n S) :
    g ∈ summandSubgroup r b S ↔ ∃ a, extendMatrix r b S a = g := by
  change (∃ a, (r.baseChange S).extendUnits a = matrixActionEquiv b S g) ↔ _
  exact exists_congr fun a => (matrixActionEquiv b S).symm_apply_eq.symm

private def matrixRangeEquiv {D : Type*} [Group D] {H : Subgroup (Matrix.GeneralLinearGroup n S)}
    (f : D →* Matrix.GeneralLinearGroup n S) (hi : Function.Injective f)
    (hr : ∀ g, g ∈ H ↔ ∃ a, f a = g) : H ≃* D :=
  (MulEquiv.ofBijective (f.codRestrict H (fun a => (hr _).mpr ⟨a, rfl⟩))
    ⟨fun a b h => hi (congrArg Subtype.val h), fun g => by
      obtain ⟨a, ha⟩ := (hr _).mp g.property
      exact ⟨a, Subtype.ext ha⟩⟩).symm

private theorem matrixRangeEquiv_toMatrix {D : Type*} [Group D]
    {H : Subgroup (Matrix.GeneralLinearGroup n S)}
    (f : D →* Matrix.GeneralLinearGroup n S) (hi : Function.Injective f)
    (hr : ∀ g, g ∈ H ↔ ∃ a, f a = g) (g : H) :
    f (matrixRangeEquiv f hi hr g) = g.val :=
  congrArg Subtype.val ((matrixRangeEquiv f hi hr).symm_apply_apply g)

private theorem action_restrictMatrix (a : (Module.End S (S ⊗[R] M))ˣ)
    (g : Matrix.GeneralLinearGroup n S) (h : extendMatrix r b S a = g) (x : S ⊗[R] M) :
    a.val x = (r.proj.baseChange S) (matrixAction b S g (r.incl.baseChange S x)) := by
  rw [← h, action_extendMatrix]
  change a.val x = (r.baseChange S).proj
    ((r.baseChange S).extend a.val ((r.baseChange S).incl x))
  rw [ModuleRetraction.extend_incl, (r.baseChange S).proj_incl]

private theorem spectrumOverProperties {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] {X : Over (Spec (CommRingCat.of R))}
    (e : X ≅ (scalarSpec R).obj (op (CommAlgCat.of R A))) :
    IsAffine X.left ∧ LocallyOfFiniteType X.hom := by
  have : IsAffine ((Over.forget _).obj ((scalarSpec R).obj (op (CommAlgCat.of R A)))) := by
    change IsAffine (Spec (CommRingCat.of A))
    infer_instance
  have ha : IsAffine X.left :=
    IsAffine.of_isIso ((Over.forget _).mapIso e).hom
  have hf : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  refine ⟨ha, ?_⟩
  rw [← Over.w e.hom]
  exact locallyOfFiniteType_comp ((Over.forget _).mapIso e).hom
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))

private theorem extendedOperation_iff
    (p : (S ⊗[R] M) → (S ⊗[R] M) → (S ⊗[R] M)) (e : Option M)
    (a : (Module.End S (S ⊗[R] M))ˣ) :
    let rS := r.baseChange S
    let g := rS.extend a.val
    let q := fun x y => rS.incl (p (rS.proj x) (rS.proj y))
    ((∀ u ∈ e.map r.incl, g (1 ⊗ₜ[R] u) = 1 ⊗ₜ[R] u) ∧
      ∀ x y, g (q x y) = q (g x) (g y)) ↔
    ((∀ u ∈ e, a.val (1 ⊗ₜ[R] u) = 1 ⊗ₜ[R] u) ∧
      ∀ x y, a.val (p x y) = p (a.val x) (a.val y)) := by
  let rS := r.baseChange S
  let g := rS.extend a.val
  have hu (u : M) : g (1 ⊗ₜ[R] r.incl u) = 1 ⊗ₜ[R] r.incl u ↔
      a.val (1 ⊗ₜ[R] u) = 1 ⊗ₜ[R] u := by
    change g (rS.incl (1 ⊗ₜ[R] u)) = rS.incl (1 ⊗ₜ[R] u) ↔ _
    rw [ModuleRetraction.extend_incl]
    exact rS.incl_injective.eq_iff
  have hop (x y : S ⊗[R] W) :
      g (rS.incl (p (rS.proj x) (rS.proj y))) = rS.incl (p (rS.proj (g x)) (rS.proj (g y))) ↔
      a.val (p (rS.proj x) (rS.proj y)) = p (a.val (rS.proj x)) (a.val (rS.proj y)) := by
    rw [ModuleRetraction.extend_incl, ModuleRetraction.proj_extend, ModuleRetraction.proj_extend]
    exact rS.incl_injective.eq_iff
  apply and_congr
  · exact ⟨fun h u hem => (hu u).mp (h _ (Option.mem_map_of_mem _ hem)), fun h _ hem => by
        obtain ⟨u, hu', rfl⟩ := Option.mem_map.mp hem
        exact (hu u).mpr (h u hu')⟩
  · refine ⟨fun h x y => ?_, fun h x y => (hop x y).mpr (h _ _)⟩
    simpa only [rS.proj_incl] using
      (hop (rS.incl x) (rS.incl y)).mp (h (rS.incl x) (rS.incl y))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
private theorem summandOperationScheme
    (P : ∀ S : CommAlgCat.{u} R, Subgroup (Module.End S (S ⊗[R] M))ˣ)
    (p : ∀ (S : Type u) [CommRing S] [Algebra R S], S ⊗[R] M → S ⊗[R] M → S ⊗[R] M)
    (e : Option M)
    (hP : ∀ (S : CommAlgCat.{u} R) (a : (Module.End S (S ⊗[R] M))ˣ),
      a ∈ P S ↔
        (∀ u ∈ e, a.val (1 ⊗ₜ[R] u) = 1 ⊗ₜ[R] u) ∧
        ∀ x y, a.val (p S x y) = p S (a.val x) (a.val y))
    (hp : ∀ {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
      (f : S →ₐ[R] T) (x y : S ⊗[R] M),
      f.toLinearMap.rTensor M (p S x y) = p T (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y))
    (ht : ∀ (S : Type u) [CommRing S] [Algebra R S] (a : Module.End S (S ⊗[R] W)),
      let q := fun x y => (r.incl.baseChange S) (p S (r.proj.baseChange S x) (r.proj.baseChange S y))
      (∀ i j, a (q (basisOperationTest b S i) (b.baseChange S j)) =
        q (a (basisOperationTest b S i)) (a (b.baseChange S j))) →
      ∀ x y, a (q x y) = q (a x) (a y)) :
    Nonempty (ClosedLinearSubgroup P) := by
  let q (S : Type u) [CommRing S] [Algebra R S] (x y : S ⊗[R] W) :=
    r.incl.baseChange S (p S (r.proj.baseChange S x) (r.proj.baseChange S y))
  have hq {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
      (f : S →ₐ[R] T) (x y : S ⊗[R] W) :
      f.toLinearMap.rTensor W (q S x y) = q T (f.toLinearMap.rTensor W x) (f.toLinearMap.rTensor W y) := by
    simp only [q, changeScalar_linear, hp]
  obtain ⟨N, c, hc, hN, _⟩ := operation_presentation b q (e.map r.incl) @hq ht
  let K := summandMatrixSubgroup r b
  obtain ⟨d, hd, _⟩ := matrixEquationsPresent R n K (summandEquations r b)
    (fun _ _ _ g => summandEquations_iff r b g)
  let J : Ideal (MatrixCoordinates R n) := Ideal.span (Set.range d)
  let I : Ideal (MatrixCoordinates R n) := J ⊔ Ideal.span (Set.range c)
  let H : MatrixSubgroup R n :=
    { subgroup := fun S _ _ => K.subgroup S ⊓ N.subgroup S
      map_mem := fun f g h => ⟨K.map_mem f g h.1, N.map_mem f g h.2⟩ }
  have hI : CutsOut I H := by
    intro S _ _ f g hg
    change (g ∈ K.subgroup S ∧ g ∈ N.subgroup S) ↔ I ≤ RingHom.ker f.toRingHom
    rw [show I = J ⊔ Ideal.span (Set.range c) from rfl, sup_le_iff]
    exact and_congr (hd S f g hg) (hc S f g hg)
  have hj : J ≤ I := le_sup_left
  let factor := Ideal.Quotient.factorₐ R hj
  have hfactor : Function.Surjective factor := Ideal.Quotient.factor_surjective hj
  obtain ⟨G, L, j, ag, al, eg, el, hjclosed, _, hpoints⟩ :=
    representMatrixInclusion (quotientRepresentation hI) (quotientRepresentation hd)
      (fun _ => inf_le_left) (CommAlgCat.ofHom factor) hfactor (by
        intro X f
        change evaluateMatrix ((f.unop.hom.comp factor).comp (Ideal.Quotient.mkₐ R J)) =
          evaluateMatrix (f.unop.hom.comp (Ideal.Quotient.mkₐ R I))
        rw [AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk])
  have hK (S : CommAlgCat.{u} R) (g : Matrix.GeneralLinearGroup n S) :
      g ∈ K.subgroup S ↔ ∃ a, extendMatrix r b S a = g := summandSubgroup_range r b g
  have hN' (S : CommAlgCat.{u} R) (a : (Module.End S (S ⊗[R] M))ˣ) :
      extendMatrix r b S a ∈ N.subgroup S ↔ a ∈ P S := by
    have hpres := hN S (extendMatrix r b S a)
    dsimp only at hpres
    rw [hpres, action_extendMatrix, hP]
    exact extendedOperation_iff r (p S) e a
  let Eₗ (S : CommAlgCat.{u} R) :=
    matrixRangeEquiv (extendMatrix r b S) (extendMatrix_injective r b) (hK S)
  let f (S : CommAlgCat.{u} R) := (extendMatrix r b S).comp (P S).subtype
  have hf (S : CommAlgCat.{u} R) : Function.Injective (f S) :=
    (extendMatrix_injective r b).comp Subtype.val_injective
  have hH (S : CommAlgCat.{u} R) (g : Matrix.GeneralLinearGroup n S) :
      g ∈ H.subgroup S ↔ ∃ a, f S a = g := by
    change (g ∈ K.subgroup S ∧ g ∈ N.subgroup S) ↔ _
    constructor
    · rintro ⟨hk, hn⟩
      obtain ⟨a, rfl⟩ := (hK S g).mp hk
      exact ⟨⟨a, (hN' S a).mp hn⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ⟨(hK S _).mpr ⟨a, rfl⟩, (hN' S a).mpr ha⟩
  let Eₐ (S : CommAlgCat.{u} R) := matrixRangeEquiv (f S) (hf S) (hH S)
  have : Algebra.FiniteType R (MatrixCoordinates R n ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType R (MatrixCoordinates R n ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R J) Ideal.Quotient.mk_surjective
  have hga := spectrumOverProperties ag
  have hla := spectrumOverProperties al
  have : IsAffine G.X.left := hga.1
  have : IsAffine L.X.left := hla.1
  refine ⟨{ group := G, generalLinear := L, inclusion := j, closed := hjclosed
            groupAffine := hga.1, linearAffine := hla.1
            groupFiniteType := hga.2, linearFiniteType := hla.2
            groupQuasiCompact := inferInstance, linearQuasiCompact := inferInstance
            linearPoints := fun S => (el.app S).groupIsoToMulEquiv.trans (Eₗ S)
            subgroupPoints := fun S => (eg.app S).groupIsoToMulEquiv.trans (Eₐ S)
            evaluatesInclusion := ?_, scalarChange := ?_ }⟩
  · intro S g
    apply extendMatrix_injective r b
    change extendMatrix r b S (Eₗ S (el.hom.app S (((schemePoints R).map j).app S g))) =
      f S (Eₐ S (eg.hom.app S g))
    rw [matrixRangeEquiv_toMatrix, matrixRangeEquiv_toMatrix]
    exact hpoints S g
  · intro S T v g x
    have hnat : el.hom.app T (((schemePoints R).obj L).map v g) =
        K.points.map v (el.hom.app S g) :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (el.hom.naturality v)) g
    change (Eₗ T (el.hom.app T (((schemePoints R).obj L).map v g))).val
        (v.hom.toLinearMap.rTensor M x) =
      v.hom.toLinearMap.rTensor M ((Eₗ S (el.hom.app S g)).val x)
    rw [hnat]
    let gS := el.hom.app S g
    let gT := K.points.map v gS
    rw [action_restrictMatrix r b _ gT.val (matrixRangeEquiv_toMatrix _ _ _ gT),
      action_restrictMatrix r b _ gS.val (matrixRangeEquiv_toMatrix _ _ _ gS),
      changeScalar_linear, matrixAction_natural, changeScalar_linear]
    rfl

theorem bilinearAutomorphismScheme : BilinearAutomorphismScheme.{u,v} := by
  intro R _ M _ _ _ _ A
  obtain ⟨n, proj, incl, _, _, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let r : ModuleRetraction R M (Fin n → R) := ⟨proj, incl, DFunLike.congr_fun h⟩
  let b := (Pi.basisFun R (Fin n)).reindex (Equiv.ulift.{u}).symm
  refine summandOperationScheme r b (fun S => bilinearStabilizer A S)
    (fun S _ _ x y => A.product.baseChange S x y) A.unit (fun S a => mem_bilinearStabilizer A S a)
    (bilinear_natural A.product) ?_
  intro S _ _ g
  exact bilinear_tests b
    ((LinearMap.compl₁₂ (A.product.baseChange S) (proj.baseChange S) (proj.baseChange S)).compr₂
      (incl.baseChange S)) g

theorem quadraticAutomorphismScheme : QuadraticAutomorphismScheme.{u,v} := by
  intro R _ M _ _ _ _ Q
  obtain ⟨n, proj, incl, _, _, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let r : ModuleRetraction R M (Fin n → R) := ⟨proj, incl, DFunLike.congr_fun h⟩
  let b := (Pi.basisFun R (Fin n)).reindex (Equiv.ulift.{u}).symm
  refine summandOperationScheme r b (fun S => quadraticStabilizer Q S)
    (fun S _ _ x y => Q.op S x y) (some Q.unit) ?_ (fun f x y => Q.natural f x y) ?_
  · intro S g
    rw [mem_quadraticStabilizer]
    simp [PreservesQuadratic]
  · intro S _ _ g
    let a : Module.End S (S ⊗[R] M) →ₗ[S] Module.End S (S ⊗[R] (Fin n → R)) :=
      (LinearMap.llcomp S _ _ _ (incl.baseChange S)).comp
        ((LinearMap.llcomp S _ _ _).flip (proj.baseChange S))
    exact quadratic_tests b (a.compQuadraticMap' ((Q.op S).comp (proj.baseChange S))) g

end ProjectiveModules

section TangentComparison

variable {k n : Type u} [Field k] [Fintype n] [DecidableEq n]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable (b : Module.Basis n k V)

private theorem mapMatrixReduction_iff (g : Matrix.GeneralLinearGroup n (DualNumber k)) :
    Matrix.GeneralLinearGroup.map (TrivSqZeroExt.fstHom k k k).toRingHom g = 1 ↔
      ∀ x : V, dualModuleReduction (matrixAction b (DualNumber k) g (1 ⊗ₜ[k] x)) = 1 ⊗ₜ[k] x := by
  let f := TrivSqZeroExt.fstHom k k k
  let g₀ := Matrix.GeneralLinearGroup.map f.toRingHom g
  have hnat (x : V) :
      dualModuleReduction (matrixAction b (DualNumber k) g (1 ⊗ₜ[k] x)) =
        matrixAction b k g₀ (1 ⊗ₜ[k] x) := by
    rw [matrixAction_natural b f, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  have hid : matrixAction b k (1 : Matrix.GeneralLinearGroup n k) = 1 :=
    (Matrix.toLinAlgEquiv (b.baseChange k)).map_one
  change g₀ = 1 ↔ _
  constructor
  · intro h x
    rw [hnat, h, hid]
    rfl
  · intro h
    apply (matrixActionEquiv b k).injective
    apply Units.ext
    change matrixAction b k g₀ = matrixAction b k 1
    rw [hid]
    apply (b.baseChange k).ext
    intro i
    rw [Module.Basis.baseChange_apply]
    exact (hnat (b i)).symm.trans (h (b i))

theorem matrixTangentComparison : MatrixTangentComparison.{u,v} := by
  intro k n _ _ _ V _ _ b H P hP
  let E := DualNumber k
  let ϕ := matrixActionEquiv b (DualNumber k)
  let F := H.points
  let f : DualKernel F → Tangent P := fun g =>
    ⟨ϕ g.toMul.val.val,
      (hP _).mp g.toMul.val.property,
      (mapMatrixReduction_iff b _).mp (congrArg Subtype.val g.toMul.property)⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact ϕ.injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro w
    let g := ϕ.symm w.val
    have hg : ϕ g = w.val := ϕ.apply_symm_apply w.val
    have hgv : matrixAction b (DualNumber k) g = w.val.val := congrArg Units.val hg
    let x : H.subgroup (DualNumber k) :=
      ⟨g, (hP g).mpr (hgv.symm ▸ w.property.1)⟩
    have hr : (F.map (dualReduction k)).hom x = 1 := by
      apply Subtype.ext
      exact (mapMatrixReduction_iff b g).mpr (hgv.symm ▸ w.property.2)
    exact ⟨⟨x, hr⟩, Subtype.ext hg⟩
  exact ⟨Equiv.ofBijective f ⟨hi, hs⟩, fun _ => rfl⟩

theorem matrixInfinitesimalCoefficient : MatrixInfinitesimalCoefficient.{u,v} := by
  intro k n _ _ _ V _ _ b D g h
  let bE := b.baseChange (DualNumber k)
  have he : LinearMap.toMatrix bE bE (matrixAction b (DualNumber k) g) = g.val := by
    change LinearMap.toMatrix bE bE (Matrix.toLin bE bE g.val) = g.val
    exact LinearMap.toMatrix_toLin _ _ _
  apply Matrix.ext
  intro i j
  rw [← he, h, LinearMap.toMatrix_apply]
  change ((bE.repr (infinitesimal D (bE j))) i).snd = _
  rw [show bE j = (1 : DualNumber k) ⊗ₜ[k] b j from Module.Basis.baseChange_apply _ _ _,
    infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul, map_add]
  simp only [bE, Finsupp.add_apply, Module.Basis.baseChange_repr_tmul,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_one, DualNumber.snd_eps,
    smul_eq_mul, mul_one, mul_zero, zero_add, LinearMap.toMatrix_apply]

end TangentComparison

section SchemeTangent

open LinearAlgebraicGroups.InfinitesimalCommutator

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {P : ∀ S : CommAlgCat.{u} k, Subgroup (Module.End S (S ⊗[k] V))ˣ}
variable (G : ClosedLinearSubgroup P)

private abbrev schemeAction (S : CommAlgCat.{u} k) :
    ((schemePoints k).obj G.group).obj S →* (Module.End S (S ⊗[k] V))ˣ :=
  (P S).subtype.comp (G.subgroupPoints S).toMonoidHom

private theorem schemeAction_injective (S : CommAlgCat.{u} k) :
    Function.Injective (schemeAction G S) :=
  Subtype.val_injective.comp (G.subgroupPoints S).injective

set_option maxRecDepth 2048 in
private theorem schemeAction_natural {S T : CommAlgCat.{u} k} (f : S ⟶ T)
    (g : ((schemePoints k).obj G.group).obj S) (x : S ⊗[k] V) :
    (schemeAction G T (((schemePoints k).obj G.group).map f g)).val (f.hom.toLinearMap.rTensor V x) =
      f.hom.toLinearMap.rTensor V ((schemeAction G S g).val x) := by
  let i := (schemePoints k).map G.inclusion
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (i.naturality f)) g
  change i.app T (((schemePoints k).obj G.group).map f g) =
    ((schemePoints k).obj G.generalLinear).map f (i.app S g) at h
  have hS := G.evaluatesInclusion S g
  have hT := G.evaluatesInclusion T (((schemePoints k).obj G.group).map f g)
  rw [h] at hT
  have hnat := G.scalarChange f (i.app S g) x
  rw [hT, hS] at hnat
  exact hnat

private theorem tensorOne_ext {S : Type u} [CommRing S] [Algebra k S]
    {a b : Module.End S (S ⊗[k] V)} (h : ∀ x : V, a (1 ⊗ₜ[k] x) = b (1 ⊗ₜ[k] x)) :
    a = b := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  have hs : s ⊗ₜ[k] x = s • (1 ⊗ₜ[k] x : S ⊗[k] V) := by rw [smul_tmul', smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, h]

private abbrev dualAlgebra := CommAlgCat.of k (DualNumber k)

set_option maxRecDepth 2048 in
private theorem schemeAction_reduces (g : ((schemePoints k).obj G.group).obj (dualAlgebra (k := k))) :
    reduceTangentPoints G.group g = 1 ↔
      ∀ x : V, dualModuleReduction ((schemeAction G dualAlgebra g).val (1 ⊗ₜ[k] x)) =
        1 ⊗ₜ[k] x := by
  let F := (schemePoints k).obj G.group
  let f := dualReduction k
  let K := CommAlgCat.of k k
  have h (x : V) : (schemeAction G K (F.map f g)).val (1 ⊗ₜ[k] x) =
      dualModuleReduction ((schemeAction G dualAlgebra g).val (1 ⊗ₜ[k] x)) := by
    have hn := schemeAction_natural G f g (1 ⊗ₜ[k] x)
    change (schemeAction G K (F.map f g)).val ((TrivSqZeroExt.fstHom k k k 1) ⊗ₜ[k] x) =
      dualModuleReduction ((schemeAction G dualAlgebra g).val (1 ⊗ₜ[k] x)) at hn
    rwa [map_one] at hn
  constructor
  · intro hg x
    rw [← h]
    change F.map f g = 1 at hg
    rw [hg, map_one]
    rfl
  · intro hg
    apply schemeAction_injective G K
    change schemeAction G K (F.map f g) = schemeAction G K 1
    rw [map_one]
    apply Units.ext
    apply tensorOne_ext
    intro x
    exact (h x).trans (hg x)

private theorem squareZero_add {S A : Type*} [CommRing S] [Ring A] [Algebra S A]
    (s : S) (hs : s * s = 0) (d e : A) :
    1 + s • (d + e) = (1 + s • d) * (1 + s • e) := by
  simp only [smul_add, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hs, zero_smul, add_zero]
  abel

private theorem infinitesimal_add (D E : Module.End k V) :
    infinitesimal (D + E) = infinitesimal D * infinitesimal E := by
  simpa only [infinitesimal, LinearMap.baseChange_add] using
    squareZero_add (ε : DualNumber k) DualNumber.eps_mul_eps
      (D.baseChange (DualNumber k) : Module.End (DualNumber k) (DualNumber k ⊗[k] V))
      (E.baseChange (DualNumber k))

private def scalarPerturbation {S : Type u} [CommRing S] [Algebra k S]
    (s : S) (D : Module.End k V) : Module.End S (S ⊗[k] V) :=
  1 + s • D.baseChange S

set_option maxRecDepth 2048 in
private theorem schemeAction_map_infinitesimal {T : CommAlgCat.{u} k} (f : dualAlgebra ⟶ T)
    (g : ((schemePoints k).obj G.group).obj dualAlgebra)
    (D : Module.End k V) (h : (schemeAction G dualAlgebra g).val = infinitesimal D) :
    (schemeAction G T (((schemePoints k).obj G.group).map f g)).val =
      scalarPerturbation (S := T) (f.hom ε) D := by
  apply tensorOne_ext
  intro x
  have hn := schemeAction_natural G f g (1 ⊗ₜ[k] x)
  rw [h, infinitesimal_apply, LinearMap.baseChange_tmul, scalar_eps_tmul, map_add] at hn
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at hn
  rw [hn]
  change _ = (1 ⊗ₜ[k] x) + f.hom ε • D.baseChange T (1 ⊗ₜ[k] x)
  rw [LinearMap.baseChange_tmul, smul_tmul', smul_eq_mul, mul_one]

private theorem scaled_epsilon (c : k) : dualNumberScale c ε = c • (ε : DualNumber k) := by
  apply TrivSqZeroExt.ext <;> simp [dualNumberScale]

private theorem infinitesimal_inverse {T : Type*} [CommRing T]
    {W : Type*} [AddCommGroup W] [Module T W]
    (g : (Module.End T W)ˣ) (s : T) (hs : s * s = 0) (D : Module.End T W)
    (h : g.val = 1 + s • D) :
    g.inv = 1 - s • D := by
  have he : g.val * (1 - s • D) = 1 := by
    rw [h]
    apply LinearMap.ext
    intro x
    change x - s • D x + s • D (x - s • D x) = x
    simpa only [← sub_eq_add_neg, LinearMap.neg_apply, smul_neg] using
      squareZero_cancel D s hs x
  calc
    g.inv = g.inv * (g.val * (1 - s • D)) := by rw [he, mul_one]
    _ = 1 - s • D := by rw [← mul_assoc, g.inv_val, one_mul]

private theorem scalarPerturbation_injective {S : Type u} [CommRing S] [Algebra k S]
    (s : S) (coeff : S →ₗ[k] k) (hc : coeff s = 1) :
    Function.Injective (scalarPerturbation (k := k) (V := V) s) := by
  intro D E h
  apply LinearMap.ext
  intro x
  have he := DFunLike.congr_fun h (1 ⊗ₜ[k] x)
  change (1 ⊗ₜ[k] x) + s • D.baseChange S (1 ⊗ₜ[k] x) =
    (1 ⊗ₜ[k] x) + s • E.baseChange S (1 ⊗ₜ[k] x) at he
  simp only [LinearMap.baseChange_tmul, add_right_inj, smul_tmul', smul_eq_mul, mul_one] at he
  have hm := congrArg (coeff.rTensor V) he
  rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, hc] at hm
  simpa only [TensorProduct.lid_tmul, one_smul] using congrArg (TensorProduct.lid k V) hm

private theorem scalarPerturbation_neg {S : Type u} [CommRing S] [Algebra k S]
    (s : S) (D : Module.End k V) :
    scalarPerturbation s (-D) = 1 - s • D.baseChange S := by
  apply LinearMap.ext
  intro x
  rw [scalarPerturbation, LinearMap.baseChange_neg]
  change x + s • (-(D.baseChange S x)) = x - s • D.baseChange S x
  rw [smul_neg, sub_eq_add_neg]

private theorem scalarPerturbation_inverse {S : Type u} [CommRing S] [Algebra k S]
    (g : (Module.End S (S ⊗[k] V))ˣ) (s : S) (hs : s * s = 0) (D : Module.End k V)
    (h : g.val = scalarPerturbation s D) :
    g.inv = scalarPerturbation s (-D) := by
  rw [scalarPerturbation_neg]
  exact infinitesimal_inverse g s hs (D.baseChange S) h

private theorem scalarPerturbation_commutator {S : Type u} [CommRing S] [Algebra k S]
    (s t : S) (hs : s * s = 0) (ht : t * t = 0) (D E : Module.End k V) :
    scalarPerturbation s D * scalarPerturbation t E *
      scalarPerturbation s (-D) * scalarPerturbation t (-E) =
      scalarPerturbation (s * t) (Specs.LinearAlgebraicGroups.Albert.Automorphisms.commutator D E) := by
  rw [scalarPerturbation_neg, scalarPerturbation_neg]
  exact squareZero_baseChange_commutator D E s t hs ht

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem schemeAction_bracket
    (d : _root_.LinearAlgebraicGroups.Specs.Lie k G.group → Module.End k V)
    (hd : ∀ p, (schemeAction G dualAlgebra p.toMul.val).val = infinitesimal (d p))
    (p q : _root_.LinearAlgebraicGroups.Specs.Lie k G.group) :
    letI := G.groupAffine
    d (_root_.LinearAlgebraicGroups.Specs.intrinsicLieBracket k G.group p q) =
      Specs.LinearAlgebraicGroups.Albert.Automorphisms.commutator (d p) (d q) := by
  have := G.groupAffine
  let F := (schemePoints k).obj G.group
  let B := TwoVariables k
  let C := CommAlgCat.of k B
  let s : B := liftS k ε
  let t : B := liftT k ε
  let st : B := liftST k ε
  have hs : s * s = 0 := by rw [show s = liftS k ε from rfl, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have ht : t * t = 0 := by rw [show t = liftT k ε from rfl, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hst : st = s * t := by
    obtain ⟨e, he⟩ := twoVariablesUniversalProperty k B
    have hh := (he (AlgHom.id k B)).2
    rw [(he (AlgHom.id k B)).1] at hh
    exact hh
  let fs : dualAlgebra ⟶ C := CommAlgCat.ofHom (liftS k)
  let ft : dualAlgebra ⟶ C := CommAlgCat.ofHom (liftT k)
  let fst : dualAlgebra ⟶ C := CommAlgCat.ofHom (liftST k)
  let x := F.map fs p.toMul.val
  let y := F.map ft q.toMul.val
  let z := lieBracket G.group p q
  let w := F.map fst z.toMul.val
  let A := schemeAction G C
  have hx : (A x).val = scalarPerturbation s (d p) :=
    schemeAction_map_infinitesimal G fs _ _ (hd p)
  have hy : (A y).val = scalarPerturbation t (d q) :=
    schemeAction_map_infinitesimal G ft _ _ (hd q)
  have hw : (A w).val = scalarPerturbation st (d z) :=
    schemeAction_map_infinitesimal G fst _ _ (hd z)
  have hcomm : w = x * y * x⁻¹ * y⁻¹ := lieBracket_isBracket G.group p q
  have hval : (A w).val = (A x).val * (A y).val * (A x).inv * (A y).inv := by
    rw [hcomm]
    simp only [map_mul, map_inv, Units.val_mul]
    rfl
  let coeff : B →ₗ[k] k :=
    { toFun := fun a => a.snd.snd
      map_add' := fun _ _ => rfl
      map_smul' := fun c a => by
        change (c • a).snd.snd = c * a.snd.snd
        rw [TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_smul, smul_eq_mul] }
  have hc : coeff st = 1 := rfl
  change d z = _
  apply scalarPerturbation_injective (V := V) st coeff hc
  rw [← hw, hval, hx, hy, scalarPerturbation_inverse _ s hs _ hx,
    scalarPerturbation_inverse _ t ht _ hy, hst]
  exact scalarPerturbation_commutator s t hs ht (d p) (d q)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem tangentDerivationsOfPreservation
    (ptest : Module.End (DualNumber k) (DualNumber k ⊗[k] V) → Prop)
    (Q : Module.End k V → Prop)
    (hp : ∀ g : (Module.End (DualNumber k) (DualNumber k ⊗[k] V))ˣ,
      g ∈ P dualAlgebra ↔ ptest g.val)
    (hQ : ∀ D, ptest (infinitesimal D) ↔ Q D) :
    TangentDerivations G Q := by
  have := G.groupAffine
  let A := schemeAction G dualAlgebra
  choose d hd using fun p : _root_.LinearAlgebraicGroups.Specs.Lie k G.group =>
    exists_infinitesimal (A p.toMul.val).val ((schemeAction_reduces G _).mp p.toMul.property)
  refine ⟨d, ?_, ?_, hd, ?_, ?_, schemeAction_bracket G d hd⟩
  · intro p q h
    apply Subtype.ext
    apply schemeAction_injective G dualAlgebra
    apply Units.ext
    exact (hd p).trans ((congrArg infinitesimal h).trans (hd q).symm)
  · intro D
    constructor
    · rintro ⟨p, rfl⟩
      rw [← hQ, ← hd]
      exact (hp _).mp ((G.subgroupPoints dualAlgebra p.toMul.val).property)
    · intro h
      let g := infinitesimalUnit D
      let p := (G.subgroupPoints dualAlgebra).symm ⟨g, (hp _).mpr ((hQ _).mpr h)⟩
      have he : A p = g := congrArg Subtype.val ((G.subgroupPoints dualAlgebra).apply_symm_apply _)
      have hr := (schemeAction_reduces G p).mpr (by rw [he]; exact infinitesimal_reduction D)
      let q : _root_.LinearAlgebraicGroups.Specs.Lie k G.group := ⟨p, hr⟩
      refine ⟨q, infinitesimal_injective ((hd q).symm.trans ?_)⟩
      exact congrArg Units.val he
  · intro p q
    apply infinitesimal_injective
    calc
      infinitesimal (d (p + q)) = (A (p + q).toMul.val).val := (hd _).symm
      _ = (A p.toMul.val).val * (A q.toMul.val).val := congrArg Units.val (map_mul A _ _)
      _ = infinitesimal (d p + d q) := by rw [hd, hd, infinitesimal_add]
  · intro c p
    let w := scalePointKernel G.group c p
    apply infinitesimal_injective
    rw [← hd w]
    have h := schemeAction_map_infinitesimal G (CommAlgCat.ofHom (dualNumberScale c)) _ _ (hd p)
    change (A w.toMul.val).val = scalarPerturbation (dualNumberScale c ε) (d p) at h
    rw [h]
    apply tensorOne_ext
    intro x
    have htmul (a : DualNumber k) (m : V) : a • ((1 : DualNumber k) ⊗ₜ[k] m) = a ⊗ₜ[k] m := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    change (1 ⊗ₜ[k] x) + dualNumberScale c ε • (d p).baseChange (DualNumber k) (1 ⊗ₜ[k] x) =
      (1 ⊗ₜ[k] x) + (ε : DualNumber k) • (c • d p).baseChange (DualNumber k) (1 ⊗ₜ[k] x)
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, htmul, htmul, scaled_epsilon, smul_tmul]
    rfl

theorem bilinearLieIdentification : BilinearLieIdentification.{u,v} := by
  intro k _ V _ _ A G
  exact tangentDerivationsOfPreservation G (PreservesBilinear A (DualNumber k))
    (IsDerivation A.product) (mem_bilinearStabilizer A _) (infinitesimal_bilinear_iff A)

theorem quadraticLieIdentification : QuadraticLieIdentification.{u,v} := by
  intro k _ V _ _ J G
  exact tangentDerivationsOfPreservation G (PreservesQuadratic J (DualNumber k))
    (IsQuadraticDerivation J) (mem_quadraticStabilizer J _) (infinitesimal_quadratic_iff J)

end SchemeTangent

end
end LinearAlgebraicGroups.Albert.Automorphisms
