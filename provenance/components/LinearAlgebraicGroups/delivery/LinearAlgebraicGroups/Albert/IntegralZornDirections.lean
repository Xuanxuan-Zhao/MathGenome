import Specs.LinearAlgebraicGroups.Albert.IntegralZornDirections
import LinearAlgebraicGroups.Composition.PeirceFrames
import LinearAlgebraicGroups.Albert.Triality
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.FreeModule.PID

namespace LinearAlgebraicGroups.Albert.IntegralZornDirections

open _root_.LinearAlgebraicGroups.Composition
open Composition.PeirceSpecification Composition.ZornSpecification
open IntegralZornDirectionsSpecification TrialitySpecification
open scoped TensorProduct Matrix

universe u

theorem integral_lifting : IntegralLifting := by
  intro e
  have hn := Zorn.isOctonion ℤ
  obtain ⟨d, ⟨c⟩⟩ := (corner e 1 0).nonempty_basis_of_pid (Zorn.coordinateBasis ℤ)
  let : Module.Finite ℤ (corner e 1 0) := (Peirce.projective_corners hn e).1
  let : Module.Free ℤ (corner e 1 0) := Module.Free.of_basis c
  let p : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩
  have hr := (Peirce.corner_rank hn e p).1
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis c, Fintype.card_fin] at hr
  obtain ⟨b⟩ := Peirce.oriented_basis_exists hn e ⟨c.reindex (finCongr hr)⟩
  obtain ⟨E, hE⟩ := Peirce.zorn_frame_equivalence hn
  exact ⟨E.symm ⟨e, b⟩, ((hE _).1.symm).trans
    (congrArg (fun p : Σ e : QuadricPoint (norm ℤ), OrientedBasis e => p.1.val)
      (E.apply_symm_apply ⟨e, b⟩))⟩

/-- An integral octonion automorphism carrying the first idempotent to the given point. -/
noncomputable def integralLift (e : QuadricPoint (norm ℤ)) : Automorphism ℤ :=
  (integral_lifting e).choose

theorem integralLift_first (e : QuadricPoint (norm ℤ)) :
    (integralLift e).toLinearEquiv (first ℤ) = e.val :=
  (integral_lifting e).choose_spec

section Directions

variable (R : Type u) [CommRing R]

private def directionCoordinates : (DirectionIndex → R) ≃ₗ[R] Specification.ZornCoordinates R where
  toFun x :=
    (x (.inl none) + (∑ i : Fin 3, x (.inl (some i))) + (∑ i : Fin 3, x (.inr (some i))),
      fun i => x (.inl (some i)), fun i => x (.inr (some i)), x (.inr none))
  invFun x
    | .inl none => x.1 - (∑ i : Fin 3, x.2.1 i) - (∑ i : Fin 3, x.2.2.1 i)
    | .inl (some i) => x.2.1 i
    | .inr none => x.2.2.2
    | .inr (some i) => x.2.2.1 i
  left_inv x := by
    funext i
    rcases i with (i | i) <;> cases i <;> dsimp
    abel
  right_inv x := by
    rcases x with ⟨a, u, v, b⟩
    simp [Prod.mk.injEq]
    abel
  map_add' x y := by
    simp only [Pi.add_apply, Prod.mk_add_mk, Prod.mk.injEq, Finset.sum_add_distrib]
    exact ⟨by abel, rfl, rfl, trivial⟩
  map_smul' a x := by
    simp only [Pi.smul_apply, Prod.smul_mk, Prod.mk.injEq, smul_add, Finset.smul_sum,
      RingHom.id_apply]
    constructor <;> simp [Pi.smul_def, smul_eq_mul]

/-- The eight direction vectors as a basis of the Zorn module. -/
noncomputable def directionBasis : Module.Basis DirectionIndex R (Zorn R) :=
  (Pi.basisFun R _).map ((directionCoordinates R).trans (Zorn.coordinates R).symm)

theorem directionBasis_apply (i : DirectionIndex) : directionBasis R i = direction R i := by
  rw [directionBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  apply (Zorn.coordinates R).injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  apply (directionCoordinates R).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext j
  rcases i with (i | i) <;> cases i <;> rcases j with (j | j) <;> cases j <;>
    simp [directionCoordinates, direction, first, second, Pi.single_apply]

end Directions

private theorem map_direction {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : DirectionIndex) : mapCoordinates f (direction R i) = direction S i := by
  have h (i : Fin 3) : f ∘ Pi.single i (1 : R) = Pi.single i (1 : S) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  apply (Zorn.coordinates S).injective
  rcases i with (i | i) <;> cases i <;>
    simp [mapCoordinates, direction, first, second, h, Function.comp_def, Pi.zero_def]

set_option backward.isDefEq.respectTransparency false in
theorem direction_basis : DirectionBasis.{u} := by
  refine ⟨directionBasis ℤ, directionBasis_apply ℤ, fun R _ i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, Zorn.baseChange_tmul, one_smul,
    directionBasis_apply, map_direction]

private theorem direction_mem_quadric (i : DirectionIndex) :
    AdjointSpecification.trace (norm ℤ) (direction ℤ i) = 1 ∧ norm ℤ (direction ℤ i) = 0 := by
  rcases i with (i | i) <;> cases i <;>
    simp [direction, first, second, Zorn.trace_formula, Zorn.norm_formula, Specification.zornNorm,
      LinearEquiv.apply_symm_apply]

/-- An integral automorphism giving the specified direction. -/
noncomputable def directionLift (i : DirectionIndex) : Automorphism ℤ :=
  integralLift ⟨direction ℤ i, direction_mem_quadric i⟩

theorem directionLift_first (i : DirectionIndex) :
    (directionLift i).toLinearEquiv (first ℤ) = direction ℤ i :=
  integralLift_first ⟨direction ℤ i, direction_mem_quadric i⟩

section Extension

variable {A : Type*} [CommRing A] (R : Type u) [CommRing R] [Algebra A R]

private noncomputable def extendZornAutomorphism (F : Automorphism A) : Automorphism R := by
  let e := ZornSpecification.baseChange A R
  let L := F.toLinearEquiv.baseChange A R (Zorn A) (Zorn A)
  have hLone : L 1 = 1 := by
    change (1 : R) ⊗ₜ[A] F.toLinearEquiv 1 = (1 : R) ⊗ₜ[A] (1 : Zorn A)
    rw [F.map_one]
  have hLmul (x y : R ⊗[A] Zorn A) : L (x * y) = L x * L y := by
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      induction y using TensorProduct.inductionOn with
      | tmul t b =>
        simp only [L, Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.baseChange_tmul, F.map_mul]
      | add x y hx hy => simp only [mul_add, map_add, hx, hy]
    | add x z hx hz => simp only [add_mul, map_add, hx, hz]
  have hLnorm : (normBaseChange R (norm A)).comp L.toLinearMap = normBaseChange R (norm A) := by
    apply baseChange_ext
    intro x
    change normBaseChange R (norm A) ((1 : R) ⊗ₜ[A] F.toLinearEquiv x) =
      normBaseChange R (norm A) ((1 : R) ⊗ₜ[A] x)
    rw [normBaseChange_tmul, normBaseChange_tmul, F.map_norm]
  refine ⟨(e.symm.trans L).trans e, ?_, ?_, ?_⟩
  · change e (L (e.symm 1)) = 1
    have he : e 1 = 1 := Zorn.baseChange_one
    rw [← he, e.symm_apply_apply, hLone]
  · intro a b
    change e (L (e.symm (a * b))) = e (L (e.symm a)) * e (L (e.symm b))
    have he (x y : R ⊗[A] Zorn A) : e (x * y) = e x * e y := Zorn.baseChange_mul x y
    have hab : e.symm (a * b) = e.symm a * e.symm b := by
      apply e.injective
      simp only [e.apply_symm_apply, he]
    rw [hab, hLmul]
    exact he _ _
  · intro a
    obtain ⟨x, rfl⟩ := e.surjective a
    change norm R (e (L (e.symm (e x)))) = norm R (e x)
    have he (y : R ⊗[A] Zorn A) : normBaseChange R (norm A) y = norm R (e y) :=
      congrArg (fun q : QuadraticForm R (R ⊗[A] Zorn A) => q y) Zorn.baseChange_norm
    rw [e.symm_apply_apply, ← he, ← he]
    exact congrArg (fun q : QuadraticForm R (R ⊗[A] Zorn A) => q x) hLnorm

private theorem extendZornAutomorphism_apply (F : Automorphism A) (x : R ⊗[A] Zorn A) :
    (extendZornAutomorphism R F).toLinearEquiv (ZornSpecification.baseChange A R x) =
      ZornSpecification.baseChange A R (F.toLinearEquiv.baseChange A R (Zorn A) (Zorn A) x) := by
  change ZornSpecification.baseChange A R
    (F.toLinearEquiv.baseChange A R (Zorn A) (Zorn A)
      ((ZornSpecification.baseChange A R).symm (ZornSpecification.baseChange A R x))) = _
  rw [LinearEquiv.symm_apply_apply]

end Extension

/-- Tensor an integral automorphism with the test ring and transport it to Zorn coordinates. -/
noncomputable def extendAutomorphism (R : Type u) [CommRing R] (F : Automorphism ℤ) :
    Automorphism R :=
  extendZornAutomorphism R F

theorem extendAutomorphism_apply (R : Type u) [CommRing R] (F : Automorphism ℤ) :
    IsExtension F (extendAutomorphism R F) :=
  extendZornAutomorphism_apply R F

set_option backward.isDefEq.respectTransparency false in
theorem extendAutomorphism_direction (R : Type u) [CommRing R] (i : DirectionIndex) :
    (extendAutomorphism R (directionLift i)).toLinearEquiv (first R) = direction R i := by
  let e := ZornSpecification.baseChange ℤ R
  let F := directionLift i
  let x : R ⊗[ℤ] Zorn ℤ := (1 : R) ⊗ₜ[ℤ] first ℤ
  have h : e x = first R := Zorn.baseChange_first
  calc
    (extendAutomorphism R F).toLinearEquiv (first R) =
        (extendAutomorphism R F).toLinearEquiv (e x) :=
      congrArg (extendAutomorphism R F).toLinearEquiv h.symm
    _ = e (F.toLinearEquiv.baseChange ℤ R (Zorn ℤ) (Zorn ℤ) x) :=
      extendAutomorphism_apply R F x
    _ = e ((1 : R) ⊗ₜ[ℤ] direction ℤ i) :=
      congrArg (fun y : Zorn ℤ => e ((1 : R) ⊗ₜ[ℤ] y)) (directionLift_first i)
    _ = direction R i := by
      change ZornSpecification.baseChange ℤ R ((1 : R) ⊗ₜ[ℤ] direction ℤ i) = _
      rw [Zorn.baseChange_tmul, one_smul, map_direction]

open private map_octonion_add map_octonion_smul map_octonion_zero from
  LinearAlgebraicGroups.Albert.Triality

private theorem map_baseChange_tmul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (x : Zorn ℤ) :
    mapCoordinates f (ZornSpecification.baseChange ℤ R (r ⊗ₜ[ℤ] x)) =
      ZornSpecification.baseChange ℤ S (f r ⊗ₜ[ℤ] x) := by
  rw [Zorn.baseChange_tmul, Zorn.baseChange_tmul, map_octonion_smul]
  congr 1
  obtain ⟨⟨a, v, w, b⟩, rfl⟩ := (Zorn.coordinates ℤ).symm.surjective x
  apply (Zorn.coordinates S).injective
  change (f (algebraMap ℤ R a), (fun i : Fin 3 => f (algebraMap ℤ R (v i))),
    (fun i : Fin 3 => f (algebraMap ℤ R (w i))), f (algebraMap ℤ R b)) =
    (algebraMap ℤ S a, (fun i : Fin 3 => algebraMap ℤ S (v i)),
      (fun i : Fin 3 => algebraMap ℤ S (w i)), algebraMap ℤ S b)
  simp

set_option maxRecDepth 1024 in
theorem extendAutomorphism_natural {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (F : Automorphism ℤ) (x : Zorn R) :
    mapCoordinates f ((extendAutomorphism R F).toLinearEquiv x) =
      (extendAutomorphism S F).toLinearEquiv (mapCoordinates f x) := by
  obtain ⟨z, rfl⟩ := (ZornSpecification.baseChange ℤ R).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul r y =>
    calc
      _ = mapCoordinates f (ZornSpecification.baseChange ℤ R (r ⊗ₜ[ℤ] F.toLinearEquiv y)) :=
        congrArg (mapCoordinates f) (extendAutomorphism_apply R F (r ⊗ₜ[ℤ] y))
      _ = ZornSpecification.baseChange ℤ S (f r ⊗ₜ[ℤ] F.toLinearEquiv y) :=
        map_baseChange_tmul f r (F.toLinearEquiv y)
      _ = (extendAutomorphism S F).toLinearEquiv (ZornSpecification.baseChange ℤ S (f r ⊗ₜ[ℤ] y)) :=
        (extendAutomorphism_apply S F (f r ⊗ₜ[ℤ] y)).symm
      _ = _ := congrArg (extendAutomorphism S F).toLinearEquiv (map_baseChange_tmul f r y).symm
  | add x y hx hy => simp only [map_add, map_octonion_add, hx, hy]

section Albert

variable {R : Type u} [CommRing R]

private theorem commutes_conjugation (F : Automorphism R) (x : Zorn R) :
    F.toLinearEquiv (Composition.conjugate (norm R) x) =
      Composition.conjugate (norm R) (F.toLinearEquiv x) := by
  have hp (y z : Zorn R) :
      (norm R).polarBilin (F.toLinearEquiv y) (F.toLinearEquiv z) = (norm R).polarBilin y z := by
    simp only [full_polar_formula, ← map_add, F.map_norm]
  have ht : compositionTrace (norm R) (F.toLinearEquiv x) = compositionTrace (norm R) x := by
    rw [compositionTrace_apply, compositionTrace_apply, ← hp x 1, F.map_one]
  simp only [conjugate_apply, map_sub, map_smul, F.map_one, ht]

private def diagonalTriple (F : Automorphism R) : relatedTriples (R := R) :=
  ⟨fun _ => F.toLinearEquiv, ⟨fun _ => F.map_norm, fun _ x y => (commutes_conjugation F (x * y)).trans
      (congrArg (Composition.conjugate (norm R)) (F.map_mul x y))⟩⟩

/-- The extended automorphism acting on each octonion block of the split Albert model. -/
noncomputable def albertAction (R : Type u) [CommRing R] (F : Automorphism ℤ) :
    frameStabilizer (R := R) :=
  (Triality.frameTriality R).choose (diagonalTriple (extendAutomorphism R F))

theorem albertAction_apply (F : Automorphism ℤ) (x : Model R) :
    (albertAction R F).val x = (x.1, fun i => (extendAutomorphism R F).toLinearEquiv (x.2 i)) :=
  (Triality.frameTriality R).choose_spec (diagonalTriple (extendAutomorphism R F)) x

theorem albertAction_natural {S : Type u} [CommRing S]
    (f : R →+* S) (F : Automorphism ℤ) (x : Model R) :
    mapModel f ((albertAction R F).val x) = (albertAction S F).val (mapModel f x) := by
  rw [albertAction_apply, albertAction_apply]
  exact Prod.ext rfl (funext fun i => extendAutomorphism_natural f F (x.2 i))

end Albert

theorem direction_actions : DirectionActions.{u} :=
  ⟨directionLift, extendAutomorphism, albertAction, directionLift_first,
    fun R _ => extendAutomorphism_direction R, fun R _ => extendAutomorphism_apply R,
    fun _ _ => albertAction_apply, fun f F =>
      ⟨extendAutomorphism_natural f F, albertAction_natural f F⟩⟩

end LinearAlgebraicGroups.Albert.IntegralZornDirections
