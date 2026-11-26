import Specs.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Batteries.Tactic.OpenPrivate

open CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.UnitaryNormEquations

noncomputable section

open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.StandardGroups
open Algebra.TensorProduct MulOpposite
open _root_.RM03.CSA (IsCentralSimple degree)
open _root_.RM03.CSA.NormOneGroup

set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {F E A R S : Type u} [Field F] [Field E] [Algebra F E]
  [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
  [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  {ι : Type u} [Fintype ι]

local instance (priority := 2000) : Algebra E (Centre F E R) := Algebra.TensorProduct.rightAlgebra

/-- Change the coefficients of the quadratic centre, retaining its (E)-algebra structure. -/
def centreMap (f : R →ₐ[F] S) : Centre F E R →ₐ[E] Centre F E S :=
  { toRingHom := (map f (AlgHom.id F E)).toRingHom
    commutes' := by
      intro e
      change map f (AlgHom.id F E) (1 ⊗ₜ[F] e) = (1 ⊗ₜ[F] e)
      simp }

theorem associateCentre_natural (f : R →ₐ[F] S) (x : R ⊗[F] A) :
    associateCentre (E := E) (changeCoefficients f x) =
      changeCoefficients (centreMap (E := E) f) (associateCentre x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem unitaryNorm_natural (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (f : R →ₐ[F] S) (x : R ⊗[F] A) :
    unitaryNorm hA b (changeCoefficients f x) = centreMap f (unitaryNorm hA b x) := by
  change normAt hA b (associateCentre (changeCoefficients f x)) = _
  rw [associateCentre_natural, normAt_natural]
  rfl

theorem adjointAt_mul (s : SecondKind F E A) (x y : R ⊗[F] A) :
    adjointAt s (x * y) = adjointAt s y * adjointAt s x := by
  simp [adjointAt]

@[simp] theorem adjointAt_one (s : SecondKind F E A) :
    adjointAt s (1 : R ⊗[F] A) = 1 := by
  simp [adjointAt]

theorem adjointAt_adj (s : SecondKind F E A) (x : R ⊗[F] A) :
    adjointAt s (adjointAt s x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp only [adjointAt_tmul, s.adjoint_adjoint]
  | add x y hx hy =>
    have ha (z w : R ⊗[F] A) : adjointAt s (z + w) = adjointAt s z + adjointAt s w := by
      simp [adjointAt]
    rw [ha, ha, hx, hy]

theorem adjointAt_natural (s : SecondKind F E A) (f : R →ₐ[F] S) (x : R ⊗[F] A) :
    adjointAt s (changeCoefficients f x) = changeCoefficients f (adjointAt s x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy =>
    simpa only [adjointAt, map_add, MulOpposite.unop_add, map_add] using congrArg₂ (· + ·) hx hy

private def unitaryNormHom (hA : IsCentralSimple E A) (b : Module.Basis ι E A) :
    (R ⊗[F] A) →* Centre F E R :=
  (normHom hA b).comp associateCentre.toMonoidHom

/-- The extended adjoint on units, with values in the opposite group. -/
def adjointUnit (s : SecondKind F E A) : (R ⊗[F] A)ˣ →* ((R ⊗[F] A)ˣ)ᵐᵒᵖ :=
  Units.opEquiv.toMonoidHom.comp (Units.map (adjointEquiv s).toMonoidHom)

@[simp] theorem adjointUnit_val (s : SecondKind F E A) (x : (R ⊗[F] A)ˣ) :
    (unop (adjointUnit s x)).val = adjointAt s x.val := rfl

private theorem adjoint_eq_inverse_iff (s : SecondKind F E A) (x : (R ⊗[F] A)ˣ) :
    adjointAt s x.val * x.val = 1 ↔ unop (adjointUnit s x) = x⁻¹ := by
  have he : (unop (adjointUnit s x) * x).val = 1 ↔ unop (adjointUnit s x) * x = 1 :=
    ⟨fun h => Units.ext (by exact h), fun h => congrArg Units.val h⟩
  exact he.trans (mul_eq_one_iff_eq_inv)

def specialUnitarySubgroup (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (s : SecondKind F E A) : Subgroup (R ⊗[F] A)ˣ where
  carrier := {x | IsSpecialUnitary hA b s x}
  one_mem' := ⟨by simp, (unitaryNormHom hA b).map_one⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hx, nx⟩ := hx
    obtain ⟨hy, ny⟩ := hy
    refine ⟨?_, ?_⟩
    · change adjointAt s (x.val * y.val) * (x.val * y.val) = 1
      rw [adjointAt_mul, mul_assoc, ← mul_assoc (adjointAt s x.val), hx, one_mul, hy]
    · change unitaryNormHom hA b (x.val * y.val) = 1
      rw [map_mul, show unitaryNormHom hA b x.val = 1 from nx,
        show unitaryNormHom hA b y.val = 1 from ny, mul_one]
  inv_mem' := by
    intro x hx
    obtain ⟨hx, nx⟩ := hx
    refine ⟨(adjoint_eq_inverse_iff s x⁻¹).2 ?_, ?_⟩
    · rw [map_inv, MulOpposite.unop_inv, (adjoint_eq_inverse_iff s x).1 hx]
    · have hh := (unitaryNormHom hA b).map_mul x.val x⁻¹.val
      change unitaryNormHom hA b (x.val * x⁻¹.val) =
        unitaryNormHom hA b x.val * unitaryNormHom hA b x⁻¹.val at hh
      rw [Units.mul_inv, map_one, show unitaryNormHom hA b x.val = 1 from nx, one_mul] at hh
      exact hh.symm

/-- Coefficient maps on the units satisfying the special unitary equations. -/
def mapSpecialUnitary (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (s : SecondKind F E A) (f : R →ₐ[F] S) :
    specialUnitarySubgroup hA b s (R := R) →* specialUnitarySubgroup hA b s (R := S) :=
  ((Units.map (changeCoefficients (A := A) f).toMonoidHom).comp
    (specialUnitarySubgroup hA b s).subtype).codRestrict _ (by
      intro x
      obtain ⟨hx, nx⟩ := x.prop
      refine ⟨?_, ?_⟩
      · change adjointAt s (changeCoefficients f x.val.val) *
          changeCoefficients f x.val.val = 1
        rw [adjointAt_natural, ← map_mul, hx, map_one]
      · change unitaryNorm hA b (changeCoefficients f x.val.val) = 1
        rw [unitaryNorm_natural, nx, map_one])

private theorem changeCoefficients_identity (x : R ⊗[F] A) :
    changeCoefficients (AlgHom.id F R) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem changeCoefficients_composition {T : Type u} [CommRing T] [Algebra F T]
    (f : R →ₐ[F] S) (g : S →ₐ[F] T) (x : R ⊗[F] A) :
    changeCoefficients (g.comp f) x = changeCoefficients g (changeCoefficients f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The functor on commutative ground-field algebras defined by the two equations. -/
def specialUnitaryPoints (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (s : SecondKind F E A) : TestAlgebra F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (specialUnitarySubgroup hA b s (R := R))
  map f := GrpCat.ofHom (mapSpecialUnitary hA b s f.hom)
  map_id R := by
    apply GrpCat.ext
    intro x
    exact Subtype.ext (Units.ext (changeCoefficients_identity x.val.val))
  map_comp f g := by
    apply GrpCat.ext
    intro x
    exact Subtype.ext (Units.ext (changeCoefficients_composition f.hom g.hom x.val.val))

open private Representation Representation.mk Representation.operations Representation.represents
  from LinearAlgebraicGroups.Affine.StandardGroups

open private coord_change from
  MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup

section Coordinates

variable {κ ν : Type u} [Fintype κ] [Fintype ν]
  (a : Module.Basis κ F A) (e : Module.Basis ν F E)
  (hA : IsCentralSimple E A) (b : Module.Basis ι E A) (s : SecondKind F E A)

local notation "Pol" => MvPolynomial (κ ⊕ κ) F

private def basisElement (c : κ → R) : R ⊗[F] A :=
  (a.baseChange R).equivFun.symm c

@[simp] private theorem basisElement_repr (c : κ → R) (i : κ) :
    (a.baseChange R).repr (basisElement a c) i = c i :=
  congrFun ((a.baseChange R).equivFun.apply_symm_apply c) i

private theorem basisElement_natural (f : R →ₐ[F] S) (c : κ → R) :
    changeCoefficients f (basisElement a c) = basisElement a (f ∘ c) := by
  apply (a.baseChange S).equivFun.injective
  funext i
  change (a.baseChange S).repr (changeCoefficients f (basisElement a c)) i =
    (a.baseChange S).repr (basisElement a (f ∘ c)) i
  rw [coord_change, basisElement_repr, basisElement_repr]
  rfl

private def equations (x y : R ⊗[F] A) : ((κ ⊕ κ ⊕ κ) ⊕ ν) → R
  | .inl (.inl i) => (a.baseChange R).repr (x * y - 1) i
  | .inl (.inr (.inl i)) => (a.baseChange R).repr (y * x - 1) i
  | .inl (.inr (.inr i)) => (a.baseChange R).repr (adjointAt s x * x - 1) i
  | .inr j => (e.baseChange R).repr (unitaryNorm hA b x - 1) j

private theorem equations_natural (f : R →ₐ[F] S) (x y : R ⊗[F] A)
    (i : (κ ⊕ κ ⊕ κ) ⊕ ν) :
    equations a e hA b s (changeCoefficients f x) (changeCoefficients f y) i =
      f (equations a e hA b s x y i) := by
  rcases i with (i | i | i) | j
  · change (a.baseChange S).repr (changeCoefficients f x * changeCoefficients f y - 1) i = _
    rw [← map_mul, ← map_one (changeCoefficients f), ← map_sub, coord_change]
    rfl
  · change (a.baseChange S).repr (changeCoefficients f y * changeCoefficients f x - 1) i = _
    rw [← map_mul, ← map_one (changeCoefficients f), ← map_sub, coord_change]
    rfl
  · change (a.baseChange S).repr
      (adjointAt s (changeCoefficients f x) * changeCoefficients f x - 1) i = _
    rw [adjointAt_natural, ← map_mul, ← map_one (changeCoefficients f), ← map_sub, coord_change]
    rfl
  · change (e.baseChange S).repr (unitaryNorm hA b (changeCoefficients f x) - 1) j = _
    rw [unitaryNorm_natural, ← map_one (centreMap f), ← map_sub]
    exact coord_change e f (unitaryNorm hA b x - 1) j

private theorem eq_zero_of_coords {M : Type u} [AddCommGroup M] [Module R M]
    {η : Type u} (d : Module.Basis η R M) (z : M) (h : ∀ i, d.repr z i = 0) : z = 0 :=
  d.repr.injective (Finsupp.ext (by simpa using h))

private theorem equations_iff (x y : R ⊗[F] A) :
    (∀ i, equations a e hA b s x y i = 0) ↔
      x * y = 1 ∧ y * x = 1 ∧ adjointAt s x * x = 1 ∧ unitaryNorm hA b x = 1 := by
  constructor
  · intro h
    exact ⟨sub_eq_zero.mp (eq_zero_of_coords (a.baseChange R) _ (fun i => h (.inl (.inl i)))),
      sub_eq_zero.mp (eq_zero_of_coords (a.baseChange R) _ (fun i => h (.inl (.inr (.inl i))))),
      sub_eq_zero.mp (eq_zero_of_coords (a.baseChange R) _ (fun i => h (.inl (.inr (.inr i))))),
      sub_eq_zero.mp (eq_zero_of_coords (e.baseChange R) _ (fun j => h (.inr j)))⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩ i
    rcases i with (i | i | i) | j <;> simp [equations, h₁, h₂, h₃, h₄]

private def genericX : Pol ⊗[F] A :=
  basisElement a (fun i => MvPolynomial.X (.inl i))

private def genericY : Pol ⊗[F] A :=
  basisElement a (fun i => MvPolynomial.X (.inr i))

private def equationIdeal : Ideal Pol :=
  Ideal.span (Set.range (equations a e hA b s (genericX a) (genericY a)))

local notation "I" => equationIdeal a e hA b s
local notation "Q" => Pol ⧸ I
local notation "q" => Ideal.Quotient.mkₐ F I

private theorem map_generic_equations (f : Pol →ₐ[F] R) (i : (κ ⊕ κ ⊕ κ) ⊕ ν) :
    f (equations a e hA b s (genericX a) (genericY a) i) =
      equations a e hA b s (basisElement a (fun j => f (MvPolynomial.X (.inl j))))
        (basisElement a (fun j => f (MvPolynomial.X (.inr j)))) i := by
  rw [← equations_natural, genericX, genericY, basisElement_natural, basisElement_natural]
  rfl

private def evaluate (R : TestAlgebra F) (f : Q →ₐ[F] R) :
    (specialUnitaryPoints hA b s).obj R := by
  let g := f.comp q
  let x := basisElement a (fun i => g (MvPolynomial.X (.inl i)))
  let y := basisElement a (fun i => g (MvPolynomial.X (.inr i)))
  have hq (i) : q (equations a e hA b s (genericX a) (genericY a) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have h (i) : equations a e hA b s x y i = 0 := by
    rw [← map_generic_equations a e hA b s g]
    change f (q _) = 0
    rw [hq, map_zero]
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (equations_iff a e hA b s x y).mp h
  exact ⟨⟨x, y, h₁, h₂⟩, h₃, h₄⟩

private theorem evaluate_coord (R : TestAlgebra F) (f : Q →ₐ[F] R) (i : κ) :
    (a.baseChange R).repr (evaluate a e hA b s R f).val.val i =
      f (q (MvPolynomial.X (.inl i))) := basisElement_repr a _ _

private theorem evaluate_inv_coord (R : TestAlgebra F) (f : Q →ₐ[F] R) (i : κ) :
    (a.baseChange R).repr ((evaluate a e hA b s R f).val⁻¹).val i =
      f (q (MvPolynomial.X (.inr i))) := basisElement_repr a _ _

private def evaluationHom (R : TestAlgebra F) (x : (specialUnitaryPoints hA b s).obj R) :
    Q →ₐ[F] R := by
  let c : κ ⊕ κ → R := Sum.elim ((a.baseChange R).repr x.val.val)
    ((a.baseChange R).repr (x.val⁻¹).val)
  let g : Pol →ₐ[F] R := MvPolynomial.aeval c
  refine Ideal.Quotient.liftₐ I g ?_
  have he :
      (basisElement a (fun i => g (MvPolynomial.X (.inl i)))) = x.val.val := by
    apply (a.baseChange R).equivFun.injective
    funext i
    change (a.baseChange R).repr (basisElement a _) i = _
    simp [g, c]
  have hi :
      (basisElement a (fun i => g (MvPolynomial.X (.inr i)))) = (x.val⁻¹).val := by
    apply (a.baseChange R).equivFun.injective
    funext i
    change (a.baseChange R).repr (basisElement a _) i = _
    simp [g, c]
  have hh := (equations_iff a e hA b s x.val.val (x.val⁻¹).val).2
    ⟨x.val.val_inv, x.val.inv_val, x.prop.1, x.prop.2⟩
  have hle : I ≤ RingHom.ker g.toRingHom := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    change g _ = 0
    rw [map_generic_equations, he, hi]
    exact hh i)
  exact fun _ hp => hle hp

private theorem evaluationHom_coord (R : TestAlgebra F)
    (x : (specialUnitaryPoints hA b s).obj R) (i : κ) :
    evaluationHom a e hA b s R x (q (MvPolynomial.X (.inl i))) =
      (a.baseChange R).repr x.val.val i := MvPolynomial.aeval_X _ _

private theorem evaluationHom_inv_coord (R : TestAlgebra F)
    (x : (specialUnitaryPoints hA b s).obj R) (i : κ) :
    evaluationHom a e hA b s R x (q (MvPolynomial.X (.inr i))) =
      (a.baseChange R).repr (x.val⁻¹).val i := MvPolynomial.aeval_X _ _

private def unitaryRepresentation : Representation Q (specialUnitaryPoints hA b s) :=
  Representation.mk (fun R =>
    { toFun := evaluate a e hA b s R
      invFun := evaluationHom a e hA b s R
      left_inv f := by
        apply Ideal.Quotient.algHom_ext F
        ext i
        cases i with
        | inl i =>
          exact (evaluationHom_coord a e hA b s R _ i).trans (evaluate_coord a e hA b s R f i)
        | inr i =>
          exact (evaluationHom_inv_coord a e hA b s R _ i).trans (evaluate_inv_coord a e hA b s R f i)
      right_inv x := by
        apply Subtype.ext
        apply Units.ext
        apply (a.baseChange R).equivFun.injective
        funext i
        exact (evaluate_coord a e hA b s R _ i).trans (evaluationHom_coord a e hA b s R x i) })
    (by
      intro R S f g
      apply Subtype.ext
      apply Units.ext
      apply (a.baseChange S).equivFun.injective
      funext i
      change (a.baseChange S).repr (evaluate a e hA b s S (f.hom.comp g)).val.val i =
        (a.baseChange S).repr (changeCoefficients f.hom (evaluate a e hA b s R g).val.val) i
      rw [coord_change, evaluate_coord, evaluate_coord, AlgHom.comp_apply])

theorem specialUnitaryRepresentability : SpecialUnitaryRepresentability.{u} := by
  intro F E A _ _ _ _ _ _ _ _ _ hA ι _ b s
  letI : Module.Finite E A := hA.2.2
  letI : Module.Finite F A := Module.Finite.trans E A
  let a := (Module.finBasis F A).reindex Equiv.ulift.symm
  let e := (Module.finBasis F E).reindex Equiv.ulift.symm
  let P := unitaryRepresentation a e hA b s
  letI := (Representation.operations P).hopf
  obtain ⟨_, _, c, _⟩ := Representation.represents P (fun _ _ _ => True) (fun _ _ => trivial)
  exact ⟨_, specialUnitaryPoints hA b s, c, fun _ => Equiv.refl _, fun _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

end Coordinates


section NormAdjoint

local instance conjugationInvPair (σ : E ≃ₐ[F] E) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ.toRingEquiv

private def adjointSemilinear (s : SecondKind F E A) :
    A ≃ₛₗ[s.conjugation.toRingHom] A where
  toFun a := unop (s.adjoint a)
  invFun a := unop (s.adjoint a)
  left_inv := s.adjoint_adjoint
  right_inv := s.adjoint_adjoint
  map_add' := by simp
  map_smul' e a := by
    rw [Algebra.smul_def, map_mul, MulOpposite.unop_mul, s.adjoint_centre,
      Algebra.smul_def, Algebra.commutes]
    rfl

private def semilinearRingEquiv {T : Type u} [CommRing T] [Algebra E T]
    (σ : E ≃ₐ[F] E) (τ : T ≃+* T)
    (hτ : ∀ c : E, τ (algebraMap E T c) = algebraMap E T (σ c)) :
    T ≃ₛₗ[σ.toRingHom] T where
  __ := τ.toAddEquiv
  map_smul' c t := by
    change τ (c • t) = σ c • τ t
    rw [Algebra.smul_def, map_mul, hτ, Algebra.smul_def]

private def extendAdjoint {T : Type u} [CommRing T] [Algebra E T]
    (s : SecondKind F E A) (τ : T ≃+* T)
    (hτ : ∀ c : E, τ (algebraMap E T c) = algebraMap E T (s.conjugation c)) :
    (T ⊗[E] A) ≃ₛₗ[s.conjugation.toRingHom] (T ⊗[E] A) :=
  TensorProduct.congr (semilinearRingEquiv s.conjugation τ hτ) (adjointSemilinear s)

private def adjointSplitting {K : Type u} [Field K] [Algebra E K] {d : ℕ}
    (s : SecondKind F E A) (τ : K ≃+* K)
    (hτ : ∀ c : E, τ (algebraMap E K c) = algebraMap E K (s.conjugation c))
    (e : (K ⊗[E] A) ≃ₐ[K] Matrix (Fin d) (Fin d) K) :
    (K ⊗[E] A) ≃ₐ[K] Matrix (Fin d) (Fin d) K := by
  let e' := ((extendAdjoint s τ hτ).symm.toAddEquiv.trans e.toAddEquiv).trans
    ((Matrix.transposeAddEquiv _ _ K).trans τ.mapMatrix.toAddEquiv)
  let l : (K ⊗[E] A) ≃ₗ[K] Matrix (Fin d) (Fin d) K :=
    { __ := e'
      map_smul' := by
        intro c x
        have h (z : K ⊗[E] A) :
            (extendAdjoint s τ hτ).symm (c • z) =
              τ.symm c • (extendAdjoint s τ hτ).symm z := by
          induction z using TensorProduct.inductionOn with
          | tmul r a =>
            change τ.symm (c * r) ⊗ₜ[E] unop (s.adjoint a) =
              τ.symm c • (τ.symm r ⊗ₜ[E] unop (s.adjoint a))
            rw [map_mul]
            rfl
          | add z w hz hw => simp only [smul_add, map_add, hz, hw]
        change (e ((extendAdjoint s τ hτ).symm (c • x))).transpose.map τ =
          c • (e ((extendAdjoint s τ hτ).symm x)).transpose.map τ
        rw [h, map_smul, Matrix.transpose_smul]
        ext i j
        simp [Matrix.smul_apply, smul_eq_mul] }
  have hl (c : K) (a : A) :
      l (c ⊗ₜ[E] a) = (e (τ.symm c ⊗ₜ[E] unop (s.adjoint a))).transpose.map τ := rfl
  apply Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct l
  · intro c d a b
    rw [hl, hl, hl, map_mul, map_mul,
      MulOpposite.unop_mul, mul_comm (τ.symm c) (τ.symm d),
      ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, Matrix.transpose_mul]
    exact (τ.toRingHom.mapMatrix).map_mul _ _
  · rw [hl]
    simp only [map_one, MulOpposite.unop_one, ← Algebra.TensorProduct.one_def,
      Matrix.transpose_one]
    exact (τ.toRingHom.mapMatrix (m := Fin d)).map_one

private theorem adjointSplitting_tmul {K : Type u} [Field K] [Algebra E K] {d : ℕ}
    (s : SecondKind F E A) (τ : K ≃+* K)
    (hτ : ∀ c : E, τ (algebraMap E K c) = algebraMap E K (s.conjugation c))
    (e : (K ⊗[E] A) ≃ₐ[K] Matrix (Fin d) (Fin d) K) (a : A) :
    adjointSplitting s τ hτ e (1 ⊗ₜ[E] unop (s.adjoint a)) =
      (e (1 ⊗ₜ[E] a)).transpose.map τ := by
  change (e (τ.symm 1 ⊗ₜ[E] unop (s.adjoint (unop (s.adjoint a))))).transpose.map τ = _
  rw [map_one, s.adjoint_adjoint]

set_option backward.isDefEq.respectTransparency true in
private theorem genericMatrix_map_transpose {K : Type u} [Field K] {d : ℕ}
    (τ : K ≃+* K) (M : ι → Matrix (Fin d) (Fin d) K) :
    _root_.Specs.RM03.CSA.genericMatrix (fun i => (M i).transpose.map τ) =
      ((MvPolynomial.map τ.toRingHom).mapMatrix (_root_.Specs.RM03.CSA.genericMatrix M)).transpose := by
  unfold _root_.Specs.RM03.CSA.genericMatrix
  rw [map_sum, Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Matrix.ext
  intro j k
  change MvPolynomial.X q * MvPolynomial.C (τ (M q k j)) =
    (MvPolynomial.map τ.toRingHom) (MvPolynomial.X q * MvPolynomial.C (M q k j))
  rw [map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  rfl

private theorem genericNorm_adjoint [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E] (hA : IsCentralSimple E A)
    (s : SecondKind F E A) (p : ι → A) :
    _root_.RM03.CSA.genericReducedNorm hA (fun i => unop (s.adjoint (p i))) =
      MvPolynomial.map s.conjugation.toRingHom (_root_.RM03.CSA.genericReducedNorm hA p) := by
  let K := AlgebraicClosure E
  let τ := s.conjugation.liftNormal K
  have hτ (c : E) : τ (algebraMap E K c) = algebraMap E K (s.conjugation c) :=
    s.conjugation.liftNormal_commutes K c
  obtain ⟨e⟩ := _root_.RM03.CSA.algEquiv_matrix_algebraicClosure hA
  apply MvPolynomial.map_injective (algebraMap E K) (algebraMap E K).injective
  rw [_root_.RM03.CSA.genericReducedNorm_map hA _ (adjointSplitting s τ.toRingEquiv hτ e)]
  rw [MvPolynomial.map_map, show (algebraMap E K).comp s.conjugation.toRingHom =
    τ.toRingHom.comp (algebraMap E K) from RingHom.ext (fun c => (hτ c).symm),
    ← MvPolynomial.map_map, _root_.RM03.CSA.genericReducedNorm_map hA p e]
  change _ = (MvPolynomial.map τ.toRingHom : MvPolynomial ι K →+* _)
    (_root_.Specs.RM03.CSA.genericMatrix fun i => e (1 ⊗ₜ[E] p i)).det
  rw [RingHom.map_det]
  simp only [adjointSplitting_tmul, genericMatrix_map_transpose, Matrix.det_transpose]
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem normAt_sum_tmul_split {K T : Type u} [Field K] [Algebra E K]
    [CommRing T] [Algebra E T] [Algebra K T] [IsScalarTower E K T]
    (hA : IsCentralSimple E A) (b : Module.Basis ι E A) (p : ι → A) (c : ι → T)
    (e : (K ⊗[E] A) ≃ₐ[K] Mat E A K) :
    normAt hA b (∑ i, c i ⊗ₜ[E] p i) =
      MvPolynomial.eval₂ (algebraMap E T) c (_root_.RM03.CSA.genericReducedNorm hA p) := by
  rw [normAt_eq_det hA b e, IsScalarTower.algebraMap_eq E K T, ← MvPolynomial.eval₂_map,
    _root_.RM03.CSA.genericReducedNorm_map hA p e]
  let f := MvPolynomial.eval₂Hom (algebraMap K T) c
  change _ = f (_root_.Specs.RM03.CSA.genericMatrix fun i => e (1 ⊗ₜ[E] p i)).det
  rw [RingHom.map_det]
  have h : extendSplitting e (∑ i, c i ⊗ₜ[E] p i) =
      f.mapMatrix (_root_.Specs.RM03.CSA.genericMatrix fun i => e (1 ⊗ₜ[E] p i)) := by
    rw [map_sum]
    unfold _root_.Specs.RM03.CSA.genericMatrix
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [extendSplitting_tmul]
    apply Matrix.ext
    intro i j
    change c q * algebraMap K T ((e (1 ⊗ₜ[E] p q)) i j) =
      f (MvPolynomial.X q * MvPolynomial.C ((e (1 ⊗ₜ[E] p q)) i j))
    rw [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
  exact congrArg Matrix.det h

private theorem normAt_sum_tmul {T : Type u} [CommRing T] [Algebra E T]
    (hA : IsCentralSimple E A) (b : Module.Basis ι E A) (p : ι → A) (c : ι → T) :
    normAt hA b (∑ i, c i ⊗ₜ[E] p i) =
      MvPolynomial.eval₂ (algebraMap E T) c (_root_.RM03.CSA.genericReducedNorm hA p) := by
  obtain ⟨e⟩ := _root_.RM03.CSA.algEquiv_matrix_algebraicClosure hA
  let K := AlgebraicClosure E
  let U := K ⊗[E] T
  let f : T →ₐ[E] U := includeRight
  apply includeRight_injective (B := T) (algebraMap E K).injective
  change f (normAt hA b _) = f.toRingHom (MvPolynomial.eval₂ _ _ _)
  rw [← normAt_natural hA b f, map_sum, MvPolynomial.hom_eval₂ _ _ f.toRingHom]
  have hf : f.toRingHom.comp (algebraMap E T) = algebraMap E U :=
    RingHom.ext f.commutes
  rw [hf]
  change normAt hA b (∑ i, f (c i) ⊗ₜ[E] p i) =
    MvPolynomial.eval₂ (algebraMap E U) (fun i => f (c i)) (_root_.RM03.CSA.genericReducedNorm hA p)
  exact normAt_sum_tmul_split hA b p (fun i => f (c i)) e

private def centreConjugation (σ : E ≃ₐ[F] E) : Centre F E R ≃ₐ[R] Centre F E R :=
  Algebra.TensorProduct.congr (.refl : R ≃ₐ[R] R) σ

private theorem centreConjugation_compatible (σ : E ≃ₐ[F] E) (c : E) :
    centreConjugation (R := R) σ (algebraMap E (Centre F E R) c) =
      algebraMap E (Centre F E R) (σ c) := rfl

private theorem associateCentre_adjoint (s : SecondKind F E A) (x : R ⊗[F] A) :
    associateCentre (E := E) (adjointAt s x) =
      extendAdjoint s (centreConjugation s.conjugation).toRingEquiv
        (centreConjugation_compatible s.conjugation) (associateCentre x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [associateCentre_tmul, adjointAt_tmul]
    change (r ⊗ₜ[F] (1 : E)) ⊗ₜ[E] unop (s.adjoint a) =
      (r ⊗ₜ[F] s.conjugation 1) ⊗ₜ[E] unop (s.adjoint a)
    rw [map_one]
  | add x y hx hy =>
    simp only [adjointAt, map_add, MulOpposite.unop_add] at hx hy ⊢
    exact congrArg₂ (· + ·) hx hy

/-- The reduced norm of the adjoint is the conjugate of the reduced norm. -/
theorem unitaryNorm_adjoint [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (hA : IsCentralSimple E A) (b : Module.Basis ι E A) (s : SecondKind F E A) (x : R ⊗[F] A) :
    unitaryNorm hA b (adjointAt s x) = centreConjugation s.conjugation (unitaryNorm hA b x) := by
  let W := Centre F E R
  let τ := centreConjugation (R := R) s.conjugation
  let e := extendAdjoint s τ.toRingEquiv (centreConjugation_compatible (R := R) s.conjugation)
  change normAt hA b (associateCentre (adjointAt s x)) = τ (normAt hA b (associateCentre x))
  rw [associateCentre_adjoint s x]
  letI : Module E W := (Algebra.TensorProduct.rightAlgebra (R := F) (A := R) (B := E)).toModule
  let y : W ⊗[E] A := associateCentre (E := E) x
  let c := fun i => (b.baseChange W).repr y i
  have hy : y = ∑ i, c i ⊗ₜ[E] b i := by
    conv_lhs => rw [← (b.baseChange W).sum_repr y]
    simp [c, Module.Basis.baseChange_apply, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  change normAt hA b (e y) = τ (normAt hA b y)
  rw [hy, map_sum]
  change normAt hA b (∑ i, τ (c i) ⊗ₜ[E] unop (s.adjoint (b i))) =
    τ (normAt hA b (∑ i, c i ⊗ₜ[E] b i))
  rw [normAt_sum_tmul, normAt_sum_tmul, genericNorm_adjoint hA s, MvPolynomial.eval₂_map]
  change _ = τ.toRingHom (MvPolynomial.eval₂ _ _ _)
  rw [MvPolynomial.hom_eval₂ _ _ τ.toRingHom]
  congr 1

end NormAdjoint


section SplitCentre

variable [Algebra E R] [IsScalarTower F E R]

@[simp] theorem centreAugmentation_tmul (r : R) (c : E) :
    centreAugmentation (r ⊗ₜ[F] c) = r * algebraMap E R c := rfl

@[simp] theorem factorProjection_tmul (r : R) (a : A) :
    factorProjection (r ⊗ₜ[F] a) = r ⊗ₜ[E] a := by
  change (r ⊗ₜ[E] (1 : A)) * ((1 : R) ⊗ₜ[E] a) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem factorProjection_associate (x : R ⊗[F] A) :
    factorProjection (E := E) x = changeCoefficients centreAugmentation (associateCentre x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [factorProjection_tmul, associateCentre_tmul, changeCoefficients,
      Algebra.TensorProduct.map_tmul, centreAugmentation_tmul, map_one, mul_one, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem factorProjection_norm (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (x : R ⊗[F] A) :
    normAt hA b (factorProjection x) =
      centreAugmentation (unitaryNorm hA b x) := by
  rw [factorProjection_associate, normAt_natural]
  rfl

private theorem centreProjections_bijective [Algebra.IsQuadraticExtension F E]
    (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1) :
    Function.Bijective
      (fun z : Centre F E R => (centreAugmentation z, centreAugmentation (centreConjugation σ z))) := by
  classical
  have hn : ∃ c : E, σ c ≠ c := by
    by_contra! h
    exact hσ (AlgEquiv.ext h)
  obtain ⟨t, ht⟩ := hn
  have hli : LinearIndependent F (![t, 1] : Fin 2 → E) := by
    rw [linearIndependent_fin2]
    refine ⟨one_ne_zero, ?_⟩
    intro a ha
    change a • (1 : E) = t at ha
    rw [Algebra.smul_def, mul_one] at ha
    exact ht (ha ▸ σ.commutes a)
  let d : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by
    simp [Algebra.IsQuadraticExtension.finrank_eq_two F E])
  have hd : (d : Fin 2 → E) = ![t, 1] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli _
  let c := (d.baseChange R).equivFun
  have hz (z : Centre F E R) : z = (c z 0 ⊗ₜ[F] t) + (c z 1 ⊗ₜ[F] (1 : E)) := by
    conv_lhs => rw [← (d.baseChange R).sum_repr z, Fin.sum_univ_two]
    simp [c, Module.Basis.baseChange_apply, hd,
      Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  let α := algebraMap E R t
  let β := algebraMap E R (σ t)
  let γ := algebraMap E R ((σ t - t)⁻¹)
  have hγ : γ * (β - α) = 1 := by
    change algebraMap E R ((σ t - t)⁻¹) * (algebraMap E R (σ t) - algebraMap E R t) = 1
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr ht), map_one]
  have hformula (z : Centre F E R) :
      (centreAugmentation z, centreAugmentation (centreConjugation σ z)) =
        (c z 0 * α + c z 1, c z 0 * β + c z 1) := by
    conv_lhs => rw [hz z]
    simp [centreConjugation, α, β]
  refine ⟨?_, ?_⟩
  · intro x y h
    change (centreAugmentation x, centreAugmentation (centreConjugation σ x)) =
      (centreAugmentation y, centreAugmentation (centreConjugation σ y)) at h
    rw [hformula, hformula, Prod.mk.injEq] at h
    have h₀ : c x 0 = c y 0 := by
      calc
        c x 0 = γ * ((c x 0 * β + c x 1) - (c x 0 * α + c x 1)) := by
          rw [show (c x 0 * β + c x 1) - (c x 0 * α + c x 1) = (β - α) * c x 0 by ring,
            ← mul_assoc, hγ, one_mul]
        _ = γ * ((c y 0 * β + c y 1) - (c y 0 * α + c y 1)) := by rw [h.1, h.2]
        _ = c y 0 := by
          rw [show (c y 0 * β + c y 1) - (c y 0 * α + c y 1) = (β - α) * c y 0 by ring,
            ← mul_assoc, hγ, one_mul]
    have h₁ : c x 1 = c y 1 := by
      have hh := h.1
      rwa [h₀, add_right_inj] at hh
    apply c.injective
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
  · rintro ⟨x, y⟩
    let a := γ * (y - x)
    let b := x - a * α
    refine ⟨(a ⊗ₜ[F] t) + (b ⊗ₜ[F] (1 : E)), ?_⟩
    change (centreAugmentation _, centreAugmentation (centreConjugation σ _)) = _
    have h₁ : a * α + b = x := by dsimp [b]; ring
    have h₂ : a * β + b = y := by
      calc
        a * β + b = (γ * (β - α)) * (y - x) + x := by dsimp [a, b]; ring
        _ = y := by rw [hγ, one_mul]; ring
    have hpair : (a * α + b, a * β + b) = (x, y) := Prod.ext h₁ h₂
    simpa [centreConjugation, α, β] using hpair

local instance splitConjugationInvPair (σ : E ≃ₐ[F] E) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ.toRingEquiv

private def adjointBasis (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (s : SecondKind F E A) : Module.Basis ι E A := by
  letI : Module.Finite E A := hA.2.2
  let e := adjointSemilinear s
  exact basisOfLinearIndependentOfCardEqFinrank' (e ∘ b) (b.linearIndependent.map_of_surjective_injective
    s.conjugation e.toAddEquiv.toAddMonoidHom s.conjugation.surjective
    (fun _ h => e.injective (h.trans (map_zero e).symm)) e.map_smulₛₗ) (Module.finrank_eq_card_basis b).symm

@[simp] private theorem adjointBasis_apply (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (s : SecondKind F E A) (i : ι) : adjointBasis hA b s i = unop (s.adjoint (b i)) := by
  simp [adjointBasis]
  rfl

private theorem factorPair_bijective [Algebra.IsQuadraticExtension F E]
    (hA : IsCentralSimple E A) (b : Module.Basis ι E A) (s : SecondKind F E A) :
    Function.Bijective (factorPair (R := R) s) := by
  classical
  let W := Centre F E R
  let τ := centreConjugation (R := R) s.conjugation
  let d := adjointBasis hA b s
  let p : (R ⊗[F] A) →ₐ[F] R ⊗[E] A := factorProjection
  let coord : (R ⊗[F] A) ≃ (ι → W) :=
    associateCentre.toEquiv.trans (b.baseChange W).equivFun.toEquiv
  let out : ((R ⊗[E] A) × (R ⊗[E] A)ᵐᵒᵖ) ≃ (ι → R × R) :=
    (Equiv.prodCongr (b.baseChange R).equivFun.toEquiv
      (MulOpposite.opEquiv.symm.trans (d.baseChange R).equivFun.toEquiv)).trans
      (Equiv.arrowProdEquivProdArrow ι (fun _ => R) (fun _ => R)).symm
  let v (z : W) : R × R := (centreAugmentation z, centreAugmentation (τ z))
  let j : W ≃ R × R := Equiv.ofBijective v (centreProjections_bijective _ s.conjugation_ne)
  suffices he : out ∘ factorPair s = (fun (f : ι → W) i => j (f i)) ∘ coord by
    have hb : Function.Bijective (out ∘ factorPair s) := by
      rw [he]
      exact (Equiv.piCongrRight (fun _ : ι => j)).bijective.comp coord.bijective
    exact ⟨fun _ _ h => hb.injective (congrArg out h),
      fun y => let ⟨x, hx⟩ := hb.surjective (out y); ⟨x, out.injective hx⟩⟩
  funext x i
  letI : Module E W := (Algebra.TensorProduct.rightAlgebra (R := F) (A := R) (B := E)).toModule
  let y : W ⊗[E] A := associateCentre (E := E) x
  let c := fun k => (b.baseChange W).repr y k
  change ((b.baseChange R).repr (p x) i, (d.baseChange R).repr (p (adjointAt s x)) i) =
    (centreAugmentation (c i), centreAugmentation (τ (c i)))
  have hy : y = ∑ k, c k ⊗ₜ[E] b k := by
    conv_lhs => rw [← (b.baseChange W).sum_repr y]
    simp [c, Module.Basis.baseChange_apply, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  apply Prod.ext
  · rw [show p x = changeCoefficients centreAugmentation y from factorProjection_associate x]
    exact coord_change b centreAugmentation y i
  · change (d.baseChange R).repr (factorProjection (adjointAt s x)) i = _
    rw [factorProjection_associate, associateCentre_adjoint, show associateCentre x = y from rfl, hy, map_sum, map_sum]
    change (d.baseChange R).repr (∑ k, centreAugmentation (τ (c k)) ⊗ₜ[E]
      unop (s.adjoint (b k))) i = _
    have hc (k : ι) : centreAugmentation (τ (c k)) ⊗ₜ[E] unop (s.adjoint (b k)) =
        centreAugmentation (τ (c k)) • (d.baseChange R) k := by
      rw [Module.Basis.baseChange_apply, adjointBasis_apply]
      simp [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [hc]
    rw [Module.Basis.repr_sum_self]

private theorem factorPair_apply (s : SecondKind F E A) (x : R ⊗[F] A) :
    factorPair s x = (factorProjection x, op (factorProjection (adjointAt s x))) := rfl

private theorem normOne_inverse (hA : IsCentralSimple E A) (b : Module.Basis ι E A)
    (y : (R ⊗[E] A)ˣ) (hy : normAt hA b y.val = 1) :
    normAt hA b (y⁻¹).val = 1 := by
  have h := (normHom hA b).map_mul y.val (y⁻¹).val
  rw [Units.mul_inv, map_one, show normHom hA b y.val = 1 from hy, one_mul] at h
  exact h.symm

theorem splitCentreComparison : SplitCentreComparison.{u} := by
  intro F E A _ _ _ _ _ _ _ _ _ hA ι _ b s R _ _ _ _
  let p : (R ⊗[F] A) →ₐ[F] (R ⊗[E] A) := factorProjection
  let B := R ⊗[E] A
  have hp := factorPair_bijective (R := R) hA b s
  refine ⟨hp, ?_, ?_⟩
  · intro x
    rw [factorPair_apply s (adjointAt s x), factorPair_apply s x, adjointAt_adj]
    rfl
  let e := AlgEquiv.ofBijective (factorPair (R := R) s) hp
  let re : (R ⊗[F] A)ˣ ≃* (B × Bᵐᵒᵖ)ˣ := Units.mapEquiv e.toMulEquiv
  let g (y : {y : Bˣ // normAt hA b y.val = 1}) : (R ⊗[F] A)ˣ :=
    re.symm ⟨(y.1.val, op (y.1⁻¹).val), ((y.1⁻¹).val, op y.1.val),
      Prod.ext (Units.mul_inv y.1) (congrArg op (Units.mul_inv y.1)),
      Prod.ext (Units.inv_mul y.1) (congrArg op (Units.inv_mul y.1))⟩
  have hg (y : {y : Bˣ // normAt hA b y.val = 1}) :
      factorPair s (g y).val = (y.1.val, op (y.1⁻¹).val) :=
    congrArg Units.val (re.apply_symm_apply _)
  have hgin (y : {y : Bˣ // normAt hA b y.val = 1}) : IsSpecialUnitary hA b s (g y) := by
    have hx := hg y
    rw [factorPair_apply, Prod.mk.injEq] at hx
    have h₂ := op_injective hx.2
    refine ⟨?_, ?_⟩
    · apply hp.injective
      rw [map_mul, map_one, factorPair_apply s (adjointAt s _), adjointAt_adj, hg]
      change (p (adjointAt s (g y).val), op (p (g y).val)) *
        (y.1.val, op (y.1⁻¹).val) = 1
      rw [hx.1, h₂]
      exact Prod.ext (Units.inv_mul y.1) (congrArg op (Units.inv_mul y.1))
    · apply (centreProjections_bijective (R := R) s.conjugation s.conjugation_ne).injective
      apply Prod.ext
      · change centreAugmentation (unitaryNorm hA b (g y).val) = centreAugmentation 1
        rw [← factorProjection_norm, hx.1, map_one]
        exact y.2
      · change centreAugmentation (centreConjugation s.conjugation (unitaryNorm hA b (g y).val)) =
          centreAugmentation (centreConjugation s.conjugation 1)
        rw [← unitaryNorm_adjoint hA b s, ← factorProjection_norm, h₂, map_one, map_one]
        exact normOne_inverse hA b y.val y.2
  let forward (x : {x : (R ⊗[F] A)ˣ // IsSpecialUnitary hA b s x}) :
      {y : Bˣ // normAt hA b y.val = 1} :=
    ⟨Units.map p.toMonoidHom x.val, by
      change normAt hA b (p x.val.val) = 1
      rw [factorProjection_norm, x.prop.2, map_one]⟩
  refine ⟨{ toFun := forward, invFun := fun y => ⟨g y, hgin y⟩
            left_inv := ?_, right_inv := ?_ }, fun _ => rfl, hg⟩
  · intro x
    apply Subtype.ext
    apply Units.ext
    apply hp.injective
    change factorPair s (g (forward x)).val = _
    rw [hg, factorPair_apply]
    apply Prod.ext
    · rfl
    · apply MulOpposite.unop_injective
      change p (x.val⁻¹).val = p (adjointAt s x.val.val)
      rw [← adjointUnit_val, (adjoint_eq_inverse_iff s x.val).mp x.prop.1]
  · intro y
    apply Subtype.ext
    apply Units.ext
    exact congrArg Prod.fst (hg y)

theorem splitCentreNaturality : SplitCentreNaturality.{u} := by
  intro F E A _ _ _ _ _ _ _ R S _ _ _ _ _ _ _ _ f x
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, factorProjection_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem factorReducedNorm : FactorReducedNorm.{u} := by
  intro E A L R _ _ _ _ _ _ _ _ _ hA ι _ b
  have hL : IsCentralSimple L (L ⊗[E] A) := _root_.RM03.CSA.isCentralSimple_baseChange hA
  refine ⟨hL, ?_, ?_⟩
  · exact congrArg Nat.sqrt (_root_.RM03.CSA.finrank_baseChange (L := L) hA)
  intro x
  let d := factorScalarExtension (E := E) (L := L) (R := R) (A := A)
  have hc (i : ι) : ((b.baseChange L).baseChange R).repr (d x) i =
      (b.baseChange R).repr x i := by
    induction x using TensorProduct.inductionOn with
    | tmul r a =>
      change ((b.baseChange L).baseChange R).repr (r ⊗ₜ[L] ((1 : L) ⊗ₜ[E] a)) i =
        (b.baseChange R).repr (r ⊗ₜ[E] a) i
      simp only [Module.Basis.baseChange_repr_tmul, smul_assoc, one_smul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  change MvPolynomial.eval₂ (algebraMap L R) _ (_root_.RM03.CSA.genericReducedNorm hL (b.baseChange L)) =
    MvPolynomial.eval₂ (algebraMap E R) _ (_root_.RM03.CSA.genericReducedNorm hA b)
  rw [_root_.RM03.CSA.reducedNorm_basis_baseChange hA b hL, MvPolynomial.eval₂_map,
    ← IsScalarTower.algebraMap_eq E L R]
  congr 1
  exact funext hc

end SplitCentre


section MatrixComparison

variable {K : Type u} [Field K] [Algebra E K]
  [Algebra E R] [Algebra E S] [Algebra K R] [Algebra K S]
  [IsScalarTower F E R] [IsScalarTower F E S] [IsScalarTower E K R] [IsScalarTower E K S]

@[simp] theorem matrixProjection_tmul (e : (K ⊗[E] A) ≃ₐ[K] Mat E A K)
    (r : R) (a : A) :
    matrixProjection e (r ⊗ₜ[F] a) = r • (e (1 ⊗ₜ[E] a)).map (algebraMap K R) := by
  change extendSplitting e (factorProjection (r ⊗ₜ[F] a)) = _
  rw [factorProjection_tmul, extendSplitting_tmul]

private def normOneUnitsEquiv (hA : IsCentralSimple E A) (b : Module.Basis ι E A) :
    {y : (R ⊗[E] A)ˣ // normAt hA b y.val = 1} ≃ normOne (R := R) hA b where
  toFun y := ⟨y.val.val, y.prop⟩
  invFun y := ⟨(isUnit_of_normAt_eq_one hA b y.val y.prop).unit,
    by rw [IsUnit.unit_spec]; exact y.prop⟩
  left_inv y := Subtype.ext (Units.ext (IsUnit.unit_spec _))
  right_inv y := Subtype.ext (IsUnit.unit_spec (isUnit_of_normAt_eq_one hA b y.val y.prop))

theorem matrixComparison : MatrixComparison.{u} := by
  intro F E A K _ _ _ _ _ _ _ _ _ _ _ hA ι _ b s e R _ _ _ _ _ _
  obtain ⟨_, _, split, hsplit, _⟩ :=
    splitCentreComparison (R := R) hA b s
  refine ⟨split.trans ((normOneUnitsEquiv hA b).trans (normOneSplit hA b e).toEquiv), ?_⟩
  intro x
  rw [Equiv.trans_apply, Equiv.trans_apply]
  have hl : ((normOneSplit hA b e).toEquiv (normOneUnitsEquiv hA b (split x))).val =
      extendSplitting e (split x).val.val := by rfl
  exact hl.trans (congrArg (fun z : (R ⊗[E] A)ˣ => extendSplitting e z.val) (hsplit x))

private theorem mapMatrix_smul_coeff {T U : Type u} [CommRing T] [CommRing U]
    {d : ℕ} (f : T →+* U) (r : T) (m : Matrix (Fin d) (Fin d) T) :
    (r • m).map f = f r • m.map f := by
  apply Matrix.ext
  intro i j
  exact f.map_mul r (m i j)

theorem matrixNaturality : MatrixNaturality.{u} := by
  intro F E A K _ _ _ _ _ _ _ _ _ e R S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f x
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, matrixProjection_tmul]
    apply Matrix.ext
    intro i j
    let t := (e (1 ⊗ₜ[E] a)) i j
    change f r * algebraMap K S t = f (r * algebraMap K R t)
    rw [map_mul, f.commutes]
  | add x y hx hy =>
    change _ = f.toRingHom.mapMatrix (matrixProjection e (x + y))
    simp only [map_add, hx, hy]
    rfl

private theorem extendOperator_smul [Algebra F K]
    {σ : K ≃ₐ[F] K} (β : Mat E A K →ₛₗ[σ.toRingHom] Mat E A K)
    (f : R →ₐ[F] S) (r : R) (x : Mat E A R) :
    extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom (r • x) =
      f r • extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom x := by
  simp only [extendMatrixOperator, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum,
    mul_smul]
  rfl

private theorem extendOperator_add [Algebra F K]
    {σ : K ≃ₐ[F] K} (β : Mat E A K →ₛₗ[σ.toRingHom] Mat E A K)
    (f : R →ₐ[F] S) (x y : Mat E A R) :
    extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom (x + y) =
      extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom x +
      extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom y := by
  simp only [extendMatrixOperator, Matrix.add_apply, map_add, add_smul, Finset.sum_add_distrib]

private theorem extendOperator_on_constants [Algebra F K]
    {σ : K ≃ₐ[F] K} (β : Mat E A K →ₛₗ[σ.toRingHom] Mat E A K) (f : R →ₐ[F] S)
    (hf : ∀ k : K, f (algebraMap K R k) = algebraMap K S (σ k)) (x : Mat E A K) :
    extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom
      (x.map (algebraMap K R)) = (β x).map (algebraMap K S) := by
  have hx : x = ∑ i, ∑ j, x i j • Matrix.single i j (1 : K) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single x
  have hβ : β x = ∑ i, ∑ j, σ (x i j) • β (Matrix.single i j 1) := by
    conv_lhs => rw [hx]
    simp only [map_sum, map_smulₛₗ]
    rfl
  simp only [extendMatrixOperator, Matrix.map_apply, AlgHom.toRingHom_eq_coe]
  change (∑ i, ∑ j, f (algebraMap K R (x i j)) •
    (β (Matrix.single i j 1)).map (algebraMap K S)) =
    (algebraMap K S).mapMatrix (β x)
  simp only [hf, hβ, map_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  exact (mapMatrix_smul_coeff (algebraMap K S) _ _).symm

private theorem matrixTransport_on_elements [Algebra F K]
    (s : SecondKind F E A) (e : (K ⊗[E] A) ≃ₐ[K] Mat E A K)
    (σ : K ≃ₐ[F] K) (odd : Bool) (β : Mat E A K →ₛₗ[σ.toRingHom] Mat E A K)
    (hβ : ∀ a : A, β (e (1 ⊗ₜ[E] a)) =
      e (1 ⊗ₜ[E] (if odd then unop (s.adjoint a) else a)))
    (f : R →ₐ[F] S) (hf : ∀ k : K, f (algebraMap K R k) = algebraMap K S (σ k))
    (x : R ⊗[F] A) :
    matrixProjection e (changeCoefficients f x) =
      extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom
        (matrixProjection e (if odd then adjointAt s x else x)) := by
  let L := extendMatrixOperator (K := K) (E := E) (A := A) β.toAddMonoidHom f.toRingHom
  have hc : ∀ a : A, β (e (1 ⊗ₜ[E] (if odd then unop (s.adjoint a) else a))) =
      e (1 ⊗ₜ[E] a) := by
    intro a
    cases odd
    · simpa using hβ a
    · simpa only [Bool.true_eq, ite_true, s.adjoint_adjoint] using hβ (unop (s.adjoint a))
  have hadd (y z : R ⊗[F] A) :
      (if odd then adjointAt s (y + z) else y + z) =
        (if odd then adjointAt s y else y) + (if odd then adjointAt s z else z) := by
    cases odd <;> simp [adjointAt, MulOpposite.unop_add]
  change matrixProjection e (changeCoefficients f x) =
    L (matrixProjection e (if odd then adjointAt s x else x))
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    have ht : (if odd then adjointAt s (r ⊗ₜ[F] a) else r ⊗ₜ[F] a) =
        r ⊗ₜ[F] (if odd then unop (s.adjoint a) else a) := by
      cases odd <;> simp
    rw [ht]
    simp only [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      matrixProjection_tmul, L, extendOperator_smul, extendOperator_on_constants β f hf, hc]
  | add x y hx hy =>
    rw [map_add, map_add, hadd, map_add, show ∀ p q, L (p + q) = L p + L q from
      extendOperator_add β f, hx, hy]

theorem matrixSemilinearTransport : MatrixSemilinearTransport.{u} := by
  intro F E A K _ _ _ _ _ _ _ _ _ _ _ _ _ hA ι _ b s e σ odd β _ hβ
    R S _ _ _ _ _ _ _ _ _ _ _ _ f hf x hx
  have ha : adjointAt s x.val = (x⁻¹).val :=
    congrArg Units.val ((adjoint_eq_inverse_iff s x).mp hx.1)
  have h := matrixTransport_on_elements s e σ odd β hβ f hf x.val
  rw [ha] at h
  exact h

end MatrixComparison

end

end LinearAlgebraicGroups.UnitaryNormEquations
