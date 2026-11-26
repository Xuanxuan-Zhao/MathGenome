import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedCharpoly
import Mathlib.Algebra.Algebra.Opposite

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u v w

namespace LinearAlgebraicGroups.QuaternionHermitianCocharacters

noncomputable section

variable {F : Type u} [Field F] {B : Type v} [Ring B] [Algebra F B]
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Conjugate transpose for a coefficient algebra with an antiautomorphism. -/
def adjoint {C : Type*} [Ring C] [Algebra F C] {m n : Type*}
    (s : C →ₐ[F] Cᵐᵒᵖ) (X : Matrix m n C) : Matrix n m C :=
  fun i j => unop (s (X j i))

theorem adjoint_mul {C : Type*} [Ring C] [Algebra F C] {m n p : Type*} [Fintype n]
    (s : C →ₐ[F] Cᵐᵒᵖ) (X : Matrix m n C) (Y : Matrix n p C) :
    adjoint s (X * Y) = adjoint s Y * adjoint s X := by
  ext i j
  simp [adjoint, Matrix.mul_apply, map_sum]

omit [Fintype ι] in
theorem adjoint_one {C : Type*} [Ring C] [Algebra F C]
    (s : C →ₐ[F] Cᵐᵒᵖ) : adjoint s (1 : Matrix ι ι C) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [adjoint, Matrix.one_apply, h, eq_comm]

/-- Extension of the antiautomorphism by the identity on the test algebra. -/
def extendConjugation {R : Type*} [CommRing R] [Algebra F R]
    (s : B →ₐ[F] Bᵐᵒᵖ) : (R ⊗[F] B) →ₐ[F] (R ⊗[F] B)ᵐᵒᵖ :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.includeLeft.toOpposite fun r t =>
      (Commute.all r t).map Algebra.TensorProduct.includeLeft)
    ((AlgHom.op Algebra.TensorProduct.includeRight).comp s)
    (fun r b => by
      change Commute (op (r ⊗ₜ[F] (1 : B))) (op ((1 : R) ⊗ₜ[F] unop (s b)))
      exact ((Commute.one_right r).tmul (Commute.one_left (unop (s b)))).op)

@[simp] theorem extendConjugation_tmul {R : Type*} [CommRing R] [Algebra F R]
    (s : B →ₐ[F] Bᵐᵒᵖ) (r : R) (b : B) :
    unop (extendConjugation s (r ⊗ₜ[F] b)) = r ⊗ₜ[F] unop (s b) := by
  rw [extendConjugation, Algebra.TensorProduct.lift_tmul]
  change ((1 : R) ⊗ₜ[F] unop (s b)) * (r ⊗ₜ[F] (1 : B)) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The Hermitian pairing on the column model of a finite free right module. -/
def pairing {C : Type*} [Ring C] [Algebra F C] (s : C →ₐ[F] Cᵐᵒᵖ)
    (H : Matrix ι ι C) (x y : ι → C) : C :=
  ∑ j, (∑ i, unop (s (x i)) * H i j) * y j

/-- Scalar extension on the coefficient algebra. -/
abbrev changeScalars {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) : R ⊗[F] B →ₐ[F] S ⊗[F] B :=
  Algebra.TensorProduct.map f (AlgHom.id F B)

theorem changeScalars_conjugation {R S : Type*} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] (f : R →ₐ[F] S) (s : B →ₐ[F] Bᵐᵒᵖ)
    (a : R ⊗[F] B) :
    changeScalars f (unop (extendConjugation s a)) =
      unop (extendConjugation s (changeScalars f a)) := by
  induction a using TensorProduct.inductionOn with
  | tmul r b => simp [Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp [ha, hb]

/-- Invertible matrices that preserve the scalar-extended Gram matrix. -/
def isometries {C : Type*} [Ring C] [Algebra F C]
    (s : C →ₐ[F] Cᵐᵒᵖ) (H : Matrix ι ι C) : Subgroup (Matrix ι ι C)ˣ where
  carrier := {g | (adjoint s g.val * H) * g.val = H}
  one_mem' := by simp [adjoint_one]
  mul_mem' := by
    intro g h hg hh
    change (adjoint s g.val * H) * g.val = H at hg
    change (adjoint s h.val * H) * h.val = H at hh
    change (adjoint s (g.val * h.val) * H) * (g.val * h.val) = H
    rw [adjoint_mul]
    calc
      (adjoint s h.val * adjoint s g.val * H) * (g.val * h.val) =
        (adjoint s h.val * ((adjoint s g.val * H) * g.val)) * h.val := by
          simp only [mul_assoc]
      _ = H := by rw [hg, hh]
  inv_mem' := by
    intro g hg
    change (adjoint s g.val * H) * g.val = H at hg
    change (adjoint s (↑g⁻¹ : Matrix ι ι C) * H) * (↑g⁻¹ : Matrix ι ι C) = H
    conv_lhs => enter [1, 2]; rw [← hg]
    calc
      (adjoint s (↑g⁻¹ : Matrix ι ι C) * ((adjoint s g.val * H) * g.val)) *
          (↑g⁻¹ : Matrix ι ι C) =
        (adjoint s (g.val * (↑g⁻¹ : Matrix ι ι C)) * H) *
          (g.val * (↑g⁻¹ : Matrix ι ι C)) := by
          rw [adjoint_mul]
          simp only [mul_assoc]
      _ = H := by simp [adjoint_one]

/-- The isometry group functor of the pairing, in a right-module basis. -/
def isometryPoints (s : B →ₐ[F] Bᵐᵒᵖ) (H : Matrix ι ι B) :
    TestAlgebra F ⥤ GrpCat.{max u v w} where
  obj R := GrpCat.of (isometries (extendConjugation (R := R) s)
    (H.map (Algebra.TensorProduct.includeRight : B →ₐ[F] R ⊗[F] B)))
  map {R S} f := GrpCat.ofHom
    { toFun := fun g =>
        ⟨Units.map (changeScalars (B := B) f.hom).mapMatrix.toMonoidHom g.val, by
          have hg := congrArg
            (changeScalars (B := B) f.hom).mapMatrix g.property
          change (adjoint (extendConjugation s)
            ((changeScalars (B := B) f.hom).mapMatrix g.val.val) *
            H.map (Algebra.TensorProduct.includeRight : B →ₐ[F] S ⊗[F] B)) *
            ((changeScalars (B := B) f.hom).mapMatrix g.val.val) =
            H.map (Algebra.TensorProduct.includeRight : B →ₐ[F] S ⊗[F] B)
          rw [map_mul, map_mul] at hg
          have hadj :
              (changeScalars (B := B) f.hom).mapMatrix
                (adjoint (extendConjugation s) g.val.val) =
              adjoint (extendConjugation s)
                ((changeScalars (B := B) f.hom).mapMatrix g.val.val) := by
            ext i j
            exact changeScalars_conjugation f.hom s _
          rw [hadj] at hg
          have hH : (changeScalars (B := B) f.hom).mapMatrix
              (H.map (Algebra.TensorProduct.includeRight : B →ₐ[F] R ⊗[F] B)) =
              H.map (Algebra.TensorProduct.includeRight : B →ₐ[F] S ⊗[F] B) := by
            ext i j
            change changeScalars f.hom (1 ⊗ₜ[F] H i j) = 1 ⊗ₜ[F] H i j
            simp [Algebra.TensorProduct.map_tmul]
          rwa [hH] at hg⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  map_id R := by
    apply GrpCat.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    change changeScalars (AlgHom.id F R) (g.val.val i j) = g.val.val i j
    induction (g.val.val i j) using TensorProduct.inductionOn with
    | tmul r b => simp
    | add a b ha hb => simp
  map_comp {R S T} f g := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Units.ext
    ext i j
    change changeScalars (g.hom.comp f.hom) (x.val.val i j) =
      changeScalars g.hom (changeScalars f.hom (x.val.val i j))
    induction (x.val.val i j) using TensorProduct.inductionOn with
    | tmul r b => simp [Algebra.TensorProduct.map_tmul]
    | add a b ha hb => simp [ha, hb]

/-- The multiplicative group on test algebras, with its groups in the universe of
the isometry groups. Its points and maps are the standard units and unit maps. -/
abbrev multiplicativePoints (F : Type u) [Field F] :
    TestAlgebra F ⥤ GrpCat.{max u v} :=
  Specs.StandardGroups.multiplicativePoints F ⋙ GrpCat.uliftFunctor.{v,u}

/-- Noncentrality is tested on all commutative test algebras by pointwise commutation. -/
def IsNoncentral {s : B →ₐ[F] Bᵐᵒᵖ} {H : Matrix ι ι B}
    (cochar : multiplicativePoints.{u,max v w} F ⟶ isometryPoints s H) : Prop :=
  ¬ ∀ (R : TestAlgebra F) (t : (multiplicativePoints.{u,max v w} F).obj R)
      (g : (isometryPoints s H).obj R), Commute (cochar.app R t) g

end

end LinearAlgebraicGroups.QuaternionHermitianCocharacters

namespace LinearAlgebraicGroups.Specs.QuaternionHermitianCocharacters

open LinearAlgebraicGroups.QuaternionHermitianCocharacters

/-- The canonical quaternion conjugation is reduced trace minus the element.
Degree two allows the characteristic-two quaternion division algebras. -/
def HermitianIsotropy : Prop :=
  ∀ {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (_ : _root_.Specs.RM03.CSA.degree F B = 2)
    (s : B ≃ₐ[F] Bᵐᵒᵖ)
    (_ : ∀ x, unop (s x) = algebraMap F B
      (-((_root_.Specs.RM03.CSA.reducedCharpoly hB x).coeff
        (_root_.Specs.RM03.CSA.degree F B - 1))) - x)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι B)
    (_ : adjoint s.toAlgHom H = H)
    (_ : ∀ x : ι → B, x ≠ 0 → ∃ y, pairing s.toAlgHom H x y ≠ 0)
    (_ : ∀ x : ι → B, ∃ a : F, pairing s.toAlgHom H x x = algebraMap F B a)
    (cochar : multiplicativePoints.{u,max v w} F ⟶ isometryPoints s.toAlgHom H),
    IsNoncentral cochar → ∃ x : ι → B, x ≠ 0 ∧ pairing s.toAlgHom H x x = 0

end LinearAlgebraicGroups.Specs.QuaternionHermitianCocharacters
