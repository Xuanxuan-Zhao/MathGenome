import MathGenome.Internal.FourVolumeAlgebra.Specs.Shared.Lie.PBWOrdered
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-! The actual successive quotients of the word-length filtration.
The grading is indexed by ℕ; all negative filtration steps are zero.
The proof parameter `hf` is the already specified filtration property, not PBW. -/
open scoped DirectSum

namespace Shared.Lie.PBW
universe u v w
variable {k : Type u} {g : Type v} {ι : Type w}
  [CommRing k] [LieRing g] [LieAlgebra k g] [LinearOrder ι]

/-- The span of the PBW words with the specified length bound. -/
def boundedSpan (b : Module.Basis ι k g) (m : ℤ) : Submodule k (U k g) :=
  Submodule.span k {a | ∃ l : OrderedWord ι, (l.val.length : ℤ) ≤ m ∧ orderedMonomial b l = a}
end Shared.Lie.PBW

namespace Shared.Lie.PBW.Graded
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

abbrev Step (n : ℕ) := filtration k g (n : ℤ)
def lower (n : ℕ) : Submodule k (Step k g n) :=
  (filtration k g ((n : ℤ) - 1)).comap (Step k g n).subtype
abbrev Piece (n : ℕ) := Step k g n ⧸ lower k g n
abbrev Associated := ⨁ n : ℕ, Piece k g n

def principal (n : ℕ) : Step k g n →ₗ[k] Piece k g n := (lower k g n).mkQ
noncomputable def symbol (n : ℕ) : Step k g n →ₗ[k] Associated k g :=
  (DirectSum.lof k ℕ (Piece k g) n).comp (principal k g n)

variable {k g} [hF : Fact (Specs.Shared.Lie.filtrationType k g)]
local notation "hf" => hF.out

private def stepMul (i j : ℕ) : Step k g i →ₗ[k] Step k g j →ₗ[k] Step k g (i+j) where
  toFun a :=
    { toFun := fun b => ⟨a.val * b.val, by
        simpa only [Step, Nat.cast_add] using hf.2.2.2.2.1 i j a b a.property b.property⟩
      map_add' := fun _ _ => Subtype.ext (mul_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (Algebra.mul_smul_comm _ _ _) }
  map_add' := fun _ _ => LinearMap.ext fun _ => Subtype.ext (add_mul _ _ _)
  map_smul' := fun _ _ => LinearMap.ext fun _ => Subtype.ext (Algebra.smul_mul_assoc _ _ _)

private def rawMul (i j : ℕ) : Step k g i →ₗ[k] Step k g j →ₗ[k] Piece k g (i+j) :=
  (LinearMap.llcomp k (Step k g j) (Step k g (i+j)) (Piece k g (i+j))
    (principal k g (i+j))).comp (stepMul i j)

private theorem rawMul_lower_left (i j : ℕ) : lower k g i ≤ (rawMul i j).ker := by
  intro a ha
  apply LinearMap.ext
  intro b
  change principal k g (i+j) (stepMul i j a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change a.val * b.val ∈ filtration k g (((i+j : ℕ) : ℤ)-1)
  have h := hf.2.2.2.2.1 ((i : ℤ)-1) j a b ha b.property
  simpa [Nat.cast_add, sub_add_eq_add_sub] using h

private theorem rawMul_lower_right (i j : ℕ) : lower k g j ≤ (rawMul i j).flip.ker := by
  intro b hb
  apply LinearMap.ext
  intro a
  change principal k g (i+j) (stepMul i j a b) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change a.val * b.val ∈ filtration k g (((i+j : ℕ) : ℤ)-1)
  have h := hf.2.2.2.2.1 i ((j : ℤ)-1) a b a.property hb
  simpa [Nat.cast_add, add_sub_assoc] using h

noncomputable def pieceMul (i j : ℕ) : Piece k g i →ₗ[k] Piece k g j →ₗ[k] Piece k g (i+j) :=
  (rawMul i j).liftQ₂ (lower k g i) (lower k g j)
    (rawMul_lower_left i j) (rawMul_lower_right i j)

@[simp] theorem pieceMul_principal (i j : ℕ) (a : Step k g i) (b : Step k g j) :
    pieceMul i j (principal k g i a) (principal k g j b) =
      principal k g (i+j) ⟨a.val * b.val, (stepMul i j a b).property⟩ := rfl

omit hF in
private theorem sigma_principal_eq {i j : ℕ} (a : Step k g i) (b : Step k g j)
    (h : i = j) (hab : a.val = b.val) :
    (⟨i, principal k g i a⟩ : GradedMonoid (Piece k g)) = ⟨j, principal k g j b⟩ := by
  subst j
  congr 1
  exact congrArg (principal k g i) (Subtype.ext hab)

omit hF in
private theorem sigma_principal_eq_mod {i j : ℕ} (a : Step k g i) (b : Step k g j)
    (h : i = j) (hab : a.val - b.val ∈ filtration k g ((i : ℤ)-1)) :
    (⟨i, principal k g i a⟩ : GradedMonoid (Piece k g)) = ⟨j, principal k g j b⟩ := by
  subst j
  congr 1
  exact (Submodule.Quotient.eq _).mpr hab

theorem symbol_congr {i j : ℕ} (a : Step k g i) (b : Step k g j)
    (h : i = j) (hab : a.val = b.val) : symbol k g i a = symbol k g j b := by
  exact DFinsupp.single_eq_of_sigma_eq (sigma_principal_eq a b h hab)

noncomputable instance pieceGOne : GradedMonoid.GOne (Piece k g) where
  one := principal k g 0 ⟨1, hf.2.2.1⟩

noncomputable instance pieceGMul : GradedMonoid.GMul (Piece k g) where
  mul := fun {i j} a b => pieceMul i j a b

noncomputable instance pieceGNonUnital : DirectSum.GNonUnitalNonAssocSemiring (Piece k g) where
  toGMul := pieceGMul
  mul_zero := fun a => map_zero (pieceMul _ _ a)
  zero_mul := fun b => by
    change pieceMul _ _ 0 b = 0
    rw [map_zero]; rfl
  mul_add := fun a b c => map_add (pieceMul _ _ a) b c
  add_mul := fun a b c => by
    change pieceMul _ _ (a+b) c = _
    rw [map_add]; rfl

noncomputable instance pieceGMonoid : GradedMonoid.GMonoid (Piece k g) where
  toGMul := pieceGMul
  toGOne := pieceGOne
  one_mul := by
    rintro ⟨i, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      change (⟨0+i, principal k g (0+i) (stepMul 0 i ⟨1, hf.2.2.1⟩ a)⟩ :
        GradedMonoid (Piece k g)) = ⟨i, principal k g i a⟩
      apply sigma_principal_eq _ _ (zero_add i)
      exact one_mul a.val
  mul_one := by
    rintro ⟨i, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      change (⟨i+0, principal k g (i+0) (stepMul i 0 a ⟨1, hf.2.2.1⟩)⟩ :
        GradedMonoid (Piece k g)) = ⟨i, principal k g i a⟩
      apply sigma_principal_eq _ _ (add_zero i)
      exact mul_one a.val
  mul_assoc := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨l, c⟩
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      induction b using Submodule.Quotient.induction_on with
      | _ b =>
        induction c using Submodule.Quotient.induction_on with
        | _ c =>
          change (⟨(i+j)+l, principal k g ((i+j)+l) (stepMul (i+j) l (stepMul i j a b) c)⟩ :
            GradedMonoid (Piece k g)) =
            ⟨i+(j+l), principal k g (i+(j+l)) (stepMul i (j+l) a (stepMul j l b c))⟩
          apply sigma_principal_eq _ _ (Nat.add_assoc i j l)
          exact mul_assoc a.val b.val c.val

noncomputable instance pieceGRing : DirectSum.GRing (Piece k g) where
  __ := pieceGMonoid (k := k) (g := g)
  __ := pieceGNonUnital (k := k) (g := g)
  natCast := fun n => principal k g 0 ⟨n, by
    simpa [Step, Algebra.smul_def] using
      (filtration k g 0).smul_mem (n : k) hf.2.2.1⟩
  natCast_zero := by
    change principal k g 0 ⟨(0 : ℕ), _⟩ = 0
    have he : (⟨((0 : ℕ) : U k g), by simp⟩ : Step k g 0) = 0 := Subtype.ext (Nat.cast_zero)
    rw [he, map_zero]
  natCast_succ := by
    intro n
    change principal k g 0 _ = principal k g 0 _ + principal k g 0 _
    rw [← map_add]
    congr 1
    exact Subtype.ext (Nat.cast_add_one n)
  intCast := fun n => principal k g 0 ⟨n, by
    simpa [Step, Algebra.smul_def] using (filtration k g 0).smul_mem (n : k) hf.2.2.1⟩
  intCast_ofNat := by
    intro n
    congr 1
    exact Subtype.ext (Int.cast_natCast n)
  intCast_negSucc_ofNat := by
    intro n
    rw [← map_neg]
    congr 1
    exact Subtype.ext (Int.cast_negSucc n)

@[simp] theorem symbol_mul (i j : ℕ) (a : Step k g i) (b : Step k g j) :
    symbol k g i a * symbol k g j b =
      symbol k g (i+j) ⟨a.val * b.val, (stepMul i j a b).property⟩ := by
  exact DirectSum.of_mul_of (A := Piece k g) (principal k g i a) (principal k g j b)

@[simp] theorem symbol_one : symbol k g 0 ⟨1, hf.2.2.1⟩ = (1 : Associated k g) := rfl

/-- Scalars lie in filtration degree zero. -/
private def scalarStep : k →ₗ[k] Step k g 0 :=
  (Algebra.linearMap k (U k g)).codRestrict _ fun r => by
    change algebraMap k (U k g) r ∈ Step k g 0
    simpa only [Algebra.algebraMap_eq_smul_one] using (Step k g 0).smul_mem r hf.2.2.1

noncomputable instance pieceGAlgebra : DirectSum.GAlgebra k (Piece k g) where
  toFun := ((principal k g 0).comp scalarStep).toAddMonoidHom
  map_one := by
    change principal k g 0 _ = principal k g 0 _
    congr 1
  map_mul := by
    intro r s
    change (⟨0, principal k g 0 (scalarStep (r*s))⟩ : GradedMonoid (Piece k g)) =
      ⟨0+0, principal k g (0+0) (stepMul 0 0 (scalarStep r) (scalarStep s))⟩
    apply sigma_principal_eq _ _ rfl
    exact map_mul (algebraMap k (U k g)) r s
  commutes := by
    rintro r ⟨i, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      change (⟨0+i, principal k g (0+i) (stepMul 0 i (scalarStep r) a)⟩ :
        GradedMonoid (Piece k g)) =
        ⟨i+0, principal k g (i+0) (stepMul i 0 a (scalarStep r))⟩
      apply sigma_principal_eq _ _ (by omega)
      exact Algebra.commutes r a.val
  smul_def := by
    rintro r ⟨i, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      change (⟨i, principal k g i (r • a)⟩ : GradedMonoid (Piece k g)) =
        ⟨0+i, principal k g (0+i) (stepMul 0 i (scalarStep r) a)⟩
      apply sigma_principal_eq _ _ (by omega)
      exact Algebra.smul_def r a.val

omit hF in
private theorem word_mem_step (xs : List g) :
    word k g xs ∈ filtration k g (xs.length : ℤ) :=
  Submodule.subset_span ⟨xs, le_rfl, rfl⟩

private theorem generator_word_commutator (x : g) (ys : List g) :
    inclusion k g x * word k g ys - word k g ys * inclusion k g x ∈
      filtration k g (ys.length : ℤ) := by
  induction ys with
  | nil => simpa [word] using (filtration k g 0).zero_mem
  | cons y ys ih =>
    have hrel : inclusion k g x * inclusion k g y - inclusion k g y * inclusion k g x =
        inclusion k g ⁅x,y⁆ := ((inclusion k g).map_lie x y).symm
    have h₁ := hf.2.2.2.2.1 1 ys.length (inclusion k g ⁅x,y⁆) (word k g ys)
      (hf.2.2.2.1 _) (word_mem_step ys)
    have h₂ := hf.2.2.2.2.1 1 ys.length (inclusion k g y)
      (inclusion k g x * word k g ys - word k g ys * inclusion k g x) (hf.2.2.2.1 _) ih
    have he : inclusion k g x * word k g (y::ys) - word k g (y::ys) * inclusion k g x =
        inclusion k g ⁅x,y⁆ * word k g ys + inclusion k g y *
          (inclusion k g x * word k g ys - word k g ys * inclusion k g x) := by
      simp only [word, List.map_cons, List.prod_cons] at *
      rw [← hrel]
      noncomm_ring
    rw [he]
    simpa [Nat.cast_add, add_comm] using (filtration k g (1+ys.length)).add_mem h₁ h₂

private theorem word_commutator (xs ys : List g) :
    word k g xs * word k g ys - word k g ys * word k g xs ∈
      filtration k g ((xs.length : ℤ) + ys.length - 1) := by
  induction xs with
  | nil => simpa [word] using (filtration k g ((ys.length : ℤ)-1)).zero_mem
  | cons x xs ih =>
    have h₁ := hf.2.2.2.2.1 1 ((xs.length : ℤ)+ys.length-1) (inclusion k g x)
      (word k g xs * word k g ys - word k g ys * word k g xs) (hf.2.2.2.1 _) ih
    have h₂ := hf.2.2.2.2.1 ys.length xs.length
      (inclusion k g x * word k g ys - word k g ys * inclusion k g x) (word k g xs)
      (generator_word_commutator x ys) (word_mem_step xs)
    have he : word k g (x::xs) * word k g ys - word k g ys * word k g (x::xs) =
        inclusion k g x * (word k g xs * word k g ys - word k g ys * word k g xs) +
        (inclusion k g x * word k g ys - word k g ys * inclusion k g x) * word k g xs := by
      simp only [word, List.map_cons, List.prod_cons] at *
      noncomm_ring
    rw [he]
    have h₁' : 1 + ((xs.length : ℤ)+ys.length-1) = xs.length + ys.length := by omega
    rw [h₁'] at h₁
    rw [add_comm] at h₂
    convert (filtration k g (xs.length+ys.length)).add_mem h₁ h₂ using 1 <;>
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] <;> congr 1 <;> omega

/-- The enveloping relation lowers every commutator by one filtration step. -/
theorem commutator_mem (i j : ℤ) (a b : U k g) (ha : a ∈ filtration k g i)
    (hb : b ∈ filtration k g j) : a*b-b*a ∈ filtration k g (i+j-1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨xs, hx, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨ys, hy, rfl⟩ := hb
      exact hf.1 (by omega) (word_commutator xs ys)
    | zero => simpa using (filtration k g (i+j-1)).zero_mem
    | add b c hb hc ihb ihc =>
      simpa only [mul_add, add_mul, add_sub_add_comm] using
        (filtration k g (i+j-1)).add_mem ihb ihc
    | smul r b hb ih =>
      simpa only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub] using
        (filtration k g (i+j-1)).smul_mem r ih
  | zero => simpa using (filtration k g (i+j-1)).zero_mem
  | add a c ha hc iha ihc =>
    simpa only [add_mul, mul_add, add_sub_add_comm] using
      (filtration k g (i+j-1)).add_mem iha ihc
  | smul r a ha ih =>
    simpa only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub] using
      (filtration k g (i+j-1)).smul_mem r ih

noncomputable instance pieceGCommRing : DirectSum.GCommRing (Piece k g) where
  __ := pieceGRing (k := k) (g := g)
  mul_comm := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      induction b using Submodule.Quotient.induction_on with
      | _ b =>
        change (⟨i+j, principal k g (i+j) (stepMul i j a b)⟩ : GradedMonoid (Piece k g)) =
          ⟨j+i, principal k g (j+i) (stepMul j i b a)⟩
        apply sigma_principal_eq_mod _ _ (Nat.add_comm i j)
        simpa only [Nat.cast_add, stepMul, LinearMap.coe_mk, AddHom.coe_mk] using commutator_mem (k := k) (g := g) i j a.val b.val a.property b.property

noncomputable def generator : g →ₗ[k] Associated k g :=
  (symbol k g 1).comp ((inclusion k g).toLinearMap.codRestrict _ hf.2.2.2.1)

noncomputable def canonicalMap : SymmetricAlgebra k g →ₐ[k] Associated k g :=
  SymmetricAlgebra.lift (R := k) (M := g) (A := Associated k g) (generator (k := k) (g := g))

@[simp] theorem canonicalMap_generator (x : g) :
    canonicalMap (SymmetricAlgebra.ι k g x) = generator (k := k) (g := g) x :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Degree-n homogeneous polynomials, described without a basis. -/
def symmetricWord (xs : List g) : SymmetricAlgebra k g :=
  (xs.map (SymmetricAlgebra.ι k g)).prod

def symmetricDegree (n : ℕ) : Submodule k (SymmetricAlgebra k g) :=
  Submodule.span k {a | ∃ xs : List g, xs.length = n ∧ symmetricWord xs = a}

noncomputable def gradedWord {ι : Type w} [LinearOrder ι] (b : Module.Basis ι k g)
    (l : OrderedWord ι) : Associated k g :=
  symbol k g l.val.length ⟨orderedMonomial b l,
    Submodule.subset_span ⟨l.val.map b, by simp, rfl⟩⟩

end Shared.Lie.PBW.Graded

namespace Specs.Shared.Lie.PBW
open _root_.Shared.Lie _root_.Shared.Lie.PBW _root_.Shared.Lie.PBW.Graded
universe u v w

/-- The complete canonical graded PBW conclusion. Bijectivity is of the algebra
homomorphism induced by the principal symbols. The homogeneous-submodule
identity states degree preservation in both directions. The final basis is fixed
on every ordered word (including the empty word), so it also records agreement
with ordered PBW in each degree. The filtration proof is asserted, not assumed. -/
def gradedExpected : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g],
    ∃ hf : filtrationType k g,
      letI : Fact (filtrationType k g) := ⟨hf⟩
      Function.Bijective (canonicalMap (k := k) (g := g)) ∧
      (∀ n : ℕ, Submodule.map (canonicalMap (k := k) (g := g)).toLinearMap
        (symmetricDegree (k := k) (g := g) n) =
          LinearMap.range (DirectSum.lof k ℕ (Piece k g) n)) ∧
      (∀ (ι : Type w) [LinearOrder ι] (b : Module.Basis ι k g),
        ∃ B : Module.Basis (OrderedWord ι) k (Associated k g),
          ∀ l, B l = gradedWord b l ∧
            canonicalMap (symmetricWord (l.val.map b)) = gradedWord b l)

/-- A separately reusable description of the filtered PBW basis. -/
def filteredBasisExpected : Prop :=
  ∀ (k : Type u) (g : Type v) (ι : Type w) [CommRing k] [LieRing g]
    [LieAlgebra k g] [LinearOrder ι] (b : Module.Basis ι k g) (m : ℤ),
    filtration k g m = boundedSpan b m

end Specs.Shared.Lie.PBW
