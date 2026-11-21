import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.NilpotentTests
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.IdealThickenings

noncomputable section
open scoped DirectSum

namespace AdvCommAlg.FormalLifting

open Specs.AdvCommAlg.FormalLifting.Thickenings

universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

lemma baseIdeal_eq_kernel (J : Ideal B) :
    baseIdeal (A := A) J = RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap A B)) := by
  ext a
  change (algebraMap A B a ∈ J) ↔ Ideal.Quotient.mk J (algebraMap A B a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.symm

lemma transition_nilpotent (I : Ideal A) (n : ℕ) (hn : 1 ≤ n) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self (by omega : n ≠ 0)) :
      A ⧸ I ^ n →+* A ⧸ I)) := by
  rw [Ideal.Quotient.factor_ker]
  refine ⟨n, ?_⟩
  simp [← Ideal.map_pow]

/-- The canonical power quotient map commutes with every transition quotient. -/
theorem powerMap_transition :
    Specs.AdvCommAlg.FormalLifting.Thickenings.transitionCompatibility.{u,v} := by
  intro A B _ _ _ J m n h
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl

/-- Formal étaleness identifies the corresponding ideal thickenings. -/
theorem powerMap_bijective :
    Specs.AdvCommAlg.FormalLifting.Thickenings.quotientIsomorphisms.{u,v} := by
  intro A B _ _ _ hEt J hsurj n hn
  let : Algebra.FormallyEtale A B := (formallyEtale_iff A B).mp hEt
  let I : Ideal A := baseIdeal (A := A) J
  let e : (A ⧸ I) ≃ₐ[A] (B ⧸ J) :=
    (Ideal.quotientEquivAlgOfEq A (baseIdeal_eq_kernel (A := A) J)).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := (Ideal.Quotient.mkₐ A J).comp (Algebra.ofId A B)) hsurj)
  let q : A ⧸ I ^ n →ₐ[A] A ⧸ I :=
    { Ideal.Quotient.factor (Ideal.pow_le_self (by omega : n ≠ 0)) with
      commutes' := fun _ => rfl }
  let g : B →ₐ[A] A ⧸ I ^ n := Algebra.FormallySmooth.liftOfSurjective
    (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A J)) q
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_self (by omega : n ≠ 0))) (transition_nilpotent I n hn)
  have hg (b : B) : q (g b) = e.symm (Ideal.Quotient.mk J b) :=
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ b
  have hgJ : J ≤ (I.map (Ideal.Quotient.mk (I ^ n))).comap g.toRingHom := by
    intro b hb
    change g b ∈ I.map (Ideal.Quotient.mk (I ^ n))
    rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_self (by omega : n ≠ 0))]
    change q (g b) = 0
    rw [hg, Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
  have hgJn : J ^ n ≤ RingHom.ker g.toRingHom := by
    calc
      J ^ n ≤ ((I.map (Ideal.Quotient.mk (I ^ n))).comap g.toRingHom) ^ n := pow_le_pow_left' hgJ n
      _ ≤ ((I.map (Ideal.Quotient.mk (I ^ n))) ^ n).comap g.toRingHom :=
        Ideal.le_comap_pow _ n
      _ = RingHom.ker g.toRingHom := by simp [← Ideal.map_pow, RingHom.ker]
  let inv : B ⧸ J ^ n →+* A ⧸ I ^ n := Ideal.Quotient.lift _ g.toRingHom hgJn
  have hleft : Function.LeftInverse inv (powerMap (A := A) J n) := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact g.commutes a
  let forward : A ⧸ I ^ n →ₐ[A] B ⧸ J ^ n :=
    { powerMap (A := A) J n with commutes' := fun _ => rfl }
  let r : B ⧸ J ^ n →ₐ[A] B ⧸ J :=
    { Ideal.Quotient.factor (Ideal.pow_le_self (by omega : n ≠ 0)) with
      commutes' := fun _ => rfl }
  have hr : r.comp (forward.comp g) = r.comp (Ideal.Quotient.mkₐ A (J ^ n)) := by
    ext b
    change r (forward (g b)) = Ideal.Quotient.mk J b
    have hcomm (x : A ⧸ I ^ n) : r (forward x) = e (q x) := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    rw [hcomm, hg, AlgEquiv.apply_symm_apply]
  have hrightg : forward.comp g = Ideal.Quotient.mkₐ A (J ^ n) :=
    Algebra.FormallyUnramified.lift_unique' r (transition_nilpotent J n hn) _ _ hr
  have hright : Function.RightInverse inv (powerMap (A := A) J n) := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact AlgHom.congr_fun hrightg b
  exact ⟨hleft.injective, hright.surjective⟩


/-- Injectivity of the power quotient identifies inverse images of all powers. -/
lemma comap_power_eq (hEt : FormallyEtale A B) (J : Ideal B)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp (algebraMap A B))) (n : ℕ) :
    (J ^ n).comap (algebraMap A B) = baseIdeal (A := A) J ^ n := by
  by_cases hn : n = 0
  · simp [hn]
  apply le_antisymm _ (Ideal.le_comap_pow _ n)
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (powerMap_bijective hEt J hsurj n (by omega)).injective
  change powerMap J n (Ideal.Quotient.mk _ a) = powerMap J n 0
  rw [map_zero]
  change Ideal.Quotient.mk (J ^ n) (algebraMap A B a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- The map on associated graded rings sends each homogeneous class to the
class of its structural image, also in degree zero. -/
theorem associatedGradedMap_homogeneous :
    Specs.AdvCommAlg.FormalLifting.Thickenings.associatedGradedHomogeneous.{u,v} := by
  intro A B _ _ _ J n a
  change Ideal.Quotient.mk _ (reesMap J (reesMonomial _ n a)) =
    Ideal.Quotient.mk _ (reesMonomial J n _)
  congr 1
  apply Subtype.ext
  change Polynomial.map (algebraMap A B) (Polynomial.monomial n a.1) =
    Polynomial.monomial n (algebraMap A B a.1)
  simp

/-- Multiplication in the Rees quotient is the usual multiplication of
homogeneous classes [a]ₙ[b]ₘ = [ab]ₙ₊ₘ. -/
lemma homogeneousClass_mul {R : Type*} [CommRing R] (I : Ideal R)
    (n m : ℕ) (a : ↥(I ^ n)) (b : ↥(I ^ m)) :
    homogeneousClass I n a * homogeneousClass I m b =
      homogeneousClass I (n + m) ⟨a.1 * b.1, by
        rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ := by
  change Ideal.Quotient.mk _ (reesMonomial I n a) *
    Ideal.Quotient.mk _ (reesMonomial I m b) = Ideal.Quotient.mk _ _
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  exact Polynomial.monomial_mul_monomial _ _ _ _

/-- A coefficient of a Rees polynomial, reduced in the usual graded piece. -/
def reesPieceCoefficient {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    reesAlgebra I →ₗ[R] GradedPiece I n where
  toFun p := Submodule.Quotient.mk ⟨p.1.coeff n, p.2 n⟩
  map_add' p q := by
    change Submodule.Quotient.mk _ = _ + _
    rw [← Submodule.Quotient.mk_add]
    congr 1
  map_smul' r p := by
    change Submodule.Quotient.mk _ = r • _
    rw [← Submodule.Quotient.mk_smul]
    congr 1

/-- The coefficient maps descend to the associated graded quotient. -/
def gradedCoefficient {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    AssociatedGraded I →ₗ[R] GradedPiece I n :=
  Submodule.liftQ ((reesIdeal I).restrictScalars R) (reesPieceCoefficient I n) (by
    intro p hp
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (mem_map_algebraMap_reesAlgebra_iff (I := I) p).mp hp n)

lemma gradedCoefficient_homogeneous {R : Type*} [CommRing R] (I : Ideal R)
    (n m : ℕ) (a : ↥(I ^ m)) :
    gradedCoefficient I n (homogeneousClass I m a) =
      if h : m = n then h ▸ (Submodule.Quotient.mk a : GradedPiece I m) else 0 := by
  classical
  by_cases h : m = n
  · subst n
    simp only [↓reduceDIte]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk a
    congr 1
    apply Subtype.ext
    simp [reesMonomial]
  · simp only [dite_eq_right h]
    change Submodule.Quotient.mk _ = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (Polynomial.monomial m a.1).coeff n ∈ I ^ (n + 1)
    simp [Polynomial.coeff_monomial, h]

lemma gradedCoefficient_pieceInclusion {R : Type*} [CommRing R] (I : Ideal R)
    (n m : ℕ) (a : GradedPiece I m) :
    gradedCoefficient I n (pieceInclusion I m a) =
      if h : m = n then h ▸ a else 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  exact gradedCoefficient_homogeneous I n m a

lemma gradedCoefficient_decomposition {R : Type*} [CommRing R] (I : Ideal R)
    (n : ℕ) (x : ⨁ m : ℕ, GradedPiece I m) :
    gradedCoefficient I n (gradedDecomposition I x) = x n := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of m a =>
    simp only [gradedDecomposition, DirectSum.toAddMonoid_of]
    change gradedCoefficient I n (pieceInclusion I m a) = _
    rw [gradedCoefficient_pieceInclusion]
    change (if h : m = n then h ▸ a else 0) = DFinsupp.single m a n
    exact DFinsupp.single_apply.symm
  | add x y hx hy => simp [hx, hy]

/-- The Rees quotient is exactly the direct sum of I^n/I^(n+1), including
its degree zero summand. -/
theorem gradedDecomposition_bijective :
    Specs.AdvCommAlg.FormalLifting.Thickenings.gradedDecompositionIsomorphism.{u} := by
  intro R _ I
  constructor
  · intro x y h
    apply DFinsupp.ext
    intro n
    simpa only [gradedCoefficient_decomposition] using congrArg (gradedCoefficient I n) h
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    classical
    rw [reesAlgebra.as_sum_support p, map_sum]
    apply AddSubgroup.sum_mem
      (AddMonoidHom.range (gradedDecomposition I))
    intro n hn
    refine ⟨DirectSum.of (fun n => GradedPiece I n) n
      (Submodule.Quotient.mk ⟨p.1.coeff n, p.2 n⟩), ?_⟩
    simp only [gradedDecomposition, DirectSum.toAddMonoid_of]
    rfl


lemma homogeneousClass_eq_of_sub_mem {R : Type*} [CommRing R] (I : Ideal R)
    (n : ℕ) (a b : ↥(I ^ n)) (h : a.1 - b.1 ∈ I ^ (n + 1)) :
    homogeneousClass I n a = homogeneousClass I n b := by
  have hq : (Submodule.Quotient.mk a : GradedPiece I n) = Submodule.Quotient.mk b :=
    (Submodule.Quotient.eq _).mpr h
  exact congrArg (pieceInclusion I n) hq

/-- The canonical map is an isomorphism of associated graded rings. -/
theorem associatedGradedMap_bijective :
    Specs.AdvCommAlg.FormalLifting.Thickenings.associatedGradedIsomorphism.{u,v} := by
  intro A B _ _ _ hEt J hsurj
  constructor
  · apply (injective_iff_map_eq_zero (associatedGradedMap (A := A) J)).mpr
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (reesIdeal J) (reesMap J p) = 0 at hx
    change Ideal.Quotient.mk _ p = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_map_algebraMap_reesAlgebra_iff] at hx ⊢
    intro n
    apply (comap_power_eq hEt J hsurj (n + 1)).le
    have hcoef := hx n
    change (Polynomial.map (algebraMap A B) p.1).coeff n ∈ J ^ (n + 1) at hcoef
    change algebraMap A B (p.1.coeff n) ∈ J ^ (n + 1)
    simpa only [Polynomial.coeff_map] using hcoef
  · have hhom (n : ℕ) (b : ↥(J ^ n)) :
        homogeneousClass J n b ∈ (associatedGradedMap (A := A) J).range := by
      obtain ⟨x, hx⟩ := (powerMap_bijective hEt J hsurj (n + 1) (by omega)).surjective
        (Ideal.Quotient.mk (J ^ (n + 1)) b.1)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hd : algebraMap A B a - b.1 ∈ J ^ (n + 1) := by
        apply Ideal.Quotient.eq.mp
        exact hx
      have ha : a ∈ baseIdeal (A := A) J ^ n := by
        apply (comap_power_eq hEt J hsurj n).le
        change algebraMap A B a ∈ J ^ n
        have hd' := Ideal.pow_le_pow_right (I := J) (Nat.le_succ n) hd
        simpa only [sub_add_cancel] using (J ^ n).add_mem hd' b.2
      refine ⟨homogeneousClass (baseIdeal (A := A) J) n ⟨a, ha⟩, ?_⟩
      rw [associatedGradedMap_homogeneous]
      exact homogeneousClass_eq_of_sub_mem J n _ b hd
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    classical
    rw [reesAlgebra.as_sum_support p, map_sum]
    apply Subring.sum_mem (associatedGradedMap (A := A) J).range
    intro n hn
    exact hhom n ⟨p.1.coeff n, p.2 n⟩

/-- The ring unit lies in the degree zero piece and is represented by 1. -/
theorem homogeneousClass_one :
    Specs.AdvCommAlg.FormalLifting.Thickenings.homogeneousUnit.{u} := by
  intro R _ I
  change Ideal.Quotient.mk (reesIdeal I) (reesMonomial I 0 ⟨1, by simp⟩) = 1
  have h : reesMonomial I 0 ⟨1, by simp⟩ = 1 := by
    apply Subtype.ext
    simp [reesMonomial]
  rw [h, map_one]

end AdvCommAlg.FormalLifting
