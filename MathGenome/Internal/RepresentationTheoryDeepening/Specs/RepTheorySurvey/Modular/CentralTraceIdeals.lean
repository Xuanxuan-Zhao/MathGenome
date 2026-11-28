import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.GroupAlgebraCenter
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.RelativeTrace
import Mathlib.Algebra.CharP.Defs
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.Ideal.Basic

noncomputable section

open scoped MonoidAlgebra
open P103.Ch08.ClassSumIntegrality (classSum)

namespace RepTheorySurvey.Modular.CentralTraceIdealsSpec

open RelativeTraceSpec

universe u v

variable (k : Type u) [Field k] {G : Type v} [Group G]

/-- The stabilizer of `x` for conjugation by `P`, as a subgroup of `G`. -/
abbrev orbitStabilizer (P : Subgroup G) (x : G) :=
  P ⊓ Subgroup.centralizer {x}

/-- The basis vector at `x` is fixed by any subgroup of its centralizer. -/
def fixedSingle {Q : Subgroup G} (x : G) (hQ : Q ≤ Subgroup.centralizer {x}) :
    fixedSubalgebra k Q :=
  ⟨MonoidAlgebra.single x 1, fun g => by
    rw [show conjugation k (g : G) (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single ((g : G) * x * (g : G)⁻¹) 1 from
        MonoidAlgebra.domCongr_single (R := k) (A := k) (MulAut.conj (g : G)) x 1]
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hQ g.property)), mul_inv_cancel_right]⟩

theorem coeff_conjugation (g y : G) (a : k[G]) :
    (conjugation k g a).coeff y = a.coeff (g⁻¹ * y * g) := by
  change (MonoidAlgebra.domCongr k k (MulAut.conj g) a).coeff y = _
  rw [MonoidAlgebra.coeff_domCongr, MulAut.conj_symm_apply]

theorem conjugation_center (g : G) (z : Subalgebra.center k k[G]) :
    conjugation k g (z : k[G]) = z := by
  ext y
  rw [coeff_conjugation]
  have h := congrArg (fun a : k[G] => a.coeff (y * g))
    (Subalgebra.mem_center_iff.mp z.property (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using h

variable [Finite G]

/-- The orbit sum is the relative trace of the basis vector from its stabilizer. -/
def orbitSum (P : Subgroup G) (x : G) : fixedSubalgebra k P :=
  relativeTrace k (show orbitStabilizer P x ≤ P from inf_le_left)
    (fixedSingle k x inf_le_right)

/-- The image of the relative trace inside the center, as an ideal. -/
def traceIdeal (P : Subgroup G) : Ideal (Subalgebra.center k k[G]) where
  carrier := {z | ∃ a : fixedSubalgebra k P,
    (relativeTrace k (show P ≤ ⊤ from le_top) a : k[G]) = (z : k[G])}
  zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
  add_mem' := by
    rintro z w ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [map_add]
    exact congrArg₂ (· + ·) ha hb
  smul_mem' := by
    rintro z w ⟨a, ha⟩
    let zP : fixedSubalgebra k P := ⟨z, fun g => conjugation_center k (g : G) z⟩
    refine ⟨zP * a, ?_⟩
    change (relativeTrace k (show P ≤ ⊤ from le_top) (zP * a) : k[G]) =
      (z : k[G]) * (w : k[G])
    rw [← ha, relativeTrace_apply, relativeTrace_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    change conjugation k (c.out : G) ((z : k[G]) * (a : k[G])) =
      (z : k[G]) * conjugation k (c.out : G) (a : k[G])
    rw [map_mul, conjugation_center]

set_option linter.checkUnivs false in
def traceIdealType :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G],
    Subgroup G → Ideal (Subalgebra.center k k[G])

/-- Some Sylow subgroup of the centralizer is carried into `P` by conjugation in `G`. -/
def sylowConjugateInto (p : ℕ) (P : Subgroup G) (x : G) : Prop :=
  ∃ (D : Sylow p (Subgroup.centralizer ({x} : Set G))) (g : G),
    ((D : Subgroup _).map (Subgroup.centralizer ({x} : Set G)).subtype).map
      (MulAut.conj g).toMonoidHom ≤ P

/-- The conjugacy classes that satisfy the centralizer-Sylow criterion. -/
def eligibleClass (p : ℕ) (P : Subgroup G) (C : ConjClasses G) : Prop :=
  ∃ x, ConjClasses.mk x = C ∧ sylowConjugateInto p P x

def traceCentralType : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G]
    (P : Subgroup G) (a : fixedSubalgebra k P),
    (relativeTrace k (show P ≤ ⊤ from le_top) a : k[G]) ∈ Subalgebra.center k k[G]

def traceOrbitSumType : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Fintype G]
    (P : Subgroup G) (x : G),
    (relativeTrace k (show P ≤ ⊤ from le_top) (orbitSum k P x) : k[G]) =
      ((P.relIndex (Subgroup.centralizer {x}) : ℕ) : k) • classSum k (ConjClasses.mk x)

def orbitIndexNonzeroType : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (P : Subgroup G) (_hP : IsPGroup p P) (x : G),
    ((P.relIndex (Subgroup.centralizer {x}) : ℕ) : k) ≠ 0 ↔
      ∃ D : Sylow p (Subgroup.centralizer ({x} : Set G)),
        (D : Subgroup _) = P.subgroupOf (Subgroup.centralizer {x})

def classSumMemTraceIdealType : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Fintype G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (P : Subgroup G) (_hP : IsPGroup p P) (x : G),
    (∃ z : Subalgebra.center k k[G], z ∈ traceIdeal k P ∧
      (z : k[G]) = classSum k (ConjClasses.mk x)) ↔ sylowConjugateInto p P x

def traceIdealBasisType : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [Group G] [Fintype G]
    (p : ℕ) [Fact p.Prime] [CharP k p] (P : Subgroup G) (_hP : IsPGroup p P),
    ∃ b : Module.Basis {C : ConjClasses G // eligibleClass p P C} k (traceIdeal k P),
      ∀ C, (((b C).val) : k[G]) = classSum k C.val

end RepTheorySurvey.Modular.CentralTraceIdealsSpec
