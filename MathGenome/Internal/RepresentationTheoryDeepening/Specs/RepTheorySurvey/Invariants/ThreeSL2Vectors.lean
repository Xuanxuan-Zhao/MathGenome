import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

namespace RepTheorySurvey.Invariants.Specs.ThreeSL2Vectors

noncomputable section

abbrev Triples (k : Type*) := Matrix (Fin 2) (Fin 3) k
abbrev Coordinates (k : Type*) [CommSemiring k] := MvPolynomial (Fin 2 × Fin 3) k
abbrev BracketPolynomials (k : Type*) [CommSemiring k] := MvPolynomial (Fin 3) k
abbrev SL₂ (k : Type*) [CommRing k] := Matrix.SpecialLinearGroup (Fin 2) k

variable {k : Type*} [Field k]

/-- The diagonal action is matrix multiplication on the three columns. -/
def act (g : SL₂ k) (v : Triples k) : Triples k := g.val * v

@[simp] theorem act_one (v : Triples k) : act (1 : SL₂ k) v = v := by
  simp [act, Matrix.SpecialLinearGroup.coe_one]

@[simp] theorem act_mul (g h : SL₂ k) (v : Triples k) :
    act (g * h) v = act g (act h v) := by
  simp [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

/-- Polynomial evaluation on a matrix of three columns. -/
abbrev evalAt (v : Triples k) : Coordinates k →+* k :=
  MvPolynomial.eval (fun i ↦ v i.1 i.2)

theorem evalAt_ext [Infinite k] {f h : Coordinates k}
    (he : ∀ v : Triples k, evalAt v f = evalAt v h) : f = h :=
  MvPolynomial.funext fun x ↦ he (Matrix.of fun i j ↦ x (i, j))

open MvPolynomial in
/-- The action on functions substitutes the coordinates of the inverse translate. -/
def pullback (g : SL₂ k) : Coordinates k →ₐ[k] Coordinates k :=
  aeval fun i ↦ ∑ j : Fin 2, C ((g⁻¹).val i.1 j) * X (j, i.2)

theorem eval_pullback (g : SL₂ k) (v : Triples k) (f : Coordinates k) :
    evalAt v (pullback g f) = evalAt (act g⁻¹ v) f := by
  let ev : Coordinates k →ₐ[k] k := MvPolynomial.aeval (fun i ↦ v i.1 i.2)
  change ev (pullback g f) =
    MvPolynomial.aeval (fun i : Fin 2 × Fin 3 ↦ act g⁻¹ v i.1 i.2) f
  rw [pullback, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun x : Fin 2 × Fin 3 → k ↦ MvPolynomial.aeval x f)
  funext i
  simp [ev, act, Matrix.mul_apply]

private theorem pullback_comp_inv [Infinite k] (g : SL₂ k) :
    (pullback g).comp (pullback g⁻¹) = AlgHom.id k (Coordinates k) := by
  apply AlgHom.ext
  intro f
  apply evalAt_ext
  intro v
  simp only [AlgHom.comp_apply, AlgHom.id_apply, eval_pullback, inv_inv,
    ← act_mul, mul_inv_cancel, act_one]

/-- The pullback left action of the actual determinant-one matrix group. -/
def action [Infinite k] : GroupAlgebraAction k (SL₂ k) (Coordinates k) where
  toFun g := AlgEquiv.ofAlgHom (pullback g) (pullback g⁻¹)
    (pullback_comp_inv g) (by simpa using pullback_comp_inv g⁻¹)
  map_one' := by
    apply AlgEquiv.ext
    intro f
    apply evalAt_ext
    intro v
    change evalAt v (pullback 1 f) = evalAt v f
    simp [eval_pullback]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro f
    apply evalAt_ext
    intro v
    change evalAt v (pullback (g * h) f) = evalAt v (pullback g (pullback h f))
    simp [eval_pullback]

/-- The coordinate polynomial for the determinant of columns i and j. -/
def minor (i j : Fin 3) : Coordinates k :=
  MvPolynomial.X (0, i) * MvPolynomial.X (1, j) -
    MvPolynomial.X (1, i) * MvPolynomial.X (0, j)

/-- The three brackets, in the order 01, 02, 12 with zero-based column indices. -/
def bracket : Fin 3 → Coordinates k := ![minor 0 1, minor 0 2, minor 1 2]

def bracketMap : BracketPolynomials k →ₐ[k] Coordinates k :=
  MvPolynomial.aeval bracket

def ActionType := ∀ {k : Type*} [Field k] [Infinite k],
  GroupAlgebraAction k (SL₂ k) (Coordinates k)

def BracketType := ∀ {k : Type*} [Field k], Fin 3 → Coordinates k

def BracketMapType := ∀ {k : Type*} [Field k],
  BracketPolynomials k →ₐ[k] Coordinates k

def BracketInjective : Prop :=
  ∀ (k : Type*) [Field k] [IsAlgClosed k],
    Function.Injective (bracketMap (k := k))

/-- The invariant ring is presented freely by the three specified brackets. -/
def BracketPresentation : Prop :=
  ∀ (k : Type*) [Field k] [IsAlgClosed k],
    ∃ e : BracketPolynomials k ≃ₐ[k] groupFixedSubalgebra (action (k := k)),
      ∀ q, (e q : Coordinates k) = bracketMap q

end

end RepTheorySurvey.Invariants.Specs.ThreeSL2Vectors
