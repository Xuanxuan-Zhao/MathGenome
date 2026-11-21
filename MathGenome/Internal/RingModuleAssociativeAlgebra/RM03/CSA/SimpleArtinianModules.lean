import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.SimpleArtinianModules
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Ring

universe u v w x

namespace RM03.CSA.SimpleArtinianModules

open RM03.Specs.CSA.SimpleArtinianModules
open scoped Matrix.Module

theorem matrixPresentation : matrixPresentationType.{u, v} := by
  intro k T _ _ _ _ _
  let : IsArtinianRing T := IsArtinianRing.of_finite k T
  obtain ⟨s, hs, E, _, _, _, he⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k T
  exact ⟨s, E, ‹_›, ‹_›, ‹_›, Nat.pos_of_ne_zero hs.out, he⟩

/-- The matrix with one prescribed column sends a vector to that column times
the corresponding entry of the vector. -/
private lemma oneColumn_smul {k T E : Type*} [Field k] [Ring T] [DivisionRing E]
    [Algebra k T] [Algebra k E] {s : ℕ}
    (e : T ≃ₐ[k] Matrix (Fin s) (Fin s) E) (j : Fin s) (z v : Fin s → E) (i : Fin s) :
    letI := columnModule e
    (e.symm (Matrix.of fun a b => if b = j then z a else 0) • v) i = z i * v j := by
  let := columnModule e
  change ((e (e.symm _) : Matrix (Fin s) (Fin s) E) • v) i = _
  rw [AlgEquiv.apply_symm_apply, Matrix.Module.smul_apply]
  simp only [Matrix.of_apply, smul_eq_mul, ite_mul, zero_mul, Fintype.sum_ite_eq']

theorem columnSimple : columnSimpleType.{u, v, w} := by
  intro k T E _ _ _ _ _ s e hs
  let : NeZero s := ⟨Nat.ne_of_gt hs⟩
  let := columnModule e
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨inferInstance, ?_⟩
  intro z hz v
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  refine ⟨e.symm (Matrix.of fun a b => if b = j then v a * (z j)⁻¹ else 0), ?_⟩
  funext i
  rw [LinearMap.toSpanSingleton_apply, oneColumn_smul, mul_assoc, inv_mul_cancel₀ hj, mul_one]

theorem columnEnd : columnEndType.{u, v, w} := by
  intro k T E _ _ _ _ _ s e hs
  let : NeZero s := ⟨Nat.ne_of_gt hs⟩
  let := columnModule e
  let := columnScalarTower e
  let f : Eᵐᵒᵖ →ₐ[k] Module.End T (Fin s → E) :=
    { toFun := fun a =>
        { toFun := fun z i => z i * a.unop
          map_add' := fun z v => funext fun i => add_mul (z i) (v i) a.unop
          map_smul' := by
            intro t z
            funext i
            change ((e t • z) i) * a.unop = (e t • (fun j => z j * a.unop)) i
            simp only [Matrix.Module.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc] }
      map_one' := LinearMap.ext fun z => funext fun i => mul_one (z i)
      map_mul' := fun a b => LinearMap.ext fun z => funext fun i => (mul_assoc _ _ _).symm
      map_zero' := LinearMap.ext fun z => funext fun i => mul_zero (z i)
      map_add' := fun a b => LinearMap.ext fun z => funext fun i => mul_add (z i) _ _
      commutes' := by
        intro r
        apply LinearMap.ext
        intro z
        funext i
        rw [Module.algebraMap_end_apply]
        change z i * ((algebraMap k Eᵐᵒᵖ) r).unop = r • z i
        rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op, Algebra.smul_def]
        exact (Algebra.commutes r (z i)).symm }
  let j : Fin s := 0
  let b : Fin s → E := Pi.single j 1
  have hf (a : Eᵐᵒᵖ) (z : Fin s → E) (i : Fin s) : f a z i = z i * a.unop := rfl
  have hb : b j = 1 := Pi.single_eq_same _ _
  have hbij : Function.Bijective f := by
    constructor
    · intro a a' h
      apply MulOpposite.unop_injective
      have h' := congrArg (fun g : Module.End T (Fin s → E) => g b j) h
      simpa only [hf, hb, one_mul] using h'
    · intro g
      refine ⟨MulOpposite.op (g b j), ?_⟩
      apply LinearMap.ext
      intro z
      funext i
      let t := e.symm (Matrix.of fun a c => if c = j then z a else 0)
      have ht (v : Fin s → E) (l : Fin s) : (t • v) l = z l * v j :=
        oneColumn_smul e j z v l
      have htb : t • b = z := funext fun l => by rw [ht, hb, mul_one]
      calc
        f (MulOpposite.op (g b j)) z i = z i * g b j := rfl
        _ = (t • g b) i := (ht _ _).symm
        _ = g (t • b) i := congrFun (g.map_smul t b).symm i
        _ = g z i := by rw [htb]
  exact ⟨AlgEquiv.ofBijective f hbij, fun _ _ _ => rfl⟩

theorem simpleModuleEquivColumn : simpleModuleEquivColumnType.{u, v, w, x} := by
  intro k T E _ _ _ _ _ _ _ s e hs S _ _ _
  let := columnModule e
  let : IsSimpleModule T (Fin s → E) := columnSimple k T E s e hs
  let : IsArtinianRing T := IsArtinianRing.of_finite k T
  obtain ⟨I, ⟨f⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule T S
  obtain ⟨J, ⟨g⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule T (Fin s → E)
  let : IsSimpleModule T I := IsSimpleModule.congr f.symm
  let : IsSimpleModule T J := IsSimpleModule.congr g.symm
  obtain ⟨h⟩ := IsSimpleRing.isIsotypic T T J I
  exact ⟨f.trans (h.trans g.symm)⟩

theorem moduleDecomposition : moduleDecompositionType.{u, v, w, x} := by
  intro k T E _ _ _ _ _ _ _ _ s e hs V _ _ _ _ _ _
  let := columnModule e
  let := columnScalarTower e
  let : IsArtinianRing T := IsArtinianRing.of_finite k T
  let : Module.Finite T V := Module.Finite.of_restrictScalars_finite k T V
  have h : IsIsotypicOfType T V (Fin s → E) := fun S _ =>
    simpleModuleEquivColumn k T E s e hs S
  obtain ⟨m, ⟨g⟩⟩ := h.linearEquiv_fun
  have hm : 0 < m := by
    by_contra! h
    have : IsEmpty (Fin m) := by simp [Nat.eq_zero_of_le_zero h]
    exact not_subsingleton V (g.toEquiv.subsingleton)
  obtain ⟨b, _⟩ := columnEnd k T E s e hs
  let f : Module.End T V ≃ₐ[k] Matrix (Fin m) (Fin m) Eᵐᵒᵖ :=
    (g.conjAlgEquiv k).trans
      ((endVecAlgEquivMatrixEnd (Fin m) k T (Fin s → E)).trans b.symm.mapMatrix)
  have hv : Module.finrank k V = s * m * Module.finrank k E := by
    rw [(g.restrictScalars k).finrank_eq]
    rw [Module.finrank_pi_fintype (R := k)]
    simp [Module.finrank_pi_fintype, Nat.mul_comm s m, Nat.mul_assoc]
  have hd : 0 < Module.finrank k E := Module.finrank_pos
  refine ⟨m, hm, ⟨g⟩, hv, ?_, ⟨f⟩, ?_, ?_⟩
  · intro n hn
    exact Nat.mul_left_cancel hs (Nat.mul_right_cancel hd (hn.symm.trans hv))
  · rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp [pow_two]
  · rw [f.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp [pow_two, ← (MulOpposite.opLinearEquiv k : E ≃ₗ[k] Eᵐᵒᵖ).finrank_eq]

theorem endSimpleAndDimension : endSimpleAndDimensionType.{u, v, w} := by
  intro k T _ _ _ _ _ V _ _ _ _ _ _
  obtain ⟨s, E, _, _, _, hs, ⟨e⟩⟩ := matrixPresentation k T
  obtain ⟨m, hm, _, hv, _, ⟨f⟩, ht, he⟩ := moduleDecomposition k T E s e hs V
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have : Module.Finite k Eᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv k)
  refine ⟨Module.Finite.equiv f.symm.toLinearEquiv,
    IsSimpleRing.of_ringEquiv f.symm.toRingEquiv inferInstance, ?_⟩
  rw [ht, he, hv]
  ring

theorem equivOfFinrankEq : equivOfFinrankEqType.{u, v, w, x} := by
  intro k T _ _ _ _ _ V _ _ _ _ _ _ W _ _ _ _ _ _ h
  obtain ⟨s, E, _, _, _, hs, ⟨e⟩⟩ := matrixPresentation k T
  obtain ⟨m, _, ⟨f⟩, _, hu, _, _, _⟩ := moduleDecomposition k T E s e hs V
  obtain ⟨n, _, ⟨g⟩, hw, _, _, _, _⟩ := moduleDecomposition k T E s e hs W
  have hn := hu n (h.trans hw)
  subst n
  exact ⟨f.trans g.symm⟩

end RM03.CSA.SimpleArtinianModules
