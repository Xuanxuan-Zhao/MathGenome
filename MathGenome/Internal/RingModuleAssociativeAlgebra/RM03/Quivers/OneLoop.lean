import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.OneLoop
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.BoundModuleEquivalence
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.AdjoinRoot

/-! The square-zero loop example. -/

open Polynomial
open scoped Polynomial

namespace RM03.OneLoop

open OneLoopSpec
open Quivers.AlgebraRepresentations
open QuiverBoundModuleEquivalenceSpec (quotientIdeal)

universe u v w

private theorem path_length (n : ℕ) : (path n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (path n).length + 1 = n + 1
    rw [ih]

private theorem walk_of_length {i : Unit} (p : Quiver.Path () i) :
    HEq (walk p.length) p := by
  induction p with
  | nil => rfl
  | @cons i j p a ih =>
    cases i
    cases j
    change Unit at a
    cases a
    exact heq_of_eq (congrArg (fun q => q.cons loop) (eq_of_heq ih))

private theorem path_of_length (p : Path Unit) : path p.length = p := by
  rcases p with ⟨⟨⟩, ⟨⟩, p⟩
  exact congrArg Path.ofPath (eq_of_heq (walk_of_length p))

theorem pathEnumeration : PathEnumeration :=
  ⟨rfl, rfl, path_length, path_of_length⟩

private def pathEquiv : ℕ ≃ Path Unit where
  toFun := path
  invFun := Path.length
  left_inv := path_length
  right_inv := path_of_length

noncomputable section

variable (k : Type u) [Field k]

local notation "a₀" => PathAlgebra.arrow k loop

private theorem loop_pow (n : ℕ) : a₀ ^ n = PathAlgebra.ofPath k (path n) := by
  induction n with
  | zero =>
    change (1 : A k) = PathAlgebra.vertex k ()
    rw [← PathAlgebra.sum_vertices]
    simp
  | succ n ih =>
    rw [pow_succ', ih, PathAlgebra.arrow_eq_ofPath, PathAlgebra.ofPath_mul_ofPath, dite_eq_left rfl]
    rfl

private def polynomialEquiv : k[X] ≃ₐ[k] A k := by
  let e := (basisMonomials k).equiv (PathAlgebra.basis k Unit) pathEquiv
  have h : (aeval a₀).toLinearMap = e.toLinearMap := by
    apply (basisMonomials k).ext
    intro n
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, PathAlgebra.basis_apply]
    change aeval a₀ (monomial n 1) = PathAlgebra.ofPath k (path n)
    rw [monomial_one_right_eq_X_pow, aeval_X_pow, loop_pow]
  exact AlgEquiv.ofBijective (aeval a₀) (by
    change Function.Bijective ((aeval a₀).toLinearMap)
    rw [h]
    exact e.bijective)

private theorem polynomialEquiv_X_pow (n : ℕ) :
    polynomialEquiv k (X ^ n) = PathAlgebra.ofPath k (path n) := by
  change aeval a₀ (X ^ n) = _
  rw [aeval_X_pow, loop_pow]

private theorem polynomialEquiv_X : polynomialEquiv k X = a₀ := by
  change aeval a₀ X = a₀
  exact aeval_X a₀

private theorem generatedIdeal_eq_span :
    QuiverRelation.generatedIdeal (relations k) = TwoSidedIdeal.span {a₀ ^ 2} := by
  have he : QuiverRelation.toElement '' relations k = {a₀ ^ 2} := by
    rw [relations, Set.image_singleton]
    have hs : QuiverRelation.toElement (squareRelation k) = a₀ ^ 2 := by
      rw [loop_pow]
      change QuiverRelation.toPathAlgebra () () (Finsupp.single (walk 2) 1) = _
      simp only [QuiverRelation.toPathAlgebra, Finsupp.linearCombination_single, one_smul]
      rfl
    rw [hs]
  change TwoSidedIdeal.span (QuiverRelation.toElement '' relations k) = _
  rw [he]

private theorem arrowIdeal_eq_span :
    PathAlgebra.arrowIdeal k Unit = TwoSidedIdeal.span {a₀} := by
  change TwoSidedIdeal.span (Set.range fun a : Arrow Unit => PathAlgebra.arrow k a.2.2) = _
  suffices Set.range (fun a : Arrow Unit => PathAlgebra.arrow k a.2.2) = {a₀} by rw [this]
  apply Set.Subset.antisymm
  · rintro y ⟨⟨⟨⟩, ⟨⟩, a⟩, rfl⟩
    change Unit at a
    cases a
    rfl
  · rintro y (rfl : y = a₀)
    exact ⟨⟨(), (), loop⟩, rfl⟩

private theorem span_isTwoSided (s : Set (A k)) : (Ideal.span s).IsTwoSided := by
  refine ⟨fun {x} y hx => ?_⟩
  have hxy : x * y = y * x := by
    obtain ⟨p, rfl⟩ := (polynomialEquiv k).surjective x
    obtain ⟨q, rfl⟩ := (polynomialEquiv k).surjective y
    rw [← map_mul, mul_comm p q, map_mul]
  rw [hxy]
  exact (Ideal.span s).mul_mem_left y hx

private theorem asIdeal_span (s : Set (A k)) :
    (TwoSidedIdeal.span s).asIdeal = Ideal.span s := by
  let := span_isTwoSided k s
  apply le_antisymm
  · rw [← Ideal.asIdeal_toTwoSided (Ideal.span s)]
    apply TwoSidedIdeal.asIdeal.monotone
    exact TwoSidedIdeal.span_le.mpr fun x hx => Ideal.mem_toTwoSided.mpr (Ideal.subset_span hx)
  · exact Ideal.span_le.mpr fun x hx => TwoSidedIdeal.mem_asIdeal.mpr
      (TwoSidedIdeal.subset_span hx)

private theorem generatedIdeal_eq_square :
    QuiverRelation.generatedIdeal (relations k) =
      PathAlgebra.idealPower (PathAlgebra.arrowIdeal k Unit) 2 := by
  have h : (QuiverRelation.generatedIdeal (relations k)).asIdeal =
      (PathAlgebra.idealPower (PathAlgebra.arrowIdeal k Unit) 2).asIdeal := by
    rw [PathAlgebra.idealPower_asIdeal, generatedIdeal_eq_span, arrowIdeal_eq_span,
      asIdeal_span, asIdeal_span]
    exact (@Ideal.span_singleton_pow _ _ a₀ (span_isTwoSided k {a₀}) 2).symm
  apply SetLike.ext
  intro y
  change y ∈ (QuiverRelation.generatedIdeal (relations k)).asIdeal ↔
    y ∈ (PathAlgebra.idealPower (PathAlgebra.arrowIdeal k Unit) 2).asIdeal
  rw [h]

theorem idealEqualsSquare : IdealEqualsSquare := by
  intro k _
  change QuiverRelation.generatedIdeal (relations k) =
      PathAlgebra.idealPower (PathAlgebra.arrowIdeal k Unit) 2 ∧
    PathAlgebra.IsAdmissible (QuiverRelation.generatedIdeal (relations k))
  have h := generatedIdeal_eq_square k
  exact ⟨h, ⟨2, by decide, h.ge, h.le⟩⟩

private theorem quotientIdeal_eq_map :
    quotientIdeal (relations k) = (xSquared k).map (polynomialEquiv k).toRingHom := by
  change (QuiverRelation.generatedIdeal (relations k)).asIdeal = _
  rw [generatedIdeal_eq_span, asIdeal_span, xSquared, Ideal.map_span, Set.image_singleton]
  rw [map_pow]
  change Ideal.span {a₀ ^ 2} = Ideal.span {(polynomialEquiv k X) ^ 2}
  rw [polynomialEquiv_X]

local notation "B" => A k ⧸ quotientIdeal (relations k)
local notation "P" => k[X] ⧸ xSquared k
local notation "D" => AdjoinRoot ((X : k[X]) ^ 2)
local notation "x" => Ideal.Quotient.mk (quotientIdeal (relations k)) a₀

private def quotientEquiv : P ≃ₐ[k] B :=
  Ideal.quotientEquivAlg _ _ (polynomialEquiv k) (quotientIdeal_eq_map k)

private theorem quotientEquiv_mk (p : k[X]) :
    quotientEquiv k (Ideal.Quotient.mk (xSquared k) p) =
      Ideal.Quotient.mk (quotientIdeal (relations k)) (polynomialEquiv k p) :=
  rfl

private theorem quotientEquiv_X :
    quotientEquiv k (Ideal.Quotient.mk (xSquared k) X) = x := by
  rw [quotientEquiv_mk, polynomialEquiv_X]

private def powerBasis : Module.Basis (Fin 2) k D :=
  (AdjoinRoot.powerBasis' (g := (X : k[X]) ^ 2) (monic_X_pow 2)).basis.reindex
    (finCongr (by simp [AdjoinRoot.powerBasis'_dim]))

private def quotientBasis : Module.Basis (Fin 2) k B :=
  (powerBasis k).map (quotientEquiv k).toLinearEquiv

private theorem powerBasis_zero : powerBasis k 0 = 1 := by
  rw [powerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  exact pow_zero (AdjoinRoot.root ((X : k[X]) ^ 2))

private theorem powerBasis_one : powerBasis k 1 = AdjoinRoot.root ((X : k[X]) ^ 2) := by
  rw [powerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  exact pow_one (AdjoinRoot.root ((X : k[X]) ^ 2))

private theorem quotientBasis_zero : quotientBasis k 0 = 1 := by
  change quotientEquiv k (powerBasis k 0) = 1
  rw [powerBasis_zero]
  exact map_one (quotientEquiv k)

private theorem quotientBasis_one : quotientBasis k 1 = x := by
  change quotientEquiv k (powerBasis k 1) = x
  rw [powerBasis_one]
  exact quotientEquiv_X k

private theorem quotient_normal_form (y : B) :
    ∃ c d : k, y = algebraMap k B c + algebraMap k B d * x := by
  let b := quotientBasis k
  refine ⟨b.repr y 0, b.repr y 1, ?_⟩
  have h := b.sum_repr y
  rw [Fin.sum_univ_two] at h
  change b.repr y 0 • quotientBasis k 0 + b.repr y 1 • quotientBasis k 1 = y at h
  simpa only [quotientBasis_zero, quotientBasis_one, Algebra.smul_def, mul_one] using h.symm

private theorem quotient_loop_sq : (x : B) ^ 2 = 0 := by
  rw [← map_pow]
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  change a₀ ^ 2 ∈ (QuiverRelation.generatedIdeal (relations k)).asIdeal
  rw [generatedIdeal_eq_span, asIdeal_span]
  exact Ideal.mem_span_singleton_self _

section Modules

variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]

private def polynomialRepresentation (T : {T : Module.End k V // T ^ 2 = 0}) :
    P →ₐ[k] Module.End k V where
  __ := Ideal.Quotient.lift (xSquared k) (aeval T.val).toRingHom (by
    have h : xSquared k ≤ RingHom.ker (aeval T.val).toRingHom := by
      apply (Ideal.span_singleton_le_iff_mem _).2
      change aeval T.val (X ^ 2) = 0
      rw [aeval_X_pow, T.property]
    exact fun p hp => h hp)
  commutes' c := (aeval T.val).commutes c

private def representationOf (T : {T : Module.End k V // T ^ 2 = 0}) :
    B →ₐ[k] Module.End k V :=
  (polynomialRepresentation k T).comp (quotientEquiv k).symm.toAlgHom

private theorem representationOf_loop (T : {T : Module.End k V // T ^ 2 = 0}) :
    representationOf k T x = T.val := by
  change polynomialRepresentation k T ((quotientEquiv k).symm x) = T.val
  rw [← quotientEquiv_X k, AlgEquiv.symm_apply_apply]
  exact aeval_X T.val

private theorem representation_ext {ρ σ : B →ₐ[k] Module.End k V}
    (h : ρ x = σ x) : ρ = σ := by
  ext y : 1
  obtain ⟨c, d, rfl⟩ := quotient_normal_form k y
  simp only [map_add, map_mul, AlgHom.commutes, h]

private def operatorEquiv : (B →ₐ[k] Module.End k V) ≃ {T : Module.End k V // T ^ 2 = 0} where
  toFun ρ := ⟨ρ x, by rw [← map_pow, quotient_loop_sq, map_zero]⟩
  invFun := representationOf k
  left_inv ρ := representation_ext k (representationOf_loop k _)
  right_inv T := Subtype.ext (representationOf_loop k T)

private def moduleEquiv : CompatibleModule k B V ≃ {T : Module.End k V // T ^ 2 = 0} :=
  representationEquiv.symm.trans (operatorEquiv k)

private theorem moduleEquiv_apply (M : CompatibleModule k B V) (z : V) :
    (moduleEquiv k M).val z = M.act x z :=
  rfl

private theorem act_normal_form (M : CompatibleModule k B V) (c d : k) (z : V) :
    M.act (algebraMap k B c + algebraMap k B d * x) z = c • z + d • M.act x z := by
  change M.toRepresentation (algebraMap k B c + algebraMap k B d * x) z = _
  simp only [map_add, map_mul, AlgHom.commutes, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, CompatibleModule.toRepresentation_apply]

private theorem moduleDescription : ModuleDescription.{u, u, v, w} k x := by
  constructor
  · intro V _ _
    refine ⟨moduleEquiv k, moduleEquiv_apply k, ?_⟩
    intro T c d z
    rw [act_normal_form, ← moduleEquiv_apply k, Equiv.apply_symm_apply]
  · intro V W _ _ _ _ M N f
    rw [moduleLinear_iff]
    refine ⟨fun h => h x, fun h y z => ?_⟩
    obtain ⟨c, d, rfl⟩ := quotient_normal_form k y
    simp only [act_normal_form, map_add, map_smul, h]

end Modules

theorem construction : Construction.{u, v, w} := by
  intro k _
  refine ⟨inferInstance, inferInstance, ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩, ?_⟩
  exact ⟨polynomialEquiv k, quotientEquiv k, quotientBasis k, polynomialEquiv_X_pow k,
    quotientEquiv_mk k, quotientBasis_zero k, quotientBasis_one k, moduleDescription k⟩

end

end RM03.OneLoop
