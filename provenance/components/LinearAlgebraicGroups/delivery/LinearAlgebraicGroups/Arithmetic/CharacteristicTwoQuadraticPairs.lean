import Specs.LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs
import LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
import LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import LinearAlgebraicGroups.Descent.RelativeRank
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.AlgebraicGeometry.EffectiveEpi
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.AbsoluteIsomorphism

import LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
open scoped TensorProduct RatFunc LaurentSeries Polynomial MatrixGroups Topology
open MulOpposite ValuativeRel
open scoped ValuativeRel
open LinearAlgebraicGroups.Specs.Arithmetic.CharacteristicTwoQuadraticPairs
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (antiValue)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels
  (AntiAutomorphism HermitianPairing quaternionConjugate)
open LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs

noncomputable section
open private split_quaternion_conjugate
  from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels



section SquareDegree

private theorem square_degree_of_generator {F : Type u} [Field F] [CharP F 2]
    (t : F) (ht : ∀ x : F, x ^ 2 ≠ t)
    (hgen : IntermediateField.adjoin (SquareField F) {t} = ⊤) :
    Module.finrank (SquareField F) F = 2 := by
  let S := SquareField F
  let c : S := (frobenius F 2).rangeRestrictField t
  let p : Polynomial S := Polynomial.X ^ 2 - Polynomial.C c
  have hir : Irreducible p := X_pow_sub_C_irreducible_of_prime Nat.prime_two (by
    intro a ha
    have h : (a : F) ^ 2 = t ^ 2 := congrArg Subtype.val ha
    have he : (a : F) = t := (frobenius F 2).injective h
    obtain ⟨b, hb⟩ := a.property
    exact ht b (hb.trans he))
  have hroot : Polynomial.aeval t p = 0 := by
    simp only [p, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_self _
  have hmin : minpoly S t = p :=
    (minpoly.eq_of_irreducible_of_monic hir hroot
      (Polynomial.monic_X_pow_sub_C c (by decide : 2 ≠ 0))).symm
  have hint : IsIntegral S t := ⟨p, Polynomial.monic_X_pow_sub_C c (by decide : 2 ≠ 0), hroot⟩
  have hdeg : p.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  rw [← IntermediateField.finrank_top', ← hgen,
    IntermediateField.adjoin.finrank hint, hmin, hdeg]

private theorem ratFunc_square_degree (k : Type v) [Field k] [Finite k] [CharP k 2] :
    Module.finrank (SquareField k⟮X⟯) k⟮X⟯ = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S := SquareField k⟮X⟯
  let t : k⟮X⟯ := RatFunc.X
  apply square_degree_of_generator t
  · intro x hx
    have hx' : x ≠ 0 := by
      intro h
      exact RatFunc.X_ne_zero (by simpa [t, h] using hx.symm)
    have hdeg := congrArg RatFunc.intDegree hx
    rw [pow_two, RatFunc.intDegree_mul hx' hx', RatFunc.intDegree_X] at hdeg
    omega
  · let J := IntermediateField.adjoin S {t}
    apply top_unique
    intro a _
    change a ∈ J
    have ht : t ∈ J := IntermediateField.subset_adjoin _ _ rfl
    have hC (c : k) : algebraMap k k⟮X⟯ c ∈ J := by
      obtain ⟨b, hb⟩ := surjective_frobenius k 2 c
      exact J.algebraMap_mem ⟨_, algebraMap k k⟮X⟯ b, by
        change (algebraMap k k⟮X⟯ b) ^ 2 = algebraMap k k⟮X⟯ c
        rw [← map_pow]
        exact congrArg (algebraMap k k⟮X⟯) hb⟩
    have hpoly (p : k[X]) : algebraMap k[X] k⟮X⟯ p ∈ J := by
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add]; exact J.add_mem hp hq
      | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
        exact J.mul_mem (hC c) (J.pow_mem ht n)
    induction a using RatFunc.induction_on with
    | _ p q _ => exact J.div_mem (hpoly p) (hpoly q)

private theorem square_degree_finite_extension {R : Type v} {F : Type u}
    [Field R] [Field F] [CharP R 2] [CharP F 2]
    [Algebra R F] [FiniteDimensional R F] :
    Module.finrank (SquareField F) F = Module.finrank (SquareField R) R := by
  let S := SquareField R
  let T := SquareField F
  let f := algebraMap R F
  let g : S →+* T := (f.comp S.subtype).codRestrict T (by
    rintro ⟨_, x, rfl⟩
    exact ⟨f x, by change f x ^ 2 = f (x ^ 2); rw [map_pow]⟩)
  let : Algebra S T := g.toAlgebra
  let : IsScalarTower S T F := ⟨fun a x y => by
    change f (a : R) * (x : F) * y = (a : R) • ((x : F) * y)
    rw [Algebra.smul_def]
    exact mul_assoc _ _ _⟩
  let eR : R ≃+* S := (frobenius R 2).rangeRestrictFieldEquiv
  let eF : F ≃+* T := (frobenius F 2).rangeRestrictFieldEquiv
  have hn : Module.finrank R F = Module.finrank S T :=
    Algebra.finrank_eq_of_equiv_equiv eR eF (by
      ext a
      change f (a ^ 2) = (f a) ^ 2
      exact f.map_pow a 2)
  have hR := Module.finrank_mul_finrank S R F
  have hT := Module.finrank_mul_finrank S T F
  rw [← hn] at hT
  apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := R) (M := F))
  simpa only [mul_comm (Module.finrank R F)] using hT.trans hR.symm

private theorem global_square_degree : GlobalSquareDegree.{u,v} := by
  intro F _ _ k _ _ _ _
  let : CharP k⟮X⟯ 2 := (algebraMap k⟮X⟯ F).charP (algebraMap k⟮X⟯ F).injective 2
  let : CharP k 2 := (algebraMap k k⟮X⟯).charP (algebraMap k k⟮X⟯).injective 2
  exact square_degree_finite_extension.trans (ratFunc_square_degree k)

private theorem laurent_coeff_square {k : Type u} [Field k] [CharP k 2]
    (x : k⸨X⸩) (n : ℤ) :
    (x ^ 2).coeff n = if n % 2 = 0 then x.coeff (n / 2) ^ 2 else 0 := by
  classical
  rw [pow_two, HahnSeries.coeff_mul]
  let s := Finset.antidiagonal x.isPWO_support x.isPWO_support n
  let f := fun p : ℤ × ℤ => x.coeff p.1 * x.coeff p.2
  let d := (n / 2, n / 2)
  have hoff : ∑ p ∈ s.erase d, f p = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ (fun p _ => Prod.swap_swap p)
    · intro p _
      change x.coeff p.1 * x.coeff p.2 + x.coeff p.2 * x.coeff p.1 = 0
      have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
      rw [mul_comm (x.coeff p.2), ← two_mul, htwo, zero_mul]
    · intro p hp _ he
      have hne := (Finset.mem_erase.mp hp).1
      have hs := (Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hp).2).2.2
      have hp' : p.2 = p.1 := congrArg Prod.fst he
      apply hne
      ext <;> dsimp [d] <;> omega
    · intro p hp
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
      refine Finset.mem_erase.mpr ⟨?_, Finset.swap_mem_antidiagonal.mpr hmem⟩
      intro he
      exact hne (by simpa [d] using congrArg Prod.swap he)
  change ∑ p ∈ s, f p = _
  by_cases hd : d ∈ s
  · have hs := (Finset.mem_antidiagonal.mp hd).2.2
    rw [← Finset.sum_erase_add _ _ hd, hoff, zero_add, ite_eq_left (by dsimp [d] at hs; omega)]
    exact (pow_two _).symm
  · rw [← Finset.erase_eq_of_notMem hd, hoff]
    split_ifs with h
    · have hz : x.coeff (n / 2) = 0 := by
        by_contra hn
        apply hd
        exact Finset.mem_antidiagonal.mpr ⟨hn, hn, by dsimp [d]; omega⟩
      simp [hz]
    · rfl

private theorem laurent_square_degree (k : Type u) [Field k] [Finite k] [CharP k 2]
    [CharP k⸨X⸩ 2] : Module.finrank (SquareField k⸨X⸩) k⸨X⸩ = 2 := by
  classical
  let t : k⸨X⸩ := HahnSeries.single 1 1
  apply square_degree_of_generator t
  · intro x hx
    have he := congrArg (fun y : k⸨X⸩ => y.coeff 1) hx
    simp [laurent_coeff_square, t] at he
  · let J := IntermediateField.adjoin (SquareField k⸨X⸩) {t}
    have ht : t ∈ J := IntermediateField.subset_adjoin _ _ rfl
    apply top_unique
    intro x _
    change x ∈ J
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let sq : k ≃+* k := frobeniusEquiv k 2
    let root (r : ℤ) : k⸨X⸩ :=
      HahnSeries.ofSuppBddBelow (fun n => sq.symm (x.coeff (2 * n + r))) (by
        refine ⟨(x.order - r) / 2, fun n hn => ?_⟩
        have hx : x.coeff (2 * n + r) ≠ 0 := by
          intro he
          exact hn (by simp [he])
        have hh := HahnSeries.order_le_of_coeff_ne_zero hx
        change (x.order - r) / 2 ≤ n
        omega)
    let a := root 0
    let b := root 1
    have hroot (r n : ℤ) : (root r).coeff n ^ 2 = x.coeff (2 * n + r) :=
      sq.apply_symm_apply _
    have hdecomp : x = a ^ 2 + b ^ 2 * t := by
      ext n
      rw [HahnSeries.coeff_add, laurent_coeff_square]
      change x.coeff n =
        (if n % 2 = 0 then a.coeff (n / 2) ^ 2 else 0) +
          (b ^ 2 * HahnSeries.single 1 1).coeff n
      rw [HahnSeries.coeff_mul_single, mul_one, laurent_coeff_square]
      by_cases hn : n % 2 = 0
      · have hodd : (n - 1) % 2 ≠ 0 := by omega
        have hindex : 2 * (n / 2) + 0 = n := by omega
        rw [ite_eq_left hn, ite_eq_right hodd, add_zero, hroot 0, hindex]
      · have heven : (n - 1) % 2 = 0 := by omega
        have hindex : 2 * ((n - 1) / 2) + 1 = n := by omega
        rw [ite_eq_right hn, ite_eq_left heven, zero_add, hroot 1, hindex]
    have square_mem (z : k⸨X⸩) : z ^ 2 ∈ J := by
      let q : SquareField k⸨X⸩ := (frobenius k⸨X⸩ 2).rangeRestrictField z
      exact J.algebraMap_mem q
    rw [hdecomp]
    exact J.add_mem (square_mem a) (J.mul_mem (square_mem b) ht)

private theorem local_square_degree : LocalSquareDegree.{u} := by
  intro F _ _ _ _ _
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, _, t, e, _, _, _, _⟩ := FunctionFieldForms.laurent_presentation F 2
  let k := LocalDivisionAlgebras.BaseResidue F
  let : Finite k := inferInstanceAs (Finite 𝓀[F])
  let : CharP k⸨X⸩ 2 := e.toRingHom.charP e.injective 2
  let C : k →+* k⸨X⸩ := HahnSeries.C
  let : CharP k 2 := C.charP C.injective 2
  let sE : SquareField k⸨X⸩ ≃+* SquareField F :=
    ((frobenius k⸨X⸩ 2).rangeRestrictFieldEquiv.symm.trans e).trans
      (frobenius F 2).rangeRestrictFieldEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv sE e ?_).symm.trans (laurent_square_degree k)
  apply RingHom.ext
  intro a
  let b := (frobenius k⸨X⸩ 2).rangeRestrictFieldEquiv.symm a
  change (e b) ^ 2 = e (a : k⸨X⸩)
  rw [← e.map_pow]
  exact congrArg e ((frobenius k⸨X⸩ 2).rangeRestrictFieldEquiv_apply_symm_apply a)

end SquareDegree

section Semitrace

open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair symmetricPart adjoint hyperbolicGram)

private theorem algebraReducedTrace_split {F A K I : Type u} [Field F] [Ring A] [Algebra F A]
    [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F A)
    (e : (K ⊗[F] A) ≃ₐ[K] Matrix I I K) (x : A) :
    algebraMap F K (algebraReducedTrace hA x) = (e (1 ⊗ₜ[F] x)).trace := by
  let e' := e.trans (Matrix.reindexAlgEquiv K K (Fintype.equivFin I))
  have hd := RM03.CSA.degree_eq_matrix_size hA e'
  have hf (m : ℕ) (hm : RM03.CSA.degree F A = m)
      (g : (K ⊗[F] A) ≃ₐ[K] Matrix (Fin m) (Fin m) K) :
      algebraMap F K (algebraReducedTrace hA x) = (g (1 ⊗ₜ[F] x)).trace := by
    subst m
    have : Nonempty (Fin (RM03.CSA.degree F A)) := ⟨⟨0, RM03.CSA.degree_pos hA⟩⟩
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin,
      ← RM03.CSA.reducedCharpoly_map hA x g]
    simp only [algebraReducedTrace, map_neg, Polynomial.coeff_map]
    rfl
  rw [hf _ hd e']
  exact (Fintype.equivFin I).symm.sum_comp (fun i => e (1 ⊗ₜ[F] x) i i)

private theorem hyperbolicGram_sq {I K : Type u} [Field K] [Fintype I] [DecidableEq I] :
    hyperbolicGram I K * hyperbolicGram I K = 1 := by
  simp [hyperbolicGram, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

open RM03.Brauer.SemilinearDescent (AlgebraAction)

variable {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}

private def traceDual {A : Type u} [Ring A] [Algebra F A] (tr : A →ₗ[F] F) :
    A →ₗ[F] Module.Dual F A where
  toFun x := tr.comp (LinearMap.mulLeft F x)
  map_add' x y := by
    ext z
    change tr ((x + y) * z) = tr (x * z) + tr (y * z)
    rw [add_mul, map_add]
  map_smul' c x := by
    ext z
    change tr ((c • x) * z) = c • tr (x * z)
    rw [smul_mul_assoc, map_smul]

omit [CharP F 2] in
private theorem reduced_trace_pairing (D : DescendedQuadraticPair ρ) :
    ∃ tr : ρ.fixedSubalgebra →ₗ[F] F,
      (∀ x, tr x = algebraReducedTrace D.centralSimple x) ∧
      (∀ x, tr (D.involution.toLinearMap x) = tr x) ∧
      (∀ x y, tr (x * y) = tr (y * x)) ∧ Function.Injective (traceDual tr) := by
  classical
  let A := ρ.fixedSubalgebra
  let : FiniteDimensional F A := D.centralSimple.2.2
  let j : A →ₐ[F] Matrix (I ⊕ I) (I ⊕ I) K :=
    (D.splitting.restrictScalars F).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hj : Function.Injective j := D.splitting.injective.comp
    (Algebra.TensorProduct.includeRight_injective (B := A) (algebraMap F K).injective)
  have htr (a : A) : algebraMap F K (algebraReducedTrace D.centralSimple a) = (j a).trace :=
    algebraReducedTrace_split D.centralSimple D.splitting a
  let tr : A →ₗ[F] F :=
    { toFun := algebraReducedTrace D.centralSimple
      map_add' := fun x y => (algebraMap F K).injective (by
        rw [map_add, htr, htr, htr, map_add, Matrix.trace_add])
      map_smul' := fun c x => (algebraMap F K).injective (by
        change algebraMap F K (algebraReducedTrace D.centralSimple (c • x)) =
          algebraMap F K (c * algebraReducedTrace D.centralSimple x)
        rw [map_mul, htr, htr, map_smul, Matrix.trace_smul, Algebra.smul_def]) }
  have traceInvariant (x : A) : tr (D.involution.toLinearMap x) = tr x := by
    have hadj : j (D.involution.toLinearMap x) = adjoint (hyperbolicGram I K) (j x) := by
      exact D.splittingInvolution (1 ⊗ₜ[F] x)
    apply (algebraMap F K).injective
    change algebraMap F K (algebraReducedTrace D.centralSimple _) =
      algebraMap F K (algebraReducedTrace D.centralSimple _)
    rw [htr, htr, hadj, adjoint, Matrix.trace_mul_cycle, hyperbolicGram_sq, Matrix.one_mul,
      Matrix.trace_transpose]
  have traceCycle (x y : A) : tr (x * y) = tr (y * x) := by
    apply (algebraMap F K).injective
    change algebraMap F K (algebraReducedTrace D.centralSimple _) =
      algebraMap F K (algebraReducedTrace D.centralSimple _)
    rw [htr, htr, map_mul, map_mul, Matrix.trace_mul_comm]
  let P := traceDual tr
  have hP : Function.Injective P := by
    apply (injective_iff_map_eq_zero P).mpr
    intro x hx
    apply hj
    rw [map_zero, Matrix.ext_iff_trace_mul_right]
    intro Z
    rw [Matrix.zero_mul, Matrix.trace_zero]
    obtain ⟨a, rfl⟩ := D.splitting.surjective Z
    induction a using TensorProduct.inductionOn with
    | tmul c a =>
      have hx' : tr (x * a) = 0 := DFunLike.congr_fun hx a
      have hx'' := htr (x * a)
      change algebraReducedTrace D.centralSimple (x * a) = 0 at hx'
      rw [hx', map_zero, map_mul] at hx''
      rw [show c ⊗ₜ[F] a = c • ((1 : K) ⊗ₜ[F] a) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, Matrix.mul_smul, Matrix.trace_smul]
      change c • (j x * j a).trace = 0
      rw [← hx'', smul_zero]
    | add a b ha hb =>
      rw [map_add, Matrix.mul_add, Matrix.trace_add, ha, hb, add_zero]
  exact ⟨tr, fun _ => rfl, traceInvariant, traceCycle, hP⟩

private theorem semitrace_representative : SemitraceRepresentative.{u} := by
  intro F K I _ _ _ _ _ _ ρ D
  let A := ρ.fixedSubalgebra
  let : FiniteDimensional F A := D.centralSimple.2.2
  obtain ⟨tr, htr, traceInvariant, traceCycle, hP⟩ := reduced_trace_pairing D
  let P := traceDual tr
  have hsurj : Function.Surjective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := F) (V := A)).symm).mp hP
  obtain ⟨f, hf⟩ := D.semitrace.exists_extend
  obtain ⟨ell, hell⟩ := hsurj f
  have hf' (x : symmetricPart D.involution) : tr (ell * x.val) = D.semitrace x :=
    (DFunLike.congr_fun hell x.val).trans (DFunLike.congr_fun hf x)
  refine ⟨ell, hP ?_, fun x => (hf' x).symm.trans (htr _)⟩
  ext x
  obtain ⟨hs, hsem⟩ := D.semitraceIdentity x
  change tr ((ell + D.involution.toLinearMap ell) * x) = tr (1 * x)
  have h₁ : tr (D.involution.toLinearMap ell * x) = tr (ell * D.involution.toLinearMap x) := by
    rw [← traceInvariant (D.involution.toLinearMap ell * x), D.involution.map_mul,
      D.involution.involutive, traceCycle]
  have h₂ := hf' ⟨_, hs⟩
  change D.semitrace ⟨_, hs⟩ = algebraReducedTrace D.centralSimple x at hsem
  rw [hsem, ← htr] at h₂
  change tr (ell * (x + D.involution.toLinearMap x)) = tr x at h₂
  rw [add_mul, map_add, one_mul, h₁, ← map_add, ← mul_add, h₂]

private theorem semitrace_equivalence (D : DescendedQuadraticPair ρ) (x : ρ.fixedSubalgebra) :
    (∀ y : symmetricPart D.involution, algebraReducedTrace D.centralSimple (x * y.val) = 0) ↔
      ∃ a, x = a + D.involution.toLinearMap a := by
  let A := ρ.fixedSubalgebra
  let : FiniteDimensional F A := D.centralSimple.2.2
  let s := D.involution.toLinearMap
  let S := symmetricPart D.involution
  obtain ⟨tr, htr, hinv, hcyc, hp⟩ := reduced_trace_pairing D
  let N : A →ₗ[F] A := LinearMap.id + s
  let L : A →ₗ[F] Module.Dual F S := S.subtype.dualMap.comp (traceDual tr)
  have hN : N.ker = S := by
    ext z
    change z ∈ N.ker ↔ z ∈ (s - LinearMap.id : A →ₗ[F] A).ker
    simp only [LinearMap.mem_ker, N, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sub_apply]
    rw [sub_eq_zero, add_eq_zero_iff_eq_neg]
    have ht : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hz : s z + s z = 0 := by rw [← two_smul F (s z), ht, zero_smul]
    rw [neg_eq_of_add_eq_zero_left hz, eq_comm]
  have hN_le : N.range ≤ L.ker := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    ext z
    change tr ((a + s a) * (z : A)) = 0
    have hz : s z.val = z.val := sub_eq_zero.mp z.property
    have ha : tr (s a * z.val) = tr (a * z.val) := by
      rw [← hinv (s a * z.val), D.involution.map_mul, D.involution.involutive]
      change tr (s z.val * a) = tr (a * z.val)
      rw [hz, hcyc]
    rw [add_mul, map_add, ha]
    exact CharTwo.add_self_eq_zero _
  have hL : Function.Surjective L := by
    have htrSurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := F) (V := A)).symm).mp hp
    intro f
    obtain ⟨g, hg⟩ := f.exists_extend
    obtain ⟨a, ha⟩ := htrSurj g
    exact ⟨a, by
      change (traceDual tr a).comp S.subtype = f
      rw [ha, hg]⟩
  have hEq : N.range = L.ker := by
    have hn := LinearMap.finrank_range_add_finrank_ker N
    have hl := LinearMap.finrank_range_add_finrank_ker L
    rw [hN] at hn
    have hd : Module.finrank F (Module.Dual F S) = Module.finrank F S :=
      Subspace.dual_finrank_eq (K := F) (V := S)
    rw [LinearMap.range_eq_top.mpr hL, finrank_top] at hl
    have hl' : Module.finrank F S + Module.finrank F L.ker = Module.finrank F A :=
      (congrArg (· + Module.finrank F L.ker) hd.symm).trans hl
    have he := hn.trans ((Nat.add_comm _ _).trans hl').symm
    exact Submodule.eq_of_le_of_finrank_le hN_le (le_of_eq (Nat.add_right_cancel he).symm)
  have key : (∀ y : S, algebraReducedTrace D.centralSimple (x * y.val) = 0) ↔ x ∈ L.ker := by
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      ext y
      change tr (x * y.val) = 0
      rw [htr, hx]
    · intro hx y
      exact (htr _).symm.trans (DFunLike.congr_fun hx y)
  rw [key, ← hEq]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

private theorem semitrace_conjugation (D : DescendedQuadraticPair ρ)
    (ell : ρ.fixedSubalgebra)
    (hf : ∀ a : symmetricPart D.involution,
      D.semitrace a = algebraReducedTrace D.centralSimple (ell * a.val))
    (g : ρ.fixedSubalgebraˣ) (hg : D.involution.toLinearMap g.val * g.val = 1) :
    PreservesSemitrace D g ↔
      ∃ a, g.inv * ell * g.val - ell = a + D.involution.toLinearMap a := by
  let s := D.involution.toLinearMap
  have hg' : s g.val = g.inv := by
    calc
      s g.val = s g.val * g.val * g.inv := by rw [mul_assoc, g.val_inv, mul_one]
      _ = g.inv := by rw [hg, one_mul]
  have hg'' : s g.inv = g.val := by rw [← hg']; exact D.involution.involutive _
  let c (a : symmetricPart D.involution) : symmetricPart D.involution :=
    ⟨g.val * a.val * g.inv, LinearMap.mem_ker.mpr (sub_eq_zero.mpr (by
      have ha : s a.val = a.val := sub_eq_zero.mp a.prop
      simp only [D.involution.map_mul]
      change s g.inv * (s a.val * s g.val) = _
      rw [hg'', hg', ha, mul_assoc]
      rfl))⟩
  obtain ⟨tr, htr, _, hcyc, _⟩ := reduced_trace_pairing D
  have hv (a : symmetricPart D.involution) :
      D.semitrace (c a) - D.semitrace a = tr ((g.inv * ell * g.val - ell) * a.val) := by
    rw [hf, hf, ← htr, ← htr, sub_mul, map_sub]
    change tr (ell * (g.val * a.val * g.inv)) - tr (ell * a.val) = _
    rw [← mul_assoc, hcyc (ell * (g.val * a.val)) g.inv]
    simp only [mul_assoc]
  rw [← semitrace_equivalence D]
  constructor
  · intro h a
    obtain ⟨b, hb, hba⟩ := h a
    have he : b = c a := Subtype.ext hb
    rw [he, ← sub_eq_zero, hv] at hba
    exact (htr _).symm.trans hba
  · intro h a
    refine ⟨c a, rfl, sub_eq_zero.mp ?_⟩
    rw [hv, htr, h]

end Semitrace

section Refinement

variable {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
  {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] {s : AntiAutomorphism F B}

private theorem bar_add (a b : B) :
    antiValue s (a + b) = antiValue s a + antiValue s b := by
  simp [antiValue]

private theorem bar_mul (a b : B) :
    antiValue s (a * b) = antiValue s b * antiValue s a := by
  simp [antiValue]

private theorem bar_scalar (a : F) : antiValue s (algebraMap F B a) = algebraMap F B a := by
  simp [antiValue]

private theorem pairing_left_add (h : HermitianPairing s V) (x y z : V) :
    h.value (x + y) z = h.value x z + h.value y z := by
  rw [h.hermitian z (x + y), h.add_right, ← antiValue, bar_add]
  exact congrArg₂ (· + ·) (h.hermitian z x).symm (h.hermitian z y).symm

private theorem pairing_left_smul (h : HermitianPairing s V) (x y : V) (a : B) :
    h.value (op a • x) y = antiValue s a * h.value x y := by
  rw [h.hermitian y (op a • x), h.smul_right, ← antiValue, bar_mul]
  exact congrArg (antiValue s a * ·) (h.hermitian y x).symm

private theorem scalarClass_scalar (a : F) : scalarClass F (algebraMap F B a) = 0 := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact ⟨a, rfl⟩

private theorem reducedTrace_equation
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hbar : ∀ a, antiValue s a = quaternionConjugate hB a) (a : B) :
    antiValue s a + a = algebraMap F B (reducedTrace hB a) := by
  rw [hbar, quaternionConjugate, sub_add_cancel]

private theorem scalarClass_bar (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hbar : ∀ a, antiValue s a = quaternionConjugate hB a) (a : B) :
    scalarClass F (antiValue s a) = -(scalarClass F a) := by
  rw [hbar, quaternionConjugate, map_sub, scalarClass_scalar, zero_sub]

private theorem bar_mul_self (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hd : _root_.Specs.RM03.CSA.degree F B = 2)
    (hbar : ∀ a, antiValue s a = quaternionConjugate hB a) (a : B) :
    antiValue s a * a = algebraMap F B (_root_.Specs.RM03.CSA.reducedNorm hB a) := by
  let L := AlgebraicClosure F
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hB
  have hd' : RM03.CSA.degree F B = 2 := hd
  have norm_formula (L' : Type u) [Field L'] [Algebra F L']
      (e' : (L' ⊗[F] B) ≃ₐ[L'] Matrix (Fin 2) (Fin 2) L') :
      algebraMap F L' (_root_.Specs.RM03.CSA.reducedNorm hB a) =
        (e' (1 ⊗ₜ[F] a)).det := by
    revert e'
    rw [← hd']
    exact fun e' => RM03.CSA.reducedNorm_map hB a e'
  let e₂ : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L := hd' ▸ e
  let T : B →ₐ[F] Matrix (Fin 2) (Fin 2) L :=
    (e₂.restrictScalars F).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hT : Function.Injective T := e₂.injective.comp
    (Algebra.TensorProduct.includeRight_injective (B := B) (algebraMap F L).injective)
  have ht : T (antiValue s a) = (T a).adjugate := by
    rw [hbar]
    exact split_quaternion_conjugate hB hd e₂ a
  have hn :
      algebraMap F L (_root_.Specs.RM03.CSA.reducedNorm hB a) = (T a).det := norm_formula L e₂
  apply hT
  rw [map_mul, ht, Matrix.adjugate_mul, T.commutes, IsScalarTower.algebraMap_apply F L,
    hn, Algebra.algebraMap_eq_smul_one]

private def reducedTraceLinear (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hbar : ∀ a, antiValue s a = quaternionConjugate hB a) : B →ₗ[F] F where
  toFun := reducedTrace hB
  map_add' a b := by
    apply (algebraMap F B).injective
    rw [map_add, ← reducedTrace_equation hB hbar (a + b),
      ← reducedTrace_equation hB hbar a, ← reducedTrace_equation hB hbar b, bar_add]
    abel
  map_smul' a b := by
    change reducedTrace hB (a • b) = a * reducedTrace hB b
    rw [Algebra.smul_def]
    apply (algebraMap F B).injective
    rw [map_mul, ← reducedTrace_equation hB hbar (algebraMap F B a * b),
      ← reducedTrace_equation hB hbar b, bar_mul, bar_scalar,
      ← Algebra.commutes a (antiValue s b), mul_add]

private def traceOnClasses [CharP F 2] (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hbar : ∀ a, antiValue s a = quaternionConjugate hB a) : ScalarClasses F B →ₗ[F] F :=
  (scalarLine F B).liftQ (reducedTraceLinear hB hbar) (by
    rintro _ ⟨a, rfl⟩
    change reducedTrace hB (algebraMap F B a) = 0
    apply (algebraMap F B).injective
    rw [← reducedTrace_equation hB hbar, bar_scalar, ← map_add, ← two_mul]
    rw [show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_mul, map_zero])

private theorem refinement_identities : RefinementIdentities.{u,v,w} := by
  intro F _ _ B _ _ hB hd s hbar V _ _ h ell hell
  refine ⟨?_, ?_, ?_, traceOnClasses hB hbar, fun a => rfl, ?_⟩
  · intro x a
    rw [refinement, map_smul, h.smul_right, pairing_left_smul]
  · intro a q q' heq
    have hk : q - q' ∈ scalarLine F B := by
      rw [← Submodule.ker_mkQ (scalarLine F B), LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr heq
    obtain ⟨c, hc⟩ := hk
    change algebraMap F B c = q - q' at hc
    apply sub_eq_zero.mp
    rw [← map_sub, ← sub_mul, ← mul_sub, ← hc, ← Algebra.commutes c (antiValue s a),
      mul_assoc, bar_mul_self hB hd hbar, ← map_mul, scalarClass_scalar]
  · intro x y
    have hc : scalarClass F (h.value y (ell x)) = scalarClass F (h.value (ell x) y) := by
      rw [h.hermitian (ell x) y, ← antiValue, scalarClass_bar hB hbar]
      apply neg_eq_iff_add_eq_zero.mpr
      rw [← two_smul F, show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_smul]
    have hadd := congrArg (scalarClass F) (hell x y)
    simp only [map_add] at hadd
    simp only [refinement, map_add, h.add_right, pairing_left_add, hc]
    rw [← hadd]
    abel
  · intro x
    change algebraMap F B (reducedTrace hB (h.value x (ell x))) = h.value x x
    rw [← reducedTrace_equation hB hbar]
    change unop (s (h.value x (ell x))) + _ = _
    rw [← h.hermitian x (ell x)]
    exact hell x x


private def pairingRight (h : HermitianPairing s V) (x : V) : V →+ B :=
  AddMonoidHom.mk' (h.value x) (h.add_right x)

private theorem refinement_hyperbolic_pair : RefinementHyperbolicPair.{u,v,w} := by
  intro F _ _ B _ _ hB hd s hbar V _ _ h ell hell e he hQe
  obtain ⟨scale, scale_well_defined, polar, t, _, trace⟩ :=
    refinement_identities hB hd s hbar h ell hell
  have htraceZero {x : V} (hx : refinement h ell x = 0) : h.value x x = 0 := by
    rw [← trace x, hx, map_zero, map_zero]
  have hee := htraceZero hQe
  obtain ⟨f₀, hef₀, hf₀e, _⟩ :=
    SymplecticInvolutionModels.quaternionHyperbolicPartner hB hd s hbar h e he hee
  have scaled_zero (x : V) (hx : refinement h ell x = 0) (a : B) :
      refinement h ell (op a • x) = 0 := by
    rw [scale, scale_well_defined a
      (h.value x (ell x)) 0 (by simpa [refinement] using hx), mul_zero, zero_mul, map_zero]
  let q := h.value f₀ (ell f₀)
  let f := f₀ + op q • e
  have hef : h.value e f = 1 := by
    simp [f, h.add_right, h.smul_right, hef₀, hee]
  have hfe : h.value f e = 1 := by
    rw [h.hermitian e f, hef]
    simp
  have hQf : refinement h ell f = 0 := by
    change refinement h ell (f₀ + op q • e) = 0
    rw [polar, scaled_zero e hQe, h.smul_right, hf₀e, one_mul, add_zero]
    change scalarClass F q + scalarClass F q = 0
    rw [← two_smul F, show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_smul]
  have hff := htraceZero hQf
  have pair_e (a b : B) (y : V) (hy : IsHyperbolicComplement h e f y) :
      h.value e (op a • e + y + op b • f) = b := by
    simp [h.add_right, h.smul_right, hee, hef, hy.1]
  have pair_f (a b : B) (y : V) (hy : IsHyperbolicComplement h e f y) :
      h.value f (op a • e + y + op b • f) = a := by
    simp [h.add_right, h.smul_right, hff, hfe, hy.2]
  refine ⟨f, hQf, hee, hff, hef, hfe, ?_, ?_⟩
  · intro x
    let a := h.value f x
    let b := h.value e x
    let y := x - op a • e - op b • f
    have hy : IsHyperbolicComplement h e f y := by
      have hsub (z x y : V) : h.value z (x - y) = h.value z x - h.value z y :=
        (pairingRight h z).map_sub x y
      constructor
      · simp [y, hsub, h.smul_right, hee, hef, b]
      · simp [y, hsub, h.smul_right, hfe, hff, a]
    have hcoords : x = op a • e + y + op b • f := by dsimp [y]; abel
    refine ⟨(a, y, b), ⟨hy, hcoords⟩, ?_⟩
    rintro ⟨a', y', b'⟩ ⟨hy', hx'⟩
    change IsHyperbolicComplement h e f y' at hy'
    change x = op a' • e + y' + op b' • f at hx'
    have ha : a = a' := (congrArg (h.value f) hx').trans (pair_f a' b' y' hy')
    have hb : b = b' := (congrArg (h.value e) hx').trans (pair_e a' b' y' hy')
    subst a' b'
    have heq := hx'.symm.trans hcoords
    have hyy : y' = y := add_left_cancel (add_right_cancel heq)
    simp [hyy]
  · intro a b y hy
    have hz : h.value y (op b • f) = 0 := by
      rw [h.smul_right, h.hermitian f y, hy.2]
      simp
    rw [polar, polar, scaled_zero e hQe, scaled_zero f hQf,
      pairing_left_smul, hy.1, mul_zero, map_zero, zero_add, add_zero, add_zero,
      pairing_left_add, hz, add_zero, pairing_left_smul, h.smul_right, hef, one_mul]
    exact add_comm _ _


private def pairingOp (h : HermitianPairing s V) (x : V) : V →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun y := op (h.value x y)
  map_add' y z := by rw [h.add_right, op_add]
  map_smul' a y := by
    change op (h.value x (a • y)) = a * op (h.value x y)
    exact congrArg op (h.smul_right x y (unop a))

private theorem pairing_right_zero (h : HermitianPairing s V) (x : V) :
    h.value x 0 = 0 :=
  (pairingRight h x).map_zero

private theorem pairing_left_zero (h : HermitianPairing s V) (x : V) :
    h.value 0 x = 0 := by
  rw [h.hermitian x 0, pairing_right_zero]
  simp

private theorem pairing_orthogonal_symm (h : HermitianPairing s V) {x y : V}
    (hxy : h.value x y = 0) : h.value y x = 0 := by
  rw [h.hermitian x y, hxy]
  simp

private theorem exists_hermitian_isotropic
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (hd : _root_.Specs.RM03.CSA.degree F B = 2)
    (hNorm : ∀ a : F, a ≠ 0 → ∃ b : Bˣ, _root_.Specs.RM03.CSA.reducedNorm hB (b : B) = a)
    (hbar : ∀ a, antiValue s a = quaternionConjugate hB a)
    (h : HermitianPairing s V) (hr : 2 ≤ Module.finrank Bᵐᵒᵖ V) :
    ∃ x : V, x ≠ 0 ∧ h.value x x = 0 := by
  classical
  let : Module.Finite Bᵐᵒᵖ V := Module.finite_of_finrank_pos (by omega)
  by_contra hn
  have anisotropic : ∀ x : V, x ≠ 0 → h.value x x ≠ 0 :=
    fun x hx hxx => hn ⟨x, hx, hxx⟩
  have hi : Nontrivial V := (Module.finrank_pos_iff (R := Bᵐᵒᵖ) (M := V)).mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let p := pairingOp h x
  have hrange : Module.finrank Bᵐᵒᵖ p.range ≤ 1 := by
    simpa using Submodule.finrank_le p.range
  have hker : 0 < Module.finrank Bᵐᵒᵖ p.ker := by
    have := p.finrank_range_add_finrank_ker
    omega
  have : Nontrivial p.ker := Module.finrank_pos_iff.mp hker
  obtain ⟨y, hy⟩ := exists_ne (0 : p.ker)
  have hy' : (y : V) ≠ 0 := fun hy' => hy (Subtype.ext hy')
  have hxy : h.value x (y : V) = 0 := by
    have hyker : p y = 0 := y.property
    exact op_injective hyker
  have hyx := pairing_orthogonal_symm h hxy
  obtain ⟨a, ha⟩ := h.central_norm x
  obtain ⟨c, hc⟩ := h.central_norm y
  have ha' : a ≠ 0 := fun ha' => anisotropic x hx (by simp [ha, ha'])
  have hc' : c ≠ 0 := fun hc' => anisotropic y hy' (by simp [hc, hc'])
  obtain ⟨b, hb⟩ := hNorm (-a / c) (div_ne_zero (neg_ne_zero.mpr ha') hc')
  let z : V := x + op (b : B) • (y : V)
  have hzx : h.value x z = h.value x x := by
    simp [z, h.add_right, h.smul_right, hxy]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, pairing_right_zero] at hzx
    exact anisotropic x hx hzx.symm
  have hzz : h.value z z = 0 := by
    change h.value (x + op (b : B) • (y : V)) (x + op (b : B) • (y : V)) = 0
    simp only [pairing_left_add, h.add_right, h.smul_right, pairing_left_smul, hxy, hyx,
      mul_zero, add_zero, zero_add, ha, hc]
    rw [← Algebra.commutes c (antiValue s (b : B)), mul_assoc, bar_mul_self hB hd hbar,
      hb, ← map_mul, mul_div_cancel₀ _ hc', ← map_add, add_neg_cancel, map_zero]
  exact anisotropic z hz hzz

private def orthogonalComplement (h : HermitianPairing s V) (e f : V) :
    Submodule Bᵐᵒᵖ V := ((pairingOp h e).prod (pairingOp h f)).ker

private theorem mem_orthogonalComplement (h : HermitianPairing s V) {e f x : V} :
    x ∈ orthogonalComplement h e f ↔ IsHyperbolicComplement h e f x := by
  change (op (h.value e x), op (h.value f x)) = (0, 0) ↔ _
  simp [IsHyperbolicComplement]

private theorem orthogonalComplement_finrank (h : HermitianPairing s V) (e f : V)
    (hr : 4 ≤ Module.finrank Bᵐᵒᵖ V) :
    2 ≤ Module.finrank Bᵐᵒᵖ (orthogonalComplement h e f) := by
  let : Module.Finite Bᵐᵒᵖ V := Module.finite_of_finrank_pos (by omega)
  let p := (pairingOp h e).prod (pairingOp h f)
  have hle : Module.finrank Bᵐᵒᵖ p.range ≤ 2 := by
    simpa [Module.finrank_prod] using Submodule.finrank_le p.range
  have heq := p.finrank_range_add_finrank_ker
  change _ ≤ Module.finrank Bᵐᵒᵖ p.ker
  omega

private def orthogonalComplementPairing (h : HermitianPairing s V) (e f : V)
    (hee : h.value e e = 0) (hff : h.value f f = 0)
    (hef : h.value e f = 1) (hfe : h.value f e = 1) :
    HermitianPairing s (orthogonalComplement h e f) where
  value x y := h.value x y
  add_right x y z := h.add_right x y z
  smul_right x y a := h.smul_right x y a
  hermitian x y := h.hermitian x y
  central_norm x := h.central_norm x
  nondegenerate x hx := by
    classical
    have hx' : (x : V) ≠ 0 := fun hx' => hx (Subtype.ext hx')
    obtain ⟨y, hy⟩ := h.nondegenerate x hx'
    let a := h.value f y
    let b := h.value e y
    let z := y - op a • e - op b • f
    have hz : z ∈ orthogonalComplement h e f := by
      rw [mem_orthogonalComplement]
      have hsub (z x y : V) : h.value z (x - y) = h.value z x - h.value z y :=
        (pairingRight h z).map_sub x y
      constructor
      · simp [z, hsub, h.smul_right, hee, hef, b]
      · simp [z, hsub, h.smul_right, hfe, hff, a]
    have hh := (mem_orthogonalComplement h).mp x.property
    refine ⟨⟨z, hz⟩, ?_⟩
    change h.value (x : V) z ≠ 0
    have hsub (z x y : V) : h.value z (x - y) = h.value z x - h.value z y :=
      (pairingRight h z).map_sub x y
    simpa [z, hsub, h.smul_right, pairing_orthogonal_symm h hh.1,
      pairing_orthogonal_symm h hh.2] using hy


private theorem quaternion_refinement_isotropy : QuaternionRefinementIsotropy.{u,v,w} := by
  classical
  intro F _ _ B _ _ hB hd hsquare hNorm s hbar V _ _ h ell hell hr
  obtain ⟨e, he, hee⟩ := exists_hermitian_isotropic hB hd hNorm hbar h (by omega)
  obtain ⟨f, hef, hfe, hff⟩ :=
    SymplecticInvolutionModels.quaternionHyperbolicPartner hB hd s hbar h e he hee
  let W := orthogonalComplement h e f
  let hW := orthogonalComplementPairing h e f hee hff hef hfe
  obtain ⟨z, hz, hzz⟩ := exists_hermitian_isotropic hB hd hNorm hbar hW
    (orthogonalComplement_finrank h e f hr)
  obtain ⟨t, hzt, htz, htt⟩ :=
    SymplecticInvolutionModels.quaternionHyperbolicPartner hB hd s hbar hW z hz hzz
  have hez := ((mem_orthogonalComplement h).mp z.property).1
  have hfz := ((mem_orthogonalComplement h).mp z.property).2
  have het := ((mem_orthogonalComplement h).mp t.property).1
  have hte := pairing_orthogonal_symm h het
  have hze := pairing_orthogonal_symm h hez
  change h.value (z : V) (z : V) = 0 at hzz
  change h.value (t : V) (z : V) = 1 at htz
  let P := Bᵐᵒᵖ × Bᵐᵒᵖ
  let p : P →+ V :=
    AddMonoidHom.mk' (fun x => x.1 • e + x.2 • (z : V)) (fun x y => by
      change (x.1 + y.1) • e + (x.2 + y.2) • (z : V) = _
      simp only [add_smul]
      abel)
  have hp : Function.Injective p := by
    apply (injective_iff_map_eq_zero p).mpr
    intro x hx
    apply Prod.ext
    · have hp₁ := congrArg (h.value f) hx
      change h.value f (op (unop x.1) • e + op (unop x.2) • (z : V)) = h.value f 0 at hp₁
      simp only [h.add_right, h.smul_right, hfe, hfz, one_mul, zero_mul, add_zero,
        pairing_right_zero] at hp₁
      exact unop_injective hp₁
    · have hp₂ := congrArg (h.value (t : V)) hx
      change h.value (t : V) (op (unop x.1) • e + op (unop x.2) • (z : V)) =
        h.value (t : V) 0 at hp₂
      simp only [h.add_right, h.smul_right, hte, htz, one_mul, zero_mul, zero_add,
        pairing_right_zero] at hp₂
      exact unop_injective hp₂
  have hbil (a b : Bᵐᵒᵖ) (x y : V) (hxy : h.value x y = 0) :
      h.value (a • x) (b • y) = 0 := by
    change h.value (op (unop a) • x) (op (unop b) • y) = 0
    rw [pairing_left_smul, h.smul_right, hxy, zero_mul, mul_zero]
  have hplane (x y : P) : h.value (p x) (p y) = 0 := by
    change h.value (x.1 • e + x.2 • (z : V)) (y.1 • e + y.2 • (z : V)) = 0
    simp [pairing_left_add, h.add_right, hbil _ _ _ _ hee, hbil _ _ _ _ hez,
      hbil _ _ _ _ hze, hbil _ _ _ _ hzz]
  obtain ⟨scale, _, polar, _, _, _⟩ := refinement_identities hB hd s hbar h ell hell
  let Q : P →+ ScalarClasses F B :=
    AddMonoidHom.mk' (fun x => refinement h ell (p x)) (fun x y => by
      rw [map_add, polar, hplane, map_zero, add_zero])
  have hscale (a : F) (x : P) :
      Q (a • x) = (frobenius F 2).rangeRestrictField a • Q x := by
    change refinement h ell (p (a • x)) = (a ^ 2 : F) • refinement h ell (p x)
    have hp_scale : p (a • x) = op (algebraMap F B a) • p x := by
      change (a • x.1) • e + (a • x.2) • (z : V) =
        op (algebraMap F B a) • (x.1 • e + x.2 • (z : V))
      rw [smul_add]
      change (a • x.1) • e + (a • x.2) • (z : V) =
        op (algebraMap F B a) • (x.1 • e) + op (algebraMap F B a) • (x.2 • (z : V))
      rw [Algebra.smul_def a x.1, Algebra.smul_def a x.2, mul_smul, mul_smul]
      rfl
    rw [hp_scale, scale, bar_scalar, mul_assoc,
      ← Algebra.commutes a (h.value (p x) (ell (p x))), ← mul_assoc, ← map_mul, ← pow_two]
    rw [← Algebra.smul_def]
    exact (scalarClass F).map_smul _ _
  by_contra hn
  have hQ : Function.Injective Q := by
    apply (injective_iff_map_eq_zero Q).mpr
    intro x hx
    by_contra hx'
    have hpx : p x ≠ 0 := fun hpx => hx' (hp (hpx.trans p.map_zero.symm))
    exact hn ⟨p x, hpx, hx⟩
  let : FiniteDimensional F B := hB.2.2
  let : FiniteDimensional (SquareField F) F :=
    Module.finite_of_finrank_pos (by rw [hsquare]; decide)
  have hBdim : Module.finrank F B = 4 := by
    rw [RM03.CSA.finrank_eq_degree_sq hB]
    change RM03.CSA.degree F B = 2 at hd
    rw [hd]
    decide
  have hSdim : Module.finrank F (ScalarClasses F B) = 3 := by
    have hl : Module.finrank F (scalarLine F B) = 1 := by
      rw [LinearMap.finrank_range_of_inj (algebraMap F B).injective]
      simp
    have hdims := (scalarLine F B).finrank_quotient_add_finrank
    rw [hl, hBdim] at hdims
    exact Nat.add_right_cancel hdims
  have hQdim : Module.finrank (SquareField F) (ScalarClasses F B) = 6 := by
    rw [← Module.finrank_mul_finrank (SquareField F) F (ScalarClasses F B), hsquare, hSdim]
  have hPdim : Module.finrank F P = 8 := by
    have hOpp : Module.finrank F Bᵐᵒᵖ = 4 :=
      (MulOpposite.opLinearEquiv F (M := B)).finrank_eq.symm.trans hBdim
    have : Module.Finite F Bᵐᵒᵖ := Module.finite_of_finrank_eq_succ hOpp
    change Module.finrank F (Bᵐᵒᵖ × Bᵐᵒᵖ) = 8
    rw [Module.finrank_prod, hOpp]
  have hRank := lift_rank_le_of_surjective_injective
    (frobenius F 2).rangeRestrictField Q (frobenius F 2).rangeRestrictField_bijective.2 hQ hscale
  let : Module.Finite (SquareField F) (ScalarClasses F B) := Module.Finite.trans F _
  have hle : Module.finrank F P ≤ Module.finrank (SquareField F) (ScalarClasses F B) := by
    simpa only [Cardinal.toNat_lift, Module.finrank] using Cardinal.toNat_le_toNat hRank
      (Cardinal.lift_lt_aleph0.mpr (Module.rank_lt_aleph0 (SquareField F) (ScalarClasses F B)))
  omega

end Refinement

section Recovery

open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair symmetricPart adjoint hyperbolicGram)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms
  (SplitComparison standardAdjoint Involution CanonicalConjugation dagger hermitianValue intoTensor)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open Matrix CategoryTheory

open private matrix_pairing_reversal hermitianValue_congr hermitianValue_single hermitianValue_laws
  nonempty_presentation alternating_transpose from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

variable {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}

private def descended_split_comparison (D : DescendedQuadraticPair ρ) :
    SplitComparison (toDivisionInvolution D.involution) K (Fintype.card I) where
  equiv := D.splitting.trans (Matrix.reindexAlgEquiv K K ((Fintype.equivFin I).sumCongr (Fintype.equivFin I)))
  adjoint a := by
    let i := (Fintype.equivFin I).sumCongr (Fintype.equivFin I)
    let e := Matrix.reindexAlgEquiv K K i
    have charK : CharP K 2 := charP_of_injective_ringHom (algebraMap F K).injective 2
    have hJ : e (hyperbolicGram I K) = Matrix.J (Fin (Fintype.card I)) K := by
      ext p q
      rcases p with p | p <;> rcases q with q | q <;>
        simp [e, i, hyperbolicGram, Matrix.J, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, CharTwo.neg_eq]
    have hJ' : -Matrix.J (Fin (Fintype.card I)) K = Matrix.J (Fin (Fintype.card I)) K :=
      Matrix.ext fun _ _ => CharTwo.neg_eq _
    change e (D.splitting ((D.involution.baseChange K).toLinearMap (1 ⊗ₜ[F] a))) = _
    rw [D.splittingInvolution]
    simp only [AlgEquiv.trans_apply, standardAdjoint, adjoint, map_mul, hJ, hJ']
    rfl

variable {C : Type u} [Ring C] [Algebra F C] {n : ℕ}

omit [CharP F 2] in
private theorem column_adjoint (s : AntiAutomorphism F C) (H : (Matrix (Fin n) (Fin n) C)ˣ)
    (X : Matrix (Fin n) (Fin n) C) (x y : Fin n → C) :
    hermitianValue s H.val (X *ᵥ x) y =
      hermitianValue s H.val x ((H.inv * dagger s X * H.val) *ᵥ y) := by
  have h : H.val * (H.inv * dagger s X * H.val) = dagger s X * H.val := by
    simp only [← mul_assoc, H.val_inv, one_mul]
  unfold hermitianValue
  rw [matrix_pairing_reversal, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, h]

omit [CharP F 2] in
private theorem dagger_gram_mul (D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) C)
    (s : AntiAutomorphism F C) (H : (Matrix (Fin n) (Fin n) C)ˣ)
    (hH : dagger s H.val = H.val)
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * dagger s (e a) * H.val)
    (a : ρ.fixedSubalgebra) : dagger s (H.val * e a) = H.val * e (D.involution.toLinearMap a) := by
  change QuaternionHermitianCocharacters.adjoint s.toAlgHom (H.val * e a) = _
  rw [QuaternionHermitianCocharacters.adjoint_mul]
  change dagger s (e a) * dagger s H.val = _
  rw [hσ, hH]
  simp only [← mul_assoc, H.val_inv, one_mul]

omit [CharP F 2] in
private theorem diagonal_of_alternating (D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) C)
    (b : Involution F C) (H : (Matrix (Fin n) (Fin n) C)ˣ)
    (hH : dagger b.anti H.val = H.val)
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * dagger b.anti (e a) * H.val)
    {δ : ρ.fixedSubalgebra} (hδ : ∃ a, δ = a + D.involution.toLinearMap a) :
    ∀ x, ∃ z, hermitianValue b.anti H.val x (e δ *ᵥ x) = z + antiValue b.anti z := by
  obtain ⟨a, rfl⟩ := hδ
  intro x
  let h := hermitianValue b.anti H.val
  have hL := hermitianValue_laws b.anti b.square H.val hH
  refine ⟨h x (e a *ᵥ x), ?_⟩
  rw [map_add, Matrix.add_mulVec, hL.add_right, ← hL.symmetric, hσ, ← column_adjoint]

omit [CharP F 2] in
private theorem alternating_of_diagonal (D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) C)
    (b : Involution F C) (H : (Matrix (Fin n) (Fin n) C)ˣ)
    (hH : dagger b.anti H.val = H.val)
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * dagger b.anti (e a) * H.val)
    {δ : ρ.fixedSubalgebra} (hδ : D.involution.toLinearMap δ = δ)
    (h : ∀ x, ∃ z, hermitianValue b.anti H.val x (e δ *ᵥ x) = z + antiValue b.anti z) :
    ∃ a, δ = a + D.involution.toLinearMap a := by
  let X := H.val * e δ
  have hx : dagger b.anti X = X := by
    rw [dagger_gram_mul D e b.anti H hH hσ, hδ]
  have hd (i : Fin n) : ∃ z, X i i = z + antiValue b.anti z := by
    obtain ⟨z, hz⟩ := h (Pi.single i 1)
    have hval (v : Fin n → C) : hermitianValue b.anti H.val v (e δ *ᵥ v) =
        hermitianValue b.anti X v v := by
      unfold hermitianValue X
      rw [Matrix.mulVec_mulVec]
    rw [hval] at hz
    rw [hermitianValue_single] at hz
    exact ⟨z, hz⟩
  choose z hz using hd
  let Y : Matrix (Fin n) (Fin n) C := of (fun i j => if i < j then X i j else if i = j then z i else 0)
  have hY : X = Y + dagger b.anti Y := by
    ext i j
    change X i j = Y i j + antiValue b.anti (Y j i)
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · simp [Y, hlt, not_lt_of_gt hlt, (ne_of_lt hlt).symm, antiValue]
    · simpa [Y] using hz i
    · have hh : antiValue b.anti (X j i) = X i j := congrFun (congrFun hx i) j
      simp [Y, hgt, not_lt_of_gt hgt, ne_of_gt hgt, hh]
  let a := e.symm (H.inv * Y)
  refine ⟨a, e.injective ?_⟩
  apply ((Units.mulLeft H).injective)
  change X = H.val * e (a + D.involution.toLinearMap a)
  have he : H.val * e a = Y := by simp [a]
  rw [map_add, Matrix.mul_add, ← dagger_gram_mul D e b.anti H hH hσ, he, ← hY]

omit [CharP F 2] in
private theorem column_isometry (D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) C)
    (s : AntiAutomorphism F C) (H : (Matrix (Fin n) (Fin n) C)ˣ)
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * dagger s (e a) * H.val)
    (g : ρ.fixedSubalgebraˣ) :
    (∀ x y, hermitianValue s H.val (e g.val *ᵥ x) (e g.val *ᵥ y) = hermitianValue s H.val x y) ↔
      D.involution.toLinearMap g.val * g.val = 1 := by
  have hm : dagger s (e g.val) * H.val * e g.val = H.val * e (D.involution.toLinearMap g.val * g.val) := by
    rw [map_mul, hσ]
    simp only [← mul_assoc, H.val_inv, one_mul]
  simp only [hermitianValue_congr, hm]
  constructor
  · intro h
    apply e.injective
    apply (Units.mulLeft H).injective
    change H.val * e (D.involution.toLinearMap g.val * g.val) = H.val * e 1
    rw [map_one, mul_one]
    ext i j
    simpa only [hermitianValue_single] using h (Pi.single i 1) (Pi.single j 1)
  · intro h x y
    rw [h, map_one, mul_one]

private theorem conjugate_difference_self_adjoint {D : DescendedQuadraticPair ρ}
    {ell : ρ.fixedSubalgebra} (hell : ell + D.involution.toLinearMap ell = 1)
    {g : ρ.fixedSubalgebraˣ} (hg : D.involution.toLinearMap g.val * g.val = 1) :
    D.involution.toLinearMap (g.inv * ell * g.val - ell) = g.inv * ell * g.val - ell := by
  let : IsSimpleRing ρ.fixedSubalgebra := D.centralSimple.1
  let : CharP ρ.fixedSubalgebra 2 := charP_of_injective_ringHom (algebraMap F ρ.fixedSubalgebra).injective 2
  let σ := D.involution.toLinearMap
  have hg' : σ g.val = g.inv := by
    calc
      σ g.val = (σ g.val * g.val) * g.inv := by rw [mul_assoc, g.val_inv, mul_one]
      _ = g.inv := by rw [hg, one_mul]
  have hgi : σ g.inv = g.val := by rw [← hg']; exact D.involution.involutive _
  have hs : σ ell = 1 - ell := eq_sub_of_add_eq' hell
  simp only [map_sub, D.involution.map_mul]
  change σ g.val * (σ ell * σ g.inv) - σ ell = _
  rw [hg', hgi, hs, sub_mul, one_mul, mul_sub, g.inv_val, ← mul_assoc]
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  calc
    _ = (1 + 1) + (g.inv * (ell * g.val) + ell) := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add, mul_assoc]

omit [CharP F 2] in
private theorem evaluate_conjugate (_D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) C)
    (s : AntiAutomorphism F C) (H : (Matrix (Fin n) (Fin n) C)ˣ)
    (ell : ρ.fixedSubalgebra) {g : ρ.fixedSubalgebraˣ}
    (hg : ∀ x y, hermitianValue s H.val (e g.val *ᵥ x) (e g.val *ᵥ y) = hermitianValue s H.val x y)
    (x : Fin n → C) :
    hermitianValue s H.val (e g.val *ᵥ x) (e ell *ᵥ (e g.val *ᵥ x)) =
      hermitianValue s H.val x (e (g.inv * ell * g.val) *ᵥ x) := by
  have h : e g.val *ᵥ (e (g.inv * ell * g.val) *ᵥ x) = e ell *ᵥ (e g.val *ᵥ x) := by
    simp only [mulVec_mulVec, ← map_mul]
    rw [← mul_assoc g.val, ← mul_assoc g.val g.inv, g.val_inv, one_mul]
  rw [← h, hg]

omit [CharP F 2] in
private theorem diagonal_sub (_D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) C)
    (s : AntiAutomorphism F C) (H : (Matrix (Fin n) (Fin n) C)ˣ)
    (a b : ρ.fixedSubalgebra) (x : Fin n → C) :
    hermitianValue s H.val x (e (a - b) *ᵥ x) =
      hermitianValue s H.val x (e a *ᵥ x) - hermitianValue s H.val x (e b *ᵥ x) := by
  simp only [hermitianValue, map_sub, Matrix.sub_mulVec, Matrix.mulVec_sub, dotProduct_sub]

private def columnAction {B : Type u} [DivisionRing B]
    (X : Matrix (Fin n) (Fin n) B) : (Fin n → B) →ₗ[Bᵐᵒᵖ] (Fin n → B) where
  toFun y := X *ᵥ y
  map_add' x y := Matrix.mulVec_add X x y
  map_smul' a y := by
    funext i
    change (X *ᵥ fun j => y j * unop a) i = (X *ᵥ y) i * unop a
    simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

omit [CharP F 2] in
private theorem quaternion_alternating_iff (D : DescendedQuadraticPair ρ)
    {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B)
    (b : Involution F B) (H : (Matrix (Fin n) (Fin n) B)ˣ)
    (hH : dagger b.anti H.val = H.val)
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * dagger b.anti (e a) * H.val)
    (hc : ∀ a, antiValue b.anti a = quaternionConjugate hB a)
    (htr : Function.Surjective (reducedTrace hB))
    {δ : ρ.fixedSubalgebra} (hδ : D.involution.toLinearMap δ = δ) :
    (∀ x, scalarClass F (hermitianValue b.anti H.val x (e δ *ᵥ x)) = 0) ↔
      ∃ a, δ = a + D.involution.toLinearMap a := by
  constructor
  · intro h
    apply alternating_of_diagonal D e b H hH hσ hδ
    intro x
    obtain ⟨c, hc'⟩ := (Submodule.Quotient.mk_eq_zero (scalarLine F B)).mp (h x)
    obtain ⟨z, hz⟩ := htr c
    refine ⟨z, ?_⟩
    calc
      _ = algebraMap F B c := hc'.symm
      _ = antiValue b.anti z + z := by rw [reducedTrace_equation hB hc z, hz]
      _ = _ := add_comm _ _
  · intro hh x
    obtain ⟨z, hz⟩ := diagonal_of_alternating D e b H hH hσ hh x
    rw [hz, add_comm z, reducedTrace_equation hB hc, scalarClass_scalar]

set_option maxHeartbeats 850000 in
private theorem quaternion_pair_recovery : QuaternionPairRecovery.{u} := by
  intro F K I _ _ _ _ _ _ ρ D B _ _ hB hd n e
  let : IsSimpleRing ρ.fixedSubalgebra := D.centralSimple.1
  let : Nonempty (Fin n) := nonempty_presentation e
  have hp : 0 < n := (Classical.choice ‹Nonempty (Fin n)›).isLt |> Nat.zero_lt_of_lt
  have hn : n = Fintype.card I := by
    have h : _root_.Specs.RM03.CSA.degree F ρ.fixedSubalgebra =
        n * _root_.Specs.RM03.CSA.degree F B :=
      RM03.CSA.degree_matrix_division D.centralSimple hB.2 hp e
    rw [D.degree, hd] at h
    omega
  obtain ⟨s, hs, hs₂, hsplit, htr⟩ := SymplecticInvolutionModels.quaternionConjugation.{u,u,u} hB hd
  let b : Involution F B := ⟨s, hs₂⟩
  let hcan : CanonicalConjugation.{u,u,u} hB b := ⟨hs, hsplit⟩
  obtain ⟨H, hH, hσ, _, hl, hnondeg, hnrm, E, hE, _, _, hnat⟩ :=
    SymplecticDivisionForms.quaternionModel.{u,u,u,u,u} D.centralSimple
      (toDivisionInvolution D.involution) (descended_split_comparison D) hB hd b hcan e
  change (∀ a, e (D.involution.toLinearMap a) = H.inv * dagger b.anti (e a) * H.val) at hσ
  let h : HermitianPairing b.anti (Fin n → B) :=
    ⟨hermitianValue b.anti H.val, hl.add_right, hl.mul_right, hl.symmetric, hnondeg, hnrm⟩
  obtain ⟨ell, hell, hf⟩ := semitrace_representative D
  refine ⟨⟨hn, b, hs, H, hH, h, rfl, hσ, ell, hell, hf, columnAction (e ell), fun _ => rfl,
    ?_, ?_, ?_, fun R => E R, ?_, fun R S f z => hnat R S f.hom z⟩⟩
  · intro x y
    change hermitianValue b.anti H.val (e ell *ᵥ x) y +
      hermitianValue b.anti H.val x (e ell *ᵥ y) = hermitianValue b.anti H.val x y
    rw [column_adjoint, ← hσ, ← hl.add_right, ← Matrix.add_mulVec, ← map_add,
      add_comm _ ell, hell, map_one, Matrix.one_mulVec]
  · intro ell' hf' x
    obtain ⟨tr, htrA, _, _, _⟩ := reduced_trace_pairing D
    have hδ : ∃ a, ell' - ell = a + D.involution.toLinearMap a :=
      (semitrace_equivalence D (ell' - ell)).mp (fun y => by
        rw [sub_mul, ← htrA, map_sub, htrA, htrA, ← hf', ← hf, sub_self])
    obtain ⟨z, hz⟩ := diagonal_of_alternating D e b H hH hσ hδ x
    have hzero : scalarClass F (hermitianValue b.anti H.val x (e (ell' - ell) *ᵥ x)) = 0 := by
      rw [hz, add_comm z, reducedTrace_equation hB hs, scalarClass_scalar]
    rw [diagonal_sub D e b.anti H, map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  · intro g hg
    have hg' := (column_isometry D e b.anti H hσ g).mp hg
    rw [semitrace_conjugation D ell hf g hg']
    rw [← quaternion_alternating_iff D hB e b H hH hσ hs htr (conjugate_difference_self_adjoint hell hg')]
    constructor
    · intro hq x
      rw [diagonal_sub D e b.anti H, map_sub, sub_eq_zero, ← evaluate_conjugate D e b.anti H ell hg]
      exact hq x
    · intro hh x
      have h := hh x
      rw [diagonal_sub D e b.anti H, map_sub, sub_eq_zero, ← evaluate_conjugate D e b.anti H ell hg] at h
      exact h
  · intro R r a
    rw [show r ⊗ₜ[F] a = r • ((1 : R) ⊗ₜ[F] a) by
       rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hE]

private def scalarConjugation (F : Type u) [Field F] : Involution F F :=
  ⟨AlgEquiv.toOpposite F F, fun _ => rfl⟩

omit [CharP F 2] in
private theorem flip_toLinearMap_matrix (X : Matrix (Fin n) (Fin n) F) :
    LinearMap.flip (Matrix.toLinearMap₂' F X : LinearMap.BilinForm F (Fin n → F)) =
      Matrix.toLinearMap₂' F X.transpose := by
  apply LinearMap.ext₂
  intro x y
  simp only [LinearMap.flip_apply, Matrix.toLinearMap₂'_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

private theorem scalar_pair_isometries (D : DescendedQuadraticPair ρ)
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F)
    (H : (Matrix (Fin n) (Fin n) F)ˣ) (hH : H.val.transpose = H.val)
    (ell : ρ.fixedSubalgebra) (q : QuadraticForm F (Fin n → F))
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * (e a).transpose * H.val)
    (hell : ell + D.involution.toLinearMap ell = 1)
    (hf : ∀ a : symmetricPart D.involution, D.semitrace a = algebraReducedTrace D.centralSimple (ell * a.val))
    (hq : ∀ x, q x = x ⬝ᵥ (H.val *ᵥ (e ell *ᵥ x)))
    (hpolar : q.polarBilin = Matrix.toLinearMap₂' F H.val)
    (g : ρ.fixedSubalgebraˣ) :
    (∀ x, q (e g.val *ᵥ x) = q x) ↔
      D.involution.toLinearMap g.val * g.val = 1 ∧ PreservesSemitrace D g := by
  let s := scalarConjugation F
  let d (a : ρ.fixedSubalgebra) (x : Fin n → F) := hermitianValue s.anti H.val x (e a *ᵥ x)
  have hq' (x : Fin n → F) : q x = d ell x := hq x
  have hp (x y : Fin n → F) : q.polarBilin x y = hermitianValue s.anti H.val x y := by
    rw [hpolar, Matrix.toLinearMap₂'_apply']
    rfl
  have hw : (∀ (x y : Fin n → F),
      hermitianValue s.anti H.val (e g.val *ᵥ x) (e g.val *ᵥ y) =
        hermitianValue s.anti H.val x y) ↔ D.involution.toLinearMap g.val * g.val = 1 :=
    column_isometry D e s.anti H hσ g
  have hc (hg : D.involution.toLinearMap g.val * g.val = 1) :
      (∀ x, q (e g.val *ᵥ x) = q x) ↔ PreservesSemitrace D g := by
    have hg' := hw.mpr hg
    let δ := g.inv * ell * g.val - ell
    have hz (x : Fin n → F) : d δ x = q (e g.val *ᵥ x) - q x := by
      simp only [hq', d, δ, diagonal_sub D e s.anti H, evaluate_conjugate D e s.anti H ell hg']
    rw [semitrace_conjugation D ell hf g hg]
    constructor
    · intro h
      apply alternating_of_diagonal D e s H hH hσ (conjugate_difference_self_adjoint hell hg)
      intro x
      refine ⟨0, ?_⟩
      change d δ x = (0 : F) + 0
      rw [hz, h, sub_self, add_zero]
    · intro h x
      obtain ⟨z, hzero⟩ := diagonal_of_alternating D e s H hH hσ h x
      change d δ x = z + z at hzero
      rwa [hz, CharTwo.add_self_eq_zero, sub_eq_zero] at hzero
  constructor
  · intro h
    have hg : D.involution.toLinearMap g.val * g.val = 1 := hw.mp (fun x y => by
      rw [← hp, ← hp, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar, ← Matrix.mulVec_add, h, h, h]
      rfl)
    exact ⟨hg, (hc hg).mp h⟩
  · rintro ⟨hg, hh⟩
    exact (hc hg).mpr hh

set_option maxHeartbeats 600000 in
private theorem split_pair_recovery : SplitPairRecovery.{u} := by
  intro F K I _ _ _ _ _ _ ρ D n e
  let : IsSimpleRing ρ.fixedSubalgebra := D.centralSimple.1
  let : Nonempty (Fin n) := nonempty_presentation e
  have hp : 0 < n := (Classical.choice ‹Nonempty (Fin n)›).isLt |> Nat.zero_lt_of_lt
  have hn : n = 2 * Fintype.card I := by
    have h : _root_.Specs.RM03.CSA.degree F ρ.fixedSubalgebra =
        n * _root_.Specs.RM03.CSA.degree F F :=
      RM03.CSA.degree_matrix_division D.centralSimple ⟨inferInstance, inferInstance⟩ hp e
    have hFF : _root_.Specs.RM03.CSA.degree F F = 1 := by
      simp [_root_.Specs.RM03.CSA.degree]
    rw [D.degree, hFF, mul_one] at h
    exact h.symm
  obtain ⟨H, _, _, hAlt, hσ, _, _, _, _, _, _, _⟩ :=
    SymplecticDivisionForms.fieldModel.{u,u,u,u} D.centralSimple
      (toDivisionInvolution D.involution) (descended_split_comparison D) e
  change (∀ a, e (D.involution.toLinearMap a) = H.inv * (e a).transpose * H.val) at hσ
  have hH : H.val.transpose = H.val :=
    (alternating_transpose hAlt).trans (Matrix.ext fun _ _ => CharTwo.neg_eq _)
  obtain ⟨ell, hell, hf⟩ := semitrace_representative D
  let X := H.val * e ell
  let q : QuadraticForm F (Fin n → F) := LinearMap.BilinMap.toQuadraticMap
    (Matrix.toLinearMap₂' F X : LinearMap.BilinForm F (Fin n → F))
  have hq (x : Fin n → F) : q x = x ⬝ᵥ (H.val *ᵥ (e ell *ᵥ x)) := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply', mulVec_mulVec]
  have hX : X + X.transpose = H.val := by
    have h : X.transpose = H.val * e (D.involution.toLinearMap ell) :=
      dagger_gram_mul D e (scalarConjugation F).anti H hH hσ ell
    rw [h]
    change H.val * e ell + H.val * e (D.involution.toLinearMap ell) = _
    rw [← Matrix.mul_add, ← map_add, hell, map_one, mul_one]
  have hpolar : q.polarBilin = Matrix.toLinearMap₂' F H.val := by
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, flip_toLinearMap_matrix, ← map_add, hX]
  have hreg : q.polarBilin.Nondegenerate := by
    rw [hpolar]
    exact Matrix.nondegenerate_toLinearMap₂'_iff.mpr
      (Matrix.nondegenerate_of_det_ne_zero (Matrix.isUnits_det_units H).ne_zero)
  exact ⟨hn, H, ell, q, hσ, hell, hf, hq, hpolar, hreg,
    scalar_pair_isometries D e H hH ell q hσ hell hf hq hpolar⟩

end Recovery



private theorem split_division_degree : SplitDivisionDegree.{u,v,w} := by
  intro F _ B _ _ hB E _ _ _ e
  let d := RM03.CSA.degree F B
  let M := Fin d → E
  let ρ : B →ₐ[F] Module.End E M :=
    (((Matrix.toLinAlgEquiv' (R := E) (n := Fin d)).restrictScalars F).toAlgHom.comp
      (e.restrictScalars F).toAlgHom).comp Algebra.TensorProduct.includeRight
  let : Module B M := Module.compHom M ρ.toRingHom
  let : IsScalarTower F B M := IsScalarTower.of_algebraMap_smul fun a x => by
    change ρ (algebraMap F B a) x = a • x
    rw [ρ.commutes]
    rfl
  have hBdim : Module.finrank F B = d ^ 2 := RM03.CSA.finrank_eq_degree_sq hB
  have hMdim : Module.finrank E M = d := Module.finrank_fin_fun E
  have hFdim := Module.finrank_mul_finrank F E M
  have hd := Module.finrank_mul_finrank F B M
  rw [hBdim, ← hFdim, hMdim, pow_two, mul_assoc] at hd
  have hdpos : 0 < d := RM03.CSA.degree_pos hB
  change d ∣ Module.finrank F E
  refine ⟨Module.finrank B M, ?_⟩
  exact (Nat.eq_of_mul_eq_mul_left hdpos (by simpa only [mul_comm (Module.finrank F E) d] using hd)).symm

private theorem split_quadratic_isotropy : SplitQuadraticIsotropy.{u,v} := by
  constructor
  · intro F _ _ k _ _ _ _ n hn
    exact FunctionFieldForms.global_bound (k := k) (K := F) 2 (by decide) (2 * n) (by omega)
  · intro F _ _ _ _ _ n hn
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact FunctionFieldForms.local_quadratic_bound F 2 (2 * n) (by omega)


section Brauer

open _root_.RM03.Brauer.ContinuousCohomology
open _root_.RM03.Brauer.ScalarObstruction
open _root_.Specs.RM03.Brauer.ContinuousCohomology (H2ContinuousValue)
open _root_.Specs.RM03.Brauer.ScalarObstruction (Presents RecordsDefect)
open _root_.Specs.RM03.Brauer (classOf)

private theorem exists_separable_closure_equiv {F E S T : Type u}
    [Field F] [Field E] [Field S] [Field T] [Algebra F S] [Algebra E T]
    [IsSepClosure F S] [IsSepClosure E T] (b : E ≃+* F) :
    ∃ s : T ≃+* S, ∀ a : E, s (algebraMap E T a) = algebraMap F S (b a) := by
  let : Algebra F T := ((algebraMap E T).comp b.symm.toRingHom).toAlgebra
  have h : (algebraMap F T).comp b.toRingHom = (RingEquiv.refl T).toRingHom.comp (algebraMap E T) := by
    ext a
    change algebraMap E T (b.symm (b a)) = algebraMap E T a
    rw [b.symm_apply_apply]
  let : IsSepClosure F T := ⟨IsSepClosure.sep_closed E, Algebra.IsSeparable.of_equiv_equiv b (RingEquiv.refl T) h⟩
  let e := IsSepClosure.equiv F T S
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  change e (algebraMap E T a) = _
  exact (congrArg e (RingHom.congr_fun h a).symm).trans (e.commutes (b a))

variable {F E S T : Type u} [Field F] [Field E] [Field S] [Field T]
  [Algebra F S] [Algebra E T]

private theorem commutes_symm {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a)) (a : F) :
    s.symm (algebraMap F S a) = algebraMap E T (b.symm a) := by
  apply s.injective
  rw [s.apply_symm_apply, h, b.apply_symm_apply]

private def conjugateAut {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a)) (σ : Gal(T/E)) : Gal(S/F) :=
  AlgEquiv.ofRingEquiv (f := (s.symm.trans σ.toRingEquiv).trans s) (fun a => by
    change s (σ (s.symm (algebraMap F S a))) = algebraMap F S a
    rw [commutes_symm h, AlgEquiv.commutes, h, b.apply_symm_apply])

private def conjugateGalois {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a)) : Gal(T/E) ≃* Gal(S/F) where
  toFun := conjugateAut h
  invFun := conjugateAut (commutes_symm h)
  left_inv σ := by
    ext x
    change s.symm (s (σ (s.symm (s x)))) = σ x
    rw [s.symm_apply_apply, s.symm_apply_apply]
  right_inv σ := by
    ext x
    change s (s.symm (σ (s (s.symm x)))) = σ x
    rw [s.apply_symm_apply, s.apply_symm_apply]
  map_mul' σ τ := AlgEquiv.ext fun x => by
    change s (σ (τ (s.symm x))) = s (σ (s.symm (s (τ (s.symm x)))))
    rw [s.symm_apply_apply]

private theorem conjugateGalois_apply {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a)) (σ : Gal(T/E)) (x : T) :
    conjugateGalois h σ (s x) = s (σ x) := by
  change s (σ (s.symm (s x))) = _
  rw [s.symm_apply_apply]

private def transportedField {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a))
    (J : IntermediateField F S) : IntermediateField E T where
  __ := (J.toSubfield.comap s.toRingHom).toSubring
  algebraMap_mem' a := by
    change s (algebraMap E T a) ∈ J
    rw [h]
    exact J.algebraMap_mem _
  inv_mem' _ hx := (J.toSubfield.comap s.toRingHom).inv_mem hx

private def transportedFieldEquiv {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a))
    (J : IntermediateField F S) : transportedField h J ≃+* J where
  toFun x := ⟨s x, x.prop⟩
  invFun x := ⟨s.symm x, by change s (s.symm (x : S)) ∈ J; rw [s.apply_symm_apply]; exact x.prop⟩
  left_inv x := Subtype.ext (s.symm_apply_apply x)
  right_inv x := Subtype.ext (s.apply_symm_apply x)
  map_mul' x y := Subtype.ext (s.map_mul x y)
  map_add' x y := Subtype.ext (s.map_add x y)

private theorem transportedField_commutes {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a)) (J : IntermediateField F S) :
    (algebraMap F J).comp b.toRingHom =
      (transportedFieldEquiv h J).toRingHom.comp (algebraMap E (transportedField h J)) :=
  RingHom.ext fun a => Subtype.ext (h a).symm

private theorem conjugateGalois_continuous {b : E ≃+* F} {s : T ≃+* S}
    (h : ∀ a, s (algebraMap E T a) = algebraMap F S (b a)) : Continuous (conjugateGalois h) := by
  apply continuous_of_continuousAt_one (conjugateGalois h)
  change Filter.Tendsto (conjugateGalois h) (𝓝 1) (𝓝 (conjugateGalois h 1))
  rw [map_one, Filter.tendsto_def]
  intro U hU
  obtain ⟨J, hJ, hJU⟩ := (krullTopology_mem_nhds_one_iff F S U).mp hU
  have hfin := Module.finite_of_finrank_pos (R := E) (M := transportedField h J)
    (by rw [Algebra.finrank_eq_of_equiv_equiv b (transportedFieldEquiv h J) (transportedField_commutes h J)];
        exact Module.finrank_pos)
  apply (krullTopology_mem_nhds_one_iff E T _).mpr
  refine ⟨transportedField h J, hfin, fun σ hσ => hJU ?_⟩
  change σ ∈ (transportedField h J).fixingSubgroup at hσ
  change conjugateGalois h σ ∈ J.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  obtain ⟨y, rfl⟩ := s.surjective x
  rw [conjugateGalois_apply h, hσ y hx]

private theorem square_root_galois_data [Algebra F E] [CharP F 2]
    [IsSepClosure F S] [IsSepClosure E T] (sq : E ≃+* F) (hsq : IsSquareRootField F E sq) :
    ∃ (s : T ≃+* S) (i : S →+* T) (r : Gal(T/E) ≃* Gal(S/F)),
      (∀ x : E, s (algebraMap E T x) = algebraMap F S (sq x)) ∧
      (∀ x : S, s (i x) = x ^ 2) ∧
      (∀ a : F, i (algebraMap F S a) = algebraMap E T (algebraMap F E a)) ∧
      (∀ (σ : Gal(T/E)) (x : S), i (r σ x) = σ (i x)) ∧
      (∀ (σ : Gal(T/E)) (x : T), r σ (s x) = s (σ x)) ∧
      Continuous r ∧ Continuous r.symm := by
  obtain ⟨s, hs⟩ := exists_separable_closure_equiv (S := S) (T := T) sq
  let : CharP S 2 := charP_of_injective_ringHom (algebraMap F S).injective 2
  let i := s.symm.toRingHom.comp (frobenius S 2)
  let r := conjugateGalois hs
  have hi (x : S) : s (i x) = x ^ 2 := s.apply_symm_apply (x ^ 2)
  refine ⟨s, i, r, hs, hi, ?_, ?_, conjugateGalois_apply hs, conjugateGalois_continuous hs,
    conjugateGalois_continuous (commutes_symm hs)⟩
  · intro a
    have ha : sq (algebraMap F E a) = a ^ 2 := (algebraMap F E).injective (by rw [hsq, map_pow])
    apply s.injective
    rw [hi, hs, ha, map_pow]
  · intro σ x
    apply s.injective
    rw [hi, ← conjugateGalois_apply hs, hi, map_pow]

section Continuous

local instance : TopologicalSpace Sˣ := ⊥
local instance : DiscreteTopology Sˣ := ⟨rfl⟩
local instance : TopologicalSpace Tˣ := ⊥
local instance : DiscreteTopology Tˣ := ⟨rfl⟩

open scoped Pointwise

private def pullScalarCocycle (r : Gal(T/E) →* Gal(S/F)) (i : S →+* T)
    (hi : ∀ (σ : Gal(T/E)) (x : S), i (r σ x) = σ (i x)) :
    ScalarCocycle F S →* ScalarCocycle E T where
  toFun c := ⟨fun p => Units.map i.toMonoidHom (c.val (r p.1, r p.2)), by
    have act (σ : Gal(T/E)) (a : Sˣ) : Units.map i.toMonoidHom (r σ • a) = σ • Units.map i.toMonoidHom a :=
      Units.ext (hi σ a.val)
    intro σ τ ν
    change Units.map i.toMonoidHom (c.val (r (σ * τ), r ν)) * Units.map i.toMonoidHom (c.val (r σ, r τ)) =
      σ • Units.map i.toMonoidHom (c.val (r τ, r ν)) * Units.map i.toMonoidHom (c.val (r σ, r (τ * ν)))
    simpa only [map_mul, act] using congrArg (Units.map i.toMonoidHom) (c.property (r σ) (r τ) (r ν))⟩
  map_one' := Subtype.ext (funext fun _ => map_one (Units.map i.toMonoidHom))
  map_mul' c d := Subtype.ext (funext fun p => map_mul (Units.map i.toMonoidHom) (c.val (r p.1, r p.2)) (d.val (r p.1, r p.2)))

private def pullContinuousCocycle (r : Gal(T/E) →* Gal(S/F)) (hr : Continuous r) (i : S →+* T)
    (hi : ∀ (σ : Gal(T/E)) (x : S), i (r σ x) = σ (i x)) :
    continuousCocycles F S →* continuousCocycles E T :=
  ((pullScalarCocycle r i hi).comp (continuousCocycles F S).subtype).codRestrict _ (fun c => by
    change Continuous (fun p : Gal(T/E) × Gal(T/E) => Units.map i.toMonoidHom (c.val.val (r p.1, r p.2)))
    exact (continuous_of_discreteTopology (f := Units.map i.toMonoidHom)).comp
      (c.property.comp ((hr.comp continuous_fst).prodMk (hr.comp continuous_snd))))

private def pullContinuousClass (r : Gal(T/E) →* Gal(S/F)) (hr : Continuous r) (i : S →+* T)
    (hi : ∀ (σ : Gal(T/E)) (x : S), i (r σ x) = σ (i x)) :
    H2ContinuousValue F S →* H2ContinuousValue E T :=
  QuotientGroup.lift _ ((continuousClass (k := E) (S := T)).comp (pullContinuousCocycle r hr i hi)) (by
    rintro c ⟨f, hf⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    let f' : continuousOneCochains E T := ⟨fun σ => Units.map i.toMonoidHom (f.val (r σ)),
      (continuous_of_discreteTopology (f := Units.map i.toMonoidHom)).comp (f.property.comp hr)⟩
    refine ⟨f', Subtype.ext (funext fun ⟨σ, τ⟩ => ?_)⟩
    have act (σ : Gal(T/E)) (a : Sˣ) : Units.map i.toMonoidHom (r σ • a) = σ • Units.map i.toMonoidHom a :=
      Units.ext (hi σ a.val)
    change (σ • Units.map i.toMonoidHom (f.val (r τ))) / Units.map i.toMonoidHom (f.val (r (σ * τ))) *
      Units.map i.toMonoidHom (f.val (r σ)) = Units.map i.toMonoidHom (c.val.val (r σ, r τ))
    rw [← hf]
    change _ = Units.map i.toMonoidHom ((r σ • f.val (r τ)) / f.val (r σ * r τ) * f.val (r σ))
    simp only [map_mul, map_div, act])

end Continuous

open RM03.Brauer (baseChangeTower baseChangeTower_tmul baseChangeCSA)
open RM03.Brauer.AbsoluteIsomorphism (finite_stage_cover)
open RM03.Brauer.ProjectiveClassification (Mat)
open Matrix

open private extendSplitting extendSplitting_tmul_matrix
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.AbsoluteIsomorphism
open private presents_apply presents_of_formula
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarObstruction
open private groupLaws
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange

/-- A finite splitting and its scalar defect base change to the transported stage. -/
private theorem base_changed_defect [Algebra F E] [IsSepClosure F S] [IsSepClosure E T]
    {b : E ≃+* F} {s : T ≃+* S} (hs : ∀ a, s (algebraMap E T a) = algebraMap F S (b a))
    (i : S →+* T) (hi : ∀ a : S, s (i a) = a ^ 2)
    (hiF : ∀ a : F, i (algebraMap F S a) = algebraMap E T (algebraMap F E a))
    (J : Stage F S) (A : _root_.CSA.{u,u} F) {n : ℕ} (hn : 0 < n)
    (p : (J ⊗[F] A) ≃ₐ[J] Mat J n) (g : Gal(J/F) → GL (Fin n) J)
    (hg : Presents p g) (c : ScalarCocycle F J) (hc : RecordsDefect g c) :
    ∃ (U : Stage E T) (q : (U ⊗[E] (baseChangeCSA F E A)) ≃ₐ[U] Mat U n)
      (g' : Gal(U/E) → GL (Fin n) U) (c' : ScalarCocycle E U),
      Presents q g' ∧ RecordsDefect g' c' ∧
      ∀ σ τ : Gal(T/E),
        absoluteUnits U (c'.val (absoluteRestrict U σ, absoluteRestrict U τ)) =
        Units.map i.toMonoidHom (absoluteUnits J
          (c.val (absoluteRestrict J (conjugateGalois hs σ), absoluteRestrict J (conjugateGalois hs τ)))) := by
  let V := transportedField hs J.toIntermediateField
  let e := transportedFieldEquiv hs J.toIntermediateField
  have he := transportedField_commutes hs J.toIntermediateField
  let : FiniteDimensional E V := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank E V
    rw [Algebra.finrank_eq_of_equiv_equiv b e he]
    exact Module.finrank_pos)
  have he' (a : E) : e (algebraMap E V a) = algebraMap F J (b a) :=
    (RingHom.congr_fun he a).symm
  let U : Stage E T := {
    toIntermediateField := V
    finiteDimensional := inferInstance
    isGalois := IsGalois.of_equiv_equiv (f := b.symm) (g := e.symm)
      (RingHom.ext fun a => (commutes_symm he' a).symm) }
  let r := conjugateGalois he'
  let j : J →+* U := (i.comp J.toIntermediateField.val.toRingHom).codRestrict V.toSubfield.toSubring (fun x => by
    change s (i (x : S)) ∈ J.toIntermediateField
    rw [hi]
    rw [pow_two]
    exact J.toIntermediateField.mul_mem x.prop x.prop)
  have hj (σ : Gal(U/E)) (x : J) : j (r σ x) = σ (j x) := by
    apply e.injective
    have h (x : J) : e (j x) = x ^ 2 := Subtype.ext (hi x)
    rw [h, ← conjugateGalois_apply he', h, map_pow]
  have hRestrict (σ : Gal(T/E)) : r (absoluteRestrict U σ) = absoluteRestrict J (conjugateGalois hs σ) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    have hco (z : U) : (e z : S) = s (z : T) := rfl
    change ((r (absoluteRestrict U σ) (e y)) : S) =
      ((absoluteRestrict J (conjugateGalois hs σ) (e y)) : S)
    rw [conjugateGalois_apply he',
      AlgEquiv.restrictNormalHom_apply, hco, hco,
      AlgEquiv.restrictNormalHom_apply, conjugateGalois_apply]
  let : Algebra F U := ((algebraMap E U).comp (algebraMap F E)).toAlgebra
  let : IsScalarTower F E U := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra J U := j.toAlgebra
  let : IsScalarTower F J U := IsScalarTower.of_algebraMap_eq (fun a =>
    Subtype.ext (hiF a).symm)
  let f := baseChangeTower F E U A
  let q := f.trans (extendSplitting (F := U) p)
  let m := GeneralLinearGroup.map (n := Fin n) j
  let g' := fun σ => m (g (r σ))
  let c' := pullScalarCocycle r.toMonoidHom j hj c
  refine ⟨U, q, g', c', presents_of_formula hn q g' ?_, ?_, ?_⟩
  · intro σ a z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, Matrix.map_add _ (map_add σ), Matrix.mul_add, Matrix.add_mul, hx, hy]
    | tmul d x =>
      have hq (z : U) : q (z ⊗ₜ[E] (d ⊗ₜ[F] x)) =
          (algebraMap E U d * z) • (p (1 ⊗ₜ[F] x)).map j := by
        simp only [q, AlgEquiv.trans_apply, f, baseChangeTower_tmul, extendSplitting_tmul_matrix,
          Algebra.smul_def]
        rfl
      have h := presents_apply hg (r σ) 1 x
      rw [map_one] at h
      have hm := congrArg (RingHom.mapMatrix (m := Fin n) j) h
      simp only [map_mul, RingHom.mapMatrix_apply] at hm
      have hm' : ((p (1 ⊗ₜ[F] x)).map (r σ)).map j = ((p (1 ⊗ₜ[F] x)).map j).map σ :=
        Matrix.ext fun p q => hj σ _
      rw [hm'] at hm
      rw [hq, hq, Matrix.map_smul' _ _ _ (map_mul σ), map_mul, AlgEquiv.commutes,
        Matrix.mul_smul, Matrix.smul_mul]
      exact congrArg (fun X : Mat U n => (algebraMap E U d * σ a) • X) hm
  · intro σ τ
    have hmap (σ : Gal(U/E)) (X : GL (Fin n) J) : m (mapGL (r σ) X) = mapGL σ (m X) :=
      GeneralLinearGroup.ext fun a b => hj σ (X a b)
    have hscalar (a : Jˣ) : m (GeneralLinearGroup.scalar (Fin n) a) =
        GeneralLinearGroup.scalar (Fin n) (Units.map j.toMonoidHom a) := by
      apply GeneralLinearGroup.ext
      intro p q
      change j (Matrix.scalar (Fin n) (a : J) p q) = Matrix.scalar (Fin n) (j (a : J)) p q
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs <;> simp
    have he := congrArg m (hc (r σ) (r τ))
    simpa only [map_mul, map_inv, hmap, hscalar, c', g', pullScalarCocycle, MonoidHom.coe_mk,
      OneHom.coe_mk, MulEquiv.coe_toMonoidHom] using he
  · intro σ τ
    apply Units.ext
    change i ((c.val (r (absoluteRestrict U σ), r (absoluteRestrict U τ))).val : S) = _
    rw [hRestrict, hRestrict]
    rfl

private theorem canonical_brauer_normalization {F S : Type u} [Field F] [Field S]
    [Algebra F S] [IsSepClosure F S] :
    HasBrauerNormalization F S (RM03.Brauer.AbsoluteIsomorphism.absoluteBrauerEquiv.{u,u,u}
      (k := F) (S := S)) := by
  intro J A n hn p g hg c hc
  let a : RM03.Brauer.AbsoluteIsomorphism.StageBrauer.{u,u,u} J :=
    ⟨classOf A, (RM03.Brauer.classOf_mem_relativeBrauerGroup_iff F J A).mpr ⟨n, hn, ⟨p⟩⟩⟩
  have h := RM03.Brauer.AbsoluteIsomorphism.absoluteBrauerEquiv_apply.{u,u,u} J a
  rw [h]
  exact congrArg (fun z => Additive.ofMul (toContinuous J z.toMul))
    (RM03.Brauer.ScalarObstruction.obstruction_formula.{u,u,u} F J A a.prop hn p g hg c hc)

private theorem frobenius_brauer_comparison : FrobeniusBrauerComparison.{u} := by
  intro F E S T _ _ _ _ _ _ _ _ _ _ sq hsq
  obtain ⟨s, i, r, hs, hi, hiF, hiGal, hr, hcont, hcont'⟩ :=
    square_root_galois_data (S := S) (T := T) sq hsq
  have hconj : r = conjugateGalois hs := by
    apply MulEquiv.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    obtain ⟨z, rfl⟩ := s.surjective x
    exact (hr σ z).trans (conjugateGalois_apply hs σ z).symm
  subst r
  let C := pullContinuousCocycle (conjugateGalois hs).toMonoidHom hcont i hiGal
  let H := pullContinuousClass (conjugateGalois hs).toMonoidHom hcont i hiGal
  refine ⟨s, i, conjugateGalois hs, hs, hi, hiF, hiGal, hr, hcont, hcont', C, H, fun _ _ _ => rfl, fun _ => rfl, ?_⟩
  let gF := RM03.Brauer.instAddCommGroup.{u,u} F
  let gE := RM03.Brauer.instAddCommGroup.{u,u} E
  refine ⟨gF, gE, groupLaws F, groupLaws E, ?_⟩
  let eF := RM03.Brauer.AbsoluteIsomorphism.absoluteBrauerEquiv.{u,u,u} (k := F) (S := S)
  let eE := RM03.Brauer.AbsoluteIsomorphism.absoluteBrauerEquiv.{u,u,u} (k := E) (S := T)
  let b := RM03.Brauer.baseChange.{u,u,u} F E
  have heF : HasBrauerNormalization F S eF := canonical_brauer_normalization
  have heE : HasBrauerNormalization E T eE := canonical_brauer_normalization
  refine ⟨eF, eE, b, heF, heE, ?_, ?_⟩
  · intro A
    exact ⟨baseChangeCSA F E A, rfl, RM03.Brauer.baseChange_classOf F E A⟩
  · intro x
    obtain ⟨J, A, rfl, n, hn, ⟨p⟩⟩ := finite_stage_cover.{u,u,u} (S := S) x
    obtain ⟨g, hg⟩ := exists_presentation hn p
    obtain ⟨c, hc⟩ := exists_recorded_defect hn hg
    obtain ⟨U, q, g', c', hg', hc', hcc⟩ := base_changed_defect hs i hi hiF J A hn p g hg c hc
    rw [show b (classOf A) = classOf (baseChangeCSA F E A) by rfl, heE U _ hn q g' hg' c' hc', heF J A hn p g hg c hc]
    apply congrArg Additive.ofMul
    change continuousClass (toContinuousCocycle U c') = continuousClass (C (toContinuousCocycle J c))
    apply congrArg (continuousClass (k := E) (S := T))
    exact Subtype.ext (Subtype.ext (funext fun ⟨σ, τ⟩ => hcc σ τ))

open private csa_eq_of_toAlgCat_eq
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange
open private equivalent_of_matrix_presentation
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.Equivalence

/-- Squaring on the transported coefficients gives the square of a continuous
class. The return map is injective since both of its input maps are isomorphisms. -/
private theorem pullContinuousClass_eq_one_of_square_eq_one
    (s : T ≃+* S) (i : S →+* T) (r : Gal(T/E) ≃* Gal(S/F))
    (hs : ∀ x : S, s (i x) = x ^ 2)
    (hr : ∀ (σ : Gal(T/E)) (x : T), r σ (s x) = s (σ x))
    (hc : Continuous r) (hc' : Continuous r.symm)
    (C : continuousCocycles F S →* continuousCocycles E T)
    (H : H2ContinuousValue F S →* H2ContinuousValue E T)
    (hC : ∀ c σ τ, (C c).val.val (σ, τ) = Units.map i.toMonoidHom (c.val.val (r σ, r τ)))
    (hH : ∀ c, H (continuousClass c) = continuousClass (C c))
    (x : H2ContinuousValue F S) (hx : x ^ 2 = 1) : H x = 1 := by
  have hcomp (σ : Gal(S/F)) (z : T) : s (r.symm σ z) = σ (s z) := by
    rw [← hr, r.apply_symm_apply]
  let C' := pullContinuousCocycle r.symm.toMonoidHom hc' s.toRingHom hcomp
  let H' := pullContinuousClass r.symm.toMonoidHom hc' s.toRingHom hcomp
  have hback (σ : Gal(T/E)) (z : S) : s.symm (r σ z) = σ (s.symm z) := by
    apply s.injective
    rw [s.apply_symm_apply, ← hr, s.apply_symm_apply]
  let C'' := pullContinuousCocycle r.toMonoidHom hc s.symm.toRingHom hback
  let H'' := pullContinuousClass r.toMonoidHom hc s.symm.toRingHom hback
  have hleft (y : H2ContinuousValue E T) : H'' (H' y) = y := by
    obtain ⟨c, rfl⟩ := (QuotientGroup.mk'_surjective (continuousCoboundaries E T)) y
    change continuousClass (C'' (C' c)) = continuousClass c
    apply congrArg (continuousClass (k := E) (S := T))
    refine Subtype.ext (Subtype.ext (funext fun ⟨σ, τ⟩ => Units.ext ?_))
    change s.symm (s ((c.val.val (r.symm (r σ), r.symm (r τ)) : Tˣ) : T)) = _
    rw [r.symm_apply_apply, r.symm_apply_apply, s.symm_apply_apply]
  have hsquare (y : H2ContinuousValue F S) : H' (H y) = y ^ 2 := by
    obtain ⟨c, rfl⟩ := (QuotientGroup.mk'_surjective (continuousCoboundaries F S)) y
    change H' (H (continuousClass c)) = _
    rw [hH, ← map_pow]
    change continuousClass (C' (C c)) = continuousClass (c ^ 2)
    apply congrArg (continuousClass (k := F) (S := S))
    refine Subtype.ext (Subtype.ext (funext fun ⟨σ, τ⟩ => Units.ext ?_))
    change s ((C c).val.val (r.symm σ, r.symm τ)).val = ((c.val.val (σ, τ)) ^ 2).val
    rw [hC, r.apply_symm_apply, r.apply_symm_apply]
    exact hs _
  apply Function.LeftInverse.injective hleft
  rw [hsquare, hx, map_one]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
private theorem division_degree_over_squares (hdeg : SplitDivisionDegree.{u,u,u}) :
    DivisionDegreeOverSquares.{u} := by
  intro F _ _ hsquare A B _ _ _ _ hA hB m hm e σ
  let E : Type u := SquareField F
  let sq : E ≃+* F := (frobenius F 2).rangeRestrictFieldEquiv.symm
  let : Algebra F E := (sq.symm.toRingHom.comp (frobenius F 2)).toAlgebra
  have hsq : IsSquareRootField F E sq := by
    intro a
    apply sq.injective
    change sq (sq.symm (sq a ^ 2)) = sq (a ^ 2)
    rw [sq.apply_symm_apply, map_pow]
  have hE : Module.finrank F E = 2 := by
    let f := (frobenius F 2).rangeRestrictFieldEquiv
    refine (Algebra.finrank_eq_of_equiv_equiv f sq ?_).trans hsquare
    apply RingHom.ext
    intro x
    exact (sq.apply_symm_apply (x ^ 2)).symm
  let : FiniteDimensional F E := Module.finite_of_finrank_pos (hE.symm ▸ (by decide : 0 < 2))
  let S := SeparableClosure F
  let T := SeparableClosure E
  obtain ⟨s, i, r, _, hi, _, _, hr, hrC, hrC', C, H, hC, hH,
    gF, gE, hgF, hgE, eF, eE, b, _, _, hb, hcomp⟩ :=
      frobenius_brauer_comparison F E S T sq hsq
  let _ := gF
  let _ := gE
  let A₀ := RM03.CSA.toCSA hA
  let B₀ := RM03.CSA.toCSA hB
  have hneg : -(classOf A₀) = classOf A₀ := by
    obtain ⟨D, hD, hneg⟩ := hgF.2.2.1 A₀
    have hD' : D = RM03.Brauer.oppositeCSA A₀ := csa_eq_of_toAlgCat_eq hD
    rw [hneg, hD']
    exact (RM03.Brauer.classOf_eq_of_algEquiv (A := A₀) (B := RM03.Brauer.oppositeCSA A₀) σ).symm
  have hA2 : classOf A₀ + classOf A₀ = 0 :=
    (congrArg (· + classOf A₀) hneg).symm.trans (neg_add_cancel (classOf A₀))
  have hsq2 : (eF (classOf A₀)).toMul ^ 2 = 1 := by
    change Additive.toMul _ ^ 2 = Additive.toMul (0 : Additive (H2ContinuousValue F S))
    rw [pow_two]
    change Additive.toMul (eF (classOf A₀) + eF (classOf A₀)) = _
    rw [← map_add, hA2, map_zero]
  have he : b (classOf A₀) = 0 := by
    apply eE.injective
    rw [hcomp, map_zero]
    exact congrArg Additive.ofMul (pullContinuousClass_eq_one_of_square_eq_one
      s i r hi hr hrC hrC' C H hC hH _ hsq2)
  have hBclass : classOf A₀ = classOf B₀ :=
    (RM03.Brauer.classOf_eq_iff F A₀ B₀).mpr (equivalent_of_matrix_presentation hm e)
  have split (C : _root_.CSA.{u,u} F) (h : b (classOf C) = 0) :
      _root_.Specs.RM03.CSA.isSplit E (E ⊗[F] C) := by
    obtain ⟨D, hD, hCD⟩ := hb C
    have hD' : D = baseChangeCSA F E C := csa_eq_of_toAlgCat_eq hD
    rw [hD'] at hCD
    change _root_.Specs.RM03.CSA.isSplit E (baseChangeCSA F E C)
    exact (hgE.2.2.2 _).mp (hCD.symm.trans h)
  have matrix {X : Type u} [Ring X] [Algebra F X] (hX : _root_.Specs.RM03.CSA.isCentralSimple F X)
      (h : _root_.Specs.RM03.CSA.isSplit E (E ⊗[F] X)) :
      Nonempty ((E ⊗[F] X) ≃ₐ[E] Matrix (Fin (_root_.Specs.RM03.CSA.degree F X))
        (Fin (_root_.Specs.RM03.CSA.degree F X)) E) := by
    obtain ⟨n, _, ⟨t⟩⟩ := h
    have ht : _root_.Specs.RM03.CSA.degree F X = n := RM03.CSA.degree_eq_matrix_size hX t
    rw [ht]
    exact ⟨t⟩
  have ha := matrix hA (split A₀ he)
  have hb' := matrix hB (split B₀ (by rwa [← hBclass]))
  refine ⟨⟨E, inferInstance, inferInstance, sq, hsq, hE, ha, hb'⟩, ?_⟩
  obtain ⟨p⟩ := hb'
  simpa only [hE] using hdeg hB p

end Brauer

section ArithmeticIsotropy

open scoped RatFunc Matrix
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair NontrialitarianSpinModel SpinModel symmetricPart)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open Matrix

variable {F : Type u} [Field F] [CharP F 2]

private theorem arithmetic_square_degree (hF : IsCharacteristicTwoArithmeticField.{u,v} F) :
    Module.finrank (SquareField F) F = 2 := by
  rcases hF with ⟨k, _, _, _, _⟩ | ⟨_, _, _⟩
  · exact global_square_degree (k := k)
  · exact local_square_degree F

private theorem arithmetic_quaternion_norm (hF : IsCharacteristicTwoArithmeticField.{u,v} F)
    {B : Type u} [DivisionRing B] [Algebra F B] (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hd : _root_.Specs.RM03.CSA.degree F B = 2) :
    ∀ a : F, a ≠ 0 → ∃ b : Bˣ, _root_.Specs.RM03.CSA.reducedNorm hB (b : B) = a := by
  rcases hF with ⟨k, _, _, _, _⟩ | ⟨_, _, _⟩
  · exact FunctionFieldForms.global_quaternion_norm (k := k) hB hd
  · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact FunctionFieldForms.local_quaternion_norm (F := F) 2 hB hd

private theorem arithmetic_quaternion_vector {K I : Type u} [Field K] [Algebra F K] [Fintype I]
    [DecidableEq I] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {D : DescendedQuadraticPair ρ}
    (hF : IsCharacteristicTwoArithmeticField.{u,v} F)
    {B : Type u} [DivisionRing B] [Algebra F B] (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (hd : _root_.Specs.RM03.CSA.degree F B = 2) {n : ℕ} (hn : 4 ≤ n)
    {e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B} (P : QuaternionPair D hB n e) :
    ∃ x : Fin n → B, x ≠ 0 ∧ refinement P.pairing P.ellAction x = 0 := by
  apply quaternion_refinement_isotropy hB hd (arithmetic_square_degree hF)
    (arithmetic_quaternion_norm hF hB hd) P.bar.anti P.canonical P.pairing P.ellAction P.pairingTraceOne
  let eOp : (Fin n → B) ≃ₗ[Bᵐᵒᵖ] (Fin n → Bᵐᵒᵖ) :=
    { toFun := fun x i => op (x i)
      invFun := fun x i => unop (x i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [eOp.finrank_eq, Module.finrank_pi, Fintype.card_fin]
  exact hn

private theorem arithmetic_matrix_quadratic_vector (hF : IsCharacteristicTwoArithmeticField.{u,v} F)
    {n : ℕ} (hn : 4 < n) (H : Matrix (Fin n) (Fin n) F) :
    ∃ x : Fin n → F, x ≠ 0 ∧ x ⬝ᵥ (H *ᵥ x) = 0 := by
  let p : MvPolynomial (Fin n) F :=
    ∑ i, ∑ j, MvPolynomial.C (H i j) * MvPolynomial.X i * MvPolynomial.X j
  have hp : p.IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact (MvPolynomial.isHomogeneous_C_mul_X _ i).mul (MvPolynomial.isHomogeneous_X F j)
  have hs : ∃ x : Fin n → F, x ≠ 0 ∧ MvPolynomial.eval x p = 0 := by
    rcases hF with ⟨k, _, _, _, _⟩ | ⟨_, _, _⟩
    · exact FunctionFieldForms.global_bound (k := k) 2 (by decide) n (by omega) p hp
    · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact FunctionFieldForms.local_quadratic_bound F 2 n (by omega) p hp
  obtain ⟨x, hx, h0⟩ := hs
  refine ⟨x, hx, ?_⟩
  have he : MvPolynomial.eval x p = x ⬝ᵥ (H *ᵥ x) := by
    simp only [p, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ac_rfl
  exact he.symm.trans h0

private theorem nontrialitarian_isotropy_from_models (hmodel : NontrialitarianSpinModel.{u})
    (quat : ArithmeticQuaternionIsotropy.{u,v}) (split : ArithmeticSplitIsotropy.{u,v}) :
    NontrialitarianIsotropy.{u,v} := by
  intro F _ _ hF G n hn hsimple hsc htype
  obtain ⟨K, _, _, _, _, ρ, D, _, _, ⟨M⟩⟩ := hmodel F G n hn hsimple hsc htype
  obtain ⟨r, B, _, _, hB, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation
    F ρ.fixedSubalgebra D.centralSimple
  have hB' : _root_.Specs.RM03.CSA.isCentralSimple F B := ⟨inferInstance, hB.1, hB.2⟩
  obtain ⟨_, hdiv⟩ := division_degree_over_squares split_division_degree
    (arithmetic_square_degree hF) D.centralSimple hB' r hr e (toDivisionInvolution D.involution).anti
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hd | hd
  · obtain ⟨iso⟩ := SymplecticInvolutionModels.degreeOneDivision hB' hd
    let e' := e.trans iso.mapMatrix
    obtain ⟨hr', H, ell, q, hAdj, hEll, hTrace, hq, hpolar, hreg, _⟩ := split_pair_recovery D r e'
    have hn' : 8 ≤ r := by
      rw [hr']
      simpa only [Fintype.card_ulift, Fintype.card_fin] using (show 8 ≤ 2 * n by omega)
    exact (split hF M r hr' hn' e' H ell q hAdj hEll hTrace hq hpolar hreg).2
  · obtain ⟨P⟩ := quaternion_pair_recovery D hB' hd r e
    have hn' : 4 ≤ r := by simpa [P.rank] using hn
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, lift, _, _, hlift, _, _⟩ :=
      quat hF M hB' hd r hn' e P
    exact ⟨lift, hlift⟩

end ArithmeticIsotropy

section PairScaling

open scoped TensorProduct Matrix
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel symmetricPart IsPairIsometry)
open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (tensorMap)

variable {F K I : Type u} [Field F] [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}

private structure PlaneProjections (D : DescendedQuadraticPair ρ) where
  first : ρ.fixedSubalgebra
  second : ρ.fixedSubalgebra
  first_idempotent : first * first = first
  second_idempotent : second * second = second
  first_second : first * second = 0
  second_first : second * first = 0
  adjoint : D.involution.toLinearMap first = second

namespace PlaneProjections

variable {D : DescendedQuadraticPair ρ} (P : PlaneProjections D)

private def complement : ρ.fixedSubalgebra := 1 - P.first - P.second

private theorem second_adjoint : D.involution.toLinearMap P.second = P.first := by
  rw [← P.adjoint, D.involution.involutive]

private theorem complement_adjoint : D.involution.toLinearMap P.complement = P.complement := by
  rw [complement, map_sub, map_sub, D.involution.map_one, P.adjoint, P.second_adjoint]
  abel

private def parts : Fin 3 → ρ.fixedSubalgebra := ![P.first, P.second, P.complement]

private theorem parts_sum : ∑ j, P.parts j = 1 := by
  simp [parts, complement, Fin.sum_univ_three]

private theorem parts_orthogonal (i j : Fin 3) :
    P.parts i * P.parts j = if i = j then P.parts i else 0 := by
  have h1 : P.first * P.complement = 0 := by
    simp [complement, mul_sub, P.first_idempotent, P.first_second]
  have h2 : P.second * P.complement = 0 := by
    simp [complement, mul_sub, P.second_idempotent, P.second_first]
  have h3 : P.complement * P.first = 0 := by
    simp [complement, sub_mul, P.first_idempotent, P.second_first]
  have h4 : P.complement * P.second = 0 := by
    simp [complement, sub_mul, P.second_idempotent, P.first_second]
  have h5 : P.complement * P.complement = P.complement := by
    calc
      _ = (1 - P.first - P.second) * P.complement := rfl
      _ = _ := by rw [sub_mul, sub_mul, one_mul, h1, h2, sub_zero, sub_zero]
  fin_cases i <;> fin_cases j <;> simp [parts, P.first_idempotent, P.second_idempotent,
    P.first_second, P.second_first, h1, h2, h3, h4, h5]

private def partCoefficients {R : Type u} [CommRing R] (t : Rˣ) : Fin 3 → Rˣ := ![t, t⁻¹, 1]

private def scale (R : TestAlgebra F) (t : Rˣ) : R ⊗[F] ρ.fixedSubalgebra :=
  ∑ i, ((partCoefficients t i : Rˣ) : R) •
    Algebra.TensorProduct.includeRight (P.parts i)

private theorem scale_explicit (R : TestAlgebra F) (t : Rˣ) :
    P.scale R t = (t : R) ⊗ₜ[F] P.first + (↑t⁻¹ : R) ⊗ₜ[F] P.second +
      (1 : R) ⊗ₜ[F] P.complement := by
  simp [scale, Fin.sum_univ_three, parts, partCoefficients, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.smul_tmul', smul_eq_mul, add_assoc]

private theorem scale_one (R : TestAlgebra F) : P.scale R 1 = 1 := by
  rw [P.scale_explicit, inv_one]
  change (1 : R) ⊗ₜ[F] P.first + 1 ⊗ₜ[F] P.second + 1 ⊗ₜ[F] P.complement = 1
  rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add]
  simp [complement, Algebra.TensorProduct.one_def]

private theorem scale_mul (R : TestAlgebra F) (s t : Rˣ) :
    P.scale R (s * t) = P.scale R s * P.scale R t := by
  classical
  let j : ρ.fixedSubalgebra →ₐ[F] R ⊗[F] ρ.fixedSubalgebra := Algebra.TensorProduct.includeRight
  have hm (i : Fin 3) : partCoefficients (s * t) i = partCoefficients s i * partCoefficients t i := by
    fin_cases i <;> simp [partCoefficients, mul_comm]
  change (∑ i, ((partCoefficients (s * t) i : Rˣ) : R) • j (P.parts i)) =
    (∑ i, ((partCoefficients s i : Rˣ) : R) • j (P.parts i)) *
    (∑ i, ((partCoefficients t i : Rˣ) : R) • j (P.parts i))
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul_comm, ← map_mul j,
    P.parts_orthogonal, apply_ite j, map_zero, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, hm, Units.val_mul]

private def scaleUnits (R : TestAlgebra F) : Rˣ →* (R ⊗[F] ρ.fixedSubalgebra)ˣ where
  toFun t := ⟨P.scale R t, P.scale R t⁻¹, by rw [← P.scale_mul, mul_inv_cancel, P.scale_one],
    by rw [← P.scale_mul, inv_mul_cancel, P.scale_one]⟩
  map_one' := Units.ext (P.scale_one R)
  map_mul' s t := Units.ext (P.scale_mul R s t)

private theorem scale_natural (R S : TestAlgebra F) (a : R ⟶ S) (t : Rˣ) :
    Units.map (tensorMap ρ.fixedSubalgebra a.hom).toMonoidHom (P.scaleUnits R t) =
      P.scaleUnits S (Units.map a.hom.toMonoidHom t) := by
  apply Units.ext
  change tensorMap ρ.fixedSubalgebra a.hom (P.scale R t) =
    P.scale S (Units.map a.hom.toMonoidHom t)
  simp [P.scale_explicit, tensorMap, Algebra.TensorProduct.map_tmul]

private theorem scale_adjoint (R : TestAlgebra F) (t : Rˣ) :
    (D.involution.baseChange R).toLinearMap (P.scale R t) = P.scale R t⁻¹ := by
  simp only [P.scale_explicit, map_add, SymplecticIsometryDescent.Involution.baseChange_tmul,
    P.adjoint, P.second_adjoint, P.complement_adjoint, inv_inv]
  abel

private theorem part_commutes {ell : ρ.fixedSubalgebra} (h₁ : Commute P.first ell)
    (h₂ : Commute P.second ell) (i : Fin 3) : Commute (P.parts i) ell := by
  have h₃ : Commute P.complement ell := (Commute.one_left ell |>.sub_left h₁).sub_left h₂
  fin_cases i <;> assumption

private theorem scale_commutes (R : TestAlgebra F) (t : Rˣ) {ell : ρ.fixedSubalgebra}
    (h₁ : Commute P.first ell) (h₂ : Commute P.second ell) :
    Commute (P.scale R t) ((1 : R) ⊗ₜ[F] ell) := by
  unfold scale
  apply Commute.sum_left
  intro i _
  change Commute (((partCoefficients t i : Rˣ) : R) •
    ((1 : R) ⊗ₜ[F] P.parts i)) ((1 : R) ⊗ₜ[F] ell)
  have h := (P.part_commutes h₁ h₂ i).map (Algebra.TensorProduct.includeRight (R := F) (A := R))
  exact h.smul_left _

end PlaneProjections

open PlaneProjections

private def traceExtension (R : TestAlgebra F) {A : Type u} [Ring A] [Algebra F A]
    (tr : A →ₗ[F] F) : R ⊗[F] A →ₗ[R] R :=
  (TensorProduct.AlgebraTensorModule.rid F R R).toLinearMap.comp (tr.baseChange R)

private theorem traceExtension_tmul (R : TestAlgebra F) {A : Type u} [Ring A] [Algebra F A]
    (tr : A →ₗ[F] F) (r : R) (a : A) :
    traceExtension R tr (r ⊗ₜ[F] a) = r * algebraMap F R (tr a) := by
  simp [traceExtension, Algebra.smul_def, mul_comm]

private theorem traceExtension_cycle (R : TestAlgebra F) {A : Type u} [Ring A] [Algebra F A]
    (tr : A →ₗ[F] F) (h : ∀ a b, tr (a * b) = tr (b * a)) (x y : R ⊗[F] A) :
    traceExtension R tr (x * y) = traceExtension R tr (y * x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_mul, mul_add, map_add, ha, hb]
  | tmul r a =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => simp only [mul_add, add_mul, map_add, hc, hd]
    | tmul s b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, traceExtension_tmul, h a b, mul_comm r s]

variable {D : DescendedQuadraticPair ρ}

private theorem scalar_extended_symmetric {R : TestAlgebra F} {a : R ⊗[F] ρ.fixedSubalgebra}
    (h : (D.involution.baseChange R).toLinearMap a = a) :
    ∃ x, (symmetricPart D.involution).subtype.baseChange R x = a := by
  let f : ρ.fixedSubalgebra →ₗ[F] ρ.fixedSubalgebra := D.involution.toLinearMap - LinearMap.id
  have eq := Module.Flat.ker_lTensor_eq R R f
  change (f.baseChange R).ker = ((symmetricPart D.involution).subtype.baseChange R).range at eq
  apply (LinearMap.mem_range).mp
  rw [← eq, LinearMap.mem_ker]
  have hf : f.baseChange R = (D.involution.baseChange R).toLinearMap - LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    simp [f, SymplecticIsometryDescent.Involution.baseChange_tmul]
  simp [hf, h]

set_option maxHeartbeats 700000 in
private theorem scale_is_pair_isometry (P : PlaneProjections D)
    (ell : ρ.fixedSubalgebra)
    (hf : ∀ a : symmetricPart D.involution, D.semitrace a =
      algebraReducedTrace D.centralSimple (ell * a.val))
    (h₁ : Commute P.first ell) (h₂ : Commute P.second ell)
    (R : TestAlgebra F) (t : Rˣ) : IsPairIsometry D R (P.scaleUnits R t) := by
  obtain ⟨tr, htr, _, hcycle, _⟩ := reduced_trace_pairing D
  let z := P.scaleUnits R t
  let f := traceExtension R tr
  let L := (1 : R) ⊗ₜ[F] ell
  let J := (symmetricPart D.involution).subtype.baseChange R
  let adj := (D.involution.baseChange R).toLinearMap
  have hL : Commute z.val L := P.scale_commutes R t h₁ h₂
  have hz : adj z.val = z.inv := P.scale_adjoint R t
  have hz' : adj z.inv = z.val := by
    rw [← hz]
    exact (D.involution.baseChange R).involutive _
  have hF (x : R ⊗[F] symmetricPart D.involution) :
      TensorProduct.AlgebraTensorModule.rid F R R (D.semitrace.baseChange R x) = f (L * J x) := by
    induction x using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [map_add, mul_add, ha, hb]
    | tmul r a =>
      simp only [J, L, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      change TensorProduct.AlgebraTensorModule.rid F R R (r ⊗ₜ[F] D.semitrace a) =
        traceExtension R tr (r ⊗ₜ[F] (ell * a.val))
      rw [TensorProduct.AlgebraTensorModule.rid_tmul, traceExtension_tmul, hf, htr,
        Algebra.smul_def, mul_comm]
  have hJ (x : R ⊗[F] symmetricPart D.involution) : adj (J x) = J x := by
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r a =>
      have ha : D.involution.toLinearMap a.val = a.val := sub_eq_zero.mp a.prop
      simp [adj, J, SymplecticIsometryDescent.Involution.baseChange_tmul, ha]
  change adj z.val * z.val = 1 ∧ _
  refine ⟨by rw [hz, z.inv_val], ?_⟩
  intro x
  obtain ⟨y, hy⟩ := scalar_extended_symmetric (D := D) (R := R) (a := z.val * J x * z.inv) (by
    simp only [(D.involution.baseChange R).map_mul]
    change adj z.inv * (adj (J x) * adj z.val) = _
    rw [hz', hJ, hz, mul_assoc])
  refine ⟨y, hy, ?_⟩
  change J y = _ at hy
  change TensorProduct.AlgebraTensorModule.rid F R R (D.semitrace.baseChange R y) =
    TensorProduct.AlgebraTensorModule.rid F R R (D.semitrace.baseChange R x)
  rw [hF, hF, hy]
  calc
    _ = f (z.inv * (L * (z.val * J x))) := by
      rw [← mul_assoc]
      exact traceExtension_cycle R tr hcycle _ _
    _ = _ := by
      rw [← mul_assoc L z.val, ← hL.eq]
      simp only [← mul_assoc, z.inv_val, one_mul]

end PairScaling

section SpinLift
open scoped CategoryTheory.MonObj
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.AdjointCocharacters (powerOnGm)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F} (M : SpinModel G D)

private abbrev pointMap {X Y : GroupScheme F} (f : X ⟶ Y) (R : TestAlgebra F) :
    Points X.X R →* Points Y.X R := (((groupPointsFunctor F).map f).app R).hom

private theorem kernel_point_sq (R : TestAlgebra F) (z : Points M.kernel.group.X R) :
    z ^ 2 = 1 := by
  apply (M.kernelPoints R).injective
  rw [map_pow, map_one]
  apply Subtype.ext
  exact (M.kernelPoints R z).prop

private theorem eq_square_of_projection_eq (R : TestAlgebra F) (a b : Points G.val.X R)
    (hab : pointMap M.projection R a = pointMap M.projection R b) : a ^ 2 = b ^ 2 := by
  let z := a⁻¹ * b
  have hz : pointMap M.projection R z = 1 := by
    rw [show z = a⁻¹ * b from rfl, map_mul, map_inv, hab, inv_mul_cancel]
  let t := M.isKernel.lift z (toUnit _) hz
  have ht : pointMap M.kernel.inclusion R t = z := M.isKernel.lift_fst z (toUnit _) hz
  have hz₂ : z ^ 2 = 1 := by rw [← ht, ← map_pow, kernel_point_sq, map_one]
  obtain ⟨N, hN, hcen⟩ := M.centralIsogeny.2.2.2
  let v := hN.lift z (toUnit _) hz
  have hv : v ≫ N.inclusion.hom.hom = z := hN.lift_fst z (toUnit _) hz
  have hza : z * a * z⁻¹ = a := by
    have h := congrArg (fun f => lift a v ≫ f) hcen
    have hid : (𝟙 G.val : G.val ⟶ G.val).hom.hom = 𝟙 G.val.X := rfl
    simpa only [Centralizes, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv,
      Category.assoc, lift_fst_assoc, lift_snd_assoc, hv, hid, Category.comp_id, lift_fst] using h
  have hc : Commute a z := ((mul_inv_eq_iff_eq_mul).mp hza).symm
  have hbez : a * z = b := by simp [z]
  rw [← hbez, hc.mul_pow, hz₂, mul_one]

private theorem fourth_power_of_commuting_images (R : TestAlgebra F) (x y : Points G.val.X R)
    (h : Commute (pointMap M.projection R x) (pointMap M.projection R y)) :
    (x * y) ^ 4 = x ^ 4 * y ^ 4 := by
  let p := pointMap M.projection R
  have hc : p (MulAut.conj y x) = p x := by
    change p (y * x * y⁻¹) = _
    rw [map_mul, map_mul, map_inv, ← h.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconj := eq_square_of_projection_eq M R (MulAut.conj y x) x hc
  rw [← map_pow] at hconj
  have hcom : Commute (x ^ 2) y := ((mul_inv_eq_iff_eq_mul).mp hconj).symm
  have hxy : p ((x * y) ^ 2) = p (x ^ 2 * y ^ 2) := by
    simpa only [map_pow, map_mul] using h.mul_pow 2
  have ht := eq_square_of_projection_eq M R _ _ hxy
  change ((x * y) ^ 2) ^ 2 = (x ^ 2 * y ^ 2) ^ 2 at ht
  rw [(hcom.pow_right 2).mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at ht
  exact ht

open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

set_option maxHeartbeats 900000 in
/-- Squaring a lift of a point through the spin cover descends as a scheme map. -/
private theorem exists_spin_square_map :
    ∃ d : M.neutral.val.X ⟶ G.val.X,
      d ≫ M.projection.hom.hom = (𝟙 M.neutral.val.X) ^ 2 := by
  let H := M.neutral.val
  let p : G.val.X ⟶ H.X := M.projection.hom.hom
  let : IsAffine G.val.X.left := G.property.1
  let : IsAffine H.X.left := M.neutral.property.1
  let : IsFinite p.left := M.centralIsogeny.1
  let : Flat p.left := M.centralIsogeny.2.1
  let : Surjective p.left := M.centralIsogeny.2.2.1
  let : IsRegularEpi p.left := isRegularEpi_of_flat_of_surjective_of_isAffine p.left
  let X : SchemeOver F := Over.mk (pullback.fst p.left p.left ≫ G.val.X.hom)
  let a : X ⟶ G.val.X := Over.homMk (pullback.fst p.left p.left) rfl
  let b : X ⟶ G.val.X := Over.homMk (pullback.snd p.left p.left) (by
    change pullback.snd p.left p.left ≫ G.val.X.hom = pullback.fst p.left p.left ≫ G.val.X.hom
    rw [← Over.w p, pullback.condition_assoc])
  have h : a ≫ p = b ≫ p := by
    ext1
    exact pullback.condition
  let q : G.val.X ⟶ G.val.X := (𝟙 G.val.X) ^ 2
  have hf : a ≫ q = b ≫ q := by
    apply hom_ext_of_points (by
      change IsAffine (pullback p.left p.left)
      infer_instance)
    intro R x
    simp only [q, MonObj.comp_pow, Category.comp_id]
    apply eq_square_of_projection_eq M R
    exact (Category.assoc x a p).symm.trans ((congrArg (x ≫ ·) h).trans (Category.assoc x b p))
  have hf' : pullback.fst p.left p.left ≫ q.left = pullback.snd p.left p.left ≫ q.left :=
    congrArg (fun x => x.left) hf
  obtain ⟨d, hd⟩ := IsRegularEpi.exists_of_isKernelPair p.left
    (IsKernelPair.of_hasPullback p.left) q.left hf'
  let : Epi p.left := Flat.epi_of_flat_of_surjective _
  let d' : H.X ⟶ G.val.X := Over.homMk d (by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, hd, Over.w, Over.w p])
  have hd' : p ≫ d' = q := by
    ext1
    exact hd
  let : Epi p := (Over.forget _).epi_of_epi_map (f := p) ‹Epi p.left›
  refine ⟨d', (cancel_epi p).mp ?_⟩
  rw [← Category.assoc, hd', MonObj.comp_pow, Category.comp_id]
  change ((𝟙 G.val.X : G.val.X ⟶ G.val.X) ^ (2 : ℕ)) ≫ M.projection.hom.hom = p ^ 2
  rw [MonObj.pow_comp, Category.id_comp]

open private pointsIso_precompose from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private abbrev gm (F : Type u) [Field F] := specGroup (groupAlgebra F IntegerCharacters.{u})

private theorem power_point (j : ℕ) (R : TestAlgebra F) (x : Points (gm F).X R) :
    pointMap (powerOnGm F j) R x = x ^ j := by
  let A := DiagonalizableGroups.groupAlgebraPointsIso F IntegerCharacters.{u}
  let E : Points (gm F).X R ≃* (IntegerCharacters.{u} →* Rˣ) := (A.app R).groupIsoToMulEquiv
  apply E.injective
  apply MonoidHom.ext
  intro m
  have he := pointsIso_precompose (powMonoidHom (α := IntegerCharacters.{u}) j) R x m
  refine he.trans ?_
  change E x (m ^ j) = _
  rw [map_pow E, map_pow]
  rfl

set_option maxHeartbeats 750000 in
private theorem lift_spin_cocharacter (c : Cocharacter M.neutral.val) :
    ∃ lift : Cocharacter G.val, lift ≫ M.projection = powerOnGm F 8 ≫ c := by
  obtain ⟨d, hd⟩ := exists_spin_square_map M
  let L := gm F
  have hL : IsAffine L.X.left := by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters.{u})))
    infer_instance
  let f : L.X ⟶ G.val.X := c.hom.hom ≫ d
  have hv (R : TestAlgebra F) (x : Points L.X R) :
      pointMap M.projection R (x ≫ f) = (pointMap c R x) ^ 2 := by
    change (x ≫ f) ≫ M.projection.hom.hom = _
    simp only [f, Category.assoc, hd, MonObj.comp_pow, Category.comp_id]
    rfl
  let a : (groupPointsFunctor F).obj L ⟶ (groupPointsFunctor F).obj G.val := {
    app R := GrpCat.ofHom {
      toFun x := (x ≫ f) ^ 4
      map_one' := by
        have hp : pointMap M.projection R ((1 : Points L.X R) ≫ f) = pointMap M.projection R 1 := by
          rw [hv, map_one, map_one, one_pow]
        have h := eq_square_of_projection_eq M R _ _ hp
        rw [one_pow] at h
        change ((1 : Points L.X R) ≫ f) ^ 4 = 1
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, h, one_pow]
      map_mul' x y := by
        have hcomm : Commute (pointMap c R x) (pointMap c R y) :=
          (Commute.all x y).map (pointMap c R)
        have he : pointMap M.projection R ((x * y) ≫ f) =
            pointMap M.projection R ((x ≫ f) * (y ≫ f)) := by
          rw [map_mul, hv, hv, hv, map_mul, hcomm.mul_pow]
        have hh := eq_square_of_projection_eq M R _ _ he
        have hpowcomm : Commute (pointMap M.projection R (x ≫ f)) (pointMap M.projection R (y ≫ f)) := by
          rw [hv, hv]
          exact (hcomm.pow_left 2).pow_right 2
        change ((x * y) ≫ f) ^ 4 = (x ≫ f) ^ 4 * (y ≫ f) ^ 4
        calc
          _ = ((x ≫ f) * (y ≫ f)) ^ 4 := by
            rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_mul, hh]
          _ = _ := fourth_power_of_commuting_images M R _ _ hpowcomm
      }
    naturality R S j := by
      apply GrpCat.ext
      intro x
      change ((testSpec F).map j.op ≫ x ≫ f) ^ 4 =
        (testSpec F).map j.op ≫ (x ≫ f) ^ 4
      simp only [MonObj.comp_pow] }
  let l := (groupHomEquiv L G.val hL).symm a
  have hl : (groupPointsFunctor F).map l = a :=
    (groupHomEquiv L G.val hL).apply_symm_apply a
  refine ⟨l, (groupHomComparison F L M.neutral.val hL).1 ?_⟩
  ext R x
  change Points L.X R at x
  change pointMap M.projection R (pointMap l R x) =
    pointMap c R (pointMap (powerOnGm F 8) R x)
  rw [show pointMap l R x = (x ≫ f) ^ 4 by
    exact DFunLike.congr_fun (congrArg (fun t => (t.app R).hom) hl) x,
    map_pow, hv, ← pow_mul]
  have hpow := power_point (F := F) 8 R x
  rw [hpow, map_pow]

end SpinLift

section ScalingCocharacter

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.SemiCartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.Specs.AdjointCocharacters (powerOnGm)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (IntegerCharacters)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel symmetricPart)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint cocharacterPoint mapPoints_unitPoint)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open PlaneProjections

open private unitEquiv unitEquiv_unitPoint unitPointHom unitPointHom_apply
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private splitTorus_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private multiplicative_group_iso from LinearAlgebraicGroups.Relative.LeviConjugacy
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private powerOnGm_epi from LinearAlgebraicGroups.Descent.RelativeRank

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F} (M : SpinModel G D)

set_option maxHeartbeats 900000 in
private theorem scale_cocharacter (P : PlaneProjections D)
    (ell : ρ.fixedSubalgebra)
    (hf : ∀ a : symmetricPart D.involution, D.semitrace a =
      algebraReducedTrace D.centralSimple (ell * a.val))
    (h₁ : Commute P.first ell) (h₂ : Commute P.second ell) :
    ∃ c : Cocharacter M.neutral.val, ∀ (R : TestAlgebra F) (t : Rˣ),
      M.fullPoints R ((cocharacterPoint c R t) ≫ M.inclusion.hom.hom) = P.scaleUnits R t := by
  classical
  have hs (R : TestAlgebra F) (t : Rˣ) : P.scaleUnits R t ∈ Set.range (M.fullPoints R) :=
    (M.fullRange R _).mpr (scale_is_pair_isometry P ell hf h₁ h₂ R t)
  choose a ha using hs
  let aHom (R : TestAlgebra F) : Rˣ →* Points M.full.val.X R := {
    toFun := a R
    map_one' := M.fullFaithful R (by rw [ha, map_one, map_one])
    map_mul' s t := M.fullFaithful R (by rw [ha, map_mul, map_mul, ha, ha]) }
  let L := gm F
  have hLa : IsAffine L.X.left := by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters.{u})))
    infer_instance
  let α : (groupPointsFunctor F).obj L ⟶ (groupPointsFunctor F).obj M.full.val := {
    app R := GrpCat.ofHom ((aHom R).comp (unitEquiv R).toMonoidHom)
    naturality R S f := by
      apply GrpCat.ext
      intro x
      change Points L.X R at x
      obtain ⟨t, rfl⟩ := (unitEquiv R).symm.surjective x
      change a S (unitEquiv S (mapPoints f ((unitEquiv R).symm t))) =
        mapPoints f (a R (unitEquiv R ((unitEquiv R).symm t)))
      change a S (unitEquiv S (mapPoints f (unitPointHom R t))) = _
      rw [unitPointHom_apply, mapPoints_unitPoint, unitEquiv_unitPoint, MulEquiv.apply_symm_apply]
      apply M.fullFaithful S
      rw [M.fullNatural, ha, ha]
      exact (P.scale_natural R S f t).symm }
  let cFull := (groupHomEquiv L M.full.val hLa).symm α
  have hcFull : (groupPointsFunctor F).map cFull = α :=
    (groupHomEquiv L M.full.val hLa).apply_symm_apply α
  have hL : ConnectedSpace L.X.left := splitTorus_connected (T := L) ⟨1, multiplicative_group_iso⟩
  have hcRange : Set.range cFull.hom.hom.left ⊆ Set.range M.inclusion.hom.hom.left := by
    rw [M.identityComponent]
    apply (isPreconnected_range cFull.hom.hom.left.continuous).subset_connectedComponent
    let b := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of F)))
    refine ⟨η[L.X].left b, ?_⟩
    have hcomp : η[L.X] ≫ cFull.hom.hom = η[M.full.val.X] := IsMonHom.one_hom _
    exact congrArg (fun f : (𝟙_ (SchemeOver F)) ⟶ M.full.val.X => f.left b) hcomp
  let : IsOpenImmersion M.inclusion.hom.hom.left := M.openImmersion
  let d := IsOpenImmersion.lift M.inclusion.hom.hom.left cFull.hom.hom.left hcRange
  let d' : L.X ⟶ M.neutral.val.X := Over.homMk d (by
    rw [← Over.w M.inclusion.hom.hom, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  let N : ClosedSubgroup M.full.val := ⟨M.neutral.val, M.inclusion, M.closedImmersion⟩
  obtain ⟨c, hc⟩ := factor_group_through_subgroup N cFull d' (by
    ext1
    exact IsOpenImmersion.lift_fac _ _ _)
  refine ⟨c, fun R t => ?_⟩
  have hp : ((cocharacterPoint c R t) ≫ M.inclusion.hom.hom) = pointMap cFull R (unitPoint R t) := by
    change pointMap (c ≫ N.inclusion) R (unitPoint R t) = _
    rw [hc]
  have hpt : pointMap cFull R (unitPoint R t) = a R (unitEquiv R (unitPoint R t)) :=
    DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) hcFull) _
  rw [hp, hpt, unitEquiv_unitPoint, ha]

private theorem scale_cocharacter_nonzero (P : PlaneProjections D) (hp : P.first ≠ 0)
    (c : Cocharacter M.neutral.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      M.fullPoints R ((cocharacterPoint c R t) ≫ M.inclusion.hom.hom) = P.scaleUnits R t) :
    c ≠ 0 := by
  intro h
  let R : TestAlgebra F := CommAlgCat.of F F⟮X⟯
  let t : Rˣ := Units.mk0 (RatFunc.X : F⟮X⟯) RatFunc.X_ne_zero
  let a : Points (gm F).X R := unitPoint R t
  have hpt : pointMap c R a = (1 : Points M.neutral.val.X R) := by
    rw [h]
    change a ≫ toUnit (gm F).X ≫ η[M.neutral.val.X] =
      toUnit ((testSpec F).obj (Opposite.op R)) ≫ η[M.neutral.val.X]
    rw [← Category.assoc]
    exact congrArg (· ≫ η[M.neutral.val.X])
      (toUnit_unique (a ≫ toUnit (gm F).X) (toUnit ((testSpec F).obj (Opposite.op R))))
  have hScale : P.scale R t = 1 := by
    have ht := hc R t
    change M.fullPoints R (pointMap M.inclusion R (pointMap c R a)) = _ at ht
    rw [hpt, map_one, map_one] at ht
    exact congrArg Units.val ht.symm
  have hcomp : P.complement * P.first = 0 := by
    simp [PlaneProjections.complement, sub_mul, P.first_idempotent, P.second_first]
  have hs := congrArg (fun x : R ⊗[F] ρ.fixedSubalgebra => x * ((1 : R) ⊗ₜ[F] P.first)) hScale
  simp only [P.scale_explicit, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    P.first_idempotent, P.second_first, hcomp, TensorProduct.tmul_zero, add_zero, one_mul] at hs
  have ht' : (t : R) ≠ 1 := by
    intro he
    change (RatFunc.X : F⟮X⟯) = 1 at he
    have hd := congrArg (RatFunc.intDegree (K := F)) he
    rw [RatFunc.intDegree_X, RatFunc.intDegree_one] at hd
    omega
  have hz : ((t : R) - 1) • ((1 : R) ⊗ₜ[F] P.first) = 0 := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.sub_tmul, hs, sub_self]
  have hzero := ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ht'))
  exact hp ((Algebra.TensorProduct.includeRight_injective (B := ρ.fixedSubalgebra)
    (algebraMap F R).injective) (hzero.trans (map_zero _).symm))

private theorem lift_spin_cocharacter_nonzero (c : Cocharacter M.neutral.val) (hc : c ≠ 0) :
    ∃ l : Cocharacter G.val, l ≠ 0 ∧ l ≫ M.projection = powerOnGm F 8 ≫ c := by
  obtain ⟨l, hl⟩ := lift_spin_cocharacter M c
  refine ⟨l, fun h => hc ?_, hl⟩
  let : Epi (powerOnGm F 8) := powerOnGm_epi (k := F) 8 (by decide)
  apply (cancel_epi (powerOnGm F 8)).mp
  rw [← hl, h, zero_comp, comp_zero]

end ScalingCocharacter

section HyperbolicPlane

open Matrix
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair symmetricPart)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (Involution dagger hermitianValue)
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open PlaneProjections

variable {F K I : Type u} [Field F] [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {B : Type u} [DivisionRing B] [Algebra F B]
  {n : ℕ} (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B)

private theorem matrix_ext_of_mulVec {X Y : Matrix (Fin n) (Fin n) B}
    (h : ∀ v, X *ᵥ v = Y *ᵥ v) : X = Y := by
  ext i j
  have hv := congrFun (h (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hv

private theorem pairing_right_separates {s : AntiAutomorphism F B}
    (h : HermitianPairing s (Fin n → B)) {x y : Fin n → B}
    (he : ∀ v, h.value v x = h.value v y) : x = y := by
  by_contra hn
  obtain ⟨v, hv⟩ := h.nondegenerate (x - y) (sub_ne_zero.mpr hn)
  apply hv
  rw [h.hermitian]
  have hsub : h.value v (x - y) = 0 := by
    rw [show h.value v (x - y) = h.value v x - h.value v y from (pairingRight h v).map_sub x y,
      he, sub_self]
  rw [hsub]
  exact congrArg unop (s.map_zero)

private theorem pairing_right_projection {s : AntiAutomorphism F B}
    (H : (Matrix (Fin n) (Fin n) B)ˣ) (x y v : Fin n → B) :
    vecMulVec x ((fun i => antiValue s (y i)) ᵥ* H.val) *ᵥ v =
      op (hermitianValue s H.val y v) • x := by
  rw [Matrix.vecMulVec_mulVec, ← dotProduct_mulVec]
  rfl

/-- The two rank-one projections obtained by pairing with the opposite line. -/
private theorem hyperbolic_projections (s : AntiAutomorphism F B)
    (H : (Matrix (Fin n) (Fin n) B)ˣ)
    (h : HermitianPairing s (Fin n → B)) (hh : h.value = hermitianValue s H.val)
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * dagger s (e a) * H.val)
    (x y : Fin n → B)
    (hxx : h.value x x = 0) (hyy : h.value y y = 0)
    (hxy : h.value x y = 1) (hyx : h.value y x = 1) :
    ∃ P : PlaneProjections D,
      (∀ v, e P.first *ᵥ v = op (h.value y v) • x) ∧
      (∀ v, e P.second *ᵥ v = op (h.value x v) • y) := by
  let A := vecMulVec x ((fun i => antiValue s (y i)) ᵥ* H.val)
  let C := vecMulVec y ((fun i => antiValue s (x i)) ᵥ* H.val)
  let a := e.symm A
  let b := e.symm C
  have ha (v : Fin n → B) : e a *ᵥ v = op (h.value y v) • x := by
    rw [show e a = A from e.apply_symm_apply A, hh]
    exact pairing_right_projection (s := s) H x y v
  have hb (v : Fin n → B) : e b *ᵥ v = op (h.value x v) • y := by
    rw [show e b = C from e.apply_symm_apply C, hh]
    exact pairing_right_projection (s := s) H y x v
  refine ⟨⟨a, b, ?_, ?_, ?_, ?_, ?_⟩, ha, hb⟩
  · apply e.injective
    rw [map_mul]
    apply matrix_ext_of_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, ha, ha, h.smul_right, hyx, one_mul]
  · apply e.injective
    rw [map_mul]
    apply matrix_ext_of_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, hb, hb, h.smul_right, hxy, one_mul]
  · apply e.injective
    rw [map_mul, map_zero]
    apply matrix_ext_of_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hb, ha, h.smul_right, hyy, zero_mul, op_zero, zero_smul]
  · apply e.injective
    rw [map_mul, map_zero]
    apply matrix_ext_of_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, ha, hb, h.smul_right, hxx, zero_mul, op_zero, zero_smul]
  · apply e.injective
    apply matrix_ext_of_mulVec
    intro v
    apply pairing_right_separates h
    intro w
    calc
      _ = h.value (e a *ᵥ w) v := by rw [hh, hσ, column_adjoint]
      _ = _ := by
        rw [ha, hb, h.smul_right, pairing_left_smul, h.hermitian y w]
        rfl

private theorem complement_column (P : PlaneProjections D) (v : Fin n → B) :
    e P.complement *ᵥ v = v - e P.first *ᵥ v - e P.second *ᵥ v := by
  rw [PlaneProjections.complement, map_sub, map_sub, map_one, sub_mulVec, sub_mulVec, one_mulVec]

private theorem projected_orthogonal {s : AntiAutomorphism F B}
    (h : HermitianPairing s (Fin n → B)) (P : PlaneProjections D) {x y : Fin n → B}
    (hxx : h.value x x = 0) (hyy : h.value y y = 0)
    (hxy : h.value x y = 1) (hyx : h.value y x = 1)
    (ha : ∀ v, e P.first *ᵥ v = op (h.value y v) • x)
    (hb : ∀ v, e P.second *ᵥ v = op (h.value x v) • y)
    (v : Fin n → B) : IsHyperbolicComplement h x y (e P.complement *ᵥ v) := by
  rw [complement_column, ha, hb]
  constructor
  · change pairingRight h x _ = _
    rw [map_sub, map_sub]
    change h.value x v - h.value x (op (h.value y v) • x) -
      h.value x (op (h.value x v) • y) = 0
    rw [h.smul_right, h.smul_right, hxx, hxy, zero_mul, one_mul, sub_zero, sub_self]
  · change pairingRight h y _ = _
    rw [map_sub, map_sub]
    change h.value y v - h.value y (op (h.value y v) • x) -
      h.value y (op (h.value x v) • y) = 0
    rw [h.smul_right, h.smul_right, hyy, hyx, zero_mul, one_mul, sub_self, sub_zero]

private theorem projections_reconstruct {s : AntiAutomorphism F B}
    (h : HermitianPairing s (Fin n → B)) (P : PlaneProjections D) {x y : Fin n → B}
    (ha : ∀ v, e P.first *ᵥ v = op (h.value y v) • x)
    (hb : ∀ v, e P.second *ᵥ v = op (h.value x v) • y)
    (v : Fin n → B) :
    v = op (h.value y v) • x + (e P.complement *ᵥ v) + op (h.value x v) • y := by
  rw [complement_column, ha, hb]
  abel

private def compressedRepresentative (P : PlaneProjections D) (ell : ρ.fixedSubalgebra) :
    ρ.fixedSubalgebra := P.second + P.complement * ell * P.complement

private theorem compressed_commutes (P : PlaneProjections D) (ell : ρ.fixedSubalgebra) :
    Commute P.first (compressedRepresentative P ell) ∧
      Commute P.second (compressedRepresentative P ell) := by
  have h₁ : P.first * P.complement = 0 := by
    simp [PlaneProjections.complement, mul_sub, P.first_idempotent, P.first_second]
  have h₂ : P.second * P.complement = 0 := by
    simp [PlaneProjections.complement, mul_sub, P.second_idempotent, P.second_first]
  have h₃ : P.complement * P.first = 0 := by
    simp [PlaneProjections.complement, sub_mul, P.first_idempotent, P.second_first]
  have h₄ : P.complement * P.second = 0 := by
    simp [PlaneProjections.complement, sub_mul, P.second_idempotent, P.first_second]
  have hm (a : ρ.fixedSubalgebra) (hl : a * P.complement = 0) (hr : P.complement * a = 0) :
      Commute a (P.complement * ell * P.complement) := by
    change a * (P.complement * ell * P.complement) = (P.complement * ell * P.complement) * a
    rw [← mul_assoc a, ← mul_assoc a, hl, zero_mul, zero_mul, mul_assoc _ P.complement, hr, mul_zero]
  exact ⟨(show Commute P.first P.second from P.first_second.trans P.second_first.symm).add_right
      (hm _ h₁ h₃), (Commute.refl P.second).add_right (hm _ h₂ h₄)⟩

private theorem compressed_trace_one (P : PlaneProjections D) (ell : ρ.fixedSubalgebra)
    (hell : ell + D.involution.toLinearMap ell = 1) :
    compressedRepresentative P ell + D.involution.toLinearMap (compressedRepresentative P ell) = 1 := by
  let r := P.complement
  have hr : r * r = r := by
    have ht := P.parts_orthogonal 2 2
    change r * r = if (2 : Fin 3) = 2 then r else 0 at ht
    simpa using ht
  unfold compressedRepresentative
  rw [map_add, D.involution.map_mul, D.involution.map_mul,
    P.second_adjoint, P.complement_adjoint]
  change P.second + r * ell * r + (P.first + r * (D.involution.toLinearMap ell * r)) = 1
  rw [← mul_assoc r]
  have hsum : r * ell * r + r * D.involution.toLinearMap ell * r = r := by
    rw [← add_mul, ← mul_add, hell, mul_one, hr]
  calc
    _ = P.first + P.second + (r * ell * r + r * D.involution.toLinearMap ell * r) := by abel
    _ = _ := by rw [hsum]; simp [r, PlaneProjections.complement]

private theorem compressed_diagonal (s : AntiAutomorphism F B)
    (H : (Matrix (Fin n) (Fin n) B)ˣ)
    (h : HermitianPairing s (Fin n → B)) (hh : h.value = hermitianValue s H.val)
    (hσ : ∀ a, e (D.involution.toLinearMap a) = H.inv * dagger s (e a) * H.val)
    (P : PlaneProjections D) (ell : ρ.fixedSubalgebra) (v : Fin n → B) {x y : Fin n → B}
    (hb : ∀ v, e P.second *ᵥ v = op (h.value x v) • y) :
    h.value v (e (compressedRepresentative P ell) *ᵥ v) =
      antiValue s (h.value y v) * h.value x v +
        h.value (e P.complement *ᵥ v) (e ell *ᵥ (e P.complement *ᵥ v)) := by
  have hm (a b : Fin n → B) : h.value (e P.complement *ᵥ a) b =
      h.value a (e P.complement *ᵥ b) := by
    rw [hh, column_adjoint, ← hσ, P.complement_adjoint]
  unfold compressedRepresentative
  rw [map_add, Matrix.add_mulVec, h.add_right, hb, h.smul_right, h.hermitian y v]
  simp only [map_mul, ← Matrix.mulVec_mulVec]
  rw [← hm]
  rfl

end HyperbolicPlane

section ArithmeticCocharacters

open Matrix CategoryTheory
open RM03.Brauer.SemilinearDescent (AlgebraAction)
open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair symmetricPart SpinModel)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (Involution dagger hermitianValue intoTensor)
open PlaneProjections

variable {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ}

private theorem trace_one_difference {a b : ρ.fixedSubalgebra}
    (ha : a + D.involution.toLinearMap a = 1)
    (hb : b + D.involution.toLinearMap b = 1) :
    D.involution.toLinearMap (a - b) = a - b := by
  let : IsSimpleRing ρ.fixedSubalgebra := D.centralSimple.1
  let : CharP ρ.fixedSubalgebra 2 := charP_of_injective_ringHom (algebraMap F ρ.fixedSubalgebra).injective 2
  rw [map_sub, show D.involution.toLinearMap a = 1 - a from eq_sub_of_add_eq' ha,
    show D.involution.toLinearMap b = 1 - b from eq_sub_of_add_eq' hb]
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  calc
    _ = (1 + 1) + (a + b) := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

private theorem semitrace_replacement {a b : ρ.fixedSubalgebra}
    (h : ∀ y : symmetricPart D.involution,
      D.semitrace y = algebraReducedTrace D.centralSimple (a * y.val))
    (hab : ∃ z, b - a = z + D.involution.toLinearMap z) :
    ∀ y : symmetricPart D.involution, D.semitrace y = algebraReducedTrace D.centralSimple (b * y.val) := by
  obtain ⟨tr, htr, _, _, _⟩ := reduced_trace_pairing D
  intro y
  have hy := (semitrace_equivalence D (b - a)).mpr hab y
  rw [sub_mul, ← htr, map_sub, sub_eq_zero, htr, htr] at hy
  exact (h y).trans hy.symm

omit [CharP F 2] in
private theorem first_projection_ne_zero {B : Type u} [DivisionRing B] [Algebra F B] {n : ℕ}
    (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) B)
    (P : PlaneProjections D) {x : Fin n → B} (hx : x ≠ 0) (ht : e P.first *ᵥ x = x) :
    P.first ≠ 0 := by
  intro hp
  rw [hp, map_zero, Matrix.zero_mulVec] at ht
  exact hx ht.symm

set_option maxHeartbeats 900000 in
private theorem arithmetic_quaternion_isotropy : ArithmeticQuaternionIsotropy.{u,v} := by
  intro F K I _ _ _ _ _ _ hF ρ D G M B _ _ hB hd n hn e P
  obtain ⟨x, hx, hqx⟩ := arithmetic_quaternion_vector hF hB hd hn P
  obtain ⟨y, hqy, hxx, hyy, hxy, hyx, hcoord, hformula⟩ :=
    refinement_hyperbolic_pair hB hd P.bar.anti P.canonical P.pairing P.ellAction P.pairingTraceOne x hx hqx
  obtain ⟨A, hAx, hAy⟩ := hyperbolic_projections e P.bar.anti P.gram P.pairing
    P.pairingFormula P.adjointFormula x y hxx hyy hxy hyx
  let ell := compressedRepresentative A P.ell
  have htrace : ell + D.involution.toLinearMap ell = 1 := compressed_trace_one A P.ell P.ellTraceOne
  have hδ : D.involution.toLinearMap (ell - P.ell) = ell - P.ell :=
    trace_one_difference htrace P.ellTraceOne
  obtain ⟨_, _, _, _, htr⟩ := SymplecticInvolutionModels.quaternionConjugation.{u,u,u} hB hd
  have hAlt : ∃ z, ell - P.ell = z + D.involution.toLinearMap z := by
    apply (quaternion_alternating_iff D hB e P.bar P.gram P.gramHermitian P.adjointFormula
      P.canonical htr hδ).mp
    intro v
    let w := e A.complement *ᵥ v
    have hW : IsHyperbolicComplement P.pairing x y w := projected_orthogonal e P.pairing A
      hxx hyy hxy hyx hAx hAy v
    have hq := hformula (P.pairing.value y v) (P.pairing.value x v) w hW
    rw [← projections_reconstruct e P.pairing A hAx hAy v] at hq
    have hc := compressed_diagonal e P.bar.anti P.gram P.pairing P.pairingFormula
      P.adjointFormula A P.ell v hAy
    change P.pairing.value v (e ell *ᵥ v) = _ at hc
    simp only [refinement, P.ellActionFormula] at hq
    rw [diagonal_sub D e P.bar.anti P.gram, map_sub, ← P.pairingFormula, hc, map_add, ← hq, sub_self]
  have hnew := semitrace_replacement P.semitraceFormula hAlt
  obtain ⟨hComm1, hComm2⟩ := compressed_commutes A P.ell
  obtain ⟨c, hc⟩ := scale_cocharacter M A ell hnew hComm1 hComm2
  have hfirst : e A.first *ᵥ x = x := by rw [hAx, hyx, op_one, one_smul]
  have hzero : c ≠ 0 := scale_cocharacter_nonzero M A (first_projection_ne_zero e A hx hfirst) c hc
  obtain ⟨lift, hlift, hproj⟩ := lift_spin_cocharacter_nonzero M c hzero
  refine ⟨x, y, hx, hqx, hqy, hxx, hyy, hxy, hyx, hcoord, hformula,
    c, 8, lift, hzero, by decide, hlift, hproj, ?_⟩
  intro R t
  let E := fun v : Fin n → B => fun i => (1 : R) ⊗ₜ[F] v i
  have hM (a : ρ.fixedSubalgebra) (v : Fin n → B) :
      (e a).map (intoTensor R B) *ᵥ E v = E (e a *ᵥ v) := by
    funext i
    let j : B →ₐ[F] R ⊗[F] B := intoTensor R B
    change ((e a).map j *ᵥ (fun i => j (v i))) i = j ((e a *ᵥ v) i)
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, map_sum, map_mul]
  have hE0 : E 0 = 0 := by
    ext i
    simp [E]
  have hscale (v : Fin n → B) :
      P.scalarExtension R (A.scale R t) *ᵥ E v =
      (t : R) • E (e A.first *ᵥ v) + (↑t⁻¹ : R) • E (e A.second *ᵥ v) +
        E (e A.complement *ᵥ v) := by
    rw [A.scale_explicit]
    simp only [map_add, P.scalarExtensionFormula, Matrix.add_mulVec, Matrix.smul_mulVec, hM, one_smul]
  rw [hc]
  change (P.scalarExtension R (A.scale R t) *ᵥ E x = _) ∧
    (P.scalarExtension R (A.scale R t) *ᵥ E y = _) ∧
    ∀ w, IsHyperbolicComplement P.pairing x y w →
      P.scalarExtension R (A.scale R t) *ᵥ E w = E w
  have hx2 : e A.second *ᵥ x = 0 := by rw [hAy, hxx, op_zero, zero_smul]
  have hy1 : e A.first *ᵥ y = 0 := by rw [hAx, hyy, op_zero, zero_smul]
  have hy2 : e A.second *ᵥ y = y := by rw [hAy, hxy, op_one, one_smul]
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · rw [hscale, complement_column, hfirst, hx2, sub_self, sub_zero, hE0, smul_zero, add_zero, add_zero]
  · rw [hscale, complement_column, hy1, hy2, sub_zero, sub_self, hE0, smul_zero, zero_add, add_zero]
  · obtain ⟨hwx, hwy⟩ := hw
    rw [hscale, complement_column, hAx w, hAy w, hwx, hwy, op_zero, zero_smul, zero_smul,
      sub_zero, sub_zero, hE0, smul_zero, smul_zero, zero_add, zero_add]

open private hermitianValue_laws hermitianValue_single hermitianValue_nondegenerate
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

set_option maxHeartbeats 950000 in
private theorem arithmetic_split_isotropy : ArithmeticSplitIsotropy.{u,v} := by
  intro F K I _ _ _ _ _ _ hF ρ D G M n _ hn e H ell q hσ hEll hTrace hq hPol hReg
  obtain ⟨x, hx, h0⟩ := arithmetic_matrix_quadratic_vector hF (by omega : 4 < n) (H.val * e ell)
  have hqx : q x = 0 := by rw [hq, Matrix.mulVec_mulVec, h0]
  let b := scalarConjugation F
  have hGram (x y : Fin n → F) : q.polarBilin x y = hermitianValue b.anti H.val x y := by
    rw [hPol, Matrix.toLinearMap₂'_apply']
    rfl
  have hH : dagger b.anti H.val = H.val := by
    ext i j
    change H.val j i = H.val i j
    rw [← hermitianValue_single b.anti H.val j i, ← hermitianValue_single b.anti H.val i j, ← hGram, ← hGram]
    exact QuadraticMap.polar_comm _ _ _
  have hL := hermitianValue_laws b.anti b.square H.val hH
  let h : HermitianPairing b.anti (Fin n → F) :=
    ⟨hermitianValue b.anti H.val, hL.add_right, hL.mul_right, hL.symmetric,
      hermitianValue_nondegenerate b.anti H, fun z => ⟨_, rfl⟩⟩
  have hP (u v : Fin n → F) : q.polarBilin u v = h.value u v := hGram u v
  have hqs (u : Fin n → F) : q u = h.value u (e ell *ᵥ u) := hq u
  have hsym (u v : Fin n → F) : h.value u v = h.value v u := h.hermitian v u
  have hal (u : Fin n → F) : h.value u u = 0 := by
    rw [← hP, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, CharTwo.two_nsmul]
  have hAdd (u v : Fin n → F) : q (u + v) = q u + q v + h.value u v :=
    (QuadraticMap.map_add (⇑q) u v).trans (congrArg (q u + q v + ·) (hP u v))
  have hScale (a : F) (u : Fin n → F) : q (op a • u) = a * a * q u := by
    have he : op a • u = a • u := funext fun i => mul_comm (u i) a
    rw [he, q.map_smul, smul_eq_mul]
  obtain ⟨y', hy'⟩ := h.nondegenerate x hx
  let y₀ := op (h.value x y')⁻¹ • y'
  have hxy₀ : h.value x y₀ = 1 := by
    change h.value x (op (h.value x y')⁻¹ • y') = 1
    rw [h.smul_right, mul_inv_cancel₀ hy']
  let y := y₀ + op (q y₀) • x
  have hxy : h.value x y = 1 := by
    simp only [y, h.add_right, h.smul_right, hxy₀, hal, zero_mul, add_zero]
  have hyx : h.value y x = 1 := (hsym y x).trans hxy
  have hqy : q y = 0 := by
    change q (y₀ + op (q y₀) • x) = 0
    rw [hAdd, hScale (q y₀) x, hqx, mul_zero, add_zero, h.smul_right, hsym y₀ x, hxy₀, one_mul,
      CharTwo.add_self_eq_zero]
  obtain ⟨P, hPx, hPy⟩ := hyperbolic_projections e b.anti H h rfl hσ x y (hal x) (hal y) hxy hyx
  let ell' := compressedRepresentative P ell
  have htrace : ell' + D.involution.toLinearMap ell' = 1 := compressed_trace_one P ell hEll
  have hAlt : ∃ z, ell' - ell = z + D.involution.toLinearMap z := by
    apply alternating_of_diagonal D e b H hH hσ (trace_one_difference htrace hEll)
    intro v
    let w := e P.complement *ᵥ v
    let a := h.value y v
    let d := h.value x v
    have hW := projected_orthogonal e h P (hal x) (hal y) hxy hyx hPx hPy v
    change h.value x w = 0 ∧ h.value y w = 0 at hW
    obtain ⟨hwx, hwy⟩ := hW
    have hval : q (op a • x + w + op d • y) = a * d + q w := by
      rw [hAdd, hAdd, hScale, hScale, hqx, hqy, mul_zero, mul_zero, zero_add, add_zero,
        pairing_left_smul, hwx, mul_zero, add_zero, h.smul_right, pairing_left_add, pairing_left_smul,
        hxy, hsym w y, hwy, add_zero, mul_one]
      exact add_comm _ _
    have hRec := projections_reconstruct e h P hPx hPy v
    change v = op a • x + w + op d • y at hRec
    rw [← hRec] at hval
    have he := compressed_diagonal e b.anti H h rfl hσ P ell v hPy
    change h.value v (e ell' *ᵥ v) = a * d + h.value w (e ell *ᵥ w) at he
    refine ⟨0, ?_⟩
    rw [diagonal_sub D e b.anti H]
    change h.value v (e ell' *ᵥ v) - h.value v (e ell *ᵥ v) = (0 : F) + 0
    rw [← hqs, he, ← hqs, ← hval, sub_self, add_zero]
  have hnew := semitrace_replacement hTrace hAlt
  obtain ⟨hC1, hC2⟩ := compressed_commutes P ell
  obtain ⟨c, hc⟩ := scale_cocharacter M P ell' hnew hC1 hC2
  have hfirst : e P.first *ᵥ x = x := by rw [hPx, hyx, op_one, one_smul]
  have hnz := scale_cocharacter_nonzero M P (first_projection_ne_zero e P hx hfirst) c hc
  obtain ⟨l, hl, _⟩ := lift_spin_cocharacter_nonzero M c hnz
  exact ⟨⟨x, hx, hqx⟩, l, hl⟩

end ArithmeticCocharacters

/- The targets in this section have one universe. The two-universe premises
use that universe in both positions. -/
section

open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels

set_option linter.unusedSectionVars false

variable
  (hArchimedeanDivision : ArchimedeanDivision.{u})
  (hCliffordSimilitudeAction : CliffordSimilitudeAction.{u})
  (hCliffordSimilitudeBaseChange : CliffordSimilitudeBaseChange.{u})
  (hCorootLattice : CorootLattice.{u})
  (hDescendedVectorImage : DescendedVectorImage.{u})
  (hEvenCliffordSimilitude : EvenCliffordSimilitude.{u})
  (hEvenCliffordVectorAction : EvenCliffordVectorAction.{u})
  (hFieldOrthogonalModel : FieldOrthogonalModel.{u})
  (hFiniteEquivariantSpinReference : FiniteEquivariantSpinReference.{u})
  (hFiniteSpinReference : FiniteSpinReference.{u})
  (hFixedVertexFiniteLevel : FixedVertexFiniteLevel.{u})
  (hFixedVertexOuterFactorization : FixedVertexOuterFactorization.{u})
  (hHyperbolicPartner : HyperbolicPartner.{u,u})
  (hNeutralPointsReducedNorm : NeutralPointsReducedNorm.{u})
  (hNonarchimedeanDivision : NonarchimedeanDivision.{u,u})
  (hNontrialitarianSpinModel : NontrialitarianSpinModel.{u})
  (hOrthogonalInvolutionDescent : OrthogonalInvolutionDescent.{u})
  (hPairIsometryModel : PairIsometryModel.{u})
  (hPairIsometryScalarExtension : PairIsometryScalarExtension.{u})
  (hPairReducedNormScalarExtension : PairReducedNormScalarExtension.{u})
  (hProjectiveCliffordAction : ProjectiveCliffordAction.{u})
  (hProjectiveSimilitudes : ProjectiveSimilitudes.{u})
  (hQuadraticPairDescent : QuadraticPairDescent.{u})
  (hQuadraticPairScalarExtension : QuadraticPairScalarExtension.{u})
  (hQuaternionSkewModel : QuaternionSkewModel.{u})
  (hQuaternionSpinIsotropy : QuaternionSpinIsotropy.{u})
  (hSimpleDCoordinates : SimpleDCoordinates.{u})
  (hSpinChartFibers : SpinChartFibers.{u})
  (hSpinSimilitudeScalarExtension : SpinSimilitudeScalarExtension.{u})
  (hSplitOrthogonalModel : SplitOrthogonalModel.{u})
  (hSplitOrthogonalTangent : SplitOrthogonalTangent.{u})
  (hSplitOrthogonalTangentBlocks : SplitOrthogonalTangentBlocks.{u})
  (hSplitPairIsometries : SplitPairIsometries.{u})
  (hSplitProjectiveSpinAction : SplitProjectiveSpinAction.{u})
  (hSplitSemitrace : SplitSemitrace.{u})
  (hSplitSpinBorel : SplitSpinBorel.{u})
  (hSplitSpinCentralIsogeny : SplitSpinCentralIsogeny.{u})
  (hSplitSpinChartInImage : SplitSpinChartInImage.{u})
  (hSplitSpinDeterminant : SplitSpinDeterminant.{u})
  (hSplitSpinDiagonalTorus : SplitSpinDiagonalTorus.{u})
  (hSplitSpinDiagramAction : SplitSpinDiagramAction.{u})
  (hSplitSpinGeometry : SplitSpinGeometry.{u})
  (hSplitSpinIdentityComponent : SplitSpinIdentityComponent.{u})
  (hSplitSpinImage : SplitSpinImage.{u})
  (hSplitSpinIntegralComparison : SplitSpinIntegralComparison.{u})
  (hSplitSpinOpenImage : SplitSpinOpenImage.{u})
  (hSplitSpinTorusRestriction : SplitSpinTorusRestriction.{u})
  (hSplitSpinTypeD : SplitSpinTypeD.{u})
  (hSplitVectorCentralizer : SplitVectorCentralizer.{u})
  (hSplitVectorTangent : SplitVectorTangent.{u})
  (hTraceOrthogonality : TraceOrthogonality.{u})
  (hTypeDPositiveRoots : TypeDPositiveRoots.{u})
  (hVectorDiagramSwitch : VectorDiagramSwitch.{u})
  (hVectorMorphismDescent : VectorMorphismDescent.{u})
  (hVectorVertexStabilizer : VectorVertexStabilizer)

include
  hArchimedeanDivision hCliffordSimilitudeAction hCliffordSimilitudeBaseChange
  hCorootLattice hDescendedVectorImage hEvenCliffordSimilitude hEvenCliffordVectorAction
  hFieldOrthogonalModel hFiniteEquivariantSpinReference hFiniteSpinReference
  hFixedVertexFiniteLevel hFixedVertexOuterFactorization hHyperbolicPartner
  hNeutralPointsReducedNorm hNonarchimedeanDivision hNontrialitarianSpinModel
  hOrthogonalInvolutionDescent hPairIsometryModel hPairIsometryScalarExtension
  hPairReducedNormScalarExtension hProjectiveCliffordAction hProjectiveSimilitudes
  hQuadraticPairDescent hQuadraticPairScalarExtension hQuaternionSkewModel
  hQuaternionSpinIsotropy hSimpleDCoordinates hSpinChartFibers
  hSpinSimilitudeScalarExtension hSplitOrthogonalModel hSplitOrthogonalTangent
  hSplitOrthogonalTangentBlocks hSplitPairIsometries hSplitProjectiveSpinAction
  hSplitSemitrace hSplitSpinBorel hSplitSpinCentralIsogeny hSplitSpinChartInImage
  hSplitSpinDeterminant hSplitSpinDiagonalTorus hSplitSpinDiagramAction hSplitSpinGeometry
  hSplitSpinIdentityComponent hSplitSpinImage hSplitSpinIntegralComparison
  hSplitSpinOpenImage hSplitSpinTorusRestriction hSplitSpinTypeD hSplitVectorCentralizer
  hSplitVectorTangent hTraceOrthogonality hTypeDPositiveRoots hVectorDiagramSwitch
  hVectorMorphismDescent hVectorVertexStabilizer

theorem localSquareDegree_conditional : LocalSquareDegree.{u} :=
  local_square_degree

theorem semitraceRepresentative_conditional : SemitraceRepresentative.{u} :=
  semitrace_representative

theorem frobeniusBrauerComparison_conditional : FrobeniusBrauerComparison.{u} :=
  frobenius_brauer_comparison

theorem divisionDegreeOverSquares_conditional : DivisionDegreeOverSquares.{u} :=
  division_degree_over_squares split_division_degree

theorem quaternionPairRecovery_conditional : QuaternionPairRecovery.{u} :=
  quaternion_pair_recovery

theorem splitPairRecovery_conditional : SplitPairRecovery.{u} :=
  split_pair_recovery

end

/- The remaining targets use the premise universes in their declared order. -/
section

open LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels

set_option linter.unusedSectionVars false

variable
  (hArchimedeanDivision : ArchimedeanDivision.{u})
  (hCliffordSimilitudeAction : CliffordSimilitudeAction.{u})
  (hCliffordSimilitudeBaseChange : CliffordSimilitudeBaseChange.{u})
  (hCorootLattice : CorootLattice.{u})
  (hDescendedVectorImage : DescendedVectorImage.{u})
  (hEvenCliffordSimilitude : EvenCliffordSimilitude.{u})
  (hEvenCliffordVectorAction : EvenCliffordVectorAction.{u})
  (hFieldOrthogonalModel : FieldOrthogonalModel.{u})
  (hFiniteEquivariantSpinReference : FiniteEquivariantSpinReference.{u})
  (hFiniteSpinReference : FiniteSpinReference.{u})
  (hFixedVertexFiniteLevel : FixedVertexFiniteLevel.{u})
  (hFixedVertexOuterFactorization : FixedVertexOuterFactorization.{u})
  (hHyperbolicPartner : HyperbolicPartner.{u,v})
  (hNeutralPointsReducedNorm : NeutralPointsReducedNorm.{u})
  (hNonarchimedeanDivision : NonarchimedeanDivision.{u,v})
  (hNontrialitarianSpinModel : NontrialitarianSpinModel.{u})
  (hOrthogonalInvolutionDescent : OrthogonalInvolutionDescent.{u})
  (hPairIsometryModel : PairIsometryModel.{u})
  (hPairIsometryScalarExtension : PairIsometryScalarExtension.{u})
  (hPairReducedNormScalarExtension : PairReducedNormScalarExtension.{u})
  (hProjectiveCliffordAction : ProjectiveCliffordAction.{u})
  (hProjectiveSimilitudes : ProjectiveSimilitudes.{u})
  (hQuadraticPairDescent : QuadraticPairDescent.{u})
  (hQuadraticPairScalarExtension : QuadraticPairScalarExtension.{u})
  (hQuaternionSkewModel : QuaternionSkewModel.{u})
  (hQuaternionSpinIsotropy : QuaternionSpinIsotropy.{u})
  (hSimpleDCoordinates : SimpleDCoordinates.{u})
  (hSpinChartFibers : SpinChartFibers.{u})
  (hSpinSimilitudeScalarExtension : SpinSimilitudeScalarExtension.{u})
  (hSplitOrthogonalModel : SplitOrthogonalModel.{u})
  (hSplitOrthogonalTangent : SplitOrthogonalTangent.{u})
  (hSplitOrthogonalTangentBlocks : SplitOrthogonalTangentBlocks.{u})
  (hSplitPairIsometries : SplitPairIsometries.{u})
  (hSplitProjectiveSpinAction : SplitProjectiveSpinAction.{u})
  (hSplitSemitrace : SplitSemitrace.{u})
  (hSplitSpinBorel : SplitSpinBorel.{u})
  (hSplitSpinCentralIsogeny : SplitSpinCentralIsogeny.{u})
  (hSplitSpinChartInImage : SplitSpinChartInImage.{u})
  (hSplitSpinDeterminant : SplitSpinDeterminant.{u})
  (hSplitSpinDiagonalTorus : SplitSpinDiagonalTorus.{u})
  (hSplitSpinDiagramAction : SplitSpinDiagramAction.{u})
  (hSplitSpinGeometry : SplitSpinGeometry.{u})
  (hSplitSpinIdentityComponent : SplitSpinIdentityComponent.{u})
  (hSplitSpinImage : SplitSpinImage.{u})
  (hSplitSpinIntegralComparison : SplitSpinIntegralComparison.{u})
  (hSplitSpinOpenImage : SplitSpinOpenImage.{u})
  (hSplitSpinTorusRestriction : SplitSpinTorusRestriction.{u})
  (hSplitSpinTypeD : SplitSpinTypeD.{u})
  (hSplitVectorCentralizer : SplitVectorCentralizer.{u})
  (hSplitVectorTangent : SplitVectorTangent.{u})
  (hTraceOrthogonality : TraceOrthogonality.{u})
  (hTypeDPositiveRoots : TypeDPositiveRoots.{u})
  (hVectorDiagramSwitch : VectorDiagramSwitch.{u})
  (hVectorMorphismDescent : VectorMorphismDescent.{u})
  (hVectorVertexStabilizer : VectorVertexStabilizer)

include
  hArchimedeanDivision hCliffordSimilitudeAction hCliffordSimilitudeBaseChange
  hCorootLattice hDescendedVectorImage hEvenCliffordSimilitude hEvenCliffordVectorAction
  hFieldOrthogonalModel hFiniteEquivariantSpinReference hFiniteSpinReference
  hFixedVertexFiniteLevel hFixedVertexOuterFactorization hHyperbolicPartner
  hNeutralPointsReducedNorm hNonarchimedeanDivision hNontrialitarianSpinModel
  hOrthogonalInvolutionDescent hPairIsometryModel hPairIsometryScalarExtension
  hPairReducedNormScalarExtension hProjectiveCliffordAction hProjectiveSimilitudes
  hQuadraticPairDescent hQuadraticPairScalarExtension hQuaternionSkewModel
  hQuaternionSpinIsotropy hSimpleDCoordinates hSpinChartFibers
  hSpinSimilitudeScalarExtension hSplitOrthogonalModel hSplitOrthogonalTangent
  hSplitOrthogonalTangentBlocks hSplitPairIsometries hSplitProjectiveSpinAction
  hSplitSemitrace hSplitSpinBorel hSplitSpinCentralIsogeny hSplitSpinChartInImage
  hSplitSpinDeterminant hSplitSpinDiagonalTorus hSplitSpinDiagramAction hSplitSpinGeometry
  hSplitSpinIdentityComponent hSplitSpinImage hSplitSpinIntegralComparison
  hSplitSpinOpenImage hSplitSpinTorusRestriction hSplitSpinTypeD hSplitVectorCentralizer
  hSplitVectorTangent hTraceOrthogonality hTypeDPositiveRoots hVectorDiagramSwitch
  hVectorMorphismDescent hVectorVertexStabilizer

theorem globalSquareDegree_conditional : GlobalSquareDegree.{u,v} :=
  @global_square_degree.{u,v}

theorem refinementIdentities_conditional : RefinementIdentities.{u,v,w} :=
  refinement_identities

theorem refinementHyperbolicPair_conditional : RefinementHyperbolicPair.{u,v,w} :=
  refinement_hyperbolic_pair

theorem quaternionRefinementIsotropy_conditional : QuaternionRefinementIsotropy.{u,v,w} :=
  quaternion_refinement_isotropy

theorem splitDivisionDegree_conditional : SplitDivisionDegree.{u,v,w} :=
  split_division_degree

theorem splitQuadraticIsotropy_conditional : SplitQuadraticIsotropy.{u,v} :=
  split_quadratic_isotropy

theorem arithmeticQuaternionIsotropy_conditional : ArithmeticQuaternionIsotropy.{u,v} :=
  arithmetic_quaternion_isotropy

theorem arithmeticSplitIsotropy_conditional : ArithmeticSplitIsotropy.{u,v} :=
  arithmetic_split_isotropy

theorem nontrialitarianIsotropy_conditional : NontrialitarianIsotropy.{u,v} :=
  nontrialitarian_isotropy_from_models hNontrialitarianSpinModel
    arithmetic_quaternion_isotropy arithmetic_split_isotropy


end

end

end LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs

universe v8_closure_9bc0312c0e1c2c17_u0 v8_closure_9bc0312c0e1c2c17_u1 v8_closure_9bc0312c0e1c2c17_u2
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«arithmeticQuaternionIsotropy» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«ArithmeticQuaternionIsotropy».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«arithmeticQuaternionIsotropy_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«arithmeticSplitIsotropy» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«ArithmeticSplitIsotropy».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«arithmeticSplitIsotropy_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«divisionDegreeOverSquares» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«DivisionDegreeOverSquares».{v8_closure_9bc0312c0e1c2c17_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«divisionDegreeOverSquares_conditional».{v8_closure_9bc0312c0e1c2c17_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«frobeniusBrauerComparison» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«FrobeniusBrauerComparison».{v8_closure_9bc0312c0e1c2c17_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«frobeniusBrauerComparison_conditional».{v8_closure_9bc0312c0e1c2c17_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«globalSquareDegree» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«GlobalSquareDegree».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«globalSquareDegree_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«localSquareDegree» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«LocalSquareDegree».{v8_closure_9bc0312c0e1c2c17_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«localSquareDegree_conditional».{v8_closure_9bc0312c0e1c2c17_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«nontrialitarianIsotropy» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«NontrialitarianIsotropy».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«nontrialitarianIsotropy_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«quaternionPairRecovery» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«QuaternionPairRecovery».{v8_closure_9bc0312c0e1c2c17_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«quaternionPairRecovery_conditional».{v8_closure_9bc0312c0e1c2c17_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«quaternionRefinementIsotropy» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«QuaternionRefinementIsotropy».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«quaternionRefinementIsotropy_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«refinementHyperbolicPair» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«RefinementHyperbolicPair».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«refinementHyperbolicPair_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«refinementIdentities» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«RefinementIdentities».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«refinementIdentities_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«semitraceRepresentative» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«SemitraceRepresentative».{v8_closure_9bc0312c0e1c2c17_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«semitraceRepresentative_conditional».{v8_closure_9bc0312c0e1c2c17_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«splitDivisionDegree» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«SplitDivisionDegree».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«splitDivisionDegree_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1, v8_closure_9bc0312c0e1c2c17_u2} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«splitPairRecovery» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«SplitPairRecovery».{v8_closure_9bc0312c0e1c2c17_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«splitPairRecovery_conditional».{v8_closure_9bc0312c0e1c2c17_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«splitQuadraticIsotropy» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«CharacteristicTwoQuadraticPairs».«SplitQuadraticIsotropy».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«CharacteristicTwoQuadraticPairs».«splitQuadraticIsotropy_conditional».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«archimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«cliffordSimilitudeBaseChange».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«corootLattice».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«descendedVectorImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordSimilitude».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«evenCliffordVectorAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fieldOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteEquivariantSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«finiteSpinReference».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexFiniteLevel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«fixedVertexOuterFactorization».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«hyperbolicPartner».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«neutralPointsReducedNorm».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nonarchimedeanDivision».{v8_closure_9bc0312c0e1c2c17_u0, v8_closure_9bc0312c0e1c2c17_u1}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«nontrialitarianSpinModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«orthogonalInvolutionDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairIsometryScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«pairReducedNormScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveCliffordAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«projectiveSimilitudes».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quadraticPairScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSkewModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«quaternionSpinIsotropy».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«simpleDCoordinates».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinChartFibers».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«spinSimilitudeScalarExtension».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalModel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitOrthogonalTangentBlocks».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitPairIsometries».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitProjectiveSpinAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSemitrace».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinBorel».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinCentralIsogeny».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinChartInImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDeterminant».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagonalTorus».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinDiagramAction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinGeometry».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIdentityComponent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinIntegralComparison».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinOpenImage».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTorusRestriction».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitSpinTypeD».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorCentralizer».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«splitVectorTangent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«traceOrthogonality».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«typeDPositiveRoots».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorDiagramSwitch».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorMorphismDescent».{v8_closure_9bc0312c0e1c2c17_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«NontrialitarianSpinModels».«vectorVertexStabilizer»)
