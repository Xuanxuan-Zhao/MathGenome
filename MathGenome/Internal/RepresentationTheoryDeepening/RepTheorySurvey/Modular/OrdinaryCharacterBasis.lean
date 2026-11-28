import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.OrdinaryCharacterBasis
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.GroupAlgebraCenter
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplitMatrixColumns
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The ordinary irreducible characters of a split group algebra form a basis of class functions. -/

noncomputable section

namespace RepTheorySurvey.Modular

open scoped MonoidAlgebra Matrix
open OrdinaryCharacterBasisSpec (moduleCharacter)

universe uK uG uI uV

variable {K : Type uK} [Field K] {G : Type uG} [Group G]

private def characterOnClasses (V : ModuleCat.{uV} K[G]) : ConjClasses G → K :=
  Quotient.lift (moduleCharacter V) fun x y hxy => by
    obtain ⟨h, rfl⟩ := isConj_iff.mp hxy
    exact (@Representation.char_conj G K (RestrictScalars K K[G] (V : Type uV))
      _ _ _ (RestrictScalars.module K K[G] (V : Type uV))
      (Representation.ofModule (k := K) (G := G) (V : Type uV)) x h).symm

private def traceForm (V : ModuleCat.{uV} K[G]) : K[G] →ₗ[K] K :=
  (LinearMap.trace K (RestrictScalars K K[G] V)).comp
    (RestrictScalars.lsmul K K[G] V).toLinearMap

private theorem characterOnClasses_mk_eq_traceForm (V : ModuleCat.{uV} K[G]) (g : G) :
    characterOnClasses V (ConjClasses.mk g) = traceForm V (MonoidAlgebra.of K G g) := rfl

variable {r : ℕ} {d : Fin r → ℕ}
  {q : K[G] →ₐ[K] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) K)}

private theorem traceForm_eq_column (V : ModuleCat.{uV} K[G]) {i : Fin r}
    (f : V ≃ₗ[K[G]] columnModule q i) (a : K[G]) :
    traceForm V a = LinearMap.trace K (Fin (d i) → K) (columnAction q i a) := by
  let fK : RestrictScalars K K[G] V ≃ₗ[K] columnModule q i :=
    { toAddEquiv := (RestrictScalars.addEquiv K K[G] V).trans f.toAddEquiv
      map_smul' := by
        intro c v
        change f (algebraMap K K[G] c • (RestrictScalars.addEquiv K K[G] V v)) =
          c • f (RestrictScalars.addEquiv K K[G] V v)
        rw [f.map_smul, IsScalarTower.algebraMap_smul] }
  have hconj : fK.conj (RestrictScalars.lsmul K K[G] V a) =
      (columnAction q i a : Module.End K (columnModule q i)) := by
    ext v
    change f (a • f.symm v) = columnAction q i a v
    rw [f.map_smul, f.apply_symm_apply, columnAction_apply]
  have htrace := @LinearMap.trace_conj' K _ (RestrictScalars K K[G] V) _
    (RestrictScalars.module K K[G] V) (columnModule q i) _ _
    (RestrictScalars.lsmul K K[G] V a) fK
  exact htrace.symm.trans (congrArg (LinearMap.trace K (columnModule q i)) hconj)

private theorem finrank_classFunctions [Finite G] (hd : ∀ i, 0 < d i)
    (e : K[G] ≃ₐ[K] ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) K)) :
    Module.finrank K (ConjClasses G → K) = r := by
  classical
  let B := (i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) K
  have hcenter (a : K[G]) :
      a ∈ Subalgebra.center K K[G] ↔
        ∀ i, ∃ c : K, Matrix.scalar (Fin (d i)) c = e a i := by
    have he : a ∈ Subalgebra.center K K[G] ↔ e a ∈ Subalgebra.center K B := by
      constructor
      · intro ha
        exact Subalgebra.map_center_le_center (f := e.toAlgHom) e.surjective ⟨a, ha, rfl⟩
      · exact fun ha => Subalgebra.comap_center_le_center (f := e.toAlgHom) e.injective ha
    rw [he, Subalgebra.center_pi]
    change (∀ i : Fin r, i ∈ (Set.univ : Set (Fin r)) →
      e a i ∈ Set.center (Matrix (Fin (d i)) (Fin (d i)) K)) ↔ _
    simp only [Set.mem_univ, true_implies, Matrix.center_eq_range, Set.mem_range]
  let scalarMap : (Fin r → K) →ₗ[K] B :=
    LinearMap.pi fun i => (Matrix.scalarAlgHom (Fin (d i)) K).toLinearMap.comp (LinearMap.proj i)
  let f : (Fin r → K) →ₗ[K] Subalgebra.center K K[G] :=
    (e.symm.toLinearMap.comp scalarMap).codRestrict (Subalgebra.center K K[G]).toSubmodule
      (fun x => (hcenter _).2 fun i => ⟨x i, by
        change Matrix.scalar (Fin (d i)) (x i) = e (e.symm (scalarMap x)) i
        rw [e.apply_symm_apply]
        rfl⟩)
  have hf (x : Fin r → K) (i : Fin r) :
      e (f x).val i = Matrix.scalar (Fin (d i)) (x i) := by
    change e (e.symm (scalarMap x)) i = _
    rw [e.apply_symm_apply]
    rfl
  have hinj : Function.Injective f := by
    intro x y h
    funext i
    have hmat := (hf x i).symm.trans ((congrArg (fun z => e z.val i) h).trans (hf y i))
    let s : Fin (d i) := ⟨0, hd i⟩
    simpa [Matrix.scalar_apply] using congrArg (fun m => m s s) hmat
  have hsurj : Function.Surjective f := by
    intro z
    choose c hc using (hcenter z.val).1 z.property
    refine ⟨c, Subtype.ext (e.injective (funext fun i => ?_))⟩
    exact (hf c i).trans (hc i)
  let := Fintype.ofFinite G
  let dimEquiv := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm
  calc
    Module.finrank K (ConjClasses G → K) =
        Module.finrank K (Subalgebra.center K K[G]) :=
      (GroupAlgebraCenter.centerClassEquiv K).finrank_eq.symm
    _ = Module.finrank K (Fin r → K) := dimEquiv.finrank_eq
    _ = r := by simp

/-- The trace characters of any complete family of simple modules over the given
split group algebra are a basis of the functions on conjugacy classes. -/
theorem ordinary_character_basis [Finite G]
    {ι : Type uI} (V : ι → ModuleCat.{max uK uV} K[G])
    (hsplit : IsSplitMatrixAlgebra K K[G]) (hV : IsSimpleRepresentativeFamily V) :
    ∃ b : Module.Basis ι K (ConjClasses G → K),
      ∀ i (g : G), b i (ConjClasses.mk g) = moduleCharacter (V i) g := by
  classical
  obtain ⟨r, d, hd, e, hcols⟩ := ordinary_columns_exist hsplit
  let q := e.toAlgHom
  have hiso (i : ι) : ∃ j, Nonempty (V i ≃ₗ[K[G]] columnModule q j) :=
    column_exhaustive q hd e.surjective
      (by
        intro a ha
        have hz : e a = 0 := RingHom.mem_ker.mp ha
        rw [(map_eq_zero_iff e e.injective).mp hz]
        exact (Ring.jacobson _).zero_mem) (V i) (hV.simple i)
  choose j hj using hiso
  let iso (i : ι) := (hj i).some
  have hj_inj : Function.Injective j := by
    intro i i' h
    apply hV.eq_of_iso
    have f : columnModule q (j i) ≃ₗ[K[G]] columnModule q (j i') := by
      rw [h]
    exact ⟨(iso i).trans (f.trans (iso i').symm)⟩
  have hj_surj : Function.Surjective j := by
    intro t
    let W := ModuleCat.of K[G] (ULift.{uV} (columnModule q t))
    let down : W ≃ₗ[K[G]] columnModule q t := ULift.moduleEquiv
    obtain ⟨i, ⟨f⟩⟩ := hV.exhaustive W (down.isSimpleModule_iff.mpr (hcols.simple t))
    exact ⟨i, hcols.eq_of_iso ⟨(iso i).symm.trans (f.symm.trans down)⟩⟩
  let indexEquiv := Equiv.ofBijective j ⟨hj_inj, hj_surj⟩
  let : Fintype ι := Fintype.ofEquiv (Fin r) indexEquiv.symm
  let := Fintype.ofFinite (ConjClasses G)
  have hcard : Fintype.card ι = Module.finrank K (ConjClasses G → K) := by
    rw [finrank_classFunctions hd e, Fintype.card_congr indexEquiv, Fintype.card_fin]
  let χ (i : ι) := characterOnClasses (V i)
  have hli : LinearIndependent K χ := by
    refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
    let T : K[G] →ₗ[K] K := ∑ l, c l • traceForm (V l)
    have hT (a : K[G]) : T a = 0 := by
      induction a using MonoidAlgebra.induction_on with
      | of g =>
        have hg := congrFun hc (ConjClasses.mk g)
        simpa only [T, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
          Pi.smul_apply, Pi.zero_apply, χ, characterOnClasses_mk_eq_traceForm] using hg
      | add a b ha hb => rw [map_add, ha, hb, add_zero]
      | smul c a ha => rw [map_smul, ha, smul_zero]
    obtain ⟨a, -, ha⟩ := column_trace_test q e.surjective (j i) ⟨0, hd (j i)⟩
    have htests (l : ι) : traceForm (V l) a = if l = i then 1 else 0 := by
      rw [traceForm_eq_column (V l) (iso l), ha]
      exact if_congr (hj_inj.eq_iff) rfl rfl
    simpa [T, LinearMap.sum_apply, LinearMap.smul_apply, htests, mul_ite] using hT a
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' χ hli hcard, fun i g => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rfl

end RepTheorySurvey.Modular
