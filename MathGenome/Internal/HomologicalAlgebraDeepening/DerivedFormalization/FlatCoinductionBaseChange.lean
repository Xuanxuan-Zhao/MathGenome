import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.FlatCoinductionBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CoinductionComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ModelQuasiIsoInvariance
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveComplexReplacement
import MathGenome.Internal.AlgebraCore.P103.Ch12.ExtBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Data.Int.Interval

namespace DerivedFormalization.FlatCoinductionBaseChange

open CategoryTheory CategoryTheory.Limits TensorProduct
open Specs.DerivedFormalization.FlatCoinductionBaseChange
open Specs.DerivedFormalization.Cochains (compValue derivedValue qValue stalkValue)
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.DerivedRestriction (restrictScalarsComplexValue
  derivedRestrictScalarsValue)
open Specs.DerivedFormalization.CoinductionComplex (coinduceValue evaluationValue restrictedRegular)
open CochainComplex.HomComplex

universe u w z v

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

variable {R : Type u} {T : Type w} [CommRing R] [CommRing T]

/-- Extending along a flat ring map is exact on the whole module category. -/
theorem extendPreservesFiniteLimits (g : R →+* T)
    (hg : @Module.Flat R T _ _ (Module.compHom T g)) :
    PreservesFiniteLimits (extend.{u,w,max w v} g) := by
  have hex : ∀ (C : ShortComplex (ModuleCat.{max w v} R)), C.Exact →
      (C.map (extend.{u,w,max w v} g)).Exact := by
    intro C hC
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
    letI : Module R T := Module.compHom T g
    letI : Module.Flat R T := hg
    exact Module.Flat.lTensor_exact T (f := C.f.hom) (g := C.g.hom) hC
  have h : (∀ C : ShortComplex (ModuleCat.{max w v} R),
      C.Exact → (C.map (extend.{u,w,max w v} g)).Exact) ↔
      PreservesFiniteLimits (extend.{u,w,max w v} g) ∧ PreservesFiniteColimits (extend.{u,w,max w v} g) :=
    (Functor.exact_tfae (extend.{u,w,max w v} g)).out 2 4
  exact (h.mp hex).1

variable (A : Type u) (B : Type w) (S : Type z) [CommRing A] [CommRing B] [CommRing S]
  [Algebra A B] [Algebra A S]

local notation "D" => changedRing A B S

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The top-to-bottom scalar extension is flat on the (B)-side as well. -/
theorem rightMapFlat [Module.Flat A S] :
    @Module.Flat B D _ _ (Module.compHom D (rightMap A B S)) := by
  have h : Module.compHom D (rightMap A B S) = Algebra.toModule := by
    apply Module.ext'
    intro b x
    exact (Algebra.smul_def b x).symm
  rw [h]
  exact Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight A B S).symm.toLinearEquiv

private abbrev sourceM (M : ModuleCat.{v} B) :=
  (restrict.{u,w,v} (algebraMap A B)).obj M

private abbrev changedM (M : ModuleCat.{max u w z v} B) :=
  ((extend.{_,_,max u w z v} (rightMap A B S) ⋙ restrict (bottomMap A B S)).obj M)

/-- The map sending (m) to (1otimes m), regarded as (A)-linear. -/
private def unitM (M : ModuleCat.{max u w z v} B) :
    sourceM A B M ⟶ (restrict.{_,_,max u w z v} (algebraMap A S)).obj (changedM.{u,w,z,v} A B S M) :=
  ((restrict.{_,_,max u w z v} (algebraMap A B)).map
    ((ModuleCat.extendRestrictScalarsAdj.{max u w z v,_,_} (rightMap A B S)).unit.app M)) ≫
    (ModuleCat.restrictScalarsComp' (f := algebraMap A B) (g := rightMap A B S)
      (gf := (bottomMap A B S).comp (algebraMap A S))
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)).inv.app
        ((extend.{_,_,max u w z v} (rightMap A B S)).obj M) ≫
    (ModuleCat.restrictScalarsComp' (f := algebraMap A S) (g := bottomMap A B S)
      (gf := (bottomMap A B S).comp (algebraMap A S)) rfl).hom.app
        ((extend.{_,_,max u w z v} (rightMap A B S)).obj M)

private def squareInv (M : ModuleCat.{max u w z v} B) :
    (extend.{_,_,max u w z v} (algebraMap A S)).obj (sourceM A B M) ⟶ changedM.{u,w,z,v} A B S M :=
  ((ModuleCat.extendRestrictScalarsAdj.{max u w z v,_,_} (algebraMap A S)).homEquiv _ _).symm
    (unitM.{u,w,z,v} A B S M)

private theorem squareInv_pure (M : ModuleCat.{max u w z v} B) (s : S) (m : M) :
    squareInv.{u,w,z,v} A B S M (pure (algebraMap A S) s (m : sourceM A B M)) =
      (pure (rightMap A B S) (bottomMap A B S s) m : changedM.{u,w,z,v} A B S M) := by
  have hone : squareInv.{u,w,z,v} A B S M (pure (algebraMap A S) 1 (m : sourceM A B M)) =
      (pure (rightMap A B S) 1 m : changedM.{u,w,z,v} A B S M) := by
    exact congrArg (fun h : sourceM A B M ⟶ _ => h (m : sourceM A B M))
      (Equiv.apply_symm_apply
        ((ModuleCat.extendRestrictScalarsAdj.{max u w z v,_,_} (algebraMap A S)).homEquiv _ _)
        (unitM.{u,w,z,v} A B S M))
  calc
    _ = squareInv.{u,w,z,v} A B S M (s • pure (algebraMap A S) 1 (m : sourceM A B M)) := by
      congr 1
      simpa only [mul_one] using
        (ModuleCat.ExtendScalars.smul_tmul (algebraMap A S) (M := sourceM A B M) s 1 m).symm
    _ = s • squareInv.{u,w,z,v} A B S M (pure (algebraMap A S) 1 (m : sourceM A B M)) :=
      (squareInv.{u,w,z,v} A B S M).hom.map_smul s _
    _ = _ := by
      rw [hone]
      change (bottomMap A B S s) • pure (rightMap A B S) 1 m = _
      simpa only [mul_one] using
        (ModuleCat.ExtendScalars.smul_tmul (rightMap A B S) (bottomMap A B S s) 1 m)

/-- The underlying tensor equivalence ((Sotimes_A B)otimes_B M
simeq Sotimes_A M), prior to equipping the map with its (S)-linearity. -/
private def squareEquiv (M : ModuleCat.{max u w z v} B) :
    ((changedM.{u,w,z,v} A B S M) : Type (max u w z v)) ≃+
      ((extend.{_,_,max u w z v} (algebraMap A S)).obj (sourceM A B M) : Type (max u w z v)) := by
  letI : Module A M := Module.compHom M (algebraMap A B)
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e :=
    TensorProduct.congr (Algebra.TensorProduct.commRight A B S).symm.toLinearEquiv (LinearEquiv.refl B M) ≪≫ₗ
    TensorProduct.comm B (B ⊗[A] S) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B B M S
  let S₀ := (ModuleCat.restrictScalars.{z} (algebraMap A S)).obj (ModuleCat.of S S)
  let scalarEquiv : S ≃ₗ[A] S₀ :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => Algebra.smul_def r s }
  exact (e.toAddEquiv.trans ((TensorProduct.comm A M S).trans
    (TensorProduct.congr scalarEquiv (LinearEquiv.refl A M))).toAddEquiv)

private theorem squareInv_bijective (M : ModuleCat.{max u w z v} B) :
    Function.Bijective (squareInv.{u,w,z,v} A B S M) := by
  have h : ⇑(squareEquiv.{u,w,z,v} A B S M).symm = ⇑(squareInv.{u,w,z,v} A B S M) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      exact ((squareEquiv.{u,w,z,v} A B S M).symm.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans ((squareInv.{u,w,z,v} A B S M).hom.map_add x y).symm)
    | tmul s m =>
      exact (squareInv_pure.{u,w,z,v} A B S M s m).symm
  rw [← h]
  exact (squareEquiv.{u,w,z,v} A B S M).symm.bijective

/-- (Sotimes_A f_*(-)) identifies with (f'_*(B'otimes_B-))
on the ordinary module categories. -/
def restrictionSquare : RestrictionSquare.{u,w,z,v} A B S :=
  (NatIso.ofComponents (fun M =>
    (LinearEquiv.ofBijective (squareInv.{u,w,z,v} A B S M).hom
      (squareInv_bijective.{u,w,z,v} A B S M)).toModuleIso) (fun {M N} k => by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change squareInv.{u,w,z,v} A B S N (pure (algebraMap A S) 1 (k m : sourceM A B N)) =
      (extend.{_,_,max u w z v} (rightMap A B S)).map k
        (squareInv.{u,w,z,v} A B S M (pure (algebraMap A S) 1 (m : sourceM A B M)))
    rw [squareInv_pure.{u,w,z,v} A B S N 1 (k (m : M)),
      squareInv_pure.{u,w,z,v} A B S M 1 (m : M)]
    rfl)).symm

theorem restrictionSquare_formula :
    TensorFormula.{u,w,z,v} A B S (restrictionSquare.{u,w,z,v} A B S) :=
  squareInv_pure.{u,w,z,v} A B S

section DerivedTrace

open Specs.DerivedFormalization.DerivedCoinduction (Coinduction)

private theorem squareMate_trace
    (G : Coinduction.{max u w z v} (algebraMap A B))
    (G' : Coinduction.{max u w z v} (bottomMap A B S))
    {L : derivedValue.{max u w z v} A ⥤ derivedValue.{max u w z v} S}
    {L' : derivedValue.{max u w z v} B ⥤ derivedValue.{max u w z v} D}
    (σ : L' ⋙ derivedRestrictScalarsValue (bottomMap A B S) ≅
      derivedRestrictScalarsValue (algebraMap A B) ⋙ L) :
    SquareTrace.{u,w,z,v} A B S G G' σ := by
  intro Y
  let k := σ.hom.app (G.functor.obj Y) ≫ L.map (G.adjunction.counit.app Y)
  change (derivedRestrictScalarsValue (bottomMap A B S)).map
      (G'.adjunction.homEquiv _ _ k) ≫ _ = k
  exact (G'.adjunction.homEquiv_counit (g := G'.adjunction.homEquiv _ _ k)).symm.trans
    (Equiv.symm_apply_apply _ _)

variable [PreservesFiniteLimits (extend.{_,_,max u w z v} (algebraMap A S))]
  [PreservesFiniteLimits (extend.{_,_,max u w z v} (rightMap A B S))]

/-- The mate of the restriction square intertwines the two derived counits. -/
theorem traceCompatibility (e : RestrictionSquare.{u,w,z,v} A B S)
    (G : Coinduction.{max u w z v} (algebraMap A B))
    (G' : Coinduction.{max u w z v} (bottomMap A B S)) :
    TraceCompatibility.{u,w,z,v} A B S e G G' :=
  squareMate_trace.{u,w,z,v} A B S G G' (derivedSquare.{u,w,z,v} A B S e)

end DerivedTrace

section HomComparison

variable {A : Type u} {S : Type z} [CommRing A] [CommRing S] [Algebra A S]

private abbrev extC := extendC.{_,_,max z v} (algebraMap A S)

private theorem extend_map_smul {M N : ModuleCat.{max z v} A} (r : A) (f : M ⟶ N) :
    (extend.{_,_,max z v} (algebraMap A S)).map (r • f) =
      algebraMap A S r • (extend.{_,_,max z v} (algebraMap A S)).map f := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change pure (algebraMap A S) 1 (r • f m) =
    algebraMap A S r • pure (algebraMap A S) 1 (f m)
  letI : Module A S := Module.compHom S (algebraMap A S)
  change (1 : S) ⊗ₜ[A] (r • f m) = _
  rw [← TensorProduct.smul_tmul]
  change pure (algebraMap A S) (algebraMap A S r * 1) (f m) = _
  exact (ModuleCat.ExtendScalars.smul_tmul (algebraMap A S)
    (algebraMap A S r) 1 (f m)).symm

/-- Componentwise extension of graded cochains, considered as a linear map over A. -/
private def cochainUnit (P I : compValue.{max z v} A) (n : ℤ) :
    (internalHomValue P I).X n ⟶
      (restrict.{_,_,max z v} (algebraMap A S)).obj
        ((internalHomValue ((extC (S := S)).obj P) ((extC (S := S)).obj I)).X n) :=
  let M := (internalHomValue P I).X n
  let N := (restrict.{_,_,max z v} (algebraMap A S)).obj
    ((internalHomValue ((extC (S := S)).obj P) ((extC (S := S)).obj I)).X n)
  ConcreteCategory.ofHom (C := ModuleCat A) (show M →ₗ[A] N from
    { toFun := fun z => (show N from z.map (extend.{_,_,max z v} (algebraMap A S)))
      map_add' := fun _ _ => Cochain.map_add ..
      map_smul' := by
        intro r z
        apply Cochain.ext
        intro p q hpq
        change _ = ((algebraMap A S r) •
          z.map (extend.{_,_,max z v} (algebraMap A S))).v p q hpq
        rw [Cochain.map_v, Cochain.smul_v, Cochain.smul_v, Cochain.map_v]
        exact extend_map_smul r _ })

private def homChangeTerm (P I : compValue.{max z v} A) (n : ℤ) :
    (extend.{_,_,max z v} (algebraMap A S)).obj ((internalHomValue P I).X n) ⟶
      (internalHomValue ((extC (S := S)).obj P) ((extC (S := S)).obj I)).X n :=
  ((ModuleCat.extendRestrictScalarsAdj.{v,u,z} (algebraMap A S)).homEquiv _ _).symm
    (cochainUnit P I n)

private theorem homChangeTerm_one (P I : compValue.{max z v} A) (n : ℤ) (z : Cochain P I n) :
    homChangeTerm (S := S) P I n (pure (algebraMap A S) 1 z) =
      z.map (extend.{_,_,max z v} (algebraMap A S)) := by
  have h := congrArg (fun f => f z)
    (Equiv.apply_symm_apply
      ((ModuleCat.extendRestrictScalarsAdj.{v,u,z} (algebraMap A S)).homEquiv _ _)
      (cochainUnit P I n))
  exact h

/-- The usual comparison from the scalar extension of the internal Hom. -/
private def homChange (P I : compValue.{max z v} A) :
    (extC (S := S)).obj (internalHomValue P I) ⟶
      internalHomValue ((extC (S := S)).obj P) ((extC (S := S)).obj I) where
  f n := homChangeTerm P I n
  comm' n m _ := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro z
    change δ n m (homChangeTerm (S := S) P I n (pure (algebraMap A S) 1 z)) =
      homChangeTerm (S := S) P I m (pure (algebraMap A S) 1 (δ n m z))
    rw [homChangeTerm_one, homChangeTerm_one]
    exact δ_map ..

private theorem homChange_naturality
    {P P' I I' : compValue.{max z v} A} (p : P' ⟶ P) (i : I ⟶ I') :
    (extC (S := S)).map (internalHomMapValue p i) ≫ homChange P' I' =
      homChange P I ≫ internalHomMapValue ((extC (S := S)).map p) ((extC (S := S)).map i) := by
  ext n : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  change homChangeTerm (S := S) P' I' n
      (pure (algebraMap A S) 1 ((internalHomMapValue p i).f n z)) =
    (internalHomMapValue ((extC (S := S)).map p) ((extC (S := S)).map i)).f n
      (homChangeTerm (S := S) P I n (pure (algebraMap A S) 1 z))
  rw [homChangeTerm_one, homChangeTerm_one]
  simp [internalHomMapValue]

end HomComparison

section Resolution

open HomologicalComplex ComplexShape

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

private theorem hasFiniteFreeResolution (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    ∃ (P : compValue.{max u v} A) (p : P ⟶ (stalkValue A).obj M),
      P.IsStrictlyLE 0 ∧ (∀ j, Module.Finite A (P.X j)) ∧
        (∀ j, Projective (P.X j)) ∧ QuasiIso p := by
  obtain ⟨Q, hfree, hfin⟩ :=
    P103.Ch12.ExtBaseChange.exists_finite_free_resolution.{u,max u v} A M
  let f : Q.complex.X 0 ⟶ M := ModuleCat.ofHom Q.ε
  have hf : Q.complex.d 1 0 ≫ f = 0 := by
    apply ModuleCat.hom_ext
    ext x : 1
    change Q.ε ((Q.complex.d 1 0).hom x) = 0
    exact LinearMap.mem_ker.mp (Q.exact_zero ▸ LinearMap.mem_range_self _ x)
  let p₀ := (ChainComplex.toSingle₀Equiv Q.complex M).symm ⟨f, hf⟩
  have h₀ : p₀.f 0 = f := ChainComplex.toSingle₀Equiv_symm_apply_f_zero f hf
  have hep : Epi f := (ModuleCat.epi_iff_surjective f).2 Q.surjective
  have ex₀ : (ShortComplex.mk (Q.complex.d 1 0) f hf).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact LinearMap.exact_iff.mpr Q.exact_zero.symm
  have hp₀ : QuasiIso p₀ := by
    constructor
    intro j
    cases j with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact (ShortComplex.exact_and_epi_g_iff_of_iso
          (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
            (by simp) (by simp [h₀]))).2 ⟨ex₀, hep⟩
      all_goals simp [HomologicalComplex.shortComplexFunctor']
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [exactAt_iff' Q.complex (n + 2) (n + 1) n ((down ℕ).prev_eq' (show (down ℕ).Rel (n + 2) (n + 1) by rfl))
        ((down ℕ).next_eq' (show (down ℕ).Rel (n + 1) n by rfl)),
        ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact LinearMap.exact_iff.mpr (Q.exact_succ n).symm
  let P := Q.complex.extend embeddingDownNat
  let k := (ChainComplex.single₀ (ModuleCat.{max u v} A)).obj M
  let e : k.extend embeddingDownNat ≅ (stalkValue A).obj M :=
    HomologicalComplex.extendSingleIso embeddingDownNat M 0 0 rfl
  let p : P ⟶ (stalkValue A).obj M := extendMap p₀ embeddingDownNat ≫ e.hom
  refine ⟨P, p, inferInstance, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ≤ 0
    · have h : embeddingDownNat.f j.natAbs = j := by
        change -(j.natAbs : ℤ) = j
        omega
      letI : Module.Finite A (Q.complex.X j.natAbs) := hfin _
      exact Module.Finite.of_surjective ((Q.complex.extendXIso embeddingDownNat h).inv.hom)
        (ModuleCat.epi_iff_surjective _ |>.1 inferInstance)
    · letI : Subsingleton (P.X j) := ModuleCat.subsingleton_of_isZero
        (CochainComplex.isZero_of_isStrictlyLE P 0 j (by omega))
      infer_instance
  · letI (n : ℕ) : Module.Free A (Q.complex.X n) := hfree n
    letI (n : ℕ) : Projective (Q.complex.X n) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis A (Q.complex.X n))
    exact fun j => inferInstance
  · letI : QuasiIso (extendMap p₀ embeddingDownNat) :=
      (quasiIso_extendMap_iff p₀ embeddingDownNat).2 hp₀
    dsimp [p]
    infer_instance

end Resolution

section FiniteDiagonals

open Specs.DerivedFormalization.CochainModels (internalHomProductValue)

variable {A : Type u} {S : Type z} [CommRing A] [CommRing S]

private def restrictProduct {K : Type u} [CommRing K] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (F : Finset ℤ)
    (h : ∀ i, i ∉ F → Subsingleton (V i)) :
    (∀ i, V i) ≃ₗ[K] (∀ i : F, V i) where
  toFun z i := z i
  invFun z i := if hi : i ∈ F then z ⟨i, hi⟩ else 0
  left_inv z := by
    funext i
    by_cases hi : i ∈ F
    · simp [hi]
    · letI := h i hi
      exact Subsingleton.elim _ _
  right_inv z := by
    funext i
    simp [i.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem homSubsingleton {K : Type u} [CommRing K] {M N : ModuleCat.{v} K}
    (h : IsZero M ∨ IsZero N) : Subsingleton (M →ₗ[K] N) := by
  rcases h with h | h
  · letI := ModuleCat.subsingleton_of_isZero h
    exact ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x (0 : M), map_zero, map_zero]⟩
  · letI := ModuleCat.subsingleton_of_isZero h
    infer_instance

private def homTermEquiv (g : A →+* S)
    (hg : letI := g.toAlgebra; Module.Flat A S)
    (M N : ModuleCat.{max z v} A) [Module.FinitePresentation A M] :
    ((extend.{_,_,max z v} g).obj (ModuleCat.of A (M →ₗ[A] N))) ≃ₗ[S]
        ((extend.{_,_,max z v} g).obj M →ₗ[S] (extend.{_,_,max z v} g).obj N) := by
  letI : Algebra A S := g.toAlgebra
  letI : Module.Flat A S := hg
  exact (Module.FinitePresentation.isBaseChange_map A M N S).equiv

private theorem homTermEquiv_one (g : A →+* S)
    (hg : letI := g.toAlgebra; Module.Flat A S)
    (M N : ModuleCat.{max z v} A) [Module.FinitePresentation A M] (f : M →ₗ[A] N) :
    homTermEquiv g hg M N (pure g 1 f) = ((extend.{_,_,max z v} g).map (ModuleCat.ofHom f)).hom := by
  letI : Algebra A S := g.toAlgebra
  letI : Module.Flat A S := hg
  exact ((Module.FinitePresentation.isBaseChange_map A M N S).equiv_tmul 1 f).trans (one_smul S _)

private theorem homChange_isIso_aux (g : A →+* S) (hg : letI := g.toAlgebra; Module.Flat A S)
    (P I : compValue.{max z v} A) (a b : ℤ) [I.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ i, Module.FinitePresentation A (P.X i)) : letI := g.toAlgebra
    IsIso (homChange (S := S) P I) := by
  letI : Algebra A S := g.toAlgebra
  let E := extend.{_,_,max z v} g
  have hn (n : ℤ) : IsIso ((homChange (S := S) P I).f n) := by
    -- In degree n, both Hom products are supported on the same finite interval.
    let F := Finset.Icc (a - n) b
    have hz (i : ℤ) (hi : i ∉ F) : IsZero (P.X i) ∨ IsZero (I.X (i + n)) := by
      have h' : ¬ (a - n ≤ i ∧ i ≤ b) := by simpa [F] using hi
      by_cases hb : i ≤ b
      · exact Or.inr (I.isZero_of_isStrictlyGE a _ (by omega))
      · exact Or.inl (P.isZero_of_isStrictlyLE b _ (by omega))
    let e₁ := internalHomProductValue P I n ≪≫ₗ
      restrictProduct (K := A) F (fun i hi => homSubsingleton (hz i hi))
    let e₂ := internalHomProductValue ((extC (S := S)).obj P) ((extC (S := S)).obj I) n ≪≫ₗ
      restrictProduct (K := S) F (fun i hi => homSubsingleton
        ((hz i hi).imp (Functor.map_isZero E) (Functor.map_isZero E)))
    let ePi : (E.obj (ModuleCat.of A (∀ i : F, P.X i →ₗ[A] I.X (i + n)))) ≃ₗ[S]
        (∀ i : F, E.obj (ModuleCat.of A (P.X i →ₗ[A] I.X (i + n)))) :=
      TensorProduct.piRight A S S _
    let eAt (i : F) := by
      letI := hP (i : ℤ)
      exact homTermEquiv g hg (P.X i) (I.X (i + n))
    let e := (E.mapIso e₁.toModuleIso).toLinearEquiv ≪≫ₗ
      ePi ≪≫ₗ LinearEquiv.piCongrRight eAt ≪≫ₗ e₂.symm
    have he : (homChange (S := S) P I).f n = e.toModuleIso.hom := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro z
      change homChangeTerm (S := S) P I n (pure g 1 z) = e (pure g 1 z)
      apply e₂.injective
      rw [homChangeTerm_one]
      funext i
      letI := hP (i : ℤ)
      change e₂ _ i = e₂ (e₂.symm _) i
      rw [e₂.apply_symm_apply]
      change _ = eAt i (ePi (((E.mapIso e₁.toModuleIso).hom)
        (pure g 1 z)) i)
      rw [Functor.mapIso_hom, ModuleCat.ExtendScalars.map_tmul]
      change ((E.map (z.v i (i + n) rfl)).hom) =
        homTermEquiv g hg (P.X i) (I.X (i + n))
          (pure g 1 ((z.v i (i + n) rfl).hom))
      exact (homTermEquiv_one g hg _ _ _).symm
    rw [he]
    infer_instance
  letI := hn
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem homChange_isIso [Algebra A S] [Module.Flat A S]
    (P I : compValue.{max z v} A) (a b : ℤ) [I.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ i, Module.FinitePresentation A (P.X i)) :
    IsIso (homChange (S := S) P I) := by
  have hg : letI := (algebraMap A S).toAlgebra; Module.Flat A S := by
    rw [toAlgebra_algebraMap]
    infer_instance
  let IsComparisonIso (alg : Algebra A S) : Prop :=
    letI := alg
    IsIso (homChange (S := S) P I)
  exact (congrArg IsComparisonIso toAlgebra_algebraMap).mp
    (homChange_isIso_aux (algebraMap A S) hg P I a b hP)

end FiniteDiagonals

section CoinductionModel

set_option quotPrecheck false
set_option hygiene false

local notation "f" => algebraMap A B
local notation "s" => algebraMap A S
local notation "t" => rightMap A B S
local notation "f'" => bottomMap A B S
local notation "R₀" => restrictedRegular.{max u w z v} f
local notation "R₁" => restrictedRegular.{max u w z v} f'
local notation "K₀" => (stalkValue A).obj R₀
local notation "K₁" => (stalkValue S).obj R₁
local notation "E" => extend.{_,_,max u w z v} s
local notation "EC" => extendC.{_,_,max u w z v} s
local notation "EBC" => extendC.{_,_,max u w z v} t
local notation "Res₀" => restrictScalarsComplexValue.{max u w z v} f
local notation "Res₁" => restrictScalarsComplexValue.{max u w z v} f'
local notation "Co₀" => coinduceValue.{max u w z v} f
local notation "Co₁" => coinduceValue.{max u w z v} f'

private abbrev coAdj {K : Type u} {L : Type w} [CommRing K] [CommRing L] (g : K →+* L) :=
  ModuleCat.restrictCoextendScalarsAdj.{v,u,w} g

private abbrev coext {K : Type u} {L : Type w} [CommRing K] [CommRing L] (g : K →+* L) :=
  ModuleCat.coextendScalars.{u,w,max w v} g

private def coinductionModuleComparison (e : RestrictionSquare.{u,w,z,v} A B S) :
    coext.{_,_,max u w z v} f ⋙ extend.{_,_,max u w z v} t ⟶ E ⋙ coext.{_,_,max u w z v} f' where
  app M := (coAdj.{_,_,max u w z v} f').homEquiv _ _
    (e.hom.app ((coext.{_,_,max u w z v} f).obj M) ≫ (E).map ((coAdj.{_,_,max u w z v} f).counit.app M))
  naturality M N x := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← (coAdj.{_,_,max u w z v} f').homEquiv_naturality_left,
      ← (coAdj.{_,_,max u w z v} f').homEquiv_naturality_right]
    congr 1
    have he := e.hom.naturality ((coext.{_,_,max u w z v} f).map x)
    have hx := (coAdj.{_,_,max u w z v} f).counit.naturality x
    dsimp only [Functor.comp_map, Functor.id_map] at he hx
    rw [← Category.assoc, he, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, hx]

private def coinductionChainComparison (e : RestrictionSquare.{u,w,z,v} A B S)
    (I : compValue.{max u w z v} A) : (EBC).obj ((Co₀).obj I) ⟶ (Co₁).obj ((EC).obj I) := by
  letI := (coAdj.{_,_,max u w z v} f).right_adjoint_additive
  letI := (coAdj.{_,_,max u w z v} f').right_adjoint_additive
  exact (NatTrans.mapHomologicalComplex (coinductionModuleComparison.{u,w,z,v} A B S e) (.up ℤ)).app I

private def squareC (e : RestrictionSquare.{u,w,z,v} A B S) :
    EBC ⋙ Res₁ ≅ Res₀ ⋙ EC :=
  NatIso.mapHomologicalComplex e (.up ℤ)

private theorem coinductionChainComparison_evaluation (e : RestrictionSquare.{u,w,z,v} A B S)
    (I : compValue.{max u w z v} A) :
    (Res₁).map (coinductionChainComparison.{u,w,z,v} A B S e I) ≫
      evaluationValue.{max u w z v} f' ((EC).obj I) =
      (squareC.{u,w,z,v} A B S e).hom.app ((Co₀).obj I) ≫ (EC).map (evaluationValue.{max u w z v} f I) := by
  ext n : 1
  let e' := (coAdj.{_,_,max u w z v} f').homEquiv
    ((extend.{_,_,max u w z v} t).obj ((coext.{_,_,max u w z v} f).obj (I.X n))) ((E).obj (I.X n))
  let k := e.hom.app ((coext.{_,_,max u w z v} f).obj (I.X n)) ≫
    (E).map ((coAdj.{_,_,max u w z v} f).counit.app (I.X n))
  exact ((coAdj.{_,_,max u w z v} f').homEquiv_counit (g := e' k)).symm.trans
    (Equiv.symm_apply_apply e' k)

private abbrev regular (L : Type u) [CommRing L] := ModuleCat.of L (ULift.{v} L)

private def regularMap :
    regular.{_,max u w z v} B ⟶ (restrict.{_,_,max u w z v} t).obj (regular.{_,max u w z v} D) :=
  ConcreteCategory.ofHom (C := ModuleCat B)
    { toFun := fun b => (show (restrict.{_,_,max u w z v} t).obj (regular.{_,max u w z v} D) from ⟨t b.down⟩)
      map_add' := fun x y => ULift.ext (map_add t x.down y.down)
      map_smul' := fun b x => ULift.ext (map_mul t b x.down) }

private def regularExtendHom :
    (extend.{_,_,max u w z v} t).obj (regular.{_,max u w z v} B) ⟶ regular.{_,max u w z v} D :=
  ((ModuleCat.extendRestrictScalarsAdj.{max u w z v,_,_} t).homEquiv _ _).symm (regularMap.{u,w,z,v} A B S)

private theorem regularExtendHom_one (b : B) :
    regularExtendHom.{u,w,z,v} A B S (pure t 1 (⟨b⟩ : regular.{_,max u w z v} B)) = ⟨t b⟩ :=
  congrArg (fun k : regular.{_,max u w z v} B ⟶ _ => k ⟨b⟩)
    (Equiv.apply_symm_apply ((ModuleCat.extendRestrictScalarsAdj.{max u w z v,_,_} t).homEquiv _ _)
      (regularMap.{u,w,z,v} A B S))

private def regularExtendIso :
    (extend.{_,_,max u w z v} t).obj (regular.{_,max u w z v} B) ≅ regular.{_,max u w z v} D where
  hom := regularExtendHom.{u,w,z,v} A B S
  inv := ModuleCat.ofHom
    { toFun := fun d => d.down • pure t (M := regular.{_,max u w z v} B) 1 ⟨1⟩
      map_add' := fun x y => add_smul x.down y.down _
      map_smul' := fun d x => mul_smul d x.down _ }
  hom_inv_id := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (regularExtendHom.{u,w,z,v} A B S (pure t 1 x)).down •
      pure t (M := regular.{_,max u w z v} B) 1 ⟨1⟩ = pure t 1 x
    rw [regularExtendHom_one.{u,w,z,v} A B S x.down]
    change t x.down • pure t (M := regular.{_,max u w z v} B) 1 ⟨1⟩ = _
    letI : Module B D := Module.compHom D t
    rw [show t x.down • pure t (M := regular.{_,max u w z v} B) 1 ⟨1⟩ =
        pure t (M := regular.{_,max u w z v} B) (x.down • (1 : D)) ⟨1⟩ by
      exact ModuleCat.ExtendScalars.smul_tmul t (M := regular.{_,max u w z v} B) (t x.down) 1 ⟨1⟩]
    change ((x.down • (1 : D)) ⊗ₜ[B] (⟨1⟩ : regular.{_,max u w z v} B)) =
      (1 : D) ⊗ₜ[B] x
    rw [TensorProduct.smul_tmul]
    congr 1
    exact ULift.ext (mul_one x.down)
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x : 1
    change regularExtendHom.{u,w,z,v} A B S (x.down • pure t (M := regular.{_,max u w z v} B) 1 ⟨1⟩) = x
    rw [(regularExtendHom.{u,w,z,v} A B S).hom.map_smul]
    rw [regularExtendHom_one.{u,w,z,v} A B S 1, map_one]
    exact ULift.ext (mul_one x.down)

private def regularChange (e : RestrictionSquare.{u,w,z,v} A B S) : (E).obj R₀ ≅ R₁ :=
  e.symm.app (regular.{_,max u w z v} B) ≪≫
    (restrict.{_,_,max u w z v} f').mapIso (regularExtendIso.{u,w,z,v} A B S)

private theorem regularChange_one (e : RestrictionSquare.{u,w,z,v} A B S)
    (he : TensorFormula.{u,w,z,v} A B S e) (b : B) :
    (regularChange.{u,w,z,v} A B S e).hom (pure s 1 (⟨b⟩ : R₀)) = (⟨t b⟩ : R₁) := by
  change regularExtendHom.{u,w,z,v} A B S
    (e.inv.app (regular.{_,max u w z v} B) (pure s 1 (⟨b⟩ : R₀))) = _
  rw [he (regular.{_,max u w z v} B) 1 (⟨b⟩ : regular.{_,max u w z v} B)]
  rw [map_one]
  exact regularExtendHom_one.{u,w,z,v} A B S b

private def stalkChange (e : RestrictionSquare.{u,w,z,v} A B S) : (EC).obj K₀ ≅ K₁ :=
  (HomologicalComplex.singleMapHomologicalComplex (E) (.up ℤ) 0).app R₀ ≪≫
    (stalkValue S).mapIso (regularChange.{u,w,z,v} A B S e)

private theorem stalkChange_f_zero (e : RestrictionSquare.{u,w,z,v} A B S)
    (he : TensorFormula.{u,w,z,v} A B S e) (b : B) :
    (stalkChange.{u,w,z,v} A B S e).hom.f 0
        (pure s 1 ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 R₀).inv ⟨b⟩)) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 R₁).inv ⟨t b⟩ := by
  change
    (((HomologicalComplex.singleMapHomologicalComplex (E) (.up ℤ) 0).hom.app R₀).f 0 ≫
      ((stalkValue S).map (regularChange.{u,w,z,v} A B S e).hom).f 0) _ = _
  simp only [stalkValue, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self]
  simp only [ModuleCat.comp_apply]
  let i₀ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 R₀
  let i₁ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((E).obj R₀)
  let i₂ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 R₁
  let x : R₀ := ⟨b⟩
  have ht : (E).map i₀.hom (pure s 1 (i₀.inv x)) = pure s 1 x :=
    (ModuleCat.ExtendScalars.map_tmul s i₀.hom 1 (i₀.inv x)).trans
      (congrArg (pure s 1) (i₀.inv_hom_id_apply x))
  change i₂.inv ((regularChange.{u,w,z,v} A B S e).hom
    (i₁.hom (i₁.inv ((E).map i₀.hom (pure s 1 (i₀.inv x)))))) = _
  rw [ht, i₁.inv_hom_id_apply, regularChange_one.{u,w,z,v} A B S e he b]

private theorem coinductionModuleComparison_formula (e : RestrictionSquare.{u,w,z,v} A B S)
    (he : TensorFormula.{u,w,z,v} A B S e) (M : ModuleCat.{max u w z v} A)
    (z : (coext.{_,_,max u w z v} f).obj M) (b : B) :
    ModuleCat.CoextendScalars.equiv f' ((E).obj M)
      ((coinductionModuleComparison.{u,w,z,v} A B S e).app M
        (e.inv.app ((coext.{_,_,max u w z v} f).obj M)
          (pure s 1 (z : (restrict.{_,_,max u w z v} f).obj ((coext.{_,_,max u w z v} f).obj M))))) (t b) =
      pure s 1 (ModuleCat.CoextendScalars.equiv f M z b) := by
  let N := (coext.{_,_,max u w z v} f).obj M
  have hp (z' : N) :
      e.inv.app N (pure s 1 (z' : (restrict.{_,_,max u w z v} f).obj N)) =
        (pure t 1 z' : changedM.{u,w,z,v} A B S N) := by
    simpa only [map_one] using he N 1 z'
  let z₁ : (extend.{_,_,max u w z v} t).obj N :=
    e.inv.app N (pure s 1 (z : (restrict.{_,_,max u w z v} f).obj N))
  let sm : D → (extend.{_,_,max u w z v} t).obj N → (extend.{_,_,max u w z v} t).obj N := (· • ·)
  change (E).map ((coAdj.{_,_,max u w z v} f).counit.app M)
      (e.hom.app N (sm (t b) z₁)) = _
  have hmul : t b • (pure t 1 z : (extend.{_,_,max u w z v} t).obj N) = pure t 1 (b • z) := by
    letI : Module B D := Module.compHom D t
    exact (ModuleCat.ExtendScalars.smul_tmul t (t b) 1 z).trans (by
      change ((b • (1 : D)) ⊗ₜ[B] z) = _
      exact TensorProduct.smul_tmul (r := b) (m := (1 : D)) (n := z))
  have hsm : sm (t b) z₁ = e.inv.app N (pure s 1 (b • z : (restrict.{_,_,max u w z v} f).obj N)) :=
    (congrArg (sm (t b)) (hp z)).trans (hmul.trans (hp (b • z)).symm)
  rw [hsm]
  have hcancel := ConcreteCategory.congr_hom (e.inv_hom_id_app N)
    (pure s 1 (b • z : (restrict.{_,_,max u w z v} f).obj N))
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hcancel
  rw [hcancel]
  let v₀ : (restrict.{_,_,max u w z v} f).obj N := (b • z : N)
  change (E).map ((coAdj.{_,_,max u w z v} f).counit.app M) (pure s 1 v₀) = _
  refine (ModuleCat.ExtendScalars.map_tmul s ((coAdj.{_,_,max u w z v} f).counit.app M) 1 v₀).trans ?_
  apply congrArg (pure s 1)
  change (b • z : (coext.{_,_,max u w z v} f).obj M) (1 : B) = z b
  rw [ModuleCat.CoextendScalars.smul_apply, one_mul]

private def modelComparison (e : RestrictionSquare.{u,w,z,v} A B S)
    {I : compValue.{max u w z v} A} {J : compValue.{max u w z v} S} (j : (EC).obj I ⟶ J) :
    (EBC).obj ((Co₀).obj I) ⟶ (Co₁).obj J :=
  coinductionChainComparison.{u,w,z,v} A B S e I ≫ (Co₁).map j

private theorem modelComparison_evaluation (e : RestrictionSquare.{u,w,z,v} A B S)
    {I : compValue.{max u w z v} A} {J : compValue.{max u w z v} S} (j : (EC).obj I ⟶ J) :
    (Res₁).map (modelComparison.{u,w,z,v} A B S e j) ≫ evaluationValue.{max u w z v} f' J =
      (squareC.{u,w,z,v} A B S e).hom.app ((Co₀).obj I) ≫
        (EC).map (evaluationValue.{max u w z v} f I) ≫ j := by
  letI : (coext.{z,max w z,max u w z v} f').Additive :=
    (coAdj.{z,max w z,max u w z v} f').right_adjoint_additive
  have hj := (NatTrans.mapHomologicalComplex ((coAdj.{_,_,max u w z v} f').counit) (.up ℤ)).naturality j
  change (Res₁).map ((Co₁).map j) ≫ evaluationValue.{max u w z v} f' J =
    evaluationValue.{max u w z v} f' ((EC).obj I) ≫ j at hj
  rw [modelComparison, Functor.map_comp, Category.assoc, hj, ← Category.assoc,
    coinductionChainComparison_evaluation, Category.assoc]

variable [PreservesFiniteLimits (extend.{_,_,max u w z v} (algebraMap A S))]

private theorem homChange_model_quasiIso [IsNoetherianRing A] [Module.Finite A B] [Module.Flat A S]
    (I : compValue.{max u w z v} A) (a : ℤ) [I.IsStrictlyGE a] [I.IsKInjective]
    {J : compValue.{max u w z v} S} [J.IsKInjective] (j : (EC).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (homChange (S := S) K₀ I ≫ internalHomMapValue (𝟙 ((EC).obj K₀)) j) := by
  have hregular : Module.Finite A R₀ := by
    change Module.Finite A ((ModuleCat.restrictScalars f).obj (regular.{_,max u w z v} B))
    letI : Module A B := Module.compHom B f
    have h : (Module.compHom B f : Module A B) = Algebra.toModule := by
      apply Module.ext'
      intro a b
      exact (Algebra.smul_def a b).symm
    have hfin : @Module.Finite A B _ _ (Module.compHom B f) := by rw [h]; infer_instance
    letI : Module.Finite A B := hfin
    change Module.Finite A (ULift.{max u w z v} B)
    infer_instance
  obtain ⟨P, p, hpBound, hpFin, hpProj, hp⟩ := hasFiniteFreeResolution.{u,max u w z v} R₀
  letI : ((EC).obj P).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => Functor.map_isZero (E) (P.isZero_of_isStrictlyLE 0 i hi)
  have hPr (i : ℤ) : Projective (((EC).obj P).X i) :=
    (ModuleCat.extendRestrictScalarsAdj.{max u w z v,_,_} s).map_projective _ (hpProj i)
  letI : ((EC).obj P).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ 0
  have hIso := homChange_isIso (S := S) P I a 0 (fun n => by
    letI := hpFin n
    exact Module.finitePresentation_of_finite A (P.X n))
  haveI : QuasiIso ((EC).map (internalHomMapValue p (𝟙 I))) := by
    haveI : QuasiIso (internalHomMapValue p (𝟙 I)) :=
      internalHomMap_quasiIso_of_isKInjective I inferInstance p hp
    infer_instance
  haveI : QuasiIso (internalHomMapValue ((EC).map p) (𝟙 J)) :=
    internalHomMap_quasiIso_of_isKInjective J inferInstance _ inferInstance
  haveI : QuasiIso (internalHomMapValue (𝟙 ((EC).obj P)) j) :=
    internalHomMap_quasiIso_of_isKProjective ((EC).obj P) inferInstance j inferInstance
  -- Compare both Hom complexes with the source replaced by its projective resolution.
  have hnat := homChange_naturality (S := S) p (𝟙 I)
  have hpost :
      internalHomMapValue (𝟙 ((EC).obj K₀)) j ≫ internalHomMapValue ((EC).map p) (𝟙 J) =
        internalHomMapValue ((EC).map p) ((EC).map (𝟙 I)) ≫
          internalHomMapValue (𝟙 ((EC).obj P)) j := by
    change internalHomMap .. ≫ internalHomMap .. = internalHomMap .. ≫ internalHomMap ..
    rw [internalHomMap_comp, internalHomMap_comp, (EC).map_id]
    simp only [Category.id_comp, Category.comp_id]
  have hw := congrArg (· ≫ internalHomMapValue (𝟙 ((EC).obj P)) j) hnat
  have hrew : (homChange (S := S) K₀ I ≫ internalHomMapValue (𝟙 ((EC).obj K₀)) j) ≫
      internalHomMapValue ((EC).map p) (𝟙 J) =
      (EC).map (internalHomMapValue p (𝟙 I)) ≫
        homChange P I ≫ internalHomMapValue (𝟙 ((EC).obj P)) j := by
    rw [Category.assoc, hpost, ← Category.assoc, ← hw, Category.assoc]
  haveI : QuasiIso ((homChange (S := S) K₀ I ≫ internalHomMapValue (𝟙 ((EC).obj K₀)) j) ≫
      internalHomMapValue ((EC).map p) (𝟙 J)) := by
    rw [hrew]
    infer_instance
  exact quasiIso_of_comp_right _ (internalHomMapValue ((EC).map p) (𝟙 J))

private theorem modelComparison_quasiIso [IsNoetherianRing A] [Module.Finite A B] [Module.Flat A S]
    (e : RestrictionSquare.{u,w,z,v} A B S) (he : TensorFormula.{u,w,z,v} A B S e)
    (I : compValue.{max u w z v} A) (a : ℤ) [I.IsStrictlyGE a] [I.IsKInjective]
    {J : compValue.{max u w z v} S} [J.IsKInjective] (j : (EC).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (modelComparison.{u,w,z,v} A B S e j) := by
  obtain ⟨e₀, h₀⟩ := DerivedFormalization.Coinduction.stalkComparison.{max u w z v,_,_} f I
  obtain ⟨e₁, h₁⟩ := DerivedFormalization.Coinduction.stalkComparison.{max u w z v,_,_} f' J
  let k := (stalkChange.{u,w,z,v} A B S e).hom
  haveI : QuasiIso (internalHomMapValue k (𝟙 J)) :=
    internalHomMap_quasiIso_of_isKInjective J inferInstance k inferInstance
  haveI := homChange_model_quasiIso.{u,w,z,v} A B S I a j
  let F := (EC).map e₀.hom ≫ (squareC.{u,w,z,v} A B S e).inv.app ((Co₀).obj I)
  haveI : IsIso F := by dsimp [F]; infer_instance
  have hcomm : (F ≫ (Res₁).map (modelComparison.{u,w,z,v} A B S e j)) ≫
      e₁.inv ≫ internalHomMapValue k (𝟙 J) =
      homChange (S := S) K₀ I ≫ internalHomMapValue (𝟙 ((EC).obj K₀)) j := by
    ext n : 1
    apply ModuleCat.ExtendScalars.hom_ext
    intro z
    apply Cochain.ext
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      obtain rfl : n = q := by omega
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      obtain ⟨⟨b⟩, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 R₀).inv)).1
          inferInstance x
      let x' := pure s 1 ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 R₀).inv (⟨b⟩ : R₀))
      let z' := e₀.hom.f n z
      let zS := (coinductionModuleComparison.{u,w,z,v} A B S e).app (I.X n)
        (e.inv.app ((coext.{_,_,max u w z v} f).obj (I.X n)) (pure s 1 z'))
      let zJ := ((Co₁).map j).f n zS
      have hF : F.f n (pure s 1 z) =
          e.inv.app ((coext.{_,_,max u w z v} f).obj (I.X n)) (pure s 1 z') := by
        change e.inv.app ((coext.{_,_,max u w z v} f).obj (I.X n))
          (((E).map (e₀.hom.f n)) (pure s 1 z)) = _
        exact congrArg (e.inv.app ((coext.{_,_,max u w z v} f).obj (I.X n)))
          (ModuleCat.ExtendScalars.map_tmul s (e₀.hom.f n) 1 z)
      simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
      change ((internalHomMapValue k (𝟙 J)).f n
        (e₁.inv.f n (((Res₁).map (modelComparison.{u,w,z,v} A B S e j)).f n
          (F.f n (pure s 1 z))))).v 0 n (zero_add n) x' =
        ((internalHomMapValue (𝟙 ((EC).obj K₀)) j).f n
          (homChangeTerm (S := S) K₀ I n (pure s 1 z))).v 0 n (zero_add n) x'
      rw [hF]
      change ((internalHomMap k (𝟙 J)).f n (e₁.inv.f n zJ)).v
          0 n (zero_add n) x' =
        ((internalHomMap (𝟙 ((EC).obj K₀)) j).f n
          (homChangeTerm (S := S) K₀ I n (pure s 1 z))).v 0 n (zero_add n) x'
      rw [internalHomMap_apply, internalHomMap_apply, homChangeTerm_one]
      change (e₁.inv.f n zJ).v 0 n (zero_add n) (k.f 0 x') =
        j.f n (((E).map (z.v 0 n (zero_add n))) x')
      rw [stalkChange_f_zero.{u,w,z,v} A B S e he b]
      rw [← h₁ n (e₁.inv.f n zJ) (t b)]
      have hcancel : e₁.hom.f n (e₁.inv.f n zJ) = zJ := by
        exact congrArg (fun h => h zJ) (congrArg (fun g => g.f n) e₁.inv_hom_id)
      rw [hcancel]
      change j.f n (ModuleCat.CoextendScalars.equiv f' ((EC).obj I |>.X n) zS (t b)) =
        j.f n (((E).map (z.v 0 n (zero_add n))) x')
      congr 1
      let zB : (coext.{_,_,max u w z v} f).obj (I.X n) := z'
      calc
        _ = pure s 1 (ModuleCat.CoextendScalars.equiv f (I.X n) zB b) :=
          coinductionModuleComparison_formula.{u,w,z,v} A B S e he (I.X n) zB b
        _ = _ :=
          (congrArg (pure s (M := I.X n) 1) (h₀ n z b)).trans
            (ModuleCat.ExtendScalars.map_tmul s (z.v 0 n (zero_add n)) 1
              ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 R₀).inv ⟨b⟩)).symm
    · exact ((E).map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 R₀ p hp)).eq_of_src _ _
  haveI : QuasiIso ((F ≫ (Res₁).map (modelComparison.{u,w,z,v} A B S e j)) ≫
      e₁.inv ≫ internalHomMapValue k (𝟙 J)) := by rw [hcomm]; infer_instance
  haveI := quasiIso_of_comp_right
    (F ≫ (Res₁).map (modelComparison.{u,w,z,v} A B S e j)) (e₁.inv ≫ internalHomMapValue k (𝟙 J))
  haveI := quasiIso_of_comp_left F ((Res₁).map (modelComparison.{u,w,z,v} A B S e j))
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (restrict.{_,_,max u w z v} f')).mp inferInstance

open Specs.DerivedFormalization.DerivedCoinduction (Coinduction)

local notation "EF" => extendFactors.{u,z,max u w z v} s
local notation "EBF" => extendFactors.{w,max w z,max u w z v} t
local notation "ED" => extendD.{_,_,max u w z v} s
local notation "EBD" => extendD.{_,_,max u w z v} t
local notation "RD₀" => derivedRestrictScalarsValue.{max u w z v} f
local notation "RD₁" => derivedRestrictScalarsValue.{max u w z v} f'
local notation "RF₀" => (restrict.{_,_,max u w z v} f).mapDerivedCategoryFactors
local notation "RF₁" => (restrict.{_,_,max u w z v} f').mapDerivedCategoryFactors

variable [PreservesFiniteLimits (extend.{_,_,max u w z v} (rightMap A B S))]

private theorem square_on_model (e : RestrictionSquare.{u,w,z,v} A B S)
    (X : compValue.{max u w z v} B) :
    (derivedSquare.{u,w,z,v} A B S e).hom.app ((qValue B).obj X) =
      (factorsRight.{u,w,z,v} A B S).hom.app X ≫
        (qValue S).map ((squareC.{u,w,z,v} A B S e).hom.app X) ≫ (factorsLeft.{u,w,z,v} A B S).inv.app X := by
  unfold derivedSquare
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  rfl

private theorem comparison_iso_on_injective_model
    [IsNoetherianRing A] [Module.Finite A B] [Module.Flat A S]
    (G : Coinduction.{max u w z v} f) (G' : Coinduction.{max u w z v} f')
    (e : RestrictionSquare.{u,w,z,v} A B S) (he : TensorFormula.{u,w,z,v} A B S e)
    (I : compValue.{max u w z v} A) (a : ℤ) [I.IsStrictlyGE a] [I.IsKInjective]
    {J : compValue.{max u w z v} S} [J.IsKInjective] (j : (EC).obj I ⟶ J) [QuasiIso j] :
    IsIso ((comparison.{u,w,z,v} A B S e G G').app ((qValue A).obj I)) := by
  let X := (Co₀).obj I
  let Y := (Co₁).obj J
  let c := modelComparison.{u,w,z,v} A B S e j
  let Y₀ := (qValue A).obj I
  let γ₀ := Specs.DerivedFormalization.DerivedCoinduction.comparison.{max u w z v} f G.adjunction I
  let γ₁ := Specs.DerivedFormalization.DerivedCoinduction.comparison.{max u w z v} f' G'.adjunction J
  let α := (EBF).hom.app X
  let β := (EF).hom.app I
  let βJ := β ≫ (qValue S).map j
  let τ : (EBD).obj (G.functor.obj Y₀) ⟶ G'.functor.obj ((ED).obj Y₀) :=
    (comparison.{u,w,z,v} A B S e G G').app Y₀
  haveI : IsIso γ₀ := G.comparison_isIso I inferInstance
  haveI : IsIso γ₁ := G'.comparison_isIso J inferInstance
  haveI : QuasiIso c := modelComparison_quasiIso.{u,w,z,v} A B S e he I a j
  haveI : IsIso ((qValue D).map c) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ c).2 inferInstance
  haveI : IsIso ((qValue S).map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ j).2 inferInstance
  have ev₀ : (RD₀).map γ₀ ≫ G.adjunction.counit.app Y₀ =
      (RF₀).hom.app X ≫ (qValue A).map (evaluationValue.{max u w z v} f I) := by
    exact (G.adjunction.homEquiv_counit (g := γ₀)).symm.trans
      (Equiv.symm_apply_apply _ _)
  have ev₁ : (G'.adjunction.homEquiv _ _).symm γ₁ =
      (RF₁).hom.app Y ≫ (qValue S).map (evaluationValue.{max u w z v} f' J) :=
    Equiv.symm_apply_apply _ _
  have htrace :
      (G'.adjunction.homEquiv _ _).symm τ =
        (derivedSquare.{u,w,z,v} A B S e).hom.app (G.functor.obj Y₀) ≫
          (ED).map (G.adjunction.counit.app Y₀) :=
    Equiv.symm_apply_apply _ _
  have hnat := (derivedSquare.{u,w,z,v} A B S e).hom.naturality γ₀
  change (RD₁).map ((EBD).map γ₀) ≫ _ =
    (derivedSquare.{u,w,z,v} A B S e).hom.app ((qValue B).obj X) ≫ (ED).map ((RD₀).map γ₀) at hnat
  have ha :
      (RD₁).map α ≫ (RF₁).hom.app ((EBC).obj X) = (factorsRight.{u,w,z,v} A B S).hom.app X := by
    simp [α, factorsRight]
  have hb :
      (factorsLeft.{u,w,z,v} A B S).inv.app X ≫ (ED).map ((RF₀).hom.app X) =
        (EF).inv.app ((Res₀).obj X) := by
    simp [factorsLeft, ← Functor.map_comp]
  have h :
      (EBD).map γ₀ ≫ τ ≫ G'.functor.map βJ =
        α ≫ (qValue D).map c ≫ γ₁ := by
    -- Transpose both maps and compare their localized evaluation maps.
    apply (G'.adjunction.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
      htrace, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm, ev₁]
    simp only [Category.assoc]
    rw [reassoc_of% hnat, ← Functor.map_comp_assoc, ev₀, Functor.map_comp, square_on_model]
    simp only [Category.assoc]
    rw [reassoc_of% hb]
    have hβ := (EF).hom.naturality (evaluationValue.{max u w z v} f I)
    change (ED).map ((qValue A).map (evaluationValue.{max u w z v} f I)) ≫ β =
      (EF).hom.app ((Res₀).obj X) ≫
        (qValue S).map ((EC).map (evaluationValue.{max u w z v} f I)) at hβ
    rw [show βJ = β ≫ (qValue S).map j from rfl, ← Category.assoc
      ((ED).map ((qValue A).map (evaluationValue.{max u w z v} f I))), hβ]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    have hα := (restrict.{_,_,max u w z v} f').mapDerivedCategoryFactors_hom_naturality c
    change (RD₁).map ((qValue D).map c) ≫ (RF₁).hom.app Y =
      (RF₁).hom.app ((EBC).obj X) ≫ (qValue S).map ((Res₁).map c) at hα
    rw [reassoc_of% hα, ← Category.assoc ((RD₁).map α), ha]
    simp only [← Functor.map_comp]
    have hc := modelComparison_evaluation.{u,w,z,v} A B S e j
    change (Res₁).map c ≫ evaluationValue.{max u w z v} f' J =
      (squareC.{u,w,z,v} A B S e).hom.app X ≫ (EC).map (evaluationValue.{max u w z v} f I) ≫ j at hc
    rw [hc]
  haveI : IsIso ((EBD).map γ₀ ≫ τ ≫ G'.functor.map βJ) := by rw [h]; infer_instance
  exact (isIso_comp_right_iff τ (G'.functor.map βJ)).1
    ((isIso_comp_left_iff ((EBD).map γ₀) _).1 inferInstance)

/-- Flat base change for the finite affine right adjoint, including its trace. -/
theorem flatCoinductionBaseChange : BaseChange.{u,w,z,v} := by
  intro A B S _ _ _ _ _ _ _ _ G G'
  letI : PreservesFiniteLimits (extend.{_,_,max u w z v} (algebraMap A S)) :=
    extendPreservesFiniteLimits.{u,z,max u w z v} (algebraMap A S) (by
      have h : (Module.compHom S (algebraMap A S) : Module A S) = Algebra.toModule :=
        Module.ext' _ _ (fun a x => (Algebra.smul_def a x).symm)
      rw [h]
      infer_instance)
  letI : PreservesFiniteLimits (extend.{_,_,max u w z v} (rightMap A B S)) :=
    extendPreservesFiniteLimits.{w,max w z,max u w z v} (rightMap A B S) (rightMapFlat A B S)
  let e := restrictionSquare.{u,w,z,v} A B S
  have he := restrictionSquare_formula.{u,w,z,v} A B S
  refine ⟨inferInstance, inferInstance, e, he, traceCompatibility.{u,w,z,v} A B S e G G', ?_⟩
  let incl : DerivedCategory.Plus (ModuleCat.{max u w z v} A) ⥤ derivedValue.{max u w z v} A :=
    DerivedCategory.Plus.ι
  let τ := Functor.whiskerLeft incl (comparison.{u,w,z,v} A B S e G G')
  haveI (Y : DerivedCategory.Plus (ModuleCat.{max u w z v} A)) : IsIso (τ.app Y) := by
    obtain ⟨a, I, hI, hBound, ⟨i⟩⟩ :=
      AdvancedHomologicalAlgebra.InjectiveComplexReplacement.plusRepresentative
        (ModuleCat.{max u w z v} A) Y
    letI : ∀ n, Injective (I.X n) := hI
    letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
    let IC := (extendC.{_,_,max u w z v} (algebraMap A S)).obj I
    have hIC : IC.IsStrictlyGE a := by
      rw [CochainComplex.isStrictlyGE_iff]
      exact fun n hn => (extend.{_,_,max u w z v} (algebraMap A S)).map_isZero
        (I.isZero_of_isStrictlyGE a n hn)
    obtain ⟨J, j, _, hq, hJ, hJBound⟩ :=
      AdvancedHomologicalAlgebra.InjectiveComplexReplacement.replacement
        (ModuleCat.{max u w z v} S) IC a hIC
    letI : ∀ n, Injective (J.X n) := hJ
    letI : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
    haveI := comparison_iso_on_injective_model.{u,w,z,v} A B S G G' e he I a j
    exact (NatTrans.isIso_app_iff_of_iso (comparison.{u,w,z,v} A B S e G G') i).2 inferInstance
  haveI := NatIso.isIso_of_isIso_app τ
  exact ⟨asIso τ, rfl⟩

private theorem squareMate_replaceExtensions
    (e : RestrictionSquare.{u,w,z,v} A B S)
    (G : Coinduction.{max u w z v} f) (G' : Coinduction.{max u w z v} f')
    {L : derivedValue.{max u w z v} A ⥤ derivedValue.{max u w z v} S}
    {L' : derivedValue.{max u w z v} B ⥤ derivedValue.{max u w z v} D}
    (α : (ED) ≅ L) (β : (EBD) ≅ L') (Y : derivedValue.{max u w z v} A) :
    (squareMate.{u,w,z,v} A B S G G' (replaceExtensions.{u,w,z,v} A B S e α β)).app Y =
      β.inv.app (G.functor.obj Y) ≫ (comparison.{u,w,z,v} A B S e G G').app Y ≫
        G'.functor.map (α.hom.app Y) := by
  apply (G'.adjunction.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  simp only [comparison, squareMate, Equiv.symm_apply_apply, replaceExtensions, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc]
  have h := α.hom.naturality (G.adjunction.counit.app Y)
  dsimp only [Functor.comp_obj, Functor.id_obj] at h
  rw [h]

/-- Flat base change for the original U09 left extensions and the U14 counits. -/
theorem flatCoinductionBaseChangeOnExtensions : BaseChangeOnExtensions.{u,w,z,v} := by
  intro A B S _ _ _ _ _ _ _ _ G G' S₀ D₀ _ _ dS dD L L'
  obtain ⟨h, h', e, he, _, iso, hiso⟩ := flatCoinductionBaseChange.{u,w,z,v} A B S G G'
  letI := h
  letI := h'
  let α := (flatExtensionAdjunction.{u,z,max u w z v} s).leftAdjointUniq L.adj
  let β := (flatExtensionAdjunction.{w,max w z,max u w z v} t).leftAdjointUniq L'.adj
  let σ := replaceExtensions.{u,w,z,v} A B S e α β
  let incl : DerivedCategory.Plus (ModuleCat.{max u w z v} A) ⥤ derivedValue.{max u w z v} A :=
    DerivedCategory.Plus.ι
  refine ⟨h, h', e, he, squareMate_trace.{u,w,z,v} A B S G G' σ, ?_⟩
  refine ⟨Functor.isoWhiskerLeft incl (Functor.isoWhiskerLeft G.functor β.symm) ≪≫ iso ≪≫
    Functor.isoWhiskerLeft incl (Functor.isoWhiskerRight α G'.functor), ?_⟩
  apply NatTrans.ext
  funext Y
  change β.inv.app (G.functor.obj (incl.obj Y)) ≫ iso.hom.app Y ≫
      G'.functor.map (α.hom.app (incl.obj Y)) =
    (squareMate.{u,w,z,v} A B S G G' σ).app (incl.obj Y)
  have hy := congrArg (fun η => η.app Y) hiso
  change iso.hom.app Y = (comparison.{u,w,z,v} A B S e G G').app (incl.obj Y) at hy
  rw [hy]
  exact (squareMate_replaceExtensions.{u,w,z,v} A B S e G G' α β (incl.obj Y)).symm

end CoinductionModel

end

end DerivedFormalization.FlatCoinductionBaseChange
