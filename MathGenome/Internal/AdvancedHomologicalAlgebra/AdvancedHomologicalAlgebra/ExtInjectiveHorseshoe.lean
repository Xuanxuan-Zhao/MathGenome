import Mathlib.Algebra.Homology.HomologySequenceLemmas
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.BoundedKModels
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtShiftedHom
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtBoundarySigns

/-! The injective horseshoe with prescribed, independently bounded endpoint models. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex HomologicalComplex HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

namespace AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe

universe w v u
variable {A : Type u} [Category.{v} A] [Abelian A]

private lemma precomp_injective {F G I : CochainComplex A ℤ} (p : F ⟶ G)
    (hp : ∀ i, Epi (p.f i)) (n : ℤ) :
    Function.Injective (fun z : Cochain G I n => (Cochain.ofHom p).comp z (zero_add n)) := by
  intro z z' h
  ext i j hij
  have := hp i
  apply (cancel_epi (p.f i)).mp
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    Cochain.congr_v h i j hij

private lemma extend_cochain {F G I : CochainComplex A ℤ} (p : F ⟶ G)
    (hp : ∀ i, Mono (p.f i)) (hI : ∀ i, Injective (I.X i))
    {n : ℤ} (z : Cochain F I n) :
    ∃ y : Cochain G I n, (Cochain.ofHom p).comp y (zero_add n) = z := by
  let := hp
  let := hI
  refine ⟨Cochain.mk (fun i j hij => Injective.factorThru (z.v i j hij) (p.f i)), ?_⟩
  ext i j hij
  simp

private lemma descend_cochain {T : ShortComplex (CochainComplex A ℤ)}
    (hT : T.ShortExact) {I : CochainComplex A ℤ} {n : ℤ} (z : Cochain T.X₂ I n)
    (hz : (Cochain.ofHom T.f).comp z (zero_add n) = 0) :
    ∃ y : Cochain T.X₃ I n, (Cochain.ofHom T.g).comp y (zero_add n) = z := by
  have h (i j : ℤ) (hij : i + n = j) :
      T.f.f i ≫ z.v i j hij = 0 := by
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using
      Cochain.congr_v hz i j hij
  let hs i := hT.map_of_exact (eval A (.up ℤ) i)
  let (i : ℤ) : Epi (T.map (eval A (.up ℤ) i)).g := (hs i).epi_g
  refine ⟨Cochain.mk (fun i j hij => (hs i).exact.desc (z.v i j hij) (h i j hij)), ?_⟩
  ext i j hij
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  exact (hs i).exact.g_desc (z.v i j hij) (h i j hij)

private lemma mono_stalk_quasiIso {X : A} {J : CochainComplex A ℤ}
    (j : Stalk X ⟶ J) (hj : QuasiIso j) (n : ℤ) : Mono (j.f n) := by
  by_cases hn : n = 0
  · subst n
    have : IsIso (homologyMap j 0) :=
      (quasiIsoAt_iff_isIso_homologyMap j 0).mp (hj.quasiIsoAt 0)
    have : IsIso ((Stalk X).homologyπ 0) :=
      (Stalk X).isIso_homologyπ (-1) 0 (by simp) (by simp [Stalk, CochainComplex.singleFunctor])
    have : IsIso ((Stalk X).iCycles 0) :=
      (Stalk X).isIso_iCycles 0 1 (by simp) (by simp [Stalk, CochainComplex.singleFunctor])
    have : Mono (cyclesMap j 0) := by
      apply mono_of_mono_fac (homologyπ_naturality j 0).symm
    rw [← IsIso.inv_hom_id_assoc ((Stalk X).iCycles 0) (j.f 0), ← cyclesMap_i]
    infer_instance
  · exact (isZero_single_obj_X (.up ℤ) 0 X n hn).mono _

/-- Strict extension of a cocycle across a termwise monic quasi-isomorphism.
The coboundary of a termwise extension descends to the acyclic cokernel. -/
private lemma extend_cocycle {F G I : CochainComplex A ℤ} [I.IsKInjective]
    (p : F ⟶ G) (hp : ∀ i, Mono (p.f i)) (hq : QuasiIso p)
    (hI : ∀ i, Injective (I.X i)) {n : ℤ} (z : Cocycle F I n) :
    ∃ y : Cocycle G I n, y.precomp p = z := by
  let : Mono p := mono_of_mono_f p hp
  let T := ShortComplex.mk p (cokernel.π p) (cokernel.condition p)
  have hT : T.ShortExact := { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel p) }
  have hK : (cokernel p).Acyclic := hT.acyclic_X₃ hq
  have hepi (i : ℤ) : Epi ((cokernel.π p).f i) := (hT.map_of_exact (eval A (.up ℤ) i)).epi_g
  obtain ⟨y, hy⟩ := extend_cochain p hp hI z.1
  obtain ⟨c, hc⟩ := descend_cochain hT (δ n (n+1) y) (by
    change (Cochain.ofHom p).comp (δ n (n+1) y) (zero_add (n+1)) = 0
    rw [← δ_ofHom_comp, hy, z.δ_eq_zero])
  change (Cochain.ofHom (cokernel.π p)).comp c (zero_add (n+1)) = δ n (n+1) y at hc
  have hcz : δ (n+1) (n+2) c = 0 := by
    apply precomp_injective (cokernel.π p) hepi
    dsimp only
    rw [← δ_ofHom_comp, hc, δ_δ, Cochain.comp_zero]
  obtain ⟨d, hd⟩ :=
    CochainComplex.IsKInjective.eq_δ_of_cocycle (Cocycle.mk c (n+2) (by omega) hcz) hK n rfl
  change δ n (n+1) d = c at hd
  let d' := (Cochain.ofHom (cokernel.π p)).comp d (zero_add n)
  have hdy : δ n (n+1) (y - d') = 0 := by
    simp only [δ_sub, d', δ_ofHom_comp, hd, hc, sub_self]
  refine ⟨Cocycle.mk (y - d') (n+1) rfl hdy, Cocycle.ext ?_⟩
  change (Cochain.ofHom p).comp (y - d') (zero_add n) = z.1
  rw [Cochain.comp_sub, hy]
  simp [d', ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

private lemma offDiagonal_relation {I J : CochainComplex A ℤ} (α : Cocycle J I 1)
    (i : ℤ) :
    α.1.v i (i+1) rfl ≫ I.d (i+1) (i+1+1) +
      J.d i (i+1) ≫ α.1.v (i+1) (i+1+1) rfl = 0 := by
  have h := Cochain.congr_v (α.δ_eq_zero 2) i (i+1+1) (by omega)
  simpa only [δ_v 1 2 (by decide) _ i (i+1+1) (by omega) (i+1) (i+1)
    (by omega) rfl, Int.negOnePow_even 2 ⟨1, rfl⟩, one_smul, Cochain.zero_v] using h

/-- The off-diagonal entry cancels the differential of the chosen middle coaugmentation. -/
private noncomputable def horseshoeDifferential {I J : CochainComplex A ℤ}
    (α : Cocycle J I 1) (i j : ℤ) : I.X i ⊞ J.X i ⟶ I.X j ⊞ J.X j :=
  if h : i + 1 = j then
    biprod.lift (biprod.fst ≫ I.d i j - biprod.snd ≫ α.1.v i j h) (biprod.snd ≫ J.d i j)
  else 0

private lemma differential_eq {I J : CochainComplex A ℤ} (α : Cocycle J I 1)
    {i j : ℤ} (h : i + 1 = j) :
    horseshoeDifferential α i j =
      biprod.lift (biprod.fst ≫ I.d i j - biprod.snd ≫ α.1.v i j h) (biprod.snd ≫ J.d i j) :=
  dite_eq_left h

private noncomputable def twistedSum {I J : CochainComplex A ℤ} (α : Cocycle J I 1) :
    CochainComplex A ℤ where
  X i := I.X i ⊞ J.X i
  d := horseshoeDifferential α
  shape i j h := dite_eq_right (fun e => h (by simpa using e))
  d_comp_d' i j k hij hjk := by
    have eij : i + 1 = j := by simpa using hij
    have ejk : j + 1 = k := by simpa using hjk
    subst j
    subst k
    rw [differential_eq α rfl, differential_eq α rfl]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, comp_sub, biprod.lift_fst_assoc,
        biprod.lift_snd_assoc, sub_comp, d_comp_d, comp_zero, zero_comp, zero_sub]
      have h := (add_comm _ _).trans (offDiagonal_relation α i)
      rw [← neg_add_eq_sub, ← neg_add, ← comp_add, h, comp_zero, neg_zero]
    · simp

private noncomputable def twistedInclusion {I J : CochainComplex A ℤ} (α : Cocycle J I 1) :
    I ⟶ twistedSum α where
  f _ := biprod.inl
  comm' i j h := by
    have hij : i + 1 = j := by simpa using h
    change biprod.inl ≫ horseshoeDifferential α i j = I.d i j ≫ biprod.inl
    apply biprod.hom_ext <;>
      simp [horseshoeDifferential, hij, Category.assoc, comp_sub]

private noncomputable def twistedProjection {I J : CochainComplex A ℤ} (α : Cocycle J I 1) :
    twistedSum α ⟶ J where
  f _ := biprod.snd
  comm' i j h := by
    have hij : i + 1 = j := by simpa using h
    change biprod.snd ≫ J.d i j = horseshoeDifferential α i j ≫ biprod.snd
    simp [horseshoeDifferential, hij]

private noncomputable def twistedRow {I J : CochainComplex A ℤ} (α : Cocycle J I 1) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (twistedInclusion α) (twistedProjection α) (by
    ext n
    exact biprod.inl_snd)

private noncomputable def twistedSplitting {I J : CochainComplex A ℤ} (α : Cocycle J I 1) (n : ℤ) :
    ((twistedRow α).map (eval A (.up ℤ) n)).Splitting where
  r := biprod.fst
  s := biprod.inr
  f_r := biprod.inl_fst
  s_g := biprod.inr_snd
  id := biprod.total

private noncomputable def twistedAugmentation {K I J : CochainComplex A ℤ}
    (α : Cocycle J I 1) (e : Cochain K I 0) (q : K ⟶ J)
    (h : δ 0 1 e = (α.precomp q).1) : K ⟶ twistedSum α where
  f n := biprod.lift (e.v n n (add_zero n)) (q.f n)
  comm' i j hij := by
    have hij' : i + 1 = j := by simpa using hij
    apply biprod.hom_ext
    · change
        (biprod.lift (e.v i i (add_zero i)) (q.f i) ≫
            horseshoeDifferential α i j) ≫ biprod.fst =
          (K.d i j ≫ biprod.lift (e.v j j (add_zero j)) (q.f j)) ≫ biprod.fst
      have he := Cochain.congr_v h i j hij'
      simp only [δ_zero_cochain_v, Cocycle.precomp_coe, Cochain.zero_cochain_comp_v,
        Cochain.ofHom_v] at he
      simpa only [horseshoeDifferential, dite_eq_left hij', Category.assoc, biprod.lift_fst,
        comp_sub, biprod.lift_fst_assoc, biprod.lift_snd_assoc] using
        (sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _)))
    · change
        (biprod.lift (e.v i i (add_zero i)) (q.f i) ≫
            horseshoeDifferential α i j) ≫ biprod.snd =
          (K.d i j ≫ biprod.lift (e.v j j (add_zero j)) (q.f j)) ≫ biprod.snd
      simpa only [horseshoeDifferential, dite_eq_left hij', Category.assoc, biprod.lift_snd,
        biprod.lift_snd_assoc] using q.comm i j

private lemma quasiIso_middle {S T : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (ρ : S ⟶ T)
    (hi : QuasiIso ρ.τ₁) (hj : QuasiIso ρ.τ₃) : QuasiIso ρ.τ₂ := by
  let := HasDerivedCategory.standard A
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact Pretriangulated.isIso₂_of_isIso₁₃ (DerivedCategory.triangleOfSES.map hS hT ρ)
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.triangleOfSES_distinguished hT)
    (show IsIso (DerivedCategory.Q.map ρ.τ₁) from inferInstance)
    (show IsIso (DerivedCategory.Q.map ρ.τ₃) from inferInstance)

theorem exists_horseshoe : existsHorseshoeType := by
  intro A _ _ S hS I J i j hi hj hI hJ
  obtain ⟨bI, hbI⟩ := hI.1
  obtain ⟨bJ, hbJ⟩ := hJ.1
  have : I.IsKInjective := (BoundedKModels.kInjective_iff A I).mp
    (BoundedKModels.boundedBelow_injective A I bI hbI hI.2)
  obtain ⟨e, t, he, ht⟩ :=
    ExtBoundarySigns.first_lifts A S hS I hI.2 0 (Cocycle.ofHom i)
  obtain ⟨α, hα⟩ := extend_cocycle j (mono_stalk_quasiIso j hj) hj hI.2 t
  let q := (CochainComplex.singleFunctor A 0).map S.g ≫ j
  have hq : δ 0 1 e = (α.precomp q).1 := by
    change δ 0 1 e = (t.precomp ((CochainComplex.singleFunctor A 0).map S.g)).1 at ht
    rw [ht, ← hα]
    change (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp
        ((Cochain.ofHom j).comp α.1 (zero_add 1)) (zero_add 1) =
      (Cochain.ofHom q).comp α.1 (zero_add 1)
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  let R : ResolvingRow S i j :=
    { middle := twistedSum α
      inclusion := twistedInclusion α
      projection := twistedProjection α
      zero := (twistedRow α).zero
      augmentation := twistedAugmentation α e q hq
      comm_left := by
        apply HomologicalComplex.hom_ext
        intro n
        apply biprod.hom_ext
        · change (i.f n ≫ biprod.inl) ≫ biprod.fst =
            (((CochainComplex.singleFunctor A 0).map S.f).f n ≫
              biprod.lift (e.v n n (add_zero n)) (q.f n)) ≫ biprod.fst
          rw [Category.assoc, Category.assoc, biprod.inl_fst, biprod.lift_fst, Category.comp_id]
          exact (by simpa only [Cochain.zero_cochain_comp_v, Cocycle.ofHom_coe, Cochain.ofHom_v]
            using (Cochain.congr_v he n n (add_zero n)).symm)
        · change (i.f n ≫ biprod.inl) ≫ biprod.snd =
            (((CochainComplex.singleFunctor A 0).map S.f).f n ≫
              biprod.lift (e.v n n (add_zero n)) (q.f n)) ≫ biprod.snd
          rw [Category.assoc, Category.assoc, biprod.inl_snd, biprod.lift_snd, comp_zero]
          have hzero : (CochainComplex.singleFunctor A 0).map S.f ≫ q = 0 := by
            simp [q, ← Functor.map_comp_assoc, S.zero]
          exact (HomologicalComplex.congr_hom hzero n).symm
      comm_right := by
        apply HomologicalComplex.hom_ext
        intro n
        exact biprod.lift_snd _ _ }
  have hT : R.row.ShortExact :=
    shortExact_of_degreewise_shortExact _ (fun n => (twistedSplitting α n).shortExact)
  have hS' : (S.map (CochainComplex.singleFunctor A 0)).ShortExact :=
    hS.map_of_exact _
  refine ⟨R, hT, ⟨⟨min bI bJ, ?_⟩, ?_⟩, quasiIso_middle hS' hT R.map hi hj,
    fun n => ⟨twistedSplitting α n⟩⟩
  · intro n hn
    have h₁ := hbI n (lt_of_lt_of_le hn (min_le_left _ _))
    have h₂ := hbJ n (lt_of_lt_of_le hn (min_le_right _ _))
    change IsZero (I.X n ⊞ J.X n)
    rw [IsZero.iff_id_eq_zero]
    exact biprod.hom_ext _ _ (h₁.eq_of_tgt _ _) (h₂.eq_of_tgt _ _)
  · intro n
    let := hI.2 n
    let := hJ.2 n
    exact inferInstanceAs (Injective (I.X n ⊞ J.X n))


private lemma postcomp_injective {K F G : CochainComplex A ℤ} (p : F ⟶ G)
    (hp : ∀ i, Mono (p.f i)) (n : ℤ) :
    Function.Injective (fun z : Cochain K F n => z.comp (Cochain.ofHom p) (add_zero n)) := by
  intro z z' h
  ext i j hij
  have := hp j
  apply (cancel_mono (p.f j)).mp
  simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using
    Cochain.congr_v h i j hij

private lemma lift_postcomp {K : CochainComplex A ℤ} {T : ShortComplex (CochainComplex A ℤ)}
    (split : SplitsDegreewise T)
    {n : ℤ} (z : Cochain K T.X₃ n) :
    ∃ b : Cochain K T.X₂ n, b.comp (Cochain.ofHom T.g) (add_zero n) = z := by
  refine ⟨Cochain.mk (fun i j hij => z.v i j hij ≫ (split j).some.s), ?_⟩
  ext i j hij
  have hs : (split j).some.s ≫ T.g.f j = 𝟙 _ := (split j).some.s_g
  simp [Category.assoc, hs]

private lemma lift_kernel {K : CochainComplex A ℤ} {T : ShortComplex (CochainComplex A ℤ)}
    (hT : T.ShortExact) {n : ℤ} (b : Cochain K T.X₂ n)
    (hb : b.comp (Cochain.ofHom T.g) (add_zero n) = 0) :
    ∃ a : Cochain K T.X₁ n, a.comp (Cochain.ofHom T.f) (add_zero n) = b := by
  have h (i j : ℤ) (hij : i + n = j) : b.v i j hij ≫ T.g.f j = 0 := by
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.zero_v] using
      Cochain.congr_v hb i j hij
  let hs j := hT.map_of_exact (eval A (.up ℤ) j)
  let (j : ℤ) : Mono (T.map (eval A (.up ℤ) j)).f := (hs j).mono_f
  refine ⟨Cochain.mk (fun i j hij => (hs j).exact.lift (b.v i j hij) (h i j hij)), ?_⟩
  ext i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.mk_v]
  exact (hs j).exact.lift_f (b.v i j hij) (h i j hij)

private lemma inclusion_mono {T : ShortComplex (CochainComplex A ℤ)} (hT : T.ShortExact)
    (i : ℤ) : Mono (T.f.f i) := (hT.map_of_exact (eval A (.up ℤ) i)).mono_f

theorem lifts : liftsType := by
  intro A _ _ T hT split X n z
  refine ⟨lift_postcomp split z.1, ?_⟩
  intro b hb
  have hz : (δ n (n+1) b).comp (Cochain.ofHom T.g) (add_zero (n+1)) = 0 := by
    rw [← δ_comp_ofHom, show b.comp (Cochain.ofHom T.g) (add_zero n) = z.1 from hb,
      z.δ_eq_zero]
  obtain ⟨a, ha⟩ := lift_kernel hT _ hz
  have hza : δ (n+1) (n+2) a = 0 := by
    apply postcomp_injective T.f (inclusion_mono hT)
    dsimp only
    rw [← δ_comp_ofHom, ha, δ_δ, Cochain.zero_comp]
  refine ⟨Cocycle.mk a (n+2) (by omega) hza, ha.symm, ?_⟩
  intro a' ha'
  apply Cocycle.ext
  apply postcomp_injective T.f (inclusion_mono hT)
  exact ha'.symm.trans ha.symm

private lemma lift_class_eq {T : ShortComplex (CochainComplex A ℤ)} (hT : T.ShortExact)
    {X : A} {n : ℤ} {z : Cocycle (Stalk X) T.X₃ n}
    {b b' : Cochain (Stalk X) T.X₂ n} {a a' : Cocycle (Stalk X) T.X₁ (n+1)}
    (hb : Lifts z b) (hb' : Lifts z b') (ha : Descends b a) (ha' : Descends b' a') :
    CohomologyClass.mk a = CohomologyClass.mk a' := by
  unfold Lifts at hb hb'
  obtain ⟨c, hc⟩ := lift_kernel hT (b-b') (by rw [Cochain.sub_comp, hb, hb', sub_self])
  rw [CohomologyClass.mk_eq_mk_iff]
  refine ⟨n, rfl, c, ?_⟩
  apply postcomp_injective T.f (inclusion_mono hT)
  dsimp only
  unfold Descends at ha ha'
  rw [← δ_comp_ofHom, hc, δ_sub, ha, ha', Cocycle.coe_sub, Cochain.sub_comp]
  rfl

section Ordinary
variable {T : ShortComplex (CochainComplex A ℤ)} (hT : T.ShortExact)
  (split : SplitsDegreewise T) {X : A} {n : ℤ}

private noncomputable def boundaryClass (z : Cocycle (Stalk X) T.X₃ n) :
    HomClass X T.X₁ (n+1) :=
  let ex := ExtBoundarySigns.second_lifts A T hT split X n z
  CohomologyClass.mk ex.choose_spec.choose

private lemma boundaryClass_eq (z : Cocycle (Stalk X) T.X₃ n)
    (b : Cochain (Stalk X) T.X₂ n) (a : Cocycle (Stalk X) T.X₁ (n+1))
    (hb : Lifts z b) (ha : Descends b a) :
    boundaryClass hT split z = CohomologyClass.mk a := by
  let ex := ExtBoundarySigns.second_lifts A T hT split X n z
  exact lift_class_eq hT ex.choose_spec.choose_spec.1 hb ex.choose_spec.choose_spec.2 ha

private noncomputable def boundaryOnCycles :
    Cocycle (Stalk X) T.X₃ n →+ HomClass X T.X₁ (n+1) where
  toFun := boundaryClass hT split
  map_zero' := by
    rw [boundaryClass_eq hT split _ 0 0, CohomologyClass.mk_zero]
    · simp [Lifts]
    · simp [Descends]
  map_add' z z' := by
    obtain ⟨b, a, hb, ha⟩ := ExtBoundarySigns.second_lifts A T hT split X n z
    obtain ⟨b', a', hb', ha'⟩ := ExtBoundarySigns.second_lifts A T hT split X n z'
    rw [boundaryClass_eq hT split z b a hb ha, boundaryClass_eq hT split z' b' a' hb' ha',
      boundaryClass_eq hT split (z+z') (b+b') (a+a'), CohomologyClass.mk_add]
    · simp only [Lifts, Cochain.add_comp, Cocycle.coe_add, hb, hb']
    · change δ n (n+1) (b+b') =
        ((a+a').1).comp (Cochain.ofHom T.f) (add_zero (n+1))
      rw [δ_add, ha, ha', Cocycle.coe_add, Cochain.add_comp]
      rfl

private lemma boundaryOnCycles_vanishes :
    coboundaries (Stalk X) T.X₃ n ≤ (boundaryOnCycles hT split (X := X) (n := n)).ker := by
  intro z hz
  obtain ⟨m, hm, c, hc⟩ := hz
  obtain ⟨d, hd⟩ := lift_postcomp split c
  change boundaryClass hT split z = 0
  rw [boundaryClass_eq hT split z (δ m n d) 0, CohomologyClass.mk_zero]
  · unfold Lifts
    rw [← δ_comp_ofHom, hd, hc]
  · simp [Descends, δ_δ]

/-- The ordinary connecting homomorphism is induced by lifting a cocycle
to the middle Hom complex, differentiating, and descending to the kernel. -/
private noncomputable def ordinaryConnectingMap : HomClass X T.X₃ n →+ HomClass X T.X₁ (n+1) :=
  CohomologyClass.descAddMonoidHom (boundaryOnCycles hT split) (boundaryOnCycles_vanishes hT split)

end Ordinary

theorem ordinary_connector : ordinaryConnectorType := by
  intro A _ _ T hT split X n
  have h : IsOrdinaryConnector T X n (ordinaryConnectingMap hT split) :=
    boundaryClass_eq hT split
  refine ⟨ordinaryConnectingMap hT split, h, ?_⟩
  intro f hf
  ext x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, a, hb, ha⟩ := ExtBoundarySigns.second_lifts A T hT split X n z
  rw [hf z b a hb ha, h z b a hb ha]

theorem connector_comparison : connectorComparisonType.{w, v, u} := by
  intro A _ _ _ S hS I J i j hi hj R hT split X n d hd x
  have hS' : (S.map (CochainComplex.singleFunctor A 0)).ShortExact := hS.map_of_exact _
  have hmid := quasiIso_middle hS' hT R.map hi hj
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨b, a, hb, ha⟩ := ExtBoundarySigns.second_lifts A R.row hT split X n z
  rw [hd z b a hb ha]
  exact ExtBoundarySigns.ordinary_second A S hS R.row hT R.map hi hmid hj X n z a b hb ha

theorem connector_independence : connectorIndependenceType.{w, v, u} := by
  intro A _ _ _ S hS I J i j hi hj hI _ R R' hR split hR' split' X n d d' hd hd'
  obtain ⟨e, he⟩ := ExtShiftedHom.injective_comparison A X S.X₁ I i hi hI.1 hI.2 (n+1)
  ext x
  apply (e.injective.comp (HomComplex.homologyAddEquiv _ _ _).symm.injective)
  change e ((HomComplex.homologyAddEquiv _ _ _).symm (d x)) =
    e ((HomComplex.homologyAddEquiv _ _ _).symm (d' x))
  rw [he, he, connector_comparison A S hS I J i j hi hj R hR split X n d hd,
    connector_comparison A S hS I J i j hi hj R' hR' split' X n d' hd']

end AdvancedHomologicalAlgebra.ExtInjectiveHorseshoe
