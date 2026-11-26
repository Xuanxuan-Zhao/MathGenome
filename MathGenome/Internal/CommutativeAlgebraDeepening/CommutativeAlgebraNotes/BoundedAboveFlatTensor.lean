import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.BoundedAboveFlatTensor
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

open CategoryTheory Category Limits HomologicalComplex MonoidalCategory
open scoped DirectSum

universe u

namespace CommutativeAlgebraNotes

noncomputable section

variable {R : Type u} [CommRing R]

private abbrev Complex (R : Type u) [CommRing R] :=
  CochainComplex (ModuleCat.{u} R) ℤ

local notation "upZ" => ComplexShape.up ℤ

private theorem add_apply {M N : ModuleCat.{u} R} (f g : M ⟶ N) (x : M) :
    (f + g) x = f x + g x := rfl

private theorem neg_apply {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) :
    (-f) x = -(f x) := rfl

private theorem exactAt_iff_cycles (K : Complex R) (n : ℤ) :
    K.ExactAt n ↔ ∀ x : K.X n, K.d n (n + 1) x = 0 →
      ∃ y : K.X (n - 1), K.d (n - 1) n y = x := by
  rw [K.exactAt_iff' (i := n - 1) (j := n) (k := n + 1)
      ((upZ).prev_eq' (show (upZ).Rel (n - 1) n by change n - 1 + 1 = n; omega))
      ((upZ).next_eq' (show (upZ).Rel n (n + 1) from rfl)),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change (∀ x : K.X n, K.d n (n + 1) x = 0 ↔
    x ∈ Set.range (K.d (n - 1) n)) ↔ _
  refine ⟨fun h x hx => (h x).mp hx, fun h x => ⟨h x, ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact ConcreteCategory.congr_hom (K.d_comp_d (n - 1) n (n + 1)) y

/-- The degreewise column coordinates of a total complex. Its differential
preserves degree tails and induces the column differential on each quotient. -/
private structure ColumnDecomposition (K : Complex R) (C : ℤ → Complex R) where
  incl (n p : ℤ) : (C p).X n ⟶ K.X n
  proj (n p : ℤ) : K.X n ⟶ (C p).X n
  incl_proj (n p : ℤ) : incl n p ≫ proj n p = 𝟙 _
  incl_proj_ne (n p q : ℤ) : p ≠ q → incl n p ≫ proj n q = 0
  ext (n : ℤ) (x y : K.X n) : (∀ p, proj n p x = proj n p y) → x = y
  lower (n : ℤ) (x : K.X n) : ∃ a : ℤ, ∀ p < a, proj n p x = 0
  differential (n n' p : ℤ) (h : n + 1 = n') (x : K.X n) :
    (∀ q < p, proj n q x = 0) →
      proj n' p (K.d n n' x) = (C p).d n n' (proj n p x)

private theorem ColumnDecomposition.acyclic {K : Complex R} {C : ℤ → Complex R}
    (D : ColumnDecomposition K C) (N : ℤ)
    (upper : ∀ p > N, ∀ n, IsZero ((C p).X n)) (hC : ∀ p, (C p).Acyclic) :
    K.Acyclic := by
  intro n
  rw [exactAt_iff_cycles]
  -- A cycle in the tail starting at N + 1 - m is killed by successively
  -- lifting its lowest component through that column's differential.
  have step (m : ℕ) (x : K.X n) (hx : K.d n (n + 1) x = 0)
      (hlo : ∀ p < N + 1 - (m : ℤ), D.proj n p x = 0) :
      ∃ y : K.X (n - 1), K.d (n - 1) n y = x := by
    induction m generalizing x with
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero]
      apply D.ext
      intro p
      rw [map_zero]
      by_cases hp : p ≤ N
      · exact (hlo p (by omega)).symm
      · exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero (upper p (by omega) n)) _ _
    | succ m ih =>
      let a : ℤ := N + 1 - ((m + 1 : ℕ) : ℤ)
      have ha : ∀ p < a, D.proj n p x = 0 := hlo
      have hd : (C a).d n (n + 1) (D.proj n a x) = 0 := by
        rw [← D.differential n (n + 1) a rfl x ha, hx, map_zero]
      obtain ⟨b, hb⟩ := (exactAt_iff_cycles (C a) n).mp (hC a n) _ hd
      let w := D.incl (n - 1) a b
      have hw (p : ℤ) (hp : p < a) : D.proj (n - 1) p w = 0 :=
        ConcreteCategory.congr_hom (D.incl_proj_ne _ _ _ (by omega)) b
      have hwa : D.proj (n - 1) a w = b := ConcreteCategory.congr_hom (D.incl_proj _ _) b
      have hdiff (p : ℤ) (hp : p ≤ a) :
          D.proj n p (K.d (n - 1) n w) = (C p).d (n - 1) n (D.proj (n - 1) p w) := by
        exact D.differential (n - 1) n p (by omega) w (fun q hq => hw q (by omega))
      have hz : K.d n (n + 1) (x - K.d (n - 1) n w) = 0 := by
        have h := ConcreteCategory.congr_hom (K.d_comp_d (n - 1) n (n + 1)) w
        rw [map_sub, hx]
        simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
          zero_sub, neg_eq_zero] using h
      obtain ⟨y, hy⟩ := ih _ hz (by
        intro p hp
        have hpa : p ≤ a := by dsimp [a] at *; omega
        rw [map_sub, hdiff p hpa]
        rcases lt_or_eq_of_le hpa with h | rfl
        · rw [ha p h, hw p h, map_zero, sub_zero]
        · rw [hwa, hb, sub_self])
      refine ⟨y + w, ?_⟩
      rw [map_add, hy, sub_add_cancel]
  intro x hx
  -- Direct-sum totalization puts each cycle in one of these finite tails.
  obtain ⟨a, ha⟩ := D.lower n x
  obtain ⟨m, hm⟩ : ∃ m : ℕ, N + 1 - (m : ℤ) ≤ a :=
    ⟨(N + 1 - a).toNat, by omega⟩
  exact step m x hx (fun p hp => ha p (lt_of_lt_of_le hp hm))

private abbrev column (F A : Complex R) (p : ℤ) : Complex R :=
  ((tensorLeft (F.X p)).mapHomologicalComplex upZ).obj A⟦(-p : ℤ)⟧

private abbrev columnMap (F : Complex R) {A B : Complex R} (f : A ⟶ B) (p : ℤ) :
    column F A p ⟶ column F B p :=
  ((tensorLeft (F.X p)).mapHomologicalComplex upZ).map f⟦(-p : ℤ)⟧'

private abbrev totalIn (F A : Complex R) (n p : ℤ) :
    (column F A p).X n ⟶ (tensorObj F A).X n :=
  ιTensorObj F A p (n + -p) n (by omega)

private abbrev sumModule (C : ℤ → Complex R) (n : ℤ) : ModuleCat R :=
  ModuleCat.of R (⨁ p : ℤ, (C p).X n)

private theorem total_hom_ext {F A : Complex R} {n : ℤ} {Y : ModuleCat R}
    {f g : (tensorObj F A).X n ⟶ Y}
    (h : ∀ p, totalIn F A n p ≫ f = totalIn F A n p ≫ g) : f = g := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  have hq : q = n + -p := by change p + q = n at hpq; omega
  subst q
  exact h p

private def totalToSum (F A : Complex R) (n : ℤ) :
    (tensorObj F A).X n ⟶ sumModule (column F A) n :=
  mapBifunctorDesc (F := curriedTensor (ModuleCat R)) (c := upZ) (fun p q h => by
    have hq : q = n + -p := by change p + q = n at h; omega
    subst q
    exact ModuleCat.ofHom (DirectSum.lof R ℤ (fun p => (column F A p).X n) p))

@[reassoc]
private theorem totalIn_totalToSum (F A : Complex R) (n p : ℤ) :
    totalIn F A n p ≫ totalToSum F A n =
      ModuleCat.ofHom (DirectSum.lof R ℤ (fun p => (column F A p).X n) p) := by
  rw [totalIn, totalToSum, ι_mapBifunctorDesc]

private def sumToTotal (F A : Complex R) (n : ℤ) :
    sumModule (column F A) n ⟶ (tensorObj F A).X n :=
  ModuleCat.ofHom (DirectSum.toModule R ℤ _ (fun p => (totalIn F A n p).hom))

private theorem totalToSum_sumToTotal (F A : Complex R) (n : ℤ) :
    totalToSum F A n ≫ sumToTotal F A n = 𝟙 _ := by
  apply total_hom_ext
  intro p
  rw [totalIn_totalToSum_assoc, comp_id]
  apply ModuleCat.hom_ext
  exact LinearMap.ext (DirectSum.toModule_lof R (φ := fun p => (totalIn F A n p).hom) p)

private def totalProj (F A : Complex R) (n p : ℤ) :
    (tensorObj F A).X n ⟶ (column F A p).X n :=
  totalToSum F A n ≫ ModuleCat.ofHom (DirectSum.component R ℤ (fun p => (column F A p).X n) p)

@[reassoc (attr := simp)]
private theorem totalIn_totalProj (F A : Complex R) (n p : ℤ) :
    totalIn F A n p ≫ totalProj F A n p = 𝟙 _ := by
  rw [totalProj, totalIn_totalToSum_assoc]
  apply ModuleCat.hom_ext
  exact DirectSum.component_comp_lof_same R (M := fun p => (column F A p).X n) p

@[reassoc]
private theorem totalIn_totalProj_ne (F A : Complex R) (n p q : ℤ) (h : p ≠ q) :
    totalIn F A n p ≫ totalProj F A n q = 0 := by
  rw [totalProj, totalIn_totalToSum_assoc]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
    DirectSum.component_comp_lof, dite_eq_right h]

private theorem totalProj_eq (F A : Complex R) (n p : ℤ) (x : (tensorObj F A).X n) :
    totalProj F A n p x = (totalToSum F A n x : DirectSum ℤ (fun p => (column F A p).X n)) p :=
  rfl

private theorem totalProj_ext (F A : Complex R) (n : ℤ) (x y : (tensorObj F A).X n)
    (h : ∀ p, totalProj F A n p x = totalProj F A n p y) : x = y := by
  have hh : totalToSum F A n x = totalToSum F A n y :=
    DFinsupp.ext (fun p => h p)
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
    (ConcreteCategory.congr_hom (totalToSum_sumToTotal F A n) x).symm.trans
      ((congrArg (sumToTotal F A n) hh).trans
        (ConcreteCategory.congr_hom (totalToSum_sumToTotal F A n) y))

private theorem totalProj_lower (F A : Complex R) (n : ℤ) (x : (tensorObj F A).X n) :
    ∃ a : ℤ, ∀ p < a, totalProj F A n p x = 0 := by
  classical
  let s := (totalToSum F A n x : DirectSum ℤ (fun p => (column F A p).X n)).support
  let a := (insert 0 s).min' (Finset.insert_nonempty _ _)
  refine ⟨a, fun p hp => ?_⟩
  rw [totalProj_eq, ← DFinsupp.notMem_support_iff]
  intro hm
  exact (not_le_of_gt hp) (Finset.min'_le _ _ (Finset.mem_insert_of_mem hm))


private theorem ιTensorObj_totalProj_ne (F A : Complex R) (n p q j : ℤ)
    (h : p + q = n) (hp : p ≠ j) :
    ιTensorObj F A p q n h ≫ totalProj F A n j = 0 := by
  have hq : q = n + -p := by omega
  subst q
  exact totalIn_totalProj_ne F A n p j hp

private theorem totalIn_d (F A : Complex R) (n n' q : ℤ) (hn : n + 1 = n') :
    totalIn F A n q ≫ (tensorObj F A).d n n' =
      (show (column F A q).X n ⟶ (tensorObj F A).X n' from
        (F.d q (q + 1) ▷ A.X (n + -q)) ≫
          ιTensorObj F A (q + 1) (n + -q) n' (by omega)) +
      (column F A q).d n n' ≫ totalIn F A n' q := by
  let T := curriedTensor (ModuleCat R)
  have hh : (upZ).Rel q (q + 1) := rfl
  have hv : (upZ).Rel (n + -q) (n' + -q) := by change n + -q + 1 = n' + -q; omega
  rw [mapBifunctor.d_eq F A T upZ, Preadditive.comp_add]
  unfold totalIn
  rw [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq F A T upZ hh (n + -q) n' (by change q + 1 + (n + -q) = n'; omega),
    mapBifunctor.d₂_eq F A T upZ q hv n' (by change q + (n' + -q) = n'; omega)]
  change 1 • (_ : _ ⟶ _) + q.negOnePow • (_ : _ ⟶ _) =
    _ + ((-q).negOnePow • (_ : _ ⟶ _)) ≫ _
  rw [one_smul, Int.negOnePow_neg, Linear.units_smul_comp]
  rfl

-- Only the current column and the preceding column can contribute.
private theorem total_d_proj (F A : Complex R) (n n' p : ℤ) (hn : n + 1 = n') :
    (tensorObj F A).d n n' ≫ totalProj F A n' p =
      totalProj F A n p ≫ (column F A p).d n n' +
      totalProj F A n (p - 1) ≫
        (totalIn F A n (p - 1) ≫ (tensorObj F A).d n n' ≫ totalProj F A n' p) := by
  apply total_hom_ext
  intro q
  rw [Preadditive.comp_add, ← Category.assoc]
  by_cases hqp : q = p
  · subst q
    rw [totalIn_totalProj_assoc, totalIn_totalProj_ne_assoc _ _ _ _ _ (by omega),
      zero_comp, add_zero, totalIn_d F A n n' p hn, Preadditive.add_comp,
      Category.assoc, ιTensorObj_totalProj_ne F A n' _ _ p _ (by omega), comp_zero,
      zero_add, Category.assoc, totalIn_totalProj, comp_id]
  · rw [totalIn_totalProj_ne_assoc _ _ _ _ _ hqp, zero_comp, zero_add]
    by_cases hh : q = p - 1
    · subst q
      rw [totalIn_totalProj_assoc, Category.assoc]
    · rw [totalIn_totalProj_ne_assoc _ _ _ _ _ hh, zero_comp,
        totalIn_d F A n n' q hn, Preadditive.add_comp, Category.assoc,
        ιTensorObj_totalProj_ne F A n' _ _ p _ (by omega), comp_zero,
        Category.assoc, totalIn_totalProj_ne _ _ _ _ _ hqp, comp_zero, add_zero]

private def tensorColumns (F A : Complex R) :
    ColumnDecomposition (tensorObj F A) (column F A) where
  incl := totalIn F A
  proj := totalProj F A
  incl_proj := totalIn_totalProj F A
  incl_proj_ne := totalIn_totalProj_ne F A
  ext := totalProj_ext F A
  lower := totalProj_lower F A
  differential n n' p hn x h := by
    have eq := ConcreteCategory.congr_hom (total_d_proj F A n n' p hn) x
    simpa only [add_apply, ModuleCat.comp_apply, h (p - 1) (by omega),
      map_zero, add_zero] using eq

private theorem total_map_proj (F : Complex R) {A B : Complex R} (f : A ⟶ B)
    (n p : ℤ) :
    (tensorHom (𝟙 F) f).f n ≫ totalProj F B n p =
      totalProj F A n p ≫ (columnMap F f p).f n := by
  apply total_hom_ext
  intro q
  have hmap : totalIn F A n q ≫ (tensorHom (𝟙 F) f).f n =
      (columnMap F f q).f n ≫ totalIn F B n q := by
    unfold totalIn HomologicalComplex.tensorHom
    rw [ι_mapBifunctorMap]
    rw [id_f, (curriedTensor (ModuleCat R)).map_id, NatTrans.id_app, id_comp]
    rfl
  rw [← Category.assoc, hmap]
  by_cases h : q = p
  · subst q
    rw [totalIn_totalProj_assoc, Category.assoc, totalIn_totalProj, comp_id]
  · rw [totalIn_totalProj_ne_assoc _ _ _ _ _ h, zero_comp, Category.assoc,
      totalIn_totalProj_ne _ _ _ _ _ h, comp_zero]

private theorem column_acyclic (F A : Complex R) (p : ℤ)
    (flat : Module.Flat R (F.X p)) (hA : A.Acyclic) : (column F A p).Acyclic := by
  intro n
  let T := tensorLeft (F.X p)
  have : T.PreservesHomology := inferInstanceAs ((tensorLeft (F.X p)).PreservesHomology)
  rw [exactAt_iff_cycles]
  intro x hx
  change (-p).negOnePow • T.map (A.d (n + -p) (n + 1 + -p)) x = 0 at hx
  have he := (A.exactAt_iff' (i := n - 1 + -p) (j := n + -p) (k := n + 1 + -p)
    ((upZ).prev_eq' (show (upZ).Rel (n - 1 + -p) (n + -p) by
      change n - 1 + -p + 1 = n + -p; omega))
    ((upZ).next_eq' (show (upZ).Rel (n + -p) (n + 1 + -p) by
      change n + -p + 1 = n + 1 + -p; omega))).mp (hA (n + -p))
  have he' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (he.map T)
  have hd : T.map (A.d (n + -p) (n + 1 + -p)) x = 0 := by
    exact (smul_eq_zero_iff_eq (a := (-p).negOnePow)).mp hx
  obtain ⟨b, hb⟩ := (he' x).mp hd
  refine ⟨(-p).negOnePow • b, ?_⟩
  change (-p).negOnePow • T.map (A.d (n - 1 + -p) (n + -p)) ((-p).negOnePow • b) = x
  change T.map (A.d (n - 1 + -p) (n + -p)) b = x at hb
  have h := map_zsmul (T.map (A.d (n - 1 + -p) (n + -p))).hom
    ((-p).negOnePow : ℤ) b
  rw [show T.map (A.d (n - 1 + -p) (n + -p)) ((-p).negOnePow • b) =
    (-p).negOnePow • T.map (A.d (n - 1 + -p) (n + -p)) b from h,
    hb, smul_smul, Int.units_mul_self, one_smul]

private theorem column_isZero (F A : Complex R) (p n : ℤ) (h : IsZero (F.X p)) :
    IsZero ((column F A p).X n) :=
  (tensorRight (A.X (n + -p))).map_isZero h

/-- A bounded-above complex of flat modules preserves acyclicity under the signed
direct-sum tensor product. -/
theorem boundedAboveFlatTensorAcyclic : Specs.boundedAboveFlatTensorAcyclicType := by
  intro R _ F flat ⟨N, hN⟩ A hA
  exact (tensorColumns F A).acyclic N
    (fun p hp n => column_isZero F A p n (CochainComplex.isZero_of_isStrictlyLE (K := F) N p hp))
    (fun p => column_acyclic F A p (flat p) hA)


open CochainComplex in
private theorem quasiIso_iff_cone_acyclic {A B : Complex R} (f : A ⟶ B) :
    QuasiIso f ↔ (mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    ← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic (ModuleCat R)).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)

section Cone

open CochainComplex

variable {A B A' B' : Complex R} (f : A ⟶ B) (g : A' ⟶ B')

private abbrev coneFst (n : ℤ) : (mappingCone f).X n ⟶ A.X (n + 1) :=
  (mappingCone.fst f).1.v n (n + 1) rfl

private abbrev coneSnd (n : ℤ) : (mappingCone f).X n ⟶ B.X n :=
  (mappingCone.snd f).v n n (add_zero n)

private abbrev coneInl (n : ℤ) : A.X (n + 1) ⟶ (mappingCone f).X n :=
  (mappingCone.inl f).v (n + 1) n (by omega)

private abbrev coneInr (n : ℤ) : B.X n ⟶ (mappingCone f).X n :=
  (mappingCone.inr f).f n

/-- The component map of graded mapping cones induced by two component maps. -/
private def coneMapAt (n : ℤ) (a : A.X (n + 1) ⟶ A'.X (n + 1))
    (b : B.X n ⟶ B'.X n) : (mappingCone f).X n ⟶ (mappingCone g).X n :=
  coneFst f n ≫ a ≫ coneInl g n + coneSnd f n ≫ b ≫ coneInr g n

@[reassoc (attr := simp)]
private theorem coneMapAt_fst (n : ℤ) (a : A.X (n + 1) ⟶ A'.X (n + 1))
    (b : B.X n ⟶ B'.X n) :
    coneMapAt f g n a b ≫ coneFst g n = coneFst f n ≫ a := by
  simp [coneMapAt, coneFst, coneInl, coneInr, Preadditive.add_comp]

@[reassoc (attr := simp)]
private theorem coneMapAt_snd (n : ℤ) (a : A.X (n + 1) ⟶ A'.X (n + 1))
    (b : B.X n ⟶ B'.X n) :
    coneMapAt f g n a b ≫ coneSnd g n = coneSnd f n ≫ b := by
  simp [coneMapAt, coneSnd, coneInl, coneInr, Preadditive.add_comp]

private theorem cone_ext_elements (n : ℤ) {x y : (mappingCone f).X n}
    (h₁ : coneFst f n x = coneFst f n y) (h₂ : coneSnd f n x = coneSnd f n y) : x = y := by
  have decompose (z : (mappingCone f).X n) :
      coneInl f n (coneFst f n z) + coneInr f n (coneSnd f n z) = z := by
    simpa only [add_apply, ModuleCat.comp_apply, ModuleCat.id_apply] using
      ConcreteCategory.congr_hom (mappingCone.id_X f n (n + 1) rfl) z
  rw [← decompose x, ← decompose y, h₁, h₂]

private theorem coneMapAt_fst_apply (n : ℤ) (a : A.X (n + 1) ⟶ A'.X (n + 1))
    (b : B.X n ⟶ B'.X n) (x : (mappingCone f).X n) :
    coneFst g n (coneMapAt f g n a b x) = a (coneFst f n x) :=
  ConcreteCategory.congr_hom (coneMapAt_fst f g n a b) x

private theorem coneMapAt_snd_apply (n : ℤ) (a : A.X (n + 1) ⟶ A'.X (n + 1))
    (b : B.X n ⟶ B'.X n) (x : (mappingCone f).X n) :
    coneSnd g n (coneMapAt f g n a b x) = b (coneSnd f n x) :=
  ConcreteCategory.congr_hom (coneMapAt_snd f g n a b) x

private theorem cone_d_fst (n : ℤ) (x : (mappingCone f).X n) :
    coneFst f (n + 1) ((mappingCone f).d n (n + 1) x) =
      -(A.d (n + 1) (n + 1 + 1) (coneFst f n x)) := by
  simpa only [ModuleCat.comp_apply, neg_apply, map_neg] using
    ConcreteCategory.congr_hom (mappingCone.d_fst_v f n (n + 1) (n + 1 + 1) rfl rfl) x

private theorem cone_d_snd (n : ℤ) (x : (mappingCone f).X n) :
    coneSnd f (n + 1) ((mappingCone f).d n (n + 1) x) =
      f.f (n + 1) (coneFst f n x) + B.d n (n + 1) (coneSnd f n x) := by
  simpa only [ModuleCat.comp_apply, add_apply] using
    ConcreteCategory.congr_hom (mappingCone.d_snd_v f n (n + 1) rfl) x

/-- A comparison which is diagonal in the column coordinates induces a tail
filtration on its cone, with the columnwise cones as successive quotients. -/
private def ColumnDecomposition.cone {CA CB : ℤ → Complex R}
    (DA : ColumnDecomposition A CA) (DB : ColumnDecomposition B CB)
    (fc : ∀ p, CA p ⟶ CB p)
    (naturality : ∀ n p, f.f n ≫ DB.proj n p = DA.proj n p ≫ (fc p).f n) :
    ColumnDecomposition (mappingCone f) (fun p => mappingCone (fc p)) where
  incl n p := coneMapAt (fc p) f n (DA.incl (n + 1) p) (DB.incl n p)
  proj n p := coneMapAt f (fc p) n (DA.proj (n + 1) p) (DB.proj n p)
  incl_proj n p := by
    apply mappingCone.ext_to (fc p) n (n + 1) rfl
    · change _ ≫ coneFst (fc p) n = _ ≫ coneFst (fc p) n
      rw [Category.assoc, coneMapAt_fst, coneMapAt_fst_assoc,
        DA.incl_proj, comp_id, id_comp]
    · change _ ≫ coneSnd (fc p) n = _ ≫ coneSnd (fc p) n
      rw [Category.assoc, coneMapAt_snd, coneMapAt_snd_assoc,
        DB.incl_proj, comp_id, id_comp]
  incl_proj_ne n p q h := by
    apply mappingCone.ext_to (fc q) n (n + 1) rfl
    · change _ ≫ coneFst (fc q) n = _ ≫ coneFst (fc q) n
      rw [Category.assoc, coneMapAt_fst, coneMapAt_fst_assoc,
        DA.incl_proj_ne _ _ _ h, comp_zero, zero_comp]
    · change _ ≫ coneSnd (fc q) n = _ ≫ coneSnd (fc q) n
      rw [Category.assoc, coneMapAt_snd, coneMapAt_snd_assoc,
        DB.incl_proj_ne _ _ _ h, comp_zero, zero_comp]
  ext n x y h := by
    apply cone_ext_elements f n
    · apply DA.ext
      intro p
      simpa only [coneMapAt_fst_apply] using
        congrArg (coneFst (fc p) n) (h p)
    · apply DB.ext
      intro p
      simpa only [coneMapAt_snd_apply] using
        congrArg (coneSnd (fc p) n) (h p)
  lower n x := by
    obtain ⟨a, ha⟩ := DA.lower (n + 1) (coneFst f n x)
    obtain ⟨b, hb⟩ := DB.lower n (coneSnd f n x)
    refine ⟨min a b, fun p hp => ?_⟩
    apply cone_ext_elements (fc p) n
    · simp only [coneMapAt_fst_apply, map_zero]
      exact ha p (lt_of_lt_of_le hp (min_le_left _ _))
    · simp only [coneMapAt_snd_apply, map_zero]
      exact hb p (lt_of_lt_of_le hp (min_le_right _ _))
  differential n n' p hn x h := by
    subst n'
    have ha (q : ℤ) (hq : q < p) : DA.proj (n + 1) q (coneFst f n x) = 0 := by
      simpa only [coneMapAt_fst_apply, map_zero] using
        congrArg (coneFst (fc q) n) (h q hq)
    have hb (q : ℤ) (hq : q < p) : DB.proj n q (coneSnd f n x) = 0 := by
      simpa only [coneMapAt_snd_apply, map_zero] using
        congrArg (coneSnd (fc q) n) (h q hq)
    apply cone_ext_elements (fc p) (n + 1)
    · rw [coneMapAt_fst_apply, cone_d_fst, cone_d_fst, coneMapAt_fst_apply, map_neg,
        DA.differential (n + 1) (n + 1 + 1) p rfl _ ha]
    · rw [coneMapAt_snd_apply, cone_d_snd, cone_d_snd, coneMapAt_fst_apply,
        coneMapAt_snd_apply, map_add, DB.differential n (n + 1) p rfl _ hb]
      rw [show DB.proj (n + 1) p (f.f (n + 1) (coneFst f n x)) =
        (fc p).f (n + 1) (DA.proj (n + 1) p (coneFst f n x)) from
        ConcreteCategory.congr_hom (naturality (n + 1) p) (coneFst f n x)]

end Cone

/-- Tensoring on the left by a bounded-above complex of flat modules preserves
quasi-isomorphisms between arbitrary cochain complexes. -/
theorem boundedAboveFlatTensorQuasiIso : Specs.boundedAboveFlatTensorQuasiIsoType := by
  intro R _ F flat ⟨N, hN⟩ A B f hf
  apply (quasiIso_iff_cone_acyclic _).mpr
  let D := (tensorColumns F A).cone (HomologicalComplex.tensorHom (𝟙 F) f)
    (tensorColumns F B) (columnMap F f) (total_map_proj F f)
  apply D.acyclic N
  · intro p hp n
    have hz := CochainComplex.isZero_of_isStrictlyLE (K := F) N p hp
    exact (CochainComplex.mappingCone.isZero_X_iff (columnMap F f p) n).mpr
      ⟨column_isZero F A p (n + 1) hz, column_isZero F B p n hz⟩
  · intro p
    apply (quasiIso_iff_cone_acyclic _).mp
    have := flat p
    exact (CochainComplex.quasiIso_shift_iff _ (-p)).mpr
      (HomologicalComplex.quasiIso_map_of_preservesHomology f (tensorLeft (F.X p)))

end

end CommutativeAlgebraNotes
