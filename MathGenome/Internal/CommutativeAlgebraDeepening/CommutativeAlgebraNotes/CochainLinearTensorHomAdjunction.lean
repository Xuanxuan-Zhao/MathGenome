import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CochainLinearTensorHomAdjunction

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace CommutativeAlgebraNotes.CochainTensorHom

open CochainComplex (linearHomComplex)
open CochainComplex.HomComplex
open HomologicalComplex (ιTensorObj mapBifunctorDesc ι_mapBifunctorDesc)

universe u
variable {R : Type u} [CommRing R]

variable {P Q J : Complex R}

private noncomputable def curryComponent {n i u' : ℤ} (hi : i + n = u')
    (f : Cochain (HomologicalComplex.tensorObj P Q) J n) :
    P.X i ⟶ (linearHomComplex R Q J).X u' :=
  ModuleCat.ofHom
    { toFun := fun x => Cochain.mk fun j v hj => ModuleCat.ofHom
        ((f.v (i + j) v (by omega)).hom.comp
          ((ιTensorObj P Q i j (i + j) rfl).hom.comp
            (TensorProduct.mk R (P.X i) (Q.X j) x)))
      map_add' := by
        intro x y
        apply Cochain.ext
        intro j v hj
        apply ModuleCat.hom_ext
        ext z
        simp
      map_smul' := by
        intro r x
        apply Cochain.ext
        intro j v hj
        apply ModuleCat.hom_ext
        ext z
        simp only [Cochain.mk_v, Cochain.smul_v, ModuleCat.hom_smul, ModuleCat.hom_ofHom,
          LinearMap.smul_apply, LinearMap.comp_apply, map_smul, RingHom.id_apply] }

private noncomputable def curryDegree (n : ℤ) :
    Cochain (HomologicalComplex.tensorObj P Q) J n →ₗ[R] Cochain P (linearHomComplex R Q J) n where
  toFun f := Cochain.mk fun _ _ hi => curryComponent hi f
  map_add' f g := by
    apply Cochain.ext
    intro i u' hi
    apply ModuleCat.hom_ext
    ext x : 1
    apply Cochain.ext
    intro j v hj
    apply ModuleCat.hom_ext
    ext y
    rfl
  map_smul' r f := by
    apply Cochain.ext
    intro i u' hi
    apply ModuleCat.hom_ext
    ext x : 1
    apply Cochain.ext
    intro j v hj
    apply ModuleCat.hom_ext
    ext y
    rfl

private lemma curryDegree_apply {n i j u' v : ℤ} (hi : i + n = u') (hj : j + u' = v)
    (f : Cochain (HomologicalComplex.tensorObj P Q) J n) (x : P.X i) (y : Q.X j) :
    (((curryDegree n f).v i u' hi x).v j v hj) y =
      f.v (i + j) v (by omega) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y)) := rfl

private lemma curryDegree_apply_at {n i j t u' v : ℤ} (hi : i + n = u') (hj : j + u' = v)
    (ht : i + j = t) (f : Cochain (HomologicalComplex.tensorObj P Q) J n)
    (x : P.X i) (y : Q.X j) :
    (((curryDegree n f).v i u' hi x).v j v hj) y =
      f.v t v (by omega) (ιTensorObj P Q i j t ht (x ⊗ₜ[R] y)) := by
  subst t
  rfl

private def uncurryComponent {n i j v : ℤ} (h : i + j + n = v)
    (g : Cochain P (linearHomComplex R Q J) n) :
    P.X i ⊗ Q.X j ⟶ J.X v :=
  ModuleCat.ofHom <| TensorProduct.lift
    { toFun x := ((g.v i (i + n) rfl x).v j v (by omega)).hom
      map_add' x y := by
        rw [map_add]
        rfl
      map_smul' r x := by
        rw [map_smul]
        rfl }

private lemma uncurryComponent_apply {n i j u' v : ℤ} (h : i + j + n = v)
    (hi : i + n = u') (hj : j + u' = v)
    (g : Cochain P (linearHomComplex R Q J) n) (x : P.X i) (y : Q.X j) :
    uncurryComponent h g (x ⊗ₜ[R] y) = (g.v i u' hi x).v j v hj y := by
  subst u'
  rfl

private noncomputable def uncurryDegree {n : ℤ} (g : Cochain P (linearHomComplex R Q J) n) :
    Cochain (HomologicalComplex.tensorObj P Q) J n :=
  Cochain.mk fun t v htv =>
    mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) (j := t) fun i j (hij : i + j = t) =>
        uncurryComponent (by omega) g

private lemma uncurryDegree_ι {n t i j v : ℤ} (htv : t + n = v)
    (hij : i + j = t) (g : Cochain P (linearHomComplex R Q J) n) :
    ιTensorObj P Q i j t hij ≫ (uncurryDegree g).v t v htv =
      uncurryComponent (by omega) g :=
  ι_mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ) (j := t) (fun a b (hab : a + b = t) =>
      uncurryComponent (n := n) (v := v) (by omega) g) i j hij

private lemma uncurryDegree_apply {n t i j u' v : ℤ} (hij : i + j = t)
    (hi : i + n = u') (hj : j + u' = v)
    (g : Cochain P (linearHomComplex R Q J) n) (x : P.X i) (y : Q.X j) :
    (uncurryDegree g).v t v (by omega) (ιTensorObj P Q i j t hij (x ⊗ₜ[R] y)) =
      (g.v i u' hi x).v j v hj y := by
  have htv : t + n = v := by omega
  have h := ConcreteCategory.congr_hom (uncurryDegree_ι htv hij g) (x ⊗ₜ[R] y)
  exact h.trans (uncurryComponent_apply (by omega) hi hj g x y)

private noncomputable def curryEquiv (n : ℤ) :
    Cochain (HomologicalComplex.tensorObj P Q) J n ≃ₗ[R] Cochain P (linearHomComplex R Q J) n :=
  { curryDegree n with
    invFun := uncurryDegree
    left_inv := by
      intro f
      apply Cochain.ext
      intro t v htv
      apply HomologicalComplex.mapBifunctor.hom_ext
        (K₁ := P) (K₂ := Q) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ)
      intro i j hij
      change i + j = t at hij
      subst t
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      change (uncurryDegree (curryDegree n f)).v (i + j) v htv
          (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y)) =
        f.v (i + j) v htv (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y))
      rw [uncurryDegree_apply rfl rfl (show j + (i + n) = v by omega), curryDegree_apply]
    right_inv := by
      intro g
      apply Cochain.ext
      intro i u' hi
      apply ModuleCat.hom_ext
      ext x : 1
      apply Cochain.ext
      intro j v hj
      apply ModuleCat.hom_ext
      ext y
      exact (curryDegree_apply hi hj (uncurryDegree g) x y).trans
        (uncurryDegree_apply rfl hi hj g x y) }

private lemma add_apply {M N : ModuleCat.{u} R} (f g : M ⟶ N) (x : M) :
    (f + g) x = f x + g x := rfl

private lemma sign_apply {M N : ModuleCat.{u} R} (s : ℤˣ) (f : M ⟶ N) (x : M) :
    (s • f) x = s • f x := rfl

private lemma map_sign {M N : ModuleCat.{u} R} (s : ℤˣ) (f : M ⟶ N) (x : M) :
    f (s • x) = s • f x := by
  change f.hom (s • x) = s • f.hom x
  simp only [Units.smul_def, map_zsmul]

open HomologicalComplex.mapBifunctor in
private lemma tensor_d_apply (i j t t' : ℤ) (ht : i + j = t) (ht' : t + 1 = t')
    (x : P.X i) (y : Q.X j) :
    (HomologicalComplex.tensorObj P Q).d t t' (ιTensorObj P Q i j t ht (x ⊗ₜ[R] y)) =
      ιTensorObj P Q (i + 1) j t' (by omega) (P.d i (i + 1) x ⊗ₜ[R] y) +
      i.negOnePow • ιTensorObj P Q i (j + 1) t' (by omega) (x ⊗ₜ[R] Q.d j (j + 1) y) := by
  let c := ComplexShape.up ℤ
  let F := curriedTensor (ModuleCat R)
  have h₁ : i + 1 + j = t' := by omega
  have h₂ : i + (j + 1) = t' := by omega
  have h :
      ιTensorObj P Q i j t ht ≫ (HomologicalComplex.tensorObj P Q).d t t' =
        (P.d i (i + 1) ▷ Q.X j) ≫ ιTensorObj P Q (i + 1) j t' h₁ +
        i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫ ιTensorObj P Q i (j + 1) t' h₂) := by
    rw [d_eq P Q F c, Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq P Q F c (show c.Rel i (i + 1) from rfl) j t' h₁,
      d₂_eq P Q F c i (show c.Rel j (j + 1) from rfl) t' h₂]
    exact congrArg (· + i.negOnePow •
      ((P.X i ◁ Q.d j (j + 1)) ≫ ιTensorObj P Q i (j + 1) t' h₂)) (one_smul ℤˣ _)
  simpa only [ModuleCat.comp_apply, add_apply, sign_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.whiskerRight_apply]
    using ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)

private lemma differential_apply {A B : Complex R} {n m i v v₀ i₁ : ℤ}
    (hnm : n + 1 = m) (hiv : i + m = v) (hv₀ : v₀ = v - 1) (hi₁ : i + 1 = i₁)
    (f : Cochain A B n) (x : A.X i) :
    ((δ n m f).v i v hiv) x =
      B.d v₀ v (f.v i v₀ (by omega) x) +
      m.negOnePow • f.v i₁ v (by omega) (A.d i i₁ x) := by
  rw [δ_v n m hnm f i v hiv v₀ i₁ hv₀ hi₁, add_apply, sign_apply,
    ModuleCat.comp_apply, ModuleCat.comp_apply]

private lemma curry_comm {n m : ℤ} (hnm : n + 1 = m)
    (f : Cochain (HomologicalComplex.tensorObj P Q) J n) :
    δ n m (curryDegree n f) = curryDegree m (δ n m f) := by
  apply Cochain.ext
  intro i u' hi
  apply ModuleCat.hom_ext
  ext x : 1
  apply Cochain.ext
  intro j v hj
  apply ModuleCat.hom_ext
  ext y
  change ((δ n m (curryDegree n f)).v i u' hi x).v j v hj y =
    ((curryDegree m (δ n m f)).v i u' hi x).v j v hj y
  have hu : u' - 1 + 1 = u' := by omega
  have hn : i + n = u' - 1 := by omega
  have hv : j + (u' - 1) = v - 1 := by omega
  have hi₁ : (i + 1) + n = u' := by omega
  have hj₁ : (j + 1) + (u' - 1) = v := by omega
  rw [differential_apply hnm hi rfl rfl, curryDegree_apply hi hj,
    differential_apply hnm (by omega : i + j + m = v) rfl rfl]
  change (δ (u' - 1) u' ((curryDegree n f).v i (u' - 1) hn x) +
      m.negOnePow • (show Cochain Q J u' from
        (curryDegree n f).v (i + 1) u' hi₁ (P.d i (i + 1) x))).v j v hj y = _
  rw [Cochain.add_v, Cochain.units_smul_v, add_apply, sign_apply,
    differential_apply hu hj rfl rfl, curryDegree_apply hn hv,
    curryDegree_apply_at hn hj₁ (by omega : i + (j + 1) = i + j + 1),
    curryDegree_apply_at hi₁ hj (by omega : i + 1 + j = i + j + 1),
    tensor_d_apply i j (i + j) (i + j + 1) rfl rfl,
    map_add, map_sign, smul_add, smul_smul]
  -- The inner Hom differential has target degree i + m.
  have hsign : m.negOnePow * i.negOnePow = u'.negOnePow := by
    rw [← Int.negOnePow_add, add_comm, hi]
  rw [hsign, add_assoc, add_comm (u'.negOnePow • _)]

/-- Tensor–Hom currying for integer-indexed cochain complexes of modules. -/
noncomputable def tensorHomIso (P Q J : Complex R) :
    linearHomComplex R (HomologicalComplex.tensorObj P Q) J ≅
      linearHomComplex R P (linearHomComplex R Q J) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (curryEquiv n).toModuleIso)
    (fun n m h => by
      apply ModuleCat.hom_ext
      ext f : 1
      exact curry_comm h f)

@[simp]
theorem tensorHomIso_apply (P Q J : Complex R) {n i j u' v : ℤ}
    (hi : i + n = u') (hj : j + u' = v) (f : Cochain (HomologicalComplex.tensorObj P Q) J n)
    (x : P.X i) (y : Q.X j) :
    (((tensorHomIso P Q J).hom.f n f).v i u' hi x).v j v hj y =
      f.v (i + j) v (by omega) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y)) :=
  curryDegree_apply hi hj f x y

/-- Precomposition in the first variable and postcomposition in the second
variable of the linear cochain Hom. -/
def homMap {A A' B B' : Complex R} (g : A' ⟶ A) (h : B ⟶ B') :
    linearHomComplex R A B ⟶ linearHomComplex R A' B' where
  f n := ModuleCat.ofHom
    { toFun := fun f => ((Cochain.ofHom g).comp f (zero_add n)).comp
        (Cochain.ofHom h) (add_zero n)
      map_add' := by intros; simp [Cochain.comp_add]
      map_smul' := by intros; simp [Cochain.comp_smul] }
  comm' := by
    intro n m _
    apply ModuleCat.hom_ext
    ext f : 1
    change δ n m (((Cochain.ofHom g).comp f (zero_add n)).comp (Cochain.ofHom h) (add_zero n)) =
      ((Cochain.ofHom g).comp (δ n m f) (zero_add m)).comp (Cochain.ofHom h) (add_zero m)
    simp

@[simp]
theorem homMap_apply {A A' B B' : Complex R} (g : A' ⟶ A) (h : B ⟶ B')
    {n i v : ℤ} (hi : i + n = v) (f : Cochain A B n) (x : A'.X i) :
    ((homMap g h).f n f).v i v hi x = h.f v (f.v i v hi (g.f i x)) := by
  change ((((Cochain.ofHom g).comp f (zero_add n)).comp (Cochain.ofHom h) (add_zero n)).v i v hi) x =
    _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply]

/-- The action of a map on a pure tensor in a summand of the total tensor. -/
private lemma tensorHom_apply {P' Q' : Complex R} (a : P' ⟶ P) (b : Q' ⟶ Q)
    (i j : ℤ) (x : P'.X i) (y : Q'.X j) :
    (HomologicalComplex.tensorHom a b).f (i + j)
      (ιTensorObj P' Q' i j (i + j) rfl (x ⊗ₜ[R] y)) =
      ιTensorObj P Q i j (i + j) rfl (a.f i x ⊗ₜ[R] b.f j y) := by
  have h := HomologicalComplex.ι_mapBifunctorMap
    (K₁ := P') (K₂ := Q') (L₁ := P) (L₂ := Q) (f₁ := a) (f₂ := b)
    (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) i j (i + j) rfl
  change ιTensorObj P' Q' i j (i + j) rfl ≫ (HomologicalComplex.tensorHom a b).f (i + j) =
    (a.f i ▷ Q'.X j) ≫ (P.X i ◁ b.f j) ≫ ιTensorObj P Q i j (i + j) rfl at h
  simpa only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] using
    ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)

/-- The currying isomorphism commutes with precomposition in both tensor factors
and postcomposition in the target. In particular it commutes with the quotient
action defined by precomposition with multiplication on a factor. -/
theorem tensorHomIso_natural {P' Q' J' : Complex R}
    (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J') :
    homMap (HomologicalComplex.tensorHom a b) c ≫ (tensorHomIso P' Q' J').hom =
      (tensorHomIso P Q J).hom ≫ homMap a (homMap b c) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext f : 1
  apply Cochain.ext
  intro i u' hi
  apply ModuleCat.hom_ext
  ext x : 1
  apply Cochain.ext
  intro j v hj
  apply ModuleCat.hom_ext
  ext y
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, tensorHomIso_apply,
    homMap_apply, tensorHom_apply]

/-- The linear cochain tensor–Hom adjunction with its component formula and
naturality in the two sources and the target. -/
theorem tensorHomAdjunction : Spec.TensorHomAdjunction.{u} := by
  intro R _
  refine ⟨@homMap R _, tensorHomIso, ?_, ?_, ?_⟩
  · exact @homMap_apply R _
  · exact @tensorHomIso_apply R _
  · exact fun a b c => tensorHomIso_natural a b c

end CommutativeAlgebraNotes.CochainTensorHom
