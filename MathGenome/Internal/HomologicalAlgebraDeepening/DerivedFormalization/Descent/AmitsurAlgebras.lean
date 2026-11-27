import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras

/-! The augmented cosimplicial algebra of a commutative ring map. -/

open CategoryTheory
open scoped BigOperators TensorProduct

namespace DerivedFormalization.Descent.AmitsurAlgebras


universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- Tensor power with `n` ordered factors. -/
abbrev TensorPower (n : ℕ) := AmitsurAlgebrasSpec.tensorPower A B n

/-- Degree `p` consists of `p + 1` factors. -/
abbrev Degree (p : ℕ) := TensorPower A B (p + 1)

/-- The inclusion into one tensor position. -/
noncomputable def factor {n : ℕ} (i : Fin n) : B →ₐ[A] TensorPower A B n :=
  AmitsurAlgebrasSpec.factor A B i

variable {A B}

noncomputable def liftFactors {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
    (f : Fin n → B →ₐ[A] D) : TensorPower A B n →ₐ[A] D :=
  AmitsurAlgebrasSpec.liftFactors f

@[simp]
theorem liftFactors_tprod {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
    (f : Fin n → B →ₐ[A] D) (x : Fin n → B) :
    liftFactors f (PiTensorProduct.tprod A x) = ∏ i, f i (x i) := by
  change PiTensorProduct.lift _ (PiTensorProduct.tprod A x) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

@[simp]
theorem liftFactors_factor {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
    (f : Fin n → B →ₐ[A] D) (i : Fin n) (b : B) :
    liftFactors f (factor A B i b) = f i b := by
  rw [factor, AmitsurAlgebrasSpec.factor, PiTensorProduct.singleAlgHom_apply, liftFactors_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

@[simp]
theorem liftFactors_comp_factor {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
    (f : Fin n → B →ₐ[A] D) (i : Fin n) :
    (liftFactors f).comp (factor A B i) = f i := by
  ext b
  exact liftFactors_factor f i b

theorem hom_ext {n : ℕ} {D : Type w} [CommRing D] [Algebra A D]
    {f g : TensorPower A B n →ₐ[A] D}
    (h : ∀ i, f.comp (factor A B i) = g.comp (factor A B i)) : f = g :=
  PiTensorProduct.algHom_ext h

/-- Push factors forward along a function of positions. The simplex diagram uses monotone
functions. Arbitrary functions also give algebra maps since the factors commute. -/
noncomputable def map {m n : ℕ} (f : Fin m → Fin n) :
    TensorPower A B m →ₐ[A] TensorPower A B n :=
  liftFactors fun i ↦ factor A B (f i)

@[simp]
theorem map_comp_factor {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) :
    (map f).comp (factor A B i) = factor A B (f i) :=
  liftFactors_comp_factor _ _

@[simp]
theorem map_factor {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) (b : B) :
    map f (factor A B i b) = factor A B (f i) b :=
  liftFactors_factor _ _ _

/-- On a pure tensor, multiply the entries in each fiber. An empty fiber contributes `1`. -/
theorem map_tprod {m n : ℕ} (f : Fin m → Fin n) (x : Fin m → B) :
    map f (PiTensorProduct.tprod A x) =
      PiTensorProduct.tprod A (fun j ↦ ∏ i ∈ Finset.univ.filter (fun i ↦ f i = j), x i) := by
  rw [map, liftFactors_tprod]
  simp only [factor, AmitsurAlgebrasSpec.factor, PiTensorProduct.singleAlgHom_apply,
    ← PiTensorProduct.tprod_prod]
  congr 1
  funext j
  rw [Finset.prod_apply, Finset.prod_filter]
  exact Finset.prod_congr rfl fun i _ ↦ by
    by_cases h : f i = j <;> simp [h]

@[simp]
theorem map_id (n : ℕ) :
    map (id : Fin n → Fin n) = AlgHom.id A (TensorPower A B n) := by
  apply hom_ext
  intro i
  simp

theorem map_comp {l m n : ℕ} (f : Fin l → Fin m) (g : Fin m → Fin n) :
    map (g ∘ f) = (map g).comp (map f : TensorPower A B l →ₐ[A] _) := by
  apply hom_ext
  intro i
  simp [AlgHom.comp_assoc]

/-- Insert the unit into position `i`. -/
noncomputable def coface {p : ℕ} (i : Fin (p + 2)) :
    Degree A B p →ₐ[A] Degree A B (p + 1) :=
  map i.succAbove

/-- Multiply the two entries in positions `i` and `i+1`. -/
noncomputable def codegeneracy {p : ℕ} (i : Fin (p + 1)) :
    Degree A B (p + 1) →ₐ[A] Degree A B p :=
  map i.predAbove

theorem coface_tprod {p : ℕ} (i : Fin (p + 2)) (x : Fin (p + 1) → B) :
    coface i (PiTensorProduct.tprod A x) = PiTensorProduct.tprod A (i.insertNth 1 x) := by
  rw [coface, map_tprod]
  congr 1
  funext j
  refine i.succAboveCases ?_ (fun k ↦ ?_) j
  · rw [Fin.insertNth_apply_same]
    have : Finset.univ.filter (fun k ↦ i.succAbove k = i) = ∅ := by simp
    rw [this, Finset.prod_empty]
  · rw [Fin.insertNth_apply_succAbove]
    have : Finset.univ.filter (fun l ↦ i.succAbove l = i.succAbove k) = {k} := by
      ext l
      simp
    rw [this, Finset.prod_singleton]

theorem codegeneracy_tprod {p : ℕ} (i : Fin (p + 1)) (x : Fin (p + 2) → B) :
    codegeneracy i (PiTensorProduct.tprod A x) =
      PiTensorProduct.tprod A (i.castSucc.contractNth (· * ·) x) := by
  rw [codegeneracy, map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    have hs : i.castSucc.succAbove i = i.succ :=
      Fin.succAbove_of_le_castSucc _ _ le_rfl
    have hf : Finset.univ.filter (fun k ↦ i.predAbove k = i) = {i.castSucc, i.succ} := by
      ext k
      refine i.castSucc.succAboveCases ?_ (fun l ↦ ?_) k
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.predAbove_succAbove,
          Finset.mem_insert, Finset.mem_singleton, Fin.succAbove_ne, false_or]
        rw [← hs, Fin.succAbove_right_inj]
    rw [hf, Finset.prod_pair]
    exact Fin.ne_of_lt Fin.castSucc_lt_succ
  · rw [Fin.contractNth_apply_of_ne _ _ _ _ (fun he ↦ h (Fin.ext he.symm))]
    have hf : Finset.univ.filter (fun k ↦ i.predAbove k = j) = {i.castSucc.succAbove j} := by
      ext k
      refine i.castSucc.succAboveCases ?_ (fun l ↦ ?_) k
      · simp [Ne.symm h]
      · simp
    rw [hf, Finset.prod_singleton]

variable (A B)

/-- The algebra map from the augmented term to each tensor power. -/
noncomputable def unit (n : ℕ) : A →ₐ[A] TensorPower A B n :=
  Algebra.ofId A _

noncomputable def augmentation : A →ₐ[A] Degree A B 0 :=
  unit A B 1

@[simp]
theorem map_comp_unit {m n : ℕ} (f : Fin m → Fin n) :
    (map f).comp (unit A B m) = unit A B n :=
  Subsingleton.elim _ _

@[simp]
theorem coface_comp_augmentation (i : Fin 2) :
    (coface i).comp (augmentation A B) = unit A B 2 :=
  map_comp_unit A B i.succAbove

/-- The cosimplicial tensor powers with all simplex maps. Functoriality proves all
coface and codegeneracy identities. -/
noncomputable def diagram : SimplexCategory ⥤ CommAlgCat.{max u v} A where
  obj p := CommAlgCat.of A (Degree A B p.len)
  map f := CommAlgCat.ofHom (map f.toOrderHom)
  map_id p := CommAlgCat.hom_ext (map_id (A := A) (B := B) (p.len + 1))
  map_comp f g := CommAlgCat.hom_ext (map_comp f.toOrderHom g.toOrderHom)

@[simp]
theorem diagram_map_hom {p q : SimplexCategory} (f : p ⟶ q) :
    ((diagram A B).map f).hom = (map f.toOrderHom : Degree A B p.len →ₐ[A] _) := rfl

@[simp]
theorem diagram_δ_hom {p : ℕ} (i : Fin (p + 2)) :
    ((diagram A B).map (SimplexCategory.δ i)).hom =
      (coface i : Degree A B p →ₐ[A] Degree A B (p + 1)) := rfl

@[simp]
theorem diagram_σ_hom {p : ℕ} (i : Fin (p + 1)) :
    ((diagram A B).map (SimplexCategory.σ i)).hom =
      (codegeneracy i : Degree A B (p + 1) →ₐ[A] Degree A B p) := rfl

/-- Extend the diagram to the empty ordinal. The copy of `A` is universe-lifted
to bundle it in the same category as the tensor powers. -/
noncomputable def augmentedDiagram : AugmentedSimplexCategory ⥤ CommAlgCat.{max u v} A :=
  WithInitial.lift (Z := CommAlgCat.of A (ULift.{v} A)) (diagram A B)
    (fun p ↦ CommAlgCat.ofHom ((unit A B (p.len + 1)).comp ULift.algEquiv.toAlgHom))
    (fun _ _ f ↦ by
      apply CommAlgCat.hom_ext
      change (map f.toOrderHom).comp ((unit A B _).comp ULift.algEquiv.toAlgHom) =
        (unit A B _).comp ULift.algEquiv.toAlgHom
      rw [← AlgHom.comp_assoc, map_comp_unit])

@[simp]
theorem augmentedDiagram_map_homTo (p : SimplexCategory) :
    ((augmentedDiagram A B).map (WithInitial.homTo p)).hom =
      (unit A B (p.len + 1)).comp ULift.algEquiv.toAlgHom := rfl

theorem augmentedDiagram_spec :
    AmitsurAlgebrasSpec.IsOrderedAugmentedDiagram A B (augmentedDiagram A B) :=
  ⟨rfl, fun _ ↦ rfl, fun _ ↦ HEq.rfl, fun _ ↦ HEq.rfl⟩

theorem orderedAugmentedDiagram : AmitsurAlgebrasSpec.orderedAugmentedDiagram.{u, v} :=
  fun A B _ _ _ ↦ ⟨augmentedDiagram A B, augmentedDiagram_spec A B⟩

theorem coface_comp_coface {p : ℕ} {i j : Fin (p + 2)} (h : i ≤ j) :
    (coface j.succ).comp (coface i) = (coface i.castSucc).comp
      (coface j : Degree A B p →ₐ[A] Degree A B (p + 1)) := by
  have hδ := congrArg (fun f ↦ ((diagram A B).map f).hom) (SimplexCategory.δ_comp_δ h)
  rw [Functor.map_comp, Functor.map_comp, CommAlgCat.hom_comp, CommAlgCat.hom_comp] at hδ
  exact hδ

/-- The tensor power of zero factors is the base algebra. -/
noncomputable def emptyEquiv : TensorPower A B 0 ≃ₐ[A] A :=
  AlgEquiv.ofAlgHom (liftFactors fun i ↦ Fin.elim0 i) (unit A B 0)
    (Subsingleton.elim _ _) (hom_ext fun i ↦ Fin.elim0 i)

@[simp]
theorem emptyEquiv_symm_toAlgHom : (emptyEquiv A B).symm.toAlgHom = unit A B 0 := rfl

theorem map_from_empty {n : ℕ} (f : Fin 0 → Fin n) :
    map f = (unit A B n).comp (emptyEquiv A B).toAlgHom :=
  hom_ext fun i ↦ Fin.elim0 i

theorem emptyPower : AmitsurAlgebrasSpec.emptyPower.{u, v} :=
  fun A B _ _ _ ↦ ⟨emptyEquiv A B, emptyEquiv_symm_toAlgHom A B⟩

/-- The degree-zero tensor power is one copy of the extension algebra. -/
noncomputable def oneEquiv : Degree A B 0 ≃ₐ[A] B :=
  AlgEquiv.ofAlgHom (liftFactors fun _ ↦ AlgHom.id A B) (factor A B 0)
    (liftFactors_comp_factor _ 0) (by
      apply hom_ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rw [AlgHom.comp_assoc, liftFactors_comp_factor, AlgHom.comp_id, AlgHom.id_comp])

@[simp]
theorem oneEquiv_symm_apply (b : B) : (oneEquiv A B).symm b = factor A B 0 b := rfl

@[simp]
theorem oneEquiv_augmentation (a : A) :
    oneEquiv A B (augmentation A B a) = algebraMap A B a :=
  (oneEquiv A B).commutes a

theorem onePower : AmitsurAlgebrasSpec.onePower.{u, v} :=
  fun A B _ _ _ ↦ ⟨oneEquiv A B, rfl, AlgHom.ext (oneEquiv_augmentation A B)⟩

/-- Concatenating two ordered sets of factors amounts to taking a binary tensor product. -/
noncomputable def appendEquiv (m n : ℕ) :
    TensorPower A B m ⊗[A] TensorPower A B n ≃ₐ[A] TensorPower A B (m + n) := by
  let left : TensorPower A B m →ₐ[A] TensorPower A B (m + n) := map (Fin.castAdd n)
  let right : TensorPower A B n →ₐ[A] TensorPower A B (m + n) := map (Fin.natAdd m)
  let f := Algebra.TensorProduct.productMap left right
  let g : TensorPower A B (m + n) →ₐ[A] TensorPower A B m ⊗[A] TensorPower A B n :=
    liftFactors (Fin.addCases
      (fun i ↦ Algebra.TensorProduct.includeLeft.comp (factor A B i))
      (fun j ↦ Algebra.TensorProduct.includeRight.comp (factor A B j)))
  have hleft : g.comp left = Algebra.TensorProduct.includeLeft := by
    apply hom_ext
    intro i
    simp [left, g, AlgHom.comp_assoc]
  have hright : g.comp right = Algebra.TensorProduct.includeRight := by
    apply hom_ext
    intro i
    simp [right, g, AlgHom.comp_assoc, Fin.addCases_right]
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply hom_ext
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [f, g, AlgHom.comp_assoc, liftFactors_comp_factor, Fin.addCases_left,
        AlgHom.id_comp]
      rw [← AlgHom.comp_assoc, Algebra.TensorProduct.productMap_left]
      exact map_comp_factor _ _
    · simp only [f, g, AlgHom.comp_assoc, liftFactors_comp_factor, Fin.addCases_right,
        AlgHom.id_comp]
      rw [← AlgHom.comp_assoc, Algebra.TensorProduct.productMap_right]
      exact map_comp_factor _ _
  · apply Algebra.TensorProduct.ext
    · rw [AlgHom.comp_assoc, show f.comp Algebra.TensorProduct.includeLeft = left by simp [f],
        hleft, AlgHom.id_comp]
    · change (g.comp f).comp Algebra.TensorProduct.includeRight = Algebra.TensorProduct.includeRight
      rw [AlgHom.comp_assoc, show f.comp Algebra.TensorProduct.includeRight = right by simp [f],
        hright]

@[simp]
theorem appendEquiv_tmul {m n : ℕ} (x : TensorPower A B m) (y : TensorPower A B n) :
    appendEquiv A B m n (x ⊗ₜ[A] y) = map (Fin.castAdd n) x * map (Fin.natAdd m) y :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ x y

theorem appendPowers : AmitsurAlgebrasSpec.appendPowers.{u, v} :=
  fun A B _ _ _ m n ↦ ⟨appendEquiv A B m n, appendEquiv_tmul A B⟩

section BaseChange

variable (S : Type w) [CommRing S] [Algebra A S]

private noncomputable def baseChangeTo (n : ℕ) :
    S ⊗[A] TensorPower A B n →ₐ[S] TensorPower S (S ⊗[A] B) n :=
  AlgHom.liftEquiv A S _ _ (liftFactors fun i ↦
    ((factor S (S ⊗[A] B) i).restrictScalars A).comp Algebra.TensorProduct.includeRight)

private noncomputable def baseChangeFrom (n : ℕ) :
    TensorPower S (S ⊗[A] B) n →ₐ[S] S ⊗[A] TensorPower A B n :=
  liftFactors fun i ↦ Algebra.TensorProduct.map (AlgHom.id S S) (factor A B i)

private theorem baseChangeTo_tmul_factor {n : ℕ} (i : Fin n) (s : S) (b : B) :
    baseChangeTo A B S n (s ⊗ₜ[A] factor A B i b) =
      factor S (S ⊗[A] B) i (s ⊗ₜ[A] b) := by
  rw [baseChangeTo, AlgHom.liftEquiv_tmul, liftFactors_factor]
  change s • factor S (S ⊗[A] B) i (1 ⊗ₜ[A] b) = _
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem baseChangeFrom_factor {n : ℕ} (i : Fin n) (s : S) (b : B) :
    baseChangeFrom A B S n (factor S (S ⊗[A] B) i (s ⊗ₜ[A] b)) =
      s ⊗ₜ[A] factor A B i b := by
  rw [baseChangeFrom, liftFactors_factor, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- Base change of an ordered tensor power agrees with the ordered power of the
base-changed algebra, with the same factor positions. -/
noncomputable def baseChangeEquiv (n : ℕ) :
    S ⊗[A] TensorPower A B n ≃ₐ[S] TensorPower S (S ⊗[A] B) n :=
  AlgEquiv.ofAlgHom (baseChangeTo A B S n) (baseChangeFrom A B S n)
    (by
      apply hom_ext
      intro i
      apply Algebra.TensorProduct.ext_ring
      refine AlgHom.ext fun b ↦ ?_
      change baseChangeTo A B S n
          (baseChangeFrom A B S n (factor S (S ⊗[A] B) i (1 ⊗ₜ[A] b))) =
        factor S (S ⊗[A] B) i (1 ⊗ₜ[A] b)
      rw [baseChangeFrom_factor, baseChangeTo_tmul_factor])
    (by
      apply Algebra.TensorProduct.ext_ring
      apply hom_ext
      intro i
      refine AlgHom.ext fun b ↦ ?_
      change baseChangeFrom A B S n (baseChangeTo A B S n (1 ⊗ₜ[A] factor A B i b)) =
        1 ⊗ₜ[A] factor A B i b
      rw [baseChangeTo_tmul_factor, baseChangeFrom_factor])

@[simp]
theorem baseChangeEquiv_tmul_factor {n : ℕ} (i : Fin n) (s : S) (b : B) :
    baseChangeEquiv A B S n (s ⊗ₜ[A] factor A B i b) =
      factor S (S ⊗[A] B) i (s ⊗ₜ[A] b) :=
  baseChangeTo_tmul_factor A B S i s b

theorem baseChangeEquiv_natural {m n : ℕ} (f : Fin m → Fin n) :
    (baseChangeEquiv A B S n).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id S S) (map f)) =
      (map f).comp (baseChangeEquiv A B S m).toAlgHom := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  refine AlgHom.ext fun b ↦ ?_
  change baseChangeEquiv A B S n
      (Algebra.TensorProduct.map (AlgHom.id S S) (map f) (1 ⊗ₜ[A] factor A B i b)) =
    map f (baseChangeEquiv A B S m (1 ⊗ₜ[A] factor A B i b))
  simp

end BaseChange

theorem baseChangePowers : AmitsurAlgebrasSpec.baseChangePowers.{u, v, w} :=
  fun A B _ _ _ S _ _ ↦ ⟨baseChangeEquiv A B S, baseChangeEquiv_tmul_factor A B S,
    baseChangeEquiv_natural A B S⟩

end DerivedFormalization.Descent.AmitsurAlgebras
