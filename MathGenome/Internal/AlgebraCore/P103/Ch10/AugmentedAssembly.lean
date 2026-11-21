import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.AugmentedAssembly
import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexConstruction
import MathGenome.Internal.AlgebraCore.P103.Ch10.ShiftsAndCones
import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexAssembly

namespace P103.Ch10.AugmentedAssembly
open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.AugmentedAssembly
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.ShiftsAndCones
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
variable {R : Type u} [Ring R] {c : ComplexShape ℤ}

theorem unaugmented_negative (K : Bicomplex.{u,v} R c) (p q : ℤ) (hp : p < 0) :
    Subsingleton (((unaugmented K).X p).X q) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply (HomologicalComplex.eval (ModuleCat R) c q).map_isZero
  exact K.isZero_stupidTrunc_X (nonnegativeEmbedding c) p (by
    intro i hi
    change i.val = p at hi
    have := i.property
    omega)

@[simp, reassoc]
theorem columnTo_from (K : Bicomplex.{u,v} R c) (p : ℤ) :
    columnToAugmented K p ≫ columnFromAugmented K p = 𝟙 _ := by
  by_cases hp : 0 ≤ p
  · simp [columnToAugmented, columnFromAugmented, hp]
  · apply HomologicalComplex.Hom.ext
    funext q
    have := unaugmented_negative K p q (by omega)
    apply ModuleCat.hom_ext
    exact Subsingleton.elim _ _

@[simp, reassoc]
theorem columnFrom_to (K : Bicomplex.{u,v} R c) (p : ℤ) (hp : 0 ≤ p) :
    columnFromAugmented K p ≫ columnToAugmented K p = 𝟙 _ := by
  simp [columnToAugmented, columnFromAugmented, hp]

/-- The retained horizontal maps are the original maps in retained coordinates. -/
theorem retained_d (K : Bicomplex.{u,v} R c) (p p' : ℤ) (hp : 0 ≤ p) (hp' : 0 ≤ p') :
    (unaugmented K).d p p' =
      (retainedColumnIso K p hp).hom ≫ K.d p p' ≫ (retainedColumnIso K p' hp').inv := by
  simpa [unaugmented, retainedColumnIso, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.stupidTrunc, nonnegativeEmbedding, ComplexShape.Embedding.mk'] using
    (K.restriction (nonnegativeEmbedding c)).extend_d_eq (nonnegativeEmbedding c)
      (i := ⟨p, hp⟩) (j := ⟨p', hp'⟩) rfl rfl

@[reassoc]
theorem retained_d_to (K : Bicomplex.{u,v} R c) (p p' : ℤ) (hp : 0 ≤ p) (hp' : 0 ≤ p') :
    (unaugmented K).d p p' ≫ columnToAugmented K p' =
      columnToAugmented K p ≫ K.d p p' := by
  rw [retained_d K p p' hp hp']
  simp [columnToAugmented, hp, hp']

@[reassoc]
theorem retained_from_d (K : Bicomplex.{u,v} R c) (p p' : ℤ) (hp : 0 ≤ p) (hp' : 0 ≤ p') :
    columnFromAugmented K p ≫ (unaugmented K).d p p' =
      K.d p p' ≫ columnFromAugmented K p' := by
  rw [retained_d K p p' hp hp']
  simp [columnFromAugmented, hp, hp']

variable [ComplexShape.TensorSigns c]

@[simp, reassoc]
theorem inclusion_totalTo (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n) :
    totalInclusion (unaugmented K) p q n h ≫ totalToAugmented K n =
      (columnToAugmented K p).f q ≫ totalInclusion K p q n h := by
  exact (unaugmented K).ι_totalDesc _ p q h

@[simp, reassoc]
theorem inclusion_totalFrom (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n) :
    totalInclusion K p q n h ≫ totalFromAugmented K n =
      (columnFromAugmented K p).f q ≫ totalInclusion (unaugmented K) p q n h := by
  exact K.ι_totalDesc _ p q h

@[simp, reassoc]
theorem totalTo_from (K : Bicomplex.{u,v} R c) (n : ℤ) :
    totalToAugmented K n ≫ totalFromAugmented K n = 𝟙 _ := by
  apply P103.Ch10.TotalComplexAssembly.total_hom_ext (unaugmented K) n
  intro p q h
  rw [inclusion_totalTo_assoc, inclusion_totalFrom,
    ← Category.assoc]
  have hf := congrArg (fun f => f.f q) (columnTo_from K p)
  change (columnToAugmented K p).f q ≫ (columnFromAugmented K p).f q = 𝟙 _ at hf
  rw [hf, Category.id_comp, Category.comp_id]

@[simp, reassoc]
theorem totalTo_projection (K : Bicomplex.{u,v} R c) (n : ℤ) :
    totalToAugmented K n ≫ totalProjection K (-1) (n + 1) n (by omega) = 0 := by
  apply P103.Ch10.TotalComplexAssembly.total_hom_ext (unaugmented K) n
  intro p q h
  rw [inclusion_totalTo_assoc, comp_zero]
  by_cases hp : 0 ≤ p
  · rw [P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne K p q (-1) (n + 1)
      n h (by omega) (Or.inl (by omega)), comp_zero]
  · have := unaugmented_negative K p q (by omega)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp

@[simp, reassoc]
theorem augmentationInclusion_totalFrom (K : Bicomplex.{u,v} R c) (n : ℤ) :
    totalInclusion K (-1) (n + 1) n (by omega) ≫ totalFromAugmented K n = 0 := by
  rw [inclusion_totalFrom]
  have hz : columnFromAugmented K (-1) = 0 := by simp [columnFromAugmented]
  rw [hz]
  simp

/-- Decomposition of the total into the p = -1 summand and the retained ones. -/
theorem augmented_decomposition (K : Bicomplex.{u,v} R c)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q)) (n : ℤ) :
    totalProjection K (-1) (n + 1) n (by omega) ≫
        totalInclusion K (-1) (n + 1) n (by omega) +
      totalFromAugmented K n ≫ totalToAugmented K n = 𝟙 _ := by
  apply P103.Ch10.TotalComplexAssembly.total_hom_ext K n
  intro p q h
  by_cases hp : p = -1
  · subst p
    have hq : q = n + 1 := by omega
    subst q
    rw [Preadditive.comp_add, ← Category.assoc,
      P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self,
      Category.id_comp, augmentationInclusion_totalFrom_assoc,
      zero_comp, add_zero, Category.comp_id]
  · by_cases hp0 : 0 ≤ p
    · rw [Preadditive.comp_add, ← Category.assoc,
        P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne K p q (-1) (n + 1)
          n h (by omega) (Or.inl hp), zero_comp, zero_add,
        inclusion_totalFrom_assoc, inclusion_totalTo, ← Category.assoc]
      have hf := congrArg (fun f => f.f q) (columnFrom_to K p hp0)
      change (columnFromAugmented K p).f q ≫ (columnToAugmented K p).f q = 𝟙 _ at hf
      rw [hf, Category.id_comp, Category.comp_id]
    · have := hs p q (by omega)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp

private theorem evaluate_equality {M N : ModuleCat.{v} R} {f g : M ⟶ N}
    (h : f = g) (x : M) : f.hom x = g.hom x :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x

theorem augmentedCoordinates_inverse (K : Bicomplex.{u,v} R c)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q)) (n : ℤ) :
    Function.LeftInverse (assembleCoordinates K n) (augmentedCoordinates K n) ∧
    Function.RightInverse (assembleCoordinates K n) (augmentedCoordinates K n) := by
  constructor
  · intro z
    exact evaluate_equality (augmented_decomposition K hs n) z
  · rintro ⟨y, x⟩
    apply Prod.ext
    · have hi := evaluate_equality
        (P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self K (-1) (n + 1) n
          (by omega)) y
      have ht := evaluate_equality (totalTo_projection K n) x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_zero,
        LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at hi ht
      change (totalProjection K (-1) (n + 1) n _).hom
        ((totalInclusion K (-1) (n + 1) n _).hom y + (totalToAugmented K n).hom x) = y
      rw [map_add, hi, ht, add_zero]
    · have hi := evaluate_equality (augmentationInclusion_totalFrom K n) y
      have ht := evaluate_equality (totalTo_from K n) x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_zero,
        LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at hi ht
      change (totalFromAugmented K n).hom
        ((totalInclusion K (-1) (n + 1) n _).hom y + (totalToAugmented K n).hom x) = x
      rw [map_add, hi, ht, zero_add]

private theorem chain_projection_d_at (K : ChainBicomplex.{u,v} R)
    (p p' q q' n m : ℤ) (hp : p' = p + 1) (hq : q' = q + 1)
    (hm : m = n - 1) (h : p + q = m) :
    (total K).d n m ≫ totalProjection K p q m h =
      totalProjection K p' q n (by omega) ≫ (K.d p' p).f q +
      p.negOnePow • (totalProjection K p q' n (by omega) ≫ (K.X p).d q' q) := by
  subst p' q' m
  exact P103.Ch10.TotalComplexAssembly.chain_totalProjection_d K p q n h

private theorem cochain_inclusion_d_at (K : CochainBicomplex.{u,v} R)
    (p p' q q' n m : ℤ) (hp : p' = p + 1) (hq : q' = q + 1)
    (hm : m = n + 1) (h : p + q = n) :
    totalInclusion K p q n h ≫ (total K).d n m =
      (K.d p p').f q ≫ totalInclusion K p' q m (by omega) +
      p.negOnePow • ((K.X p).d q q' ≫ totalInclusion K p q' m (by omega)) := by
  subst p' q' m
  have hd := P103.Ch10.TotalComplexAssembly.cochain_totalInclusion_d K p q n (n + 1) h
  rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (p + 1) q (n + 1) (by change p + 1 + q = n + 1; omega),
    K.ιTotalOrZero_eq (ComplexShape.up ℤ) p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)] at hd
  exact hd

/-- The augmentation components commute with the chain differentials. -/
theorem chainAugmentation_comm (K : ChainBicomplex.{u,v} R) (n : ℤ) :
    chainAugmentationComponent K (n + 1) ≫ (K.X (-1)).d (n + 1) n =
      (total (unaugmented K)).d (n + 1) n ≫ chainAugmentationComponent K n := by
  have hproj := chain_projection_d_at (unaugmented K) 0 1 n (n + 1) (n + 1) n
    (by omega) rfl (by omega) (by omega)
  simp only [Int.negOnePow_zero, one_smul] at hproj
  have hhor := congrArg (fun f => f.f n) (retained_d_to K 1 0 (by omega) (by omega))
  change ((unaugmented K).d 1 0).f n ≫ (columnToAugmented K 0).f n =
    (columnToAugmented K 1).f n ≫ (K.d 1 0).f n at hhor
  have hsq := congrArg (fun f => f.f n) (K.d_comp_d 1 0 (-1))
  change (K.d 1 0).f n ≫ (K.d 0 (-1)).f n = 0 at hsq
  have hz : ((unaugmented K).d 1 0).f n ≫ (columnToAugmented K 0).f n ≫
      (K.d 0 (-1)).f n = 0 := by
    rw [← Category.assoc, hhor, Category.assoc, hsq, comp_zero]
  have hv : (columnToAugmented K 0).f (n + 1) ≫ (K.d 0 (-1)).f (n + 1) ≫
      (K.X (-1)).d (n + 1) n =
      ((unaugmented K).X 0).d (n + 1) n ≫ (columnToAugmented K 0).f n ≫
        (K.d 0 (-1)).f n := by
    rw [(K.d 0 (-1)).comm, ← Category.assoc, (columnToAugmented K 0).comm,
      Category.assoc]
  dsimp only [chainAugmentationComponent]
  rw [← Category.assoc ((total (unaugmented K)).d (n + 1) n), hproj,
    Preadditive.add_comp]
  simp only [Category.assoc]
  rw [hz, comp_zero, zero_add, hv]

/-- The cochain augmentation components commute with the cochain differentials. -/
theorem cochainAugmentation_comm (K : CochainBicomplex.{u,v} R) (n : ℤ) :
    cochainAugmentationComponent K n ≫ (total (unaugmented K)).d n (n + 1) =
      (K.X (-1)).d n (n + 1) ≫ cochainAugmentationComponent K (n + 1) := by
  have hinc := cochain_inclusion_d_at (unaugmented K) 0 1 n (n + 1) n (n + 1)
    (by omega) rfl rfl (by omega)
  simp only [Int.negOnePow_zero, one_smul] at hinc
  have hhor := congrArg (fun f => f.f n) (retained_from_d K 0 1 (by omega) (by omega))
  change (columnFromAugmented K 0).f n ≫ ((unaugmented K).d 0 1).f n =
    (K.d 0 1).f n ≫ (columnFromAugmented K 1).f n at hhor
  have hsq := congrArg (fun f => f.f n) (K.d_comp_d (-1) 0 1)
  change (K.d (-1) 0).f n ≫ (K.d 0 1).f n = 0 at hsq
  have hz : (K.d (-1) 0).f n ≫ (columnFromAugmented K 0).f n ≫
      ((unaugmented K).d 0 1).f n = 0 := by
    rw [hhor, ← Category.assoc, hsq, zero_comp]
  have hv : (K.d (-1) 0).f n ≫ (columnFromAugmented K 0).f n ≫
      ((unaugmented K).X 0).d n (n + 1) =
      (K.X (-1)).d n (n + 1) ≫ (K.d (-1) 0).f (n + 1) ≫
        (columnFromAugmented K 0).f (n + 1) := by
    rw [(columnFromAugmented K 0).comm, ← Category.assoc, (K.d (-1) 0).comm,
      Category.assoc]
  dsimp only [cochainAugmentationComponent]
  simp only [Category.assoc]
  rw [hinc, Preadditive.comp_add, Preadditive.comp_add]
  simp only [← Category.assoc] at hz hv ⊢
  rw [hz, zero_comp, zero_add, hv]

theorem chainAugmentation_exists (K : ChainBicomplex.{u,v} R) :
    ∃ f : total (unaugmented K) ⟶ K.X (-1),
      ∀ n, f.f n = chainAugmentationComponent K n := by
  exact ⟨ChainComplex.ofHom (chainAugmentationComponent K) (chainAugmentation_comm K),
    fun _ => rfl⟩

theorem cochainAugmentation_exists (K : CochainBicomplex.{u,v} R) :
    ∃ f : K.X (-1) ⟶ total (unaugmented K),
      ∀ n, f.f n = cochainAugmentationComponent K n := by
  exact ⟨CochainComplex.ofHom (cochainAugmentationComponent K) (cochainAugmentation_comm K),
    fun _ => rfl⟩


@[reassoc]
theorem totalFrom_projection (K : Bicomplex.{u,v} R c) (p q n : ℤ) (h : p + q = n) :
    totalFromAugmented K n ≫ totalProjection (unaugmented K) p q n h =
      totalProjection K p q n h ≫ (columnFromAugmented K p).f q := by
  apply P103.Ch10.TotalComplexAssembly.total_hom_ext K n
  intro i j hij
  rw [inclusion_totalFrom_assoc]
  by_cases hi : i = p
  · subst i
    have hj : j = q := by omega
    subst j
    simp
  · rw [P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne (unaugmented K) i j p q n hij h (Or.inl hi),
      P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne_assoc K i j p q n hij h (Or.inl hi), comp_zero, zero_comp]

@[reassoc]
theorem totalTo_projection_retained (K : Bicomplex.{u,v} R c)
    (p q n : ℤ) (h : p + q = n) (_hp : 0 ≤ p) :
    totalToAugmented K n ≫ totalProjection K p q n h =
      totalProjection (unaugmented K) p q n h ≫ (columnToAugmented K p).f q := by
  apply P103.Ch10.TotalComplexAssembly.total_hom_ext (unaugmented K) n
  intro i j hij
  rw [inclusion_totalTo_assoc]
  by_cases hi : i = p
  · subst i
    have hj : j = q := by omega
    subst j
    simp
  · rw [P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne K i j p q n hij h (Or.inl hi),
      P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne_assoc (unaugmented K) i j p q n hij h (Or.inl hi),
      comp_zero, zero_comp]

theorem total_target_ext (K : Bicomplex.{u,v} R c) (n : ℤ) {M : ModuleCat.{v} R}
    {f g : M ⟶ (total K).X n}
    (h : ∀ p q (hpq : p + q = n),
      f ≫ totalProjection K p q n hpq = g ≫ totalProjection K p q n hpq) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply P103.Ch10.TotalComplexAssembly.total_ext K n
  intro p q hpq
  exact evaluate_equality (h p q hpq) z

/-- The first component of the chain matrix. -/
theorem chain_augmentation_projection_d (K : ChainBicomplex.{u,v} R) (n : ℤ) :
    (total K).d n (n - 1) ≫ totalProjection K (-1) n (n - 1) (by omega) =
      totalFromAugmented K n ≫ chainAugmentationComponent K n -
      totalProjection K (-1) (n + 1) n (by omega) ≫ (K.X (-1)).d (n + 1) n := by
  have hd := chain_projection_d_at K (-1) 0 n (n + 1) n (n - 1)
    (by omega) rfl rfl (by omega)
  have hf := congrArg (fun f => f.f n) (columnFrom_to K 0 (by omega))
  change (columnFromAugmented K 0).f n ≫ (columnToAugmented K 0).f n = 𝟙 _ at hf
  rw [hd]
  simp only [chainAugmentationComponent]
  rw [totalFrom_projection_assoc, ← Category.assoc
    ((columnFromAugmented K 0).f n), hf, Category.id_comp]
  simp [Int.negOnePow_neg, sub_eq_add_neg]

/-- The retained component of the chain matrix. -/
theorem chain_totalFrom_d (K : ChainBicomplex.{u,v} R) (n : ℤ) :
    (total K).d n (n - 1) ≫ totalFromAugmented K (n - 1) =
      totalFromAugmented K n ≫ (total (unaugmented K)).d n (n - 1) := by
  apply total_target_ext (unaugmented K) (n - 1)
  intro p q h
  by_cases hp : 0 ≤ p
  · have hh := congrArg (fun f => f.f q) (retained_from_d K (p + 1) p (by omega) hp)
    change (columnFromAugmented K (p + 1)).f q ≫ ((unaugmented K).d (p + 1) p).f q =
      (K.d (p + 1) p).f q ≫ (columnFromAugmented K p).f q at hh
    rw [Category.assoc, totalFrom_projection, ← Category.assoc,
      P103.Ch10.TotalComplexAssembly.chain_totalProjection_d K p q n h,
      Category.assoc, P103.Ch10.TotalComplexAssembly.chain_totalProjection_d (unaugmented K) p q n h]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, totalFrom_projection_assoc]
    rw [hh, (columnFromAugmented K p).comm]
  · have := unaugmented_negative K p q (by omega)
    apply ModuleCat.hom_ext
    exact Subsingleton.elim _ _


private theorem cochain_projection_d_at (K : CochainBicomplex.{u,v} R)
    (p p' q q' n m : ℤ) (hp : p' = p - 1) (hq : q' = q - 1)
    (hm : m = n + 1) (h : p + q = m) :
    (total K).d n m ≫ totalProjection K p q m h =
      totalProjection K p' q n (by omega) ≫ (K.d p' p).f q +
      p.negOnePow • (totalProjection K p q' n (by omega) ≫ (K.X p).d q' q) := by
  subst p' q' m
  exact P103.Ch10.TotalComplexAssembly.cochain_totalProjection_d K p q n h

theorem cochain_augmentation_projection_d (K : CochainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q)) (n : ℤ) :
    (total K).d n (n + 1) ≫ totalProjection K (-1) ((n + 1) + 1) (n + 1) (by omega) =
      -(totalProjection K (-1) (n + 1) n (by omega) ≫
        (K.X (-1)).d (n + 1) ((n + 1) + 1)) := by
  have hd := cochain_projection_d_at K (-1) (-2) ((n + 1) + 1) (n + 1) n (n + 1)
    (by omega) (by omega) rfl (by omega)
  have hz : (K.d (-2) (-1)).f ((n + 1) + 1) = 0 := by
    have := hs (-2) ((n + 1) + 1) (by omega)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    simp
  rw [hd, hz, comp_zero, zero_add]
  simp [Int.negOnePow_neg]

/-- The off-diagonal term in the retained cochain coordinates is augmentation. -/
theorem cochain_totalFrom_d (K : CochainBicomplex.{u,v} R) (n : ℤ) :
    (total K).d n (n + 1) ≫ totalFromAugmented K (n + 1) =
      totalProjection K (-1) (n + 1) n (by omega) ≫ cochainAugmentationComponent K (n + 1) +
      totalFromAugmented K n ≫ (total (unaugmented K)).d n (n + 1) := by
  apply total_target_ext (unaugmented K) (n + 1)
  intro p q h
  by_cases hp : 0 ≤ p
  · rw [Category.assoc, totalFrom_projection, ← Category.assoc,
      P103.Ch10.TotalComplexAssembly.cochain_totalProjection_d K p q n h,
      Preadditive.add_comp]
    simp only [Preadditive.add_comp, Category.assoc]
    rw [P103.Ch10.TotalComplexAssembly.cochain_totalProjection_d (unaugmented K) p q n h]
    simp only [Preadditive.comp_add, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc, totalFrom_projection_assoc]
    by_cases hp0 : p = 0
    · subst p
      have hq : q = n + 1 := by omega
      subst q
      simp only [cochainAugmentationComponent, Category.assoc]
      rw [P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self]
      simp [columnFromAugmented, Int.negOnePow_zero]
    · have hh := congrArg (fun f => f.f q) (retained_from_d K (p - 1) p (by omega) hp)
      change (columnFromAugmented K (p - 1)).f q ≫ ((unaugmented K).d (p - 1) p).f q =
        (K.d (p - 1) p).f q ≫ (columnFromAugmented K p).f q at hh
      simp only [cochainAugmentationComponent, Category.assoc]
      rw [P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne (unaugmented K)
        0 (n + 1) p q (n + 1) (by omega) h (Or.inl (Ne.symm hp0))]
      simp only [comp_zero, zero_add]
      rw [hh, (columnFromAugmented K p).comm]
  · have := unaugmented_negative K p q (by omega)
    apply ModuleCat.hom_ext
    exact Subsingleton.elim _ _


/-- The splitting with any explicitly named adjacent vertical degree. -/
def coordinatesEquiv (K : Bicomplex.{u,v} R c)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q))
    (n q : ℤ) (h : -1 + q = n) :
    (total K).X n ≃ₗ[R] (K.X (-1)).X q × (total (unaugmented K)).X n :=
  LinearEquiv.ofBijective ((totalProjection K (-1) q n h).hom.prod
    (totalFromAugmented K n).hom) (by
      have hq : q = n + 1 := by omega
      subst q
      exact ⟨(augmentedCoordinates_inverse K hs n).1.injective,
        (augmentedCoordinates_inverse K hs n).2.surjective⟩)

private theorem chain_augmentation_projection_d_at (K : ChainBicomplex.{u,v} R)
    (n q : ℤ) (h : q = n + 1) :
    (total K).d n (n - 1) ≫ totalProjection K (-1) n (n - 1) (by omega) =
      totalFromAugmented K n ≫ chainAugmentationComponent K n -
      totalProjection K (-1) q n (by omega) ≫ (K.X (-1)).d q n := by
  subst q
  exact chain_augmentation_projection_d K n

/-- Full chain differential in the manuscript's coordinates. -/
theorem chain_coordinates_d (K : ChainBicomplex.{u,v} R) (n : ℤ)
    (z : (total K).X (n - 1)) :
    chainCoordinates K (n - 1) ((total K).d (n - 1) ((n - 1) - 1) z) =
      (-((K.X (-1)).d n (n - 1)) (chainCoordinates K n z).1 +
          (chainAugmentationComponent K (n - 1)) (chainCoordinates K n z).2,
        (total (unaugmented K)).d (n - 1) ((n - 1) - 1) (chainCoordinates K n z).2) := by
  apply Prod.ext
  · have hd' := chain_augmentation_projection_d_at K (n - 1) n (by omega)
    have hz := evaluate_equality hd' z
    simpa [chainCoordinates, sub_eq_add_neg, add_comm] using hz
  · exact evaluate_equality (chain_totalFrom_d K (n - 1)) z

/-- Full cochain differential in the manuscript's coordinates. -/
theorem cochain_coordinates_d (K : CochainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q)) (n : ℤ)
    (z : (total K).X n) :
    augmentedCoordinates K (n + 1) ((total K).d n (n + 1) z) =
      (-((K.X (-1)).d (n + 1) ((n + 1) + 1)) (augmentedCoordinates K n z).1,
        (cochainAugmentationComponent K (n + 1)) (augmentedCoordinates K n z).1 +
          (total (unaugmented K)).d n (n + 1) (augmentedCoordinates K n z).2) := by
  apply Prod.ext
  · simpa [augmentedCoordinates] using evaluate_equality (cochain_augmentation_projection_d K hs n) z
  · exact evaluate_equality (cochain_totalFrom_d K n) z


/-- Sign change on the retained coordinate after shifting the augmented total. -/
def chainConeEquiv (K : ChainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q))
    (f : total (unaugmented K) ⟶ K.X (-1)) (n : ℤ) :
    (chainShift (total K)).X n ≃ₗ[R] (cone f).X n :=
  (chainShiftTermEquiv (total K) n).trans
    ((coordinatesEquiv K hs (n - 1) n (by omega)).trans
      (((LinearEquiv.refl R _).prodCongr (LinearEquiv.neg R)).trans
        (chainConeTermEquiv f n).symm))

@[simp]
theorem chainConeEquiv_coordinates (K : ChainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q))
    (f : total (unaugmented K) ⟶ K.X (-1)) (n : ℤ)
    (z : (chainShift (total K)).X n) :
    chainConeTermEquiv f n (chainConeEquiv K hs f n z) =
      ((chainCoordinates K n (chainShiftTermEquiv (total K) n z)).1,
        -(chainCoordinates K n (chainShiftTermEquiv (total K) n z)).2) := by
  simp [chainConeEquiv, coordinatesEquiv, chainCoordinates]

def chainConeIso (K : ChainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q))
    (f : total (unaugmented K) ⟶ K.X (-1))
    (hf : ∀ n, f.f n = chainAugmentationComponent K n) :
    chainShift (total K) ≅ cone f :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (chainConeEquiv K hs f n).toModuleIso) (by
    intro n m hnm
    have hm : m = n - 1 := by change m + 1 = n at hnm; omega
    subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (chainConeTermEquiv f (n - 1)).injective
    change chainConeTermEquiv f (n - 1)
      ((cone f).d n (n - 1) (chainConeEquiv K hs f n z)) =
      chainConeTermEquiv f (n - 1)
        (chainConeEquiv K hs f (n - 1) ((chainShift (total K)).d n (n - 1) z))
    rw [P103.Ch10.ShiftsAndCones.chain_cone_differential,
      chainConeEquiv_coordinates, chainConeEquiv_coordinates,
      P103.Ch10.ShiftsAndCones.chain_shift_differential]
    simp only [map_neg]
    rw [chain_coordinates_d, hf]
    simp [add_comm])

/-- Reordering the two summands identifies the cochain augmented total with a cone. -/
def cochainConeEquiv (K : CochainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q))
    (f : K.X (-1) ⟶ total (unaugmented K)) (n : ℤ) :
    (total K).X n ≃ₗ[R] (cone f).X n :=
  (coordinatesEquiv K hs n (n + 1) (by omega)).trans
    ((LinearEquiv.prodComm R _ _).trans (cochainConeTermEquiv f n).symm)

@[simp]
theorem cochainConeEquiv_coordinates (K : CochainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q))
    (f : K.X (-1) ⟶ total (unaugmented K)) (n : ℤ) (z : (total K).X n) :
    cochainConeTermEquiv f n (cochainConeEquiv K hs f n z) =
      ((augmentedCoordinates K n z).2, (augmentedCoordinates K n z).1) := by
  simp [cochainConeEquiv, coordinatesEquiv, augmentedCoordinates]

def cochainConeIso (K : CochainBicomplex.{u,v} R)
    (hs : ∀ p q, p < -1 → Subsingleton ((K.X p).X q))
    (f : K.X (-1) ⟶ total (unaugmented K))
    (hf : ∀ n, f.f n = cochainAugmentationComponent K n) :
    total K ≅ cone f :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainConeEquiv K hs f n).toModuleIso) (by
    intro n m hnm
    have hm : m = n + 1 := hnm.symm
    subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (cochainConeTermEquiv f (n + 1)).injective
    change cochainConeTermEquiv f (n + 1)
      ((cone f).d n (n + 1) (cochainConeEquiv K hs f n z)) =
      cochainConeTermEquiv f (n + 1)
        (cochainConeEquiv K hs f (n + 1) ((total K).d n (n + 1) z))
    rw [P103.Ch10.ShiftsAndCones.cochain_cone_differential,
      cochainConeEquiv_coordinates, cochainConeEquiv_coordinates,
      cochain_coordinates_d K hs, hf]
    simp [add_comm])


/-- Shift preserves acyclicity via the adjacent homology equivalence. -/
theorem chainShift_acyclic (C : Chain.{u,v} R) (hC : Acyclic C) :
    Acyclic (chainShift C) := by
  intro n
  have := hC (n - 1)
  exact (chainShiftHomologyEquiv C n).injective.subsingleton

/-- Augmented horizontal chain rows assemble to the specified quasi-isomorphism. -/
theorem chain_rows_quasiIsomorphism (K : ChainBicomplex.{u,v} R) (b : ℤ)
    (hs : SupportedQuadrant K (-1) b) (hr : RowsAcyclic K) :
    ∃ f : total (unaugmented K) ⟶ K.X (-1), ChainRowResult K f := by
  obtain ⟨f, hf⟩ := chainAugmentation_exists K
  have hleft : ∀ p q, p < -1 → Subsingleton ((K.X p).X q) :=
    fun p q hp => hs p q (Or.inl hp)
  let e := chainConeIso K hleft f hf
  refine ⟨f, hf, ?_, ?_, e, ?_⟩
  · apply (P103.Ch10.ShiftsAndCones.chain_cone_criterion f).mpr
    apply P103.Ch10.TotalComplexAssembly.acyclic_of_iso e
    apply chainShift_acyclic
    exact P103.Ch10.TotalComplexAssembly.chain_acyclic_of_columns_or_rows K (-1) b hs (Or.inr hr)
  · intro n z
    simpa only [hf] using chain_coordinates_d K n z
  · intro n z
    exact chainConeEquiv_coordinates K hleft f n z

/-- Augmented horizontal cochain rows assemble to the specified quasi-isomorphism. -/
theorem cochain_rows_quasiIsomorphism (K : CochainBicomplex.{u,v} R) (b : ℤ)
    (hs : SupportedQuadrant K (-1) b) (hr : RowsAcyclic K) :
    ∃ f : K.X (-1) ⟶ total (unaugmented K), CochainRowResult K f := by
  obtain ⟨f, hf⟩ := cochainAugmentation_exists K
  have hleft : ∀ p q, p < -1 → Subsingleton ((K.X p).X q) :=
    fun p q hp => hs p q (Or.inl hp)
  let e := cochainConeIso K hleft f hf
  refine ⟨f, hf, ?_, ?_, e, ?_⟩
  · apply (P103.Ch10.ShiftsAndCones.cochain_cone_criterion f).mpr
    apply P103.Ch10.TotalComplexAssembly.acyclic_of_iso e
    exact P103.Ch10.TotalComplexAssembly.cochain_acyclic_of_columns_or_rows K (-1) b hs (Or.inr hr)
  · intro n z
    simpa only [hf] using cochain_coordinates_d K hleft n z
  · intro n z
    exact cochainConeEquiv_coordinates K hleft f n z

omit [ComplexShape.TensorSigns c] in
/-- Isomorphisms induce inverse maps on the explicit quotient homology. -/
theorem quasiIsomorphism_of_iso {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (e : C ≅ D) : QuasiIsomorphism e.hom := by
  intro n
  have hl := congrArg (fun f => homologyMap f n) e.hom_inv_id
  have hr := congrArg (fun f => homologyMap f n) e.inv_hom_id
  change P103.Ch10.Complexes.homologyMap (e.hom ≫ e.inv) n =
    P103.Ch10.Complexes.homologyMap (𝟙 C) n at hl
  change P103.Ch10.Complexes.homologyMap (e.inv ≫ e.hom) n =
    P103.Ch10.Complexes.homologyMap (𝟙 D) n at hr
  rw [P103.Ch10.Complexes.homologyMap_comp e.hom e.inv n,
    P103.Ch10.Complexes.homologyMap_id C n] at hl
  rw [P103.Ch10.Complexes.homologyMap_comp e.inv e.hom n,
    P103.Ch10.Complexes.homologyMap_id D n] at hr
  have hl' := DFunLike.congr_fun hl
  have hr' := DFunLike.congr_fun hr
  exact ⟨fun x y h => (hl' x).symm.trans ((congrArg (homologyMap e.inv n) h).trans (hl' y)),
    fun y => ⟨homologyMap e.inv n y, hr' y⟩⟩

omit [ComplexShape.TensorSigns c] in
theorem quasiIsomorphism_comp {C D E : HomologicalComplex (ModuleCat.{v} R) c}
    {f : C ⟶ D} {g : D ⟶ E} (hf : QuasiIsomorphism f) (hg : QuasiIsomorphism g) :
    QuasiIsomorphism (f ≫ g) := by
  intro n
  change Function.Bijective (P103.Ch10.Complexes.homologyMap (f ≫ g) n)
  rw [P103.Ch10.Complexes.homologyMap_comp f g n]
  exact (hg n).comp (hf n)

/-- The augmented chain column version, transported by the signed interchange. -/
theorem chain_columns_quasiIsomorphism (K : ChainBicomplex.{u,v} R) (a : ℤ)
    (hs : SupportedQuadrant K a (-1)) (hc : ColumnsAcyclic K) :
    ∃ g : total (unaugmented K.flip) ⟶ K.flip.X (-1),
      ChainRowResult K.flip g ∧
        QuasiIsomorphism ((signedInterchange (unaugmented K.flip)).hom ≫ g) := by
  have hs' : SupportedQuadrant K.flip (-1) a := fun p q hpq => hs q p hpq.symm
  obtain ⟨g, hg⟩ := chain_rows_quasiIsomorphism K.flip a hs' hc
  exact ⟨g, hg, quasiIsomorphism_comp
    (quasiIsomorphism_of_iso (signedInterchange (unaugmented K.flip))) hg.2.1⟩

/-- The augmented cochain column version, transported by the signed interchange. -/
theorem cochain_columns_quasiIsomorphism (K : CochainBicomplex.{u,v} R) (a : ℤ)
    (hs : SupportedQuadrant K a (-1)) (hc : ColumnsAcyclic K) :
    ∃ g : K.flip.X (-1) ⟶ total (unaugmented K.flip),
      CochainRowResult K.flip g ∧
        QuasiIsomorphism (g ≫ (signedInterchange (unaugmented K.flip)).inv) := by
  have hs' : SupportedQuadrant K.flip (-1) a := fun p q hpq => hs q p hpq.symm
  obtain ⟨g, hg⟩ := cochain_rows_quasiIsomorphism K.flip a hs' hc
  exact ⟨g, hg, quasiIsomorphism_comp hg.2.1
    (quasiIsomorphism_of_iso (signedInterchange (unaugmented K.flip)).symm)⟩

end
end P103.Ch10.AugmentedAssembly
