import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveSpaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open scoped BigOperators

universe u
noncomputable section

set_option Elab.async false


namespace LinearAlgebraicGroups.Specs.ProjectiveTwistChartModules

open ProjectiveSpaces (coordinateProjectiveSpace coordinateOpen coordinate_mem_degree_one grading)
open OrderedCechComparison (groundRingHomOpen)

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ChartIndex (ι : Type u) := {s : Finset ι // s.Nonempty}

variable {k ι : Type u} [Field k]

/-- The product defining the standard intersection indexed by the finite set `s`. -/
def coordinateProduct (k ι : Type u) [Field k] (s : Finset ι) : MvPolynomial ι k :=
  ∏ i ∈ s, MvPolynomial.X i

theorem coordinateProduct_degree (k ι : Type u) [Field k] (s : Finset ι) :
    coordinateProduct k ι s ∈ grading k ι s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [coordinateProduct] using (show (1 : MvPolynomial ι k) ∈ grading k ι 0 from
      SetLike.GradedOne.one_mem)
  | @insert j s hj ih =>
    rw [coordinateProduct, Finset.prod_insert hj, Finset.card_insert_of_notMem hj, add_comm]
    exact SetLike.mul_mem_graded (coordinate_mem_degree_one k ι j) ih

/-- The intersection of the standard coordinate opens indexed by a finite set. -/
abbrev chartOpen (k : Type u) [Field k] (s : Finset ι) :
    (coordinateProjectiveSpace k ι).left.Opens :=
  Proj.basicOpen (grading k ι) (coordinateProduct k ι s)

abbrev ChartRing (k : Type u) [Field k] (S : ChartIndex ι) :=
  Γ((coordinateProjectiveSpace k ι).left, chartOpen k S.val)

abbrev indexOf (S : (ChartIndex ι)ᵒᵈᵒᵖ) : ChartIndex ι := OrderDual.ofDual S.unop

abbrev indexSubset {S T : (ChartIndex ι)ᵒᵈᵒᵖ} (h : S ⟶ T) :
    (indexOf S).val ⊆ (indexOf T).val := leOfHom h.unop

theorem chartOpen_eq_inf (k ι : Type u) [Field k] (s : Finset ι) :
    chartOpen k s = s.inf (coordinateOpen k ι) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chartOpen, coordinateProduct, Proj.basicOpen_one]
  | @insert j s hj ih =>
    rw [Finset.inf_insert]
    change Proj.basicOpen (grading k ι) (coordinateProduct k ι (insert j s)) = _
    rw [show coordinateProduct k ι (insert j s) =
      MvPolynomial.X j * coordinateProduct k ι s by simp [coordinateProduct, hj],
      Proj.basicOpen_mul]
    change coordinateOpen k ι j ⊓ chartOpen k s = _
    rw [ih]

theorem chartOpen_anti {s t : Finset ι} (h : s ⊆ t) : chartOpen k t ≤ chartOpen k s :=
  by
    rw [chartOpen_eq_inf, chartOpen_eq_inf]
    exact Finset.le_inf fun i hi => Finset.inf_le (h hi)

/-- The diagram of actual regular sections on the nonempty chart intersections. -/
def chartRings (k ι : Type u) [Field k] : (ChartIndex ι)ᵒᵈᵒᵖ ⥤ CommRingCat.{u} where
  obj S := ChartRing k (indexOf S)
  map h := (coordinateProjectiveSpace k ι).left.presheaf.map
    (homOfLE (chartOpen_anti (indexSubset h))).op
  map_id S := by
    exact ((coordinateProjectiveSpace k ι).left.presheaf.map_id _)
  map_comp f g := by
    rw [← Functor.map_comp]
    rfl

abbrev insertIndex [DecidableEq ι] (i : ι) (S : ChartIndex ι) : ChartIndex ι :=
  ⟨insert i S.val, Finset.insert_nonempty _ _⟩

abbrev insertHom [DecidableEq ι] (i : ι) (S : ChartIndex ι) :
    (op (OrderDual.toDual S) : (ChartIndex ι)ᵒᵈᵒᵖ) ⟶ op (OrderDual.toDual (insertIndex i S)) :=
  (homOfLE (Finset.subset_insert i S.val)).op

abbrev LaurentRing (k ι : Type u) [Field k] := AddMonoidAlgebra k (ι → ℤ)

/-- Integer exponents of the image of a polynomial monomial. -/
def polynomialExponent : (ι →₀ ℕ) →+ (ι → ℤ) where
  toFun a i := a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

/-- The polynomial algebra embeds in the algebra with integer exponents. -/
def polynomialToLaurent : MvPolynomial ι k →ₐ[k] LaurentRing k ι :=
  AddMonoidAlgebra.mapDomainAlgHom k k polynomialExponent

def coordinateExponent [DecidableEq ι] (i : ι) : ι → ℤ := fun j => if j = i then 1 else 0

def coordinateProductExponent [DecidableEq ι] (s : Finset ι) : ι → ℤ :=
  fun i => if i ∈ s then 1 else 0

def ratioExponent [DecidableEq ι] (i j : ι) : ι → ℤ :=
  coordinateExponent i - coordinateExponent j

/-- Monomials of the specified total degree, with poles only at inverted coordinates. -/
def allowed [Fintype ι] (d : ℤ) (S : Set ι) : Set (ι → ℤ) :=
  {a | (∑ i, a i) = d ∧ ∀ i ∉ S, 0 ≤ a i}

abbrev LaurentPart [Fintype ι] (k : Type u) [Field k] (d : ℤ) (S : Set ι) :
    Submodule k (LaurentRing k ι) :=
  AddMonoidAlgebra.supported k k (allowed d S)

/-- The structural map from the field on a chart intersection. -/
abbrev chartGround (k : Type u) [Field k] (S : ChartIndex ι) : k →+* ChartRing k S :=
  groundRingHomOpen (coordinateProjectiveSpace k ι) (chartOpen k S.val)

variable [Fintype ι] [DecidableEq ι]

/-- The homogeneous fraction `p / (∏ i ∈ S, X i)^n` as a regular section. -/
def chartFraction (S : ChartIndex ι) (n : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ grading k ι (n • S.val.card)) : ChartRing k S :=
  (Proj.basicOpenIsoAway (grading k ι) _ (coordinateProduct_degree k ι S.val)
    (Finset.card_pos.mpr S.property)).hom
      (Away.mk _ (coordinateProduct_degree k ι S.val) n p hp)

/-- The geometric chart algebra, expressed inside the common Laurent ring. -/
structure ChartGeometry (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] where
  affine (S : ChartIndex ι) : IsAffineOpen (chartOpen k S.val)
  embed (S : ChartIndex ι) : ChartRing k S →+* LaurentRing k ι
  injective (S : ChartIndex ι) : Function.Injective (embed S)
  range (S : ChartIndex ι) (x : LaurentRing k ι) :
    x ∈ (embed S).range ↔ x ∈ LaurentPart k 0 (S.val : Set ι)
  fraction_coeff (S : ChartIndex ι) (n : ℕ) (p : MvPolynomial ι k)
      (hp : p ∈ grading k ι (n • S.val.card)) :
    embed S (chartFraction S n p hp) =
      polynomialToLaurent p * AddMonoidAlgebra.single (-(n • coordinateProductExponent S.val)) 1
  constants (S : ChartIndex ι) (a : k) :
    embed S (chartGround k S a) = AddMonoidAlgebra.single 0 a
  restrict_embed {S T : (ChartIndex ι)ᵒᵈᵒᵖ} (h : S ⟶ T) (r : (chartRings k ι).obj S) :
    embed (indexOf T) ((chartRings k ι).map h r) = embed (indexOf S) r
  ratio (S : ChartIndex ι) (i j : ι) (hj : j ∈ S.val) : ChartRing k S
  ratio_coeff (S : ChartIndex ι) (i j : ι) (hj : j ∈ S.val) :
    embed S (ratio S i j hj) = AddMonoidAlgebra.single (ratioExponent i j) 1
  ratio_self (S : ChartIndex ι) (j : ι) (hj : j ∈ S.val) : ratio S j j hj = 1
  ratio_mul (S : ChartIndex ι) (i j l : ι) (hj : j ∈ S.val) (hl : l ∈ S.val) :
    ratio S i j hj * ratio S j l hl = ratio S i l hl
  ratio_restrict {S T : (ChartIndex ι)ᵒᵈᵒᵖ} (h : S ⟶ T) (i j : ι) (hj : j ∈ (indexOf S).val) :
    (chartRings k ι).map h (ratio (indexOf S) i j hj) =
      ratio (indexOf T) i j (indexSubset h hj)
  insert_open (S : ChartIndex ι) (i j : ι) (hj : j ∈ S.val) :
    chartOpen k (insertIndex i S).val =
      (coordinateProjectiveSpace k ι).left.basicOpen (ratio S i j hj)
  ring_localization (S : ChartIndex ι) (i j : ι) (hj : j ∈ S.val) :
    @IsLocalization.Away _ _ (ratio S i j hj) (ChartRing k (insertIndex i S)) _
      ((chartRings k ι).map (insertHom i S)).hom.toAlgebra

/-- Existence over every field of the actual geometric chart ring diagram. -/
def ChartGeometryExists : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [LinearOrder ι] [Nonempty ι],
    Nonempty (ChartGeometry k ι)


/-- The ring diagram viewed as a presheaf of rings. -/
abbrev chartRingPresheaf (k ι : Type u) [Field k] :=
  chartRings k ι ⋙ forget₂ CommRingCat RingCat

/-- The ratio of two inverted coordinates is a unit. -/
def ChartGeometry.ratioUnit (G : ChartGeometry k ι) (S : ChartIndex ι)
    (i j : ι) (hi : i ∈ S.val) (hj : j ∈ S.val) : (ChartRing k S)ˣ where
  val := G.ratio S i j hj
  inv := G.ratio S j i hi
  val_inv := (G.ratio_mul S i j i hj hi).trans (G.ratio_self S i hi)
  inv_val := (G.ratio_mul S j i j hi hj).trans (G.ratio_self S j hj)

def powerExponent (d : ℤ) (i : ι) : ι → ℤ := d • coordinateExponent i

abbrev chartObject (S : ChartIndex ι) : (ChartIndex ι)ᵒᵈᵒᵖ := op (OrderDual.toDual S)

abbrev chartModuleAt (M : PresheafOfModules.{u} (chartRingPresheaf k ι))
    (S : ChartIndex ι) : ModuleCat.{u} (ChartRing k S) := M.obj (chartObject S)

set_option backward.isDefEq.respectTransparency false in
/-- The actual module restriction to an adjoining chart is localization at the given element. -/
def localizesAt (M : PresheafOfModules.{u} (chartRingPresheaf k ι))
    (S : ChartIndex ι) (i : ι) (r : ChartRing k S) : Prop :=
  let T := M.obj (chartObject (insertIndex i S))
  let N := (ModuleCat.restrictScalars ((chartRingPresheaf k ι).map (insertHom i S)).hom).obj T
  @IsLocalizedModule (ChartRing k S) _ (M.obj (chartObject S)) N _ _
    (M.obj (chartObject S)).isModule N.isModule (Submonoid.powers r) (M.map (insertHom i S)).hom

set_option backward.isDefEq.respectTransparency false in
/-- The degree-d twist, with its action, transitions and localizations on the geometric charts. -/
structure TwistDiagram (G : ChartGeometry k ι) (d : ℤ) where
  modules : PresheafOfModules.{u} (chartRingPresheaf k ι)
  coefficients (S : ChartIndex ι) :
    chartModuleAt modules S ≃+ LaurentPart k d (S.val : Set ι)
  smul_coeff (S : ChartIndex ι) (r : ChartRing k S)
      (x : chartModuleAt modules S) :
    ((coefficients S (r • x) : LaurentPart k d (S.val : Set ι)) : LaurentRing k ι) =
      G.embed S r * (coefficients S x : LaurentRing k ι)
  ground_coeff (S : ChartIndex ι) (a : k)
      (x : chartModuleAt modules S) :
    ((coefficients S (chartGround k S a • x) : LaurentPart k d (S.val : Set ι)) :
      LaurentRing k ι) = a • (coefficients S x : LaurentRing k ι)
  restrict_coeff {S T : (ChartIndex ι)ᵒᵈᵒᵖ} (h : S ⟶ T) (x : modules.obj S) :
    (coefficients (indexOf T) (modules.map h x) : LaurentRing k ι) =
      (coefficients (indexOf S) x : LaurentRing k ι)
  basis (S : ChartIndex ι) (i : ι) (hi : i ∈ S.val) :
    ChartRing k S ≃ₗ[ChartRing k S] chartModuleAt modules S
  basis_coeff (S : ChartIndex ι) (i : ι) (hi : i ∈ S.val) (r : ChartRing k S) :
    (coefficients S (basis S i hi r) : LaurentRing k ι) =
      G.embed S r * AddMonoidAlgebra.single (powerExponent d i) 1
  basis_transition (S : ChartIndex ι) (i j : ι) (hi : i ∈ S.val) (hj : j ∈ S.val) :
    basis S i hi 1 =
      ((G.ratioUnit S i j hi hj ^ d : (ChartRing k S)ˣ) : ChartRing k S) • basis S j hj 1
  localized (S : ChartIndex ι) (i j : ι) (hj : j ∈ S.val) :
    localizesAt modules S i (G.ratio S i j hj)

def TwistDiagramsExist : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] (G : ChartGeometry k ι) (d : ℤ),
    Nonempty (TwistDiagram G d)

/-- The underlying Laurent module diagram, extended to allow an empty inverted set. -/
abbrev laurentPresheaf (k : Type u) [Field k] (d : ℤ) :
    (Set ι)ᵒᵈᵒᵖ ⥤ ModuleCat.{u} k where
  obj S := ModuleCat.of k (LaurentPart k d (OrderDual.ofDual S.unop))
  map {S T} h := by
    have hST : OrderDual.ofDual S.unop ⊆ OrderDual.ofDual T.unop := leOfHom h.unop
    exact ModuleCat.ofHom (Submodule.inclusion
      (AddMonoidAlgebra.supported_mono (fun _ ha =>
        ⟨ha.1, fun i hi => ha.2 i (fun hi' => hi (hST hi'))⟩)))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)


/-- Inclusion of the nonempty finite chart sets in the lattice of sets used by Čech cochains. -/
abbrev chartSets (ι : Type u) : (ChartIndex ι)ᵒᵈᵒᵖ ⥤ (Set ι)ᵒᵈᵒᵖ where
  obj S := op (OrderDual.toDual ((indexOf S).val : Set ι))
  map {S T} h := (homOfLE (X := (Set ι)ᵒᵈ)
    (x := OrderDual.toDual ((indexOf T).val : Set ι))
    (y := OrderDual.toDual ((indexOf S).val : Set ι))
    (fun {_} hi => indexSubset h hi)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the chart modules along the structural field maps. -/
def groundDiagram (M : PresheafOfModules.{u} (chartRingPresheaf k ι)) :
    (ChartIndex ι)ᵒᵈᵒᵖ ⥤ ModuleCat.{u} k where
  obj S := (ModuleCat.restrictScalars (chartGround k (indexOf S))).obj (M.obj S)
  map {S T} h := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (chartGround k (indexOf S))).obj (M.obj S))
    (Y := (ModuleCat.restrictScalars (chartGround k (indexOf T))).obj (M.obj T))
    { toFun x := M.map h x
      map_add' := map_add (M.map h).hom
      map_smul' a x := by
        have hg := Specs.OrderedCechComparison.localScalars_comp (X := coordinateProjectiveSpace k ι)
          (homOfLE (chartOpen_anti (indexSubset h)))
        have ha : chartGround k (indexOf T) a =
            (chartRingPresheaf k ι).map h (chartGround k (indexOf S) a) :=
          congrArg (fun f => f a) hg
        let z : M.obj T := M.map h x
        let : Module (ChartRing k (indexOf T)) (M.obj T) := (M.obj T).isModule
        change M.map h (chartGround k (indexOf S) a • x) = chartGround k (indexOf T) a • z
        exact (M.map_smul h _ x).trans
          (congrArg (fun r : ChartRing k (indexOf T) => r • z) ha.symm) }
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.map (𝟙 S) x = x
    rw [M.map_id]
    rfl
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext (by
    intro x
    exact M.map_comp_apply f g x))

set_option backward.isDefEq.respectTransparency false in
/-- The field-linear coefficients and the restriction maps agree with the Laurent diagram. -/
def GroundComparison : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι] (G : ChartGeometry k ι)
    (d : ℤ) (M : TwistDiagram G d),
    ∃ e : groundDiagram M.modules ≅ chartSets ι ⋙ laurentPresheaf k d,
      ∀ (S : (ChartIndex ι)ᵒᵈᵒᵖ) (x : M.modules.obj S),
        e.hom.app S x = M.coefficients (indexOf S) x

/-- Exponents of fixed total degree, and the subset of coordinate indices with poles. -/
abbrev Exponents (ι : Type u) [Fintype ι] (d : ℤ) := {a : ι → ℤ // (∑ j, a j) = d}

def negativeSupport {d : ℤ} (a : Exponents ι d) : Finset ι :=
  Finset.univ.filter fun j => a.val j < 0

abbrev monomials (k : Type u) [Field k] (d : ℤ) (S : Set ι) :=
  Finsupp.supported k k {a : Exponents ι d | (negativeSupport a : Set ι) ⊆ S}

abbrev monomialPresheaf (k : Type u) [Field k] (d : ℤ) :
    (Set ι)ᵒᵈᵒᵖ ⥤ ModuleCat.{u} k where
  obj S := ModuleCat.of k (monomials k d (OrderDual.ofDual S.unop))
  map {S T} h := by
    have hST : OrderDual.ofDual S.unop ⊆ OrderDual.ofDual T.unop := leOfHom h.unop
    exact ModuleCat.ofHom (Submodule.inclusion
      (Finsupp.supported_mono fun _ ha => Set.Subset.trans ha hST))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

def singletonCoordinates (i : ι) : (Set ι)ᵒᵈ := OrderDual.toDual {i}

open OrderedCechComparison (cechComplex tupleOpen)

variable [LinearOrder ι]


/-- Every tuple in the ordered Čech complex determines a nonempty set of charts. -/
def tupleIndex {n : ℕ} (e : Fin (n + 1) ↪o ι) : ChartIndex ι :=
  ⟨Finset.univ.map e.toEmbedding, ⟨e 0, Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩⟩

omit [Fintype ι] [DecidableEq ι] in
theorem tupleIndex_coe {n : ℕ} (e : Fin (n + 1) ↪o ι) :
    OrderDual.ofDual (tupleOpen singletonCoordinates e) = ((tupleIndex e).val : Set ι) := by
  ext i
  change i ∈ (⋃ j, ({e j} : Set ι)) ↔ _
  simp [tupleIndex, eq_comm]

omit [Fintype ι] [DecidableEq ι] in
theorem tupleIndex_open (k : Type u) [Field k] {n : ℕ} (e : Fin (n + 1) ↪o ι) :
    chartOpen k (tupleIndex e).val = tupleOpen (coordinateOpen k ι) e := by
  rw [chartOpen_eq_inf]
  change (Finset.univ.map e.toEmbedding).inf (coordinateOpen k ι) = _
  rw [Finset.inf_map, Finset.inf_univ_eq_iInf]
  rfl

abbrev laurentCech (k : Type u) [Field k] (d : ℤ) :=
  cechComplex singletonCoordinates (laurentPresheaf (ι := ι) k d)

abbrev monomialCech (k : Type u) [Field k] (d : ℤ) :=
  cechComplex singletonCoordinates (monomialPresheaf (ι := ι) k d)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison sends each cochain to the same coefficients indexed by fixed-degree exponents. -/
structure OrderedLaurentComparison (k ι : Type u) [Field k] [Fintype ι] [LinearOrder ι] (d : ℤ) where
  iso : laurentCech (ι := ι) k d ≅ monomialCech (ι := ι) k d
  coeff (n : ℕ) (x : (laurentCech (ι := ι) k d).X n) (e : Fin (n + 1) ↪o ι)
      (a : Exponents ι d) :
    ((iso.hom.f n x e : monomials k d (OrderDual.ofDual (tupleOpen singletonCoordinates e))).val) a =
      (x e : LaurentRing k ι).coeff a.val

def OrderedLaurentComparisonExists : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [LinearOrder ι] (d : ℤ),
    Nonempty (OrderedLaurentComparison k ι d)

end LinearAlgebraicGroups.Specs.ProjectiveTwistChartModules
