import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleBoundary
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleTriangulation

/-! The oriented external product on finite singular chains, assembled from
the canonical shuffle model, its tensor boundary identity, and the geometric
triangulation. All statements use the same affine cells and permutation signs.
The smooth restriction uses chart-local ambient extensions at every corner. -/
noncomputable section
namespace P202.ShuffleChains

/-- R-linear extension of the prescribed signed shuffle on a pair of bases. -/
def shuffleComponent : P202Specs.ShuffleChains.shuffleComponent_type :=
  @P202Specs.ShuffleModel.shuffleComponent

/-- The finite diagonal total map on the ordinary tensor complex. -/
def shuffle : P202Specs.ShuffleChains.shuffle_type :=
  @P202Specs.ShuffleModel.shuffle

theorem path_initial : P202Specs.ShuffleChains.path_initial_type :=
  @P202.ShuffleModel.path_initial

theorem path_terminal : P202Specs.ShuffleChains.path_terminal_type :=
  @P202.ShuffleModel.path_terminal

theorem path_step : P202Specs.ShuffleChains.path_step_type :=
  @P202.ShuffleModel.path_step

theorem parametrization_vertex : P202Specs.ShuffleChains.parametrization_vertex_type :=
  @P202.ShuffleModel.parametrization_vertex

theorem parametrization_weights : P202Specs.ShuffleChains.parametrization_weights_type :=
  @P202.ShuffleModel.parametrization_weights

theorem simplex_formula : P202Specs.ShuffleChains.simplex_formula_type :=
  @P202.ShuffleModel.simplex_formula

theorem component_formula : P202Specs.ShuffleChains.component_formula_type :=
  @P202.ShuffleModel.component_formula

theorem component_natural : P202Specs.ShuffleChains.component_natural_type :=
  @P202.ShuffleModel.component_natural

theorem naturality : P202Specs.ShuffleChains.naturality_type :=
  @P202.ShuffleModel.naturality

theorem component_zero_left : P202Specs.ShuffleChains.component_zero_left_type :=
  @P202.ShuffleModel.component_zero_left

theorem component_zero_right : P202Specs.ShuffleChains.component_zero_right_type :=
  @P202.ShuffleModel.component_zero_right

theorem ambientParametrization_smooth : P202Specs.ShuffleChains.ambientParametrization_smooth_type :=
  @P202.ShuffleModel.ambientParametrization_smooth

theorem ambientParametrization_weights : P202Specs.ShuffleChains.ambientParametrization_weights_type :=
  @P202.ShuffleModel.ambientParametrization_weights

theorem smooth_pullback : P202Specs.ShuffleChains.smooth_pullback_type :=
  @P202.ShuffleModel.smooth_pullback

theorem smooth_shuffle : P202Specs.ShuffleChains.smooth_shuffle_type :=
  @P202.ShuffleModel.smooth_shuffle

theorem chain_identity : P202Specs.ShuffleChains.chain_identity_type :=
  @P202.ShuffleBoundary.chain_identity

theorem triangulation : P202Specs.ShuffleChains.triangulation_type :=
  @P202.ShuffleTriangulation.triangulation

/-- The sign in the chain sum is the actual determinant sign. -/
theorem orientation : P202Specs.ShuffleChains.orientation_type := by
  intro p q s
  exact P202.ShuffleTriangulation.orientation s

theorem chain_map_realization : P202Specs.ShuffleChains.chain_map_realization_type :=
  @P202.ShuffleBoundary.chain_map_realization

theorem permutation_sign : P202Specs.ShuffleChains.permutation_sign_type :=
  @P202.ShuffleModel.permutation_sign

theorem face_ambient_extension : P202Specs.ShuffleChains.face_ambient_extension_type :=
  @P202.ShuffleModel.face_ambient_extension

theorem charts_pullback : P202Specs.ShuffleChains.charts_pullback_type :=
  @P202.ShuffleModel.charts_pullback

theorem charts_shuffle : P202Specs.ShuffleChains.charts_shuffle_type :=
  @P202.ShuffleModel.charts_shuffle

theorem smooth_face : P202Specs.ShuffleChains.smooth_face_type :=
  @P202.ShuffleModel.smooth_face

theorem smooth_boundary : P202Specs.ShuffleChains.smooth_boundary_type :=
  @P202.ShuffleModel.smooth_boundary

theorem smooth_simplex : P202Specs.ShuffleChains.smooth_simplex_type :=
  @P202.ShuffleModel.smooth_simplex

theorem smooth_restriction : P202Specs.ShuffleChains.smooth_restriction_type :=
  @P202.ShuffleModel.smooth_restriction

theorem smooth_total_restriction : P202Specs.ShuffleChains.smooth_total_restriction_type :=
  @P202.ShuffleModel.smooth_total_restriction

theorem standard_orientation : P202Specs.ShuffleChains.standard_orientation_type :=
  @P202.ShuffleTriangulation.standard_orientation

theorem standard_basis_orientation : P202Specs.ShuffleChains.standard_basis_orientation_type :=
  @P202.ShuffleTriangulation.standard_basis_orientation

theorem ordinary_boundary_zero : P202Specs.ShuffleChains.ordinary_boundary_zero_type :=
  @P202.ShuffleBoundary.ordinary_boundary_zero

end P202.ShuffleChains
