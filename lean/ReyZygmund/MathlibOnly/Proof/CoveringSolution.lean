import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Geometry.PrescribedCover
import ReyZygmund.Geometry.ShiftedGridIco

/-! # Prescribed-scale covering in the independent formulation

The constructed alternating grids use the public corner formula and both
half-open conventions. The scalar placement puts the original closed cube
strictly between the covering cube's corners.
-/

namespace ReyZygmund.MathlibOnly

/-- Covering by the prescribed `3 ^ d` alternating shifted grids. -/
theorem prescribed_scale_covering : PrescribedScaleCovering := by
  intro d _hd
  refine ⟨Geometry.shiftedDyadicGrid d, Geometry.shiftedDyadicGrid_cubes d,
    Geometry.shiftedDyadicGrid_IcoGrid d, ?_⟩
  intro s hs Q hwidth
  exact Geometry.prescribed_dyadic_cover_Ico Q s hs hwidth

end ReyZygmund.MathlibOnly
