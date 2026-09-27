import ReyZygmund.Geometry.Flatten

open MeasureTheory
open scoped BigOperators

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def flattenCoordinatesValueContract : Prop :=
  ∀ {m : ℕ} (d : Fin m → ℕ) (x : ProductPoint d) (i : Fin m) (k : Fin (d i)),
    flattenCoordinates d x (finSigmaFinEquiv ⟨i, k⟩) = x i k

def volumePreservingUncurryContract : Prop :=
  ∀ {m : ℕ} (d : Fin m → ℕ),
    MeasurePreserving
      (MeasurableEquiv.piCurry (fun (i : Fin m) (_ : Fin (d i)) => ℝ)).symm
      volume volume

def volumePreservingFlattenContract : Prop :=
  ∀ {m : ℕ} (d : Fin m → ℕ),
    MeasurePreserving (flattenCoordinates d) volume volume

end ReyZygmundVerification
