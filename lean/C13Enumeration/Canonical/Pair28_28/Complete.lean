import C13Enumeration.Canonical.Pair28_28.Part000
namespace C13.Enumeration.Canonical.Pair28_28
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link26 8) = link link26 8) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link26 link26 hole 8 8 [0,4,5,6,7,1,2,3,9,10,11]
    (by decide +kernel) (by decide +kernel) Data28.matrix Data28.matrix
    Data28.matrix_checked Data28.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link26 link26 hole 8 hole 8 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link26 link26 hole 8 hole 8 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair28_28
