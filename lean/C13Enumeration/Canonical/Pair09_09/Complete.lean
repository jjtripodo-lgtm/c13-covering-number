import C13Enumeration.Canonical.Pair09_09.Part000
namespace C13.Enumeration.Canonical.Pair09_09
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem complete (e : Equiv.Perm Point) (he : e hole = 2) (hc : e (2 : Point) = hole)
    (hs : transport e (link link05 2) = link link05 2) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link05 link05 hole 2 2 [0,1,6,7,3,4,5,8,9,10,11]
    (by decide +kernel) (by decide +kernel) Data09.matrix Data09.matrix
    Data09.matrix_checked Data09.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link05 link05 hole 2 hole 2 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link05 link05 hole 2 hole 2 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair09_09
