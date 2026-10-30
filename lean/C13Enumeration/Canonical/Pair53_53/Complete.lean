import C13Enumeration.Canonical.Pair53_53.Part000
namespace C13.Enumeration.Canonical.Pair53_53
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link54 8) = link link54 8) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link54 link54 hole 8 8 [9,10,11,0,1,4,5,2,3,6,7]
    (by decide +kernel) (by decide +kernel) Data53.matrix Data53.matrix
    Data53.matrix_checked Data53.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link54 link54 hole 8 hole 8 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link54 link54 hole 8 hole 8 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair53_53
