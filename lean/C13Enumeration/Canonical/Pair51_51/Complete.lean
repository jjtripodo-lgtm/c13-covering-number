import C13Enumeration.Canonical.Pair51_51.Part000
namespace C13.Enumeration.Canonical.Pair51_51
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem complete (e : Equiv.Perm Point) (he : e hole = 0) (hc : e (0 : Point) = hole)
    (hs : transport e (link link52 0) = link link52 0) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link52 link52 hole 0 0 [4,8,1,2,3,5,6,7,9,10,11]
    (by decide +kernel) (by decide +kernel) Data51.matrix Data51.matrix
    Data51.matrix_checked Data51.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link52 link52 hole 0 hole 0 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem valid1 : (((maps.drop 16).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) ++ ((maps.drop 16).take 16) := by rfl
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨valid0,valid1⟩
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link52 link52 hole 0 hole 0 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair51_51
