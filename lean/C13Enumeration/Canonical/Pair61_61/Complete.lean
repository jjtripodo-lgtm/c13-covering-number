import C13Enumeration.Canonical.Pair61_61.Part000
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (4 : Point) = hole)
    (hs : transport e (link figure6 4) = link figure6 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete figure6 figure6 hole 4 4 [5,0,1,2,3,6,7,8,9,10,11]
    (by decide +kernel) (by decide +kernel) Data61.matrix Data61.matrix
    Data61.matrix_checked Data61.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap figure6 figure6 hole 4 hole 4 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem valid1 : (((maps.drop 16).take 16).all validMap) = true := by decide +kernel
theorem valid2 : (((maps.drop 32).take 16).all validMap) = true := by decide +kernel
theorem valid3 : (((maps.drop 48).take 16).all validMap) = true := by decide +kernel
theorem valid4 : (((maps.drop 64).take 16).all validMap) = true := by decide +kernel
theorem valid5 : (((maps.drop 80).take 16).all validMap) = true := by decide +kernel
theorem valid6 : (((maps.drop 96).take 16).all validMap) = true := by decide +kernel
theorem valid7 : (((maps.drop 112).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) ++ ((maps.drop 16).take 16) ++ ((maps.drop 32).take 16) ++ ((maps.drop 48).take 16) ++ ((maps.drop 64).take 16) ++ ((maps.drop 80).take 16) ++ ((maps.drop 96).take 16) ++ ((maps.drop 112).take 16) := by rfl
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨valid0,valid1,valid2,valid3,valid4,valid5,valid6,valid7⟩
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap figure6 figure6 hole 4 hole 4 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair61_61
