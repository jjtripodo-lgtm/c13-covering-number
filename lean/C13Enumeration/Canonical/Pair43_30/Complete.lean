import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair43_30
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link40 4) (link link27 5) Data43.matrix Data30.matrix
def finish := crossMapFinish link40 link27 hole 4 5
def table0 : Point → Point := anchorTable hole hole 5
def table1 : Point → Point := put table0 0 0
def table2 : Point → Point := put table1 10 8

theorem bound2 : ∀ f ∈ assignSearch step finish [6,7,1,2,3,5,8,9,11] [1,2,3,4,6,7,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,1,2,3,5,8,9,11] [1,2,3,4,6,7,9,10,11] [] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound1 : ∀ f ∈ assignSearch step finish [10,6,7,1,2,3,5,8,9,11] [1,2,3,4,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [6,7,1,2,3,5,8,9,11] [1,2,3,4,6,7,8,9,10,11] [8] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [0,10,6,7,1,2,3,5,8,9,11] [0,1,2,3,4,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [10,6,7,1,2,3,5,8,9,11] [0,1,2,3,4,6,7,8,9,10,11] [0] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound1

theorem complete (e : Equiv.Perm Point) (he : e hole = 5) (hc : e (4 : Point) = hole)
    (hs : transport e (link link40 4) = link link27 5) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link40 link27 hole 4 5 [0,10,6,7,1,2,3,5,8,9,11]
    (by decide +kernel) (by decide +kernel) Data43.matrix Data30.matrix
    Data43.matrix_checked Data30.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link40 link27 hole 4 hole 5 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link40 link27 hole 4 hole 5 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair43_30
