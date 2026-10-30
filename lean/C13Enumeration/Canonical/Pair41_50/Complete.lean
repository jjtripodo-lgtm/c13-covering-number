import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair41_50
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link38 5) (link link51 4) Data41.matrix Data50.matrix
def finish := crossMapFinish link38 link51 hole 5 4
def table0 : Point → Point := anchorTable hole hole 4
def table1 : Point → Point := put table0 7 6
def table2 : Point → Point := put table1 0 0
def table3 : Point → Point := put table1 0 10

theorem bound3 : ∀ f ∈ assignSearch step finish [8,1,2,3,4,6,9,10,11] [0,1,2,3,5,7,8,9,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,4,6,9,10,11] [0,1,2,3,5,7,8,9,11] [] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound2 : ∀ f ∈ assignSearch step finish [8,1,2,3,4,6,9,10,11] [1,2,3,5,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [1,2,3,4,6,9,10,11] [1,2,3,5,7,8,9,10,11] [] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound1 : ∀ f ∈ assignSearch step finish [0,8,1,2,3,4,6,9,10,11] [0,1,2,3,5,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [8,1,2,3,4,6,9,10,11] [0,1,2,3,5,7,8,9,10,11] [0,10] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound2
    · exact bound3

theorem bound0 : ∀ f ∈ assignSearch step finish [7,0,8,1,2,3,4,6,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,8,1,2,3,4,6,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] [6] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound1

theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (5 : Point) = hole)
    (hs : transport e (link link38 5) = link link51 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link38 link51 hole 5 4 [7,0,8,1,2,3,4,6,9,10,11]
    (by decide +kernel) (by decide +kernel) Data41.matrix Data50.matrix
    Data41.matrix_checked Data50.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link38 link51 hole 5 hole 4 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link38 link51 hole 5 hole 4 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair41_50
