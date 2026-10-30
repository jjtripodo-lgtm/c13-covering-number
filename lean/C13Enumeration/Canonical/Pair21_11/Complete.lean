import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair21_11
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := []
def step := starStep (link link16 0) (link link07 0) Data21.matrix Data11.matrix
def finish := crossMapFinish link16 link07 hole 0 0
def table0 : Point → Point := anchorTable hole hole 0
def table1 : Point → Point := put table0 1 3
def table2 : Point → Point := put table1 4 4
def table3 : Point → Point := put table1 4 5

theorem bound3 : ∀ f ∈ assignSearch step finish [5,2,3,6,7,8,9,10,11] [1,2,4,6,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [2,3,6,7,8,9,10,11] [1,2,4,6,7,8,9,10,11] [] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound2 : ∀ f ∈ assignSearch step finish [5,2,3,6,7,8,9,10,11] [1,2,5,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [2,3,6,7,8,9,10,11] [1,2,5,6,7,8,9,10,11] [] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound1 : ∀ f ∈ assignSearch step finish [4,5,2,3,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,2,3,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] [4,5] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound2
    · exact bound3

theorem bound0 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] [3] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound1

theorem complete (e : Equiv.Perm Point) (he : e hole = 0) (hc : e (0 : Point) = hole)
    (hs : transport e (link link16 0) = link link07 0) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link16 link07 hole 0 0 [1,4,5,2,3,6,7,8,9,10,11]
    (by decide +kernel) (by decide +kernel) Data21.matrix Data11.matrix
    Data21.matrix_checked Data11.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link16 link07 hole 0 hole 0 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link16 link07 hole 0 hole 0 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair21_11
