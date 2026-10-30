import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair00_00
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := [![12,1,2,3,4,5,6,7,8,9,10,11,0],![12,1,3,2,4,5,7,6,8,9,11,10,0],![12,1,3,2,5,4,6,7,9,8,10,11,0],![12,1,2,3,5,4,7,6,9,8,11,10,0]]
def step := starStep (link link01 0) (link link01 0) Data00.matrix Data00.matrix
def finish := crossMapFinish link01 link01 hole 0 0
def table0 : Point → Point := anchorTable hole hole 0
def table1 : Point → Point := put table0 2 2
def table2 : Point → Point := put table1 3 3
def table3 : Point → Point := put table2 1 1
def table4 : Point → Point := put table3 4 4
def table5 : Point → Point := put table4 5 5
def table6 : Point → Point := put table5 6 6
def table7 : Point → Point := put table6 7 7
def table8 : Point → Point := put table7 8 8
def table9 : Point → Point := put table8 9 9
def table10 : Point → Point := put table9 10 10
def table11 : Point → Point := put table10 11 11
def table12 : Point → Point := put table3 4 5
def table13 : Point → Point := put table12 5 4
def table14 : Point → Point := put table13 6 7
def table15 : Point → Point := put table14 7 6
def table16 : Point → Point := put table15 8 9
def table17 : Point → Point := put table16 9 8
def table18 : Point → Point := put table17 10 11
def table19 : Point → Point := put table18 11 10
def table20 : Point → Point := put table0 2 3
def table21 : Point → Point := put table20 3 2
def table22 : Point → Point := put table21 1 1
def table23 : Point → Point := put table22 4 4
def table24 : Point → Point := put table23 5 5
def table25 : Point → Point := put table24 6 7
def table26 : Point → Point := put table25 7 6
def table27 : Point → Point := put table26 8 8
def table28 : Point → Point := put table27 9 9
def table29 : Point → Point := put table28 10 11
def table30 : Point → Point := put table29 11 10
def table31 : Point → Point := put table22 4 5
def table32 : Point → Point := put table31 5 4
def table33 : Point → Point := put table32 6 6
def table34 : Point → Point := put table33 7 7
def table35 : Point → Point := put table34 8 9
def table36 : Point → Point := put table35 9 8
def table37 : Point → Point := put table36 10 10
def table38 : Point → Point := put table37 11 11

theorem bound38 : ∀ f ∈ assignSearch step finish [] [] table38, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound37 : ∀ f ∈ assignSearch step finish [11] [11] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound38

theorem bound36 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound37

theorem bound35 : ∀ f ∈ assignSearch step finish [9,10,11] [8,10,11] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [8,10,11] [8] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound36

theorem bound34 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [9] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound35

theorem bound33 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [7,8,9,10,11] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [7,8,9,10,11] [7] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [6] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound33

theorem bound31 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [4,6,7,8,9,10,11] table31, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [4,6,7,8,9,10,11] [4] table31 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound32

theorem bound30 : ∀ f ∈ assignSearch step finish [] [] table30, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound29 : ∀ f ∈ assignSearch step finish [11] [10] table29, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table29 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound30

theorem bound28 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table28, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table28 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound29

theorem bound27 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table27, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound28

theorem bound26 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table26, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [8] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound27

theorem bound25 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,8,9,10,11] [6] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound26

theorem bound24 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [7] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound25

theorem bound23 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [5,6,7,8,9,10,11] table23, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [5,6,7,8,9,10,11] [5] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound24

theorem bound22 : ∀ f ∈ assignSearch step finish [4,5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] [4,5] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound23
    · exact bound31

theorem bound21 : ∀ f ∈ assignSearch step finish [1,4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] [1] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound22

theorem bound20 : ∀ f ∈ assignSearch step finish [3,1,4,5,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [1,4,5,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] [2] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound21

theorem bound19 : ∀ f ∈ assignSearch step finish [] [] table19, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound18 : ∀ f ∈ assignSearch step finish [11] [10] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [9,10,11] [8,10,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [8,10,11] [8] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [9] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,8,9,10,11] [6] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound15

theorem bound13 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [7] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [4,6,7,8,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [4,6,7,8,9,10,11] [4] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ f ∈ assignSearch step finish [] [] table11, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound10 : ∀ f ∈ assignSearch step finish [11] [11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [8] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [7,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [7,8,9,10,11] [7] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [6] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [5,6,7,8,9,10,11] [5,6,7,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,8,9,10,11] [5,6,7,8,9,10,11] [5] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [4,5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] [4,5] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound4
    · exact bound12

theorem bound2 : ∀ f ∈ assignSearch step finish [1,4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] [1] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound3

theorem bound1 : ∀ f ∈ assignSearch step finish [3,1,4,5,6,7,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [1,4,5,6,7,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] [3] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [2,3,1,4,5,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,1,4,5,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] [2,3] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound20

theorem complete (e : Equiv.Perm Point) (he : e hole = 0) (hc : e (0 : Point) = hole)
    (hs : transport e (link link01 0) = link link01 0) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link01 link01 hole 0 0 [2,3,1,4,5,6,7,8,9,10,11]
    (by decide +kernel) (by decide +kernel) Data00.matrix Data00.matrix
    Data00.matrix_checked Data00.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link01 link01 hole 0 hole 0 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link01 link01 hole 0 hole 0 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair00_00
