import C13Enumeration.Template8.Part001
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound15 : ∀ f ∈ assignSearch step finish [7,9,10,11] [3,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [3,9,10,11] [3] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [3,6,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [3,6,9,10,11] [6] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound15

theorem bound13 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [3,5,6,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [3,5,6,9,10,11] [5] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [3,4,5,6,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [3,4,5,6,9,10,11] [4] table12 ?_ ?_
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

theorem bound7 : ∀ f ∈ assignSearch step finish [7,9,10,11] [7,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [7,9,10,11] [7] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [6,7,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [6,7,9,10,11] [6] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [5,6,7,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [5,6,7,9,10,11] [5] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [4,5,6,7,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [4,5,6,7,9,10,11] [4] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [3,4,5,6,7,9,10,11] [3,4,5,6,7,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,6,7,9,10,11] [3,4,5,6,7,9,10,11] [3,7] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound4
    · exact bound12

theorem bound2 : ∀ f ∈ assignSearch step finish [2,3,4,5,6,7,9,10,11] [2,3,4,5,6,7,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,6,7,9,10,11] [2,3,4,5,6,7,9,10,11] [2,3,6,7] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound3
    · exact bound20
    · exact bound37
    · exact bound54

theorem bound1 : ∀ f ∈ assignSearch step finish [1,2,3,4,5,6,7,9,10,11] [1,2,3,4,5,6,7,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,4,5,6,7,9,10,11] [1,2,3,4,5,6,7,9,10,11] [1] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [0,1,2,3,4,5,6,7,9,10,11] [0,1,2,3,4,5,6,7,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,2,3,4,5,6,7,9,10,11] [0,1,2,3,4,5,6,7,9,10,11] [0,1] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound71
end C13.Enumeration.Template8
