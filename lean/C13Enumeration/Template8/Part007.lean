import C13Enumeration.Template8.Part008
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound127 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [3,6,9,10,11] table127, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [3,6,9,10,11] [3] table127 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound128

theorem bound126 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [3,4,6,9,10,11] table126, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [3,4,6,9,10,11] [4] table126 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound127

theorem bound125 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [3,4,5,6,9,10,11] table125, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [3,4,5,6,9,10,11] [5] table125 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound126

theorem bound124 : ∀ f ∈ assignSearch step finish [3,4,5,6,7,9,10,11] [2,3,4,5,6,9,10,11] table124, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,6,7,9,10,11] [2,3,4,5,6,9,10,11] [2,6] table124 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound125
    · exact bound133

theorem bound123 : ∀ f ∈ assignSearch step finish [] [] table123, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound122 : ∀ f ∈ assignSearch step finish [11] [10] table122, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table122 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound123

theorem bound121 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table121, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table121 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound122

theorem bound120 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table120, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table120 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound121

theorem bound119 : ∀ f ∈ assignSearch step finish [7,9,10,11] [3,9,10,11] table119, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [3,9,10,11] [3] table119 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound120

theorem bound118 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [2,3,9,10,11] table118, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [2,3,9,10,11] [2] table118 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound119

theorem bound117 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [2,3,4,9,10,11] table117, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [2,3,4,9,10,11] [4] table117 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound118

theorem bound116 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [2,3,4,5,9,10,11] table116, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [2,3,4,5,9,10,11] [5] table116 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound117

theorem bound115 : ∀ f ∈ assignSearch step finish [] [] table115, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound114 : ∀ f ∈ assignSearch step finish [11] [10] table114, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table114 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound115

theorem bound113 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table113, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table113 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound114

theorem bound112 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table112, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table112 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound113
end C13.Enumeration.Template8
