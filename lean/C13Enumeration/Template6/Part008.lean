import C13Enumeration.Template6.Part009
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound143 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [5,7,8,9,11] table143, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [5,7,8,9,11] [7] table143 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound144

theorem bound142 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [4,5,7,8,9,11] table142, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [4,5,7,8,9,11] [4] table142 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound143

theorem bound141 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,4,5,7,8,9,11] table141, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,4,5,7,8,9,11] [1,11] table141 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound142
    · exact bound149

theorem bound140 : ∀ f ∈ assignSearch step finish [] [] table140, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound139 : ∀ f ∈ assignSearch step finish [11] [9] table139, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table139 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound140

theorem bound138 : ∀ f ∈ assignSearch step finish [9,11] [2,9] table138, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,9] [2] table138 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound139

theorem bound137 : ∀ f ∈ assignSearch step finish [8,9,11] [2,9,11] table137, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,9,11] [11] table137 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound138

theorem bound136 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,5,9,11] table136, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,5,9,11] [5] table136 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound137

theorem bound135 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,4,5,9,11] table135, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,4,5,9,11] [4] table135 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound136

theorem bound134 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,4,5,7,9,11] table134, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,4,5,7,9,11] [7] table134 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound135

theorem bound133 : ∀ f ∈ assignSearch step finish [] [] table133, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound132 : ∀ f ∈ assignSearch step finish [11] [9] table132, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table132 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound133

theorem bound131 : ∀ f ∈ assignSearch step finish [9,11] [8,9] table131, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,9] [8] table131 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound132

theorem bound130 : ∀ f ∈ assignSearch step finish [8,9,11] [8,9,11] table130, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [8,9,11] [11] table130 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound131

theorem bound129 : ∀ f ∈ assignSearch step finish [7,8,9,11] [5,8,9,11] table129, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [5,8,9,11] [5] table129 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound130

theorem bound128 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [4,5,8,9,11] table128, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [4,5,8,9,11] [4] table128 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound129
end C13.Enumeration.Template6
