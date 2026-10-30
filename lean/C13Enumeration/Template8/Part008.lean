import C13Enumeration.Template8.Data
namespace C13.Enumeration.Template8
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound140 : ∀ f ∈ assignSearch step finish [] [] table140, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound139 : ∀ f ∈ assignSearch step finish [11] [11] table139, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table139 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound140

theorem bound138 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table138, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table138 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound139

theorem bound137 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table137, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table137 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound138

theorem bound136 : ∀ f ∈ assignSearch step finish [7,9,10,11] [2,9,10,11] table136, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [2,9,10,11] [2] table136 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound137

theorem bound135 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [2,3,9,10,11] table135, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [2,3,9,10,11] [3] table135 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound136

theorem bound134 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [2,3,4,9,10,11] table134, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [2,3,4,9,10,11] [4] table134 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound135

theorem bound133 : ∀ f ∈ assignSearch step finish [4,5,6,7,9,10,11] [2,3,4,5,9,10,11] table133, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,9,10,11] [2,3,4,5,9,10,11] [5] table133 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound134

theorem bound132 : ∀ f ∈ assignSearch step finish [] [] table132, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound131 : ∀ f ∈ assignSearch step finish [11] [11] table131, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table131 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound132

theorem bound130 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table130, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table130 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound131

theorem bound129 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table129, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table129 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound130

theorem bound128 : ∀ f ∈ assignSearch step finish [7,9,10,11] [6,9,10,11] table128, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [6,9,10,11] [6] table128 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound129
end C13.Enumeration.Template8
