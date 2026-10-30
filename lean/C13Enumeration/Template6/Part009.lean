import C13Enumeration.Template6.Part010
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound159 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,5,9,11] table159, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,5,9,11] [5] table159 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound160

theorem bound158 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,5,7,9,11] table158, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,5,7,9,11] [7] table158 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound159

theorem bound157 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,4,5,7,9,11] table157, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,4,5,7,9,11] [4] table157 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound158

theorem bound156 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,4,5,7,9,11] table156, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,4,5,7,9,11] [1,11] table156 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound157
    · exact bound164

theorem bound155 : ∀ f ∈ assignSearch step finish [] [] table155, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound154 : ∀ f ∈ assignSearch step finish [11] [9] table154, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table154 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound155

theorem bound153 : ∀ f ∈ assignSearch step finish [9,11] [1,9] table153, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,9] [1] table153 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound154

theorem bound152 : ∀ f ∈ assignSearch step finish [8,9,11] [1,8,9] table152, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,8,9] [8] table152 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound153

theorem bound151 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,5,8,9] table151, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,5,8,9] [5] table151 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound152

theorem bound150 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,5,7,8,9] table150, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,5,7,8,9] [7] table150 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound151

theorem bound149 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,4,5,7,8,9] table149, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,4,5,7,8,9] [4] table149 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound150

theorem bound148 : ∀ f ∈ assignSearch step finish [] [] table148, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound147 : ∀ f ∈ assignSearch step finish [11] [9] table147, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table147 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound148

theorem bound146 : ∀ f ∈ assignSearch step finish [9,11] [9,11] table146, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [9,11] [11] table146 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound147

theorem bound145 : ∀ f ∈ assignSearch step finish [8,9,11] [8,9,11] table145, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [8,9,11] [8] table145 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound146

theorem bound144 : ∀ f ∈ assignSearch step finish [7,8,9,11] [5,8,9,11] table144, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [5,8,9,11] [5] table144 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound145
end C13.Enumeration.Template6
