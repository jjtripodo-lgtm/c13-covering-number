import C13Enumeration.Canonical.Pair61_61.Part005
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound159 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,10] table159, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,10] [10] table159 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound160

theorem bound158 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,6,10] table158, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,6,10] [6] table158 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound159

theorem bound157 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,6,8,10] table157, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,6,8,10] [8] table157 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound158

theorem bound156 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,6,8,10] table156, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,6,8,10] [3,10] table156 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound157
    · exact bound163

theorem bound155 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,6,7,8,10] table155, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,6,7,8,10] [7] table155 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound156

theorem bound154 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,6,7,8,10,11] table154, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,6,7,8,10,11] [11] table154 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound155

theorem bound153 : ∀ f ∈ assignSearch step finish [] [] table153, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound152 : ∀ f ∈ assignSearch step finish [11] [11] table152, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table152 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound153

theorem bound151 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table151, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [9] table151 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound152

theorem bound150 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,11] table150, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,11] [3] table150 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound151

theorem bound149 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,9,11] table149, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,9,11] [0] table149 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound150

theorem bound148 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,9,11] table148, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,9,11] [2] table148 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound149

theorem bound147 : ∀ f ∈ assignSearch step finish [] [] table147, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound146 : ∀ f ∈ assignSearch step finish [11] [0] table146, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table146 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound147

theorem bound145 : ∀ f ∈ assignSearch step finish [10,11] [0,2] table145, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,2] [2] table145 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound146

theorem bound144 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,7] table144, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,7] [7] table144 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound145

theorem bound143 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,7,11] table143, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,7,11] [11] table143 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound144

theorem bound142 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,7,9,11] table142, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,7,9,11] [9] table142 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound143

theorem bound141 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,7,9,11] table141, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,7,9,11] [3,7] table141 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound142
    · exact bound148

theorem bound140 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,7,9,10,11] table140, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,7,9,10,11] [10] table140 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound141

theorem bound139 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,6,7,9,10,11] table139, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,6,7,9,10,11] [6] table139 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound140

theorem bound138 : ∀ f ∈ assignSearch step finish [] [] table138, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound137 : ∀ f ∈ assignSearch step finish [11] [9] table137, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table137 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound138

theorem bound136 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table136, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [11] table136 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound137

theorem bound135 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,11] table135, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,11] [3] table135 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound136

theorem bound134 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,3,9,11] table134, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,3,9,11] [2] table134 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound135

theorem bound133 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,9,11] table133, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,9,11] [0] table133 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound134

theorem bound132 : ∀ f ∈ assignSearch step finish [] [] table132, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound131 : ∀ f ∈ assignSearch step finish [11] [2] table131, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table131 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound132

theorem bound130 : ∀ f ∈ assignSearch step finish [10,11] [0,2] table130, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,2] [0] table130 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound131

theorem bound129 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,7] table129, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,7] [7] table129 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound130

theorem bound128 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,7,9] table128, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,7,9] [9] table128 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound129
end C13.Enumeration.Canonical.Pair61_61
