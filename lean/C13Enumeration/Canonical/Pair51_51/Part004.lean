import C13Enumeration.Canonical.Pair51_51.Part005
namespace C13.Enumeration.Canonical.Pair51_51
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound159 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,7,9,10] table159, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,7,9,10] [9] table159 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound160

theorem bound158 : ∀ f ∈ assignSearch step finish [] [] table158, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound157 : ∀ f ∈ assignSearch step finish [11] [10] table157, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table157 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound158

theorem bound156 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table156, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [9] table156 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound157

theorem bound155 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table155, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table155 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound156

theorem bound154 : ∀ f ∈ assignSearch step finish [7,9,10,11] [6,9,10,11] table154, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [6,9,10,11] [6] table154 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound155

theorem bound153 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,9,10,11] table153, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,9,10,11] [5] table153 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound154

theorem bound152 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [5,6,7,9,10,11] table152, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [5,6,7,9,10,11] [7,11] table152 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound153
    · exact bound159

theorem bound151 : ∀ f ∈ assignSearch step finish [3,5,6,7,9,10,11] [2,5,6,7,9,10,11] table151, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,9,10,11] [2,5,6,7,9,10,11] [2] table151 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound152

theorem bound150 : ∀ f ∈ assignSearch step finish [2,3,5,6,7,9,10,11] [1,2,5,6,7,9,10,11] table150, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,5,6,7,9,10,11] [1,2,5,6,7,9,10,11] [1,2] table150 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound151
    · exact bound165

theorem bound149 : ∀ f ∈ assignSearch step finish [] [] table149, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound148 : ∀ f ∈ assignSearch step finish [11] [5] table148, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [5] [5] table148 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound149

theorem bound147 : ∀ f ∈ assignSearch step finish [10,11] [5,7] table147, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [5,7] [7] table147 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound148

theorem bound146 : ∀ f ∈ assignSearch step finish [9,10,11] [5,6,7] table146, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [5,6,7] [6] table146 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound147

theorem bound145 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,6,7,9] table145, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,6,7,9] [9] table145 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound146

theorem bound144 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,7,9,11] table144, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,7,9,11] [11] table144 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound145

theorem bound143 : ∀ f ∈ assignSearch step finish [] [] table143, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound142 : ∀ f ∈ assignSearch step finish [11] [9] table142, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table142 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound143

theorem bound141 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table141, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [11] table141 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound142

theorem bound140 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table140, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [10] table140 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound141

theorem bound139 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,9,10,11] table139, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,9,10,11] [5] table139 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound140

theorem bound138 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,7,9,10,11] table138, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,7,9,10,11] [7] table138 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound139

theorem bound137 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [5,6,7,9,10,11] table137, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [5,6,7,9,10,11] [6,10] table137 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound138
    · exact bound144

theorem bound136 : ∀ f ∈ assignSearch step finish [3,5,6,7,9,10,11] [1,5,6,7,9,10,11] table136, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,9,10,11] [1,5,6,7,9,10,11] [1] table136 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound137

theorem bound135 : ∀ f ∈ assignSearch step finish [] [] table135, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound134 : ∀ f ∈ assignSearch step finish [11] [7] table134, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table134 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound135

theorem bound133 : ∀ f ∈ assignSearch step finish [10,11] [5,7] table133, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [5,7] [5] table133 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound134

theorem bound132 : ∀ f ∈ assignSearch step finish [9,10,11] [5,6,7] table132, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [5,6,7] [6] table132 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound133

theorem bound131 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,6,7,11] table131, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,6,7,11] [11] table131 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound132

theorem bound130 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,7,9,11] table130, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,7,9,11] [9] table130 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound131

theorem bound129 : ∀ f ∈ assignSearch step finish [] [] table129, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound128 : ∀ f ∈ assignSearch step finish [11] [11] table128, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table128 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound129
end C13.Enumeration.Canonical.Pair51_51
