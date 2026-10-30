import C13Enumeration.Canonical.Pair51_51.Data
namespace C13.Enumeration.Canonical.Pair51_51
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound178 : ∀ f ∈ assignSearch step finish [] [] table178, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound177 : ∀ f ∈ assignSearch step finish [11] [5] table177, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [5] [5] table177 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound178

theorem bound176 : ∀ f ∈ assignSearch step finish [10,11] [5,6] table176, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [5,6] [6] table176 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound177

theorem bound175 : ∀ f ∈ assignSearch step finish [9,10,11] [5,6,7] table175, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [5,6,7] [7] table175 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound176

theorem bound174 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,6,7,9] table174, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,6,7,9] [9] table174 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound175

theorem bound173 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,7,9,10] table173, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,7,9,10] [10] table173 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound174

theorem bound172 : ∀ f ∈ assignSearch step finish [] [] table172, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound171 : ∀ f ∈ assignSearch step finish [11] [9] table171, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table171 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound172

theorem bound170 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table170, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [10] table170 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound171

theorem bound169 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table169, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table169 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound170

theorem bound168 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,9,10,11] table168, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,9,10,11] [5] table168 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound169

theorem bound167 : ∀ f ∈ assignSearch step finish [6,7,9,10,11] [5,6,9,10,11] table167, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,9,10,11] [5,6,9,10,11] [6] table167 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound168

theorem bound166 : ∀ f ∈ assignSearch step finish [5,6,7,9,10,11] [5,6,7,9,10,11] table166, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,9,10,11] [5,6,7,9,10,11] [7,11] table166 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound167
    · exact bound173

theorem bound165 : ∀ f ∈ assignSearch step finish [3,5,6,7,9,10,11] [1,5,6,7,9,10,11] table165, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [5,6,7,9,10,11] [1,5,6,7,9,10,11] [1] table165 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound166

theorem bound164 : ∀ f ∈ assignSearch step finish [] [] table164, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound163 : ∀ f ∈ assignSearch step finish [11] [6] table163, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table163 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound164

theorem bound162 : ∀ f ∈ assignSearch step finish [10,11] [5,6] table162, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [5,6] [5] table162 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound163

theorem bound161 : ∀ f ∈ assignSearch step finish [9,10,11] [5,6,7] table161, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [5,6,7] [7] table161 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound162

theorem bound160 : ∀ f ∈ assignSearch step finish [7,9,10,11] [5,6,7,10] table160, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [9,10,11] [5,6,7,10] [10] table160 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound161
end C13.Enumeration.Canonical.Pair51_51
