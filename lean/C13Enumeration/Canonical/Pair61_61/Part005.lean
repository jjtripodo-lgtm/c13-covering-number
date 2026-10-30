import C13Enumeration.Canonical.Pair61_61.Part006
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound191 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table191, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [9] table191 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound192

theorem bound190 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table190, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table190 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound191

theorem bound189 : ∀ f ∈ assignSearch step finish [8,9,10,11] [7,9,10,11] table189, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [7,9,10,11] [7] table189 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound190

theorem bound188 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,7,9,10,11] table188, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,7,9,10,11] [6] table188 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound189

theorem bound187 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table187, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [8,11] table187 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound188
    · exact bound194

theorem bound186 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [3,6,7,8,9,10,11] table186, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [3,6,7,8,9,10,11] [3] table186 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound187

theorem bound185 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,3,6,7,8,9,10,11] table185, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,3,6,7,8,9,10,11] [1] table185 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound186

theorem bound184 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,3,6,7,8,9,10,11] table184, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,3,6,7,8,9,10,11] [0,1,6,7,9,10] table184 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound185
    · exact bound200
    · exact bound215
    · exact bound230
    · exact bound245
    · exact bound260

theorem bound183 : ∀ f ∈ assignSearch step finish [] [] table183, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound182 : ∀ f ∈ assignSearch step finish [11] [8] table182, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table182 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound183

theorem bound181 : ∀ f ∈ assignSearch step finish [10,11] [6,8] table181, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,8] [6] table181 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound182

theorem bound180 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,8] table180, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,8] [3] table180 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound181

theorem bound179 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,6,8] table179, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,6,8] [0] table179 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound180

theorem bound178 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,6,8] table178, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,6,8] [2] table178 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound179

theorem bound177 : ∀ f ∈ assignSearch step finish [] [] table177, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound176 : ∀ f ∈ assignSearch step finish [11] [0] table176, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table176 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound177

theorem bound175 : ∀ f ∈ assignSearch step finish [10,11] [0,2] table175, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,2] [2] table175 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound176

theorem bound174 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,10] table174, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,10] [10] table174 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound175

theorem bound173 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,8,10] table173, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,8,10] [8] table173 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound174

theorem bound172 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,6,8,10] table172, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,6,8,10] [6] table172 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound173

theorem bound171 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,6,8,10] table171, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,6,8,10] [3,10] table171 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound172
    · exact bound178

theorem bound170 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,6,7,8,10] table170, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,6,7,8,10] [7] table170 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound171

theorem bound169 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,6,7,8,9,10] table169, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,6,7,8,9,10] [9] table169 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound170

theorem bound168 : ∀ f ∈ assignSearch step finish [] [] table168, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound167 : ∀ f ∈ assignSearch step finish [11] [6] table167, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table167 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound168

theorem bound166 : ∀ f ∈ assignSearch step finish [10,11] [6,8] table166, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,8] [8] table166 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound167

theorem bound165 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,8] table165, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,8] [3] table165 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound166

theorem bound164 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,3,6,8] table164, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,3,6,8] [2] table164 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound165

theorem bound163 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,6,8] table163, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,6,8] [0] table163 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound164

theorem bound162 : ∀ f ∈ assignSearch step finish [] [] table162, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound161 : ∀ f ∈ assignSearch step finish [11] [2] table161, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table161 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound162

theorem bound160 : ∀ f ∈ assignSearch step finish [10,11] [0,2] table160, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,2] [0] table160 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound161
end C13.Enumeration.Canonical.Pair61_61
