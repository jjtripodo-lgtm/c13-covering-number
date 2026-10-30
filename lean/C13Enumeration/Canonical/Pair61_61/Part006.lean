import C13Enumeration.Canonical.Pair61_61.Part007
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound223 : ∀ f ∈ assignSearch step finish [] [] table223, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound222 : ∀ f ∈ assignSearch step finish [11] [1] table222, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table222 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound223

theorem bound221 : ∀ f ∈ assignSearch step finish [10,11] [0,1] table221, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,1] [0] table221 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound222

theorem bound220 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,8] table220, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,8] [8] table220 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound221

theorem bound219 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,8,9] table219, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,8,9] [9] table219 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound220

theorem bound218 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,8,9,10] table218, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,8,9,10] [10] table218 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound219

theorem bound217 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,8,9,10] table217, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,8,9,10] [3,8] table217 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound218
    · exact bound224

theorem bound216 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,8,9,10,11] table216, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [11] table216 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound217

theorem bound215 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] table215, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] [7] table215 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound216

theorem bound214 : ∀ f ∈ assignSearch step finish [] [] table214, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound213 : ∀ f ∈ assignSearch step finish [11] [6] table213, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table213 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound214

theorem bound212 : ∀ f ∈ assignSearch step finish [10,11] [6,7] table212, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,7] [7] table212 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound213

theorem bound211 : ∀ f ∈ assignSearch step finish [9,10,11] [6,7,8] table211, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [6,7,8] [8] table211 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound212

theorem bound210 : ∀ f ∈ assignSearch step finish [8,9,10,11] [6,7,8,9] table210, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [6,7,8,9] [9] table210 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound211

theorem bound209 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,7,8,9,10] table209, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,7,8,9,10] [10] table209 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound210

theorem bound208 : ∀ f ∈ assignSearch step finish [] [] table208, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound207 : ∀ f ∈ assignSearch step finish [11] [9] table207, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table207 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound208

theorem bound206 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table206, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [10] table206 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound207

theorem bound205 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table205, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table205 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound206

theorem bound204 : ∀ f ∈ assignSearch step finish [8,9,10,11] [6,9,10,11] table204, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [6,9,10,11] [6] table204 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound205

theorem bound203 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,7,9,10,11] table203, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,7,9,10,11] [7] table203 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound204

theorem bound202 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table202, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [8,11] table202 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound203
    · exact bound209

theorem bound201 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [3,6,7,8,9,10,11] table201, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [3,6,7,8,9,10,11] [3] table201 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound202

theorem bound200 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,3,6,7,8,9,10,11] table200, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,3,6,7,8,9,10,11] [0] table200 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound201

theorem bound199 : ∀ f ∈ assignSearch step finish [] [] table199, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound198 : ∀ f ∈ assignSearch step finish [11] [7] table198, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table198 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound199

theorem bound197 : ∀ f ∈ assignSearch step finish [10,11] [6,7] table197, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,7] [6] table197 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound198

theorem bound196 : ∀ f ∈ assignSearch step finish [9,10,11] [6,7,8] table196, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [6,7,8] [8] table196 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound197

theorem bound195 : ∀ f ∈ assignSearch step finish [8,9,10,11] [6,7,8,10] table195, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [6,7,8,10] [10] table195 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound196

theorem bound194 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [6,7,8,9,10] table194, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [6,7,8,9,10] [9] table194 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound195

theorem bound193 : ∀ f ∈ assignSearch step finish [] [] table193, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound192 : ∀ f ∈ assignSearch step finish [11] [10] table192, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table192 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound193
end C13.Enumeration.Canonical.Pair61_61
