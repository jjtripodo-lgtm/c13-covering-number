import C13Enumeration.Canonical.Pair61_61.Part009
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound287 : ∀ f ∈ assignSearch step finish [9,10,11] [1,8,11] table287, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,8,11] [1] table287 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound288

theorem bound286 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,7,8,11] table286, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,7,8,11] [7] table286 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound287

theorem bound285 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,7,8,10,11] table285, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,7,8,10,11] [10] table285 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound286

theorem bound284 : ∀ f ∈ assignSearch step finish [] [] table284, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound283 : ∀ f ∈ assignSearch step finish [11] [7] table283, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table283 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound284

theorem bound282 : ∀ f ∈ assignSearch step finish [10,11] [7,10] table282, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [7,10] [10] table282 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound283

theorem bound281 : ∀ f ∈ assignSearch step finish [9,10,11] [2,7,10] table281, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,7,10] [2] table281 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound282

theorem bound280 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,7,8,10] table280, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,7,8,10] [8] table280 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound281

theorem bound279 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,7,8,10,11] table279, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,7,8,10,11] [11] table279 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound280

theorem bound278 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,7,8,10,11] table278, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,7,8,10,11] [1,2] table278 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound279
    · exact bound285

theorem bound277 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,7,8,10,11] table277, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,7,8,10,11] [0] table277 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound278

theorem bound276 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,7,8,9,10,11] table276, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,7,8,9,10,11] [9] table276 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound277

theorem bound275 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,2,6,7,8,9,10,11] table275, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,2,6,7,8,9,10,11] [6,7,8,9,10,11] table275 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound276
    · exact bound291
    · exact bound306
    · exact bound321
    · exact bound336
    · exact bound351

theorem bound274 : ∀ f ∈ assignSearch step finish [] [] table274, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound273 : ∀ f ∈ assignSearch step finish [11] [7] table273, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table273 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound274

theorem bound272 : ∀ f ∈ assignSearch step finish [10,11] [6,7] table272, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,7] [6] table272 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound273

theorem bound271 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,7] table271, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,7] [3] table271 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound272

theorem bound270 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,6,7] table270, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,6,7] [0] table270 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound271

theorem bound269 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,6,7] table269, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,6,7] [1] table269 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound270

theorem bound268 : ∀ f ∈ assignSearch step finish [] [] table268, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound267 : ∀ f ∈ assignSearch step finish [11] [0] table267, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table267 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound268

theorem bound266 : ∀ f ∈ assignSearch step finish [10,11] [0,1] table266, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,1] [1] table266 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound267

theorem bound265 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,11] table265, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,11] [11] table265 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound266

theorem bound264 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,7,11] table264, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,7,11] [7] table264 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound265

theorem bound263 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,6,7,11] table263, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,6,7,11] [6] table263 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound264

theorem bound262 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,6,7,11] table262, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,6,7,11] [3,11] table262 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound263
    · exact bound269

theorem bound261 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,6,7,8,11] table261, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,6,7,8,11] [8] table261 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound262

theorem bound260 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,6,7,8,9,11] table260, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,6,7,8,9,11] [9] table260 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound261

theorem bound259 : ∀ f ∈ assignSearch step finish [] [] table259, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound258 : ∀ f ∈ assignSearch step finish [11] [6] table258, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table258 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound259

theorem bound257 : ∀ f ∈ assignSearch step finish [10,11] [6,7] table257, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,7] [7] table257 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound258

theorem bound256 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,7] table256, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,7] [3] table256 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound257
end C13.Enumeration.Canonical.Pair61_61
