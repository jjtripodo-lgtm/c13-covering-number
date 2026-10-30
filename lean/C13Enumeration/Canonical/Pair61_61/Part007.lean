import C13Enumeration.Canonical.Pair61_61.Part008
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound255 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,3,6,7] table255, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,3,6,7] [1] table255 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound256

theorem bound254 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,6,7] table254, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,6,7] [0] table254 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound255

theorem bound253 : ∀ f ∈ assignSearch step finish [] [] table253, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound252 : ∀ f ∈ assignSearch step finish [11] [1] table252, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table252 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound253

theorem bound251 : ∀ f ∈ assignSearch step finish [10,11] [0,1] table251, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,1] [0] table251 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound252

theorem bound250 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,11] table250, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,11] [11] table250 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound251

theorem bound249 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,6,11] table249, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,6,11] [6] table249 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound250

theorem bound248 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,6,7,11] table248, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,6,7,11] [7] table248 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound249

theorem bound247 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,6,7,11] table247, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,6,7,11] [3,11] table247 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound248
    · exact bound254

theorem bound246 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,6,7,8,11] table246, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,6,7,8,11] [8] table246 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound247

theorem bound245 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,6,7,8,10,11] table245, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,6,7,8,10,11] [10] table245 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound246

theorem bound244 : ∀ f ∈ assignSearch step finish [] [] table244, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound243 : ∀ f ∈ assignSearch step finish [11] [10] table243, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table243 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound244

theorem bound242 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table242, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [9] table242 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound243

theorem bound241 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,10] table241, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,10] [3] table241 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound242

theorem bound240 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,9,10] table240, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,9,10] [0] table240 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound241

theorem bound239 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,9,10] table239, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,9,10] [1] table239 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound240

theorem bound238 : ∀ f ∈ assignSearch step finish [] [] table238, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound237 : ∀ f ∈ assignSearch step finish [11] [0] table237, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table237 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound238

theorem bound236 : ∀ f ∈ assignSearch step finish [10,11] [0,1] table236, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,1] [1] table236 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound237

theorem bound235 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,8] table235, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,8] [8] table235 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound236

theorem bound234 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,8,10] table234, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,8,10] [10] table234 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound235

theorem bound233 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,8,9,10] table233, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,8,9,10] [9] table233 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound234

theorem bound232 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,8,9,10] table232, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,8,9,10] [3,8] table232 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound233
    · exact bound239

theorem bound231 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,8,9,10,11] table231, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [11] table231 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound232

theorem bound230 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] table230, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] [6] table230 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound231

theorem bound229 : ∀ f ∈ assignSearch step finish [] [] table229, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound228 : ∀ f ∈ assignSearch step finish [11] [9] table228, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table228 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound229

theorem bound227 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table227, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [10] table227 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound228

theorem bound226 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,10] table226, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,10] [3] table226 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound227

theorem bound225 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,3,9,10] table225, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,3,9,10] [1] table225 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound226

theorem bound224 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,9,10] table224, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,9,10] [0] table224 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound225
end C13.Enumeration.Canonical.Pair61_61
