import C13Enumeration.Template6.Part000
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (6 : Point) = hole)
    (hs : transport e (link link09 6) = link link09 6) : (e : Point → Point) ∈ maps := by
  exact star_template_maps_complete link09 hole 6 [0,10,1,2,3,4,5,7,8,9,11]
    (by decide +kernel) (by decide +kernel) matrix matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link09 link09 hole 6 hole 6 f)
def mapsPart (n : Nat) : List (Point → Point) := (maps.drop (16*n)).take 16

theorem validPart0 : ((mapsPart 0).all validMap) = true := by decide +kernel
theorem validPart1 : ((mapsPart 1).all validMap) = true := by decide +kernel
theorem validPart2 : ((mapsPart 2).all validMap) = true := by decide +kernel
theorem validPart3 : ((mapsPart 3).all validMap) = true := by decide +kernel
theorem validPart4 : ((mapsPart 4).all validMap) = true := by decide +kernel
theorem validPart5 : ((mapsPart 5).all validMap) = true := by decide +kernel

theorem maps_parts : maps = mapsPart 0 ++ mapsPart 1 ++ mapsPart 2 ++ mapsPart 3 ++ mapsPart 4 ++ mapsPart 5 := by rfl

theorem listed_chunk0 : (((maps.drop 0).take 16).all fun f => decide (GoodMap link09 link09 hole 6 hole 6 f)) = true := by
  decide +kernel

theorem listed_chunk1 : (((maps.drop 16).take 16).all fun f => decide (GoodMap link09 link09 hole 6 hole 6 f)) = true := by
  decide +kernel

theorem listed_chunk2 : (((maps.drop 32).take 16).all fun f => decide (GoodMap link09 link09 hole 6 hole 6 f)) = true := by
  decide +kernel

theorem listed_chunk3 : (((maps.drop 48).take 16).all fun f => decide (GoodMap link09 link09 hole 6 hole 6 f)) = true := by
  decide +kernel

theorem listed_chunk4 : (((maps.drop 64).take 16).all fun f => decide (GoodMap link09 link09 hole 6 hole 6 f)) = true := by
  decide +kernel

theorem listed_chunk5 : (((maps.drop 80).take 16).all fun f => decide (GoodMap link09 link09 hole 6 hole 6 f)) = true := by
  decide +kernel

theorem listed_maps_check : (maps.all fun f => decide (GoodMap link09 link09 hole 6 hole 6 f)) = true := by
  have hsplit : maps = ((maps.drop 0).take 16) ++ ((maps.drop 16).take 16) ++ ((maps.drop 32).take 16) ++ ((maps.drop 48).take 16) ++ ((maps.drop 64).take 16) ++ ((maps.drop 80).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨listed_chunk0,listed_chunk1,listed_chunk2,listed_chunk3,listed_chunk4,listed_chunk5⟩
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link09 link09 hole 6 hole 6 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp listed_maps_check) f hf)
end C13.Enumeration.Template6
