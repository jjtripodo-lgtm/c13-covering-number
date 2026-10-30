import C13Enumeration.DegreeEightPilot.Data
namespace C13.Enumeration.DegreeEightPilot.Source02Center01
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def valuesA : Array Nat := #[4,0,1,1,3,3,2,2,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,3,1,2,2,1,1,1,1,1,1,0,1,0,1,3,2,2,1,1,1,1,1,1,0,3,0,2,2,5,3,2,2,1,3,1,1,0,3,0,2,2,3,5,2,2,3,1,1,1,0,2,0,1,1,2,2,4,2,1,1,1,3,0,2,0,1,1,2,2,2,4,1,1,3,1,0,1,0,1,1,1,3,1,1,3,1,1,1,0,1,0,1,1,3,1,1,1,1,3,1,1,0,1,0,1,1,1,1,1,3,1,1,3,1,0,1,0,1,1,1,1,3,1,1,1,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrixA (a b : Point) : Nat := valuesA.getD (13*a.val+b.val) 0
theorem matrixA_checked : ∀ a b, matrixA a b = coDegree (link link02 1) a b := by decide +kernel

def maps : List (Point → Point) := [![5,12,7,6,0,1,2,3,9,8,11,10,4],![5,12,6,7,0,1,3,2,9,8,10,11,4],![5,12,6,7,1,0,2,3,8,9,11,10,4],![5,12,7,6,1,0,3,2,8,9,10,11,4]]
def step := starStep (link link02 1) (link link01 4) matrixA matrix
def finish := crossMapFinish link02 link01 hole 1 4
def table0 : Point → Point := anchorTable hole hole 4
def table1 : Point → Point := put table0 4 0
def table2 : Point → Point := put table1 5 1
def table3 : Point → Point := put table2 0 5
def table4 : Point → Point := put table3 6 2
def table5 : Point → Point := put table4 7 3
def table6 : Point → Point := put table5 2 7
def table7 : Point → Point := put table6 3 6
def table8 : Point → Point := put table7 8 9
def table9 : Point → Point := put table8 9 8
def table10 : Point → Point := put table9 10 11
def table11 : Point → Point := put table10 11 10
def table12 : Point → Point := put table3 6 3
def table13 : Point → Point := put table12 7 2
def table14 : Point → Point := put table13 2 6
def table15 : Point → Point := put table14 3 7
def table16 : Point → Point := put table15 8 9
def table17 : Point → Point := put table16 9 8
def table18 : Point → Point := put table17 10 10
def table19 : Point → Point := put table18 11 11
def table20 : Point → Point := put table0 4 1
def table21 : Point → Point := put table20 5 0
def table22 : Point → Point := put table21 0 5
def table23 : Point → Point := put table22 6 2
def table24 : Point → Point := put table23 7 3
def table25 : Point → Point := put table24 2 6
def table26 : Point → Point := put table25 3 7
def table27 : Point → Point := put table26 8 8
def table28 : Point → Point := put table27 9 9
def table29 : Point → Point := put table28 10 11
def table30 : Point → Point := put table29 11 10
def table31 : Point → Point := put table22 6 3
def table32 : Point → Point := put table31 7 2
def table33 : Point → Point := put table32 2 7
def table34 : Point → Point := put table33 3 6
def table35 : Point → Point := put table34 8 8
def table36 : Point → Point := put table35 9 9
def table37 : Point → Point := put table36 10 10
def table38 : Point → Point := put table37 11 11

theorem bound38 : ∀ f ∈ assignSearch step finish [] [] table38, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound37 : ∀ f ∈ assignSearch step finish [11] [11] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound38

theorem bound36 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound37

theorem bound35 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound36

theorem bound34 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [8] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound35

theorem bound33 : ∀ f ∈ assignSearch step finish [3,8,9,10,11] [6,8,9,10,11] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [8,9,10,11] [6,8,9,10,11] [6] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ f ∈ assignSearch step finish [2,3,8,9,10,11] [6,7,8,9,10,11] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,8,9,10,11] [6,7,8,9,10,11] [7] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound33

theorem bound31 : ∀ f ∈ assignSearch step finish [7,2,3,8,9,10,11] [2,6,7,8,9,10,11] table31, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [2,3,8,9,10,11] [2,6,7,8,9,10,11] [2] table31 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound32

theorem bound30 : ∀ f ∈ assignSearch step finish [] [] table30, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound29 : ∀ f ∈ assignSearch step finish [11] [10] table29, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table29 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound30

theorem bound28 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table28, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table28 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound29

theorem bound27 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table27, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound28

theorem bound26 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table26, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [8] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound27

theorem bound25 : ∀ f ∈ assignSearch step finish [3,8,9,10,11] [7,8,9,10,11] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [8,9,10,11] [7,8,9,10,11] [7] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound26

theorem bound24 : ∀ f ∈ assignSearch step finish [2,3,8,9,10,11] [6,7,8,9,10,11] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,8,9,10,11] [6,7,8,9,10,11] [6] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound25

theorem bound23 : ∀ f ∈ assignSearch step finish [7,2,3,8,9,10,11] [3,6,7,8,9,10,11] table23, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [2,3,8,9,10,11] [3,6,7,8,9,10,11] [3] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound24

theorem bound22 : ∀ f ∈ assignSearch step finish [6,7,2,3,8,9,10,11] [2,3,6,7,8,9,10,11] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,2,3,8,9,10,11] [2,3,6,7,8,9,10,11] [2,3] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound23
    · exact bound31

theorem bound21 : ∀ f ∈ assignSearch step finish [0,6,7,2,3,8,9,10,11] [2,3,5,6,7,8,9,10,11] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [6,7,2,3,8,9,10,11] [2,3,5,6,7,8,9,10,11] [5] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound22

theorem bound20 : ∀ f ∈ assignSearch step finish [5,0,6,7,2,3,8,9,10,11] [0,2,3,5,6,7,8,9,10,11] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [0,6,7,2,3,8,9,10,11] [0,2,3,5,6,7,8,9,10,11] [0] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound21

theorem bound19 : ∀ f ∈ assignSearch step finish [] [] table19, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound18 : ∀ f ∈ assignSearch step finish [11] [11] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [9,10,11] [8,10,11] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [8,10,11] [8] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [9] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [3,8,9,10,11] [7,8,9,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [8,9,10,11] [7,8,9,10,11] [7] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound15

theorem bound13 : ∀ f ∈ assignSearch step finish [2,3,8,9,10,11] [6,7,8,9,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,8,9,10,11] [6,7,8,9,10,11] [6] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [7,2,3,8,9,10,11] [2,6,7,8,9,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [2,3,8,9,10,11] [2,6,7,8,9,10,11] [2] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ f ∈ assignSearch step finish [] [] table11, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound10 : ∀ f ∈ assignSearch step finish [11] [10] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [9,10,11] [8,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [8,10,11] [8] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ f ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [8,9,10,11] [9] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [3,8,9,10,11] [6,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [8,9,10,11] [6,8,9,10,11] [6] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [2,3,8,9,10,11] [6,7,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,8,9,10,11] [6,7,8,9,10,11] [7] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [7,2,3,8,9,10,11] [3,6,7,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [2,3,8,9,10,11] [3,6,7,8,9,10,11] [3] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [6,7,2,3,8,9,10,11] [2,3,6,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,2,3,8,9,10,11] [2,3,6,7,8,9,10,11] [2,3] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound4
    · exact bound12

theorem bound2 : ∀ f ∈ assignSearch step finish [0,6,7,2,3,8,9,10,11] [2,3,5,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [6,7,2,3,8,9,10,11] [2,3,5,6,7,8,9,10,11] [5] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound3

theorem bound1 : ∀ f ∈ assignSearch step finish [5,0,6,7,2,3,8,9,10,11] [1,2,3,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [0,6,7,2,3,8,9,10,11] [1,2,3,5,6,7,8,9,10,11] [1] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [4,5,0,6,7,2,3,8,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,0,6,7,2,3,8,9,10,11] [0,1,2,3,5,6,7,8,9,10,11] [0,1] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound20

theorem complete_maps (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (1 : Point) = hole)
    (hs : transport e (link link02 1) = link link01 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link02 link01 hole 1 4 [4,5,0,6,7,2,3,8,9,10,11]
    (by decide +kernel) (by decide +kernel) matrixA matrix matrixA_checked matrix_checked maps bound0 e he hc hs

def pick : Fin maps.length → table.Index := ![⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]

theorem rows_checked : ∀ i : Fin maps.length,
    (codedDomain.pencil (table.row (pick i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes02 1 4 (fun x => maps.get i ((Equiv.refl Point) x))).toFinset := by
  decide +kernel

theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (1 : Point) = hole)
    (hs : transport e (link link02 1) = link link01 4) :
    ∃ p ∈ codedDomain.supported.domain.2, RepresentsPencil p (emitPencil link02 1 4 e) := by
  exact mapsRepresented_of_code_checks codedDomain table RawClass9.CatalogCodes.codes02
    link02 RawClass9.CatalogCodes.checked02 1 4 (Equiv.refl Point) maps pick rows_checked
    e (complete_maps e he hc hs)
end C13.Enumeration.DegreeEightPilot.Source02Center01
