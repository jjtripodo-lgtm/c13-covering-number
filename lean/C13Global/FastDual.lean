import C13Global.QuadUniverse
import C13Global.EmptyCore
import C13Global.RawDual
namespace C13.Global
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def quadMask : Mask := 9019518416950528558373478086511232658977980824891177721177636926312346534904278502866076317039886743974800348292372143905644807215480958775237835488942453051668846182647161161037274733495616198149652297823688715717490612562306141359265081465565467854673342699403354940986817845874764633529205803336231917398034701497470041669715694603746520683890897369439285370071567381344193454993657249195117220471000791645913668473717009001933967755774593934979111054344231577961265519786509424914993787525969883891775230937249580508937411303737085216831792849129536857440755810684386765932932522726498704062926851676801191109397721563337290469546593159306783723490656974674389093123101979104082196530366139935153676787433316011952451486612663142615937474023795516992075400134893200204727844995998951625883097717194480925354219710827004991988362796457207541259889284928480274903134055283027556557847166618239008918497945729456755850136110877182754890514963209391382876402222025697174614501916945810118310632911594641236439309996245705637523280183078958843675536246168687862230052141975967592561709435272113064816116797257869623324140692840999239078360718209389913210880
theorem quadMask_checked : listMask quadCodes = quadMask := by decide +kernel

def fastValidRowB (root : List Code) (K : Family Point) (Q : Finset Point) (r : LinearRow) : Bool :=
  match r.test with
  | .covers t => decide (0 ≤ r.weight) && decide (r.demand = 1) &&
      quadMask.testBit t.toNat && rootUncoveredB root t
  | .incident q => decide (q ∈ Q ∧ r.demand = (15 - degree K q : Nat))
  | .block _ => false

def fastLeafCheck (columns root : List Code) (K : Family Point) (Q : Finset Point)
    (rows : List LinearRow) (bound : Int) : Bool :=
  rows.all (fastValidRowB root K Q) && certificateB columns rows bound 14

theorem fastValidRow_sound (root : List Code) (K : Family Point)
    (binding : decodeSource root = K) (Q : Finset Point) (r : LinearRow)
    (h : fastValidRowB root K Q r = true) : RawValidRow K Q r := by
  cases ht : r.test with
  | covers t =>
    have hh : 0 ≤ r.weight ∧ r.demand = 1 ∧ quadMask.testBit t.toNat = true ∧
        rootUncoveredB root t = true := by
      simpa only [fastValidRowB,ht,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
    have hmem : t ∈ quadCodes := mem_of_mask_eq quadCodes quadMask quadMask_checked t hh.2.2.1
    have hgeom : decodeTyped t ⊆ univ.erase hole ∧ (decodeTyped t).card = 4 :=
      of_decide_eq_true (List.all_eq_true.mp quadCodes_valid t hmem)
    simp only [RawValidRow,ht]
    refine ⟨hh.1,hh.2.1,hgeom.1,hgeom.2,?_⟩
    intro B hB hsub
    rw [← binding] at hB
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
    have hn := rootUncovered_sound root t hh.2.2.2 b hb
    have hs := (C13.Enumeration.Census.subsetB_iff t b).2 hsub
    change subsetB t b = true at hs
    rw [hn] at hs
    contradiction
  | incident q =>
    simpa only [fastValidRowB,RawValidRow,ht,decide_eq_true_eq] using h
  | block b =>
    simp only [fastValidRowB,ht] at h
    contradiction

theorem fastLeafCheck_sound (columns root : List Code) (K : Family Point)
    (binding : decodeSource root = K) (Q : Finset Point) (rows : List LinearRow) (bound : Int)
    (h : fastLeafCheck columns root K Q rows bound = true) :
    rawLeafCheck columns K Q rows bound = true := by
  have hh : rows.all (fastValidRowB root K Q) = true ∧ certificateB columns rows bound 14 = true := by
    simpa only [fastLeafCheck,Bool.and_eq_true] using h
  simp only [rawLeafCheck,Bool.and_eq_true]
  refine ⟨?_,hh.2⟩
  apply List.all_eq_true.mpr
  intro r hr
  exact decide_eq_true (fastValidRow_sound root K binding Q r (List.all_eq_true.mp hh.1 r hr))
end C13.Global
