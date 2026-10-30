import C13Enumeration.Census.Figure6Columns0Part0
import C13Enumeration.Census.Figure6Columns0Part1
import C13Enumeration.Census.Figure6Columns0Part2
import C13Enumeration.Census.Figure6Columns0Part3
import C13Enumeration.Census.Figure6Columns0Part4
import C13Enumeration.Census.Figure6Columns0Part5
import C13Enumeration.Census.Figure6Columns0Part6
namespace C13.Enumeration.Census.Figure6Case0
set_option Elab.async false
set_option maxRecDepth 10000
private theorem suffix25 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 800) (witnesses.drop 800) = true := by
  have ha : blockCodes.length ≤ 800 := by decide +kernel
  have hb : witnesses.length ≤ 800 := by decide +kernel
  rw [List.drop_eq_nil_of_le ha,List.drop_eq_nil_of_le hb]
  rfl
private theorem suffix24 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 768) (witnesses.drop 768) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 768).drop 32) ((witnesses.drop 768).drop 32) = true := by
    simpa only [List.drop_drop] using suffix25
  have hh := zipAllExact_append_true columnChunk24 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix23 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 736) (witnesses.drop 736) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 736).drop 32) ((witnesses.drop 736).drop 32) = true := by
    simpa only [List.drop_drop] using suffix24
  have hh := zipAllExact_append_true columnChunk23 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix22 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 704) (witnesses.drop 704) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 704).drop 32) ((witnesses.drop 704).drop 32) = true := by
    simpa only [List.drop_drop] using suffix23
  have hh := zipAllExact_append_true columnChunk22 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix21 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 672) (witnesses.drop 672) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 672).drop 32) ((witnesses.drop 672).drop 32) = true := by
    simpa only [List.drop_drop] using suffix22
  have hh := zipAllExact_append_true columnChunk21 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix20 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 640) (witnesses.drop 640) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 640).drop 32) ((witnesses.drop 640).drop 32) = true := by
    simpa only [List.drop_drop] using suffix21
  have hh := zipAllExact_append_true columnChunk20 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix19 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 608) (witnesses.drop 608) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 608).drop 32) ((witnesses.drop 608).drop 32) = true := by
    simpa only [List.drop_drop] using suffix20
  have hh := zipAllExact_append_true columnChunk19 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix18 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 576) (witnesses.drop 576) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 576).drop 32) ((witnesses.drop 576).drop 32) = true := by
    simpa only [List.drop_drop] using suffix19
  have hh := zipAllExact_append_true columnChunk18 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix17 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 544) (witnesses.drop 544) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 544).drop 32) ((witnesses.drop 544).drop 32) = true := by
    simpa only [List.drop_drop] using suffix18
  have hh := zipAllExact_append_true columnChunk17 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix16 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 512) (witnesses.drop 512) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 512).drop 32) ((witnesses.drop 512).drop 32) = true := by
    simpa only [List.drop_drop] using suffix17
  have hh := zipAllExact_append_true columnChunk16 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix15 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 480) (witnesses.drop 480) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 480).drop 32) ((witnesses.drop 480).drop 32) = true := by
    simpa only [List.drop_drop] using suffix16
  have hh := zipAllExact_append_true columnChunk15 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix14 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 448) (witnesses.drop 448) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 448).drop 32) ((witnesses.drop 448).drop 32) = true := by
    simpa only [List.drop_drop] using suffix15
  have hh := zipAllExact_append_true columnChunk14 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix13 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 416) (witnesses.drop 416) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 416).drop 32) ((witnesses.drop 416).drop 32) = true := by
    simpa only [List.drop_drop] using suffix14
  have hh := zipAllExact_append_true columnChunk13 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix12 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 384) (witnesses.drop 384) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 384).drop 32) ((witnesses.drop 384).drop 32) = true := by
    simpa only [List.drop_drop] using suffix13
  have hh := zipAllExact_append_true columnChunk12 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix11 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 352) (witnesses.drop 352) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 352).drop 32) ((witnesses.drop 352).drop 32) = true := by
    simpa only [List.drop_drop] using suffix12
  have hh := zipAllExact_append_true columnChunk11 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix10 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 320) (witnesses.drop 320) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 320).drop 32) ((witnesses.drop 320).drop 32) = true := by
    simpa only [List.drop_drop] using suffix11
  have hh := zipAllExact_append_true columnChunk10 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix9 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 288) (witnesses.drop 288) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 288).drop 32) ((witnesses.drop 288).drop 32) = true := by
    simpa only [List.drop_drop] using suffix10
  have hh := zipAllExact_append_true columnChunk09 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix8 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 256) (witnesses.drop 256) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 256).drop 32) ((witnesses.drop 256).drop 32) = true := by
    simpa only [List.drop_drop] using suffix9
  have hh := zipAllExact_append_true columnChunk08 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix7 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 224) (witnesses.drop 224) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 224).drop 32) ((witnesses.drop 224).drop 32) = true := by
    simpa only [List.drop_drop] using suffix8
  have hh := zipAllExact_append_true columnChunk07 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix6 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 192) (witnesses.drop 192) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 192).drop 32) ((witnesses.drop 192).drop 32) = true := by
    simpa only [List.drop_drop] using suffix7
  have hh := zipAllExact_append_true columnChunk06 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix5 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 160) (witnesses.drop 160) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 160).drop 32) ((witnesses.drop 160).drop 32) = true := by
    simpa only [List.drop_drop] using suffix6
  have hh := zipAllExact_append_true columnChunk05 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix4 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 128) (witnesses.drop 128) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 128).drop 32) ((witnesses.drop 128).drop 32) = true := by
    simpa only [List.drop_drop] using suffix5
  have hh := zipAllExact_append_true columnChunk04 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix3 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 96) (witnesses.drop 96) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 96).drop 32) ((witnesses.drop 96).drop 32) = true := by
    simpa only [List.drop_drop] using suffix4
  have hh := zipAllExact_append_true columnChunk03 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix2 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 64) (witnesses.drop 64) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 64).drop 32) ((witnesses.drop 64).drop 32) = true := by
    simpa only [List.drop_drop] using suffix3
  have hh := zipAllExact_append_true columnChunk02 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix1 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 32) (witnesses.drop 32) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 32).drop 32) ((witnesses.drop 32).drop 32) = true := by
    simpa only [List.drop_drop] using suffix2
  have hh := zipAllExact_append_true columnChunk01 ht
  simpa only [List.take_append_drop] using hh
private theorem suffix0 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) (blockCodes.drop 0) (witnesses.drop 0) = true := by
  have ht : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 0).drop 32) ((witnesses.drop 0).drop 32) = true := by
    simpa only [List.drop_drop] using suffix1
  have hh := zipAllExact_append_true columnChunk00 ht
  simpa only [List.take_append_drop] using hh
theorem columns_checked : columnsCertificateB columns Figure6Alphabets.alphabet points witnesses = true := by
  simpa only [columnsCertificateB,List.drop_zero] using suffix0
end C13.Enumeration.Census.Figure6Case0
