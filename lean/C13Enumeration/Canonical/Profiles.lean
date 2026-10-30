import Mathlib.Tactic.FinCases
import C13Enumeration.Canonical.Keys00
import C13Enumeration.Canonical.Keys01
import C13Enumeration.Canonical.Keys02
import C13Enumeration.Canonical.Keys03
import C13Enumeration.Canonical.Keys04
import C13Enumeration.Canonical.Keys05
import C13Enumeration.Canonical.Keys06
import C13Enumeration.Canonical.Keys07
import C13Enumeration.Canonical.Keys08
import C13Enumeration.Canonical.Keys09
import C13Enumeration.Canonical.Keys10
import C13Enumeration.Canonical.Keys11
import C13Enumeration.Canonical.Keys12
import C13Enumeration.Canonical.Keys13
import C13Enumeration.Canonical.Keys14
import C13Enumeration.Canonical.Keys15
namespace C13.Enumeration.Canonical
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem keys_checked (i : Fin 62) : profileKey i = keys i := by
  fin_cases i
  · exact key00_checked
  · exact key01_checked
  · exact key02_checked
  · exact key03_checked
  · exact key04_checked
  · exact key05_checked
  · exact key06_checked
  · exact key07_checked
  · exact key08_checked
  · exact key09_checked
  · exact key10_checked
  · exact key11_checked
  · exact key12_checked
  · exact key13_checked
  · exact key14_checked
  · exact key15_checked
  · exact key16_checked
  · exact key17_checked
  · exact key18_checked
  · exact key19_checked
  · exact key20_checked
  · exact key21_checked
  · exact key22_checked
  · exact key23_checked
  · exact key24_checked
  · exact key25_checked
  · exact key26_checked
  · exact key27_checked
  · exact key28_checked
  · exact key29_checked
  · exact key30_checked
  · exact key31_checked
  · exact key32_checked
  · exact key33_checked
  · exact key34_checked
  · exact key35_checked
  · exact key36_checked
  · exact key37_checked
  · exact key38_checked
  · exact key39_checked
  · exact key40_checked
  · exact key41_checked
  · exact key42_checked
  · exact key43_checked
  · exact key44_checked
  · exact key45_checked
  · exact key46_checked
  · exact key47_checked
  · exact key48_checked
  · exact key49_checked
  · exact key50_checked
  · exact key51_checked
  · exact key52_checked
  · exact key53_checked
  · exact key54_checked
  · exact key55_checked
  · exact key56_checked
  · exact key57_checked
  · exact key58_checked
  · exact key59_checked
  · exact key60_checked
  · exact key61_checked

theorem keys_invariant (i j : Fin 62) (e : Equiv.Perm Point)
    (h : transport e (templates i).star = (templates j).star) : keys i = keys j := by
  rw [← keys_checked i,← keys_checked j]
  exact congrArg (fun p => profileReferences.idxOf (profileMoments p)) ((templates i).profile_invariant (templates j) e h)
end C13.Enumeration.Canonical
