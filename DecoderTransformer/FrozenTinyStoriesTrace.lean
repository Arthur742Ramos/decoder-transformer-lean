import DecoderTransformer.IEEETraceCertificate
import Mathlib.Tactic

namespace DecoderTransformer
namespace FrozenTinyStoriesTrace

noncomputable section

/-!
# Frozen TinyStories checkpoint trace

This is the Lean counterpart of Frozen_TinyStories_Trace.thy. The source
checkpoint payload is retained as explicit sign/exponent/mantissa triples.
The definitions below retain those fields as actual binary32 values and use
the IEEE decoder from `IEEE754Projection` for the real view. The trace is
therefore checked against the source formalization's finite-value and RNE
certificate boundary, while the source AFP's unresolved halfway preference
remains explicit in the nearest-value selector.

Model: roneneldan/TinyStories-1M
Revision: 77f1b168e219585646439073245fe87e56b3023e
Checkpoint URL: https://huggingface.co/roneneldan/TinyStories-1M/resolve/77f1b168e219585646439073245fe87e56b3023e/pytorch_model.bin
Config SHA256: ff74c30d5ebb5ab1da0f2ea479adf7197c504b42b5522a858c334ab91ed4958c
Checkpoint SHA256: 07f9609ea882b8163ff3b23d40e2b82cb715d409631beb15c84b164f3877dae7
-/

abbrev frozen_binary32 := ieee_binary32

structure FrozenBitFields where
  sign : Nat
  exponent : Nat
  mantissa : Nat

def frozenDecode (sign exponent mantissa : Nat) : ℝ :=
  let significand : ℝ := 1 + (mantissa : ℝ) / (2 ^ (23 : Nat))
  let magnitude : ℝ :=
    if 127 ≤ exponent then
      significand * (2 ^ (exponent - 127))
    else
      significand / (2 ^ (127 - exponent))
  if sign = 0 then magnitude else -magnitude

def frozenMake (sign exponent mantissa : Nat) : frozen_binary32 :=
  ⟨sign ≠ 0, Fin.ofNat _ exponent, Fin.ofNat _ mantissa⟩

def frozen_embedding_0 : frozen_binary32 := frozenMake 0 123 5074352
def frozen_embedding_0_bits : FrozenBitFields := ⟨0, 123, 5074352⟩
def frozen_embedding_1 : frozen_binary32 := frozenMake 1 123 3382044
def frozen_embedding_1_bits : FrozenBitFields := ⟨1, 123, 3382044⟩
def frozen_embedding_2 : frozen_binary32 := frozenMake 1 123 7491020
def frozen_embedding_2_bits : FrozenBitFields := ⟨1, 123, 7491020⟩
def frozen_embedding_3 : frozen_binary32 := frozenMake 1 117 1123531
def frozen_embedding_3_bits : FrozenBitFields := ⟨1, 117, 1123531⟩
def frozen_embedding_4 : frozen_binary32 := frozenMake 0 122 4708213
def frozen_embedding_4_bits : FrozenBitFields := ⟨0, 122, 4708213⟩
def frozen_embedding_5 : frozen_binary32 := frozenMake 1 122 5862559
def frozen_embedding_5_bits : FrozenBitFields := ⟨1, 122, 5862559⟩
def frozen_embedding_6 : frozen_binary32 := frozenMake 1 120 8243867
def frozen_embedding_6_bits : FrozenBitFields := ⟨1, 120, 8243867⟩
def frozen_embedding_7 : frozen_binary32 := frozenMake 1 124 153629
def frozen_embedding_7_bits : FrozenBitFields := ⟨1, 124, 153629⟩
def frozen_embedding_8 : frozen_binary32 := frozenMake 1 120 2841710
def frozen_embedding_8_bits : FrozenBitFields := ⟨1, 120, 2841710⟩
def frozen_embedding_9 : frozen_binary32 := frozenMake 1 120 771879
def frozen_embedding_9_bits : FrozenBitFields := ⟨1, 120, 771879⟩
def frozen_embedding_10 : frozen_binary32 := frozenMake 0 123 2103767
def frozen_embedding_10_bits : FrozenBitFields := ⟨0, 123, 2103767⟩
def frozen_embedding_11 : frozen_binary32 := frozenMake 0 122 6336013
def frozen_embedding_11_bits : FrozenBitFields := ⟨0, 122, 6336013⟩
def frozen_embedding_12 : frozen_binary32 := frozenMake 0 125 2797787
def frozen_embedding_12_bits : FrozenBitFields := ⟨0, 125, 2797787⟩
def frozen_embedding_13 : frozen_binary32 := frozenMake 1 124 5531178
def frozen_embedding_13_bits : FrozenBitFields := ⟨1, 124, 5531178⟩
def frozen_embedding_14 : frozen_binary32 := frozenMake 1 124 460533
def frozen_embedding_14_bits : FrozenBitFields := ⟨1, 124, 460533⟩
def frozen_embedding_15 : frozen_binary32 := frozenMake 1 123 2350548
def frozen_embedding_15_bits : FrozenBitFields := ⟨1, 123, 2350548⟩
def frozen_embedding_16 : frozen_binary32 := frozenMake 1 124 350479
def frozen_embedding_16_bits : FrozenBitFields := ⟨1, 124, 350479⟩
def frozen_embedding_17 : frozen_binary32 := frozenMake 1 124 3291407
def frozen_embedding_17_bits : FrozenBitFields := ⟨1, 124, 3291407⟩
def frozen_embedding_18 : frozen_binary32 := frozenMake 1 123 992045
def frozen_embedding_18_bits : FrozenBitFields := ⟨1, 123, 992045⟩
def frozen_embedding_19 : frozen_binary32 := frozenMake 0 122 3314477
def frozen_embedding_19_bits : FrozenBitFields := ⟨0, 122, 3314477⟩
def frozen_embedding_20 : frozen_binary32 := frozenMake 0 124 8111437
def frozen_embedding_20_bits : FrozenBitFields := ⟨0, 124, 8111437⟩
def frozen_embedding_21 : frozen_binary32 := frozenMake 1 122 588320
def frozen_embedding_21_bits : FrozenBitFields := ⟨1, 122, 588320⟩
def frozen_embedding_22 : frozen_binary32 := frozenMake 1 122 3677860
def frozen_embedding_22_bits : FrozenBitFields := ⟨1, 122, 3677860⟩
def frozen_embedding_23 : frozen_binary32 := frozenMake 1 124 349479
def frozen_embedding_23_bits : FrozenBitFields := ⟨1, 124, 349479⟩
def frozen_embedding_24 : frozen_binary32 := frozenMake 0 122 7978651
def frozen_embedding_24_bits : FrozenBitFields := ⟨0, 122, 7978651⟩
def frozen_embedding_25 : frozen_binary32 := frozenMake 1 122 8209427
def frozen_embedding_25_bits : FrozenBitFields := ⟨1, 122, 8209427⟩
def frozen_embedding_26 : frozen_binary32 := frozenMake 1 124 638524
def frozen_embedding_26_bits : FrozenBitFields := ⟨1, 124, 638524⟩
def frozen_embedding_27 : frozen_binary32 := frozenMake 0 124 3777630
def frozen_embedding_27_bits : FrozenBitFields := ⟨0, 124, 3777630⟩
def frozen_embedding_28 : frozen_binary32 := frozenMake 0 125 744085
def frozen_embedding_28_bits : FrozenBitFields := ⟨0, 125, 744085⟩
def frozen_embedding_29 : frozen_binary32 := frozenMake 1 123 2969911
def frozen_embedding_29_bits : FrozenBitFields := ⟨1, 123, 2969911⟩
def frozen_embedding_30 : frozen_binary32 := frozenMake 1 120 7392880
def frozen_embedding_30_bits : FrozenBitFields := ⟨1, 120, 7392880⟩
def frozen_embedding_31 : frozen_binary32 := frozenMake 1 124 934096
def frozen_embedding_31_bits : FrozenBitFields := ⟨1, 124, 934096⟩
def frozen_embedding_32 : frozen_binary32 := frozenMake 1 123 5022965
def frozen_embedding_32_bits : FrozenBitFields := ⟨1, 123, 5022965⟩
def frozen_embedding_33 : frozen_binary32 := frozenMake 1 124 165071
def frozen_embedding_33_bits : FrozenBitFields := ⟨1, 124, 165071⟩
def frozen_embedding_34 : frozen_binary32 := frozenMake 0 124 2851502
def frozen_embedding_34_bits : FrozenBitFields := ⟨0, 124, 2851502⟩
def frozen_embedding_35 : frozen_binary32 := frozenMake 0 123 1501519
def frozen_embedding_35_bits : FrozenBitFields := ⟨0, 123, 1501519⟩
def frozen_embedding_36 : frozen_binary32 := frozenMake 0 123 7774871
def frozen_embedding_36_bits : FrozenBitFields := ⟨0, 123, 7774871⟩
def frozen_embedding_37 : frozen_binary32 := frozenMake 1 122 2257260
def frozen_embedding_37_bits : FrozenBitFields := ⟨1, 122, 2257260⟩
def frozen_embedding_38 : frozen_binary32 := frozenMake 1 123 2797954
def frozen_embedding_38_bits : FrozenBitFields := ⟨1, 123, 2797954⟩
def frozen_embedding_39 : frozen_binary32 := frozenMake 0 124 2160532
def frozen_embedding_39_bits : FrozenBitFields := ⟨0, 124, 2160532⟩
def frozen_embedding_40 : frozen_binary32 := frozenMake 0 124 100566
def frozen_embedding_40_bits : FrozenBitFields := ⟨0, 124, 100566⟩
def frozen_embedding_41 : frozen_binary32 := frozenMake 1 121 4669156
def frozen_embedding_41_bits : FrozenBitFields := ⟨1, 121, 4669156⟩
def frozen_embedding_42 : frozen_binary32 := frozenMake 1 124 1471778
def frozen_embedding_42_bits : FrozenBitFields := ⟨1, 124, 1471778⟩
def frozen_embedding_43 : frozen_binary32 := frozenMake 1 120 2435857
def frozen_embedding_43_bits : FrozenBitFields := ⟨1, 120, 2435857⟩
def frozen_embedding_44 : frozen_binary32 := frozenMake 0 123 4183445
def frozen_embedding_44_bits : FrozenBitFields := ⟨0, 123, 4183445⟩
def frozen_embedding_45 : frozen_binary32 := frozenMake 0 123 839455
def frozen_embedding_45_bits : FrozenBitFields := ⟨0, 123, 839455⟩
def frozen_embedding_46 : frozen_binary32 := frozenMake 0 123 1054274
def frozen_embedding_46_bits : FrozenBitFields := ⟨0, 123, 1054274⟩
def frozen_embedding_47 : frozen_binary32 := frozenMake 0 124 2786495
def frozen_embedding_47_bits : FrozenBitFields := ⟨0, 124, 2786495⟩
def frozen_embedding_48 : frozen_binary32 := frozenMake 0 121 7688957
def frozen_embedding_48_bits : FrozenBitFields := ⟨0, 121, 7688957⟩
def frozen_embedding_49 : frozen_binary32 := frozenMake 0 123 1877686
def frozen_embedding_49_bits : FrozenBitFields := ⟨0, 123, 1877686⟩
def frozen_embedding_50 : frozen_binary32 := frozenMake 0 124 2535363
def frozen_embedding_50_bits : FrozenBitFields := ⟨0, 124, 2535363⟩
def frozen_embedding_51 : frozen_binary32 := frozenMake 1 118 3553136
def frozen_embedding_51_bits : FrozenBitFields := ⟨1, 118, 3553136⟩
def frozen_embedding_52 : frozen_binary32 := frozenMake 0 123 7302229
def frozen_embedding_52_bits : FrozenBitFields := ⟨0, 123, 7302229⟩
def frozen_embedding_53 : frozen_binary32 := frozenMake 1 121 2628688
def frozen_embedding_53_bits : FrozenBitFields := ⟨1, 121, 2628688⟩
def frozen_embedding_54 : frozen_binary32 := frozenMake 1 124 8021435
def frozen_embedding_54_bits : FrozenBitFields := ⟨1, 124, 8021435⟩
def frozen_embedding_55 : frozen_binary32 := frozenMake 0 122 8372337
def frozen_embedding_55_bits : FrozenBitFields := ⟨0, 122, 8372337⟩
def frozen_embedding_56 : frozen_binary32 := frozenMake 1 124 1235890
def frozen_embedding_56_bits : FrozenBitFields := ⟨1, 124, 1235890⟩
def frozen_embedding_57 : frozen_binary32 := frozenMake 1 124 1176480
def frozen_embedding_57_bits : FrozenBitFields := ⟨1, 124, 1176480⟩
def frozen_embedding_58 : frozen_binary32 := frozenMake 1 122 3874130
def frozen_embedding_58_bits : FrozenBitFields := ⟨1, 122, 3874130⟩
def frozen_embedding_59 : frozen_binary32 := frozenMake 1 123 1894818
def frozen_embedding_59_bits : FrozenBitFields := ⟨1, 123, 1894818⟩
def frozen_embedding_60 : frozen_binary32 := frozenMake 0 123 4643282
def frozen_embedding_60_bits : FrozenBitFields := ⟨0, 123, 4643282⟩
def frozen_embedding_61 : frozen_binary32 := frozenMake 1 120 1797825
def frozen_embedding_61_bits : FrozenBitFields := ⟨1, 120, 1797825⟩
def frozen_embedding_62 : frozen_binary32 := frozenMake 1 122 6634529
def frozen_embedding_62_bits : FrozenBitFields := ⟨1, 122, 6634529⟩
def frozen_embedding_63 : frozen_binary32 := frozenMake 1 124 3497855
def frozen_embedding_63_bits : FrozenBitFields := ⟨1, 124, 3497855⟩
def frozen_position_embedding_0 : frozen_binary32 := frozenMake 0 123 6834890
def frozen_position_embedding_0_bits : FrozenBitFields := ⟨0, 123, 6834890⟩
def frozen_position_embedding_1 : frozen_binary32 := frozenMake 1 123 2247292
def frozen_position_embedding_1_bits : FrozenBitFields := ⟨1, 123, 2247292⟩
def frozen_position_embedding_2 : frozen_binary32 := frozenMake 1 123 2685672
def frozen_position_embedding_2_bits : FrozenBitFields := ⟨1, 123, 2685672⟩
def frozen_position_embedding_3 : frozen_binary32 := frozenMake 0 122 5285549
def frozen_position_embedding_3_bits : FrozenBitFields := ⟨0, 122, 5285549⟩
def frozen_position_embedding_4 : frozen_binary32 := frozenMake 0 122 4003512
def frozen_position_embedding_4_bits : FrozenBitFields := ⟨0, 122, 4003512⟩
def frozen_position_embedding_5 : frozen_binary32 := frozenMake 1 119 1830391
def frozen_position_embedding_5_bits : FrozenBitFields := ⟨1, 119, 1830391⟩
def frozen_position_embedding_6 : frozen_binary32 := frozenMake 0 124 730047
def frozen_position_embedding_6_bits : FrozenBitFields := ⟨0, 124, 730047⟩
def frozen_position_embedding_7 : frozen_binary32 := frozenMake 0 120 2673853
def frozen_position_embedding_7_bits : FrozenBitFields := ⟨0, 120, 2673853⟩
def frozen_position_embedding_8 : frozen_binary32 := frozenMake 1 123 6999084
def frozen_position_embedding_8_bits : FrozenBitFields := ⟨1, 123, 6999084⟩
def frozen_position_embedding_9 : frozen_binary32 := frozenMake 0 121 6284948
def frozen_position_embedding_9_bits : FrozenBitFields := ⟨0, 121, 6284948⟩
def frozen_position_embedding_10 : frozen_binary32 := frozenMake 1 123 4579441
def frozen_position_embedding_10_bits : FrozenBitFields := ⟨1, 123, 4579441⟩
def frozen_position_embedding_11 : frozen_binary32 := frozenMake 0 122 4009761
def frozen_position_embedding_11_bits : FrozenBitFields := ⟨0, 122, 4009761⟩
def frozen_position_embedding_12 : frozen_binary32 := frozenMake 0 120 1475608
def frozen_position_embedding_12_bits : FrozenBitFields := ⟨0, 120, 1475608⟩
def frozen_position_embedding_13 : frozen_binary32 := frozenMake 1 123 5763516
def frozen_position_embedding_13_bits : FrozenBitFields := ⟨1, 123, 5763516⟩
def frozen_position_embedding_14 : frozen_binary32 := frozenMake 1 123 3497347
def frozen_position_embedding_14_bits : FrozenBitFields := ⟨1, 123, 3497347⟩
def frozen_position_embedding_15 : frozen_binary32 := frozenMake 1 121 8134189
def frozen_position_embedding_15_bits : FrozenBitFields := ⟨1, 121, 8134189⟩
def frozen_position_embedding_16 : frozen_binary32 := frozenMake 1 120 467460
def frozen_position_embedding_16_bits : FrozenBitFields := ⟨1, 120, 467460⟩
def frozen_position_embedding_17 : frozen_binary32 := frozenMake 1 122 5138390
def frozen_position_embedding_17_bits : FrozenBitFields := ⟨1, 122, 5138390⟩
def frozen_position_embedding_18 : frozen_binary32 := frozenMake 1 123 3487886
def frozen_position_embedding_18_bits : FrozenBitFields := ⟨1, 123, 3487886⟩
def frozen_position_embedding_19 : frozen_binary32 := frozenMake 0 124 624313
def frozen_position_embedding_19_bits : FrozenBitFields := ⟨0, 124, 624313⟩
def frozen_position_embedding_20 : frozen_binary32 := frozenMake 0 122 1050888
def frozen_position_embedding_20_bits : FrozenBitFields := ⟨0, 122, 1050888⟩
def frozen_position_embedding_21 : frozen_binary32 := frozenMake 0 123 2095765
def frozen_position_embedding_21_bits : FrozenBitFields := ⟨0, 123, 2095765⟩
def frozen_position_embedding_22 : frozen_binary32 := frozenMake 1 120 3784933
def frozen_position_embedding_22_bits : FrozenBitFields := ⟨1, 120, 3784933⟩
def frozen_position_embedding_23 : frozen_binary32 := frozenMake 0 120 1237648
def frozen_position_embedding_23_bits : FrozenBitFields := ⟨0, 120, 1237648⟩
def frozen_position_embedding_24 : frozen_binary32 := frozenMake 1 123 2240519
def frozen_position_embedding_24_bits : FrozenBitFields := ⟨1, 123, 2240519⟩
def frozen_position_embedding_25 : frozen_binary32 := frozenMake 0 123 1274269
def frozen_position_embedding_25_bits : FrozenBitFields := ⟨0, 123, 1274269⟩
def frozen_position_embedding_26 : frozen_binary32 := frozenMake 1 123 4570856
def frozen_position_embedding_26_bits : FrozenBitFields := ⟨1, 123, 4570856⟩
def frozen_position_embedding_27 : frozen_binary32 := frozenMake 0 122 5037279
def frozen_position_embedding_27_bits : FrozenBitFields := ⟨0, 122, 5037279⟩
def frozen_position_embedding_28 : frozen_binary32 := frozenMake 0 122 193764
def frozen_position_embedding_28_bits : FrozenBitFields := ⟨0, 122, 193764⟩
def frozen_position_embedding_29 : frozen_binary32 := frozenMake 0 120 6055250
def frozen_position_embedding_29_bits : FrozenBitFields := ⟨0, 120, 6055250⟩
def frozen_position_embedding_30 : frozen_binary32 := frozenMake 0 120 3334649
def frozen_position_embedding_30_bits : FrozenBitFields := ⟨0, 120, 3334649⟩
def frozen_position_embedding_31 : frozen_binary32 := frozenMake 0 122 5762943
def frozen_position_embedding_31_bits : FrozenBitFields := ⟨0, 122, 5762943⟩
def frozen_position_embedding_32 : frozen_binary32 := frozenMake 0 122 1232976
def frozen_position_embedding_32_bits : FrozenBitFields := ⟨0, 122, 1232976⟩
def frozen_position_embedding_33 : frozen_binary32 := frozenMake 1 120 1444170
def frozen_position_embedding_33_bits : FrozenBitFields := ⟨1, 120, 1444170⟩
def frozen_position_embedding_34 : frozen_binary32 := frozenMake 1 121 7889879
def frozen_position_embedding_34_bits : FrozenBitFields := ⟨1, 121, 7889879⟩
def frozen_position_embedding_35 : frozen_binary32 := frozenMake 0 122 6529135
def frozen_position_embedding_35_bits : FrozenBitFields := ⟨0, 122, 6529135⟩
def frozen_position_embedding_36 : frozen_binary32 := frozenMake 1 119 5154390
def frozen_position_embedding_36_bits : FrozenBitFields := ⟨1, 119, 5154390⟩
def frozen_position_embedding_37 : frozen_binary32 := frozenMake 1 122 4354395
def frozen_position_embedding_37_bits : FrozenBitFields := ⟨1, 122, 4354395⟩
def frozen_position_embedding_38 : frozen_binary32 := frozenMake 1 123 3441543
def frozen_position_embedding_38_bits : FrozenBitFields := ⟨1, 123, 3441543⟩
def frozen_position_embedding_39 : frozen_binary32 := frozenMake 1 122 209378
def frozen_position_embedding_39_bits : FrozenBitFields := ⟨1, 122, 209378⟩
def frozen_position_embedding_40 : frozen_binary32 := frozenMake 0 122 8086285
def frozen_position_embedding_40_bits : FrozenBitFields := ⟨0, 122, 8086285⟩
def frozen_position_embedding_41 : frozen_binary32 := frozenMake 0 122 6927812
def frozen_position_embedding_41_bits : FrozenBitFields := ⟨0, 122, 6927812⟩
def frozen_position_embedding_42 : frozen_binary32 := frozenMake 1 124 288524
def frozen_position_embedding_42_bits : FrozenBitFields := ⟨1, 124, 288524⟩
def frozen_position_embedding_43 : frozen_binary32 := frozenMake 1 122 5150856
def frozen_position_embedding_43_bits : FrozenBitFields := ⟨1, 122, 5150856⟩
def frozen_position_embedding_44 : frozen_binary32 := frozenMake 1 124 206157
def frozen_position_embedding_44_bits : FrozenBitFields := ⟨1, 124, 206157⟩
def frozen_position_embedding_45 : frozen_binary32 := frozenMake 1 122 782221
def frozen_position_embedding_45_bits : FrozenBitFields := ⟨1, 122, 782221⟩
def frozen_position_embedding_46 : frozen_binary32 := frozenMake 0 122 5529046
def frozen_position_embedding_46_bits : FrozenBitFields := ⟨0, 122, 5529046⟩
def frozen_position_embedding_47 : frozen_binary32 := frozenMake 1 123 5084929
def frozen_position_embedding_47_bits : FrozenBitFields := ⟨1, 123, 5084929⟩
def frozen_position_embedding_48 : frozen_binary32 := frozenMake 0 123 3164351
def frozen_position_embedding_48_bits : FrozenBitFields := ⟨0, 123, 3164351⟩
def frozen_position_embedding_49 : frozen_binary32 := frozenMake 1 122 4692803
def frozen_position_embedding_49_bits : FrozenBitFields := ⟨1, 122, 4692803⟩
def frozen_position_embedding_50 : frozen_binary32 := frozenMake 1 120 4352345
def frozen_position_embedding_50_bits : FrozenBitFields := ⟨1, 120, 4352345⟩
def frozen_position_embedding_51 : frozen_binary32 := frozenMake 0 119 3797983
def frozen_position_embedding_51_bits : FrozenBitFields := ⟨0, 119, 3797983⟩
def frozen_position_embedding_52 : frozen_binary32 := frozenMake 1 123 5906369
def frozen_position_embedding_52_bits : FrozenBitFields := ⟨1, 123, 5906369⟩
def frozen_position_embedding_53 : frozen_binary32 := frozenMake 1 123 3724803
def frozen_position_embedding_53_bits : FrozenBitFields := ⟨1, 123, 3724803⟩
def frozen_position_embedding_54 : frozen_binary32 := frozenMake 1 121 4157412
def frozen_position_embedding_54_bits : FrozenBitFields := ⟨1, 121, 4157412⟩
def frozen_position_embedding_55 : frozen_binary32 := frozenMake 1 121 6380686
def frozen_position_embedding_55_bits : FrozenBitFields := ⟨1, 121, 6380686⟩
def frozen_position_embedding_56 : frozen_binary32 := frozenMake 0 124 826840
def frozen_position_embedding_56_bits : FrozenBitFields := ⟨0, 124, 826840⟩
def frozen_position_embedding_57 : frozen_binary32 := frozenMake 0 123 6550819
def frozen_position_embedding_57_bits : FrozenBitFields := ⟨0, 123, 6550819⟩
def frozen_position_embedding_58 : frozen_binary32 := frozenMake 0 123 1056291
def frozen_position_embedding_58_bits : FrozenBitFields := ⟨0, 123, 1056291⟩
def frozen_position_embedding_59 : frozen_binary32 := frozenMake 1 120 3879974
def frozen_position_embedding_59_bits : FrozenBitFields := ⟨1, 120, 3879974⟩
def frozen_position_embedding_60 : frozen_binary32 := frozenMake 0 122 5649743
def frozen_position_embedding_60_bits : FrozenBitFields := ⟨0, 122, 5649743⟩
def frozen_position_embedding_61 : frozen_binary32 := frozenMake 0 123 2720454
def frozen_position_embedding_61_bits : FrozenBitFields := ⟨0, 123, 2720454⟩
def frozen_position_embedding_62 : frozen_binary32 := frozenMake 0 124 82375
def frozen_position_embedding_62_bits : FrozenBitFields := ⟨0, 124, 82375⟩
def frozen_position_embedding_63 : frozen_binary32 := frozenMake 0 123 184526
def frozen_position_embedding_63_bits : FrozenBitFields := ⟨0, 123, 184526⟩
def frozen_input_activation_0 : frozen_binary32 := frozenMake 0 124 5954621
def frozen_input_activation_0_bits : FrozenBitFields := ⟨0, 124, 5954621⟩
def frozen_input_activation_1 : frozen_binary32 := frozenMake 1 124 2814668
def frozen_input_activation_1_bits : FrozenBitFields := ⟨1, 124, 2814668⟩
def frozen_input_activation_2 : frozen_binary32 := frozenMake 1 124 5088346
def frozen_input_activation_2_bits : FrozenBitFields := ⟨1, 124, 5088346⟩
def frozen_input_activation_3 : frozen_binary32 := frozenMake 0 122 4988295
def frozen_input_activation_3_bits : FrozenBitFields := ⟨0, 122, 4988295⟩
def frozen_input_activation_4 : frozen_binary32 := frozenMake 0 123 4355862
def frozen_input_activation_4_bits : FrozenBitFields := ⟨0, 123, 4355862⟩
def frozen_input_activation_5 : frozen_binary32 := frozenMake 1 122 7139934
def frozen_input_activation_5_bits : FrozenBitFields := ⟨1, 122, 7139934⟩
def frozen_input_activation_6 : frozen_binary32 := frozenMake 0 123 7769643
def frozen_input_activation_6_bits : FrozenBitFields := ⟨0, 123, 7769643⟩
def frozen_input_activation_7 : frozen_binary32 := frozenMake 1 123 7313058
def frozen_input_activation_7_bits : FrozenBitFields := ⟨1, 123, 7313058⟩
def frozen_input_activation_8 : frozen_binary32 := frozenMake 1 124 7133
def frozen_input_activation_8_bits : FrozenBitFields := ⟨1, 124, 7133⟩
def frozen_input_activation_9 : frozen_binary32 := frozenMake 0 121 1704704
def frozen_input_activation_9_bits : FrozenBitFields := ⟨0, 121, 1704704⟩
def frozen_input_activation_10 : frozen_binary32 := frozenMake 1 121 1514088
def frozen_input_activation_10_bits : FrozenBitFields := ⟨1, 121, 1514088⟩
def frozen_input_activation_11 : frozen_binary32 := frozenMake 0 123 5172887
def frozen_input_activation_11_bits : FrozenBitFields := ⟨0, 123, 5172887⟩
def frozen_input_activation_12 : frozen_binary32 := frozenMake 0 125 3106044
def frozen_input_activation_12_bits : FrozenBitFields := ⟨0, 125, 3106044⟩
def frozen_input_activation_13 : frozen_binary32 := frozenMake 1 125 2109316
def frozen_input_activation_13_bits : FrozenBitFields := ⟨1, 125, 2109316⟩
def frozen_input_activation_14 : frozen_binary32 := frozenMake 1 124 6403510
def frozen_input_activation_14_bits : FrozenBitFields := ⟨1, 124, 6403510⟩
def frozen_input_activation_15 : frozen_binary32 := frozenMake 1 123 6481247
def frozen_input_activation_15_bits : FrozenBitFields := ⟨1, 123, 6481247⟩
def frozen_input_activation_16 : frozen_binary32 := frozenMake 1 124 903983
def frozen_input_activation_16_bits : FrozenBitFields := ⟨1, 124, 903983⟩
def frozen_input_activation_17 : frozen_binary32 := frozenMake 1 124 6673156
def frozen_input_activation_17_bits : FrozenBitFields := ⟨1, 124, 6673156⟩
def frozen_input_activation_18 : frozen_binary32 := frozenMake 1 124 2239966
def frozen_input_activation_18_bits : FrozenBitFields := ⟨1, 124, 2239966⟩
def frozen_input_activation_19 : frozen_binary32 := frozenMake 0 124 3550084
def frozen_input_activation_19_bits : FrozenBitFields := ⟨0, 124, 3550084⟩
def frozen_input_activation_20 : frozen_binary32 := frozenMake 0 125 1041352
def frozen_input_activation_20_bits : FrozenBitFields := ⟨0, 125, 1041352⟩
def frozen_input_activation_21 : frozen_binary32 := frozenMake 0 122 3603210
def frozen_input_activation_21_bits : FrozenBitFields := ⟨0, 122, 3603210⟩
def frozen_input_activation_22 : frozen_binary32 := frozenMake 1 122 6721245
def frozen_input_activation_22_bits : FrozenBitFields := ⟨1, 122, 6721245⟩
def frozen_input_activation_23 : frozen_binary32 := frozenMake 1 123 7884284
def frozen_input_activation_23_bits : FrozenBitFields := ⟨1, 123, 7884284⟩
def frozen_input_activation_24 : frozen_binary32 := frozenMake 1 121 1393382
def frozen_input_activation_24_bits : FrozenBitFields := ⟨1, 121, 1393382⟩
def frozen_input_activation_25 : frozen_binary32 := frozenMake 0 120 2522268
def frozen_input_activation_25_bits : FrozenBitFields := ⟨0, 120, 2522268⟩
def frozen_input_activation_26 : frozen_binary32 := frozenMake 1 124 7118256
def frozen_input_activation_26_bits : FrozenBitFields := ⟨1, 124, 7118256⟩
def frozen_input_activation_27 : frozen_binary32 := frozenMake 0 124 7134102
def frozen_input_activation_27_bits : FrozenBitFields := ⟨0, 124, 7134102⟩
def frozen_input_activation_28 : frozen_binary32 := frozenMake 0 125 1816882
def frozen_input_activation_28_bits : FrozenBitFields := ⟨0, 125, 1816882⟩
def frozen_input_activation_29 : frozen_binary32 := frozenMake 1 123 1164429
def frozen_input_activation_29_bits : FrozenBitFields := ⟨1, 123, 1164429⟩
def frozen_input_activation_30 : frozen_binary32 := frozenMake 1 118 7844316
def frozen_input_activation_30_bits : FrozenBitFields := ⟨1, 118, 7844316⟩
def frozen_input_activation_31 : frozen_binary32 := frozenMake 1 123 3181024
def frozen_input_activation_31_bits : FrozenBitFields := ⟨1, 123, 3181024⟩
def frozen_input_activation_32 : frozen_binary32 := frozenMake 1 123 212173
def frozen_input_activation_32_bits : FrozenBitFields := ⟨1, 123, 212173⟩
def frozen_input_activation_33 : frozen_binary32 := frozenMake 1 124 779620
def frozen_input_activation_33_bits : FrozenBitFields := ⟨1, 124, 779620⟩
def frozen_input_activation_34 : frozen_binary32 := frozenMake 0 124 816691
def frozen_input_activation_34_bits : FrozenBitFields := ⟨0, 124, 816691⟩
def frozen_input_activation_35 : frozen_binary32 := frozenMake 0 124 285891
def frozen_input_activation_35_bits : FrozenBitFields := ⟨0, 124, 285891⟩
def frozen_input_activation_36 : frozen_binary32 := frozenMake 0 123 6928434
def frozen_input_activation_36_bits : FrozenBitFields := ⟨0, 123, 6928434⟩
def frozen_input_activation_37 : frozen_binary32 := frozenMake 1 123 3305828
def frozen_input_activation_37_bits : FrozenBitFields := ⟨1, 123, 3305828⟩
def frozen_input_activation_38 : frozen_binary32 := frozenMake 1 124 3119748
def frozen_input_activation_38_bits : FrozenBitFields := ⟨1, 124, 3119748⟩
def frozen_input_activation_39 : frozen_binary32 := frozenMake 0 124 11036
def frozen_input_activation_39_bits : FrozenBitFields := ⟨0, 124, 11036⟩
def frozen_input_activation_40 : frozen_binary32 := frozenMake 0 124 4219289
def frozen_input_activation_40_bits : FrozenBitFields := ⟨0, 124, 4219289⟩
def frozen_input_activation_41 : frozen_binary32 := frozenMake 0 122 398930
def frozen_input_activation_41_bits : FrozenBitFields := ⟨0, 122, 398930⟩
def frozen_input_activation_42 : frozen_binary32 := frozenMake 1 125 880151
def frozen_input_activation_42_bits : FrozenBitFields := ⟨1, 125, 880151⟩
def frozen_input_activation_43 : frozen_binary32 := frozenMake 1 122 7856972
def frozen_input_activation_43_bits : FrozenBitFields := ⟨1, 122, 7856972⟩
def frozen_input_activation_44 : frozen_binary32 := frozenMake 1 122 846346
def frozen_input_activation_44_bits : FrozenBitFields := ⟨1, 122, 846346⟩
def frozen_input_activation_45 : frozen_binary32 := frozenMake 0 122 896689
def frozen_input_activation_45_bits : FrozenBitFields := ⟨0, 122, 896689⟩
def frozen_input_activation_46 : frozen_binary32 := frozenMake 0 123 8013101
def frozen_input_activation_46_bits : FrozenBitFields := ⟨0, 123, 8013101⟩
def frozen_input_activation_47 : frozen_binary32 := frozenMake 0 123 488061
def frozen_input_activation_47_bits : FrozenBitFields := ⟨0, 123, 488061⟩
def frozen_input_activation_48 : frozen_binary32 := frozenMake 0 123 7183742
def frozen_input_activation_48_bits : FrozenBitFields := ⟨0, 123, 7183742⟩
def frozen_input_activation_49 : frozen_binary32 := frozenMake 0 121 6513746
def frozen_input_activation_49_bits : FrozenBitFields := ⟨0, 121, 6513746⟩
def frozen_input_activation_50 : frozen_binary32 := frozenMake 0 124 1739053
def frozen_input_activation_50_bits : FrozenBitFields := ⟨0, 124, 1739053⟩
def frozen_input_activation_51 : frozen_binary32 := frozenMake 0 118 4042830
def frozen_input_activation_51_bits : FrozenBitFields := ⟨0, 118, 4042830⟩
def frozen_input_activation_52 : frozen_binary32 := frozenMake 0 120 2778272
def frozen_input_activation_52_bits : FrozenBitFields := ⟨0, 120, 2778272⟩
def frozen_input_activation_53 : frozen_binary32 := frozenMake 1 123 6479127
def frozen_input_activation_53_bits : FrozenBitFields := ⟨1, 123, 6479127⟩
def frozen_input_activation_54 : frozen_binary32 := frozenMake 1 125 600540
def frozen_input_activation_54_bits : FrozenBitFields := ⟨1, 125, 600540⟩
def frozen_input_activation_55 : frozen_binary32 := frozenMake 0 122 987690
def frozen_input_activation_55_bits : FrozenBitFields := ⟨0, 122, 987690⟩
def frozen_input_activation_56 : frozen_binary32 := frozenMake 1 119 4700992
def frozen_input_activation_56_bits : FrozenBitFields := ⟨1, 119, 4700992⟩
def frozen_input_activation_57 : frozen_binary32 := frozenMake 1 121 8374388
def frozen_input_activation_57_bits : FrozenBitFields := ⟨1, 121, 8374388⟩
def frozen_input_activation_58 : frozen_binary32 := frozenMake 0 121 4865512
def frozen_input_activation_58_bits : FrozenBitFields := ⟨0, 121, 4865512⟩
def frozen_input_activation_59 : frozen_binary32 := frozenMake 1 123 3428391
def frozen_input_activation_59_bits : FrozenBitFields := ⟨1, 123, 3428391⟩
def frozen_input_activation_60 : frozen_binary32 := frozenMake 0 124 1636925
def frozen_input_activation_60_bits : FrozenBitFields := ⟨0, 124, 1636925⟩
def frozen_input_activation_61 : frozen_binary32 := frozenMake 0 123 1447150
def frozen_input_activation_61_bits : FrozenBitFields := ⟨0, 123, 1447150⟩
def frozen_input_activation_62 : frozen_binary32 := frozenMake 0 123 1041790
def frozen_input_activation_62_bits : FrozenBitFields := ⟨0, 123, 1041790⟩
def frozen_input_activation_63 : frozen_binary32 := frozenMake 1 123 6811184
def frozen_input_activation_63_bits : FrozenBitFields := ⟨1, 123, 6811184⟩
def frozen_kernel_0_0 : frozen_binary32 := frozenMake 1 118 5224699
def frozen_kernel_0_0_bits : FrozenBitFields := ⟨1, 118, 5224699⟩
def frozen_kernel_0_1 : frozen_binary32 := frozenMake 0 122 3128469
def frozen_kernel_0_1_bits : FrozenBitFields := ⟨0, 122, 3128469⟩
def frozen_kernel_0_2 : frozen_binary32 := frozenMake 0 121 7637911
def frozen_kernel_0_2_bits : FrozenBitFields := ⟨0, 121, 7637911⟩
def frozen_kernel_0_3 : frozen_binary32 := frozenMake 1 119 8381415
def frozen_kernel_0_3_bits : FrozenBitFields := ⟨1, 119, 8381415⟩
def frozen_kernel_0_4 : frozen_binary32 := frozenMake 0 120 6738071
def frozen_kernel_0_4_bits : FrozenBitFields := ⟨0, 120, 6738071⟩
def frozen_kernel_0_5 : frozen_binary32 := frozenMake 0 121 3087089
def frozen_kernel_0_5_bits : FrozenBitFields := ⟨0, 121, 3087089⟩
def frozen_kernel_0_6 : frozen_binary32 := frozenMake 1 121 299807
def frozen_kernel_0_6_bits : FrozenBitFields := ⟨1, 121, 299807⟩
def frozen_kernel_0_7 : frozen_binary32 := frozenMake 1 119 2209599
def frozen_kernel_0_7_bits : FrozenBitFields := ⟨1, 119, 2209599⟩
def frozen_kernel_0_8 : frozen_binary32 := frozenMake 0 122 4026999
def frozen_kernel_0_8_bits : FrozenBitFields := ⟨0, 122, 4026999⟩
def frozen_kernel_0_9 : frozen_binary32 := frozenMake 0 120 2430844
def frozen_kernel_0_9_bits : FrozenBitFields := ⟨0, 120, 2430844⟩
def frozen_kernel_0_10 : frozen_binary32 := frozenMake 0 121 3687498
def frozen_kernel_0_10_bits : FrozenBitFields := ⟨0, 121, 3687498⟩
def frozen_kernel_0_11 : frozen_binary32 := frozenMake 0 122 554361
def frozen_kernel_0_11_bits : FrozenBitFields := ⟨0, 122, 554361⟩
def frozen_kernel_0_12 : frozen_binary32 := frozenMake 1 122 5458651
def frozen_kernel_0_12_bits : FrozenBitFields := ⟨1, 122, 5458651⟩
def frozen_kernel_0_13 : frozen_binary32 := frozenMake 1 120 4778072
def frozen_kernel_0_13_bits : FrozenBitFields := ⟨1, 120, 4778072⟩
def frozen_kernel_0_14 : frozen_binary32 := frozenMake 0 121 1407349
def frozen_kernel_0_14_bits : FrozenBitFields := ⟨0, 121, 1407349⟩
def frozen_kernel_0_15 : frozen_binary32 := frozenMake 1 121 4170002
def frozen_kernel_0_15_bits : FrozenBitFields := ⟨1, 121, 4170002⟩
def frozen_kernel_0_16 : frozen_binary32 := frozenMake 1 121 1869772
def frozen_kernel_0_16_bits : FrozenBitFields := ⟨1, 121, 1869772⟩
def frozen_kernel_0_17 : frozen_binary32 := frozenMake 1 121 3281070
def frozen_kernel_0_17_bits : FrozenBitFields := ⟨1, 121, 3281070⟩
def frozen_kernel_0_18 : frozen_binary32 := frozenMake 1 122 1758620
def frozen_kernel_0_18_bits : FrozenBitFields := ⟨1, 122, 1758620⟩
def frozen_kernel_0_19 : frozen_binary32 := frozenMake 0 118 686048
def frozen_kernel_0_19_bits : FrozenBitFields := ⟨0, 118, 686048⟩
def frozen_kernel_0_20 : frozen_binary32 := frozenMake 0 121 3743167
def frozen_kernel_0_20_bits : FrozenBitFields := ⟨0, 121, 3743167⟩
def frozen_kernel_0_21 : frozen_binary32 := frozenMake 1 119 2418418
def frozen_kernel_0_21_bits : FrozenBitFields := ⟨1, 119, 2418418⟩
def frozen_kernel_0_22 : frozen_binary32 := frozenMake 0 119 2015393
def frozen_kernel_0_22_bits : FrozenBitFields := ⟨0, 119, 2015393⟩
def frozen_kernel_0_23 : frozen_binary32 := frozenMake 0 119 703489
def frozen_kernel_0_23_bits : FrozenBitFields := ⟨0, 119, 703489⟩
def frozen_kernel_0_24 : frozen_binary32 := frozenMake 0 122 1645734
def frozen_kernel_0_24_bits : FrozenBitFields := ⟨0, 122, 1645734⟩
def frozen_kernel_0_25 : frozen_binary32 := frozenMake 0 118 5996730
def frozen_kernel_0_25_bits : FrozenBitFields := ⟨0, 118, 5996730⟩
def frozen_kernel_0_26 : frozen_binary32 := frozenMake 1 121 1822788
def frozen_kernel_0_26_bits : FrozenBitFields := ⟨1, 121, 1822788⟩
def frozen_kernel_0_27 : frozen_binary32 := frozenMake 0 121 1277057
def frozen_kernel_0_27_bits : FrozenBitFields := ⟨0, 121, 1277057⟩
def frozen_kernel_0_28 : frozen_binary32 := frozenMake 1 122 1427378
def frozen_kernel_0_28_bits : FrozenBitFields := ⟨1, 122, 1427378⟩
def frozen_kernel_0_29 : frozen_binary32 := frozenMake 1 119 3639482
def frozen_kernel_0_29_bits : FrozenBitFields := ⟨1, 119, 3639482⟩
def frozen_kernel_0_30 : frozen_binary32 := frozenMake 0 119 1348070
def frozen_kernel_0_30_bits : FrozenBitFields := ⟨0, 119, 1348070⟩
def frozen_kernel_0_31 : frozen_binary32 := frozenMake 1 123 288156
def frozen_kernel_0_31_bits : FrozenBitFields := ⟨1, 123, 288156⟩
def frozen_kernel_0_32 : frozen_binary32 := frozenMake 0 123 90798
def frozen_kernel_0_32_bits : FrozenBitFields := ⟨0, 123, 90798⟩
def frozen_kernel_0_33 : frozen_binary32 := frozenMake 1 120 4808610
def frozen_kernel_0_33_bits : FrozenBitFields := ⟨1, 120, 4808610⟩
def frozen_kernel_0_34 : frozen_binary32 := frozenMake 1 121 1525205
def frozen_kernel_0_34_bits : FrozenBitFields := ⟨1, 121, 1525205⟩
def frozen_kernel_0_35 : frozen_binary32 := frozenMake 1 121 7194731
def frozen_kernel_0_35_bits : FrozenBitFields := ⟨1, 121, 7194731⟩
def frozen_kernel_0_36 : frozen_binary32 := frozenMake 1 120 4369203
def frozen_kernel_0_36_bits : FrozenBitFields := ⟨1, 120, 4369203⟩
def frozen_kernel_0_37 : frozen_binary32 := frozenMake 0 116 2958092
def frozen_kernel_0_37_bits : FrozenBitFields := ⟨0, 116, 2958092⟩
def frozen_kernel_0_38 : frozen_binary32 := frozenMake 0 118 1208593
def frozen_kernel_0_38_bits : FrozenBitFields := ⟨0, 118, 1208593⟩
def frozen_kernel_0_39 : frozen_binary32 := frozenMake 1 121 1599792
def frozen_kernel_0_39_bits : FrozenBitFields := ⟨1, 121, 1599792⟩
def frozen_kernel_0_40 : frozen_binary32 := frozenMake 1 118 2806924
def frozen_kernel_0_40_bits : FrozenBitFields := ⟨1, 118, 2806924⟩
def frozen_kernel_0_41 : frozen_binary32 := frozenMake 0 122 5118147
def frozen_kernel_0_41_bits : FrozenBitFields := ⟨0, 122, 5118147⟩
def frozen_kernel_0_42 : frozen_binary32 := frozenMake 0 123 1905657
def frozen_kernel_0_42_bits : FrozenBitFields := ⟨0, 123, 1905657⟩
def frozen_kernel_0_43 : frozen_binary32 := frozenMake 0 122 855751
def frozen_kernel_0_43_bits : FrozenBitFields := ⟨0, 122, 855751⟩
def frozen_kernel_0_44 : frozen_binary32 := frozenMake 1 122 4038769
def frozen_kernel_0_44_bits : FrozenBitFields := ⟨1, 122, 4038769⟩
def frozen_kernel_0_45 : frozen_binary32 := frozenMake 0 122 3288804
def frozen_kernel_0_45_bits : FrozenBitFields := ⟨0, 122, 3288804⟩
def frozen_kernel_0_46 : frozen_binary32 := frozenMake 1 122 3075038
def frozen_kernel_0_46_bits : FrozenBitFields := ⟨1, 122, 3075038⟩
def frozen_kernel_0_47 : frozen_binary32 := frozenMake 0 122 38155
def frozen_kernel_0_47_bits : FrozenBitFields := ⟨0, 122, 38155⟩
def frozen_kernel_0_48 : frozen_binary32 := frozenMake 0 121 4047975
def frozen_kernel_0_48_bits : FrozenBitFields := ⟨0, 121, 4047975⟩
def frozen_kernel_0_49 : frozen_binary32 := frozenMake 1 122 5610822
def frozen_kernel_0_49_bits : FrozenBitFields := ⟨1, 122, 5610822⟩
def frozen_kernel_0_50 : frozen_binary32 := frozenMake 0 122 6642879
def frozen_kernel_0_50_bits : FrozenBitFields := ⟨0, 122, 6642879⟩
def frozen_kernel_0_51 : frozen_binary32 := frozenMake 1 122 4702632
def frozen_kernel_0_51_bits : FrozenBitFields := ⟨1, 122, 4702632⟩
def frozen_kernel_0_52 : frozen_binary32 := frozenMake 0 120 1051091
def frozen_kernel_0_52_bits : FrozenBitFields := ⟨0, 120, 1051091⟩
def frozen_kernel_0_53 : frozen_binary32 := frozenMake 1 118 1249983
def frozen_kernel_0_53_bits : FrozenBitFields := ⟨1, 118, 1249983⟩
def frozen_kernel_0_54 : frozen_binary32 := frozenMake 0 120 3830612
def frozen_kernel_0_54_bits : FrozenBitFields := ⟨0, 120, 3830612⟩
def frozen_kernel_0_55 : frozen_binary32 := frozenMake 0 121 5080758
def frozen_kernel_0_55_bits : FrozenBitFields := ⟨0, 121, 5080758⟩
def frozen_kernel_0_56 : frozen_binary32 := frozenMake 0 122 5890291
def frozen_kernel_0_56_bits : FrozenBitFields := ⟨0, 122, 5890291⟩
def frozen_kernel_0_57 : frozen_binary32 := frozenMake 1 121 7593629
def frozen_kernel_0_57_bits : FrozenBitFields := ⟨1, 121, 7593629⟩
def frozen_kernel_0_58 : frozen_binary32 := frozenMake 1 123 251443
def frozen_kernel_0_58_bits : FrozenBitFields := ⟨1, 123, 251443⟩
def frozen_kernel_0_59 : frozen_binary32 := frozenMake 0 123 2891762
def frozen_kernel_0_59_bits : FrozenBitFields := ⟨0, 123, 2891762⟩
def frozen_kernel_0_60 : frozen_binary32 := frozenMake 1 122 5342669
def frozen_kernel_0_60_bits : FrozenBitFields := ⟨1, 122, 5342669⟩
def frozen_kernel_0_61 : frozen_binary32 := frozenMake 1 121 7770590
def frozen_kernel_0_61_bits : FrozenBitFields := ⟨1, 121, 7770590⟩
def frozen_kernel_0_62 : frozen_binary32 := frozenMake 1 122 963613
def frozen_kernel_0_62_bits : FrozenBitFields := ⟨1, 122, 963613⟩
def frozen_kernel_0_63 : frozen_binary32 := frozenMake 1 118 2563801
def frozen_kernel_0_63_bits : FrozenBitFields := ⟨1, 118, 2563801⟩
def frozen_kernel_1_0 : frozen_binary32 := frozenMake 0 123 1354358
def frozen_kernel_1_0_bits : FrozenBitFields := ⟨0, 123, 1354358⟩
def frozen_kernel_1_1 : frozen_binary32 := frozenMake 1 123 1197167
def frozen_kernel_1_1_bits : FrozenBitFields := ⟨1, 123, 1197167⟩
def frozen_kernel_1_2 : frozen_binary32 := frozenMake 1 121 7222080
def frozen_kernel_1_2_bits : FrozenBitFields := ⟨1, 121, 7222080⟩
def frozen_kernel_1_3 : frozen_binary32 := frozenMake 0 123 1486014
def frozen_kernel_1_3_bits : FrozenBitFields := ⟨0, 123, 1486014⟩
def frozen_kernel_1_4 : frozen_binary32 := frozenMake 0 123 4285308
def frozen_kernel_1_4_bits : FrozenBitFields := ⟨0, 123, 4285308⟩
def frozen_kernel_1_5 : frozen_binary32 := frozenMake 0 122 267822
def frozen_kernel_1_5_bits : FrozenBitFields := ⟨0, 122, 267822⟩
def frozen_kernel_1_6 : frozen_binary32 := frozenMake 0 122 8034609
def frozen_kernel_1_6_bits : FrozenBitFields := ⟨0, 122, 8034609⟩
def frozen_kernel_1_7 : frozen_binary32 := frozenMake 1 122 77048
def frozen_kernel_1_7_bits : FrozenBitFields := ⟨1, 122, 77048⟩
def frozen_kernel_1_8 : frozen_binary32 := frozenMake 0 122 1891076
def frozen_kernel_1_8_bits : FrozenBitFields := ⟨0, 122, 1891076⟩
def frozen_kernel_1_9 : frozen_binary32 := frozenMake 0 122 5335006
def frozen_kernel_1_9_bits : FrozenBitFields := ⟨0, 122, 5335006⟩
def frozen_kernel_1_10 : frozen_binary32 := frozenMake 1 123 264536
def frozen_kernel_1_10_bits : FrozenBitFields := ⟨1, 123, 264536⟩
def frozen_kernel_1_11 : frozen_binary32 := frozenMake 0 121 4227652
def frozen_kernel_1_11_bits : FrozenBitFields := ⟨0, 121, 4227652⟩
def frozen_kernel_1_12 : frozen_binary32 := frozenMake 1 124 533454
def frozen_kernel_1_12_bits : FrozenBitFields := ⟨1, 124, 533454⟩
def frozen_kernel_1_13 : frozen_binary32 := frozenMake 1 123 4842360
def frozen_kernel_1_13_bits : FrozenBitFields := ⟨1, 123, 4842360⟩
def frozen_kernel_1_14 : frozen_binary32 := frozenMake 1 122 570502
def frozen_kernel_1_14_bits : FrozenBitFields := ⟨1, 122, 570502⟩
def frozen_kernel_1_15 : frozen_binary32 := frozenMake 1 123 2323780
def frozen_kernel_1_15_bits : FrozenBitFields := ⟨1, 123, 2323780⟩
def frozen_kernel_1_16 : frozen_binary32 := frozenMake 1 119 5276935
def frozen_kernel_1_16_bits : FrozenBitFields := ⟨1, 119, 5276935⟩
def frozen_kernel_1_17 : frozen_binary32 := frozenMake 1 122 1919277
def frozen_kernel_1_17_bits : FrozenBitFields := ⟨1, 122, 1919277⟩
def frozen_kernel_1_18 : frozen_binary32 := frozenMake 0 120 7240382
def frozen_kernel_1_18_bits : FrozenBitFields := ⟨0, 120, 7240382⟩
def frozen_kernel_1_19 : frozen_binary32 := frozenMake 1 122 8138915
def frozen_kernel_1_19_bits : FrozenBitFields := ⟨1, 122, 8138915⟩
def frozen_kernel_1_20 : frozen_binary32 := frozenMake 0 123 536248
def frozen_kernel_1_20_bits : FrozenBitFields := ⟨0, 123, 536248⟩
def frozen_kernel_1_21 : frozen_binary32 := frozenMake 0 124 947364
def frozen_kernel_1_21_bits : FrozenBitFields := ⟨0, 124, 947364⟩
def frozen_kernel_1_22 : frozen_binary32 := frozenMake 0 122 5161997
def frozen_kernel_1_22_bits : FrozenBitFields := ⟨0, 122, 5161997⟩
def frozen_kernel_1_23 : frozen_binary32 := frozenMake 1 120 91511
def frozen_kernel_1_23_bits : FrozenBitFields := ⟨1, 120, 91511⟩
def frozen_kernel_1_24 : frozen_binary32 := frozenMake 0 122 2762327
def frozen_kernel_1_24_bits : FrozenBitFields := ⟨0, 122, 2762327⟩
def frozen_kernel_1_25 : frozen_binary32 := frozenMake 1 122 920367
def frozen_kernel_1_25_bits : FrozenBitFields := ⟨1, 122, 920367⟩
def frozen_kernel_1_26 : frozen_binary32 := frozenMake 0 122 3004765
def frozen_kernel_1_26_bits : FrozenBitFields := ⟨0, 122, 3004765⟩
def frozen_kernel_1_27 : frozen_binary32 := frozenMake 0 123 2722710
def frozen_kernel_1_27_bits : FrozenBitFields := ⟨0, 123, 2722710⟩
def frozen_kernel_1_28 : frozen_binary32 := frozenMake 0 122 1850932
def frozen_kernel_1_28_bits : FrozenBitFields := ⟨0, 122, 1850932⟩
def frozen_kernel_1_29 : frozen_binary32 := frozenMake 1 122 146614
def frozen_kernel_1_29_bits : FrozenBitFields := ⟨1, 122, 146614⟩
def frozen_kernel_1_30 : frozen_binary32 := frozenMake 1 122 8271729
def frozen_kernel_1_30_bits : FrozenBitFields := ⟨1, 122, 8271729⟩
def frozen_kernel_1_31 : frozen_binary32 := frozenMake 1 122 5391442
def frozen_kernel_1_31_bits : FrozenBitFields := ⟨1, 122, 5391442⟩
def frozen_kernel_1_32 : frozen_binary32 := frozenMake 0 121 7748470
def frozen_kernel_1_32_bits : FrozenBitFields := ⟨0, 121, 7748470⟩
def frozen_kernel_1_33 : frozen_binary32 := frozenMake 0 122 7073732
def frozen_kernel_1_33_bits : FrozenBitFields := ⟨0, 122, 7073732⟩
def frozen_kernel_1_34 : frozen_binary32 := frozenMake 0 121 7899362
def frozen_kernel_1_34_bits : FrozenBitFields := ⟨0, 121, 7899362⟩
def frozen_kernel_1_35 : frozen_binary32 := frozenMake 0 120 2694524
def frozen_kernel_1_35_bits : FrozenBitFields := ⟨0, 120, 2694524⟩
def frozen_kernel_1_36 : frozen_binary32 := frozenMake 1 121 1430455
def frozen_kernel_1_36_bits : FrozenBitFields := ⟨1, 121, 1430455⟩
def frozen_kernel_1_37 : frozen_binary32 := frozenMake 1 119 4416350
def frozen_kernel_1_37_bits : FrozenBitFields := ⟨1, 119, 4416350⟩
def frozen_kernel_1_38 : frozen_binary32 := frozenMake 0 122 1588126
def frozen_kernel_1_38_bits : FrozenBitFields := ⟨0, 122, 1588126⟩
def frozen_kernel_1_39 : frozen_binary32 := frozenMake 1 119 3771550
def frozen_kernel_1_39_bits : FrozenBitFields := ⟨1, 119, 3771550⟩
def frozen_kernel_1_40 : frozen_binary32 := frozenMake 0 122 6072260
def frozen_kernel_1_40_bits : FrozenBitFields := ⟨0, 122, 6072260⟩
def frozen_kernel_1_41 : frozen_binary32 := frozenMake 1 123 2120345
def frozen_kernel_1_41_bits : FrozenBitFields := ⟨1, 123, 2120345⟩
def frozen_kernel_1_42 : frozen_binary32 := frozenMake 0 122 3995011
def frozen_kernel_1_42_bits : FrozenBitFields := ⟨0, 122, 3995011⟩
def frozen_kernel_1_43 : frozen_binary32 := frozenMake 0 121 7885399
def frozen_kernel_1_43_bits : FrozenBitFields := ⟨0, 121, 7885399⟩
def frozen_kernel_1_44 : frozen_binary32 := frozenMake 0 120 3268294
def frozen_kernel_1_44_bits : FrozenBitFields := ⟨0, 120, 3268294⟩
def frozen_kernel_1_45 : frozen_binary32 := frozenMake 1 120 309075
def frozen_kernel_1_45_bits : FrozenBitFields := ⟨1, 120, 309075⟩
def frozen_kernel_1_46 : frozen_binary32 := frozenMake 0 120 8248022
def frozen_kernel_1_46_bits : FrozenBitFields := ⟨0, 120, 8248022⟩
def frozen_kernel_1_47 : frozen_binary32 := frozenMake 0 122 7629628
def frozen_kernel_1_47_bits : FrozenBitFields := ⟨0, 122, 7629628⟩
def frozen_kernel_1_48 : frozen_binary32 := frozenMake 0 123 1505554
def frozen_kernel_1_48_bits : FrozenBitFields := ⟨0, 123, 1505554⟩
def frozen_kernel_1_49 : frozen_binary32 := frozenMake 1 123 993221
def frozen_kernel_1_49_bits : FrozenBitFields := ⟨1, 123, 993221⟩
def frozen_kernel_1_50 : frozen_binary32 := frozenMake 1 123 2156306
def frozen_kernel_1_50_bits : FrozenBitFields := ⟨1, 123, 2156306⟩
def frozen_kernel_1_51 : frozen_binary32 := frozenMake 1 123 4267018
def frozen_kernel_1_51_bits : FrozenBitFields := ⟨1, 123, 4267018⟩
def frozen_kernel_1_52 : frozen_binary32 := frozenMake 0 122 2479212
def frozen_kernel_1_52_bits : FrozenBitFields := ⟨0, 122, 2479212⟩
def frozen_kernel_1_53 : frozen_binary32 := frozenMake 0 122 3689305
def frozen_kernel_1_53_bits : FrozenBitFields := ⟨0, 122, 3689305⟩
def frozen_kernel_1_54 : frozen_binary32 := frozenMake 1 123 3567316
def frozen_kernel_1_54_bits : FrozenBitFields := ⟨1, 123, 3567316⟩
def frozen_kernel_1_55 : frozen_binary32 := frozenMake 1 122 2632131
def frozen_kernel_1_55_bits : FrozenBitFields := ⟨1, 122, 2632131⟩
def frozen_kernel_1_56 : frozen_binary32 := frozenMake 0 121 4295384
def frozen_kernel_1_56_bits : FrozenBitFields := ⟨0, 121, 4295384⟩
def frozen_kernel_1_57 : frozen_binary32 := frozenMake 1 122 1453705
def frozen_kernel_1_57_bits : FrozenBitFields := ⟨1, 122, 1453705⟩
def frozen_kernel_1_58 : frozen_binary32 := frozenMake 0 124 358750
def frozen_kernel_1_58_bits : FrozenBitFields := ⟨0, 124, 358750⟩
def frozen_kernel_1_59 : frozen_binary32 := frozenMake 1 121 4104420
def frozen_kernel_1_59_bits : FrozenBitFields := ⟨1, 121, 4104420⟩
def frozen_kernel_1_60 : frozen_binary32 := frozenMake 1 122 6513894
def frozen_kernel_1_60_bits : FrozenBitFields := ⟨1, 122, 6513894⟩
def frozen_kernel_1_61 : frozen_binary32 := frozenMake 1 123 4089748
def frozen_kernel_1_61_bits : FrozenBitFields := ⟨1, 123, 4089748⟩
def frozen_kernel_1_62 : frozen_binary32 := frozenMake 1 123 194969
def frozen_kernel_1_62_bits : FrozenBitFields := ⟨1, 123, 194969⟩
def frozen_kernel_1_63 : frozen_binary32 := frozenMake 0 109 7936852
def frozen_kernel_1_63_bits : FrozenBitFields := ⟨0, 109, 7936852⟩
def frozen_kernel_2_0 : frozen_binary32 := frozenMake 1 120 3350547
def frozen_kernel_2_0_bits : FrozenBitFields := ⟨1, 120, 3350547⟩
def frozen_kernel_2_1 : frozen_binary32 := frozenMake 1 120 2390278
def frozen_kernel_2_1_bits : FrozenBitFields := ⟨1, 120, 2390278⟩
def frozen_kernel_2_2 : frozen_binary32 := frozenMake 1 121 1658206
def frozen_kernel_2_2_bits : FrozenBitFields := ⟨1, 121, 1658206⟩
def frozen_kernel_2_3 : frozen_binary32 := frozenMake 1 120 6779796
def frozen_kernel_2_3_bits : FrozenBitFields := ⟨1, 120, 6779796⟩
def frozen_kernel_2_4 : frozen_binary32 := frozenMake 1 120 457501
def frozen_kernel_2_4_bits : FrozenBitFields := ⟨1, 120, 457501⟩
def frozen_kernel_2_5 : frozen_binary32 := frozenMake 1 121 5163568
def frozen_kernel_2_5_bits : FrozenBitFields := ⟨1, 121, 5163568⟩
def frozen_kernel_2_6 : frozen_binary32 := frozenMake 1 121 2534389
def frozen_kernel_2_6_bits : FrozenBitFields := ⟨1, 121, 2534389⟩
def frozen_kernel_2_7 : frozen_binary32 := frozenMake 1 121 1312917
def frozen_kernel_2_7_bits : FrozenBitFields := ⟨1, 121, 1312917⟩
def frozen_kernel_2_8 : frozen_binary32 := frozenMake 0 121 1918106
def frozen_kernel_2_8_bits : FrozenBitFields := ⟨0, 121, 1918106⟩
def frozen_kernel_2_9 : frozen_binary32 := frozenMake 0 120 5834289
def frozen_kernel_2_9_bits : FrozenBitFields := ⟨0, 120, 5834289⟩
def frozen_kernel_2_10 : frozen_binary32 := frozenMake 0 123 1100218
def frozen_kernel_2_10_bits : FrozenBitFields := ⟨0, 123, 1100218⟩
def frozen_kernel_2_11 : frozen_binary32 := frozenMake 1 121 13279
def frozen_kernel_2_11_bits : FrozenBitFields := ⟨1, 121, 13279⟩
def frozen_kernel_2_12 : frozen_binary32 := frozenMake 0 120 7471389
def frozen_kernel_2_12_bits : FrozenBitFields := ⟨0, 120, 7471389⟩
def frozen_kernel_2_13 : frozen_binary32 := frozenMake 0 120 6729382
def frozen_kernel_2_13_bits : FrozenBitFields := ⟨0, 120, 6729382⟩
def frozen_kernel_2_14 : frozen_binary32 := frozenMake 0 120 294353
def frozen_kernel_2_14_bits : FrozenBitFields := ⟨0, 120, 294353⟩
def frozen_kernel_2_15 : frozen_binary32 := frozenMake 1 120 7120333
def frozen_kernel_2_15_bits : FrozenBitFields := ⟨1, 120, 7120333⟩
def frozen_kernel_2_16 : frozen_binary32 := frozenMake 1 120 7690559
def frozen_kernel_2_16_bits : FrozenBitFields := ⟨1, 120, 7690559⟩
def frozen_kernel_2_17 : frozen_binary32 := frozenMake 0 119 6032231
def frozen_kernel_2_17_bits : FrozenBitFields := ⟨0, 119, 6032231⟩
def frozen_kernel_2_18 : frozen_binary32 := frozenMake 1 121 6589094
def frozen_kernel_2_18_bits : FrozenBitFields := ⟨1, 121, 6589094⟩
def frozen_kernel_2_19 : frozen_binary32 := frozenMake 0 120 2335207
def frozen_kernel_2_19_bits : FrozenBitFields := ⟨0, 120, 2335207⟩
def frozen_kernel_2_20 : frozen_binary32 := frozenMake 0 121 1899376
def frozen_kernel_2_20_bits : FrozenBitFields := ⟨0, 121, 1899376⟩
def frozen_kernel_2_21 : frozen_binary32 := frozenMake 1 120 1704646
def frozen_kernel_2_21_bits : FrozenBitFields := ⟨1, 120, 1704646⟩
def frozen_kernel_2_22 : frozen_binary32 := frozenMake 0 115 6742331
def frozen_kernel_2_22_bits : FrozenBitFields := ⟨0, 115, 6742331⟩
def frozen_kernel_2_23 : frozen_binary32 := frozenMake 1 119 1969682
def frozen_kernel_2_23_bits : FrozenBitFields := ⟨1, 119, 1969682⟩
def frozen_kernel_2_24 : frozen_binary32 := frozenMake 0 120 905079
def frozen_kernel_2_24_bits : FrozenBitFields := ⟨0, 120, 905079⟩
def frozen_kernel_2_25 : frozen_binary32 := frozenMake 0 122 3077336
def frozen_kernel_2_25_bits : FrozenBitFields := ⟨0, 122, 3077336⟩
def frozen_kernel_2_26 : frozen_binary32 := frozenMake 0 121 1353263
def frozen_kernel_2_26_bits : FrozenBitFields := ⟨0, 121, 1353263⟩
def frozen_kernel_2_27 : frozen_binary32 := frozenMake 0 118 1498835
def frozen_kernel_2_27_bits : FrozenBitFields := ⟨0, 118, 1498835⟩
def frozen_kernel_2_28 : frozen_binary32 := frozenMake 0 120 4433162
def frozen_kernel_2_28_bits : FrozenBitFields := ⟨0, 120, 4433162⟩
def frozen_kernel_2_29 : frozen_binary32 := frozenMake 1 119 7371888
def frozen_kernel_2_29_bits : FrozenBitFields := ⟨1, 119, 7371888⟩
def frozen_kernel_2_30 : frozen_binary32 := frozenMake 1 117 1728602
def frozen_kernel_2_30_bits : FrozenBitFields := ⟨1, 117, 1728602⟩
def frozen_kernel_2_31 : frozen_binary32 := frozenMake 1 119 479840
def frozen_kernel_2_31_bits : FrozenBitFields := ⟨1, 119, 479840⟩
def frozen_kernel_2_32 : frozen_binary32 := frozenMake 0 120 4022739
def frozen_kernel_2_32_bits : FrozenBitFields := ⟨0, 120, 4022739⟩
def frozen_kernel_2_33 : frozen_binary32 := frozenMake 1 120 6648237
def frozen_kernel_2_33_bits : FrozenBitFields := ⟨1, 120, 6648237⟩
def frozen_kernel_2_34 : frozen_binary32 := frozenMake 1 119 4236553
def frozen_kernel_2_34_bits : FrozenBitFields := ⟨1, 119, 4236553⟩
def frozen_kernel_2_35 : frozen_binary32 := frozenMake 0 118 6972305
def frozen_kernel_2_35_bits : FrozenBitFields := ⟨0, 118, 6972305⟩
def frozen_kernel_2_36 : frozen_binary32 := frozenMake 0 119 250677
def frozen_kernel_2_36_bits : FrozenBitFields := ⟨0, 119, 250677⟩
def frozen_kernel_2_37 : frozen_binary32 := frozenMake 0 120 706434
def frozen_kernel_2_37_bits : FrozenBitFields := ⟨0, 120, 706434⟩
def frozen_kernel_2_38 : frozen_binary32 := frozenMake 1 120 1417744
def frozen_kernel_2_38_bits : FrozenBitFields := ⟨1, 120, 1417744⟩
def frozen_kernel_2_39 : frozen_binary32 := frozenMake 0 121 4874168
def frozen_kernel_2_39_bits : FrozenBitFields := ⟨0, 121, 4874168⟩
def frozen_kernel_2_40 : frozen_binary32 := frozenMake 1 120 1991347
def frozen_kernel_2_40_bits : FrozenBitFields := ⟨1, 120, 1991347⟩
def frozen_kernel_2_41 : frozen_binary32 := frozenMake 0 119 7297330
def frozen_kernel_2_41_bits : FrozenBitFields := ⟨0, 119, 7297330⟩
def frozen_kernel_2_42 : frozen_binary32 := frozenMake 0 120 1386744
def frozen_kernel_2_42_bits : FrozenBitFields := ⟨0, 120, 1386744⟩
def frozen_kernel_2_43 : frozen_binary32 := frozenMake 1 121 1576847
def frozen_kernel_2_43_bits : FrozenBitFields := ⟨1, 121, 1576847⟩
def frozen_kernel_2_44 : frozen_binary32 := frozenMake 0 120 4110101
def frozen_kernel_2_44_bits : FrozenBitFields := ⟨0, 120, 4110101⟩
def frozen_kernel_2_45 : frozen_binary32 := frozenMake 1 120 4377528
def frozen_kernel_2_45_bits : FrozenBitFields := ⟨1, 120, 4377528⟩
def frozen_kernel_2_46 : frozen_binary32 := frozenMake 1 120 7646547
def frozen_kernel_2_46_bits : FrozenBitFields := ⟨1, 120, 7646547⟩
def frozen_kernel_2_47 : frozen_binary32 := frozenMake 1 119 7834348
def frozen_kernel_2_47_bits : FrozenBitFields := ⟨1, 119, 7834348⟩
def frozen_kernel_2_48 : frozen_binary32 := frozenMake 0 116 2360222
def frozen_kernel_2_48_bits : FrozenBitFields := ⟨0, 116, 2360222⟩
def frozen_kernel_2_49 : frozen_binary32 := frozenMake 0 119 5276912
def frozen_kernel_2_49_bits : FrozenBitFields := ⟨0, 119, 5276912⟩
def frozen_kernel_2_50 : frozen_binary32 := frozenMake 1 119 3112615
def frozen_kernel_2_50_bits : FrozenBitFields := ⟨1, 119, 3112615⟩
def frozen_kernel_2_51 : frozen_binary32 := frozenMake 0 121 1136855
def frozen_kernel_2_51_bits : FrozenBitFields := ⟨0, 121, 1136855⟩
def frozen_kernel_2_52 : frozen_binary32 := frozenMake 0 119 6904828
def frozen_kernel_2_52_bits : FrozenBitFields := ⟨0, 119, 6904828⟩
def frozen_kernel_2_53 : frozen_binary32 := frozenMake 0 121 2082326
def frozen_kernel_2_53_bits : FrozenBitFields := ⟨0, 121, 2082326⟩
def frozen_kernel_2_54 : frozen_binary32 := frozenMake 0 120 8209858
def frozen_kernel_2_54_bits : FrozenBitFields := ⟨0, 120, 8209858⟩
def frozen_kernel_2_55 : frozen_binary32 := frozenMake 1 120 3819251
def frozen_kernel_2_55_bits : FrozenBitFields := ⟨1, 120, 3819251⟩
def frozen_kernel_2_56 : frozen_binary32 := frozenMake 1 120 55545
def frozen_kernel_2_56_bits : FrozenBitFields := ⟨1, 120, 55545⟩
def frozen_kernel_2_57 : frozen_binary32 := frozenMake 1 121 868402
def frozen_kernel_2_57_bits : FrozenBitFields := ⟨1, 121, 868402⟩
def frozen_kernel_2_58 : frozen_binary32 := frozenMake 0 119 4223153
def frozen_kernel_2_58_bits : FrozenBitFields := ⟨0, 119, 4223153⟩
def frozen_kernel_2_59 : frozen_binary32 := frozenMake 0 120 8135226
def frozen_kernel_2_59_bits : FrozenBitFields := ⟨0, 120, 8135226⟩
def frozen_kernel_2_60 : frozen_binary32 := frozenMake 0 120 7599904
def frozen_kernel_2_60_bits : FrozenBitFields := ⟨0, 120, 7599904⟩
def frozen_kernel_2_61 : frozen_binary32 := frozenMake 1 120 3104494
def frozen_kernel_2_61_bits : FrozenBitFields := ⟨1, 120, 3104494⟩
def frozen_kernel_2_62 : frozen_binary32 := frozenMake 0 121 2017299
def frozen_kernel_2_62_bits : FrozenBitFields := ⟨0, 121, 2017299⟩
def frozen_kernel_2_63 : frozen_binary32 := frozenMake 0 119 2508278
def frozen_kernel_2_63_bits : FrozenBitFields := ⟨0, 119, 2508278⟩
def frozen_kernel_3_0 : frozen_binary32 := frozenMake 0 121 2237673
def frozen_kernel_3_0_bits : FrozenBitFields := ⟨0, 121, 2237673⟩
def frozen_kernel_3_1 : frozen_binary32 := frozenMake 0 122 1730686
def frozen_kernel_3_1_bits : FrozenBitFields := ⟨0, 122, 1730686⟩
def frozen_kernel_3_2 : frozen_binary32 := frozenMake 1 122 564214
def frozen_kernel_3_2_bits : FrozenBitFields := ⟨1, 122, 564214⟩
def frozen_kernel_3_3 : frozen_binary32 := frozenMake 0 119 4466303
def frozen_kernel_3_3_bits : FrozenBitFields := ⟨0, 119, 4466303⟩
def frozen_kernel_3_4 : frozen_binary32 := frozenMake 1 121 2046313
def frozen_kernel_3_4_bits : FrozenBitFields := ⟨1, 121, 2046313⟩
def frozen_kernel_3_5 : frozen_binary32 := frozenMake 0 117 5168394
def frozen_kernel_3_5_bits : FrozenBitFields := ⟨0, 117, 5168394⟩
def frozen_kernel_3_6 : frozen_binary32 := frozenMake 1 121 4355560
def frozen_kernel_3_6_bits : FrozenBitFields := ⟨1, 121, 4355560⟩
def frozen_kernel_3_7 : frozen_binary32 := frozenMake 1 120 3556535
def frozen_kernel_3_7_bits : FrozenBitFields := ⟨1, 120, 3556535⟩
def frozen_kernel_3_8 : frozen_binary32 := frozenMake 1 122 1414385
def frozen_kernel_3_8_bits : FrozenBitFields := ⟨1, 122, 1414385⟩
def frozen_kernel_3_9 : frozen_binary32 := frozenMake 1 121 3068496
def frozen_kernel_3_9_bits : FrozenBitFields := ⟨1, 121, 3068496⟩
def frozen_kernel_3_10 : frozen_binary32 := frozenMake 0 123 1698018
def frozen_kernel_3_10_bits : FrozenBitFields := ⟨0, 123, 1698018⟩
def frozen_kernel_3_11 : frozen_binary32 := frozenMake 1 120 5926302
def frozen_kernel_3_11_bits : FrozenBitFields := ⟨1, 120, 5926302⟩
def frozen_kernel_3_12 : frozen_binary32 := frozenMake 1 122 661867
def frozen_kernel_3_12_bits : FrozenBitFields := ⟨1, 122, 661867⟩
def frozen_kernel_3_13 : frozen_binary32 := frozenMake 1 121 709202
def frozen_kernel_3_13_bits : FrozenBitFields := ⟨1, 121, 709202⟩
def frozen_kernel_3_14 : frozen_binary32 := frozenMake 0 121 3288022
def frozen_kernel_3_14_bits : FrozenBitFields := ⟨0, 121, 3288022⟩
def frozen_kernel_3_15 : frozen_binary32 := frozenMake 1 120 3825085
def frozen_kernel_3_15_bits : FrozenBitFields := ⟨1, 120, 3825085⟩
def frozen_kernel_3_16 : frozen_binary32 := frozenMake 1 119 4575685
def frozen_kernel_3_16_bits : FrozenBitFields := ⟨1, 119, 4575685⟩
def frozen_kernel_3_17 : frozen_binary32 := frozenMake 1 122 1292000
def frozen_kernel_3_17_bits : FrozenBitFields := ⟨1, 122, 1292000⟩
def frozen_kernel_3_18 : frozen_binary32 := frozenMake 0 121 2041098
def frozen_kernel_3_18_bits : FrozenBitFields := ⟨0, 121, 2041098⟩
def frozen_kernel_3_19 : frozen_binary32 := frozenMake 0 122 2582483
def frozen_kernel_3_19_bits : FrozenBitFields := ⟨0, 122, 2582483⟩
def frozen_kernel_3_20 : frozen_binary32 := frozenMake 0 120 2023679
def frozen_kernel_3_20_bits : FrozenBitFields := ⟨0, 120, 2023679⟩
def frozen_kernel_3_21 : frozen_binary32 := frozenMake 0 122 314724
def frozen_kernel_3_21_bits : FrozenBitFields := ⟨0, 122, 314724⟩
def frozen_kernel_3_22 : frozen_binary32 := frozenMake 0 120 5089812
def frozen_kernel_3_22_bits : FrozenBitFields := ⟨0, 120, 5089812⟩
def frozen_kernel_3_23 : frozen_binary32 := frozenMake 1 121 5598946
def frozen_kernel_3_23_bits : FrozenBitFields := ⟨1, 121, 5598946⟩
def frozen_kernel_3_24 : frozen_binary32 := frozenMake 1 121 4608895
def frozen_kernel_3_24_bits : FrozenBitFields := ⟨1, 121, 4608895⟩
def frozen_kernel_3_25 : frozen_binary32 := frozenMake 1 122 3232530
def frozen_kernel_3_25_bits : FrozenBitFields := ⟨1, 122, 3232530⟩
def frozen_kernel_3_26 : frozen_binary32 := frozenMake 0 122 42744
def frozen_kernel_3_26_bits : FrozenBitFields := ⟨0, 122, 42744⟩
def frozen_kernel_3_27 : frozen_binary32 := frozenMake 0 120 393216
def frozen_kernel_3_27_bits : FrozenBitFields := ⟨0, 120, 393216⟩
def frozen_kernel_3_28 : frozen_binary32 := frozenMake 1 119 2451464
def frozen_kernel_3_28_bits : FrozenBitFields := ⟨1, 119, 2451464⟩
def frozen_kernel_3_29 : frozen_binary32 := frozenMake 1 120 1954746
def frozen_kernel_3_29_bits : FrozenBitFields := ⟨1, 120, 1954746⟩
def frozen_kernel_3_30 : frozen_binary32 := frozenMake 1 119 4411950
def frozen_kernel_3_30_bits : FrozenBitFields := ⟨1, 119, 4411950⟩
def frozen_kernel_3_31 : frozen_binary32 := frozenMake 0 121 2885279
def frozen_kernel_3_31_bits : FrozenBitFields := ⟨0, 121, 2885279⟩
def frozen_kernel_3_32 : frozen_binary32 := frozenMake 0 122 6093189
def frozen_kernel_3_32_bits : FrozenBitFields := ⟨0, 122, 6093189⟩
def frozen_kernel_3_33 : frozen_binary32 := frozenMake 0 116 4168535
def frozen_kernel_3_33_bits : FrozenBitFields := ⟨0, 116, 4168535⟩
def frozen_kernel_3_34 : frozen_binary32 := frozenMake 1 121 3338891
def frozen_kernel_3_34_bits : FrozenBitFields := ⟨1, 121, 3338891⟩
def frozen_kernel_3_35 : frozen_binary32 := frozenMake 0 121 4566420
def frozen_kernel_3_35_bits : FrozenBitFields := ⟨0, 121, 4566420⟩
def frozen_kernel_3_36 : frozen_binary32 := frozenMake 0 120 134438
def frozen_kernel_3_36_bits : FrozenBitFields := ⟨0, 120, 134438⟩
def frozen_kernel_3_37 : frozen_binary32 := frozenMake 0 120 428045
def frozen_kernel_3_37_bits : FrozenBitFields := ⟨0, 120, 428045⟩
def frozen_kernel_3_38 : frozen_binary32 := frozenMake 1 120 6675360
def frozen_kernel_3_38_bits : FrozenBitFields := ⟨1, 120, 6675360⟩
def frozen_kernel_3_39 : frozen_binary32 := frozenMake 1 121 4664291
def frozen_kernel_3_39_bits : FrozenBitFields := ⟨1, 121, 4664291⟩
def frozen_kernel_3_40 : frozen_binary32 := frozenMake 1 121 4010639
def frozen_kernel_3_40_bits : FrozenBitFields := ⟨1, 121, 4010639⟩
def frozen_kernel_3_41 : frozen_binary32 := frozenMake 0 121 2084347
def frozen_kernel_3_41_bits : FrozenBitFields := ⟨0, 121, 2084347⟩
def frozen_kernel_3_42 : frozen_binary32 := frozenMake 0 121 4570792
def frozen_kernel_3_42_bits : FrozenBitFields := ⟨0, 121, 4570792⟩
def frozen_kernel_3_43 : frozen_binary32 := frozenMake 1 120 571619
def frozen_kernel_3_43_bits : FrozenBitFields := ⟨1, 120, 571619⟩
def frozen_kernel_3_44 : frozen_binary32 := frozenMake 1 122 3250284
def frozen_kernel_3_44_bits : FrozenBitFields := ⟨1, 122, 3250284⟩
def frozen_kernel_3_45 : frozen_binary32 := frozenMake 0 120 6473116
def frozen_kernel_3_45_bits : FrozenBitFields := ⟨0, 120, 6473116⟩
def frozen_kernel_3_46 : frozen_binary32 := frozenMake 1 122 882056
def frozen_kernel_3_46_bits : FrozenBitFields := ⟨1, 122, 882056⟩
def frozen_kernel_3_47 : frozen_binary32 := frozenMake 0 116 3947291
def frozen_kernel_3_47_bits : FrozenBitFields := ⟨0, 116, 3947291⟩
def frozen_kernel_3_48 : frozen_binary32 := frozenMake 1 121 768801
def frozen_kernel_3_48_bits : FrozenBitFields := ⟨1, 121, 768801⟩
def frozen_kernel_3_49 : frozen_binary32 := frozenMake 1 120 6358715
def frozen_kernel_3_49_bits : FrozenBitFields := ⟨1, 120, 6358715⟩
def frozen_kernel_3_50 : frozen_binary32 := frozenMake 1 121 3906475
def frozen_kernel_3_50_bits : FrozenBitFields := ⟨1, 121, 3906475⟩
def frozen_kernel_3_51 : frozen_binary32 := frozenMake 0 122 7483413
def frozen_kernel_3_51_bits : FrozenBitFields := ⟨0, 122, 7483413⟩
def frozen_kernel_3_52 : frozen_binary32 := frozenMake 1 120 2850651
def frozen_kernel_3_52_bits : FrozenBitFields := ⟨1, 120, 2850651⟩
def frozen_kernel_3_53 : frozen_binary32 := frozenMake 1 120 3331474
def frozen_kernel_3_53_bits : FrozenBitFields := ⟨1, 120, 3331474⟩
def frozen_kernel_3_54 : frozen_binary32 := frozenMake 0 122 542369
def frozen_kernel_3_54_bits : FrozenBitFields := ⟨0, 122, 542369⟩
def frozen_kernel_3_55 : frozen_binary32 := frozenMake 1 121 6921374
def frozen_kernel_3_55_bits : FrozenBitFields := ⟨1, 121, 6921374⟩
def frozen_kernel_3_56 : frozen_binary32 := frozenMake 1 121 5560085
def frozen_kernel_3_56_bits : FrozenBitFields := ⟨1, 121, 5560085⟩
def frozen_kernel_3_57 : frozen_binary32 := frozenMake 0 122 6573013
def frozen_kernel_3_57_bits : FrozenBitFields := ⟨0, 122, 6573013⟩
def frozen_kernel_3_58 : frozen_binary32 := frozenMake 1 120 1601165
def frozen_kernel_3_58_bits : FrozenBitFields := ⟨1, 120, 1601165⟩
def frozen_kernel_3_59 : frozen_binary32 := frozenMake 0 121 982652
def frozen_kernel_3_59_bits : FrozenBitFields := ⟨0, 121, 982652⟩
def frozen_kernel_3_60 : frozen_binary32 := frozenMake 1 122 1454750
def frozen_kernel_3_60_bits : FrozenBitFields := ⟨1, 122, 1454750⟩
def frozen_kernel_3_61 : frozen_binary32 := frozenMake 0 118 1145344
def frozen_kernel_3_61_bits : FrozenBitFields := ⟨0, 118, 1145344⟩
def frozen_kernel_3_62 : frozen_binary32 := frozenMake 0 122 239121
def frozen_kernel_3_62_bits : FrozenBitFields := ⟨0, 122, 239121⟩
def frozen_kernel_3_63 : frozen_binary32 := frozenMake 1 117 4212317
def frozen_kernel_3_63_bits : FrozenBitFields := ⟨1, 117, 4212317⟩

def frozen_embedding : List frozen_binary32 := [
  frozen_embedding_0,
  frozen_embedding_1,
  frozen_embedding_2,
  frozen_embedding_3,
  frozen_embedding_4,
  frozen_embedding_5,
  frozen_embedding_6,
  frozen_embedding_7,
  frozen_embedding_8,
  frozen_embedding_9,
  frozen_embedding_10,
  frozen_embedding_11,
  frozen_embedding_12,
  frozen_embedding_13,
  frozen_embedding_14,
  frozen_embedding_15,
  frozen_embedding_16,
  frozen_embedding_17,
  frozen_embedding_18,
  frozen_embedding_19,
  frozen_embedding_20,
  frozen_embedding_21,
  frozen_embedding_22,
  frozen_embedding_23,
  frozen_embedding_24,
  frozen_embedding_25,
  frozen_embedding_26,
  frozen_embedding_27,
  frozen_embedding_28,
  frozen_embedding_29,
  frozen_embedding_30,
  frozen_embedding_31,
  frozen_embedding_32,
  frozen_embedding_33,
  frozen_embedding_34,
  frozen_embedding_35,
  frozen_embedding_36,
  frozen_embedding_37,
  frozen_embedding_38,
  frozen_embedding_39,
  frozen_embedding_40,
  frozen_embedding_41,
  frozen_embedding_42,
  frozen_embedding_43,
  frozen_embedding_44,
  frozen_embedding_45,
  frozen_embedding_46,
  frozen_embedding_47,
  frozen_embedding_48,
  frozen_embedding_49,
  frozen_embedding_50,
  frozen_embedding_51,
  frozen_embedding_52,
  frozen_embedding_53,
  frozen_embedding_54,
  frozen_embedding_55,
  frozen_embedding_56,
  frozen_embedding_57,
  frozen_embedding_58,
  frozen_embedding_59,
  frozen_embedding_60,
  frozen_embedding_61,
  frozen_embedding_62,
  frozen_embedding_63
]

def frozen_position_embedding : List frozen_binary32 := [
  frozen_position_embedding_0,
  frozen_position_embedding_1,
  frozen_position_embedding_2,
  frozen_position_embedding_3,
  frozen_position_embedding_4,
  frozen_position_embedding_5,
  frozen_position_embedding_6,
  frozen_position_embedding_7,
  frozen_position_embedding_8,
  frozen_position_embedding_9,
  frozen_position_embedding_10,
  frozen_position_embedding_11,
  frozen_position_embedding_12,
  frozen_position_embedding_13,
  frozen_position_embedding_14,
  frozen_position_embedding_15,
  frozen_position_embedding_16,
  frozen_position_embedding_17,
  frozen_position_embedding_18,
  frozen_position_embedding_19,
  frozen_position_embedding_20,
  frozen_position_embedding_21,
  frozen_position_embedding_22,
  frozen_position_embedding_23,
  frozen_position_embedding_24,
  frozen_position_embedding_25,
  frozen_position_embedding_26,
  frozen_position_embedding_27,
  frozen_position_embedding_28,
  frozen_position_embedding_29,
  frozen_position_embedding_30,
  frozen_position_embedding_31,
  frozen_position_embedding_32,
  frozen_position_embedding_33,
  frozen_position_embedding_34,
  frozen_position_embedding_35,
  frozen_position_embedding_36,
  frozen_position_embedding_37,
  frozen_position_embedding_38,
  frozen_position_embedding_39,
  frozen_position_embedding_40,
  frozen_position_embedding_41,
  frozen_position_embedding_42,
  frozen_position_embedding_43,
  frozen_position_embedding_44,
  frozen_position_embedding_45,
  frozen_position_embedding_46,
  frozen_position_embedding_47,
  frozen_position_embedding_48,
  frozen_position_embedding_49,
  frozen_position_embedding_50,
  frozen_position_embedding_51,
  frozen_position_embedding_52,
  frozen_position_embedding_53,
  frozen_position_embedding_54,
  frozen_position_embedding_55,
  frozen_position_embedding_56,
  frozen_position_embedding_57,
  frozen_position_embedding_58,
  frozen_position_embedding_59,
  frozen_position_embedding_60,
  frozen_position_embedding_61,
  frozen_position_embedding_62,
  frozen_position_embedding_63
]

def frozen_input_activation : List frozen_binary32 := [
  frozen_input_activation_0,
  frozen_input_activation_1,
  frozen_input_activation_2,
  frozen_input_activation_3,
  frozen_input_activation_4,
  frozen_input_activation_5,
  frozen_input_activation_6,
  frozen_input_activation_7,
  frozen_input_activation_8,
  frozen_input_activation_9,
  frozen_input_activation_10,
  frozen_input_activation_11,
  frozen_input_activation_12,
  frozen_input_activation_13,
  frozen_input_activation_14,
  frozen_input_activation_15,
  frozen_input_activation_16,
  frozen_input_activation_17,
  frozen_input_activation_18,
  frozen_input_activation_19,
  frozen_input_activation_20,
  frozen_input_activation_21,
  frozen_input_activation_22,
  frozen_input_activation_23,
  frozen_input_activation_24,
  frozen_input_activation_25,
  frozen_input_activation_26,
  frozen_input_activation_27,
  frozen_input_activation_28,
  frozen_input_activation_29,
  frozen_input_activation_30,
  frozen_input_activation_31,
  frozen_input_activation_32,
  frozen_input_activation_33,
  frozen_input_activation_34,
  frozen_input_activation_35,
  frozen_input_activation_36,
  frozen_input_activation_37,
  frozen_input_activation_38,
  frozen_input_activation_39,
  frozen_input_activation_40,
  frozen_input_activation_41,
  frozen_input_activation_42,
  frozen_input_activation_43,
  frozen_input_activation_44,
  frozen_input_activation_45,
  frozen_input_activation_46,
  frozen_input_activation_47,
  frozen_input_activation_48,
  frozen_input_activation_49,
  frozen_input_activation_50,
  frozen_input_activation_51,
  frozen_input_activation_52,
  frozen_input_activation_53,
  frozen_input_activation_54,
  frozen_input_activation_55,
  frozen_input_activation_56,
  frozen_input_activation_57,
  frozen_input_activation_58,
  frozen_input_activation_59,
  frozen_input_activation_60,
  frozen_input_activation_61,
  frozen_input_activation_62,
  frozen_input_activation_63
]

def frozen_kernel_0 : List frozen_binary32 := [
  frozen_kernel_0_0,
  frozen_kernel_0_1,
  frozen_kernel_0_2,
  frozen_kernel_0_3,
  frozen_kernel_0_4,
  frozen_kernel_0_5,
  frozen_kernel_0_6,
  frozen_kernel_0_7,
  frozen_kernel_0_8,
  frozen_kernel_0_9,
  frozen_kernel_0_10,
  frozen_kernel_0_11,
  frozen_kernel_0_12,
  frozen_kernel_0_13,
  frozen_kernel_0_14,
  frozen_kernel_0_15,
  frozen_kernel_0_16,
  frozen_kernel_0_17,
  frozen_kernel_0_18,
  frozen_kernel_0_19,
  frozen_kernel_0_20,
  frozen_kernel_0_21,
  frozen_kernel_0_22,
  frozen_kernel_0_23,
  frozen_kernel_0_24,
  frozen_kernel_0_25,
  frozen_kernel_0_26,
  frozen_kernel_0_27,
  frozen_kernel_0_28,
  frozen_kernel_0_29,
  frozen_kernel_0_30,
  frozen_kernel_0_31,
  frozen_kernel_0_32,
  frozen_kernel_0_33,
  frozen_kernel_0_34,
  frozen_kernel_0_35,
  frozen_kernel_0_36,
  frozen_kernel_0_37,
  frozen_kernel_0_38,
  frozen_kernel_0_39,
  frozen_kernel_0_40,
  frozen_kernel_0_41,
  frozen_kernel_0_42,
  frozen_kernel_0_43,
  frozen_kernel_0_44,
  frozen_kernel_0_45,
  frozen_kernel_0_46,
  frozen_kernel_0_47,
  frozen_kernel_0_48,
  frozen_kernel_0_49,
  frozen_kernel_0_50,
  frozen_kernel_0_51,
  frozen_kernel_0_52,
  frozen_kernel_0_53,
  frozen_kernel_0_54,
  frozen_kernel_0_55,
  frozen_kernel_0_56,
  frozen_kernel_0_57,
  frozen_kernel_0_58,
  frozen_kernel_0_59,
  frozen_kernel_0_60,
  frozen_kernel_0_61,
  frozen_kernel_0_62,
  frozen_kernel_0_63
]

def frozen_kernel_1 : List frozen_binary32 := [
  frozen_kernel_1_0,
  frozen_kernel_1_1,
  frozen_kernel_1_2,
  frozen_kernel_1_3,
  frozen_kernel_1_4,
  frozen_kernel_1_5,
  frozen_kernel_1_6,
  frozen_kernel_1_7,
  frozen_kernel_1_8,
  frozen_kernel_1_9,
  frozen_kernel_1_10,
  frozen_kernel_1_11,
  frozen_kernel_1_12,
  frozen_kernel_1_13,
  frozen_kernel_1_14,
  frozen_kernel_1_15,
  frozen_kernel_1_16,
  frozen_kernel_1_17,
  frozen_kernel_1_18,
  frozen_kernel_1_19,
  frozen_kernel_1_20,
  frozen_kernel_1_21,
  frozen_kernel_1_22,
  frozen_kernel_1_23,
  frozen_kernel_1_24,
  frozen_kernel_1_25,
  frozen_kernel_1_26,
  frozen_kernel_1_27,
  frozen_kernel_1_28,
  frozen_kernel_1_29,
  frozen_kernel_1_30,
  frozen_kernel_1_31,
  frozen_kernel_1_32,
  frozen_kernel_1_33,
  frozen_kernel_1_34,
  frozen_kernel_1_35,
  frozen_kernel_1_36,
  frozen_kernel_1_37,
  frozen_kernel_1_38,
  frozen_kernel_1_39,
  frozen_kernel_1_40,
  frozen_kernel_1_41,
  frozen_kernel_1_42,
  frozen_kernel_1_43,
  frozen_kernel_1_44,
  frozen_kernel_1_45,
  frozen_kernel_1_46,
  frozen_kernel_1_47,
  frozen_kernel_1_48,
  frozen_kernel_1_49,
  frozen_kernel_1_50,
  frozen_kernel_1_51,
  frozen_kernel_1_52,
  frozen_kernel_1_53,
  frozen_kernel_1_54,
  frozen_kernel_1_55,
  frozen_kernel_1_56,
  frozen_kernel_1_57,
  frozen_kernel_1_58,
  frozen_kernel_1_59,
  frozen_kernel_1_60,
  frozen_kernel_1_61,
  frozen_kernel_1_62,
  frozen_kernel_1_63
]

def frozen_kernel_2 : List frozen_binary32 := [
  frozen_kernel_2_0,
  frozen_kernel_2_1,
  frozen_kernel_2_2,
  frozen_kernel_2_3,
  frozen_kernel_2_4,
  frozen_kernel_2_5,
  frozen_kernel_2_6,
  frozen_kernel_2_7,
  frozen_kernel_2_8,
  frozen_kernel_2_9,
  frozen_kernel_2_10,
  frozen_kernel_2_11,
  frozen_kernel_2_12,
  frozen_kernel_2_13,
  frozen_kernel_2_14,
  frozen_kernel_2_15,
  frozen_kernel_2_16,
  frozen_kernel_2_17,
  frozen_kernel_2_18,
  frozen_kernel_2_19,
  frozen_kernel_2_20,
  frozen_kernel_2_21,
  frozen_kernel_2_22,
  frozen_kernel_2_23,
  frozen_kernel_2_24,
  frozen_kernel_2_25,
  frozen_kernel_2_26,
  frozen_kernel_2_27,
  frozen_kernel_2_28,
  frozen_kernel_2_29,
  frozen_kernel_2_30,
  frozen_kernel_2_31,
  frozen_kernel_2_32,
  frozen_kernel_2_33,
  frozen_kernel_2_34,
  frozen_kernel_2_35,
  frozen_kernel_2_36,
  frozen_kernel_2_37,
  frozen_kernel_2_38,
  frozen_kernel_2_39,
  frozen_kernel_2_40,
  frozen_kernel_2_41,
  frozen_kernel_2_42,
  frozen_kernel_2_43,
  frozen_kernel_2_44,
  frozen_kernel_2_45,
  frozen_kernel_2_46,
  frozen_kernel_2_47,
  frozen_kernel_2_48,
  frozen_kernel_2_49,
  frozen_kernel_2_50,
  frozen_kernel_2_51,
  frozen_kernel_2_52,
  frozen_kernel_2_53,
  frozen_kernel_2_54,
  frozen_kernel_2_55,
  frozen_kernel_2_56,
  frozen_kernel_2_57,
  frozen_kernel_2_58,
  frozen_kernel_2_59,
  frozen_kernel_2_60,
  frozen_kernel_2_61,
  frozen_kernel_2_62,
  frozen_kernel_2_63
]

def frozen_kernel_3 : List frozen_binary32 := [
  frozen_kernel_3_0,
  frozen_kernel_3_1,
  frozen_kernel_3_2,
  frozen_kernel_3_3,
  frozen_kernel_3_4,
  frozen_kernel_3_5,
  frozen_kernel_3_6,
  frozen_kernel_3_7,
  frozen_kernel_3_8,
  frozen_kernel_3_9,
  frozen_kernel_3_10,
  frozen_kernel_3_11,
  frozen_kernel_3_12,
  frozen_kernel_3_13,
  frozen_kernel_3_14,
  frozen_kernel_3_15,
  frozen_kernel_3_16,
  frozen_kernel_3_17,
  frozen_kernel_3_18,
  frozen_kernel_3_19,
  frozen_kernel_3_20,
  frozen_kernel_3_21,
  frozen_kernel_3_22,
  frozen_kernel_3_23,
  frozen_kernel_3_24,
  frozen_kernel_3_25,
  frozen_kernel_3_26,
  frozen_kernel_3_27,
  frozen_kernel_3_28,
  frozen_kernel_3_29,
  frozen_kernel_3_30,
  frozen_kernel_3_31,
  frozen_kernel_3_32,
  frozen_kernel_3_33,
  frozen_kernel_3_34,
  frozen_kernel_3_35,
  frozen_kernel_3_36,
  frozen_kernel_3_37,
  frozen_kernel_3_38,
  frozen_kernel_3_39,
  frozen_kernel_3_40,
  frozen_kernel_3_41,
  frozen_kernel_3_42,
  frozen_kernel_3_43,
  frozen_kernel_3_44,
  frozen_kernel_3_45,
  frozen_kernel_3_46,
  frozen_kernel_3_47,
  frozen_kernel_3_48,
  frozen_kernel_3_49,
  frozen_kernel_3_50,
  frozen_kernel_3_51,
  frozen_kernel_3_52,
  frozen_kernel_3_53,
  frozen_kernel_3_54,
  frozen_kernel_3_55,
  frozen_kernel_3_56,
  frozen_kernel_3_57,
  frozen_kernel_3_58,
  frozen_kernel_3_59,
  frozen_kernel_3_60,
  frozen_kernel_3_61,
  frozen_kernel_3_62,
  frozen_kernel_3_63
]

def frozen_trace_kernels : List (List frozen_binary32) := [
  frozen_kernel_0,
  frozen_kernel_1,
  frozen_kernel_2,
  frozen_kernel_3
]

def frozen_trace_witnesses : List (List frozen_binary32) := [
  ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_0,
  ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_1,
  ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_2,
  ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_3
]

def frozen_threshold_128 : frozen_binary32 := frozenMake 0 134 0
def frozen_threshold_128_bits : FrozenBitFields := ⟨0, 134, 0⟩

def frozen_embedding_bits : List FrozenBitFields := [
  frozen_embedding_0_bits,
  frozen_embedding_1_bits,
  frozen_embedding_2_bits,
  frozen_embedding_3_bits,
  frozen_embedding_4_bits,
  frozen_embedding_5_bits,
  frozen_embedding_6_bits,
  frozen_embedding_7_bits,
  frozen_embedding_8_bits,
  frozen_embedding_9_bits,
  frozen_embedding_10_bits,
  frozen_embedding_11_bits,
  frozen_embedding_12_bits,
  frozen_embedding_13_bits,
  frozen_embedding_14_bits,
  frozen_embedding_15_bits,
  frozen_embedding_16_bits,
  frozen_embedding_17_bits,
  frozen_embedding_18_bits,
  frozen_embedding_19_bits,
  frozen_embedding_20_bits,
  frozen_embedding_21_bits,
  frozen_embedding_22_bits,
  frozen_embedding_23_bits,
  frozen_embedding_24_bits,
  frozen_embedding_25_bits,
  frozen_embedding_26_bits,
  frozen_embedding_27_bits,
  frozen_embedding_28_bits,
  frozen_embedding_29_bits,
  frozen_embedding_30_bits,
  frozen_embedding_31_bits,
  frozen_embedding_32_bits,
  frozen_embedding_33_bits,
  frozen_embedding_34_bits,
  frozen_embedding_35_bits,
  frozen_embedding_36_bits,
  frozen_embedding_37_bits,
  frozen_embedding_38_bits,
  frozen_embedding_39_bits,
  frozen_embedding_40_bits,
  frozen_embedding_41_bits,
  frozen_embedding_42_bits,
  frozen_embedding_43_bits,
  frozen_embedding_44_bits,
  frozen_embedding_45_bits,
  frozen_embedding_46_bits,
  frozen_embedding_47_bits,
  frozen_embedding_48_bits,
  frozen_embedding_49_bits,
  frozen_embedding_50_bits,
  frozen_embedding_51_bits,
  frozen_embedding_52_bits,
  frozen_embedding_53_bits,
  frozen_embedding_54_bits,
  frozen_embedding_55_bits,
  frozen_embedding_56_bits,
  frozen_embedding_57_bits,
  frozen_embedding_58_bits,
  frozen_embedding_59_bits,
  frozen_embedding_60_bits,
  frozen_embedding_61_bits,
  frozen_embedding_62_bits,
  frozen_embedding_63_bits
]

def frozen_position_embedding_bits : List FrozenBitFields := [
  frozen_position_embedding_0_bits,
  frozen_position_embedding_1_bits,
  frozen_position_embedding_2_bits,
  frozen_position_embedding_3_bits,
  frozen_position_embedding_4_bits,
  frozen_position_embedding_5_bits,
  frozen_position_embedding_6_bits,
  frozen_position_embedding_7_bits,
  frozen_position_embedding_8_bits,
  frozen_position_embedding_9_bits,
  frozen_position_embedding_10_bits,
  frozen_position_embedding_11_bits,
  frozen_position_embedding_12_bits,
  frozen_position_embedding_13_bits,
  frozen_position_embedding_14_bits,
  frozen_position_embedding_15_bits,
  frozen_position_embedding_16_bits,
  frozen_position_embedding_17_bits,
  frozen_position_embedding_18_bits,
  frozen_position_embedding_19_bits,
  frozen_position_embedding_20_bits,
  frozen_position_embedding_21_bits,
  frozen_position_embedding_22_bits,
  frozen_position_embedding_23_bits,
  frozen_position_embedding_24_bits,
  frozen_position_embedding_25_bits,
  frozen_position_embedding_26_bits,
  frozen_position_embedding_27_bits,
  frozen_position_embedding_28_bits,
  frozen_position_embedding_29_bits,
  frozen_position_embedding_30_bits,
  frozen_position_embedding_31_bits,
  frozen_position_embedding_32_bits,
  frozen_position_embedding_33_bits,
  frozen_position_embedding_34_bits,
  frozen_position_embedding_35_bits,
  frozen_position_embedding_36_bits,
  frozen_position_embedding_37_bits,
  frozen_position_embedding_38_bits,
  frozen_position_embedding_39_bits,
  frozen_position_embedding_40_bits,
  frozen_position_embedding_41_bits,
  frozen_position_embedding_42_bits,
  frozen_position_embedding_43_bits,
  frozen_position_embedding_44_bits,
  frozen_position_embedding_45_bits,
  frozen_position_embedding_46_bits,
  frozen_position_embedding_47_bits,
  frozen_position_embedding_48_bits,
  frozen_position_embedding_49_bits,
  frozen_position_embedding_50_bits,
  frozen_position_embedding_51_bits,
  frozen_position_embedding_52_bits,
  frozen_position_embedding_53_bits,
  frozen_position_embedding_54_bits,
  frozen_position_embedding_55_bits,
  frozen_position_embedding_56_bits,
  frozen_position_embedding_57_bits,
  frozen_position_embedding_58_bits,
  frozen_position_embedding_59_bits,
  frozen_position_embedding_60_bits,
  frozen_position_embedding_61_bits,
  frozen_position_embedding_62_bits,
  frozen_position_embedding_63_bits
]

def frozen_input_activation_bits : List FrozenBitFields := [
  frozen_input_activation_0_bits,
  frozen_input_activation_1_bits,
  frozen_input_activation_2_bits,
  frozen_input_activation_3_bits,
  frozen_input_activation_4_bits,
  frozen_input_activation_5_bits,
  frozen_input_activation_6_bits,
  frozen_input_activation_7_bits,
  frozen_input_activation_8_bits,
  frozen_input_activation_9_bits,
  frozen_input_activation_10_bits,
  frozen_input_activation_11_bits,
  frozen_input_activation_12_bits,
  frozen_input_activation_13_bits,
  frozen_input_activation_14_bits,
  frozen_input_activation_15_bits,
  frozen_input_activation_16_bits,
  frozen_input_activation_17_bits,
  frozen_input_activation_18_bits,
  frozen_input_activation_19_bits,
  frozen_input_activation_20_bits,
  frozen_input_activation_21_bits,
  frozen_input_activation_22_bits,
  frozen_input_activation_23_bits,
  frozen_input_activation_24_bits,
  frozen_input_activation_25_bits,
  frozen_input_activation_26_bits,
  frozen_input_activation_27_bits,
  frozen_input_activation_28_bits,
  frozen_input_activation_29_bits,
  frozen_input_activation_30_bits,
  frozen_input_activation_31_bits,
  frozen_input_activation_32_bits,
  frozen_input_activation_33_bits,
  frozen_input_activation_34_bits,
  frozen_input_activation_35_bits,
  frozen_input_activation_36_bits,
  frozen_input_activation_37_bits,
  frozen_input_activation_38_bits,
  frozen_input_activation_39_bits,
  frozen_input_activation_40_bits,
  frozen_input_activation_41_bits,
  frozen_input_activation_42_bits,
  frozen_input_activation_43_bits,
  frozen_input_activation_44_bits,
  frozen_input_activation_45_bits,
  frozen_input_activation_46_bits,
  frozen_input_activation_47_bits,
  frozen_input_activation_48_bits,
  frozen_input_activation_49_bits,
  frozen_input_activation_50_bits,
  frozen_input_activation_51_bits,
  frozen_input_activation_52_bits,
  frozen_input_activation_53_bits,
  frozen_input_activation_54_bits,
  frozen_input_activation_55_bits,
  frozen_input_activation_56_bits,
  frozen_input_activation_57_bits,
  frozen_input_activation_58_bits,
  frozen_input_activation_59_bits,
  frozen_input_activation_60_bits,
  frozen_input_activation_61_bits,
  frozen_input_activation_62_bits,
  frozen_input_activation_63_bits
]

def frozen_kernel_0_bits : List FrozenBitFields := [
  frozen_kernel_0_0_bits,
  frozen_kernel_0_1_bits,
  frozen_kernel_0_2_bits,
  frozen_kernel_0_3_bits,
  frozen_kernel_0_4_bits,
  frozen_kernel_0_5_bits,
  frozen_kernel_0_6_bits,
  frozen_kernel_0_7_bits,
  frozen_kernel_0_8_bits,
  frozen_kernel_0_9_bits,
  frozen_kernel_0_10_bits,
  frozen_kernel_0_11_bits,
  frozen_kernel_0_12_bits,
  frozen_kernel_0_13_bits,
  frozen_kernel_0_14_bits,
  frozen_kernel_0_15_bits,
  frozen_kernel_0_16_bits,
  frozen_kernel_0_17_bits,
  frozen_kernel_0_18_bits,
  frozen_kernel_0_19_bits,
  frozen_kernel_0_20_bits,
  frozen_kernel_0_21_bits,
  frozen_kernel_0_22_bits,
  frozen_kernel_0_23_bits,
  frozen_kernel_0_24_bits,
  frozen_kernel_0_25_bits,
  frozen_kernel_0_26_bits,
  frozen_kernel_0_27_bits,
  frozen_kernel_0_28_bits,
  frozen_kernel_0_29_bits,
  frozen_kernel_0_30_bits,
  frozen_kernel_0_31_bits,
  frozen_kernel_0_32_bits,
  frozen_kernel_0_33_bits,
  frozen_kernel_0_34_bits,
  frozen_kernel_0_35_bits,
  frozen_kernel_0_36_bits,
  frozen_kernel_0_37_bits,
  frozen_kernel_0_38_bits,
  frozen_kernel_0_39_bits,
  frozen_kernel_0_40_bits,
  frozen_kernel_0_41_bits,
  frozen_kernel_0_42_bits,
  frozen_kernel_0_43_bits,
  frozen_kernel_0_44_bits,
  frozen_kernel_0_45_bits,
  frozen_kernel_0_46_bits,
  frozen_kernel_0_47_bits,
  frozen_kernel_0_48_bits,
  frozen_kernel_0_49_bits,
  frozen_kernel_0_50_bits,
  frozen_kernel_0_51_bits,
  frozen_kernel_0_52_bits,
  frozen_kernel_0_53_bits,
  frozen_kernel_0_54_bits,
  frozen_kernel_0_55_bits,
  frozen_kernel_0_56_bits,
  frozen_kernel_0_57_bits,
  frozen_kernel_0_58_bits,
  frozen_kernel_0_59_bits,
  frozen_kernel_0_60_bits,
  frozen_kernel_0_61_bits,
  frozen_kernel_0_62_bits,
  frozen_kernel_0_63_bits
]

def frozen_kernel_1_bits : List FrozenBitFields := [
  frozen_kernel_1_0_bits,
  frozen_kernel_1_1_bits,
  frozen_kernel_1_2_bits,
  frozen_kernel_1_3_bits,
  frozen_kernel_1_4_bits,
  frozen_kernel_1_5_bits,
  frozen_kernel_1_6_bits,
  frozen_kernel_1_7_bits,
  frozen_kernel_1_8_bits,
  frozen_kernel_1_9_bits,
  frozen_kernel_1_10_bits,
  frozen_kernel_1_11_bits,
  frozen_kernel_1_12_bits,
  frozen_kernel_1_13_bits,
  frozen_kernel_1_14_bits,
  frozen_kernel_1_15_bits,
  frozen_kernel_1_16_bits,
  frozen_kernel_1_17_bits,
  frozen_kernel_1_18_bits,
  frozen_kernel_1_19_bits,
  frozen_kernel_1_20_bits,
  frozen_kernel_1_21_bits,
  frozen_kernel_1_22_bits,
  frozen_kernel_1_23_bits,
  frozen_kernel_1_24_bits,
  frozen_kernel_1_25_bits,
  frozen_kernel_1_26_bits,
  frozen_kernel_1_27_bits,
  frozen_kernel_1_28_bits,
  frozen_kernel_1_29_bits,
  frozen_kernel_1_30_bits,
  frozen_kernel_1_31_bits,
  frozen_kernel_1_32_bits,
  frozen_kernel_1_33_bits,
  frozen_kernel_1_34_bits,
  frozen_kernel_1_35_bits,
  frozen_kernel_1_36_bits,
  frozen_kernel_1_37_bits,
  frozen_kernel_1_38_bits,
  frozen_kernel_1_39_bits,
  frozen_kernel_1_40_bits,
  frozen_kernel_1_41_bits,
  frozen_kernel_1_42_bits,
  frozen_kernel_1_43_bits,
  frozen_kernel_1_44_bits,
  frozen_kernel_1_45_bits,
  frozen_kernel_1_46_bits,
  frozen_kernel_1_47_bits,
  frozen_kernel_1_48_bits,
  frozen_kernel_1_49_bits,
  frozen_kernel_1_50_bits,
  frozen_kernel_1_51_bits,
  frozen_kernel_1_52_bits,
  frozen_kernel_1_53_bits,
  frozen_kernel_1_54_bits,
  frozen_kernel_1_55_bits,
  frozen_kernel_1_56_bits,
  frozen_kernel_1_57_bits,
  frozen_kernel_1_58_bits,
  frozen_kernel_1_59_bits,
  frozen_kernel_1_60_bits,
  frozen_kernel_1_61_bits,
  frozen_kernel_1_62_bits,
  frozen_kernel_1_63_bits
]

def frozen_kernel_2_bits : List FrozenBitFields := [
  frozen_kernel_2_0_bits,
  frozen_kernel_2_1_bits,
  frozen_kernel_2_2_bits,
  frozen_kernel_2_3_bits,
  frozen_kernel_2_4_bits,
  frozen_kernel_2_5_bits,
  frozen_kernel_2_6_bits,
  frozen_kernel_2_7_bits,
  frozen_kernel_2_8_bits,
  frozen_kernel_2_9_bits,
  frozen_kernel_2_10_bits,
  frozen_kernel_2_11_bits,
  frozen_kernel_2_12_bits,
  frozen_kernel_2_13_bits,
  frozen_kernel_2_14_bits,
  frozen_kernel_2_15_bits,
  frozen_kernel_2_16_bits,
  frozen_kernel_2_17_bits,
  frozen_kernel_2_18_bits,
  frozen_kernel_2_19_bits,
  frozen_kernel_2_20_bits,
  frozen_kernel_2_21_bits,
  frozen_kernel_2_22_bits,
  frozen_kernel_2_23_bits,
  frozen_kernel_2_24_bits,
  frozen_kernel_2_25_bits,
  frozen_kernel_2_26_bits,
  frozen_kernel_2_27_bits,
  frozen_kernel_2_28_bits,
  frozen_kernel_2_29_bits,
  frozen_kernel_2_30_bits,
  frozen_kernel_2_31_bits,
  frozen_kernel_2_32_bits,
  frozen_kernel_2_33_bits,
  frozen_kernel_2_34_bits,
  frozen_kernel_2_35_bits,
  frozen_kernel_2_36_bits,
  frozen_kernel_2_37_bits,
  frozen_kernel_2_38_bits,
  frozen_kernel_2_39_bits,
  frozen_kernel_2_40_bits,
  frozen_kernel_2_41_bits,
  frozen_kernel_2_42_bits,
  frozen_kernel_2_43_bits,
  frozen_kernel_2_44_bits,
  frozen_kernel_2_45_bits,
  frozen_kernel_2_46_bits,
  frozen_kernel_2_47_bits,
  frozen_kernel_2_48_bits,
  frozen_kernel_2_49_bits,
  frozen_kernel_2_50_bits,
  frozen_kernel_2_51_bits,
  frozen_kernel_2_52_bits,
  frozen_kernel_2_53_bits,
  frozen_kernel_2_54_bits,
  frozen_kernel_2_55_bits,
  frozen_kernel_2_56_bits,
  frozen_kernel_2_57_bits,
  frozen_kernel_2_58_bits,
  frozen_kernel_2_59_bits,
  frozen_kernel_2_60_bits,
  frozen_kernel_2_61_bits,
  frozen_kernel_2_62_bits,
  frozen_kernel_2_63_bits
]

def frozen_kernel_3_bits : List FrozenBitFields := [
  frozen_kernel_3_0_bits,
  frozen_kernel_3_1_bits,
  frozen_kernel_3_2_bits,
  frozen_kernel_3_3_bits,
  frozen_kernel_3_4_bits,
  frozen_kernel_3_5_bits,
  frozen_kernel_3_6_bits,
  frozen_kernel_3_7_bits,
  frozen_kernel_3_8_bits,
  frozen_kernel_3_9_bits,
  frozen_kernel_3_10_bits,
  frozen_kernel_3_11_bits,
  frozen_kernel_3_12_bits,
  frozen_kernel_3_13_bits,
  frozen_kernel_3_14_bits,
  frozen_kernel_3_15_bits,
  frozen_kernel_3_16_bits,
  frozen_kernel_3_17_bits,
  frozen_kernel_3_18_bits,
  frozen_kernel_3_19_bits,
  frozen_kernel_3_20_bits,
  frozen_kernel_3_21_bits,
  frozen_kernel_3_22_bits,
  frozen_kernel_3_23_bits,
  frozen_kernel_3_24_bits,
  frozen_kernel_3_25_bits,
  frozen_kernel_3_26_bits,
  frozen_kernel_3_27_bits,
  frozen_kernel_3_28_bits,
  frozen_kernel_3_29_bits,
  frozen_kernel_3_30_bits,
  frozen_kernel_3_31_bits,
  frozen_kernel_3_32_bits,
  frozen_kernel_3_33_bits,
  frozen_kernel_3_34_bits,
  frozen_kernel_3_35_bits,
  frozen_kernel_3_36_bits,
  frozen_kernel_3_37_bits,
  frozen_kernel_3_38_bits,
  frozen_kernel_3_39_bits,
  frozen_kernel_3_40_bits,
  frozen_kernel_3_41_bits,
  frozen_kernel_3_42_bits,
  frozen_kernel_3_43_bits,
  frozen_kernel_3_44_bits,
  frozen_kernel_3_45_bits,
  frozen_kernel_3_46_bits,
  frozen_kernel_3_47_bits,
  frozen_kernel_3_48_bits,
  frozen_kernel_3_49_bits,
  frozen_kernel_3_50_bits,
  frozen_kernel_3_51_bits,
  frozen_kernel_3_52_bits,
  frozen_kernel_3_53_bits,
  frozen_kernel_3_54_bits,
  frozen_kernel_3_55_bits,
  frozen_kernel_3_56_bits,
  frozen_kernel_3_57_bits,
  frozen_kernel_3_58_bits,
  frozen_kernel_3_59_bits,
  frozen_kernel_3_60_bits,
  frozen_kernel_3_61_bits,
  frozen_kernel_3_62_bits,
  frozen_kernel_3_63_bits
]


@[simp] lemma frozen_input_activation_0_finite : ieeeIsFinite frozen_input_activation_0 := by
  simp [frozen_input_activation_0, frozenMake, ieeeIsFinite, binary32Format,
    ieeeExponentMax]

lemma frozen_input_activation_0_small : |ieeeVal frozen_input_activation_0| < 1 := by
  norm_num [frozen_input_activation_0, frozenMake, frozenDecode, ieeeVal,
    ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_1_finite : ieeeIsFinite frozen_input_activation_1 := by
  simp [frozen_input_activation_1, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_1_small : |ieeeVal frozen_input_activation_1| < 1 := by
  norm_num [frozen_input_activation_1, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_2_finite : ieeeIsFinite frozen_input_activation_2 := by
  simp [frozen_input_activation_2, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_2_small : |ieeeVal frozen_input_activation_2| < 1 := by
  norm_num [frozen_input_activation_2, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_3_finite : ieeeIsFinite frozen_input_activation_3 := by
  simp [frozen_input_activation_3, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_3_small : |ieeeVal frozen_input_activation_3| < 1 := by
  norm_num [frozen_input_activation_3, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_4_finite : ieeeIsFinite frozen_input_activation_4 := by
  simp [frozen_input_activation_4, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_4_small : |ieeeVal frozen_input_activation_4| < 1 := by
  norm_num [frozen_input_activation_4, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_5_finite : ieeeIsFinite frozen_input_activation_5 := by
  simp [frozen_input_activation_5, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_5_small : |ieeeVal frozen_input_activation_5| < 1 := by
  norm_num [frozen_input_activation_5, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_6_finite : ieeeIsFinite frozen_input_activation_6 := by
  simp [frozen_input_activation_6, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_6_small : |ieeeVal frozen_input_activation_6| < 1 := by
  norm_num [frozen_input_activation_6, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_7_finite : ieeeIsFinite frozen_input_activation_7 := by
  simp [frozen_input_activation_7, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_7_small : |ieeeVal frozen_input_activation_7| < 1 := by
  norm_num [frozen_input_activation_7, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_8_finite : ieeeIsFinite frozen_input_activation_8 := by
  simp [frozen_input_activation_8, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_8_small : |ieeeVal frozen_input_activation_8| < 1 := by
  norm_num [frozen_input_activation_8, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_9_finite : ieeeIsFinite frozen_input_activation_9 := by
  simp [frozen_input_activation_9, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_9_small : |ieeeVal frozen_input_activation_9| < 1 := by
  norm_num [frozen_input_activation_9, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_10_finite : ieeeIsFinite frozen_input_activation_10 := by
  simp [frozen_input_activation_10, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_10_small : |ieeeVal frozen_input_activation_10| < 1 := by
  norm_num [frozen_input_activation_10, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_11_finite : ieeeIsFinite frozen_input_activation_11 := by
  simp [frozen_input_activation_11, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_11_small : |ieeeVal frozen_input_activation_11| < 1 := by
  norm_num [frozen_input_activation_11, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_12_finite : ieeeIsFinite frozen_input_activation_12 := by
  simp [frozen_input_activation_12, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_12_small : |ieeeVal frozen_input_activation_12| < 1 := by
  norm_num [frozen_input_activation_12, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_13_finite : ieeeIsFinite frozen_input_activation_13 := by
  simp [frozen_input_activation_13, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_13_small : |ieeeVal frozen_input_activation_13| < 1 := by
  norm_num [frozen_input_activation_13, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_14_finite : ieeeIsFinite frozen_input_activation_14 := by
  simp [frozen_input_activation_14, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_14_small : |ieeeVal frozen_input_activation_14| < 1 := by
  norm_num [frozen_input_activation_14, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_15_finite : ieeeIsFinite frozen_input_activation_15 := by
  simp [frozen_input_activation_15, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_15_small : |ieeeVal frozen_input_activation_15| < 1 := by
  norm_num [frozen_input_activation_15, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_16_finite : ieeeIsFinite frozen_input_activation_16 := by
  simp [frozen_input_activation_16, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_16_small : |ieeeVal frozen_input_activation_16| < 1 := by
  norm_num [frozen_input_activation_16, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_17_finite : ieeeIsFinite frozen_input_activation_17 := by
  simp [frozen_input_activation_17, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_17_small : |ieeeVal frozen_input_activation_17| < 1 := by
  norm_num [frozen_input_activation_17, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_18_finite : ieeeIsFinite frozen_input_activation_18 := by
  simp [frozen_input_activation_18, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_18_small : |ieeeVal frozen_input_activation_18| < 1 := by
  norm_num [frozen_input_activation_18, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_19_finite : ieeeIsFinite frozen_input_activation_19 := by
  simp [frozen_input_activation_19, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_19_small : |ieeeVal frozen_input_activation_19| < 1 := by
  norm_num [frozen_input_activation_19, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_20_finite : ieeeIsFinite frozen_input_activation_20 := by
  simp [frozen_input_activation_20, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_20_small : |ieeeVal frozen_input_activation_20| < 1 := by
  norm_num [frozen_input_activation_20, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_21_finite : ieeeIsFinite frozen_input_activation_21 := by
  simp [frozen_input_activation_21, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_21_small : |ieeeVal frozen_input_activation_21| < 1 := by
  norm_num [frozen_input_activation_21, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_22_finite : ieeeIsFinite frozen_input_activation_22 := by
  simp [frozen_input_activation_22, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_22_small : |ieeeVal frozen_input_activation_22| < 1 := by
  norm_num [frozen_input_activation_22, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_23_finite : ieeeIsFinite frozen_input_activation_23 := by
  simp [frozen_input_activation_23, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_23_small : |ieeeVal frozen_input_activation_23| < 1 := by
  norm_num [frozen_input_activation_23, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_24_finite : ieeeIsFinite frozen_input_activation_24 := by
  simp [frozen_input_activation_24, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_24_small : |ieeeVal frozen_input_activation_24| < 1 := by
  norm_num [frozen_input_activation_24, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_25_finite : ieeeIsFinite frozen_input_activation_25 := by
  simp [frozen_input_activation_25, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_25_small : |ieeeVal frozen_input_activation_25| < 1 := by
  norm_num [frozen_input_activation_25, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_26_finite : ieeeIsFinite frozen_input_activation_26 := by
  simp [frozen_input_activation_26, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_26_small : |ieeeVal frozen_input_activation_26| < 1 := by
  norm_num [frozen_input_activation_26, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_27_finite : ieeeIsFinite frozen_input_activation_27 := by
  simp [frozen_input_activation_27, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_27_small : |ieeeVal frozen_input_activation_27| < 1 := by
  norm_num [frozen_input_activation_27, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_28_finite : ieeeIsFinite frozen_input_activation_28 := by
  simp [frozen_input_activation_28, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_28_small : |ieeeVal frozen_input_activation_28| < 1 := by
  norm_num [frozen_input_activation_28, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_29_finite : ieeeIsFinite frozen_input_activation_29 := by
  simp [frozen_input_activation_29, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_29_small : |ieeeVal frozen_input_activation_29| < 1 := by
  norm_num [frozen_input_activation_29, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_30_finite : ieeeIsFinite frozen_input_activation_30 := by
  simp [frozen_input_activation_30, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_30_small : |ieeeVal frozen_input_activation_30| < 1 := by
  norm_num [frozen_input_activation_30, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_31_finite : ieeeIsFinite frozen_input_activation_31 := by
  simp [frozen_input_activation_31, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_31_small : |ieeeVal frozen_input_activation_31| < 1 := by
  norm_num [frozen_input_activation_31, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_32_finite : ieeeIsFinite frozen_input_activation_32 := by
  simp [frozen_input_activation_32, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_32_small : |ieeeVal frozen_input_activation_32| < 1 := by
  norm_num [frozen_input_activation_32, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_33_finite : ieeeIsFinite frozen_input_activation_33 := by
  simp [frozen_input_activation_33, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_33_small : |ieeeVal frozen_input_activation_33| < 1 := by
  norm_num [frozen_input_activation_33, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_34_finite : ieeeIsFinite frozen_input_activation_34 := by
  simp [frozen_input_activation_34, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_34_small : |ieeeVal frozen_input_activation_34| < 1 := by
  norm_num [frozen_input_activation_34, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_35_finite : ieeeIsFinite frozen_input_activation_35 := by
  simp [frozen_input_activation_35, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_35_small : |ieeeVal frozen_input_activation_35| < 1 := by
  norm_num [frozen_input_activation_35, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_36_finite : ieeeIsFinite frozen_input_activation_36 := by
  simp [frozen_input_activation_36, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_36_small : |ieeeVal frozen_input_activation_36| < 1 := by
  norm_num [frozen_input_activation_36, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_37_finite : ieeeIsFinite frozen_input_activation_37 := by
  simp [frozen_input_activation_37, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_37_small : |ieeeVal frozen_input_activation_37| < 1 := by
  norm_num [frozen_input_activation_37, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_38_finite : ieeeIsFinite frozen_input_activation_38 := by
  simp [frozen_input_activation_38, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_38_small : |ieeeVal frozen_input_activation_38| < 1 := by
  norm_num [frozen_input_activation_38, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_39_finite : ieeeIsFinite frozen_input_activation_39 := by
  simp [frozen_input_activation_39, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_39_small : |ieeeVal frozen_input_activation_39| < 1 := by
  norm_num [frozen_input_activation_39, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_40_finite : ieeeIsFinite frozen_input_activation_40 := by
  simp [frozen_input_activation_40, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_40_small : |ieeeVal frozen_input_activation_40| < 1 := by
  norm_num [frozen_input_activation_40, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_41_finite : ieeeIsFinite frozen_input_activation_41 := by
  simp [frozen_input_activation_41, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_41_small : |ieeeVal frozen_input_activation_41| < 1 := by
  norm_num [frozen_input_activation_41, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_42_finite : ieeeIsFinite frozen_input_activation_42 := by
  simp [frozen_input_activation_42, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_42_small : |ieeeVal frozen_input_activation_42| < 1 := by
  norm_num [frozen_input_activation_42, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_43_finite : ieeeIsFinite frozen_input_activation_43 := by
  simp [frozen_input_activation_43, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_43_small : |ieeeVal frozen_input_activation_43| < 1 := by
  norm_num [frozen_input_activation_43, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_44_finite : ieeeIsFinite frozen_input_activation_44 := by
  simp [frozen_input_activation_44, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_44_small : |ieeeVal frozen_input_activation_44| < 1 := by
  norm_num [frozen_input_activation_44, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_45_finite : ieeeIsFinite frozen_input_activation_45 := by
  simp [frozen_input_activation_45, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_45_small : |ieeeVal frozen_input_activation_45| < 1 := by
  norm_num [frozen_input_activation_45, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_46_finite : ieeeIsFinite frozen_input_activation_46 := by
  simp [frozen_input_activation_46, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_46_small : |ieeeVal frozen_input_activation_46| < 1 := by
  norm_num [frozen_input_activation_46, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_47_finite : ieeeIsFinite frozen_input_activation_47 := by
  simp [frozen_input_activation_47, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_47_small : |ieeeVal frozen_input_activation_47| < 1 := by
  norm_num [frozen_input_activation_47, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_48_finite : ieeeIsFinite frozen_input_activation_48 := by
  simp [frozen_input_activation_48, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_48_small : |ieeeVal frozen_input_activation_48| < 1 := by
  norm_num [frozen_input_activation_48, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_49_finite : ieeeIsFinite frozen_input_activation_49 := by
  simp [frozen_input_activation_49, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_49_small : |ieeeVal frozen_input_activation_49| < 1 := by
  norm_num [frozen_input_activation_49, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_50_finite : ieeeIsFinite frozen_input_activation_50 := by
  simp [frozen_input_activation_50, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_50_small : |ieeeVal frozen_input_activation_50| < 1 := by
  norm_num [frozen_input_activation_50, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_51_finite : ieeeIsFinite frozen_input_activation_51 := by
  simp [frozen_input_activation_51, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_51_small : |ieeeVal frozen_input_activation_51| < 1 := by
  norm_num [frozen_input_activation_51, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_52_finite : ieeeIsFinite frozen_input_activation_52 := by
  simp [frozen_input_activation_52, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_52_small : |ieeeVal frozen_input_activation_52| < 1 := by
  norm_num [frozen_input_activation_52, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_53_finite : ieeeIsFinite frozen_input_activation_53 := by
  simp [frozen_input_activation_53, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_53_small : |ieeeVal frozen_input_activation_53| < 1 := by
  norm_num [frozen_input_activation_53, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_54_finite : ieeeIsFinite frozen_input_activation_54 := by
  simp [frozen_input_activation_54, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_54_small : |ieeeVal frozen_input_activation_54| < 1 := by
  norm_num [frozen_input_activation_54, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_55_finite : ieeeIsFinite frozen_input_activation_55 := by
  simp [frozen_input_activation_55, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_55_small : |ieeeVal frozen_input_activation_55| < 1 := by
  norm_num [frozen_input_activation_55, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_56_finite : ieeeIsFinite frozen_input_activation_56 := by
  simp [frozen_input_activation_56, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_56_small : |ieeeVal frozen_input_activation_56| < 1 := by
  norm_num [frozen_input_activation_56, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_57_finite : ieeeIsFinite frozen_input_activation_57 := by
  simp [frozen_input_activation_57, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_57_small : |ieeeVal frozen_input_activation_57| < 1 := by
  norm_num [frozen_input_activation_57, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_58_finite : ieeeIsFinite frozen_input_activation_58 := by
  simp [frozen_input_activation_58, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_58_small : |ieeeVal frozen_input_activation_58| < 1 := by
  norm_num [frozen_input_activation_58, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_59_finite : ieeeIsFinite frozen_input_activation_59 := by
  simp [frozen_input_activation_59, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_59_small : |ieeeVal frozen_input_activation_59| < 1 := by
  norm_num [frozen_input_activation_59, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_60_finite : ieeeIsFinite frozen_input_activation_60 := by
  simp [frozen_input_activation_60, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_60_small : |ieeeVal frozen_input_activation_60| < 1 := by
  norm_num [frozen_input_activation_60, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_61_finite : ieeeIsFinite frozen_input_activation_61 := by
  simp [frozen_input_activation_61, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_61_small : |ieeeVal frozen_input_activation_61| < 1 := by
  norm_num [frozen_input_activation_61, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_62_finite : ieeeIsFinite frozen_input_activation_62 := by
  simp [frozen_input_activation_62, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_62_small : |ieeeVal frozen_input_activation_62| < 1 := by
  norm_num [frozen_input_activation_62, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_input_activation_63_finite : ieeeIsFinite frozen_input_activation_63 := by
  simp [frozen_input_activation_63, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_input_activation_63_small : |ieeeVal frozen_input_activation_63| < 1 := by
  norm_num [frozen_input_activation_63, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_0_finite : ieeeIsFinite frozen_kernel_0_0 := by
  simp [frozen_kernel_0_0, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_0_small : |ieeeVal frozen_kernel_0_0| < 1 := by
  norm_num [frozen_kernel_0_0, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_1_finite : ieeeIsFinite frozen_kernel_0_1 := by
  simp [frozen_kernel_0_1, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_1_small : |ieeeVal frozen_kernel_0_1| < 1 := by
  norm_num [frozen_kernel_0_1, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_2_finite : ieeeIsFinite frozen_kernel_0_2 := by
  simp [frozen_kernel_0_2, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_2_small : |ieeeVal frozen_kernel_0_2| < 1 := by
  norm_num [frozen_kernel_0_2, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_3_finite : ieeeIsFinite frozen_kernel_0_3 := by
  simp [frozen_kernel_0_3, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_3_small : |ieeeVal frozen_kernel_0_3| < 1 := by
  norm_num [frozen_kernel_0_3, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_4_finite : ieeeIsFinite frozen_kernel_0_4 := by
  simp [frozen_kernel_0_4, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_4_small : |ieeeVal frozen_kernel_0_4| < 1 := by
  norm_num [frozen_kernel_0_4, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_5_finite : ieeeIsFinite frozen_kernel_0_5 := by
  simp [frozen_kernel_0_5, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_5_small : |ieeeVal frozen_kernel_0_5| < 1 := by
  norm_num [frozen_kernel_0_5, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_6_finite : ieeeIsFinite frozen_kernel_0_6 := by
  simp [frozen_kernel_0_6, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_6_small : |ieeeVal frozen_kernel_0_6| < 1 := by
  norm_num [frozen_kernel_0_6, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_7_finite : ieeeIsFinite frozen_kernel_0_7 := by
  simp [frozen_kernel_0_7, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_7_small : |ieeeVal frozen_kernel_0_7| < 1 := by
  norm_num [frozen_kernel_0_7, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_8_finite : ieeeIsFinite frozen_kernel_0_8 := by
  simp [frozen_kernel_0_8, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_8_small : |ieeeVal frozen_kernel_0_8| < 1 := by
  norm_num [frozen_kernel_0_8, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_9_finite : ieeeIsFinite frozen_kernel_0_9 := by
  simp [frozen_kernel_0_9, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_9_small : |ieeeVal frozen_kernel_0_9| < 1 := by
  norm_num [frozen_kernel_0_9, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_10_finite : ieeeIsFinite frozen_kernel_0_10 := by
  simp [frozen_kernel_0_10, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_10_small : |ieeeVal frozen_kernel_0_10| < 1 := by
  norm_num [frozen_kernel_0_10, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_11_finite : ieeeIsFinite frozen_kernel_0_11 := by
  simp [frozen_kernel_0_11, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_11_small : |ieeeVal frozen_kernel_0_11| < 1 := by
  norm_num [frozen_kernel_0_11, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_12_finite : ieeeIsFinite frozen_kernel_0_12 := by
  simp [frozen_kernel_0_12, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_12_small : |ieeeVal frozen_kernel_0_12| < 1 := by
  norm_num [frozen_kernel_0_12, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_13_finite : ieeeIsFinite frozen_kernel_0_13 := by
  simp [frozen_kernel_0_13, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_13_small : |ieeeVal frozen_kernel_0_13| < 1 := by
  norm_num [frozen_kernel_0_13, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_14_finite : ieeeIsFinite frozen_kernel_0_14 := by
  simp [frozen_kernel_0_14, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_14_small : |ieeeVal frozen_kernel_0_14| < 1 := by
  norm_num [frozen_kernel_0_14, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_15_finite : ieeeIsFinite frozen_kernel_0_15 := by
  simp [frozen_kernel_0_15, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_15_small : |ieeeVal frozen_kernel_0_15| < 1 := by
  norm_num [frozen_kernel_0_15, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_16_finite : ieeeIsFinite frozen_kernel_0_16 := by
  simp [frozen_kernel_0_16, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_16_small : |ieeeVal frozen_kernel_0_16| < 1 := by
  norm_num [frozen_kernel_0_16, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_17_finite : ieeeIsFinite frozen_kernel_0_17 := by
  simp [frozen_kernel_0_17, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_17_small : |ieeeVal frozen_kernel_0_17| < 1 := by
  norm_num [frozen_kernel_0_17, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_18_finite : ieeeIsFinite frozen_kernel_0_18 := by
  simp [frozen_kernel_0_18, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_18_small : |ieeeVal frozen_kernel_0_18| < 1 := by
  norm_num [frozen_kernel_0_18, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_19_finite : ieeeIsFinite frozen_kernel_0_19 := by
  simp [frozen_kernel_0_19, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_19_small : |ieeeVal frozen_kernel_0_19| < 1 := by
  norm_num [frozen_kernel_0_19, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_20_finite : ieeeIsFinite frozen_kernel_0_20 := by
  simp [frozen_kernel_0_20, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_20_small : |ieeeVal frozen_kernel_0_20| < 1 := by
  norm_num [frozen_kernel_0_20, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_21_finite : ieeeIsFinite frozen_kernel_0_21 := by
  simp [frozen_kernel_0_21, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_21_small : |ieeeVal frozen_kernel_0_21| < 1 := by
  norm_num [frozen_kernel_0_21, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_22_finite : ieeeIsFinite frozen_kernel_0_22 := by
  simp [frozen_kernel_0_22, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_22_small : |ieeeVal frozen_kernel_0_22| < 1 := by
  norm_num [frozen_kernel_0_22, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_23_finite : ieeeIsFinite frozen_kernel_0_23 := by
  simp [frozen_kernel_0_23, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_23_small : |ieeeVal frozen_kernel_0_23| < 1 := by
  norm_num [frozen_kernel_0_23, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_24_finite : ieeeIsFinite frozen_kernel_0_24 := by
  simp [frozen_kernel_0_24, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_24_small : |ieeeVal frozen_kernel_0_24| < 1 := by
  norm_num [frozen_kernel_0_24, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_25_finite : ieeeIsFinite frozen_kernel_0_25 := by
  simp [frozen_kernel_0_25, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_25_small : |ieeeVal frozen_kernel_0_25| < 1 := by
  norm_num [frozen_kernel_0_25, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_26_finite : ieeeIsFinite frozen_kernel_0_26 := by
  simp [frozen_kernel_0_26, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_26_small : |ieeeVal frozen_kernel_0_26| < 1 := by
  norm_num [frozen_kernel_0_26, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_27_finite : ieeeIsFinite frozen_kernel_0_27 := by
  simp [frozen_kernel_0_27, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_27_small : |ieeeVal frozen_kernel_0_27| < 1 := by
  norm_num [frozen_kernel_0_27, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_28_finite : ieeeIsFinite frozen_kernel_0_28 := by
  simp [frozen_kernel_0_28, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_28_small : |ieeeVal frozen_kernel_0_28| < 1 := by
  norm_num [frozen_kernel_0_28, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_29_finite : ieeeIsFinite frozen_kernel_0_29 := by
  simp [frozen_kernel_0_29, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_29_small : |ieeeVal frozen_kernel_0_29| < 1 := by
  norm_num [frozen_kernel_0_29, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_30_finite : ieeeIsFinite frozen_kernel_0_30 := by
  simp [frozen_kernel_0_30, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_30_small : |ieeeVal frozen_kernel_0_30| < 1 := by
  norm_num [frozen_kernel_0_30, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_31_finite : ieeeIsFinite frozen_kernel_0_31 := by
  simp [frozen_kernel_0_31, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_31_small : |ieeeVal frozen_kernel_0_31| < 1 := by
  norm_num [frozen_kernel_0_31, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_32_finite : ieeeIsFinite frozen_kernel_0_32 := by
  simp [frozen_kernel_0_32, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_32_small : |ieeeVal frozen_kernel_0_32| < 1 := by
  norm_num [frozen_kernel_0_32, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_33_finite : ieeeIsFinite frozen_kernel_0_33 := by
  simp [frozen_kernel_0_33, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_33_small : |ieeeVal frozen_kernel_0_33| < 1 := by
  norm_num [frozen_kernel_0_33, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_34_finite : ieeeIsFinite frozen_kernel_0_34 := by
  simp [frozen_kernel_0_34, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_34_small : |ieeeVal frozen_kernel_0_34| < 1 := by
  norm_num [frozen_kernel_0_34, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_35_finite : ieeeIsFinite frozen_kernel_0_35 := by
  simp [frozen_kernel_0_35, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_35_small : |ieeeVal frozen_kernel_0_35| < 1 := by
  norm_num [frozen_kernel_0_35, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_36_finite : ieeeIsFinite frozen_kernel_0_36 := by
  simp [frozen_kernel_0_36, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_36_small : |ieeeVal frozen_kernel_0_36| < 1 := by
  norm_num [frozen_kernel_0_36, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_37_finite : ieeeIsFinite frozen_kernel_0_37 := by
  simp [frozen_kernel_0_37, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_37_small : |ieeeVal frozen_kernel_0_37| < 1 := by
  norm_num [frozen_kernel_0_37, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_38_finite : ieeeIsFinite frozen_kernel_0_38 := by
  simp [frozen_kernel_0_38, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_38_small : |ieeeVal frozen_kernel_0_38| < 1 := by
  norm_num [frozen_kernel_0_38, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_39_finite : ieeeIsFinite frozen_kernel_0_39 := by
  simp [frozen_kernel_0_39, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_39_small : |ieeeVal frozen_kernel_0_39| < 1 := by
  norm_num [frozen_kernel_0_39, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_40_finite : ieeeIsFinite frozen_kernel_0_40 := by
  simp [frozen_kernel_0_40, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_40_small : |ieeeVal frozen_kernel_0_40| < 1 := by
  norm_num [frozen_kernel_0_40, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_41_finite : ieeeIsFinite frozen_kernel_0_41 := by
  simp [frozen_kernel_0_41, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_41_small : |ieeeVal frozen_kernel_0_41| < 1 := by
  norm_num [frozen_kernel_0_41, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_42_finite : ieeeIsFinite frozen_kernel_0_42 := by
  simp [frozen_kernel_0_42, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_42_small : |ieeeVal frozen_kernel_0_42| < 1 := by
  norm_num [frozen_kernel_0_42, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_43_finite : ieeeIsFinite frozen_kernel_0_43 := by
  simp [frozen_kernel_0_43, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_43_small : |ieeeVal frozen_kernel_0_43| < 1 := by
  norm_num [frozen_kernel_0_43, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_44_finite : ieeeIsFinite frozen_kernel_0_44 := by
  simp [frozen_kernel_0_44, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_44_small : |ieeeVal frozen_kernel_0_44| < 1 := by
  norm_num [frozen_kernel_0_44, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_45_finite : ieeeIsFinite frozen_kernel_0_45 := by
  simp [frozen_kernel_0_45, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_45_small : |ieeeVal frozen_kernel_0_45| < 1 := by
  norm_num [frozen_kernel_0_45, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_46_finite : ieeeIsFinite frozen_kernel_0_46 := by
  simp [frozen_kernel_0_46, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_46_small : |ieeeVal frozen_kernel_0_46| < 1 := by
  norm_num [frozen_kernel_0_46, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_47_finite : ieeeIsFinite frozen_kernel_0_47 := by
  simp [frozen_kernel_0_47, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_47_small : |ieeeVal frozen_kernel_0_47| < 1 := by
  norm_num [frozen_kernel_0_47, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_48_finite : ieeeIsFinite frozen_kernel_0_48 := by
  simp [frozen_kernel_0_48, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_48_small : |ieeeVal frozen_kernel_0_48| < 1 := by
  norm_num [frozen_kernel_0_48, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_49_finite : ieeeIsFinite frozen_kernel_0_49 := by
  simp [frozen_kernel_0_49, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_49_small : |ieeeVal frozen_kernel_0_49| < 1 := by
  norm_num [frozen_kernel_0_49, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_50_finite : ieeeIsFinite frozen_kernel_0_50 := by
  simp [frozen_kernel_0_50, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_50_small : |ieeeVal frozen_kernel_0_50| < 1 := by
  norm_num [frozen_kernel_0_50, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_51_finite : ieeeIsFinite frozen_kernel_0_51 := by
  simp [frozen_kernel_0_51, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_51_small : |ieeeVal frozen_kernel_0_51| < 1 := by
  norm_num [frozen_kernel_0_51, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_52_finite : ieeeIsFinite frozen_kernel_0_52 := by
  simp [frozen_kernel_0_52, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_52_small : |ieeeVal frozen_kernel_0_52| < 1 := by
  norm_num [frozen_kernel_0_52, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_53_finite : ieeeIsFinite frozen_kernel_0_53 := by
  simp [frozen_kernel_0_53, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_53_small : |ieeeVal frozen_kernel_0_53| < 1 := by
  norm_num [frozen_kernel_0_53, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_54_finite : ieeeIsFinite frozen_kernel_0_54 := by
  simp [frozen_kernel_0_54, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_54_small : |ieeeVal frozen_kernel_0_54| < 1 := by
  norm_num [frozen_kernel_0_54, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_55_finite : ieeeIsFinite frozen_kernel_0_55 := by
  simp [frozen_kernel_0_55, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_55_small : |ieeeVal frozen_kernel_0_55| < 1 := by
  norm_num [frozen_kernel_0_55, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_56_finite : ieeeIsFinite frozen_kernel_0_56 := by
  simp [frozen_kernel_0_56, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_56_small : |ieeeVal frozen_kernel_0_56| < 1 := by
  norm_num [frozen_kernel_0_56, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_57_finite : ieeeIsFinite frozen_kernel_0_57 := by
  simp [frozen_kernel_0_57, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_57_small : |ieeeVal frozen_kernel_0_57| < 1 := by
  norm_num [frozen_kernel_0_57, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_58_finite : ieeeIsFinite frozen_kernel_0_58 := by
  simp [frozen_kernel_0_58, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_58_small : |ieeeVal frozen_kernel_0_58| < 1 := by
  norm_num [frozen_kernel_0_58, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_59_finite : ieeeIsFinite frozen_kernel_0_59 := by
  simp [frozen_kernel_0_59, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_59_small : |ieeeVal frozen_kernel_0_59| < 1 := by
  norm_num [frozen_kernel_0_59, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_60_finite : ieeeIsFinite frozen_kernel_0_60 := by
  simp [frozen_kernel_0_60, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_60_small : |ieeeVal frozen_kernel_0_60| < 1 := by
  norm_num [frozen_kernel_0_60, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_61_finite : ieeeIsFinite frozen_kernel_0_61 := by
  simp [frozen_kernel_0_61, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_61_small : |ieeeVal frozen_kernel_0_61| < 1 := by
  norm_num [frozen_kernel_0_61, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_62_finite : ieeeIsFinite frozen_kernel_0_62 := by
  simp [frozen_kernel_0_62, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_62_small : |ieeeVal frozen_kernel_0_62| < 1 := by
  norm_num [frozen_kernel_0_62, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_0_63_finite : ieeeIsFinite frozen_kernel_0_63 := by
  simp [frozen_kernel_0_63, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_0_63_small : |ieeeVal frozen_kernel_0_63| < 1 := by
  norm_num [frozen_kernel_0_63, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_0_finite : ieeeIsFinite frozen_kernel_1_0 := by
  simp [frozen_kernel_1_0, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_0_small : |ieeeVal frozen_kernel_1_0| < 1 := by
  norm_num [frozen_kernel_1_0, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_1_finite : ieeeIsFinite frozen_kernel_1_1 := by
  simp [frozen_kernel_1_1, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_1_small : |ieeeVal frozen_kernel_1_1| < 1 := by
  norm_num [frozen_kernel_1_1, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_2_finite : ieeeIsFinite frozen_kernel_1_2 := by
  simp [frozen_kernel_1_2, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_2_small : |ieeeVal frozen_kernel_1_2| < 1 := by
  norm_num [frozen_kernel_1_2, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_3_finite : ieeeIsFinite frozen_kernel_1_3 := by
  simp [frozen_kernel_1_3, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_3_small : |ieeeVal frozen_kernel_1_3| < 1 := by
  norm_num [frozen_kernel_1_3, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_4_finite : ieeeIsFinite frozen_kernel_1_4 := by
  simp [frozen_kernel_1_4, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_4_small : |ieeeVal frozen_kernel_1_4| < 1 := by
  norm_num [frozen_kernel_1_4, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_5_finite : ieeeIsFinite frozen_kernel_1_5 := by
  simp [frozen_kernel_1_5, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_5_small : |ieeeVal frozen_kernel_1_5| < 1 := by
  norm_num [frozen_kernel_1_5, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_6_finite : ieeeIsFinite frozen_kernel_1_6 := by
  simp [frozen_kernel_1_6, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_6_small : |ieeeVal frozen_kernel_1_6| < 1 := by
  norm_num [frozen_kernel_1_6, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_7_finite : ieeeIsFinite frozen_kernel_1_7 := by
  simp [frozen_kernel_1_7, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_7_small : |ieeeVal frozen_kernel_1_7| < 1 := by
  norm_num [frozen_kernel_1_7, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_8_finite : ieeeIsFinite frozen_kernel_1_8 := by
  simp [frozen_kernel_1_8, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_8_small : |ieeeVal frozen_kernel_1_8| < 1 := by
  norm_num [frozen_kernel_1_8, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_9_finite : ieeeIsFinite frozen_kernel_1_9 := by
  simp [frozen_kernel_1_9, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_9_small : |ieeeVal frozen_kernel_1_9| < 1 := by
  norm_num [frozen_kernel_1_9, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_10_finite : ieeeIsFinite frozen_kernel_1_10 := by
  simp [frozen_kernel_1_10, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_10_small : |ieeeVal frozen_kernel_1_10| < 1 := by
  norm_num [frozen_kernel_1_10, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_11_finite : ieeeIsFinite frozen_kernel_1_11 := by
  simp [frozen_kernel_1_11, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_11_small : |ieeeVal frozen_kernel_1_11| < 1 := by
  norm_num [frozen_kernel_1_11, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_12_finite : ieeeIsFinite frozen_kernel_1_12 := by
  simp [frozen_kernel_1_12, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_12_small : |ieeeVal frozen_kernel_1_12| < 1 := by
  norm_num [frozen_kernel_1_12, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_13_finite : ieeeIsFinite frozen_kernel_1_13 := by
  simp [frozen_kernel_1_13, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_13_small : |ieeeVal frozen_kernel_1_13| < 1 := by
  norm_num [frozen_kernel_1_13, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_14_finite : ieeeIsFinite frozen_kernel_1_14 := by
  simp [frozen_kernel_1_14, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_14_small : |ieeeVal frozen_kernel_1_14| < 1 := by
  norm_num [frozen_kernel_1_14, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_15_finite : ieeeIsFinite frozen_kernel_1_15 := by
  simp [frozen_kernel_1_15, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_15_small : |ieeeVal frozen_kernel_1_15| < 1 := by
  norm_num [frozen_kernel_1_15, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_16_finite : ieeeIsFinite frozen_kernel_1_16 := by
  simp [frozen_kernel_1_16, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_16_small : |ieeeVal frozen_kernel_1_16| < 1 := by
  norm_num [frozen_kernel_1_16, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_17_finite : ieeeIsFinite frozen_kernel_1_17 := by
  simp [frozen_kernel_1_17, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_17_small : |ieeeVal frozen_kernel_1_17| < 1 := by
  norm_num [frozen_kernel_1_17, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_18_finite : ieeeIsFinite frozen_kernel_1_18 := by
  simp [frozen_kernel_1_18, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_18_small : |ieeeVal frozen_kernel_1_18| < 1 := by
  norm_num [frozen_kernel_1_18, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_19_finite : ieeeIsFinite frozen_kernel_1_19 := by
  simp [frozen_kernel_1_19, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_19_small : |ieeeVal frozen_kernel_1_19| < 1 := by
  norm_num [frozen_kernel_1_19, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_20_finite : ieeeIsFinite frozen_kernel_1_20 := by
  simp [frozen_kernel_1_20, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_20_small : |ieeeVal frozen_kernel_1_20| < 1 := by
  norm_num [frozen_kernel_1_20, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_21_finite : ieeeIsFinite frozen_kernel_1_21 := by
  simp [frozen_kernel_1_21, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_21_small : |ieeeVal frozen_kernel_1_21| < 1 := by
  norm_num [frozen_kernel_1_21, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_22_finite : ieeeIsFinite frozen_kernel_1_22 := by
  simp [frozen_kernel_1_22, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_22_small : |ieeeVal frozen_kernel_1_22| < 1 := by
  norm_num [frozen_kernel_1_22, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_23_finite : ieeeIsFinite frozen_kernel_1_23 := by
  simp [frozen_kernel_1_23, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_23_small : |ieeeVal frozen_kernel_1_23| < 1 := by
  norm_num [frozen_kernel_1_23, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_24_finite : ieeeIsFinite frozen_kernel_1_24 := by
  simp [frozen_kernel_1_24, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_24_small : |ieeeVal frozen_kernel_1_24| < 1 := by
  norm_num [frozen_kernel_1_24, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_25_finite : ieeeIsFinite frozen_kernel_1_25 := by
  simp [frozen_kernel_1_25, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_25_small : |ieeeVal frozen_kernel_1_25| < 1 := by
  norm_num [frozen_kernel_1_25, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_26_finite : ieeeIsFinite frozen_kernel_1_26 := by
  simp [frozen_kernel_1_26, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_26_small : |ieeeVal frozen_kernel_1_26| < 1 := by
  norm_num [frozen_kernel_1_26, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_27_finite : ieeeIsFinite frozen_kernel_1_27 := by
  simp [frozen_kernel_1_27, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_27_small : |ieeeVal frozen_kernel_1_27| < 1 := by
  norm_num [frozen_kernel_1_27, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_28_finite : ieeeIsFinite frozen_kernel_1_28 := by
  simp [frozen_kernel_1_28, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_28_small : |ieeeVal frozen_kernel_1_28| < 1 := by
  norm_num [frozen_kernel_1_28, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_29_finite : ieeeIsFinite frozen_kernel_1_29 := by
  simp [frozen_kernel_1_29, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_29_small : |ieeeVal frozen_kernel_1_29| < 1 := by
  norm_num [frozen_kernel_1_29, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_30_finite : ieeeIsFinite frozen_kernel_1_30 := by
  simp [frozen_kernel_1_30, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_30_small : |ieeeVal frozen_kernel_1_30| < 1 := by
  norm_num [frozen_kernel_1_30, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_31_finite : ieeeIsFinite frozen_kernel_1_31 := by
  simp [frozen_kernel_1_31, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_31_small : |ieeeVal frozen_kernel_1_31| < 1 := by
  norm_num [frozen_kernel_1_31, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_32_finite : ieeeIsFinite frozen_kernel_1_32 := by
  simp [frozen_kernel_1_32, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_32_small : |ieeeVal frozen_kernel_1_32| < 1 := by
  norm_num [frozen_kernel_1_32, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_33_finite : ieeeIsFinite frozen_kernel_1_33 := by
  simp [frozen_kernel_1_33, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_33_small : |ieeeVal frozen_kernel_1_33| < 1 := by
  norm_num [frozen_kernel_1_33, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_34_finite : ieeeIsFinite frozen_kernel_1_34 := by
  simp [frozen_kernel_1_34, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_34_small : |ieeeVal frozen_kernel_1_34| < 1 := by
  norm_num [frozen_kernel_1_34, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_35_finite : ieeeIsFinite frozen_kernel_1_35 := by
  simp [frozen_kernel_1_35, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_35_small : |ieeeVal frozen_kernel_1_35| < 1 := by
  norm_num [frozen_kernel_1_35, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_36_finite : ieeeIsFinite frozen_kernel_1_36 := by
  simp [frozen_kernel_1_36, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_36_small : |ieeeVal frozen_kernel_1_36| < 1 := by
  norm_num [frozen_kernel_1_36, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_37_finite : ieeeIsFinite frozen_kernel_1_37 := by
  simp [frozen_kernel_1_37, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_37_small : |ieeeVal frozen_kernel_1_37| < 1 := by
  norm_num [frozen_kernel_1_37, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_38_finite : ieeeIsFinite frozen_kernel_1_38 := by
  simp [frozen_kernel_1_38, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_38_small : |ieeeVal frozen_kernel_1_38| < 1 := by
  norm_num [frozen_kernel_1_38, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_39_finite : ieeeIsFinite frozen_kernel_1_39 := by
  simp [frozen_kernel_1_39, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_39_small : |ieeeVal frozen_kernel_1_39| < 1 := by
  norm_num [frozen_kernel_1_39, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_40_finite : ieeeIsFinite frozen_kernel_1_40 := by
  simp [frozen_kernel_1_40, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_40_small : |ieeeVal frozen_kernel_1_40| < 1 := by
  norm_num [frozen_kernel_1_40, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_41_finite : ieeeIsFinite frozen_kernel_1_41 := by
  simp [frozen_kernel_1_41, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_41_small : |ieeeVal frozen_kernel_1_41| < 1 := by
  norm_num [frozen_kernel_1_41, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_42_finite : ieeeIsFinite frozen_kernel_1_42 := by
  simp [frozen_kernel_1_42, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_42_small : |ieeeVal frozen_kernel_1_42| < 1 := by
  norm_num [frozen_kernel_1_42, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_43_finite : ieeeIsFinite frozen_kernel_1_43 := by
  simp [frozen_kernel_1_43, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_43_small : |ieeeVal frozen_kernel_1_43| < 1 := by
  norm_num [frozen_kernel_1_43, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_44_finite : ieeeIsFinite frozen_kernel_1_44 := by
  simp [frozen_kernel_1_44, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_44_small : |ieeeVal frozen_kernel_1_44| < 1 := by
  norm_num [frozen_kernel_1_44, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_45_finite : ieeeIsFinite frozen_kernel_1_45 := by
  simp [frozen_kernel_1_45, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_45_small : |ieeeVal frozen_kernel_1_45| < 1 := by
  norm_num [frozen_kernel_1_45, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_46_finite : ieeeIsFinite frozen_kernel_1_46 := by
  simp [frozen_kernel_1_46, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_46_small : |ieeeVal frozen_kernel_1_46| < 1 := by
  norm_num [frozen_kernel_1_46, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_47_finite : ieeeIsFinite frozen_kernel_1_47 := by
  simp [frozen_kernel_1_47, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_47_small : |ieeeVal frozen_kernel_1_47| < 1 := by
  norm_num [frozen_kernel_1_47, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_48_finite : ieeeIsFinite frozen_kernel_1_48 := by
  simp [frozen_kernel_1_48, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_48_small : |ieeeVal frozen_kernel_1_48| < 1 := by
  norm_num [frozen_kernel_1_48, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_49_finite : ieeeIsFinite frozen_kernel_1_49 := by
  simp [frozen_kernel_1_49, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_49_small : |ieeeVal frozen_kernel_1_49| < 1 := by
  norm_num [frozen_kernel_1_49, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_50_finite : ieeeIsFinite frozen_kernel_1_50 := by
  simp [frozen_kernel_1_50, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_50_small : |ieeeVal frozen_kernel_1_50| < 1 := by
  norm_num [frozen_kernel_1_50, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_51_finite : ieeeIsFinite frozen_kernel_1_51 := by
  simp [frozen_kernel_1_51, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_51_small : |ieeeVal frozen_kernel_1_51| < 1 := by
  norm_num [frozen_kernel_1_51, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_52_finite : ieeeIsFinite frozen_kernel_1_52 := by
  simp [frozen_kernel_1_52, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_52_small : |ieeeVal frozen_kernel_1_52| < 1 := by
  norm_num [frozen_kernel_1_52, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_53_finite : ieeeIsFinite frozen_kernel_1_53 := by
  simp [frozen_kernel_1_53, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_53_small : |ieeeVal frozen_kernel_1_53| < 1 := by
  norm_num [frozen_kernel_1_53, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_54_finite : ieeeIsFinite frozen_kernel_1_54 := by
  simp [frozen_kernel_1_54, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_54_small : |ieeeVal frozen_kernel_1_54| < 1 := by
  norm_num [frozen_kernel_1_54, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_55_finite : ieeeIsFinite frozen_kernel_1_55 := by
  simp [frozen_kernel_1_55, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_55_small : |ieeeVal frozen_kernel_1_55| < 1 := by
  norm_num [frozen_kernel_1_55, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_56_finite : ieeeIsFinite frozen_kernel_1_56 := by
  simp [frozen_kernel_1_56, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_56_small : |ieeeVal frozen_kernel_1_56| < 1 := by
  norm_num [frozen_kernel_1_56, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_57_finite : ieeeIsFinite frozen_kernel_1_57 := by
  simp [frozen_kernel_1_57, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_57_small : |ieeeVal frozen_kernel_1_57| < 1 := by
  norm_num [frozen_kernel_1_57, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_58_finite : ieeeIsFinite frozen_kernel_1_58 := by
  simp [frozen_kernel_1_58, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_58_small : |ieeeVal frozen_kernel_1_58| < 1 := by
  norm_num [frozen_kernel_1_58, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_59_finite : ieeeIsFinite frozen_kernel_1_59 := by
  simp [frozen_kernel_1_59, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_59_small : |ieeeVal frozen_kernel_1_59| < 1 := by
  norm_num [frozen_kernel_1_59, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_60_finite : ieeeIsFinite frozen_kernel_1_60 := by
  simp [frozen_kernel_1_60, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_60_small : |ieeeVal frozen_kernel_1_60| < 1 := by
  norm_num [frozen_kernel_1_60, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_61_finite : ieeeIsFinite frozen_kernel_1_61 := by
  simp [frozen_kernel_1_61, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_61_small : |ieeeVal frozen_kernel_1_61| < 1 := by
  norm_num [frozen_kernel_1_61, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_62_finite : ieeeIsFinite frozen_kernel_1_62 := by
  simp [frozen_kernel_1_62, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_62_small : |ieeeVal frozen_kernel_1_62| < 1 := by
  norm_num [frozen_kernel_1_62, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_1_63_finite : ieeeIsFinite frozen_kernel_1_63 := by
  simp [frozen_kernel_1_63, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_1_63_small : |ieeeVal frozen_kernel_1_63| < 1 := by
  norm_num [frozen_kernel_1_63, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_0_finite : ieeeIsFinite frozen_kernel_2_0 := by
  simp [frozen_kernel_2_0, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_0_small : |ieeeVal frozen_kernel_2_0| < 1 := by
  norm_num [frozen_kernel_2_0, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_1_finite : ieeeIsFinite frozen_kernel_2_1 := by
  simp [frozen_kernel_2_1, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_1_small : |ieeeVal frozen_kernel_2_1| < 1 := by
  norm_num [frozen_kernel_2_1, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_2_finite : ieeeIsFinite frozen_kernel_2_2 := by
  simp [frozen_kernel_2_2, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_2_small : |ieeeVal frozen_kernel_2_2| < 1 := by
  norm_num [frozen_kernel_2_2, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_3_finite : ieeeIsFinite frozen_kernel_2_3 := by
  simp [frozen_kernel_2_3, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_3_small : |ieeeVal frozen_kernel_2_3| < 1 := by
  norm_num [frozen_kernel_2_3, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_4_finite : ieeeIsFinite frozen_kernel_2_4 := by
  simp [frozen_kernel_2_4, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_4_small : |ieeeVal frozen_kernel_2_4| < 1 := by
  norm_num [frozen_kernel_2_4, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_5_finite : ieeeIsFinite frozen_kernel_2_5 := by
  simp [frozen_kernel_2_5, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_5_small : |ieeeVal frozen_kernel_2_5| < 1 := by
  norm_num [frozen_kernel_2_5, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_6_finite : ieeeIsFinite frozen_kernel_2_6 := by
  simp [frozen_kernel_2_6, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_6_small : |ieeeVal frozen_kernel_2_6| < 1 := by
  norm_num [frozen_kernel_2_6, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_7_finite : ieeeIsFinite frozen_kernel_2_7 := by
  simp [frozen_kernel_2_7, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_7_small : |ieeeVal frozen_kernel_2_7| < 1 := by
  norm_num [frozen_kernel_2_7, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_8_finite : ieeeIsFinite frozen_kernel_2_8 := by
  simp [frozen_kernel_2_8, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_8_small : |ieeeVal frozen_kernel_2_8| < 1 := by
  norm_num [frozen_kernel_2_8, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_9_finite : ieeeIsFinite frozen_kernel_2_9 := by
  simp [frozen_kernel_2_9, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_9_small : |ieeeVal frozen_kernel_2_9| < 1 := by
  norm_num [frozen_kernel_2_9, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_10_finite : ieeeIsFinite frozen_kernel_2_10 := by
  simp [frozen_kernel_2_10, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_10_small : |ieeeVal frozen_kernel_2_10| < 1 := by
  norm_num [frozen_kernel_2_10, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_11_finite : ieeeIsFinite frozen_kernel_2_11 := by
  simp [frozen_kernel_2_11, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_11_small : |ieeeVal frozen_kernel_2_11| < 1 := by
  norm_num [frozen_kernel_2_11, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_12_finite : ieeeIsFinite frozen_kernel_2_12 := by
  simp [frozen_kernel_2_12, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_12_small : |ieeeVal frozen_kernel_2_12| < 1 := by
  norm_num [frozen_kernel_2_12, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_13_finite : ieeeIsFinite frozen_kernel_2_13 := by
  simp [frozen_kernel_2_13, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_13_small : |ieeeVal frozen_kernel_2_13| < 1 := by
  norm_num [frozen_kernel_2_13, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_14_finite : ieeeIsFinite frozen_kernel_2_14 := by
  simp [frozen_kernel_2_14, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_14_small : |ieeeVal frozen_kernel_2_14| < 1 := by
  norm_num [frozen_kernel_2_14, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_15_finite : ieeeIsFinite frozen_kernel_2_15 := by
  simp [frozen_kernel_2_15, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_15_small : |ieeeVal frozen_kernel_2_15| < 1 := by
  norm_num [frozen_kernel_2_15, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_16_finite : ieeeIsFinite frozen_kernel_2_16 := by
  simp [frozen_kernel_2_16, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_16_small : |ieeeVal frozen_kernel_2_16| < 1 := by
  norm_num [frozen_kernel_2_16, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_17_finite : ieeeIsFinite frozen_kernel_2_17 := by
  simp [frozen_kernel_2_17, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_17_small : |ieeeVal frozen_kernel_2_17| < 1 := by
  norm_num [frozen_kernel_2_17, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_18_finite : ieeeIsFinite frozen_kernel_2_18 := by
  simp [frozen_kernel_2_18, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_18_small : |ieeeVal frozen_kernel_2_18| < 1 := by
  norm_num [frozen_kernel_2_18, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_19_finite : ieeeIsFinite frozen_kernel_2_19 := by
  simp [frozen_kernel_2_19, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_19_small : |ieeeVal frozen_kernel_2_19| < 1 := by
  norm_num [frozen_kernel_2_19, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_20_finite : ieeeIsFinite frozen_kernel_2_20 := by
  simp [frozen_kernel_2_20, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_20_small : |ieeeVal frozen_kernel_2_20| < 1 := by
  norm_num [frozen_kernel_2_20, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_21_finite : ieeeIsFinite frozen_kernel_2_21 := by
  simp [frozen_kernel_2_21, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_21_small : |ieeeVal frozen_kernel_2_21| < 1 := by
  norm_num [frozen_kernel_2_21, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_22_finite : ieeeIsFinite frozen_kernel_2_22 := by
  simp [frozen_kernel_2_22, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_22_small : |ieeeVal frozen_kernel_2_22| < 1 := by
  norm_num [frozen_kernel_2_22, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_23_finite : ieeeIsFinite frozen_kernel_2_23 := by
  simp [frozen_kernel_2_23, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_23_small : |ieeeVal frozen_kernel_2_23| < 1 := by
  norm_num [frozen_kernel_2_23, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_24_finite : ieeeIsFinite frozen_kernel_2_24 := by
  simp [frozen_kernel_2_24, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_24_small : |ieeeVal frozen_kernel_2_24| < 1 := by
  norm_num [frozen_kernel_2_24, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_25_finite : ieeeIsFinite frozen_kernel_2_25 := by
  simp [frozen_kernel_2_25, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_25_small : |ieeeVal frozen_kernel_2_25| < 1 := by
  norm_num [frozen_kernel_2_25, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_26_finite : ieeeIsFinite frozen_kernel_2_26 := by
  simp [frozen_kernel_2_26, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_26_small : |ieeeVal frozen_kernel_2_26| < 1 := by
  norm_num [frozen_kernel_2_26, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_27_finite : ieeeIsFinite frozen_kernel_2_27 := by
  simp [frozen_kernel_2_27, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_27_small : |ieeeVal frozen_kernel_2_27| < 1 := by
  norm_num [frozen_kernel_2_27, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_28_finite : ieeeIsFinite frozen_kernel_2_28 := by
  simp [frozen_kernel_2_28, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_28_small : |ieeeVal frozen_kernel_2_28| < 1 := by
  norm_num [frozen_kernel_2_28, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_29_finite : ieeeIsFinite frozen_kernel_2_29 := by
  simp [frozen_kernel_2_29, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_29_small : |ieeeVal frozen_kernel_2_29| < 1 := by
  norm_num [frozen_kernel_2_29, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_30_finite : ieeeIsFinite frozen_kernel_2_30 := by
  simp [frozen_kernel_2_30, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_30_small : |ieeeVal frozen_kernel_2_30| < 1 := by
  norm_num [frozen_kernel_2_30, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_31_finite : ieeeIsFinite frozen_kernel_2_31 := by
  simp [frozen_kernel_2_31, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_31_small : |ieeeVal frozen_kernel_2_31| < 1 := by
  norm_num [frozen_kernel_2_31, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_32_finite : ieeeIsFinite frozen_kernel_2_32 := by
  simp [frozen_kernel_2_32, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_32_small : |ieeeVal frozen_kernel_2_32| < 1 := by
  norm_num [frozen_kernel_2_32, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_33_finite : ieeeIsFinite frozen_kernel_2_33 := by
  simp [frozen_kernel_2_33, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_33_small : |ieeeVal frozen_kernel_2_33| < 1 := by
  norm_num [frozen_kernel_2_33, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_34_finite : ieeeIsFinite frozen_kernel_2_34 := by
  simp [frozen_kernel_2_34, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_34_small : |ieeeVal frozen_kernel_2_34| < 1 := by
  norm_num [frozen_kernel_2_34, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_35_finite : ieeeIsFinite frozen_kernel_2_35 := by
  simp [frozen_kernel_2_35, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_35_small : |ieeeVal frozen_kernel_2_35| < 1 := by
  norm_num [frozen_kernel_2_35, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_36_finite : ieeeIsFinite frozen_kernel_2_36 := by
  simp [frozen_kernel_2_36, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_36_small : |ieeeVal frozen_kernel_2_36| < 1 := by
  norm_num [frozen_kernel_2_36, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_37_finite : ieeeIsFinite frozen_kernel_2_37 := by
  simp [frozen_kernel_2_37, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_37_small : |ieeeVal frozen_kernel_2_37| < 1 := by
  norm_num [frozen_kernel_2_37, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_38_finite : ieeeIsFinite frozen_kernel_2_38 := by
  simp [frozen_kernel_2_38, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_38_small : |ieeeVal frozen_kernel_2_38| < 1 := by
  norm_num [frozen_kernel_2_38, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_39_finite : ieeeIsFinite frozen_kernel_2_39 := by
  simp [frozen_kernel_2_39, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_39_small : |ieeeVal frozen_kernel_2_39| < 1 := by
  norm_num [frozen_kernel_2_39, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_40_finite : ieeeIsFinite frozen_kernel_2_40 := by
  simp [frozen_kernel_2_40, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_40_small : |ieeeVal frozen_kernel_2_40| < 1 := by
  norm_num [frozen_kernel_2_40, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_41_finite : ieeeIsFinite frozen_kernel_2_41 := by
  simp [frozen_kernel_2_41, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_41_small : |ieeeVal frozen_kernel_2_41| < 1 := by
  norm_num [frozen_kernel_2_41, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_42_finite : ieeeIsFinite frozen_kernel_2_42 := by
  simp [frozen_kernel_2_42, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_42_small : |ieeeVal frozen_kernel_2_42| < 1 := by
  norm_num [frozen_kernel_2_42, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_43_finite : ieeeIsFinite frozen_kernel_2_43 := by
  simp [frozen_kernel_2_43, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_43_small : |ieeeVal frozen_kernel_2_43| < 1 := by
  norm_num [frozen_kernel_2_43, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_44_finite : ieeeIsFinite frozen_kernel_2_44 := by
  simp [frozen_kernel_2_44, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_44_small : |ieeeVal frozen_kernel_2_44| < 1 := by
  norm_num [frozen_kernel_2_44, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_45_finite : ieeeIsFinite frozen_kernel_2_45 := by
  simp [frozen_kernel_2_45, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_45_small : |ieeeVal frozen_kernel_2_45| < 1 := by
  norm_num [frozen_kernel_2_45, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_46_finite : ieeeIsFinite frozen_kernel_2_46 := by
  simp [frozen_kernel_2_46, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_46_small : |ieeeVal frozen_kernel_2_46| < 1 := by
  norm_num [frozen_kernel_2_46, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_47_finite : ieeeIsFinite frozen_kernel_2_47 := by
  simp [frozen_kernel_2_47, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_47_small : |ieeeVal frozen_kernel_2_47| < 1 := by
  norm_num [frozen_kernel_2_47, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_48_finite : ieeeIsFinite frozen_kernel_2_48 := by
  simp [frozen_kernel_2_48, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_48_small : |ieeeVal frozen_kernel_2_48| < 1 := by
  norm_num [frozen_kernel_2_48, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_49_finite : ieeeIsFinite frozen_kernel_2_49 := by
  simp [frozen_kernel_2_49, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_49_small : |ieeeVal frozen_kernel_2_49| < 1 := by
  norm_num [frozen_kernel_2_49, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_50_finite : ieeeIsFinite frozen_kernel_2_50 := by
  simp [frozen_kernel_2_50, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_50_small : |ieeeVal frozen_kernel_2_50| < 1 := by
  norm_num [frozen_kernel_2_50, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_51_finite : ieeeIsFinite frozen_kernel_2_51 := by
  simp [frozen_kernel_2_51, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_51_small : |ieeeVal frozen_kernel_2_51| < 1 := by
  norm_num [frozen_kernel_2_51, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_52_finite : ieeeIsFinite frozen_kernel_2_52 := by
  simp [frozen_kernel_2_52, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_52_small : |ieeeVal frozen_kernel_2_52| < 1 := by
  norm_num [frozen_kernel_2_52, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_53_finite : ieeeIsFinite frozen_kernel_2_53 := by
  simp [frozen_kernel_2_53, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_53_small : |ieeeVal frozen_kernel_2_53| < 1 := by
  norm_num [frozen_kernel_2_53, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_54_finite : ieeeIsFinite frozen_kernel_2_54 := by
  simp [frozen_kernel_2_54, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_54_small : |ieeeVal frozen_kernel_2_54| < 1 := by
  norm_num [frozen_kernel_2_54, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_55_finite : ieeeIsFinite frozen_kernel_2_55 := by
  simp [frozen_kernel_2_55, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_55_small : |ieeeVal frozen_kernel_2_55| < 1 := by
  norm_num [frozen_kernel_2_55, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_56_finite : ieeeIsFinite frozen_kernel_2_56 := by
  simp [frozen_kernel_2_56, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_56_small : |ieeeVal frozen_kernel_2_56| < 1 := by
  norm_num [frozen_kernel_2_56, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_57_finite : ieeeIsFinite frozen_kernel_2_57 := by
  simp [frozen_kernel_2_57, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_57_small : |ieeeVal frozen_kernel_2_57| < 1 := by
  norm_num [frozen_kernel_2_57, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_58_finite : ieeeIsFinite frozen_kernel_2_58 := by
  simp [frozen_kernel_2_58, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_58_small : |ieeeVal frozen_kernel_2_58| < 1 := by
  norm_num [frozen_kernel_2_58, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_59_finite : ieeeIsFinite frozen_kernel_2_59 := by
  simp [frozen_kernel_2_59, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_59_small : |ieeeVal frozen_kernel_2_59| < 1 := by
  norm_num [frozen_kernel_2_59, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_60_finite : ieeeIsFinite frozen_kernel_2_60 := by
  simp [frozen_kernel_2_60, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_60_small : |ieeeVal frozen_kernel_2_60| < 1 := by
  norm_num [frozen_kernel_2_60, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_61_finite : ieeeIsFinite frozen_kernel_2_61 := by
  simp [frozen_kernel_2_61, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_61_small : |ieeeVal frozen_kernel_2_61| < 1 := by
  norm_num [frozen_kernel_2_61, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_62_finite : ieeeIsFinite frozen_kernel_2_62 := by
  simp [frozen_kernel_2_62, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_62_small : |ieeeVal frozen_kernel_2_62| < 1 := by
  norm_num [frozen_kernel_2_62, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_2_63_finite : ieeeIsFinite frozen_kernel_2_63 := by
  simp [frozen_kernel_2_63, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_2_63_small : |ieeeVal frozen_kernel_2_63| < 1 := by
  norm_num [frozen_kernel_2_63, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_0_finite : ieeeIsFinite frozen_kernel_3_0 := by
  simp [frozen_kernel_3_0, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_0_small : |ieeeVal frozen_kernel_3_0| < 1 := by
  norm_num [frozen_kernel_3_0, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_1_finite : ieeeIsFinite frozen_kernel_3_1 := by
  simp [frozen_kernel_3_1, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_1_small : |ieeeVal frozen_kernel_3_1| < 1 := by
  norm_num [frozen_kernel_3_1, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_2_finite : ieeeIsFinite frozen_kernel_3_2 := by
  simp [frozen_kernel_3_2, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_2_small : |ieeeVal frozen_kernel_3_2| < 1 := by
  norm_num [frozen_kernel_3_2, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_3_finite : ieeeIsFinite frozen_kernel_3_3 := by
  simp [frozen_kernel_3_3, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_3_small : |ieeeVal frozen_kernel_3_3| < 1 := by
  norm_num [frozen_kernel_3_3, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_4_finite : ieeeIsFinite frozen_kernel_3_4 := by
  simp [frozen_kernel_3_4, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_4_small : |ieeeVal frozen_kernel_3_4| < 1 := by
  norm_num [frozen_kernel_3_4, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_5_finite : ieeeIsFinite frozen_kernel_3_5 := by
  simp [frozen_kernel_3_5, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_5_small : |ieeeVal frozen_kernel_3_5| < 1 := by
  norm_num [frozen_kernel_3_5, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_6_finite : ieeeIsFinite frozen_kernel_3_6 := by
  simp [frozen_kernel_3_6, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_6_small : |ieeeVal frozen_kernel_3_6| < 1 := by
  norm_num [frozen_kernel_3_6, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_7_finite : ieeeIsFinite frozen_kernel_3_7 := by
  simp [frozen_kernel_3_7, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_7_small : |ieeeVal frozen_kernel_3_7| < 1 := by
  norm_num [frozen_kernel_3_7, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_8_finite : ieeeIsFinite frozen_kernel_3_8 := by
  simp [frozen_kernel_3_8, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_8_small : |ieeeVal frozen_kernel_3_8| < 1 := by
  norm_num [frozen_kernel_3_8, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_9_finite : ieeeIsFinite frozen_kernel_3_9 := by
  simp [frozen_kernel_3_9, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_9_small : |ieeeVal frozen_kernel_3_9| < 1 := by
  norm_num [frozen_kernel_3_9, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_10_finite : ieeeIsFinite frozen_kernel_3_10 := by
  simp [frozen_kernel_3_10, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_10_small : |ieeeVal frozen_kernel_3_10| < 1 := by
  norm_num [frozen_kernel_3_10, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_11_finite : ieeeIsFinite frozen_kernel_3_11 := by
  simp [frozen_kernel_3_11, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_11_small : |ieeeVal frozen_kernel_3_11| < 1 := by
  norm_num [frozen_kernel_3_11, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_12_finite : ieeeIsFinite frozen_kernel_3_12 := by
  simp [frozen_kernel_3_12, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_12_small : |ieeeVal frozen_kernel_3_12| < 1 := by
  norm_num [frozen_kernel_3_12, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_13_finite : ieeeIsFinite frozen_kernel_3_13 := by
  simp [frozen_kernel_3_13, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_13_small : |ieeeVal frozen_kernel_3_13| < 1 := by
  norm_num [frozen_kernel_3_13, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_14_finite : ieeeIsFinite frozen_kernel_3_14 := by
  simp [frozen_kernel_3_14, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_14_small : |ieeeVal frozen_kernel_3_14| < 1 := by
  norm_num [frozen_kernel_3_14, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_15_finite : ieeeIsFinite frozen_kernel_3_15 := by
  simp [frozen_kernel_3_15, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_15_small : |ieeeVal frozen_kernel_3_15| < 1 := by
  norm_num [frozen_kernel_3_15, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_16_finite : ieeeIsFinite frozen_kernel_3_16 := by
  simp [frozen_kernel_3_16, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_16_small : |ieeeVal frozen_kernel_3_16| < 1 := by
  norm_num [frozen_kernel_3_16, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_17_finite : ieeeIsFinite frozen_kernel_3_17 := by
  simp [frozen_kernel_3_17, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_17_small : |ieeeVal frozen_kernel_3_17| < 1 := by
  norm_num [frozen_kernel_3_17, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_18_finite : ieeeIsFinite frozen_kernel_3_18 := by
  simp [frozen_kernel_3_18, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_18_small : |ieeeVal frozen_kernel_3_18| < 1 := by
  norm_num [frozen_kernel_3_18, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_19_finite : ieeeIsFinite frozen_kernel_3_19 := by
  simp [frozen_kernel_3_19, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_19_small : |ieeeVal frozen_kernel_3_19| < 1 := by
  norm_num [frozen_kernel_3_19, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_20_finite : ieeeIsFinite frozen_kernel_3_20 := by
  simp [frozen_kernel_3_20, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_20_small : |ieeeVal frozen_kernel_3_20| < 1 := by
  norm_num [frozen_kernel_3_20, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_21_finite : ieeeIsFinite frozen_kernel_3_21 := by
  simp [frozen_kernel_3_21, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_21_small : |ieeeVal frozen_kernel_3_21| < 1 := by
  norm_num [frozen_kernel_3_21, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_22_finite : ieeeIsFinite frozen_kernel_3_22 := by
  simp [frozen_kernel_3_22, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_22_small : |ieeeVal frozen_kernel_3_22| < 1 := by
  norm_num [frozen_kernel_3_22, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_23_finite : ieeeIsFinite frozen_kernel_3_23 := by
  simp [frozen_kernel_3_23, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_23_small : |ieeeVal frozen_kernel_3_23| < 1 := by
  norm_num [frozen_kernel_3_23, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_24_finite : ieeeIsFinite frozen_kernel_3_24 := by
  simp [frozen_kernel_3_24, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_24_small : |ieeeVal frozen_kernel_3_24| < 1 := by
  norm_num [frozen_kernel_3_24, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_25_finite : ieeeIsFinite frozen_kernel_3_25 := by
  simp [frozen_kernel_3_25, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_25_small : |ieeeVal frozen_kernel_3_25| < 1 := by
  norm_num [frozen_kernel_3_25, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_26_finite : ieeeIsFinite frozen_kernel_3_26 := by
  simp [frozen_kernel_3_26, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_26_small : |ieeeVal frozen_kernel_3_26| < 1 := by
  norm_num [frozen_kernel_3_26, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_27_finite : ieeeIsFinite frozen_kernel_3_27 := by
  simp [frozen_kernel_3_27, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_27_small : |ieeeVal frozen_kernel_3_27| < 1 := by
  norm_num [frozen_kernel_3_27, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_28_finite : ieeeIsFinite frozen_kernel_3_28 := by
  simp [frozen_kernel_3_28, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_28_small : |ieeeVal frozen_kernel_3_28| < 1 := by
  norm_num [frozen_kernel_3_28, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_29_finite : ieeeIsFinite frozen_kernel_3_29 := by
  simp [frozen_kernel_3_29, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_29_small : |ieeeVal frozen_kernel_3_29| < 1 := by
  norm_num [frozen_kernel_3_29, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_30_finite : ieeeIsFinite frozen_kernel_3_30 := by
  simp [frozen_kernel_3_30, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_30_small : |ieeeVal frozen_kernel_3_30| < 1 := by
  norm_num [frozen_kernel_3_30, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_31_finite : ieeeIsFinite frozen_kernel_3_31 := by
  simp [frozen_kernel_3_31, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_31_small : |ieeeVal frozen_kernel_3_31| < 1 := by
  norm_num [frozen_kernel_3_31, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_32_finite : ieeeIsFinite frozen_kernel_3_32 := by
  simp [frozen_kernel_3_32, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_32_small : |ieeeVal frozen_kernel_3_32| < 1 := by
  norm_num [frozen_kernel_3_32, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_33_finite : ieeeIsFinite frozen_kernel_3_33 := by
  simp [frozen_kernel_3_33, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_33_small : |ieeeVal frozen_kernel_3_33| < 1 := by
  norm_num [frozen_kernel_3_33, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_34_finite : ieeeIsFinite frozen_kernel_3_34 := by
  simp [frozen_kernel_3_34, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_34_small : |ieeeVal frozen_kernel_3_34| < 1 := by
  norm_num [frozen_kernel_3_34, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_35_finite : ieeeIsFinite frozen_kernel_3_35 := by
  simp [frozen_kernel_3_35, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_35_small : |ieeeVal frozen_kernel_3_35| < 1 := by
  norm_num [frozen_kernel_3_35, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_36_finite : ieeeIsFinite frozen_kernel_3_36 := by
  simp [frozen_kernel_3_36, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_36_small : |ieeeVal frozen_kernel_3_36| < 1 := by
  norm_num [frozen_kernel_3_36, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_37_finite : ieeeIsFinite frozen_kernel_3_37 := by
  simp [frozen_kernel_3_37, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_37_small : |ieeeVal frozen_kernel_3_37| < 1 := by
  norm_num [frozen_kernel_3_37, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_38_finite : ieeeIsFinite frozen_kernel_3_38 := by
  simp [frozen_kernel_3_38, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_38_small : |ieeeVal frozen_kernel_3_38| < 1 := by
  norm_num [frozen_kernel_3_38, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_39_finite : ieeeIsFinite frozen_kernel_3_39 := by
  simp [frozen_kernel_3_39, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_39_small : |ieeeVal frozen_kernel_3_39| < 1 := by
  norm_num [frozen_kernel_3_39, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_40_finite : ieeeIsFinite frozen_kernel_3_40 := by
  simp [frozen_kernel_3_40, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_40_small : |ieeeVal frozen_kernel_3_40| < 1 := by
  norm_num [frozen_kernel_3_40, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_41_finite : ieeeIsFinite frozen_kernel_3_41 := by
  simp [frozen_kernel_3_41, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_41_small : |ieeeVal frozen_kernel_3_41| < 1 := by
  norm_num [frozen_kernel_3_41, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_42_finite : ieeeIsFinite frozen_kernel_3_42 := by
  simp [frozen_kernel_3_42, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_42_small : |ieeeVal frozen_kernel_3_42| < 1 := by
  norm_num [frozen_kernel_3_42, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_43_finite : ieeeIsFinite frozen_kernel_3_43 := by
  simp [frozen_kernel_3_43, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_43_small : |ieeeVal frozen_kernel_3_43| < 1 := by
  norm_num [frozen_kernel_3_43, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_44_finite : ieeeIsFinite frozen_kernel_3_44 := by
  simp [frozen_kernel_3_44, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_44_small : |ieeeVal frozen_kernel_3_44| < 1 := by
  norm_num [frozen_kernel_3_44, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_45_finite : ieeeIsFinite frozen_kernel_3_45 := by
  simp [frozen_kernel_3_45, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_45_small : |ieeeVal frozen_kernel_3_45| < 1 := by
  norm_num [frozen_kernel_3_45, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_46_finite : ieeeIsFinite frozen_kernel_3_46 := by
  simp [frozen_kernel_3_46, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_46_small : |ieeeVal frozen_kernel_3_46| < 1 := by
  norm_num [frozen_kernel_3_46, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_47_finite : ieeeIsFinite frozen_kernel_3_47 := by
  simp [frozen_kernel_3_47, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_47_small : |ieeeVal frozen_kernel_3_47| < 1 := by
  norm_num [frozen_kernel_3_47, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_48_finite : ieeeIsFinite frozen_kernel_3_48 := by
  simp [frozen_kernel_3_48, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_48_small : |ieeeVal frozen_kernel_3_48| < 1 := by
  norm_num [frozen_kernel_3_48, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_49_finite : ieeeIsFinite frozen_kernel_3_49 := by
  simp [frozen_kernel_3_49, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_49_small : |ieeeVal frozen_kernel_3_49| < 1 := by
  norm_num [frozen_kernel_3_49, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_50_finite : ieeeIsFinite frozen_kernel_3_50 := by
  simp [frozen_kernel_3_50, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_50_small : |ieeeVal frozen_kernel_3_50| < 1 := by
  norm_num [frozen_kernel_3_50, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_51_finite : ieeeIsFinite frozen_kernel_3_51 := by
  simp [frozen_kernel_3_51, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_51_small : |ieeeVal frozen_kernel_3_51| < 1 := by
  norm_num [frozen_kernel_3_51, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_52_finite : ieeeIsFinite frozen_kernel_3_52 := by
  simp [frozen_kernel_3_52, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_52_small : |ieeeVal frozen_kernel_3_52| < 1 := by
  norm_num [frozen_kernel_3_52, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_53_finite : ieeeIsFinite frozen_kernel_3_53 := by
  simp [frozen_kernel_3_53, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_53_small : |ieeeVal frozen_kernel_3_53| < 1 := by
  norm_num [frozen_kernel_3_53, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_54_finite : ieeeIsFinite frozen_kernel_3_54 := by
  simp [frozen_kernel_3_54, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_54_small : |ieeeVal frozen_kernel_3_54| < 1 := by
  norm_num [frozen_kernel_3_54, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_55_finite : ieeeIsFinite frozen_kernel_3_55 := by
  simp [frozen_kernel_3_55, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_55_small : |ieeeVal frozen_kernel_3_55| < 1 := by
  norm_num [frozen_kernel_3_55, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_56_finite : ieeeIsFinite frozen_kernel_3_56 := by
  simp [frozen_kernel_3_56, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_56_small : |ieeeVal frozen_kernel_3_56| < 1 := by
  norm_num [frozen_kernel_3_56, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_57_finite : ieeeIsFinite frozen_kernel_3_57 := by
  simp [frozen_kernel_3_57, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_57_small : |ieeeVal frozen_kernel_3_57| < 1 := by
  norm_num [frozen_kernel_3_57, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_58_finite : ieeeIsFinite frozen_kernel_3_58 := by
  simp [frozen_kernel_3_58, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_58_small : |ieeeVal frozen_kernel_3_58| < 1 := by
  norm_num [frozen_kernel_3_58, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_59_finite : ieeeIsFinite frozen_kernel_3_59 := by
  simp [frozen_kernel_3_59, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_59_small : |ieeeVal frozen_kernel_3_59| < 1 := by
  norm_num [frozen_kernel_3_59, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_60_finite : ieeeIsFinite frozen_kernel_3_60 := by
  simp [frozen_kernel_3_60, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_60_small : |ieeeVal frozen_kernel_3_60| < 1 := by
  norm_num [frozen_kernel_3_60, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_61_finite : ieeeIsFinite frozen_kernel_3_61 := by
  simp [frozen_kernel_3_61, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_61_small : |ieeeVal frozen_kernel_3_61| < 1 := by
  norm_num [frozen_kernel_3_61, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_62_finite : ieeeIsFinite frozen_kernel_3_62 := by
  simp [frozen_kernel_3_62, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_62_small : |ieeeVal frozen_kernel_3_62| < 1 := by
  norm_num [frozen_kernel_3_62, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

@[simp] lemma frozen_kernel_3_63_finite : ieeeIsFinite frozen_kernel_3_63 := by
  simp [frozen_kernel_3_63, frozenMake, ieeeIsFinite, binary32Format, ieeeExponentMax]

lemma frozen_kernel_3_63_small : |ieeeVal frozen_kernel_3_63| < 1 := by
  norm_num [frozen_kernel_3_63, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

lemma frozen_input_shape : frozen_input_activation.length = 64 := by
  simp [frozen_input_activation]

lemma frozen_kernel_shapes :
    frozen_trace_kernels.length = 4 ∧
      ∀ k ∈ frozen_trace_kernels, k.length = 64 := by
  simp [frozen_trace_kernels, frozen_kernel_0, frozen_kernel_1, frozen_kernel_2, frozen_kernel_3]

lemma frozen_input_finite : ∀ x ∈ frozen_input_activation, ieeeIsFinite x := by
  simp [frozen_input_activation]

lemma frozen_input_small : ∀ x ∈ frozen_input_activation, |ieeeVal x| < 1 := by
  simp [frozen_input_activation, frozen_input_activation_0_small, frozen_input_activation_1_small, frozen_input_activation_2_small, frozen_input_activation_3_small, frozen_input_activation_4_small, frozen_input_activation_5_small, frozen_input_activation_6_small, frozen_input_activation_7_small, frozen_input_activation_8_small, frozen_input_activation_9_small, frozen_input_activation_10_small, frozen_input_activation_11_small, frozen_input_activation_12_small, frozen_input_activation_13_small, frozen_input_activation_14_small, frozen_input_activation_15_small, frozen_input_activation_16_small, frozen_input_activation_17_small, frozen_input_activation_18_small, frozen_input_activation_19_small, frozen_input_activation_20_small, frozen_input_activation_21_small, frozen_input_activation_22_small, frozen_input_activation_23_small, frozen_input_activation_24_small, frozen_input_activation_25_small, frozen_input_activation_26_small, frozen_input_activation_27_small, frozen_input_activation_28_small, frozen_input_activation_29_small, frozen_input_activation_30_small, frozen_input_activation_31_small, frozen_input_activation_32_small, frozen_input_activation_33_small, frozen_input_activation_34_small, frozen_input_activation_35_small, frozen_input_activation_36_small, frozen_input_activation_37_small, frozen_input_activation_38_small, frozen_input_activation_39_small, frozen_input_activation_40_small, frozen_input_activation_41_small, frozen_input_activation_42_small, frozen_input_activation_43_small, frozen_input_activation_44_small, frozen_input_activation_45_small, frozen_input_activation_46_small, frozen_input_activation_47_small, frozen_input_activation_48_small, frozen_input_activation_49_small, frozen_input_activation_50_small, frozen_input_activation_51_small, frozen_input_activation_52_small, frozen_input_activation_53_small, frozen_input_activation_54_small, frozen_input_activation_55_small, frozen_input_activation_56_small, frozen_input_activation_57_small, frozen_input_activation_58_small, frozen_input_activation_59_small, frozen_input_activation_60_small, frozen_input_activation_61_small, frozen_input_activation_62_small, frozen_input_activation_63_small]

lemma frozen_threshold_128_value : ieeeVal frozen_threshold_128 = 128 := by
  norm_num [frozen_threshold_128, frozenMake, frozenDecode, ieeeVal, ieeeSignValue, ieeeBias, binary32Format]

lemma frozen_threshold_128_bound : 128 < ieeeThreshold binary32Format := by
  norm_num [ieeeThreshold, ieeeExponentMax, ieeeBias, binary32Format]

lemma frozen_threshold_129_bound : 129 < ieeeThreshold binary32Format := by
  norm_num [ieeeThreshold, ieeeExponentMax, ieeeBias, binary32Format]

lemma frozen_kernel_0_finite : ∀ x ∈ frozen_kernel_0, ieeeIsFinite x := by
  simp [frozen_kernel_0]

lemma frozen_kernel_0_small : ∀ x ∈ frozen_kernel_0, |ieeeVal x| < 1 := by
  simp [frozen_kernel_0, frozen_kernel_0_0_small, frozen_kernel_0_1_small, frozen_kernel_0_2_small, frozen_kernel_0_3_small, frozen_kernel_0_4_small, frozen_kernel_0_5_small, frozen_kernel_0_6_small, frozen_kernel_0_7_small, frozen_kernel_0_8_small, frozen_kernel_0_9_small, frozen_kernel_0_10_small, frozen_kernel_0_11_small, frozen_kernel_0_12_small, frozen_kernel_0_13_small, frozen_kernel_0_14_small, frozen_kernel_0_15_small, frozen_kernel_0_16_small, frozen_kernel_0_17_small, frozen_kernel_0_18_small, frozen_kernel_0_19_small, frozen_kernel_0_20_small, frozen_kernel_0_21_small, frozen_kernel_0_22_small, frozen_kernel_0_23_small, frozen_kernel_0_24_small, frozen_kernel_0_25_small, frozen_kernel_0_26_small, frozen_kernel_0_27_small, frozen_kernel_0_28_small, frozen_kernel_0_29_small, frozen_kernel_0_30_small, frozen_kernel_0_31_small, frozen_kernel_0_32_small, frozen_kernel_0_33_small, frozen_kernel_0_34_small, frozen_kernel_0_35_small, frozen_kernel_0_36_small, frozen_kernel_0_37_small, frozen_kernel_0_38_small, frozen_kernel_0_39_small, frozen_kernel_0_40_small, frozen_kernel_0_41_small, frozen_kernel_0_42_small, frozen_kernel_0_43_small, frozen_kernel_0_44_small, frozen_kernel_0_45_small, frozen_kernel_0_46_small, frozen_kernel_0_47_small, frozen_kernel_0_48_small, frozen_kernel_0_49_small, frozen_kernel_0_50_small, frozen_kernel_0_51_small, frozen_kernel_0_52_small, frozen_kernel_0_53_small, frozen_kernel_0_54_small, frozen_kernel_0_55_small, frozen_kernel_0_56_small, frozen_kernel_0_57_small, frozen_kernel_0_58_small, frozen_kernel_0_59_small, frozen_kernel_0_60_small, frozen_kernel_0_61_small, frozen_kernel_0_62_small, frozen_kernel_0_63_small]

lemma frozen_kernel_0_certificate :
    ieeeFmaDotCertificate
        (ieeeThreshold binary32Format) 1
        frozen_input_activation frozen_kernel_0
        (ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_0) := by
  apply ieeeFmaDotTailCertificate
  · simp [frozen_input_activation, frozen_kernel_0]
  · norm_num [frozen_input_activation, frozen_kernel_0]
  · exact frozen_input_finite
  · exact frozen_kernel_0_finite
  · exact frozen_input_small
  · exact frozen_kernel_0_small
  · norm_num [frozen_input_activation, ieeeThreshold, ieeeExponentMax, ieeeBias, binary32Format]

lemma frozen_kernel_1_finite : ∀ x ∈ frozen_kernel_1, ieeeIsFinite x := by
  simp [frozen_kernel_1]

lemma frozen_kernel_1_small : ∀ x ∈ frozen_kernel_1, |ieeeVal x| < 1 := by
  simp [frozen_kernel_1, frozen_kernel_1_0_small, frozen_kernel_1_1_small, frozen_kernel_1_2_small, frozen_kernel_1_3_small, frozen_kernel_1_4_small, frozen_kernel_1_5_small, frozen_kernel_1_6_small, frozen_kernel_1_7_small, frozen_kernel_1_8_small, frozen_kernel_1_9_small, frozen_kernel_1_10_small, frozen_kernel_1_11_small, frozen_kernel_1_12_small, frozen_kernel_1_13_small, frozen_kernel_1_14_small, frozen_kernel_1_15_small, frozen_kernel_1_16_small, frozen_kernel_1_17_small, frozen_kernel_1_18_small, frozen_kernel_1_19_small, frozen_kernel_1_20_small, frozen_kernel_1_21_small, frozen_kernel_1_22_small, frozen_kernel_1_23_small, frozen_kernel_1_24_small, frozen_kernel_1_25_small, frozen_kernel_1_26_small, frozen_kernel_1_27_small, frozen_kernel_1_28_small, frozen_kernel_1_29_small, frozen_kernel_1_30_small, frozen_kernel_1_31_small, frozen_kernel_1_32_small, frozen_kernel_1_33_small, frozen_kernel_1_34_small, frozen_kernel_1_35_small, frozen_kernel_1_36_small, frozen_kernel_1_37_small, frozen_kernel_1_38_small, frozen_kernel_1_39_small, frozen_kernel_1_40_small, frozen_kernel_1_41_small, frozen_kernel_1_42_small, frozen_kernel_1_43_small, frozen_kernel_1_44_small, frozen_kernel_1_45_small, frozen_kernel_1_46_small, frozen_kernel_1_47_small, frozen_kernel_1_48_small, frozen_kernel_1_49_small, frozen_kernel_1_50_small, frozen_kernel_1_51_small, frozen_kernel_1_52_small, frozen_kernel_1_53_small, frozen_kernel_1_54_small, frozen_kernel_1_55_small, frozen_kernel_1_56_small, frozen_kernel_1_57_small, frozen_kernel_1_58_small, frozen_kernel_1_59_small, frozen_kernel_1_60_small, frozen_kernel_1_61_small, frozen_kernel_1_62_small, frozen_kernel_1_63_small]

lemma frozen_kernel_1_certificate :
    ieeeFmaDotCertificate
        (ieeeThreshold binary32Format) 1
        frozen_input_activation frozen_kernel_1
        (ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_1) := by
  apply ieeeFmaDotTailCertificate
  · simp [frozen_input_activation, frozen_kernel_1]
  · norm_num [frozen_input_activation, frozen_kernel_1]
  · exact frozen_input_finite
  · exact frozen_kernel_1_finite
  · exact frozen_input_small
  · exact frozen_kernel_1_small
  · norm_num [frozen_input_activation, ieeeThreshold, ieeeExponentMax, ieeeBias, binary32Format]

lemma frozen_kernel_2_finite : ∀ x ∈ frozen_kernel_2, ieeeIsFinite x := by
  simp [frozen_kernel_2]

lemma frozen_kernel_2_small : ∀ x ∈ frozen_kernel_2, |ieeeVal x| < 1 := by
  simp [frozen_kernel_2, frozen_kernel_2_0_small, frozen_kernel_2_1_small, frozen_kernel_2_2_small, frozen_kernel_2_3_small, frozen_kernel_2_4_small, frozen_kernel_2_5_small, frozen_kernel_2_6_small, frozen_kernel_2_7_small, frozen_kernel_2_8_small, frozen_kernel_2_9_small, frozen_kernel_2_10_small, frozen_kernel_2_11_small, frozen_kernel_2_12_small, frozen_kernel_2_13_small, frozen_kernel_2_14_small, frozen_kernel_2_15_small, frozen_kernel_2_16_small, frozen_kernel_2_17_small, frozen_kernel_2_18_small, frozen_kernel_2_19_small, frozen_kernel_2_20_small, frozen_kernel_2_21_small, frozen_kernel_2_22_small, frozen_kernel_2_23_small, frozen_kernel_2_24_small, frozen_kernel_2_25_small, frozen_kernel_2_26_small, frozen_kernel_2_27_small, frozen_kernel_2_28_small, frozen_kernel_2_29_small, frozen_kernel_2_30_small, frozen_kernel_2_31_small, frozen_kernel_2_32_small, frozen_kernel_2_33_small, frozen_kernel_2_34_small, frozen_kernel_2_35_small, frozen_kernel_2_36_small, frozen_kernel_2_37_small, frozen_kernel_2_38_small, frozen_kernel_2_39_small, frozen_kernel_2_40_small, frozen_kernel_2_41_small, frozen_kernel_2_42_small, frozen_kernel_2_43_small, frozen_kernel_2_44_small, frozen_kernel_2_45_small, frozen_kernel_2_46_small, frozen_kernel_2_47_small, frozen_kernel_2_48_small, frozen_kernel_2_49_small, frozen_kernel_2_50_small, frozen_kernel_2_51_small, frozen_kernel_2_52_small, frozen_kernel_2_53_small, frozen_kernel_2_54_small, frozen_kernel_2_55_small, frozen_kernel_2_56_small, frozen_kernel_2_57_small, frozen_kernel_2_58_small, frozen_kernel_2_59_small, frozen_kernel_2_60_small, frozen_kernel_2_61_small, frozen_kernel_2_62_small, frozen_kernel_2_63_small]

lemma frozen_kernel_2_certificate :
    ieeeFmaDotCertificate
        (ieeeThreshold binary32Format) 1
        frozen_input_activation frozen_kernel_2
        (ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_2) := by
  apply ieeeFmaDotTailCertificate
  · simp [frozen_input_activation, frozen_kernel_2]
  · norm_num [frozen_input_activation, frozen_kernel_2]
  · exact frozen_input_finite
  · exact frozen_kernel_2_finite
  · exact frozen_input_small
  · exact frozen_kernel_2_small
  · norm_num [frozen_input_activation, ieeeThreshold, ieeeExponentMax, ieeeBias, binary32Format]

lemma frozen_kernel_3_finite : ∀ x ∈ frozen_kernel_3, ieeeIsFinite x := by
  simp [frozen_kernel_3]

lemma frozen_kernel_3_small : ∀ x ∈ frozen_kernel_3, |ieeeVal x| < 1 := by
  simp [frozen_kernel_3, frozen_kernel_3_0_small, frozen_kernel_3_1_small, frozen_kernel_3_2_small, frozen_kernel_3_3_small, frozen_kernel_3_4_small, frozen_kernel_3_5_small, frozen_kernel_3_6_small, frozen_kernel_3_7_small, frozen_kernel_3_8_small, frozen_kernel_3_9_small, frozen_kernel_3_10_small, frozen_kernel_3_11_small, frozen_kernel_3_12_small, frozen_kernel_3_13_small, frozen_kernel_3_14_small, frozen_kernel_3_15_small, frozen_kernel_3_16_small, frozen_kernel_3_17_small, frozen_kernel_3_18_small, frozen_kernel_3_19_small, frozen_kernel_3_20_small, frozen_kernel_3_21_small, frozen_kernel_3_22_small, frozen_kernel_3_23_small, frozen_kernel_3_24_small, frozen_kernel_3_25_small, frozen_kernel_3_26_small, frozen_kernel_3_27_small, frozen_kernel_3_28_small, frozen_kernel_3_29_small, frozen_kernel_3_30_small, frozen_kernel_3_31_small, frozen_kernel_3_32_small, frozen_kernel_3_33_small, frozen_kernel_3_34_small, frozen_kernel_3_35_small, frozen_kernel_3_36_small, frozen_kernel_3_37_small, frozen_kernel_3_38_small, frozen_kernel_3_39_small, frozen_kernel_3_40_small, frozen_kernel_3_41_small, frozen_kernel_3_42_small, frozen_kernel_3_43_small, frozen_kernel_3_44_small, frozen_kernel_3_45_small, frozen_kernel_3_46_small, frozen_kernel_3_47_small, frozen_kernel_3_48_small, frozen_kernel_3_49_small, frozen_kernel_3_50_small, frozen_kernel_3_51_small, frozen_kernel_3_52_small, frozen_kernel_3_53_small, frozen_kernel_3_54_small, frozen_kernel_3_55_small, frozen_kernel_3_56_small, frozen_kernel_3_57_small, frozen_kernel_3_58_small, frozen_kernel_3_59_small, frozen_kernel_3_60_small, frozen_kernel_3_61_small, frozen_kernel_3_62_small, frozen_kernel_3_63_small]

lemma frozen_kernel_3_certificate :
    ieeeFmaDotCertificate
        (ieeeThreshold binary32Format) 1
        frozen_input_activation frozen_kernel_3
        (ieeeFmaDotTailWitnesses frozen_input_activation frozen_kernel_3) := by
  apply ieeeFmaDotTailCertificate
  · simp [frozen_input_activation, frozen_kernel_3]
  · norm_num [frozen_input_activation, frozen_kernel_3]
  · exact frozen_input_finite
  · exact frozen_kernel_3_finite
  · exact frozen_input_small
  · exact frozen_kernel_3_small
  · norm_num [frozen_input_activation, ieeeThreshold, ieeeExponentMax, ieeeBias, binary32Format]

theorem frozen_trace_certificate :
    frozen_trace_witnesses.length = 4 ∧
      ∀ i, i < 4 →
        ieeeFmaDotCertificate
          (ieeeThreshold binary32Format) 1
          frozen_input_activation (frozen_trace_kernels.getD i [])
          (frozen_trace_witnesses.getD i []) := by
  constructor
  · simp [frozen_trace_witnesses, frozen_trace_kernels]
  · intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · simpa [frozen_trace_witnesses, frozen_trace_kernels] using frozen_kernel_0_certificate
    · simpa [frozen_trace_witnesses, frozen_trace_kernels] using frozen_kernel_1_certificate
    · simpa [frozen_trace_witnesses, frozen_trace_kernels] using frozen_kernel_2_certificate
    · simpa [frozen_trace_witnesses, frozen_trace_kernels] using frozen_kernel_3_certificate

theorem frozen_trace_safe :
    ∀ i, i < 4 →
      ieeeFmaDotSafe
        (ieeeThreshold binary32Format) 1 frozen_input_activation
        (frozen_trace_kernels.getD i []) := by
  intro i hi
  exact ieeeFmaDotCertificate_imp_safe ((frozen_trace_certificate).2 i hi)

theorem frozen_trace_error :
    ∀ i, i < 4 →
      |dotProduct (frozen_input_activation.map ieeeVal)
          ((frozen_trace_kernels.getD i []).map ieeeVal) -
        ieeeVal (ieeeFmaDot frozen_input_activation
          (frozen_trace_kernels.getD i []))| ≤ 64 := by
  intro i hi
  have htraceLength : frozen_trace_kernels.length = 4 :=
    frozen_kernel_shapes.1
  have hi' : i < frozen_trace_kernels.length := by
    simpa [htraceLength] using hi
  have hkernelLength : (frozen_trace_kernels.getD i []).length = 64 := by
    rw [List.getD_eq_getElem _ _ hi']
    exact frozen_kernel_shapes.2 _ (List.getElem_mem hi')
  have herr := ieeeFmaDot_error (epsilon := (1 : ℝ)) (by norm_num)
    (frozen_trace_safe i hi)
  have hbound := herr
  rw [frozen_input_shape, hkernelLength] at hbound
  norm_num at hbound ⊢
  exact hbound

end
end FrozenTinyStoriesTrace
end DecoderTransformer
