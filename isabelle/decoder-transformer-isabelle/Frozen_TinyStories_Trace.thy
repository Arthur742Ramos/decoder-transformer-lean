(* Generated deterministically by tools/import_frozen_checkpoint.py. *)
(* Model: roneneldan/TinyStories-1M; revision: 77f1b168e219585646439073245fe87e56b3023e *)
(* Checkpoint URL: https://huggingface.co/roneneldan/TinyStories-1M/resolve/77f1b168e219585646439073245fe87e56b3023e/pytorch_model.bin *)
(* Config SHA256: ff74c30d5ebb5ab1da0f2ea479adf7197c504b42b5522a858c334ab91ed4958c *)
(* Checkpoint SHA256: 07f9609ea882b8163ff3b23d40e2b82cb715d409631beb15c84b164f3877dae7 *)

theory Frozen_TinyStories_Trace
  imports IEEE_Trace_Certificate
begin

section \<open>Frozen TinyStories-1M binary32 activation trace\<close>

text \<open>
  This theory is generated from a public frozen TinyStories-1M
  GPT-Neo checkpoint.  It preserves exact binary32 bit fields for
  token The, position zero, and four layer-zero projection rows.
  The certificate covers every FMA step in this selected linear
  activation slice; it does not silently claim a full GPT-Neo
  attention/GELU/softmax proof.
  The error theorem below is intentionally a replayable local FMA
  certificate demonstration, not a numerical accuracy estimate: its
  bound 64 is the worst-case sum of one unit budget for each of the
  64 certified steps in a selected row.
\<close>

type_synonym frozen_binary32 = "(8, 23) IEEE.float"

lift_definition frozen_embedding_0 :: frozen_binary32
  is "(0, 123, 5074352)" .

lift_definition frozen_embedding_1 :: frozen_binary32
  is "(1, 123, 3382044)" .

lift_definition frozen_embedding_2 :: frozen_binary32
  is "(1, 123, 7491020)" .

lift_definition frozen_embedding_3 :: frozen_binary32
  is "(1, 117, 1123531)" .

lift_definition frozen_embedding_4 :: frozen_binary32
  is "(0, 122, 4708213)" .

lift_definition frozen_embedding_5 :: frozen_binary32
  is "(1, 122, 5862559)" .

lift_definition frozen_embedding_6 :: frozen_binary32
  is "(1, 120, 8243867)" .

lift_definition frozen_embedding_7 :: frozen_binary32
  is "(1, 124, 153629)" .

lift_definition frozen_embedding_8 :: frozen_binary32
  is "(1, 120, 2841710)" .

lift_definition frozen_embedding_9 :: frozen_binary32
  is "(1, 120, 771879)" .

lift_definition frozen_embedding_10 :: frozen_binary32
  is "(0, 123, 2103767)" .

lift_definition frozen_embedding_11 :: frozen_binary32
  is "(0, 122, 6336013)" .

lift_definition frozen_embedding_12 :: frozen_binary32
  is "(0, 125, 2797787)" .

lift_definition frozen_embedding_13 :: frozen_binary32
  is "(1, 124, 5531178)" .

lift_definition frozen_embedding_14 :: frozen_binary32
  is "(1, 124, 460533)" .

lift_definition frozen_embedding_15 :: frozen_binary32
  is "(1, 123, 2350548)" .

lift_definition frozen_embedding_16 :: frozen_binary32
  is "(1, 124, 350479)" .

lift_definition frozen_embedding_17 :: frozen_binary32
  is "(1, 124, 3291407)" .

lift_definition frozen_embedding_18 :: frozen_binary32
  is "(1, 123, 992045)" .

lift_definition frozen_embedding_19 :: frozen_binary32
  is "(0, 122, 3314477)" .

lift_definition frozen_embedding_20 :: frozen_binary32
  is "(0, 124, 8111437)" .

lift_definition frozen_embedding_21 :: frozen_binary32
  is "(1, 122, 588320)" .

lift_definition frozen_embedding_22 :: frozen_binary32
  is "(1, 122, 3677860)" .

lift_definition frozen_embedding_23 :: frozen_binary32
  is "(1, 124, 349479)" .

lift_definition frozen_embedding_24 :: frozen_binary32
  is "(0, 122, 7978651)" .

lift_definition frozen_embedding_25 :: frozen_binary32
  is "(1, 122, 8209427)" .

lift_definition frozen_embedding_26 :: frozen_binary32
  is "(1, 124, 638524)" .

lift_definition frozen_embedding_27 :: frozen_binary32
  is "(0, 124, 3777630)" .

lift_definition frozen_embedding_28 :: frozen_binary32
  is "(0, 125, 744085)" .

lift_definition frozen_embedding_29 :: frozen_binary32
  is "(1, 123, 2969911)" .

lift_definition frozen_embedding_30 :: frozen_binary32
  is "(1, 120, 7392880)" .

lift_definition frozen_embedding_31 :: frozen_binary32
  is "(1, 124, 934096)" .

lift_definition frozen_embedding_32 :: frozen_binary32
  is "(1, 123, 5022965)" .

lift_definition frozen_embedding_33 :: frozen_binary32
  is "(1, 124, 165071)" .

lift_definition frozen_embedding_34 :: frozen_binary32
  is "(0, 124, 2851502)" .

lift_definition frozen_embedding_35 :: frozen_binary32
  is "(0, 123, 1501519)" .

lift_definition frozen_embedding_36 :: frozen_binary32
  is "(0, 123, 7774871)" .

lift_definition frozen_embedding_37 :: frozen_binary32
  is "(1, 122, 2257260)" .

lift_definition frozen_embedding_38 :: frozen_binary32
  is "(1, 123, 2797954)" .

lift_definition frozen_embedding_39 :: frozen_binary32
  is "(0, 124, 2160532)" .

lift_definition frozen_embedding_40 :: frozen_binary32
  is "(0, 124, 100566)" .

lift_definition frozen_embedding_41 :: frozen_binary32
  is "(1, 121, 4669156)" .

lift_definition frozen_embedding_42 :: frozen_binary32
  is "(1, 124, 1471778)" .

lift_definition frozen_embedding_43 :: frozen_binary32
  is "(1, 120, 2435857)" .

lift_definition frozen_embedding_44 :: frozen_binary32
  is "(0, 123, 4183445)" .

lift_definition frozen_embedding_45 :: frozen_binary32
  is "(0, 123, 839455)" .

lift_definition frozen_embedding_46 :: frozen_binary32
  is "(0, 123, 1054274)" .

lift_definition frozen_embedding_47 :: frozen_binary32
  is "(0, 124, 2786495)" .

lift_definition frozen_embedding_48 :: frozen_binary32
  is "(0, 121, 7688957)" .

lift_definition frozen_embedding_49 :: frozen_binary32
  is "(0, 123, 1877686)" .

lift_definition frozen_embedding_50 :: frozen_binary32
  is "(0, 124, 2535363)" .

lift_definition frozen_embedding_51 :: frozen_binary32
  is "(1, 118, 3553136)" .

lift_definition frozen_embedding_52 :: frozen_binary32
  is "(0, 123, 7302229)" .

lift_definition frozen_embedding_53 :: frozen_binary32
  is "(1, 121, 2628688)" .

lift_definition frozen_embedding_54 :: frozen_binary32
  is "(1, 124, 8021435)" .

lift_definition frozen_embedding_55 :: frozen_binary32
  is "(0, 122, 8372337)" .

lift_definition frozen_embedding_56 :: frozen_binary32
  is "(1, 124, 1235890)" .

lift_definition frozen_embedding_57 :: frozen_binary32
  is "(1, 124, 1176480)" .

lift_definition frozen_embedding_58 :: frozen_binary32
  is "(1, 122, 3874130)" .

lift_definition frozen_embedding_59 :: frozen_binary32
  is "(1, 123, 1894818)" .

lift_definition frozen_embedding_60 :: frozen_binary32
  is "(0, 123, 4643282)" .

lift_definition frozen_embedding_61 :: frozen_binary32
  is "(1, 120, 1797825)" .

lift_definition frozen_embedding_62 :: frozen_binary32
  is "(1, 122, 6634529)" .

lift_definition frozen_embedding_63 :: frozen_binary32
  is "(1, 124, 3497855)" .

definition frozen_embedding :: "frozen_binary32 vector" where
  "frozen_embedding = [frozen_embedding_0, frozen_embedding_1, frozen_embedding_2, frozen_embedding_3, frozen_embedding_4, frozen_embedding_5, frozen_embedding_6, frozen_embedding_7, frozen_embedding_8, frozen_embedding_9, frozen_embedding_10, frozen_embedding_11, frozen_embedding_12, frozen_embedding_13, frozen_embedding_14, frozen_embedding_15, frozen_embedding_16, frozen_embedding_17, frozen_embedding_18, frozen_embedding_19, frozen_embedding_20, frozen_embedding_21, frozen_embedding_22, frozen_embedding_23, frozen_embedding_24, frozen_embedding_25, frozen_embedding_26, frozen_embedding_27, frozen_embedding_28, frozen_embedding_29, frozen_embedding_30, frozen_embedding_31, frozen_embedding_32, frozen_embedding_33, frozen_embedding_34, frozen_embedding_35, frozen_embedding_36, frozen_embedding_37, frozen_embedding_38, frozen_embedding_39, frozen_embedding_40, frozen_embedding_41, frozen_embedding_42, frozen_embedding_43, frozen_embedding_44, frozen_embedding_45, frozen_embedding_46, frozen_embedding_47, frozen_embedding_48, frozen_embedding_49, frozen_embedding_50, frozen_embedding_51, frozen_embedding_52, frozen_embedding_53, frozen_embedding_54, frozen_embedding_55, frozen_embedding_56, frozen_embedding_57, frozen_embedding_58, frozen_embedding_59, frozen_embedding_60, frozen_embedding_61, frozen_embedding_62, frozen_embedding_63]"

lift_definition frozen_position_embedding_0 :: frozen_binary32
  is "(0, 123, 6834890)" .

lift_definition frozen_position_embedding_1 :: frozen_binary32
  is "(1, 123, 2247292)" .

lift_definition frozen_position_embedding_2 :: frozen_binary32
  is "(1, 123, 2685672)" .

lift_definition frozen_position_embedding_3 :: frozen_binary32
  is "(0, 122, 5285549)" .

lift_definition frozen_position_embedding_4 :: frozen_binary32
  is "(0, 122, 4003512)" .

lift_definition frozen_position_embedding_5 :: frozen_binary32
  is "(1, 119, 1830391)" .

lift_definition frozen_position_embedding_6 :: frozen_binary32
  is "(0, 124, 730047)" .

lift_definition frozen_position_embedding_7 :: frozen_binary32
  is "(0, 120, 2673853)" .

lift_definition frozen_position_embedding_8 :: frozen_binary32
  is "(1, 123, 6999084)" .

lift_definition frozen_position_embedding_9 :: frozen_binary32
  is "(0, 121, 6284948)" .

lift_definition frozen_position_embedding_10 :: frozen_binary32
  is "(1, 123, 4579441)" .

lift_definition frozen_position_embedding_11 :: frozen_binary32
  is "(0, 122, 4009761)" .

lift_definition frozen_position_embedding_12 :: frozen_binary32
  is "(0, 120, 1475608)" .

lift_definition frozen_position_embedding_13 :: frozen_binary32
  is "(1, 123, 5763516)" .

lift_definition frozen_position_embedding_14 :: frozen_binary32
  is "(1, 123, 3497347)" .

lift_definition frozen_position_embedding_15 :: frozen_binary32
  is "(1, 121, 8134189)" .

lift_definition frozen_position_embedding_16 :: frozen_binary32
  is "(1, 120, 467460)" .

lift_definition frozen_position_embedding_17 :: frozen_binary32
  is "(1, 122, 5138390)" .

lift_definition frozen_position_embedding_18 :: frozen_binary32
  is "(1, 123, 3487886)" .

lift_definition frozen_position_embedding_19 :: frozen_binary32
  is "(0, 124, 624313)" .

lift_definition frozen_position_embedding_20 :: frozen_binary32
  is "(0, 122, 1050888)" .

lift_definition frozen_position_embedding_21 :: frozen_binary32
  is "(0, 123, 2095765)" .

lift_definition frozen_position_embedding_22 :: frozen_binary32
  is "(1, 120, 3784933)" .

lift_definition frozen_position_embedding_23 :: frozen_binary32
  is "(0, 120, 1237648)" .

lift_definition frozen_position_embedding_24 :: frozen_binary32
  is "(1, 123, 2240519)" .

lift_definition frozen_position_embedding_25 :: frozen_binary32
  is "(0, 123, 1274269)" .

lift_definition frozen_position_embedding_26 :: frozen_binary32
  is "(1, 123, 4570856)" .

lift_definition frozen_position_embedding_27 :: frozen_binary32
  is "(0, 122, 5037279)" .

lift_definition frozen_position_embedding_28 :: frozen_binary32
  is "(0, 122, 193764)" .

lift_definition frozen_position_embedding_29 :: frozen_binary32
  is "(0, 120, 6055250)" .

lift_definition frozen_position_embedding_30 :: frozen_binary32
  is "(0, 120, 3334649)" .

lift_definition frozen_position_embedding_31 :: frozen_binary32
  is "(0, 122, 5762943)" .

lift_definition frozen_position_embedding_32 :: frozen_binary32
  is "(0, 122, 1232976)" .

lift_definition frozen_position_embedding_33 :: frozen_binary32
  is "(1, 120, 1444170)" .

lift_definition frozen_position_embedding_34 :: frozen_binary32
  is "(1, 121, 7889879)" .

lift_definition frozen_position_embedding_35 :: frozen_binary32
  is "(0, 122, 6529135)" .

lift_definition frozen_position_embedding_36 :: frozen_binary32
  is "(1, 119, 5154390)" .

lift_definition frozen_position_embedding_37 :: frozen_binary32
  is "(1, 122, 4354395)" .

lift_definition frozen_position_embedding_38 :: frozen_binary32
  is "(1, 123, 3441543)" .

lift_definition frozen_position_embedding_39 :: frozen_binary32
  is "(1, 122, 209378)" .

lift_definition frozen_position_embedding_40 :: frozen_binary32
  is "(0, 122, 8086285)" .

lift_definition frozen_position_embedding_41 :: frozen_binary32
  is "(0, 122, 6927812)" .

lift_definition frozen_position_embedding_42 :: frozen_binary32
  is "(1, 124, 288524)" .

lift_definition frozen_position_embedding_43 :: frozen_binary32
  is "(1, 122, 5150856)" .

lift_definition frozen_position_embedding_44 :: frozen_binary32
  is "(1, 124, 206157)" .

lift_definition frozen_position_embedding_45 :: frozen_binary32
  is "(1, 122, 782221)" .

lift_definition frozen_position_embedding_46 :: frozen_binary32
  is "(0, 122, 5529046)" .

lift_definition frozen_position_embedding_47 :: frozen_binary32
  is "(1, 123, 5084929)" .

lift_definition frozen_position_embedding_48 :: frozen_binary32
  is "(0, 123, 3164351)" .

lift_definition frozen_position_embedding_49 :: frozen_binary32
  is "(1, 122, 4692803)" .

lift_definition frozen_position_embedding_50 :: frozen_binary32
  is "(1, 120, 4352345)" .

lift_definition frozen_position_embedding_51 :: frozen_binary32
  is "(0, 119, 3797983)" .

lift_definition frozen_position_embedding_52 :: frozen_binary32
  is "(1, 123, 5906369)" .

lift_definition frozen_position_embedding_53 :: frozen_binary32
  is "(1, 123, 3724803)" .

lift_definition frozen_position_embedding_54 :: frozen_binary32
  is "(1, 121, 4157412)" .

lift_definition frozen_position_embedding_55 :: frozen_binary32
  is "(1, 121, 6380686)" .

lift_definition frozen_position_embedding_56 :: frozen_binary32
  is "(0, 124, 826840)" .

lift_definition frozen_position_embedding_57 :: frozen_binary32
  is "(0, 123, 6550819)" .

lift_definition frozen_position_embedding_58 :: frozen_binary32
  is "(0, 123, 1056291)" .

lift_definition frozen_position_embedding_59 :: frozen_binary32
  is "(1, 120, 3879974)" .

lift_definition frozen_position_embedding_60 :: frozen_binary32
  is "(0, 122, 5649743)" .

lift_definition frozen_position_embedding_61 :: frozen_binary32
  is "(0, 123, 2720454)" .

lift_definition frozen_position_embedding_62 :: frozen_binary32
  is "(0, 124, 82375)" .

lift_definition frozen_position_embedding_63 :: frozen_binary32
  is "(0, 123, 184526)" .

definition frozen_position_embedding :: "frozen_binary32 vector" where
  "frozen_position_embedding = [frozen_position_embedding_0, frozen_position_embedding_1, frozen_position_embedding_2, frozen_position_embedding_3, frozen_position_embedding_4, frozen_position_embedding_5, frozen_position_embedding_6, frozen_position_embedding_7, frozen_position_embedding_8, frozen_position_embedding_9, frozen_position_embedding_10, frozen_position_embedding_11, frozen_position_embedding_12, frozen_position_embedding_13, frozen_position_embedding_14, frozen_position_embedding_15, frozen_position_embedding_16, frozen_position_embedding_17, frozen_position_embedding_18, frozen_position_embedding_19, frozen_position_embedding_20, frozen_position_embedding_21, frozen_position_embedding_22, frozen_position_embedding_23, frozen_position_embedding_24, frozen_position_embedding_25, frozen_position_embedding_26, frozen_position_embedding_27, frozen_position_embedding_28, frozen_position_embedding_29, frozen_position_embedding_30, frozen_position_embedding_31, frozen_position_embedding_32, frozen_position_embedding_33, frozen_position_embedding_34, frozen_position_embedding_35, frozen_position_embedding_36, frozen_position_embedding_37, frozen_position_embedding_38, frozen_position_embedding_39, frozen_position_embedding_40, frozen_position_embedding_41, frozen_position_embedding_42, frozen_position_embedding_43, frozen_position_embedding_44, frozen_position_embedding_45, frozen_position_embedding_46, frozen_position_embedding_47, frozen_position_embedding_48, frozen_position_embedding_49, frozen_position_embedding_50, frozen_position_embedding_51, frozen_position_embedding_52, frozen_position_embedding_53, frozen_position_embedding_54, frozen_position_embedding_55, frozen_position_embedding_56, frozen_position_embedding_57, frozen_position_embedding_58, frozen_position_embedding_59, frozen_position_embedding_60, frozen_position_embedding_61, frozen_position_embedding_62, frozen_position_embedding_63]"

lift_definition frozen_input_activation_0 :: frozen_binary32
  is "(0, 124, 5954621)" .

lift_definition frozen_input_activation_1 :: frozen_binary32
  is "(1, 124, 2814668)" .

lift_definition frozen_input_activation_2 :: frozen_binary32
  is "(1, 124, 5088346)" .

lift_definition frozen_input_activation_3 :: frozen_binary32
  is "(0, 122, 4988295)" .

lift_definition frozen_input_activation_4 :: frozen_binary32
  is "(0, 123, 4355862)" .

lift_definition frozen_input_activation_5 :: frozen_binary32
  is "(1, 122, 7139934)" .

lift_definition frozen_input_activation_6 :: frozen_binary32
  is "(0, 123, 7769643)" .

lift_definition frozen_input_activation_7 :: frozen_binary32
  is "(1, 123, 7313058)" .

lift_definition frozen_input_activation_8 :: frozen_binary32
  is "(1, 124, 7133)" .

lift_definition frozen_input_activation_9 :: frozen_binary32
  is "(0, 121, 1704704)" .

lift_definition frozen_input_activation_10 :: frozen_binary32
  is "(1, 121, 1514088)" .

lift_definition frozen_input_activation_11 :: frozen_binary32
  is "(0, 123, 5172887)" .

lift_definition frozen_input_activation_12 :: frozen_binary32
  is "(0, 125, 3106044)" .

lift_definition frozen_input_activation_13 :: frozen_binary32
  is "(1, 125, 2109316)" .

lift_definition frozen_input_activation_14 :: frozen_binary32
  is "(1, 124, 6403510)" .

lift_definition frozen_input_activation_15 :: frozen_binary32
  is "(1, 123, 6481247)" .

lift_definition frozen_input_activation_16 :: frozen_binary32
  is "(1, 124, 903983)" .

lift_definition frozen_input_activation_17 :: frozen_binary32
  is "(1, 124, 6673156)" .

lift_definition frozen_input_activation_18 :: frozen_binary32
  is "(1, 124, 2239966)" .

lift_definition frozen_input_activation_19 :: frozen_binary32
  is "(0, 124, 3550084)" .

lift_definition frozen_input_activation_20 :: frozen_binary32
  is "(0, 125, 1041352)" .

lift_definition frozen_input_activation_21 :: frozen_binary32
  is "(0, 122, 3603210)" .

lift_definition frozen_input_activation_22 :: frozen_binary32
  is "(1, 122, 6721245)" .

lift_definition frozen_input_activation_23 :: frozen_binary32
  is "(1, 123, 7884284)" .

lift_definition frozen_input_activation_24 :: frozen_binary32
  is "(1, 121, 1393382)" .

lift_definition frozen_input_activation_25 :: frozen_binary32
  is "(0, 120, 2522268)" .

lift_definition frozen_input_activation_26 :: frozen_binary32
  is "(1, 124, 7118256)" .

lift_definition frozen_input_activation_27 :: frozen_binary32
  is "(0, 124, 7134102)" .

lift_definition frozen_input_activation_28 :: frozen_binary32
  is "(0, 125, 1816882)" .

lift_definition frozen_input_activation_29 :: frozen_binary32
  is "(1, 123, 1164429)" .

lift_definition frozen_input_activation_30 :: frozen_binary32
  is "(1, 118, 7844316)" .

lift_definition frozen_input_activation_31 :: frozen_binary32
  is "(1, 123, 3181024)" .

lift_definition frozen_input_activation_32 :: frozen_binary32
  is "(1, 123, 212173)" .

lift_definition frozen_input_activation_33 :: frozen_binary32
  is "(1, 124, 779620)" .

lift_definition frozen_input_activation_34 :: frozen_binary32
  is "(0, 124, 816691)" .

lift_definition frozen_input_activation_35 :: frozen_binary32
  is "(0, 124, 285891)" .

lift_definition frozen_input_activation_36 :: frozen_binary32
  is "(0, 123, 6928434)" .

lift_definition frozen_input_activation_37 :: frozen_binary32
  is "(1, 123, 3305828)" .

lift_definition frozen_input_activation_38 :: frozen_binary32
  is "(1, 124, 3119748)" .

lift_definition frozen_input_activation_39 :: frozen_binary32
  is "(0, 124, 11036)" .

lift_definition frozen_input_activation_40 :: frozen_binary32
  is "(0, 124, 4219289)" .

lift_definition frozen_input_activation_41 :: frozen_binary32
  is "(0, 122, 398930)" .

lift_definition frozen_input_activation_42 :: frozen_binary32
  is "(1, 125, 880151)" .

lift_definition frozen_input_activation_43 :: frozen_binary32
  is "(1, 122, 7856972)" .

lift_definition frozen_input_activation_44 :: frozen_binary32
  is "(1, 122, 846346)" .

lift_definition frozen_input_activation_45 :: frozen_binary32
  is "(0, 122, 896689)" .

lift_definition frozen_input_activation_46 :: frozen_binary32
  is "(0, 123, 8013101)" .

lift_definition frozen_input_activation_47 :: frozen_binary32
  is "(0, 123, 488061)" .

lift_definition frozen_input_activation_48 :: frozen_binary32
  is "(0, 123, 7183742)" .

lift_definition frozen_input_activation_49 :: frozen_binary32
  is "(0, 121, 6513746)" .

lift_definition frozen_input_activation_50 :: frozen_binary32
  is "(0, 124, 1739053)" .

lift_definition frozen_input_activation_51 :: frozen_binary32
  is "(0, 118, 4042830)" .

lift_definition frozen_input_activation_52 :: frozen_binary32
  is "(0, 120, 2778272)" .

lift_definition frozen_input_activation_53 :: frozen_binary32
  is "(1, 123, 6479127)" .

lift_definition frozen_input_activation_54 :: frozen_binary32
  is "(1, 125, 600540)" .

lift_definition frozen_input_activation_55 :: frozen_binary32
  is "(0, 122, 987690)" .

lift_definition frozen_input_activation_56 :: frozen_binary32
  is "(1, 119, 4700992)" .

lift_definition frozen_input_activation_57 :: frozen_binary32
  is "(1, 121, 8374388)" .

lift_definition frozen_input_activation_58 :: frozen_binary32
  is "(0, 121, 4865512)" .

lift_definition frozen_input_activation_59 :: frozen_binary32
  is "(1, 123, 3428391)" .

lift_definition frozen_input_activation_60 :: frozen_binary32
  is "(0, 124, 1636925)" .

lift_definition frozen_input_activation_61 :: frozen_binary32
  is "(0, 123, 1447150)" .

lift_definition frozen_input_activation_62 :: frozen_binary32
  is "(0, 123, 1041790)" .

lift_definition frozen_input_activation_63 :: frozen_binary32
  is "(1, 123, 6811184)" .

definition frozen_input_activation :: "frozen_binary32 vector" where
  "frozen_input_activation = [frozen_input_activation_0, frozen_input_activation_1, frozen_input_activation_2, frozen_input_activation_3, frozen_input_activation_4, frozen_input_activation_5, frozen_input_activation_6, frozen_input_activation_7, frozen_input_activation_8, frozen_input_activation_9, frozen_input_activation_10, frozen_input_activation_11, frozen_input_activation_12, frozen_input_activation_13, frozen_input_activation_14, frozen_input_activation_15, frozen_input_activation_16, frozen_input_activation_17, frozen_input_activation_18, frozen_input_activation_19, frozen_input_activation_20, frozen_input_activation_21, frozen_input_activation_22, frozen_input_activation_23, frozen_input_activation_24, frozen_input_activation_25, frozen_input_activation_26, frozen_input_activation_27, frozen_input_activation_28, frozen_input_activation_29, frozen_input_activation_30, frozen_input_activation_31, frozen_input_activation_32, frozen_input_activation_33, frozen_input_activation_34, frozen_input_activation_35, frozen_input_activation_36, frozen_input_activation_37, frozen_input_activation_38, frozen_input_activation_39, frozen_input_activation_40, frozen_input_activation_41, frozen_input_activation_42, frozen_input_activation_43, frozen_input_activation_44, frozen_input_activation_45, frozen_input_activation_46, frozen_input_activation_47, frozen_input_activation_48, frozen_input_activation_49, frozen_input_activation_50, frozen_input_activation_51, frozen_input_activation_52, frozen_input_activation_53, frozen_input_activation_54, frozen_input_activation_55, frozen_input_activation_56, frozen_input_activation_57, frozen_input_activation_58, frozen_input_activation_59, frozen_input_activation_60, frozen_input_activation_61, frozen_input_activation_62, frozen_input_activation_63]"

lift_definition frozen_kernel_0_0 :: frozen_binary32
  is "(1, 118, 5224699)" .

lift_definition frozen_kernel_0_1 :: frozen_binary32
  is "(0, 122, 3128469)" .

lift_definition frozen_kernel_0_2 :: frozen_binary32
  is "(0, 121, 7637911)" .

lift_definition frozen_kernel_0_3 :: frozen_binary32
  is "(1, 119, 8381415)" .

lift_definition frozen_kernel_0_4 :: frozen_binary32
  is "(0, 120, 6738071)" .

lift_definition frozen_kernel_0_5 :: frozen_binary32
  is "(0, 121, 3087089)" .

lift_definition frozen_kernel_0_6 :: frozen_binary32
  is "(1, 121, 299807)" .

lift_definition frozen_kernel_0_7 :: frozen_binary32
  is "(1, 119, 2209599)" .

lift_definition frozen_kernel_0_8 :: frozen_binary32
  is "(0, 122, 4026999)" .

lift_definition frozen_kernel_0_9 :: frozen_binary32
  is "(0, 120, 2430844)" .

lift_definition frozen_kernel_0_10 :: frozen_binary32
  is "(0, 121, 3687498)" .

lift_definition frozen_kernel_0_11 :: frozen_binary32
  is "(0, 122, 554361)" .

lift_definition frozen_kernel_0_12 :: frozen_binary32
  is "(1, 122, 5458651)" .

lift_definition frozen_kernel_0_13 :: frozen_binary32
  is "(1, 120, 4778072)" .

lift_definition frozen_kernel_0_14 :: frozen_binary32
  is "(0, 121, 1407349)" .

lift_definition frozen_kernel_0_15 :: frozen_binary32
  is "(1, 121, 4170002)" .

lift_definition frozen_kernel_0_16 :: frozen_binary32
  is "(1, 121, 1869772)" .

lift_definition frozen_kernel_0_17 :: frozen_binary32
  is "(1, 121, 3281070)" .

lift_definition frozen_kernel_0_18 :: frozen_binary32
  is "(1, 122, 1758620)" .

lift_definition frozen_kernel_0_19 :: frozen_binary32
  is "(0, 118, 686048)" .

lift_definition frozen_kernel_0_20 :: frozen_binary32
  is "(0, 121, 3743167)" .

lift_definition frozen_kernel_0_21 :: frozen_binary32
  is "(1, 119, 2418418)" .

lift_definition frozen_kernel_0_22 :: frozen_binary32
  is "(0, 119, 2015393)" .

lift_definition frozen_kernel_0_23 :: frozen_binary32
  is "(0, 119, 703489)" .

lift_definition frozen_kernel_0_24 :: frozen_binary32
  is "(0, 122, 1645734)" .

lift_definition frozen_kernel_0_25 :: frozen_binary32
  is "(0, 118, 5996730)" .

lift_definition frozen_kernel_0_26 :: frozen_binary32
  is "(1, 121, 1822788)" .

lift_definition frozen_kernel_0_27 :: frozen_binary32
  is "(0, 121, 1277057)" .

lift_definition frozen_kernel_0_28 :: frozen_binary32
  is "(1, 122, 1427378)" .

lift_definition frozen_kernel_0_29 :: frozen_binary32
  is "(1, 119, 3639482)" .

lift_definition frozen_kernel_0_30 :: frozen_binary32
  is "(0, 119, 1348070)" .

lift_definition frozen_kernel_0_31 :: frozen_binary32
  is "(1, 123, 288156)" .

lift_definition frozen_kernel_0_32 :: frozen_binary32
  is "(0, 123, 90798)" .

lift_definition frozen_kernel_0_33 :: frozen_binary32
  is "(1, 120, 4808610)" .

lift_definition frozen_kernel_0_34 :: frozen_binary32
  is "(1, 121, 1525205)" .

lift_definition frozen_kernel_0_35 :: frozen_binary32
  is "(1, 121, 7194731)" .

lift_definition frozen_kernel_0_36 :: frozen_binary32
  is "(1, 120, 4369203)" .

lift_definition frozen_kernel_0_37 :: frozen_binary32
  is "(0, 116, 2958092)" .

lift_definition frozen_kernel_0_38 :: frozen_binary32
  is "(0, 118, 1208593)" .

lift_definition frozen_kernel_0_39 :: frozen_binary32
  is "(1, 121, 1599792)" .

lift_definition frozen_kernel_0_40 :: frozen_binary32
  is "(1, 118, 2806924)" .

lift_definition frozen_kernel_0_41 :: frozen_binary32
  is "(0, 122, 5118147)" .

lift_definition frozen_kernel_0_42 :: frozen_binary32
  is "(0, 123, 1905657)" .

lift_definition frozen_kernel_0_43 :: frozen_binary32
  is "(0, 122, 855751)" .

lift_definition frozen_kernel_0_44 :: frozen_binary32
  is "(1, 122, 4038769)" .

lift_definition frozen_kernel_0_45 :: frozen_binary32
  is "(0, 122, 3288804)" .

lift_definition frozen_kernel_0_46 :: frozen_binary32
  is "(1, 122, 3075038)" .

lift_definition frozen_kernel_0_47 :: frozen_binary32
  is "(0, 122, 38155)" .

lift_definition frozen_kernel_0_48 :: frozen_binary32
  is "(0, 121, 4047975)" .

lift_definition frozen_kernel_0_49 :: frozen_binary32
  is "(1, 122, 5610822)" .

lift_definition frozen_kernel_0_50 :: frozen_binary32
  is "(0, 122, 6642879)" .

lift_definition frozen_kernel_0_51 :: frozen_binary32
  is "(1, 122, 4702632)" .

lift_definition frozen_kernel_0_52 :: frozen_binary32
  is "(0, 120, 1051091)" .

lift_definition frozen_kernel_0_53 :: frozen_binary32
  is "(1, 118, 1249983)" .

lift_definition frozen_kernel_0_54 :: frozen_binary32
  is "(0, 120, 3830612)" .

lift_definition frozen_kernel_0_55 :: frozen_binary32
  is "(0, 121, 5080758)" .

lift_definition frozen_kernel_0_56 :: frozen_binary32
  is "(0, 122, 5890291)" .

lift_definition frozen_kernel_0_57 :: frozen_binary32
  is "(1, 121, 7593629)" .

lift_definition frozen_kernel_0_58 :: frozen_binary32
  is "(1, 123, 251443)" .

lift_definition frozen_kernel_0_59 :: frozen_binary32
  is "(0, 123, 2891762)" .

lift_definition frozen_kernel_0_60 :: frozen_binary32
  is "(1, 122, 5342669)" .

lift_definition frozen_kernel_0_61 :: frozen_binary32
  is "(1, 121, 7770590)" .

lift_definition frozen_kernel_0_62 :: frozen_binary32
  is "(1, 122, 963613)" .

lift_definition frozen_kernel_0_63 :: frozen_binary32
  is "(1, 118, 2563801)" .

definition frozen_kernel_0 :: "frozen_binary32 vector" where
  "frozen_kernel_0 = [frozen_kernel_0_0, frozen_kernel_0_1, frozen_kernel_0_2, frozen_kernel_0_3, frozen_kernel_0_4, frozen_kernel_0_5, frozen_kernel_0_6, frozen_kernel_0_7, frozen_kernel_0_8, frozen_kernel_0_9, frozen_kernel_0_10, frozen_kernel_0_11, frozen_kernel_0_12, frozen_kernel_0_13, frozen_kernel_0_14, frozen_kernel_0_15, frozen_kernel_0_16, frozen_kernel_0_17, frozen_kernel_0_18, frozen_kernel_0_19, frozen_kernel_0_20, frozen_kernel_0_21, frozen_kernel_0_22, frozen_kernel_0_23, frozen_kernel_0_24, frozen_kernel_0_25, frozen_kernel_0_26, frozen_kernel_0_27, frozen_kernel_0_28, frozen_kernel_0_29, frozen_kernel_0_30, frozen_kernel_0_31, frozen_kernel_0_32, frozen_kernel_0_33, frozen_kernel_0_34, frozen_kernel_0_35, frozen_kernel_0_36, frozen_kernel_0_37, frozen_kernel_0_38, frozen_kernel_0_39, frozen_kernel_0_40, frozen_kernel_0_41, frozen_kernel_0_42, frozen_kernel_0_43, frozen_kernel_0_44, frozen_kernel_0_45, frozen_kernel_0_46, frozen_kernel_0_47, frozen_kernel_0_48, frozen_kernel_0_49, frozen_kernel_0_50, frozen_kernel_0_51, frozen_kernel_0_52, frozen_kernel_0_53, frozen_kernel_0_54, frozen_kernel_0_55, frozen_kernel_0_56, frozen_kernel_0_57, frozen_kernel_0_58, frozen_kernel_0_59, frozen_kernel_0_60, frozen_kernel_0_61, frozen_kernel_0_62, frozen_kernel_0_63]"

lift_definition frozen_kernel_1_0 :: frozen_binary32
  is "(0, 123, 1354358)" .

lift_definition frozen_kernel_1_1 :: frozen_binary32
  is "(1, 123, 1197167)" .

lift_definition frozen_kernel_1_2 :: frozen_binary32
  is "(1, 121, 7222080)" .

lift_definition frozen_kernel_1_3 :: frozen_binary32
  is "(0, 123, 1486014)" .

lift_definition frozen_kernel_1_4 :: frozen_binary32
  is "(0, 123, 4285308)" .

lift_definition frozen_kernel_1_5 :: frozen_binary32
  is "(0, 122, 267822)" .

lift_definition frozen_kernel_1_6 :: frozen_binary32
  is "(0, 122, 8034609)" .

lift_definition frozen_kernel_1_7 :: frozen_binary32
  is "(1, 122, 77048)" .

lift_definition frozen_kernel_1_8 :: frozen_binary32
  is "(0, 122, 1891076)" .

lift_definition frozen_kernel_1_9 :: frozen_binary32
  is "(0, 122, 5335006)" .

lift_definition frozen_kernel_1_10 :: frozen_binary32
  is "(1, 123, 264536)" .

lift_definition frozen_kernel_1_11 :: frozen_binary32
  is "(0, 121, 4227652)" .

lift_definition frozen_kernel_1_12 :: frozen_binary32
  is "(1, 124, 533454)" .

lift_definition frozen_kernel_1_13 :: frozen_binary32
  is "(1, 123, 4842360)" .

lift_definition frozen_kernel_1_14 :: frozen_binary32
  is "(1, 122, 570502)" .

lift_definition frozen_kernel_1_15 :: frozen_binary32
  is "(1, 123, 2323780)" .

lift_definition frozen_kernel_1_16 :: frozen_binary32
  is "(1, 119, 5276935)" .

lift_definition frozen_kernel_1_17 :: frozen_binary32
  is "(1, 122, 1919277)" .

lift_definition frozen_kernel_1_18 :: frozen_binary32
  is "(0, 120, 7240382)" .

lift_definition frozen_kernel_1_19 :: frozen_binary32
  is "(1, 122, 8138915)" .

lift_definition frozen_kernel_1_20 :: frozen_binary32
  is "(0, 123, 536248)" .

lift_definition frozen_kernel_1_21 :: frozen_binary32
  is "(0, 124, 947364)" .

lift_definition frozen_kernel_1_22 :: frozen_binary32
  is "(0, 122, 5161997)" .

lift_definition frozen_kernel_1_23 :: frozen_binary32
  is "(1, 120, 91511)" .

lift_definition frozen_kernel_1_24 :: frozen_binary32
  is "(0, 122, 2762327)" .

lift_definition frozen_kernel_1_25 :: frozen_binary32
  is "(1, 122, 920367)" .

lift_definition frozen_kernel_1_26 :: frozen_binary32
  is "(0, 122, 3004765)" .

lift_definition frozen_kernel_1_27 :: frozen_binary32
  is "(0, 123, 2722710)" .

lift_definition frozen_kernel_1_28 :: frozen_binary32
  is "(0, 122, 1850932)" .

lift_definition frozen_kernel_1_29 :: frozen_binary32
  is "(1, 122, 146614)" .

lift_definition frozen_kernel_1_30 :: frozen_binary32
  is "(1, 122, 8271729)" .

lift_definition frozen_kernel_1_31 :: frozen_binary32
  is "(1, 122, 5391442)" .

lift_definition frozen_kernel_1_32 :: frozen_binary32
  is "(0, 121, 7748470)" .

lift_definition frozen_kernel_1_33 :: frozen_binary32
  is "(0, 122, 7073732)" .

lift_definition frozen_kernel_1_34 :: frozen_binary32
  is "(0, 121, 7899362)" .

lift_definition frozen_kernel_1_35 :: frozen_binary32
  is "(0, 120, 2694524)" .

lift_definition frozen_kernel_1_36 :: frozen_binary32
  is "(1, 121, 1430455)" .

lift_definition frozen_kernel_1_37 :: frozen_binary32
  is "(1, 119, 4416350)" .

lift_definition frozen_kernel_1_38 :: frozen_binary32
  is "(0, 122, 1588126)" .

lift_definition frozen_kernel_1_39 :: frozen_binary32
  is "(1, 119, 3771550)" .

lift_definition frozen_kernel_1_40 :: frozen_binary32
  is "(0, 122, 6072260)" .

lift_definition frozen_kernel_1_41 :: frozen_binary32
  is "(1, 123, 2120345)" .

lift_definition frozen_kernel_1_42 :: frozen_binary32
  is "(0, 122, 3995011)" .

lift_definition frozen_kernel_1_43 :: frozen_binary32
  is "(0, 121, 7885399)" .

lift_definition frozen_kernel_1_44 :: frozen_binary32
  is "(0, 120, 3268294)" .

lift_definition frozen_kernel_1_45 :: frozen_binary32
  is "(1, 120, 309075)" .

lift_definition frozen_kernel_1_46 :: frozen_binary32
  is "(0, 120, 8248022)" .

lift_definition frozen_kernel_1_47 :: frozen_binary32
  is "(0, 122, 7629628)" .

lift_definition frozen_kernel_1_48 :: frozen_binary32
  is "(0, 123, 1505554)" .

lift_definition frozen_kernel_1_49 :: frozen_binary32
  is "(1, 123, 993221)" .

lift_definition frozen_kernel_1_50 :: frozen_binary32
  is "(1, 123, 2156306)" .

lift_definition frozen_kernel_1_51 :: frozen_binary32
  is "(1, 123, 4267018)" .

lift_definition frozen_kernel_1_52 :: frozen_binary32
  is "(0, 122, 2479212)" .

lift_definition frozen_kernel_1_53 :: frozen_binary32
  is "(0, 122, 3689305)" .

lift_definition frozen_kernel_1_54 :: frozen_binary32
  is "(1, 123, 3567316)" .

lift_definition frozen_kernel_1_55 :: frozen_binary32
  is "(1, 122, 2632131)" .

lift_definition frozen_kernel_1_56 :: frozen_binary32
  is "(0, 121, 4295384)" .

lift_definition frozen_kernel_1_57 :: frozen_binary32
  is "(1, 122, 1453705)" .

lift_definition frozen_kernel_1_58 :: frozen_binary32
  is "(0, 124, 358750)" .

lift_definition frozen_kernel_1_59 :: frozen_binary32
  is "(1, 121, 4104420)" .

lift_definition frozen_kernel_1_60 :: frozen_binary32
  is "(1, 122, 6513894)" .

lift_definition frozen_kernel_1_61 :: frozen_binary32
  is "(1, 123, 4089748)" .

lift_definition frozen_kernel_1_62 :: frozen_binary32
  is "(1, 123, 194969)" .

lift_definition frozen_kernel_1_63 :: frozen_binary32
  is "(0, 109, 7936852)" .

definition frozen_kernel_1 :: "frozen_binary32 vector" where
  "frozen_kernel_1 = [frozen_kernel_1_0, frozen_kernel_1_1, frozen_kernel_1_2, frozen_kernel_1_3, frozen_kernel_1_4, frozen_kernel_1_5, frozen_kernel_1_6, frozen_kernel_1_7, frozen_kernel_1_8, frozen_kernel_1_9, frozen_kernel_1_10, frozen_kernel_1_11, frozen_kernel_1_12, frozen_kernel_1_13, frozen_kernel_1_14, frozen_kernel_1_15, frozen_kernel_1_16, frozen_kernel_1_17, frozen_kernel_1_18, frozen_kernel_1_19, frozen_kernel_1_20, frozen_kernel_1_21, frozen_kernel_1_22, frozen_kernel_1_23, frozen_kernel_1_24, frozen_kernel_1_25, frozen_kernel_1_26, frozen_kernel_1_27, frozen_kernel_1_28, frozen_kernel_1_29, frozen_kernel_1_30, frozen_kernel_1_31, frozen_kernel_1_32, frozen_kernel_1_33, frozen_kernel_1_34, frozen_kernel_1_35, frozen_kernel_1_36, frozen_kernel_1_37, frozen_kernel_1_38, frozen_kernel_1_39, frozen_kernel_1_40, frozen_kernel_1_41, frozen_kernel_1_42, frozen_kernel_1_43, frozen_kernel_1_44, frozen_kernel_1_45, frozen_kernel_1_46, frozen_kernel_1_47, frozen_kernel_1_48, frozen_kernel_1_49, frozen_kernel_1_50, frozen_kernel_1_51, frozen_kernel_1_52, frozen_kernel_1_53, frozen_kernel_1_54, frozen_kernel_1_55, frozen_kernel_1_56, frozen_kernel_1_57, frozen_kernel_1_58, frozen_kernel_1_59, frozen_kernel_1_60, frozen_kernel_1_61, frozen_kernel_1_62, frozen_kernel_1_63]"

lift_definition frozen_kernel_2_0 :: frozen_binary32
  is "(1, 120, 3350547)" .

lift_definition frozen_kernel_2_1 :: frozen_binary32
  is "(1, 120, 2390278)" .

lift_definition frozen_kernel_2_2 :: frozen_binary32
  is "(1, 121, 1658206)" .

lift_definition frozen_kernel_2_3 :: frozen_binary32
  is "(1, 120, 6779796)" .

lift_definition frozen_kernel_2_4 :: frozen_binary32
  is "(1, 120, 457501)" .

lift_definition frozen_kernel_2_5 :: frozen_binary32
  is "(1, 121, 5163568)" .

lift_definition frozen_kernel_2_6 :: frozen_binary32
  is "(1, 121, 2534389)" .

lift_definition frozen_kernel_2_7 :: frozen_binary32
  is "(1, 121, 1312917)" .

lift_definition frozen_kernel_2_8 :: frozen_binary32
  is "(0, 121, 1918106)" .

lift_definition frozen_kernel_2_9 :: frozen_binary32
  is "(0, 120, 5834289)" .

lift_definition frozen_kernel_2_10 :: frozen_binary32
  is "(0, 123, 1100218)" .

lift_definition frozen_kernel_2_11 :: frozen_binary32
  is "(1, 121, 13279)" .

lift_definition frozen_kernel_2_12 :: frozen_binary32
  is "(0, 120, 7471389)" .

lift_definition frozen_kernel_2_13 :: frozen_binary32
  is "(0, 120, 6729382)" .

lift_definition frozen_kernel_2_14 :: frozen_binary32
  is "(0, 120, 294353)" .

lift_definition frozen_kernel_2_15 :: frozen_binary32
  is "(1, 120, 7120333)" .

lift_definition frozen_kernel_2_16 :: frozen_binary32
  is "(1, 120, 7690559)" .

lift_definition frozen_kernel_2_17 :: frozen_binary32
  is "(0, 119, 6032231)" .

lift_definition frozen_kernel_2_18 :: frozen_binary32
  is "(1, 121, 6589094)" .

lift_definition frozen_kernel_2_19 :: frozen_binary32
  is "(0, 120, 2335207)" .

lift_definition frozen_kernel_2_20 :: frozen_binary32
  is "(0, 121, 1899376)" .

lift_definition frozen_kernel_2_21 :: frozen_binary32
  is "(1, 120, 1704646)" .

lift_definition frozen_kernel_2_22 :: frozen_binary32
  is "(0, 115, 6742331)" .

lift_definition frozen_kernel_2_23 :: frozen_binary32
  is "(1, 119, 1969682)" .

lift_definition frozen_kernel_2_24 :: frozen_binary32
  is "(0, 120, 905079)" .

lift_definition frozen_kernel_2_25 :: frozen_binary32
  is "(0, 122, 3077336)" .

lift_definition frozen_kernel_2_26 :: frozen_binary32
  is "(0, 121, 1353263)" .

lift_definition frozen_kernel_2_27 :: frozen_binary32
  is "(0, 118, 1498835)" .

lift_definition frozen_kernel_2_28 :: frozen_binary32
  is "(0, 120, 4433162)" .

lift_definition frozen_kernel_2_29 :: frozen_binary32
  is "(1, 119, 7371888)" .

lift_definition frozen_kernel_2_30 :: frozen_binary32
  is "(1, 117, 1728602)" .

lift_definition frozen_kernel_2_31 :: frozen_binary32
  is "(1, 119, 479840)" .

lift_definition frozen_kernel_2_32 :: frozen_binary32
  is "(0, 120, 4022739)" .

lift_definition frozen_kernel_2_33 :: frozen_binary32
  is "(1, 120, 6648237)" .

lift_definition frozen_kernel_2_34 :: frozen_binary32
  is "(1, 119, 4236553)" .

lift_definition frozen_kernel_2_35 :: frozen_binary32
  is "(0, 118, 6972305)" .

lift_definition frozen_kernel_2_36 :: frozen_binary32
  is "(0, 119, 250677)" .

lift_definition frozen_kernel_2_37 :: frozen_binary32
  is "(0, 120, 706434)" .

lift_definition frozen_kernel_2_38 :: frozen_binary32
  is "(1, 120, 1417744)" .

lift_definition frozen_kernel_2_39 :: frozen_binary32
  is "(0, 121, 4874168)" .

lift_definition frozen_kernel_2_40 :: frozen_binary32
  is "(1, 120, 1991347)" .

lift_definition frozen_kernel_2_41 :: frozen_binary32
  is "(0, 119, 7297330)" .

lift_definition frozen_kernel_2_42 :: frozen_binary32
  is "(0, 120, 1386744)" .

lift_definition frozen_kernel_2_43 :: frozen_binary32
  is "(1, 121, 1576847)" .

lift_definition frozen_kernel_2_44 :: frozen_binary32
  is "(0, 120, 4110101)" .

lift_definition frozen_kernel_2_45 :: frozen_binary32
  is "(1, 120, 4377528)" .

lift_definition frozen_kernel_2_46 :: frozen_binary32
  is "(1, 120, 7646547)" .

lift_definition frozen_kernel_2_47 :: frozen_binary32
  is "(1, 119, 7834348)" .

lift_definition frozen_kernel_2_48 :: frozen_binary32
  is "(0, 116, 2360222)" .

lift_definition frozen_kernel_2_49 :: frozen_binary32
  is "(0, 119, 5276912)" .

lift_definition frozen_kernel_2_50 :: frozen_binary32
  is "(1, 119, 3112615)" .

lift_definition frozen_kernel_2_51 :: frozen_binary32
  is "(0, 121, 1136855)" .

lift_definition frozen_kernel_2_52 :: frozen_binary32
  is "(0, 119, 6904828)" .

lift_definition frozen_kernel_2_53 :: frozen_binary32
  is "(0, 121, 2082326)" .

lift_definition frozen_kernel_2_54 :: frozen_binary32
  is "(0, 120, 8209858)" .

lift_definition frozen_kernel_2_55 :: frozen_binary32
  is "(1, 120, 3819251)" .

lift_definition frozen_kernel_2_56 :: frozen_binary32
  is "(1, 120, 55545)" .

lift_definition frozen_kernel_2_57 :: frozen_binary32
  is "(1, 121, 868402)" .

lift_definition frozen_kernel_2_58 :: frozen_binary32
  is "(0, 119, 4223153)" .

lift_definition frozen_kernel_2_59 :: frozen_binary32
  is "(0, 120, 8135226)" .

lift_definition frozen_kernel_2_60 :: frozen_binary32
  is "(0, 120, 7599904)" .

lift_definition frozen_kernel_2_61 :: frozen_binary32
  is "(1, 120, 3104494)" .

lift_definition frozen_kernel_2_62 :: frozen_binary32
  is "(0, 121, 2017299)" .

lift_definition frozen_kernel_2_63 :: frozen_binary32
  is "(0, 119, 2508278)" .

definition frozen_kernel_2 :: "frozen_binary32 vector" where
  "frozen_kernel_2 = [frozen_kernel_2_0, frozen_kernel_2_1, frozen_kernel_2_2, frozen_kernel_2_3, frozen_kernel_2_4, frozen_kernel_2_5, frozen_kernel_2_6, frozen_kernel_2_7, frozen_kernel_2_8, frozen_kernel_2_9, frozen_kernel_2_10, frozen_kernel_2_11, frozen_kernel_2_12, frozen_kernel_2_13, frozen_kernel_2_14, frozen_kernel_2_15, frozen_kernel_2_16, frozen_kernel_2_17, frozen_kernel_2_18, frozen_kernel_2_19, frozen_kernel_2_20, frozen_kernel_2_21, frozen_kernel_2_22, frozen_kernel_2_23, frozen_kernel_2_24, frozen_kernel_2_25, frozen_kernel_2_26, frozen_kernel_2_27, frozen_kernel_2_28, frozen_kernel_2_29, frozen_kernel_2_30, frozen_kernel_2_31, frozen_kernel_2_32, frozen_kernel_2_33, frozen_kernel_2_34, frozen_kernel_2_35, frozen_kernel_2_36, frozen_kernel_2_37, frozen_kernel_2_38, frozen_kernel_2_39, frozen_kernel_2_40, frozen_kernel_2_41, frozen_kernel_2_42, frozen_kernel_2_43, frozen_kernel_2_44, frozen_kernel_2_45, frozen_kernel_2_46, frozen_kernel_2_47, frozen_kernel_2_48, frozen_kernel_2_49, frozen_kernel_2_50, frozen_kernel_2_51, frozen_kernel_2_52, frozen_kernel_2_53, frozen_kernel_2_54, frozen_kernel_2_55, frozen_kernel_2_56, frozen_kernel_2_57, frozen_kernel_2_58, frozen_kernel_2_59, frozen_kernel_2_60, frozen_kernel_2_61, frozen_kernel_2_62, frozen_kernel_2_63]"

lift_definition frozen_kernel_3_0 :: frozen_binary32
  is "(0, 121, 2237673)" .

lift_definition frozen_kernel_3_1 :: frozen_binary32
  is "(0, 122, 1730686)" .

lift_definition frozen_kernel_3_2 :: frozen_binary32
  is "(1, 122, 564214)" .

lift_definition frozen_kernel_3_3 :: frozen_binary32
  is "(0, 119, 4466303)" .

lift_definition frozen_kernel_3_4 :: frozen_binary32
  is "(1, 121, 2046313)" .

lift_definition frozen_kernel_3_5 :: frozen_binary32
  is "(0, 117, 5168394)" .

lift_definition frozen_kernel_3_6 :: frozen_binary32
  is "(1, 121, 4355560)" .

lift_definition frozen_kernel_3_7 :: frozen_binary32
  is "(1, 120, 3556535)" .

lift_definition frozen_kernel_3_8 :: frozen_binary32
  is "(1, 122, 1414385)" .

lift_definition frozen_kernel_3_9 :: frozen_binary32
  is "(1, 121, 3068496)" .

lift_definition frozen_kernel_3_10 :: frozen_binary32
  is "(0, 123, 1698018)" .

lift_definition frozen_kernel_3_11 :: frozen_binary32
  is "(1, 120, 5926302)" .

lift_definition frozen_kernel_3_12 :: frozen_binary32
  is "(1, 122, 661867)" .

lift_definition frozen_kernel_3_13 :: frozen_binary32
  is "(1, 121, 709202)" .

lift_definition frozen_kernel_3_14 :: frozen_binary32
  is "(0, 121, 3288022)" .

lift_definition frozen_kernel_3_15 :: frozen_binary32
  is "(1, 120, 3825085)" .

lift_definition frozen_kernel_3_16 :: frozen_binary32
  is "(1, 119, 4575685)" .

lift_definition frozen_kernel_3_17 :: frozen_binary32
  is "(1, 122, 1292000)" .

lift_definition frozen_kernel_3_18 :: frozen_binary32
  is "(0, 121, 2041098)" .

lift_definition frozen_kernel_3_19 :: frozen_binary32
  is "(0, 122, 2582483)" .

lift_definition frozen_kernel_3_20 :: frozen_binary32
  is "(0, 120, 2023679)" .

lift_definition frozen_kernel_3_21 :: frozen_binary32
  is "(0, 122, 314724)" .

lift_definition frozen_kernel_3_22 :: frozen_binary32
  is "(0, 120, 5089812)" .

lift_definition frozen_kernel_3_23 :: frozen_binary32
  is "(1, 121, 5598946)" .

lift_definition frozen_kernel_3_24 :: frozen_binary32
  is "(1, 121, 4608895)" .

lift_definition frozen_kernel_3_25 :: frozen_binary32
  is "(1, 122, 3232530)" .

lift_definition frozen_kernel_3_26 :: frozen_binary32
  is "(0, 122, 42744)" .

lift_definition frozen_kernel_3_27 :: frozen_binary32
  is "(0, 120, 393216)" .

lift_definition frozen_kernel_3_28 :: frozen_binary32
  is "(1, 119, 2451464)" .

lift_definition frozen_kernel_3_29 :: frozen_binary32
  is "(1, 120, 1954746)" .

lift_definition frozen_kernel_3_30 :: frozen_binary32
  is "(1, 119, 4411950)" .

lift_definition frozen_kernel_3_31 :: frozen_binary32
  is "(0, 121, 2885279)" .

lift_definition frozen_kernel_3_32 :: frozen_binary32
  is "(0, 122, 6093189)" .

lift_definition frozen_kernel_3_33 :: frozen_binary32
  is "(0, 116, 4168535)" .

lift_definition frozen_kernel_3_34 :: frozen_binary32
  is "(1, 121, 3338891)" .

lift_definition frozen_kernel_3_35 :: frozen_binary32
  is "(0, 121, 4566420)" .

lift_definition frozen_kernel_3_36 :: frozen_binary32
  is "(0, 120, 134438)" .

lift_definition frozen_kernel_3_37 :: frozen_binary32
  is "(0, 120, 428045)" .

lift_definition frozen_kernel_3_38 :: frozen_binary32
  is "(1, 120, 6675360)" .

lift_definition frozen_kernel_3_39 :: frozen_binary32
  is "(1, 121, 4664291)" .

lift_definition frozen_kernel_3_40 :: frozen_binary32
  is "(1, 121, 4010639)" .

lift_definition frozen_kernel_3_41 :: frozen_binary32
  is "(0, 121, 2084347)" .

lift_definition frozen_kernel_3_42 :: frozen_binary32
  is "(0, 121, 4570792)" .

lift_definition frozen_kernel_3_43 :: frozen_binary32
  is "(1, 120, 571619)" .

lift_definition frozen_kernel_3_44 :: frozen_binary32
  is "(1, 122, 3250284)" .

lift_definition frozen_kernel_3_45 :: frozen_binary32
  is "(0, 120, 6473116)" .

lift_definition frozen_kernel_3_46 :: frozen_binary32
  is "(1, 122, 882056)" .

lift_definition frozen_kernel_3_47 :: frozen_binary32
  is "(0, 116, 3947291)" .

lift_definition frozen_kernel_3_48 :: frozen_binary32
  is "(1, 121, 768801)" .

lift_definition frozen_kernel_3_49 :: frozen_binary32
  is "(1, 120, 6358715)" .

lift_definition frozen_kernel_3_50 :: frozen_binary32
  is "(1, 121, 3906475)" .

lift_definition frozen_kernel_3_51 :: frozen_binary32
  is "(0, 122, 7483413)" .

lift_definition frozen_kernel_3_52 :: frozen_binary32
  is "(1, 120, 2850651)" .

lift_definition frozen_kernel_3_53 :: frozen_binary32
  is "(1, 120, 3331474)" .

lift_definition frozen_kernel_3_54 :: frozen_binary32
  is "(0, 122, 542369)" .

lift_definition frozen_kernel_3_55 :: frozen_binary32
  is "(1, 121, 6921374)" .

lift_definition frozen_kernel_3_56 :: frozen_binary32
  is "(1, 121, 5560085)" .

lift_definition frozen_kernel_3_57 :: frozen_binary32
  is "(0, 122, 6573013)" .

lift_definition frozen_kernel_3_58 :: frozen_binary32
  is "(1, 120, 1601165)" .

lift_definition frozen_kernel_3_59 :: frozen_binary32
  is "(0, 121, 982652)" .

lift_definition frozen_kernel_3_60 :: frozen_binary32
  is "(1, 122, 1454750)" .

lift_definition frozen_kernel_3_61 :: frozen_binary32
  is "(0, 118, 1145344)" .

lift_definition frozen_kernel_3_62 :: frozen_binary32
  is "(0, 122, 239121)" .

lift_definition frozen_kernel_3_63 :: frozen_binary32
  is "(1, 117, 4212317)" .

definition frozen_kernel_3 :: "frozen_binary32 vector" where
  "frozen_kernel_3 = [frozen_kernel_3_0, frozen_kernel_3_1, frozen_kernel_3_2, frozen_kernel_3_3, frozen_kernel_3_4, frozen_kernel_3_5, frozen_kernel_3_6, frozen_kernel_3_7, frozen_kernel_3_8, frozen_kernel_3_9, frozen_kernel_3_10, frozen_kernel_3_11, frozen_kernel_3_12, frozen_kernel_3_13, frozen_kernel_3_14, frozen_kernel_3_15, frozen_kernel_3_16, frozen_kernel_3_17, frozen_kernel_3_18, frozen_kernel_3_19, frozen_kernel_3_20, frozen_kernel_3_21, frozen_kernel_3_22, frozen_kernel_3_23, frozen_kernel_3_24, frozen_kernel_3_25, frozen_kernel_3_26, frozen_kernel_3_27, frozen_kernel_3_28, frozen_kernel_3_29, frozen_kernel_3_30, frozen_kernel_3_31, frozen_kernel_3_32, frozen_kernel_3_33, frozen_kernel_3_34, frozen_kernel_3_35, frozen_kernel_3_36, frozen_kernel_3_37, frozen_kernel_3_38, frozen_kernel_3_39, frozen_kernel_3_40, frozen_kernel_3_41, frozen_kernel_3_42, frozen_kernel_3_43, frozen_kernel_3_44, frozen_kernel_3_45, frozen_kernel_3_46, frozen_kernel_3_47, frozen_kernel_3_48, frozen_kernel_3_49, frozen_kernel_3_50, frozen_kernel_3_51, frozen_kernel_3_52, frozen_kernel_3_53, frozen_kernel_3_54, frozen_kernel_3_55, frozen_kernel_3_56, frozen_kernel_3_57, frozen_kernel_3_58, frozen_kernel_3_59, frozen_kernel_3_60, frozen_kernel_3_61, frozen_kernel_3_62, frozen_kernel_3_63]"

definition frozen_trace_kernels :: "frozen_binary32 vector list" where
  "frozen_trace_kernels = [frozen_kernel_0, frozen_kernel_1, frozen_kernel_2, frozen_kernel_3]"

definition frozen_trace_witnesses :: "frozen_binary32 vector list" where
  "frozen_trace_witnesses =
    map (ieee_fma_dot_tail_witnesses frozen_input_activation)
      frozen_trace_kernels"

lift_definition frozen_threshold_128 :: frozen_binary32
  is "(0, 134, 0)" .

lemma frozen_input_activation_0_finite:
  "IEEE.is_finite frozen_input_activation_0"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_0_small:
  "\<bar>IEEE.valof frozen_input_activation_0\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_1_finite:
  "IEEE.is_finite frozen_input_activation_1"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_1_small:
  "\<bar>IEEE.valof frozen_input_activation_1\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_2_finite:
  "IEEE.is_finite frozen_input_activation_2"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_2_small:
  "\<bar>IEEE.valof frozen_input_activation_2\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_3_finite:
  "IEEE.is_finite frozen_input_activation_3"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_3_small:
  "\<bar>IEEE.valof frozen_input_activation_3\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_4_finite:
  "IEEE.is_finite frozen_input_activation_4"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_4_small:
  "\<bar>IEEE.valof frozen_input_activation_4\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_5_finite:
  "IEEE.is_finite frozen_input_activation_5"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_5_small:
  "\<bar>IEEE.valof frozen_input_activation_5\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_6_finite:
  "IEEE.is_finite frozen_input_activation_6"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_6_small:
  "\<bar>IEEE.valof frozen_input_activation_6\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_7_finite:
  "IEEE.is_finite frozen_input_activation_7"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_7_small:
  "\<bar>IEEE.valof frozen_input_activation_7\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_8_finite:
  "IEEE.is_finite frozen_input_activation_8"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_8_small:
  "\<bar>IEEE.valof frozen_input_activation_8\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_9_finite:
  "IEEE.is_finite frozen_input_activation_9"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_9_small:
  "\<bar>IEEE.valof frozen_input_activation_9\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_10_finite:
  "IEEE.is_finite frozen_input_activation_10"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_10_small:
  "\<bar>IEEE.valof frozen_input_activation_10\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_11_finite:
  "IEEE.is_finite frozen_input_activation_11"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_11_small:
  "\<bar>IEEE.valof frozen_input_activation_11\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_12_finite:
  "IEEE.is_finite frozen_input_activation_12"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_12_small:
  "\<bar>IEEE.valof frozen_input_activation_12\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_13_finite:
  "IEEE.is_finite frozen_input_activation_13"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_13_small:
  "\<bar>IEEE.valof frozen_input_activation_13\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_14_finite:
  "IEEE.is_finite frozen_input_activation_14"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_14_small:
  "\<bar>IEEE.valof frozen_input_activation_14\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_15_finite:
  "IEEE.is_finite frozen_input_activation_15"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_15_small:
  "\<bar>IEEE.valof frozen_input_activation_15\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_16_finite:
  "IEEE.is_finite frozen_input_activation_16"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_16_small:
  "\<bar>IEEE.valof frozen_input_activation_16\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_17_finite:
  "IEEE.is_finite frozen_input_activation_17"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_17_small:
  "\<bar>IEEE.valof frozen_input_activation_17\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_18_finite:
  "IEEE.is_finite frozen_input_activation_18"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_18_small:
  "\<bar>IEEE.valof frozen_input_activation_18\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_19_finite:
  "IEEE.is_finite frozen_input_activation_19"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_19_small:
  "\<bar>IEEE.valof frozen_input_activation_19\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_20_finite:
  "IEEE.is_finite frozen_input_activation_20"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_20_small:
  "\<bar>IEEE.valof frozen_input_activation_20\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_21_finite:
  "IEEE.is_finite frozen_input_activation_21"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_21_small:
  "\<bar>IEEE.valof frozen_input_activation_21\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_22_finite:
  "IEEE.is_finite frozen_input_activation_22"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_22_small:
  "\<bar>IEEE.valof frozen_input_activation_22\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_23_finite:
  "IEEE.is_finite frozen_input_activation_23"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_23_small:
  "\<bar>IEEE.valof frozen_input_activation_23\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_24_finite:
  "IEEE.is_finite frozen_input_activation_24"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_24_small:
  "\<bar>IEEE.valof frozen_input_activation_24\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_25_finite:
  "IEEE.is_finite frozen_input_activation_25"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_25_small:
  "\<bar>IEEE.valof frozen_input_activation_25\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_26_finite:
  "IEEE.is_finite frozen_input_activation_26"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_26_small:
  "\<bar>IEEE.valof frozen_input_activation_26\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_27_finite:
  "IEEE.is_finite frozen_input_activation_27"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_27_small:
  "\<bar>IEEE.valof frozen_input_activation_27\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_28_finite:
  "IEEE.is_finite frozen_input_activation_28"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_28_small:
  "\<bar>IEEE.valof frozen_input_activation_28\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_29_finite:
  "IEEE.is_finite frozen_input_activation_29"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_29_small:
  "\<bar>IEEE.valof frozen_input_activation_29\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_30_finite:
  "IEEE.is_finite frozen_input_activation_30"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_30_small:
  "\<bar>IEEE.valof frozen_input_activation_30\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_31_finite:
  "IEEE.is_finite frozen_input_activation_31"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_31_small:
  "\<bar>IEEE.valof frozen_input_activation_31\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_32_finite:
  "IEEE.is_finite frozen_input_activation_32"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_32_small:
  "\<bar>IEEE.valof frozen_input_activation_32\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_33_finite:
  "IEEE.is_finite frozen_input_activation_33"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_33_small:
  "\<bar>IEEE.valof frozen_input_activation_33\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_34_finite:
  "IEEE.is_finite frozen_input_activation_34"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_34_small:
  "\<bar>IEEE.valof frozen_input_activation_34\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_35_finite:
  "IEEE.is_finite frozen_input_activation_35"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_35_small:
  "\<bar>IEEE.valof frozen_input_activation_35\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_36_finite:
  "IEEE.is_finite frozen_input_activation_36"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_36_small:
  "\<bar>IEEE.valof frozen_input_activation_36\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_37_finite:
  "IEEE.is_finite frozen_input_activation_37"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_37_small:
  "\<bar>IEEE.valof frozen_input_activation_37\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_38_finite:
  "IEEE.is_finite frozen_input_activation_38"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_38_small:
  "\<bar>IEEE.valof frozen_input_activation_38\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_39_finite:
  "IEEE.is_finite frozen_input_activation_39"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_39_small:
  "\<bar>IEEE.valof frozen_input_activation_39\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_40_finite:
  "IEEE.is_finite frozen_input_activation_40"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_40_small:
  "\<bar>IEEE.valof frozen_input_activation_40\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_41_finite:
  "IEEE.is_finite frozen_input_activation_41"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_41_small:
  "\<bar>IEEE.valof frozen_input_activation_41\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_42_finite:
  "IEEE.is_finite frozen_input_activation_42"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_42_small:
  "\<bar>IEEE.valof frozen_input_activation_42\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_43_finite:
  "IEEE.is_finite frozen_input_activation_43"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_43_small:
  "\<bar>IEEE.valof frozen_input_activation_43\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_44_finite:
  "IEEE.is_finite frozen_input_activation_44"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_44_small:
  "\<bar>IEEE.valof frozen_input_activation_44\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_45_finite:
  "IEEE.is_finite frozen_input_activation_45"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_45_small:
  "\<bar>IEEE.valof frozen_input_activation_45\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_46_finite:
  "IEEE.is_finite frozen_input_activation_46"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_46_small:
  "\<bar>IEEE.valof frozen_input_activation_46\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_47_finite:
  "IEEE.is_finite frozen_input_activation_47"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_47_small:
  "\<bar>IEEE.valof frozen_input_activation_47\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_48_finite:
  "IEEE.is_finite frozen_input_activation_48"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_48_small:
  "\<bar>IEEE.valof frozen_input_activation_48\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_49_finite:
  "IEEE.is_finite frozen_input_activation_49"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_49_small:
  "\<bar>IEEE.valof frozen_input_activation_49\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_50_finite:
  "IEEE.is_finite frozen_input_activation_50"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_50_small:
  "\<bar>IEEE.valof frozen_input_activation_50\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_51_finite:
  "IEEE.is_finite frozen_input_activation_51"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_51_small:
  "\<bar>IEEE.valof frozen_input_activation_51\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_52_finite:
  "IEEE.is_finite frozen_input_activation_52"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_52_small:
  "\<bar>IEEE.valof frozen_input_activation_52\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_53_finite:
  "IEEE.is_finite frozen_input_activation_53"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_53_small:
  "\<bar>IEEE.valof frozen_input_activation_53\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_54_finite:
  "IEEE.is_finite frozen_input_activation_54"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_54_small:
  "\<bar>IEEE.valof frozen_input_activation_54\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_55_finite:
  "IEEE.is_finite frozen_input_activation_55"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_55_small:
  "\<bar>IEEE.valof frozen_input_activation_55\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_56_finite:
  "IEEE.is_finite frozen_input_activation_56"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_56_small:
  "\<bar>IEEE.valof frozen_input_activation_56\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_57_finite:
  "IEEE.is_finite frozen_input_activation_57"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_57_small:
  "\<bar>IEEE.valof frozen_input_activation_57\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_58_finite:
  "IEEE.is_finite frozen_input_activation_58"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_58_small:
  "\<bar>IEEE.valof frozen_input_activation_58\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_59_finite:
  "IEEE.is_finite frozen_input_activation_59"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_59_small:
  "\<bar>IEEE.valof frozen_input_activation_59\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_60_finite:
  "IEEE.is_finite frozen_input_activation_60"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_60_small:
  "\<bar>IEEE.valof frozen_input_activation_60\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_61_finite:
  "IEEE.is_finite frozen_input_activation_61"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_61_small:
  "\<bar>IEEE.valof frozen_input_activation_61\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_62_finite:
  "IEEE.is_finite frozen_input_activation_62"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_62_small:
  "\<bar>IEEE.valof frozen_input_activation_62\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_activation_63_finite:
  "IEEE.is_finite frozen_input_activation_63"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_input_activation_63_small:
  "\<bar>IEEE.valof frozen_input_activation_63\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_0_finite:
  "IEEE.is_finite frozen_kernel_0_0"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_0_small:
  "\<bar>IEEE.valof frozen_kernel_0_0\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_1_finite:
  "IEEE.is_finite frozen_kernel_0_1"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_1_small:
  "\<bar>IEEE.valof frozen_kernel_0_1\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_2_finite:
  "IEEE.is_finite frozen_kernel_0_2"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_2_small:
  "\<bar>IEEE.valof frozen_kernel_0_2\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_3_finite:
  "IEEE.is_finite frozen_kernel_0_3"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_3_small:
  "\<bar>IEEE.valof frozen_kernel_0_3\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_4_finite:
  "IEEE.is_finite frozen_kernel_0_4"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_4_small:
  "\<bar>IEEE.valof frozen_kernel_0_4\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_5_finite:
  "IEEE.is_finite frozen_kernel_0_5"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_5_small:
  "\<bar>IEEE.valof frozen_kernel_0_5\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_6_finite:
  "IEEE.is_finite frozen_kernel_0_6"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_6_small:
  "\<bar>IEEE.valof frozen_kernel_0_6\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_7_finite:
  "IEEE.is_finite frozen_kernel_0_7"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_7_small:
  "\<bar>IEEE.valof frozen_kernel_0_7\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_8_finite:
  "IEEE.is_finite frozen_kernel_0_8"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_8_small:
  "\<bar>IEEE.valof frozen_kernel_0_8\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_9_finite:
  "IEEE.is_finite frozen_kernel_0_9"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_9_small:
  "\<bar>IEEE.valof frozen_kernel_0_9\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_10_finite:
  "IEEE.is_finite frozen_kernel_0_10"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_10_small:
  "\<bar>IEEE.valof frozen_kernel_0_10\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_11_finite:
  "IEEE.is_finite frozen_kernel_0_11"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_11_small:
  "\<bar>IEEE.valof frozen_kernel_0_11\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_12_finite:
  "IEEE.is_finite frozen_kernel_0_12"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_12_small:
  "\<bar>IEEE.valof frozen_kernel_0_12\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_13_finite:
  "IEEE.is_finite frozen_kernel_0_13"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_13_small:
  "\<bar>IEEE.valof frozen_kernel_0_13\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_14_finite:
  "IEEE.is_finite frozen_kernel_0_14"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_14_small:
  "\<bar>IEEE.valof frozen_kernel_0_14\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_15_finite:
  "IEEE.is_finite frozen_kernel_0_15"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_15_small:
  "\<bar>IEEE.valof frozen_kernel_0_15\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_16_finite:
  "IEEE.is_finite frozen_kernel_0_16"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_16_small:
  "\<bar>IEEE.valof frozen_kernel_0_16\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_17_finite:
  "IEEE.is_finite frozen_kernel_0_17"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_17_small:
  "\<bar>IEEE.valof frozen_kernel_0_17\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_18_finite:
  "IEEE.is_finite frozen_kernel_0_18"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_18_small:
  "\<bar>IEEE.valof frozen_kernel_0_18\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_19_finite:
  "IEEE.is_finite frozen_kernel_0_19"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_19_small:
  "\<bar>IEEE.valof frozen_kernel_0_19\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_20_finite:
  "IEEE.is_finite frozen_kernel_0_20"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_20_small:
  "\<bar>IEEE.valof frozen_kernel_0_20\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_21_finite:
  "IEEE.is_finite frozen_kernel_0_21"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_21_small:
  "\<bar>IEEE.valof frozen_kernel_0_21\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_22_finite:
  "IEEE.is_finite frozen_kernel_0_22"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_22_small:
  "\<bar>IEEE.valof frozen_kernel_0_22\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_23_finite:
  "IEEE.is_finite frozen_kernel_0_23"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_23_small:
  "\<bar>IEEE.valof frozen_kernel_0_23\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_24_finite:
  "IEEE.is_finite frozen_kernel_0_24"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_24_small:
  "\<bar>IEEE.valof frozen_kernel_0_24\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_25_finite:
  "IEEE.is_finite frozen_kernel_0_25"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_25_small:
  "\<bar>IEEE.valof frozen_kernel_0_25\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_26_finite:
  "IEEE.is_finite frozen_kernel_0_26"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_26_small:
  "\<bar>IEEE.valof frozen_kernel_0_26\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_27_finite:
  "IEEE.is_finite frozen_kernel_0_27"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_27_small:
  "\<bar>IEEE.valof frozen_kernel_0_27\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_28_finite:
  "IEEE.is_finite frozen_kernel_0_28"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_28_small:
  "\<bar>IEEE.valof frozen_kernel_0_28\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_29_finite:
  "IEEE.is_finite frozen_kernel_0_29"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_29_small:
  "\<bar>IEEE.valof frozen_kernel_0_29\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_30_finite:
  "IEEE.is_finite frozen_kernel_0_30"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_30_small:
  "\<bar>IEEE.valof frozen_kernel_0_30\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_31_finite:
  "IEEE.is_finite frozen_kernel_0_31"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_31_small:
  "\<bar>IEEE.valof frozen_kernel_0_31\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_32_finite:
  "IEEE.is_finite frozen_kernel_0_32"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_32_small:
  "\<bar>IEEE.valof frozen_kernel_0_32\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_33_finite:
  "IEEE.is_finite frozen_kernel_0_33"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_33_small:
  "\<bar>IEEE.valof frozen_kernel_0_33\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_34_finite:
  "IEEE.is_finite frozen_kernel_0_34"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_34_small:
  "\<bar>IEEE.valof frozen_kernel_0_34\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_35_finite:
  "IEEE.is_finite frozen_kernel_0_35"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_35_small:
  "\<bar>IEEE.valof frozen_kernel_0_35\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_36_finite:
  "IEEE.is_finite frozen_kernel_0_36"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_36_small:
  "\<bar>IEEE.valof frozen_kernel_0_36\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_37_finite:
  "IEEE.is_finite frozen_kernel_0_37"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_37_small:
  "\<bar>IEEE.valof frozen_kernel_0_37\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_38_finite:
  "IEEE.is_finite frozen_kernel_0_38"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_38_small:
  "\<bar>IEEE.valof frozen_kernel_0_38\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_39_finite:
  "IEEE.is_finite frozen_kernel_0_39"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_39_small:
  "\<bar>IEEE.valof frozen_kernel_0_39\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_40_finite:
  "IEEE.is_finite frozen_kernel_0_40"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_40_small:
  "\<bar>IEEE.valof frozen_kernel_0_40\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_41_finite:
  "IEEE.is_finite frozen_kernel_0_41"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_41_small:
  "\<bar>IEEE.valof frozen_kernel_0_41\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_42_finite:
  "IEEE.is_finite frozen_kernel_0_42"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_42_small:
  "\<bar>IEEE.valof frozen_kernel_0_42\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_43_finite:
  "IEEE.is_finite frozen_kernel_0_43"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_43_small:
  "\<bar>IEEE.valof frozen_kernel_0_43\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_44_finite:
  "IEEE.is_finite frozen_kernel_0_44"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_44_small:
  "\<bar>IEEE.valof frozen_kernel_0_44\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_45_finite:
  "IEEE.is_finite frozen_kernel_0_45"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_45_small:
  "\<bar>IEEE.valof frozen_kernel_0_45\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_46_finite:
  "IEEE.is_finite frozen_kernel_0_46"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_46_small:
  "\<bar>IEEE.valof frozen_kernel_0_46\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_47_finite:
  "IEEE.is_finite frozen_kernel_0_47"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_47_small:
  "\<bar>IEEE.valof frozen_kernel_0_47\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_48_finite:
  "IEEE.is_finite frozen_kernel_0_48"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_48_small:
  "\<bar>IEEE.valof frozen_kernel_0_48\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_49_finite:
  "IEEE.is_finite frozen_kernel_0_49"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_49_small:
  "\<bar>IEEE.valof frozen_kernel_0_49\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_50_finite:
  "IEEE.is_finite frozen_kernel_0_50"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_50_small:
  "\<bar>IEEE.valof frozen_kernel_0_50\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_51_finite:
  "IEEE.is_finite frozen_kernel_0_51"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_51_small:
  "\<bar>IEEE.valof frozen_kernel_0_51\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_52_finite:
  "IEEE.is_finite frozen_kernel_0_52"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_52_small:
  "\<bar>IEEE.valof frozen_kernel_0_52\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_53_finite:
  "IEEE.is_finite frozen_kernel_0_53"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_53_small:
  "\<bar>IEEE.valof frozen_kernel_0_53\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_54_finite:
  "IEEE.is_finite frozen_kernel_0_54"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_54_small:
  "\<bar>IEEE.valof frozen_kernel_0_54\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_55_finite:
  "IEEE.is_finite frozen_kernel_0_55"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_55_small:
  "\<bar>IEEE.valof frozen_kernel_0_55\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_56_finite:
  "IEEE.is_finite frozen_kernel_0_56"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_56_small:
  "\<bar>IEEE.valof frozen_kernel_0_56\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_57_finite:
  "IEEE.is_finite frozen_kernel_0_57"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_57_small:
  "\<bar>IEEE.valof frozen_kernel_0_57\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_58_finite:
  "IEEE.is_finite frozen_kernel_0_58"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_58_small:
  "\<bar>IEEE.valof frozen_kernel_0_58\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_59_finite:
  "IEEE.is_finite frozen_kernel_0_59"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_59_small:
  "\<bar>IEEE.valof frozen_kernel_0_59\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_60_finite:
  "IEEE.is_finite frozen_kernel_0_60"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_60_small:
  "\<bar>IEEE.valof frozen_kernel_0_60\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_61_finite:
  "IEEE.is_finite frozen_kernel_0_61"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_61_small:
  "\<bar>IEEE.valof frozen_kernel_0_61\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_62_finite:
  "IEEE.is_finite frozen_kernel_0_62"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_62_small:
  "\<bar>IEEE.valof frozen_kernel_0_62\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_0_63_finite:
  "IEEE.is_finite frozen_kernel_0_63"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_0_63_small:
  "\<bar>IEEE.valof frozen_kernel_0_63\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_0_finite:
  "IEEE.is_finite frozen_kernel_1_0"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_0_small:
  "\<bar>IEEE.valof frozen_kernel_1_0\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_1_finite:
  "IEEE.is_finite frozen_kernel_1_1"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_1_small:
  "\<bar>IEEE.valof frozen_kernel_1_1\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_2_finite:
  "IEEE.is_finite frozen_kernel_1_2"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_2_small:
  "\<bar>IEEE.valof frozen_kernel_1_2\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_3_finite:
  "IEEE.is_finite frozen_kernel_1_3"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_3_small:
  "\<bar>IEEE.valof frozen_kernel_1_3\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_4_finite:
  "IEEE.is_finite frozen_kernel_1_4"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_4_small:
  "\<bar>IEEE.valof frozen_kernel_1_4\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_5_finite:
  "IEEE.is_finite frozen_kernel_1_5"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_5_small:
  "\<bar>IEEE.valof frozen_kernel_1_5\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_6_finite:
  "IEEE.is_finite frozen_kernel_1_6"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_6_small:
  "\<bar>IEEE.valof frozen_kernel_1_6\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_7_finite:
  "IEEE.is_finite frozen_kernel_1_7"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_7_small:
  "\<bar>IEEE.valof frozen_kernel_1_7\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_8_finite:
  "IEEE.is_finite frozen_kernel_1_8"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_8_small:
  "\<bar>IEEE.valof frozen_kernel_1_8\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_9_finite:
  "IEEE.is_finite frozen_kernel_1_9"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_9_small:
  "\<bar>IEEE.valof frozen_kernel_1_9\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_10_finite:
  "IEEE.is_finite frozen_kernel_1_10"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_10_small:
  "\<bar>IEEE.valof frozen_kernel_1_10\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_11_finite:
  "IEEE.is_finite frozen_kernel_1_11"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_11_small:
  "\<bar>IEEE.valof frozen_kernel_1_11\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_12_finite:
  "IEEE.is_finite frozen_kernel_1_12"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_12_small:
  "\<bar>IEEE.valof frozen_kernel_1_12\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_13_finite:
  "IEEE.is_finite frozen_kernel_1_13"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_13_small:
  "\<bar>IEEE.valof frozen_kernel_1_13\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_14_finite:
  "IEEE.is_finite frozen_kernel_1_14"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_14_small:
  "\<bar>IEEE.valof frozen_kernel_1_14\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_15_finite:
  "IEEE.is_finite frozen_kernel_1_15"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_15_small:
  "\<bar>IEEE.valof frozen_kernel_1_15\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_16_finite:
  "IEEE.is_finite frozen_kernel_1_16"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_16_small:
  "\<bar>IEEE.valof frozen_kernel_1_16\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_17_finite:
  "IEEE.is_finite frozen_kernel_1_17"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_17_small:
  "\<bar>IEEE.valof frozen_kernel_1_17\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_18_finite:
  "IEEE.is_finite frozen_kernel_1_18"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_18_small:
  "\<bar>IEEE.valof frozen_kernel_1_18\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_19_finite:
  "IEEE.is_finite frozen_kernel_1_19"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_19_small:
  "\<bar>IEEE.valof frozen_kernel_1_19\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_20_finite:
  "IEEE.is_finite frozen_kernel_1_20"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_20_small:
  "\<bar>IEEE.valof frozen_kernel_1_20\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_21_finite:
  "IEEE.is_finite frozen_kernel_1_21"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_21_small:
  "\<bar>IEEE.valof frozen_kernel_1_21\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_22_finite:
  "IEEE.is_finite frozen_kernel_1_22"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_22_small:
  "\<bar>IEEE.valof frozen_kernel_1_22\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_23_finite:
  "IEEE.is_finite frozen_kernel_1_23"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_23_small:
  "\<bar>IEEE.valof frozen_kernel_1_23\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_24_finite:
  "IEEE.is_finite frozen_kernel_1_24"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_24_small:
  "\<bar>IEEE.valof frozen_kernel_1_24\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_25_finite:
  "IEEE.is_finite frozen_kernel_1_25"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_25_small:
  "\<bar>IEEE.valof frozen_kernel_1_25\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_26_finite:
  "IEEE.is_finite frozen_kernel_1_26"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_26_small:
  "\<bar>IEEE.valof frozen_kernel_1_26\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_27_finite:
  "IEEE.is_finite frozen_kernel_1_27"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_27_small:
  "\<bar>IEEE.valof frozen_kernel_1_27\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_28_finite:
  "IEEE.is_finite frozen_kernel_1_28"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_28_small:
  "\<bar>IEEE.valof frozen_kernel_1_28\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_29_finite:
  "IEEE.is_finite frozen_kernel_1_29"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_29_small:
  "\<bar>IEEE.valof frozen_kernel_1_29\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_30_finite:
  "IEEE.is_finite frozen_kernel_1_30"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_30_small:
  "\<bar>IEEE.valof frozen_kernel_1_30\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_31_finite:
  "IEEE.is_finite frozen_kernel_1_31"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_31_small:
  "\<bar>IEEE.valof frozen_kernel_1_31\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_32_finite:
  "IEEE.is_finite frozen_kernel_1_32"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_32_small:
  "\<bar>IEEE.valof frozen_kernel_1_32\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_33_finite:
  "IEEE.is_finite frozen_kernel_1_33"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_33_small:
  "\<bar>IEEE.valof frozen_kernel_1_33\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_34_finite:
  "IEEE.is_finite frozen_kernel_1_34"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_34_small:
  "\<bar>IEEE.valof frozen_kernel_1_34\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_35_finite:
  "IEEE.is_finite frozen_kernel_1_35"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_35_small:
  "\<bar>IEEE.valof frozen_kernel_1_35\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_36_finite:
  "IEEE.is_finite frozen_kernel_1_36"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_36_small:
  "\<bar>IEEE.valof frozen_kernel_1_36\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_37_finite:
  "IEEE.is_finite frozen_kernel_1_37"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_37_small:
  "\<bar>IEEE.valof frozen_kernel_1_37\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_38_finite:
  "IEEE.is_finite frozen_kernel_1_38"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_38_small:
  "\<bar>IEEE.valof frozen_kernel_1_38\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_39_finite:
  "IEEE.is_finite frozen_kernel_1_39"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_39_small:
  "\<bar>IEEE.valof frozen_kernel_1_39\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_40_finite:
  "IEEE.is_finite frozen_kernel_1_40"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_40_small:
  "\<bar>IEEE.valof frozen_kernel_1_40\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_41_finite:
  "IEEE.is_finite frozen_kernel_1_41"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_41_small:
  "\<bar>IEEE.valof frozen_kernel_1_41\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_42_finite:
  "IEEE.is_finite frozen_kernel_1_42"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_42_small:
  "\<bar>IEEE.valof frozen_kernel_1_42\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_43_finite:
  "IEEE.is_finite frozen_kernel_1_43"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_43_small:
  "\<bar>IEEE.valof frozen_kernel_1_43\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_44_finite:
  "IEEE.is_finite frozen_kernel_1_44"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_44_small:
  "\<bar>IEEE.valof frozen_kernel_1_44\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_45_finite:
  "IEEE.is_finite frozen_kernel_1_45"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_45_small:
  "\<bar>IEEE.valof frozen_kernel_1_45\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_46_finite:
  "IEEE.is_finite frozen_kernel_1_46"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_46_small:
  "\<bar>IEEE.valof frozen_kernel_1_46\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_47_finite:
  "IEEE.is_finite frozen_kernel_1_47"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_47_small:
  "\<bar>IEEE.valof frozen_kernel_1_47\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_48_finite:
  "IEEE.is_finite frozen_kernel_1_48"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_48_small:
  "\<bar>IEEE.valof frozen_kernel_1_48\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_49_finite:
  "IEEE.is_finite frozen_kernel_1_49"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_49_small:
  "\<bar>IEEE.valof frozen_kernel_1_49\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_50_finite:
  "IEEE.is_finite frozen_kernel_1_50"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_50_small:
  "\<bar>IEEE.valof frozen_kernel_1_50\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_51_finite:
  "IEEE.is_finite frozen_kernel_1_51"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_51_small:
  "\<bar>IEEE.valof frozen_kernel_1_51\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_52_finite:
  "IEEE.is_finite frozen_kernel_1_52"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_52_small:
  "\<bar>IEEE.valof frozen_kernel_1_52\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_53_finite:
  "IEEE.is_finite frozen_kernel_1_53"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_53_small:
  "\<bar>IEEE.valof frozen_kernel_1_53\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_54_finite:
  "IEEE.is_finite frozen_kernel_1_54"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_54_small:
  "\<bar>IEEE.valof frozen_kernel_1_54\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_55_finite:
  "IEEE.is_finite frozen_kernel_1_55"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_55_small:
  "\<bar>IEEE.valof frozen_kernel_1_55\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_56_finite:
  "IEEE.is_finite frozen_kernel_1_56"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_56_small:
  "\<bar>IEEE.valof frozen_kernel_1_56\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_57_finite:
  "IEEE.is_finite frozen_kernel_1_57"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_57_small:
  "\<bar>IEEE.valof frozen_kernel_1_57\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_58_finite:
  "IEEE.is_finite frozen_kernel_1_58"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_58_small:
  "\<bar>IEEE.valof frozen_kernel_1_58\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_59_finite:
  "IEEE.is_finite frozen_kernel_1_59"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_59_small:
  "\<bar>IEEE.valof frozen_kernel_1_59\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_60_finite:
  "IEEE.is_finite frozen_kernel_1_60"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_60_small:
  "\<bar>IEEE.valof frozen_kernel_1_60\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_61_finite:
  "IEEE.is_finite frozen_kernel_1_61"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_61_small:
  "\<bar>IEEE.valof frozen_kernel_1_61\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_62_finite:
  "IEEE.is_finite frozen_kernel_1_62"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_62_small:
  "\<bar>IEEE.valof frozen_kernel_1_62\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_1_63_finite:
  "IEEE.is_finite frozen_kernel_1_63"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_1_63_small:
  "\<bar>IEEE.valof frozen_kernel_1_63\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_0_finite:
  "IEEE.is_finite frozen_kernel_2_0"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_0_small:
  "\<bar>IEEE.valof frozen_kernel_2_0\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_1_finite:
  "IEEE.is_finite frozen_kernel_2_1"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_1_small:
  "\<bar>IEEE.valof frozen_kernel_2_1\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_2_finite:
  "IEEE.is_finite frozen_kernel_2_2"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_2_small:
  "\<bar>IEEE.valof frozen_kernel_2_2\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_3_finite:
  "IEEE.is_finite frozen_kernel_2_3"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_3_small:
  "\<bar>IEEE.valof frozen_kernel_2_3\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_4_finite:
  "IEEE.is_finite frozen_kernel_2_4"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_4_small:
  "\<bar>IEEE.valof frozen_kernel_2_4\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_5_finite:
  "IEEE.is_finite frozen_kernel_2_5"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_5_small:
  "\<bar>IEEE.valof frozen_kernel_2_5\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_6_finite:
  "IEEE.is_finite frozen_kernel_2_6"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_6_small:
  "\<bar>IEEE.valof frozen_kernel_2_6\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_7_finite:
  "IEEE.is_finite frozen_kernel_2_7"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_7_small:
  "\<bar>IEEE.valof frozen_kernel_2_7\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_8_finite:
  "IEEE.is_finite frozen_kernel_2_8"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_8_small:
  "\<bar>IEEE.valof frozen_kernel_2_8\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_9_finite:
  "IEEE.is_finite frozen_kernel_2_9"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_9_small:
  "\<bar>IEEE.valof frozen_kernel_2_9\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_10_finite:
  "IEEE.is_finite frozen_kernel_2_10"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_10_small:
  "\<bar>IEEE.valof frozen_kernel_2_10\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_11_finite:
  "IEEE.is_finite frozen_kernel_2_11"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_11_small:
  "\<bar>IEEE.valof frozen_kernel_2_11\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_12_finite:
  "IEEE.is_finite frozen_kernel_2_12"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_12_small:
  "\<bar>IEEE.valof frozen_kernel_2_12\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_13_finite:
  "IEEE.is_finite frozen_kernel_2_13"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_13_small:
  "\<bar>IEEE.valof frozen_kernel_2_13\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_14_finite:
  "IEEE.is_finite frozen_kernel_2_14"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_14_small:
  "\<bar>IEEE.valof frozen_kernel_2_14\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_15_finite:
  "IEEE.is_finite frozen_kernel_2_15"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_15_small:
  "\<bar>IEEE.valof frozen_kernel_2_15\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_16_finite:
  "IEEE.is_finite frozen_kernel_2_16"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_16_small:
  "\<bar>IEEE.valof frozen_kernel_2_16\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_17_finite:
  "IEEE.is_finite frozen_kernel_2_17"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_17_small:
  "\<bar>IEEE.valof frozen_kernel_2_17\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_18_finite:
  "IEEE.is_finite frozen_kernel_2_18"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_18_small:
  "\<bar>IEEE.valof frozen_kernel_2_18\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_19_finite:
  "IEEE.is_finite frozen_kernel_2_19"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_19_small:
  "\<bar>IEEE.valof frozen_kernel_2_19\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_20_finite:
  "IEEE.is_finite frozen_kernel_2_20"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_20_small:
  "\<bar>IEEE.valof frozen_kernel_2_20\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_21_finite:
  "IEEE.is_finite frozen_kernel_2_21"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_21_small:
  "\<bar>IEEE.valof frozen_kernel_2_21\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_22_finite:
  "IEEE.is_finite frozen_kernel_2_22"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_22_small:
  "\<bar>IEEE.valof frozen_kernel_2_22\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_23_finite:
  "IEEE.is_finite frozen_kernel_2_23"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_23_small:
  "\<bar>IEEE.valof frozen_kernel_2_23\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_24_finite:
  "IEEE.is_finite frozen_kernel_2_24"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_24_small:
  "\<bar>IEEE.valof frozen_kernel_2_24\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_25_finite:
  "IEEE.is_finite frozen_kernel_2_25"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_25_small:
  "\<bar>IEEE.valof frozen_kernel_2_25\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_26_finite:
  "IEEE.is_finite frozen_kernel_2_26"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_26_small:
  "\<bar>IEEE.valof frozen_kernel_2_26\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_27_finite:
  "IEEE.is_finite frozen_kernel_2_27"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_27_small:
  "\<bar>IEEE.valof frozen_kernel_2_27\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_28_finite:
  "IEEE.is_finite frozen_kernel_2_28"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_28_small:
  "\<bar>IEEE.valof frozen_kernel_2_28\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_29_finite:
  "IEEE.is_finite frozen_kernel_2_29"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_29_small:
  "\<bar>IEEE.valof frozen_kernel_2_29\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_30_finite:
  "IEEE.is_finite frozen_kernel_2_30"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_30_small:
  "\<bar>IEEE.valof frozen_kernel_2_30\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_31_finite:
  "IEEE.is_finite frozen_kernel_2_31"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_31_small:
  "\<bar>IEEE.valof frozen_kernel_2_31\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_32_finite:
  "IEEE.is_finite frozen_kernel_2_32"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_32_small:
  "\<bar>IEEE.valof frozen_kernel_2_32\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_33_finite:
  "IEEE.is_finite frozen_kernel_2_33"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_33_small:
  "\<bar>IEEE.valof frozen_kernel_2_33\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_34_finite:
  "IEEE.is_finite frozen_kernel_2_34"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_34_small:
  "\<bar>IEEE.valof frozen_kernel_2_34\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_35_finite:
  "IEEE.is_finite frozen_kernel_2_35"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_35_small:
  "\<bar>IEEE.valof frozen_kernel_2_35\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_36_finite:
  "IEEE.is_finite frozen_kernel_2_36"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_36_small:
  "\<bar>IEEE.valof frozen_kernel_2_36\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_37_finite:
  "IEEE.is_finite frozen_kernel_2_37"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_37_small:
  "\<bar>IEEE.valof frozen_kernel_2_37\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_38_finite:
  "IEEE.is_finite frozen_kernel_2_38"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_38_small:
  "\<bar>IEEE.valof frozen_kernel_2_38\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_39_finite:
  "IEEE.is_finite frozen_kernel_2_39"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_39_small:
  "\<bar>IEEE.valof frozen_kernel_2_39\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_40_finite:
  "IEEE.is_finite frozen_kernel_2_40"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_40_small:
  "\<bar>IEEE.valof frozen_kernel_2_40\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_41_finite:
  "IEEE.is_finite frozen_kernel_2_41"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_41_small:
  "\<bar>IEEE.valof frozen_kernel_2_41\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_42_finite:
  "IEEE.is_finite frozen_kernel_2_42"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_42_small:
  "\<bar>IEEE.valof frozen_kernel_2_42\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_43_finite:
  "IEEE.is_finite frozen_kernel_2_43"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_43_small:
  "\<bar>IEEE.valof frozen_kernel_2_43\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_44_finite:
  "IEEE.is_finite frozen_kernel_2_44"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_44_small:
  "\<bar>IEEE.valof frozen_kernel_2_44\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_45_finite:
  "IEEE.is_finite frozen_kernel_2_45"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_45_small:
  "\<bar>IEEE.valof frozen_kernel_2_45\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_46_finite:
  "IEEE.is_finite frozen_kernel_2_46"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_46_small:
  "\<bar>IEEE.valof frozen_kernel_2_46\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_47_finite:
  "IEEE.is_finite frozen_kernel_2_47"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_47_small:
  "\<bar>IEEE.valof frozen_kernel_2_47\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_48_finite:
  "IEEE.is_finite frozen_kernel_2_48"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_48_small:
  "\<bar>IEEE.valof frozen_kernel_2_48\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_49_finite:
  "IEEE.is_finite frozen_kernel_2_49"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_49_small:
  "\<bar>IEEE.valof frozen_kernel_2_49\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_50_finite:
  "IEEE.is_finite frozen_kernel_2_50"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_50_small:
  "\<bar>IEEE.valof frozen_kernel_2_50\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_51_finite:
  "IEEE.is_finite frozen_kernel_2_51"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_51_small:
  "\<bar>IEEE.valof frozen_kernel_2_51\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_52_finite:
  "IEEE.is_finite frozen_kernel_2_52"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_52_small:
  "\<bar>IEEE.valof frozen_kernel_2_52\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_53_finite:
  "IEEE.is_finite frozen_kernel_2_53"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_53_small:
  "\<bar>IEEE.valof frozen_kernel_2_53\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_54_finite:
  "IEEE.is_finite frozen_kernel_2_54"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_54_small:
  "\<bar>IEEE.valof frozen_kernel_2_54\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_55_finite:
  "IEEE.is_finite frozen_kernel_2_55"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_55_small:
  "\<bar>IEEE.valof frozen_kernel_2_55\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_56_finite:
  "IEEE.is_finite frozen_kernel_2_56"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_56_small:
  "\<bar>IEEE.valof frozen_kernel_2_56\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_57_finite:
  "IEEE.is_finite frozen_kernel_2_57"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_57_small:
  "\<bar>IEEE.valof frozen_kernel_2_57\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_58_finite:
  "IEEE.is_finite frozen_kernel_2_58"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_58_small:
  "\<bar>IEEE.valof frozen_kernel_2_58\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_59_finite:
  "IEEE.is_finite frozen_kernel_2_59"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_59_small:
  "\<bar>IEEE.valof frozen_kernel_2_59\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_60_finite:
  "IEEE.is_finite frozen_kernel_2_60"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_60_small:
  "\<bar>IEEE.valof frozen_kernel_2_60\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_61_finite:
  "IEEE.is_finite frozen_kernel_2_61"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_61_small:
  "\<bar>IEEE.valof frozen_kernel_2_61\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_62_finite:
  "IEEE.is_finite frozen_kernel_2_62"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_62_small:
  "\<bar>IEEE.valof frozen_kernel_2_62\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_2_63_finite:
  "IEEE.is_finite frozen_kernel_2_63"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_2_63_small:
  "\<bar>IEEE.valof frozen_kernel_2_63\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_0_finite:
  "IEEE.is_finite frozen_kernel_3_0"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_0_small:
  "\<bar>IEEE.valof frozen_kernel_3_0\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_1_finite:
  "IEEE.is_finite frozen_kernel_3_1"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_1_small:
  "\<bar>IEEE.valof frozen_kernel_3_1\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_2_finite:
  "IEEE.is_finite frozen_kernel_3_2"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_2_small:
  "\<bar>IEEE.valof frozen_kernel_3_2\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_3_finite:
  "IEEE.is_finite frozen_kernel_3_3"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_3_small:
  "\<bar>IEEE.valof frozen_kernel_3_3\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_4_finite:
  "IEEE.is_finite frozen_kernel_3_4"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_4_small:
  "\<bar>IEEE.valof frozen_kernel_3_4\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_5_finite:
  "IEEE.is_finite frozen_kernel_3_5"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_5_small:
  "\<bar>IEEE.valof frozen_kernel_3_5\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_6_finite:
  "IEEE.is_finite frozen_kernel_3_6"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_6_small:
  "\<bar>IEEE.valof frozen_kernel_3_6\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_7_finite:
  "IEEE.is_finite frozen_kernel_3_7"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_7_small:
  "\<bar>IEEE.valof frozen_kernel_3_7\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_8_finite:
  "IEEE.is_finite frozen_kernel_3_8"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_8_small:
  "\<bar>IEEE.valof frozen_kernel_3_8\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_9_finite:
  "IEEE.is_finite frozen_kernel_3_9"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_9_small:
  "\<bar>IEEE.valof frozen_kernel_3_9\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_10_finite:
  "IEEE.is_finite frozen_kernel_3_10"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_10_small:
  "\<bar>IEEE.valof frozen_kernel_3_10\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_11_finite:
  "IEEE.is_finite frozen_kernel_3_11"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_11_small:
  "\<bar>IEEE.valof frozen_kernel_3_11\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_12_finite:
  "IEEE.is_finite frozen_kernel_3_12"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_12_small:
  "\<bar>IEEE.valof frozen_kernel_3_12\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_13_finite:
  "IEEE.is_finite frozen_kernel_3_13"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_13_small:
  "\<bar>IEEE.valof frozen_kernel_3_13\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_14_finite:
  "IEEE.is_finite frozen_kernel_3_14"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_14_small:
  "\<bar>IEEE.valof frozen_kernel_3_14\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_15_finite:
  "IEEE.is_finite frozen_kernel_3_15"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_15_small:
  "\<bar>IEEE.valof frozen_kernel_3_15\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_16_finite:
  "IEEE.is_finite frozen_kernel_3_16"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_16_small:
  "\<bar>IEEE.valof frozen_kernel_3_16\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_17_finite:
  "IEEE.is_finite frozen_kernel_3_17"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_17_small:
  "\<bar>IEEE.valof frozen_kernel_3_17\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_18_finite:
  "IEEE.is_finite frozen_kernel_3_18"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_18_small:
  "\<bar>IEEE.valof frozen_kernel_3_18\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_19_finite:
  "IEEE.is_finite frozen_kernel_3_19"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_19_small:
  "\<bar>IEEE.valof frozen_kernel_3_19\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_20_finite:
  "IEEE.is_finite frozen_kernel_3_20"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_20_small:
  "\<bar>IEEE.valof frozen_kernel_3_20\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_21_finite:
  "IEEE.is_finite frozen_kernel_3_21"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_21_small:
  "\<bar>IEEE.valof frozen_kernel_3_21\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_22_finite:
  "IEEE.is_finite frozen_kernel_3_22"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_22_small:
  "\<bar>IEEE.valof frozen_kernel_3_22\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_23_finite:
  "IEEE.is_finite frozen_kernel_3_23"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_23_small:
  "\<bar>IEEE.valof frozen_kernel_3_23\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_24_finite:
  "IEEE.is_finite frozen_kernel_3_24"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_24_small:
  "\<bar>IEEE.valof frozen_kernel_3_24\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_25_finite:
  "IEEE.is_finite frozen_kernel_3_25"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_25_small:
  "\<bar>IEEE.valof frozen_kernel_3_25\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_26_finite:
  "IEEE.is_finite frozen_kernel_3_26"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_26_small:
  "\<bar>IEEE.valof frozen_kernel_3_26\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_27_finite:
  "IEEE.is_finite frozen_kernel_3_27"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_27_small:
  "\<bar>IEEE.valof frozen_kernel_3_27\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_28_finite:
  "IEEE.is_finite frozen_kernel_3_28"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_28_small:
  "\<bar>IEEE.valof frozen_kernel_3_28\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_29_finite:
  "IEEE.is_finite frozen_kernel_3_29"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_29_small:
  "\<bar>IEEE.valof frozen_kernel_3_29\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_30_finite:
  "IEEE.is_finite frozen_kernel_3_30"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_30_small:
  "\<bar>IEEE.valof frozen_kernel_3_30\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_31_finite:
  "IEEE.is_finite frozen_kernel_3_31"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_31_small:
  "\<bar>IEEE.valof frozen_kernel_3_31\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_32_finite:
  "IEEE.is_finite frozen_kernel_3_32"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_32_small:
  "\<bar>IEEE.valof frozen_kernel_3_32\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_33_finite:
  "IEEE.is_finite frozen_kernel_3_33"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_33_small:
  "\<bar>IEEE.valof frozen_kernel_3_33\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_34_finite:
  "IEEE.is_finite frozen_kernel_3_34"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_34_small:
  "\<bar>IEEE.valof frozen_kernel_3_34\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_35_finite:
  "IEEE.is_finite frozen_kernel_3_35"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_35_small:
  "\<bar>IEEE.valof frozen_kernel_3_35\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_36_finite:
  "IEEE.is_finite frozen_kernel_3_36"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_36_small:
  "\<bar>IEEE.valof frozen_kernel_3_36\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_37_finite:
  "IEEE.is_finite frozen_kernel_3_37"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_37_small:
  "\<bar>IEEE.valof frozen_kernel_3_37\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_38_finite:
  "IEEE.is_finite frozen_kernel_3_38"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_38_small:
  "\<bar>IEEE.valof frozen_kernel_3_38\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_39_finite:
  "IEEE.is_finite frozen_kernel_3_39"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_39_small:
  "\<bar>IEEE.valof frozen_kernel_3_39\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_40_finite:
  "IEEE.is_finite frozen_kernel_3_40"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_40_small:
  "\<bar>IEEE.valof frozen_kernel_3_40\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_41_finite:
  "IEEE.is_finite frozen_kernel_3_41"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_41_small:
  "\<bar>IEEE.valof frozen_kernel_3_41\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_42_finite:
  "IEEE.is_finite frozen_kernel_3_42"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_42_small:
  "\<bar>IEEE.valof frozen_kernel_3_42\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_43_finite:
  "IEEE.is_finite frozen_kernel_3_43"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_43_small:
  "\<bar>IEEE.valof frozen_kernel_3_43\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_44_finite:
  "IEEE.is_finite frozen_kernel_3_44"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_44_small:
  "\<bar>IEEE.valof frozen_kernel_3_44\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_45_finite:
  "IEEE.is_finite frozen_kernel_3_45"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_45_small:
  "\<bar>IEEE.valof frozen_kernel_3_45\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_46_finite:
  "IEEE.is_finite frozen_kernel_3_46"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_46_small:
  "\<bar>IEEE.valof frozen_kernel_3_46\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_47_finite:
  "IEEE.is_finite frozen_kernel_3_47"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_47_small:
  "\<bar>IEEE.valof frozen_kernel_3_47\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_48_finite:
  "IEEE.is_finite frozen_kernel_3_48"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_48_small:
  "\<bar>IEEE.valof frozen_kernel_3_48\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_49_finite:
  "IEEE.is_finite frozen_kernel_3_49"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_49_small:
  "\<bar>IEEE.valof frozen_kernel_3_49\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_50_finite:
  "IEEE.is_finite frozen_kernel_3_50"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_50_small:
  "\<bar>IEEE.valof frozen_kernel_3_50\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_51_finite:
  "IEEE.is_finite frozen_kernel_3_51"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_51_small:
  "\<bar>IEEE.valof frozen_kernel_3_51\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_52_finite:
  "IEEE.is_finite frozen_kernel_3_52"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_52_small:
  "\<bar>IEEE.valof frozen_kernel_3_52\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_53_finite:
  "IEEE.is_finite frozen_kernel_3_53"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_53_small:
  "\<bar>IEEE.valof frozen_kernel_3_53\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_54_finite:
  "IEEE.is_finite frozen_kernel_3_54"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_54_small:
  "\<bar>IEEE.valof frozen_kernel_3_54\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_55_finite:
  "IEEE.is_finite frozen_kernel_3_55"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_55_small:
  "\<bar>IEEE.valof frozen_kernel_3_55\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_56_finite:
  "IEEE.is_finite frozen_kernel_3_56"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_56_small:
  "\<bar>IEEE.valof frozen_kernel_3_56\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_57_finite:
  "IEEE.is_finite frozen_kernel_3_57"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_57_small:
  "\<bar>IEEE.valof frozen_kernel_3_57\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_58_finite:
  "IEEE.is_finite frozen_kernel_3_58"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_58_small:
  "\<bar>IEEE.valof frozen_kernel_3_58\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_59_finite:
  "IEEE.is_finite frozen_kernel_3_59"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_59_small:
  "\<bar>IEEE.valof frozen_kernel_3_59\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_60_finite:
  "IEEE.is_finite frozen_kernel_3_60"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_60_small:
  "\<bar>IEEE.valof frozen_kernel_3_60\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_61_finite:
  "IEEE.is_finite frozen_kernel_3_61"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_61_small:
  "\<bar>IEEE.valof frozen_kernel_3_61\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_62_finite:
  "IEEE.is_finite frozen_kernel_3_62"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_62_small:
  "\<bar>IEEE.valof frozen_kernel_3_62\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_kernel_3_63_finite:
  "IEEE.is_finite frozen_kernel_3_63"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma frozen_kernel_3_63_small:
  "\<bar>IEEE.valof frozen_kernel_3_63\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

lemma frozen_input_shape:
  "length frozen_input_activation = 64"
  by (simp add: frozen_input_activation_def)

lemma frozen_kernel_shapes:
  "length frozen_trace_kernels = 4 \<and>
   (\<forall>k \<in> set frozen_trace_kernels. length k = 64)"
  by (simp add: frozen_trace_kernels_def frozen_kernel_0_def
      frozen_kernel_1_def frozen_kernel_2_def frozen_kernel_3_def)

lemma frozen_input_finite:
  "\<forall>x \<in> set frozen_input_activation. IEEE.is_finite x"
  by (simp add: frozen_input_activation_def frozen_input_activation_0_finite frozen_input_activation_1_finite frozen_input_activation_2_finite frozen_input_activation_3_finite frozen_input_activation_4_finite frozen_input_activation_5_finite frozen_input_activation_6_finite frozen_input_activation_7_finite frozen_input_activation_8_finite frozen_input_activation_9_finite frozen_input_activation_10_finite frozen_input_activation_11_finite frozen_input_activation_12_finite frozen_input_activation_13_finite frozen_input_activation_14_finite frozen_input_activation_15_finite frozen_input_activation_16_finite frozen_input_activation_17_finite frozen_input_activation_18_finite frozen_input_activation_19_finite frozen_input_activation_20_finite frozen_input_activation_21_finite frozen_input_activation_22_finite frozen_input_activation_23_finite frozen_input_activation_24_finite frozen_input_activation_25_finite frozen_input_activation_26_finite frozen_input_activation_27_finite frozen_input_activation_28_finite frozen_input_activation_29_finite frozen_input_activation_30_finite frozen_input_activation_31_finite frozen_input_activation_32_finite frozen_input_activation_33_finite frozen_input_activation_34_finite frozen_input_activation_35_finite frozen_input_activation_36_finite frozen_input_activation_37_finite frozen_input_activation_38_finite frozen_input_activation_39_finite frozen_input_activation_40_finite frozen_input_activation_41_finite frozen_input_activation_42_finite frozen_input_activation_43_finite frozen_input_activation_44_finite frozen_input_activation_45_finite frozen_input_activation_46_finite frozen_input_activation_47_finite frozen_input_activation_48_finite frozen_input_activation_49_finite frozen_input_activation_50_finite frozen_input_activation_51_finite frozen_input_activation_52_finite frozen_input_activation_53_finite frozen_input_activation_54_finite frozen_input_activation_55_finite frozen_input_activation_56_finite frozen_input_activation_57_finite frozen_input_activation_58_finite frozen_input_activation_59_finite frozen_input_activation_60_finite frozen_input_activation_61_finite frozen_input_activation_62_finite frozen_input_activation_63_finite)

lemma frozen_input_small:
  "\<forall>x \<in> set frozen_input_activation. \<bar>IEEE.valof x\<bar> < 1"
  by (simp add: frozen_input_activation_def frozen_input_activation_0_small frozen_input_activation_1_small frozen_input_activation_2_small frozen_input_activation_3_small frozen_input_activation_4_small frozen_input_activation_5_small frozen_input_activation_6_small frozen_input_activation_7_small frozen_input_activation_8_small frozen_input_activation_9_small frozen_input_activation_10_small frozen_input_activation_11_small frozen_input_activation_12_small frozen_input_activation_13_small frozen_input_activation_14_small frozen_input_activation_15_small frozen_input_activation_16_small frozen_input_activation_17_small frozen_input_activation_18_small frozen_input_activation_19_small frozen_input_activation_20_small frozen_input_activation_21_small frozen_input_activation_22_small frozen_input_activation_23_small frozen_input_activation_24_small frozen_input_activation_25_small frozen_input_activation_26_small frozen_input_activation_27_small frozen_input_activation_28_small frozen_input_activation_29_small frozen_input_activation_30_small frozen_input_activation_31_small frozen_input_activation_32_small frozen_input_activation_33_small frozen_input_activation_34_small frozen_input_activation_35_small frozen_input_activation_36_small frozen_input_activation_37_small frozen_input_activation_38_small frozen_input_activation_39_small frozen_input_activation_40_small frozen_input_activation_41_small frozen_input_activation_42_small frozen_input_activation_43_small frozen_input_activation_44_small frozen_input_activation_45_small frozen_input_activation_46_small frozen_input_activation_47_small frozen_input_activation_48_small frozen_input_activation_49_small frozen_input_activation_50_small frozen_input_activation_51_small frozen_input_activation_52_small frozen_input_activation_53_small frozen_input_activation_54_small frozen_input_activation_55_small frozen_input_activation_56_small frozen_input_activation_57_small frozen_input_activation_58_small frozen_input_activation_59_small frozen_input_activation_60_small frozen_input_activation_61_small frozen_input_activation_62_small frozen_input_activation_63_small)

lemma frozen_threshold_128_bound:
  "128 < IEEE.threshold TYPE(frozen_binary32)"
proof -
  have exponent: "IEEE.exponent frozen_threshold_128 = 134"
    by transfer simp
  have fraction: "IEEE.fraction frozen_threshold_128 = 0"
    by transfer simp
  have sign: "IEEE.sign frozen_threshold_128 = 0"
    by transfer simp
  have finite: "IEEE.is_finite frozen_threshold_128"
    unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
    using exponent fraction by (simp add: emax_eq)
  have val: "IEEE.valof frozen_threshold_128 = 128"
    using exponent fraction sign by (simp add: valof_eq IEEE.bias_def)
  have bound:
    "\<bar>IEEE.valof frozen_threshold_128\<bar> <
      IEEE.threshold TYPE(frozen_binary32)"
    using float_val_lt_threshold[where a=frozen_threshold_128]
      finite val by simp
  show ?thesis using bound val by simp
qed

lemma frozen_threshold_129_bound:
  "129 < IEEE.threshold TYPE(frozen_binary32)"
  by (simp add: threshold_def bias_def emax_eq; arith)

lemma frozen_kernel_0_finite:
  "\<forall>x \<in> set frozen_kernel_0. IEEE.is_finite x"
  by (simp add: frozen_kernel_0_def
      frozen_kernel_0_0_finite frozen_kernel_0_1_finite frozen_kernel_0_2_finite frozen_kernel_0_3_finite frozen_kernel_0_4_finite frozen_kernel_0_5_finite frozen_kernel_0_6_finite frozen_kernel_0_7_finite frozen_kernel_0_8_finite frozen_kernel_0_9_finite frozen_kernel_0_10_finite frozen_kernel_0_11_finite frozen_kernel_0_12_finite frozen_kernel_0_13_finite frozen_kernel_0_14_finite frozen_kernel_0_15_finite frozen_kernel_0_16_finite frozen_kernel_0_17_finite frozen_kernel_0_18_finite frozen_kernel_0_19_finite frozen_kernel_0_20_finite frozen_kernel_0_21_finite frozen_kernel_0_22_finite frozen_kernel_0_23_finite frozen_kernel_0_24_finite frozen_kernel_0_25_finite frozen_kernel_0_26_finite frozen_kernel_0_27_finite frozen_kernel_0_28_finite frozen_kernel_0_29_finite frozen_kernel_0_30_finite frozen_kernel_0_31_finite frozen_kernel_0_32_finite frozen_kernel_0_33_finite frozen_kernel_0_34_finite frozen_kernel_0_35_finite frozen_kernel_0_36_finite frozen_kernel_0_37_finite frozen_kernel_0_38_finite frozen_kernel_0_39_finite frozen_kernel_0_40_finite frozen_kernel_0_41_finite frozen_kernel_0_42_finite frozen_kernel_0_43_finite frozen_kernel_0_44_finite frozen_kernel_0_45_finite frozen_kernel_0_46_finite frozen_kernel_0_47_finite frozen_kernel_0_48_finite frozen_kernel_0_49_finite frozen_kernel_0_50_finite frozen_kernel_0_51_finite frozen_kernel_0_52_finite frozen_kernel_0_53_finite frozen_kernel_0_54_finite frozen_kernel_0_55_finite frozen_kernel_0_56_finite frozen_kernel_0_57_finite frozen_kernel_0_58_finite frozen_kernel_0_59_finite frozen_kernel_0_60_finite frozen_kernel_0_61_finite frozen_kernel_0_62_finite frozen_kernel_0_63_finite)

lemma frozen_kernel_0_small:
  "\<forall>x \<in> set frozen_kernel_0. \<bar>IEEE.valof x\<bar> < 1"
  by (simp add: frozen_kernel_0_def
      frozen_kernel_0_0_small frozen_kernel_0_1_small frozen_kernel_0_2_small frozen_kernel_0_3_small frozen_kernel_0_4_small frozen_kernel_0_5_small frozen_kernel_0_6_small frozen_kernel_0_7_small frozen_kernel_0_8_small frozen_kernel_0_9_small frozen_kernel_0_10_small frozen_kernel_0_11_small frozen_kernel_0_12_small frozen_kernel_0_13_small frozen_kernel_0_14_small frozen_kernel_0_15_small frozen_kernel_0_16_small frozen_kernel_0_17_small frozen_kernel_0_18_small frozen_kernel_0_19_small frozen_kernel_0_20_small frozen_kernel_0_21_small frozen_kernel_0_22_small frozen_kernel_0_23_small frozen_kernel_0_24_small frozen_kernel_0_25_small frozen_kernel_0_26_small frozen_kernel_0_27_small frozen_kernel_0_28_small frozen_kernel_0_29_small frozen_kernel_0_30_small frozen_kernel_0_31_small frozen_kernel_0_32_small frozen_kernel_0_33_small frozen_kernel_0_34_small frozen_kernel_0_35_small frozen_kernel_0_36_small frozen_kernel_0_37_small frozen_kernel_0_38_small frozen_kernel_0_39_small frozen_kernel_0_40_small frozen_kernel_0_41_small frozen_kernel_0_42_small frozen_kernel_0_43_small frozen_kernel_0_44_small frozen_kernel_0_45_small frozen_kernel_0_46_small frozen_kernel_0_47_small frozen_kernel_0_48_small frozen_kernel_0_49_small frozen_kernel_0_50_small frozen_kernel_0_51_small frozen_kernel_0_52_small frozen_kernel_0_53_small frozen_kernel_0_54_small frozen_kernel_0_55_small frozen_kernel_0_56_small frozen_kernel_0_57_small frozen_kernel_0_58_small frozen_kernel_0_59_small frozen_kernel_0_60_small frozen_kernel_0_61_small frozen_kernel_0_62_small frozen_kernel_0_63_small)

lemma frozen_kernel_1_finite:
  "\<forall>x \<in> set frozen_kernel_1. IEEE.is_finite x"
  by (simp add: frozen_kernel_1_def
      frozen_kernel_1_0_finite frozen_kernel_1_1_finite frozen_kernel_1_2_finite frozen_kernel_1_3_finite frozen_kernel_1_4_finite frozen_kernel_1_5_finite frozen_kernel_1_6_finite frozen_kernel_1_7_finite frozen_kernel_1_8_finite frozen_kernel_1_9_finite frozen_kernel_1_10_finite frozen_kernel_1_11_finite frozen_kernel_1_12_finite frozen_kernel_1_13_finite frozen_kernel_1_14_finite frozen_kernel_1_15_finite frozen_kernel_1_16_finite frozen_kernel_1_17_finite frozen_kernel_1_18_finite frozen_kernel_1_19_finite frozen_kernel_1_20_finite frozen_kernel_1_21_finite frozen_kernel_1_22_finite frozen_kernel_1_23_finite frozen_kernel_1_24_finite frozen_kernel_1_25_finite frozen_kernel_1_26_finite frozen_kernel_1_27_finite frozen_kernel_1_28_finite frozen_kernel_1_29_finite frozen_kernel_1_30_finite frozen_kernel_1_31_finite frozen_kernel_1_32_finite frozen_kernel_1_33_finite frozen_kernel_1_34_finite frozen_kernel_1_35_finite frozen_kernel_1_36_finite frozen_kernel_1_37_finite frozen_kernel_1_38_finite frozen_kernel_1_39_finite frozen_kernel_1_40_finite frozen_kernel_1_41_finite frozen_kernel_1_42_finite frozen_kernel_1_43_finite frozen_kernel_1_44_finite frozen_kernel_1_45_finite frozen_kernel_1_46_finite frozen_kernel_1_47_finite frozen_kernel_1_48_finite frozen_kernel_1_49_finite frozen_kernel_1_50_finite frozen_kernel_1_51_finite frozen_kernel_1_52_finite frozen_kernel_1_53_finite frozen_kernel_1_54_finite frozen_kernel_1_55_finite frozen_kernel_1_56_finite frozen_kernel_1_57_finite frozen_kernel_1_58_finite frozen_kernel_1_59_finite frozen_kernel_1_60_finite frozen_kernel_1_61_finite frozen_kernel_1_62_finite frozen_kernel_1_63_finite)

lemma frozen_kernel_1_small:
  "\<forall>x \<in> set frozen_kernel_1. \<bar>IEEE.valof x\<bar> < 1"
  by (simp add: frozen_kernel_1_def
      frozen_kernel_1_0_small frozen_kernel_1_1_small frozen_kernel_1_2_small frozen_kernel_1_3_small frozen_kernel_1_4_small frozen_kernel_1_5_small frozen_kernel_1_6_small frozen_kernel_1_7_small frozen_kernel_1_8_small frozen_kernel_1_9_small frozen_kernel_1_10_small frozen_kernel_1_11_small frozen_kernel_1_12_small frozen_kernel_1_13_small frozen_kernel_1_14_small frozen_kernel_1_15_small frozen_kernel_1_16_small frozen_kernel_1_17_small frozen_kernel_1_18_small frozen_kernel_1_19_small frozen_kernel_1_20_small frozen_kernel_1_21_small frozen_kernel_1_22_small frozen_kernel_1_23_small frozen_kernel_1_24_small frozen_kernel_1_25_small frozen_kernel_1_26_small frozen_kernel_1_27_small frozen_kernel_1_28_small frozen_kernel_1_29_small frozen_kernel_1_30_small frozen_kernel_1_31_small frozen_kernel_1_32_small frozen_kernel_1_33_small frozen_kernel_1_34_small frozen_kernel_1_35_small frozen_kernel_1_36_small frozen_kernel_1_37_small frozen_kernel_1_38_small frozen_kernel_1_39_small frozen_kernel_1_40_small frozen_kernel_1_41_small frozen_kernel_1_42_small frozen_kernel_1_43_small frozen_kernel_1_44_small frozen_kernel_1_45_small frozen_kernel_1_46_small frozen_kernel_1_47_small frozen_kernel_1_48_small frozen_kernel_1_49_small frozen_kernel_1_50_small frozen_kernel_1_51_small frozen_kernel_1_52_small frozen_kernel_1_53_small frozen_kernel_1_54_small frozen_kernel_1_55_small frozen_kernel_1_56_small frozen_kernel_1_57_small frozen_kernel_1_58_small frozen_kernel_1_59_small frozen_kernel_1_60_small frozen_kernel_1_61_small frozen_kernel_1_62_small frozen_kernel_1_63_small)

lemma frozen_kernel_2_finite:
  "\<forall>x \<in> set frozen_kernel_2. IEEE.is_finite x"
  by (simp add: frozen_kernel_2_def
      frozen_kernel_2_0_finite frozen_kernel_2_1_finite frozen_kernel_2_2_finite frozen_kernel_2_3_finite frozen_kernel_2_4_finite frozen_kernel_2_5_finite frozen_kernel_2_6_finite frozen_kernel_2_7_finite frozen_kernel_2_8_finite frozen_kernel_2_9_finite frozen_kernel_2_10_finite frozen_kernel_2_11_finite frozen_kernel_2_12_finite frozen_kernel_2_13_finite frozen_kernel_2_14_finite frozen_kernel_2_15_finite frozen_kernel_2_16_finite frozen_kernel_2_17_finite frozen_kernel_2_18_finite frozen_kernel_2_19_finite frozen_kernel_2_20_finite frozen_kernel_2_21_finite frozen_kernel_2_22_finite frozen_kernel_2_23_finite frozen_kernel_2_24_finite frozen_kernel_2_25_finite frozen_kernel_2_26_finite frozen_kernel_2_27_finite frozen_kernel_2_28_finite frozen_kernel_2_29_finite frozen_kernel_2_30_finite frozen_kernel_2_31_finite frozen_kernel_2_32_finite frozen_kernel_2_33_finite frozen_kernel_2_34_finite frozen_kernel_2_35_finite frozen_kernel_2_36_finite frozen_kernel_2_37_finite frozen_kernel_2_38_finite frozen_kernel_2_39_finite frozen_kernel_2_40_finite frozen_kernel_2_41_finite frozen_kernel_2_42_finite frozen_kernel_2_43_finite frozen_kernel_2_44_finite frozen_kernel_2_45_finite frozen_kernel_2_46_finite frozen_kernel_2_47_finite frozen_kernel_2_48_finite frozen_kernel_2_49_finite frozen_kernel_2_50_finite frozen_kernel_2_51_finite frozen_kernel_2_52_finite frozen_kernel_2_53_finite frozen_kernel_2_54_finite frozen_kernel_2_55_finite frozen_kernel_2_56_finite frozen_kernel_2_57_finite frozen_kernel_2_58_finite frozen_kernel_2_59_finite frozen_kernel_2_60_finite frozen_kernel_2_61_finite frozen_kernel_2_62_finite frozen_kernel_2_63_finite)

lemma frozen_kernel_2_small:
  "\<forall>x \<in> set frozen_kernel_2. \<bar>IEEE.valof x\<bar> < 1"
  by (simp add: frozen_kernel_2_def
      frozen_kernel_2_0_small frozen_kernel_2_1_small frozen_kernel_2_2_small frozen_kernel_2_3_small frozen_kernel_2_4_small frozen_kernel_2_5_small frozen_kernel_2_6_small frozen_kernel_2_7_small frozen_kernel_2_8_small frozen_kernel_2_9_small frozen_kernel_2_10_small frozen_kernel_2_11_small frozen_kernel_2_12_small frozen_kernel_2_13_small frozen_kernel_2_14_small frozen_kernel_2_15_small frozen_kernel_2_16_small frozen_kernel_2_17_small frozen_kernel_2_18_small frozen_kernel_2_19_small frozen_kernel_2_20_small frozen_kernel_2_21_small frozen_kernel_2_22_small frozen_kernel_2_23_small frozen_kernel_2_24_small frozen_kernel_2_25_small frozen_kernel_2_26_small frozen_kernel_2_27_small frozen_kernel_2_28_small frozen_kernel_2_29_small frozen_kernel_2_30_small frozen_kernel_2_31_small frozen_kernel_2_32_small frozen_kernel_2_33_small frozen_kernel_2_34_small frozen_kernel_2_35_small frozen_kernel_2_36_small frozen_kernel_2_37_small frozen_kernel_2_38_small frozen_kernel_2_39_small frozen_kernel_2_40_small frozen_kernel_2_41_small frozen_kernel_2_42_small frozen_kernel_2_43_small frozen_kernel_2_44_small frozen_kernel_2_45_small frozen_kernel_2_46_small frozen_kernel_2_47_small frozen_kernel_2_48_small frozen_kernel_2_49_small frozen_kernel_2_50_small frozen_kernel_2_51_small frozen_kernel_2_52_small frozen_kernel_2_53_small frozen_kernel_2_54_small frozen_kernel_2_55_small frozen_kernel_2_56_small frozen_kernel_2_57_small frozen_kernel_2_58_small frozen_kernel_2_59_small frozen_kernel_2_60_small frozen_kernel_2_61_small frozen_kernel_2_62_small frozen_kernel_2_63_small)

lemma frozen_kernel_3_finite:
  "\<forall>x \<in> set frozen_kernel_3. IEEE.is_finite x"
  by (simp add: frozen_kernel_3_def
      frozen_kernel_3_0_finite frozen_kernel_3_1_finite frozen_kernel_3_2_finite frozen_kernel_3_3_finite frozen_kernel_3_4_finite frozen_kernel_3_5_finite frozen_kernel_3_6_finite frozen_kernel_3_7_finite frozen_kernel_3_8_finite frozen_kernel_3_9_finite frozen_kernel_3_10_finite frozen_kernel_3_11_finite frozen_kernel_3_12_finite frozen_kernel_3_13_finite frozen_kernel_3_14_finite frozen_kernel_3_15_finite frozen_kernel_3_16_finite frozen_kernel_3_17_finite frozen_kernel_3_18_finite frozen_kernel_3_19_finite frozen_kernel_3_20_finite frozen_kernel_3_21_finite frozen_kernel_3_22_finite frozen_kernel_3_23_finite frozen_kernel_3_24_finite frozen_kernel_3_25_finite frozen_kernel_3_26_finite frozen_kernel_3_27_finite frozen_kernel_3_28_finite frozen_kernel_3_29_finite frozen_kernel_3_30_finite frozen_kernel_3_31_finite frozen_kernel_3_32_finite frozen_kernel_3_33_finite frozen_kernel_3_34_finite frozen_kernel_3_35_finite frozen_kernel_3_36_finite frozen_kernel_3_37_finite frozen_kernel_3_38_finite frozen_kernel_3_39_finite frozen_kernel_3_40_finite frozen_kernel_3_41_finite frozen_kernel_3_42_finite frozen_kernel_3_43_finite frozen_kernel_3_44_finite frozen_kernel_3_45_finite frozen_kernel_3_46_finite frozen_kernel_3_47_finite frozen_kernel_3_48_finite frozen_kernel_3_49_finite frozen_kernel_3_50_finite frozen_kernel_3_51_finite frozen_kernel_3_52_finite frozen_kernel_3_53_finite frozen_kernel_3_54_finite frozen_kernel_3_55_finite frozen_kernel_3_56_finite frozen_kernel_3_57_finite frozen_kernel_3_58_finite frozen_kernel_3_59_finite frozen_kernel_3_60_finite frozen_kernel_3_61_finite frozen_kernel_3_62_finite frozen_kernel_3_63_finite)

lemma frozen_kernel_3_small:
  "\<forall>x \<in> set frozen_kernel_3. \<bar>IEEE.valof x\<bar> < 1"
  by (simp add: frozen_kernel_3_def
      frozen_kernel_3_0_small frozen_kernel_3_1_small frozen_kernel_3_2_small frozen_kernel_3_3_small frozen_kernel_3_4_small frozen_kernel_3_5_small frozen_kernel_3_6_small frozen_kernel_3_7_small frozen_kernel_3_8_small frozen_kernel_3_9_small frozen_kernel_3_10_small frozen_kernel_3_11_small frozen_kernel_3_12_small frozen_kernel_3_13_small frozen_kernel_3_14_small frozen_kernel_3_15_small frozen_kernel_3_16_small frozen_kernel_3_17_small frozen_kernel_3_18_small frozen_kernel_3_19_small frozen_kernel_3_20_small frozen_kernel_3_21_small frozen_kernel_3_22_small frozen_kernel_3_23_small frozen_kernel_3_24_small frozen_kernel_3_25_small frozen_kernel_3_26_small frozen_kernel_3_27_small frozen_kernel_3_28_small frozen_kernel_3_29_small frozen_kernel_3_30_small frozen_kernel_3_31_small frozen_kernel_3_32_small frozen_kernel_3_33_small frozen_kernel_3_34_small frozen_kernel_3_35_small frozen_kernel_3_36_small frozen_kernel_3_37_small frozen_kernel_3_38_small frozen_kernel_3_39_small frozen_kernel_3_40_small frozen_kernel_3_41_small frozen_kernel_3_42_small frozen_kernel_3_43_small frozen_kernel_3_44_small frozen_kernel_3_45_small frozen_kernel_3_46_small frozen_kernel_3_47_small frozen_kernel_3_48_small frozen_kernel_3_49_small frozen_kernel_3_50_small frozen_kernel_3_51_small frozen_kernel_3_52_small frozen_kernel_3_53_small frozen_kernel_3_54_small frozen_kernel_3_55_small frozen_kernel_3_56_small frozen_kernel_3_57_small frozen_kernel_3_58_small frozen_kernel_3_59_small frozen_kernel_3_60_small frozen_kernel_3_61_small frozen_kernel_3_62_small frozen_kernel_3_63_small)

lemma frozen_kernel_0_certificate:
  "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation frozen_kernel_0
      (ieee_fma_dot_tail_witnesses frozen_input_activation frozen_kernel_0)"
  by (rule ieee_fma_dot_tail_certificate,
      simp_all add: frozen_input_activation_def frozen_kernel_0_def
        frozen_input_finite frozen_kernel_0_finite frozen_input_small
        frozen_kernel_0_small frozen_threshold_129_bound)
lemma frozen_kernel_1_certificate:
  "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation frozen_kernel_1
      (ieee_fma_dot_tail_witnesses frozen_input_activation frozen_kernel_1)"
  by (rule ieee_fma_dot_tail_certificate,
      simp_all add: frozen_input_activation_def frozen_kernel_1_def
        frozen_input_finite frozen_kernel_1_finite frozen_input_small
        frozen_kernel_1_small frozen_threshold_129_bound)
lemma frozen_kernel_2_certificate:
  "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation frozen_kernel_2
      (ieee_fma_dot_tail_witnesses frozen_input_activation frozen_kernel_2)"
  by (rule ieee_fma_dot_tail_certificate,
      simp_all add: frozen_input_activation_def frozen_kernel_2_def
        frozen_input_finite frozen_kernel_2_finite frozen_input_small
        frozen_kernel_2_small frozen_threshold_129_bound)
lemma frozen_kernel_3_certificate:
  "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation frozen_kernel_3
      (ieee_fma_dot_tail_witnesses frozen_input_activation frozen_kernel_3)"
  by (rule ieee_fma_dot_tail_certificate,
      simp_all add: frozen_input_activation_def frozen_kernel_3_def
        frozen_input_finite frozen_kernel_3_finite frozen_input_small
        frozen_kernel_3_small frozen_threshold_129_bound)
theorem frozen_trace_certificate:
  "length frozen_trace_witnesses = 4 \<and>
   (\<forall>i < 4. ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation (frozen_trace_kernels ! i)
      (frozen_trace_witnesses ! i))"
proof (rule conjI)
  show "length frozen_trace_witnesses = 4"
    by (simp add: frozen_trace_witnesses_def frozen_trace_kernels_def)
  show "\<forall>i < 4. ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation (frozen_trace_kernels ! i)
      (frozen_trace_witnesses ! i)"
  proof (intro allI impI)
    fix i :: nat
    assume i_lt: "i < 4"
    have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
      using i_lt by arith
    from i_cases
    show "ieee_fma_dot_certificate
        (IEEE.threshold TYPE(frozen_binary32)) 1
        frozen_input_activation (frozen_trace_kernels ! i)
        (frozen_trace_witnesses ! i)"
    proof (elim disjE)
      assume i0: "i = 0"
      show ?thesis using i0 frozen_kernel_0_certificate
        by (simp add: frozen_trace_witnesses_def frozen_trace_kernels_def)
      next
      assume i1: "i = 1"
      show ?thesis using i1 frozen_kernel_1_certificate
        by (simp add: frozen_trace_witnesses_def frozen_trace_kernels_def)
      next
      assume i2: "i = 2"
      show ?thesis using i2 frozen_kernel_2_certificate
        by (simp add: frozen_trace_witnesses_def frozen_trace_kernels_def)
      next
      assume i3: "i = 3"
      show ?thesis using i3 frozen_kernel_3_certificate
        by (simp add: frozen_trace_witnesses_def frozen_trace_kernels_def)
    qed
  qed
qed

theorem frozen_trace_safe:
  "\<forall>i < 4. ieee_fma_dot_safe
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation (frozen_trace_kernels ! i)"
  using frozen_trace_certificate
  by (auto simp: ieee_fma_dot_certificate_imp_safe
      frozen_trace_witnesses_def)

text \<open>
  This is a certificate-replay result only.  The number 64 is a
  deliberately conservative compositional envelope, not an estimate
  of the TinyStories checkpoint's observed floating-point error.
\<close>

theorem frozen_trace_error:
  "\<forall>i < 4. \<bar>dot_product
      (map IEEE.valof frozen_input_activation)
      (map IEEE.valof (frozen_trace_kernels ! i)) -
      IEEE.valof (ieee_fma_dot frozen_input_activation
        (frozen_trace_kernels ! i))\<bar> \<le> 64"
proof (intro allI impI)
  fix i :: nat
  assume i: "i < 4"
  have cert:
    "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation (frozen_trace_kernels ! i)
      (frozen_trace_witnesses ! i)"
    using frozen_trace_certificate i by simp
  have safe:
    "ieee_fma_dot_safe
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation (frozen_trace_kernels ! i)"
    by (rule ieee_fma_dot_certificate_imp_safe[OF cert])
  have error:
    "\<bar>dot_product (map IEEE.valof frozen_input_activation)
        (map IEEE.valof (frozen_trace_kernels ! i)) -
        IEEE.valof (ieee_fma_dot frozen_input_activation
          (frozen_trace_kernels ! i))\<bar> \<le>
      real (min (length frozen_input_activation)
        (length (frozen_trace_kernels ! i))) * 1"
    using ieee_fma_dot_error[where epsilon=1, OF _ safe]
      by simp
  have lengths:
    "min (length frozen_input_activation)
        (length (frozen_trace_kernels ! i)) = 64"
    using frozen_input_shape i by (simp add: frozen_kernel_shapes)
  from error lengths
  show "\<bar>dot_product (map IEEE.valof frozen_input_activation)
      (map IEEE.valof (frozen_trace_kernels ! i)) -
      IEEE.valof (ieee_fma_dot frozen_input_activation
        (frozen_trace_kernels ! i))\<bar> \<le> 64"
    by simp
qed

end
