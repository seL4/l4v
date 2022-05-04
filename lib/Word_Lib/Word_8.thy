(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Words of Length 8"

theory Word_8
imports
  More_Word
  Enumeration_Word
  Even_More_List
  Signed_Words
  Word_Lemmas
begin

context
  includes bit_operations_syntax
begin

lemma len8: "len_of (x :: 8 itself) = 8" by simp

lemma word8_and_max_simp:
  \<open>x AND 0xFF = x\<close> for x :: \<open>8 word\<close>
  using word_and_full_mask_simp [of x]
  by (simp add: numeral_eq_Suc mask_Suc_exp)

lemma enum_word8_eq:
  \<open>enum = [0 :: 8 word, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                            20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
                            37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
                            54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
                            71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
                            88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103,
                            104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
                            118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
                            132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                            146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
                            160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                            174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
                            188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
                            202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215,
                            216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
                            230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243,
                            244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>map unat ?lhs = [0..<256]\<close>
    by (simp add: enum_word_def comp_def take_bit_nat_eq_self map_idem_upt_eq unsigned_of_nat)
  also have \<open>\<dots> = map unat ?rhs\<close>
    by (simp add: upt_zero_numeral_unfold)
  finally show ?thesis
    using unat_inj by (rule map_injective)
qed

lemma set_enum_word8_def:
  "(set enum :: 8 word set) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                            20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
                            37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
                            54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70,
                            71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87,
                            88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103,
                            104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
                            118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
                            132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145,
                            146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
                            160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
                            174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187,
                            188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
                            202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215,
                            216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
                            230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243,
                            244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255}"
  by (simp add: enum_word8_eq)

lemma set_strip_insert: "\<lbrakk> x \<in> insert a S; x \<noteq> a \<rbrakk> \<Longrightarrow> x \<in> S"
  by simp

lemma word8_exhaust:
  fixes x :: \<open>8 word\<close>
  shows "\<lbrakk>x \<noteq> 0; x \<noteq> 1; x \<noteq> 2; x \<noteq> 3; x \<noteq> 4; x \<noteq> 5; x \<noteq> 6; x \<noteq> 7; x \<noteq> 8; x \<noteq> 9; x \<noteq> 10; x \<noteq> 11; x \<noteq>
          12; x \<noteq> 13; x \<noteq> 14; x \<noteq> 15; x \<noteq> 16; x \<noteq> 17; x \<noteq> 18; x \<noteq> 19; x \<noteq> 20; x \<noteq> 21; x \<noteq> 22; x \<noteq>
          23; x \<noteq> 24; x \<noteq> 25; x \<noteq> 26; x \<noteq> 27; x \<noteq> 28; x \<noteq> 29; x \<noteq> 30; x \<noteq> 31; x \<noteq> 32; x \<noteq> 33; x \<noteq>
          34; x \<noteq> 35; x \<noteq> 36; x \<noteq> 37; x \<noteq> 38; x \<noteq> 39; x \<noteq> 40; x \<noteq> 41; x \<noteq> 42; x \<noteq> 43; x \<noteq> 44; x \<noteq>
          45; x \<noteq> 46; x \<noteq> 47; x \<noteq> 48; x \<noteq> 49; x \<noteq> 50; x \<noteq> 51; x \<noteq> 52; x \<noteq> 53; x \<noteq> 54; x \<noteq> 55; x \<noteq>
          56; x \<noteq> 57; x \<noteq> 58; x \<noteq> 59; x \<noteq> 60; x \<noteq> 61; x \<noteq> 62; x \<noteq> 63; x \<noteq> 64; x \<noteq> 65; x \<noteq> 66; x \<noteq>
          67; x \<noteq> 68; x \<noteq> 69; x \<noteq> 70; x \<noteq> 71; x \<noteq> 72; x \<noteq> 73; x \<noteq> 74; x \<noteq> 75; x \<noteq> 76; x \<noteq> 77; x \<noteq>
          78; x \<noteq> 79; x \<noteq> 80; x \<noteq> 81; x \<noteq> 82; x \<noteq> 83; x \<noteq> 84; x \<noteq> 85; x \<noteq> 86; x \<noteq> 87; x \<noteq> 88; x \<noteq>
          89; x \<noteq> 90; x \<noteq> 91; x \<noteq> 92; x \<noteq> 93; x \<noteq> 94; x \<noteq> 95; x \<noteq> 96; x \<noteq> 97; x \<noteq> 98; x \<noteq> 99; x \<noteq>
          100; x \<noteq> 101; x \<noteq> 102; x \<noteq> 103; x \<noteq> 104; x \<noteq> 105; x \<noteq> 106; x \<noteq> 107; x \<noteq> 108; x \<noteq> 109; x \<noteq>
          110; x \<noteq> 111; x \<noteq> 112; x \<noteq> 113; x \<noteq> 114; x \<noteq> 115; x \<noteq> 116; x \<noteq> 117; x \<noteq> 118; x \<noteq> 119; x \<noteq>
          120; x \<noteq> 121; x \<noteq> 122; x \<noteq> 123; x \<noteq> 124; x \<noteq> 125; x \<noteq> 126; x \<noteq> 127; x \<noteq> 128; x \<noteq> 129; x \<noteq>
          130; x \<noteq> 131; x \<noteq> 132; x \<noteq> 133; x \<noteq> 134; x \<noteq> 135; x \<noteq> 136; x \<noteq> 137; x \<noteq> 138; x \<noteq> 139; x \<noteq>
          140; x \<noteq> 141; x \<noteq> 142; x \<noteq> 143; x \<noteq> 144; x \<noteq> 145; x \<noteq> 146; x \<noteq> 147; x \<noteq> 148; x \<noteq> 149; x \<noteq>
          150; x \<noteq> 151; x \<noteq> 152; x \<noteq> 153; x \<noteq> 154; x \<noteq> 155; x \<noteq> 156; x \<noteq> 157; x \<noteq> 158; x \<noteq> 159; x \<noteq>
          160; x \<noteq> 161; x \<noteq> 162; x \<noteq> 163; x \<noteq> 164; x \<noteq> 165; x \<noteq> 166; x \<noteq> 167; x \<noteq> 168; x \<noteq> 169; x \<noteq>
          170; x \<noteq> 171; x \<noteq> 172; x \<noteq> 173; x \<noteq> 174; x \<noteq> 175; x \<noteq> 176; x \<noteq> 177; x \<noteq> 178; x \<noteq> 179; x \<noteq>
          180; x \<noteq> 181; x \<noteq> 182; x \<noteq> 183; x \<noteq> 184; x \<noteq> 185; x \<noteq> 186; x \<noteq> 187; x \<noteq> 188; x \<noteq> 189; x \<noteq>
          190; x \<noteq> 191; x \<noteq> 192; x \<noteq> 193; x \<noteq> 194; x \<noteq> 195; x \<noteq> 196; x \<noteq> 197; x \<noteq> 198; x \<noteq> 199; x \<noteq>
          200; x \<noteq> 201; x \<noteq> 202; x \<noteq> 203; x \<noteq> 204; x \<noteq> 205; x \<noteq> 206; x \<noteq> 207; x \<noteq> 208; x \<noteq> 209; x \<noteq>
          210; x \<noteq> 211; x \<noteq> 212; x \<noteq> 213; x \<noteq> 214; x \<noteq> 215; x \<noteq> 216; x \<noteq> 217; x \<noteq> 218; x \<noteq> 219; x \<noteq>
          220; x \<noteq> 221; x \<noteq> 222; x \<noteq> 223; x \<noteq> 224; x \<noteq> 225; x \<noteq> 226; x \<noteq> 227; x \<noteq> 228; x \<noteq> 229; x \<noteq>
          230; x \<noteq> 231; x \<noteq> 232; x \<noteq> 233; x \<noteq> 234; x \<noteq> 235; x \<noteq> 236; x \<noteq> 237; x \<noteq> 238; x \<noteq> 239; x \<noteq>
          240; x \<noteq> 241; x \<noteq> 242; x \<noteq> 243; x \<noteq> 244; x \<noteq> 245; x \<noteq> 246; x \<noteq> 247; x \<noteq> 248; x \<noteq> 249; x \<noteq>
          250; x \<noteq> 251; x \<noteq> 252; x \<noteq> 253; x \<noteq> 254; x \<noteq> 255\<rbrakk> \<Longrightarrow> P"
  apply (subgoal_tac "x \<in> set enum", subst (asm) set_enum_word8_def)
    apply (drule set_strip_insert, assumption)+
   apply (erule emptyE)
  apply (subst enum_UNIV, rule UNIV_I)
  done

end

end
