(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory HaskellLemmaBucket
imports
  HaskellLib_H
  NonDetMonadLemmaBucket
begin

lemma map_bits_to_bl:  
  "map (op !! x) [0..<size x] = reverse (to_bl x)"
  apply simp
  apply (subst list_eq_iff_nth_eq)
  apply rule
   apply (simp add: word_size)
  apply simp
  apply rule
  apply rule
  apply (subst test_bit_bl)
  apply (simp add: word_size)
  done

lemma not_orList_is_replicate:
  "\<not> orList ls \<Longrightarrow> ls = replicate (length ls) False"
proof (induct ls rule: rev_induct)
  case Nil thus ?case unfolding orList_def by simp
next
  case (snoc l ls)

  from snoc.prems have ol: "\<not> orList ls" and nl: "\<not> l" unfolding orList_def by auto
  have "ls = replicate (length ls) False" by (rule snoc.hyps [OF ol])
  thus ?case
    by (rule ssubst) (simp add: nl replicate_app_Cons_same [where xs = "[]", simplified])
qed

lemma andList_Cons:
  assumes al: "andList $ map P (y # ys)"
  shows   "P y"
  using al unfolding andList_def
  by simp (induct rule: rev_induct, simp+)

lemma andList_mapE:
  assumes al: "andList $ map P xs"
  and     xv: "x \<in> set xs"
  shows   "P x"
  using al xv
proof (induct xs arbitrary: x rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc y ys)

  show ?case
  proof (cases "x = y")
    case True
    with snoc.prems show ?thesis by (simp add: andList_def)
  next
    case False
    with snoc.prems show ?thesis
      by (auto simp: andList_def intro!: snoc.hyps)
  qed
qed

lemma andList_to_aligned:
  assumes al: "andList $ map (\<lambda>x. x && mask pageBits = 0) xs"
  and     xv: "x \<in> set xs"
  shows   "is_aligned x pageBits"
proof (subst is_aligned_mask)
  from al show "x && mask pageBits = 0" by (rule andList_mapE) fact
qed

(* minimum/maximum *)

lemma maximum_ge: "x \<in> set b \<Longrightarrow> x \<le> maximum b"
  unfolding maximum_def by (auto intro: Max_ge)

lemma less_minimum_not_in:
  "\<lbrakk> ls \<noteq> []; x < minimum ls \<rbrakk> \<Longrightarrow> x \<notin> set ls"
  unfolding minimum_def by auto

lemma minimum_le_member:
  "\<lbrakk> x \<in> set ls; ls \<noteq> []\<rbrakk> \<Longrightarrow> minimum ls \<le> x"
  unfolding minimum_def
  apply (rule Min_le)
    apply simp
   apply simp
  done

lemma minimum_map_distrib:
  fixes f :: "('a :: linorder) \<Rightarrow> 'a" and ls :: "'a list"
  assumes minf: "\<And>x y. \<lbrakk>x \<in> set ls; y \<in> set ls\<rbrakk> \<Longrightarrow> min (f x) (f y) = f (min x y)"
  and      lsn: "ls \<noteq> []"
  shows "minimum (map f ls) = f (minimum ls)"
  unfolding minimum_def
  apply simp
  apply (rule Min_image_distrib)
    apply (erule (1) minf)
   apply simp
  apply (simp add: lsn)
  done

lemma minimum_enum_upto:
  fixes x :: "'a::len word"
  assumes le: "x \<le> y"
  shows   "minimum [x .e. y] = x"
  unfolding minimum_def using le by (auto intro!: MinI)

lemma break_subsetsD:
  "break f xs = (ys, zs) \<Longrightarrow> set ys \<subseteq> set xs \<and> set zs \<subseteq> set xs"
  apply (induct xs arbitrary: ys zs)
   apply simp
  apply (case_tac "break f xs")
  apply (elim meta_allE, drule(1) meta_mp)
  apply (fastforce simp: split_def split: split_if_asm)
  done

lemma distinct_prop_breakD:
  "\<lbrakk> distinct_prop P xs; break f xs = (ys, zs) \<rbrakk>
    \<Longrightarrow> \<forall>y \<in> set ys. \<forall>z \<in> set zs. P y z"
  apply (induct xs arbitrary: ys zs)
   apply simp
  apply (simp add: split_def split: split_if_asm)
  apply (case_tac "break f xs")
  apply (elim meta_allE, drule(1) meta_mp)
  apply (frule break_subsetsD)
  apply fastforce
  done

lemma stateAssert_wp:
  "\<lbrace>\<lambda>s. P s \<longrightarrow> Q () s\<rbrace> stateAssert P e \<lbrace>Q\<rbrace>"
  by (clarsimp simp: stateAssert_def) wp

lemma is_aligned_alignUp[simp]:
  "is_aligned (alignUp p n) n"
  by (simp add: alignUp_def complement_def
                is_aligned_mask mask_def
                word_bw_assocs)

lemma alignUp_le[simp]:
  "alignUp p n \<le> p + 2 ^ n - 1"
  unfolding alignUp_def
  by (rule word_and_le2)

lemma complement_mask:
  "complement (2 ^ n - 1) = ~~ mask n"
  unfolding complement_def mask_def
  by simp

lemma haskell_assert_wp:
  "\<lbrace>\<lambda>s. Q \<longrightarrow> P s\<rbrace> haskell_assert Q xs \<lbrace>\<lambda>_. P\<rbrace>"
  by simp wp

lemma init_append_last:
  "xs \<noteq> [] \<Longrightarrow> init xs @ [last xs] = xs"
  apply (induct xs rule: rev_induct)
   apply simp
  apply (simp add: init_def)
  done

lemma no_fail_stateAssert:
  "no_fail P (stateAssert P xs)"
  apply (simp add: stateAssert_def)
  apply (rule no_fail_pre, wp no_fail_bind)
  apply simp
  done

lemma empty_fail_stateAssert:
  "empty_fail (stateAssert P s)"
  by (simp add: stateAssert_def assert_def empty_fail_get)

lemma haskell_fail_wp:
  "\<lbrace>\<top>\<rbrace> haskell_fail x \<lbrace>P\<rbrace>"
  by simp

lemma no_fail_haskell_fail [simp, wp]:
  "no_fail \<bottom> (haskell_fail xs)"
  by simp

lemma in_assocs_is_fun:
  "(x \<in> set (assocs f)) = (f (fst x) = snd x)"
  by (cases x) (auto simp add: assocs_def)

lemma fun_is_in_assocs:
  "(f x = y) = ((x,y) \<in> set (assocs f))"
  by (simp add: in_assocs_is_fun)

lemma empty_set_is_null:
  "(set xs = {}) = null xs"
  by (clarsimp simp: null_def)
  
lemma assert_into_when:
  "(assert P) = (when (\<not> P) (haskell_fail []))"
  by (simp add: assert_def when_def)

lemma const_apply:
  "const x y = x"
  by (simp add: const_def)

lemma const_None_empty:
  "const None = empty"
  by (rule ext, simp add: const_apply)

lemma headM_tailM_Cons:
  "headM (x # xs) = return x"
  "tailM (x # xs) = return xs"
  by (simp add: headM_def tailM_def)+

(* Moved by hand *)
lemma replicateM_mapM:
  "replicateM n f = mapM (\<lambda>x. f) (replicate n ())"
  by (simp add: replicateM_def mapM_def)

lemma alignUp_idem:
  fixes a :: "'a::len word"
  assumes al: "is_aligned a n"
  and   sz: "n < len_of TYPE('a)"
  shows "alignUp a n = a"
  using sz al unfolding alignUp_def 
  apply (simp add: complement_mask)
  apply (subst x_power_minus_1)
  apply (subst neg_mask_is_div)    
  apply (simp only: word_arith_nat_div  unat_word_ariths)
  apply (simp only: unat_power_lower)
  apply (subst power_mod_div)
  apply (erule is_alignedE)
  apply simp
  apply (subst unat_mult_power_lem)
   apply simp
  apply (subst unat_sub)
   apply (subst unat_arith_simps)
   apply (simp add: word_bits_def)
  apply (simp add: word_bits_def del: unat_1)
  apply simp
  done

lemma alignUp_not_aligned_eq:
  fixes a :: "'a :: len word"
  assumes al: "\<not> is_aligned a n"
  and     sz: "n < len_of TYPE('a)"
  shows   "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
proof -
  have anz: "a mod 2 ^ n \<noteq> 0" 
    by (rule not_aligned_mod_nz) fact+
  
  hence um: "unat (a mod 2 ^ n - 1) div 2 ^ n = 0" using sz
    apply -
    apply (rule div_less)
    apply (simp add: unat_minus_one)
    apply (rule order_less_trans)
     apply (rule diff_Suc_less)
     apply (erule contrapos_np)
     apply (simp add: unat_eq_zero)
    apply (subst unat_power_lower [symmetric, OF sz[unfolded word_bits_def]])  
    apply (subst word_less_nat_alt [symmetric])
    apply (rule word_mod_less_divisor)
    apply (simp add: p2_gt_0)
    done
    
  have "a + 2 ^ n - 1 = (a div 2 ^ n) * 2 ^ n + (a mod 2 ^ n) + 2 ^ n - 1"
    by (simp add: word_mod_div_equality)
  also have "\<dots> = (a mod 2 ^ n - 1) + (a div 2 ^ n + 1) * 2 ^ n"
    by (simp add: field_simps)
  finally show "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n" using sz    
    unfolding alignUp_def
    apply (subst complement_mask)
    apply (erule ssubst)
    apply (subst neg_mask_is_div)
    apply (simp add: word_arith_nat_div)
    apply (subst unat_word_ariths(1) unat_word_ariths(2))+
    apply (subst uno_simps)
    apply (subst unat_1)
    apply (subst mod_add_right_eq [symmetric])
    apply simp
    apply (subst power_mod_div)
    apply (subst div_mult_self1)
     apply simp
    apply (subst um)
    apply simp
    apply (subst mod_mod_power)
    apply simp
    apply (subst word_unat_power, subst Abs_fnat_hom_mult)
    apply (subst mult_mod_left)
    apply (subst power_add [symmetric])
    apply simp
    apply (subst Abs_fnat_hom_1)
    apply (subst Abs_fnat_hom_add)
    apply (subst word_unat_power, subst Abs_fnat_hom_mult)
    apply (subst word_unat.Rep_inverse[symmetric], subst Abs_fnat_hom_mult)
    apply simp
    done
qed

lemma alignUp_ge:
  fixes a :: "'a :: len word"
  assumes sz: "n < len_of TYPE('a)"
  and nowrap: "alignUp a n \<noteq> 0"
  shows "a \<le> alignUp a n"
proof (cases "is_aligned a n")
  case True
  thus ?thesis using sz
    by (subst alignUp_idem, simp_all)
next
  case False

  have lt0: "unat a div 2 ^ n < 2 ^ (len_of TYPE('a) - n)" using sz
    apply -
    apply (subst td_gal_lt [symmetric])
     apply simp
    apply (simp add: power_add [symmetric])
    done

  have"2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ len_of TYPE('a)" using sz
    apply -
    apply (rule nat_le_power_trans)
    apply simp
    apply (rule Suc_leI [OF lt0])
    apply simp
    done
  moreover have "2 ^ n * (unat a div 2 ^ n + 1) \<noteq> 2 ^ len_of TYPE('a)" using nowrap sz
    apply -  
    apply (erule contrapos_nn)
    apply (subst alignUp_not_aligned_eq [OF False sz])
    apply (subst unat_arith_simps)
    apply (subst unat_word_ariths)
    apply (subst unat_word_ariths)
    apply simp
    apply (subst mult_mod_left)
    apply (simp add: unat_div field_simps power_add[symmetric] mod_mod_power min.absorb2)
    done
  ultimately have lt: "2 ^ n * (unat a div 2 ^ n + 1) < 2 ^ len_of TYPE('a)" by simp
      
  have "a = a div 2 ^ n * 2 ^ n + a mod 2 ^ n" by (rule word_mod_div_equality [symmetric])
  also have "\<dots> < (a div 2 ^ n + 1) * 2 ^ n" using sz lt
    apply (simp add: field_simps)
    apply (rule word_add_less_mono1)
    apply (rule word_mod_less_divisor)
    apply (simp add: word_less_nat_alt)
    apply (subst unat_word_ariths)
    apply (simp add: unat_div)
    done
  also have "\<dots> =  alignUp a n"
    by (rule alignUp_not_aligned_eq [symmetric]) fact+  
  finally show ?thesis by (rule order_less_imp_le)
qed

lemma alignUp_le_greater_al:
  fixes x :: "'a :: len word"
  assumes le: "a \<le> x"
  and     sz: "n < len_of TYPE('a)"
  and     al: "is_aligned x n"
  shows   "alignUp a n \<le> x"
proof (cases "is_aligned a n")
  case True
  thus ?thesis using sz le by (simp add: alignUp_idem)
next
  case False

  hence anz: "a mod 2 ^ n \<noteq> 0" 
    by (rule not_aligned_mod_nz)
  
  from al obtain k where xk: "x = 2 ^ n * of_nat k" and kv: "k < 2 ^ (len_of TYPE('a) - n)"
    by (auto elim!: is_alignedE)
  
  hence kn: "unat (of_nat k :: 'a word) * unat ((2::'a word) ^ n) < 2 ^ len_of TYPE('a)" 
    using sz
    apply (subst unat_of_nat_eq)
     apply (erule order_less_le_trans)
     apply simp
    apply (subst mult.commute)
    apply simp
    apply (rule nat_less_power_trans)
     apply simp
    apply simp
    done

  have au: "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n" 
    by (rule alignUp_not_aligned_eq) fact+
  also have "\<dots> \<le> of_nat k * 2 ^ n"
  proof (rule word_mult_le_mono1 [OF inc_le _ kn])
    show "a div 2 ^ n < of_nat k" using kv xk le sz anz
      by (simp add: alignUp_div_helper)
  
    show "(0:: 'a word) < 2 ^ n" using sz by (simp add: p2_gt_0 sz)
  qed
    
  finally show ?thesis using xk by (simp add: field_simps)
qed

lemma alignUp_is_aligned_nz:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < len_of TYPE('a)"
  and     ax: "a \<le> x"
  and     az: "a \<noteq> 0"
  shows   "alignUp (a::'a :: len word) n \<noteq> 0"
proof (cases "is_aligned a n")
  case True
  hence "alignUp a n = a" using sz by (simp add: alignUp_idem)
  thus ?thesis using az by simp
next
  case False
  hence anz: "a mod 2 ^ n \<noteq> 0" 
    by (rule not_aligned_mod_nz)

  {
    assume asm: "alignUp a n = 0"

    have lt0: "unat a div 2 ^ n < 2 ^ (len_of TYPE('a) - n)" using sz
      apply -
      apply (subst td_gal_lt [symmetric])
      apply simp
      apply (simp add: power_add [symmetric])
      done

    have leq: "2 ^ n * (unat a div 2 ^ n + 1) \<le> 2 ^ len_of TYPE('a)" using sz
      apply -
      apply (rule nat_le_power_trans)
      apply simp
      apply (rule Suc_leI [OF lt0])
      apply simp
      done    

    from al obtain k where  kv: "k < 2 ^ (len_of TYPE('a) - n)" and xk: "x = 2 ^ n * of_nat k"
      by (auto elim!: is_alignedE)

    hence "a div 2 ^ n < of_nat k" using ax sz anz
      by (rule alignUp_div_helper)

    hence r: "unat a div 2 ^ n < k" using sz
      apply (simp add: unat_div word_less_nat_alt)
      apply (subst (asm) unat_of_nat)
      apply (subst (asm) mod_less)
       apply (rule order_less_le_trans [OF kv])
       apply simp+
      done
    
    have "alignUp a n = (a div 2 ^ n + 1) * 2 ^ n"
      by (rule alignUp_not_aligned_eq) fact+
    
    hence "\<dots> = 0" using asm by simp
    hence "unat a div 2 ^ n = 2 ^ (len_of TYPE('a) - n) - 1" using sz leq
      apply -
      apply (rule nat_diff_add)
      apply simp
      apply (subst nat_mult_eq_cancel1 [where k = "2 ^ n", symmetric])
      apply simp
      apply (subst power_add [symmetric])
      apply simp
      apply (drule unat_cong)
      apply simp
      apply (subst (asm) unat_word_ariths)
      apply (subst (asm) unat_word_ariths)
      apply (simp add: unat_div mult_mod_left power_add [symmetric] mod_mod_power
                       min.absorb2)
      apply (clarsimp simp: field_simps)
      apply (rule ccontr)
      apply (drule (1) order_le_neq_trans)
      apply (simp)
      done
    
    hence "2 ^ (len_of TYPE('a) - n) - 1 < k" using r
      by simp
    hence False using kv by simp
  } thus ?thesis by (clarsimp)
qed

lemma alignUp_ar_helper:
  fixes a :: "'a :: len word"
  assumes al: "is_aligned x n"
  and     sz: "n < len_of TYPE('a)"
  and    sub: "{x..x + 2 ^ n - 1} \<subseteq> {a..b}"
  and    anz: "a \<noteq> 0"
  shows "a \<le> alignUp a n \<and> alignUp a n + 2 ^ n - 1 \<le> b"
proof 
  from al have xl: "x \<le> x + 2 ^ n - 1" by (simp add: is_aligned_no_overflow)
    
  from xl sub have ax: "a \<le> x"
    by (clarsimp elim!: range_subset_lower [where x = x])

  show "a \<le> alignUp a n"
  proof (rule alignUp_ge)
    show "alignUp a n \<noteq> 0" using al sz ax anz
      by (rule alignUp_is_aligned_nz)   
  qed fact+  
  
  show "alignUp a n + 2 ^ n - 1 \<le> b"
  proof (rule order_trans)
    from xl show tp: "x + 2 ^ n - 1 \<le> b" using sub
      by (clarsimp elim!: range_subset_upper [where x = x])
    
    from ax have "alignUp a n \<le> x"
      by (rule alignUp_le_greater_al) fact+
    hence "alignUp a n + (2 ^ n - 1) \<le> x + (2 ^ n - 1)" using xl
      apply -
      apply (erule word_plus_mono_left)
      apply (subst olen_add_eqv)
      apply (simp add: field_simps)
      done
    thus "alignUp a n + 2 ^ n - 1 \<le> x + 2 ^ n - 1"
      by (simp add: field_simps)
  qed
qed
  
lemma orList_False:
  "(\<not> orList bs) = (set bs \<subseteq> {False})"
  apply (induct bs)
  apply (simp_all add: orList_def foldl_True)
  apply (case_tac a)   
  apply (simp_all add: orList_def foldl_True)
  done

lemma Cons_eq_tails:
  "((xs # xxs) = tails ys) = (ys = xs \<and> xxs = tl (tails ys))"
  by (case_tac ys, auto)

lemma findM_on_outcome':
  assumes x: "\<And>x xs. \<lbrace>\<lambda>s. Q None s \<and> x \<in> fn s \<and> set xs \<subseteq> fn s\<rbrace> f x
                     \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q (Some x) s) \<and> (\<not> rv \<longrightarrow> Q None s \<and> set xs \<subseteq> fn s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Q None s \<and> set xs \<subseteq> fn s\<rbrace> findM f xs \<lbrace>Q\<rbrace>"
  apply (induct xs)
   apply (simp, wp)
  apply (simp, wp)
   apply assumption
  apply (rule x)
  done


lemma findM_on_outcome:
  assumes x: "\<And>x ys. x \<in> set xs \<Longrightarrow> \<lbrace>Q None and I\<rbrace> f x \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q (Some x) s) \<and> (\<not> rv \<longrightarrow> Q None s \<and> I s)\<rbrace>"
  shows      "\<lbrace>Q None and I\<rbrace> findM f xs \<lbrace>Q\<rbrace>"
  apply (rule hoare_vcg_precond_imp)
   apply (rule findM_on_outcome' [where fn="\<lambda>s. if I s then set xs else {}"])
   apply (case_tac "x \<notin> set xs")
    apply simp
   apply (simp cong: rev_conj_cong)
   apply (case_tac "\<not> set xsa \<subseteq> set xs")
    apply simp
   apply simp
   apply (rule hoare_vcg_precond_imp)
    apply (rule hoare_post_imp [OF _ x])
     apply clarsimp
    apply assumption
   apply simp
  apply simp
  done

lemma in_set_tailsD: "xs \<in> set (tails ys) \<Longrightarrow> set xs \<subseteq> set ys"
  apply (induct ys)
   apply simp
  apply simp
  apply (erule disjE)
   apply simp
  apply simp
  apply blast
  done

lemma notin_set_tails_set:
  "x \<notin> set xs \<Longrightarrow> \<forall>xs' \<in> set (tails xs). \<forall>x' \<in> set xs'. x \<noteq> x'"
  by (fastforce dest!: in_set_tailsD)

lemma set_tails_set: "(set (tails v) \<subseteq> {x. set x \<subseteq> S}) = (set v \<subseteq> S)"
  apply (induct v, simp_all)
  done

lemma filter_assocs_Cons:
  fixes v :: "('a :: len) word" shows
  "\<lbrakk> f (v, g v); \<forall>x < v. \<not> f (x, g x) \<rbrakk> \<Longrightarrow>
     filter f (assocs g) = (v, g v) # tl (filter f (assocs g))"
  apply (simp add: assocs_def)
  apply (cut_tac v=v in enum_word_div)
  apply clarsimp
  apply (subst map_cong [OF _ refl], assumption)+
  apply (simp(no_asm))
  apply simp
  done

lemma snd_stateAssert_after:
  "\<not> snd ((do _ \<leftarrow> f; stateAssert R vs od) s) \<Longrightarrow>
  \<not>snd (f s) \<and> (\<forall>(rv, s') \<in> fst (f s). R s')"
  apply (clarsimp simp: bind_def stateAssert_def get_def assert_def 
      return_def fail_def split_def split: split_if_asm)
  done
    
lemma oblivious_stateAssert [simp]:
  "oblivious f (stateAssert g xs) = (\<forall>s. g (f s) = g s)"
  apply (simp add: oblivious_def stateAssert_def exec_get
                   assert_def return_def fail_def split: split_if)
  apply auto
  done

lemma stateAssert_def2:
  "stateAssert f xs = do v \<leftarrow> gets f; if v then return () else fail od"
  by (simp add: stateAssert_def gets_def assert_def)

lemma findM_is_mapME:
  "(findM f xs >>= g)
   = liftM (\<lambda>_. ())
      (doE ys \<leftarrow> mapME_x (\<lambda>x. do v \<leftarrow> f x;
                             if v then do g (Some x); throwError () od
                             else returnOk () od) xs;
              liftE (g None) odE)"
  apply (induct xs)
   apply (simp add: mapME_x_def sequenceE_x_def liftM_def returnOk_bind)
   apply (simp add: liftE_def)
  apply (simp add: mapME_x_Cons bindE_assoc liftE_bindE[symmetric]
                   liftM_def cong: if_cong)
  apply (simp add: liftE_bindE bind_assoc)
  apply (rule bind_cong[OF refl])
  apply (simp add: bindE_assoc split: split_if)
  apply (simp add: liftE_bindE bind_assoc throwError_bind)
  done

end
