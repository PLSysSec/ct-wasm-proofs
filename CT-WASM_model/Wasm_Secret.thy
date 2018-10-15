section {* Security Proofs *}

theory Wasm_Secret imports Wasm_Secret_Aux "AFP/Coinductive/Coinductive" "HOL-Library.BNF_Corec" begin

inductive action_indistinguishable :: "action \<Rightarrow> action \<Rightarrow> bool" ("_ \<sim>'_a _" 60) where
  refl:"a \<sim>_a a"
| binop_32:"safe_binop_i iop \<Longrightarrow> (Binop_i32_Some_action iop c1 c2) \<sim>_a (Binop_i32_Some_action iop c1' c2')"
| binop_64:"safe_binop_i iop \<Longrightarrow> (Binop_i64_Some_action iop c1 c2) \<sim>_a (Binop_i64_Some_action iop c1' c2')"
| select:"(Select_action Secret c1) \<sim>_a (Select_action Secret c2)"
| host_Some:"\<lbrakk>store_public_agree s s'; publics_agree vcs vcs'; store_public_agree s_o s'_o; publics_agree vcs_o vcs'_o\<rbrakk> \<Longrightarrow> (Callcl_host_Some_action s vcs s_o vcs_o Untrusted tf f hs) \<sim>_a (Callcl_host_Some_action s' vcs' s'_o vcs'_o Untrusted tf f hs')"
| host_None:"\<lbrakk>store_public_agree s s'; publics_agree vcs vcs'\<rbrakk> \<Longrightarrow> (Callcl_host_None_action s vcs Untrusted tf f hs) \<sim>_a (Callcl_host_None_action s' vcs' Untrusted tf f hs')"
| convert_Some:"\<lbrakk>is_int_t t1; is_int_t t2; types_agree t1 v; public_agree v v'\<rbrakk> \<Longrightarrow> (Convert_Some_action t1 t2 v) \<sim>_a (Convert_Some_action t1 t2 v')"
| convert_None:"\<lbrakk>is_int_t t1; is_int_t t2; types_agree t1 v; public_agree v v'\<rbrakk> \<Longrightarrow> (Convert_None_action t1 t2 v) \<sim>_a (Convert_None_action t1 t2 v')"

lemma action_indistinguishable_symm:
  assumes "a \<sim>_a b"
  shows "b \<sim>_a a"
  using assms
proof (induction rule: action_indistinguishable.induct)
  case (refl a)
  thus ?case
    using action_indistinguishable.refl
    by -
next
  case (binop_32 iop c1 c2 c1' c2')
  thus ?case
    using action_indistinguishable.binop_32
    by blast
next
  case (binop_64 iop c1 c2 c1' c2')
  thus ?case
    using action_indistinguishable.binop_64
    by blast
next
  case (select c1 c2)
  thus ?case
    using action_indistinguishable.select
    by blast
next
  case (host_Some s s' vcs vcs' tf f)
  thus ?case
    using action_indistinguishable.host_Some store_public_agree_symm publics_agree_symm
    by metis
next
  case (host_None s s' vcs vcs' tf f)
  thus ?case
    using action_indistinguishable.host_None store_public_agree_symm publics_agree_symm
    by metis
next
  case (convert_Some t1 t2 v v')
  thus ?case
    using action_indistinguishable.convert_Some public_agree_imp_types_agree public_agree_symm
    by metis
next
  case (convert_None t1 t2 v v')
  thus ?case
    using action_indistinguishable.convert_None public_agree_imp_types_agree public_agree_symm
    by metis
qed

lemma action_indistinguishable_trans:
  assumes "a \<sim>_a b"
          "b \<sim>_a c"
  shows "a \<sim>_a c"
  using assms
proof (induction a b rule: action_indistinguishable.induct)
  case (refl a)
  thus ?case
    by -
next
  case (binop_32 iop c1 c2 c1' c2')
  thus ?case
    by (fastforce simp add: action_indistinguishable.simps)
next
  case (binop_64 iop c1 c2 c1' c2')
  thus ?case
    by (fastforce simp add: action_indistinguishable.simps)
next
  case (select sec c)
  thus ?case
    by (fastforce simp add: action_indistinguishable.simps)
next
  case (host_Some s s' vcs vcs' s_o s_o' vcs_o vcs_o' tf f hs hs')
  thus ?case
    using store_public_agree_trans[OF host_Some(1)] publics_agree_trans[OF host_Some(2)]
          store_public_agree_trans[OF host_Some(3)] publics_agree_trans[OF host_Some(4)]
    by (fastforce simp add: action_indistinguishable.simps)
next
  case (host_None s s' vcs vcs' tf f)
  thus ?case
    using store_public_agree_trans[OF host_None(1)] publics_agree_trans[OF host_None(2)]
    by (fastforce simp add: action_indistinguishable.simps)
next
  case (convert_Some t1 t2 v v')
  thus ?case
    using public_agree_trans[OF convert_Some(4)]
    by (fastforce simp add: action_indistinguishable.simps)
next
  case (convert_None t1 t2 v v')
  thus ?case
    using public_agree_trans[OF convert_None(4)]
    by (fastforce simp add: action_indistinguishable.simps)
qed


lemma equivp_action_indistinguishable: "equivp action_indistinguishable"
  using action_indistinguishable.refl action_indistinguishable_symm action_indistinguishable_trans
  unfolding equivp_reflp_symp_transp reflp_def symp_def transp_def
  by blast

lemma equivp_obs: "equivp (list_all2 action_indistinguishable)"
  using equivp_action_indistinguishable list.rel_reflp list.rel_symp list.rel_transp
  unfolding equivp_reflp_symp_transp
  by blast

quotient_type (overloaded) observation = "action list" / "list_all2 action_indistinguishable"
  using equivp_obs
  by blast

abbreviation abs_obs :: "action list \<Rightarrow> observation" ("$\<A> _" 60) where
  "abs_obs a \<equiv> abs_observation a"

inductive reduction_actions :: "[s, v list, e list, nat, action list] \<Rightarrow> bool" ("r'_actions \<lparr>_;_;_\<rparr> _ _" 60) where
  "\<lbrakk>const_list es \<or> es = [Trap]\<rbrakk> \<Longrightarrow> r_actions \<lparr>s;vs;es\<rparr> i []"
| "\<lbrakk>\<lparr>s;vs;es\<rparr> a\<leadsto>_i \<lparr>s';vs';es'\<rparr>; r_actions \<lparr>s';vs';es'\<rparr> i as\<rbrakk> \<Longrightarrow> r_actions \<lparr>s;vs;es\<rparr> i (a#as)"

inductive reduce_weight :: "[s, v list, e list, nat, nat, s, v list, e list] \<Rightarrow> bool" ("\<lparr>_;_;_\<rparr> |_|\<leadsto>'_ _ \<lparr>_;_;_\<rparr>" 60) where
  "\<lparr>s;vs;es\<rparr> a\<leadsto>_i \<lparr>s';vs';es'\<rparr> \<Longrightarrow> \<lparr>s;vs;es\<rparr> |(weight a)|\<leadsto>_i \<lparr>s';vs';es'\<rparr>"

inductive reduction_weight :: "[s, v list, e list, nat, nat] \<Rightarrow> bool" ("r'_weight \<lparr>_;_;_\<rparr> _ _" 60) where
  "\<lbrakk>const_list es \<or> es = [Trap]\<rbrakk> \<Longrightarrow> r_weight \<lparr>s;vs;es\<rparr> i 0"
| "\<lbrakk>\<lparr>s;vs;es\<rparr> |w|\<leadsto>_i \<lparr>s';vs';es'\<rparr>; r_weight \<lparr>s';vs';es'\<rparr> i w'\<rbrakk> \<Longrightarrow> r_weight \<lparr>s;vs;es\<rparr> i (w+w')"

lemma r_actions_imp_r_weight:
  assumes "r_actions \<lparr>s;vs;es\<rparr> i as"
  shows "r_weight \<lparr>s;vs;es\<rparr> i (sum_list (map weight as))"
  using assms
proof (induction rule: reduction_actions.induct)
  case (1 es s vs i)
  thus ?case
    using reduction_weight.intros(1)
    by fastforce
next
  case (2 s vs es a i s' vs' es' as)
  show ?case
    using reduce_weight.intros(1)[OF 2(1)] reduction_weight.intros(2)[OF _ 2(3)]
    by fastforce
qed

lemma memories_public_agree_helper:
  assumes "smem_ind s i = Some j"
          "store_public_agree s s'"
          "store_typing s \<S>"
          "i < length (inst s)"
          "s.mem s ! j = (m, sec)"
  shows "smem_ind s' i = Some j"
        "j < length (s.mem s')"
        "memories_public_agree (s.mem s) (s.mem s')"
        "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
        "\<exists>m'. s.mem s' ! j = (m', sec)"
proof -
  show "smem_ind s' i = Some j"
    using store_public_agree_smem_ind_eq assms(1,2)
    by fastforce
  moreover
  show "j < length (s.mem s')"
    using store_typing_imp_inst_length_eq[OF assms(3)] assms(1,4)
          store_public_agree_imp_store_typing[OF assms(3,2)]
          store_typing_imp_mem_agree_Some(1)[OF assms(3)]
          store_typing_imp_mem_length_eq
    by fastforce
  thus mem_agree:"memories_public_agree (s.mem s) (s.mem s')" "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
    using assms(2)
    by (metis store_public_agree_def, metis list_all2_nthD2 store_public_agree_def)
  thus "\<exists>m'. s.mem s' ! j = (m', sec)"
    using assms(5)
    unfolding memory_public_agree_def
    by (metis eq_snd_iff)
qed

lemma load_helper:
  assumes "smem_ind s i = Some j"
          "s.mem s ! j = (m, sec)"
          "store_typing s \<S>"
          "i < length (inst s)"
          "\<C> = (s_inst \<S> ! i)\<lparr>trust_t := tr, local := local (s_inst \<S> ! i) @ tvs, label := arb_labs, return := arb_return\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 sec' k, $Load t tp a off] : (ts _> ts')"
  shows "t_sec t = sec"
proof-
  have "option_projr (memory (s_inst \<S> ! i)) = Some sec"
    using store_typing_imp_mem_agree_inst[OF assms(3)] assms(1,2,4)
          store_typing_imp_inst_length_eq[OF assms(3)]
    by fastforce
  thus t_sec_is:"t_sec t = sec"
    using b_e_type_load(1)[OF unlift_b_e[of \<S> \<C> "[Load t tp a off]"]]
          e_type_comp_conc1[of \<S> \<C> "[$C ConstInt32 sec' k]" "[$Load t tp a off]"]
          assms(5,6)
    unfolding option_projr_def
    by fastforce
qed

lemma store_helper:
  assumes "smem_ind s i = Some j"
          "s.mem s ! j = (m, sec)"
          "exprs_public_agree [$C ConstInt32 sec' k, $C v, $Store t tp a off] es'"
          "store_public_agree s s'"
          "store_typing s \<S>"
          "i < length (inst s)"
          "\<C> = (s_inst \<S> ! i)\<lparr>trust_t := tr, local := local (s_inst \<S> ! i) @ tvs, label := arb_labs, return := arb_return\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 sec' k, $C v, $Store t tp a off] : (ts _> ts')"
  shows "t_sec t = sec"
        "sec' = Public"
        "types_agree t v"
        "\<exists>v' v''. es'= [$C v', $C v'', $Store t tp a off] \<and>
                  v' = (ConstInt32 sec' k) \<and>
                  public_agree v v''"
        "smem_ind s' i = Some j"
        "j < length (s.mem s')"
        "memories_public_agree (s.mem s) (s.mem s')"
        "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
        "\<exists>m'. s.mem s' ! j = (m', sec)"
proof -
  have "option_projr (memory (s_inst \<S> ! i)) = Some sec"
    using store_typing_imp_mem_agree_inst[OF assms(5)] assms(1,2,6)
          store_typing_imp_inst_length_eq[OF assms(5)]
    by fastforce
  thus t_sec_is:"t_sec t = sec"
    using b_e_type_store(2)[OF unlift_b_e[of \<S> \<C> "[Store t tp a off]"]]
          e_type_comp_conc2[of \<S> \<C> "[$C ConstInt32 sec' k]" "[$C v]" "[$Store t tp a off]"]
          assms(7,8)
    unfolding option_projr_def
    by fastforce
  show sec_def:"sec' = Public"
               "types_agree t v"
    using types_preserved_store(2,3) assms
    by auto
  thus  es'_def:"\<exists>v' v''. es'= [$C v', $C v'', $Store t tp a off] \<and>
                          v' = (ConstInt32 sec' k) \<and>
                          public_agree v v''"
    using exprs_public_agree_imp_publics_agree1_const2[OF assms(3)]
    by (fastforce simp add: expr_public_agree.simps public_agree_def typeof_def t_sec_def)
  show mem_agree:"smem_ind s' i = Some j"
                 "j < length (s.mem s')"
                 "memories_public_agree (s.mem s) (s.mem s')"
                 "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
                 "\<exists>m'. s.mem s' ! j = (m', sec)"
    using memories_public_agree_helper[OF assms(1,4,5,6,2)]
    by auto
qed

lemma load_m_imp_load_m':
  assumes "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
          "s.mem s ! j = (m, sec)"
          "s.mem s' ! j = (m', sec)"
          "load m n off l = Some bs"
  shows "\<exists>bs'. load m' n off l = Some bs'"
  using assms load_size
  unfolding memory_public_agree_def
  by (metis fst_conv option.exhaust)

lemma load_packed_m_imp_load_packed_m':
  assumes "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
          "s.mem s ! j = (m, sec)"
          "s.mem s' ! j = (m', sec)"
          "load_packed sx m n off lp l = Some bs"
  shows "\<exists>bs'. load_packed sx m' n off lp l = Some bs'"
  using assms load_packed_size
  unfolding memory_public_agree_def
  by (metis fst_conv option.exhaust)

lemma store_m_imp_store_m':
  assumes "t_sec t = sec"
          "types_agree t v"
          "public_agree v v''"
          "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
          "s.mem s ! j = (m, sec)"
          "s.mem s' ! j = (m', sec)"
          "store m (nat_of_int k) off (bits v) (t_length t) = Some mem'"
   shows  "\<exists>mem''. store m' (nat_of_int k) off (bits v'') (t_length t) = Some mem'' \<and>
                   memory_public_agree (mem',sec) (mem'',sec)"
proof -
  obtain mem'' where store_def:"store m' (nat_of_int k) off (bits v'') (t_length t) = Some mem''"
    using store_size1 assms(4,5,6,7)
    unfolding memory_public_agree_def
    by (metis option.exhaust prod.sel(1))
  moreover
  have mem_eq:"mem_size mem' = mem_size mem''"
    using assms(4,5,6,7) store_size store_def
    unfolding memory_public_agree_def
    by simp metis
  have "memory_public_agree (mem',sec) (mem'',sec)"
  proof (cases sec)
    case Secret
    thus ?thesis
      using Secret mem_eq
      unfolding memory_public_agree_def
      by auto
  next
    case Public
    hence "v = v''"
      using assms(1,2,3)
      unfolding types_agree_def public_agree_def
      by fastforce
    thus ?thesis
      using assms(4,5,6,7) store_def mem_eq
      unfolding memory_public_agree_def
      by auto
  qed
  ultimately
  show ?thesis
    by blast
qed

lemma store_packed_m_imp_store_packed_m':
  assumes "t_sec t = sec"
          "types_agree t v"
          "public_agree v v''"
          "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
          "s.mem s ! j = (m, sec)"
          "s.mem s' ! j = (m', sec)"
          "store_packed m (nat_of_int k) off (bits v) (tp_length tp) = Some mem'"
   shows  "\<exists>mem''. store_packed m' (nat_of_int k) off (bits v'') (tp_length tp) = Some mem'' \<and>
                   memory_public_agree (mem',sec) (mem'',sec)"
proof -
  obtain mem'' where store_def:"store_packed m' (nat_of_int k) off (bits v'') (tp_length tp) = Some mem''"
    using store_packed_size1 assms(4,5,6,7)
    unfolding memory_public_agree_def
    by (metis option.exhaust prod.sel(1))
  moreover
  have mem_eq:"mem_size mem' = mem_size mem''"
    using assms(4,5,6,7) store_packed_size store_def
    unfolding memory_public_agree_def
    by simp metis
  have "memory_public_agree (mem',sec) (mem'',sec)"
  proof (cases sec)
    case Secret
    thus ?thesis
      using Secret mem_eq
      unfolding memory_public_agree_def
      by auto
  next
    case Public
    hence "v = v''"
      using assms(1,2,3)
      unfolding types_agree_def public_agree_def
      by fastforce
    thus ?thesis
      using assms(4,5,6,7) store_def mem_eq
      unfolding memory_public_agree_def
      by auto
  qed
  ultimately
  show ?thesis
    by blast
qed

lemma binop_i_secret_imp_binop_i_some:
  assumes "safe_binop_i iop"
  shows "\<exists>c. app_binop_i iop c1 c2 = Some c"
  using assms
proof (cases iop)
  case (Shr sx)
  thus ?thesis
  by (cases sx) (auto simp add: app_binop_i_def)
qed (auto simp add: safe_binop_i_def app_binop_i_def)

lemma cvtop_secret_imp_cvt_some:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v, $Cvtop t2 Convert t1 sx] : (ts _> ts')"
          "is_secret_t (typeof v)"
  shows "\<exists>v'. cvt t2 sx v = Some v'"
proof -
  have sec_agree:"typeof v = t1"
                 "t2 \<noteq> t1"
                 "t_sec t2 = t_sec t1"
                 "(sx = None) = (is_float_t t2 \<and> is_float_t t1 \<or> is_int_t t2 \<and> is_int_t t1 \<and> t_length t2 < t_length t1)"
    using typeof_cvtop[OF assms(1)]
    unfolding typeof_def
    by blast+
  have "(t1 = (T_i32 Secret) \<and> t2 = (T_i64 Secret)) \<or> (t1 = (T_i64 Secret) \<and> t2 = (T_i32 Secret))"
  proof -
    have ints:"is_int_t t2" "is_int_t t1"
      using sec_agree(1,3) assms(2) is_secret_int_t
      by auto
    show ?thesis
      using sec_agree(1,2,3) is_int_t_exists[OF ints(1)] is_int_t_exists[OF ints(2)] assms(2) t_sec_def
      by auto
  qed
  then consider (1) "t1 = (T_i32 Secret)" "t2 = (T_i64 Secret)" "\<exists>c. v = ConstInt32 Secret c"
              | (2) "t1 = (T_i64 Secret)" "t2 = (T_i32 Secret)" "\<exists>c. v = ConstInt64 Secret c"
    using typeof_i32 typeof_i64 sec_agree(1)
    unfolding public_agree_def
    by fastforce
  thus ?thesis
  proof cases
    case 1
    then obtain s where "sx = Some s"
      using sec_agree(4)
      unfolding is_int_t_def t_length_def is_float_t_def
      by auto
    thus ?thesis
      using 1
      unfolding cvt_def cvt_i64_def
      by (cases s) auto
  next
    case 2
    hence "sx = None"
      using sec_agree(4)
      unfolding is_int_t_def t_length_def
      by auto
    thus ?thesis
      using 2
      unfolding cvt_def cvt_i32_def
      by auto
  qed
qed

lemma publics_agree_imp_reduce_simple:
  assumes "\<lparr>es\<rparr> a\<leadsto> \<lparr>es_a\<rparr>"
          "exprs_public_agree es es'"
          "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts')"
          "trust_t \<C> = Untrusted"
  shows "\<exists>a' es'_a. \<lparr>es'\<rparr> a'\<leadsto> \<lparr>es'_a\<rparr> \<and> exprs_public_agree es_a es'_a \<and> (a \<sim>_a a')"
  using assms
proof (induction rule: reduce_simple.induct)
  case (unop_i32 sec' c sec iop)
  obtain v where v_def:"es' = [$C v, $Unop_i (T_i32 sec) iop]"
                       "public_agree (ConstInt32 sec' c) v"
    using exprs_public_agree_imp_publics_agree1_const1[OF unop_i32(1)]
    by (fastforce simp add: expr_public_agree.simps)
  have sec_agree:"sec' = sec"
    using typeof_unop_testop[OF unop_i32(2)]
    unfolding typeof_def
    by auto
  show ?case
  proof (cases sec)
    case Secret
    obtain c' where "v = ConstInt32 sec c'"
      using sec_agree v_def(2) public_agree_public_i32
      by blast
    moreover
    have "expr_public_agree ($C ConstInt32 sec (app_unop_i iop c)) ($C ConstInt32 sec (app_unop_i iop c'))"
      using t_sec_def Secret expr_public_agree.intros(2)[of "ConstInt32 sec (app_unop_i iop c)" "ConstInt32 sec (app_unop_i iop c')"]
      unfolding public_agree_def typeof_def
      by simp
    ultimately
    show ?thesis
      using v_def(1) reduce_simple.unop_i32 action_indistinguishable.intros(1)
      by fastforce
  next
    case Public
    hence "v = ConstInt32 sec c"
      using v_def(2) sec_agree
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using v_def(1) reduce_simple.unop_i32 exprs_public_agree_refl[of "[$C ConstInt32 sec (app_unop_i iop c)]"]
            action_indistinguishable.intros(1)
      by fastforce
  qed
next
  case (unop_i64 sec' c sec iop)
  obtain v where v_def:"es' = [$C v, $Unop_i (T_i64 sec) iop]"
                       "public_agree (ConstInt64 sec' c) v"
    using exprs_public_agree_imp_publics_agree1_const1[OF unop_i64(1)]
    by (fastforce simp add: expr_public_agree.simps)
  have sec_agree:"sec' = sec"
    using typeof_unop_testop[OF unop_i64(2)]
    unfolding typeof_def
    by auto
  show ?case
  proof (cases sec)
    case Secret
    obtain c' where "v = ConstInt64 sec c'"
      using sec_agree v_def(2) public_agree_public_i64
      by blast
    moreover
    have "expr_public_agree ($C ConstInt64 sec (app_unop_i iop c)) ($C ConstInt64 sec (app_unop_i iop c'))"
      using Secret expr_public_agree.intros(2)[of "ConstInt64 sec (app_unop_i iop c)" "ConstInt64 sec (app_unop_i iop c')"]
      unfolding public_agree_def typeof_def t_sec_def
      by simp
    ultimately
    show ?thesis
      using v_def(1) reduce_simple.unop_i64 action_indistinguishable.intros(1)
      by fastforce
  next
    case Public
    hence "v = ConstInt64 sec c"
      using v_def(2) sec_agree
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using v_def(1) reduce_simple.unop_i64 exprs_public_agree_refl[of "[$C ConstInt64 sec (app_unop_i iop c)]"]
            action_indistinguishable.intros(1)
      by fastforce
  qed
next
  case (unop_f32 c fop)
  obtain v where v_def:"es' = [$C v, $Unop_f T_f32 fop]"
                       "public_agree (ConstFloat32 c) v"
    using exprs_public_agree_imp_publics_agree1_const1[OF unop_f32(1)]
    by (fastforce simp add: expr_public_agree.simps)
  hence "v = ConstFloat32 c"
    using v_def(2)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using v_def(1) reduce_simple.unop_f32 exprs_public_agree_refl[of "[$C ConstFloat32 (app_unop_f fop c)]"]
          action_indistinguishable.intros(1)
    by fastforce
next
  case (unop_f64 c fop)
  obtain v where v_def:"es' = [$C v, $Unop_f T_f64 fop]"
                       "public_agree (ConstFloat64 c) v"
    using exprs_public_agree_imp_publics_agree1_const1[OF unop_f64(1)]
    by (fastforce simp add: expr_public_agree.simps)
  hence "v = ConstFloat64 c"
    using v_def(2)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using v_def(1) reduce_simple.unop_f64 exprs_public_agree_refl[of "[$C ConstFloat64 (app_unop_f fop c)]"]
          action_indistinguishable.intros(1)
    by fastforce
next
  case (binop_i32_Some iop c1 c2 c sec' sec'' sec)
  have is_safe:"sec' = sec" "sec'' = sec" "is_secret_t (T_i32 sec) \<Longrightarrow> safe_binop_i iop"
    using typeof_binop_relop[OF binop_i32_Some(3)]
    unfolding typeof_def
    by fastforce+
  then obtain c1' c2' where es'_def:"es' = [$C ConstInt32 sec c1', $C ConstInt32 sec c2', $Binop_i (T_i32 sec) iop]"
                                    "public_agree (ConstInt32 sec c1) (ConstInt32 sec c1')"
                                    "public_agree (ConstInt32 sec c2) (ConstInt32 sec c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_i32_Some(2)]
          expr_public_agree_refl[of "$Binop_i (T_i32 sec) iop"]
          public_agree_public_i32[of sec c1]
          public_agree_public_i32[of sec c2]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    then obtain c' where c_def:"app_binop_i iop c1' c2' = Some c'"
      using binop_i_secret_imp_binop_i_some typeof_binop_relop(3)[OF binop_i32_Some(3)]
      unfolding typeof_def t_sec_def
      by fastforce
    have abs_agree:"(Binop_i32_Some_action iop c1 c2) \<sim>_a (Binop_i32_Some_action iop c1' c2')"
      using is_safe(3) Secret t_sec_def
      by (simp add: action_indistinguishable.intros(2))
    thus ?thesis
      using reduce_simple.binop_i32_Some[OF c_def] es'_def(1) Secret
            expr_public_agree.intros(2)[of "ConstInt32 sec c" "ConstInt32 sec c'"]
      unfolding public_agree_def typeof_def t_sec_def
      by fastforce
  next
    case Public
    hence "c1 = c1'" "c2 = c2'"
      using es'_def(2,3)
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using es'_def(1) reduce_simple.binop_i32_Some[OF binop_i32_Some(1)]
            exprs_public_agree_refl[of "[$C ConstInt32 sec c]"] action_indistinguishable.intros(1)
      by fastforce
  qed
next
  case (binop_i32_None iop c1 c2 sec' sec'' sec)
  have "sec' = sec" "sec'' = sec" "is_secret_t (T_i32 sec) \<Longrightarrow> safe_binop_i iop"
    using typeof_binop_relop[OF binop_i32_None(3)]
    unfolding typeof_def
    by fastforce+
  then obtain c1' c2' where es'_def:"es' = [$C ConstInt32 sec c1', $C ConstInt32 sec c2', $Binop_i (T_i32 sec) iop]"
                                    "public_agree (ConstInt32 sec c1) (ConstInt32 sec c1')"
                                    "public_agree (ConstInt32 sec c2) (ConstInt32 sec c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_i32_None(2)]
          expr_public_agree_refl[of "$Binop_i (T_i32 sec) iop"]
          public_agree_public_i32[of sec c1]
          public_agree_public_i32[of sec c2]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    thus ?thesis
      using binop_i_secret_imp_binop_i_some[of iop c1 c2] typeof_binop_relop(3)[OF binop_i32_None(3)]
            binop_i32_None(1)
      unfolding typeof_def t_sec_def
      by fastforce
  next
    case Public
    hence "c1 = c1'" "c2 = c2'"
      using es'_def(2,3)
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using es'_def(1) reduce_simple.binop_i32_None[OF binop_i32_None(1)]
            exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
      by fastforce
  qed
next
  case (binop_i64_Some iop c1 c2 c sec' sec'' sec)
  have is_safe:"sec' = sec" "sec'' = sec" "is_secret_t (T_i64 sec) \<Longrightarrow> safe_binop_i iop"
    using typeof_binop_relop[OF binop_i64_Some(3)]
    unfolding typeof_def
    by fastforce+
  then obtain c1' c2' where es'_def:"es' = [$C ConstInt64 sec c1', $C ConstInt64 sec c2', $Binop_i (T_i64 sec) iop]"
                                    "public_agree (ConstInt64 sec c1) (ConstInt64 sec c1')"
                                    "public_agree (ConstInt64 sec c2) (ConstInt64 sec c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_i64_Some(2)]
          expr_public_agree_refl[of "$Binop_i (T_i64 sec) iop"]
          public_agree_public_i64[of sec c1]
          public_agree_public_i64[of sec c2]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    then obtain c' where c_def:"app_binop_i iop c1' c2' = Some c'"
      using binop_i_secret_imp_binop_i_some typeof_binop_relop(3)[OF binop_i64_Some(3)]
      unfolding typeof_def t_sec_def
      by fastforce
    have abs_agree:"(Binop_i64_Some_action iop c1 c2) \<sim>_a (Binop_i64_Some_action  iop c1' c2')"
      using is_safe(3) Secret t_sec_def
      by (simp add: action_indistinguishable.intros(3))
    thus ?thesis
      using reduce_simple.binop_i64_Some[OF c_def] es'_def(1) Secret
            expr_public_agree.intros(2)[of "ConstInt64 sec c" "ConstInt64 sec c'"]
      unfolding public_agree_def typeof_def t_sec_def
      by fastforce
  next
    case Public
    hence "c1 = c1'" "c2 = c2'"
      using es'_def(2,3)
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using es'_def(1) reduce_simple.binop_i64_Some[OF binop_i64_Some(1)]
            exprs_public_agree_refl[of "[$C ConstInt64 sec c]"] action_indistinguishable.intros(1)
      by fastforce
  qed
next
  case (binop_i64_None iop c1 c2 sec' sec'' sec)
  have "sec' = sec" "sec'' = sec" "is_secret_t (T_i64 sec) \<Longrightarrow> safe_binop_i iop"
    using typeof_binop_relop[OF binop_i64_None(3)]
    unfolding typeof_def
    by fastforce+
  then obtain c1' c2' where es'_def:"es' = [$C ConstInt64 sec c1', $C ConstInt64 sec c2', $Binop_i (T_i64 sec) iop]"
                                    "public_agree (ConstInt64 sec c1) (ConstInt64 sec c1')"
                                    "public_agree (ConstInt64 sec c2) (ConstInt64 sec c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_i64_None(2)]
          expr_public_agree_refl[of "$Binop_i (T_i64 sec) iop"]
          public_agree_public_i64[of sec c1]
          public_agree_public_i64[of sec c2]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    thus ?thesis
      using binop_i_secret_imp_binop_i_some[of iop c1 c2] typeof_binop_relop(3)[OF binop_i64_None(3)]
            binop_i64_None(1)
      unfolding typeof_def t_sec_def
      by fastforce
  next
    case Public
    hence "c1 = c1'" "c2 = c2'"
      using es'_def(2,3)
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using es'_def(1) reduce_simple.binop_i64_None[OF binop_i64_None(1)]
            exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
      by fastforce
  qed
next
  case (binop_f32_Some fop c1 c2 c)
  obtain c1' c2' where es'_def:"es' = [$C ConstFloat32 c1', $C ConstFloat32 c2', $Binop_f T_f32 fop]"
                                    "public_agree (ConstFloat32 c1) (ConstFloat32 c1')"
                                    "public_agree (ConstFloat32 c2) (ConstFloat32 c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_f32_Some(2)]
          expr_public_agree_refl[of "$Binop_f T_f32 fop"]
          public_agree_public_f32[of c1]
          public_agree_public_f32[of c2]
    unfolding typeof_def
    by (fastforce simp add: expr_public_agree.simps)
  hence "c1 = c1'" "c2 = c2'"
    using es'_def(2,3)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using es'_def(1) reduce_simple.binop_f32_Some[OF binop_f32_Some(1)]
          exprs_public_agree_refl[of "[$C ConstFloat32 c]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (binop_f32_None fop c1 c2)
  obtain c1' c2' where es'_def:"es' = [$C ConstFloat32 c1', $C ConstFloat32 c2', $Binop_f T_f32 fop]"
                                    "public_agree (ConstFloat32 c1) (ConstFloat32 c1')"
                                    "public_agree (ConstFloat32 c2) (ConstFloat32 c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_f32_None(2)]
          expr_public_agree_refl[of "$Binop_f T_f32 fop"]
          public_agree_public_f32[of c1]
          public_agree_public_f32[of c2]
    unfolding typeof_def
    by (fastforce simp add: expr_public_agree.simps)
  hence "c1 = c1'" "c2 = c2'"
    using es'_def(2,3)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using es'_def(1) reduce_simple.binop_f32_None[OF binop_f32_None(1)]
          exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (binop_f64_Some fop c1 c2 c)
  then obtain c1' c2' where es'_def:"es' = [$C ConstFloat64 c1', $C ConstFloat64 c2', $Binop_f T_f64 fop]"
                                    "public_agree (ConstFloat64 c1) (ConstFloat64 c1')"
                                    "public_agree (ConstFloat64 c2) (ConstFloat64 c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_f64_Some(2)]
          expr_public_agree_refl[of "$Binop_f T_f64 fop"]
          public_agree_public_f64[of c1]
          public_agree_public_f64[of c2]
    unfolding typeof_def
    by (fastforce simp add: expr_public_agree.simps)
  hence "c1 = c1'" "c2 = c2'"
    using es'_def(2,3)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using es'_def(1) reduce_simple.binop_f64_Some[OF binop_f64_Some(1)]
          exprs_public_agree_refl[of "[$C ConstFloat64 c]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (binop_f64_None fop c1 c2)
  then obtain c1' c2' where es'_def:"es' = [$C ConstFloat64 c1', $C ConstFloat64 c2', $Binop_f T_f64 fop]"
                                    "public_agree (ConstFloat64 c1) (ConstFloat64 c1')"
                                    "public_agree (ConstFloat64 c2) (ConstFloat64 c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF binop_f64_None(2)]
          expr_public_agree_refl[of "$Binop_f T_f64 fop"]
          public_agree_public_f64[of c1]
          public_agree_public_f64[of c2]
    unfolding typeof_def
    by (fastforce simp add: expr_public_agree.simps)
  hence "c1 = c1'" "c2 = c2'"
    using es'_def(2,3)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using es'_def(1) reduce_simple.binop_f64_None[OF binop_f64_None(1)]
          exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (testop_i32 sec' c sec testop)
  obtain v where v_def:"es' = [$C v, $Testop (T_i32 sec) testop]"
                       "public_agree (ConstInt32 sec' c) v"
    using exprs_public_agree_imp_publics_agree1_const1[OF testop_i32(1)]
    by (fastforce simp add: expr_public_agree.simps)
  have sec_agree:"sec' = sec"
    using typeof_unop_testop[OF testop_i32(2)]
    unfolding typeof_def
    by auto
  show ?case
  proof (cases sec)
    case Secret
    obtain c' where "v = ConstInt32 sec c'"
      using sec_agree v_def(2) public_agree_public_i32
      by blast
    moreover
    have "expr_public_agree ($C ConstInt32 sec (wasm_bool (app_testop_i testop c))) ($C ConstInt32 sec (wasm_bool (app_testop_i testop c')))"
      using Secret expr_public_agree.intros(2)
      unfolding public_agree_def typeof_def t_sec_def
      by simp
    ultimately
    show ?thesis
      using v_def(1) reduce_simple.testop_i32 action_indistinguishable.intros(1)
      by fastforce
  next
    case Public
    hence "v = ConstInt32 sec c"
      using v_def(2) sec_agree
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using v_def(1) reduce_simple.testop_i32 action_indistinguishable.intros(1)
            exprs_public_agree_refl[of "[$C ConstInt32 sec (wasm_bool (app_testop_i testop c))]"]
      by fastforce
  qed
next
  case (testop_i64 sec' c sec testop)
  obtain v where v_def:"es' = [$C v, $Testop (T_i64 sec) testop]"
                       "public_agree (ConstInt64 sec' c) v"
    using exprs_public_agree_imp_publics_agree1_const1[OF testop_i64(1)]
    by (fastforce simp add: expr_public_agree.simps)
  have sec_agree:"sec' = sec"
    using typeof_unop_testop[OF testop_i64(2)]
    unfolding typeof_def
    by auto
  show ?case
  proof (cases sec)
    case Secret
    obtain c' where "v = ConstInt64 sec c'"
      using sec_agree v_def(2) public_agree_public_i64
      by blast
    moreover
    have "expr_public_agree ($C ConstInt32 sec (wasm_bool (app_testop_i testop c))) ($C ConstInt32 sec (wasm_bool (app_testop_i testop c')))"
      using Secret expr_public_agree.intros(2)
      unfolding public_agree_def typeof_def t_sec_def
      by simp
    ultimately
    show ?thesis
      using v_def(1) reduce_simple.testop_i64 action_indistinguishable.intros(1)
      by fastforce
  next
    case Public
    hence "v = ConstInt64 sec c"
      using v_def(2) sec_agree
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using v_def(1) reduce_simple.testop_i64 action_indistinguishable.intros(1)
            exprs_public_agree_refl[of "[$C ConstInt32 sec (wasm_bool (app_testop_i testop c))]"]
      by fastforce
  qed
next
  case (relop_i32 sec' c1 sec'' c2 sec iop)
  have "sec' = sec" "sec'' = sec"
    using typeof_binop_relop[OF relop_i32(2)]
    unfolding typeof_def
    by fastforce+
  then obtain c1' c2' where es'_def:"es' = [$C ConstInt32 sec c1', $C ConstInt32 sec c2', $Relop_i (T_i32 sec) iop]"
                                    "public_agree (ConstInt32 sec c1) (ConstInt32 sec c1')"
                                    "public_agree (ConstInt32 sec c2) (ConstInt32 sec c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF relop_i32(1)]
          expr_public_agree_refl[of "$Relop_i (T_i32 sec) iop"]
          public_agree_public_i32[of sec c1]
          public_agree_public_i32[of sec c2]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    hence "public_agree (ConstInt32 sec (wasm_bool (app_relop_i iop c1 c2))) (ConstInt32 sec (wasm_bool (app_relop_i iop c1' c2')))"
      unfolding public_agree_def typeof_def t_sec_def
      by fastforce
    thus ?thesis
      using reduce_simple.relop_i32 es'_def(1) Secret  expr_public_agree.intros(2)
            action_indistinguishable.intros(1)
      by fastforce
  next
    case Public
    hence "c1 = c1'" "c2 = c2'"
      using es'_def(2,3)
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using es'_def(1) reduce_simple.relop_i32 action_indistinguishable.intros(1)
            exprs_public_agree_refl[of "[$C ConstInt32 sec (wasm_bool (app_relop_i iop c1 c2))]"]
      by fastforce
  qed
next
  case (relop_i64 sec' c1 sec'' c2 sec iop)
  have "sec' = sec" "sec'' = sec"
    using typeof_binop_relop[OF relop_i64(2)]
    unfolding typeof_def
    by fastforce+
  then obtain c1' c2' where es'_def:"es' = [$C ConstInt64 sec c1', $C ConstInt64 sec c2', $Relop_i (T_i64 sec) iop]"
                                    "public_agree (ConstInt64 sec c1) (ConstInt64 sec c1')"
                                    "public_agree (ConstInt64 sec c2) (ConstInt64 sec c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF relop_i64(1)]
          expr_public_agree_refl[of "$Relop_i (T_i64 sec) iop"]
          public_agree_public_i64[of sec c1]
          public_agree_public_i64[of sec c2]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    hence "public_agree (ConstInt32 sec (wasm_bool (app_relop_i iop c1 c2))) (ConstInt32 sec (wasm_bool (app_relop_i iop c1' c2')))"
      unfolding public_agree_def typeof_def t_sec_def
      by fastforce
    thus ?thesis
      using reduce_simple.relop_i64 es'_def(1) Secret  expr_public_agree.intros(2)
            action_indistinguishable.intros(1)
      by fastforce
  next
    case Public
    hence "c1 = c1'" "c2 = c2'"
      using es'_def(2,3)
      unfolding public_agree_def typeof_def t_sec_def
      by auto
    thus ?thesis
      using es'_def(1) reduce_simple.relop_i64 action_indistinguishable.intros(1)
            exprs_public_agree_refl[of "[$C ConstInt32 sec (wasm_bool (app_relop_i iop c1 c2))]"]
      by fastforce
  qed
next
  case (relop_f32 c1 c2 fop)
  then obtain c1' c2' where es'_def:"es' = [$C ConstFloat32 c1', $C ConstFloat32 c2', $Relop_f T_f32 fop]"
                                    "public_agree (ConstFloat32 c1) (ConstFloat32 c1')"
                                    "public_agree (ConstFloat32 c2) (ConstFloat32 c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF relop_f32(1)]
          expr_public_agree_refl[of "$Relop_f T_f32 fop"]
          public_agree_public_f32[of c1]
          public_agree_public_f32[of c2]
    by (fastforce simp add: expr_public_agree.simps)
  hence "c1 = c1'" "c2 = c2'"
    using es'_def(2,3)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using es'_def(1) reduce_simple.relop_f32 action_indistinguishable.intros(1)
          exprs_public_agree_refl[of "[$C ConstInt32 Public (wasm_bool (app_relop_f fop c1 c2))]"]
    by fastforce
next
  case (relop_f64 c1 c2 fop)
  then obtain c1' c2' where es'_def:"es' = [$C ConstFloat64 c1', $C ConstFloat64 c2', $Relop_f T_f64 fop]"
                                    "public_agree (ConstFloat64 c1) (ConstFloat64 c1')"
                                    "public_agree (ConstFloat64 c2) (ConstFloat64 c2')"
    using exprs_public_agree_imp_publics_agree1_const2[OF relop_f64(1)]
          expr_public_agree_refl[of "$Relop_f T_f64 fop"]
          public_agree_public_f64[of c1]
          public_agree_public_f64[of c2]
    by (fastforce simp add: expr_public_agree.simps)
  hence "c1 = c1'" "c2 = c2'"
    using es'_def(2,3)
    unfolding public_agree_def typeof_def t_sec_def
    by auto
  thus ?case
    using es'_def(1) reduce_simple.relop_f64 action_indistinguishable.intros(1)
          exprs_public_agree_refl[of "[$C ConstInt32 Public (wasm_bool (app_relop_f fop c1 c2))]"]
    by fastforce
next
  case (convert_Some t1 v t2 sx v')
  obtain v'' where v_def:"es' = [$C v'', $Cvtop t2 Convert t1 sx]"
                         "public_agree v v''"
    using exprs_public_agree_imp_publics_agree1_const1[OF convert_Some(3)]
    by (fastforce simp add: expr_public_agree.simps)
  have sec_agree:"typeof v = t1"
                 "t2 \<noteq> t1"
                 "t_sec t2 = t_sec t1"
                 "(sx = None) = (is_float_t t2 \<and> is_float_t t1 \<or> is_int_t t2 \<and> is_int_t t1 \<and> t_length t2 < t_length t1)"
    using typeof_cvtop[OF convert_Some(4)]
    unfolding typeof_def
    by blast+
  show ?case
  proof (cases "t_sec (typeof v)")
    case Secret
    have "\<S>\<bullet>\<C> \<turnstile> [$C v'', $Cvtop t2 Convert t1 sx] : (ts _> ts')"
      using e_typing_s_typing.intros(1)
            exprs_public_agree_imp_b_e_typing[OF unlift_b_e[of _ _ "[C v, Cvtop t2 Convert t1 sx]"]]
            v_def(1) convert_Some(3,4)
      by (metis to_e_list_2)
    hence "\<exists>v'''. cvt t2 sx v'' = Some v'''"
      using cvtop_secret_imp_cvt_some Secret public_agree_imp_typeof[OF v_def(2)]
      by fastforce
    then obtain v''' where v'''_def:"cvt t2 sx v'' = Some v'''"
      by blast
    hence "exprs_public_agree [($C v')] [($C v''')]"
      using t_cvt convert_Some(2) sec_agree(1,3) Secret expr_public_agree.intros(2)
      unfolding public_agree_def
      by simp
    thus ?thesis
      using reduce_simple.convert_Some[OF _ v'''_def] v_def(1) action_indistinguishable.intros(7)
            public_agree_imp_types_agree_insecure[OF convert_Some(1)]
      by (metis Secret is_secret_int_t sec_agree(1,3) types_agree_def v_def(2))
  next
    case Public
    hence "v'' = v"
      using v_def(2)
      unfolding public_agree_def
      by fastforce
    thus ?thesis
      using convert_Some(1,2) v_def(1) exprs_public_agree_refl reduce_simple.convert_Some
            action_indistinguishable.intros(1)
      by blast
  qed
next
  case (convert_None t1 v t2 sx)
  obtain v'' where v_def:"es' = [$C v'', $Cvtop t2 Convert t1 sx]"
                         "public_agree v v''"
    using exprs_public_agree_imp_publics_agree1_const1[OF convert_None(3)]
    by (fastforce simp add: expr_public_agree.simps)
  have sec_agree:"typeof v = t1"
                 "t2 \<noteq> t1"
                 "t_sec t2 = t_sec t1"
                 "(sx = None) = (is_float_t t2 \<and> is_float_t t1 \<or> is_int_t t2 \<and> is_int_t t1 \<and> t_length t2 < t_length t1)"
    using typeof_cvtop[OF convert_None(4)]
    unfolding typeof_def
    by blast+
  show ?case
  proof (cases "t_sec (typeof v)")
    case Secret
    thus ?thesis
      using cvtop_secret_imp_cvt_some[OF convert_None(4)] Secret convert_None(2)
      by fastforce
  next
    case Public
    hence "v'' = v"
      using v_def(2)
      unfolding public_agree_def
      by fastforce
    thus ?thesis
      using convert_None(1,2) v_def(1) exprs_public_agree_refl reduce_simple.convert_None
            action_indistinguishable.intros(1)
      by blast
  qed
next
  case (reinterpret t1 v t2)
  obtain v'' where v_def:"es' = [$C v'', $Cvtop t2 Reinterpret t1 None]"
                         "public_agree v v''"
    using exprs_public_agree_imp_publics_agree1_const1[OF reinterpret(2)]
    by (fastforce simp add: expr_public_agree.simps)
  have typeof_v:"typeof v = t1" "t2 \<noteq> t1" "t_sec t2 = t_sec t1" "t_length t2 = t_length t1"
    using typeof_cvtop(1,3)[OF reinterpret(3)]
    by blast+
  thus ?case
  proof (cases "t_sec (typeof v'')")
    case Secret
    hence "exprs_public_agree [$C wasm_deserialise (bits v) t2] [$C wasm_deserialise (bits v'') t2]"
      using wasm_deserialise_type[of _ t2]  expr_public_agree.intros(2) typeof_v(1,3)
            public_agree_imp_typeof[OF v_def(2)]
      unfolding public_agree_def
      by auto
    thus ?thesis
      using v_def reduce_simple.reinterpret reinterpret(1) public_agree_imp_types_agree_insecure
            action_indistinguishable.intros(1)
      by blast
  next
    case Public
    hence "v = v''"
      using v_def(2)
      unfolding public_agree_def
      by auto
    thus ?thesis
      using v_def(1) reduce_simple.reinterpret reinterpret(1) action_indistinguishable.intros(1)
            exprs_public_agree_refl[of "[$C wasm_deserialise (bits v) t2]"]
      by blast
  qed
next
  case (classify t1 v t2)
  obtain v'' where v_def:"es' = [$C v'', $Cvtop t2 Classify t1 None]"
                         "public_agree v v''"
    using exprs_public_agree_imp_publics_agree1_const1[OF classify(2)]
    by (fastforce simp add: expr_public_agree.simps)
  have typeof_v:"typeof v = t1" "is_int_t t1" "is_public_t t1" "classify_t t1 = t2"
    using typeof_cvtop(1,4)[OF classify(3)]
    by blast+
  thus ?case
  proof (cases "t_sec (typeof v'')")
    case Secret
    thus ?thesis
      using typeof_v(1,3) v_def(2) public_agree_imp_typeof
      by auto
  next
    case Public
    hence "v = v''"
      using v_def(2)
      unfolding public_agree_def
      by auto
    thus ?thesis
      using v_def(1) reduce_simple.classify classify(1) action_indistinguishable.intros(1)
            exprs_public_agree_refl[of "[$C classify v]"]
      by blast
  qed
next
  case (declassify t1 v t2)
  show ?case
    using typeof_cvtop(5)[OF declassify(3)] declassify(4)
    by fastforce
next
  case unreachable
  thus ?case
    using reduce_simple.unreachable exprs_public_agree_imp_publics_agree1_const0[OF unreachable(1)]
          action_indistinguishable.intros(1)
    by (fastforce simp add: expr_public_agree.simps)
next
  case nop
  thus ?case
    using reduce_simple.nop exprs_public_agree_imp_publics_agree1_const0[OF nop(1)]
          action_indistinguishable.intros(1)
    by (fastforce simp add: expr_public_agree.simps)
next
  case (drop v)
  obtain v'' where v_def:"es' = [$C v'', $Drop]"
                         "public_agree v v''"
    using exprs_public_agree_imp_publics_agree1_const1[OF drop(1)]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.drop action_indistinguishable.intros(1)
    by blast
next
  case (select_false n v1 v2 sec sec')
  then obtain v1' v2' n' where es'_def:"es' = [$C v1', $C v2', $C ConstInt32 sec n', $Select sec]"
                                       "public_agree v1 v1'"
                                       "public_agree v2 v2'"
                                       "public_agree (ConstInt32 sec n) (ConstInt32 sec n')"
                                       "sec = sec'"
                                       "typeof v1 = typeof v2"
                                       "sec = Secret \<longrightarrow> is_secret_t (typeof v1)"
                                       "sec = Secret \<longrightarrow> is_secret_t (typeof v2)"
    using exprs_public_agree_imp_publics_agree1_const3[OF select_false(2)]
          typeof_select[OF select_false(3)] public_agree_public_i32
    unfolding typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    hence v2_v1':"public_agree v2 v1'"
      using es'_def(2,6,7,8) public_agree_def
      by auto
    thus ?thesis
      using reduce_simple.select_false
            reduce_simple.select_true
            expr_public_agree.intros(2)
            action_indistinguishable.intros(1)
            es'_def(1,3)
      by (metis Secret action_indistinguishable.select es'_def(5) expr_public_agree_imp_expr_publics_agree)
  next
    case Public
    hence "n = n'"
      using es'_def(4)
      unfolding public_agree_def typeof_def t_sec_def
      by simp
    thus ?thesis
      using reduce_simple.select_false[OF select_false(1)] expr_public_agree.intros(2)
            action_indistinguishable.intros(1) es'_def(1,3,5)
      by fastforce
  qed
next
  case (select_true n v1 v2 sec sec')
  then obtain v1' v2' n' where es'_def:"es' = [$C v1', $C v2', $C ConstInt32 sec n', $Select sec]"
                                       "public_agree v1 v1'"
                                       "public_agree v2 v2'"
                                       "public_agree (ConstInt32 sec n) (ConstInt32 sec n')"
                                       "sec = sec'"
                                       "typeof v1 = typeof v2"
                                       "sec = Secret \<longrightarrow> is_secret_t (typeof v1)"
                                       "sec = Secret \<longrightarrow> is_secret_t (typeof v2)"
    using exprs_public_agree_imp_publics_agree1_const3[OF select_true(2)]
          typeof_select[OF select_true(3)] public_agree_public_i32
    unfolding typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
  proof (cases sec)
    case Secret
    hence v2_v1':"public_agree v1 v2'"
      using es'_def(3,6,7,8) public_agree_def
      by auto
    thus ?thesis
      using reduce_simple.select_false
            reduce_simple.select_true
            expr_public_agree.intros(2)
            action_indistinguishable.intros(1)
            es'_def(1,2)
      by (metis Secret action_indistinguishable.select es'_def(5) expr_public_agree_imp_expr_publics_agree)
  next
    case Public
    hence "n = n'"
      using es'_def(4)
      unfolding public_agree_def typeof_def t_sec_def
      by simp
    thus ?thesis
      using reduce_simple.select_true[OF select_true(1)] expr_public_agree.intros(2)
            action_indistinguishable.intros(1) es'_def(1,2,5)
      by fastforce
  qed
next
  case (block vs n t1s t2s m es)
  obtain vs' e where es'_def:"es' = (vs' @ [e])"
                             "exprs_public_agree vs vs'"
                             "expr_public_agree ($Block (t1s _> t2s) es) e"
                             "const_list vs'"
    using block(1,5) list_all2_append1[of expr_public_agree vs "[($Block (t1s _> t2s) es)]"]
          exprs_public_agree_const_list
    by (metis exprs_public_agree_imp_publics_agree1_const0)
  then obtain bes where e_def:"e = ($Block (t1s _> t2s) bes)"
                              "exprs_public_agree ($*es) ($*bes)"
    using exprs_public_agree_refl
    unfolding expr_public_agree.simps[of "($Block (t1s _> t2s) es)" e]
    by auto
  have "exprs_public_agree [Label m [] (vs @ ($* es))] [Label m [] (vs' @ ($* bes))]"
    using expr_public_agree.intros(6) exprs_public_agree_refl[of "[]"]
          es'_def(2) e_def(2)
    by (simp add: list_all2_appendI)
  thus ?case
    using reduce_simple.block[OF es'_def(4) _ block(3,4)] block(2) es'_def(1) list_all2_lengthD[OF es'_def(2)]
          e_def(1) action_indistinguishable.intros(1)
    by fastforce
next
  case (loop vs n t1s t2s m es)
  obtain vs' e where es'_def:"es' = (vs' @ [e])"
                             "exprs_public_agree vs vs'"
                             "expr_public_agree ($Loop (t1s _> t2s) es) e"
                             "const_list vs'"
    using loop(1,5) list_all2_append1[of expr_public_agree vs "[($Loop (t1s _> t2s) es)]"]
          exprs_public_agree_const_list
    by (metis exprs_public_agree_imp_publics_agree1_const0)
  then obtain bes where e_def:"e = ($Loop (t1s _> t2s) bes)"
                              "exprs_public_agree ($*es) ($*bes)"
    using exprs_public_agree_refl
    unfolding expr_public_agree.simps[of "($Loop (t1s _> t2s) es)" e]
    by auto
  have "exprs_public_agree [Label n [$Loop (t1s _> t2s) es] (vs @ ($* es))]
                             [Label n [$Loop (t1s _> t2s) bes] (vs' @ ($* bes))]"
    using expr_public_agree.intros(6)[OF _ list_all2_appendI[OF es'_def(2) e_def(2)]]
          es'_def(3) e_def(1)
    by fastforce
  thus ?case
    using reduce_simple.loop[OF es'_def(4) _ loop(3,4)] loop(2) es'_def(1) list_all2_lengthD[OF es'_def(2)]
          e_def(1) action_indistinguishable.intros(1)
    by fastforce
next
  case (if_false n sec tf e1s e2s)
  have "sec = Public"
    using typeof_if[OF if_false(3)]
    by -
  then obtain e where es'_def:"es' = [$C ConstInt32 sec n, e]"
                              "expr_public_agree ($If tf e1s e2s) e"
    using exprs_public_agree_imp_publics_agree1_const1[OF if_false(2)]
    unfolding public_agree_def typeof_def t_sec_def
    by fastforce
  moreover
  then obtain e1s' e2s' where e_def:"e = ($If tf e1s' e2s')"
                                    "exprs_public_agree ($*e1s) ($*e1s')"
                                    "exprs_public_agree ($*e2s) ($*e2s')"
    using exprs_public_agree_refl
    unfolding expr_public_agree.simps[of "($If tf e1s e2s)"]
    by fastforce
  moreover
  have "exprs_public_agree [$Block tf e2s] [$Block tf e2s']"
    using expr_public_agree.intros(3)[OF e_def(3)]
    by simp
  ultimately
  show ?case
    using reduce_simple.if_false if_false(1) action_indistinguishable.intros(1)
    by fastforce
next
  case (if_true n sec tf e1s e2s)
  have "sec = Public"
    using typeof_if[OF if_true(3)]
    by -
  then obtain e where es'_def:"es' = [$C ConstInt32 sec n, e]"
                              "expr_public_agree ($If tf e1s e2s) e"
    using exprs_public_agree_imp_publics_agree1_const1[OF if_true(2)]
    unfolding public_agree_def typeof_def t_sec_def
    by fastforce
  moreover
  then obtain e1s' e2s' where e_def:"e = ($If tf e1s' e2s')"
                                    "exprs_public_agree ($*e1s) ($*e1s')"
                                    "exprs_public_agree ($*e2s) ($*e2s')"
    using exprs_public_agree_refl
    unfolding expr_public_agree.simps[of "($If tf e1s e2s)"]
    by fastforce
  moreover
  have "exprs_public_agree [$Block tf e1s] [$Block tf e1s']"
    using expr_public_agree.intros(3)[OF e_def(2)]
    by simp
  ultimately
  show ?case
    using reduce_simple.if_true if_true(1) action_indistinguishable.intros(1)
    by fastforce
next
  case (label_const vs n les)
  obtain les' vs' where "es' = [Label n les' vs']"
                   "exprs_public_agree les les'"
                   "exprs_public_agree vs vs'"
    using expr_public_agree_label exprs_public_agree_imp_publics_agree1_const0[OF label_const(2)]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.label_const exprs_public_agree_const_list[OF _ label_const(1)]
          action_indistinguishable.intros(1)
    by fastforce
next
  case (label_trap n les)
  obtain les' where "es' = [Label n les' [Trap]]"
                   "exprs_public_agree les les'"
    using expr_public_agree_label exprs_public_agree_imp_publics_agree1_const0[OF label_trap(1)]
          exprs_public_agree_imp_publics_agree1_const0[of Trap]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.label_trap exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (br vs n i lholed LI es)
  obtain les LI' where es'_def:"es' = [Label n les LI']"
                                "exprs_public_agree es les"
                                "exprs_public_agree LI LI'"
    using expr_public_agree_local exprs_public_agree_imp_publics_agree1_const0[OF br(4)]
    by (fastforce simp add: expr_public_agree.simps)
  obtain lholed' vs' where les_def:"Lfilled i lholed' (vs' @ [$Br i]) LI'"
                                   "lholed_public_agree lholed lholed'"
                                   "exprs_public_agree vs vs'"
    using exprs_public_agree_imp_lholed_public_agree[OF br(3) es'_def(3)]
          exprs_public_agree_imp_publics_agree1_const0[of "$Br i"]
    unfolding list_all2_append1[of expr_public_agree vs "[$Br i]"]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
    using reduce_simple.br[OF _ _ les_def(1)] les_def(3) br(1,2)
          exprs_public_agree_const_list[OF les_def(3)] es'_def(1,2)
          list_all2_lengthD[OF les_def(3)] list_all2_appendI action_indistinguishable.intros(1)
    by fastforce
next
  case (br_if_false n sec i)
  have "sec = Public"
    using typeof_br_if[OF br_if_false(3)]
    by -
  hence es'_def:"es' = [$C ConstInt32 sec n, ($Br_if i)]"
    using exprs_public_agree_imp_publics_agree1_const1[OF br_if_false(2)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.br_if_false[OF br_if_false(1)] action_indistinguishable.intros(1)
    by blast
next
  case (br_if_true n sec i)
  have "sec = Public"
    using typeof_br_if[OF br_if_true(3)]
    by -
  hence es'_def:"es' = [$C ConstInt32 sec n, ($Br_if i)]"
    using exprs_public_agree_imp_publics_agree1_const1[OF br_if_true(2)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.br_if_true[OF br_if_true(1)] expr_public_agree.intros(1)
          action_indistinguishable.intros(1)
    by blast
next
  case (br_table "is" c sec i')
  have "sec = Public"
    using typeof_br_table[OF br_table(3)]
    by -
  hence es'_def:"es' = [$C ConstInt32 sec c, ($Br_table is i')]"
    using exprs_public_agree_imp_publics_agree1_const1[OF br_table(2)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.br_table[OF br_table(1)] expr_public_agree.intros(1)
          action_indistinguishable.intros(1)
    by blast
next
  case (br_table_length"is" c sec i')
  have "sec = Public"
    using typeof_br_table[OF br_table_length(3)]
    by -
  hence es'_def:"es' = [$C ConstInt32 sec c, ($Br_table is i')]"
    using exprs_public_agree_imp_publics_agree1_const1[OF br_table_length(2)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.br_table_length[OF br_table_length(1)] expr_public_agree.intros(1)
          action_indistinguishable.intros(1)
    by blast
next
  case (local_const es n i vs)
  obtain vs' ves where "es' = [Local n i vs' ves]"
                   "exprs_public_agree es ves"
                   "publics_agree vs vs'"
    using expr_public_agree_local exprs_public_agree_imp_publics_agree1_const0[OF local_const(3)]
    by fastforce
  thus ?case
    using reduce_simple.local_const exprs_public_agree_const_list[OF _ local_const(1)]
          local_const(2) list_all2_lengthD action_indistinguishable.intros(1)
    by fastforce
next
  case (local_trap n i vs)
  obtain vs' where "es' = [Local n i vs' [Trap]]"
                   "publics_agree vs vs'"
    using expr_public_agree_local exprs_public_agree_imp_publics_agree1_const0[OF local_trap(1)]
          exprs_public_agree_imp_publics_agree1_const0[of Trap]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce_simple.local_trap exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (return vs n j lholed es i vls)
  obtain vls' les where es'_def:"es' = [Local n i vls' les]"
                                "publics_agree vls vls'"
                                "exprs_public_agree es les"
    using expr_public_agree_local exprs_public_agree_imp_publics_agree1_const0[OF return(4)]
    by (fastforce simp add: expr_public_agree.simps)
  obtain lholed' vs' where les_def:"Lfilled j lholed' (vs' @ [$Return]) les"
                                   "lholed_public_agree lholed lholed'"
                                   "exprs_public_agree vs vs'"
    using exprs_public_agree_imp_lholed_public_agree[OF return(3) es'_def(3)]
          exprs_public_agree_imp_publics_agree1_const0[of "$Return"]
    unfolding list_all2_append1[of expr_public_agree vs "[$Return]"]
    by (fastforce simp add: expr_public_agree.simps)
  show ?case
    using reduce_simple.return[OF _ _ les_def(1)] les_def(3) return(1,2)
          exprs_public_agree_const_list[OF les_def(3)] es'_def(1)
          list_all2_lengthD[OF les_def(3)] action_indistinguishable.intros(1)
    by fastforce
next
  case (tee_local v i)
  obtain v'' where v_def:"es' = [v'', ($Tee_local i)]"
                         "expr_public_agree v v''"
    using tee_local(2) list_all2_Cons1[of expr_public_agree]
    by (fastforce simp add: expr_public_agree.simps[of "$Tee_local i"])
  thus ?case
    using reduce_simple.tee_local expr_public_agree_const[OF v_def(2) tee_local(1)]
          expr_public_agree_refl action_indistinguishable.intros(1)
    by fastforce
next
  case (trap es lholed)
  have "es' \<noteq> [Trap]"
  proof -
    {
      assume "es' = [Trap]"
      hence False
        using trap(1,3) exprs_public_agree_imp_publics_agree1_const0[OF exprs_public_agree_symm]
        by (fastforce simp add: expr_public_agree.simps[of Trap])
    }
    thus ?thesis
      by blast
  qed
  moreover
  thus ?case
    using exprs_public_agree_imp_lholed_public_agree[OF trap(2,3)] action_indistinguishable.intros(1)
          reduce_simple.trap exprs_public_agree_trap_imp_is_trap
    by fastforce
qed

lemma exprs_public_agree_imp_reduce:
  assumes "\<lparr>s;vs;es\<rparr> a\<leadsto>_ i \<lparr>s_a;vs_a;es_a\<rparr>"
          "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
          "store_typing s \<S>"
          "tvs = map typeof vs"
          "i < length (inst s)"
          "\<C> = ((s_inst \<S>)!i)\<lparr>trust_t := Untrusted, local := (local ((s_inst \<S>)!i) @ tvs), label := arb_labs, return := arb_return\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "\<exists>a' s'_a vs'_a es'_a. \<lparr>s';vs';es'\<rparr> a'\<leadsto>_ i \<lparr>s'_a;vs'_a;es'_a\<rparr> \<and>
                               exprs_public_agree es_a es'_a \<and>
                               publics_agree vs_a vs'_a \<and>
                               store_public_agree s_a s'_a \<and>
                               (a \<sim>_a a')"
  using assms assms(1)
proof (induction arbitrary: s' vs' es' arb_labs arb_return ts ts' tvs \<C> rule: reduce.induct)
  case (basic e a e' s vs i)
  show ?case
    using publics_agree_imp_reduce_simple[OF basic(1,2,9)]
          reduce.intros(1)[of es' _ _ s' vs'] basic(3,4,8)
    by fastforce
next
  case (call s vs j i)
  have "es' = [$Call j]"
    using call(1)
    by (simp add: list_all2_Cons1 expr_public_agree.simps)
  hence "\<lparr>s';vs';es'\<rparr> Call_action\<leadsto>_i \<lparr>s';vs';[Callcl (sfunc s' i j)]\<rparr>"
    using reduce.intros(2)
    by blast
  thus ?case
    using call(2,3) store_public_agree_sfunc_eq exprs_public_agree_refl[of "[Callcl (sfunc s i j)]"]
          action_indistinguishable.intros(1)
    by fastforce
next
  case (call_indirect_Some s i c cl j tf vs sec)
  hence "sec = Public"
    using types_preserved_call_indirect_None(2)
    by blast
  hence "es' = [$C ConstInt32 Public c, $Call_indirect j]"
    using exprs_public_agree_imp_publics_agree1_const1[OF call_indirect_Some(4)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  hence "\<lparr>s';vs';es'\<rparr> (Call_indirect_Some_action c)\<leadsto>_i \<lparr>s';vs';[Callcl cl]\<rparr>"
    using reduce.intros(3)[OF _ _ call_indirect_Some(3)] call_indirect_Some(1,2,6)
          store_public_agree_stab_eq store_public_agree_stypes_eq
    by fastforce
  thus ?case
    using call_indirect_Some(5,6) store_public_agree_sfunc_eq exprs_public_agree_refl[of "[Callcl cl]"]
          action_indistinguishable.intros(1)
    by fastforce
next
  case (call_indirect_None s i c cl j vs sec)
  hence "sec = Public"
    using types_preserved_call_indirect_None(2)
    by blast
  hence "es' = [$C ConstInt32 Public c, $Call_indirect j]"
    using exprs_public_agree_imp_publics_agree1_const1[OF call_indirect_None(2)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  hence "\<lparr>s';vs';es'\<rparr>  (Call_indirect_None_action c)\<leadsto>_i \<lparr>s';vs';[Trap]\<rparr>"
    using reduce.intros(4) store_agree_imp_callcl_cond[OF call_indirect_None(4,1)]
    by fastforce
  thus ?case
    using call_indirect_None(3,4) store_public_agree_sfunc_eq exprs_public_agree_refl[of "[Trap]"]
          action_indistinguishable.intros(1)
    by fastforce
next
  case (callcl_native cl j tr t1s t2s ts es ves vcs n k m zs s vs i)
  obtain vcs' where vcs'_def:"es' = (($$*vcs') @ [Callcl cl])" "publics_agree vcs vcs'"
    using callcl_native(2,8) exprs_public_agree_imp_publics_agree1[of vcs "Callcl cl" es']
    by (fastforce simp add: expr_public_agree.simps)
  hence "\<lparr>s';vs';($$*vcs') @ [Callcl cl]\<rparr>  (Callcl_native_action n)\<leadsto>_ i \<lparr>s';vs';[Local m j (vcs' @ zs) [$Block ([] _> t2s) es]]\<rparr>"
    using reduce.callcl_native[OF _ _ _ callcl_native(4,5,6,7)] list_all2_lengthD[OF vcs'_def(2)]
          callcl_native(1,3)
    by fastforce
  moreover
  have "expr_public_agree
           (Local m j (vcs @ zs) [$Block ([] _> t2s) es])
             (Local m j (vcs' @ zs) [$Block ([] _> t2s) es])"
    using expr_public_agree.intros(7)[OF _ exprs_public_agree_refl] vcs'_def
           list_all2_appendI[OF _ publics_agree_refl[of zs]]
    by fastforce
  ultimately
  show ?case
    using callcl_native(9,10) vcs'_def(1) action_indistinguishable.intros(1)
    by fastforce
next
  case (callcl_host_Some cl tr t1s t2s f ves vcs n m s hs s_a vcs_a vs i s')
  obtain vcs' where es'_def:"es' = (($$*vcs') @ [(Callcl cl)])"
                            "publics_agree vcs vcs'"
    using exprs_public_agree_imp_publics_agree1[of vcs "(Callcl cl)"] callcl_host_Some(2,7)
    by (fastforce simp add: expr_public_agree.simps)
  have tr_def:"tr = Untrusted"
    using typeof_callcl_host callcl_host_Some(1,2,13,14)
    unfolding trust_compat_def
    by fastforce
  obtain s'_a vcs'_a where host_def:"host_apply s' (t1s _> t2s) f vcs' hs =  Some (s'_a, vcs'_a)"
                                    "store_public_agree s_a s'_a"
                                    "publics_agree vcs_a vcs'_a"
    using es'_def(2) callcl_host_Some(6,9) host_trust_security_Some
    by blast
  have "length vcs' = n"
    using list_all2_lengthD callcl_host_Some(3) es'_def(2)
    by fastforce
  thus ?case
    using reduce.callcl_host_Some[OF callcl_host_Some(1) _ _ callcl_host_Some(4,5) host_def(1)]
          es'_def callcl_host_Some(8,9) host_def(2,3) action_indistinguishable.host_Some tr_def
          publics_agree_imp_exprs_public_agree[OF host_def(3) exprs_public_agree_refl[of "[]"]]
    by (metis append_Nil2)
next
  case (callcl_host_None cl tr t1s t2s f ves vcs n m s vs hs i)
  obtain vcs' where es'_def:"es' = (($$*vcs') @ [(Callcl cl)])"
                            "publics_agree vcs vcs'"
    using exprs_public_agree_imp_publics_agree1[of vcs "(Callcl cl)"] callcl_host_None(2,6)
    by (fastforce simp add: expr_public_agree.simps)
  have tr_def:"tr = Untrusted"
    using typeof_callcl_host callcl_host_None(1,2,12,13)
    unfolding trust_compat_def
    by fastforce
  have "length vcs' = n"
    using list_all2_lengthD callcl_host_None(3) es'_def(2)
    by fastforce
  thus ?case
    using reduce.callcl_host_None[OF callcl_host_None(1) _ _ callcl_host_None(4,5)]
          callcl_host_None(7,8) exprs_public_agree_refl[of "[Trap]"] es'_def
          action_indistinguishable.host_None tr_def
    by metis
next
  case (get_local vi j s v vs i)
  have "es' = [$Get_local j]"
    using get_local(2) exprs_public_agree_imp_publics_agree1[of "[]" "$Get_local j" es']
    by clarsimp (simp add: expr_public_agree.simps)
  moreover
  obtain vi' v' vs'' where vs'_def:"vs' = vi' @ [v'] @ vs''" "publics_agree vi vi'" "publics_agree [v] [v']" "publics_agree vs vs''"
    using get_local(3) list_all2_append1[of public_agree vi "([v]@vs)" vs']
          list_all2_append1[of public_agree "[v]" vs]
    by (metis publics_agree1)
  ultimately
  have "\<lparr>s';vi'@[v']@vs'';es'\<rparr>  Get_local_action\<leadsto>_ i \<lparr>s';vi'@[v']@vs'';[$C v']\<rparr>"
    using reduce.get_local get_local(1) list_all2_lengthD
    by fastforce
  thus ?case
    using vs'_def(1,3) get_local(3,4) public_agree_imp_expr_public_agree action_indistinguishable.intros(1)
    by fastforce
next
  case (set_local vi j s v vs v' i)
  obtain v'' where v''_def:"es' = [$C v'', $Set_local j]" "public_agree v' v''"
    using exprs_public_agree_imp_publics_agree1_const1[OF set_local(2)]
    by clarsimp (auto simp add: expr_public_agree.simps)
  moreover
  obtain vi_a v_a vs_a where vs'_def:"vs' = vi_a @ [v_a] @ vs_a" "publics_agree vi vi_a" "publics_agree [v] [v_a]" "publics_agree vs vs_a"
    using set_local(3) list_all2_append1[of public_agree vi "([v]@vs)" vs']
          list_all2_append1[of public_agree "[v]" vs]
    by (metis publics_agree1)
  ultimately
  have "\<lparr>s';vi_a@[v_a]@vs_a;es'\<rparr>  Set_local_action\<leadsto>_ i \<lparr>s';vi_a@[v'']@vs_a;[]\<rparr>"
    using reduce.set_local set_local(1) list_all2_lengthD
    by fastforce
  thus ?case
    using vs'_def v''_def(2) set_local(3,4) action_indistinguishable.intros(1)
    by (fastforce simp add: list_all2_appendI)
next
  case (get_global s vs j i)
  have "es' = [$Get_global j]"
    using get_global(1) exprs_public_agree_imp_publics_agree1[of "[]" "$Get_global j" es']
    by simp (fastforce simp add: expr_public_agree.simps)
  hence "\<lparr>s';vs';es'\<rparr>  Get_global_action\<leadsto>_ i \<lparr>s';vs';[$C sglob_val s' i j]\<rparr>"
    using reduce.get_global
    by fastforce
  moreover
  have "public_agree (sglob_val s i j) (sglob_val s' i j)"
  proof -
    have "length (global \<C>) > j"
      using b_e_type_get_global get_global(8) unlift_b_e[of _ _ "[Get_global j]" "(ts _> ts')"]
      by fastforce
    hence "sglob_ind s i j < length (s.globs s)"
      using get_global(6,7) store_typing_imp_glob_agree(1)[OF get_global(4)]
            store_typing_imp_inst_length_eq[OF get_global(4)]
            store_typing_imp_glob_length_eq[OF get_global(4)]
      by fastforce
    thus ?thesis
      using store_public_agree_sglob_val_agree[OF get_global(3)]
      by fastforce
  qed
  ultimately
  show ?case
    using get_global(2,3) expr_public_agree.intros(2) action_indistinguishable.intros(1)
    by fastforce
next
  case (set_global s i j v s_a vs s')
  obtain v'' where es'_def:"es' = [$C v'', $Set_global j]"
                           "public_agree v v''"
    using exprs_public_agree_imp_publics_agree1_const1[OF set_global(2)]
    by (fastforce simp add: expr_public_agree.simps)
  have "length (global \<C>) > j"
    using b_e_type_set_global set_global(9) b_e_type_comp2_unlift
          e_type_comp_conc1[of \<S> \<C> "[$C v]" "[$Set_global j]" ts ts']
    by blast
  moreover
  obtain k where k_def:"sglob_ind s i j = k"
    by blast
  ultimately
  have "k < length (s.globs s)"
    using set_global(7,8) store_typing_imp_glob_agree(1)[OF set_global(5)]
          store_typing_imp_inst_length_eq[OF set_global(5)]
          store_typing_imp_glob_length_eq[OF set_global(5)]
    by fastforce
  moreover
  hence k'_def:"global_public_agree ((s.globs s)!k) ((s.globs s')!k)" "sglob_ind s' i j = k"
    using k_def store_public_agree_sglob_ind_eq[OF set_global(4)] set_global(4) list_all2_nthD
    unfolding store_public_agree_def
    by fastforce+
  hence "global_public_agree (((s.globs s)!k)\<lparr>g_val := v\<rparr>) (((s.globs s')!k)\<lparr>g_val := v''\<rparr>)"
    using es'_def(2)
    unfolding global_public_agree_def
    by fastforce
  ultimately
  have "globals_public_agree ((globs s)[k:=((globs s)!k)\<lparr>g_val := v\<rparr>])
                               ((globs s')[k:=((globs s')!k)\<lparr>g_val := v''\<rparr>])"
    using store_public_agree_sglob_ind_eq[OF set_global(4)] list_all2_update_cong[of global_public_agree]
          set_global(4)
    unfolding store_public_agree_def
    by fastforce
  hence "store_public_agree (supdate_glob s i j v) (supdate_glob s' i j v'')"
    using set_global(4) k_def k'_def(2)
    unfolding store_public_agree_def supdate_glob_def supdate_glob_s_def
    by simp
  thus ?case
    using es'_def reduce.set_global set_global(1,3) exprs_public_agree_refl[of "[]"]
          action_indistinguishable.intros(1)
    by fastforce
next
  case (load_Some s i j m sec k off t bs vs sec' a)
  have t_sec_is:"t_sec t = sec"
    using load_helper[OF load_Some(1,2,7,9,10,11)]
    by -
  obtain m' bs' where m'_def:"smem_ind s' i = Some j"
                             "s.mem s' ! j = (m', sec)"
                             "memory_public_agree (s.mem s ! j) (s.mem s' ! j)"
                             "load m' (nat_of_int k) off (t_length t) = Some bs'"
    using memories_public_agree_helper[OF load_Some(1,6,7,9,2)]
          load_m_imp_load_m'[OF _ load_Some(2) _ load_Some(3)]
    by fastforce
  have sec_def:"sec' = Public"
    using types_preserved_load(2)[OF load_Some(11)] exists_v_typeof
    by fastforce
  hence "es' = [$C ConstInt32 sec' k, $Load t None a off]"
    using exprs_public_agree_imp_publics_agree1_const1[OF load_Some(4)]
    by (fastforce simp add: expr_public_agree.simps public_agree_def typeof_def t_sec_def)
  hence "\<lparr>s';vs';es'\<rparr> (Load_Some_action t (nat_of_int k) a off)\<leadsto>_ i \<lparr>s';vs';[$C wasm_deserialise bs' t]\<rparr>"
    using reduce.load_Some[OF m'_def(1,2,4)]
    by fastforce
  moreover
  have "public_agree (wasm_deserialise bs t) (wasm_deserialise bs' t)"
  proof (cases sec)
    case Secret
    thus ?thesis
      using wasm_deserialise_type t_sec_is
      unfolding public_agree_def
      by auto
  next
    case Public
    thus ?thesis
      using load_Some(2,3) m'_def(2,3,4)
      unfolding public_agree_def memory_public_agree_def
      by auto
  qed
  ultimately
  show ?case
    using load_Some(5,6) expr_public_agree.intros(2) action_indistinguishable.intros(1)
    by fastforce
next
  case (load_None s i j m sec k off t vs sec' a)
  have sec_def:"sec' = Public"
    using types_preserved_load(2)[OF load_None(11)] exists_v_typeof
    by fastforce
  hence "es' = [$C ConstInt32 sec' k, $Load t None a off]"
    using exprs_public_agree_imp_publics_agree1_const1[OF load_None(4)]
    by (fastforce simp add: expr_public_agree.simps public_agree_def typeof_def t_sec_def)
  hence "\<lparr>s';vs';es'\<rparr>  (Load_None_action t (nat_of_int k) a off)\<leadsto>_ i \<lparr>s';vs';[Trap]\<rparr>"
    using reduce.load_None memories_public_agree_helper[OF load_None(1,6,7,9,2)]
          load_None(2,3) load_size
    by (metis prod.sel(1) memory_public_agree_def)
  thus ?case
    using load_None(5,6) exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (load_packed_Some s i j m sec sx k off tp t bs vs sec' a)
  have t_sec_is:"t_sec t = sec"
    using load_helper[OF load_packed_Some(1,2,7,9,10,11)]
    by -
  obtain m' bs' where m'_def:"smem_ind s' i = Some j"
                             "s.mem s' ! j = (m', sec)"
                             "memory_public_agree (s.mem s ! j) (s.mem s' ! j)"
                             "load_packed sx m' (nat_of_int k) off (tp_length tp) (t_length t) = Some bs'"
    using memories_public_agree_helper[OF load_packed_Some(1,6,7,9,2)]
          load_packed_m_imp_load_packed_m'[OF _ load_packed_Some(2) _ load_packed_Some(3)]
    by fastforce
  have sec_def:"sec' = Public"
    using types_preserved_load(2)[OF load_packed_Some(11)] exists_v_typeof
    by fastforce
  hence "es' = [$C ConstInt32 sec' k, $Load t (Some (tp, sx)) a off]"
    using exprs_public_agree_imp_publics_agree1_const1[OF load_packed_Some(4)]
    by (fastforce simp add: expr_public_agree.simps public_agree_def typeof_def t_sec_def)
  hence "\<lparr>s';vs';es'\<rparr> (Load_packed_Some_action tp sx (nat_of_int k) a off)\<leadsto>_ i \<lparr>s';vs';[$C wasm_deserialise bs' t]\<rparr>"
    using reduce.load_packed_Some[OF m'_def(1,2,4)]
    by fastforce
  moreover
  have "public_agree (wasm_deserialise bs t) (wasm_deserialise bs' t)"
  proof (cases sec)
    case Secret
    thus ?thesis
      using wasm_deserialise_type t_sec_is
      unfolding public_agree_def
      by auto
  next
    case Public
    thus ?thesis
      using load_packed_Some(2,3) m'_def(2,3,4)
      unfolding public_agree_def memory_public_agree_def
      by auto
  qed
  ultimately
  show ?case
    using load_packed_Some(5,6) expr_public_agree.intros(2) action_indistinguishable.intros(1)
    by fastforce
next
  case (load_packed_None s i j m sec sx k off tp t vs sec' a)
  have sec_def:"sec' = Public"
    using types_preserved_load(2)[OF load_packed_None(11)] exists_v_typeof
    by fastforce
  hence "es' = [$C ConstInt32 sec' k, $Load t (Some (tp, sx)) a off]"
    using exprs_public_agree_imp_publics_agree1_const1[OF load_packed_None(4)]
    by (fastforce simp add: expr_public_agree.simps public_agree_def typeof_def t_sec_def)
  hence "\<lparr>s';vs';es'\<rparr>  (Load_packed_None_action tp sx (nat_of_int k) a off)\<leadsto>_ i \<lparr>s';vs';[Trap]\<rparr>"
    using reduce.load_packed_None memories_public_agree_helper[OF load_packed_None(1,6,7,9,2)]
          load_packed_None(2,3) load_packed_size memory_public_agree_imp_eq_length
    by auto
  thus ?case
    using load_packed_None(5,6) exprs_public_agree_refl[of "[Trap]"] action_indistinguishable.intros(1)
    by fastforce
next
  case (store_Some t v s i j m sec k off mem' vs sec' a)
  obtain v' v'' m' where helpers:"t_sec t = sec"
                                 "sec' = Public"
                                 "types_agree t v"
                                 "es'= [$C v', $C v'', $Store t None a off]"
                                 "v' = (ConstInt32 sec' k)"
                                 "public_agree v v''"
                                 "smem_ind s' i = Some j"
                                 "j < length (s.mem s')"
                                 "memories_public_agree (s.mem s) (s.mem s')"
                                 "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
                                 "s.mem s' ! j = (m', sec)"
    using store_helper[OF store_Some(2,3,5,7,8,10,11,12)]
    by auto
  obtain mem'' where store_def:"store m' (nat_of_int k) off (bits v'') (t_length t) = Some mem''"
                              "memory_public_agree (mem',sec) (mem'',sec)"
    using store_m_imp_store_m'
          store_Some(3,4) helpers(1,3,6,10,11)
    by blast
  hence "store_public_agree
        (s\<lparr>s.mem := s.mem s[j := (mem', sec)]\<rparr>) (s'\<lparr>s.mem := s.mem s' [j := (mem'', sec)]\<rparr>)"
    using store_Some
    unfolding store_public_agree_def
    by (simp add: list_all2_update_cong)
  thus ?case
    using reduce.store_Some[OF _ helpers(7,11) store_def(1)]
          public_agree_imp_types_agree_insecure[OF store_Some(1) helpers(6)] helpers(4,5)
          exprs_public_agree_refl[of "[Trap]"]
          store_Some(6) action_indistinguishable.intros(1)
    by fastforce
next
  case (store_None t v s i j m sec k off vs sec' a)
  obtain v' v'' m' where helpers:"t_sec t = sec"
                                 "sec' = Public"
                                 "types_agree t v"
                                 "es'= [$C v', $C v'', $Store t None a off]"
                                 "v' = (ConstInt32 sec' k)"
                                 "public_agree v v''"
                                 "smem_ind s' i = Some j"
                                 "j < length (s.mem s')"
                                 "memories_public_agree (s.mem s) (s.mem s')"
                                 "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
                                 "s.mem s' ! j = (m', sec)"
    using store_helper[OF store_None(2,3,5,7,8,10,11,12)]
    by auto
  have store_def:"store m' (nat_of_int k) off (bits v'') (t_length t) = None"
    using store_size1 store_None(3,4) helpers(10,11)
    unfolding memory_public_agree_def
    by fastforce
  show ?case
    using reduce.store_None[OF _ helpers(7,11) store_def]
          public_agree_imp_types_agree_insecure[OF store_None(1) helpers(6)] helpers(4,5)
          exprs_public_agree_refl[of "[Trap]"]
          store_None(6,7) action_indistinguishable.intros(1)
    by blast
next
  case (store_packed_Some t v s i j m sec k off tp mem vs sec' a)
  obtain v' v'' m' where helpers:"t_sec t = sec"
                                 "sec' = Public"
                                 "types_agree t v"
                                 "es'= [$C v', $C v'', $Store t (Some tp) a off]"
                                 "v' = (ConstInt32 sec' k)"
                                 "public_agree v v''"
                                 "smem_ind s' i = Some j"
                                 "j < length (s.mem s')"
                                 "memories_public_agree (s.mem s) (s.mem s')"
                                 "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
                                 "s.mem s' ! j = (m', sec)"
    using store_helper[OF store_packed_Some(2,3,5,7,8,10,11,12)]
    by auto
  obtain mem' where store_def:"store_packed m' (nat_of_int k) off (bits v'') (tp_length tp) = Some mem'"
                              "memory_public_agree (mem,sec) (mem',sec)"
    using store_packed_m_imp_store_packed_m'
          store_packed_Some(3,4) helpers(1,3,6,10,11)
    by blast
  hence "store_public_agree
        (s\<lparr>s.mem := s.mem s[j := (mem, sec)]\<rparr>) (s'\<lparr>s.mem := s.mem s' [j := (mem', sec)]\<rparr>)"
    using store_packed_Some
    unfolding store_public_agree_def
    by (simp add: list_all2_update_cong)
  thus ?case
    using reduce.store_packed_Some[OF _ helpers(7,11) store_def(1)]
          public_agree_imp_types_agree_insecure[OF store_packed_Some(1) helpers(6)] helpers(4,5)
          exprs_public_agree_refl[of "[Trap]"]
          store_packed_Some(6) action_indistinguishable.intros(1)
    by fastforce
next
  case (store_packed_None t v s i j m sec k off tp vs sec' a)
  obtain v' v'' m' where helpers:"t_sec t = sec"
                                 "sec' = Public"
                                 "types_agree t v"
                                 "es'= [$C v', $C v'', $Store t (Some tp) a off]"
                                 "v' = (ConstInt32 sec' k)"
                                 "public_agree v v''"
                                 "smem_ind s' i = Some j"
                                 "j < length (s.mem s')"
                                 "memories_public_agree (s.mem s) (s.mem s')"
                                 "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
                                 "s.mem s' ! j = (m', sec)"
    using store_helper[OF store_packed_None(2,3,5,7,8,10,11,12)]
    by auto
  have store_def:"store_packed m' (nat_of_int k) off (bits v'') (tp_length tp) = None"
    using store_packed_size1 store_packed_None(3,4) helpers(10,11)
    unfolding memory_public_agree_def
    by fastforce
  show ?case
    using reduce.store_packed_None[OF _ helpers(7,11) store_def]
          public_agree_imp_types_agree_insecure[OF store_packed_None(1) helpers(6)] helpers(4,5)
          exprs_public_agree_refl[of "[Trap]"]
          store_packed_None(6,7) action_indistinguishable.intros(1)
    by blast
next
  case (current_memory s i j m sec n vs)
  have "es' = [$Current_memory]"
    using exprs_public_agree_imp_publics_agree1_const0[OF current_memory(4)]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using reduce.current_memory[of s' i j _ sec n vs'] action_indistinguishable.intros(1)
          memories_public_agree_helper[OF current_memory(1,6,7,9,2)]
          current_memory(2,5,6) memory_public_agree_imp_eq_length current_memory(3)
          exprs_public_agree_refl[of "[$C ConstInt32 Public (int_of_nat n)]"]
    by fastforce
next
  case (grow_memory s i j m sec n c mem' vs sec')
  hence "sec' = Public"
    using types_preserved_grow_memory
    by blast
  moreover
  hence "es' = [$C ConstInt32 Public c, $Grow_memory]"
    using exprs_public_agree_imp_publics_agree1_const1[OF grow_memory(5)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  moreover
  obtain m' where mem_agree:"smem_ind s' i = Some j"
                            "j < length (s.mem s')"
                            "memories_public_agree (s.mem s) (s.mem s')"
                            "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
                            "s.mem s' ! j = (m', sec)"
    using memories_public_agree_helper[OF grow_memory(1,7,8,10,2)]
    by auto
  moreover
  hence "mem_size m' = mem_size m"
        "sec = Public \<Longrightarrow> m = m'"
    using grow_memory(2,3)
    unfolding memory_public_agree_def
    by auto
  then obtain mem'' where mem''_def:"mem_size m' = mem_size m"
                                    "mem_grow m' (nat_of_int c) = mem''"
                                    "mem_size mem' = mem_size mem''"
                                    "sec = Public \<Longrightarrow> mem' = mem''"
    using mem_grow_size grow_memory(4)
    by metis
  ultimately
  have "\<lparr>s';vs';es'\<rparr>  (Grow_memory_Some_action n (nat_of_int c))\<leadsto>_i \<lparr>s'\<lparr>s.mem := s.mem s'[j := (mem'', sec)]\<rparr>;vs';[$C ConstInt32 Public (int_of_nat n)]\<rparr>"
    using reduce.grow_memory grow_memory(3)
    by fastforce
  moreover
  have "memory_public_agree (mem', sec) (mem'', sec)"
    using mem''_def(3,4)
    unfolding memory_public_agree_def
    by (cases sec) auto
  hence "store_public_agree (s\<lparr>s.mem := s.mem s[j := (mem', sec)]\<rparr>) (s'\<lparr>s.mem := s.mem s'[j := (mem'', sec)]\<rparr>)"
    using mem_agree(1) list_all2_update_cong grow_memory(7)
    unfolding store_public_agree_def
    by fastforce
  ultimately
  show ?case
    using exprs_public_agree_refl[of "[$C ConstInt32 Public (int_of_nat n)]"] grow_memory(6)
          action_indistinguishable.intros(1)
    by fastforce
next
  case (grow_memory_fail s i j m sec n vs sec' c)
  hence "sec' = Public"
    using types_preserved_grow_memory
    by blast
  hence "es' = [$C ConstInt32 Public c, $Grow_memory]"
    using exprs_public_agree_imp_publics_agree1_const1[OF grow_memory_fail(4)]
    unfolding public_agree_def typeof_def t_sec_def
    by (fastforce simp add: expr_public_agree.simps)
  moreover
  obtain m' where mem_agree:"smem_ind s' i = Some j"
                            "j < length (s.mem s')"
                            "memories_public_agree (s.mem s) (s.mem s')"
                            "memory_public_agree ((s.mem s)!j) ((s.mem s')!j)"
                            "s.mem s' ! j = (m', sec)"
    using memories_public_agree_helper[OF grow_memory_fail(1,6,7,9,2)]
    by auto
  hence "mem_size m' = n"
    using grow_memory_fail(2,3) mem_grow_size
    unfolding memory_public_agree_def
    by fastforce
  ultimately
  have "\<lparr>s';vs';es'\<rparr>  (Grow_memory_None_action n (nat_of_int c))\<leadsto>_i \<lparr>s';vs';[$C ConstInt32 Public int32_minus_one]\<rparr>"
    using reduce.grow_memory_fail[OF mem_agree(1,5)]
    by blast
  thus ?case
    using exprs_public_agree_refl[of "[$C ConstInt32 Public int32_minus_one]"] grow_memory_fail(5,6)
          action_indistinguishable.intros(1)
    by fastforce
next
  case (label s vs es a i s_a vs_a es_a k lholed les les_a s' vs' les')
  obtain lholed' es' where lholed'_def:"lholed_public_agree lholed lholed'"
                                       "exprs_public_agree es es'"
                                       "Lfilled k lholed' es' les'"
    using exprs_public_agree_imp_lholed_public_agree[OF label(2,5)]
    by blast
  obtain a' s'_a vs'_a es'_a where es'_a_def:"\<lparr>s';vs';es'\<rparr> a'\<leadsto>_ i \<lparr>s'_a;vs'_a;es'_a\<rparr>"
                                             "exprs_public_agree es_a es'_a"
                                             "publics_agree vs_a vs'_a"
                                             "store_public_agree s_a s'_a"
                                             "a \<sim>_a a'"
    using label(4)[OF lholed'_def(2) label(6,7,8,9,10)]
          types_exist_lfilled_weak[OF label(2,12)] label(1,11)
    by fastforce
  obtain les'_a where "Lfilled k lholed' es'_a les'_a" "exprs_public_agree les_a les'_a"
    using lholed_public_agree_imp_exprs_public_agree[OF lholed'_def(1) label(3) es'_a_def(2)]
    by blast
  thus ?case
    using reduce.label[OF es'_a_def(1) lholed'_def(3)] es'_a_def(3,4,5)
    by blast
next
  case (local s vs es a i s_a vs_a es_a v0s n j s' vs' es')
  obtain vs'' es'' where es'_def:"es' = [Local n i vs'' es'']"
                                 "publics_agree vs vs''"
                                 "exprs_public_agree es es''"
    using local(3) expr_public_agree_local[OF exprs_public_agree_imp_expr_public_agree]
    by (metis (no_types, lifting) list_all2_Cons1 list_all2_Nil)
  obtain tls \<C>' where tls_def:"i < length (inst s)"
                           "\<C>' = (s_inst \<S> ! i)\<lparr>trust_t := Untrusted, local := local (s_inst \<S> ! i) @ map typeof vs, label := label (s_inst \<S> ! i), return := Some tls\<rparr>"
                           "\<S>\<bullet>\<C>' \<turnstile> es : ([] _> tls)"
    using e_type_local[OF local(10)] store_typing_imp_inst_length_eq[OF local(6)] local(9)
    by fastforce
  obtain a' s'_a vs'_a es'_a where "\<lparr>s';vs'';es''\<rparr> a'\<leadsto>_ i \<lparr>s'_a;vs'_a;es'_a\<rparr>"
                                   "exprs_public_agree es_a es'_a"
                                   "publics_agree vs_a vs'_a"
                                   "store_public_agree s_a s'_a"
                                   "a \<sim>_a a'"
    using local(2)[OF es'_def(3,2) local(5,6) _ tls_def local(1)]
    by fastforce
  thus ?case
    using reduce.local es'_def(1) expr_public_agree.intros(7) local(4)
    by fastforce
qed

lemma actions_indistinguishable_secrets:
  assumes "r_actions \<lparr>s;vs;es\<rparr> i as"
          "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
          "store_typing s \<S>"
          "tvs = map typeof vs"
          "i < length (inst s)"
          "\<C> = ((s_inst \<S>)!i)\<lparr>trust_t := Untrusted, local := (local ((s_inst \<S>)!i) @ tvs), label := arb_labs, return := arb_return\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "\<exists>as'. (r_actions \<lparr>s';vs';es'\<rparr> i as') \<and> list_all2 action_indistinguishable as as'"
  using assms
proof (induction s vs es i as arbitrary: s' vs' es' arb_labs arb_return \<C> rule: reduction_actions.induct)
  case (1 es s vs)
  have "const_list es' \<or> es' = [Trap]"
    using 1(1)
  proof (rule disjE)
    assume "const_list es"
    thus ?thesis
      using exprs_public_agree_const_list 1(2)
      by simp
  next
    assume local_assms:"es = [Trap]"
    thus ?thesis
      using 1(2)
      by (simp add: list_all2_Cons1 expr_public_agree.simps)
  qed
  thus ?case
    using reduction_actions.intros(1)
    by fastforce
next
  case (2 s vs es a i s_a vs_a es_a as s' vs' es')
  have "store_typing s_a \<S>" "i < length (inst s_a)"
    using store_preserved1[OF 2(1,7,11)] 2(7,8,9,10) store_typing_imp_inst_length_eq
    by fastforce+
  moreover
  have "\<S>\<bullet>\<C> \<turnstile> es_a : (ts _> ts')" "tvs = map typeof vs_a"
    using types_preserved_e1[OF 2(1,7,8,9,10,11)] 2(8)
    by auto
  moreover
  obtain a' s'_a vs'_a es'_a where "\<lparr>s';vs';es'\<rparr> a'\<leadsto>_ i \<lparr>s'_a;vs'_a;es'_a\<rparr>"
                                   "exprs_public_agree es_a es'_a"
                                   "publics_agree vs_a vs'_a"
                                   "store_public_agree s_a s'_a"
                                   "a \<sim>_a a'"
    using exprs_public_agree_imp_reduce[OF 2(1,4,5,6,7,8,9,10,11)]
    by blast
  ultimately
  show ?case
    using 2(3,10) reduction_actions.intros(2)
    by fastforce
qed

lemma function_actions_indistinguishable_secrets:
  assumes "r_actions \<lparr>s;vs;es\<rparr> i as"
          "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
          "store_typing s \<S>"
          "\<S>\<bullet>Untrusted\<bullet>rs \<tturnstile>_i vs;es : ts'"
  shows "\<exists>as'. (r_actions \<lparr>s';vs';es'\<rparr> i as') \<and> list_all2 action_indistinguishable as as'"
proof -
  obtain tvs rs \<C> where \<C>_def:"tvs = map typeof vs"
                              "i < length (inst s)"
                              "\<C> = (s_inst \<S> ! i)\<lparr>trust_t := Untrusted, local := local (s_inst \<S> ! i) @ tvs, label := label (s_inst \<S> ! i), return := rs\<rparr>"
                              "\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts')"
    using assms(6) store_typing_imp_inst_length_eq[OF assms(5)]
    unfolding s_typing.simps
    by fastforce
  thus ?thesis
    using actions_indistinguishable_secrets[OF assms(1,2,3,4,5) \<C>_def]
    by fastforce
qed

theorem config_actions_indistinguishable_secrets:
  assumes "\<turnstile>_i s;vs;es : (Untrusted,ts)"
          "r_actions \<lparr>s;vs;es\<rparr> i as"
          "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
  shows "\<exists>as'. (r_actions \<lparr>s';vs';es'\<rparr> i as') \<and> list_all2 action_indistinguishable as as'"
proof -
  obtain \<S> where "store_typing s \<S>" "\<S>\<bullet>Untrusted\<bullet>None \<tturnstile>_i vs;es : ts"
    using assms(1) config_typing.simps
    by blast
  thus ?thesis
    using assms(2,3,4,5) function_actions_indistinguishable_secrets
    by blast
qed
(*
definition program_actions :: "[s, v list, e list, nat, action list] \<Rightarrow> bool" ("p'_actions \<lparr>_;_;_\<rparr> _ _" 60) where
  "program_actions s vs es i as \<equiv> (\<exists>ts. \<turnstile>_i s;vs;es : (Untrusted,ts)) \<and> (r_actions \<lparr>s;vs;es\<rparr> i as)"

definition program_actions_set :: "[s, v list, e list, nat] \<Rightarrow> (action list) set" ("p'_actions'_set \<lparr>_;_;_\<rparr> _" 60) where
  "program_actions_set s vs es i = Collect (program_actions s vs es i)"

lemma program_actions_indistinguishable_secrets:
  assumes "(p_actions \<lparr>s;vs;es\<rparr> i as)"
          "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
  shows "\<exists>as'. (p_actions \<lparr>s';vs';es'\<rparr> i as') \<and> list_all2 action_indistinguishable as as'"
  using assms(1) config_actions_indistinguishable_secrets[OF _ _ assms(2,3,4)]
        exprs_public_agree_imp_config_typing[OF _ assms(4,3,2)]
  unfolding program_actions_def
  by blast

lemma program_actions_indistinguishable_secrets_abs:
  assumes "(p_actions \<lparr>s;vs;es\<rparr> i as)"
          "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
  shows "\<exists>as'. (p_actions \<lparr>s';vs';es'\<rparr> i as') \<and> ($\<A> as) = ($\<A> as')"
  using Quotient3_observation program_actions_indistinguishable_secrets[OF assms]
  unfolding Quotient3_def
  by metis

lemma program_actions_indistinguishable_secrets_abs_set:
  assumes "t \<in> (image abs_obs (p_actions_set \<lparr>s;vs;es\<rparr> i))"
          "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
  shows "t \<in> (image abs_obs (p_actions_set \<lparr>s';vs';es'\<rparr> i))"
proof -
  obtain as where "(p_actions \<lparr>s;vs;es\<rparr> i as) \<and> ($\<A> as) = t"
    using assms(1) program_actions_set_def
    by blast
  then obtain as' where "(p_actions \<lparr>s';vs';es'\<rparr> i as') \<and> ($\<A> as') = t"
    using program_actions_indistinguishable_secrets_abs[OF _ assms(2,3,4)]
    by fastforce
  thus ?thesis
    unfolding program_actions_set_def
    by blast
qed

lemma program_actions_indistinguishable_secrets_abs_set_equiv:
  assumes "exprs_public_agree es es'"
          "publics_agree vs vs'"
          "store_public_agree s s'"
  shows "(image abs_obs (p_actions_set \<lparr>s;vs;es\<rparr> i)) = (image abs_obs (p_actions_set \<lparr>s';vs';es'\<rparr> i))"
  using program_actions_indistinguishable_secrets_abs_set[OF _ assms]
        program_actions_indistinguishable_secrets_abs_set[OF _ exprs_public_agree_symm[OF assms(1)]
                                                               publics_agree_symm[OF assms(2)]
                                                               store_public_agree_symm[OF assms(3)]]
  by fastforce

lift_definition config_quot_program_actions_set :: "[config_quot, nat] \<Rightarrow> observation set" is "(\<lambda>(s,vs,es) i. image abs_obs (p_actions_set \<lparr>s;vs;es\<rparr> i))"
proof -
  fix prod prod'
  assume assms:"config_indistinguishable prod prod'"
  thus "(case prod of (s, vs, es) \<Rightarrow> \<lambda>i. image abs_obs (p_actions_set \<lparr>s;vs;es\<rparr> i)) = (case prod' of (s, vs, es) \<Rightarrow> \<lambda>i. image abs_obs (p_actions_set \<lparr>s;vs;es\<rparr> i))"
    using assms config_indistinguishable_symm[OF assms]
    apply (cases prod)
    apply (cases prod')
    apply simp
    apply (metis program_actions_indistinguishable_secrets_abs_set_equiv)
    done
qed

theorem config_quot_program_actions_set_p_actions_set_obss_commutes:
  shows "image abs_obs (p_actions_set \<lparr>s;vs;es\<rparr> i) = config_quot_program_actions_set (abs_config_quot (s,vs,es)) i"
  by (simp add: config_quot_program_actions_set.abs_eq)
*)
lemma config_indistinguishable_imp_reduce:
  assumes "\<lparr>s;vs;es\<rparr> a\<leadsto>_ i \<lparr>s_a;vs_a;es_a\<rparr>"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "\<exists>a' s'_a vs'_a es'_a. \<lparr>s';vs';es'\<rparr> a'\<leadsto>_ i \<lparr>s'_a;vs'_a;es'_a\<rparr> \<and>
                               ((s_a,vs_a,es_a) \<sim>_c (s'_a,vs'_a,es'_a)) \<and>
                               (a \<sim>_a a')"
proof -
  obtain \<S> where \<S>_def:"store_typing s \<S>"
                       "\<S>\<bullet>Untrusted\<bullet>None \<tturnstile>_i vs;es : ts"
    using assms(3)
    unfolding config_typing.simps
    by blast
  have config_agree:"exprs_public_agree es es'"
                    "publics_agree vs vs'"
                    "store_public_agree s s'"
    using assms(2)
    by simp_all
  obtain tvs \<C> where \<C>_def:"tvs = map typeof vs"
                           "i < length (inst s)"
                           "\<C> = (s_inst \<S> ! i) \<lparr>trust_t := Untrusted, local := local (s_inst \<S> ! i) @ tvs, label := label (s_inst \<S> ! i), return := None\<rparr>"
                           "\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts)"
    using \<S>_def(2) store_typing_imp_inst_length_eq[OF \<S>_def(1)]
    unfolding s_typing.simps
    by fastforce
  show ?thesis
    using exprs_public_agree_imp_reduce[OF assms(1) config_agree \<S>_def(1) \<C>_def]
    by fastforce
qed

definition config_bisimulation :: "((s \<times> v list \<times> e list) \<times> nat) rel \<Rightarrow> bool" where
  "config_bisimulation R \<equiv>
     \<forall>(((s1,vs1,es1),i1),((s2,vs2,es2),i2)) \<in> R.
       (\<forall>s1' vs1' es1' a. \<lparr>s1;vs1;es1\<rparr> a\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr> \<longrightarrow> (\<exists>s2' vs2' es2' a'. \<lparr>s2;vs2;es2\<rparr> a'\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr> \<and> (((s1',vs1',es1'),i1),((s2',vs2',es2'),i2)) \<in> R \<and> (a \<sim>_a a')))
       \<and> (\<forall>s2' vs2' es2' a. \<lparr>s2;vs2;es2\<rparr> a\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr> \<longrightarrow> (\<exists>s1' vs1' es1' a'. \<lparr>s1;vs1;es1\<rparr> a'\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr> \<and> (((s1',vs1',es1'),i1),((s2',vs2',es2'),i2)) \<in> R \<and> (a \<sim>_a a')))"

definition config_bisimilar :: "((s \<times> v list \<times> e list) \<times> nat) rel" where
  "config_bisimilar \<equiv> \<Union> { R. config_bisimulation R }"

lemma config_bisimilar_ex_config_bisimulation:
  assumes "(((s,vs,es),i), ((s',vs',es'),i')) \<in> config_bisimilar"
  shows "\<exists>R. config_bisimulation R \<and> (((s,vs,es),i), ((s',vs',es'),i')) \<in> R"
  using assms
  unfolding config_bisimilar_def
  by simp
(*
inductive_set ex_bisimulation :: "[s, v list, e list, nat, s, v list, e list] \<Rightarrow> (s \<times> v list \<times> e list \<times> nat) rel"
  for s::s and vs::"v list" and es::"e list" and i::nat and s'::s and vs'::"v list" and es'::"e list" where
  "\<lbrakk>(s,vs,es) \<sim>_c (s',vs',es'); \<turnstile>_i s;vs;es : (Untrusted,ts)\<rbrakk> \<Longrightarrow> ((s,vs,es,i),(s',vs',es',i)) \<in> ex_bisimulation s vs es i s' vs' es'"
| "\<lbrakk>((s1,vs1,es1,i),(s2,vs2,es2,i)) \<in> ex_bisimulation s vs es i s' vs' es';
    \<lparr>s1;vs1;es1\<rparr> a1\<leadsto>_i \<lparr>s1';vs1';es1'\<rparr>;
    \<lparr>s2;vs2;es2\<rparr> a2\<leadsto>_i \<lparr>s2';vs2';es2'\<rparr>;
    config_indistinguishable (s1',vs1',es1') (s2',vs2',es2');
    \<turnstile>_i s1';vs1';es1' : (Untrusted,ts);
    action_indistinguishable a1 a2\<rbrakk> \<Longrightarrow> ((s1',vs1',es1',i),(s2',vs2',es2',i)) \<in> ex_bisimulation s vs es i s' vs' es'"

lemma ex_bisimulation_imp_config_type:
  assumes "((s1,vs1,es1,i), (s2,vs2,es2,i)) \<in> ex_bisimulation s vs es i s' vs' es'"
  shows "config_indistinguishable (s1,vs1,es1) (s2,vs2,es2)"
        "\<exists>ts. \<turnstile>_i s1;vs1;es1 : (Untrusted,ts)"
  using assms
proof (induction rule: ex_bisimulation.induct)
  case (1 ts)
  thus "config_indistinguishable (s, vs, es) (s', vs', es')"
       "\<exists>ts. \<turnstile>_i s;vs;es : (Untrusted,ts)"
    by blast+
next
  case (2 s1 vs1 es1 s2 vs2 es2 a1 s1' vs1' es1' a2 s2' vs2' es2' ts)
  thus "config_indistinguishable (s1', vs1', es1') (s2', vs2', es2')"
       "\<exists>ts. \<turnstile>_i s1';vs1';es1' : (Untrusted,ts)"
    by blast+
qed

lemma ex_bisimulation_config_bisimulation1:
  assumes "((s1,vs1,es1,i1), (s2,vs2,es2,i2)) \<in> ex_bisimulation s vs es i s' vs' es'"
          "\<lparr>s1;vs1;es1\<rparr> a1\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr>"
  shows "(\<exists>s2' vs2' es2' a2 ts. \<lparr>s2;vs2;es2\<rparr> a2 \<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr> \<and>
                                ((s1',vs1',es1',i1),(s2',vs2',es2',i2)) \<in> ex_bisimulation s vs es i s' vs' es' \<and>
                                action_indistinguishable a1 a2)"
  using assms assms(1)
proof (induction arbitrary: a1 s1' vs1' es1' rule: ex_bisimulation.induct)
  case (1 ts)
  obtain a' s'_a vs'_a es'_a where s'_red:"\<lparr>s';vs';es'\<rparr> a'\<leadsto>_ i \<lparr>s'_a;vs'_a;es'_a\<rparr>"
                                          "config_indistinguishable (s1', vs1', es1') (s'_a, vs'_a, es'_a)"
                                          "action_indistinguishable a1 a'"
    using config_indistinguishable_imp_reduce[OF 1(3,1,2)]
    by blast
  have "((s1',vs1',es1',i),(s'_a,vs'_a,es'_a,i)) \<in> ex_bisimulation s vs es i s' vs' es'"
    using ex_bisimulation.intros(2)[OF ex_bisimulation.intros(1)[OF 1(1,2)] 1(3) s'_red(1,2) _ s'_red(3)]
          preservation[OF 1(2,3)]
    by simp
  thus ?case
    using 1 s'_red(1,3)
    by fastforce
next
  case (2 s1 vs1 es1 s2 vs2 es2 a1 s1' vs1' es1' a2 s2' vs2' es2' ts a s1'_a vs1'_a es1'_a)
  obtain a'' s2'_a vs2'_a es2'_a where s2'_red:"\<lparr>s2';vs2';es2'\<rparr> a''\<leadsto>_ i \<lparr>s2'_a;vs2'_a;es2'_a\<rparr>"
                                               "config_indistinguishable (s1'_a, vs1'_a, es1'_a) (s2'_a, vs2'_a, es2'_a)"
                                               "action_indistinguishable a a''"
    using config_indistinguishable_imp_reduce[OF 2(8,4,5)]
    by blast
  have "((s1'_a,vs1'_a,es1'_a,i),(s2'_a,vs2'_a,es2'_a,i)) \<in> ex_bisimulation s vs es i s' vs' es'"
    using ex_bisimulation.intros(2)[OF 2(9,8) s2'_red(1,2) _ s2'_red(3)]
          preservation[OF 2(5,8)]
    by simp
  thus ?case
    using s2'_red(1,3)
    by fastforce
qed

lemma ex_bisimulation_config_bisimulation2:
  assumes "((s1,vs1,es1,i1), (s2,vs2,es2,i2)) \<in> ex_bisimulation s vs es i s' vs' es'"
          "\<lparr>s2;vs2;es2\<rparr> a2\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr>"
  shows "(\<exists>s1' vs1' es1' a1 ts. \<lparr>s1;vs1;es1\<rparr> a1 \<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr> \<and>
                                ((s1',vs1',es1',i1),(s2',vs2',es2',i2)) \<in> ex_bisimulation s vs es i s' vs' es' \<and>
                                action_indistinguishable a2 a1)"
  using assms assms(1)
proof (induction arbitrary: a2 s2' vs2' es2' rule: ex_bisimulation.induct)
  case (1 ts)
  obtain a s_a vs_a es_a where s'_red:"\<lparr>s;vs;es\<rparr> a\<leadsto>_ i \<lparr>s_a;vs_a;es_a\<rparr>"
                                      "config_indistinguishable (s2', vs2', es2') (s_a, vs_a, es_a)"
                                      "action_indistinguishable a2 a"
    using config_indistinguishable_imp_reduce[OF 1(3) config_indistinguishable_symm[OF 1(1)]] 1(1)
          exprs_public_agree_imp_config_typing[OF 1(2)]
    by fastforce
  have "((s_a,vs_a,es_a,i), (s2',vs2',es2',i)) \<in> ex_bisimulation s vs es i s' vs' es'"
    using ex_bisimulation.intros(2)[OF ex_bisimulation.intros(1)[OF 1(1,2)] s'_red(1) 1(3)]
          config_indistinguishable_symm[OF s'_red(2)] action_indistinguishable_symm[OF s'_red(3)]
          preservation[OF 1(2) s'_red(1)] exprs_public_agree_imp_config_typing
    by simp
  thus ?case
    using 1 s'_red(1,3)
    by fastforce
next
  case (2 s1 vs1 es1 s2 vs2 es2 a1 s1' vs1' es1' a2 s2' vs2' es2' ts a s2'_a vs2'_a es2'_a)
  obtain a'' s1'_a vs1'_a es1'_a where s1'_red:"\<lparr>s1';vs1';es1'\<rparr> a''\<leadsto>_ i \<lparr>s1'_a;vs1'_a;es1'_a\<rparr>"
                                               "config_indistinguishable (s2'_a, vs2'_a, es2'_a) (s1'_a, vs1'_a, es1'_a)"
                                               "action_indistinguishable a a''"
    using config_indistinguishable_imp_reduce[OF 2(8) config_indistinguishable_symm[OF 2(4)]] 2(4)
          exprs_public_agree_imp_config_typing[OF 2(5)]
    by fastforce
  have "((s1'_a,vs1'_a,es1'_a,i),(s2'_a,vs2'_a,es2'_a,i)) \<in> ex_bisimulation s vs es i s' vs' es'"
    using ex_bisimulation.intros(2)[OF 2(9) s1'_red(1) 2(8)]
          preservation[OF 2(5) s1'_red(1)] action_indistinguishable_symm[OF s1'_red(3)]
          config_indistinguishable_symm[OF s1'_red(2)]
    by simp
  thus ?case
    using s1'_red(1,3)
    by fastforce
qed

lemma ex_bisimulation_config_bisimulation:
  "config_bisimulation (ex_bisimulation s vs es i s' vs' es')"
proof -
  {
    fix s1 vs1 es1 i1 s2 vs2 es2 i2
    assume assms:"((s1,vs1,es1,i1),(s2,vs2,es2,i2)) \<in> (ex_bisimulation s vs es i s' vs' es')"
    have "(\<forall>s1' vs1' es1' a. \<lparr>s1;vs1;es1\<rparr> a\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr> \<longrightarrow>
             (\<exists>s2' vs2' es2' a'. \<lparr>s2;vs2;es2\<rparr> a'\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr>
             \<and> ((s1',vs1',es1',i1),(s2',vs2',es2',i2)) \<in> (ex_bisimulation s vs es i s' vs' es')
             \<and> action_indistinguishable a a'))
          \<and> (\<forall>s2' vs2' es2' a. \<lparr>s2;vs2;es2\<rparr> a\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr> \<longrightarrow>
               (\<exists>s1' vs1' es1' a'. \<lparr>s1;vs1;es1\<rparr> a'\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr>
               \<and> ((s1',vs1',es1',i1),(s2',vs2',es2',i2)) \<in> (ex_bisimulation s vs es i s' vs' es')
               \<and> action_indistinguishable a a'))"
      using ex_bisimulation_config_bisimulation1[OF assms]
            ex_bisimulation_config_bisimulation2[OF assms]
      by fastforce
  }
  thus ?thesis
    unfolding config_bisimulation_def
    by fastforce
qed
*)
definition typed_indistinguishable_pairs :: "((s \<times> v list \<times> e list) \<times> nat) rel" where
  "typed_indistinguishable_pairs \<equiv>
     { (((s,vs,es),i1),((s',vs',es'),i2)). ((s,vs,es) \<sim>_c (s',vs',es')) \<and> i1 = i2
                                           \<and> (\<exists>ts. \<turnstile>_i1 s;vs;es : (Untrusted,ts))}"

lemma config_bisimulation_typed_indistinguishable_pairs1:
  assumes "(((s1,vs1,es1),i1), ((s2,vs2,es2),i2)) \<in> typed_indistinguishable_pairs"
          "\<lparr>s1;vs1;es1\<rparr> a1\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr>"
  shows "(\<exists>s2' vs2' es2' a2 ts. \<lparr>s2;vs2;es2\<rparr> a2 \<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr> \<and>
                                (((s1',vs1',es1'),i1),((s2',vs2',es2'),i2)) \<in> typed_indistinguishable_pairs \<and>
                                (a1 \<sim>_a a2))"
proof -
  have bisim_is:"(s1,vs1,es1) \<sim>_c (s2,vs2,es2)"
                "i1 = i2"
                "(\<exists>ts. \<turnstile>_i1 s1;vs1;es1 : (Untrusted,ts))"
    using assms(1)
    unfolding typed_indistinguishable_pairs_def
    by auto
  show ?thesis
    using config_indistinguishable_imp_reduce[OF assms(2) bisim_is(1)] bisim_is(2,3) preservation[OF _ assms(2)]
    unfolding typed_indistinguishable_pairs_def
    by fastforce
qed

lemma config_bisimulation_typed_indistinguishable_pairs2:
  assumes "(((s1,vs1,es1),i1), ((s2,vs2,es2),i2)) \<in> typed_indistinguishable_pairs"
          "\<lparr>s2;vs2;es2\<rparr> a2\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr>"
  shows "(\<exists>s1' vs1' es1' a1 ts. \<lparr>s1;vs1;es1\<rparr> a1 \<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr> \<and>
                                (((s1',vs1',es1'),i1),((s2',vs2',es2'),i2)) \<in> typed_indistinguishable_pairs \<and>
                                (a2 \<sim>_a a1))"
proof -
  obtain ts where bisim_is:"(s1,vs1,es1) \<sim>_c (s2,vs2,es2)"
                           "i1 = i2"
                           "(\<turnstile>_i1 s1;vs1;es1 : (Untrusted,ts))"
    using assms(1)
    unfolding typed_indistinguishable_pairs_def
    by auto
  have c2_type:"(s2,vs2,es2) \<sim>_c (s1,vs1,es1)"
               "(\<turnstile>_i2 s2;vs2;es2 : (Untrusted,ts))"
    using exprs_public_agree_imp_config_typing[OF bisim_is(3)] bisim_is(1)
          config_indistinguishable_symm[OF bisim_is(1)] bisim_is(2)
    by fastforce+
  show ?thesis
    using config_indistinguishable_imp_reduce[OF assms(2) config_indistinguishable_symm[OF bisim_is(1)] c2_type(2)] bisim_is(2)
          preservation[OF bisim_is(3)]
    unfolding typed_indistinguishable_pairs_def
    by (fastforce simp only: config_indistinguishable_symm)
qed

lemma config_bisimulation_typed_indistinguishable_pairs:
  "config_bisimulation typed_indistinguishable_pairs"
proof -
  {
    fix s1 vs1 es1 i1 s2 vs2 es2 i2
    assume assms:"(((s1,vs1,es1),i1),((s2,vs2,es2),i2)) \<in> typed_indistinguishable_pairs"
    have "(\<forall>s1' vs1' es1' a. \<lparr>s1;vs1;es1\<rparr> a\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr> \<longrightarrow>
             (\<exists>s2' vs2' es2' a'. \<lparr>s2;vs2;es2\<rparr> a'\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr>
             \<and> (((s1',vs1',es1'),i1),((s2',vs2',es2'),i2)) \<in> typed_indistinguishable_pairs
             \<and> (a \<sim>_a a')))
          \<and> (\<forall>s2' vs2' es2' a. \<lparr>s2;vs2;es2\<rparr> a\<leadsto>_i2 \<lparr>s2';vs2';es2'\<rparr> \<longrightarrow>
               (\<exists>s1' vs1' es1' a'. \<lparr>s1;vs1;es1\<rparr> a'\<leadsto>_i1 \<lparr>s1';vs1';es1'\<rparr>
               \<and> (((s1',vs1',es1'),i1),((s2',vs2',es2'),i2)) \<in> typed_indistinguishable_pairs
               \<and> (a \<sim>_a a')))"
      using config_bisimulation_typed_indistinguishable_pairs1[OF assms]
            config_bisimulation_typed_indistinguishable_pairs2[OF assms]
      by fastforce
  }
  thus ?thesis
    unfolding config_bisimulation_def
    by fastforce
qed

theorem config_indistinguishable_imp_config_bisimilar:
  assumes "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "(((s,vs,es),i), ((s',vs',es'),i)) \<in> config_bisimilar"
proof -
  have "(((s,vs,es),i), ((s',vs',es'),i)) \<in> typed_indistinguishable_pairs"
    using assms
    unfolding typed_indistinguishable_pairs_def
    by fastforce
  thus ?thesis
    using config_bisimulation_typed_indistinguishable_pairs
    unfolding config_bisimilar_def
    by blast
qed

inductive reduce_relpowp :: "s \<Rightarrow> v list \<Rightarrow> e list \<Rightarrow> action list \<Rightarrow> nat \<Rightarrow> s \<Rightarrow> v list \<Rightarrow> e list \<Rightarrow> bool" ("\<lparr>_;_;_\<rparr> _^^\<leadsto>'_ _ \<lparr>_;_;_\<rparr>" 60) where
  "\<lparr>s;vs;es\<rparr> []^^\<leadsto>_i \<lparr>s;vs;es\<rparr>"
| "\<lbrakk>\<lparr>s;vs;es\<rparr> a\<leadsto>_i \<lparr>s'';vs'';es''\<rparr>; \<lparr>s'';vs'';es''\<rparr> as^^\<leadsto>_i \<lparr>s';vs';es'\<rparr>\<rbrakk> \<Longrightarrow> \<lparr>s;vs;es\<rparr> (a#as)^^\<leadsto>_i \<lparr>s';vs';es'\<rparr>"

theorem config_indistinguishable_trace_noninterference:
  assumes "\<lparr>s;vs;es\<rparr> as^^\<leadsto>_i \<lparr>s_as;vs_as;es_as\<rparr>"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "\<exists>s'_as vs'_as es'_as as'. \<lparr>s';vs';es'\<rparr> as'^^\<leadsto>_i \<lparr>s'_as;vs'_as;es'_as\<rparr> \<and>
                                   list_all2 action_indistinguishable as as' \<and>
                                   config_indistinguishable (s_as,vs_as,es_as) (s'_as,vs'_as,es'_as)"
  using assms
proof (induction s vs es as i s_as vs_as es_as arbitrary: s' vs' es' rule: reduce_relpowp.induct)
  case (1 s vs es i)
  thus ?case
    using reduce_relpowp.intros(1)
    by fastforce
next
  case (2 s vs es a i s_a vs_a es_a as s_aas vs_aas es_aas)
  obtain a' s'_a vs'_a es'_a where es'_a_def:"\<lparr>s';vs';es'\<rparr> a'\<leadsto>_ i \<lparr>s'_a;vs'_a;es'_a\<rparr>"
                                             "config_indistinguishable (s_a, vs_a, es_a) (s'_a, vs'_a, es'_a)"
                                             "a \<sim>_a a'"
    using config_indistinguishable_imp_reduce[OF 2(1,4,5)]
    by blast
  have "\<turnstile>_ i s_a;vs_a;es_a : (Untrusted, ts)"
    using preservation[OF 2(5,1)]
    by -
  thus ?case
    using 2(3)[OF es'_a_def(2)] reduce_relpowp.intros(2)[OF es'_a_def(1)] es'_a_def(2,3)
    by fastforce
qed

lemma rep_config_untrusted_quot_typing:
  assumes "((s,vs,es),i) = (rep_config_untrusted_quot x)"
  shows  "\<exists>ts. \<turnstile>_i s;vs;es : (Untrusted,ts)"
proof -
  have "((s,vs,es),i) \<sim>_cp ((s,vs,es),i)"
    using Quotient3_config_untrusted_quot assms
    unfolding Quotient3_def
    by metis
  thus ?thesis
    unfolding config_untrusted_equiv_def
    by simp
qed

end
