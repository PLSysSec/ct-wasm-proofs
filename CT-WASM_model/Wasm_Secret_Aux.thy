section {* Auxiliary Security Properties *}

theory Wasm_Secret_Aux imports Wasm_Soundness "HOL-Eisbach.Eisbach_Tools" begin

lemma memory_public_agree_imp_eq_length:
  assumes "memory_public_agree m m'"
    shows "mem_size (fst m) = mem_size (fst m')"
  using assms
  unfolding memory_public_agree_def
  by auto

lemma store_public_agree_smem_ind_eq:
  assumes "store_public_agree s s'"
  shows "(smem_ind s i) = (smem_ind s' i)"
  using assms
  unfolding store_public_agree_def smem_ind_def
  by fastforce

lemma store_public_agree_sfunc_eq:
  assumes "store_public_agree s s'"
  shows "(sfunc s i j) = (sfunc s' i j)"
  using assms
  unfolding store_public_agree_def sfunc_def sfunc_ind_def
  by fastforce

lemma store_public_agree_stab_eq:
  assumes "store_public_agree s s'"
  shows "(stab s i j) = (stab s' i j)"
  using assms
  unfolding store_public_agree_def stab_def stab_s_def
  by presburger

lemma store_public_agree_sglob_ind_eq:
  assumes "store_public_agree s s'"
          "(sglob_ind s i j) < length (globs s)"
  shows "(sglob_ind s i j) = (sglob_ind s' i j)"
  using assms
  unfolding store_public_agree_def sglob_ind_def
  by fastforce

lemma store_public_agree_sglob_val_agree:
  assumes "store_public_agree s s'"
          "(sglob_ind s i j) < length (globs s)"
  shows "public_agree (sglob_val s i j) (sglob_val s' i j)"
  using assms list_all2_nthD
  unfolding store_public_agree_def global_public_agree_def sglob_val_def sglob_def sglob_ind_def
  by fastforce

lemma store_public_agree_stypes_eq:
  assumes "store_public_agree s s'"
  shows "(stypes s i j) = (stypes s' i j)"
  using assms
  unfolding store_public_agree_def stypes_def
  by fastforce

lemma store_agree_imp_callcl_cond:
  assumes "store_public_agree s s'"
          "(stab s i (nat_of_int c) = Some cl \<and> stypes s i j \<noteq> cl_type cl) \<or> stab s i (nat_of_int c) = None"
  shows "(stab s' i (nat_of_int c) = Some cl \<and> stypes s' i j \<noteq> cl_type cl) \<or> stab s' i (nat_of_int c) = None"
  using assms store_public_agree_stab_eq store_public_agree_stypes_eq
  by fastforce

lemma public_agree_imp_typeof:
  assumes "public_agree v v'"
  shows "typeof v = typeof v'"
  using assms
  unfolding public_agree_def
  by auto

lemma not_typeof_imp_no_public_agree:
  assumes "typeof v \<noteq> typeof v'"
  shows "\<not>public_agree v v'"
  using assms
  unfolding public_agree_def
  by auto

lemma publics_agree_imp_typeof:
  assumes "publics_agree vs vs'"
  shows "map typeof vs = map typeof vs'"
  using assms
proof (induction vs arbitrary: vs')
  case Nil
  thus ?case
    by blast
next
  case (Cons a vs)
  thus ?case
    using public_agree_imp_typeof
    by (metis list.simps(9) list_all2_Cons1)
qed

lemma public_agree_imp_types_agree_insecure:
  assumes "types_agree_insecure t v"
          "public_agree v v'"
  shows "types_agree_insecure t v'"
  using assms public_agree_imp_typeof
  unfolding types_agree_insecure_def
  by fastforce

lemma public_agree_imp_types_agree:
  assumes "types_agree t v"
          "public_agree v v'"
  shows "types_agree t v'"
  using assms public_agree_imp_typeof
  unfolding types_agree_def
  by fastforce

lemma publics_agree_nil1:
  assumes "publics_agree [] vs"
  shows "vs = []"
  using assms
  by simp

lemma publics_agree_nil2:
  assumes "publics_agree vs []"
  shows "vs = []"
  using assms
  by simp

lemma public_agree_refl: "public_agree v v"
  by (simp add: public_agree_def)

lemma public_agree_public_i32:
  assumes "public_agree (ConstInt32 sec c) v"
  shows "\<exists>c. v = (ConstInt32 sec c)"
  using assms
  by (cases v; auto simp add: public_agree_def typeof_def)

lemma public_agree_public_i64:
  assumes "public_agree (ConstInt64 sec c) v"
  shows "\<exists>c. v = (ConstInt64 sec c)"
  using assms
  by (cases v; auto simp add: public_agree_def typeof_def)

lemma public_agree_public_f32:
  assumes "public_agree (ConstFloat32 c) v"
  shows "\<exists>c. v = (ConstFloat32 c)"
  using assms
  by (cases v; auto simp add: public_agree_def typeof_def)

lemma public_agree_public_f64:
  assumes "public_agree (ConstFloat64 c) v"
  shows "\<exists>c. v = (ConstFloat64 c)"
  using assms
  by (cases v; auto simp add: public_agree_def typeof_def)

lemma publics_agree_refl: "publics_agree vs vs"
  using public_agree_refl
  by (fastforce simp add: list_all2_refl)

lemma publics_agree1:
  assumes "publics_agree [v] es'"
  shows "\<exists>v'. es' = [v']"
  using assms
  by (metis list_all2_Cons1 publics_agree_nil1)

lemma publics_agree_secret1:
  assumes "publics_agree [v] es'"
          "t_sec (typeof v) = Public"
  shows "es' = [v]"
  using assms
  unfolding public_agree_def
  by (simp add: list_all2_Cons1)

lemma publics_agree_public1:
  assumes "publics_agree [v] es'"
          "t_sec (typeof v) = Public"
  shows "\<exists>v'. es' = [v'] \<and> public_agree v v'"
  using assms
  unfolding public_agree_def
  by (simp add: list_all2_Cons1)

lemma memories_public_agree_refl: "memories_public_agree ms ms"
  unfolding memory_public_agree_def
  by (simp add: list_all2_refl)

lemma globals_public_agree_refl: "globals_public_agree gs gs"
  unfolding global_public_agree_def public_agree_def
  by (simp add: list_all2_refl)

lemmas expr_public_agree_refl = expr_public_agree.intros(1)

lemma exprs_public_agree_refl: "exprs_public_agree es es"
  by (simp add: expr_public_agree_refl list_all2_refl)

lemma list_all2_symm:
  assumes "list_all2 P xs ys"
          "(\<And>x y. P x y \<Longrightarrow> P y x)"
  shows "list_all2 P ys xs"
  using assms
  by (simp add: list_all2_conv_all_nth)

lemma public_agree_symm:
  assumes "public_agree v v'"
  shows "public_agree v' v"
  using assms
  unfolding public_agree_def
  by auto

lemma public_agree_trans:
  assumes "public_agree v v'"
          "public_agree v' v''"
  shows "public_agree v v''"
  using assms
  unfolding public_agree_def
  by auto

lemma equivp_public_agree:"equivp public_agree"
  unfolding equivp_def public_agree_def
  by metis

lemma publics_agree_trans:
  assumes "publics_agree vs vs'"
          "publics_agree vs' vs''"
  shows "publics_agree vs vs''"
  using assms list.rel_transp equivp_public_agree
  unfolding transp_def equivp_reflp_symp_transp
  by blast

lemma memories_public_agree_symm:
  assumes "memories_public_agree ms ms'"
  shows "memories_public_agree ms' ms"
  using list_all2_symm assms
  unfolding memory_public_agree_def
  by fastforce

lemma globals_public_agree_symm:
  assumes "globals_public_agree gs gs'"
  shows "globals_public_agree gs' gs"
  using list_all2_symm assms public_agree_symm
  unfolding global_public_agree_def
  by (metis (mono_tags, lifting))

lemma transp_memory_public_agree:"transp memory_public_agree"
  unfolding transp_def memory_public_agree_def
  by fastforce

lemma memories_public_agree_trans:
  assumes "memories_public_agree ms ms'"
          "memories_public_agree ms' ms''"
  shows "memories_public_agree ms ms''"
  using assms list.rel_transp[OF transp_memory_public_agree]
  unfolding transp_def
  by metis

lemma transp_global_public_agree:"transp global_public_agree"
  using equivp_public_agree
  unfolding transp_def global_public_agree_def equivp_reflp_symp_transp
  by metis

lemma globals_public_agree_trans:
  assumes "globals_public_agree gs gs'"
          "globals_public_agree gs' gs''"
  shows "globals_public_agree gs gs''"
  using assms list.rel_transp[OF transp_global_public_agree]
  unfolding transp_def
  by metis

lemma equivp_memories_public_agree: "equivp memories_public_agree"
  using memories_public_agree_refl memories_public_agree_symm memories_public_agree_trans
        equivpI
  unfolding reflp_def symp_def transp_def
  by blast

lemma equivp_globals_public_agree: "equivp globals_public_agree"
  using globals_public_agree_refl globals_public_agree_symm globals_public_agree_trans
        equivpI
  unfolding reflp_def symp_def transp_def
  by blast

lemma list_all2_flip_args:
  assumes "list_all2 (\<lambda>x y. P x y) xs ys"
  shows "list_all2 (\<lambda>y x. P x y) ys xs"
  using assms
  by (simp add: list_all2_conv_all_nth)

lemma publics_agree_symm:
  assumes "publics_agree vs vs'"
  shows "publics_agree vs' vs"
  using public_agree_symm list_all2_symm[OF assms]
  by fastforce

lemma expr_public_agree_symm:
  assumes "expr_public_agree e e'"
  shows "expr_public_agree e' e"
  using assms
proof (induction rule: expr_public_agree.induct)
  case (1 e)
  thus ?case
    using expr_public_agree_refl
    by blast
next
  case (2 v v')
  thus ?case
    using public_agree_symm expr_public_agree.intros(2)
    by auto
next
  case (3 bes bes' tf)
  show ?case
    using expr_public_agree.intros(3) list_all2_mono[OF list_all2_flip_args[OF 3(1)]]
    by fastforce
next
  case (4 bes bes' tf)
  show ?case
    using expr_public_agree.intros(4) list_all2_mono[OF list_all2_flip_args[OF 4(1)]]
    by fastforce
next
  case (5 bes1 bes1' bes2 bes2' tf)
  show ?case
    using expr_public_agree.intros(5) list_all2_mono[OF list_all2_flip_args] 5(1,2)
    by fastforce
next
  case (6 les les' es es' n)
  show ?case
    using expr_public_agree.intros(6)
          list_all2_mono[OF list_all2_flip_args[OF 6(1)]]
          list_all2_mono[OF list_all2_flip_args[OF 6(2)]]
    by fastforce
next
  case (7 vs vs' es es' n iforce)
  show ?case
    using expr_public_agree.intros(7) list_all2_mono[OF list_all2_flip_args[OF 7(2)]]
          publics_agree_symm[OF 7(1)]
    by fastforce
qed

lemma exprs_public_agree_symm:
  assumes "exprs_public_agree es es'"
  shows "exprs_public_agree es' es"
  using assms list_all2_symm expr_public_agree_symm
  by blast

lemma store_public_agree_refl: "store_public_agree s s"
  using memories_public_agree_refl globals_public_agree_refl
  unfolding store_public_agree_def
  by simp

lemma store_public_agree_symm:
  assumes "store_public_agree s s'"
  shows "store_public_agree s' s"
  using assms memories_public_agree_symm globals_public_agree_symm
  unfolding store_public_agree_def
  by simp

lemma store_public_agree_trans:
  assumes "store_public_agree s s'"
          "store_public_agree s' s''"
  shows "store_public_agree s s''"
  using assms memories_public_agree_trans globals_public_agree_trans
  unfolding store_public_agree_def
  by metis

lemma expr_public_agree_imp_public_agree:
  assumes "expr_public_agree ($C v) e"
  shows "\<exists>v'. e = ($C v') \<and> public_agree v v'"
  using assms expr_public_agree.simps public_agree_refl
  by auto

lemma expr_public_agree_block:
  assumes "expr_public_agree ($Block tf es) les"
  shows "\<exists>es'. les = ($Block tf es') \<and> exprs_public_agree ($*es) ($*es')"
  using assms publics_agree_refl exprs_public_agree_refl
  by (fastforce simp add: expr_public_agree.simps)

lemma expr_public_agree_loop:
  assumes "expr_public_agree ($Loop tf es) les"
  shows "\<exists>es'. les = ($Loop tf es') \<and> exprs_public_agree ($*es) ($*es')"
  using assms publics_agree_refl exprs_public_agree_refl
  by (fastforce simp add: expr_public_agree.simps)

lemma expr_public_agree_if:
  assumes "expr_public_agree ($If tf es1 es2) les"
  shows "\<exists>es1' es2'. les = ($If tf es1' es2') \<and> exprs_public_agree ($*es1) ($*es1') \<and> exprs_public_agree ($*es2) ($*es2')"
  using assms publics_agree_refl exprs_public_agree_refl
  by (fastforce simp add: expr_public_agree.simps)

lemma expr_public_agree_local:
  assumes "expr_public_agree (Local n i vs es) les"
  shows "\<exists>vs' es'. les = (Local n i vs' es') \<and> publics_agree vs vs' \<and> exprs_public_agree es es'"
  using assms publics_agree_refl exprs_public_agree_refl
  by (fastforce simp add: expr_public_agree.simps)

lemma expr_public_agree_label:
  assumes "expr_public_agree (Label n les es) e'"
  shows "\<exists>les' es''. e' = (Label n les' es'') \<and> exprs_public_agree les les' \<and> exprs_public_agree es es''"
  using assms publics_agree_refl exprs_public_agree_refl
  by (fastforce simp add: expr_public_agree.simps)

lemmas expr_public_agree_imp_expr_publics_agree = list.rel_intros(2)[OF _ list.rel_intros(1), of expr_public_agree]

lemma expr_public_agree_basic:
  assumes "expr_public_agree ($b_e1) e2"
  shows "\<exists>b_e2. e2 = $b_e2"
  using assms
  by (fastforce simp add: expr_public_agree.simps)

lemma exprs_public_agree_imp_expr_public_agree:
  assumes "exprs_public_agree [e1] [e2]"
  shows "expr_public_agree e1 e2"
  using assms
  by auto

lemmas public_agree_imp_expr_public_agree = expr_public_agree.intros(2)

lemma exprs_public_agree_imp_publics_agree_cons:
  assumes "exprs_public_agree (($C v)#es) es'"
  shows "\<exists>v' es''. es' = (($C v')#es'') \<and> public_agree v v' \<and> exprs_public_agree es es''"
  using assms list_all2_Cons1[of expr_public_agree] expr_public_agree_imp_public_agree
  by fastforce

lemma exprs_public_agree_imp_publics_agree:
  assumes "exprs_public_agree (($$* ves)@es) es'"
  shows "\<exists>ves' es''. es' = (($$* ves')@es'') \<and> publics_agree ves ves' \<and> exprs_public_agree es es''"
  using assms
proof (induction ves arbitrary: es')
  case Nil
  thus ?case
    using publics_agree_refl
    by auto
next
  case (Cons a ves)
  obtain b es'' where es''_def:"es' = ($C b)#es''" "public_agree a b" "exprs_public_agree (($$* ves) @ es) es''"
    using Cons(2) exprs_public_agree_imp_publics_agree_cons
    by fastforce
  moreover
  obtain ves' es''' where "es'' = ($$* ves') @ es'''" "publics_agree ves ves'" "exprs_public_agree es es'''"
    using Cons(1)[OF es''_def(3)]
    by blast
  ultimately
  have "es' = ($$* b#ves') @ es''' \<and> publics_agree (a#ves) (b#ves') \<and> exprs_public_agree es es'''"
    by (simp)
  thus ?case
    by blast
qed

lemma exprs_public_agree_imp_publics_agree1:
  assumes "exprs_public_agree (($$* ves)@[e]) es'"
  shows "\<exists>ves' e'. es' = (($$* ves')@[e']) \<and> publics_agree ves ves' \<and> expr_public_agree e e'"
  using exprs_public_agree_imp_publics_agree[OF assms]
  by (metis list_all2_Cons1 list_all2_Nil)

lemma exprs_public_agree_imp_publics_agree1_const0:
  assumes "exprs_public_agree [e] es'"
  shows "\<exists>e'. es' = [e'] \<and> expr_public_agree e e'"
  using exprs_public_agree_imp_publics_agree1[of "[]" e es'] assms
  by fastforce

lemma b_e_exprs_public_agree_imp_publics_agree1_const0:
  assumes "exprs_public_agree ($*[b_e]) es'"
  shows "\<exists>b_e'. es' = [$b_e'] \<and> expr_public_agree ($b_e) ($b_e')"
proof -
  have "exprs_public_agree [$b_e] es'"
    using assms
    by simp
  then obtain e' where "es' = [e']" "expr_public_agree ($b_e) e'"
    using exprs_public_agree_imp_publics_agree1_const0
    by blast
  thus ?thesis
    by (cases e') (fastforce simp add: expr_public_agree.simps)+
qed

lemma exprs_public_agree_trap_imp_is_trap:
  assumes "exprs_public_agree [Trap] es"
  shows "es = [Trap]"
  using exprs_public_agree_imp_publics_agree1_const0[OF assms]
  by (fastforce simp add: expr_public_agree.simps)

lemma exprs_public_agree_imp_publics_agree1_const1:
  assumes "exprs_public_agree [($C v),e] es'"
  shows "\<exists>v' e'. es' = [($C v'),e'] \<and> public_agree v v' \<and> expr_public_agree e e'"
  using exprs_public_agree_imp_publics_agree1[of "[v]" e es'] assms publics_agree1 exprs_public_agree_imp_publics_agree_cons
  by fastforce

lemma exprs_public_agree_imp_publics_agree1_const2:
  assumes "exprs_public_agree [($C v1),($C v2),e] es'"
  shows "\<exists>v1' v2' e'. es' = [($C v1'),($C v2'),e'] \<and>
                      public_agree v1 v1' \<and>
                      public_agree v2 v2' \<and>
                      expr_public_agree e e'"
  using exprs_public_agree_imp_publics_agree_cons exprs_public_agree_imp_publics_agree1_const1 assms
  by blast

lemma exprs_public_agree_imp_publics_agree1_const3:
  assumes "exprs_public_agree [($C v1),($C v2),($C v3),e] es'"
  shows "\<exists>v1' v2' v3' e'. es' = [($C v1'),($C v2'),($C v3'),e'] \<and>
                      public_agree v1 v1' \<and>
                      public_agree v2 v2' \<and>
                      public_agree v3 v3' \<and>
                      expr_public_agree e e'"
  using exprs_public_agree_imp_publics_agree_cons exprs_public_agree_imp_publics_agree1_const2 assms
  by blast

lemma publics_agree_imp_exprs_public_agree_cons:
  assumes "public_agree v v'"
          "exprs_public_agree es es'"
  shows "exprs_public_agree (($C v)#es) (($C v')#es')"
  using assms(2) list.rel_intros(2) public_agree_imp_expr_public_agree[OF assms(1)]
  by fastforce

lemma publics_agree_imp_exprs_public_agree:
  assumes "publics_agree ves ves'"
          "exprs_public_agree es es'"
  shows "exprs_public_agree (($$* ves)@es) (($$* ves')@es')"
  using assms
proof (induction ves arbitrary: ves')
  case Nil
  thus ?case
    using publics_agree_nil1
    by fastforce
next
  case (Cons a ves)
  obtain b ves'' where ves''_def:"ves' = b#ves''" "public_agree a b" "publics_agree ves ves''"
    using Cons(2) list_all2_Cons1[of public_agree]
    by fastforce
  show ?case
    using Cons(1)[OF ves''_def(3) Cons(3)] ves''_def(1,2) publics_agree_imp_exprs_public_agree_cons
    by simp
qed

lemma expr_public_agree_const:
  assumes "expr_public_agree e e'"
          "is_const e"
  shows "is_const e'"
  using expr_public_agree_imp_public_agree assms e_type_const_unwrap
  unfolding is_const_def
  by fastforce

lemma exprs_public_agree_const_list:
  assumes "exprs_public_agree es es'"
          "const_list es"
  shows "const_list es'"
  using assms
proof (induction es arbitrary: es')
  case Nil
  thus ?case
  by simp
next
  case (Cons a es)
  thus ?case
    by (metis append_Nil2 exprs_public_agree_imp_publics_agree list_all2_Nil
              e_type_const_conv_vs is_const_list)
qed

lemma exprs_public_agree_basic:
  assumes "exprs_public_agree ($* ves) es'"
  shows "\<exists>ves'. es' = ($* ves')"
  using assms
proof (induction ves arbitrary: es')
  case Nil
  thus ?case
    by simp
next
  case (Cons a ves)
  thus ?case
    using list_all2_Cons1[of expr_public_agree "$a" "$*ves" es'] inj_basic expr_public_agree_basic
    by (metis list.map(2))
qed

lemma exprs_public_agree_app3:
  assumes "exprs_public_agree (vs @ es @ es') les"
  shows "\<exists>vs_a es_a es'_a. les = vs_a @ es_a @ es'_a \<and>
                           exprs_public_agree vs vs_a \<and>
                           exprs_public_agree es es_a \<and>
                           exprs_public_agree es' es'_a"
  using list_all2_append1[of expr_public_agree] assms
  by fastforce

lemma store_public_agree_imp_store_typing:
  assumes "store_typing s \<S>"
          "store_public_agree s s'"
  shows "store_typing s' \<S>"
proof -
  obtain \<C>s tfs ns ms tgs where \<S>_def:"\<S> = \<lparr>s_inst = \<C>s, s_funcs = tfs, s_tab = ns, s_mem = ms, s_globs = tgs\<rparr>"
    using s_context.cases
    by blast
  obtain insts fs tclss bss gs where s_def:"s = \<lparr>s.inst = insts, s.funcs = fs, s.tab = tclss, s.mem = bss, s.globs = gs\<rparr>"
    using s.cases
    by blast
  obtain insts' fs' tclss' bss' gs' where s'_def:"s' = \<lparr>s.inst = insts', s.funcs = fs', s.tab = tclss', s.mem = bss', s.globs = gs'\<rparr>"
    using s.cases
    by blast
  have "list_all2 (inst_typing \<S>) insts' \<C>s"
       "list_all2 (cl_typing \<S>) fs' tfs"
       "list_all (tab_agree \<S>) (concat tclss')"
       "list_all2 (\<lambda> tcls n. n \<le> length tcls) tclss' ns"
    using assms \<S>_def s_def s'_def
    unfolding store_typing.simps store_public_agree_def
    by auto
  moreover
  have "list_all2 mem_agree bss' ms"
  proof -
    have "list_all2 (\<lambda> (bs,sec) (m,sec'). m \<le> mem_size bs \<and> sec = sec') bss ms"
      using assms(1) \<S>_def s_def
      unfolding store_typing.simps mem_agree_def
      by blast
    moreover
    have "list_all2 (\<lambda> (bs,sec) (bs',sec'). mem_size bs = mem_size bs' \<and> sec = sec') bss bss'"
      using s_def s'_def assms(2) list_all2_mono
      unfolding store_public_agree_def memory_public_agree_def
      by fastforce
    ultimately
    show ?thesis
      by (auto simp add: case_prod_beta' list_all2_conv_all_nth mem_agree_def)
  qed
  moreover
  have "list_all2 glob_agree gs' tgs"
  proof -
    have "list_all2 glob_agree gs tgs"
      using assms(1) \<S>_def s_def
      unfolding store_typing.simps
      by blast
    moreover
    have "list_all2 (\<lambda>x y. g_mut x = g_mut y \<and> public_agree (g_val x) (g_val y)) gs gs'"
      using s_def s'_def assms(2)
      unfolding store_public_agree_def global_public_agree_def
      by fastforce
    ultimately
    show ?thesis
      using public_agree_imp_typeof
      unfolding glob_agree_def
      by (auto simp add: list_all2_conv_all_nth)
  qed
  ultimately
  show ?thesis
    using \<S>_def s'_def store_typing.intros
    by blast
qed

lemma exprs_public_agree_imp_lholed_public_agree:
  assumes "Lfilled k lholed es les"
          "exprs_public_agree les les'"
    shows "\<exists>lholed' es'. lholed_public_agree lholed lholed' \<and>
                         exprs_public_agree es es' \<and>
                         Lfilled k lholed' es' les'"
  using assms
proof (induction arbitrary: les' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  obtain vs_a es_a es'_a where les'_def:"les' = vs_a @ es_a @ es'_a"
                                        "exprs_public_agree vs vs_a"
                                        "exprs_public_agree es es_a"
                                        "exprs_public_agree es' es'_a"
    using exprs_public_agree_app3[OF L0(3)]
    by fastforce
  have "lholed_public_agree lholed (LBase vs_a es'_a)"
    using L0(2) les'_def(2,4) lholed_public_agree.intros(1)
    by blast
  thus ?case
    using les'_def(1,2,3) Lfilled.intros(1) L0(1) exprs_public_agree_const_list[OF les'_def(2)]
    by fastforce
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  obtain vs_a les_a es''_a where les'_def:"les' = vs_a @ les_a @ es''_a"
                                         "exprs_public_agree vs vs_a"
                                         "exprs_public_agree [Label n es' lfilledk] les_a"
                                         "exprs_public_agree es'' es''_a"
    using exprs_public_agree_app3[OF LN(5)]
    by fastforce
  obtain es'_a lfilledk_a where les_a_def:"les_a = [Label n es'_a lfilledk_a]"
                                          "exprs_public_agree es' es'_a"
                                          "exprs_public_agree lfilledk lfilledk_a"
    using expr_public_agree_label les'_def(3) exprs_public_agree_imp_publics_agree1_const0
    by blast
  then obtain l' es_a where l'_def:"lholed_public_agree l l'"
                                   "exprs_public_agree es es_a"
                                   "Lfilled k l' es_a lfilledk_a"
    using LN(4)
    by blast
  hence "lholed_public_agree lholed (LRec vs_a n es'_a l' es''_a)"
    using LN(2) les'_def(2,4) les_a_def(2) lholed_public_agree.intros(2)
    by blast
  thus ?case
    using les_a_def(1) les'_def(1) l'_def(2,3) Lfilled.intros(2)
          exprs_public_agree_const_list[OF les'_def(2) LN(1)]
    by blast
qed

lemma lholed_public_agree_imp_exprs_public_agree:
  assumes "lholed_public_agree lholed lholed'"
          "Lfilled k lholed es les"
          "exprs_public_agree es es'"
  shows "\<exists>les'. Lfilled k lholed' es' les' \<and> exprs_public_agree les les'"
  using assms(2,1,3)
proof (induction arbitrary: es' lholed' rule: Lfilled.induct)
  case (L0 vs lholed bes es)
  obtain vs_a bes_a where lholed'_def:"lholed' = LBase vs_a bes_a"
                                      "exprs_public_agree vs vs_a"
                                      "exprs_public_agree bes bes_a"
                                      "const_list vs_a"
    using L0(1,2,3) lholed_public_agree.simps[of lholed lholed']
          exprs_public_agree_const_list[of vs]
    by fastforce
  show ?case
    using Lfilled.intros(1)[OF lholed'_def(4,1), of es'] L0(4) lholed'_def(2,3)
          list_all2_appendI[of expr_public_agree]
    by auto
next
  case (LN vs lholed n lres l es'' k es lfilledk)
  obtain vs_a lres_a l_a es''_a where lholed'_def:"lholed' = LRec vs_a n lres_a l_a es''_a"
                                                  "exprs_public_agree vs vs_a"
                                                  "exprs_public_agree lres lres_a"
                                                  "exprs_public_agree es'' es''_a"
                                                  "lholed_public_agree l l_a"
                                                  "const_list vs_a"
    using LN(1,2,5) lholed_public_agree.simps[of lholed lholed']
          exprs_public_agree_const_list[of vs]
    by fastforce
  obtain lfilledk' where lfilledk:"Lfilled k l_a es' lfilledk'" "exprs_public_agree lfilledk lfilledk'"
    using LN(4,6) lholed'_def(5)
    by blast
  have "exprs_public_agree [Label n lres lfilledk] [Label n lres_a lfilledk']"
    using lholed'_def(3) lfilledk(2) expr_public_agree.intros(6)
    by blast
  thus ?case
    using Lfilled.intros(2)[OF lholed'_def(6,1) lfilledk(1)] lholed'_def(2,4)
          list_all2_appendI[of expr_public_agree]
    by auto
qed

method solve_exprs_public_agree_imp_b_e_typing_trivial =
  (match premises in A:"exprs_public_agree ($* [b_e]) ($* bes')"
                 and B:"\<C> \<turnstile> [b_e] : tf"
         for b_e bes' \<C> tf \<Rightarrow>
     \<open>solves \<open>insert b_e_exprs_public_agree_imp_publics_agree1_const0[OF A] B;
              fastforce simp add: expr_public_agree.simps\<close>\<close>)

lemma exprs_public_agree_imp_b_e_typing:
  assumes "\<C> \<turnstile> bes : tf"
          "exprs_public_agree ($*bes) ($*bes')"
  shows "\<C> \<turnstile> bes' : tf"
  using assms(1,2,1)
proof (induction arbitrary: bes' rule: b_e_typing.induct)
  case (const \<C> v)
  obtain v' where "bes' = [C v']"
                  "public_agree v v'"
    using exprs_public_agree_imp_publics_agree1_const0[of "$C v"] expr_public_agree_imp_public_agree
          const(1)
    by fastforce
  thus ?case
    using public_agree_imp_typeof b_e_typing.intros(1)
    by fastforce
next
  case (block tf tn tm \<C> es)
  obtain e' where e'_def:"($*bes') = [e']"
                         "expr_public_agree ($Block tf es) e'"
    using block(4) exprs_public_agree_imp_publics_agree1_const0[of "$Block tf es" "$*bes'"]
    by fastforce
  obtain es' where "e' = ($Block tf es')"
                   "exprs_public_agree ($*es) ($*es')"
    using e'_def(2) exprs_public_agree_refl[of "($*es)"]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using block(3)[OF _ block(2)] e'_def(1) b_e_typing.block block(1)
    by fastforce
next
  case (loop tf tn tm \<C> es)
  obtain e' where e'_def:"($*bes') = [e']"
                         "expr_public_agree ($Loop tf es) e'"
    using loop(4) exprs_public_agree_imp_publics_agree1_const0[of "$Loop tf es" "$*bes'"]
    by fastforce
  obtain es' where "e' = ($Loop tf es')"
                   "exprs_public_agree ($*es) ($*es')"
    using e'_def(2) exprs_public_agree_refl[of "($*es)"]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using loop(3)[OF _ loop(2)] e'_def(1) b_e_typing.loop loop(1)
    by fastforce
next
  case (if_wasm tf tn tm \<C> es1 es2)
  obtain e' where e'_def:"($*bes') = [e']"
                         "expr_public_agree ($If tf es1 es2) e'"
    using if_wasm(6) exprs_public_agree_imp_publics_agree1_const0[of "$If tf es1 es2" "$*bes'"]
    by fastforce
  obtain es1' es2' where p:"e' = ($If tf es1' es2')"
                         "exprs_public_agree ($*es1) ($*es1')"
                         "exprs_public_agree ($*es2) ($*es2')"
    using e'_def(2) exprs_public_agree_refl[of "($*es1)"] exprs_public_agree_refl[of "($*es2)"]
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using e'_def(1) b_e_typing.if_wasm[OF if_wasm(1) if_wasm(4)[OF _ if_wasm(2)] if_wasm(5)[OF _ if_wasm(3)]]
    by fastforce
next
  case (empty \<C>)
  thus ?case
    by simp
next
  case (composition \<C> es t1s t2s e t3s)
  obtain us vs where
        bes'_def:"($* bes') = (us @ vs)"
                 "exprs_public_agree ($* es) us"
                 "exprs_public_agree ($* [e]) vs"
    using list_all2_append1[of expr_public_agree "$* es" "$*[e]" "($* bes')"] composition(5)
    by fastforce
  have "\<exists>b_us. us = $*b_us" (*TODO: there should be a lemma for this*)
    using bes'_def(1)
    apply (induction us arbitrary: bes')
     apply simp
    apply (metis (no_types, hide_lams) Cons_eq_map_D append_Cons list.simps(9))
    done
  then obtain b_us b_v where 1:"($* bes') = (($*b_us) @ ($*[b_v]))"
                              "exprs_public_agree ($* es) ($*b_us)"
                              "exprs_public_agree ($* [e]) ($*[b_v])"
    using b_e_exprs_public_agree_imp_publics_agree1_const0[OF bes'_def(3)] bes'_def
    by (metis to_e_list_1)
  thus ?case
    using b_e_typing.composition[OF composition(3)[OF 1(2) composition(1)] composition(4)[OF 1(3) composition(2)]]
          map_injective[OF _ inj_basic, of bes' "b_us @ [b_v]"]
    by fastforce
next
  case (weakening \<C> es t1s t2s ts)
  show ?case
    using weakening(2)[OF weakening(3,1)] b_e_typing.weakening
    by fastforce
qed solve_exprs_public_agree_imp_b_e_typing_trivial+

lemma exprs_public_agree_imp_e_typing_s_typing:
  "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts') \<Longrightarrow> exprs_public_agree es es' \<Longrightarrow> \<S>\<bullet>\<C> \<turnstile> es' : (ts _> ts')"
  "\<S>\<bullet>tr\<bullet>rs \<tturnstile>_i vs;es : ts' \<Longrightarrow> publics_agree vs vs' \<Longrightarrow> exprs_public_agree es es' \<Longrightarrow> \<S>\<bullet>tr\<bullet>rs \<tturnstile>_i vs';es' : ts'"
proof (induction es "(ts _> ts')" and es ts' arbitrary: ts ts' es' and vs' es' rule: e_typing_s_typing.inducts)
  case (1 \<C> b_es tf \<S>)
  show ?case
    using 1(2) exprs_public_agree_basic[OF 1(2)]
          e_typing_s_typing.intros(1)[OF exprs_public_agree_imp_b_e_typing[OF 1(1)]]
    by blast
next
  case (2 \<S> \<C> es t2s e)
  thus ?case
    using e_typing_s_typing.intros(2)
    by (metis (full_types) e_type_comp_conc list_all2_append1)
next
  case (3 \<S> \<C> es t1s t2s ts)
  thus ?case
    using e_typing_s_typing.intros(3)
    by blast
next
  case (4 \<S> \<C> tf)
  thus ?case
    using e_typing_s_typing.intros(4) exprs_public_agree_trap_imp_is_trap
    by blast
next
  case (5 \<S> \<C> ts i vs es n)
  obtain vs' es'' where "es' = [Local n i vs' es'']"
                        "publics_agree vs vs'"
                        "exprs_public_agree es es''"
    using 5(4) exprs_public_agree_imp_publics_agree1_const0 expr_public_agree_local
    by blast
  thus ?case
    using e_typing_s_typing.intros(5)[OF 5(2)] 5(3)
    by blast
next
  case (6 \<C> tr \<S> cl)
  have "es' = [Callcl cl]"
    using 6(3) exprs_public_agree_imp_publics_agree1_const0
    by (fastforce simp add: expr_public_agree.simps)
  thus ?case
    using e_typing_s_typing.intros(6) 6(1,2)
    by blast
next
  case (7 \<S> \<C> e0s ts t2s es n)
  obtain les' es'' where "es' = [Label n les' es'']"
                         "exprs_public_agree e0s les'"
                         "exprs_public_agree es es''"
    using 7(6) exprs_public_agree_imp_publics_agree1_const0 expr_public_agree_label
    by blast
  thus ?case
    using e_typing_s_typing.intros(7) 7(2,4,5)
    by blast
next
  case (8 i \<S> tvs vs \<C> rs es ts)
  have "tvs = map typeof vs'"
    using 8(2,7) publics_agree_imp_typeof
    by blast
  thus ?case
    using e_typing_s_typing.intros(8)[OF 8(1) _ 8(3) 8(5)[OF 8(8)] 8(6)]
    by blast
qed

lemma exprs_public_agree_imp_config_typing:
  assumes "\<turnstile>_i s;vs;es : ts"
          "store_public_agree s s'"
          "publics_agree vs vs'"
          "exprs_public_agree es es'"
  shows "\<turnstile>_i s';vs';es' : ts"
  using assms(1) store_public_agree_imp_store_typing[OF _ assms(2)] publics_agree_imp_typeof[OF assms(3)]
        exprs_public_agree_imp_e_typing_s_typing(2)[OF _ assms(3,4)]
  unfolding config_typing.simps
  by fastforce

fun config_indistinguishable :: "(s \<times> v list \<times> e list) \<Rightarrow> (s \<times> v list \<times> e list) \<Rightarrow> bool" ("_ \<sim>'_c _" 60) where
  "((s,vs,es) \<sim>_c (s',vs',es')) = (store_public_agree s s' \<and> publics_agree vs vs' \<and> exprs_public_agree es es')"

lemma config_indistinguishable_imp_config_typing:
  assumes "\<turnstile>_i s;vs;es : ts"
          "(s,vs,es) \<sim>_c (s',vs',es')"
  shows "\<turnstile>_i s';vs';es' : ts"
  using exprs_public_agree_imp_config_typing[OF assms(1)] assms(2)
  by simp
  
lemma expr_public_agree_trans:
  assumes "expr_public_agree a b"
          "expr_public_agree b c"
  shows "expr_public_agree a c"
  using assms
proof -
note hyp_trans =
  list_all2_trans[of "(\<lambda>x1 x2. expr_public_agree x1 x2 \<and> (\<forall>x. expr_public_agree x2 x \<longrightarrow> expr_public_agree x1 x))" expr_public_agree expr_public_agree]
show ?thesis
  using assms
proof (induction arbitrary: c rule: expr_public_agree.induct)
  case (1 e)
  thus ?case
    by simp
next
  case (2 v v')
  {
    fix e v v'
    assume local_assms:"public_agree v v'" "expr_public_agree ($C v) e"
    then obtain v'' where "e = $C v''"
                          "public_agree v v''"
      using expr_public_agree_imp_public_agree
      by blast
    hence "expr_public_agree ($C v') e"
      using equivp_public_agree expr_public_agree_imp_public_agree
      by (metis equivp_def local_assms(1) public_agree_imp_expr_public_agree)
  }
  thus ?case
    using 2 public_agree_symm
    by blast
next
  case (3 bes bes' tf)
  obtain bes'' where "c = ($Block tf bes'')"
                     "exprs_public_agree ($*bes') ($*bes'')"
    using 3(2) expr_public_agree_block
    by blast
  thus ?case
    using 3(1) hyp_trans expr_public_agree.intros(3)
    by simp
next
  case (4 bes bes' tf)
  obtain bes'' where "c = ($Loop tf bes'')"
                     "exprs_public_agree ($*bes') ($*bes'')"
    using 4(2) expr_public_agree_loop
    by blast
  thus ?case
    using expr_public_agree.intros(4) 4(1) hyp_trans
    by simp
next
  case (5 bes1 bes1' bes2 bes2' tf)
  obtain bes1'' bes2'' where "c = ($If tf bes1'' bes2'')"
                             "exprs_public_agree ($*bes1') ($*bes1'')"
                             "exprs_public_agree ($*bes2') ($*bes2'')"
    using 5(3) expr_public_agree_if
    by blast
  thus ?case
    using expr_public_agree.intros(5) 5(1,2) hyp_trans
    by simp
next
  case (6 les les' es es' n)
  obtain les'' es'' where "c = (Label n les'' es'')"
                          "exprs_public_agree les' les''"
                          "exprs_public_agree es' es''"
    using 6(3) expr_public_agree_label
    by blast
  thus ?case
    using expr_public_agree.intros(6)  6(1,2) hyp_trans
    by simp
next
  case (7 vs vs' es es' n i)
  obtain vs'' es'' where c_def:"c = (Local n i vs'' es'')"
                               "publics_agree vs' vs''"
                               "exprs_public_agree es' es''"
    using 7(3) expr_public_agree_local
    by blast
  moreover
  hence "publics_agree vs vs''"
    using 7(1) equivp_transp[OF equivp_public_agree] list_all2_trans[OF _ 7(1) c_def(2), of public_agree]
    by fastforce
  thus ?case
    using expr_public_agree.intros(7) 7(1,2) hyp_trans c_def
    unfolding transp_def
    by fastforce
qed
qed

lemma equivp_expr_public_agree:"equivp expr_public_agree"
  using expr_public_agree_trans expr_public_agree_refl expr_public_agree_symm equivpI
  unfolding reflp_def symp_def transp_def
  by blast

lemma equivp_exprs_public_agree:"equivp exprs_public_agree"
  using equivp_expr_public_agree list.rel_reflp list.rel_symp list.rel_transp
  unfolding equivp_reflp_symp_transp
  by blast

lemma exprs_public_agree_trans:
  assumes "exprs_public_agree es es'"
          "exprs_public_agree es' es''"
  shows "exprs_public_agree es es''"
  using assms equivp_exprs_public_agree
  unfolding equivp_reflp_symp_transp transp_def
  by blast

lemma equivp_store_public_agree:"equivp store_public_agree"
  using store_public_agree_trans store_public_agree_refl store_public_agree_symm equivpI
  unfolding reflp_def symp_def transp_def
  by blast

lemma config_indistinguishable_refl:"config_indistinguishable c c"
  using store_public_agree_refl publics_agree_refl exprs_public_agree_refl
  by (cases c) simp

lemma config_indistinguishable_symm:
  assumes "c \<sim>_c c'"
  shows "c' \<sim>_c c"
  using assms store_public_agree_symm publics_agree_symm exprs_public_agree_symm
  by (cases c) (cases c'; simp)

lemma config_indistinguishable_trans:
  assumes "c \<sim>_c c'"
          "c' \<sim>_c c''"
  shows "c \<sim>_c c''"
  using assms store_public_agree_trans publics_agree_trans exprs_public_agree_trans
  apply (cases c)
  apply (cases c')
  apply (cases c'')
  apply simp
  apply metis
  done

lemma equivp_config_indistinguishable:"equivp config_indistinguishable"
  using config_indistinguishable_trans config_indistinguishable_refl config_indistinguishable_symm equivpI
  unfolding reflp_def symp_def transp_def
  by blast

definition config_untrusted_equiv :: "((s \<times> v list \<times> e list) \<times> nat) \<Rightarrow> ((s \<times> v list \<times> e list) \<times> nat) \<Rightarrow> bool" ("_ \<sim>'_cp _" 60) where
  "config_untrusted_equiv \<equiv>
    (\<lambda>((s,vs,es),i) ((s',vs',es'),i'). ((s,vs,es) \<sim>_c (s',vs',es')) \<and>
                                       (\<exists>ts. \<turnstile>_i s;vs;es : (Untrusted,ts)) \<and>
                                       i = i')"

lemma ex_config_untrusted_equiv_refl: "\<exists>s vs es i. (((s,vs,es),i) \<sim>_cp ((s,vs,es),i))"
proof -
  obtain \<S> \<C>s e_s e_inst where \<S>_def:
    "\<S> = \<lparr>s_inst = \<C>s, s_funcs = [], s_tab = [], s_mem = [], s_globs = []\<rparr>"
    "\<C>s = [\<lparr>trust_t = Untrusted, types_t = [], func_t = [], global = [], table = None, memory = None, local = [], label = [], return = None\<rparr>]"
    "e_s = \<lparr>inst = e_inst, funcs = [], tab = [], mem = [], globs = []\<rparr>"
    "e_inst = [\<lparr>types = [], funcs = [], tab = None, mem = None, globs = []\<rparr>]"
    by blast
  hence "list_all2 (inst_typing \<S>) [\<lparr>types = [], funcs = [], tab = None, mem = None, globs = []\<rparr>] \<C>s"
    unfolding inst_typing.simps memi_agree_def
    by auto
  hence "\<turnstile>_0 e_s;[];[] : (Untrusted,[])"
    using e_typing_s_typing.intros(1)[OF b_e_typing.intros(35)] \<S>_def
    unfolding config_typing.simps store_typing.simps s_typing.simps
    by auto
  moreover
  have "(e_s,[],[]) \<sim>_c (e_s,[],[])"
    using \<S>_def(3,4) store_public_agree_def
    by auto
  ultimately
  show ?thesis
    unfolding config_untrusted_equiv_def
    by simp blast
qed

lemma config_untrusted_equiv_symm:
  assumes "((s,vs,es),i) \<sim>_cp ((s',vs',es'),i')"
  shows "((s',vs',es'),i') \<sim>_cp ((s,vs,es),i)"
proof -
  have "i' = i"
    using assms
    unfolding config_untrusted_equiv_def
    by auto
  moreover
  have "(s',vs',es') \<sim>_c (s,vs,es)"
    using assms config_indistinguishable_symm
    unfolding config_untrusted_equiv_def
    by (simp del: config_indistinguishable.simps)
  moreover
  have "(\<exists>ts. \<turnstile>_i s';vs';es' : (Untrusted,ts))"
    using assms config_indistinguishable_imp_config_typing
    unfolding config_untrusted_equiv_def
    by fastforce
  ultimately
  show ?thesis
    unfolding config_untrusted_equiv_def
    by fastforce
qed

lemma config_untrusted_equiv_trans:
  assumes "((s,vs,es),i) \<sim>_cp ((s'',vs'',es''),i'')"
          "((s'',vs'',es''),i'') \<sim>_cp ((s',vs',es'),i')"
  shows "((s,vs,es),i) \<sim>_cp ((s',vs',es'),i')"
proof -
  have "i = i'"
    using assms
    unfolding config_untrusted_equiv_def
    by auto
  moreover
  have "(s,vs,es) \<sim>_c (s',vs',es')"
    using assms config_indistinguishable_trans
    unfolding config_untrusted_equiv_def
    by (simp del: config_indistinguishable.simps)  blast
  ultimately
  show ?thesis
    using assms(1)
    unfolding config_untrusted_equiv_def
    by fastforce
qed

lemma part_equivp_config_untrusted_equiv:"part_equivp config_untrusted_equiv"
  using part_equivpI[of config_untrusted_equiv] ex_config_untrusted_equiv_refl
        config_untrusted_equiv_symm config_untrusted_equiv_trans
  unfolding symp_def transp_def
  by fast

definition config_inst_length :: "(s \<times> v list \<times> e list) \<Rightarrow> nat" where
  "config_inst_length c = length (inst (fst c))"

quotient_type config_untrusted_quot = "((s \<times> v list \<times> e list) \<times> nat)" / partial:config_untrusted_equiv
  by (rule part_equivp_config_untrusted_equiv)

lift_definition config_untrusted_quot_inst_length :: "config_untrusted_quot \<Rightarrow> nat" is "(\<lambda>(c,i). length (inst (fst c)))"
proof -
  fix prod1::"((s \<times> v list \<times> e list) \<times> nat)" and prod2::"((s \<times> v list \<times> e list) \<times> nat)"
  assume assms:"config_untrusted_equiv prod1 prod2"
  show "(case prod1 of
        (c, i) \<Rightarrow> length (inst (fst c))) =
       (case prod2 of
        (c, i) \<Rightarrow> length (inst (fst c)))"
  proof (cases prod1; cases prod2)
    fix a1 b1 a2 b2
    assume local_assms:"prod1 = (a1,b1)" "prod2 = (a2,b2)"
    thus ?thesis
      using assms
      unfolding config_untrusted_equiv_def
      apply (cases a1; cases a2)
      apply simp
      apply (metis config_typing.simps store_public_agree_imp_store_typing store_typing_imp_inst_length_eq)
      done
  qed
qed

lift_definition config_untrusted_quot_store_typing :: "config_untrusted_quot \<Rightarrow> s_context \<Rightarrow> bool" is "(\<lambda>(c,i) \<S>. store_typing (fst c) \<S>)"
proof -
  fix prod1::"((s \<times> v list \<times> e list) \<times> nat)" and prod2::"((s \<times> v list \<times> e list) \<times> nat)"
  assume assms:"config_untrusted_equiv prod1 prod2"
  show "(case prod1 of
        (c, i) \<Rightarrow> store_typing (fst c)) =
       (case prod2 of
        (c, i) \<Rightarrow> store_typing (fst c))"
  proof (cases prod1; cases prod2)
    fix a1 b1 a2 b2
    assume local_assms:"prod1 = (a1,b1)" "prod2 = (a2,b2)"
    thus ?thesis
      using fun_eq_iff[symmetric, of "store_typing (fst a1)" "store_typing (fst a2)"]
            assms
      unfolding config_untrusted_equiv_def
      apply (cases a1; cases a2)
      apply simp
      apply (metis store_public_agree_imp_store_typing store_public_agree_symm)
      done
  qed
qed

lift_definition config_untrusted_quot_e_typing :: "[s_context, t_context, config_untrusted_quot, tf] \<Rightarrow> bool" is "(\<lambda>\<S> \<C> (c,i) tf. (\<S>\<bullet>\<C> \<turnstile> (snd (snd c)) : tf))"
proof -
  fix \<S> \<C> and prod1::"((s \<times> v list \<times> e list) \<times> nat)" and prod2::"((s \<times> v list \<times> e list) \<times> nat)"
  assume assms:"config_untrusted_equiv prod1 prod2"
  show "(case prod1 of
        (c, i) \<Rightarrow>
          e_typing \<S>
           \<C> (snd (snd c))) =
       (case prod2 of
        (c, i) \<Rightarrow>
          e_typing \<S>
           \<C> (snd (snd c)))"
  proof (cases prod1; cases prod2)
    fix a1 b1 a2 b2
    assume local_assms:"prod1 = (a1,b1)" "prod2 = (a2,b2)"
    thus ?thesis
      using assms
            fun_eq_iff[symmetric, of "e_typing \<S> \<C> (snd (snd a1))" "e_typing \<S> \<C> (snd (snd a2))"]
      unfolding config_untrusted_equiv_def
      apply (cases a1; cases a2)
      apply simp
      apply (metis exprs_public_agree_imp_e_typing_s_typing(1) exprs_public_agree_symm tf.exhaust)
      done
  qed
qed

lift_definition config_untrusted_quot_s_typing :: "[s_context, trust, (t list) option, config_untrusted_quot, t list] \<Rightarrow> bool" is "(\<lambda>\<S> tr rs (c,i) ts. (\<S>\<bullet>tr\<bullet>rs \<tturnstile>_i (fst (snd c));(snd (snd c)) : ts))"
proof -
  fix \<S> tr rs prod1 prod2
  assume assms:"config_untrusted_equiv prod1 prod2"
  show "(case prod1 of
        (c, i) \<Rightarrow>
          s_typing \<S> tr
           rs i (fst (snd c))
           (snd (snd c))) =
       (case prod2 of
        (c, i) \<Rightarrow>
          s_typing \<S> tr
           rs i (fst (snd c))
           (snd (snd c)))"
  proof (cases prod1; cases prod2)
    fix a1 b1 a2 b2
    assume local_assms:"prod1 = (a1,b1)" "prod2 = (a2,b2)"
    thus ?thesis
      using assms
            fun_eq_iff[symmetric, of "s_typing \<S> tr rs b1 (fst (snd a1)) (snd (snd a1))"
                                       "s_typing \<S> tr rs b2 (fst (snd a2)) (snd (snd a2))"]
      unfolding config_untrusted_equiv_def
      apply (cases a1; cases a2)
      apply simp
      apply (meson exprs_public_agree_imp_e_typing_s_typing(2) exprs_public_agree_symm publics_agree_symm)
      done
  qed
qed

lift_definition config_untrusted_quot_config_typing :: "[config_untrusted_quot, trust \<times> t list] \<Rightarrow> bool" is "(\<lambda>((s,vs,es),i) ts. (\<turnstile>_i s;vs;es : ts))"
proof -
  fix prod1 prod2
  assume assms:"config_untrusted_equiv prod1 prod2"
  show "(case prod1 of
        (x, xa) \<Rightarrow>
          (case x of
           (s, vs, es) \<Rightarrow>
             \<lambda>i. config_typing i s vs es)
           xa) =
       (case prod2 of
        (x, xa) \<Rightarrow>
          (case x of
           (s, vs, es) \<Rightarrow>
             \<lambda>i. config_typing i s vs es)
           xa)"
  proof (cases prod1; cases prod2)
    fix a1 b1 a2 b2
    assume local_assms:"prod1 = (a1,b1)" "prod2 = (a2,b2)"
    thus ?thesis
    using assms config_indistinguishable_symm
          fun_eq_iff[symmetric, of "(case a1 of (s, xa, xb) \<Rightarrow> config_typing b1 s xa xb)"
                                     "(case a2 of (s, xa, xb) \<Rightarrow> config_typing b2 s xa xb)"]
    unfolding config_untrusted_equiv_def
    apply (cases a1; cases a2)
    apply simp
    apply (meson config_indistinguishable.simps config_indistinguishable_imp_config_typing)
    done
qed
qed

end