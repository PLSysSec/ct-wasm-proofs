section {* Constant Time (coinductive) *}

theory Wasm_Constant_Time imports Wasm_Secret begin

lemma equivp_observation: "equivp (llist_all2 action_indistinguishable)"
  using equivp_action_indistinguishable reflp_llist_all2 symp_llist_all2 transp_llist_all2
  unfolding equivp_reflp_symp_transp
  by blast

quotient_type (overloaded) observation = "action llist" / "llist_all2 action_indistinguishable"
  using equivp_observation
  by blast

coinductive config_is_trace :: "[(s \<times> v list \<times> e list), nat, action llist] \<Rightarrow> bool" where
  base:"\<lbrakk> \<forall>s' vs' es' a'. \<not>\<lparr>s;vs;es\<rparr> a'\<leadsto>_i \<lparr>s';vs';es'\<rparr> \<rbrakk> \<Longrightarrow> config_is_trace (s,vs,es) i LNil"
| step:"\<lbrakk> \<lparr>s;vs;es\<rparr> a\<leadsto>_i \<lparr>s';vs';es'\<rparr>; config_is_trace (s',vs',es') i tr \<rbrakk> \<Longrightarrow> config_is_trace (s,vs,es) i (LCons a tr)"

definition config_trace_set :: "[(s \<times> v list \<times> e list), nat] \<Rightarrow> (action llist) set"  where
  "config_trace_set \<equiv> \<lambda>c i. Collect (config_is_trace c i)"

definition ct_prop :: "[(s \<times> v list \<times> e list), nat, action llist] \<Rightarrow> bool" where
  "ct_prop c i tr \<equiv> \<exists>tr'. llist_all2 action_indistinguishable tr tr' \<and> config_is_trace c i tr'"

coinductive P_co :: "[(s \<times> v list \<times> e list), nat, action llist] \<Rightarrow> bool" where
  base:"\<lbrakk> \<forall>s' vs' es' a'. \<not>\<lparr>s;vs;es\<rparr> a'\<leadsto>_i \<lparr>s';vs';es'\<rparr> \<rbrakk> \<Longrightarrow> P_co (s,vs,es) i LNil"
| step:"\<lbrakk> \<lparr>s;vs;es\<rparr> a'\<leadsto>_i \<lparr>s';vs';es'\<rparr>; action_indistinguishable a a'; P_co (s',vs',es') i tr \<rbrakk> \<Longrightarrow> P_co (s,vs,es) i (LCons a tr)"
thm P_co.coinduct

lemma ct_prop_coinduct_weak[consumes 1, case_names ct_prop]:
  assumes base:"X xa i xb"
  and step:
  "(\<And>x1 x2 x3.
    X x1 x2 x3 \<Longrightarrow>
    (\<exists>s vs es i.
        x1 = (s, vs, es) \<and>
        x2 = i \<and>
        x3 = LNil \<and>
        (\<forall>s' vs' es' a'. \<not> \<lparr>s;vs;es\<rparr> a'\<leadsto>_ i \<lparr>s';vs';es'\<rparr>)) \<or>
    (\<exists>s vs es a' i s' vs' es' a tr.
        x1 = (s, vs, es) \<and>
        x2 = i \<and>
        x3 = LCons a tr \<and>
        \<lparr>s;vs;es\<rparr> a'\<leadsto>_ i \<lparr>s';vs';es'\<rparr> \<and>
        (a \<sim>_a a') \<and>
        X (s', vs', es') i tr))"
   shows "ct_prop xa i xb"
proof -
  def transX \<equiv> "\<lambda> (s,vs,es) a as. (SOME ((s',vs',es'),a').  \<lparr>s;vs;es\<rparr> a'\<leadsto>_ i \<lparr>s';vs';es'\<rparr> \<and> (a \<sim>_a a') \<and> X (s',vs',es') i as)"
  def realtr \<equiv> "\<lambda>c b. unfold_llist
    (\<lambda>(c, abs). lnull abs)
    (\<lambda>(c, abs). snd (transX c (lhd abs) (ltl abs)))
    (\<lambda>(c, abs). (fst (transX c (lhd abs) (ltl abs)), (ltl abs)))
    (c, b)"
  have realtr_simps:
    "\<And>c. realtr c LNil = LNil"
    "\<And>c abs. lnull (realtr c abs) \<longleftrightarrow> lnull abs"
    "\<And>c abs. \<not> lnull abs \<Longrightarrow> lhd (realtr c abs) = snd (transX c (lhd abs) (ltl abs))"
    "\<And>c abs. \<not> lnull abs \<Longrightarrow> ltl (realtr c abs) = realtr (fst (transX c (lhd abs) (ltl abs))) (ltl abs)"
    "\<And>c tl abs. realtr c (LCons tl abs) =
       LCons
         (snd (transX c tl abs))
           (realtr (fst (transX c tl abs)) abs)"
    by (simp_all add: realtr_def)
  have "config_is_trace xa i (realtr xa xb)"
    using base step
  proof (coinduction arbitrary: xa xb)
    case config_is_trace
    show ?case
    proof (cases xb)
      case LNil
      thus ?thesis
        using config_is_trace realtr_simps(1)
        by (cases xa) fastforce
    next
      case (LCons aa aas)
      obtain a as xa' where transX_is:"realtr xa xb = LCons a as"
                                      "a = (snd (transX xa aa aas))"
                                      "xa' = (fst (transX xa aa aas))"
                                      "as = (realtr xa' aas)"
        using LCons realtr_simps(5)
        by simp
      obtain s' vs' es' where xa'_def:"xa' = (s',vs',es')"
        by (metis prod.collapse)
      obtain s vs es where xa_def:"xa = (s, vs, es)"
                                  "\<exists>a' s' vs' es' a tr.
                                    \<lparr>s;vs;es\<rparr> a'\<leadsto>_ i \<lparr>s';vs';es'\<rparr> \<and>
                                    (aa \<sim>_a a') \<and> X (s', vs', es') i aas"
        using config_is_trace LCons
        by fastforce
      hence "\<lparr>s;vs;es\<rparr> a \<leadsto>_ i \<lparr>s';vs';es'\<rparr> \<and> (aa \<sim>_a a) \<and> X (s',vs',es') i aas"
        using transX_is(2,3) xa'_def
        unfolding transX_def
        by (metis (mono_tags, lifting) prod.collapse someI split_conv) (* TODO: slow *)
      thus ?thesis
        using transX_is config_is_trace(2) xa_def(1) xa'_def
        by force
    qed
  qed
  moreover
  have "llist_all2 action_indistinguishable xb (realtr xa xb)"
    using base step
  proof (coinduction arbitrary: xa xb)
    case LNil
    thus ?case
      by (simp add: realtr_simps(2))
  next
    case LCons
    obtain aa aas where xb_def:"xb = LCons aa aas"
      by (metis LCons(3) lhd_LCons_ltl)
    obtain a as xa' where transX_is:"realtr xa xb = LCons a as"
                                    "a = (snd (transX xa aa aas))"
                                    "xa' = (fst (transX xa aa aas))"
                                    "as = (realtr xa' aas)"
      using realtr_simps(5) xb_def
      by simp
      obtain s' vs' es' where xa'_def:"xa' = (s',vs',es')"
        by (metis prod.collapse)
      obtain s vs es where xa_def:"xa = (s, vs, es)"
                           "\<exists>a' s' vs' es' a tr.
                             \<lparr>s;vs;es\<rparr> a'\<leadsto>_ i \<lparr>s';vs';es'\<rparr> \<and>
                             (aa \<sim>_a a') \<and> X (s', vs', es') i aas"
        using xb_def LCons(1,2)
        by fastforce
      hence "\<lparr>s;vs;es\<rparr> a \<leadsto>_ i \<lparr>s';vs';es'\<rparr> \<and> (aa \<sim>_a a) \<and> X (s',vs',es') i aas"
        using transX_is(2,3) xa'_def
        unfolding transX_def
        by (metis (mono_tags, lifting) prod.collapse someI split_conv) (* TODO: slow *)
    thus ?case
      using LCons(2) transX_is(1,4) xb_def xa'_def
      by auto
  qed
  ultimately
  show ?thesis
    unfolding ct_prop_def
    by blast
qed

lemma config_indistinguishable_imp_reduce2:
  assumes "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
          "config_is_trace (s,vs,es) i tr"
  shows "ct_prop (s',vs',es') i tr"
  using assms
proof (coinduction arbitrary: s vs es s' vs' es' tr rule: ct_prop_coinduct_weak)
  case (ct_prop s vs es s' vs' es' tr)
  show ?case
    using ct_prop(3)
  proof (cases rule: config_is_trace.cases)
    case base
    thus ?thesis
      using ct_prop(1,2)
      by (metis config_indistinguishable_imp_config_typing config_indistinguishable_imp_reduce config_indistinguishable_symm)
  next
    case (step a s' vs' es' tr)
    thus ?thesis
      using ct_prop(1,2)
      by (simp del: config_indistinguishable.simps) (meson config_indistinguishable_imp_reduce preservation)
  qed
qed

lemma config_indistinguishable_imp_reduce3:
  assumes "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
          "config_is_trace (s,vs,es) i tr"
  shows "\<exists>tr'. llist_all2 action_indistinguishable tr tr' \<and> config_is_trace (s',vs',es') i tr'"
  using config_indistinguishable_imp_reduce2 assms
  unfolding ct_prop_def
  by auto

lemma program_actions_set2_indistinguishable_secrets_co:
  assumes "tr \<in> (config_trace_set (s, vs, es) i)"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "\<exists>tr' \<in> (config_trace_set (s', vs', es') i). llist_all2 action_indistinguishable tr tr'"
proof -
  have "config_is_trace (s,vs,es) i tr"
    using assms(1)
    unfolding config_trace_set_def
    by fastforce
  then obtain tr' where "config_is_trace (s',vs',es') i tr' \<and> llist_all2 action_indistinguishable tr tr'"
    using config_indistinguishable_imp_reduce3[OF assms(2,3)]
    by fastforce
  thus ?thesis
    unfolding config_trace_set_def
    by fastforce
qed

lemma program_actions2_indistinguishable_secrets_abs_set_co:
  assumes "t \<in> (image abs_observation (config_trace_set (s, vs, es) i))"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "t \<in> (image abs_observation (config_trace_set (s', vs', es') i))"
proof -
  obtain tr where "config_is_trace (s,vs,es) i tr \<and> (abs_observation tr) = t"
    using assms(1)
    unfolding config_trace_set_def
    by fastforce
  then obtain tr' where "config_is_trace (s',vs',es') i tr' \<and> (abs_observation tr') = t"
    using Quotient3_observation config_indistinguishable_imp_reduce3[OF assms(2,3)]
    unfolding Quotient3_def
    by metis
  thus ?thesis
    unfolding config_trace_set_def
    by fastforce
qed

lemma program_actions2_indistinguishable_secrets_abs_set_equiv_co:
  assumes "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "(image abs_observation (config_trace_set (s, vs, es) i)) = (image abs_observation (config_trace_set (s', vs', es') i))"
  using program_actions2_indistinguishable_secrets_abs_set_co[OF _ assms(1,2)]
    config_indistinguishable_imp_config_typing[OF assms(2,1)]
        program_actions2_indistinguishable_secrets_abs_set_co[OF _ config_indistinguishable_symm[OF assms(1)]]
  by fastforce

lift_definition config_obs_set :: "((s \<times> v list \<times> e list) \<times> nat) \<Rightarrow> observation set" is "(\<lambda>(c,i). (config_trace_set c i))" .

lift_definition config_untrusted_quot_obs_set :: "config_untrusted_quot \<Rightarrow> observation set" is "(\<lambda>c. config_obs_set c)"
proof -
  fix prod1 prod2
  assume assms:"prod1 \<sim>_cp prod2"
  show "config_obs_set prod1 = config_obs_set prod2"
  proof (cases prod1; cases prod2)
    fix c1 i1 c2 i2
    assume prod_assms:"prod1 = (c1,i1)" "prod2 = (c2,i2)"
    show ?thesis
    proof (cases c1; cases c2)
      fix s vs es s' vs' es'
      assume config_assms:"c1 = (s,vs,es)" "c2 = (s',vs',es')"
      obtain ts where ts_def:"(s,vs,es) \<sim>_c (s',vs',es')"
                             "\<turnstile>_i1 s;vs;es : (Untrusted,ts)"
                             "i1 = i2"
        using assms prod_assms config_assms
        unfolding config_untrusted_equiv_def
        by fastforce
      thus ?thesis
        using assms prod_assms config_assms program_actions2_indistinguishable_secrets_abs_set_equiv_co
        unfolding config_obs_set_def
        by simp
    qed
  qed
qed

definition constant_time :: "((s \<times> v list \<times> e list) \<times> nat) \<Rightarrow> bool" where
  "constant_time = (\<lambda>(c, i). \<forall>c'. (c \<sim>_c c') \<longrightarrow> ((config_obs_set (c,i)) = (config_obs_set (c',i))))"

theorem config_untrusted_constant_time:
  assumes "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "constant_time ((s,vs,es),i)"
  using program_actions2_indistinguishable_secrets_abs_set_equiv_co assms
  unfolding constant_time_def config_obs_set_def
  by simp

lift_definition config_untrusted_quot_constant_time :: "config_untrusted_quot \<Rightarrow> bool" is constant_time
proof -
  fix prod1 prod2
  assume assms:"prod1 \<sim>_cp prod2"
  show "constant_time prod1 = constant_time prod2"
  proof (cases prod1; cases prod2)
    fix c i c' i'
    assume local_assms:"prod1 = (c,i)" "prod2 = (c',i')"
    show ?thesis
    proof (cases c; cases c')
      fix s vs es s' vs' es'
      assume inner_assms:"c = (s,vs,es)" "c' = (s',vs',es')"
      thus ?thesis
        using assms local_assms config_untrusted_constant_time
        unfolding config_untrusted_equiv_def
        by (simp del: config_indistinguishable.simps) (metis config_indistinguishable_imp_config_typing)
    qed
  qed
qed
  
lemma config_untrusted_quot_constant_time_trivial:
  "config_untrusted_quot_constant_time = (\<lambda>x. True)"
  using config_untrusted_constant_time rep_config_untrusted_quot_typing
  unfolding config_untrusted_quot_constant_time.rep_eq
  by (metis prod.exhaust)

end