section {* Constant Time (inductive) *}

theory Wasm_Constant_Time_Ind imports Wasm_Secret begin

definition config_actions :: "[s, v list, e list, nat, action list] \<Rightarrow> bool" ("p'_actions \<lparr>_;_;_\<rparr> _ _" 60) where
  "config_actions s vs es i as \<equiv> (\<exists>s' vs' es'. \<lparr>s;vs;es\<rparr> as^^\<leadsto>_i \<lparr>s';vs';es'\<rparr>)"

definition config_trace_set_ind :: "[(s \<times> v list \<times> e list), nat] \<Rightarrow> (action list) set" where
  "config_trace_set_ind \<equiv> \<lambda>(s,vs,es) i. Collect (config_actions s vs es i)"

lemma config_actions_indistinguishable_secrets_ind:
  assumes "(p_actions \<lparr>s;vs;es\<rparr> i as)"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "\<exists>as'. (p_actions \<lparr>s';vs';es'\<rparr> i as') \<and> list_all2 action_indistinguishable as as'"
  using assms(1,3) config_indistinguishable_trace_noninterference[OF _ assms(2)]
        config_indistinguishable_imp_config_typing[OF _ assms(2)]
  unfolding config_actions_def
  by blast

lemma config_actions_indistinguishable_secrets_abs_ind:
  assumes "(p_actions \<lparr>s;vs;es\<rparr> i as)"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "\<exists>as'. (p_actions \<lparr>s';vs';es'\<rparr> i as') \<and> ($\<A> as) = ($\<A> as')"
  using Quotient3_observation config_actions_indistinguishable_secrets_ind[OF assms]
  unfolding Quotient3_def
  by metis

lemma config_trace_set_ind_indistinguishable_secrets_ind:
  assumes "as \<in> (config_trace_set_ind (s,vs,es) i)"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "\<exists>as' \<in> (config_trace_set_ind (s',vs',es') i). list_all2 action_indistinguishable as as'"
proof -
  have "(p_actions \<lparr>s;vs;es\<rparr> i as)"
    using assms(1)
    unfolding config_trace_set_ind_def
    by fastforce
  then obtain as' where "(p_actions \<lparr>s';vs';es'\<rparr> i as') \<and> list_all2 action_indistinguishable as as'"
    using config_actions_indistinguishable_secrets_ind[OF _ assms(2,3)]
    by fastforce
  thus ?thesis
    unfolding config_trace_set_ind_def
    by fastforce
qed

lemma config_actions_indistinguishable_secrets_abs_set_ind:
  assumes "t \<in> (image abs_obs (config_trace_set_ind (s,vs,es) i))"
          "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "t \<in> (image abs_obs (config_trace_set_ind (s',vs',es') i))"
proof -
  obtain as where "(p_actions \<lparr>s;vs;es\<rparr> i as) \<and> ($\<A> as) = t"
    using assms(1)
    unfolding config_trace_set_ind_def
    by fastforce
  then obtain as' where "(p_actions \<lparr>s';vs';es'\<rparr> i as') \<and> ($\<A> as') = t"
    using config_actions_indistinguishable_secrets_abs_ind[OF _ assms(2)] assms(3)
    by fastforce
  thus ?thesis
    unfolding config_trace_set_ind_def
    by fastforce
qed

lemma config_actions_indistinguishable_secrets_abs_set_equiv_ind:
  assumes "(s,vs,es) \<sim>_c (s',vs',es')"
          "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "(image abs_obs (config_trace_set_ind (s,vs,es) i)) = (image abs_obs (config_trace_set_ind (s',vs',es') i))"
  using config_actions_indistinguishable_secrets_abs_set_ind[OF _ assms(1,2)]
        config_indistinguishable_imp_config_typing[OF assms(2,1)]
        config_actions_indistinguishable_secrets_abs_set_ind[OF _ config_indistinguishable_symm[OF assms(1)]]
  by fastforce

lift_definition config_obs_set_ind :: "((s \<times> v list \<times> e list) \<times> nat) \<Rightarrow> observation set" is "(\<lambda>(c,i). (config_trace_set_ind c i))" .

lift_definition config_untrusted_quot_obs_set_ind :: "config_untrusted_quot \<Rightarrow> observation set" is "(\<lambda>c. config_obs_set_ind c)"
proof -
  fix prod1 prod2
  assume assms:"prod1 \<sim>_cp prod2"
  show "config_obs_set_ind prod1 = config_obs_set_ind prod2"
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
        using assms prod_assms config_assms config_actions_indistinguishable_secrets_abs_set_equiv_ind
        unfolding config_obs_set_ind_def
        by simp
    qed
  qed
qed

definition constant_time_ind :: "((s \<times> v list \<times> e list) \<times> nat) \<Rightarrow> bool" where
  "constant_time_ind = (\<lambda>(c, i). \<forall>c'. (c \<sim>_c c') \<longrightarrow> ((config_obs_set_ind (c,i)) = (config_obs_set_ind (c',i))))"

theorem config_untrusted_constant_time_ind:
  assumes "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "constant_time_ind ((s,vs,es),i)"
    using config_actions_indistinguishable_secrets_abs_set_equiv_ind assms
    unfolding constant_time_ind_def config_obs_set_ind_def
    by simp

lift_definition config_untrusted_quot_constant_time_ind :: "config_untrusted_quot \<Rightarrow> bool" is constant_time_ind
proof -
  fix prod1 prod2
  assume assms:"prod1 \<sim>_cp prod2"
  show "constant_time_ind prod1 = constant_time_ind prod2"
  proof (cases prod1; cases prod2)
    fix c i c' i'
    assume local_assms:"prod1 = (c,i)" "prod2 = (c',i')"
    show ?thesis
    proof (cases c; cases c')
      fix s vs es s' vs' es'
      assume inner_assms:"c = (s,vs,es)" "c' = (s',vs',es')"
      thus ?thesis
        using assms local_assms config_untrusted_constant_time_ind
        unfolding config_untrusted_equiv_def
        by (simp del: config_indistinguishable.simps) (metis config_indistinguishable_imp_config_typing)
    qed
  qed
qed
  
lemma config_untrusted_quot_constant_time_trivial_ind:
  "config_untrusted_quot_constant_time_ind = (\<lambda>x. True)"
  using config_untrusted_constant_time_ind rep_config_untrusted_quot_typing
  unfolding config_untrusted_quot_constant_time_ind.rep_eq
  by (metis prod.exhaust)

definition "trace_set_equiv = rel_set (list_all2 action_indistinguishable)"

definition constant_time_traces_ind :: "((s \<times> v list \<times> e list) \<times> nat) \<Rightarrow> bool" where
  "constant_time_traces_ind = (\<lambda>(c, i). \<forall>c'. (c \<sim>_c c') \<longrightarrow> trace_set_equiv (config_trace_set_ind c i) (config_trace_set_ind c' i))"

lemma config_untrusted_constant_time_traces:
  assumes "\<turnstile>_i s;vs;es : (Untrusted,ts)"
  shows "constant_time_traces_ind ((s,vs,es),i)"
  using assms
  unfolding trace_set_equiv_def rel_set_def constant_time_traces_ind_def
  apply (simp del: config_indistinguishable.simps)
  apply (metis config_indistinguishable_imp_config_typing config_indistinguishable_symm config_trace_set_ind_indistinguishable_secrets_ind observation.abs_eq_iff)
  done
end