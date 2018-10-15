section {* Set Based Leakage Model (sketch)*}

theory Wasm_Leakage imports Wasm_Secret begin

datatype arith_leakage =
  Unop_i32_leakage unop_i
| Unop_i64_leakage unop_i
| Unop_f32_leakage unop_f f32
| Unop_f64_leakage unop_f f64
| Binop_i32_Some_safe_leakage binop_i
| Binop_i32_None_safe_leakage binop_i
| Binop_i64_Some_safe_leakage binop_i
| Binop_i64_None_safe_leakage binop_i
| Binop_i32_Some_leakage binop_i i32 i32
| Binop_i32_None_leakage binop_i i32 i32
| Binop_i64_Some_leakage binop_i i64 i64
| Binop_i64_None_leakage binop_i i64 i64
| Binop_f32_Some_leakage binop_f f32 f32
| Binop_f32_None_leakage binop_f f32 f32
| Binop_f64_Some_leakage binop_f f64 f64
| Binop_f64_None_leakage binop_f f64 f64
| Testop_i32_leakage testop
| Testop_i64_leakage testop
| Relop_i32_leakage relop_i
| Relop_i64_leakage relop_i
| Relop_f32_leakage relop_f f32 f32
| Relop_f64_leakage relop_f f64 f64

datatype host_leakage =
  Callcl_host_Some_leakage "mem list"
| Callcl_host_None_leakage "mem list"

datatype leakage =
  Arith_leakage arith_leakage
| Host_leakage host_leakage
| Empty_leakage
| Convert_Some_int_leakage t t
| Convert_None_int_leakage t t
| Convert_Some_leakage t t v
| Convert_None_leakage t t v
| Select_leakage "i32 option"
| If_false_leakage i32
| If_true_leakage i32
| Br_if_false_leakage i32
| Br_if_true_leakage i32
| Br_table_leakage i32
| Br_table_length_leakage i32
| Call_indirect_Some_leakage i32
| Call_indirect_None_leakage i32
| Callcl_native_leakage nat
| Load_Some_leakage t nat a off
| Load_None_leakage t nat a off
| Load_packed_Some_leakage tp sx nat a off
| Load_packed_None_leakage tp sx nat a off
| Store_Some_leakage t nat a off
| Store_None_leakage t nat a off
| Store_packed_Some_leakage t tp nat a off
| Store_packed_None_leakage t tp nat a off
| Current_memory_leakage nat
| Grow_memory_Some_leakage nat nat
| Grow_memory_None_leakage nat nat

definition action_leakage :: "action \<Rightarrow> leakage" where
"action_leakage a =
  (case a of
  Unop_i32_action op' \<Rightarrow> Arith_leakage (Unop_i32_leakage op')
| Unop_i64_action op' \<Rightarrow> Arith_leakage (Unop_i64_leakage op')
| Unop_f32_action op' c \<Rightarrow> Arith_leakage (Unop_f32_leakage op' c)
| Unop_f64_action op' c \<Rightarrow> Arith_leakage (Unop_f64_leakage op' c)
| Binop_i32_Some_action op' c1 c2 \<Rightarrow> Arith_leakage (if (safe_binop_i op')
                                                     then Binop_i32_Some_safe_leakage op'
                                                     else Binop_i32_Some_leakage op' c1 c2)
| Binop_i32_None_action op' c1 c2 \<Rightarrow> Arith_leakage (if (safe_binop_i op')
                                                     then Binop_i32_None_safe_leakage op'
                                                     else Binop_i32_None_leakage op' c1 c2)
| Binop_i64_Some_action op' c1 c2 \<Rightarrow> Arith_leakage (if (safe_binop_i op')
                                                     then Binop_i64_Some_safe_leakage op'
                                                     else Binop_i64_Some_leakage op' c1 c2)
| Binop_i64_None_action op' c1 c2 \<Rightarrow>Arith_leakage (if (safe_binop_i op')
                                                    then Binop_i64_None_safe_leakage op'
                                                    else Binop_i64_None_leakage op' c1 c2)
| Binop_f32_Some_action op' c1 c2 \<Rightarrow> Arith_leakage (Binop_f32_Some_leakage op' c1 c2)
| Binop_f32_None_action op' c1 c2 \<Rightarrow> Arith_leakage (Binop_f32_None_leakage op' c1 c2)
| Binop_f64_Some_action op' c1 c2 \<Rightarrow> Arith_leakage (Binop_f64_Some_leakage op' c1 c2)
| Binop_f64_None_action op' c1 c2 \<Rightarrow> Arith_leakage (Binop_f64_None_leakage op' c1 c2)
| Testop_i32_action op' \<Rightarrow> Arith_leakage (Testop_i32_leakage op')
| Testop_i64_action op' \<Rightarrow> Arith_leakage (Testop_i64_leakage op')
| Relop_i32_action op' \<Rightarrow> Arith_leakage (Relop_i32_leakage op')
| Relop_i64_action op' \<Rightarrow> Arith_leakage (Relop_i64_leakage op')
| Relop_f32_action  op' c1 c2 \<Rightarrow> Arith_leakage (Relop_f32_leakage  op' c1 c2)
| Relop_f64_action  op' c1 c2 \<Rightarrow> Arith_leakage (Relop_f64_leakage  op' c1 c2)
| Convert_Some_action t1 t2 c \<Rightarrow> (if is_int_t t1 \<and> is_int_t t2
                                   then Convert_Some_int_leakage t1 t2
                                   else Convert_Some_leakage t1 t2 c)
| Convert_None_action t1 t2 c \<Rightarrow> (if is_int_t t1 \<and> is_int_t t2
                                   then Convert_None_int_leakage t1 t2
                                   else Convert_None_leakage t1 t2 c)
| Reinterpret_action \<Rightarrow> Empty_leakage
| Classify_action \<Rightarrow> Empty_leakage
| Declassify_action \<Rightarrow> Empty_leakage
| Unreachable_action \<Rightarrow> Empty_leakage
| Nop_action \<Rightarrow> Empty_leakage
| Drop_action  \<Rightarrow> Empty_leakage
| Select_action sec c \<Rightarrow> if (sec = Secret) then Select_leakage None else Select_leakage (Some c)
| Block_action  \<Rightarrow> Empty_leakage
| Loop_action \<Rightarrow> Empty_leakage
| If_false_action c \<Rightarrow> If_false_leakage c
| If_true_action c \<Rightarrow> If_true_leakage c
| Label_const_action \<Rightarrow> Empty_leakage
| Label_trap_action \<Rightarrow> Empty_leakage
| Br_action \<Rightarrow> Empty_leakage
| Br_if_false_action c \<Rightarrow> Br_if_false_leakage c
| Br_if_true_action c \<Rightarrow> Br_if_true_leakage c
| Br_table_action c \<Rightarrow> Br_table_leakage c
| Br_table_length_action c \<Rightarrow> Br_table_length_leakage c
| Local_const_action \<Rightarrow> Empty_leakage
| Local_trap_action \<Rightarrow> Empty_leakage
| Return_action \<Rightarrow> Empty_leakage
| Tee_local_action \<Rightarrow> Empty_leakage
| Trap_action \<Rightarrow> Empty_leakage
| Call_action \<Rightarrow> Empty_leakage
| Call_indirect_Some_action c \<Rightarrow> Call_indirect_Some_leakage c
| Call_indirect_None_action c \<Rightarrow> Call_indirect_None_leakage c
| Callcl_native_action n \<Rightarrow> Callcl_native_leakage n
| Callcl_host_Some_action s args s' out tr tf host hs \<Rightarrow> Host_leakage (Callcl_host_Some_leakage (map fst (filter (\<lambda>(m,sec). sec = Public) (mem s))))
| Callcl_host_None_action s args tr tf host hs \<Rightarrow> Host_leakage (Callcl_host_Some_leakage (map fst (filter (\<lambda>(m,sec). sec = Public) (mem s))))
| Get_local_action \<Rightarrow> Empty_leakage
| Set_local_action \<Rightarrow> Empty_leakage
| Get_global_action \<Rightarrow> Empty_leakage
| Set_global_action \<Rightarrow> Empty_leakage
| Load_Some_action t n a off \<Rightarrow> Load_Some_leakage t n a off
| Load_None_action t n a off \<Rightarrow> Load_None_leakage t n a off
| Load_packed_Some_action tp sx n a off \<Rightarrow> Load_packed_Some_leakage tp sx n a off
| Load_packed_None_action tp sx n a off \<Rightarrow> Load_packed_None_leakage tp sx n a off
| Store_Some_action t n a off \<Rightarrow> Store_Some_leakage t n a off
| Store_None_action t n a off \<Rightarrow> Store_None_leakage t n a off
| Store_packed_Some_action t tp n a off \<Rightarrow> Store_packed_Some_leakage t tp n a off
| Store_packed_None_action t tp n a off \<Rightarrow> Store_packed_None_leakage t tp n a off
| Current_memory_action l \<Rightarrow> Current_memory_leakage l
| Grow_memory_Some_action l c \<Rightarrow> Grow_memory_Some_leakage l c
| Grow_memory_None_action l c \<Rightarrow> Grow_memory_None_leakage l c
| Label_action \<Rightarrow> Empty_leakage
| Local_action \<Rightarrow> Empty_leakage)"

lemma memory_agree_filter:
  assumes "memory_public_agree m m'"
  shows "(\<lambda>(m,sec). sec = Public) m = (\<lambda>(m,sec). sec = Public) m'"
  using assms
  unfolding memory_public_agree_def
  by (cases m; cases m') auto

lemma memories_agree_filter:
  assumes "memories_public_agree ms ms'"
  shows "filter (\<lambda>(m,sec). sec = Public) ms = filter (\<lambda>(m,sec). sec = Public) ms'"
  using assms
proof (induction ms arbitrary: ms')
  case Nil
  thus ?case
    by simp
next
  case (Cons a ms)
  obtain a' ms'' where "ms' = a'#ms''"
                       "memory_public_agree a a'"
                       "memories_public_agree ms ms''"
    using Cons(2)
    by (metis list_all2_Cons1)
  thus ?case
    using Cons(1) memory_agree_filter
    by (fastforce simp add: memory_public_agree_def)
qed

lemma action_indistinguishable_imp_action_leakage_eq:
  assumes "a \<sim>_a a'"
          "action_leakage a = obs"
  shows "action_leakage a' = obs"
  using assms
proof (induction rule: action_indistinguishable.induct)
  case (host_Some s s' vcs vcs' s_o s'_o vcs_o vcs'_o tf f hs hs')
  have "filter (\<lambda>(m,sec). sec = Public) (mem s) = filter (\<lambda>(m,sec). sec = Public) (mem s')"
    using host_Some(1) store_public_agree_def memories_agree_filter
    by simp
  thus ?case
    using host_Some(5)
    by (auto simp add: action_leakage_def)
next
  case (host_None s s' vcs vcs' tf f hs hs')
  have "filter (\<lambda>(m,sec). sec = Public) (mem s) = filter (\<lambda>(m,sec). sec = Public) (mem s')"
    using host_None(1) store_public_agree_def memories_agree_filter
    by simp
  thus ?case
    using host_None(3)
    by (auto simp add: action_leakage_def)
qed (auto simp add: action_leakage_def)

end