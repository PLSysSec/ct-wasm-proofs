theory Wasm_Base imports Main "Wasm_Type_Abs/Wasm_Type_Abs" begin

type_synonym (* immediate *)
  i = nat
type_synonym (* static offset *)
  off = nat
type_synonym (* alignment exponent *)
  a = nat

datatype
  sx = S | U

(* primitive types *)
typedecl i32
typedecl i64
typedecl f32  
typedecl f64

instantiation i32 :: wasm_int begin instance .. end
instantiation i64 :: wasm_int begin instance .. end
instantiation f32 :: wasm_float begin instance .. end
instantiation f64 :: wasm_float begin instance .. end

(* memory *)
typedecl bits
typedecl mem

(* host *)
typedecl host

axiomatization
    mem_size :: "mem \<Rightarrow> nat"
and mem_grow :: "mem \<Rightarrow> nat \<Rightarrow> mem"
and load :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> nat \<Rightarrow> bits option"
and store :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bits \<Rightarrow> nat \<Rightarrow> mem option"
and load_packed :: "sx \<Rightarrow> mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> nat \<Rightarrow> bits option"
and store_packed :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bits \<Rightarrow> nat \<Rightarrow> mem option"
where
    mem_grow_size:"\<And>m n m'. (mem_grow m n = m') \<Longrightarrow> (mem_size m + 64000) = mem_size m'"
and load_size:"\<And>m n off l. (load m n off l = None) = (mem_size m \<le> (off + n + l))"
and load_packed_size:"\<And>sx m n off l. (load_packed sx m n off l = None) = (mem_size m \<le> (off + n + l))"
and store_size:"\<And>m n off v l m'. (store m n off v l = Some m') \<Longrightarrow> mem_size m = mem_size m'"
and store_packed_size:"\<And>m n off v l m'. (store_packed m n off v l = Some m') \<Longrightarrow> mem_size m = mem_size m'"
and store_size1:"\<And>m n off v l. (store m n off v l = None) = (mem_size m \<le> (off + n + l))"
and store_packed_size1:"\<And>m n off v l. (store_packed m n off v l = None) = (mem_size m \<le> (off + n + l))"
end