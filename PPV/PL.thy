(*  Title:   PL.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology

*)

subsection \<open> PL \<close>

theory PL
  imports HPProg
begin


definition hp_eq (infixl "=\<^sub>P\<^sub>L" 50) where "hp_eq \<equiv> hp_lift2 HOL.eq"
definition hp_true ("\<top>\<^sub>P\<^sub>L") where "hp_true \<equiv> hp_const True"
definition hp_false ("\<bottom>\<^sub>P\<^sub>L") where "hp_false \<equiv> hp_const False"
definition hp_and (infixr "\<and>\<^sub>P\<^sub>L" 35) where "hp_and \<equiv> hp_lift2 conj"
definition hp_implies (infixr "\<longrightarrow>\<^sub>P\<^sub>L" 25) where "hp_implies \<equiv> hp_lift2 implies"
definition hp_neg ("\<not>\<^sub>P\<^sub>L") where "hp_neg t \<equiv> t \<longrightarrow>\<^sub>P\<^sub>L \<bottom>\<^sub>P\<^sub>L"
definition hp_or (infixr "\<or>\<^sub>P\<^sub>L" 30) where "hp_or \<phi> \<psi> \<equiv> \<not>\<^sub>P\<^sub>L (\<not>\<^sub>P\<^sub>L \<phi> \<and>\<^sub>P\<^sub>L \<not>\<^sub>P\<^sub>L \<psi>)"
definition hp_less (infix "<\<^sub>P\<^sub>L" 50) where "hp_less \<equiv> hp_lift2 less"
definition hp_less_eq (infix "\<le>\<^sub>P\<^sub>L" 50) where "hp_less_eq t1 t2 \<equiv> \<not>\<^sub>P\<^sub>L (t2 <\<^sub>P\<^sub>L t1) "
definition hp_all :: "['a quasi_borel, 'a \<Rightarrow> 'env \<Rightarrow> bool] \<Rightarrow> 'env \<Rightarrow> bool" where
"hp_all X \<phi> \<equiv> (\<lambda>env. \<forall>x\<in>qbs_space X. \<phi> x env)"
syntax
 "_hp_all" :: "pttrn \<Rightarrow> 'a quasi_borel \<Rightarrow> ('env \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<forall>\<^sub>P\<^sub>L(_/\<in>\<^sub>P\<^sub>L_)./ _)" [0, 0, 10] 10)
translations
 "\<forall>\<^sub>P\<^sub>L x \<in>\<^sub>P\<^sub>L X. \<phi>" \<rightleftharpoons> "CONST hp_all X (\<lambda>x. \<phi>)"

definition "hp_conjall \<Psi> \<equiv> (\<lambda>env. \<forall>\<phi>\<in>\<Psi>. \<phi> env)"
definition hp_conjall_fix :: "('cont \<times> 't1 \<Rightarrow> bool) set \<Rightarrow> ('cont \<Rightarrow> 't1) \<Rightarrow> 'cont \<Rightarrow> bool" where
"hp_conjall_fix \<Psi> \<equiv> (\<lambda>f env. hp_conjall \<Psi> (env,f env))"

lemma hp_conjall_union:
  "hp_conjall (\<Psi> \<union> \<Phi>) = (hp_conjall \<Psi> \<and>\<^sub>P\<^sub>L hp_conjall \<Phi>)"
  by(auto simp add: hp_conjall_def hp_and_def)

lemma hp_conjall_empty:
 "hp_conjall {} = \<top>\<^sub>P\<^sub>L"
  by(simp add: hp_conjall_def hp_true_def hp_const_def)

lemma hp_conjall_fix_empty:
 "hp_conjall_fix {} k = \<top>\<^sub>P\<^sub>L"
  by(simp add: hp_conjall_fix_def hp_conjall_def hp_true_def hp_const_def)

lemma hp_conjall_fix_empty':
 "hp_conjall_fix {} = (\<lambda>_. \<top>\<^sub>P\<^sub>L)"
  by(standard,rule hp_conjall_fix_empty)  

lemma hp_less_eq_def2:
 "hp_less_eq (t1 :: _ \<Rightarrow> 'a :: linorder) t2 = hp_lift2 less_eq t1 t2"
  by(standard,auto simp add: hp_less_eq_def hp_less_def hp_false_def hp_neg_def hp_implies_def hp_const_def)

lemma hp_true_assm:
 "(\<top>\<^sub>P\<^sub>L \<longrightarrow>\<^sub>P\<^sub>L \<phi>) = \<phi>"
  by(simp add: hp_true_def hp_implies_def hp_const_def)

lemma hp_true_assm':
 "(\<forall>\<^sub>P\<^sub>L x \<in>\<^sub>P\<^sub>L X. \<top>\<^sub>P\<^sub>L \<longrightarrow>\<^sub>P\<^sub>L \<phi> x) = (\<forall>\<^sub>P\<^sub>L x \<in>\<^sub>P\<^sub>L X. \<phi> x)"
  by(simp add: hp_true_def hp_implies_def hp_const_def hp_all_def)

lemmas hp_definitions = var1_def var2_def var3_def var4_def var5_def var6_def var7_def
                 hp_const_def hp_abs_def hp_suc_def hp_real_def hp_constf_def
                 hp_abs'_def hp_suc'_def hp_real'_def hp_ennreal'_def hp_enn2real'_def
                 hp_plus'_def hp_minus'_def hp_uminus'_def hp_times'_def hp_div'_def
                 hp_plus''_def hp_minus''_def hp_uminus''_def hp_times''_def hp_div''_def
                 hp_ennreal_def hp_enn2real_def hp_funplus'_def fun_diff_def fun_Compl_def
                 hp_funtimes'_def hp_fundiv'_def qbs_eval_def comp_def
                 hp_pair_def hp_fst_def hp_snd_def hp_inl_def hp_inr_def hp_case_def
                 hp_lambda_def hp_app_def hp_return_def hp_bind_def hp_rec_nat_def
                 hp_ennexpect_def hp_expect_def hp_integrable_def hp_var_def hp_pair_measure_def
                 hp_eq_def hp_true_def hp_false_def hp_and_def hp_implies_def hp_or_def
                 hp_neg_def hp_less_def hp_less_eq_def2 hp_power_one hp_power_square hp_all_def hp_id_def


type_synonym 'cont assump = "('cont \<Rightarrow> bool) set"

definition pl_der :: "['cont quasi_borel, 'cont assump, 'cont \<Rightarrow> bool] \<Rightarrow> bool" where
"pl_der Gam Psi phi \<equiv> (\<forall>x\<in> qbs_space Gam. hp_conjall Psi x \<longrightarrow> phi x)"

syntax
 "_pl_der" :: "any \<Rightarrow> 'cont quasi_borel \<Rightarrow> ('cont \<Rightarrow> bool) \<Rightarrow> 'cont assump \<Rightarrow> bool" ("_ | _ \<turnstile>\<^sub>P\<^sub>L _" 21)

translations
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>" \<rightleftharpoons> "CONST pl_der \<Gamma> \<Psi> \<phi>"

term "\<forall>\<^sub>P\<^sub>Lr\<in>\<^sub>P\<^sub>L\<real>\<^sub>Q. hp_const 0 \<le>\<^sub>P\<^sub>L hp_const r *\<^sub>t hp_const r"


lemma pl_weakening:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  shows "\<Gamma> | \<Psi> \<union> \<Phi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  using assms by(auto simp add: pl_der_def hp_conjall_def)

lemma pl_contweakening:
  assumes "\<phi>' = (\<lambda>(k,_). \<phi> k)"
          "\<Psi>' = (\<lambda>\<psi>. (\<lambda>(k,_). \<psi> k)) `\<Psi>"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
    shows "\<Gamma>,,X | \<Psi>' \<turnstile>\<^sub>P\<^sub>L \<phi>'"
  using assms by(simp add: pl_der_def hp_conjall_def hpprog_context_def)

(*    \<phi> \<in> \<Psi> 
   ---------------
    \<Gamma> | \<Psi> |-pl \<phi> *)
lemma pl_ax:
  assumes "\<phi> \<in> \<Psi>"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  using assms by(auto simp: pl_der_def hp_conjall_def)

(* (\<Gamma> |- t1 : T) (\<Gamma> |- t2 : T)  t1 = t2
  --------------------------------------
          \<Gamma> | \<Psi> |-pl t1 = t2            *)
lemma pl_conv:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; T"
          "\<Gamma> \<turnstile>\<^sub>t t1 ;; T"
      and "\<And>x. x \<in> qbs_space \<Gamma> \<Longrightarrow> t1 x = t2 x"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t1 =\<^sub>P\<^sub>L t2"
  using assms(3) by(simp add: hpprog_typing_def pl_der_def hp_eq_def)


lemma pl_eq_refl:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t =\<^sub>P\<^sub>L t"
  by(simp add: pl_der_def hp_definitions)

lemma pl_eq_sym:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t1 =\<^sub>P\<^sub>L t2"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t2 =\<^sub>P\<^sub>L t1"
  using assms by(simp add: hp_definitions pl_der_def)

lemma pl_eq_trans:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t1 =\<^sub>P\<^sub>L t2"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t2 =\<^sub>P\<^sub>L t3"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t1 =\<^sub>P\<^sub>L t3"
  using assms by(simp add: pl_der_def hp_eq_def)



(* \<Gamma> | \<Psi> |-pl \<phi>[t/x]     \<Gamma> | \<Psi> |-pl t = u
  -----------------------------------------
               \<Gamma> | \<Psi> |- \<phi>[u/x]             *)
lemma pl_subst:
 assumes "\<phi> = (\<lambda>t. \<lambda>k. \<phi>' k (t k))"
         "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t =\<^sub>P\<^sub>L u"
     and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> t"
   shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> u"
  using assms by(simp add: hp_eq_def pl_der_def)

(*  \<Gamma> | \<Psi>,\<psi> |-pl \<phi>
  --------------------
   \<Gamma> | \<Psi> |-pl \<psi> \<longrightarrow> \<phi> *)
lemma pl_impI:
  assumes "\<Gamma> | \<Psi> \<union> {\<psi>} \<turnstile>\<^sub>P\<^sub>L \<phi>"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<psi> \<longrightarrow>\<^sub>P\<^sub>L \<phi>"
  using assms by(simp add: pl_der_def hp_conjall_def hp_implies_def)


(* \<Gamma> | \<Psi> |-pl \<psi> \<longrightarrow> \<phi>    \<Gamma> | \<Psi> |-pl \<psi>
  -------------------------------------
             \<Gamma> | \<Psi> |-pl \<phi>             *)
lemma pl_impE:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<psi> \<longrightarrow>\<^sub>P\<^sub>L \<phi>"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<psi>"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  using assms by(simp add: pl_der_def hp_implies_def)

lemma pl_impE':
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<psi>"
  shows "\<Gamma> | \<Psi> \<union> {\<phi>} \<turnstile>\<^sub>P\<^sub>L \<psi>"
  apply(rule pl_impE[where \<psi>=\<phi>])
   apply(rule pl_weakening,fact)
  apply(rule pl_ax,simp)
  done



(* \<Gamma> | \<Psi> |-pl \<phi>     \<Gamma> | \<Psi> |-pl \<psi>
  --------------------------------
         \<Gamma> | \<Psi> |-pl \<phi> \<and> \<psi>        *)
lemma pl_andI:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<psi>"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<and>\<^sub>P\<^sub>L \<psi>"
  using assms by(simp add: pl_der_def hp_and_def)

(* \<Gamma> | \<Psi> |-pl \<phi> \<and> \<psi> 
  -------------------
     \<Gamma> | \<Psi> |-pl \<psi>   *)
lemma pl_andEr:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<and>\<^sub>P\<^sub>L \<psi>"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<psi>"
  using assms by(simp add: pl_der_def hp_and_def)


(* \<Gamma> | \<Psi> |-pl \<phi> \<and> \<psi> 
  -------------------
     \<Gamma> | \<Psi> |-pl \<phi>   *)
lemma pl_andEl:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<and>\<^sub>P\<^sub>L \<psi>"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  using assms by(simp add: pl_der_def hp_and_def)


(* \<Gamma>, x : X | \<Psi> |-pl \<phi>   \<Gamma> |- \<Psi> wf 
  ----------------------------------
          \<Gamma> | \<Psi> |-pl \<forall>x:X. \<phi>      *)
lemma pl_allI:
  assumes "\<Psi> = (\<lambda>\<psi>. (\<lambda>(k,_). \<psi> k)) `\<Psi>'"
          "\<phi>' = (\<lambda>t k. \<phi> (k,t k))"
      and "\<Gamma>,,X | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
    shows "\<Gamma> | \<Psi>' \<turnstile>\<^sub>P\<^sub>L  \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi>' (hp_const x)"
  using assms by(simp add: pl_der_def hpprog_context_def hp_all_def hp_conjall_def hp_const_def)

lemma pl_allI_indep:
  assumes "(\<Gamma> :: 'cont quasi_borel) | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>L(X::'a quasi_borel). \<phi>"
proof -
  define \<phi>' :: "('cont \<Rightarrow> 'a) \<Rightarrow> 'cont \<Rightarrow> bool"
    where "\<phi>' = (\<lambda>_. \<phi>)"
  then have 1:"(\<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi>) = (\<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi>' (hp_const x))"
    by simp
  define \<phi>0 :: "'cont \<times> 'a \<Rightarrow> bool"
    where "\<phi>0 \<equiv> (\<lambda>(k,x). \<phi> k)"
  show ?thesis
    apply(simp add: 1)
    apply(rule pl_allI[where \<phi>=\<phi>0],simp,simp add: \<phi>'_def \<phi>0_def)
    apply(rule pl_contweakening[where \<phi>=\<phi>],simp add: \<phi>0_def,simp)
    apply(rule assms)
    done
qed

(* \<Gamma> | \<Psi> |-pl \<forall>x:T. \<phi>   \<Gamma> |- e : T 
  ----------------------------------
          \<Gamma> | \<Psi> |-pl \<phi>[e/x]        *)
lemma pl_allE:
  assumes "\<phi> = (\<lambda>t env. \<phi>' (t env) env)"
          "\<Gamma> \<turnstile>\<^sub>t e ;; X"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi> (hp_const x)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> e"
  using assms qbs_morphismE(1)[OF assms(2)[simplified hpprog_typing_def]]
  by(auto simp add: pl_der_def hp_definitions)

lemma pl_allE_indep:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi>"
      and "(\<Gamma> :: 'cont quasi_borel) \<turnstile>\<^sub>t e ;; (X :: 'a quasi_borel)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
proof -
  define \<phi>' :: "('cont \<Rightarrow> 'a) \<Rightarrow> 'cont \<Rightarrow> bool"
    where "\<phi>' = (\<lambda>_. \<phi>)"
  show ?thesis
    apply(simp add: fun_cong[OF sym[OF \<phi>'_def],of e])
    apply(rule pl_allE[OF _ assms(2)],simp add: \<phi>'_def)
    apply(simp add: \<phi>'_def)
    apply(rule assms(1))
    done
qed

lemma pl_allEVar:
  assumes "\<phi> = (\<lambda>t env. \<phi>' (env,t env))"
          "\<Psi>' = (\<lambda>\<psi>. (\<lambda>(k,_). \<psi> k)) `\<Psi>"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>L(X::'a quasi_borel). \<phi> (hp_const x)"
    shows "\<Gamma>,,X | \<Psi>' \<turnstile>\<^sub>P\<^sub>L \<phi>'"
proof -
  define \<phi>'' :: "_ \<Rightarrow> _ \<times> 'a \<Rightarrow> bool"
    where "\<phi>'' = (\<lambda>t env. \<phi>' (fst env, t env))"
  then have 1:"\<phi>' = \<phi>'' var1" by(simp add: var1_def)
  show ?thesis
    apply(simp add: 1)
    apply(rule pl_allE[of \<phi>'' _ _ var1 X],simp add: \<phi>''_def,simp add: hpt_var1)
    apply(rule pl_contweakening[of _ "\<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi> (hp_const x)" _ \<Psi>],simp add: \<phi>''_def assms(1) hp_all_def split_beta' hp_const_def,fact)
    apply fact
    done
qed

(*
  ---------------
   \<Gamma> | \<Psi> |-pl \<top>  *)
lemma pl_topI:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<top>\<^sub>P\<^sub>L"
  by(simp add: pl_der_def hp_true_def hp_const_def)


(* \<Gamma> | \<Psi> |-pl \<bottom>    \<Gamma> |- \<phi> wf 
  ----------------------------
         \<Gamma> | \<Psi> |-pl \<phi>        *)
lemma pl_botE:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<bottom>\<^sub>P\<^sub>L"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  using assms by(simp add: pl_der_def hp_false_def hp_const_def)


(* \<Gamma> | \<Psi> |-pl \<phi>[0/n]    \<Gamma>, n : \<nat> | \<Psi>, \<phi> |-pl \<phi>[n+1/n]
  -----------------------------------------------------
               \<Gamma> | \<Psi> |-pl \<forall>n. \<phi> n                    *)
lemma pl_nat:
  assumes "\<Psi>' = (\<lambda>\<psi>. (\<lambda>(k,_). \<psi> k)) `\<Psi>"
          "\<phi>' = (\<lambda>t envn. \<phi> (hp_const (t envn)) (fst envn))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> (hp_const 0)"
      and "\<Gamma> ,, \<nat>\<^sub>Q | \<Psi>' \<union> {\<phi>' var1}  \<turnstile>\<^sub>P\<^sub>L \<phi>' (hp_suc var1)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. \<phi> (hp_const n)"
proof(auto simp add: hp_definitions pl_der_def)
  fix x
  fix n :: nat
  assume h:"x \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> x"
  then show "\<phi> (\<lambda>_. n) x"
    using assms by(induction n; simp add: pl_der_def hp_definitions hpprog_context_def hp_conjall_def)
qed

(*    \<Gamma>, n : \<nat> | \<Psi>, \<forall>k. k < n \<longrightarrow> \<phi>[k/n] |-pl \<phi>
  -----------------------------------------------
              \<Gamma> | \<Psi> |-pl \<forall>n. \<phi> n                *)
lemma pl_snat:
  assumes "\<Psi>' = (\<lambda>\<psi>. (\<lambda>(k,_). \<psi> k)) `\<Psi>"
          "\<phi>' = (\<lambda>t envn. \<phi> (hp_const (t envn)) (fst envn))"
      and "\<Gamma> ,, \<nat>\<^sub>Q | \<Psi>' \<union> {\<forall>\<^sub>P\<^sub>Lk\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const k <\<^sub>P\<^sub>L var1 \<longrightarrow>\<^sub>P\<^sub>L \<phi>' (hp_const k)}  \<turnstile>\<^sub>P\<^sub>L \<phi>' var1"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. \<phi> (hp_const n)"
  unfolding pl_der_def hp_all_def
proof auto
  fix x
  fix n :: nat
  assume H: "x \<in> qbs_space \<Gamma>"
            "hp_conjall \<Psi> x"
  show "\<phi> (hp_const n) x"
  proof(induction n rule : less_induct)
    case ih:(less n)
    then show ?case
      using assms H by(simp add: pl_der_def hp_conjall_def hpprog_context_def hp_definitions)
  qed
qed

lemma pl_dne:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<not>\<^sub>P\<^sub>L (\<not>\<^sub>P\<^sub>L \<phi>)"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  using assms by(simp add: hp_neg_def hp_implies_def hp_false_def pl_der_def hp_const_def)

lemma pl_negE:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<not>\<^sub>P\<^sub>L \<phi>"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<bottom>\<^sub>P\<^sub>L"
  apply(rule pl_impE[where \<psi>="\<phi>"])
   apply(simp add: assms(1)[simplified hp_neg_def])
  apply fact
  done

lemma pl_negI:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<bottom>\<^sub>P\<^sub>L"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<not>\<^sub>P\<^sub>L \<phi>"
  using assms by(simp add: hp_neg_def)

lemma pl_orIl:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<or>\<^sub>P\<^sub>L \<psi>"
  apply(simp add: hp_or_def)
  apply(rule pl_negI)
  apply(rule pl_impI)
  apply(rule pl_negE[where \<phi>="\<phi>"])
   apply(rule pl_andEl[where \<psi>="\<not>\<^sub>P\<^sub>L \<psi>"])
   apply(rule pl_ax,simp)
  apply(rule pl_weakening)
  apply fact
  done

lemma pl_orIr:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<psi>"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<or>\<^sub>P\<^sub>L \<psi>"
  apply(simp add: hp_or_def)
  apply(rule pl_negI)
  apply(rule pl_impI)
  apply(rule pl_negE[where \<phi>="\<psi>"])
   apply(rule pl_andEr[where \<phi>="\<not>\<^sub>P\<^sub>L \<phi>"])
   apply(rule pl_ax,simp)
  apply(rule pl_weakening)
  apply fact
  done

lemma pl_orE:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>1 \<or>\<^sub>P\<^sub>L \<phi>2"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>1 \<longrightarrow>\<^sub>P\<^sub>L \<psi>"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>2 \<longrightarrow>\<^sub>P\<^sub>L \<psi>"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<psi>"
  apply(rule pl_dne)
  apply(rule pl_negI)
  apply(rule pl_impI)
  apply(rule pl_negE[OF pl_weakening[where \<Phi>="{\<not>\<^sub>P\<^sub>L \<psi>}",OF assms(1)[simplified hp_or_def]]])
  apply(rule pl_andI)
   apply(rule pl_negI)
   apply(rule pl_impI)
   apply(rule pl_negE[where \<phi>=\<psi>])
    apply(rule pl_ax,simp)
   apply(rule pl_impE[where \<psi>=\<phi>1])
    apply(rule pl_weakening[OF pl_weakening[OF assms(2),of "{\<not>\<^sub>P\<^sub>L \<psi>}"],of "{\<phi>1}"])
   apply(rule pl_ax,simp)

  apply(rule pl_negI)
   apply(rule pl_impI)
   apply(rule pl_negE[where \<phi>=\<psi>])
    apply(rule pl_ax,simp)
   apply(rule pl_impE[where \<psi>=\<phi>2])
    apply(rule pl_weakening[OF pl_weakening[OF assms(3),of "{\<not>\<^sub>P\<^sub>L \<psi>}"],of "{\<phi>2}"])
  apply(rule pl_ax,simp)
  done


lemma pl_imp_equal:
  assumes "\<phi>' = (\<lambda>k env. \<phi>'' env (k env))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L e1 =\<^sub>P\<^sub>L e2"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<phi>' e1"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<phi>' e2"
  apply(rule pl_impI)
  apply(rule pl_subst[where t="e1"],simp add: assms(1))
   apply(rule pl_impE[OF pl_weakening[where \<Phi>="{\<phi>}",OF assms(2)]])
  apply(rule pl_ax,simp)
  apply(rule pl_impE[OF pl_weakening[where \<Phi>="{\<phi>}",OF assms(3)]])
  apply(rule pl_ax,simp)
  done

lemma pl_imp_andEl:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<psi>1 \<and>\<^sub>P\<^sub>L \<psi>2"
  shows  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<psi>1"
  apply(rule pl_impI)
  apply(rule pl_andEl)
  apply(rule pl_impE[OF pl_weakening[where \<Phi>="{\<phi>}",OF assms]])
  apply(rule pl_ax,simp)
  done

lemma pl_imp_andEr:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<psi>1 \<and>\<^sub>P\<^sub>L \<psi>2"
  shows  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> \<longrightarrow>\<^sub>P\<^sub>L \<psi>2"
  apply(rule pl_impI)
  apply(rule pl_andEr)
  apply(rule pl_impE[OF pl_weakening[where \<Phi>="{\<phi>}",OF assms]])
  apply(rule pl_ax,simp)
  done

lemma pl_allimp_andEl:
  assumes "\<phi> = (\<lambda>t k. \<phi>' (k,(t k)))"
          "\<psi>1 = (\<lambda>t k. \<psi>1' (k,(t k)))"
          "\<psi>2 = (\<lambda>t k. \<psi>2' (k,(t k)))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi> (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<psi>1 (hp_const x) \<and>\<^sub>P\<^sub>L \<psi>2 (hp_const x)"
    shows  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi> (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<psi>1 (hp_const x)"
  apply(rule pl_allI[where \<phi>="\<phi>' \<longrightarrow>\<^sub>P\<^sub>L \<psi>1'"],simp,simp add: assms(1,2) hp_const_def hp_implies_def split_beta')
  apply(rule pl_impI)
  apply(rule pl_andEl[where \<psi>="\<psi>2'"])
  apply(rule pl_impE[where \<psi>="\<phi>'"])
   apply(rule pl_weakening)
   apply(rule pl_allEVar[where \<phi>="\<lambda>r. \<phi> r \<longrightarrow>\<^sub>P\<^sub>L \<psi>1 r \<and>\<^sub>P\<^sub>L \<psi>2 r"],simp add: assms(1-3) hp_definitions,simp)
   apply(fact)
  apply(rule pl_ax,simp)
  done

lemma pl_allimp_andEr:
  assumes "\<phi> = (\<lambda>t k. \<phi>' (k,t k))"
          "\<psi>1 = (\<lambda>t k. \<psi>1' (k,t k))"
          "\<psi>2 = (\<lambda>t k. \<psi>2' (k,t k))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi> (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<psi>1 (hp_const x) \<and>\<^sub>P\<^sub>L \<psi>2 (hp_const x)"
    shows  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi> (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<psi>2 (hp_const x)"
  apply(rule pl_allI[where \<phi>="\<phi>' \<longrightarrow>\<^sub>P\<^sub>L \<psi>2'"],simp,simp add: assms(1,3) hp_const_def hp_implies_def split_beta')
  apply(rule pl_impI)
  apply(rule pl_andEr[where \<phi>="\<psi>1'"])
  apply(rule pl_impE[where \<psi>="\<phi>'"])
   apply(rule pl_weakening)
   apply(rule pl_allEVar[where \<phi>="\<lambda>r. \<phi> r \<longrightarrow>\<^sub>P\<^sub>L \<psi>1 r \<and>\<^sub>P\<^sub>L \<psi>2 r"],simp add: assms(1-3) hp_definitions,simp)
   apply(fact)
  apply(rule pl_ax,simp)
  done

lemma pl_allimp_addassm:
  assumes "\<phi> = (\<lambda>t k. \<phi>' (k,t k))"
          "\<psi> = (\<lambda>t k. \<psi>' (k,t k))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<phi> (hp_const x)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<psi> (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<phi> (hp_const x)"
  apply(rule pl_allI[where \<phi>="\<psi>' \<longrightarrow>\<^sub>P\<^sub>L \<phi>'"],simp,simp add: assms(1,2) hp_const_def hp_implies_def split_beta')
  apply(rule pl_impI)
  apply(rule pl_weakening)
  apply(rule pl_allEVar[where \<phi>=\<phi>],fact,simp)
  apply fact
  done

lemma pl_cut:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>1 \<longrightarrow>\<^sub>P\<^sub>L \<phi>2"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>2 \<longrightarrow>\<^sub>P\<^sub>L \<phi>3"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi>1 \<longrightarrow>\<^sub>P\<^sub>L \<phi>3"
  apply(rule pl_impI)
  apply(rule pl_impE[OF pl_weakening[OF assms(2),of "{\<phi>1}"]])
  apply(rule pl_impE[OF pl_weakening[OF assms(1),of "{\<phi>1}"]])
  apply(rule pl_ax,simp)
  done

lemma pl_fst_pair:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_fst (hp_pair a b) =\<^sub>P\<^sub>L a"
  by(simp add: hp_definitions pl_der_def)

lemma pl_snd_pair:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_snd (hp_pair a b) =\<^sub>P\<^sub>L b"
  by(simp add: hp_definitions pl_der_def)

lemma pl_pair_fstsnd:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_pair (hp_fst z) (hp_snd z) =\<^sub>P\<^sub>L z"
  by(simp add: hp_definitions pl_der_def)

lemma pl_hp_id:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_id =\<^sub>P\<^sub>L hp_lambda var1"
  by(auto simp add: hp_definitions pl_der_def)

lemma pl_lambda_const:
  assumes "t = (\<lambda>envx. t' (fst envx))"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_lambda t =\<^sub>P\<^sub>L hp_constf t'"
  by(auto simp add: assms hp_definitions pl_der_def)

lemma pl_beta:
  assumes "t = (\<lambda>env. f (env,e env))"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_app (hp_lambda f) e =\<^sub>P\<^sub>L t"
  by(simp add: hp_definitions assms pl_der_def)

lemma pl_eta:
  assumes "t = (\<lambda>envx. t' (fst envx))"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_lambda (hp_app t var1) =\<^sub>P\<^sub>L t'"
  by(auto simp add: assms hp_definitions pl_der_def)

lemma pl_rec_nat_0:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_app (hp_rec_nat t f) (hp_const 0) =\<^sub>P\<^sub>L t"
  by(simp add: hp_rec_nat_simp' pl_der_def hp_eq_def)

lemma pl_rec_nat_suc:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_app (hp_rec_nat t f) (hp_suc e) =\<^sub>P\<^sub>L hp_app (hp_app f e) (hp_app (hp_rec_nat t f) e)"
  by(simp add: hp_rec_nat_simp' pl_der_def hp_eq_def)

text \<open> axioms \<close>
lemma hp_ennexpect_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_ennexpect t (hp_constf c) =\<^sub>P\<^sub>L c"
  using qbs_prob_ennintegral_const by(auto simp add: hp_definitions pl_der_def)

lemma hp_expect_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect t (hp_constf c) =\<^sub>P\<^sub>L c"
  using qbs_prob_integral_const by(auto simp add: hp_definitions pl_der_def)

lemma hp_expect_const':
  assumes "f' = (\<lambda>env. f (fst env))"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect t (hp_lambda f') =\<^sub>P\<^sub>L f"
  using qbs_prob_integral_const by(auto simp add: hp_definitions pl_der_def curry_def assms)

lemma pl_expect_nonneg:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; monadP_qbs X"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. hp_const 0 \<le>\<^sub>P\<^sub>L hp_app f (hp_const x)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const 0 \<le>\<^sub>P\<^sub>L hp_expect t f"
  using qbs_prob_integral_nonneg[of _ X] assms(2)[simplified hp_definitions pl_der_def, simplified] qbs_morphismE(1)[OF assms(1)[simplified hpprog_typing_def]]
  apply(simp add: hp_definitions monadP_qbs_Px_def pl_der_def)
  by blast

lemma pl_ennexpect_add:
  assumes "\<Gamma> \<turnstile>\<^sub>t e1 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
          "\<Gamma> \<turnstile>\<^sub>t e2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t t ;; monadP_qbs T"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_ennexpect t (e1 +\<^sub>t e2) =\<^sub>P\<^sub>L hp_ennexpect t e1 +\<^sub>t hp_ennexpect t e2"
  using qbs_prob_ennintegral_add[of _ T] qbs_morphismE(1)[OF assms(1)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF assms(2)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF assms(3)[simplified hpprog_typing_def]]
  apply(simp add: pl_der_def hp_definitions hpprog_typing_def monadP_qbs_Px_def)
  by blast

lemma pl_expect_add:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e1"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e2"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect t (e1 +\<^sub>t e2)
         =\<^sub>P\<^sub>L hp_expect t e1 +\<^sub>t hp_expect t e2"
  using assms qbs_prob_integral_add
  by(force simp add: pl_der_def hp_definitions)

lemma pl_ennexpect_cmult:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; exp_qbs X \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t t ;; monadP_qbs X"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_ennexpect t (hp_constf c *\<^sub>t e) =\<^sub>P\<^sub>L c *\<^sub>t hp_ennexpect t e"
  unfolding pl_der_def
proof auto
  fix x
  assume "x \<in> qbs_space \<Gamma>"
  then show "((hp_ennexpect t (hp_constf c *\<^sub>t e) =\<^sub>P\<^sub>L c *\<^sub>t hp_ennexpect t e)) x"
    using qbs_prob_ennintegral_cmult qbs_morphismE(1)[of e \<Gamma> "exp_qbs X \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"] qbs_morphismE(1)[of t \<Gamma> "monadP_qbs X"] assms
    by(fastforce simp: hpprog_typing_def hp_definitions pl_der_def monadP_qbs_Px_def)
qed

lemma pl_expect_cmult:
    "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect t (hp_constf c *\<^sub>t e) =\<^sub>P\<^sub>L c *\<^sub>t hp_expect t e"
  using qbs_prob_integral_cmult
  by(auto simp add: pl_der_def hp_definitions)

lemma pl_var_eq:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_var t e =\<^sub>P\<^sub>L hp_expect t ((e -\<^sub>t hp_constf (hp_expect t e)) *\<^sub>t (e -\<^sub>t hp_constf (hp_expect t e)))"
  by(simp add: pl_der_def hp_var_def2 hp_eq_def)

lemma pl_integrableI:
  assumes "f' = (\<lambda>env r. ennreal \<bar>f env r\<bar>)"
          "\<Gamma> \<turnstile>\<^sub>t f ;; exp_qbs X \<real>\<^sub>Q"
          "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs X"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_ennexpect e f' <\<^sub>P\<^sub>L hp_const \<infinity>"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable e f"
  unfolding pl_der_def hp_integrable_def
proof auto
  fix x
  assume "x \<in> qbs_space \<Gamma>" "hp_conjall \<Psi> x"
  then show "qbs_integrable (e x) (f x)"
    using assms(2-4) qbs_integrable_iff_bounded[of "e x" X "f x"] qbs_morphismE(1)[OF assms(2)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF assms(3)[simplified hpprog_typing_def]]
    by(fastforce simp: hp_definitions pl_der_def hpprog_typing_def assms(1) monadP_qbs_Px_def)
qed

lemma pl_integrable_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t (hp_constf c)"
  using qbs_integrable_const by(auto simp add:pl_der_def hp_definitions)

lemma pl_integrable_return:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; exp_qbs X \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t x ;; X"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_return X x) e"
  using assms qbs_integrable_return[where X=X] qbs_morphismE(1)[OF assms(1)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF assms(2)[simplified hpprog_typing_def]]
  by(fastforce simp: hp_definitions hpprog_typing_def pl_der_def)

lemma pl_integrable_bind_return:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs Y"
          "\<Gamma>,,Y \<turnstile>\<^sub>t e' ;; Z"
      and "\<Gamma> \<turnstile>\<^sub>t e'' ;; exp_qbs Z \<real>\<^sub>Q"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_bind e (hp_lambda (hp_return Z e'))) e'' \<longrightarrow>\<^sub>P\<^sub>L hp_integrable e (hp_comp e'' (hp_lambda e'))"
proof(auto simp add: pl_der_def hp_definitions hp_comp_def)
  fix x
  assume "x \<in> qbs_space \<Gamma>"
         "qbs_integrable (e x \<bind> curry (\<lambda>env. qbs_return Z (e' env)) x) (e'' x)"
  then show "qbs_integrable (e x) (\<lambda>xa. e'' x (e' (x, xa)))"
    using qbs_integrable_bind_return[of "e x" Y "e'' x" Z "curry e' x"] qbs_morphismE(1)[OF assms(3)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF curry_preserves_morphisms[OF assms(2)[simplified hpprog_typing_def hpprog_context_def]]]
          qbs_morphismE(1)[OF assms(1)[simplified hpprog_typing_def]]
    by(fastforce simp: curry_def comp_def monadP_qbs_Px_def)
qed

lemma pl_integrable_bind_return':
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs Y"
          "\<Gamma>,,Y \<turnstile>\<^sub>t e' ;; Z"
      and "\<Gamma> \<turnstile>\<^sub>t e'' ;; exp_qbs Z \<real>\<^sub>Q"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable e (hp_comp e'' (hp_lambda e')) \<longrightarrow>\<^sub>P\<^sub>L hp_integrable (hp_bind e (hp_lambda (hp_return Z e'))) e''"
proof(auto simp add: pl_der_def hp_definitions hp_comp_def)
  fix x
  assume "x \<in> qbs_space \<Gamma>"
         "qbs_integrable (e x) (\<lambda>xa. e'' x (e' (x, xa)))"
  then show "qbs_integrable (e x \<bind> curry (\<lambda>env. qbs_return Z (e' env)) x) (e'' x)"
    using qbs_integrable_bind_return[of "e x" Y "e'' x" Z "curry e' x"]  qbs_morphismE(1)[OF assms(3)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF curry_preserves_morphisms[OF assms(2)[simplified hpprog_typing_def hpprog_context_def]]]
          qbs_morphismE(1)[OF assms(1)[simplified hpprog_typing_def]]
    by(fastforce simp: curry_def comp_def)
qed

lemma pl_integrable_add:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e1"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e2"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t (e1 +\<^sub>t e2)"
  using assms qbs_integrable_add by(simp add: pl_der_def hp_definitions)

lemma pl_integrable_diff:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e1"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e2"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t (e1 -\<^sub>t e2)"
  using assms qbs_integrable_diff by(simp add: pl_der_def hp_definitions)

lemma pl_integrable_mult:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t (hp_constf c *\<^sub>t e)"
  using assms qbs_integrable_mult by(simp add: pl_der_def hp_definitions)

lemma pl_integrable_indep1':
  assumes "e' = (\<lambda>t env xy. e env (t (env,xy)))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) (e' (hp_fst var1))"
  using qbs_integrable_indep1 assms(2)
  by(auto simp add: hp_definitions pl_der_def assms(1) curry_def)

lemma pl_integrable_indep1:
  assumes "e' = (\<lambda>t envxy. e (fst envxy) (t envxy))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) (hp_lambda (e' (hp_fst var1)))"
  using qbs_integrable_indep1 assms(2)
  by(auto simp add: hp_definitions pl_der_def assms(1) curry_def)

lemma pl_integrable_indep2':
  assumes "e' = (\<lambda>t env xy. e env (t (env,xy)))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) (e' (hp_snd var1))"
  using qbs_integrable_indep2 assms(2)
  by(auto simp add: hp_definitions pl_der_def assms(1) curry_def)

lemma pl_integrable_indep2:
  assumes "e' = (\<lambda>t envxy. e (fst envxy) (t envxy))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) (hp_lambda (e' (hp_snd var1)))"
  using qbs_integrable_indep2 assms(2)
  by(auto simp add: hp_definitions pl_der_def assms(1) curry_def)

lemma pl_integrable_indep_mult':
  assumes "e' = (\<lambda>t env xy. e env (t (env,xy)))"
          "f' = (\<lambda>t env xy. f env (t (env,xy)))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) (e' (hp_fst var1) *\<^sub>t f' (hp_snd var1))"
  using qbs_integrable_indep_mult assms(3,4)
  by(auto simp add: hp_definitions pl_der_def assms(1,2) curry_def,blast)

lemma pl_integrable_indep_mult:
  assumes "e' = (\<lambda>t envxy. e (fst envxy) (t envxy))"
          "f' = (\<lambda>t envxy. f (fst envxy) (t envxy))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) (hp_lambda (e' (hp_fst var1)) *\<^sub>t hp_lambda (f' (hp_snd var1)))"
  using qbs_integrable_indep_mult assms(3,4)
  by(auto simp add: hp_definitions pl_der_def assms(1,2) curry_def,blast)

lemma pl_var_affine:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_var t (hp_constf a *\<^sub>t e +\<^sub>t hp_constf b) =\<^sub>P\<^sub>L a^\<^sup>t2 *\<^sub>t hp_var t e"
proof(auto simp add: hp_definitions pl_der_def)
  fix x
  assume "x \<in> qbs_space \<Gamma>"
        " hp_conjall \<Psi> x"
  then show "qbs_prob_var (t x) (\<lambda>env. a x * e x env + b x) = a x * a x * qbs_prob_var (t x) (e x)"
    using qbs_prob_var_affine[of "t x" "e x" "a x" "b x"] assms
    by(simp add: hp_integrable_def pl_der_def power2_eq_square)
qed


lemma pl_expect_fst:
  assumes "e' = (\<lambda>t envxy. e (fst envxy) (t envxy))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) (hp_lambda (e' (hp_fst var1))) =\<^sub>P\<^sub>L hp_expect s e"
  using qbs_prob_integral_indep1 assms(2)
  by(auto simp add: assms(1) hp_definitions pl_der_def curry_def)

lemma pl_expect_fst':
  assumes "e' = (\<lambda>t env xy. e env (t (env,xy)))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) (e' (hp_fst var1)) =\<^sub>P\<^sub>L hp_expect s e"
  using qbs_prob_integral_indep1 assms(2)
  by(auto simp add: assms(1) hp_definitions pl_der_def)

lemma pl_expect_snd:
  assumes "e' = (\<lambda>t envxy. e (fst envxy) (t envxy))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) (hp_lambda (e' (hp_snd var1))) =\<^sub>P\<^sub>L hp_expect t e"
  using qbs_prob_integral_indep2 assms(2)
  by(auto simp add: assms(1) hp_definitions pl_der_def curry_def)

lemma pl_expect_snd':
  assumes "e' = (\<lambda>t env xy. e env (t (env,xy)))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) (e' (hp_snd var1)) =\<^sub>P\<^sub>L hp_expect t e"
  using qbs_prob_integral_indep2 assms(2)
  by(auto simp add: assms(1) hp_definitions pl_der_def)


lemma pl_expect_Fubini_fst:
  assumes "f' = (\<lambda>t envxy. f (fst (fst envxy)) (t envxy))"
          "t' = (\<lambda>env. t (fst env))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) f =\<^sub>P\<^sub>L hp_expect s (hp_lambda (hp_expect t' (hp_lambda (f' (hp_pair var2 var1)))))"
  using qbs_prob_integral_Fubini_fst assms(3)
  by(fastforce simp: assms(1,2) hp_definitions curry_def pl_der_def)

lemma pl_expect_Fubini_fst':
  assumes "f' = (\<lambda>t envy x. f (fst envy) (t (envy,x)))"
          "t' = (\<lambda>env. t (fst env))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) f =\<^sub>P\<^sub>L hp_expect s (hp_lambda (hp_expect t' (f' (hp_pair var2 var1))))"
  using qbs_prob_integral_Fubini_fst assms(3)
  by(fastforce simp: assms(1,2) hp_definitions curry_def pl_der_def)

lemma pl_expect_Fubini_snd:
  assumes "f' = (\<lambda>t envxy. f (fst (fst envxy)) (t envxy))"
          "s' = (\<lambda>env. s (fst env))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) f =\<^sub>P\<^sub>L hp_expect t (hp_lambda (hp_expect s' (hp_lambda (f' (hp_pair var1 var2)))))"
  using qbs_prob_integral_Fubini_snd assms(3)
  by(fastforce simp: assms(1,2) hp_definitions curry_def pl_der_def)

lemma pl_expect_Fubini_snd':
  assumes "f' = (\<lambda>t envx y. f (fst envx) (t (envx,y)))"
          "s' = (\<lambda>env. s (fst env))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable (hp_pair_measure s t) f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) f =\<^sub>P\<^sub>L hp_expect t (hp_lambda (hp_expect s' (f' (hp_pair var1 var2))))"
  using qbs_prob_integral_Fubini_snd assms(3)
  by(fastforce simp: assms(1,2) hp_definitions curry_def pl_der_def)

lemma comp_id:
 "hp_comp hp_id e = e"
  by(simp add: hp_comp_def hp_id_def hp_const_def)

lemma pl_comp_id_left:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_comp hp_id e =\<^sub>P\<^sub>L e"
  by(simp add: hp_comp_def pl_der_def hp_definitions)

lemma pl_comp_id_sq_left:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_comp (hp_id *\<^sub>t hp_id) e =\<^sub>P\<^sub>L e *\<^sub>t e"
  by(simp add: hp_comp_def pl_der_def hp_definitions)

lemma pl_ennexpect_bind:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs Y"
          "\<Gamma>,,Y \<turnstile>\<^sub>t e' ;; Z"
      and "\<Gamma> \<turnstile>\<^sub>t e'' ;; exp_qbs Z \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_ennexpect (hp_bind e (hp_lambda (hp_return Z e'))) e'' =\<^sub>P\<^sub>L hp_ennexpect e (hp_comp e'' (hp_lambda e'))"
  unfolding hp_ennexpect_def hp_bind_def hp_lambda_def hp_return_def hp_eq_def hp_comp_def pl_der_def curry_def
proof auto
  fix x
  assume "x \<in> qbs_space \<Gamma>"
  then show "qbs_prob_ennintegral (e x \<bind> (\<lambda>y. qbs_return Z (e' (x, y)))) (e'' x) =
         qbs_prob_ennintegral (e x) (e'' x \<circ> (\<lambda>y. e' (x, y)))"
    using qbs_prob_ennintegral_bind_return[of "e x" Y "e'' x" Z "curry e' x"] assms curry_preserves_morphisms[of e' \<Gamma> Y Z] qbs_morphismE(1)[of e'' \<Gamma> "exp_qbs Z \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"] qbs_morphismE(1)[of "curry e'" \<Gamma> "exp_qbs Y Z"] qbs_morphismE(1)[of e \<Gamma> "monadP_qbs Y"]
    by(fastforce simp: hpprog_typing_def hpprog_context_def curry_def)
qed

lemma pl_expect_bind:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs Y"
          "\<Gamma>,,Y \<turnstile>\<^sub>t e' ;; Z"
      and "\<Gamma> \<turnstile>\<^sub>t e'' ;; exp_qbs Z \<real>\<^sub>Q"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_bind e (hp_lambda (hp_return Z e'))) e'' =\<^sub>P\<^sub>L hp_expect e (hp_comp e'' (hp_lambda e'))"
  unfolding hp_expect_def hp_bind_def hp_lambda_def hp_return_def hp_eq_def hp_comp_def pl_der_def curry_def
proof auto
  fix x
  assume "x \<in> qbs_space \<Gamma>"
  then show "qbs_prob_integral (e x \<bind> (\<lambda>y. qbs_return Z (e' (x, y)))) (e'' x) =
         qbs_prob_integral (e x) (e'' x \<circ> (\<lambda>y. e' (x, y)))"
    using qbs_prob_integral_bind_return[of "e x" Y "e'' x" Z "curry e' x"] assms curry_preserves_morphisms[of e' \<Gamma> Y Z] qbs_morphismE(1)[of e'' \<Gamma> "exp_qbs Z \<real>\<^sub>Q"] qbs_morphismE(1)[of "curry e'" \<Gamma> "exp_qbs Y Z"] qbs_morphismE(1)[of e \<Gamma> "monadP_qbs Y"]
    by(fastforce simp: hpprog_typing_def hpprog_context_def curry_def)
qed

lemma pl_pair_bind_return2:
  assumes "t2' = (\<lambda>kx. t2 (fst kx))"
          "e' = (\<lambda>v2 v1 k. e (fst (fst k)) (v2 k, v1 k))"
          "\<Gamma> \<turnstile>\<^sub>t t1 ;; monadP_qbs X"
          "\<Gamma> \<turnstile>\<^sub>t t2 ;; monadP_qbs Y"
          "\<Gamma> \<turnstile>\<^sub>t e ;; exp_qbs (X \<Otimes>\<^sub>Q Y) (monadP_qbs Z)"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (hp_bind t1 (hp_lambda (hp_bind t2' (hp_lambda (e' var2 var1))))) =\<^sub>P\<^sub>L hp_bind (hp_bind t1 (hp_lambda (hp_bind t2' (hp_lambda (hp_return (X \<Otimes>\<^sub>Q Y) (hp_pair var2 var1)))))) e"
proof(auto simp add: assms(1,2) pl_der_def hp_definitions curry_def)
  fix x
  assume "x \<in> qbs_space \<Gamma>"
  then have "t1 x \<in> monadP_qbs_Px X"
            "t2 x \<in> monadP_qbs_Px Y"
            "e x \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs Z"
    using qbs_morphismE(1)[OF assms(3)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF assms(4)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF assms(5)[simplified hpprog_typing_def]]
    by auto      
  thus "t1 x \<bind> (\<lambda>r1. t2 x \<bind> (\<lambda>r2. e x (r1, r2))) =
        t1 x \<bind> (\<lambda>r1. t2 x \<bind> (\<lambda>r2. qbs_return (X \<Otimes>\<^sub>Q Y) (r1, r2))) \<bind> e x"
    using qbs_pair_bind_return2[of "e x" X Y Z "t1 x" "t2 x"]
    by simp
qed


lemma pl_pair_measure_bind_return:
  assumes "n' = (\<lambda>env. n (fst env))"
          "\<Gamma> \<turnstile>\<^sub>t m ;; monadP_qbs M"
      and "\<Gamma> \<turnstile>\<^sub>t n ;; monadP_qbs N"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L m \<bind> hp_lambda (n' \<bind> hp_lambda (hp_return (M \<Otimes>\<^sub>Q N) (hp_pair var2 var1))) =\<^sub>P\<^sub>L hp_pair_measure m n"
proof(auto simp add: pl_der_def hp_eq_def)
  fix x
  assume "x \<in> qbs_space \<Gamma>"
  then show "(m \<bind> hp_lambda (n' \<bind> hp_lambda (hp_return (M \<Otimes>\<^sub>Q N) (hp_pair var2 var1)))) x = hp_pair_measure m n x"
    using qbs_prob_pair_measure_eq_bind[of "m x" M "n x" N] qbs_morphismE(1)[OF assms(2)[simplified hpprog_typing_def]] qbs_morphismE(1)[OF assms(3)[simplified hpprog_typing_def]]
    by(force simp add: hp_pair_measure_def hp_lambda_def hp_bind_def hp_return_def hp_pair_def curry_def var1_def var2_def assms(1))
qed

text \<open> We explicitly introduce probability measures for readability. \<close>
definition "hp_eprob \<equiv> hp_lift2 qbs_emeasure"
definition "hp_prob \<equiv> hp_lift2 qbs_measure"

definition hp_set :: "('typ \<Rightarrow> 'cont \<Rightarrow> bool) \<Rightarrow> 'cont \<Rightarrow> 'typ set" where
"hp_set P \<equiv> (\<lambda>env. {x. P x env})"
syntax
  "_hp_set" :: "pttrn \<Rightarrow> ('cont \<Rightarrow> bool) \<Rightarrow> 'cont \<Rightarrow> 'typ set" ("(1{_./ _}\<^sub>t)")
translations
  "{x. P}\<^sub>t" \<rightleftharpoons> "CONST hp_set (\<lambda>x. P)"

lemmas hp_definitions' = hp_definitions hp_prob_def hp_eprob_def hp_set_def hp_comp_def

term "hp_eprob e {r. a \<le>\<^sub>P\<^sub>L \<bar>hp_const r\<bar>\<^sub>t}\<^sub>t"

lemma pl_markov_inequality1:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs \<real>\<^sub>Q"
          "\<Gamma> \<turnstile>\<^sub>t a ;; \<real>\<^sub>Q"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable e (\<lambda>env x. x)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const 0 <\<^sub>P\<^sub>L a \<longrightarrow>\<^sub>P\<^sub>L hp_eprob e {r. a \<le>\<^sub>P\<^sub>L \<bar>hp_const r\<bar>\<^sub>t}\<^sub>t \<le>\<^sub>P\<^sub>L hp_ennreal (hp_expect e (\<lambda>env x. \<bar>x\<bar>) /\<^sub>t  a)"
proof(auto simp add: hp_definitions pl_der_def hp_eprob_def hp_set_def)
  fix x
  assume H:"x \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> x"
           "0 < a x"
  then have "qbs_space (qbs_prob_space_qbs (e x)) = UNIV"
    using qbs_morphismE(2)[OF assms(1)[simplified hpprog_typing_def]] 
    by(simp add: monadP_qbs_Px_def)
  thus "qbs_emeasure (e x) {r. a x \<le> \<bar>r\<bar>} \<le> ennreal (qbs_prob_integral (e x) abs / a x)"
    using qbs_prob_integral_Markov_inequality_abs[OF _ _ H(3),of "e x" _ "\<lambda>x. x"] assms(2,3) H
    by(simp add: pl_der_def hpprog_typing_def hp_integrable_def qbs_prob_measure_space)
qed

lemma pl_markov_inequality2:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs \<real>\<^sub>Q"
          "\<Gamma> \<turnstile>\<^sub>t a ;; \<real>\<^sub>Q"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable e (\<lambda>env x. x)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const 0 <\<^sub>P\<^sub>L a \<longrightarrow>\<^sub>P\<^sub>L hp_prob e (\<lambda>env. {r. a env \<le> \<bar>r\<bar>}) \<le>\<^sub>P\<^sub>L hp_expect e (\<lambda>env x. \<bar>x\<bar>) /\<^sub>t  a"
proof(auto simp add: hp_definitions pl_der_def hp_prob_def)
  fix x
  assume H:"x \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> x"
           "0 < a x"
  then have "qbs_space (qbs_prob_space_qbs (e x)) = UNIV"
    using qbs_morphismE(2)[OF assms(1)[simplified hpprog_typing_def]]
    by(simp add: monadP_qbs_Px_def)
  thus "qbs_measure (e x) {r. a x \<le> \<bar>r\<bar>} \<le> qbs_prob_integral (e x) abs / a x"
    using qbs_prob_integral_Markov_inequality_abs'[OF _ _ H(3),of "e x" _ "\<lambda>x. x"] assms(2,3) H
    by(simp add: pl_der_def hpprog_typing_def hp_integrable_def qbs_prob_measure_space)
qed

lemma pl_chebyshev_inequality:
  assumes "\<Gamma> \<turnstile>\<^sub>t d ;; monadP_qbs \<real>\<^sub>Q"
          "\<Gamma> \<turnstile>\<^sub>t b ;; \<real>\<^sub>Q"
          "\<Gamma> \<turnstile>\<^sub>t \<mu> ;; \<real>\<^sub>Q"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable d (hp_id)"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable d (hp_id *\<^sub>t hp_id)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const 0 <\<^sub>P\<^sub>L b \<and>\<^sub>P\<^sub>L \<mu> =\<^sub>P\<^sub>L hp_expect d hp_id \<longrightarrow>\<^sub>P\<^sub>L hp_prob d {r. b \<le>\<^sub>P\<^sub>L \<bar>hp_const r -\<^sub>t \<mu> \<bar>\<^sub>t}\<^sub>t \<le>\<^sub>P\<^sub>L hp_var d hp_id /\<^sub>t b^\<^sup>t2"
proof(auto simp add: hp_definitions hp_prob_def pl_der_def hp_set_def)
  fix x
  assume H:"x \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> x"
           "0 < b x"
  then have "qbs_space (qbs_prob_space_qbs (d x)) = UNIV"
    using qbs_morphismE(2)[OF assms(1)[simplified hpprog_typing_def]]
    by(simp add: monadP_qbs_Px_def)
  thus "qbs_measure (d x) {r. b x \<le> \<bar>r - qbs_prob_integral (d x) id\<bar>} \<le> qbs_prob_var (d x) id / (b x * b x)"
    using qbs_prob_integral_Chebyshev_inequality[of "d x" _ id "b x"] assms(4,5) H
    by(simp add: pl_der_def power2_eq_square hp_definitions)
qed


lemma pl_suc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_suc n =\<^sub>P\<^sub>L hp_const 1 +\<^sub>t n"
  by(simp add: hp_definitions pl_der_def)

lemma pl_plus_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const c1 +\<^sub>t hp_const c2 =\<^sub>P\<^sub>L hp_const (c1 + c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_plus_constf:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf c1 +\<^sub>t hp_constf c2 =\<^sub>P\<^sub>L hp_constf (c1 +\<^sub>t c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minus_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const c1 -\<^sub>t hp_const c2 =\<^sub>P\<^sub>L hp_const (c1 - c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minus_constf:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf c1 -\<^sub>t hp_constf c2 =\<^sub>P\<^sub>L hp_constf (c1 -\<^sub>t c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_times_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const c1 *\<^sub>t hp_const c2 =\<^sub>P\<^sub>L hp_const (c1 * c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_times_constf:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf c1 *\<^sub>t hp_constf c2 =\<^sub>P\<^sub>L hp_constf (c1 *\<^sub>t c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_div_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const c1 /\<^sub>t hp_const c2 =\<^sub>P\<^sub>L hp_const (c1 / c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_div_constf:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf c1 /\<^sub>t hp_constf c2 =\<^sub>P\<^sub>L hp_constf (c1 /\<^sub>t c2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_power_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const c ^\<^sup>tn =\<^sub>P\<^sub>L hp_const (c^n)"
  by(induction n; auto simp add: hp_definitions pl_der_def)

lemma pl_abs_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<bar>hp_const c\<bar>\<^sub>t =\<^sub>P\<^sub>L hp_const \<bar>c\<bar>"
  by(simp add: hp_definitions pl_der_def)

lemma pl_real_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_real (hp_const n) =\<^sub>P\<^sub>L hp_const (real n)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_real_plus:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_real (n1 +\<^sub>t n2) =\<^sub>P\<^sub>L hp_real n1 +\<^sub>t hp_real n2"
  by(simp add: hp_definitions pl_der_def)

lemma pl_enn2real_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_enn2real (hp_const r) =\<^sub>P\<^sub>L hp_const (enn2real r)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_ennreal_const:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_ennreal (hp_const r) =\<^sub>P\<^sub>L hp_const (ennreal r)"
  by(simp add: hp_definitions pl_der_def)

text \<open> use different type classes, but \<open>\<nat>\<close>, \<open>\<real>\<close> and, ennreal are instances of these classes \<close>
lemma pl_plus_left0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0::'a::comm_monoid_add) +\<^sub>t n =\<^sub>P\<^sub>L n"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funplus_left0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_const (0::'a::comm_monoid_add)) +\<^sub>t f =\<^sub>P\<^sub>L f"
  by(simp add: hp_definitions pl_der_def)

lemma pl_plus_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> 'a::ab_semigroup_add) +\<^sub>t n2 =\<^sub>P\<^sub>L n2 +\<^sub>t n1"
  by(simp add: hp_definitions pl_der_def add.commute)

lemma pl_funplus_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'b \<Rightarrow> 'a::ab_semigroup_add) +\<^sub>t f2 =\<^sub>P\<^sub>L f2 +\<^sub>t f1"
  by(simp add: hp_definitions pl_der_def add.commute)

lemma pl_plus_assoc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> 'a::semigroup_add) +\<^sub>t (n2 +\<^sub>t n3) =\<^sub>P\<^sub>L (n1 +\<^sub>t n2) +\<^sub>t n3"
  by(simp add: hp_definitions pl_der_def add.assoc)

lemma pl_funplus_assoc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'b \<Rightarrow> 'a::semigroup_add) +\<^sub>t (f2 +\<^sub>t f3) =\<^sub>P\<^sub>L (f1 +\<^sub>t f2) +\<^sub>t f3"
  by(simp add: hp_definitions pl_der_def add.assoc)


lemma pl_minusn_0_n:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0 :: nat) -\<^sub>t n =\<^sub>P\<^sub>L hp_const 0"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusn_0_n:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_const (0 :: nat)) -\<^sub>t f =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusn_n_0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L n -\<^sub>t hp_const (0 :: nat) =\<^sub>P\<^sub>L n"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusn_n_0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L f -\<^sub>t hp_constf (hp_const (0 :: nat)) =\<^sub>P\<^sub>L f"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusn_suc_suc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_suc n1 -\<^sub>t hp_suc n2 =\<^sub>P\<^sub>L n1 -\<^sub>t n2"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusn_suc_suc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_suc n1) -\<^sub>t hp_constf (hp_suc n2) =\<^sub>P\<^sub>L hp_constf n1 -\<^sub>t hp_constf n2"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusn_left:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> nat) -\<^sub>t (n2 +\<^sub>t n3) =\<^sub>P\<^sub>L n1 -\<^sub>t n2 -\<^sub>t n3"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusn_left:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> 'a \<Rightarrow> nat) -\<^sub>t (n2 +\<^sub>t n3) =\<^sub>P\<^sub>L n1 -\<^sub>t n2 -\<^sub>t n3"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusn_cancel:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> nat) +\<^sub>t k -\<^sub>t (n2 +\<^sub>t k) =\<^sub>P\<^sub>L n1 -\<^sub>t n2"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusn_cancel:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'a \<Rightarrow> nat) +\<^sub>t g -\<^sub>t (f2 +\<^sub>t g) =\<^sub>P\<^sub>L f1 -\<^sub>t f2"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusn_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> nat) -\<^sub>t n2 -\<^sub>t n3 =\<^sub>P\<^sub>L n1 -\<^sub>t n3 -\<^sub>t n2"
  by(simp add: hp_definitions pl_der_def add.commute)

lemma pl_funminusn_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'a \<Rightarrow> nat) -\<^sub>t f2 -\<^sub>t f3 =\<^sub>P\<^sub>L f1 -\<^sub>t f3 -\<^sub>t f2"
  by(simp add: hp_definitions pl_der_def add.commute)

lemma pl_minusr_eq0:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L r1 -\<^sub>t r2 =\<^sub>P\<^sub>L hp_const (0 :: real) \<longrightarrow>\<^sub>P\<^sub>L r1 =\<^sub>P\<^sub>L r2"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusr_eq0:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L r1 -\<^sub>t r2 =\<^sub>P\<^sub>L hp_constf (hp_const (0 :: real)) \<longrightarrow>\<^sub>P\<^sub>L r1 =\<^sub>P\<^sub>L r2"
proof(auto simp add: hp_definitions pl_der_def)
  fix x
  assume "(\<lambda>xa. r1 x xa - r2 x xa) = (\<lambda>_. 0)"
  then have "\<And>k. r1 x k - r2 x k = 0"
    by meson
  thus "r1 x = r2 x" by auto
qed

lemma pl_minusr_minus0:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L r1 =\<^sub>P\<^sub>L r2 \<longrightarrow>\<^sub>P\<^sub>L r1 -\<^sub>t r2 =\<^sub>P\<^sub>L hp_const (0 :: real)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusr_minus0:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L r1 =\<^sub>P\<^sub>L r2 \<longrightarrow>\<^sub>P\<^sub>L r1 -\<^sub>t r2 =\<^sub>P\<^sub>L hp_constf (hp_const (0 :: real))"
  by(simp add: hp_definitions pl_der_def)

lemma pl_uminus_times:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L -\<^sub>t (r :: 'env \<Rightarrow> real) =\<^sub>P\<^sub>L -\<^sub>t (hp_const 1) *\<^sub>t r"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funuminus_times:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L -\<^sub>t (f :: 'env \<Rightarrow> 'a \<Rightarrow> real) =\<^sub>P\<^sub>L -\<^sub>t (hp_constf (hp_const 1)) *\<^sub>t f"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusr_plus_uminus:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> real) -\<^sub>t r2 =\<^sub>P\<^sub>L r1 +\<^sub>t (-\<^sub>t r2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusr_plus_uminus:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> 'a \<Rightarrow> real) -\<^sub>t r2 =\<^sub>P\<^sub>L r1 +\<^sub>t (-\<^sub>t r2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusenn_0_n:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0 :: ennreal) -\<^sub>t n =\<^sub>P\<^sub>L hp_const 0"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusenn_0_n:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_const (0 :: ennreal)) -\<^sub>t f =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusenn_n_0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L n -\<^sub>t hp_const (0 :: ennreal) =\<^sub>P\<^sub>L n"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusenn_n_0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L f -\<^sub>t hp_constf (hp_const (0 :: ennreal)) =\<^sub>P\<^sub>L f"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusenn_top_minus:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (\<infinity> :: ennreal) -\<^sub>t r =\<^sub>P\<^sub>L hp_const \<infinity>"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funminusenn_top_minus:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_const (\<infinity> :: ennreal)) -\<^sub>t f =\<^sub>P\<^sub>L hp_constf (hp_const \<infinity>)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusenn_minus_top:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L r1 -\<^sub>t r2 =\<^sub>P\<^sub>L hp_const (\<infinity>::ennreal) \<longrightarrow>\<^sub>P\<^sub>L r1 =\<^sub>P\<^sub>L hp_const \<infinity>"
  by(simp add: hp_definitions pl_der_def)

lemma pl_minusennn_left:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> ennreal) -\<^sub>t (r2 +\<^sub>t r3) =\<^sub>P\<^sub>L r1 -\<^sub>t r2 -\<^sub>t r3"
  by(simp add: hp_definitions pl_der_def diff_add_eq_diff_diff_swap_ennreal)

lemma pl_funminusenn_left:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> 'a \<Rightarrow> ennreal) -\<^sub>t (r2 +\<^sub>t r3) =\<^sub>P\<^sub>L r1 -\<^sub>t r2 -\<^sub>t r3"
  by(simp add: hp_definitions pl_der_def diff_add_eq_diff_diff_swap_ennreal)

lemma pl_minusenn_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> ennreal) -\<^sub>t r2 -\<^sub>t r3 =\<^sub>P\<^sub>L r1 -\<^sub>t r3 -\<^sub>t r2"
  by(simp add: hp_definitions pl_der_def add.commute diff_diff_commute_ennreal)

lemma pl_funminusenn_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'a \<Rightarrow> ennreal) -\<^sub>t f2 -\<^sub>t f3 =\<^sub>P\<^sub>L f1 -\<^sub>t f3 -\<^sub>t f2"
  by(simp add: hp_definitions pl_der_def add.commute diff_diff_commute_ennreal)

lemma pl_times_left0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0::'a::comm_semiring_1) *\<^sub>t n =\<^sub>P\<^sub>L hp_const 0"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funtimes_left0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf( hp_const (0::'a::comm_semiring_1)) *\<^sub>t n =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_times_left1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (1::'a::comm_semiring_1) *\<^sub>t n =\<^sub>P\<^sub>L n"
  by(simp add: hp_definitions pl_der_def)

lemma pl_funtimes_left1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_const (1::'a::comm_semiring_1)) *\<^sub>t f =\<^sub>P\<^sub>L f"
  by(simp add: hp_definitions pl_der_def)

lemma pl_times_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> 'a::comm_semiring_1) *\<^sub>t n2 =\<^sub>P\<^sub>L n2 *\<^sub>t n1"
  by(simp add: hp_definitions pl_der_def mult.commute)

lemma pl_funtimes_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'b \<Rightarrow> 'a::comm_semiring_1) *\<^sub>t f2 =\<^sub>P\<^sub>L f2 *\<^sub>t f1"
  by(simp add: hp_definitions pl_der_def mult.commute)

lemma pl_times_assoc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> 'a::comm_semiring_1) *\<^sub>t (n2 *\<^sub>t n3) =\<^sub>P\<^sub>L (n1 *\<^sub>t n2) *\<^sub>t n3"
  by(simp add: hp_definitions pl_der_def mult.assoc)

lemma pl_funtimes_assoc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'b \<Rightarrow> 'a::comm_semiring_1) *\<^sub>t (f2 *\<^sub>t f3) =\<^sub>P\<^sub>L (f1 *\<^sub>t f2) *\<^sub>t f3"
  by(simp add: hp_definitions pl_der_def mult.assoc)

lemma pl_times_distrib:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> 'a::comm_semiring_1) *\<^sub>t (n2 +\<^sub>t n3) =\<^sub>P\<^sub>L n1 *\<^sub>t n2  +\<^sub>t n1 *\<^sub>t n3"
  by(simp add: hp_definitions pl_der_def distrib_left)

lemma pl_funtimes_distrib:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'b \<Rightarrow> 'a::comm_semiring_1) *\<^sub>t (f2 +\<^sub>t f3) =\<^sub>P\<^sub>L f1 *\<^sub>t f2  +\<^sub>t f1 *\<^sub>t f3"
  by(simp add: hp_definitions pl_der_def distrib_left)

lemma pl_times_minusn_distrib:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 :: 'env \<Rightarrow> nat) *\<^sub>t (n2 -\<^sub>t n3) =\<^sub>P\<^sub>L n1 *\<^sub>t n2 -\<^sub>t n1 *\<^sub>t n3"
  by(simp add: hp_definitions pl_der_def diff_mult_distrib2)

lemma pl_funtimes_minusn_distrib:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'b \<Rightarrow> nat) *\<^sub>t (f2 -\<^sub>t f3) =\<^sub>P\<^sub>L f1 *\<^sub>t f2 -\<^sub>t f1 *\<^sub>t f3"
  by(simp add: hp_definitions pl_der_def diff_mult_distrib2)

lemma pl_div_real_def:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> real) /\<^sub>t r2 =\<^sub>P\<^sub>L r1 *\<^sub>t (hp_const 1 /\<^sub>t r2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_fundiv_real_def:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'a \<Rightarrow> real) /\<^sub>t f2 =\<^sub>P\<^sub>L f1 *\<^sub>t (hp_constf (hp_const 1) /\<^sub>t f2)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_div1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> real) /\<^sub>t (hp_const 1) =\<^sub>P\<^sub>L r1"
  by(simp add: hp_definitions pl_der_def)

lemma pl_fundiv1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'a \<Rightarrow> real) /\<^sub>t (hp_constf (hp_const 1)) =\<^sub>P\<^sub>L f1"
  by(simp add: hp_definitions pl_der_def)

lemma pl_div_times_div:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 /\<^sub>t (r3 :: 'env \<Rightarrow> real)) *\<^sub>t (r2 /\<^sub>t r4) =\<^sub>P\<^sub>L (r1 *\<^sub>t r2) /\<^sub>t (r3 *\<^sub>t r4)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_fundiv_times_div:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 /\<^sub>t (f3 :: 'env \<Rightarrow> 'a \<Rightarrow> real)) *\<^sub>t (f2 /\<^sub>t f4) =\<^sub>P\<^sub>L (f1 *\<^sub>t f2) /\<^sub>t (f3 *\<^sub>t f4)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_div_div:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const 0 <\<^sub>P\<^sub>L t \<longrightarrow>\<^sub>P\<^sub>L t /\<^sub>t t =\<^sub>P\<^sub>L hp_const (1 :: real)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_div_ennreal_0_div:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0 :: ennreal) /\<^sub>t r =\<^sub>P\<^sub>L hp_const 0"
  by(simp add: hp_definitions pl_der_def)

lemma pl_fundiv_ennreal_0_div:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_const (0 :: ennreal)) /\<^sub>t f =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_div_ennreal_div_top:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L r /\<^sub>t hp_const (\<infinity> :: ennreal) =\<^sub>P\<^sub>L hp_const 0"
  by(simp add: hp_definitions pl_der_def)

lemma pl_fundiv_ennreal_div_top:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L f /\<^sub>t hp_constf (hp_const (\<infinity> :: ennreal)) =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_times_div_ennreal:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> ennreal) *\<^sub>t (r2 /\<^sub>t r3) =\<^sub>P\<^sub>L (r1 *\<^sub>t r2) /\<^sub>t r3"
  by(simp add: hp_definitions pl_der_def ennreal_times_divide)

lemma pl_funtimes_div_ennreal:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'a \<Rightarrow> ennreal) *\<^sub>t (f2 /\<^sub>t f3) =\<^sub>P\<^sub>L (f1 *\<^sub>t f2) /\<^sub>t f3"
  by(simp add: hp_definitions pl_der_def ennreal_times_divide)

lemma pl_power1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t ^\<^sup>t 1 =\<^sub>P\<^sub>L t"
  by(simp add: hp_definitions pl_der_def)

lemma pl_power_square:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L t ^\<^sup>t 2 =\<^sub>P\<^sub>L t *\<^sub>t t"
  by(simp add: hp_definitions pl_der_def)

lemma pl_abs_plus:
   "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_lambda (f +\<^sub>t g) =\<^sub>P\<^sub>L hp_lambda f +\<^sub>t hp_lambda g"
  by(auto simp add: hp_definitions pl_der_def)

lemma pl_abs_minus:
   "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_lambda (f -\<^sub>t g) =\<^sub>P\<^sub>L hp_lambda f -\<^sub>t hp_lambda g"
  by(auto simp add: hp_definitions pl_der_def)

lemma pl_abs_times:
   "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_lambda (f *\<^sub>t g) =\<^sub>P\<^sub>L hp_lambda f *\<^sub>t hp_lambda g"
  by(auto simp add: hp_definitions pl_der_def)

lemma pl_abs_div:
   "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_lambda (f /\<^sub>t g) =\<^sub>P\<^sub>L hp_lambda f /\<^sub>t hp_lambda g"
  by(auto simp add: hp_definitions pl_der_def)


lemma pl_ennreal_noninfty:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<not>\<^sub>P\<^sub>L (hp_ennreal r =\<^sub>P\<^sub>L hp_const \<infinity>)"
  by(simp add: hp_definitions pl_der_def)

(* TODO: axioms for ordering *)
lemma pl_order_const:
  assumes "n1 < n2"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const n1 <\<^sub>P\<^sub>L hp_const n2"
  by(simp add: hp_definitions assms pl_der_def)

lemma pl_order_irrefl:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<not>\<^sub>P\<^sub>L ((t :: 'cont \<Rightarrow> ('a::order)) <\<^sub>P\<^sub>L t)"
  by(simp add: hp_definitions pl_der_def)

lemma pl_nzero_least:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0::nat) \<le>\<^sub>P\<^sub>L t"
  by(simp add: hp_definitions pl_der_def)

lemma pl_less_eq_def1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (e1::_ \<Rightarrow> (_::linorder)) \<le>\<^sub>P\<^sub>L e2 \<longrightarrow>\<^sub>P\<^sub>L e1 =\<^sub>P\<^sub>L e2 \<or>\<^sub>P\<^sub>L e1 <\<^sub>P\<^sub>L e2"
  by(auto simp add: hp_definitions pl_der_def)

lemma pl_nzero_orgt0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0::nat) =\<^sub>P\<^sub>L t \<or>\<^sub>P\<^sub>L  hp_const (0::nat) <\<^sub>P\<^sub>L t"
  apply(rule pl_impE[where \<psi>="hp_const (0::nat) \<le>\<^sub>P\<^sub>L t"])
   apply(rule pl_less_eq_def1)
  apply(rule pl_nzero_least)
  done

lemma pl_order_nat_real_const:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (n::nat) <\<^sub>P\<^sub>L e \<longrightarrow>\<^sub>P\<^sub>L hp_const (real n) <\<^sub>P\<^sub>L hp_real e"
  by(simp add: hp_definitions pl_der_def)

lemma pl_order_nat_real:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L n1 <\<^sub>P\<^sub>L n2 \<longrightarrow>\<^sub>P\<^sub>L hp_real n1 <\<^sub>P\<^sub>L hp_real n2"
  by(simp add: hp_definitions pl_der_def)

lemma pl_rorder_plust:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (e1::_ \<Rightarrow> real) <\<^sub>P\<^sub>L e2 \<and>\<^sub>P\<^sub>L hp_const 0 <\<^sub>P\<^sub>L t \<longrightarrow>\<^sub>P\<^sub>L e1 <\<^sub>P\<^sub>L e2 +\<^sub>t t"
  by(simp add: hp_definitions pl_der_def)


lemma pl_plus_right0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L n +\<^sub>t hp_const (0::'a::comm_monoid_add) =\<^sub>P\<^sub>L n"
  apply(rule pl_subst[OF _ pl_plus_com],simp add: hp_definitions)
  apply(rule pl_plus_left0)
  done

lemma pl_funplus_right0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L f +\<^sub>t hp_constf (hp_const (0::'a::comm_monoid_add)) =\<^sub>P\<^sub>L f"
  apply(rule pl_subst[OF _ pl_funplus_com],simp add: hp_definitions)
  apply(rule pl_funplus_left0)
  done

lemma pl_minusr_0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r :: 'env \<Rightarrow> real) -\<^sub>t r =\<^sub>P\<^sub>L hp_const 0"
  apply(rule pl_impE[OF pl_minusr_minus0])
  apply(rule pl_eq_refl)
  done

lemma pl_funminusr_0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r :: 'env \<Rightarrow> 'a \<Rightarrow> real) -\<^sub>t r =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  apply(rule pl_impE[OF pl_funminusr_minus0])
  apply(rule pl_eq_refl)
  done

lemma pl_times_right0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L n *\<^sub>t hp_const (0::'a::comm_semiring_1) =\<^sub>P\<^sub>L hp_const 0"
  apply(rule pl_subst[OF _ pl_times_com[of _ _ _ n]],simp add: hp_definitions)
  apply(rule pl_times_left0)
  done

lemma pl_funtimes_right0:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L f *\<^sub>t hp_constf (hp_const (0::'a::comm_semiring_1)) =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ f]],simp add: hp_definitions)
  apply(rule pl_funtimes_left0)
  done

lemma pl_times_right1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L n *\<^sub>t hp_const (1::'a::comm_semiring_1) =\<^sub>P\<^sub>L n"
  apply(rule pl_subst[OF _ pl_times_com[of _ _ _ n]],simp add: hp_definitions)
  apply(rule pl_times_left1)
  done

lemma pl_funtimes_right1:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L f *\<^sub>t hp_constf (hp_const (1::'a::comm_semiring_1)) =\<^sub>P\<^sub>L f"
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ f]],simp add: hp_definitions)
  apply(rule pl_funtimes_left1)
  done

lemma pl_times_distrib':
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (n1 +\<^sub>t n2) *\<^sub>t (n3 :: 'env \<Rightarrow> 'a::comm_semiring_1) =\<^sub>P\<^sub>L n1 *\<^sub>t n3 +\<^sub>t n2 *\<^sub>t n3"
  apply(rule pl_subst[OF _ pl_times_com[of _ _ n3 "n1 +\<^sub>t n2"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_distrib]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_com[of _ _ n1 n3]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_com[of _ _ n2 n3]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_funtimes_distrib':
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 +\<^sub>t f2) *\<^sub>t (f3 :: 'env \<Rightarrow> 'b \<Rightarrow> 'a::comm_semiring_1) =\<^sub>P\<^sub>L f1 *\<^sub>t f3  +\<^sub>t f2 *\<^sub>t f3"
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ f3 "f1 +\<^sub>t f2"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ f1 f3]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ f2 f3]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_plus_sq:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L ((n1:: 'env \<Rightarrow> 'a::comm_semiring_1) +\<^sub>t n2) *\<^sub>t (n1 +\<^sub>t n2) =\<^sub>P\<^sub>L n1 *\<^sub>t n1 +\<^sub>t n2 *\<^sub>t n2 +\<^sub>t hp_const 2 *\<^sub>t n1 *\<^sub>t n2"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_distrib]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_distrib']],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_distrib']],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_plus_assoc[of _ _ _ "n2 *\<^sub>t n1"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_assoc[of _ _ "n2 *\<^sub>t n1 "]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_com[of _ _ n1 n2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_left1[of _ _ "n1 *\<^sub>t n2"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_distrib'[of _ _ _ _ "(n1 *\<^sub>t n2)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_const]],simp add: hp_definitions,simp)
  apply(rule pl_subst[OF _ pl_times_assoc],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_plus_com[of _ _ "n2 *\<^sub>t n2" "hp_const 2 *\<^sub>t (n1 *\<^sub>t n2)"]],simp add: hp_definitions)
  apply(rule pl_plus_assoc)
  done

lemma pl_funplus_sq:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L ((f1:: 'env \<Rightarrow> 'b \<Rightarrow> 'a::comm_semiring_1) +\<^sub>t f2) *\<^sub>t (f1 +\<^sub>t f2) =\<^sub>P\<^sub>L f1 *\<^sub>t f1 +\<^sub>t f2 *\<^sub>t f2 +\<^sub>t hp_constf (hp_const 2) *\<^sub>t f1 *\<^sub>t f2"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib']],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib']],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funplus_assoc[of _ _ _ "f2 *\<^sub>t f1"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funplus_assoc[of _ _ "f2 *\<^sub>t f1 "]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ f1 f2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_left1[of _ _ "f1 *\<^sub>t f2"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_distrib'[of _ _ _ _ "(f1 *\<^sub>t f2)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_constf]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_const]],simp add: hp_definitions,simp)
  apply(rule pl_subst[OF _ pl_funtimes_assoc],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funplus_com[of _ _ "f2 *\<^sub>t f2" "hp_constf (hp_const 2) *\<^sub>t (f1 *\<^sub>t f2)"]],simp add: hp_definitions)
  apply(rule pl_funplus_assoc)
  done

lemma pl_div_real_0_div:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_const (0 :: real) /\<^sub>t r =\<^sub>P\<^sub>L hp_const 0"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_real_def[of _ _ "hp_const (0::real)"]]],simp add: hp_definitions)
  apply(rule pl_times_left0)
  done

lemma pl_fundiv_real_0_div:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_constf (hp_const (0 :: real)) /\<^sub>t f =\<^sub>P\<^sub>L hp_constf (hp_const 0)"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "hp_constf (hp_const (0::real))"]]],simp add: hp_definitions)
  apply(rule pl_funtimes_left0)
  done

lemma pl_div_plus_distr:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 +\<^sub>t r2) /\<^sub>t (r3 :: 'env \<Rightarrow> real) =\<^sub>P\<^sub>L r1 /\<^sub>t r3 +\<^sub>t r2 /\<^sub>t r3"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_real_def[of _ _ r1]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_real_def[of _ _ r2]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_real_def[of _ _ "r1 +\<^sub>t r2"]]],simp add: hp_definitions)
  apply(rule pl_times_distrib')
  done

lemma pl_fundiv_plus_distr:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 +\<^sub>t f2) /\<^sub>t (f3 :: 'env \<Rightarrow> 'a \<Rightarrow> real) =\<^sub>P\<^sub>L f1 /\<^sub>t f3 +\<^sub>t f2 /\<^sub>t f3"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ f1]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ f2]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "f1 +\<^sub>t f2"]]],simp add: hp_definitions)
  apply(rule pl_funtimes_distrib')
  done

lemma pl_div_timesr:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1  *\<^sub>t r2) /\<^sub>t (r3 :: 'env \<Rightarrow> real) =\<^sub>P\<^sub>L r1 *\<^sub>t (r2 /\<^sub>t r3)"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_real_def[of _ _ r2]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_assoc[of _ _ r1]]], simp add: hp_definitions)
  apply(rule pl_div_real_def)
  done

lemma pl_fundiv_timesr:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1  *\<^sub>t f2) /\<^sub>t (f3 :: 'env \<Rightarrow> 'a \<Rightarrow> real) =\<^sub>P\<^sub>L f1 *\<^sub>t (f2 /\<^sub>t f3)"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ f2]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc[of _ _ f1]]], simp add: hp_definitions)
  apply(rule pl_fundiv_real_def)
  done

lemma pl_div_times_div_swap:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 /\<^sub>t (r3 :: 'env \<Rightarrow> real)) *\<^sub>t (r2 /\<^sub>t r4) =\<^sub>P\<^sub>L (r1 /\<^sub>t r4) *\<^sub>t (r2 /\<^sub>t r3)"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_times_div[of _ _ r1 r3]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_com[of _ _ r4]],simp add: hp_definitions)
  apply(rule pl_eq_sym)
  apply(rule pl_div_times_div)
  done

lemma pl_fundiv_times_div_swap:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 /\<^sub>t (f3 :: 'env \<Rightarrow> 'a \<Rightarrow> real)) *\<^sub>t (f2 /\<^sub>t f4) =\<^sub>P\<^sub>L (f1 /\<^sub>t f4) *\<^sub>t (f2 /\<^sub>t f3)"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_times_div[of _ _ f1 f3]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ f4]],simp add: hp_definitions)
  apply(rule pl_eq_sym)
  apply(rule pl_fundiv_times_div)
  done

lemma pl_minusr_left:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> real) -\<^sub>t (r2 +\<^sub>t r3) =\<^sub>P\<^sub>L r1 -\<^sub>t r2 -\<^sub>t r3"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_minusr_plus_uminus[of _ _ r1 "r2 +\<^sub>t r3"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_uminus_times[where r="r2 +\<^sub>t r3"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_distrib[of _ _ "-\<^sub>t hp_const 1" r2 r3]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_uminus_times[where r="r2"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_uminus_times[where r="r3"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_assoc[of _ _ r1 "-\<^sub>t r2" "-\<^sub>t r3"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_minusr_plus_uminus[of _ _ r1 r2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_minusr_plus_uminus[of _ _ _ r3]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_funminusr_left:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> 'a \<Rightarrow> real) -\<^sub>t (r2 +\<^sub>t r3) =\<^sub>P\<^sub>L r1 -\<^sub>t r2 -\<^sub>t r3"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_plus_uminus[of _ _ r1 "r2 +\<^sub>t r3"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funuminus_times[where f="r2 +\<^sub>t r3"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib[of _ _ _ r2 r3]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funuminus_times[where f="r2"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funuminus_times[where f="r3"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funplus_assoc[of _ _ r1 "-\<^sub>t r2" "-\<^sub>t r3"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funminusr_plus_uminus[of _ _ r1 r2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funminusr_plus_uminus[of _ _ _ r3]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_minusr_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> real) -\<^sub>t r2 -\<^sub>t r3 =\<^sub>P\<^sub>L r1 -\<^sub>t r3 -\<^sub>t r2"
  apply(rule pl_subst[OF _ pl_minusr_left[of _ _ r1 r2 r3]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_minusr_left[of _ _ r1 r3 r2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_plus_com[of _ _ r3 r2]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_funminusr_com:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> 'a \<Rightarrow> real) -\<^sub>t r2 -\<^sub>t r3 =\<^sub>P\<^sub>L r1 -\<^sub>t r3 -\<^sub>t r2"
  apply(rule pl_subst[OF _ pl_funminusr_left[of _ _ r1 r2 r3]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funminusr_left[of _ _ r1 r3 r2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funplus_com[of _ _ r3 r2]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_minusr_assoc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> real) +\<^sub>t r2 -\<^sub>t r3 =\<^sub>P\<^sub>L r1 +\<^sub>t (r2 -\<^sub>t r3)"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_minusr_plus_uminus[of _ _ "r1 +\<^sub>t r2" r3]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_plus_assoc[of _ _ r1 r2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_minusr_plus_uminus[of _ _ "r2" r3]]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_funminusr_assoc:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> 'a \<Rightarrow> real) +\<^sub>t r2 -\<^sub>t r3 =\<^sub>P\<^sub>L r1 +\<^sub>t (r2 -\<^sub>t r3)"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_plus_uminus[of _ _ "r1 +\<^sub>t r2" r3]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funplus_assoc[of _ _ r1 r2]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_plus_uminus[of _ _ "r2" r3]]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_timesr_minus_distrib:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (r1 :: 'env \<Rightarrow> real) *\<^sub>t (r2 -\<^sub>t r3) =\<^sub>P\<^sub>L r1 *\<^sub>t r2  -\<^sub>t r1 *\<^sub>t r3"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_minusr_plus_uminus[of _ _ r2]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_minusr_plus_uminus[of _ _ "r1 *\<^sub>t r2"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_uminus_times]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_com[of _ _ _ "-\<^sub>t hp_const 1"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_assoc],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_com[of _ _ "-\<^sub>t hp_const 1"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_uminus_times],simp add: hp_definitions)
  apply(rule pl_times_distrib)
  done

lemma pl_funtimesr_minus_distrib:
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L (f1 :: 'env \<Rightarrow> 'a \<Rightarrow> real) *\<^sub>t (f2 -\<^sub>t f3) =\<^sub>P\<^sub>L f1 *\<^sub>t f2  -\<^sub>t f1 *\<^sub>t f3"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_plus_uminus[of _ _ f2]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_plus_uminus[of _ _ "f1 *\<^sub>t f2"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funuminus_times]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ "-\<^sub>t hp_constf (hp_const 1)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_assoc],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ "-\<^sub>t hp_constf (hp_const 1)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funuminus_times],simp add: hp_definitions)
  apply(rule pl_funtimes_distrib)
  done

lemma pl_var_affine':
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_var t (hp_constf a *\<^sub>t e +\<^sub>t hp_constf b) =\<^sub>P\<^sub>L a^\<^sup>t2 *\<^sub>t hp_var t e"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_var_eq[of _ _ t "hp_constf a *\<^sub>t e +\<^sub>t hp_constf b"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_add[OF pl_integrable_mult[OF assms,of a] pl_integrable_const[of _ _ _ b]]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_cmult[of _ _ t a e]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF hp_expect_const[where c="b"]]], simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_plus_constf[of \<Gamma> \<Psi> "a *\<^sub>t hp_expect t e" b]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_times_constf[of _ _ a "hp_expect t e"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_left[of _ _ "hp_constf a *\<^sub>t e +\<^sub>t hp_constf b" "hp_constf a *\<^sub>t hp_constf (hp_expect t e)" "hp_constf b"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funminusr_com],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_assoc]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funminusr_0]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funplus_right0]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimesr_minus_distrib],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ "hp_constf a"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _  "hp_constf a" "e -\<^sub>t hp_constf (hp_expect t e)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_assoc],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_cmult]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_var_eq],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_power_square],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done


lemma pl_var_cmult:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t e"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_var t (hp_constf a *\<^sub>t e) =\<^sub>P\<^sub>L a^\<^sup>t2 *\<^sub>t hp_var t e"
  apply(rule pl_subst[OF _  pl_funplus_right0[where f="hp_constf a *\<^sub>t e"]],simp add: hp_definitions)
  apply(rule pl_var_affine[OF assms])
  done

lemma pl_expect_indep_plus:
  assumes "e' = (\<lambda>t envxy. e (fst envxy) (t envxy))"
          "f' = (\<lambda>t envxy. f (fst envxy) (t envxy))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) (hp_lambda (e' (hp_fst var1)) +\<^sub>t hp_lambda (f' (hp_snd var1))) =\<^sub>P\<^sub>L hp_expect s e +\<^sub>t hp_expect t f"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_add[of _ _ _ "hp_lambda (e' (hp_fst var1))"]]],simp add: hp_definitions)
    apply(rule pl_integrable_indep1[OF assms(1)],fact)
   apply(rule pl_integrable_indep2[OF assms(2)],fact)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_fst[OF assms(1) assms(3)]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_snd[OF assms(2) assms(4)]]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

lemma pl_expect_indep_plus':
  assumes "e' = (\<lambda>t env xy. e env (t (env,xy)))"
          "f' = (\<lambda>t env xy. f env (t (env,xy)))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t f"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_expect (hp_pair_measure s t) (e' (hp_fst var1) +\<^sub>t f' (hp_snd var1)) =\<^sub>P\<^sub>L hp_expect s e +\<^sub>t hp_expect t f"
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_add[of _ _ _ "e' (hp_fst var1)"]]],simp add: hp_definitions)
    apply(rule pl_integrable_indep1'[OF assms(1)],fact)
   apply(rule pl_integrable_indep2'[OF assms(2)],fact)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_fst'[OF assms(1) assms(3)]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_snd'[OF assms(2) assms(4)]]],simp add: hp_definitions)
  apply(rule pl_eq_refl)
  done

(* TODO: prove the following lemmas with rules. *)
lemma pl_var_indep_plus:
  assumes "e' = (\<lambda>t envxy. e (fst envxy) (t envxy))"
          "f' = (\<lambda>t envxy. f (fst envxy) (t envxy))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s (e *\<^sub>t e)"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t f"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t (f *\<^sub>t f)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_var (hp_pair_measure s t) (hp_lambda (e' (hp_fst var1)) +\<^sub>t hp_lambda (f' (hp_snd var1))) =\<^sub>P\<^sub>L hp_var s e +\<^sub>t hp_var t f"
  using qbs_prob_var_indep_plus' assms(3-6)
  by(simp add: assms(1,2) hp_definitions pl_der_def monoid_mult_class.power2_eq_square,blast)

lemma pl_var_indep_plus':
  assumes "e' = (\<lambda>t env xy. e env (t (env,xy)))"
          "f' = (\<lambda>t env xy. f env (t (env,xy)))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s e"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable s (e *\<^sub>t e)"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t f"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable t (f *\<^sub>t f)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_var (hp_pair_measure s t) (e' (hp_fst var1) +\<^sub>t f' (hp_snd var1)) =\<^sub>P\<^sub>L hp_var s e +\<^sub>t hp_var t f"
  using qbs_prob_var_indep_plus' assms(3-6)
  by(simp add: assms(1,2) hp_definitions pl_der_def monoid_mult_class.power2_eq_square,blast)

lemma pl_var_bind:
  assumes "\<Gamma> \<turnstile>\<^sub>t e ;; monadP_qbs Y"
          "\<Gamma>,,Y \<turnstile>\<^sub>t e' ;; Z"
      and "\<Gamma> \<turnstile>\<^sub>t e'' ;; exp_qbs Z \<real>\<^sub>Q"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_var (hp_bind e (hp_lambda (hp_return Z e'))) e'' =\<^sub>P\<^sub>L hp_var e (hp_comp e'' (hp_lambda e'))"
proof(auto simp add: hp_definitions hp_comp_def curry_def pl_der_def)
  fix x
  assume "x \<in> qbs_space \<Gamma>"
  then show "qbs_prob_var (e x \<bind> (\<lambda>y. qbs_return Z (e' (x, y)))) (e'' x) =
         qbs_prob_var (e x) (\<lambda>y. e'' x (e' (x, y)))"
    using qbs_prob_var_bind_return[of "e x" Y "e'' x" Z "curry e' x"] assms curry_preserves_morphisms[of e' \<Gamma> Y Z] qbs_morphismE(1)[of e'' \<Gamma> "exp_qbs Z \<real>\<^sub>Q"] qbs_morphismE(1)[of "curry e'" \<Gamma> "exp_qbs Y Z"] qbs_morphismE(1)[of e \<Gamma> "monadP_qbs Y"]
    by(fastforce simp: hpprog_typing_def hpprog_context_def curry_def comp_def monadP_qbs_Px_def)
qed

end