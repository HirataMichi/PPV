(*  Title:   MonteCarlol.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology

*)

subsection \<open> MonteCarlo Approximation \<close>

theory MonteCarlo
  imports "UPL"
begin


text \<open> We write the program as an Isabelle/HOL term. \<close>
fun montecarlo :: "'a qbs_prob_space \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real qbs_prob_space" where
"montecarlo _ _ 0           = qbs_return \<real>\<^sub>Q 0" |
"montecarlo d h (Suc n) = montecarlo d h n \<bind>
                                (\<lambda>m::real. d \<bind>
                                    (\<lambda>x::'a. qbs_return \<real>\<^sub>Q ((h x + m* (real n)) / (real (Suc n)))))"

text \<open> We write the program as an HPProg term. \<close>
definition hp_montecarlo ::
   "('b \<times> 'a qbs_prob_space) \<times> ('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real qbs_prob_space" where
"hp_montecarlo \<equiv>
 hp_rec_nat (hp_return \<real>\<^sub>Q (hp_const 0))
    (\<lambda>\<^sub>t (\<lambda>\<^sub>t (var1 \<bind>\<^sub>t
            \<lambda>\<^sub>t (var5 \<bind>\<^sub>t
                 \<lambda>\<^sub>t (hp_return \<real>\<^sub>Q
                       (((var5 $\<^sub>t var1) +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4)))))))"

text \<open> Check that  @{term hp_montecarlo} is correct because its definition is complicated. \<close>
lemma montecarlo_equal:
  "montecarlo d h = hp_montecarlo (((),d),h)"
  apply standard
  subgoal for n
    apply(induction n; simp add: hp_definitions curry_def hp_montecarlo_def)
    done
  done

text \<open> We define the following terms. \<close>
(*  If
    \<Gamma> \<turnstile> hp_montecarlo ;; \<nat>\<^sub>Q \<Rightarrow>\<^sub>Q P\<^sub>t \<real>\<^sub>Q
    then
    \<Gamma>,, X    \<turnstile> hp_montecarlo'  ;; \<nat>\<^sub>Q \<Rightarrow>\<^sub>Q P\<^sub>t \<real>\<^sub>Q
    \<Gamma>,, X,,Y \<turnstile> hp_montecarlo'' ;; \<nat>\<^sub>Q \<Rightarrow>\<^sub>Q P\<^sub>t \<real>\<^sub>Q. *)
definition "hp_montecarlo' = (\<lambda>(env,_). hp_montecarlo env)"
definition "hp_montecarlo'' = (\<lambda>((env,_),_). hp_montecarlo env)"

lemma hp_montecarlo'_def2:
 "hp_montecarlo' = hp_rec_nat (hp_return \<real>\<^sub>Q (hp_const 0))
                      (hp_lambda (hp_lambda (hp_bind var1
                                           (hp_lambda (hp_bind var6 
                                                               (hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var6 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4)))))))))"
  by(simp add: hp_montecarlo'_def hp_montecarlo_def split_beta' hp_definitions curry_def)

lemma pl_montecarlo'_def:
  "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L hp_montecarlo' =\<^sub>P\<^sub>L hp_rec_nat (hp_return \<real>\<^sub>Q (hp_const 0))
                      (hp_lambda (hp_lambda (hp_bind var1
                                           (hp_lambda (hp_bind var6 
                                                               (hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var6 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4)))))))))"
  by(simp add: pl_der_def hp_montecarlo'_def2 hp_eq_def)

lemma montecarlo_typing':
 "\<Gamma>,,monadP_qbs X,,exp_qbs X \<real>\<^sub>Q \<turnstile>\<^sub>t hp_montecarlo ;; exp_qbs \<nat>\<^sub>Q (monadP_qbs \<real>\<^sub>Q)"
  unfolding hp_montecarlo_def
  apply(rule hpt_recnat)
   apply(rule hpt_return)
   apply(rule hpt_realc)
  apply(rule hpt_abs)
  apply(rule hpt_abs)
  apply(rule hpt_bind)
  apply(rule hpt_var1)
   apply(rule hpt_abs)
   apply(rule hpt_bind)
   apply(rule hpt_var5)
  apply(rule hpt_abs)
  apply(rule hpt_return)
  apply(rule hpt_divr)
   apply(rule hpt_plusr)
    apply(rule hpt_app)
     apply(rule hpt_var5)
    apply(rule hpt_var1)
   apply(rule hpt_timesr)
    apply(rule hpt_var2)
   apply(rule hpt_real)
   apply(rule hpt_var4)
  apply(rule hpt_real)
  apply(rule hpt_suc)
  apply(rule hpt_var4)
  done

lemma montecarlo'_typing:
 ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q ,, Y \<turnstile>\<^sub>t hp_montecarlo' ;; exp_qbs \<nat>\<^sub>Q (monadP_qbs \<real>\<^sub>Q)"
  unfolding hp_montecarlo'_def2
  apply(rule hpt_recnat)
   apply(rule hpt_return)
   apply(rule hpt_realc)
  apply(rule hpt_abs)
  apply(rule hpt_abs)
  apply(rule hpt_bind)
  apply(rule hpt_var1)
   apply(rule hpt_abs)
   apply(rule hpt_bind)
   apply(rule hpt_var6)
  apply(rule hpt_abs)
  apply(rule hpt_return)
  apply(rule hpt_divr)
   apply(rule hpt_plusr)
    apply(rule hpt_app)
     apply(rule hpt_var6)
    apply(rule hpt_var1)
   apply(rule hpt_timesr)
    apply(rule hpt_var2)
   apply(rule hpt_real)
   apply(rule hpt_var4)
  apply(rule hpt_real)
  apply(rule hpt_suc)
  apply(rule hpt_var4)
  done

definition "\<Phi>mon \<equiv> {hp_const 0 <\<^sub>P\<^sub>L var5, var4 =\<^sub>P\<^sub>L hp_expect var2 var1, var3^\<^sup>t2 =\<^sub>P\<^sub>L hp_var var2 var1,
                      hp_integrable var2 var1, hp_integrable var2 (var1 *\<^sub>t var1)}" 

lemma montecarlo_integrable:
",\<real>\<^sub>Q,,\<real>\<^sub>Q,,\<real>\<^sub>Q,,P\<^sub>t X,,(X \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) | \<Phi>mon
      \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>L n \<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_montecarlo $\<^sub>t hp_const n) hp_id
                   \<and>\<^sub>P\<^sub>L hp_integrable (hp_montecarlo $\<^sub>t hp_const n) (hp_id *\<^sub>t hp_id)"
  apply(rule pl_nat[of "{hp_const 0 <\<^sub>P\<^sub>L var6, var5 =\<^sub>P\<^sub>L hp_expect var3 var2, var4^\<^sup>t2 =\<^sub>P\<^sub>L hp_var var3 var2, hp_integrable var3 var2, hp_integrable var3 (var2 *\<^sub>t var2)}" _ "\<lambda>t. hp_integrable (hp_app hp_montecarlo' t) hp_id \<and>\<^sub>P\<^sub>L hp_integrable (hp_app hp_montecarlo' t) (hp_id *\<^sub>t hp_id)"],simp add: \<Phi>mon_def split_beta' hp_definitions,simp add: hp_montecarlo'_def split_beta' hp_definitions id_def)
(* base case *)
   apply(unfold  hp_montecarlo_def)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_rec_nat_0]],simp add: hp_definitions)
   apply(rule pl_andI)
    apply(rule pl_integrable_return,rule hpt_id,rule hpt_realc)
   apply(rule pl_integrable_return,rule hpt_funtimesr,rule hpt_id,rule hpt_id,rule hpt_realc)
(* induction case *)
    (* calculation *)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_montecarlo'_def]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_rec_nat_suc]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_montecarlo'_def],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_beta[of "(hp_lambda (var1 \<bind> hp_lambda (var5 \<bind> hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var5 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4))))))"
                                                     "hp_lambda (hp_bind var1 (hp_lambda (hp_bind var6 (hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var6 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4)))))))" var1]]],simp add: hp_definitions,simp add: hp_definitions curry_def)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_beta[of "(hp_bind (hp_app hp_montecarlo' var1) (hp_lambda (hp_bind var4 (hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var4 var1 +\<^sub>t var2 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)))))))" "(hp_bind var1 (hp_lambda (hp_bind var5 (hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var5 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4)))))))" "hp_app hp_montecarlo' var1"]]],simp add: hp_definitions,simp add: hp_definitions curry_def)
     (* bind transformation *)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_pair_bind_return2[of var4 var3 _ "hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var3 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var2) /\<^sub>t hp_real (hp_suc var2)))"]]],simp add: hp_definitions,simp add: hp_definitions ,simp add :hp_definitions)
     apply(rule hpt_app, rule montecarlo'_typing,rule hpt_var1,rule hpt_var3,rule hpt_abs,rule hpt_return,rule hpt_divr,rule hpt_plusr,rule hpt_app,rule hpt_var3,rule hpt_snd,rule hpt_var1,rule hpt_timesr,rule hpt_fst,rule hpt_var1,rule hpt_real,rule hpt_var2,rule hpt_real,rule hpt_suc,rule hpt_var2)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_pair_measure_bind_return[where m="hp_app hp_montecarlo' var1" and n=var3]]],simp add: hp_definitions,simp add: hp_definitions,rule hpt_app,rule montecarlo'_typing,rule hpt_var1,rule hpt_var3)

  apply(rule pl_andI)
 (* two cases *)
  (* hp_id *) 
   apply(rule pl_impE[OF pl_integrable_bind_return'[of _ "hp_pair_measure (hp_app hp_montecarlo' var1) var3"]],rule hpt_pair_measure,rule hpt_app,rule montecarlo'_typing,rule hpt_var1,rule hpt_var3,rule hpt_divr,rule hpt_plusr,rule hpt_app,rule hpt_var3,rule hpt_snd,rule hpt_var1,rule hpt_timesr,rule hpt_fst,rule hpt_var1,rule hpt_real,rule hpt_var2,rule hpt_real,rule hpt_suc,rule hpt_var2,rule hpt_id)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_comp_id_left]],simp add: hp_definitions)


   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var3 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var2"]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_plus[where f="hp_app var3 (hp_snd var1)"]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_funplus_com[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var2)"]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "(hp_lambda (hp_fst var1 *\<^sub>t hp_real var2) +\<^sub>t hp_lambda (hp_app var3 (hp_snd var1)))"]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib'[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var2)"]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _  pl_fundiv_real_def[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var2)"]],simp add: hp_definitions)
   apply(rule pl_subst[OF _  pl_fundiv_real_def[of _ _ "hp_lambda (hp_app var3 (hp_snd var1))"]],simp add: hp_definitions)
   apply(rule pl_subst[OF _  pl_abs_div[of _ _ "hp_fst var1 *\<^sub>t hp_real var2"]],simp add: hp_definitions)
   apply(rule pl_subst[OF _  pl_abs_div[of _ _ "hp_app var3 (hp_snd var1)"]],simp add: hp_definitions)
   apply(rule pl_integrable_add)
    apply(rule pl_integrable_indep1[of _ "hp_lambda (var1 *\<^sub>t hp_real var2 /\<^sub>t hp_real (hp_suc var2))"],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="var1 *\<^sub>t hp_real var2" and g="hp_real (hp_suc var2)"]]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_times[where f=var1 and g="hp_real var2"]]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "hp_lambda var1 *\<^sub>t hp_lambda (hp_real var2)" "hp_lambda (hp_real (hp_suc var2))"]]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_hp_id],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var2)" "hp_real (hp_suc var1)"]]],simp add: hp_definitions,simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real var2" "hp_real var1"]]],simp add: hp_definitions,simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var1)"]]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ hp_id "hp_constf (hp_real var1)"]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ hp_id]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf[of _ _ "hp_real var1"]]],simp add: hp_definitions)
    apply(rule pl_integrable_mult)
    apply(rule pl_andEl[where \<psi>="hp_integrable (hp_app hp_montecarlo' var1) (hp_id *\<^sub>t hp_id)"])
    apply(rule pl_ax,simp)
   apply(rule pl_integrable_indep2[of _ "hp_lambda (hp_app var3 var1 /\<^sub>t hp_real (hp_suc var2))"],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var3 var1" and g="hp_real (hp_suc var2)"]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var2)" "hp_real (hp_suc var1)"]]],simp add: hp_definitions,simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_eta[of var3 var2]]],simp add: hp_definitions,simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ var2]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var1)"]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ var2]],simp add: hp_definitions)
   apply(rule pl_integrable_mult)
   apply(rule pl_ax,simp)
  (* hp_id^2 *)
  apply(rule pl_impE[OF pl_integrable_bind_return'[of _ "hp_pair_measure (hp_app hp_montecarlo' var1) var3"]],rule hpt_pair_measure,rule hpt_app,rule montecarlo'_typing,rule hpt_var1,rule hpt_var3,rule hpt_divr,rule hpt_plusr,rule hpt_app,rule hpt_var3,rule hpt_snd,rule hpt_var1,rule hpt_timesr,rule hpt_fst,rule hpt_var1,rule hpt_real,rule hpt_var2,rule hpt_real,rule hpt_suc,rule hpt_var2,rule hpt_funtimesr,rule hpt_id,rule hpt_id)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_comp_id_sq_left]],simp add: hp_definitions)

  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var3 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var2"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_plus[where f="hp_app var3 (hp_snd var1)"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funplus_com[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var2)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "(hp_lambda (hp_fst var1 *\<^sub>t hp_real var2) +\<^sub>t hp_lambda (hp_app var3 (hp_snd var1)))"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib'[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var2)"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_fundiv_real_def[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var2)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_fundiv_real_def[of _ _ "hp_lambda (hp_app var3 (hp_snd var1))"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_abs_div[of _ _ "hp_fst var1 *\<^sub>t hp_real var2"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_abs_div[of _ _ "hp_app var3 (hp_snd var1)"]],simp add: hp_definitions)

  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_fst var1 *\<^sub>t hp_real var2" and g="hp_real (hp_suc var2)"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_times[where f="hp_fst var1" and g="hp_real var2"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "hp_lambda (hp_fst var1) *\<^sub>t hp_lambda (hp_real var2)" "hp_lambda (hp_real (hp_suc var2))"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var2)" "hp_real (hp_suc var1)"]]],simp add: hp_definitions,simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real var2" "hp_real var1"]]],simp add: hp_definitions,simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var1)"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ _ "hp_constf (hp_real var1)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ "hp_lambda (hp_fst var1)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf[of _ _ "hp_real var1"]]],simp add: hp_definitions)

  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var3 (hp_snd var1)" and g="hp_real (hp_suc var2)"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var2)" "hp_real (hp_suc var1)"]]],simp add: hp_definitions,simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "hp_lambda (hp_app var3 (hp_snd var1))"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var1)"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ "hp_lambda (hp_app var3 (hp_snd var1))"]],simp add: hp_definitions)

  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funplus_sq]],simp add: hp_definitions)

  (* 3 cases *)
  apply(rule pl_integrable_add)
   apply(rule pl_integrable_add)
    (* 1st *)
    apply(rule pl_subst[OF _ pl_funtimes_assoc],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc[of _ _ "hp_lambda (hp_fst var1)"]]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ "hp_lambda (hp_fst var1)"]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ "hp_constf (hp_real var1 *\<^sub>t (hp_const 1 /\<^sub>t hp_real (hp_suc var1)))"]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf]],simp add: hp_definitions)
    apply(rule pl_integrable_mult)
    apply(rule pl_subst[OF _ pl_abs_times],simp add: hp_definitions)
    apply(rule pl_integrable_indep1[of _ "hp_lambda (var1 *\<^sub>t var1)"],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_times]],simp add: hp_definitions)
    apply(rule pl_subst[OF _ pl_hp_id],simp add: hp_definitions)
    apply(rule pl_andEr[where \<phi>="hp_integrable (hp_app hp_montecarlo' var1) hp_id"])
    apply(rule pl_ax,simp)
   (* 2nd *)
   apply(rule pl_subst[OF _ pl_funtimes_assoc],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc[of _ _ "hp_lambda (hp_app var3 (hp_snd var1))"]]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ "hp_lambda (hp_app var3 (hp_snd var1))"]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ "hp_constf (hp_const 1 /\<^sub>t hp_real (hp_suc var1))"]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf]],simp add: hp_definitions)
   apply(rule pl_integrable_mult)
   apply(rule pl_subst[OF _ pl_abs_times],simp add: hp_definitions)
   apply(rule pl_integrable_indep2[of _ "hp_lambda (hp_app var3 var1 *\<^sub>t hp_app var3 var1)"],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_times]],simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_eq_sym[OF pl_eta[of _ var2]]],simp add: hp_definitions,simp add: hp_definitions)
   apply(rule pl_ax,simp)
   (* 3rd *)
  apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ "hp_constf (hp_const 2)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_assoc],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc[of _ _ "hp_lambda (hp_fst var1)"]]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ "hp_lambda (hp_fst var1)"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ "hp_constf (hp_const 1 /\<^sub>t hp_real (hp_suc var1))"]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf]],simp add: hp_definitions)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf]],simp add: hp_definitions)
  apply(rule pl_integrable_mult)

  apply(rule pl_integrable_indep_mult[of _ "hp_lambda var1" _ "hp_lambda (hp_app var3 var1)"],simp add: hp_definitions,simp add: hp_definitions)
   apply(rule pl_subst[OF _ pl_hp_id],simp add: hp_definitions)
   apply(rule pl_andEl[where \<psi>="hp_integrable (hp_app hp_montecarlo' var1) (hp_id *\<^sub>t hp_id)"])
   apply(rule pl_ax,simp)
  apply(rule pl_subst[OF _ pl_eq_sym[OF pl_eta[of _ var2]]],simp add: hp_definitions,simp add: hp_definitions)
  apply(rule pl_ax,simp)
  done

lemma montecarlo_integrable':
 ",\<real>\<^sub>Q,,\<real>\<^sub>Q,,\<real>\<^sub>Q,,monadP_qbs X,,exp_qbs X \<real>\<^sub>Q | \<Phi>mon \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>L n \<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo (hp_const n)) hp_id"
  apply(rule pl_allI[where \<phi>=" hp_integrable (hp_app hp_montecarlo' var1) hp_id"],simp,simp add: hp_definitions hp_montecarlo'_def id_def)
  apply(rule pl_andEl[where \<psi>="hp_integrable (hp_app hp_montecarlo' var1) (hp_id *\<^sub>t hp_id)"])
  apply(rule pl_allE[where \<phi>="\<lambda>t. hp_integrable (hp_app hp_montecarlo' t) hp_id \<and>\<^sub>P\<^sub>L hp_integrable (hp_app hp_montecarlo' t) (hp_id *\<^sub>t hp_id)"],simp add: hp_definitions,rule hpt_var1)
  apply(rule pl_contweakening[where \<phi>="\<forall>\<^sub>P\<^sub>L n \<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo (hp_const n)) hp_id \<and>\<^sub>P\<^sub>L hp_integrable (hp_app hp_montecarlo (hp_const n)) (hp_id *\<^sub>t hp_id)"],simp add: hp_montecarlo'_def split_beta' hp_definitions,simp)
  apply(rule montecarlo_integrable)
  done

lemma montecarlo_integrable2':
 ",\<real>\<^sub>Q,,\<real>\<^sub>Q,,\<real>\<^sub>Q,,monadP_qbs X,,exp_qbs X \<real>\<^sub>Q | \<Phi>mon \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>L n \<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo (hp_const n)) (hp_id *\<^sub>t hp_id)"
  apply(rule pl_allI[where \<phi>=" hp_integrable (hp_app hp_montecarlo' var1) (hp_id *\<^sub>t hp_id)"],simp,simp add: hp_definitions hp_montecarlo'_def id_def)
  apply(rule pl_andEr[where \<phi>="hp_integrable (hp_app hp_montecarlo' var1) hp_id"])
  apply(rule pl_allE[where \<phi>="\<lambda>t. hp_integrable (hp_app hp_montecarlo' t) hp_id \<and>\<^sub>P\<^sub>L hp_integrable (hp_app hp_montecarlo' t) (hp_id *\<^sub>t hp_id)"],simp add: hp_definitions,rule hpt_var1)
  apply(rule pl_contweakening[where \<phi>="\<forall>\<^sub>P\<^sub>L n \<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo (hp_const n)) hp_id \<and>\<^sub>P\<^sub>L hp_integrable (hp_app hp_montecarlo (hp_const n)) (hp_id *\<^sub>t hp_id)"],simp add: hp_montecarlo'_def split_beta' hp_definitions,simp)
  apply(rule montecarlo_integrable)
  done

(* var5 = \<epsilon>, var4 = expectation, var3 = variance, var2= d, var1 = h *)
lemma montecarlo_judgement:
 ",\<real>\<^sub>Q,,\<real>\<^sub>Q,,\<real>\<^sub>Q,,P\<^sub>t X,,(X \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) | \<Phi>mon
    \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_montecarlo ;; \<nat>\<^sub>Q \<Rightarrow>\<^sub>Q P\<^sub>t \<real>\<^sub>Q 
         | \<lambda>r. \<forall>\<^sub>P\<^sub>L n \<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n
                      \<longrightarrow>\<^sub>P\<^sub>L hp_prob (r $\<^sub>t hp_const n) {y. var5 \<le>\<^sub>P\<^sub>L \<bar>hp_const y -\<^sub>t var4\<bar>\<^sub>t}\<^sub>t
                            \<le>\<^sub>P\<^sub>L (var3^\<^sup>t2 /\<^sub>t hp_real (hp_const n)) *\<^sub>t (hp_const 1 /\<^sub>tvar5^\<^sup>t2)"
proof(rule upl_sub[where \<phi>="\<lambda>r. \<forall>\<^sub>P\<^sub>L n \<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n  \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app r (hp_const n)) hp_id =\<^sub>P\<^sub>L var4 \<and>\<^sub>P\<^sub>L hp_var (hp_app r (hp_const n)) hp_id =\<^sub>P\<^sub>L var3^\<^sup>t2 /\<^sub>t (hp_real (hp_const n))"],simp add: hp_definitions')
  show ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q | \<Phi>mon \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_montecarlo ;; exp_qbs \<nat>\<^sub>Q (monadP_qbs \<real>\<^sub>Q) |
               \<lambda>r. \<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app r (hp_const n)) hp_id =\<^sub>P\<^sub>L var4 \<and>\<^sub>P\<^sub>L
                                                             hp_var (hp_app r (hp_const n)) hp_id =\<^sub>P\<^sub>L var3 ^\<^sup>t 2 /\<^sub>t hp_real (hp_const n)"
    unfolding hp_montecarlo_def 

  proof(rule upl_recnat'[of "{hp_const (0::nat) <\<^sub>P\<^sub>L hp_const 0}" "{hp_const 0 <\<^sub>P\<^sub>L var1}" "{hp_const 0 <\<^sub>P\<^sub>L hp_suc var2}" "\<lambda>t. hp_const 0 <\<^sub>P\<^sub>L t" "{hp_const 0 <\<^sub>P\<^sub>L var7, var6 =\<^sub>P\<^sub>L hp_expect var4 var3, var5^\<^sup>t2 =\<^sub>P\<^sub>L hp_var var4 var3, hp_integrable var4 var3, hp_integrable var4 (var3 *\<^sub>t var3)}" _ "\<lambda>t r. hp_expect r hp_id =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var r hp_id =\<^sub>P\<^sub>L var5^\<^sup>t2 /\<^sub>t (hp_real t)" _ "{hp_const 0 <\<^sub>P\<^sub>L var2 \<longrightarrow>\<^sub>P\<^sub>L hp_expect var1 hp_id =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var var1 hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real var2}" "hp_montecarlo''" _ _ ",\<real>\<^sub>Q,,\<real>\<^sub>Q,,\<real>\<^sub>Q,,monadP_qbs X,,exp_qbs X \<real>\<^sub>Q" "monadP_qbs \<real>\<^sub>Q"],simp add: hp_definitions,simp add: hp_definitions split_beta',simp add: hp_definitions hp_conjall_def hp_conjall_fix_def,simp add: hp_definitions \<Phi>mon_def split_beta',simp add: hp_definitions id_def,simp add: hp_definitions hp_conjall_def split_beta' id_def,force simp add:hp_definitions,simp add: hp_montecarlo_def hp_montecarlo''_def split_beta')
    (* base case *)
    show ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q | \<Phi>mon \<union> {hp_const (0::nat) <\<^sub>P\<^sub>L hp_const 0} \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_return \<real>\<^sub>Q (hp_const 0) ;; monadP_qbs \<real>\<^sub>Q | 
            \<lambda>r. hp_expect r hp_id =\<^sub>P\<^sub>L var4 \<and>\<^sub>P\<^sub>L hp_var r hp_id =\<^sub>P\<^sub>L var3 ^\<^sup>t 2 /\<^sub>t hp_real (hp_const 0)"
      apply(rule upl_return,simp add: hp_definitions)
      apply(rule upl_const[OF _ hpt_realc],simp add: hp_definitions)
      apply(rule pl_botE)
      apply(rule pl_negE[where \<phi>="hp_const 0 <\<^sub>P\<^sub>L hp_const (0::nat)"])
       apply(rule pl_order_irrefl)
      apply(rule pl_ax,simp)
      done
  next
   (*induction step *)
    have hpl:",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q ,, \<nat>\<^sub>Q ,, monadP_qbs \<real>\<^sub>Q
        | {hp_const 0 <\<^sub>P\<^sub>L var7, var6 =\<^sub>P\<^sub>L hp_expect var4 var3, var5 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var4 var3, hp_integrable var4 var3, hp_integrable var4 (var3 *\<^sub>t var3)} \<union> {hp_const 0 <\<^sub>P\<^sub>L hp_suc var2} \<union> {hp_const 0 <\<^sub>P\<^sub>L var2 \<longrightarrow>\<^sub>P\<^sub>L hp_expect var1 hp_id =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var var1 hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real var2} \<union> {var1 =\<^sub>P\<^sub>L hp_app hp_montecarlo'' var2}
       \<turnstile>\<^sub>P\<^sub>L hp_expect (var1 \<bind> hp_lambda (var5 \<bind>
                                             hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var5 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4))))) hp_id =\<^sub>P\<^sub>L var6
       \<and>\<^sub>P\<^sub>L hp_var    (var1 \<bind> hp_lambda (var5 \<bind>
                                             hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var5 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4))))) hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real (hp_suc var2)"
       (* main part 
        substitution *)
           (* bind to bind return *)
       apply(rule pl_subst[of "\<lambda>t. hp_expect t hp_id =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var t hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real (hp_suc var2)" _ ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q ,, \<nat>\<^sub>Q ,, monadP_qbs \<real>\<^sub>Q" _ "hp_bind (hp_bind var1 (hp_lambda (hp_bind var5 (hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1)))))) (hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3))))"],simp add: hp_definitions)
        apply(rule pl_eq_sym)
        apply(rule pl_pair_bind_return2[of var5 var4 "\<lambda>v2 v1. hp_return \<real>\<^sub>Q ((hp_app var5 v1 +\<^sub>t v2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4))" "hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var4 (hp_snd var1) +\<^sub>t (hp_fst var1) *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)))" ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q ,, \<nat>\<^sub>Q ,, monadP_qbs \<real>\<^sub>Q" var1 "\<real>\<^sub>Q" X "\<real>\<^sub>Q"],simp add: var5_def var4_def comp_def,simp add: hp_definitions)
          apply(rule hpt_var1,rule hpt_var4,rule hpt_abs,rule hpt_return,rule hpt_divr,rule hpt_plusr,rule hpt_app[where X=X],rule hpt_var4,rule hpt_snd,rule hpt_var1,rule hpt_timesr,rule hpt_fst,rule hpt_var1,rule hpt_real,rule hpt_var3,rule hpt_real,rule hpt_suc,rule hpt_var3)


       apply(rule pl_subst[of "\<lambda>t. t =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var (var1 \<bind> hp_lambda (var5 \<bind> hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1))) \<bind> hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)))) hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real (hp_suc var2)" _ _ _ "hp_expect (var1 \<bind> hp_lambda (var5 \<bind> hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1)))) (hp_lambda((hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)))" "hp_expect (var1 \<bind> hp_lambda (var5 \<bind> hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1))) \<bind>  hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)))) hp_id"],simp add: hp_definitions)
        apply(rule pl_eq_sym)
        apply(rule pl_expect_bind[of ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q ,, \<nat>\<^sub>Q ,, monadP_qbs \<real>\<^sub>Q" "hp_bind var1 (hp_lambda (var5 \<bind> hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1))))" "\<real>\<^sub>Q \<Otimes>\<^sub>Q X" "(hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)" "\<real>\<^sub>Q" hp_id,simplified comp_id])
          apply(rule hpt_bind,rule hpt_var1,rule hpt_abs,rule hpt_bind,rule hpt_var5,rule hpt_abs,rule hpt_return,rule hpt_pair,rule hpt_var2,rule hpt_var1)
         apply(rule hpt_divr,rule hpt_plusr,rule hpt_app,rule hpt_var4,rule hpt_snd,rule hpt_var1,rule hpt_timesr,rule hpt_fst,rule hpt_var1,rule hpt_real,rule hpt_var3,rule hpt_real,rule hpt_suc,rule hpt_var3,rule hpt_id)


      apply(rule pl_subst[of _ _ _ _ "hp_var (hp_bind var1 (hp_lambda (hp_bind var5 (hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1)))))) (hp_lambda ((hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)))" "hp_var (var1 \<bind> hp_lambda (var5 \<bind> hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1))) \<bind> hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3)))) hp_id"],simp add: hp_definitions)
        apply(rule pl_eq_sym)

       apply(rule pl_subst[OF _  pl_eq_sym[OF pl_var_bind[of _ "hp_bind var1 (hp_lambda (hp_bind var5 (hp_lambda (hp_return (\<real>\<^sub>Q \<Otimes>\<^sub>Q X) (hp_pair var2 var1)))))" "(\<real>\<^sub>Q \<Otimes>\<^sub>Q X)" "((hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3) /\<^sub>t hp_real (hp_suc var3))" "\<real>\<^sub>Q" hp_id]]],simp add: hp_definitions)
          apply(rule hpt_bind,rule hpt_var1,rule hpt_abs,rule hpt_bind,rule hpt_var5,rule hpt_abs,rule hpt_return,rule hpt_pair,rule hpt_var2,rule hpt_var1)
         apply(rule hpt_divr,rule hpt_plusr,rule hpt_app,rule hpt_var4,rule hpt_snd,rule hpt_var1,rule hpt_timesr,rule hpt_fst,rule hpt_var1,rule hpt_real,rule hpt_var3,rule hpt_real,rule hpt_suc,rule hpt_var3,rule hpt_id,simp only: comp_id,rule pl_eq_refl)

       apply(rule pl_subst[OF _ pl_eq_sym[OF pl_pair_measure_bind_return[of _ var4]]],simp add: hp_definitions,simp add: hp_definitions,rule hpt_var1,rule hpt_var4)

       (* numerical transformation *)
       apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var4 (hp_snd var1) +\<^sub>t hp_fst var1 *\<^sub>t hp_real var3"]]],simp add: hp_definitions)
       apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_plus[where f="hp_app var4 (hp_snd var1)"]]],simp add: hp_definitions)
       apply(rule pl_subst[OF _ pl_funplus_com[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var3)"]],simp add: hp_definitions)
       apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "(hp_lambda (hp_fst var1 *\<^sub>t hp_real var3) +\<^sub>t hp_lambda (hp_app var4 (hp_snd var1)))"]]],simp add: hp_definitions)
       apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_distrib'[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var3)"]]],simp add: hp_definitions)

       apply(rule pl_subst[OF _  pl_fundiv_real_def[of _ _ "hp_lambda (hp_fst var1 *\<^sub>t hp_real var3)"]],simp add: hp_definitions)
       apply(rule pl_subst[OF _  pl_fundiv_real_def[of _ _ "hp_lambda (hp_app var4 (hp_snd var1))"]],simp add: hp_definitions)
       apply(rule pl_subst[OF _  pl_abs_div[of _ _ "hp_fst var1 *\<^sub>t hp_real var3"]],simp add: hp_definitions)
       apply(rule pl_subst[OF _  pl_abs_div[of _ _ "hp_app var4 (hp_snd var1)"]],simp add: hp_definitions)
    proof -
      let ?\<Gamma> = ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q ,, \<nat>\<^sub>Q ,, monadP_qbs \<real>\<^sub>Q"
      let ?\<Psi> = "{hp_const 0 <\<^sub>P\<^sub>L var7, var6 =\<^sub>P\<^sub>L hp_expect var4 var3, var5 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var4 var3, hp_integrable var4 var3, hp_integrable var4 (var3 *\<^sub>t var3)} \<union> {hp_const 0 <\<^sub>P\<^sub>L hp_suc var2} \<union> {hp_const 0 <\<^sub>P\<^sub>L var2 \<longrightarrow>\<^sub>P\<^sub>L hp_expect var1 hp_id =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var var1 hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real var2} \<union> {var1 =\<^sub>P\<^sub>L hp_app hp_montecarlo'' var2}"
      have integrable_hp_id:
           "?\<Gamma> | ?\<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable var1 hp_id"
        apply(rule pl_subst[where t="hp_app hp_montecarlo'' var2" and u=var1],simp add: hp_definitions)
         apply(rule pl_eq_sym)
         apply(rule pl_ax,simp)
        apply(rule pl_allE[where e=var2],simp add: hp_definitions)
        apply(rule hpt_var2)
        apply (simp,rule pl_weakening[where \<Psi>="{hp_const 0 <\<^sub>P\<^sub>L var7, var6 =\<^sub>P\<^sub>L hp_expect var4 var3, var5 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var4 var3, hp_integrable var4 var3, hp_integrable var4 (var3 *\<^sub>t var3)}" and \<Phi>="?\<Psi>",simplified])
        apply(rule pl_contweakening[of _ "\<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo' (hp_const x)) hp_id" _ "{hp_const 0 <\<^sub>P\<^sub>L var6, var5 =\<^sub>P\<^sub>L hp_expect var3 var2, var4 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var3 var2, hp_integrable var3 var2, hp_integrable var3 (var2 *\<^sub>t var2)}"],simp add: hp_definitions hp_montecarlo'_def hp_montecarlo''_def split_beta' id_def,simp add: hp_definitions split_beta')
        apply(rule pl_contweakening[of _ "\<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo (hp_const x)) hp_id" _ "{hp_const 0 <\<^sub>P\<^sub>L var5, var4 =\<^sub>P\<^sub>L hp_expect var2 var1, var3 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var2 var1, hp_integrable var2 var1, hp_integrable var2 (var1 *\<^sub>t var1)}"],simp add: hp_definitions hp_montecarlo'_def hp_montecarlo''_def split_beta' id_def,simp add: hp_definitions split_beta')
        apply(rule montecarlo_integrable'[simplified \<Phi>mon_def,simplified])
        done
      have integrable_hp_id':
           "?\<Gamma> | ?\<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable var1 (hp_id *\<^sub>t hp_id)"
        apply(rule pl_subst[where t="hp_app hp_montecarlo'' var2" and u=var1],simp add: hp_definitions)
         apply(rule pl_eq_sym)
         apply(rule pl_ax,simp)
        apply(rule pl_allE[where e=var2],simp add: hp_definitions)
        apply(rule hpt_var2)
        apply (simp,rule pl_weakening[where \<Psi>="{hp_const 0 <\<^sub>P\<^sub>L var7, var6 =\<^sub>P\<^sub>L hp_expect var4 var3, var5 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var4 var3, hp_integrable var4 var3, hp_integrable var4 (var3 *\<^sub>t var3)}" and \<Phi>="?\<Psi>",simplified])
        apply(rule pl_contweakening[of _ "\<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo' (hp_const x)) (hp_id *\<^sub>t hp_id)" _ "{hp_const 0 <\<^sub>P\<^sub>L var6, var5 =\<^sub>P\<^sub>L hp_expect var3 var2, var4 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var3 var2, hp_integrable var3 var2, hp_integrable var3 (var2 *\<^sub>t var2)}"],simp add: hp_definitions hp_montecarlo'_def hp_montecarlo''_def split_beta' id_def,simp add: hp_definitions split_beta')
        apply(rule pl_contweakening[of _ "\<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_integrable (hp_app hp_montecarlo (hp_const x)) (hp_id *\<^sub>t hp_id)" _ "{hp_const 0 <\<^sub>P\<^sub>L var5, var4 =\<^sub>P\<^sub>L hp_expect var2 var1, var3 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var2 var1, hp_integrable var2 var1, hp_integrable var2 (var1 *\<^sub>t var1)}"],simp add: hp_definitions hp_montecarlo'_def hp_montecarlo''_def split_beta' id_def,simp add: hp_definitions split_beta')
        apply(rule montecarlo_integrable2'[simplified \<Phi>mon_def,simplified])
        done
      have integrable_var3:
           "?\<Gamma> | ?\<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable var4 var3"
        apply(rule pl_ax,simp)
        done
      have integrable_var3':
           "?\<Gamma> | ?\<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable var4 (var3 *\<^sub>t var3)"
        apply(rule pl_ax,simp)
        done
      have integrable1:
           "?\<Gamma> | ?\<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable var1 (hp_lambda (var1 *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3)))"
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="var1 *\<^sub>t hp_real var3" and g="hp_real (hp_suc var3)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_times[where f=var1 and g="hp_real var3"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "hp_lambda var1 *\<^sub>t hp_lambda (hp_real var3)" "hp_lambda (hp_real (hp_suc var3))"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_hp_id],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var3)" "hp_real (hp_suc var2)"]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real var3" "hp_real var2"]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ hp_id "hp_constf (hp_real var2)"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ hp_id]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf[of _ _ "hp_real var2"]]],simp add: hp_definitions)
        apply(rule pl_integrable_mult)
        apply(rule integrable_hp_id)
        done
      have integrable1':
           "?\<Gamma> | ?\<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable var1 (hp_lambda (var1 *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3)) *\<^sub>t hp_lambda (var1 *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3)))"
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="var1 *\<^sub>t hp_real var3" and g="hp_real (hp_suc var3)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_times[where f=var1 and g="hp_real var3"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "hp_lambda var1 *\<^sub>t hp_lambda (hp_real var3)" "hp_lambda (hp_real (hp_suc var3))"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_hp_id],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var3)" "hp_real (hp_suc var2)"]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real var3" "hp_real var2"]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ hp_id "hp_constf (hp_real var2)"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ hp_id]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf[of _ _ "hp_real var2"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ "hp_constf (hp_real var2 *\<^sub>t (hp_const 1 /\<^sub>t hp_real (hp_suc var2)))"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ hp_id]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ _ hp_id]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc[of _ _ _ _ "hp_id *\<^sub>t hp_id"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf]],simp add: hp_definitions)
        apply(rule pl_integrable_mult)
        apply(rule integrable_hp_id')
        done
      have integrable2:
           "?\<Gamma> | ?\<Psi> \<turnstile>\<^sub>P\<^sub>L hp_integrable var4 (hp_lambda (hp_app var4 var1 /\<^sub>t hp_real (hp_suc var3)))"
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var4 var1" and g="hp_real (hp_suc var3)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var3)" "hp_real (hp_suc var2)"]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_eta[of var4 var3]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ var3]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ var3]],simp add: hp_definitions)
        apply(rule pl_integrable_mult)
        apply(rule integrable_var3)
        done
      have integrable2':
           "?\<Gamma> | ?\<Psi>  \<turnstile>\<^sub>P\<^sub>L hp_integrable var4 (hp_lambda (hp_app var4 var1 /\<^sub>t hp_real (hp_suc var3)) *\<^sub>t hp_lambda (hp_app var4 var1 /\<^sub>t hp_real (hp_suc var3)))"
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var4 var1" and g="hp_real (hp_suc var3)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var3)" "hp_real (hp_suc var2)"]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_eta[of var4 var3]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ var3]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ var3]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ "hp_constf (hp_const 1 /\<^sub>t hp_real (hp_suc var2))"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ var3]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ _ var3]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_funtimes_assoc[of _ _ _ _ "var3 *\<^sub>t var3"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf]],simp add: hp_definitions)
        apply(rule pl_integrable_mult)
        apply(rule integrable_var3')
        done
      show "?\<Gamma> | ?\<Psi>
           \<turnstile>\<^sub>P\<^sub>L  hp_expect (hp_pair_measure var1 var4) (hp_lambda (hp_fst var1 *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3)) +\<^sub>t hp_lambda (hp_app var4 (hp_snd var1) /\<^sub>t hp_real (hp_suc var3)))
                   =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L
                hp_var (hp_pair_measure var1 var4) (hp_lambda (hp_fst var1 *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3)) +\<^sub>t hp_lambda (hp_app var4 (hp_snd var1) /\<^sub>t hp_real (hp_suc var3)))
                   =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real (hp_suc var2)"

        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_indep_plus[of "\<lambda>t. t *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3)" "hp_lambda (var1 *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3))" "\<lambda>t. hp_app var4 t /\<^sub>t hp_real (hp_suc var3)" "hp_lambda (hp_app var4 var1 /\<^sub>t hp_real (hp_suc var3))" _ _ "var1" "var4"]]],simp add: hp_definitions,simp add: hp_definitions,simp add: hp_definitions,rule integrable1,rule integrable2)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_var_indep_plus[of "\<lambda>t. t *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3)" "hp_lambda (var1 *\<^sub>t hp_real var3 /\<^sub>t hp_real (hp_suc var3))" "\<lambda>t. hp_app var4 t /\<^sub>t hp_real (hp_suc var3)" "hp_lambda (hp_app var4 var1 /\<^sub>t hp_real (hp_suc var3))" _ _ "var1" "var4"]]],simp add: hp_definitions,simp add: hp_definitions,simp add: hp_definitions,rule integrable1,rule integrable1',rule integrable2,rule integrable2')

          (* var1 *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="var1 *\<^sub>t hp_real var3" and g="hp_real (hp_suc var3)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_times[where f=var1 and g="hp_real var3"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ "hp_lambda var1 *\<^sub>t hp_lambda (hp_real var3)" "hp_lambda (hp_real (hp_suc var3))"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_hp_id],simp add: hp_definitions)
          (* var4 *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_abs_div[where f="hp_app var4 var1" and g="hp_real (hp_suc var3)"]]],simp add: hp_definitions)

           (* var4 *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var3)" "hp_real (hp_suc var2)"]]],simp add: hp_definitions,simp add: hp_definitions)
           (* var1 *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real (hp_suc var3)" "hp_real (hp_suc var2)"]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_lambda_const[of "hp_real var3" "hp_real var2"]]],simp add: hp_definitions,simp add: hp_definitions)

           (* var1 *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_assoc[of _ _ hp_id "hp_constf (hp_real var2)"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ hp_id]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_constf[of _ _ "hp_real var2"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_real_def[of _ _ "hp_real var2"]],simp add: hp_definitions)
               (* expectation var *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_cmult[of _ _ var1 "hp_real var2 /\<^sub>t hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_var_cmult[OF integrable_hp_id]]],simp add: hp_definitions)

           (* var4 *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_eta[of var4 var3]]],simp add: hp_definitions,simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_fundiv_real_def[of _ _ var3]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_constf[of _ _ "hp_const 1" "hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_funtimes_com[of _ _ _ var3]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_expect_cmult[where t=var4 and c="hp_const 1 /\<^sub>t hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_var_cmult[OF integrable_var3]]],simp add: hp_definitions)
 
        apply(rule pl_subst[where u="hp_expect var4 var3" and t=var6],simp add: hp_definitions)
         apply(rule pl_ax,simp)
        apply(rule pl_subst[where u="hp_var var4 var3" and t="var5 ^\<^sup>t 2"],simp add: hp_definitions)
         apply(rule pl_ax,simp)
        (* the equation about expectation *)
        apply(rule pl_subst[OF _ pl_times_com[of _ _ _ "hp_real var2 /\<^sub>t hp_real (hp_suc var2)"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_times_com[of _ _ _ "hp_const 1 /\<^sub>t hp_real (hp_suc var2)"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_timesr[of _ _ "hp_expect var1 hp_id"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_timesr[of _ _ var6]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_right1[of _ _ var6]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_plus_distr[of _ _ _ var6]],simp add: hp_definitions)

        (* the equation about var *)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_power_square[where t="hp_real var2 /\<^sub>t hp_real (hp_suc var2)"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_power_square[where t="hp_const 1 /\<^sub>t hp_real (hp_suc var2)"]]],simp add: hp_definitions)

        apply(rule pl_orE[OF pl_nzero_orgt0[where t=var2]])
   (* case var2 (=n) is equal to zero *)
        apply(rule pl_impI)
         apply(rule pl_subst[where u=var2 and t="hp_const 0"],simp add: hp_definitions)
          apply(rule pl_ax,simp)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_suc[of _ _ "hp_const 0"]]],simp add: hp_definitions)
           (* change var2 to 0 *)
         apply(rule pl_subst[where u="hp_real (hp_const 0)" and t="hp_const 0"],simp add: hp_definitions)
          apply(rule pl_subst[OF _ pl_eq_sym[OF pl_real_const[of _ _ 0]]],simp add: hp_definitions,simp)
          apply(rule pl_eq_refl)

         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_right0[of _ _ "hp_const 1"]]],simp add: hp_definitions)
         apply(rule pl_subst[where u="hp_real (hp_const 1)" and t="hp_const 1"],simp add: hp_definitions)
          apply(rule pl_subst[OF _ pl_eq_sym[OF pl_real_const[of _ _ 1]]],simp add: hp_definitions,simp)
          apply(rule pl_eq_refl)
         apply(rule pl_andI)
      (* expectation *)
          apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_right0[where n="hp_expect var1 hp_id"]]],simp add: hp_definitions)
          apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_left0[where n=var6]]],simp add: hp_definitions)
          apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div1[of _ _ var6]]],simp add: hp_definitions)
          apply(rule pl_eq_refl)
      (* var *)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_real_0_div[where r="hp_const 1"]]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_left0]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_left0]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_plus_left0]],simp add: hp_definitions)
         apply(rule pl_subst[where u="hp_const 1 /\<^sub>t hp_const 1" and t="hp_const 1"],simp add: hp_definitions)
          apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_const]],simp add: hp_definitions,simp)
          apply(rule pl_eq_refl)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_left1]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_left1]],simp add: hp_definitions)
         apply(rule pl_eq_sym)
         apply(rule pl_div1)
   (* case var2 (=n) is greater than zero *)
        apply(rule pl_impI)
        apply(rule pl_andI)
      (* expectation *)
        (* subst with IH *)
         apply(rule pl_subst[where u="hp_expect var1 hp_id" and t="var6"],simp add: hp_definitions)
          apply(rule pl_eq_sym)
          apply(rule pl_andEl[where \<psi>="hp_var var1 hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real var2"])
          apply(rule pl_impE[where \<psi>="hp_const 0 <\<^sub>P\<^sub>L var2"])
           apply(rule pl_ax,simp)
          apply(rule pl_ax,simp)
        (* nemerical transformation *)
         apply(rule pl_subst[of "\<lambda>t. (var6 *\<^sub>t hp_real var2 +\<^sub>t t) /\<^sub>t hp_real (hp_suc var2) =\<^sub>P\<^sub>L var6",OF _ pl_times_right1[where n=var6]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_times_distrib[of _ _ var6]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_timesr[of _ _ var6]]],simp add: hp_definitions)
         apply(rule pl_subst[where u="hp_const (1::real)" and t="hp_real (hp_const 1)"],simp add: hp_definitions)
          apply(rule pl_subst[OF _ pl_real_const[where n=1,simplified]],simp add: hp_definitions,simp)
          apply(rule pl_eq_refl)

          (* var2 + 1 / var2 + 1 = 1 *)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_suc]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_real_plus]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_plus_com[of _ _ "hp_real var2"]],simp add: hp_definitions)
         apply(rule pl_subst[where u="(hp_real var2 +\<^sub>t hp_real (hp_const 1)) /\<^sub>t (hp_real var2 +\<^sub>t hp_real (hp_const 1))" and t="hp_const 1"],simp add: hp_definitions)
          apply(rule pl_eq_sym)
          apply(rule pl_impE[OF pl_div_div[where t="hp_real var2 +\<^sub>t hp_real (hp_const 1)"]])
          apply(rule pl_impE[OF pl_rorder_plust[of _ _ "hp_const 0" "hp_real var2 " "hp_real (hp_const 1)"]])
          apply(rule pl_subst[OF _ pl_real_const[where n=0,simplified]],simp add: hp_definitions)
          apply(rule pl_andI)
           apply(rule pl_impE[OF pl_order_nat_real])
           apply(rule pl_ax,simp)
          apply(rule pl_impE[OF pl_order_nat_real])
          apply(rule pl_order_const,simp)
 
         apply(rule pl_times_right1)
      (* var *)
        (* subst with IH *)
        apply(rule pl_subst[where u="hp_var var1 hp_id" and t="var5 ^\<^sup>t 2 /\<^sub>t hp_real var2"],simp add: hp_definitions)
         apply(rule pl_eq_sym)
         apply(rule pl_andEr[where \<phi>="hp_expect var1 hp_id =\<^sub>P\<^sub>L var6"])
         apply(rule pl_impE[where \<psi>="hp_const 0 <\<^sub>P\<^sub>L var2"])
          apply(rule pl_ax,simp)
         apply(rule pl_ax,simp)
        (* numerical transformation *)
        apply(rule pl_subst[OF _  pl_times_assoc[of _ _ "hp_real var2 /\<^sub>t hp_real (hp_suc var2)"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_times_div_swap[of _ _ "hp_real var2" "hp_real var2"]],simp add: hp_definitions)
        apply(rule pl_subst[where u="hp_real var2 /\<^sub>t hp_real var2" and t="hp_const 1"],simp add: hp_definitions)
         apply(rule pl_eq_sym)
         apply(rule pl_impE[OF pl_div_div])
         apply(rule pl_subst[OF _ pl_real_const[where n=0,simplified]],simp add: hp_definitions)
         apply(rule pl_impE[OF pl_order_nat_real])
         apply(rule pl_ax,simp)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_left1]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_times_div[of _ _ "hp_real var2"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_div_times_div[of _ _ "hp_const 1"]]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_times_com[of _ _ "var5 ^\<^sup>t 2"]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_eq_sym[OF pl_times_right1]],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_real_def],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_plus_distr],simp add: hp_definitions)
        apply(rule pl_subst[of "\<lambda>t. (hp_real var2 *\<^sub>t var5 ^\<^sup>t 2 +\<^sub>tt) /\<^sub>t (hp_real (hp_suc var2) *\<^sub>t hp_real (hp_suc var2)) =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real (hp_suc var2)",OF _ pl_times_left1],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_times_distrib'],simp add: hp_definitions)
        apply(rule pl_subst[OF _ pl_div_times_div],simp add: hp_definitions)
        apply(rule pl_subst[where u="(hp_real var2 +\<^sub>t hp_const 1) /\<^sub>t hp_real (hp_suc var2)" and t="hp_const 1"],simp add: hp_definitions)
         apply(rule pl_eq_sym)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_suc]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_plus_com[of _ _ var2]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_real_plus]],simp add: hp_definitions)
         apply(rule pl_subst[OF _ pl_eq_sym[OF pl_real_const[where n=1]]],simp add: hp_definitions,simp)
         apply(rule pl_impE[OF pl_div_div])
         apply(rule pl_impE[OF pl_rorder_plust])
         apply(rule pl_andI)
          apply(rule pl_subst[OF _ pl_real_const[where n=0,simplified]],simp add: hp_definitions)
          apply(rule pl_impE[OF pl_order_nat_real])
          apply(rule pl_ax,simp)
         apply(rule pl_order_const,simp)
        apply(rule pl_times_left1)
        done
    qed
    show ",\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q ,, \<nat>\<^sub>Q ,, monadP_qbs \<real>\<^sub>Q |
          {hp_const 0 <\<^sub>P\<^sub>L var7, var6 =\<^sub>P\<^sub>L hp_expect var4 var3, var5 ^\<^sup>t 2 =\<^sub>P\<^sub>L hp_var var4 var3, hp_integrable var4 var3, hp_integrable var4 (var3 *\<^sub>t var3)} \<union> {hp_const 0 <\<^sub>P\<^sub>L hp_suc var2} \<union>
            {hp_const 0 <\<^sub>P\<^sub>L var2 \<longrightarrow>\<^sub>P\<^sub>L hp_expect var1 hp_id =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var var1 hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real var2} \<union> {var1 =\<^sub>P\<^sub>L hp_app hp_montecarlo'' var2} \<turnstile>\<^sub>U\<^sub>P\<^sub>L
                 var1 \<bind> hp_lambda (var5 \<bind> hp_lambda (hp_return \<real>\<^sub>Q ((hp_app var5 var1 +\<^sub>t var2 *\<^sub>t hp_real var4) /\<^sub>t hp_real (hp_suc var4)))) ;; monadP_qbs \<real>\<^sub>Q |
                     \<lambda>r. hp_expect r hp_id =\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L hp_var r hp_id =\<^sub>P\<^sub>L var5 ^\<^sup>t 2 /\<^sub>t hp_real (hp_suc var2)"
      apply(rule upl_if_pl)
        apply(rule hpt_bind,rule hpt_var1,rule hpt_abs,rule hpt_bind,rule hpt_var5,rule hpt_abs,rule hpt_return,rule hpt_divr,rule hpt_plusr,rule hpt_app,rule hpt_var5,rule hpt_var1,rule hpt_timesr,rule hpt_var2,rule hpt_real,rule hpt_var4,rule hpt_real,rule hpt_suc,rule hpt_var4)
      apply(simp add: hp_definitions)
      apply(rule hpl)
      done
  qed
next
  show " ,\<real>\<^sub>Q ,, \<real>\<^sub>Q ,, \<real>\<^sub>Q ,, monadP_qbs X ,, exp_qbs X \<real>\<^sub>Q | \<Phi>mon \<turnstile>\<^sub>P\<^sub>L
   (\<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app hp_montecarlo (hp_const n)) hp_id =\<^sub>P\<^sub>L var4 \<and>\<^sub>P\<^sub>L hp_var (hp_app hp_montecarlo (hp_const n)) hp_id =\<^sub>P\<^sub>L var3 ^\<^sup>t 2 /\<^sub>t hp_real (hp_const n))
    \<longrightarrow>\<^sub>P\<^sub>L (\<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n \<longrightarrow>\<^sub>P\<^sub>L hp_prob (hp_app hp_montecarlo (hp_const n)) {y. var5 \<le>\<^sub>P\<^sub>L \<bar>hp_const y -\<^sub>t var4\<bar>\<^sub>t}\<^sub>t \<le>\<^sub>P\<^sub>L var3 ^\<^sup>t 2 /\<^sub>t hp_real (hp_const n) *\<^sub>t (hp_const 1 /\<^sub>t var5 ^\<^sup>t 2))"
    apply(rule pl_impI)
    apply(rule pl_allI[of "(\<lambda>\<psi> (k, _). \<psi> k) ` \<Phi>mon \<union> {\<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app hp_montecarlo' (hp_const n)) hp_id =\<^sub>P\<^sub>L var5 \<and>\<^sub>P\<^sub>L hp_var (hp_app hp_montecarlo' (hp_const n)) hp_id =\<^sub>P\<^sub>L var4 ^\<^sup>t 2 /\<^sub>t hp_real (hp_const n)}" _ _ "hp_const 0 <\<^sub>P\<^sub>L var1 \<longrightarrow>\<^sub>P\<^sub>L hp_prob (hp_app hp_montecarlo' var1) {y. var6 \<le>\<^sub>P\<^sub>L \<bar>hp_const y -\<^sub>t var5\<bar>\<^sub>t}\<^sub>t \<le>\<^sub>P\<^sub>L var4 ^\<^sup>t 2 /\<^sub>t hp_real var1 *\<^sub>t (hp_const 1 /\<^sub>t var6 ^\<^sup>t 2)"],simp add: hp_definitions hp_montecarlo'_def split_beta',simp add: hp_definitions' split_beta' hp_montecarlo'_def)
    apply(rule pl_impI)
    apply(rule pl_subst[of "\<lambda>t. hp_prob (hp_app hp_montecarlo' var1) {y. var6 \<le>\<^sub>P\<^sub>L \<bar>hp_const y -\<^sub>t var5\<bar>\<^sub>t}\<^sub>t \<le>\<^sub>P\<^sub>L t *\<^sub>t (hp_const 1 /\<^sub>t var6 ^\<^sup>t 2)" _ _ _ "hp_var (hp_app hp_montecarlo' var1) hp_id" "var4 ^\<^sup>t 2 /\<^sub>t hp_real var1"],simp add: hp_definitions hp_montecarlo'_def)
     apply(rule pl_andEr[where \<phi>="hp_expect (hp_app hp_montecarlo' var1) hp_id =\<^sub>P\<^sub>L var5"])
     apply(rule pl_impE'[where \<phi>="hp_const 0 <\<^sub>P\<^sub>L var1"])
     apply(rule pl_allE[of "\<lambda>t. hp_const 0 <\<^sub>P\<^sub>L t \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app hp_montecarlo' t) hp_id =\<^sub>P\<^sub>L var5 \<and>\<^sub>P\<^sub>L hp_var (hp_app hp_montecarlo' t) hp_id =\<^sub>P\<^sub>L var4 ^\<^sup>t 2 /\<^sub>t hp_real t" _ _ var1 "\<nat>\<^sub>Q"],simp add: hp_definitions,simp add: hpt_var1)
     apply(rule pl_ax,simp)
    apply(rule pl_subst[of "\<lambda>t. hp_prob (hp_app hp_montecarlo' var1) {y. var6 \<le>\<^sub>P\<^sub>L \<bar>hp_const y -\<^sub>t var5\<bar>\<^sub>t}\<^sub>t \<le>\<^sub>P\<^sub>L t",OF _  pl_div_real_def[of _ _ "hp_var (hp_app hp_montecarlo' var1) hp_id" "var6 ^\<^sup>t 2"]],simp add: hp_definitions)
    apply(rule pl_impE[where \<psi>="hp_const 0 <\<^sub>P\<^sub>L var6 \<and>\<^sub>P\<^sub>L var5 =\<^sub>P\<^sub>L hp_expect (hp_app hp_montecarlo' var1) hp_id"])


     apply(rule pl_chebyshev_inequality[of _ "hp_app hp_montecarlo' var1" var6 var5])
         apply(rule hpt_app)
          apply(rule hpt_addcont[OF _ montecarlo_typing'],simp add: hp_montecarlo'_def)
         apply(rule hpt_var1,simp,rule hpt_var6,rule hpt_var5)
      apply(rule pl_impE')
      apply(rule pl_allEVar[of "\<lambda>t. hp_const 0 <\<^sub>P\<^sub>L t \<longrightarrow>\<^sub>P\<^sub>L hp_integrable (hp_app hp_montecarlo t) hp_id" _ _ " \<Phi>mon \<union> {\<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app hp_montecarlo (hp_const n)) hp_id =\<^sub>P\<^sub>L var4 \<and>\<^sub>P\<^sub>L hp_var (hp_app hp_montecarlo (hp_const n)) hp_id =\<^sub>P\<^sub>L var3 ^\<^sup>t 2 /\<^sub>t hp_real (hp_const n)}"],simp add: hp_definitions hp_montecarlo'_def,simp add: hp_definitions hp_montecarlo'_def split_beta')
      apply(rule pl_weakening)
      apply(rule pl_allimp_addassm[of _ "\<lambda>k. qbs_integrable (hp_montecarlo (fst k) (snd k)) (\<lambda>x. x)" _ "\<lambda>k. 0 < snd k"],simp add: hp_definitions',simp add: hp_definitions)
      apply(rule montecarlo_integrable')
     apply(rule pl_impE')
     apply(rule pl_allEVar[of "\<lambda>t. hp_const 0 <\<^sub>P\<^sub>L t \<longrightarrow>\<^sub>P\<^sub>L hp_integrable (hp_app hp_montecarlo t) (hp_id *\<^sub>t hp_id)" _ _ " \<Phi>mon \<union> {\<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. hp_const 0 <\<^sub>P\<^sub>L hp_const n \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app hp_montecarlo (hp_const n)) hp_id =\<^sub>P\<^sub>L var4 \<and>\<^sub>P\<^sub>L hp_var (hp_app hp_montecarlo (hp_const n)) hp_id =\<^sub>P\<^sub>L var3 ^\<^sup>t 2 /\<^sub>t hp_real (hp_const n)}"],simp add: hp_definitions hp_montecarlo'_def,simp add: hp_definitions hp_montecarlo'_def split_beta')
     apply(rule pl_weakening)
     apply(rule pl_allimp_addassm[of _ "\<lambda>k. qbs_integrable (hp_montecarlo (fst k) (snd k)) (\<lambda>x. x * x)" _ "\<lambda>k. 0 < snd k"],simp add: hp_definitions',simp add: hp_definitions)
     apply(rule montecarlo_integrable2')

    apply(rule pl_andI)
      apply(rule pl_ax,simp add: \<Phi>mon_def hp_definitions split_beta')
     apply(rule pl_eq_sym)
     apply(rule pl_andEl[where \<psi>="hp_var (hp_app hp_montecarlo' var1) hp_id =\<^sub>P\<^sub>L var4 ^\<^sup>t 2 /\<^sub>t hp_real var1"])
     apply(rule pl_impE'[where \<phi>="hp_const 0 <\<^sub>P\<^sub>L var1"])
     apply(rule pl_allE[of "\<lambda>t. hp_const 0 <\<^sub>P\<^sub>L t \<longrightarrow>\<^sub>P\<^sub>L hp_expect (hp_app hp_montecarlo' t) hp_id =\<^sub>P\<^sub>L var5 \<and>\<^sub>P\<^sub>L hp_var (hp_app hp_montecarlo' t) hp_id =\<^sub>P\<^sub>L var4 ^\<^sup>t 2 /\<^sub>t hp_real t" _ _ var1 "\<nat>\<^sub>Q"],simp add: hp_definitions,simp add: hpt_var1)
     apply(rule pl_ax,simp)
    done
qed


end