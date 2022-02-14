(*  Title:   UPL.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology

*)
subsection \<open> UPL \<close>

theory UPL
  imports PL

begin

definition upl_der :: "['cont quasi_borel, 'cont assump, 'cont \<Rightarrow> 'typ, 'typ quasi_borel, ('cont \<Rightarrow> 'typ) \<Rightarrow> 'cont \<Rightarrow> bool] \<Rightarrow> bool" where
"upl_der \<Gamma> \<Psi> t T \<phi> \<equiv> (hpprog_typing \<Gamma> t T \<and> (\<exists>\<phi>'. \<phi> = (\<lambda>t k. \<phi>' k (t k))) \<and> (\<forall>k\<in>qbs_space \<Gamma>. hp_conjall \<Psi> k \<longrightarrow> \<phi> t k))"

syntax
 "_upl_der" :: "any \<Rightarrow> 'cont quasi_borel \<Rightarrow> 'cont assump \<Rightarrow> ('cont \<Rightarrow> 'typ) \<Rightarrow> 'typ quasi_borel \<Rightarrow> (('cont \<Rightarrow> 'typ) \<Rightarrow> 'cont \<Rightarrow> bool) \<Rightarrow> bool" ("_ | _ \<turnstile>\<^sub>U\<^sub>P\<^sub>L _ ;; _ | _" 21)

translations
 "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>" \<rightleftharpoons> "CONST upl_der \<Gamma> \<Psi> e T \<phi>"

(* Example *)
term "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_const 1 ;; \<nat>\<^sub>Q | \<lambda>r. hp_const 1 \<le>\<^sub>P\<^sub>L r +\<^sub>t r"

lemma upl_phi_equiv1:
  assumes "\<phi> = (\<lambda>r env. \<psi> env (r env))"
      and "e k = e' k"
    shows "\<phi> e k = \<phi> e' k"
  using assms by simp

lemma upl_phi_const:
  assumes "\<phi> = (\<lambda>r env. \<psi> env (r env))"
  shows "\<phi> (hp_const (e k)) k = \<phi> e k"
  by(simp add: assms hp_const_def)

text \<open> The completeness theorem w.r.t. derivability is proved by expanding definitions. \<close>
lemma pl_upl_complete:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; T"
      and "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
    shows "(\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> t) \<longleftrightarrow> (\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L t ;; T | \<phi>)"
  using assms
  by(auto simp add: pl_der_def upl_der_def)

lemma pl_if_upl:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; T"
          "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L t ;; T | \<phi>"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> t"
  using pl_upl_complete[OF assms(1,2)] assms(3)
  by simp

lemma upl_if_pl:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; T"
          "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> t"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L t ;; T | \<phi>"
  using pl_upl_complete[OF assms(1,2)] assms(3)
  by simp

lemma upl_const:
  assumes "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
          "\<Gamma> \<turnstile>\<^sub>t hp_const c ;; T"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> (hp_const c)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_const c ;; T | \<phi>"
  using assms by(auto simp add: pl_der_def upl_der_def)

lemma upl_var1:
  assumes "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma>,,X | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> var1"
    shows "\<Gamma>,,X | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L var1 ;; X | \<phi>"
  using assms hpt_var1 by(auto simp add: pl_der_def upl_der_def)

lemma upl_var2:
  assumes "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma>,,Z,,Y | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> var2"
    shows "\<Gamma>,,Z,,Y | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L var2 ;; Z | \<phi>"
  using assms hpt_var2 by(auto simp add: pl_der_def upl_der_def)

lemma upl_var3:
  assumes "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma>,,Z,,Y,,X | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> var3"
    shows "\<Gamma>,,Z,,Y,,X | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L var3 ;; Z | \<phi>"
  using assms hpt_var3 by(auto simp add: pl_der_def upl_der_def)

lemma upl_var4:
  assumes "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma>,,Z,,Y,,X,,W | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> var4"
    shows "\<Gamma>,,Z,,Y,,X,,W | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L var4 ;; Z | \<phi>"
  using assms hpt_var4 by(auto simp add: pl_der_def upl_der_def)

lemma upl_var5:
  assumes "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma>,,Z,,Y,,X,,W,,V | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> var5"
    shows "\<Gamma>,,Z,,Y,,X,,W,,V | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L var5 ;; Z | \<phi>"
  using assms hpt_var5 by(auto simp add: pl_der_def upl_der_def)

(*         \<Gamma>, x : X | \<Psi>,\<phi>' |-upl e : Y | \<phi>
  ----------------------------------------------------
   \<Gamma> | \<Psi> |-upl (\<lambda>x. e) : X \<Rightarrow> Y | \<forall>x. \<phi>' \<longrightarrow> \<phi>[r x/r] *)
lemma upl_abs:
  assumes "\<Psi> = (\<lambda>\<psi>. (\<lambda>(k,_). \<psi> k)) `\<Psi>'"
          "\<Phi>' = (\<lambda>x env. curry (hp_conjall \<Phi>) env x)"
          "\<phi> = (\<lambda>r k. \<phi>' (snd k) (\<lambda>l. r (l,snd k)) (fst k))"
      and "\<Gamma>,,X | \<Psi> \<union> \<Phi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>"
    shows "\<Gamma> | \<Psi>' \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_lambda e ;; exp_qbs X T | (\<lambda>r. \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<Phi>' x \<longrightarrow>\<^sub>P\<^sub>L \<phi>' x (hp_app r (hp_const x)))"
proof(auto simp add: hp_definitions upl_der_def)
  show "\<Gamma> \<turnstile>\<^sub>t curry e ;; exp_qbs X T"
    using assms(4) hpt_abs[of \<Gamma> X e T]
    by(simp add: hp_definitions upl_der_def)
next
  obtain \<psi> where h:"\<phi> = (\<lambda>t k. \<psi> k (t k))"
    using assms(4) by(auto simp add: upl_der_def)
  define \<psi>' where "\<psi>' \<equiv> (\<lambda>env f. \<forall>x\<in>qbs_space X. \<Phi>' x env \<longrightarrow> \<psi> (env,x) (f x))"
  have "\<And> x r env. \<phi>' x (\<lambda>k. r k x) env = \<psi> (env, x) (r env x)"
  proof -
    fix x r env
    have "\<phi>' x (\<lambda>k. r k x) env = \<phi> (case_prod r) (env,x)"
      by (simp add: assms(3))
    also have "... = (\<lambda>t k. \<psi> k (t k)) (case_prod r) (env,x)"
      by(simp add: h)
    finally show "\<phi>' x (\<lambda>k. r k x) env = \<psi> (env, x) (r env x)" by simp
  qed
  hence "(\<lambda>r env. \<forall>x\<in>qbs_space X. \<Phi>' x env \<longrightarrow> \<phi>' x (\<lambda>xa. r xa x) env) = (\<lambda>r env. \<psi>' env (r env))"
    by(simp add: \<psi>'_def comp_def qbs_eval_def)
  thus " \<exists>\<phi>''. (\<lambda>r env. \<forall>x\<in>qbs_space X. \<Phi>' x env \<longrightarrow> \<phi>' x (\<lambda>xa. r xa x) env) = (\<lambda>t k. \<phi>'' k (t k))"
    by auto
next
  fix k x
  assume h:"k \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi>' k"
           "x \<in> qbs_space X"
           "\<Phi>' x k"
  then have "hp_conjall ((\<lambda>\<psi> (k, _). \<psi> k) ` \<Psi>' \<union> \<Phi>) (k,x)"
    by (auto simp add:  assms(1,2) curry_def hp_and_def hp_conjall_union[of "(\<lambda>\<psi> (k, _). \<psi> k) ` \<Psi>'" \<Phi>] hp_conjall_def)
    
  thus "\<phi>' x (\<lambda>xa. e (xa, x)) k"
    using h assms by(simp add: upl_der_def hpprog_context_def)
qed

lemma upl_abs':
  assumes "\<Psi> = (\<lambda>\<psi>. (\<lambda>(k,_). \<psi> k)) `\<Psi>'"
          "\<Phi>' = hp_conjall_fix \<Phi>"
          "\<phi> = (\<lambda>r k. \<phi>' (hp_const (snd k)) (\<lambda>l. r (l,snd k)) (fst k))"
      and "\<Gamma>,,X | \<Psi> \<union> \<Phi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>"
    shows "\<Gamma> | \<Psi>' \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_lambda e ;; exp_qbs X T | (\<lambda>r. \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LX. \<Phi>' (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<phi>' (hp_const x) (hp_app r (hp_const x)))"
proof(auto simp add: hp_definitions upl_der_def)
  show "\<Gamma> \<turnstile>\<^sub>t curry e ;; exp_qbs X T"
    using assms(4) hpt_abs[of \<Gamma> X e T]
    by(simp add: hp_definitions upl_der_def)
next
  obtain \<psi> where h:"\<phi> = (\<lambda>t k. \<psi> k (t k))"
    using assms(4) by(auto simp add: upl_der_def)
  define \<psi>' where "\<psi>' \<equiv> (\<lambda>env f. \<forall>x\<in>qbs_space X. \<Phi>' (hp_const x) env \<longrightarrow> \<psi> (env,x) (f x))"
  have "\<And> x r env. \<phi>' (hp_const x) (\<lambda>k. r k x) env = \<psi> (env, x) (r env x)"
  proof -
    fix x r env
    have "\<phi>' (hp_const x) (\<lambda>k. r k x) env = \<phi> (case_prod r) (env,x)"
      by (simp add: assms(3))
    also have "... = (\<lambda>t k. \<psi> k (t k)) (case_prod r) (env,x)"
      by(simp add: h)
    finally show "\<phi>' (hp_const x) (\<lambda>k. r k x) env = \<psi> (env, x) (r env x)" by simp
  qed
  hence "(\<lambda>r env. \<forall>x\<in>qbs_space X. \<Phi>' (hp_const x) env \<longrightarrow> \<phi>' (hp_const x) (\<lambda>xa. r xa x) env) = (\<lambda>r env. \<psi>' env (r env))"
    by(simp add: \<psi>'_def comp_def qbs_eval_def)
  thus " \<exists>\<phi>''. (\<lambda>r env. \<forall>x\<in>qbs_space X. \<Phi>' (\<lambda>_. x) env \<longrightarrow> \<phi>' (\<lambda>_. x) (\<lambda>xa. r xa x) env) = (\<lambda>t k. \<phi>'' k (t k))"
    by (auto simp add: hp_const_def)
next
  fix k x
  assume h:"k \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi>' k"
           "x \<in> qbs_space X"
           "\<Phi>' (\<lambda>_. x) k"
  then have "hp_conjall ((\<lambda>\<psi> (k, _). \<psi> k) ` \<Psi>' \<union> \<Phi>) (k,x)"
    by (auto simp add:  assms(1,2) curry_def hp_and_def hp_conjall_union[of "(\<lambda>\<psi> (k, _). \<psi> k) ` \<Psi>'" \<Phi>] hp_conjall_def hp_const_def hp_conjall_fix_def)
  thus "\<phi>' (\<lambda>_. x) (\<lambda>xa. e (xa, x)) k "
    using h assms by(simp add: upl_der_def comp_def qbs_eval_def hpprog_context_def hp_const_def)
qed


(*  \<Gamma> | \<Psi> |-upl e : T | \<phi>    \<Gamma> | \<Psi> |-pl \<phi> e \<longrightarrow> \<psi> e
   --------------------------------------------------
                \<Gamma> | \<Psi> |-upl e : T | \<psi>               *)
lemma upl_sub:
  assumes "\<psi> = (\<lambda>r env. \<psi>' env (r env))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<phi> e \<longrightarrow>\<^sub>P\<^sub>L \<psi> e"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<psi>"
  using assms by(auto simp add: pl_der_def upl_der_def hp_implies_def)

(*  \<Gamma> | \<Psi> \<turnstile>upl f : T1 \<Rightarrow> T2 | \<forall>x:T1. \<phi>1[x/r] \<longrightarrow> \<phi>[r x/x]    \<Gamma> | \<Psi> \<turnstile>upl e : T1 | \<phi>1
   ----------------------------------------------------------------------------------
                              \<Gamma> | \<Psi> \<turnstile>upl f x : T2 | \<phi>[e/x]                          *)
lemma upl_app:
  assumes "\<phi> = (\<lambda>t r env. \<phi>' (t env) env (r env))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L f ;; exp_qbs T1 T2 | (\<lambda>r. \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LT1. \<psi> (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<phi> (hp_const x) (hp_app r (hp_const x)))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T1 | \<psi>"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_app f e ;; T2 | \<phi> e"
proof(auto simp add: upl_der_def)
  show "\<Gamma> \<turnstile>\<^sub>t hp_app f e ;; T2"
    using hpt_app assms(2,3) by(auto simp add: upl_der_def)
next
  show "\<exists>\<phi>'. \<phi> e = (\<lambda>t k. \<phi>' k (t k))"
    using assms(1) by auto
next
  obtain \<psi>' where h1: "\<psi> = (\<lambda>r env. \<psi>' env (r env))"
    using assms(3) by(auto simp add: upl_der_def)
  fix k
  assume h:"k \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> k"
  then have "e k \<in> qbs_space T1"
    using assms(3) qbs_morphismE(1)[of e \<Gamma> T1]
    by(auto simp add: upl_der_def hpprog_typing_def)
  moreover have "(\<psi> (hp_const (e k)) k)"
    using  assms(3) h upl_phi_const[OF h1,of e k]
    by(simp add: upl_der_def)
  ultimately have "\<phi> (hp_const (e k)) (hp_app f (hp_const (e k))) k"
    using h assms(2) by(simp add: upl_der_def hp_implies_def hp_all_def)
  moreover have "(\<phi> (hp_const (e k)) (hp_app f (hp_const (e k))) k) = (\<phi> e (hp_app f e) k)"
    by(simp add: hp_definitions assms(1))
  ultimately show "\<phi> e (hp_app f e) k"
    by simp
qed


(*  \<Gamma> | \<Psi> \<turnstile>upl e : T1 \<times> T2 | \<phi> [\<pi>1(r)/r]
   --------------------------------------
           \<Gamma> | \<Psi> \<turnstile>upl \<pi>1 e : T1 | \<phi>     *)
lemma upl_proj1:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T1 \<Otimes>\<^sub>Q (T2 :: 't2 quasi_borel) | \<lambda>r. \<phi> (hp_fst r)"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_fst e ;; T1 | (\<phi> :: ('env \<Rightarrow> 't1) \<Rightarrow> 'env \<Rightarrow> bool)"
  using assms hpt_fst[of \<Gamma> e T1 T2]
proof(auto simp add: upl_der_def hp_fst_def)
  fix \<phi>' :: "'env \<Rightarrow> 't1 \<times> 't2 \<Rightarrow> bool"
  define fr :: "'t1 \<Rightarrow> 't1 \<times> 't2"
    where "fr \<equiv> (\<lambda>k1. (k1,undefined))"
  define \<psi> :: "'env \<Rightarrow> 't1 \<Rightarrow> bool"
    where "\<psi> \<equiv> (\<lambda>env t1. \<phi>' env (fr t1))"
  have hfr:"\<And>r'. fst \<circ> (fr \<circ> r') = r'"
    by(auto simp add: fr_def)
  assume h1:"(\<lambda>r. \<phi> (\<lambda>env. fst (r env))) = (\<lambda>t k. \<phi>' k (t k))"
  have "\<And>r' env. \<phi> r' env = \<phi>' env (fr (r' env))"
  proof -
    fix r' env
    have "\<phi> r' env = (\<lambda>r. \<phi> (\<lambda>env. fst (r env))) (fr \<circ> r') env"
      using hfr[of r'] by(auto simp add: comp_def)
    also have "... = (\<lambda>t k. \<phi>' k (t k)) (fr \<circ> r') env"
      by (metis h1)
    finally show "\<phi> r' env = \<phi>' env (fr (r' env))"
      by auto
  qed
  hence "\<phi> = (\<lambda>t k. \<psi> k (t k))"
    by(auto simp add: \<psi>_def)
  thus "\<exists>\<phi>''. \<phi> = (\<lambda>t k. \<phi>'' k (t k))"
    by auto
qed

(*  \<Gamma> | \<Psi> \<turnstile>upl e : T1 \<times> T2 | \<phi> [\<pi>2(r)/r]
   --------------------------------------
           \<Gamma> | \<Psi> \<turnstile>upl \<pi>2 e : T2 | \<phi>     *)
lemma upl_proj2:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; (T1 :: 't1 quasi_borel) \<Otimes>\<^sub>Q T2 | \<lambda>r. \<phi> (hp_snd r)"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_snd e ;; T2 | (\<phi> :: ('env \<Rightarrow> 't2) \<Rightarrow> 'env \<Rightarrow> bool)"
  using assms hpt_snd[of \<Gamma> e T1 T2]
proof(auto simp add: upl_der_def hp_snd_def)
  fix \<phi>' :: "'env \<Rightarrow> 't1 \<times> 't2 \<Rightarrow> bool"
  define fr :: "'t2 \<Rightarrow> 't1 \<times> 't2"
    where "fr \<equiv> (\<lambda>k2. (undefined,k2))"
  define \<psi> :: "'env \<Rightarrow> 't2 \<Rightarrow> bool"
    where "\<psi> \<equiv> (\<lambda>env t1. \<phi>' env (fr t1))"
  have hfr:"\<And>r'. snd \<circ> (fr \<circ> r') = r'"
    by(auto simp add: fr_def)
  assume h1:"(\<lambda>r. \<phi> (\<lambda>env. snd (r env))) = (\<lambda>t k. \<phi>' k (t k))"
  have "\<And>r' env. \<phi> r' env = \<phi>' env (fr (r' env))"
  proof -
    fix r' env
    have "\<phi> r' env = (\<lambda>r. \<phi> (\<lambda>env. snd (r env))) (fr \<circ> r') env"
      using hfr[of r'] by(auto simp add: comp_def)
    also have "... = (\<lambda>t k. \<phi>' k (t k)) (fr \<circ> r') env"
      by (metis h1)
    finally show "\<phi> r' env = \<phi>' env (fr (r' env))"
      by auto
  qed
  hence "\<phi> = (\<lambda>t k. \<psi> k (t k))"
    by(auto simp add: \<psi>_def)
  thus "\<exists>\<phi>''. \<phi> = (\<lambda>t k. \<phi>'' k (t k))"
    by auto
qed

(* \<Gamma> | \<Psi> \<turnstile>upl e1 : T1 | \<phi>1     \<Gamma> | \<Psi> \<turnstile>upl e2 : T2 | \<phi>2    \<Gamma> | \<Psi> \<turnstile>pl \<forall>x:T1, \<forall>y:T2, \<phi>1[x/r] \<longrightarrow> \<phi>2[y/r] \<longrightarrow> \<phi>[(x,y)/r]
  -----------------------------------------------------------------------------------------------------------------------
                                    \<Gamma> | \<Psi> \<turnstile>upl (e1,e2) : T1 \<times> T2 | \<phi>                                                    *)
lemma upl_pair:
  assumes "\<phi> = (\<lambda>r env. \<phi>' env (r env))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e1 ;; T1 | \<phi>1"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e2 ;; T2 | \<phi>2"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>P\<^sub>L \<forall>\<^sub>P\<^sub>Lx\<in>\<^sub>P\<^sub>LT1. \<forall>\<^sub>P\<^sub>Ly\<in>\<^sub>P\<^sub>LT2. \<phi>1 (hp_const x) \<longrightarrow>\<^sub>P\<^sub>L \<phi>2 (hp_const y) \<longrightarrow>\<^sub>P\<^sub>L \<phi> (hp_pair (hp_const x) (hp_const y))"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_pair e1 e2 ;; T1 \<Otimes>\<^sub>Q T2 | \<phi>"
  unfolding upl_der_def apply auto
  using assms(2,3) hpt_pair[of \<Gamma> e1 T1 e2 T2] apply(simp add: upl_der_def)
  using assms(1) apply auto[1]
proof -
  fix k
  assume h:"k \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> k"
  then have "\<phi>1 (hp_const (e1 k)) k" "\<phi>2 (hp_const (e2 k)) k"
    using assms(2,3) by(auto simp add: hp_const_def upl_der_def)
  moreover have "e1 k \<in> qbs_space T1" "e2 k \<in> qbs_space T2"
    using qbs_morphismE(1)[of e1 \<Gamma> T1] qbs_morphismE(1)[of e2 \<Gamma> T2] assms(2,3) h
    by(auto simp add: upl_der_def hpprog_typing_def)
  ultimately have "\<phi> (hp_pair (hp_const (e1 k)) (hp_const (e2 k))) k"
    using assms(2-4) h by(simp add: upl_der_def hp_definitions pl_der_def)
  thus "\<phi> (hp_pair e1 e2) k"
    by(simp add: assms(1) hp_definitions)
qed


(* \<Gamma> | \<Psi>, \<phi>'[0/n] |-upl t0 : T | \<phi>[0/n]    \<Gamma>, n : \<nat>, t : T | \<Psi>, \<phi>'[Suc n/n], \<phi>' \<longrightarrow> \<phi>[t/r], t = f n |-upl e : T | \<phi>[Suc n/n]
  -------------------------------------------------------------------------------------------------------------------
                    \<Gamma> | \<Psi> |-upl rec t0 (\<lambda>n t. e) : \<nat> \<Rightarrow> T | \<forall>n. \<phi>' \<longrightarrow> \<phi>[r n/r]                                     *)
lemma upl_recnat':
  assumes "\<Phi>0 = (\<lambda>\<psi>. (\<lambda>k. \<psi> (k,0))) `\<Phi>"
          "\<Phi>Sn = (\<lambda>\<psi>. (\<lambda>((k,n),_). \<psi> (k,Suc n))) `\<Phi>"
          "\<Phi>' = hp_conjall_fix \<Phi>"
          "\<Psi>' = (\<lambda>\<psi>. (\<lambda>((k,_),_). \<psi> k)) `\<Psi>"
          "\<phi>' = (\<lambda>fn ft k. \<phi> (hp_const (fn k)) (hp_const (ft k)) (fst (fst k)))"
          "IH = {(\<lambda>((k,n),t). hp_conjall \<Phi> (k,n) \<longrightarrow> \<phi> (hp_const n) (hp_const t) k)}"
          "\<And>n. \<exists>\<psi>n. \<phi> (hp_const n) = (\<lambda>r env. \<psi>n env (r env))"
          "fn = (\<lambda>envnt. hp_rec_nat t0 (hp_lambda (hp_lambda e)) (fst (fst envnt)))"
          "\<Gamma> | \<Psi> \<union> \<Phi>0 \<turnstile>\<^sub>U\<^sub>P\<^sub>L t0 ;; T | \<phi> (hp_const 0)"
     and  "\<Gamma> ,, \<nat>\<^sub>Q ,, T | \<Psi>' \<union> \<Phi>Sn \<union> IH \<union> {var1 =\<^sub>P\<^sub>L hp_app fn var2}  \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>' (hp_suc var2)"
   shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_rec_nat t0 (hp_lambda (hp_lambda e)) ;; (exp_qbs \<nat>\<^sub>Q T) | (\<lambda>r. \<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. \<Phi>' (hp_const n) \<longrightarrow>\<^sub>P\<^sub>L \<phi> (hp_const n) (hp_app r (hp_const n)))"
proof(auto simp add: upl_der_def)
  show "\<Gamma> \<turnstile>\<^sub>t hp_rec_nat t0 (hp_lambda (hp_lambda e)) ;; exp_qbs \<nat>\<^sub>Q T"
    using hpt_recnat'[of \<Gamma> t0 T e] assms(9,10)
    by(auto simp add: upl_der_def)
next
  have "\<forall>n. \<exists>\<psi>n. \<forall>r env. \<phi> (hp_const n) r env = \<psi>n env (r env)"
  proof
    fix n
    obtain \<psi>n where "\<phi> (hp_const n) = (\<lambda>r env. \<psi>n env (r env))"
      using assms(7)[of n] by auto
    thus "\<exists>\<psi>n. \<forall>r env. \<phi> (hp_const n) r env = \<psi>n env (r env)"
      by auto
  qed
  hence "\<exists>\<psi>. \<forall>n r env. \<phi> (hp_const n) r env = \<psi> n env (r env)"
    by(rule choice)
  then obtain \<psi> where hp:"\<forall>n r env. \<phi> (hp_const n) r env = \<psi> n env (r env)"
    by auto

  define \<psi>' where "\<psi>' \<equiv> (\<lambda>env t. \<forall>n\<in>qbs_space \<nat>\<^sub>Q. \<Phi>' (hp_const n) env \<longrightarrow> \<psi> n env (t n))"
  then have "(\<lambda>r. \<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. \<Phi>' (hp_const n) \<longrightarrow>\<^sub>P\<^sub>L \<phi> (hp_const n) (hp_app r (hp_const n))) = (\<lambda>t k. \<psi>' k (t k))"
    using hp by(auto simp add: hp_definitions)
  thus "\<exists>\<psi>'. (\<lambda>r. \<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. \<Phi>' (hp_const n) \<longrightarrow>\<^sub>P\<^sub>L \<phi> (hp_const n) (hp_app r (hp_const n))) = (\<lambda>t k. \<psi>' k (t k))"
    by auto
next
  fix k
  assume h:"k \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> k"
  show "(\<forall>\<^sub>P\<^sub>Ln\<in>\<^sub>P\<^sub>L\<nat>\<^sub>Q. \<Phi>' (hp_const n) \<longrightarrow>\<^sub>P\<^sub>L \<phi> (hp_const n) (hp_app (hp_rec_nat t0 (hp_lambda (hp_lambda e))) (hp_const n))) k"
  proof(auto simp add: hp_all_def hp_implies_def)
    fix n
    assume "\<Phi>' (hp_const n) k"
    then show "\<phi> (hp_const n) (hp_app (hp_rec_nat t0 (hp_lambda (hp_lambda e))) (hp_const n)) k"
    proof(induction n)
      case 0
      then show ?case
        using assms(1,3,9) h by(force simp add: upl_der_def hp_definitions hp_conjall_fix_def hp_conjall_def)
    next
      case ih:(Suc n)
      let ?f = "hp_rec_nat t0 (hp_lambda (hp_lambda e))"
      let ?env = "((k,n),?f k n)"
      have ht:"?f k n \<in> qbs_space T"
        using hpt_recnat'[of \<Gamma> t0 T e] h(1) qbs_morphismE(1)[of ?f \<Gamma> "exp_qbs \<nat>\<^sub>Q T"] qbs_morphismE(1)[of "?f k" "\<nat>\<^sub>Q" T] assms(10,9)
        by(auto simp add: upl_der_def hpprog_typing_def)
      hence "?env \<in> qbs_space (\<Gamma> ,, \<nat>\<^sub>Q ,, T)"
        by(simp add: h(1) hpprog_context_def)
      moreover have "hp_conjall \<Psi>' ?env"
        using h by(simp add: assms(4) hp_conjall_def)
      moreover have "hp_conjall \<Phi>Sn ?env"
        using assms(2,3) ih(2) by(simp add: hp_conjall_fix_def hp_conjall_def hp_const_def)
      moreover have "hp_conjall IH ?env"
      proof -
        have "(hp_app (hp_rec_nat t0 (hp_lambda (hp_lambda e))) (\<lambda>a. n)) k = hp_const (hp_rec_nat t0 (hp_lambda (hp_lambda e)) k n) k"
          by(simp add: hp_definitions)
        hence "\<phi> (hp_const n) (hp_app (hp_rec_nat t0 (hp_lambda (hp_lambda e))) (\<lambda>a. n)) k = \<phi> (hp_const n) (hp_const (hp_rec_nat t0 (hp_lambda (hp_lambda e)) k n)) k"
          using upl_phi_equiv1[of "\<phi> (hp_const n)" _ "hp_app (hp_rec_nat t0 (hp_lambda (hp_lambda e))) (\<lambda>a. n)" k "hp_const (hp_rec_nat t0 (hp_lambda (hp_lambda e)) k n)"] assms(7)[of n]
          by auto
        thus ?thesis
          using ih(1) assms(3)
          by(simp add: assms(6) hp_conjall_def hp_conjall_fix_def hp_const_def)
      qed
      moreover have "(var1 =\<^sub>P\<^sub>L hp_app fn var2) ?env"
        by(simp add: assms(8) hp_definitions)
      ultimately have "\<phi>' (hp_suc var2) e ?env"
        using assms(10) by(simp add: upl_der_def hp_conjall_union hp_conjall_def,blast)
      moreover have "\<phi>' (hp_suc var2) e ?env = \<phi> (hp_const (Suc n)) (hp_app ?f (hp_const (Suc n))) k"
                     (is "?lhs = ?rhs")
      proof -
        obtain \<psi> where hpsi:"\<phi> (hp_const (Suc n)) = (\<lambda>r env. \<psi> env (r env))"
          using assms(7)[of "Suc n"] by auto
        have "?lhs = \<phi> (hp_const (hp_suc var2 ((k, n), hp_rec_nat t0 (hp_lambda (hp_lambda e)) k n))) (hp_const (e ((k, n), ?f k n))) k"
          by(simp add: assms(5))
        also have "... =  \<phi> (hp_const (Suc n)) (hp_const (e ((k, n), hp_rec_nat t0 (hp_lambda (hp_lambda e)) k n))) k"
          by(simp add: hp_definitions)
        also have "... = \<phi> (hp_const (Suc n)) (hp_app (hp_app (hp_lambda (hp_lambda e)) (hp_const n)) (hp_app ?f (hp_const n))) k"
          apply(rule upl_phi_equiv1[of "\<phi> (hp_const (Suc n))"],simp_all add: hp_definitions)
          using hpsi by(auto simp add: hp_const_def)
        also have "... = ?rhs"
          by(simp add: hp_definitions)
        finally show ?thesis .
      qed
      ultimately show "\<phi> (hp_const (Suc n)) (hp_app (hp_rec_nat t0 (hp_lambda (hp_lambda e))) (hp_const (Suc n))) k"
        by simp
    qed
  qed
qed

(* \<Gamma> | \<Psi> \<turnstile>upl e : T | \<phi>1   \<Gamma> | \<Psi> \<turnstile>upl e : T | \<phi>2
  ------------------------------------------------
               \<Gamma> | \<Psi> \<turnstile>upl e : T | \<phi>1 \<and> \<phi>2       *)
lemma upl_andI:
  assumes "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>1"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>2"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T 
               | (\<lambda>r. \<phi>1 r \<and>\<^sub>P\<^sub>L \<phi>2 r)"
  using assms by(auto simp add: upl_der_def hp_and_def)


(* \<Gamma> | \<Psi>, \<phi>'[e/r] \<turnstile>upl e : T | \<phi>1
  --------------------------------
    \<Gamma> | \<Psi> \<turnstile>upl e : T | \<phi>' \<longrightarrow> \<phi>1 *)
lemma upl_impI:
  assumes "\<Gamma> | \<Psi> \<union> \<Phi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<phi>1"
    shows "\<Gamma> | \<Psi>  \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | (\<lambda>r. hp_conjall \<Phi> \<longrightarrow>\<^sub>P\<^sub>L \<phi>1 r)"
proof(auto simp add: upl_der_def hp_implies_def)
  show "\<Gamma> \<turnstile>\<^sub>t e ;; T"
    using assms by(simp add: upl_der_def)
next
  obtain \<phi>1' where 1:"\<phi>1 = (\<lambda>r env. \<phi>1' env (r env))"
    using assms by(auto simp add: upl_der_def)
  show "\<exists>\<phi>'. (\<lambda>r env. hp_conjall \<Phi> env \<longrightarrow> \<phi>1 r env) = (\<lambda>t k. \<phi>' k (t k))"
    by(rule exI[where x="\<lambda>env x. hp_conjall \<Phi> env \<longrightarrow> \<phi>1' env x"],simp add: 1)
next
  fix k
  assume "k \<in> qbs_space \<Gamma>"
         "hp_conjall \<Psi> k"
         "hp_conjall \<Phi> k"
  then show "\<phi>1 e k"
    using assms
    by(simp add: hp_conjall_def upl_der_def,blast)
qed

(* \<Gamma> | \<Psi> \<turnstile>upl e : T | \<phi>[return r/r]
  ----------------------------------
         \<Gamma> | \<Psi> \<turnstile>upl e : P[T] | \<phi>     *)
lemma upl_return:
  assumes "\<phi> = (\<lambda>t k. \<phi>' k (t k))"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; T | \<lambda>r. \<phi> (hp_return T r)"
  shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L hp_return T e ;; monadP_qbs T | \<phi>"
  using assms hpt_return[of \<Gamma> e T] by(auto simp add: upl_der_def hp_return_def)

(* \<Gamma> | \<Psi> \<turnstile>upl e : P[T1] | \<phi>1     \<Gamma> | \<Psi> \<turnstile>upl f : T1 \<Rightarrow> P[T2] | \<forall>s:P[T1]. \<phi>1[s/r] \<longrightarrow> \<phi>2[bind s r/r]
  --------------------------------------------------------------------------------------------------
                              \<Gamma> | \<Psi> \<turnstile>upl bind e f : P[T2] | \<phi>2                                    *)
lemma upl_bind:
  assumes "\<phi>2 = (\<lambda>r env. \<psi>' env (r env))"
          "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L e ;; monadP_qbs T1 | \<phi>1"
      and "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L f ;; exp_qbs T1 (monadP_qbs T2) | \<lambda>r. \<forall>\<^sub>P\<^sub>Ls\<in>\<^sub>P\<^sub>LmonadP_qbs T1. \<phi>1 (hp_const s) \<longrightarrow>\<^sub>P\<^sub>L \<phi>2 (hp_const s \<bind> r)"
    shows "\<Gamma> | \<Psi> \<turnstile>\<^sub>U\<^sub>P\<^sub>L  e \<bind> f ;; monadP_qbs T2 | \<phi>2"
proof(auto simp add: upl_der_def)
  show "\<Gamma> \<turnstile>\<^sub>t e \<bind> f ;; monadP_qbs T2"
    using assms(2,3) hpt_bind[of \<Gamma> e T1 f T2]
    by(simp add: upl_der_def)
next
  show "\<exists>\<phi>'. \<phi>2 = (\<lambda>t k. \<phi>' k (t k))"
    using assms(1) by auto
next
  fix k
  assume h:"k \<in> qbs_space \<Gamma>"
           "hp_conjall \<Psi> k "
  then have "e k \<in> qbs_space (monadP_qbs T1)"
    using assms(2) qbs_morphismE(1)[of e \<Gamma> "monadP_qbs T1"]
    by(auto simp add: upl_der_def hpprog_typing_def)
  moreover have "\<phi>1 (hp_const (e k)) k"
    using upl_phi_const[of \<phi>1 _ e k] assms(2) h
    by(auto simp add: upl_der_def)
  ultimately have "\<phi>2 (hp_const (e k) \<bind> f) k"
    using assms(3) h by(simp add: upl_der_def hp_implies_def hp_all_def)
  moreover have "(\<phi>2 (hp_const (e k) \<bind> f) k) = (\<phi>2 (e \<bind> f) k)"
    using assms(1) by(simp add: hp_const_def hp_bind_def)
  ultimately show "\<phi>2 (e \<bind> f) k"
    by simp
qed

end