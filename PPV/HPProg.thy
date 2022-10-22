(*  Title:   HPProg.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology

*)
section \<open> Formalization of PPV \<close>

text \<open> We formalize PPV(Probabilistic Programming Verification framework)~\cite{Sato_2019}.\<close>

subsection \<open> Language: HPProg \<close>

theory HPProg
  imports "../Quasi_Borel_Spaces/Measure_as_QuasiBorel_Measure"
begin

definition hpprog_typing :: "['cont quasi_borel, 'cont \<Rightarrow> 'typ, 'typ quasi_borel] \<Rightarrow> bool" where
"hpprog_typing \<Gamma> e T \<equiv> e \<in> \<Gamma> \<rightarrow>\<^sub>Q T"

syntax
 "_hpprog_typing" :: "any \<Rightarrow> 'cont quasi_borel \<Rightarrow> ('cont \<Rightarrow> 'typ) \<Rightarrow> 'typ quasi_borel \<Rightarrow> bool" ("_ \<turnstile>\<^sub>t _ ;; _" 60)

translations
 "\<Gamma> \<turnstile>\<^sub>t e ;; T" \<rightleftharpoons> "CONST hpprog_typing \<Gamma> e T"

definition hpprog_context :: "['a quasi_borel,'b quasi_borel] \<Rightarrow> ('a \<times> 'b) quasi_borel" (infixl ",," 78)  where
"hpprog_context \<equiv> pair_qbs"

definition empty_context :: "unit quasi_borel" ("\<emptyset>\<^sub>C") where
"empty_context \<equiv> unit_quasi_borel"

abbreviation monadP_qbs_type ("P\<^sub>t") where "monadP_qbs_type \<equiv> monadP_qbs"

declare empty_context_def[simplified]

definition unit_x :: "'a quasi_borel \<Rightarrow> (unit \<times> 'a) quasi_borel" (",_" [79] 79)where
"unit_x X \<equiv> unit_quasi_borel \<Otimes>\<^sub>Q X"

lemma hp_unit_context[simp] :
 ",X = unit_quasi_borel ,, X"
  by(simp add: unit_x_def hpprog_context_def)

definition hp_lift :: "['a \<Rightarrow> 'b, 'cont \<Rightarrow> 'a] \<Rightarrow> 'cont \<Rightarrow> 'b" where
"hp_lift f x \<equiv> (\<lambda>env. f (x env))"
definition hp_lift2 :: "['a \<Rightarrow> 'b \<Rightarrow> 'c, 'cont \<Rightarrow> 'a, 'cont \<Rightarrow> 'b] \<Rightarrow> 'cont \<Rightarrow> 'c" where
"hp_lift2 f x y \<equiv> (\<lambda>env. f (x env) (y env))"

declare hp_lift_def[simp]
declare hp_lift2_def[simp]


lemma hpt_addcont:
  assumes "t' = (\<lambda>(env,x). t env)"
      and "\<Gamma> \<turnstile>\<^sub>t t ;; T"
    shows "\<Gamma>,,X \<turnstile>\<^sub>t t' ;; T"
  using qbs_morphism_fst''[OF assms(2)[simplified hpprog_typing_def],of X]
  by(simp add: assms(1) hpprog_typing_def hpprog_context_def split_beta')

subsubsection \<open> Variables \<close>
definition var1 :: "'a \<times> 'b \<Rightarrow> 'b" where
"var1 \<equiv> snd"

definition var2 :: "('a \<times> 'b) \<times> 'c \<Rightarrow> 'b" where
"var2 \<equiv> snd \<circ> fst"

definition var3 :: "(('a \<times> 'b) \<times> 'c) \<times> 'd \<Rightarrow> 'b" where
"var3 \<equiv> snd \<circ> fst \<circ> fst"

definition var4 :: "((('a \<times> 'b) \<times> 'c) \<times> 'd) \<times> 'e \<Rightarrow> 'b" where
"var4 \<equiv> snd \<circ> fst \<circ> fst \<circ> fst"

definition var5 :: "(((('a \<times> 'b) \<times> 'c) \<times> 'd) \<times> 'e) \<times> 'f \<Rightarrow> 'b" where
"var5 \<equiv> snd \<circ> fst \<circ> fst \<circ> fst \<circ> fst"

definition var6 :: "((((('a \<times> 'b) \<times> 'c) \<times> 'd) \<times> 'e) \<times> 'f) \<times> 'g  \<Rightarrow> 'b" where
"var6 = snd \<circ> fst \<circ> fst \<circ> fst \<circ> fst \<circ> fst"

definition var7 :: "(((((('a \<times> 'b) \<times> 'c) \<times> 'd) \<times> 'e) \<times> 'f) \<times> 'g) \<times> 'h  \<Rightarrow> 'b" where
"var7 = snd \<circ> fst \<circ> fst \<circ> fst \<circ> fst \<circ> fst \<circ> fst"

lemma hpt_var1:
 "\<Gamma>,,Z  \<turnstile>\<^sub>t var1 ;; Z"
  using snd_qbs_morphism
  by(auto simp add: hpprog_typing_def hpprog_context_def var1_def)

lemma hpt_var2:
 "\<Gamma>,,Z,,Y \<turnstile>\<^sub>t var2 ;; Z"
  unfolding var2_def hpprog_typing_def hpprog_context_def
  using qbs_morphism_comp[OF fst_qbs_morphism snd_qbs_morphism]
  by auto

lemma hpt_var3:
 "\<Gamma>,,Z,,Y,,X \<turnstile>\<^sub>t var3 ;; Z"
  unfolding var3_def hpprog_typing_def hpprog_context_def
  using qbs_morphism_comp[OF fst_qbs_morphism qbs_morphism_comp[OF fst_qbs_morphism snd_qbs_morphism]]
  by auto

lemma hpt_var4:
 "\<Gamma>,,Z,,Y,,X,,W \<turnstile>\<^sub>t var4 ;; Z"
  unfolding var4_def hpprog_typing_def hpprog_context_def
  by (meson fst_qbs_morphism qbs_morphism_comp snd_qbs_morphism)

lemma hpt_var5:
 "\<Gamma>,,Z,,Y,,X,,W,,V \<turnstile>\<^sub>t var5 ;; Z"
  unfolding var5_def hpprog_typing_def hpprog_context_def
  by (meson fst_qbs_morphism qbs_morphism_comp snd_qbs_morphism)

lemma hpt_var6:
 "\<Gamma>,,Z,,Y,,X,,W,,V,,U \<turnstile>\<^sub>t var6 ;; Z"
  unfolding var6_def hpprog_typing_def hpprog_context_def
  by (meson fst_qbs_morphism qbs_morphism_comp snd_qbs_morphism)

lemma hpt_var7:
 "\<Gamma>,,Z,,Y,,X,,W,,V,,U,,T \<turnstile>\<^sub>t var7 ;; Z"
  unfolding var7_def hpprog_typing_def hpprog_context_def
  by (meson fst_qbs_morphism qbs_morphism_comp snd_qbs_morphism)


definition "hp_context \<equiv> fst"


subsubsection \<open> Constants \<close>
definition hp_const :: "'a \<Rightarrow> 'env \<Rightarrow> 'a" where
"hp_const k \<equiv> (\<lambda>env. k)"

(*
  --------------------
       \<Gamma> |- n : \<nat>     *)
lemma hpt_natc:
  "\<Gamma> \<turnstile>\<^sub>t (hp_const (n :: nat)) ;; \<nat>\<^sub>Q"
  using qbs_morphism_const[of n nat_quasi_borel \<Gamma>]
  by(simp add: hpprog_typing_def hp_const_def)

(*
  --------------------
      \<Gamma> |- r : \<real>     *)
lemma hpt_realc:
  "\<Gamma> \<turnstile>\<^sub>t (hp_const (r :: real)) ;; \<real>\<^sub>Q"
  using qbs_morphism_const[of r "\<real>\<^sub>Q" \<Gamma>]
  by(simp add: hpprog_typing_def hp_const_def)

(*
  ----------------------
      \<Gamma> |- r : ennreal *)
lemma hpt_ennrealc:
  "\<Gamma> \<turnstile>\<^sub>t (hp_const (r :: ennreal)) ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  using qbs_morphism_const[of r ennreal_quasi_borel \<Gamma>]
  by(simp add: hpprog_typing_def hp_const_def)

(*
  ---------------------
      \<Gamma> |- () : unit  *)
lemma hpt_unitc:
  "\<Gamma> \<turnstile>\<^sub>t (hp_const ()) ;; unit_quasi_borel"
  using to_unit_quasi_borel_morphism[of \<Gamma>]
  by(simp add: hpprog_typing_def hp_const_def to_unit_quasi_borel_def)

definition "hp_constf \<equiv> hp_lift hp_const"
(*       \<Gamma> |- t : Y
   ----------------------(x \<notin> t)
     \<Gamma> |- \<lambda>x. t : X \<Rightarrow> Y       *)
lemma hpt_constf:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; Y"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_constf t ;; exp_qbs X Y"
proof -
  have 1:"case_prod (hp_constf t) = t \<circ> fst"
    by(auto simp add: hp_constf_def hp_const_def)
  have "case_prod (hp_constf t) \<in> \<Gamma> \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>QY"
    using qbs_morphism_comp[of fst "\<Gamma> \<Otimes>\<^sub>Q X" \<Gamma> t Y] assms fst_qbs_morphism[of \<Gamma> X]
    by(simp add: hpprog_typing_def 1)
  thus ?thesis
    using curry_preserves_morphisms[of "case_prod (hp_constf t)" \<Gamma> X Y]
    by(simp add: hpprog_typing_def)
qed


subsubsection \<open> Lambda Abstraction \<close>
definition hp_lambda ("\<lambda>\<^sub>t")
  where "hp_lambda \<equiv> curry"

(*   x : X, \<Gamma> |- t : T
   -----------------------
    \<Gamma> |- (\<lambda>x. t) : X \<Rightarrow> T *)
lemma hpt_abs:
  assumes "\<Gamma>,,X \<turnstile>\<^sub>t t ;; T"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_lambda t ;; X \<Rightarrow>\<^sub>Q T"
  using curry_preserves_morphisms[of t] assms
  by(simp add: hpprog_typing_def hpprog_context_def hp_lambda_def)


subsubsection \<open> Function Application \<close>
definition hp_app :: "['cont \<Rightarrow> 'a \<Rightarrow> 'b, 'cont \<Rightarrow> 'a] \<Rightarrow> 'cont \<Rightarrow> 'b" (infixr "$\<^sub>t" 1) where
"hp_app f x \<equiv> qbs_eval \<circ> (\<lambda>env. (f env,x env))" 

(* \<Gamma> |- f : T1 \<Rightarrow> T2   \<Gamma> |- x : T1  
   --------------------------------- 
           \<Gamma> |- f x : T2            *)
lemma hpt_app:
  assumes "\<Gamma> \<turnstile>\<^sub>t f ;; (exp_qbs X Y)"
      and "\<Gamma> \<turnstile>\<^sub>t x ;; X"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_app f x ;; Y"
  unfolding hp_app_def hpprog_typing_def
  by(rule qbs_morphism_comp[OF qbs_morphism_tuple[OF assms[simplified hpprog_typing_def]] qbs_eval_morphism])


subsubsection \<open> Pair \<close>
definition "hp_pair \<equiv> hp_lift2 Pair"

(* \<Gamma> |- t1 : X    \<Gamma> |- t2 Y 
  ---------------------------
     \<Gamma> |- (t1,t2) : X \<times> Y  *)
lemma hpt_pair:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; X"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; Y"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_pair t1 t2 ;; X \<Otimes>\<^sub>Q Y"
  using assms qbs_morphism_tuple[of t1 \<Gamma> X t2 Y]
  by(simp add: hpprog_typing_def hp_pair_def)


subsubsection \<open> Projections \<close>
definition "hp_fst \<equiv> hp_lift fst"
definition "hp_snd \<equiv> hp_lift snd"

(*  \<Gamma> |- s : X \<times> Y
  ------------------
    \<Gamma> |- fst s : X *)
lemma hpt_fst:
  assumes "\<Gamma> \<turnstile>\<^sub>t s ;; X \<Otimes>\<^sub>Q Y"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_fst s ;; X"
  using assms fst_qbs_morphism qbs_morphism_comp[of s \<Gamma> _ fst X]
  by(auto simp: hp_fst_def hpprog_typing_def o_def)

(*  \<Gamma> |- s : X \<times> Y
   ------------------
    \<Gamma> |- snd s : X  *)
lemma hpt_snd:
  assumes "\<Gamma> \<turnstile>\<^sub>t s ;; X \<Otimes>\<^sub>Q Y"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_snd s ;; Y"
  using assms snd_qbs_morphism qbs_morphism_comp[of s \<Gamma> "X \<Otimes>\<^sub>Q Y" snd Y]
  by(auto simp: hp_snd_def hpprog_typing_def o_def)


subsubsection \<open> Copair \<close>
definition "hp_inl \<equiv> hp_lift Inl"
definition "hp_inr \<equiv> hp_lift Inr"

(*      \<Gamma> |- t : X 
   ---------------------
     \<Gamma> |- inl t : X + Y *)
lemma hpt_inl:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; X"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_inl t ;; X <+>\<^sub>Q Y"
  using assms Inl_qbs_morphism[of X Y] qbs_morphism_comp[of t \<Gamma> X Inl]
  by(auto simp: hp_inl_def hpprog_typing_def o_def)

(*      \<Gamma> |- t : X 
   ---------------------
     \<Gamma> |- inr t : X + Y *)
lemma hpt_inr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; Y"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_inr t ;; X <+>\<^sub>Q Y"
  using assms qbs_morphism_comp[OF _ Inr_qbs_morphism[of Y X]]
  by(auto simp: hp_inr_def hpprog_typing_def comp_def)


subsubsection \<open> Cases \<close>
definition hp_case :: "[ 'cont \<Rightarrow> 'a + 'b, 'cont \<times> 'a \<Rightarrow> 'c, 'cont \<times> 'b \<Rightarrow> 'c] \<Rightarrow> 'cont \<Rightarrow> 'c" where
"hp_case t t1 t2 \<equiv> (\<lambda>env. case_sum (curry t1 env) (curry t2 env) (t env))"

(* \<Gamma> |- t : X + Y    x : X, \<Gamma> |- t1 : Z   y ; Y, \<Gamma> |- t2 : Z  
   ------------------------------------------------------------
         \<Gamma> |- case t with
              | inl x \<Rightarrow> t1
              | inr y \<Rightarrow> t2 : Z                                 *)
lemma hpt_case:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; X <+>\<^sub>Q Y"
          "\<Gamma>,,X \<turnstile>\<^sub>t t1 ;; Z"
      and "\<Gamma>,,Y \<turnstile>\<^sub>t t2 ;; Z"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_case t t1 t2 ;; Z"
proof -
  have "(\<lambda>env. case_sum (curry t1 env) (curry t2 env) (t env)) = case_prod (case_prod case_sum) \<circ> (\<lambda>env. ((curry t1 env,curry t2 env),t env))"
    by auto
  also have "... \<in> \<Gamma> \<rightarrow>\<^sub>Q Z"
    using assms
    by(auto intro!: qbs_morphism_comp[where Y="(exp_qbs X Z \<Otimes>\<^sub>Q exp_qbs Y Z) \<Otimes>\<^sub>Q (X <+>\<^sub>Q Y)"] qbs_morphism_tuple curry_preserves_morphisms uncurry_preserves_morphisms case_sum_morphism
              simp: hpprog_typing_def hpprog_context_def)
  finally show ?thesis
    by(simp add: hp_case_def hpprog_typing_def)
qed

subsubsection \<open> List \<close>
abbreviation "list \<equiv> list_qbs"
definition hp_nil :: "'env \<Rightarrow> 'a list" ("[]\<^sub>t") where
"hp_nil \<equiv> hp_const []"

lemma hpt_nil:
 "\<Gamma> \<turnstile>\<^sub>t hp_nil ;; list X"
  unfolding hp_nil_def hpprog_typing_def hp_const_def
  by(auto intro!: qbs_morphismI qbs_closed2_dest simp: list_qbs_space)

definition hp_cons' :: "['env, 'a, 'a list] \<Rightarrow> 'a list" where
"hp_cons' \<equiv> hp_const Cons"

lemma hpt_cons':
 "\<Gamma> \<turnstile>\<^sub>t hp_cons' ;; exp_qbs X (exp_qbs (list X) (list X))"
  unfolding hpprog_typing_def hp_cons'_def hp_const_def
  by(rule qbs_morphism_const,simp add: cons_qbs_morphism)

definition "hp_cons hx hl \<equiv> hp_app (hp_app hp_cons' hx) hl"
lemma hpt_cons:
  assumes "\<Gamma> \<turnstile>\<^sub>t l ;; list X"
      and "\<Gamma> \<turnstile>\<^sub>t x ;; X"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_cons x l ;; list X"
  unfolding hp_cons_def
  apply(rule hpt_app)+
    apply(rule hpt_cons')
   apply fact+
  done

syntax
  "_hp_list" :: "args => 'env \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)"    ("[(_)]\<^sub>t")

translations
  "[x, xs]\<^sub>t" == "CONST hp_cons x [xs]\<^sub>t"
  "[x]\<^sub>t" == "CONST hp_cons x []\<^sub>t"

lemma
  "\<Gamma>,,\<real>\<^sub>Q,,\<real>\<^sub>Q \<turnstile>\<^sub>t [var1, hp_const 1, var2]\<^sub>t ;; list \<real>\<^sub>Q"
  apply(rule hpt_cons)+
     apply(rule hpt_nil)
    apply(rule hpt_var2)
   apply(rule hpt_realc)
  apply(rule hpt_var1)
  done


subsubsection \<open> Return \<close>
definition hp_return :: "[ 'a quasi_borel,'cont \<Rightarrow> 'a] \<Rightarrow> 'cont \<Rightarrow> 'a qbs_prob_space" where
"hp_return X t \<equiv> (\<lambda>env. qbs_return X (t env))"

(*        \<Gamma> |- t : T
   -------------------------
      \<Gamma> |- return T t : P T *)
lemma hpt_return:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; T"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_return T t ;; (monadP_qbs T)"
  using assms qbs_return_morphism[of T] qbs_morphism_comp[of t \<Gamma> T "qbs_return T" "monadP_qbs T"]
  by(simp add: hpprog_typing_def o_def hp_return_def)


subsubsection \<open> Bind \<close>
definition hp_bind (infixl "\<bind>\<^sub>t" 54) where "hp_bind \<equiv> hp_lift2 qbs_bind"

adhoc_overloading Monad_Syntax.bind hp_bind

(*  \<Gamma> |- s : P T1     \<Gamma> |- f : T1 \<Rightarrow> P T2
    --------------------------------------
           \<Gamma> |- s \<bind> f : P T2            *)
lemma hpt_bind:
 assumes "\<Gamma> \<turnstile>\<^sub>t s ;; (monadP_qbs T1)"
     and "\<Gamma> \<turnstile>\<^sub>t f ;; (exp_qbs T1 (monadP_qbs T2))"
    shows "\<Gamma> \<turnstile>\<^sub>t s \<bind>\<^sub>t f ;; (monadP_qbs T2)"
  using qbs_bind_morphism[of s \<Gamma> T1] assms
  by (simp add: hpprog_typing_def hp_bind_def)


subsubsection \<open> Normal Distribution \<close>
definition "hp_normal' \<equiv> hp_const qbs_normal_distribution"
definition "hp_normal \<equiv> (\<lambda>\<mu> \<sigma>. hp_app (hp_app hp_normal' \<mu>) \<sigma>)"
lemma hpt_normal':
  "\<Gamma> \<turnstile>\<^sub>t hp_normal' ;; exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q (monadP_qbs \<real>\<^sub>Q))"
  using qbs_morphism_const[of qbs_normal_distribution "exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q (monadP_qbs \<real>\<^sub>Q))" \<Gamma>]
  by(simp add: hp_normal'_def hpprog_typing_def hp_const_def qbs_normal_distribution_morphism)

lemma hpt_normal:
  assumes "\<Gamma> \<turnstile>\<^sub>t \<mu> ;; \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t \<sigma> ;; \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_normal \<mu> \<sigma> ;; monadP_qbs \<real>\<^sub>Q"
  unfolding hp_normal_def
  apply(rule hpt_app,rule hpt_app,rule hpt_normal')
  by fact+

subsubsection \<open> Uniform Distribution \<close>
definition "hp_uniform' \<equiv> hp_const qbs_interval_uniform_distribution"
definition "hp_uniform \<equiv> (\<lambda>a b. hp_app (hp_app hp_uniform' a) b)"
lemma hpt_uniform':
  "\<Gamma> \<turnstile>\<^sub>t hp_uniform' ;; exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q (monadP_qbs \<real>\<^sub>Q))"
  unfolding hp_uniform'_def hp_const_def hpprog_typing_def
  using qbs_morphism_const[of qbs_interval_uniform_distribution "exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q (monadP_qbs \<real>\<^sub>Q))" \<Gamma>] qbs_interval_uniform_distribution_morphism
  by simp

lemma hpt_uniform:
  assumes "\<Gamma> \<turnstile>\<^sub>t a ;; \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t b ;; \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_uniform a b ;; monadP_qbs \<real>\<^sub>Q"
  unfolding hp_uniform_def
  apply(rule hpt_app,rule hpt_app,rule hpt_uniform')
  by fact+

subsubsection \<open>Bernoulli Distribution\<close>
definition "hp_bernoulli' \<equiv> hp_const qbs_bernoulli"
definition "hp_bernoulli \<equiv> (\<lambda>x. hp_app hp_bernoulli' x)"
lemma hpt_bernoulli':
  "\<Gamma> \<turnstile>\<^sub>t hp_bernoulli' ;; exp_qbs \<real>\<^sub>Q (monadP_qbs \<bool>\<^sub>Q)"
  using qbs_morphism_const[of qbs_bernoulli " exp_qbs \<real>\<^sub>Q (monadP_qbs \<bool>\<^sub>Q)"]
  by(auto simp add: hp_bernoulli'_def hpprog_typing_def hp_const_def qbs_bernoulli_morphism)

lemma hpt_bernoulli:
  assumes "\<Gamma> \<turnstile>\<^sub>t r ;; \<real>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_bernoulli r ;; monadP_qbs \<bool>\<^sub>Q"
  unfolding hp_bernoulli_def
  by(rule hpt_app,rule hpt_bernoulli',fact)

subsubsection \<open> Numeral Functions \<close>

definition "hp_suc' \<equiv> hp_const Suc"
definition "hp_suc \<equiv> hp_app hp_suc'"

definition "hp_real' \<equiv> hp_const real"
definition "hp_real \<equiv> hp_app hp_real'"

definition "hp_enn2real' \<equiv> hp_const enn2real"
definition "hp_enn2real \<equiv> hp_app hp_enn2real'"

definition "hp_abs' \<equiv> hp_const abs"
definition hp_abs :: "('cont \<Rightarrow> 'b::abs) \<Rightarrow> 'cont \<Rightarrow> 'b" ("\<bar>_\<bar>\<^sub>t") where
"hp_abs \<equiv> hp_app hp_abs'"

definition "hp_ennreal' \<equiv> hp_const ennreal"
definition "hp_ennreal \<equiv> hp_app hp_ennreal'"

consts
  hp_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+\<^sub>t" 65)
consts
  hp_minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-\<^sub>t" 65)
consts
  hp_uminus :: "'a \<Rightarrow> 'a"  ("-\<^sub>t _" [81] 80)
consts
  hp_times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*\<^sub>t" 70)
consts
  hp_div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "'/\<^sub>t" 70)

definition "hp_plus'' \<equiv> hp_const plus"
definition "hp_plus' x y \<equiv> (hp_app (hp_app hp_plus'' x) y)"

definition "hp_minus'' \<equiv> hp_const minus"
definition "hp_minus' x y \<equiv> (hp_app (hp_app hp_minus'' x) y)"

definition "hp_uminus'' \<equiv> hp_const uminus"
definition "hp_uminus' \<equiv> hp_app hp_uminus''"

definition "hp_times'' \<equiv> hp_const times"
definition "hp_times' x y \<equiv> hp_app (hp_app hp_times'' x) y"

definition "hp_div'' \<equiv> hp_const inverse_divide"
definition "hp_div' x y \<equiv> hp_app (hp_app hp_div'' x) y"

definition "hp_power'' \<equiv> hp_const power"

fun hp_power' :: "['env \<Rightarrow> ('a :: monoid_mult), nat] \<Rightarrow> 'env \<Rightarrow> 'a" (infixr "^\<^sup>t" 80) where
"hp_power' hn 0       = hp_const 1" |
"hp_power' hn (Suc n) = hp_times' hn (hp_power' hn n)"

definition "hp_funplus' \<equiv> hp_lift2 hp_plus'"
definition "hp_funtimes' \<equiv> hp_lift2 hp_times'"
definition "hp_fundiv' \<equiv> hp_lift2 hp_div'"

adhoc_overloading hp_plus hp_plus'
adhoc_overloading hp_plus hp_funplus'
adhoc_overloading hp_minus hp_minus'
adhoc_overloading hp_uminus hp_uminus'
adhoc_overloading hp_times hp_times'
adhoc_overloading hp_times hp_funtimes'
adhoc_overloading hp_div hp_div'
adhoc_overloading hp_div hp_fundiv'

lemma hp_power_one:
 "t^\<^sup>t1 = t"
  by(simp add: hp_times'_def hp_const_def hp_app_def qbs_eval_def hp_times''_def comp_def)

lemma hp_power_square:
 "t^\<^sup>t2 = t *\<^sub>t t"
  by(simp add: hp_times'_def numeral_2_eq_2 hp_const_def  hp_app_def qbs_eval_def hp_times''_def comp_def)

lemma hpt_suc':
  "\<Gamma> \<turnstile>\<^sub>t hp_suc' ;; exp_qbs \<nat>\<^sub>Q \<nat>\<^sub>Q"
  unfolding hp_suc'_def hpprog_typing_def hp_const_def
  by(rule qbs_morphism_const,simp add: nat_qbs_morphism)

lemma hpt_suc:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<nat>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_suc t ;; \<nat>\<^sub>Q"
  unfolding hp_suc_def
  by(rule hpt_app,rule hpt_suc',fact)

lemma hpt_plusn':
 "\<Gamma> \<turnstile>\<^sub>t hp_plus'' ;; exp_qbs \<nat>\<^sub>Q (exp_qbs \<nat>\<^sub>Q \<nat>\<^sub>Q)"
  unfolding hp_plus''_def hpprog_typing_def hp_const_def
  apply(rule qbs_morphism_const,simp)
  apply(rule nat_qbs_morphism,simp)
  apply(rule nat_qbs_morphism,simp)
  done

lemma hpt_plusn:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<nat>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<nat>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 +\<^sub>t t2 ;; \<nat>\<^sub>Q"
  unfolding hp_plus'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_plusn')
  by fact+

lemma hpt_minusn':
 "\<Gamma> \<turnstile>\<^sub>t hp_minus'' ;; exp_qbs \<nat>\<^sub>Q (exp_qbs \<nat>\<^sub>Q \<nat>\<^sub>Q)"
  unfolding hp_minus''_def hpprog_typing_def hp_const_def
  apply(rule qbs_morphism_const,simp)
  apply(rule nat_qbs_morphism,simp)
  apply(rule nat_qbs_morphism,simp)
  done

lemma hpt_minusn:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<nat>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<nat>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 -\<^sub>t t2 ;; \<nat>\<^sub>Q"
  unfolding hp_minus'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_minusn')
  by fact+

lemma hpt_timesn':
 "\<Gamma> \<turnstile>\<^sub>t hp_times'' ;; exp_qbs \<nat>\<^sub>Q (exp_qbs \<nat>\<^sub>Q \<nat>\<^sub>Q)"
  unfolding hp_times''_def hpprog_typing_def hp_const_def
  apply(rule qbs_morphism_const,simp)
  apply(rule nat_qbs_morphism,simp)
  apply(rule nat_qbs_morphism,simp)
  done

lemma hpt_timesn:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<nat>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<nat>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 *\<^sub>t t2 ;; \<nat>\<^sub>Q"
  unfolding hp_times'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_timesn')
  by fact+

lemma hpt_powern:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<nat>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t t^\<^sup>t n ;; \<nat>\<^sub>Q"
  by(induction n; simp add: hpt_natc hpt_timesn assms)

lemma hpt_real':
 "\<Gamma> \<turnstile>\<^sub>t hp_real' ;; exp_qbs \<nat>\<^sub>Q \<real>\<^sub>Q"
  unfolding hp_real'_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule nat_qbs_morphism,simp)
  done

lemma hpt_real:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<nat>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_real t ;; \<real>\<^sub>Q"
  unfolding hp_real_def
  apply(rule hpt_app,rule hpt_real')
  by fact

lemma hpt_ennreal':
 "\<Gamma> \<turnstile>\<^sub>t hp_ennreal' ;; exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  unfolding hp_ennreal'_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const)
  by auto

lemma hpt_ennreal:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<real>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_ennreal t ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  unfolding hp_ennreal_def
  apply(rule hpt_app,rule hpt_ennreal')
  by fact

lemma hpt_absr':
 "\<Gamma> \<turnstile>\<^sub>t hp_abs' ;; exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q"
  unfolding hp_abs'_def hpprog_typing_def hp_const_def
  apply(rule qbs_morphism_const)
  by auto

lemma hpt_absr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<real>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t \<bar>t\<bar>\<^sub>t ;; \<real>\<^sub>Q"
  unfolding hp_abs_def
  apply(rule hpt_app,rule hpt_absr')
  by fact

lemma hpt_plusr':
  "\<Gamma> \<turnstile>\<^sub>t hp_plus'' ;; exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)"
  unfolding hp_plus''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (+)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_plusr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 +\<^sub>t t2 ;; \<real>\<^sub>Q"
  unfolding hp_plus'_def
  apply(rule hpt_app,rule hpt_app, rule hpt_plusr')
  by fact+

lemma hpt_minusr':
  "\<Gamma> \<turnstile>\<^sub>t hp_minus'' ;; exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)"
  unfolding hp_minus''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (-)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_minusr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 -\<^sub>t t2 ;; \<real>\<^sub>Q"
  unfolding hp_minus'_def
  apply(rule hpt_app,rule hpt_app, rule hpt_minusr')
  by fact+

lemma hpt_uminusr':
  "\<Gamma> \<turnstile>\<^sub>t hp_uminus'' ;; exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q"
  unfolding hp_uminus''_def hpprog_typing_def hp_const_def
  apply(rule qbs_morphism_const)
  by auto

lemma hp_uminusr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<real>\<^sub>Q"
  shows"\<Gamma> \<turnstile>\<^sub>t -\<^sub>t t ;; \<real>\<^sub>Q"
  unfolding hp_uminus'_def
  apply(rule hpt_app,rule hpt_uminusr')
  by fact

lemma hpt_timesr':
  "\<Gamma> \<turnstile>\<^sub>t hp_times'' ;; exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)"
  unfolding hp_times''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (*)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_timesr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 *\<^sub>t t2 ;; \<real>\<^sub>Q"
  unfolding hp_times'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_timesr')
  by fact+

lemma hpt_divr':
  "\<Gamma> \<turnstile>\<^sub>t hp_div'' ;; exp_qbs \<real>\<^sub>Q (exp_qbs \<real>\<^sub>Q \<real>\<^sub>Q)"
  unfolding hp_div''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (/)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_divr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 /\<^sub>t t2 ;; \<real>\<^sub>Q"
  unfolding hp_div'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_divr')
  by fact+

lemma hpt_powerr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<real>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t t^\<^sup>tn ;; \<real>\<^sub>Q"
  by(induction n; simp add: hpt_realc assms hpt_timesr)

lemma hpt_enn2real':
  "\<Gamma> \<turnstile>\<^sub>t hp_enn2real' ;; exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<real>\<^sub>Q"
  unfolding hpprog_typing_def hp_enn2real'_def hp_const_def
  apply(rule qbs_morphism_const)
  by auto

lemma hpt_enn2real:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "\<Gamma> \<turnstile>\<^sub>t hp_enn2real t ;; \<real>\<^sub>Q"
  unfolding hp_enn2real_def
  apply(rule hpt_app,rule hpt_enn2real')
  by fact

interpretation ennreal_ennreal : pair_standard_borel_space_UNIV ennreal_borel ennreal_borel
  by standard

lemma hpt_plusennr':
  "\<Gamma> \<turnstile>\<^sub>t hp_plus'' ;; exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 (exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0)"
  unfolding hp_plus''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (+)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_plusennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 +\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  unfolding hp_plus'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_plusennr')
  by fact+

lemma hpt_minusennr':
  "\<Gamma> \<turnstile>\<^sub>t hp_minus'' ;; exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 (exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0)"
  unfolding hp_minus''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (-)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_minusennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 -\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  unfolding hp_minus'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_minusennr')
  by fact+

lemma hpt_timesennr':
  "\<Gamma> \<turnstile>\<^sub>t hp_times'' ;; exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 (exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0)"
  unfolding hp_times''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (*)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_timesennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 *\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  unfolding hp_times'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_timesennr')
  by fact+

lemma hpt_divennr':
  "\<Gamma> \<turnstile>\<^sub>t hp_div'' ;; exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 (exp_qbs \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0 \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0)"
  unfolding hp_div''_def hp_const_def hpprog_typing_def
  apply(rule qbs_morphism_const,simp)
  apply(rule curry_preserves_morphisms[where f="case_prod (/)",simplified curry_def split_beta',simplified])
  by auto

lemma hpt_divennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t1 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t t1 /\<^sub>t t2 ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  unfolding hp_div'_def
  apply(rule hpt_app,rule hpt_app,rule hpt_divennr')
  by fact+

lemma hpt_powerennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t t ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "\<Gamma> \<turnstile>\<^sub>t t^\<^sup>tn ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  by(induction n; simp add: hpt_ennrealc assms hpt_timesennr)

lemma hpt_function:
  assumes "\<And>(\<Gamma>::('a \<times> 'b) quasi_borel) t1 t2.
      (\<Gamma> \<turnstile>\<^sub>t t1 ;; T) \<Longrightarrow> (\<Gamma> \<turnstile>\<^sub>t t2 ;; T) \<Longrightarrow> (\<Gamma> \<turnstile>\<^sub>t hp_lift2 f t1 t2 ;; T)"
          "(\<Gamma>::'a quasi_borel) \<turnstile>\<^sub>t f1 ;; exp_qbs (K:: 'b quasi_borel) T "
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs K T"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_lift2 (hp_lift2 f) f1 f2 ;; exp_qbs K T"
  using assms
proof -
  have "\<Gamma>,,K  \<turnstile>\<^sub>t (\<lambda>(l,k). f1 l k) ;; T"
       "\<Gamma>,,K  \<turnstile>\<^sub>t (\<lambda>(l,k). f2 l k) ;; T"
    using assms(2,3) uncurry_preserves_morphisms[of f1 \<Gamma> K T] uncurry_preserves_morphisms[of f2 \<Gamma> K T]
    by(auto simp add: hpprog_typing_def hpprog_context_def)
  hence "\<Gamma>,,K \<turnstile>\<^sub>t hp_lift2 f (\<lambda>(l,k). f1 l k) (\<lambda>(l,k). f2 l k) ;; T"
    using assms(1)[of "\<Gamma>,,K"] by simp
  hence "\<Gamma> \<turnstile>\<^sub>t curry (hp_lift2 f (\<lambda>(l,k). f1 l k) (\<lambda>(l,k). f2 l k)) ;; exp_qbs K T"
    using curry_preserves_morphisms[of _ \<Gamma> K T]
    by(simp add: hpprog_typing_def hpprog_context_def)
  moreover have "curry (hp_lift2 f (\<lambda>(l,k). f1 l k) (\<lambda>(l,k). f2 l k)) = hp_lift2 (hp_lift2 f) f1 f2"
    by(rule ext,auto)
  ultimately show ?thesis by simp
qed

lemma hpt_funplusn:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<nat>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<nat>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 +\<^sub>t f2 ;; exp_qbs T \<nat>\<^sub>Q"
  using hpt_function[OF _ assms] hpt_plusn
  by(auto simp add: hp_funplus'_def hp_plus'_def hp_plus''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funplusr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 +\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
  using hpt_function[OF _ assms(1) assms(2)] hpt_plusr
  by(auto simp add: hp_funplus'_def hp_plus'_def hp_plus''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funplusennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 +\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  using hpt_function[OF _ assms(1) assms(2)] hpt_plusennr
  by(auto simp add: hp_funplus'_def hp_plus'_def hp_plus''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funminusn:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<nat>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<nat>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 -\<^sub>t f2 ;; exp_qbs T \<nat>\<^sub>Q"
  using hpt_function[OF _ assms(1) assms(2),of minus] hpt_minusn
  by(auto simp add: hp_minus'_def fun_diff_def hp_minus''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funminusr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 -\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
  using hpt_function[OF _ assms(1) assms(2)] hpt_minusr
  by(auto simp add: hp_minus'_def fun_diff_def hp_minus''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funuminusr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f ;; exp_qbs T \<real>\<^sub>Q"
  shows "\<Gamma> \<turnstile>\<^sub>t -\<^sub>t f ;; exp_qbs T \<real>\<^sub>Q"
proof -
  have "(\<lambda>z. f (fst z) (snd z)) \<in> borel_measurable (qbs_to_measure (\<Gamma> \<Otimes>\<^sub>Q T))"
    using uncurry_preserves_morphisms[OF assms[simplified hpprog_typing_def]]
    by(auto simp: case_prod_beta')
  hence "(\<lambda>z. - f (fst z) (snd z)) \<in> borel_measurable (qbs_to_measure (\<Gamma> \<Otimes>\<^sub>Q T))"
    by simp
  hence "(\<lambda>z. - f (fst z) (snd z)) \<in> \<Gamma> \<Otimes>\<^sub>Q T \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    by auto
  thus ?thesis
    using curry_preserves_morphisms[of "\<lambda>z. - f (fst z) (snd z)" \<Gamma> T "\<real>\<^sub>Q",simplified curry_def,simplified]
    by(simp add: hpprog_typing_def hp_uminus'_def fun_Compl_def hp_uminus''_def hp_const_def hp_app_def qbs_eval_def comp_def)
qed

lemma hpt_funminusennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 -\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  using hpt_function[OF _ assms(1) assms(2)] hpt_minusennr
  by(auto simp add: hp_minus'_def fun_diff_def hp_minus''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funtimesn:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<nat>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<nat>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 *\<^sub>t f2 ;; exp_qbs T \<nat>\<^sub>Q"
  using hpt_function[OF _ assms(1) assms(2)] hpt_timesn
  by(auto simp add: hp_funtimes'_def hp_times'_def hp_times''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funtimesr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 *\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
  using hpt_function[OF _ assms(1) assms(2)] hpt_timesr
  by(auto simp add: hp_funtimes'_def hp_times'_def hp_times''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_funtimesennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 *\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  using hpt_function[OF _ assms(1) assms(2)] hpt_timesennr
  by(auto simp add: hp_funtimes'_def hp_times'_def hp_times''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_fundivr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 /\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q"
  using hpt_function[OF _ assms(1) assms(2)] hpt_divr
  by(auto simp add: hp_fundiv'_def hp_div'_def hp_div''_def hp_const_def hp_app_def qbs_eval_def comp_def)

lemma hpt_fundivennr:
  assumes "\<Gamma> \<turnstile>\<^sub>t f1 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "\<Gamma> \<turnstile>\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t f1 /\<^sub>t f2 ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  using hpt_function[OF _ assms(1) assms(2)] hpt_divennr
  by(auto simp add: hp_fundiv'_def hp_div'_def hp_div''_def hp_const_def hp_app_def qbs_eval_def comp_def)




subsubsection \<open> Primitive Recursive Functions \<close>

definition "hp_rec_nat \<equiv> hp_lift2 rec_nat"

lemma hp_rec_nat_simp:
 "hp_rec_nat t0 f k 0       = t0 k"
 "hp_rec_nat t0 f k (Suc n) = f k n (hp_rec_nat t0 f k n)"
  by(auto simp add: hp_rec_nat_def)

lemma hp_rec_nat_simp':
 "hp_app (hp_rec_nat t0 f) (hp_const 0) = t0"
 "hp_app (hp_rec_nat t0 f) (hp_suc e) = hp_app (hp_app f e) (hp_app (hp_rec_nat t0 f) e) "
  by(auto simp add: hp_app_def hp_rec_nat_def hp_const_def qbs_eval_def hp_suc_def hp_suc'_def)

(* \<Gamma> |- t0 : T     \<Gamma> |- f : \<nat> \<Rightarrow> T \<Rightarrow> T 
   ---------------------------------------
          \<Gamma> |- rec t0 f : \<nat> \<Rightarrow> T          *)
lemma hpt_recnat:
  assumes "\<Gamma>  \<turnstile>\<^sub>t t0 ;; T"
      and "\<Gamma>  \<turnstile>\<^sub>t f ;; (exp_qbs \<nat>\<^sub>Q (exp_qbs T T))"
    shows "\<Gamma>  \<turnstile>\<^sub>t hp_rec_nat t0 f ;; (exp_qbs \<nat>\<^sub>Q T)"
  unfolding hpprog_typing_def
proof(rule arg_swap_morphism,rule nat_qbs_morphism,auto)
  fix n
  show "(\<lambda>y. hp_rec_nat t0 f y n) \<in> \<Gamma> \<rightarrow>\<^sub>Q T"
    unfolding hp_rec_nat_def hp_lift2_def
  proof(induction n)
    case 0
    then show ?case
      using assms(1) by(simp add: hpprog_typing_def)
  next
    case ih:(Suc n')
    have "(\<lambda>y. f y n' (rec_nat (t0 y) (f y) n')) = case_prod (case_prod f) \<circ> (\<lambda>y. ((y,n'),rec_nat (t0 y) (f y) n'))"
      by auto
    also have "... \<in> \<Gamma> \<rightarrow>\<^sub>Q T"
      apply(rule qbs_morphism_comp[of _ _ "(\<Gamma> \<Otimes>\<^sub>Q \<nat>\<^sub>Q) \<Otimes>\<^sub>Q T"],rule qbs_morphism_tuple,rule qbs_morphism_tuple)
      using qbs_morphism_ident[of \<Gamma>] qbs_morphism_const[of n' "\<nat>\<^sub>Q"] ih uncurry_preserves_morphisms[of f \<Gamma>] uncurry_preserves_morphisms[of "case_prod f"] assms(2)
         by(auto simp add: id_def hpprog_typing_def)
    finally show ?case by simp
  qed
qed

lemma hpt_recnat':
  assumes "\<Gamma>  \<turnstile>\<^sub>t t0 ;; T"
      and "\<Gamma> ,, \<nat>\<^sub>Q,, T \<turnstile>\<^sub>t e ;; T"
    shows "\<Gamma>  \<turnstile>\<^sub>t hp_rec_nat t0 (hp_lambda (hp_lambda e)) ;; (exp_qbs \<nat>\<^sub>Q T)"
  by(rule hpt_recnat[OF assms(1) hpt_abs[OF hpt_abs[OF assms(2)]]])

definition "hp_rec_list \<equiv> hp_lift2 rec_list"

(*  \<Gamma> |- t0 : T     \<Gamma> |- f : X \<Rightarrow> list X \<Rightarrow> T \<Rightarrow> T 
   ---------------------------------------
          \<Gamma> |- rec t0 f : list X \<Rightarrow> T          *)
lemma hpt_reclist:
  assumes "\<Gamma>  \<turnstile>\<^sub>t t0 ;; T"
      and "\<Gamma>  \<turnstile>\<^sub>t f ;; (exp_qbs X (exp_qbs (list X) (exp_qbs T T)))"
    shows "\<Gamma>  \<turnstile>\<^sub>t hp_rec_list t0 f ;; (exp_qbs (list X) T)"
  unfolding hpprog_typing_def hp_rec_list_def
  by(auto intro!: qbs_morphism_comp[OF qbs_morphism_tuple[OF assms(1)[simplified hpprog_typing_def] assms(2)[simplified hpprog_typing_def]],of "case_prod rec_list",simplified comp_def split_beta fst_conv snd_conv] uncurry_preserves_morphisms rec_list_morphism[simplified])

lemma hpt_reclist':
  assumes "\<Gamma>  \<turnstile>\<^sub>t t0 ;; T"
      and "\<Gamma> ,, X ,, list X ,, T \<turnstile>\<^sub>t e ;; T"
    shows "\<Gamma>  \<turnstile>\<^sub>t hp_rec_list t0 (hp_lambda (hp_lambda (hp_lambda e))) ;; (exp_qbs (list X) T)"
  by(rule hpt_reclist[OF assms(1) hpt_abs[OF hpt_abs[OF hpt_abs[OF assms(2)]]]])

subsubsection \<open> Ennriched Expressions \<close>
definition "hp_integrable \<equiv> hp_lift2 qbs_integrable"
definition "hp_expect \<equiv> hp_lift2 qbs_prob_integral"
definition "hp_ennexpect \<equiv> hp_lift2 qbs_prob_ennintegral"
definition "hp_var \<equiv> hp_lift2 qbs_prob_var"
term hp_powerr
lemma hp_var_def2:
  "hp_var t e = hp_expect t ( (e -\<^sub>t hp_constf (hp_expect t e)) *\<^sub>t (e -\<^sub>t hp_constf (hp_expect t e)))"
  by(simp add: hp_var_def hp_expect_def hp_constf_def hp_funtimes'_def qbs_prob_var_def power2_eq_square hp_const_def hp_times'_def hp_minus'_def hp_app_def hp_times''_def hp_minus''_def qbs_eval_def comp_def)


(* \<Gamma> |- m : P T    \<Gamma> |- f : T \<Rightarrow> ennreal 
   ---------------------------------------
         \<Gamma> |- E_x~m [f x] : ennreal      *)
lemma hpt_ennexpect:
  assumes "\<Gamma> \<turnstile>\<^sub>t m ;; monadP_qbs T"
      and "\<Gamma> \<turnstile>\<^sub>t f ;; exp_qbs T \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_ennexpect m f ;; \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  using qbs_prob_ennintegral_morphism[OF assms(1)[simplified hpprog_typing_def] assms(2)[simplified hpprog_typing_def]]
  by(simp add: hpprog_typing_def hp_ennexpect_def)

(* \<Gamma> |- m : P T    \<Gamma> |- f : T \<Rightarrow> \<real>    f : integrable w.r.t. m
   -----------------------------------------------------------
                 \<Gamma> |- E_x~m [f x] : \<real>                         *)
lemma hpt_expect:
  assumes "\<Gamma> \<turnstile>\<^sub>t m ;; monadP_qbs T"
          "\<Gamma> \<turnstile>\<^sub>t f ;; exp_qbs T \<real>\<^sub>Q"
      and "\<And>x. x \<in> qbs_space \<Gamma> \<Longrightarrow> hp_integrable m f x"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_expect m f ;; \<real>\<^sub>Q"
  using qbs_prob_integral_morphism[OF assms(1)[simplified hpprog_typing_def] assms(2)[simplified hpprog_typing_def]] assms(3)
  by(simp add: hpprog_typing_def hp_expect_def hp_integrable_def)


subsubsection \<open> Product Measure \<close>
definition hp_pair_measure (infixr "\<Otimes>\<^sub>Q\<^sub>t" 80) where
"hp_pair_measure \<equiv> hp_lift2 qbs_prob_pair_measure"

lemma hpt_pair_measure:
  assumes "\<Gamma> \<turnstile>\<^sub>t m ;; monadP_qbs M"
      and "\<Gamma> \<turnstile>\<^sub>t n ;; monadP_qbs N"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_pair_measure m n ;; monadP_qbs (M \<Otimes>\<^sub>Q N)"
  using qbs_morphism_comp[OF qbs_morphism_tuple[OF assms[simplified hpprog_typing_def]] qbs_prob_pair_measure_morphism]
  by(simp add: hpprog_typing_def comp_def hp_pair_measure_def)

definition "hp_id \<equiv> hp_const id"
lemma hpt_id:
 "\<Gamma> \<turnstile>\<^sub>t hp_id ;; exp_qbs X X"
  unfolding hpprog_typing_def hp_id_def hp_const_def
  by(rule qbs_morphism_const[of _ "exp_qbs X X",simplified,OF qbs_morphism_ident])

definition "hp_comp \<equiv> hp_lift2 comp"
lemma hpt_comp:
  assumes "\<Gamma> \<turnstile>\<^sub>t f ;; exp_qbs X Y"
      and "\<Gamma> \<turnstile>\<^sub>t g ;; exp_qbs Y Z"
    shows "\<Gamma> \<turnstile>\<^sub>t hp_comp g f ;; exp_qbs X Z"
  using exp_qbs_comp_morphism[of f \<Gamma> X Y g Z] assms
  by(simp add: hpprog_typing_def hp_comp_def)

text \<open> The followings are examples. \<close>
lemma "\<Gamma>,, Y \<turnstile>\<^sub>t \<lambda>\<^sub>t var1 $\<^sub>t var1 ;; Y"
  apply(rule hpt_app)
   apply(rule hpt_abs)
   apply(rule hpt_var1)
  apply(rule hpt_var1)
  done

lemma "\<Gamma> \<turnstile>\<^sub>t \<lambda>\<^sub>t (\<lambda>\<^sub>t (hp_normal var2 var1)) ;; \<real>\<^sub>Q \<Rightarrow>\<^sub>Q \<real>\<^sub>Q \<Rightarrow>\<^sub>Q P\<^sub>t \<real>\<^sub>Q"
  apply(rule hpt_abs)
  apply(rule hpt_abs)
  apply(rule hpt_normal)
   apply(rule hpt_var2)
  apply(rule hpt_var1)
  done

end