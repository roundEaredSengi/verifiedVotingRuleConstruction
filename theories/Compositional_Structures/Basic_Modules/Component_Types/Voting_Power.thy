section \<open>Voting Power\<close>

theory Voting_Power
  imports Electoral_Module
          Distance    
          "HOL-Probability.Probability_Measure"

begin

subsection \<open>Definitions\<close>

type_synonym ('a, 'v, 'r) Swing_Weight =
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> ereal"

type_synonym ('a, 'v, 'r) Voting_Power =
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'v \<Rightarrow> ereal"

text \<open>Symmetry of voting power measures\<close>

type_synonym ('a, 'v, 'r) Voting_Power_Domain =
  "('a, 'v, 'r) Electoral_Module \<times> ('a, 'v) Election set \<times> 'v"

fun rename_rule :: "('v \<Rightarrow> 'v) \<Rightarrow> ('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v, 'r) Electoral_Module" where
  "rename_rule \<pi> f = (\<lambda> V A p. (fun\<^sub>\<E> f) ((the_inv (rename \<pi>)) (A, V, p)))"

fun rename_pow :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v, 'r) Voting_Power_Domain)" where
  "rename_pow \<pi> (f, E, v) = (rename_rule \<pi> f, (rename \<pi>) ` E, \<pi> v)"

fun uncurry3 :: "('w \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> (('w \<times> 'x \<times> 'y) \<Rightarrow> 'z)" where
  "uncurry3 f = (\<lambda>(w,x,y). f w x y)"

fun is_sym_pow :: "('a, 'v, 'r) Voting_Power_Domain set \<Rightarrow> ('a, 'v, 'r) Voting_Power \<Rightarrow> bool" where
  "is_sym_pow X \<delta> = (is_symmetry (uncurry3 \<delta>) (Invariance 
    (action_induced_rel (Bij (UNIV::('v set))) X (\<lambda> \<pi>. rename_pow \<pi>))))"

text \<open>Voting power as weighted sum over swing elections.\<close>
fun weighted_voting_power :: 
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow>
  ('a, 'v, 'r) Swing_Weight \<Rightarrow> 'v \<Rightarrow> ereal" where
  "weighted_voting_power f E weight v = (\<Sum> e \<in> E. weight f e v)"

fun coincide_except :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> bool" where
  "coincide_except e1 e2 v = 
      (\<forall> w \<in> (voters_\<E> e1) - {v}. profile_\<E> e1 w = profile_\<E> e2 w)"

fun swing_votes :: 
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'v \<Rightarrow> (('a, 'v) Election) rel" where
  "swing_votes f E v = {(e1, e2) \<in> E \<times> E. 
      fun\<^sub>\<E> f e1 \<noteq> fun\<^sub>\<E> f e2 \<and> voters_\<E> e1 = voters_\<E> e2 \<and> coincide_except e1 e2 v}"

fun discrete_dist :: "'x Distance" where
  "discrete_dist x y = (if (x = y) then 0 else 1)"

fun raw_weight :: 
  "'r Distance \<Rightarrow> ('a, 'v) Election set \<Rightarrow> ('a, 'v, 'r) Swing_Weight" where
  "raw_weight d E f e v = (\<Sum> (e1, e2) \<in> swing_votes f E v. 
    (discrete_dist e e1) * (d (fun\<^sub>\<E> f e1) (fun\<^sub>\<E> f e2)))"

text \<open>
  Raw power defines the weights of swing elections as the 
  total result distance achievable via swing voting.\<close>
fun raw_power :: "'r Distance \<Rightarrow> ('a, 'v, 'r) Voting_Power" where
  "raw_power d f E v = weighted_voting_power f E (raw_weight d E) v"

subsection \<open>Specific Power Indices\<close>

fun banzhaf\<^sub>r\<^sub>a\<^sub>w :: "('a, 'v, 'r) Voting_Power" where
  "banzhaf\<^sub>r\<^sub>a\<^sub>w f E v = (1/(ereal (card E))) * (raw_power discrete_dist f E v)"

text \<open>Identically distributed probability space.\<close>
locale idd_prob_space = prob_space +                   
  assumes "\<forall> S \<subseteq> space M. emeasure M S = (card S)/(card (space M))"

fun swap_voters :: "'v \<Rightarrow> 'v \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "swap_voters v w e = 
    (let \<pi> = (\<lambda>x::'v. (if x = w then v else (if x = v then w else x))) in
      rename \<pi> e)"

lemma rename_inv_commute:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows
    "the_inv (rename \<pi>) = rename (the_inv \<pi>)"
proof -
  have "(rename (the_inv \<pi>)) \<circ> (rename \<pi>) = id"
    unfolding comp_def
    using rename_inv ext assms id_def inj_def prod_cases3 rename_inj
    by (metis (no_types, lifting))
  thus "the_inv (rename \<pi>) = rename (the_inv \<pi>)"
    using  ext assms bij_betw_the_inv_into comp_apply id_apply rename_inj the_inv_f_f
    by (metis (no_types, lifting))
qed

lemma anon_rule_imp_symmetry_pow_const:
  fixes
    \<delta> :: "('a, 'v, 'r) Voting_Power" and
    f :: "('a, 'v, 'r) Electoral_Module" and
    E :: "('a, 'v) Election set" and
    X :: "('a, 'v, 'r) Voting_Power_Domain set" and
    v :: 'v and
    w :: 'v 
  assumes 
    sym_pow: "is_sym_pow X \<delta>" and
    anon_rule: "anonymity_in E f" and
    well_formed_counting_domain: "swap_voters v w ` E  = E" and
    domain_constrained_delta: 
      "\<forall> f g Y x. (\<forall> e \<in> Y. 
        f (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e) = 
        g (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e))
        \<longrightarrow> \<delta> f Y x = \<delta> g Y x" and
    valid_v: "(f, E, v) \<in> X"
  shows "\<delta> f E v = \<delta> f E w"
proof -
  (* Generally, the symmetric power of v under f, E equals that of pi(v) under f_pi, pi(E). *)
  let ?\<pi> = "(\<lambda> x :: 'v. (if x = w then v else (if x = v then w else x)))"
  have bij0: "bij ?\<pi> \<and> bij (the_inv ?\<pi>)"
    by (simp add: bij_betw_the_inv_into involuntory_imp_bij)
  hence bij: "?\<pi> \<in> Bij UNIV \<and> (the_inv ?\<pi>) \<in> Bij UNIV"
    unfolding Bij_def extensional_def
    by simp
  moreover have 
    "((rename_rule ?\<pi> f), ((rename ?\<pi>) ` E), (?\<pi> v)) = rename_pow ?\<pi> (f, E, v)"
    by simp
  ultimately have 
    "\<exists> x \<in> Bij UNIV. 
      rename_pow x (f, E, v) = ((rename_rule ?\<pi> f), ((rename ?\<pi>) ` E), (?\<pi> v))"
    using valid_v
    by metis
  hence
    "((f, E, v), ((rename_rule ?\<pi> f), ((rename ?\<pi>) ` E), (?\<pi> v))) \<in> 
      action_induced_rel (Bij (UNIV::('v set))) X (\<lambda> \<pi>. rename_pow \<pi>)"
    using valid_v
    by simp
  hence eq0: "\<delta> f E v = \<delta> (rename_rule ?\<pi> f) ((rename ?\<pi>) ` E) (?\<pi> v)"
    using sym_pow
    by simp
  (* pi(v) = w, E_pi = E and f_pi = f (constrained to E) yields the result 
    given that delta does not care about values of f outside of E. *)
  have 
    "\<forall> e \<in> E. extensional_continuation (the_inv (rename ?\<pi>)) E e = 
                (the_inv (rename ?\<pi>)) e"
    by simp
  hence 
    "\<forall> e \<in> E. \<exists> x \<in> Bij UNIV. 
      extensional_continuation (the_inv (rename ?\<pi>)) E e = 
      (the_inv (rename ?\<pi>)) e"
    using bij id_Bij
    unfolding \<phi>_anon.simps
    by blast
  hence "\<forall> e \<in> E. \<exists> x \<in> Bij UNIV. \<phi>_anon E x e = (the_inv (rename ?\<pi>)) e"
    unfolding \<phi>_anon.simps
    using rename_inv_commute
    by (metis (no_types, lifting) bij0 bij)
  hence "\<forall> e \<in> E. (e, (the_inv (rename ?\<pi>)) e) \<in> anonymity\<^sub>\<R> E"
    using bij
    unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps bijection\<^sub>\<V>\<^sub>\<G>_def BijGroup_def
    by simp
  hence
    "\<forall> e \<in> E. rename_rule ?\<pi> f (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e) = 
                f (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e)"
    using anon_rule alternatives_\<E>.elims prod.collapse profile_\<E>.elims voters_\<E>.elims
    unfolding anonymity_in.simps is_symmetry.simps fun\<^sub>\<E>.simps rename_rule.simps
    by (metis (lifting))
  hence "\<delta> f E w = \<delta> (rename_rule ?\<pi> f) E w"
    using domain_constrained_delta
    by presburger
  moreover have "w = ?\<pi> v"
    by simp
  moreover have "E = (rename ?\<pi>) ` E"
    using well_formed_counting_domain
    by simp
  ultimately have "\<delta> f E w = \<delta> (rename_rule ?\<pi> f) ((rename ?\<pi>) ` E) (?\<pi> v)"
    by simp
  thus "\<delta> f E v = \<delta> f E w"
    using eq0
    by simp
qed

end