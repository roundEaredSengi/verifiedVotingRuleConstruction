theory Voting_Power_Comparison
  imports Voting_Power_Scratch
          Simple_Voting_Game
          Voting_Rule

begin

(*
locale Voting_Model_Comparison =
  fixes
    model_similarity :: "'x \<Rightarrow> 'y \<Rightarrow> bool"

locale Voting_Power_Comparison =
  fixes 
    delta1 :: "('x, 'v) Voting_Power" and
    delta2 :: "('y, 'v) Voting_Power" and
    similarity :: "('x, 'v) Voting_Power \<Rightarrow> ('y, 'v) Voting_Power \<Rightarrow> bool"
  assumes
    "similarity delta1 delta2"

definition (in Voting_Model_Comparison) numerical_similarity :: 
  "('x, 'v) Voting_Power \<Rightarrow> ('y, 'v) Voting_Power \<Rightarrow> bool" where
  "numerical_similarity delta1 delta2 = (\<forall>m1 m2. model_similarity m1 m2 \<longrightarrow> (\<forall>v. delta1 m1 v = delta2 m2 v))"

locale Numerical_Voting_Power_Comparison = 
    model_comp: Voting_Model_Comparison model_similarity + 
    power_comp: Voting_Power_Comparison delta1 delta2 model_comp.numerical_similarity 
    for model1 and model2 and model_similarity and delta1 and delta2
begin

thm power_comp.Voting_Power_Comparison_axioms

end 
*)

fun preimg_in :: "'x set \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x set" where
  "preimg_in X f Y = {x |x. x \<in> X \<and> f x \<in> Y}"

definition svg_rule_equivalence :: 
  "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" where
  "svg_rule_equivalence \<R> \<G> = (
    voters \<R> = fst \<G> \<and>
    card (ballots \<R>) = 2 \<and> 
    card (results \<R>) = 2 \<and> 
    (\<exists>\<sigma>::'b \<Rightarrow> 'r. \<exists>r \<in> results \<R>. bij_betw \<sigma> (ballots \<R>) (results \<R>) \<and>
      (\<forall>p. rule \<R> p = r \<longleftrightarrow> preimg_in (voters \<R>) p (preimg_in (ballots \<R>) \<sigma> {r}) \<in> (coalitions \<G>))
    )
  )"

definition svg_rule_power_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power \<Rightarrow> ('v Simple_Voting_Game, 'v) Voting_Power \<Rightarrow> bool"
  where 
    "svg_rule_power_equivalence \<delta>1 \<delta>2 = (
      \<forall>\<R> \<G>. svg_rule_equivalence \<R> \<G> \<longrightarrow> (\<forall>v \<in> voters \<R> \<inter> fst \<G>. \<delta>1 \<R> v = \<delta>2 \<G> v)
    )"

definition svg_rule_axiom_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power_Axiom \<Rightarrow> 
    ('v Simple_Voting_Game, 'v) Voting_Power_Axiom \<Rightarrow> bool" where
  "svg_rule_axiom_equivalence \<phi>1 \<phi>2 = (\<forall>m1 m2 \<delta>1 \<delta>2. 
    svg_rule_equivalence m1 m2 \<and> svg_rule_power_equivalence \<delta>1 \<delta>2 \<longrightarrow> (\<phi>1 {m1} \<delta>1 \<longleftrightarrow> \<phi>2 {m2} \<delta>2))"

theorem block_equivalence:
  "svg_rule_axiom_equivalence block_axiom_rule block_axiom_svg_on"
  sorry

text \<open>
  On voting rules that correspond to simple voting games, 
  the Banzhaf indices on voting rules and SVGs behave the same.
\<close>
theorem banzhaf_equivalence:
  "svg_rule_power_equivalence banzhaf_rule_1 banzhaf_svg_1"
proof (unfold svg_rule_power_equivalence_def, safe)
  fix
    v :: 'a and V' :: "'a set" and \<F> :: "'a set set" and
    V :: "'a set" and B :: "'b set" and R :: "'c set" and f :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c"
  assume
    vot_v_rule: "v \<in> voters (V, B, R, f)" and
    vot_v_game: "v \<in> voters_svg (V', \<F>)" and
    equiv: "svg_rule_equivalence (V, B, R, f) (V', \<F>)"
  hence eq_vot_set: "V = V'"
    unfolding svg_rule_equivalence_def
    by simp
  hence eq_card: "card V = card V'"
    by simp
  let ?n = "card V"
  have ballots_2: "card B = 2"
    using equiv
    unfolding svg_rule_equivalence_def
    by simp
  have results_2: "card R = 2"
    using equiv
    unfolding svg_rule_equivalence_def
    by simp
  obtain \<sigma> :: "'b \<Rightarrow> 'c" and r :: 'c where
    "r \<in> R" and bij: "bij_betw \<sigma> B R" and 
    decision_corresp: "\<forall>p. f p = r \<longleftrightarrow> preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>"  
    using equiv  
    unfolding svg_rule_equivalence_def fst_def snd_def
    by auto
  hence "card (R - {r}) = 1"
    using results_2
    by simp
  then obtain s :: 'c where "R - {r} = {s}" 
    by (rule card_1_singletonE)
  hence "R = {s, r}"
    using \<open>r \<in> R\<close>    
    by auto
  moreover have "\<forall>p. f p \<in> R"
    sorry (* TODO currently does not hold, we need an assumption for that as well \<Rightarrow> locales? *)
  ultimately have neq_rewrite: "\<forall>p q. f p \<noteq> f q \<longleftrightarrow> \<not> (f p = r \<longleftrightarrow> f q = r)"
    using ballots_2
    by auto
  have swing_rewrite: "\<forall>p q.
    (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)
    \<longleftrightarrow> (swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1)"
    sorry
  show "banzhaf_rule_1 (V, B, R, f) v = banzhaf_svg_1 (V', \<F>) v"
  proof (cases "finite V")
    case True
    hence rewrite_rule: "banzhaf_rule_1 (V, B, R, f) v = 
      (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
        Max {characteristic (swing_vote_rule f v p) {1} q | q. q \<in> actual_funcset V B})"
      using ballots_2
      by simp
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      Max {characteristic (\<lambda>q. differ_only_on v p q \<and> f p \<noteq> f q) {True} q | q. q \<in> actual_funcset V B})"
      by simp
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      Max {characteristic (\<lambda>q. True) {True} q | q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and> f p \<noteq> f q})"
      sorry (* TODO helpers for "characteristic" function *)
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      if {q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and> f p \<noteq> f q} \<noteq> {} then 1 else 0)"
      sorry
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      if {q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and> (f p = r) \<noteq> (f q = r)} \<noteq> {} then 1 else 0)"
      using neq_rewrite
      by simp
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      if {q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and> 
        (preimg_in V p (preimg_in B \<sigma> {r}) \<in> \<F>) \<noteq> (preimg_in V q (preimg_in B \<sigma> {r}) \<in> \<F>)} \<noteq> {} 
        then 1 else 0)"
      using decision_corresp
      by simp
    also have "... = (1 / 2^?n) * (\<Sum> p \<in> actual_funcset V B. 
      if {q. q \<in> actual_funcset V B \<and> differ_only_on v p q \<and> 
        swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})) = 1} \<noteq> {} 
        then 1 else 0)"
      using swing_rewrite
      by simp
    also have "... = (1 / 2^?n) * 
      (\<Sum> p \<in> actual_funcset V B. swing_vote_svg \<F> v (preimg_in V p (preimg_in B \<sigma> {r})))"
      sorry
    also have "... = (1 / 2^?n) * 
      (\<Sum> S \<in> {preimg_in V p (preimg_in B \<sigma> {r}) |p. p \<in> actual_funcset V B}. swing_vote_svg \<F> v S)"
      sorry
    also have "... = (1 / 2^?n) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)"
      sorry
    also have "... = banzhaf_svg_1 (V, \<F>) v"
      by simp
    finally show ?thesis
      using eq_vot_set
      by simp
  next
    case False
    hence "banzhaf_rule_1 (V, B, R, f) v = 0"
      by simp
    moreover from False have "banzhaf_svg_1 (V', \<F>) v = 0"
      using eq_vot_set
      by simp
    ultimately show ?thesis
      by simp
  qed
qed

theorem block_satisfied_by_rule_banzhaf:
  "block_axiom_rule {} banzhaf_rule_1" (* TODO: define monotone binary voting rules *)
  sorry

end