theory Voting_Power_Scratch
  imports "HOL-Library.Extended_Nonnegative_Real"
          "HOL-Probability.Probability_Measure"
          "../Voting_Models/Voting_Model_Scratch"

begin

section \<open>Auxiliary Definitions and Lemmas\<close>

fun actual_funcset :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x \<Rightarrow> 'y) set" where
  "actual_funcset X Y = funcset X Y \<inter> extensional X"

fun characteristic :: "('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x \<Rightarrow> nat" where
  "characteristic f Y x = (if f x \<in> Y then 1 else 0)"

lemma set_card: 
  fixes 
    X :: "'x set" and
    \<phi> :: "'x \<Rightarrow> bool"
  shows
    "finite X \<Longrightarrow> card {x | x. x \<in> X \<and> \<phi> x} = sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X"
proof (induction "card X" arbitrary: X)
  case 0
  hence "X = {}"
    by simp
  hence "{x | x. x \<in> X \<and> \<phi> x} = {}"
    by blast
  hence "card {x | x. x \<in> X \<and> \<phi> x} = 0"
    by (metis card.empty)
  moreover have "sum (\<lambda>x. if (\<phi> x) then 1::nat else 0) X = 0"
    using \<open>X = {}\<close>
    by simp
  ultimately show ?case
    using "0.hyps" "0.prems"
    by simp
next
  case (Suc x)
  hence "card X > 0"
    by simp
  then obtain a :: 'x where "a \<in> X"
    by fastforce (* TODO *)
  have "x = card X - 1"
    using Suc.hyps
    by simp
  hence "x = card (X-{a})"
    using \<open>a \<in> X\<close>
    by simp
  hence card_minus_a:
    "card {x |x. x \<in> X-{a} \<and> \<phi> x} = (\<Sum>x\<in>X-{a}. if \<phi> x then 1::nat else 0)"
    using Suc.hyps Suc.prems
    by blast
  have 
    "{x |x. x \<in> X \<and> \<phi> x} = {x |x. x \<in> X-{a} \<and> \<phi> x} \<union> (if (\<phi> a) then {a} else {})"
    using \<open>a \<in> X\<close>
    by auto
  moreover have "{x |x. x \<in> X-{a} \<and> \<phi> x} \<inter> (if (\<phi> a) then {a} else {}) = {}"
    by simp
  moreover have "finite {x |x. x \<in> X-{a} \<and> \<phi> x}"
    using Suc.prems
    by simp
  moreover have "finite (if (\<phi> a) then {a} else {})"
    by simp
  ultimately have
    "card {x |x. x \<in> X \<and> \<phi> x} = card {x |x. x \<in> X-{a} \<and> \<phi> x} + card (if (\<phi> a) then {a} else {})"
    using card_Un_Int 
    by simp
  hence
    "card {x |x. x \<in> X \<and> \<phi> x} = 
      (\<Sum>x\<in>X - {a}. if \<phi> x then 1 else 0) + (if (\<phi> a) then 1::nat else 0)"
    using card_minus_a
    by simp
  moreover have 
    "(\<Sum>x\<in>X - {a}. if \<phi> x then 1 else 0) =
      (\<Sum>x\<in>X. if \<phi> x then 1 else 0) - (if \<phi> a then 1::nat else 0)"
    using sum_diff1[of X "\<lambda>x. if (\<phi> x) then 1::nat else 0" a] Suc.prems \<open>a \<in> X\<close>
    by (meson sum_diff1_nat)
  ultimately show ?case
    by (metis (no_types, lifting) Suc.prems \<open>a \<in> X\<close> add.commute sum.remove)
qed

lemma card_funcset: 
  fixes
    X :: "'x set" and Y :: "'y set"
  assumes
    "finite X" and "finite Y"
  shows
    "card (actual_funcset X Y) = (card X)^(card Y)"
  sorry

section \<open>Simple Voting Games\<close>

fun swing_vote_svg :: "'v set set \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> ereal" where
  "swing_vote_svg \<F> v S = (if ((S \<union> {v}) \<in> \<F>) \<noteq> ((S - {v}) \<in> \<F>) then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for simple voting games:
  Count the number of coalitions a voter can change by switching their vote and average over those.
\<close>
fun banzhaf_svg_1 :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_svg_1 (V, \<F>) v = (1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)"

value "banzhaf_svg_1 ({1::nat, 2}, {{1}, {1,2}}) 1"

fun banzhaf_prob_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v set measure" where
  "banzhaf_prob_svg G = uniform_count_measure (Pow (fst G))"

lemma banzhaf_1_is_prob_svg:
  fixes
    V :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v
  assumes
    "finite V" and "\<F> \<subseteq> Pow V" and "v \<in> V"
  shows
    "banzhaf_svg_1 (V, \<F>) v = emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}"
proof -
  let ?swings = "{S | S. swing_vote_svg \<F> v S = 1}"
  have "\<forall>S. swing_vote_svg \<F> v S = 1 \<longrightarrow> S \<subseteq> V"
  proof (simp, safe)
    fix 
      S :: "'v set" and
      x :: 'v
    assume 
      "insert v S \<in> \<F>" and "x \<in> S"
    hence "S \<union> {v} \<subseteq> V"
      using assms(2)
      by blast
    thus "x \<in> V"
      using \<open>x \<in> S\<close>
      by blast
  next
    fix 
      S :: "'v set" and
      x :: 'v
    assume 
      "x \<in> S" and "x \<notin> V" and "S - {v} \<in> \<F>"
    hence "S - {v} \<subseteq> V"
      using assms(2)
      by blast
    hence "S \<subseteq> V"
      using assms(2) assms(3)
      by blast
    hence "x \<in> V"
      using \<open>x \<in> S\<close>
      by blast
    thus "False"
      using \<open>x \<notin> V\<close>
      by blast
  qed
  hence subset: "?swings \<subseteq> Pow V"
    by blast
  moreover have fin_pow: "finite (Pow V)"
    using assms(1)
    by simp
  ultimately have rewrite_prob:
    "emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}
      = (card {S | S. swing_vote_svg \<F> v S = 1})/(card (Pow V))"
    unfolding banzhaf_prob_svg.simps
    using emeasure_uniform_count_measure[of "Pow V" ?swings]
    by simp
  have "ereal (1/(2^(card V))) = ereal (1/(card (Pow V)))"
    using assms(1) Power.card_Pow[of V, OF assms(1)]
    by simp
  hence 
    "\<forall>x::ereal. (1/(2^(card V))) * x = (1/(card (Pow V))) * x"
    by (metis ereal_divide ereal_power numeral_eq_ereal one_ereal_def power_eq_0_iff zero_neq_numeral)
  hence rewrite_pow':
    "(1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)
    = (1/(card (Pow V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)"
    by simp

  have swing_vote: 
    "(\<lambda>S. (if swing_vote_svg \<F> v S = 1 then 1 else 0)) = (\<lambda>S. swing_vote_svg \<F> v S)"
    by auto
  have swings: "?swings = {S |S. S \<in> Pow V \<and> swing_vote_svg \<F> v S = 1}"
    using subset
    by blast

  hence "card ?swings = card {S |S. S \<in> Pow V \<and> swing_vote_svg \<F> v S = 1}"
    by simp
  also have 
    "... = (\<Sum>S\<in>Pow V. if swing_vote_svg \<F> v S = 1 then 1 else 0)"
    by (rule set_card[of "Pow V" "\<lambda>S. swing_vote_svg \<F> v S = 1", OF fin_pow])
  also have 
    "... = (\<Sum>S\<in>Pow V. swing_vote_svg \<F> v S)"
    using swing_vote
    sorry
  finally have
    "(\<Sum>S\<in>Pow V. swing_vote_svg \<F> v S) = card {S |S. swing_vote_svg \<F> v S = 1}"
    by simp
  hence rewrite_pow:
    "banzhaf_svg_1 (V, \<F>) v = (1/(card (Pow V))) * card {S | S. swing_vote_svg \<F> v S = 1}"
    using rewrite_pow'
    by simp
  thus ?thesis
    using rewrite_prob
    by simp
qed

section \<open>Voting Rules\<close>

fun differ_only_on :: "'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> bool" where
  "differ_only_on v p p' = (\<forall>x. p x \<noteq> p' x \<longrightarrow> x = v)"

fun swing_vote_rule :: "(('v \<Rightarrow> 'b) \<Rightarrow> 'r) \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ereal" where
  "swing_vote_rule f v p p' = (if (differ_only_on v p p' \<and> f p \<noteq> f p') then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for voting rules:
  Count the number of profiles where the outcome would change if a voter changed their ballot
  while all other voters kept theirs, then average over all profiles.
\<close>

fun banzhaf_rule_1 :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_rule_1 (V, B, R, f) v = 
    (1/(real ((card B)^(card V)))) * 
      (\<Sum> p \<in> actual_funcset V B. 
        Max {characteristic (swing_vote_rule f v p) {1} q | q. q \<in> actual_funcset V B})" 

(* TODO: test value banzhaf_rule_1 *)

(* Banzhaf index where probability interpretation breaks: *)
fun banzhaf_rule_2 :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_rule_2 (V, B, R, f) v = 
    (1/(real ((card B)^(card V)))) * 
      (\<Sum> p \<in> actual_funcset V B. \<Sum> q \<in> actual_funcset V B. (swing_vote_rule f v p q))" 
(* Additional danger of not stating the intended voting power measure
when formalizing with weird types: Almost wrote \<^latex>\<open>p \<in> UNIV\<close> here *)

fun banzhaf_prob_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v \<Rightarrow> 'b) measure" where
  "banzhaf_prob_rule (V, B, R, f) = uniform_count_measure (actual_funcset V B)"
                                                
lemma banzhaf_1_is_prob_rule:
  fixes
    X :: "('v, 'b, 'r) Voting_Rule" and
    v :: 'v
  assumes
    "finite (voters X)" and "finite (ballots X)" and "v \<in> V"
  shows
    "banzhaf_rule_1 X v = emeasure (banzhaf_prob_rule X) 
      {p | p. p \<in> actual_funcset (voters X) (ballots X) 
        \<and> (\<exists>q \<in> actual_funcset (voters X) (ballots X). swing_vote_rule (rule X) v p q = 1)}"
proof -
  let ?V = "voters X"
  let ?B = "ballots X"
  let ?f = "rule X"
  let ?swings = 
    "{p |p. p \<in> actual_funcset ?V ?B \<and> (\<exists>q\<in>actual_funcset ?V ?B. swing_vote_rule ?f v p q = 1)}"
  have "finite (actual_funcset ?V ?B)"
    sorry
  moreover have "?swings \<subseteq> actual_funcset ?V ?B"
    sorry
  ultimately have prob:
    "emeasure (uniform_count_measure (actual_funcset ?V ?B)) ?swings
      = (real (card ?swings))/(real (card (actual_funcset ?V ?B)))"
    using emeasure_uniform_count_measure[of "actual_funcset ?V ?B" ?swings]
    by simp
  have "X = (?V, ?B, results X, ?f)"
    by simp
  hence
    "banzhaf_prob_rule X = uniform_count_measure (actual_funcset ?V ?B)"
    by (metis banzhaf_prob_rule.simps)
  with prob have prob_rewrite:
    "banzhaf_prob_rule X ?swings = (real (card ?swings))/(real (card (actual_funcset ?V ?B)))"
    by simp
  have
    "(\<Sum> p \<in> actual_funcset ?V ?B. 
        Max {characteristic (swing_vote_rule ?f v p) {1} q | q. q \<in> actual_funcset ?V ?B})
      = card ?swings"
    sorry
  hence
    "banzhaf_rule_1 X v = (1/(real ((card ?B)^(card ?V)))) * (card ?swings)"
    sorry
  hence
    "banzhaf_rule_1 X v = (1/(real (card (actual_funcset ?V ?B)))) * (card ?swings)"
    using card_funcset[of ?V ?B] assms
    sorry
  hence power_rewrite:
    "banzhaf_rule_1 X v = (real (card ?swings))/(real (card (actual_funcset ?V ?B)))"
    by argo
  thus ?thesis
    using prob_rewrite
    by simp
qed

text \<open>
  The second Banzhaf definition on voting rules generally is an expected value rather 
  than a probability distribution. 
  However, depending on the voter and the event, it may align with individual probabilities.
  
  To make the difference between this probabilistic interpretation and the one from
  banzhaf_1_is_prob_rule clear, we show that if there is a voter who is able to influence the
  election result in at least one way for every ballot profile and at least two ways for at
  least one ballot profile, their Banzhaf index is > 1 and thus no probability.
\<close>
lemma baby_example_banzhaf_2_not_prob:
  fixes                                    
    X :: "('v, 'b, 'r) Voting_Rule" and
    v :: 'v              
  assumes
    "finite (voters X)" and 
    "finite (ballots X)" and 
    "v \<in> V" and
    always_influence: (* v can influence the election result in every profile *)
      "\<forall>p \<in> actual_funcset (voters X) (ballots X). \<exists>q \<in> actual_funcset (voters X) (ballots X). 
        swing_vote_rule (rule X) v p q = 1" and
    influence_options: (* v has multiple options to influence the election result in at least one profile *)
      "\<exists>p \<in> actual_funcset (voters X) (ballots X). 
        \<exists>q \<in> actual_funcset (voters X) (ballots X). \<exists>q' \<in> actual_funcset (voters X) (ballots X). 
          q \<noteq> q' \<and> swing_vote_rule (rule X) v p q = 1 \<and> swing_vote_rule (rule X) v p q' = 1"
  shows
    "banzhaf_rule_2 X v > 1"
  sorry

lemma banzhaf_2_is_expectation_rule:
  "True" (* TODO *)
  sorry

section \<open>Strategic Games\<close>

text \<open>
  First formulation of a Banzhaf index for strategic games: TODO
\<close>
fun banzhaf_strat_1 :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_strat_1 (V, R, A, P, f) v = 0" (* TODO *)
                     
end