chapter \<open>Voting Rule\<close>

theory Voting_Rule
  imports Voting_Power_Scratch

begin

section \<open>Voting Model\<close>

fun differ_only_on :: "'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> bool" where
  "differ_only_on v p p' = (\<forall>x. p x \<noteq> p' x \<longrightarrow> x = v)"

section \<open>Voting Power Indices\<close>

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

section \<open>Voting Power Properties\<close>

(* TODO evaluation order of let? *)
fun block_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('v, 'b, 'r) Voting_Rule \<times> 'v" where
  "block_rule (V,B,R,f) v w = (let x = (SOME x::'v. x \<notin> V) in (((V - {v,w}) \<union> {x}, B, R, f), x))"

fun block_axiom_rule :: "(('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> ereal) \<Rightarrow> bool" where
  "block_axiom_rule \<delta> = (\<forall>f::('v, 'b, 'r) Voting_Rule. \<forall>v\<in>(voters f). \<forall>w\<in>(voters f).
    (uncurry \<delta>) (block_rule f v w) \<ge> Max{\<delta> f v, \<delta> f w})"

fun banzhaf_prob_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v \<Rightarrow> 'b) measure" where
  "banzhaf_prob_rule (V, B, R, f) = uniform_count_measure (actual_funcset V B)"

section \<open>Property Proofs\<close>
                                                
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

end