theory Voting_Power_Scratch
  imports "HOL-Library.Extended_Real"
          "../Voting_Models/Voting_Model_Scratch"

begin

fun swing_vote_svg :: "'v set set \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> ereal" where
  "swing_vote_svg \<F> v S = (if ((S \<union> {v}) \<in> \<F>) \<noteq> ((S - {v}) \<in> \<F>) then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for simple voting games:
  Count the number of coalitions a voter can change by switching their vote and average over those.
\<close>
fun banzhaf_svg_1 :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_svg_1 (V, \<F>) v = (1/(2^(card V))) * (\<Sum> S \<in> {S::'v set. S \<subseteq> V}. swing_vote_svg \<F> v S)"



fun differ_only_on :: "'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> bool" where
  "differ_only_on v p p' = (\<forall>x. p x \<noteq> p' x \<longrightarrow> x = v)"

fun swing_vote :: "(('v \<Rightarrow> 'b) \<Rightarrow> 'r) \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ereal" where
  "swing_vote f v p p' = (if (differ_only_on v p p' \<and> f p \<noteq> f p') then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for voting rules:
  Count the number of profiles where the outcome would change if a voter changed their ballot
  while all other voters kept theirs, then average over all profiles.
\<close>
fun banzhaf_rule_1 :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_rule_1 (V, B, R, f) v = 
    (1/(real ((card B)^(card V)))) * 
      (\<Sum> p \<in> UNIV. \<Sum> p' \<in> UNIV. (swing_vote f v p p'))" (* Why are the carrier sets needed? *)



text \<open>
  First formulation of a Banzhaf index for strategic games: TODO
\<close>
fun banzhaf_strat_1 :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_strat_1 (V, R, A, P, f) v = 0" (* TODO *)
                     
end