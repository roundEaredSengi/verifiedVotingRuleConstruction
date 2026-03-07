chapter \<open>Strategic Game\<close>

theory Strategic_Game
  imports Voting_Rule

begin

section \<open>Voting Model\<close>

section \<open>Voting Power Indices\<close>

text \<open>
  First formulation of a Banzhaf index for strategic games: 
  The same as the Banzhaf index of the induced voting rule.
\<close>
fun banzhaf_strat_1 :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_strat_1 G v = banzhaf_rule_1 (strat_rule G) v" (* TODO *)

text \<open>
  Second formulation of a Banzhaf index for strategic games: 
  Assumes the optimal strategy profiles from a given solution concept are uniformly distributed.
\<close>
fun banzhaf_strat_2 :: 
  "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v, 'a, 'r) Solution_Concept \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_strat_2 G C v = (1/(card (C G))) 
    * (\<Sum> A \<in> C G. (Max {characteristic (swing_vote_rule (outcome_map G) v A) {1} A' | A'. A' \<in> C G}))"

text \<open>
  Third formulation of a Banzhaf index for strategic games: 
  Includes the notion of success. 
  A voter v's successful swing vote is a strategy profile A where v prefers the result after 
  changing their vote to the result in A. 
\<close>
(* TODO type abbreviations for frequent types *)
fun swing_vote_success ::
  "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ereal" where
  "swing_vote_success G v A A' = 
    (if (differ_only_on v A A' 
      \<and> (outcome_map G A, outcome_map G A') \<in> preferences G v) then 1 else 0)"

fun banzhaf_strat_3 ::
  "('v, 'a, 'r) Solution_Concept \<Rightarrow> (('v, 'a, 'r) Strategic_Game, 'v) Voting_Power" where
  "banzhaf_strat_3 C G v = (1/(card (C G)))
    * (\<Sum> A \<in> C G. (Max {characteristic (swing_vote_success G v A) {1} A' | A'. A' \<in> C G}))"

section \<open>Voting Power Properties\<close>

fun is_null_player_strat :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_null_player_strat G v = (\<forall>A. range (swing_vote_success G v A) = {0})"

fun null_player_axiom_strat :: 
  "('v, 'a, 'r) Strategic_Game set \<Rightarrow> (('v, 'a, 'r) Strategic_Game, 'v) Voting_Power \<Rightarrow> bool" where
  "null_player_axiom_strat X \<delta> = 
    (\<forall>G \<in> X. \<forall>v \<in> voters_strat G. is_null_player_strat G v \<longrightarrow> \<delta> G v = 0)"

section \<open>Property Proofs\<close>

lemma  banzhaf_3_satisfies_null_player_axiom:
  fixes
    C :: "('v, 'a, 'r) Solution_Concept"
  shows
    "null_player_axiom_strat UNIV (banzhaf_strat_3 C)"
  sorry

end