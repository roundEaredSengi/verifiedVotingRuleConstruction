chapter \<open>Voting Rule\<close>

theory Voting_Rule
  imports Voting_Model

begin

section \<open>Voting Rule Definition\<close>

type_synonym ('v, 'b, 'r) Voting_Rule = 
  "'v Voters \<times> 'b set \<times> 'r set \<times> ('v, 'b, 'r) Aggregation_Method"

abbreviation rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" where
  "rule X \<equiv> snd (snd (snd X))"

abbreviation voters :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v set" where
  "voters X \<equiv> fst X"

abbreviation ballots :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'b set" where
  "ballots X \<equiv> fst (snd X)"

abbreviation results :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'r set" where
  "results X \<equiv> fst (snd (snd X))"

section \<open>Voting Rules as a Voting Model\<close>

locale voting_rule_model =
  voting_model R voters ballots results rule
  for R :: "('v, 'b, 'r) Voting_Rule set"

sublocale voting_rule_model \<subseteq> voting_model R voters ballots results rule
  by (rule local.voting_model_axioms)
(* TODO why can I write utter bs here? *)

definition valid_voting_rules :: "('v, 'b, 'r) Voting_Rule set" where
  "valid_voting_rules =
    {\<R> :: ('v, 'b, 'r) Voting_Rule. \<forall>p \<in> funcset (voters \<R>) (ballots \<R>). rule \<R> p \<in> results \<R>}"

interpretation voting_rules: voting_rule_model valid_voting_rules
  unfolding valid_voting_rules_def
  by (unfold_locales, simp)

(* TODO electoral_module as locale instantiation?  *)


end