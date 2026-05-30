chapter \<open>Voting Rule\<close>

theory Voting_Rule
  imports Voting_Model

begin

section \<open>Voting Rules as a Voting Model\<close>

locale voting_rule_model =
  voting_model R id
  for R :: "('v, 'b, 'r) Voting_Rule set"

sublocale voting_rule_model \<subseteq> voting_model R id
  by (rule local.voting_model_axioms)
(* TODO why can I write utter bs here? *)

definition valid_voting_rules :: "('v, 'b, 'r) Voting_Rule set" where
  "valid_voting_rules =
    {\<R> :: ('v, 'b, 'r) Voting_Rule. 
      \<forall>p \<in> funcset (rule_voters \<R>) (rule_ballots \<R>). rule \<R> p \<in> rule_results \<R>}"

interpretation voting_rules: voting_rule_model valid_voting_rules
  unfolding valid_voting_rules_def
  by (unfold_locales, simp)

(* TODO electoral_module as locale instantiation?  *)


end