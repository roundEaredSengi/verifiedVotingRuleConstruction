chapter \<open>Voting Models\<close>

theory Voting_Model
  imports "HOL-Library.Extended_Nonnegative_Real"

begin

section \<open>Voting Rule Definition\<close>

type_synonym 'x Voters = "'x set" (*TODO*)
type_synonym 'b Ballots = "'b set" (*TODO*)
type_synonym 'r Results = "'r set" (*TODO*)
type_synonym ('v, 'b, 'r) Aggregation_Method = "(('v \<Rightarrow> 'b) \<Rightarrow> 'r)" (*TODO*)

text \<open>
  We use voting rules as a kind of "canonical voting model" in the sense that every voting model
  comes with a transformation of its structures into voting rules.
\<close> 
type_synonym ('v, 'b, 'r) Voting_Rule = 
  "'v Voters \<times> 'b Ballots \<times> 'r Results \<times> ('v, 'b, 'r) Aggregation_Method"

abbreviation rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" where
  "rule X \<equiv> snd (snd (snd X))"

abbreviation rule_voters :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v set" where
  "rule_voters X \<equiv> fst X"

abbreviation rule_ballots :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'b set" where
  "rule_ballots X \<equiv> fst (snd X)"

abbreviation rule_results :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'r set" where
  "rule_results X \<equiv> fst (snd (snd X))"

fun rule_profiles :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v \<Rightarrow> 'b) set" where
  "rule_profiles r = funcset (rule_voters r) (rule_ballots r)"

abbreviation rule_profile :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> bool" where
  "rule_profile r p \<equiv> (p \<in> rule_profiles r)"

fun preimg_in :: "'x set \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x set" where
  "preimg_in X f Y = {x |x. x \<in> X \<and> f x \<in> Y}"

fun valid_voting_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> bool" where
  "valid_voting_rule f = (\<forall>p \<in> rule_profiles f. (rule f) p \<in> rule_results f)"

fun rename_aggregation :: 
  "('v, 'b, 'r) Aggregation_Method \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" where
  "rename_aggregation f \<sigma> p = f (p \<circ> \<sigma>)"

fun rename_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('v, 'b, 'r) Voting_Rule" where
  "rename_rule f \<sigma> = 
    (\<sigma> ` (rule_voters f), rule_ballots f, rule_results f, rename_aggregation (rule f) \<sigma>)"

section \<open>Voting Model Definition\<close>

type_synonym ('v, 'b) Profile = "'v \<Rightarrow> 'b"
type_synonym ('x, 'v, 'b, 'r) Voting_Rule_Transformation = "'x \<Rightarrow> ('v, 'b, 'r) Voting_Rule"

(* 
Voting models as types of a typeclass: 
  class voting_model where
    voter_set :: "\<alpha> \<Rightarrow> 'v set" 
Problem: 'v is an additional type variable.
*)
 
(* Same thing (+ more) as a locale: *)

\<comment> \<open>
  A voting model consists of a set of voting configurations of a given type \<^latex>\<open>\<tau>\<close>,
  each of which models a real world voting situation by modelling, at the very least,
  the real world set of eligible voters, the set of eligible results and the set of
  possible ballots/votes per voter as well as the aggregation method that defines
  how individual choices map to an election outcome.
\<close>
locale voting_model = 
  fixes
    voting_structures :: "'\<tau> set" and
    semantics :: "('\<tau>, 'v, 'b, 'r) Voting_Rule_Transformation"
  assumes "\<forall>x \<in> voting_structures. valid_voting_rule (semantics x)"
begin

abbreviation voters :: "'\<tau> \<Rightarrow> 'v Voters" where "voters x \<equiv> (rule_voters (semantics x))"
abbreviation ballots :: "'\<tau> \<Rightarrow> 'b Ballots" where "ballots x \<equiv> (rule_ballots (semantics x))"
abbreviation results :: "'\<tau> \<Rightarrow> 'r Results" where "results x \<equiv> (rule_results (semantics x))"
abbreviation aggregation :: "'\<tau> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" where 
  "aggregation x \<equiv> (rule (semantics x))"

abbreviation card_vot :: "'\<tau> \<Rightarrow> nat" where
  "card_vot x \<equiv> card (voters x)"

abbreviation card_ball :: "'\<tau> \<Rightarrow> nat" where
  "card_ball x \<equiv> card (ballots x)"

abbreviation valid_voter :: "'\<tau> \<Rightarrow> 'v \<Rightarrow> bool" where
  "valid_voter x v \<equiv> (v \<in> rule_voters (semantics x))"

fun differ_only_on :: "'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "differ_only_on v p q = (\<forall>w. w \<noteq> v \<longrightarrow> p w = q w)"

fun is_single_swing :: "'\<tau> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "is_single_swing setup v p q = 
    (differ_only_on v p q \<and> valid_voter setup v \<and> 
    rule (semantics setup) p \<noteq> rule (semantics setup) q)"

fun has_swing :: "'\<tau> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "has_swing setup v p = (\<exists>q. is_single_swing setup v p q)"

abbreviation profile :: "'\<tau> \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "profile \<equiv> rule_profile \<circ> semantics"

abbreviation profiles :: "'\<tau> \<Rightarrow> ('v, 'b) Profile set" where
  "profiles \<equiv> rule_profiles \<circ> semantics"

definition vote_changes :: "'\<tau> \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile set" where
  "vote_changes x p v = {q |q. profile x q \<and> q v \<noteq> p v}"

end

end