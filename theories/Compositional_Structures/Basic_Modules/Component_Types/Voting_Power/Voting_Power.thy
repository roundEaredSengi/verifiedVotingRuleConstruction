chapter \<open>Voting Power Definitions\<close>
theory Voting_Power
  imports Voting_Model
          "HOL-Probability.Probability_Measure"

begin

section \<open>Voting Power Definition\<close>

type_synonym ('x, 'v) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> ereal"
type_synonym ('x, 'v) Voting_Power_Axiom = "('x, 'v) Voting_Power \<Rightarrow> bool"

section \<open>Voting Power Hierarchy\<close>

\<comment> \<open>
  A voting power index has as domain all pairs of voting model objects 
  and (not necessarily) eligible voters.
  
  We require that a voter who is not eligible in a given voting model object has power equal to 0.
\<close>
locale voting_power = voting_model domain semantics
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" +
  fixes
    \<delta> :: "('\<alpha>, 'v) Voting_Power"

section \<open>Voting Power Axioms\<close>

fun diff :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'x set" where
  "diff f g = {x::'x |x. f x \<noteq> g x}"

fun (in voting_power) swing_vote_predicate :: 
  "('\<alpha> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool) \<Rightarrow> bool" where
  "swing_vote_predicate sv = 
    (\<forall>a \<in> domain. \<forall>v \<in> voters a. \<forall>p \<in> profiles a. sv a v p \<longrightarrow> 
      (\<exists>q \<in> profiles a. v \<in> diff p q \<and> aggregation a p \<noteq> aggregation a q))"

(*
locale block_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes (* Fix additional semantic notions needed to define the block axiom property here *) 
    block_model :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  assumes 
    block_sane: "\<forall>m1 \<in> domain. \<forall>m2. \<forall>v \<in> voters m1. \<forall>w \<in> voters m1. \<forall>x. 
      block_model m1 m2 v w x \<longrightarrow> True" and (* TODO: block condition on corresponding voting rule *)
    block_axiom: "\<forall>m1 \<in> domain. \<forall>m2. \<forall>v \<in> voters m1. \<forall>w \<in> voters m1. \<forall>x. 
      block_model m1 m2 v w x \<longrightarrow> \<delta> m2 x \<ge> Max{\<delta> m1 v, \<delta> m2 w}"
*)

locale null_player_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes
    sv :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool"
  assumes
    swing_vote_predicate: "swing_vote_predicate sv" and
    null_player_axiom: 
      "\<forall>m \<in> domain. \<forall>v \<in> voters m. (has_swing m v = (\<lambda>p. False)) \<longrightarrow> \<delta> m v = 0"

locale total_power_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and
    \<delta> :: "('\<alpha>, 'v) Voting_Power" +
  fixes
    sv :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool"
  assumes
    swing_vote_predicate: "swing_vote_predicate sv" and
    total_power_axiom: 
      "\<forall>m \<in> domain. (\<Sum>v \<in> voters m. \<delta> m v) = 
        (\<Sum>v \<in> voters m. card {p |p. p \<in> profiles m \<and> sv m v p}) 
          / (power (card_ball m) (card_vot m))"

fun (in voting_power) voter_renaming_transformation :: "(('v \<Rightarrow> 'v) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
  "voter_renaming_transformation \<Phi> = 
    (\<forall>m \<in> domain. \<forall>\<sigma> :: 'v \<Rightarrow> 'v. bij \<sigma> \<longrightarrow> 
      \<Phi> \<sigma> m \<in> domain \<and> semantics (\<Phi> \<sigma> m) = rename_rule (semantics m) \<sigma>)"

locale symmetry_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes
    \<Phi> :: "('v \<Rightarrow> 'v) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" 
  assumes
    (* Potential additional symmetry requirements: same voter order, same datetime, ... *)
    isomorphism_sane: "voter_renaming_transformation \<Phi>" and 
    symmetry_axiom: 
      "\<forall>m \<in> domain. \<forall>\<sigma> :: 'v \<Rightarrow> 'v. bij \<sigma> \<longrightarrow> (\<forall>v \<in> voters m. \<delta> m v = \<delta> (\<Phi> \<sigma> m) (\<sigma> v))"

locale transfer_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes
    (* \<odot> :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" and \<otimes> :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" *)
    tf1 :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" and tf2 :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>"
  assumes
    model_transformation_1: "\<forall>a \<in> domain. \<forall>b \<in> domain. tf1 a b \<in> domain" and
    model_transformation_2: "\<forall>a \<in> domain. \<forall>b \<in> domain. tf2 a b \<in> domain" and
    transfer_axiom: "True" (* TODO *)

locale ipower = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes
    space :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> 'x measure" and
    event :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> 'x set"
  assumes
    space_sane: "\<forall>m \<in> domain. \<forall>v \<in> voters m. prob_space (space m v)" and
    event_sane: "\<forall>m \<in> domain. \<forall>v \<in> voters m. event m v \<in> sets (space m v)" and
    ipower:
      "\<forall>m \<in> domain. \<forall>v \<in> voters m. 
        \<delta> m v \<ge> 0 \<and> \<delta> m v = enn2ereal (emeasure (space m v) (event m v))"

end