chapter \<open>Voting Power Definitions\<close>
theory Voting_Power
  imports Voting_Model
          "HOL-Probability.Probability_Measure"

begin

section \<open>Voting Power Definition\<close>

type_synonym ('x, 'v) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> ereal"
type_synonym ('x, 'v) Voting_Power_Axiom = "'x set \<Rightarrow> ('x, 'v) Voting_Power \<Rightarrow> bool"

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
  assumes
    no_voter_no_power: "\<forall>a \<in> domain. \<forall>v. v \<notin> rule_voters (semantics a) \<longrightarrow> \<delta> a v = 0"

section \<open>Voting Power Indices Based on Properties\<close>

locale block_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes (* Fix additional semantic notions needed to define the block axiom property here *) 
    block_model :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  assumes 
    block_sane: "\<forall>m1 \<in> domain. \<forall>m2. \<forall>v \<in> voters m1. \<forall>w \<in> voters m1. \<forall>x. 
      block_model m1 m2 v w x \<longrightarrow> True" and (* TODO: block condition on corresponding voting rule *)
    block_axiom: "\<forall>m1 \<in> domain. \<forall>m2. \<forall>v \<in> voters m1. \<forall>w \<in> voters m1. \<forall>x. 
      block_model m1 m2 v w x \<longrightarrow> \<delta> m2 x \<ge> Max{\<delta> m1 v, \<delta> m2 w}"

locale null_player_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  assumes
    null_player_axiom: 
      "\<forall>m \<in> domain. \<forall>v \<in> voters m. (has_swing m v = (\<lambda>p. False)) \<longrightarrow> \<delta> m v = 0"

fun (in voting_power) isomorphism_sanity :: "(('v \<Rightarrow> 'v) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
  "isomorphism_sanity \<pi> = (\<forall>m1 \<in> domain. \<forall>m2 \<in> domain. \<forall>\<sigma>. 
    bij_betw \<sigma> (voters m1) (voters m2) \<longrightarrow> m2 = \<pi> \<sigma> m1 \<longrightarrow>
      (ballots m1 = ballots m2 \<and> results m1 = results m2 \<and>
      (\<forall>p \<in> profiles m2. aggregation m1 (p \<circ> \<sigma>) = aggregation m2 p)))"

fun (in voting_power) symmetry :: "(('v \<Rightarrow> 'v) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> bool" where
  "symmetry \<pi> = (\<forall>m1 \<in> domain. \<forall>m2 \<in> domain. \<forall>\<sigma>. 
    bij_betw \<sigma> (voters m1) (voters m2) \<longrightarrow> m2 = \<pi> \<sigma> m1 \<longrightarrow> (\<forall>v \<in> voters m1. \<delta> m1 v = \<delta> m2 (\<sigma> v)))"

locale symmetry_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes
    isomorphism :: "('v \<Rightarrow> 'v) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" 
  assumes
    (* Potential additional symmetry requirements: same voter order, same datetime, ... *)
    isomorphism_sane: "isomorphism_sanity isomorphism" and 
    symmetry_axiom: "symmetry isomorphism"

locale transfer_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes 
    meet :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" and
    join :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" and
    meet_res :: "'r \<Rightarrow> 'r \<Rightarrow> 'r" and (* TODO this or "'\<alpha> \<Rightarrow> ('r::lattice) set"? *)
    join_res :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
  assumes
    meet_valid: "\<forall>x \<in> domain. \<forall>y \<in> domain. meet x y \<in> domain" and
    join_valid: "\<forall>x \<in> domain. \<forall>y \<in> domain. join x y \<in> domain" and
    meet_sane: "\<forall>x \<in> domain. \<forall>y \<in> domain. \<forall>p. profile x p \<and> profile y p \<longrightarrow> 
      aggregation (meet x y) p = meet_res (aggregation x p) (aggregation y p)" and 
    join_sane: "\<forall>x \<in> domain. \<forall>y \<in> domain. \<forall>p. profile x p \<and> profile y p \<longrightarrow> 
      aggregation (join x y) p = join_res (aggregation x p) (aggregation y p)" and
    transfer_axiom: "\<forall>m1 \<in> domain. \<forall>m2 \<in> domain. voters m1 = voters m2 \<longrightarrow>
      (\<forall>v \<in> voters m1. \<delta> (meet m1 m2) v + \<delta> (join m1 m2) v = \<delta> m1 v + \<delta> m2 v)"

locale total_power_axiom = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and
    \<delta> :: "('\<alpha>, 'v) Voting_Power" +
  fixes
    swings :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'b) set"
  assumes
    swings_sane: "\<forall>x \<in> domain. \<forall>v \<in> voters x. \<forall>p \<in> swings x v. \<exists>q. 
        profile x q \<and> p v \<noteq> q v \<and> aggregation x p \<noteq> aggregation x q" and
    total_power_axiom: 
      "\<forall>x \<in> domain. (\<Sum>v \<in> voters x. \<delta> x v) = (card (swings x v))/(card (profiles x))" 
      (* TODO is this the division we want? *)

locale ipower = voting_power domain semantics \<delta>
  for domain :: "'\<alpha> set" and semantics :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta> +
  fixes
    space :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> 'x measure" and
    event :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> 'x set"
  assumes
    space_sane: "\<forall>m \<in> domain. \<forall>v \<in> voters m. prob_space (space m v)" and
    event_sane: "\<forall>m \<in> domain. \<forall>v \<in> voters m. event m v \<in> sets (space m v)" and
    ipower:
      "\<forall>m \<in> domain. \<forall>v \<in> voters m. \<delta> m v \<ge> 0 \<and> \<delta> m v = emeasure (space m v) (event m v)"

end