chapter \<open>Voting Power Definitions\<close>
theory Voting_Power
  imports Voting_Model
          "HOL-Probability.Probability_Measure"

begin

section \<open>Voting Power Definition\<close>

type_synonym ('x, 'v) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> ereal"

section \<open>Voting Power Hierarchy\<close>

\<comment> \<open>
  A voting power index has as domain all pairs of voting model objects 
  and (not necessarily) eligible voters.
  
  We require that a voter who is not eligible in a given voting model object has power equal to 0.
\<close>
locale voting_power = voting_model domain voters ballots results aggregation 
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" +
  fixes
    \<delta> :: "('\<alpha>, 'v) Voting_Power"
  assumes
    no_voter_no_power: "\<forall>a \<in> domain. \<forall>v. v \<notin> voters a \<longrightarrow> \<delta> a v = 0"

section \<open>Voting Power Indices Based on Properties\<close>

locale block_axiom = voting_power domain voters ballots results aggregation \<delta>
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and \<delta> +
  fixes (* Fix additional semantic notions needed to define the block axiom property here *) 
    block_model :: "'\<alpha> \<Rightarrow> '\<alpha> \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  assumes 
    block_sane: "\<forall>m1 \<in> domain. \<forall>m2. \<forall>v \<in> voters m1. \<forall>w \<in> voters m1. \<forall>x. 
      block_model m1 m2 v w x \<longrightarrow> True" and (* TODO: block condition on corresponding voting rule *)
    block_axiom: "\<forall>m1 \<in> domain. \<forall>m2. \<forall>v \<in> voters m1. \<forall>w \<in> voters m1. \<forall>x. 
      block_model m1 m2 v w x \<longrightarrow> \<delta> m2 x \<ge> Max{\<delta> m1 v, \<delta> m2 w}"

locale null_player_axiom = voting_power domain voters ballots results aggregation \<delta>
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and \<delta> +
  assumes
    null_player_axiom: 
      "\<forall>m \<in> domain. \<forall>v \<in> voters m. (has_swing m v = (\<lambda>p. False)) \<longrightarrow> \<delta> m v = 0"

locale symmetry_axiom = voting_power domain voters ballots results aggregation \<delta>
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and \<delta> +
  fixes
    isomorphism :: "('v \<Rightarrow> 'v) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" 
  assumes
    (* Potential additional symmetry requirements: same voter order, same datetime, ... *)
    isomorphism_sane: "\<forall>m1 \<in> domain. \<forall>m2 \<in> domain. \<forall>\<sigma>. 
      bij_betw \<sigma> (voters m1) (voters m2) \<longrightarrow> m2 = isomorphism \<sigma> m1 \<longrightarrow>
      (\<forall>p \<in> profiles m2. aggregation m1 (p \<circ> \<sigma>) = aggregation m2 p)" and 
    symmetry_axiom: "\<forall>m1 \<in> domain. \<forall>m2 \<in> domain. \<forall>\<sigma>. 
      bij_betw \<sigma> (voters m1) (voters m2) \<longrightarrow> m2 = isomorphism \<sigma> m1 \<longrightarrow>
      (\<forall>v \<in> voters m1. \<delta> m1 v = \<delta> m2 (\<sigma> v))"

locale transfer_axiom = voting_power domain voters ballots results aggregation \<delta>
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and \<delta> +
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

locale total_power_axiom = voting_power domain voters ballots results aggregation \<delta>
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and 
    \<delta> :: "('\<alpha>, 'v) Voting_Power" +
  fixes
    swings :: "'\<alpha> \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'b) set"
  assumes
    swings_sane: "\<forall>x \<in> domain. \<forall>v \<in> voters x. \<forall>p \<in> swings x v. \<exists>q. 
        profile x q \<and> p v \<noteq> q v \<and> aggregation x p \<noteq> aggregation x q" and
    total_power_axiom: 
      "\<forall>x \<in> domain. (\<Sum>v \<in> voters x. \<delta> x v) = (card (swings x v))/(card (profiles x))" 
      (* TODO what to divide by? what's the equivalent of 2^(n-1) in SVGs? *)

locale ipower = voting_power domain voters ballots results aggregation \<delta>
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and \<delta> +
  fixes
    space :: "('\<alpha> \<times> 'v) measure"
  assumes
    space_sane: "prob_space space" and
    ipower: "\<forall>m \<in> domain. \<forall>v \<in> voters m. \<exists>A \<in> sets space. 
      \<delta> m v \<ge> 0 \<and> ennreal (\<delta> m v) = emeasure space A"

end