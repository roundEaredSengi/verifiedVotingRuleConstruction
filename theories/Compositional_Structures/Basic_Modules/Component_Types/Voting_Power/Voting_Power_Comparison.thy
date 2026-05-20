chapter \<open>Voting Power Comparison\<close>
theory Voting_Power_Comparison
  imports Voting_Power
          Voting_Model_Comparison

begin

section \<open>Voting Power Comparison Definition\<close>

locale voting_power_comparison = 
  pow1: voting_power domain1 voters1 ballots1 results1 aggregation1 \<delta>1 +
  pow2: voting_power domain2 voters2 ballots2 results2 aggregation2 \<delta>2 +
  comp: 
    voting_model_comparison 
      domain1 domain2 voters1 voters2 ballots1 ballots2 
      results1 results2 aggregation1 aggregation2 model_equivalence
      for model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" and
          domain1 and voters1 :: "'\<alpha> \<Rightarrow> 'v set" and ballots1 :: "'\<alpha> \<Rightarrow> 'b set" and 
          results1 :: "'\<alpha> \<Rightarrow> 'r set" and aggregation1 \<delta>1 and
          domain2 and voters2 :: "'\<beta> \<Rightarrow> 'v set" and ballots2 :: "'\<beta> \<Rightarrow> 'b set" and 
          results2 :: "'\<beta> \<Rightarrow> 'r set" and aggregation2 \<delta>2
begin

section \<open>Voting Power Comparison Properties\<close>

\<comment> \<open>
The two power indices are equivalent w.r.t. their domains 
if they yield identical power values for equivalent inputs.

Note that model equivalence implies voters1 m1 = voters2 m2, 
so choosing a v from the first set should be sane.
\<close>
definition power_equality :: bool where
  "power_equality = (\<forall>m1 \<in> domain1. \<forall>m2 \<in> domain2. model_equivalence m1 m2
    \<longrightarrow> (\<forall>v \<in> voters1 m1. \<delta>1 m1 v = \<delta>2 m2 v))"

end

end