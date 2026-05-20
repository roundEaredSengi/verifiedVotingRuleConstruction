theory Voting_Model_Comparison
  imports Voting_Rule
          Simple_Voting_Game

begin

section \<open>Voting Model Comparison\<close>

\<comment> \<open>
  To compare two voting models, we fix them and a notion of two objects being equivalent, 
  that is, representing the same voting system.
  We require that any two objects that represent
  the same voting system are associated with the same aggregation method and the same sets of 
  eligible voters, ballots and results, respectively.
  Note that requiring equality instead of bijections might be rather strict. 
  However, since bijections only represent renaming, we just require the same names for simplicity.
\<close>
locale voting_model_comparison = 
  m1: voting_model "X1::('\<alpha> set)" voters1 ballots1 results1 tallying1 + 
  m2: voting_model "X2::('\<beta> set)" voters2 ballots2 results2 tallying2
  for X1 X2 and 
    voters1 :: "'\<alpha> \<Rightarrow> 'v set" and voters2 :: "'\<beta> \<Rightarrow> 'v set" and
    ballots1 :: "'\<alpha> \<Rightarrow> 'b set" and ballots2 :: "'\<beta> \<Rightarrow> 'b set" and 
    results1 :: "'\<alpha> \<Rightarrow> 'r set" and results2 :: "'\<beta> \<Rightarrow> 'r set" and
    tallying1 :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and 
    tallying2 :: "'\<beta> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" +
  fixes model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" 
  assumes 
    "\<forall>a \<in> X1. \<forall>b \<in> X2. model_equivalence a b \<longrightarrow> 
      voters1 a = voters2 b \<and>
      results1 a = results2 b \<and>
      ballots1 a = ballots2 b \<and>
      tallying1 a = tallying2 b"

end