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
  m1: voting_model "X1::('\<alpha> set)" semantics1 + 
  m2: voting_model "X2::('\<beta> set)" semantics2
  for X1 X2 and 
    semantics1 :: "('\<alpha>, 'v, 'b, 'r) Voting_Rule_Transformation" and 
    semantics2 :: "('\<beta>, 'v, 'b, 'r) Voting_Rule_Transformation" +
  fixes model_equivalence :: "'\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> bool" 
  assumes 
    equiv_sane: "\<forall>a \<in> X1. \<forall>b \<in> X2. model_equivalence a b \<longrightarrow> semantics1 a = semantics2 b"

definition (in voting_model_comparison) domain_equivalence :: bool where
  "domain_equivalence \<equiv> 
    (\<forall>x1 \<in> X1. \<exists>x2 \<in> X2. model_equivalence x1 x2) \<and> (\<forall>x2 \<in> X2. \<exists>x1 \<in> X1. model_equivalence x1 x2)"

end