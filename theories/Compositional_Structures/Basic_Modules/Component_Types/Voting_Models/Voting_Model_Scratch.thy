theory Voting_Model_Scratch
  imports Main

begin

type_synonym ('v, 'b, 'r) Tallying_Method = "(('v \<Rightarrow> 'b) \<Rightarrow> 'r)" (*TODO*)
type_synonym 'x Voters = "'x set" (*TODO*)

text \<open>
A simple voting game is a tuple consisting of a set (of voters) 
and a set family (of voter coalitions).
\<close>
type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set set)"

text \<open>
A voting rule is a tuple consisting of three sets (of voters, ballots and outcomes)
and a map (the tallying method).
\<close>
type_synonym ('v, 'b, 'r) Voting_Rule = "'v Voters \<times> 'b set \<times> 'r set \<times> ('v, 'b, 'r) Tallying_Method"

fun rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v, 'b, 'r) Tallying_Method" where
  "rule (V, B, R, f) = f"

fun voters :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v set" where
  "voters (V, B, R, f) = V"

fun ballots :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'b set" where
  "ballots (V, B, R, f) = B"

text \<open>
A strategic game is a tuple consisting of two sets (of voters and outcomes),
a vector of sets (of strategies per voters), a vector of relations 
(one preference relation over outcomes per voter) and a map (the tallying method).
\<close>
type_synonym ('v, 'a, 'r) Strategic_Game = 
  "'v set \<times> 'r set \<times> ('v \<Rightarrow> 'a set) \<times> ('v \<Rightarrow> 'r rel) \<times> (('v \<Rightarrow> 'a) \<Rightarrow> 'r)"  

end