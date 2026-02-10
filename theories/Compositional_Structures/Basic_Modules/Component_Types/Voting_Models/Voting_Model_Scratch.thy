theory Voting_Model_Scratch
  imports Main

begin

type_synonym ('v, 'b, 'r) Tallying_Method = "(('v \<Rightarrow> 'b) \<Rightarrow> 'r)" (*TODO*)
type_synonym 'x Voters = "'x set" (*TODO*)

text \<open>
A voting rule is a tuple consisting of three sets (of voters, ballots and outcomes)
and a map (the tallying method).
\<close>
(* TODO 'r set-valued? *)
type_synonym ('v, 'b, 'r) Voting_Rule = "'v Voters \<times> 'b set \<times> 'r set \<times> ('v, 'b, 'r) Tallying_Method"

abbreviation rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v, 'b, 'r) Tallying_Method" where
  "rule X \<equiv> snd (snd (snd X))"

abbreviation voters :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v set" where
  "voters X \<equiv> fst X"

abbreviation ballots :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'b set" where
  "ballots X \<equiv> fst (snd X)"

abbreviation results :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'r set" where
  "results X \<equiv> fst (snd (snd X))"

text \<open>
A strategic game is a tuple consisting of two sets (of voters and outcomes),
a vector of sets (of strategies per voters), a vector of relations 
(one preference relation over outcomes per voter) and a map (the tallying method).
\<close>
type_synonym ('v, 'a, 'r) Strategic_Game = 
  "'v set \<times> 'r set \<times> ('v \<Rightarrow> 'a set) \<times> ('v \<Rightarrow> 'r rel) \<times> (('v \<Rightarrow> 'a) \<Rightarrow> 'r)"

text \<open>
A solution concept is a set of ideal, according to some optimality conditions,
strategy profiles to be chosen by players in a strategic game.
\<close>
type_synonym ('v, 'a, 'r) Solution_Concept =
  "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v \<Rightarrow> 'a) set"

fun strat_rule :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v, 'a, 'r) Voting_Rule" where
  "strat_rule (V, R, \<A>, \<P>, f) = (V, \<Union>(\<A> ` V), R, f)"

abbreviation outcome_map ::  "('v, 'a, 'r) Strategic_Game \<Rightarrow> (('v \<Rightarrow> 'a) \<Rightarrow> 'r)" where
  "outcome_map G \<equiv> snd (snd (snd (snd G)))"

abbreviation preferences ::  "('v, 'a, 'r) Strategic_Game \<Rightarrow> ('v \<Rightarrow> 'r rel)" where
  "preferences G \<equiv> fst (snd (snd (snd G)))"
  
end