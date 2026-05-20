chapter \<open>Voting Models\<close>

theory Voting_Model
  imports "HOL-Library.Extended_Nonnegative_Real"

begin

section \<open>Auxiliary Definitions\<close>

type_synonym 'x Voters = "'x set" (*TODO*)
type_synonym 'b Ballots = "'b set" (*TODO*)
type_synonym 'r Results = "'r set" (*TODO*)
type_synonym ('v, 'b, 'r) Aggregation_Method = "(('v \<Rightarrow> 'b) \<Rightarrow> 'r)" (*TODO*)

fun preimg_in :: "'x set \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x set" where
  "preimg_in X f Y = {x |x. x \<in> X \<and> f x \<in> Y}"

section \<open>Voting Model Definition\<close>

(* 
Voting models as types of a typeclass: 
  class voting_model where
    voter_set :: "\<alpha> \<Rightarrow> 'v set" 
Problem: 'v is an additional type variable.
*)
 
(* Same thing (+ more) as a locale: *)

type_synonym ('v, 'b) Profile = "'v \<Rightarrow> 'b"

\<comment> \<open>
  A voting model consists of a set of voting configurations of a given type \<^latex>\<open>\<tau>\<close>,
  each of which models a real world voting situation by modelling, at the very least,
  the real world set of eligible voters, the set of eligible results and the set of
  possible ballots/votes per voter as well as the aggregation method that defines
  how individual choices map to an election outcome.
\<close>
locale voting_model = 
  fixes
    voting_setups :: "'\<tau> set" and
    eligible_voters :: "'\<tau> \<Rightarrow> 'v set" and
    ballot_set :: "'\<tau> \<Rightarrow> 'b set" and
    result_set :: "'\<tau> \<Rightarrow> 'r set" and
    aggregation_method :: "'\<tau> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method"
  assumes
    "\<forall>c \<in> voting_setups. 
      \<forall>p \<in> funcset (eligible_voters c) (ballot_set c). aggregation_method c p \<in> result_set c"
begin

abbreviation valid_voter :: "'\<tau> \<Rightarrow> 'v \<Rightarrow> bool" where
  "valid_voter x v \<equiv> (v \<in> eligible_voters x)"

fun differ_only_on :: "'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "differ_only_on v p q = (\<forall>w. w \<noteq> v \<longrightarrow> p w = q w)"

fun is_single_swing :: "'\<tau> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "is_single_swing setup v p q = 
    (differ_only_on v p q \<and> valid_voter setup v \<and> 
    aggregation_method setup p \<noteq> aggregation_method setup q)"

fun has_swing :: "'\<tau> \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "has_swing setup v p = (\<exists>q. is_single_swing setup v p q)"

definition profile :: "'\<tau> \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "profile x p = (\<forall>v \<in> eligible_voters x. p v \<in> ballot_set x)"

definition profiles :: "'\<tau> \<Rightarrow> ('v, 'b) Profile set" where
  "profiles x = Collect (profile x)"

definition vote_changes :: "'\<tau> \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'v \<Rightarrow> ('v, 'b) Profile set" where
  "vote_changes x p v = {q |q. profile x q \<and> q v \<noteq> p v}"

end

end