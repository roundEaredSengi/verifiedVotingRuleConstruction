section \<open>Simple Voting Games\<close>

theory Simple_Voting_Game
  imports Cooperative_Game
          "../Social_Choice_Types/Voting_Models"
          "../Voting_Power"
          "HOL-Probability.Probability_Measure"

begin

subsection \<open>Simple Voting Games\<close>

type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set \<Rightarrow> bool)"

fun SVG_payoff :: "'v Simple_Voting_Game \<Rightarrow> ('v set \<Rightarrow> real)" where
  "SVG_payoff G S = (if (snd G S) then 1 else 0)"

fun players :: "'v Simple_Voting_Game \<Rightarrow> 'v set" where
  "players G = fst G"

fun value_fun :: "'v Simple_Voting_Game \<Rightarrow> ('v set \<Rightarrow> bool)" where
  "value_fun G = snd G"

type_synonym 'v SVG_Voting_Power_Domain = "'v Simple_Voting_Game \<times> 'v"

fun game :: "'v SVG_Voting_Power_Domain \<Rightarrow> 'v Simple_Voting_Game" where
  "game G = fst G"

fun player :: "'v SVG_Voting_Power_Domain \<Rightarrow> 'v" where
  "player G = snd G"

fun uncurry2 :: "('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> (('x \<times> 'y) \<Rightarrow> 'z)" where
  "uncurry2 f = (\<lambda>(x,y). f x y)"

type_synonym 'v SVG_Voting_Power = "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ereal"

type_synonym 'v Uncurried_SVG_Voting_Power = "'v SVG_Voting_Power_Domain \<Rightarrow> ereal"

subsection \<open>Simple Voting Games as a Voting Model\<close>

text \<open>
  A simple voting game is a voting model for voting systems with binary decisions:
  Each voter chooses one out of two options, modelled as True and False and the result is
  the True-option iff the voters choosing it are 
\<close>
locale simple_voting_game = (* TODO model using 0, 1 instead of Booleans *)
  voting_model \<V> "UNIV::(bool set)" "UNIV::(bool set)" \<G> "\<lambda>p. value_fun \<G> (preimg p \<V> True)"
  for \<V> :: "'v set" and \<G> :: "'v Simple_Voting_Game" +
  assumes 
    valid_voters: "players \<G> = \<V>"

sublocale simple_voting_game \<subseteq> 
  voting_model \<V> "UNIV::(bool set)" "UNIV::(bool set)" \<G> "\<lambda>p. value_fun \<G> (preimg p \<V> True)" 
proof (unfold_locales) qed

lemma rule_svg_isomorphism:
  fixes
    \<V> :: "'v set" and
    \<F> :: "('v \<Rightarrow> bool) \<Rightarrow> bool" and
    \<G> :: "'v Simple_Voting_Game" and
    f :: "('v \<Rightarrow> bool) \<Rightarrow> bool" and
    isomorphism :: "(('v \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool"
  assumes
    "voting_rule \<V> (UNIV::bool set) (UNIV::bool set) \<F>" and
    "simple_voting_game \<V> \<G>" and
    "model_isomorphism \<V> (UNIV::bool set) (UNIV::bool set) \<F> \<G> f isomorphism"
  shows
    "f = \<F>" and "f = (\<lambda>p. value_fun \<G> (preimg p \<V> True))"
    (* 
      TODO won't be able to show that? 
      There should be counterexamples in the current implementation - fix that!
    *)
  sorry

interpretation majority_svg_5_voters:
  simple_voting_game "{1,2,3,4,5}" "({1,2,3,4,5}, \<lambda>S. card S \<ge> 3)"
proof (unfold_locales, simp_all) qed

subsection \<open>Voting Power on Simple Voting Games\<close>

fun swing_vote :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool" where
  "swing_vote G v S = (S \<subseteq> players G \<and> value_fun G (S \<union> {v}) \<noteq> value_fun G (S \<union> {v}))"

fun \<delta>\<^sub>B\<^sub>Z :: "('v, 'v Simple_Voting_Game) Voting_Power" where
  "\<delta>\<^sub>B\<^sub>Z G v = 
    (1/2^(card (players G))) 
      * (real (card (preimg (swing_vote G v) {S. S \<subseteq> players G} True)))"

definition AN\<^sub>S\<^sub>V\<^sub>G :: "('v, bool, bool, 'v Simple_Voting_Game) abstract_notions" where
  "AN\<^sub>S\<^sub>V\<^sub>G = 
    (|
      has_swing_vote = (\<lambda> G v. v \<in> players G \<and> (\<exists> S. swing_vote G v S)), 
      rename_model = (\<lambda> \<pi> G. (\<pi> ` (players G), (\<lambda> S. value_fun G {p \<in> players G. \<pi> p \<in> S})))
    |)" (* TODO official preimg function? *)
 
fun tally\<^sub>S\<^sub>V\<^sub>G :: "'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> bool) \<Rightarrow> bool)" where
  "tally\<^sub>S\<^sub>V\<^sub>G \<G> p = value_fun \<G> (preimg p (players \<G>) True)"

lemma classic_svg_banzhaf:
  fixes
    \<V> :: "'v set" and
    \<M> :: "'v Simple_Voting_Game set"
  assumes
    "finite \<V>"
  shows
    "banzhaf_index \<V> (UNIV::(bool set)) (UNIV::(bool set)) {(\<G>, tally\<^sub>S\<^sub>V\<^sub>G \<G>) | \<G>. \<G> \<in> \<M>} \<delta>\<^sub>B\<^sub>Z AN\<^sub>S\<^sub>V\<^sub>G" 
  sorry

end